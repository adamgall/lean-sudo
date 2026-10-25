import LeanSudo.IoLog
import LeanSudo.Sys.Core
import LeanSudo.Sys.Prim.IoLog
import LeanSudo.Sys.Prim.Extra
import LeanSudo.Sys.LogSrv
import LeanSudo.Sys.Relay
import LeanSudo.Sys.TimeFormat

namespace LeanSudo.Sys.IoLog


private structure Zlib where
  handle : UInt64 := 0
  openFn : UInt64 := 0
  writeFn : UInt64 := 0
  flushFn : UInt64 := 0
  closeFn : UInt64 := 0
  deriving Inhabited

private structure State where
  active : Bool := false
  compressed : Bool := false
  flush : Bool := false
  ignoreErrors : Bool := false
  passwords : Bool := false
  filtered : Bool := false
  uid : UInt32 := 0
  gid : UInt32 := 0
  mode : UInt32 := 0
  files : Array (Option (UInt32 × UInt64)) := Array.replicate 6 none
  patterns : Array UInt64 := #[]
  last : Nat := 0
  deriving Inhabited

private initialize current : IO.Ref State ← IO.mkRef {}
private initialize compression : IO.Ref Zlib ← IO.mkRef {}

private def discard (action : IO α) : IO Unit := do
  try let _ ← action; pure () catch _ => pure ()

private def failure (context : String) : IO α :=
  throw (IO.userError context)

private def abort : IO Unit := do
  let s ← current.get
  let z ← compression.get
  current.set { s with active := false, files := Array.replicate 6 none, patterns := #[] }
  for file in s.files do
    if let some (fd, gz) := file then
      if gz != 0 then discard (Prim.IoLog.gzclose z.closeFn gz) else discard (Prim.IoLog.close fd)
  for pattern in s.patterns do
    Prim.IoLog.regexRelease pattern
    Prim.IoLog.free pattern

private def loadCompression : IO Unit := do
  let constants ← Prim.IoLog.constants
  let mut z ← compression.get
  if z.handle == 0 then
    let handle ← Prim.IoLog.dlopen "libz.so.1" (constants.loadNow ||| constants.loadLocal)
    if handle == 0 then failure "I/O log compression: Function not implemented"
    z := {
      handle
      openFn := ← Prim.IoLog.dlsym handle "gzdopen"
      writeFn := ← Prim.IoLog.dlsym handle "gzwrite"
      flushFn := ← Prim.IoLog.dlsym handle "gzflush"
      closeFn := ← Prim.IoLog.dlsym handle "gzclose" }
    compression.set z
  if z.openFn == 0 || z.writeFn == 0 || z.flushFn == 0 || z.closeFn == 0 then
    failure "I/O log compression ABI: Function not implemented"

private def compilePatterns (patterns : Array String) : IO Unit := do
  let constants ← Prim.IoLog.constants
  unless (← current.get).passwords do
    for text in patterns do
      let pattern ← Prim.IoLog.regexAlloc
      if (← Prim.IoLog.regexCompile pattern text
          (constants.regexExtended ||| constants.regexNoSub)) != 0 then
        Prim.IoLog.free pattern
        failure "I/O log password filter: Invalid argument"
      current.modify fun s => { s with patterns := s.patterns.push pattern }

def remote (flags : UInt32) (patterns : Array String) : IO Unit := do
  abort
  current.modify fun s => { s with
    ignoreErrors := flags &&& 128 != 0
    passwords := flags &&& 256 != 0 }
  try compilePatterns patterns catch e => abort; throw e

private def dirMode (constants : Prim.IoLog.Constants) (mode : UInt32) : UInt32 :=
  let mode := mode ||| constants.ownerAll
  let mode := if mode &&& constants.groupReadWrite != 0 then
    mode ||| constants.groupExecute else mode
  if mode &&& constants.otherReadWrite != 0 then mode ||| constants.otherExecute else mode

private def directory (path : String) : IO UInt32 := do
  let constants ← Prim.IoLog.constants
  unless path.startsWith "/" do failure "I/O log directory: Invalid argument"
  let s ← current.get
  let flags := constants.readOnly ||| constants.directory ||| constants.closeExec
  let descriptor ← IO.mkRef (← Prim.IoLog.openat constants.currentDirectory "/" flags 0)
  try
    for part in path.splitOn "/" do
      unless part.isEmpty do
        let fd ← descriptor.get
        if part == "." || part == ".." then failure "I/O log directory: Invalid argument"
        let status ← Prim.IoLog.mkdirat fd part constants.ownerAll
        if status != 0 && status != constants.alreadyExists then
          failure ("I/O log directory: " ++ (← Prim.IoLog.errorText status))
        let next ← Prim.IoLog.openat fd part (flags ||| constants.noFollow) 0
        discard (Prim.IoLog.close fd)
        descriptor.set next
        let fd := next
        if status == 0 then
          Prim.IoLog.chown fd s.uid s.gid
          Prim.IoLog.chmod fd (dirMode constants s.mode)
    let fd ← descriptor.get
    Prim.IoLog.chown fd s.uid s.gid
    Prim.IoLog.chmod fd (dirMode constants s.mode)
    return fd
  catch e =>
    discard (Prim.IoLog.close (← descriptor.get))
    throw e

private def logFile (dir : UInt32) (name : String) : IO UInt32 := do
  let constants ← Prim.IoLog.constants
  let s ← current.get
  let flags := constants.writeOnly ||| constants.create ||| constants.noFollow |||
    constants.closeExec ||| constants.nonblock
  let fd ← Prim.IoLog.openat dir name flags constants.ownerReadWrite
  try
    let (mode, links, uid) ← Prim.IoLog.stat fd
    unless mode &&& constants.fileType.toNat == constants.regularFile.toNat &&
        links == 1 && (uid == 0 || uid == s.uid.toNat) do
      failure "I/O log session files: Invalid argument"
    Prim.IoLog.chown fd s.uid s.gid
    Prim.IoLog.chmod fd s.mode
    Prim.IoLog.truncate fd 0
    return fd
  catch e =>
    discard (Prim.IoLog.close fd)
    throw e

private partial def writeAll (fd : UInt32) (bytes : ByteArray) (offset : Nat := 0) : IO Unit := do
  if offset < bytes.size then
    let constants ← Prim.IoLog.constants
    let (count, error) ← Prim.IoLog.write fd bytes offset.toUInt64
    if error == constants.interrupted then
      writeAll fd bytes offset
    else
      if error != 0 then failure (← Prim.IoLog.errorText error)
      if count == 0 then failure "Input/output error"
      writeAll fd bytes (offset + count)

private def sequenceValue (bytes : ByteArray) : IO Nat := do
  if bytes.isEmpty then return 0
  unless bytes.size == 6 || (bytes.size == 7 && bytes[6]! == 10) do
    failure "I/O log sequence: Invalid argument"
  let mut value := 0
  for i in [:6] do
    let c := bytes[i]!.toNat
    let digit ← if 48 ≤ c && c ≤ 57 then pure (c - 48)
      else if 65 ≤ c && c ≤ 90 then pure (c - 65 + 10)
      else if 97 ≤ c && c ≤ 122 then pure (c - 97 + 10)
      else failure "I/O log sequence: Invalid argument"
    value := value * 36 + digit
  return value

private def prepare (dir user group : String) (mode maxseq : UInt32) : IO Nat := do
  let constants ← Prim.IoLog.constants
  current.set { mode := (mode &&& constants.permissions) ||| constants.ownerReadWrite }
  let some owner ← LeanSudo.Sys.getpwnam user | failure "I/O log owner: No such file or directory"
  let gid ← if group.isEmpty then pure owner.gid else do
    let some group ← LeanSudo.Sys.getgrnam group |
      failure "I/O log group: No such file or directory"
    pure group.gid
  current.modify fun s => { s with uid := owner.uid.toUInt32, gid := gid.toUInt32 }
  let s ← current.get
  let d ← directory dir
  let flags := constants.readWrite ||| constants.create ||| constants.noFollow |||
    constants.closeExec ||| constants.nonblock
  let fd ← try Prim.IoLog.openat d "seq" flags constants.ownerReadWrite
    finally discard (Prim.IoLog.close d)
  try
    let (mode, links, _) ← Prim.IoLog.stat fd
    unless mode &&& constants.fileType.toNat == constants.regularFile.toNat && links == 1 do
      failure "I/O log sequence: Invalid argument"
    Prim.IoLog.lock fd constants.lockExclusive
    Prim.IoLog.chown fd s.uid s.gid
    Prim.IoLog.chmod fd s.mode
    let value := LeanSudo.IoLog.nextSequence
      (← sequenceValue (← Prim.IoLog.pread fd 7 0)) maxseq.toNat
    let bytes := (LeanSudo.IoLog.sequence value ++ "\n").toUTF8
    unless (← Prim.IoLog.pwrite fd bytes 0) == 7 do failure "I/O log sequence: Invalid argument"
    Prim.IoLog.truncate fd 7
    return value
  finally discard (Prim.IoLog.close fd)

private def clock (formats : Array String) (locale : String) : IO (Array String) := do
  let constants ← Prim.IoLog.constants
  let (seconds, nanos) ← Prim.IoLog.clock constants.realtime
  let some tm ← Prim.CoreLogs.localtime seconds.toUInt64 |
    failure "Value too large for defined data type"
  LeanSudo.Sys.Prim.Extra.withLocale locale "unable to initialize I/O logging locale" do
    let (rows, cols) ← try
      let flags := constants.readOnly ||| constants.noControllingTty ||| constants.closeExec
      let fd ← Prim.IoLog.openat constants.currentDirectory "/dev/tty" flags 0
      try Prim.IoLog.winsize fd finally discard (Prim.IoLog.close fd)
    catch _ => pure (0, 0)
    let mut facts := #[toString seconds, toString nanos, toString rows, toString cols]
    for key in formats do
      let format := "%" ++ key
      let bytes ← LeanSudo.Sys.TimeFormat.format format tm
      let value := if bytes.size < 256 then Prim.CoreFacts.decodeLossy bytes else ""
      facts := facts.push (if value.isEmpty then format else value)
    return facts

private def start (path legacy json : String) (flags : UInt32)
    (patterns : Array String) : IO Unit := do
  let constants ← Prim.IoLog.constants
  current.modify fun s => { s with
    compressed := flags &&& 32 != 0
    flush := flags &&& 64 != 0
    ignoreErrors := flags &&& 128 != 0
    passwords := flags &&& 256 != 0 }
  if (← current.get).compressed then loadCompression
  compilePatterns patterns
  let d ← directory path
  try
    for (name, text) in [("log", legacy), ("log.json", json)] do
      let fd ← logFile d name
      try
        writeAll fd ((text.splitOn (String.singleton (Char.ofNat 0))).head!).toUTF8
      catch e =>
        discard (Prim.IoLog.close fd)
        throw e
      Prim.IoLog.close fd
    let names := #["stdin", "stdout", "stderr", "ttyin", "ttyout", "timing"]
    for i in [:6] do
      if i == 5 || flags &&& (1 <<< i.toUInt32) != 0 then
        let fd ← logFile d names[i]!
        current.modify fun s => { s with files := s.files.set! i (some (fd, 0)) }
        if (← current.get).compressed then
          let gz ← Prim.IoLog.gzdopen (← compression.get).openFn fd "wb"
          if gz == 0 then failure "I/O log session files: Input/output error"
          current.modify fun s => { s with files := s.files.set! i (some (fd, gz)) }
    let (sec, ns) ← Prim.IoLog.clock constants.monotonic
    current.modify fun s => { s with active := true, last := sec * 1000000000 + ns }
  finally discard (Prim.IoLog.close d)

def «open» (p : LeanSudo.IoLog.Plan) (m : LeanSudo.IoLog.Metadata)
    (locale : String) : IO (Option String) := do
  try
    let keys := (LeanSudo.IoLog.timeKeys p.dir.toList ++
      LeanSudo.IoLog.timeKeys p.file.toList).eraseDups
    let facts ← clock keys.toArray locale
    let seconds := (facts[0]!).toNat!
    let nanos := (facts[1]!).toNat!
    let time := keys.zipIdx.map fun (key, n) => (key, facts[n + 4]!)
    let rows := (facts[2]!).toNat!
    let cols := (facts[3]!).toNat!
    let m := { m with rows := if rows == 0 then m.rows else rows
                      cols := if cols == 0 then m.cols else cols }
    let dir := LeanSudo.IoLog.expandPath m "" time p.dir
    let seq ← prepare dir p.user p.group p.mode.toUInt32 p.maxseq.toUInt32
    let file := LeanSudo.IoLog.expandPath m (LeanSudo.IoLog.sequencePath seq) time p.file
    let path := if file.startsWith "/" then file else dir ++ "/" ++ file
    let streams := [p.stdin, p.stdout, p.stderr, p.ttyin, p.ttyout,
      p.compress, p.flush, p.ignoreErrors, p.logPasswords]
    let flags := (streams.zipIdx.foldl
      (fun (n : Nat) (b, i) => if b then n + 2 ^ i else n) 0).toUInt32
    start path (LeanSudo.IoLog.legacyLog m seconds) (LeanSudo.IoLog.jsonLog m seconds nanos)
      flags p.passpromptRegex
    return some path
  catch e =>
    abort
    if !p.ignoreErrors then throw e
    return none

private def put (stream : Nat) (bytes : ByteArray) : IO Unit := do
  let constants ← Prim.IoLog.constants
  let s ← current.get
  let some (fd, gz) := s.files[stream]! | failure "I/O log write: Bad file descriptor"
  if s.compressed then
    let z ← compression.get
    if bytes.size > constants.intMax.toNat then failure "I/O log write: Input/output error"
    unless (← Prim.IoLog.gzwrite z.writeFn gz bytes).toNat == bytes.size do
      failure "I/O log write: Input/output error"
    if s.flush && (← Prim.IoLog.gzflush z.flushFn gz constants.syncFlush) != 0 then
      failure "I/O log flush: Input/output error"
  else writeAll fd bytes

private def timing (event : Nat) (detail : String) : IO Unit := do
  let constants ← Prim.IoLog.constants
  let (sec, ns) ← Prim.IoLog.clock constants.monotonic
  let now := sec * 1000000000 + ns
  let elapsed := now - (← current.get).last
  let line := LeanSudo.IoLog.timingRecord event (elapsed / 1000000000) (elapsed % 1000000000) detail
  if line.utf8ByteSize ≥ 160 then failure "I/O log timing: Value too large for defined data type"
  put 5 line.toUTF8
  current.modify fun s => { s with last := now }

private def localFailure (action : IO Unit) : IO Unit := do
  try action catch e =>
    let ignoreErrors := (← current.get).ignoreErrors
    abort
    unless ignoreErrors do throw e

def active : IO Bool := do
  return (← current.get).active || (← LeanSudo.Sys.LogSrv.active)

def streamEnabled (index : UInt32) : IO Bool := do
  if ← LeanSudo.Sys.LogSrv.streamEnabled index then return true
  let s ← current.get
  return s.active && index < 5 && (s.files[index.toNat]!).isSome

def stream (index : UInt32) (bytes : ByteArray) : IO Unit := do
  unless (← active) && index < 5 do return
  let s ← current.get
  if !s.passwords && index == 4 then
    let terminated := bytes.push 0
    let mut filtered := false
    for pattern in s.patterns do
      if (← Prim.IoLog.regexMatch pattern terminated 0) == 0 then
        filtered := true
        break
    current.modify fun s => { s with filtered }
  unless (← streamEnabled index) && !bytes.isEmpty do return
  let mut bytes := bytes
  if !s.passwords && index == 3 && (← current.get).filtered then
    for i in [:bytes.size] do
      if bytes[i]! == 10 || bytes[i]! == 13 then
        current.modify fun s => { s with filtered := false }
        break
      bytes := bytes.set! i 42
  if ← LeanSudo.Sys.LogSrv.streamEnabled index then
    LeanSudo.Sys.LogSrv.ioEvent index bytes 0 0
  else localFailure do
    put index.toNat bytes
    timing index.toNat (toString bytes.size)

def window (rows cols : UInt32) : IO Unit := do
  if ← LeanSudo.Sys.LogSrv.active then
    LeanSudo.Sys.LogSrv.ioEvent 5 ByteArray.empty rows cols
  else if (← current.get).active then
    localFailure (timing 5 s!"{rows} {cols}")

def suspend (signal : UInt32) : IO Unit := do
  unless ← active do return
  let constants ← Prim.IoLog.constants
  let name := if signal == constants.sigCont then "CONT"
    else if signal == constants.sigTstp then "TSTP"
    else if signal == constants.sigTtin then "TTIN"
    else if signal == constants.sigTtou then "TTOU" else "STOP"
  if ← LeanSudo.Sys.LogSrv.active then
    LeanSudo.Sys.LogSrv.ioEvent 7 name.toUTF8 0 0
  else localFailure (timing 7 name)

def close (_exitCode _signalNumber : UInt32) : IO Unit := do
  let s ← current.get
  unless s.active do return
  let constants ← Prim.IoLog.constants
  let mut failed := false
  if let some (fd, _) := s.files[5]! then
    try Prim.IoLog.chmod fd (s.mode &&& (~~~constants.writePermissions))
    catch _ => failed := true
  let z ← compression.get
  for file in s.files do
    if let some (fd, gz) := file then
      if gz != 0 then
        if (← Prim.IoLog.gzclose z.closeFn gz) != 0 then failed := true
      else
        try Prim.IoLog.close fd catch _ => failed := true
  current.modify fun s => { s with files := Array.replicate 6 none }
  abort
  if failed && !s.ignoreErrors then failure "I/O log close: Input/output error"

def relayHooks : LeanSudo.Sys.RelayHooks where
  onStream := fun index bytes => do stream index bytes; return true
  needsStream := streamEnabled
  forcePty := active
  onWindow := window
  onSuspend := suspend
  onTick := LeanSudo.Sys.LogSrv.poll
  onFinish := fun _ => close 0 0

end LeanSudo.Sys.IoLog
