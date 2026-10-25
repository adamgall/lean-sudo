import LeanSudo.Timestamp
import LeanSudo.Background
import LeanSudo.Sys.Prim.Timestamp
import LeanSudo.Sys.Prim.Exec
import Std.Sync.Mutex

namespace LeanSudo.Sys

structure TimestampConfig where
  directory : String := "/run/sudo/ts"
  uid : Nat
  ownerUid : Nat := 0
  ownerGid : Nat := 0
  deriving Inhabited

structure TimestampKey where
  scope : Timestamp.Scope
  lockScope : Timestamp.Scope
  sid : Nat
  authUid : Nat
  deriving Inhabited

private initialize platformCache : IO.Ref (Option Prim.Timestamp.Constants) ← IO.mkRef none

private def getPlatform : IO Prim.Timestamp.Constants := do
  if let some platform ← platformCache.get then return platform
  let platform ← Prim.Timestamp.constants
  platformCache.set (some platform)
  return platform

private def hasError (result : Prim.Timestamp.Result α) (code : UInt64) : Bool :=
  match result with
  | .error error => error.toUInt64 == code
  | .ok _ => false

private partial def retry (action : IO (Prim.Timestamp.Result α)) :
    IO (Prim.Timestamp.Result α) := do
  let platform ← getPlatform
  match ← action with
  | .error error =>
    if error.toUInt64 == platform.interrupted then retry action else return .error error
  | .ok value => return .ok value

private def failure (what : String) (error : UInt32) : IO α := do
  throw (IO.userError s!"{what}: {← Prim.Timestamp.errorText error}")

private def finish (what : String) (result : Prim.Timestamp.Result α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => failure what error

private abbrev Fs := ExceptT UInt32 IO

private def call (action : IO (Prim.Timestamp.Result α)) : Fs α :=
  ExceptT.mk (retry action)

private def discardClose (fd : UInt32) : IO Unit := do
  let _ ← Prim.Timestamp.close fd

private def realTime : IO (Prim.Timestamp.Result Prim.Timestamp.Time) := do
  let platform ← getPlatform
  match ← retry (Prim.Timestamp.clock platform.realtime.toUInt32) with
  | .ok time => return .ok time
  | .error _ =>
    return (← retry Prim.Timestamp.timeofday).map fun time =>
      { time with fraction := time.fraction * 1000 }

private initialize useRealTime : IO.Ref Bool ← IO.mkRef false
private initialize lockMutex : Std.Mutex Unit ← Std.Mutex.new ()

def bootTimeNanos : IO Nat := do
  let platform ← getPlatform
  if (← Prim.Timestamp.monotonic) == platform.sysconfError then useRealTime.set true
  let result ← if ← useRealTime.get then pure (.error 0)
    else retry (Prim.Timestamp.clock platform.boottime.toUInt32)
  let time ← match result with
    | .ok time => pure time
    | .error _ => do
      useRealTime.set true
      finish "timestamp clock" (← realTime)
  let sec := time.seconds.toNat
  let ns := time.fraction.toNat
  if sec > platform.timeMax.toNat || ns >= 1000000000 ||
      sec * 1000000000 + ns >= UInt64.size then
    failure "timestamp clock" platform.overflow.toUInt32
  return sec * 1000000000 + ns

private def clockTicks : IO Nat := do
  let platform ← getPlatform
  match ← Prim.Timestamp.ticks with
  | .ok n =>
    if n == 0 || n > platform.longMax then
      failure "sysconf(_SC_CLK_TCK)" platform.invalid.toUInt32
    else return n.toNat
  | .error e =>
    failure "sysconf(_SC_CLK_TCK)" (if e == 0 then platform.invalid.toUInt32 else e)

def getsid : IO Nat := return (← finish "getsid" (← Prim.Timestamp.getsid)).toNat
def getppid : IO Nat := do
  if let some (_, parent) ← Background.invokingProcess then return parent
  return (← Prim.Timestamp.getppid).toNat

private def readProcStat (pid : String) : IO (Option (List UInt8)) := do
  try
    return some (← IO.FS.readBinFile s!"/proc/{pid}/stat").data.toList
  catch _ => return none

def processStartTime (pid : Nat) : IO (Option Nat) := do
  let some bs ← readProcStat (toString pid) | return none
  let some ticks := Timestamp.statField bs 22 | return none
  let frequency ← clockTicks
  if frequency == 0 then throw (IO.userError "invalid clock tick frequency")
  return some (ticks / frequency * 1000000000 + ticks % frequency * 1000000000 / frequency)

def ttyDevice : IO (Option Nat) := do
  let some bs ← readProcStat "self" | return none
  match Timestamp.statField bs 7 with
  | some n => return if n == 0 then none else some (Timestamp.ttyNrToDev n)
  | none => return none

private def components (path : String) : List String :=
  (path.splitOn "/").filter (· != "")

private def safeComponent (platform : Prim.Timestamp.Constants) (name : String) : Bool :=
  name != "." && name != ".." && name.utf8ByteSize <= platform.nameMax.toNat

private def validPath (platform : Prim.Timestamp.Constants)
    (directory name : String) (uid gid : UInt32) : Bool :=
  uid.toUInt64 != platform.uidInvalid && gid.toUInt64 != platform.gidInvalid &&
  directory.startsWith "/" && directory.utf8ByteSize < platform.pathMax.toNat &&
  !directory.contains '\x00' && !name.isEmpty && !name.contains '\x00' &&
  !name.contains '/' && safeComponent platform name &&
    (components directory).all (safeComponent platform)

private def directorySafe (p : Prim.Timestamp.Constants)
    (mode uid gid ownerUid ownerGid : Nat) : Prop :=
  mode &&& p.typeMask.toNat = p.directory.toNat ∧ uid = ownerUid ∧
    mode &&& p.otherWrite.toNat = 0 ∧ (mode &&& p.groupWrite.toNat = 0 ∨ gid = ownerGid)

private instance (p : Prim.Timestamp.Constants) (mode uid gid ownerUid ownerGid : Nat) :
    Decidable (directorySafe p mode uid gid ownerUid ownerGid) :=
  inferInstanceAs (Decidable (mode &&& p.typeMask.toNat = p.directory.toNat ∧
    uid = ownerUid ∧ mode &&& p.otherWrite.toNat = 0 ∧
      (mode &&& p.groupWrite.toNat = 0 ∨ gid = ownerGid)))

theorem timestamp_directory_rejects_world_write
    (p : Prim.Timestamp.Constants) (mode uid gid ownerUid ownerGid : Nat)
    (writable : mode &&& p.otherWrite.toNat ≠ 0) :
    ¬ directorySafe p mode uid gid ownerUid ownerGid := by
  intro safe
  exact writable safe.2.2.1

private def checkDirectory (fd uid gid : UInt32) : Fs UInt32 := do
  let platform ← getPlatform
  try
    let st ← call (Prim.Timestamp.stat fd)
    if st.mode &&& platform.typeMask != platform.directory then
      throw platform.notDirectory.toUInt32
    if !decide (directorySafe platform
        st.mode.toNat st.uid.toNat st.gid.toNat uid.toNat gid.toNat) then
      throw platform.denied.toUInt32
    return fd
  catch error =>
    discardClose fd
    throw error

private def rootFlags (platform : Prim.Timestamp.Constants) : UInt32 :=
  (platform.openReadOnly ||| platform.openDirectory ||| platform.openCloexec).toUInt32

private def directoryFlags (platform : Prim.Timestamp.Constants) : UInt32 :=
  rootFlags platform ||| platform.openNonblock.toUInt32
private def cwdFd (platform : Prim.Timestamp.Constants) : UInt32 :=
  platform.currentDirectory.toUInt32

private def timestampDirectory (path : String) (uid gid : UInt32) (create : Bool) :
    Fs UInt32 := do
  let platform ← getPlatform
  let cwdFd := cwdFd platform
  let rootFlags := rootFlags platform
  let directoryFlags := directoryFlags platform
  match ← liftM (retry (Prim.Timestamp.openAt cwdFd path directoryFlags 0)) with
  | .ok fd => checkDirectory fd uid gid
  | .error error =>
    if !create || error.toUInt64 != platform.noEntry then throw error
    let current ← IO.mkRef (← call (Prim.Timestamp.openAt cwdFd "/" rootFlags 0))
    try
      let names := (components path).toArray
      for i in [:names.size] do
        let dir ← current.get
        let name := names[i]!
        let final := i + 1 == names.size
        let mut created := false
        let fd ← match ← liftM (retry (Prim.Timestamp.openAt dir name directoryFlags 0)) with
          | .ok fd => pure fd
          | .error error => do
            if error.toUInt64 != platform.noEntry then throw error
            match ← liftM (retry
                (Prim.Timestamp.mkdirAt dir name platform.privateDir.toUInt32)) with
            | .ok _ => created := true
            | .error error => if error.toUInt64 != platform.alreadyExists then throw error
            let nofollow := if created && !final then platform.openNofollow.toUInt32 else 0
            call (Prim.Timestamp.openAt dir name (directoryFlags ||| nofollow) 0)
        discardClose dir
        current.set fd
        let dir := fd
        let st ← call (Prim.Timestamp.stat dir)
        if st.mode &&& platform.typeMask != platform.directory then
          throw platform.notDirectory.toUInt32
        if created || final then
          call (Prim.Timestamp.chown dir uid gid)
          if created then call (Prim.Timestamp.chmod dir
            (if final then platform.privateDir else platform.traverseDir).toUInt32)
    catch error =>
      discardClose (← current.get)
      throw error
    checkDirectory (← current.get) uid gid

private def ownerOpen (dir : UInt32) (name : String) (uid : UInt32) (create : Bool) :
    Fs UInt32 := do
  let platform ← getPlatform
  let saved ← Prim.Timestamp.geteuid
  if saved != uid then call (Prim.Timestamp.seteuid uid)
  let flags := platform.openReadWrite ||| platform.openCloexec |||
    (if create then platform.openCreate else 0)
  let opened ← liftM (retry
    (Prim.Timestamp.openAt dir name flags.toUInt32 platform.privateFile.toUInt32))
  if saved != uid then
    match ← liftM (retry (Prim.Timestamp.seteuid saved)) with
    | .ok _ => pure ()
    | .error error =>
      if let .ok fd := opened then discardClose fd
      throw error
  ExceptT.mk (pure opened)

private def bootEpoch : IO (Option Nat) := do
  let platform ← getPlatform
  let cwdFd := cwdFd platform
  let opened ← retry (Prim.Timestamp.openAt cwdFd "/proc/stat"
    (platform.openReadOnly ||| platform.openCloexec).toUInt32 0)
  let .ok fd := opened | return none
  try
    let mut offset := 0
    let mut line := ByteArray.empty
    let mut overlong := false
    repeat
      let .ok bytes ← retry (Prim.Timestamp.pread fd offset 4096) | return none
      if bytes.isEmpty then return none
      offset := offset + bytes.size.toUInt64
      for byte in bytes do
        if byte == 10 then
          if !overlong then
            let text := String.fromUTF8! line
            if text.startsWith "btime " then
              let digits := text.drop 6 |>.toString
              if !digits.isEmpty && digits.toList.all (fun c => '0' ≤ c && c ≤ '9') then
                if let some value := digits.toNat? then
                  if value > 0 && value <= platform.timeMax.toNat then return some value
          line := ByteArray.empty
          overlong := false
        else if line.size < 254 then line := line.push byte
        else overlong := true
    return none
  finally discardClose fd

private def predatesBoot (st : Prim.Timestamp.Stat) : IO Bool := do
  let platform ← getPlatform
  let .ok now ← realTime | return false
  let some boot ← bootEpoch | return false
  if now.seconds > platform.timeMax || now.seconds.toNat < boot then return false
  if now.seconds.toNat == boot && now.fraction > platform.longMax then return false
  return st.mtime > platform.timeMax || st.mtime.toNat < boot

private def tsOpen (directory name : String) (uid gid : UInt32) (create : Bool) :
    IO (Option UInt32) := do
  let platform ← getPlatform
  if !validPath platform directory name uid gid then
    failure "timestamp path or owner" platform.invalid.toUInt32
  let opened ← (timestampDirectory directory uid gid create).run
  if !create && hasError opened platform.noEntry then return none
  let dir ← finish "timestamp directory" opened
  let action : Fs UInt32 := do
    let fd ← ownerOpen dir name uid create
    let current ← IO.mkRef fd
    try
      let st ← call (Prim.Timestamp.stat fd)
      if ← predatesBoot st then
        discardClose fd
        current.set (UInt32.size - 1).toUInt32
        match ← liftM (retry (Prim.Timestamp.unlinkAt dir name)) with
        | .error error => if error.toUInt64 != platform.noEntry then throw error
        | .ok _ => pure ()
        let reopened ← ownerOpen dir name uid create
        current.set reopened
        let _ ← call (Prim.Timestamp.stat reopened)
      return ← current.get
    catch error =>
      let fd ← current.get
      if fd != (UInt32.size - 1).toUInt32 then discardClose fd
      throw error
  let result ← try action.run finally discardClose dir
  if !create && hasError result platform.noEntry then return none
  return some (← finish "timestamp open" result)

private def validFd (what : String) (fd : UInt32) : IO Unit := do
  let platform ← getPlatform
  if fd.toUInt64 > platform.fdMax then failure what platform.badFd.toUInt32 else pure ()

private def validExtent (what : String) (offset length : Nat) : IO Unit := do
  let platform ← getPlatform
  if offset + length > platform.offsetMax.toNat then
    failure what platform.overflow.toUInt32 else pure ()

private def tsSize (fd : UInt32) : IO UInt64 := do
  validFd "timestamp size" fd
  let st ← finish "timestamp size" (← retry (Prim.Timestamp.stat fd))
  validExtent "timestamp size" st.size.toNat 0
  return st.size

private def tsReadAt (fd : UInt32) (offset : UInt64) (length : UInt32) : IO ByteArray := do
  validFd "timestamp read" fd
  validExtent "timestamp read" offset.toNat length.toNat
  let mut bytes := ByteArray.empty
  while bytes.size < length.toNat do
    let part ← finish "timestamp read" (← retry
      (Prim.Timestamp.pread fd (offset + bytes.size.toUInt64) (length - bytes.size.toUInt32)))
    if part.isEmpty then break
    bytes := bytes ++ part
  return bytes

private def tsWriteAt (fd : UInt32) (offset : UInt64) (bytes : ByteArray) : IO Unit := do
  let platform ← getPlatform
  validFd "timestamp pwrite" fd
  validExtent "timestamp pwrite" offset.toNat bytes.size
  let mut total := 0
  while total < bytes.size do
    let count := min (bytes.size - total) platform.ssizeMax.toNat
    let n ← finish "timestamp pwrite" (← retry
      (Prim.Timestamp.pwrite fd (offset + total.toUInt64) bytes total.toUInt64 count.toUInt64))
    if n == 0 then failure "timestamp pwrite" platform.ioError.toUInt32
    total := total + n.toNat

private def tsTruncate (fd : UInt32) (length : UInt64) : IO Unit := do
  validFd "timestamp truncate" fd
  validExtent "timestamp truncate" length.toNat 0
  finish "timestamp truncate" (← retry (Prim.Timestamp.truncate fd length))

private def interrupted : IO α := do
  let platform ← getPlatform
  throw (.interrupted "timestamp lock" platform.interrupted.toUInt32
    (← Prim.Timestamp.errorText platform.interrupted.toUInt32))

private def drainInterrupts (signals : UInt32) : IO Bool := do
  let mut caught := false
  repeat
    match ← Prim.Exec.readSignal signals with
    | none => return caught
    | some _ => caught := true
  return caught

private def tsLock (fd : UInt32) (offset length : UInt64) (lock : Bool) : IO Unit := do
  let platform ← getPlatform
  validFd "timestamp lock" fd
  validExtent "timestamp lock" offset.toNat length.toNat
  if !lock then
    return ← finish "timestamp lock"
      (← retry (Prim.Timestamp.lock fd offset length platform.unlock.toUInt32))
  lockMutex.mutex.lock
  let action : IO Unit := do
    let mask := (1 : UInt64) <<< (platform.sigInt - 1) |||
      (1 : UInt64) <<< (platform.sigQuit - 1)
    let signals ← Prim.Exec.signalFd mask
    let attempt : IO Unit := do
      repeat
        if ← drainInterrupts signals then interrupted
        let result ← Prim.Timestamp.waitLock fd offset length platform.writeLock.toUInt32
          platform.sigInt.toUInt32 platform.sigQuit.toUInt32
        if result.status == 0 then
          try
            if result.signal != 0 || (← drainInterrupts signals) then interrupted
            if result.error != 0 then failure "timestamp lock" result.error
          catch error =>
            let _ ← retry (Prim.Timestamp.lock fd offset length platform.unlock.toUInt32)
            throw error
          return
        if result.signal != 0 then
          let _ ← drainInterrupts signals
          interrupted
        if result.error.toUInt64 != platform.interrupted then
          failure "timestamp lock" result.error
    try attempt finally discardClose signals
  try action finally lockMutex.mutex.unlock

private def tsClose (fd : UInt32) : IO Unit := do
  let platform ← getPlatform
  validFd "timestamp close" fd
  match ← Prim.Timestamp.close fd with
  | .error error =>
    if error.toUInt64 != platform.interrupted then failure "timestamp close" error
  | .ok _ => pure ()

private def tsRemove (directory name : String) (uid gid : UInt32) : IO Unit := do
  let platform ← getPlatform
  if !validPath platform directory name uid gid then
    failure "timestamp path or owner" platform.invalid.toUInt32
  let opened ← (timestampDirectory directory uid gid false).run
  if hasError opened platform.noEntry then return
  let dir ← finish "timestamp directory" opened
  let result ← try retry (Prim.Timestamp.unlinkAt dir name) finally discardClose dir
  if hasError result platform.noEntry then return
  finish "timestamp remove" result

private def uidToUInt32 (uid : Nat) : IO UInt32 := do
  let platform ← getPlatform
  if uid < min (UInt32.size - 1) platform.uidInvalid.toNat then return uid.toUInt32
  else throw (IO.userError s!"timestamp: uid {uid} out of range")

private def markerDirectory (dir : UInt32) (name display : String) (create : Bool) :
    IO (Option UInt32) := do
  let platform ← getPlatform
  let rootFlags := rootFlags platform
  let mut created := false
  if create then
    match ← Prim.Timestamp.mkdirAt dir name platform.privateDir.toUInt32 with
    | .ok _ => created := true
    | .error error => if error.toUInt64 != platform.alreadyExists then failure display error
  let opened ← Prim.Timestamp.openAt dir name (rootFlags ||| platform.openNofollow.toUInt32) 0
  match opened with
  | .error error =>
    if !create && error.toUInt64 == platform.noEntry then return none
    if error.toUInt64 == platform.symlinkLoop || error.toUInt64 == platform.notDirectory then
      throw (IO.userError s!"{display}: not a directory")
    failure display error
  | .ok fd =>
    try
      let st ← finish display (← Prim.Timestamp.stat fd)
      if st.mode &&& platform.typeMask != platform.directory then
        throw (IO.userError s!"{display}: not a directory")
      if st.uid != 0 then throw (IO.userError s!"{display} is owned by uid {st.uid}, should be 0")
      if created then finish display (← Prim.Timestamp.chmod fd platform.privateDir.toUInt32)
      else if st.mode &&& (platform.groupWrite ||| platform.otherWrite) != 0 then
        throw (IO.userError s!"{display} is group or world writable")
      return some fd
    catch error =>
      discardClose fd
      throw error

def stateMarker (dir : String) (uid : Nat) (create : Bool) : IO Bool := do
  let platform ← getPlatform
  let cwdFd := cwdFd platform
  let rootFlags := rootFlags platform
  let uid ← uidToUInt32 uid
  if !dir.startsWith "/" || dir.contains '\x00' then
    throw (IO.userError "invalid state directory")
  let current ← IO.mkRef (← finish "/" (← Prim.Timestamp.openAt cwdFd "/" rootFlags 0))
  try
    for name in components dir do
      let fd ← current.get
      if name == "." || name == ".." then
        throw (IO.userError "invalid state directory component")
      let some next ← markerDirectory fd name dir create | return false
      discardClose fd
      current.set next
    let flags := platform.openReadOnly ||| platform.openNofollow ||| platform.openCloexec |||
      platform.openNonblock ||| (if create then platform.openCreate else 0)
    let opened ← Prim.Timestamp.openAt (← current.get) (toString uid)
      flags.toUInt32 platform.privateFile.toUInt32
    discardClose (← current.get)
    current.set (UInt32.size - 1).toUInt32
    if !create && hasError opened platform.noEntry then return false
    let marker ← finish "state marker" opened
    let st ← try Prim.Timestamp.stat marker finally discardClose marker
    let .ok st := st | throw (IO.userError "unsafe state marker")
    if st.mode &&& platform.typeMask != platform.regular || st.uid != 0 ||
        st.mode &&& (platform.groupWrite ||| platform.otherWrite) != 0 then
      throw (IO.userError "unsafe state marker")
    return true
  finally
    let fd ← current.get
    if fd != (UInt32.size - 1).toUInt32 then discardClose fd

private def openTimestamp (config : TimestampConfig) (create : Bool) : IO (Option UInt32) := do
  let _ ← uidToUInt32 config.uid
  tsOpen config.directory (toString config.uid)
    (← uidToUInt32 config.ownerUid) (← uidToUInt32 config.ownerGid) create

private def lockRecord (fd : UInt32) (offset : Nat) (lock : Bool) : IO Unit := do
  if offset >= UInt64.size then throw (IO.userError "timestamp offset out of range")
  tsLock fd offset.toUInt64 Timestamp.recordSize.toUInt64 lock

private def writeEntry (fd : UInt32) (offset : Nat) (entry : Timestamp.DiskEntry) : IO Unit := do
  if !decide entry.Representable then throw (IO.userError "timestamp record is out of range")
  if offset >= UInt64.size then throw (IO.userError "timestamp offset out of range")
  tsWriteAt fd offset.toUInt64 (Timestamp.encodeEntry entry)

private def headerWord (bytes : ByteArray) (offset : Nat) : Nat :=
  (bytes[offset]?.getD 0).toNat + 256 * (bytes[offset + 1]?.getD 0).toNat

private def initializeHeader (fd : UInt32) (extent : Nat) : IO Nat := do
  let bytes ← tsReadAt fd 0 Timestamp.recordSize.toUInt32
  let size := headerWord bytes 2
  let kind := headerWord bytes 4
  if bytes.size >= 40 && kind == 4 && size >= 8 && size <= extent then return extent
  if bytes.size >= 40 && size == 40 then
    let header := ByteArray.mk #[bytes[0]!, bytes[1]!, 40, 0, 4, 0] ++
      ByteArray.mk (Array.replicate 34 0)
    tsWriteAt fd 0 header
    return extent
  tsTruncate fd 0
  tsWriteAt fd 0 (Timestamp.encodeEntry Timestamp.lockEntry)
  return Timestamp.recordSize

private structure Ticket where
  fd : UInt32
  offset : Nat
  key : TimestampKey
  global : Bool

private def scanFile (fd : UInt32) (extent : Nat) (initial : α)
    (step : α → Timestamp.LocatedEntry → IO (ForInStep α)) : IO α := do
  let mut state := initial
  let mut offset := 0
  for _ in [:extent / 4] do
    let bytes ← tsReadAt fd offset.toUInt64 Timestamp.recordSize.toUInt32
    match Timestamp.scanStep bytes offset extent with
    | .stop => break
    | .next next located =>
      offset := next
      if let some located := located then
        match ← step state located with
        | .done result => return result
        | .yield result => state := result
  return state

private def initialEntry (key : TimestampKey) (scope : Timestamp.Scope) : Timestamp.DiskEntry :=
  Timestamp.entryFor key.lockScope key.sid
    { scope, authUid := key.authUid, time := 0, disabled := true }

private def findEntry (fd : UInt32) (extent : Nat) (scope : Timestamp.Scope) (authUid : Nat) :
    IO (Option Timestamp.LocatedEntry) :=
  scanFile fd extent none fun _ located =>
    pure (if located.matches scope authUid then .done (some located) else .yield none)

private def openTicket (config : TimestampConfig) (key : TimestampKey) : IO Ticket := do
  if key.lockScope == .global then throw (IO.userError "timestamp lock scope must be terminal or process")
  let some fd ← openTimestamp config true | throw (IO.userError "unable to open timestamp file")
  try
    lockRecord fd 0 true
    let (offset, lockOffset) ← try
      let mut extent ← initializeHeader fd (← tsSize fd).toNat
      let lockOffset ← match ← findEntry fd extent key.lockScope key.authUid with
        | some located => pure located.offset
        | none => do
          let offset := extent
          writeEntry fd offset (initialEntry key key.lockScope)
          extent := extent + Timestamp.recordSize
          pure offset
      let offset ← if key.scope == .global then
          match ← findEntry fd extent key.scope key.authUid with
          | some located => pure located.offset
          | none => do
            writeEntry fd extent (initialEntry key key.scope)
            pure extent
        else pure lockOffset
      pure (offset, lockOffset)
    finally
      lockRecord fd 0 false
    lockRecord fd lockOffset true
    return { fd, offset, key, global := key.scope == .global }
  catch e =>
    tsClose fd
    throw e

private def readTicket (ticket : Ticket) : IO (List Timestamp.Record) := do
  if ticket.global then lockRecord ticket.fd ticket.offset true
  try
    let bytes ← tsReadAt ticket.fd ticket.offset.toUInt64 Timestamp.recordSize.toUInt32
    let some located := Timestamp.decodeSlot bytes ticket.offset | return []
    return (located.recordFor ticket.key.scope ticket.key.authUid ticket.key.sid).toList
  finally
    if ticket.global then lockRecord ticket.fd ticket.offset false

private def updateTicket (ticket : Ticket) (record : Timestamp.Record) : IO Unit := do
  let some entry := Timestamp.updateEntry ticket.key.scope ticket.key.lockScope
      ticket.key.sid ticket.key.authUid record |
    throw (IO.userError "timestamp update does not match locked record")
  if ticket.global then lockRecord ticket.fd ticket.offset true
  try writeEntry ticket.fd ticket.offset entry
  finally
    if ticket.global then lockRecord ticket.fd ticket.offset false

def readTimestamp (config : TimestampConfig) (key : TimestampKey) : IO (List Timestamp.Record) := do
  let some fd ← openTimestamp config false | return []
  try
    let extent := (← tsSize fd).toNat
    let header ← tsReadAt fd 0 8
    if headerWord header 4 != 4 then return []
    let some located ← findEntry fd extent key.scope key.authUid | return []
    return (located.recordFor key.scope key.authUid key.sid).toList
  finally tsClose fd

private def reportCacheError (report : String → IO Unit) (error : IO.Error) : IO Unit :=
  match error with
  | .interrupted _ _ _ => pure ()
  | _ => report error.toString

def withTimestampFile (config : TimestampConfig) (key : TimestampKey)
    (f : List Timestamp.Record → IO (Option Timestamp.Record × α))
    (report : String → IO Unit := fun _ => pure ()) : IO α := do
  let opened : Except IO.Error Ticket ←
    try pure (.ok (← openTicket config key)) catch e => pure (.error e)
  match opened with
  | .error e =>
    reportCacheError report e
    return (← f []).2
  | .ok ticket =>
    try
      let records ← try readTicket ticket catch e => reportCacheError report e; pure []
      let (record, result) ← f records
      if let some record := record then
        try updateTicket ticket record catch e => reportCacheError report e
      return result
    finally tsClose ticket.fd

def invalidateTimestamp (config : TimestampConfig) (scope : Timestamp.Scope) : IO Unit := do
  let some fd ← openTimestamp config false | return
  try
    lockRecord fd 0 true
    let extent := (← tsSize fd).toNat
    scanFile fd extent () fun _ located => do
      if located.matches scope 0 true then
        let entry := Timestamp.disabledEntry located.entry
        tsWriteAt fd (located.offset + 6).toUInt64
          (ByteArray.mk (Timestamp.encNat 2 entry.flags).toArray)
      pure (.yield ())
  finally tsClose fd

def removeTimestampFile (config : TimestampConfig) : IO Unit := do
  let _ ← uidToUInt32 config.uid
  tsRemove config.directory (toString config.uid)
    (← uidToUInt32 config.ownerUid) (← uidToUInt32 config.ownerGid)

end LeanSudo.Sys
