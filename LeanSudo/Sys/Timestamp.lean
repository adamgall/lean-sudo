import LeanSudo.Timestamp
import LeanSudo.Background
import LeanSudo.Sys.Prim.Timestamp
import LeanSudo.Sys.Prim.Exec
import LeanSudo.Sys.FrontSignals
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

private def octal (n : Nat) : String := String.ofList (Nat.toDigits 8 n)

private def pathPrefixes (path : String) : List (String × String) := Id.run do
  let mut out := #[]
  let mut seen := ""
  let mut name := ""
  for c in path.toList do
    if c == '/' then
      if !name.isEmpty then out := out.push (name, seen)
      name := ""
    else name := name.push c
    seen := seen.push c
  if !name.isEmpty then out := out.push (name, seen)
  return out.toList

private def insecureDirectory (path : String) (st : Prim.Timestamp.Stat) (uid gid : UInt32) :
    IO (Option (UInt32 × String)) := do
  let p ← getPlatform
  if decide (directorySafe p st.mode.toNat st.uid.toNat st.gid.toNat uid.toNat gid.toNat) then
    return none
  if st.mode &&& p.typeMask != p.directory then
    return some (p.notDirectory.toUInt32,
      s!"{path}: {← Prim.Timestamp.errorText p.notDirectory.toUInt32}")
  if st.uid != uid.toUInt64 then
    return some (p.denied.toUInt32, s!"{path} is owned by uid {st.uid}, should be {uid}")
  if st.mode &&& p.otherWrite != 0 then
    return some (p.denied.toUInt32, s!"{path} is world writable")
  return some (p.denied.toUInt32, s!"{path} is owned by gid {st.gid}, should be {gid}")

private def searchFlags (p : Prim.Timestamp.Constants) : UInt32 :=
  (p.openReadOnly ||| p.openNonblock ||| p.openCloexec).toUInt32

private def cwdFd (platform : Prim.Timestamp.Constants) : UInt32 :=
  platform.currentDirectory.toUInt32

private def rootFlags (platform : Prim.Timestamp.Constants) : UInt32 :=
  (platform.openReadOnly ||| platform.openDirectory ||| platform.openCloexec).toUInt32

private abbrev DirResult := Except (UInt32 × List String) UInt32

private structure DirLog where
  lastError : IO.Ref UInt32
  messages : IO.Ref (List String)

private def DirLog.fail (log : DirLog) (error : UInt32) (message : String) : Fs α := do
  log.lastError.set error
  log.messages.modify (· ++ [s!"{message}: {← Prim.Timestamp.errorText error}"])
  throw error

private def DirLog.note (log : DirLog) (action : IO (Prim.Timestamp.Result Unit)) : IO Unit := do
  if let .error error ← action then log.lastError.set error

private def attempt (action : IO (Prim.Timestamp.Result α)) : Fs (Prim.Timestamp.Result α) :=
  liftM (retry action)

private def requireDirectory (log : DirLog) (fd : UInt32) (pathPrefix : String) : Fs Unit := do
  let p ← getPlatform
  let checked : Fs Unit := do
    match ← attempt (Prim.Timestamp.stat fd) with
    | .error error => log.fail error s!"unable to stat {pathPrefix}"
    | .ok st =>
      if st.mode &&& p.typeMask != p.directory then
        log.messages.modify (· ++
          [s!"{pathPrefix} exists but is not a directory (0{octal st.mode.toNat})"])
        throw (← log.lastError.get)
  tryCatch checked fun error => do
    discardClose fd
    throw error

private def openComponent (log : DirLog) (uid gid dir : UInt32) (name pathPrefix : String) :
    Fs UInt32 := do
  let p ← getPlatform
  let flags := searchFlags p
  let reopen : Fs UInt32 := do
    match ← attempt (Prim.Timestamp.openAt dir name flags 0) with
    | .error error => log.fail error s!"unable to open {pathPrefix}"
    | .ok fd =>
      requireDirectory log fd pathPrefix
      pure fd
  match ← attempt (Prim.Timestamp.openAt dir name flags 0) with
  | .ok fd =>
    requireDirectory log fd pathPrefix
    pure fd
  | .error error =>
    log.lastError.set error
    if error.toUInt64 != p.noEntry then log.fail error s!"unable to open {pathPrefix}"
    match ← attempt (Prim.Timestamp.mkdirAt dir name p.traverseDir.toUInt32) with
    | .error error =>
      if error.toUInt64 != p.alreadyExists then log.fail error s!"unable to mkdir {pathPrefix}"
      else
        log.lastError.set error
        reopen
    | .ok () =>
      match ← attempt (Prim.Timestamp.openAt dir name (flags ||| p.openNofollow.toUInt32) 0) with
      | .error error => log.fail error s!"unable to open {pathPrefix}"
      | .ok fd =>
        requireDirectory log fd pathPrefix
        log.note (Prim.Timestamp.chown fd uid gid)
        log.note (Prim.Timestamp.chmod fd p.traverseDir.toUInt32)
        pure fd

private def openParent (log : DirLog) (path : String) (uid gid : UInt32) : Fs UInt32 := do
  let p ← getPlatform
  let root ← match ← attempt (Prim.Timestamp.openAt (cwdFd p) "/" (searchFlags p) 0) with
    | .ok fd => pure fd
    | .error error => log.fail error "unable to open /"
  let parent ← IO.mkRef root
  tryFinally (do
    for (name, pathPrefix) in (pathPrefixes path).dropLast do
      let dir ← parent.get
      let next ← openComponent log uid gid dir name pathPrefix
      discardClose dir
      parent.set next
    let fd ← parent.get
    parent.set (UInt32.size - 1).toUInt32
    pure fd) (do
    let fd ← parent.get
    if fd != (UInt32.size - 1).toUInt32 then discardClose fd)

private def makeDirectory (log : DirLog) (path : String) (uid gid : UInt32) : Fs UInt32 := do
  let p ← getPlatform
  let some (base, _) := (pathPrefixes path).getLast? | throw (← log.lastError.get)
  let parent ← openParent log path uid gid
  tryFinally (do
    let made ← attempt (Prim.Timestamp.mkdirAt parent base p.privateDir.toUInt32)
    if let .error error := made then
      if error.toUInt64 != p.alreadyExists then log.fail error s!"unable to mkdir {path}"
      log.lastError.set error
    match ← attempt (Prim.Timestamp.openAt parent base (searchFlags p) 0) with
    | .error error =>
      log.lastError.set error
      throw error
    | .ok fd =>
      log.note (Prim.Timestamp.chown fd uid gid)
      if made matches .ok () then log.note (Prim.Timestamp.chmod fd p.privateDir.toUInt32)
      pure fd) (discardClose parent)

structure TimestampNotice where
  message : String
  errstr : Option String := none
  alert : Bool := false

def TimestampNotice.text (notice : TimestampNotice) : String :=
  match notice.errstr with
  | some errstr => s!"{notice.message}: {errstr}"
  | none => notice.message

def TimestampNotice.logReason (notice : TimestampNotice) : String :=
  match notice.errstr with
  | some errstr => s!"{notice.message} : {errstr}"
  | none => notice.message

private abbrev Notices := IO.Ref (Array TimestampNotice)

private def raise (sink : Notices) (notices : List TimestampNotice) : IO α := do
  sink.modify (· ++ notices.toArray)
  throw (IO.userError ("\n".intercalate (notices.map (·.text))))

private def secureOpenDir (path : String) (uid gid : UInt32) (create : Bool) : IO DirResult := do
  let p ← getPlatform
  let missing (error : UInt32) : IO DirResult := do
    if !create then return .error (error, [s!"{path}: {← Prim.Timestamp.errorText error}"])
    let log : DirLog := { lastError := ← IO.mkRef error, messages := ← IO.mkRef [] }
    match ← (makeDirectory log path uid gid).run with
    | .ok fd => return .ok fd
    | .error _ =>
      let error ← log.lastError.get
      return .error (error,
        (← log.messages.get) ++ [s!"{path}: {← Prim.Timestamp.errorText error}"])
  match ← retry (Prim.Timestamp.openAt (cwdFd p) path (searchFlags p) 0) with
  | .error error => missing error
  | .ok fd =>
    match ← retry (Prim.Timestamp.stat fd) with
    | .error error => discardClose fd; missing error
    | .ok st =>
      if let some (error, message) ← insecureDirectory path st uid gid then
        discardClose fd
        return .error (error, [message])
      return .ok fd

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

private def tsOpen (sink : Notices) (directory name : String) (uid gid : UInt32) (create : Bool) :
    IO (Option UInt32) := do
  let platform ← getPlatform
  if !validPath platform directory name uid gid then
    failure "timestamp path or owner" platform.invalid.toUInt32
  let directoryResult ← secureOpenDir directory uid gid create
  if let .error (error, messages) := directoryResult then
    if !create && error.toUInt64 == platform.noEntry then return none
    raise sink (messages.map fun message => { message })
  let .ok dir := directoryResult | return none
  let reopenIfStale (first : Except UInt32 UInt32) : IO (Except UInt32 UInt32) := do
    let .ok fd := first | return first
    let .ok st ← retry (Prim.Timestamp.stat fd) | return first
    if !(← predatesBoot st) then return first
    discardClose fd
    let _ ← retry (Prim.Timestamp.unlinkAt dir name)
    (ownerOpen dir name uid create).run
  let opened ← tryFinally (do reopenIfStale (← (ownerOpen dir name uid create).run))
    (discardClose dir)
  match opened with
  | .ok fd => return some fd
  | .error error =>
    if !create && error.toUInt64 == platform.noEntry then return none
    let errstr := some (← Prim.Timestamp.errorText error)
    raise sink [{ message := s!"unable to open {directory}/{name}", errstr, alert := true }]

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
    FrontSignals.collect
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
  let dir ← match ← secureOpenDir directory uid gid false with
    | .ok dir => pure dir
    | .error (error, messages) =>
      if error.toUInt64 == platform.noEntry then pure (UInt32.size - 1).toUInt32
      else throw (IO.userError ("\n".intercalate messages))
  if dir == (UInt32.size - 1).toUInt32 then return
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

private def openTimestamp (sink : Notices) (config : TimestampConfig) (create : Bool) :
    IO (Option UInt32) := do
  let _ ← uidToUInt32 config.uid
  tsOpen sink config.directory (toString config.uid)
    (← uidToUInt32 config.ownerUid) (← uidToUInt32 config.ownerGid) create

private def lockRecord (fd : UInt32) (offset : Nat) (lock : Bool) : IO Unit := do
  if offset >= UInt64.size then throw (IO.userError "timestamp offset out of range")
  tsLock fd offset.toUInt64 Timestamp.recordSize.toUInt64 lock

private def writeBytes (sink : Notices) (fd : UInt32) (fname : String) (offset : Nat)
    (bytes : ByteArray) : IO Unit := do
  let failed (errstr : Option String) : IO Unit :=
    raise sink [{ message := s!"unable to write to {fname}", errstr, alert := true }]
  if offset + bytes.size >= UInt64.size then failed none
  match ← retry (Prim.Timestamp.pwrite fd offset.toUInt64 bytes 0 bytes.size.toUInt64) with
  | .error error => failed (some (← Prim.Timestamp.errorText error))
  | .ok n =>
    if n.toNat != bytes.size then
      if n != 0 then
        let _ ← retry (Prim.Timestamp.truncate fd offset.toUInt64)
      failed none

private def writeEntry (sink : Notices) (fd : UInt32) (fname : String) (offset : Nat)
    (entry : Timestamp.DiskEntry) : IO Unit := do
  if !decide entry.Representable then throw (IO.userError "timestamp record is out of range")
  writeBytes sink fd fname offset (Timestamp.encodeEntry entry)

private def headerWord (bytes : ByteArray) (offset : Nat) : Nat :=
  (bytes[offset]?.getD 0).toNat + 256 * (bytes[offset + 1]?.getD 0).toNat

private structure TsFile where
  size : IO Nat
  readAt : Nat → Nat → IO ByteArray
  writeAt : Nat → ByteArray → IO Unit
  truncate : IO Unit

private def readOrEmpty (fd : UInt32) (offset length : Nat) : IO ByteArray := do
  if length == 0 || offset + length >= UInt64.size then return ByteArray.empty
  try tsReadAt fd offset.toUInt64 length.toUInt32 catch _ => pure ByteArray.empty

private def realFile (sink : Notices) (fd : UInt32) (fname : String) : TsFile where
  size := do return (← tsSize fd).toNat
  readAt := readOrEmpty fd
  writeAt := writeBytes sink fd fname
  truncate := do
    match ← retry (Prim.Timestamp.truncate fd 0) with
    | .ok () => pure ()
    | .error error =>
      let errstr := some (← Prim.Timestamp.errorText error)
      raise sink [{ message := "unable to truncate time stamp file to 0 bytes", errstr }]

private def overlayFile (fd : UInt32) : IO TsFile := do
  let base ← try pure (← tsSize fd).toNat catch _ => pure 0
  let state ← IO.mkRef (base, ([] : List (Nat × ByteArray)))
  let total : IO Nat := do
    let (baseSize, writes) ← state.get
    return writes.foldl (fun m (offset, bytes) => max m (offset + bytes.size)) baseSize
  return {
    size := total
    readAt := fun offset length => do
      let (baseSize, writes) ← state.get
      let size ← total
      if offset >= size then return ByteArray.empty
      let n := min length (size - offset)
      let original ← if offset < baseSize then readOrEmpty fd offset (min n (baseSize - offset))
        else pure ByteArray.empty
      return ByteArray.mk ((List.range n).map fun i =>
        match writes.find? (fun (o, b) => o ≤ offset + i && offset + i < o + b.size) with
        | some (o, b) => b[offset + i - o]!
        | none => original[i]?.getD 0).toArray
    writeAt := fun offset bytes => state.modify fun (b, ws) => (b, (offset, bytes) :: ws)
    truncate := state.set (0, []) }

private def findRecord (file : TsFile) (start : Nat) (accept : Timestamp.LocatedEntry → Bool) :
    IO (Option Timestamp.LocatedEntry × Nat) := do
  let mut pos := start
  for _ in [:(← file.size) + 2] do
    let bytes ← file.readAt pos Timestamp.recordSize
    if bytes.size != Timestamp.recordSize then return (none, pos + bytes.size)
    pos := pos + Timestamp.recordSize
    let size := headerWord bytes 2
    if size != Timestamp.recordSize then
      pos := pos + size - Timestamp.recordSize
      if size == 0 then return (none, pos)
      continue
    if let some located := Timestamp.decodeSlot bytes (pos - Timestamp.recordSize) then
      if accept located then return (some located, pos)
  return (none, pos)

private structure Ticket where
  sink : Notices
  fd : UInt32
  fname : String
  offset : Nat
  key : TimestampKey
  global : Bool

private def initialEntry (key : TimestampKey) (scope : Timestamp.Scope) : Timestamp.DiskEntry :=
  Timestamp.entryFor key.lockScope key.sid
    { scope, authUid := key.authUid, time := 0, disabled := true }

namespace TimestampStorage

def selectEntry (scope : Timestamp.Scope) (authUid : Nat) (located : Timestamp.LocatedEntry) :
    ForInStep (Option Timestamp.LocatedEntry) :=
  if located.matches scope authUid then .done (some located) else .yield none

def recordsFor (key : TimestampKey) (located : Timestamp.LocatedEntry) :
    List Timestamp.Record :=
  (located.recordFor key.scope key.authUid key.sid).toList

def updateFor (key : TimestampKey) (record : Timestamp.Record) :
    Option Timestamp.DiskEntry :=
  Timestamp.updateEntry key.scope key.lockScope key.sid key.authUid record

theorem selectEntry_model (scope : Timestamp.Scope) (authUid : Nat)
    (located : Timestamp.LocatedEntry) :
    selectEntry scope authUid located = .done (some located) ↔
      located.matches scope authUid = true := by
  simp [selectEntry]

theorem selectEntry_uid (scope : Timestamp.Scope) (authUid : Nat)
    (located : Timestamp.LocatedEntry)
    (h : selectEntry scope authUid located = .done (some located)) :
    located.entry.authUid = authUid :=
  Timestamp.LocatedEntry.matches_uid ((selectEntry_model scope authUid located).mp h)

theorem recordsFor_model (key : TimestampKey) (located : Timestamp.LocatedEntry)
    (record : Timestamp.Record) :
    record ∈ recordsFor key located ↔
      located.recordFor key.scope key.authUid key.sid = some record := by
  simp [recordsFor]

theorem lookup_model (key : TimestampKey) (located : Timestamp.LocatedEntry)
    (now : Nat) (timeout : Option Nat) :
    Timestamp.lookup now timeout key.scope key.authUid (recordsFor key located) = true ↔
      ∃ record, located.recordFor key.scope key.authUid key.sid = some record ∧
        Timestamp.valid now timeout key.scope key.authUid record = true := by
  simp only [Timestamp.lookup_iff, recordsFor_model]

theorem authorized_sound (key : TimestampKey) (located : Timestamp.LocatedEntry)
    (now : Nat) (timeout : Option Nat)
    (h : Timestamp.lookup now timeout key.scope key.authUid (recordsFor key located) = true) :
    ∃ record, located.recordFor key.scope key.authUid key.sid = some record ∧
      located.entry.authUid = key.authUid ∧ located.matches key.scope key.authUid = true ∧
      located.startValid = true ∧ located.timeValid = true ∧
      (located.entry.kind = 1 ∨ located.entry.sid = key.sid) ∧
      record.scope = key.scope ∧ record.authUid = key.authUid ∧
      record.disabled = false ∧ record.time ≤ now ∧
      ∀ t, timeout = some t → t ≠ 0 ∧ now - record.time < t * 10 ^ 9 := by
  obtain ⟨record, hr, hv⟩ := (lookup_model key located now timeout).mp h
  exact ⟨record, hr, Timestamp.LocatedEntry.authorized_sound hr hv⟩

theorem recordsFor_invalid_start (key : TimestampKey) (located : Timestamp.LocatedEntry)
    (h : located.startValid = false) : recordsFor key located = [] := by
  simp [recordsFor, located.recordFor_invalid_start key.scope key.authUid key.sid h]

theorem recordsFor_invalid_time (key : TimestampKey) (located : Timestamp.LocatedEntry)
    (h : located.timeValid = false) : recordsFor key located = [] := by
  simp [recordsFor, located.recordFor_invalid_time key.scope key.authUid key.sid h]

theorem recordsFor_wrong_session (key : TimestampKey) (located : Timestamp.LocatedEntry)
    (hg : located.entry.kind ≠ 1) (hs : located.entry.sid ≠ key.sid) :
    recordsFor key located = [] := by
  simp [recordsFor, located.recordFor_wrong_sid key.scope key.authUid key.sid hg hs]


theorem updateFor_sound (key : TimestampKey) (record : Timestamp.Record)
    (entry : Timestamp.DiskEntry) (h : updateFor key record = some entry) :
    record.scope = key.scope ∧ record.authUid = key.authUid ∧
      entry.toRecord = some record ∧ entry.matches key.scope key.authUid = true :=
  Timestamp.updateEntry_sound h

theorem updateFor_wrong_uid (key : TimestampKey) (record : Timestamp.Record)
    (h : record.authUid ≠ key.authUid) : updateFor key record = none :=
  Timestamp.updateEntry_wrong_uid key.scope key.lockScope key.sid key.authUid record h

theorem updateFor_wrong_scope (key : TimestampKey) (record : Timestamp.Record)
    (h : record.scope ≠ key.scope) : updateFor key record = none :=
  Timestamp.updateEntry_wrong_scope key.scope key.lockScope key.sid key.authUid record h

theorem initialEntry_model (key : TimestampKey) (scope : Timestamp.Scope) :
    (initialEntry key scope).toRecord =
      some { scope, authUid := key.authUid, time := 0, disabled := true } :=
  Timestamp.entryFor_projection key.lockScope key.sid _

theorem initialEntry_denied (key : TimestampKey) (scope : Timestamp.Scope)
    (now : Nat) (timeout : Option Nat) (record : Timestamp.Record)
    (h : (initialEntry key scope).toRecord = some record) :
    Timestamp.valid now timeout key.scope key.authUid record = false := by
  rw [initialEntry_model] at h
  cases Option.some.inj h
  simp [Timestamp.valid]

theorem invalidated_records_denied (key : TimestampKey) (located : Timestamp.LocatedEntry)
    (now : Nat) (timeout : Option Nat) :
    Timestamp.lookup now timeout key.scope key.authUid
      (recordsFor key { located with entry := Timestamp.disabledEntry located.entry }) =
      false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  obtain ⟨record, hr, hv⟩ := (lookup_model key
    { located with entry := Timestamp.disabledEntry located.entry } now timeout).mp accepted
  have denied := located.disabled_not_valid key.scope key.authUid key.sid now timeout hr
  simp [denied] at hv

end TimestampStorage

private def writeKey (file : TsFile) (offset : Nat) (entry : Timestamp.DiskEntry) : IO Unit := do
  if !decide entry.Representable then throw (IO.userError "timestamp record is out of range")
  file.writeAt offset (Timestamp.encodeEntry entry)

private def lockPlan (file : TsFile) (key : TimestampKey) : IO (Nat × Nat) := do
  let first ← file.readAt 0 Timestamp.recordSize
  let size := headerWord first 2
  let mut pos := first.size
  let mut overwrite : Bool := first.size < 40
  if !overwrite && headerWord first 4 != 4 then
    if size == 40 then
      file.writeAt 0 (ByteArray.mk #[first[0]!, first[1]!, 40, 0, 4, 0] ++
        ByteArray.mk (Array.replicate 34 0))
    else overwrite := true
  if overwrite then
    file.truncate
    file.writeAt pos (Timestamp.encodeEntry Timestamp.lockEntry)
    pos := pos + Timestamp.recordSize
  else if size != Timestamp.recordSize then pos := size
  let (found, next) ← findRecord file pos fun l => l.matches key.lockScope key.authUid
  let lockPos ← match found with
    | some _ => pure (next - Timestamp.recordSize)
    | none => do
      writeKey file next (initialEntry key key.lockScope)
      pure next
  if key.scope != .global then return (lockPos, lockPos)
  let (found, next) ← findRecord file 0 fun l => l.matches .global key.authUid
  if found.isSome then return (lockPos, next - Timestamp.recordSize)
  writeKey file next (initialEntry key .global)
  return (lockPos, next)

private def seekable (fd : UInt32) : IO Bool := do
  match ← retry (Prim.Timestamp.pread fd 0 0) with
  | .ok _ => return true
  | .error _ => return false

private def tryLock (fd : UInt32) (offset : Nat) : IO Bool := do
  try
    lockRecord fd offset true
    return true
  catch e =>
    match e with
    | .interrupted .. => throw e
    | _ => return false

private def unlockQuiet (fd : UInt32) (offset : Nat) : IO Unit := do
  try lockRecord fd offset false catch _ => pure ()

private def openTicket (sink : Notices) (config : TimestampConfig) (key : TimestampKey) :
    IO (Option Ticket) := do
  if key.lockScope == .global then
    throw (IO.userError "timestamp lock scope must be terminal or process")
  let some fd ← openTimestamp sink config true | return none
  let fname := s!"{config.directory}/{config.uid}"
  let attempt : IO (Option Nat) := do
    if !(← seekable fd) then return none
    if !(← tryLock fd 0) then return none
    let (lockPos, offset) ← tryFinally (lockPlan (realFile sink fd fname) key)
      (unlockQuiet fd 0)
    if !(← tryLock fd lockPos) then return none
    return some offset
  let locked ← tryCatch attempt fun e => do
    tsClose fd
    throw e
  match locked with
  | none =>
    tsClose fd
    return none
  | some offset =>
    return some { sink, fd, fname, offset, key, global := key.scope == .global }

private def futureRecord (ticket : Ticket) (timeout : Option Nat)
    (located : Timestamp.LocatedEntry) : IO Bool := do
  let some limit := timeout | return false
  if limit == 0 then return false
  let some record := located.recordFor ticket.key.scope ticket.key.authUid ticket.key.sid |
    return false
  return !record.disabled && record.time > (← bootTimeNanos)

private def readTicket (ticket : Ticket) (timeout : Option Nat) :
    IO (Option (List Timestamp.Record)) := do
  if ticket.global then
    if !(← tryLock ticket.fd ticket.offset) then return none
  tryFinally (do
    let bytes ← readOrEmpty ticket.fd ticket.offset Timestamp.recordSize
    if bytes.size != Timestamp.recordSize then return none
    let some located := Timestamp.decodeSlot bytes ticket.offset | return some []
    if ← futureRecord ticket timeout located then
      let notice : TimestampNotice :=
        { message := "ignoring time stamp from the future", alert := true }
      ticket.sink.modify (·.push notice)
      let disabled := { located with entry := Timestamp.disabledEntry located.entry }
      try
        writeBytes ticket.sink ticket.fd ticket.fname (ticket.offset + 6)
          (ByteArray.mk (Timestamp.encNat 2 disabled.entry.flags).toArray)
      catch _ => pure ()
      return some (TimestampStorage.recordsFor ticket.key disabled)
    return some (TimestampStorage.recordsFor ticket.key located))
    (if ticket.global then unlockQuiet ticket.fd ticket.offset else pure ())

private def updateTicket (ticket : Ticket) (record : Timestamp.Record) : IO Unit := do
  let some entry := TimestampStorage.updateFor ticket.key record |
    throw (IO.userError "timestamp update does not match locked record")
  let locked ← if ticket.global then tryLock ticket.fd ticket.offset else pure false
  tryFinally (writeEntry ticket.sink ticket.fd ticket.fname ticket.offset entry)
    (if locked then unlockQuiet ticket.fd ticket.offset else pure ())

def readTimestamp (config : TimestampConfig) (key : TimestampKey) : IO (List Timestamp.Record) := do
  if key.lockScope == .global then return []
  let some fd ← openTimestamp (← IO.mkRef #[]) config false | return []
  tryFinally (do
    if !(← seekable fd) then return []
    let file ← overlayFile fd
    let (_, offset) ← lockPlan file key
    let bytes ← file.readAt offset Timestamp.recordSize
    if bytes.size != Timestamp.recordSize then return []
    let some located := Timestamp.decodeSlot bytes offset | return []
    return TimestampStorage.recordsFor key located) (tsClose fd)

private def reportNotices (sink : Notices) (report : TimestampNotice → IO Unit)
    (error : Option IO.Error) : IO Unit := do
  let notices ← sink.get
  sink.set #[]
  for notice in notices do report notice
  if let some error := error then
    match error with
    | .interrupted _ _ _ => pure ()
    | _ => if notices.isEmpty then report { message := error.toString }

structure TimestampHooks where
  suspend : IO Unit
  resume : IO Bool

private def closeSlot (slot : IO.Ref (Option Ticket)) : IO Unit := do
  let some ticket ← slot.get | return
  slot.set none
  tsClose ticket.fd

private def ticketHooks (sink : Notices) (report : TimestampNotice → IO Unit)
    (config : TimestampConfig) (key : TimestampKey) (slot : IO.Ref (Option Ticket)) :
    TimestampHooks where
  suspend := try closeSlot slot catch _ => pure ()
  resume := do
    try
      let ticket ← openTicket sink config key
      slot.set ticket
      reportNotices sink report none
      return ticket.isSome
    catch e =>
      reportNotices sink report (some e)
      return false

def withTimestampHooks (config : TimestampConfig) (key : TimestampKey)
    (report : TimestampNotice → IO Unit) (f : TimestampHooks → IO α) : IO α := do
  let slot : IO.Ref (Option Ticket) ← IO.mkRef none
  try f (ticketHooks (← IO.mkRef #[]) report config key slot) finally closeSlot slot

def withTimestampFile (config : TimestampConfig) (key : TimestampKey) (timeout : Option Nat)
    (f : TimestampHooks → List Timestamp.Record → IO (Option Timestamp.Record × α))
    (report : TimestampNotice → IO Unit := fun _ => pure ()) : IO α := do
  let sink ← IO.mkRef #[]
  let slot : IO.Ref (Option Ticket) ← IO.mkRef none
  let hooks := ticketHooks sink report config key slot
  let opened : Except IO.Error (Option Ticket) ←
    try pure (.ok (← openTicket sink config key)) catch e => pure (.error e)
  try
    match opened with
    | .error e =>
      reportNotices sink report (some e)
      return (← f hooks []).2
    | .ok none =>
      reportNotices sink report none
      return (← f hooks []).2
    | .ok (some ticket) =>
      slot.set (some ticket)
      let status ← try readTicket ticket timeout catch e =>
        reportNotices sink report (some e)
        pure none
      reportNotices sink report none
      let (record, result) ← f hooks (status.getD [])
      if status.isSome then
        if let some record := record then
          if let some current ← slot.get then
            try updateTicket current record catch e => reportNotices sink report (some e)
      return result
  finally closeSlot slot

def invalidateTimestamp (config : TimestampConfig) (scope : Timestamp.Scope) : IO Unit := do
  let sink ← IO.mkRef #[]
  let some fd ← openTimestamp sink config false | return
  try
    lockRecord fd 0 true
    let file := realFile sink fd s!"{config.directory}/{config.uid}"
    let mut pos := 0
    for _ in [:(← file.size) / Timestamp.recordSize + 2] do
      let (found, next) ← findRecord file pos fun l => l.matches scope 0 true
      let some located := found | break
      if located.entry.flags % 2 == 0 then
        let entry := Timestamp.disabledEntry located.entry
        file.writeAt (located.offset + 6) (ByteArray.mk (Timestamp.encNat 2 entry.flags).toArray)
      pos := next
  finally tsClose fd

def removeTimestampFile (config : TimestampConfig) : IO Unit := do
  let _ ← uidToUInt32 config.uid
  tsRemove config.directory (toString config.uid)
    (← uidToUInt32 config.ownerUid) (← uidToUInt32 config.ownerGid)

end LeanSudo.Sys
