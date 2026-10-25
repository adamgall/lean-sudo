import LeanSudo.Sys.Core
import LeanSudo.Helper
import LeanSudo.Sys.Prim.Exec
import LeanSudo.Sys.Prim.Posix
import LeanSudo.Sys.Prim.Extra
import LeanSudo.Sys.Prim.Visudo

namespace LeanSudo.Visudo

namespace P
export LeanSudo.Sys.Prim.Posix
  (S_IRWXU S_IRWXG S_IRWXO S_ISUID S_ISGID S_ISVTX O_NONBLOCK O_NOCTTY O_CLOEXEC
    S_IRUSR S_IRGRP S_IWUSR S_IFMT S_IFREG SIGHUP SIGINT SIGQUIT SIGTERM
    EINTR O_RDWR ENOENT O_CREAT EAGAIN EACCES EIO O_WRONLY O_TRUNC STDERR_FILENO
    INT_MAX O_RDONLY O_NOFOLLOW)
end P

private def permissionBits (_ : Unit) : UInt32 := P.S_IRWXU () ||| P.S_IRWXG () ||| P.S_IRWXO ()

private def modeBits (_ : Unit) : UInt32 :=
  permissionBits () ||| P.S_ISUID () ||| P.S_ISGID () ||| P.S_ISVTX ()

private def openFlags (_ : Unit) : UInt32 := P.O_NONBLOCK () ||| P.O_NOCTTY () ||| P.O_CLOEXEC ()

private def defaultMode (_ : String) : UInt32 := P.S_IRUSR () ||| P.S_IRGRP ()

inductive LockResult where
  | locked
  | busy
  | missing
  deriving Repr, BEq, Inhabited

private structure Metadata where
  dev : Nat
  ino : Nat
  mode : Nat
  uid : Nat
  gid : Nat
  size : Nat
  sec : Nat
  nsec : Nat
  deriving Inhabited

@[extern "leansudo_visudo_errno"] private opaque errorText (error : UInt32) : IO String
@[extern "leansudo_visudo_open"] private opaque openRaw (path : @& String)
    (flags mode : UInt32) : IO (UInt32 × USize)
@[extern "leansudo_visudo_close"] private opaque closeRaw (fd : UInt32) : IO UInt32
@[extern "leansudo_visudo_stat"]
private opaque statRaw (path : @& String) : IO (Except UInt32 Metadata)
@[extern "leansudo_visudo_fstat"]
private opaque fstatRaw (fd : UInt32) : IO (Except UInt32 Metadata)
@[extern "leansudo_visudo_ofd_lock"] private opaque lockRaw (fd : UInt32) : IO UInt32
@[extern "leansudo_visudo_write"] private opaque writeRaw (fd : UInt32)
    (bytes : @& String) (offset : USize) : IO (UInt32 × USize)
@[extern "leansudo_visudo_sync"] private opaque syncRaw (fd : UInt32) : IO UInt32
@[extern "leansudo_visudo_unlink"] private opaque unlinkRaw (path : @& String) : IO UInt32
@[extern "leansudo_visudo_futimens"] private opaque timeRaw (fd : UInt32)
    (sec nsec : UInt64) : IO UInt32
@[extern "leansudo_visudo_chown"] private opaque chownRaw (fd uid gid : UInt32) : IO UInt32
@[extern "leansudo_visudo_chmod"] private opaque chmodRaw (fd mode : UInt32) : IO UInt32
@[extern "leansudo_visudo_exit"] private opaque exitRaw (status : UInt32) : IO Unit
@[extern "leansudo_visudo_open_max"] private opaque openMax : IO UInt64
@[extern "leansudo_visudo_raise"] private opaque raiseRaw (signo : UInt32) : IO UInt32
@[extern "leansudo_visudo_wait_exited"] private opaque waitExited (status : UInt32) : Bool
@[extern "leansudo_visudo_no_uid"] private opaque noUid : Unit → UInt32
@[extern "leansudo_visudo_no_gid"] private opaque noGid : Unit → UInt32

private def validPath (path : String) : IO Unit :=
  if path.contains '\x00' then throw (IO.userError "invalid path") else pure ()

private def failPath (what path : String) (error : UInt32) : IO α := do
  let context := if what.isEmpty then path else what ++ " " ++ path
  throw (IO.userError s!"{context}: {← errorText error}")

private def checkResult (what path : String) (error : UInt32) : IO Unit := do
  if error != 0 then failPath what path error

private def fileStat (path : String) : IO Metadata := do
  validPath path
  match ← statRaw path with
  | .ok st => return st
  | .error error => failPath "unable to stat" path error

private def descriptorStat (fd : UInt32) (path : String) : IO Metadata := do
  match ← fstatRaw fd with
  | .ok st => return st
  | .error error => failPath "unable to stat" path error

private def closeQuietly (fd : UInt32) : IO Unit := do
  let _ ← closeRaw fd

private def unlinkQuietly (path : String) : IO Unit := do
  let _ ← unlinkRaw path

private structure LockedFile where
  path : String
  fd : UInt32
  dev : Nat
  ino : Nat

private structure CleanupTask where
  task : Task (Except IO.Error Unit)
  wake : UInt32

private initialize lockedFiles : IO.Ref (Array LockedFile) ← IO.mkRef #[]
private initialize temporaryFiles : IO.Ref (Array String) ← IO.mkRef #[]
private initialize cleanupTask : IO.Ref (Option CleanupTask) ← IO.mkRef none

private def sameFile (file : LockedFile) (st : Metadata) : Bool :=
  file.dev == st.dev && file.ino == st.ino

private def regularFile (st : Metadata) : Bool :=
  st.mode &&& (P.S_IFMT ()).toNat == (P.S_IFREG ()).toNat

private def cleanupSignal (signo : UInt32) : IO Unit := do
  let files ← temporaryFiles.get
  for index in [:files.size] do unlinkQuietly files[files.size - 1 - index]!
  try
    let description ← LeanSudo.Sys.Prim.Extra.signalDescription signo
    (← IO.getStderr).putStr s!"visudo exiting due to signal: {description}\n"
    (← IO.getStderr).flush
  catch _ => pure ()
  exitRaw signo

private def dispatchSignal (signo : UInt32) : IO Unit := do
  if [P.SIGHUP (), P.SIGINT (), P.SIGQUIT (), P.SIGTERM ()].contains signo &&
      !(← temporaryFiles.get).isEmpty then
    cleanupSignal signo
  else
    let error ← raiseRaw signo
    if error != 0 then throw (IO.userError (← errorText error))
    let bit := (1 : UInt64) <<< (signo.toUInt64 - 1)
    LeanSudo.Sys.Prim.Exec.signalMask (~~~bit)
    LeanSudo.Sys.Prim.Exec.signalMask (~~~(0 : UInt64))

private partial def consumeSignals (fd : UInt32) (fds : Array (UInt32 × UInt32)) : IO Unit := do
  let (error, ready) ← LeanSudo.Sys.Prim.Exec.poll fds (~~~(0 : UInt32))
  if error == P.EINTR () then return ← consumeSignals fd fds
  if error != 0 then throw (IO.userError (← errorText error))
  if ready[1]! != 0 then return
  match ← LeanSudo.Sys.Prim.Exec.readSignal fd with
  | some signal => dispatchSignal signal.signo
  | none => pure ()
  consumeSignals fd fds

def initializeSignals : IO Unit := do
  if (← cleanupTask.get).isSome then return
  let mask ← LeanSudo.Sys.Prim.Exec.startupMask
  let fd ← LeanSudo.Sys.Prim.Exec.signalFd (~~~mask)
  let (reader, writer) ← try LeanSudo.Sys.Prim.Exec.pipe (P.O_CLOEXEC ())
    catch error =>
      closeQuietly fd
      throw error
  let pollIn := LeanSudo.Sys.Prim.Exec.K.POLLIN ()
  let fds := #[(fd, pollIn), (reader, pollIn)]
  let task ← IO.asTask (prio := .dedicated) do
    try consumeSignals fd fds
    finally
      closeQuietly reader
      closeQuietly fd
  cleanupTask.set (some { task, wake := writer })

def shutdownSignals : IO Unit := do
  let some running ← cleanupTask.get | return
  cleanupTask.set none
  closeQuietly running.wake
  match running.task.get with
  | .ok () => pure ()
  | .error error => throw error

private def trackTemp (path : String) : IO Unit := do
  initializeSignals
  temporaryFiles.modify fun files => if files.contains path then files else files.push path

def lockFile (path : String) (mode : UInt32 := defaultMode path) : IO LockResult := do
  validPath path
  let files ← lockedFiles.get
  if files.any (·.path == path) then return .locked
  let flags := P.O_RDWR () ||| openFlags ()
  let (error, opened) ← openRaw path flags 0
  let created := error == P.ENOENT ()
  let (error, opened) ←
    if created then openRaw path (flags ||| P.O_CREAT ()) mode else pure (error, opened)
  checkResult "" path error
  let fd := opened.toNat.toUInt32
  let st ← match ← fstatRaw fd with
    | .ok st => pure st
    | .error _ =>
      closeQuietly fd
      throw (IO.userError s!"{path} is not a regular file")
  unless regularFile st do
    closeQuietly fd
    throw (IO.userError s!"{path} is not a regular file")
  if files.any (sameFile · st) then
    closeQuietly fd
    return .locked
  let error ← lockRaw fd
  if error != 0 then
    closeQuietly fd
    if error == P.EAGAIN () || error == P.EACCES () then return .busy
    failPath "unable to lock" path error
  lockedFiles.set (files.push { path, fd, dev := st.dev, ino := st.ino })
  return if created then .missing else .locked

private partial def writeAll (fd : UInt32) (path : String) (bytes : String)
    (offset : Nat := 0) : IO Unit := do
  if offset >= bytes.utf8ByteSize then return
  let (error, count) ← writeRaw fd bytes offset.toUSize
  if error == P.EINTR () then return ← writeAll fd path bytes offset
  checkResult "unable to write to" path error
  if count == 0 then failPath "unable to write to" path (P.EIO ())
  writeAll fd path bytes (offset + count.toNat)

def createTemp (original path content : String) : IO Unit := do
  validPath original
  validPath path
  trackTemp path
  let flags := P.O_WRONLY () ||| P.O_CREAT () ||| P.O_TRUNC () ||| P.O_NOCTTY () ||| P.O_CLOEXEC ()
  let (error, opened) ← openRaw path flags (P.S_IRUSR () ||| P.S_IWUSR ())
  checkResult "" path error
  let fd := opened.toNat.toUInt32
  try
    writeAll fd path content
    checkResult "unable to write to" path (← syncRaw fd)
    let st ← fileStat original
    checkResult "unable to set time on" path (← timeRaw fd st.sec.toUInt64 st.nsec.toUInt64)
  catch error =>
    closeQuietly fd
    unlinkQuietly path
    throw error
  let error ← closeRaw fd
  if error != 0 then
    unlinkQuietly path
    failPath "unable to write to" path error

def fileModified (original temp : String) : IO Bool := do
  validPath original
  validPath temp
  let a ← fileStat original
  let b ← fileStat temp
  return a.size != b.size || a.sec != b.sec || a.nsec != b.nsec

private def exportPath : IO String := do
  if let some path ← IO.getEnv "PATH" then return path
  let (error, length, path) ← LeanSudo.Sys.Prim.Visudo.defaultPath
  checkResult "unable to execute" "cvtsudoers" error
  if length.toNat != path.utf8ByteSize + 1 then
    failPath "unable to execute" "cvtsudoers" (P.EIO ())
  return path

private def executeExport (search : String) (args env : Array String) : IO UInt32 := do
  let mut denied := false
  let mut error := P.ENOENT ()
  let mut cwd : Option String := none
  for directory in search.splitOn ":" do
    if !directory.startsWith "/" && cwd.isNone then
      cwd := some (← LeanSudo.Sys.getcwd)
    let directory := if directory.startsWith "/" then directory
      else if directory.isEmpty then cwd.getD "" else cwd.getD "" ++ "/" ++ directory
    let path := directory ++ "/cvtsudoers"
    error ← LeanSudo.Sys.Prim.Exec.execve path args env
    if error == LeanSudo.Sys.Prim.Exec.K.ENOEXEC () then
      error ← LeanSudo.Sys.Prim.Exec.execve "/bin/sh"
        (#["/bin/sh", path] ++ args.extract 1 args.size) env
    if error == P.EACCES () then
      denied := true
    else if error != P.ENOENT () &&
        error != LeanSudo.Sys.Prim.Visudo.ENOTDIR () &&
        error != LeanSudo.Sys.Prim.Visudo.ESTALE () &&
        error != LeanSudo.Sys.Prim.Visudo.ENODEV () &&
        error != LeanSudo.Sys.Prim.Posix.ETIMEDOUT () then
      return error
  return if denied then P.EACCES () else error

def exportSudoers (input output : String) : IO Unit := do
  validPath input
  validPath output
  let search ← exportPath
  let args := #["cvtsudoers", "-f", "json", "-o", output, "--", input]
  let env := (← LeanSudo.Sys.environ).toArray.map fun (key, value) => key ++ "=" ++ value
  let error ← try
    LeanSudo.Sys.Prim.Exec.signalMask (← LeanSudo.Sys.Prim.Exec.startupMask)
    executeExport search args env
  finally LeanSudo.Sys.Prim.Exec.signalMask (~~~(0 : UInt64))
  checkResult "unable to execute" "cvtsudoers" error

private def editorHelper (payload : Lean.Json) : IO UInt32 := do
  let (path, args, env) ←
    match (Lean.fromJson? payload : Except String (String × Array String × Array String)) with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  if path.contains '\x00' then throw (IO.userError "invalid editor")
  if args.any (·.contains '\x00') then throw (IO.userError "invalid editor argument")
  if env.any (·.contains '\x00') then throw (IO.userError "invalid editor environment")
  let mask ← LeanSudo.Helper.inheritedMask
  let first := P.STDERR_FILENO () + 1
  if (← LeanSudo.Sys.Prim.Exec.closeRange first (~~~(0 : UInt32)) 0) != 0 then
    let maximum ← openMax
    if maximum > (P.INT_MAX ()).toUInt64 then return 127
    for fd in [first.toNat:maximum.toNat] do closeQuietly fd.toUInt32
  LeanSudo.Sys.Prim.Exec.signalMask mask
  let error ← LeanSudo.Sys.Prim.Exec.execve path args env
  try
    (← IO.getStderr).putStr s!"visudo: unable to run {path}: {← errorText error}\n"
    (← IO.getStderr).flush
  catch _ => pure ()
  return 127

def registerHelpers : IO Unit :=
  LeanSudo.Helper.register "visudo.editor" editorHelper

private partial def waitEditor (pid : UInt32) : IO Bool := do
  let (result, status) ← LeanSudo.Sys.Prim.Exec.waitpid pid 0
  if result == -(P.EINTR ()).toUInt64.toInt64 then return ← waitEditor pid
  return result > 0 && waitExited status

def runEditor (path : String) (args : Array String) : IO Bool := do
  if path.contains '\x00' then throw (IO.userError "invalid editor")
  if args.any (·.contains '\x00') then throw (IO.userError "invalid editor argument")
  let env := (← LeanSudo.Sys.environ).toArray.map fun (key, value) => key ++ "=" ++ value
  let pid ← try
      LeanSudo.Helper.spawn "visudo.editor" (Lean.toJson (path, args, env))
    catch error => throw (IO.userError s!"unable to execute {path}: {error}")
  waitEditor pid

private def setOwnerModeRaw (path : String) (uid gid mode : UInt32) : IO Unit := do
  validPath path
  if uid == noUid () || gid == noGid () || mode > modeBits () then
    throw (IO.userError "invalid owner or mode")
  let flags := P.O_RDONLY () ||| P.O_NOFOLLOW () ||| openFlags ()
  let (error, opened) ← openRaw path flags 0
  checkResult "unable to open" path error
  let fd := opened.toNat.toUInt32
  try
    let st ← descriptorStat fd path
    unless regularFile st do throw (IO.userError s!"{path} is not a regular file")
    checkResult "unable to set (uid, gid) of" path (← chownRaw fd uid gid)
    checkResult "unable to change mode of" path (← chmodRaw fd mode)
    checkResult "unable to sync" path (← syncRaw fd)
  finally closeQuietly fd

def setOwnerMode (path : String) (uid gid mode : Nat) : IO Unit :=
  if uid < (noUid ()).toNat && gid < (noGid ()).toNat && mode ≤ (modeBits ()).toNat then
    setOwnerModeRaw path uid.toUInt32 gid.toUInt32 mode.toUInt32
  else throw (IO.userError s!"invalid owner {uid}:{gid} or mode {mode}")

def correctLockedMetadata (path : String) (uid gid mode : UInt32)
    (owner perms : Bool) : IO Unit := do
  validPath path
  if uid == noUid () || gid == noGid () || mode > modeBits () then
    throw (IO.userError "invalid owner or mode")
  let files ← lockedFiles.get
  let file ← match files.find? (·.path == path) with
    | some file => pure (some file)
    | none =>
      let st ← fileStat path
      pure (files.find? (sameFile · st))
  let some file := file | throw (IO.userError "sudoers file is not locked")
  let st ← descriptorStat file.fd path
  if owner && (st.uid != uid.toNat || st.gid != gid.toNat) then
    checkResult "unable to set (uid, gid) of" path (← chownRaw file.fd uid gid)
  if perms && st.mode &&& (permissionBits ()).toNat != mode.toNat then
    checkResult "unable to change mode of" path (← chmodRaw file.fd mode)

end LeanSudo.Visudo
