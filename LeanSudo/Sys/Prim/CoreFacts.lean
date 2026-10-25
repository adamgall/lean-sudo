import LeanSudo.Sys.Prim.Posix

namespace LeanSudo.Sys.Prim.CoreFacts

@[extern "lean_cf_decode_lossy"] opaque decodeLossy (bytes : @& ByteArray) : String
@[extern "lean_cf_strerror"] opaque strerror (error : UInt32) : IO String
@[extern "lean_cf_setuid"] opaque setuid (uid : UInt32) : IO Int
@[extern "lean_cf_shell_begin"] opaque shellBegin : IO Unit
@[extern "lean_cf_shell_end"] opaque shellEnd : IO Unit
@[extern "lean_cf_shell_next"] opaque shellNext : IO (Option ByteArray)
@[extern "lean_cf_groups"] opaque groups (capacity : UInt32) : IO (Int × Array Nat)
@[extern "lean_cf_sysconf"] opaque nssSize (selector : UInt32) : IO Int
abbrev NssResult := Int × Array ByteArray × Array Nat
@[extern "lean_cf_pwnam"] opaque pwnam (name : @& String) (uid size : UInt32) : IO NssResult
@[extern "lean_cf_pwuid"] opaque pwuid (name : @& String) (uid size : UInt32) : IO NssResult
@[extern "lean_cf_grnam"] opaque grnam (name : @& String) (gid size : UInt32) : IO NssResult
@[extern "lean_cf_grgid"] opaque grgid (name : @& String) (gid size : UInt32) : IO NssResult
@[extern "lean_cf_grouplist"]
opaque groupList (name : @& String) (gid capacity : UInt32) : IO (Int × Int × Array Nat)
@[extern "lean_cf_hostname"] opaque hostname : IO (Int × ByteArray)
@[extern "lean_cf_ttyname"] opaque ttyname (fd : UInt32) : IO (Option ByteArray)
@[extern "lean_cf_environment"] opaque environment : IO USize
@[extern "lean_cf_environment_entry"]
opaque environmentEntry (cursor : USize) : IO (Option ByteArray)
@[extern "lean_cf_getenv"] opaque getenv (name : @& String) : IO (Option ByteArray)
@[extern "lean_cf_unsetenv"] opaque unsetenv (name : @& String) : IO Int
@[extern "lean_cf_tzset"] opaque tzset : IO Unit
@[extern "lean_cf_setlocale"] opaque setlocale : IO Unit
@[extern "lean_cf_stat"] opaque stat (path : @& String) : IO (Int × Array Int)
@[extern "lean_cf_lstat"] opaque lstat (path : @& String) : IO (Int × Array Int)
@[extern "lean_cf_fstat"] opaque fstat (fd : UInt32) : IO (Int × Array Int)
@[extern "lean_cf_realpath"] opaque realpath (path : @& String) : IO (Option ByteArray)
@[extern "lean_cf_access"] opaque access (path : @& String) (mode : UInt32) : IO Int
@[extern "lean_cf_open"] opaque openFile (path : @& String) (flags : UInt32) : IO Int
@[extern "lean_cf_close"] opaque close (fd : UInt32) : IO Int
@[extern "lean_cf_dup"] opaque dup (fd : UInt32) : IO Int
@[extern "lean_cf_read"]
opaque read (fd size : UInt32) : IO (Int × ByteArray)
@[extern "lean_cf_fdopendir"] opaque fdopendir (fd : UInt32) : IO (Int × USize)
@[extern "lean_cf_readdir"] opaque readdir (handle : USize) : IO (Int × Option ByteArray)
@[extern "lean_cf_closedir"] opaque closedir (handle : USize) : IO Int
@[extern "lean_cf_getcwd"] opaque getcwd : IO (Int × ByteArray)
@[extern "lean_cf_write"]
opaque write (fd : UInt32) (bytes : @& ByteArray) (offset : USize) : IO Int

private def errnoValue (code : UInt32) : Int := code.toNat

private def readOpenFlags (_ : Unit) : UInt32 :=
  Posix.O_RDONLY () ||| Posix.O_CLOEXEC () ||| Posix.O_NONBLOCK () ||| Posix.O_NOCTTY ()

def failErrno {α : Type} (error : Int) : IO α := do
  throw (IO.userError (← strerror error.natAbs.toUInt32))

def check (result : Int) : IO Unit := do
  if result < 0 then failErrno result

def checkString (s : String) : IO Unit := do
  if s.contains (Char.ofNat 0) then throw (IO.userError "argument contains a NUL byte")

def decode (bytes : ByteArray) (message : String) : IO String :=
  match String.fromUTF8? bytes with
  | some s => pure s
  | none => throw (IO.userError message)

partial def validShells : IO (Array String) := do
  shellBegin
  try
    let mut out := #[]
    repeat
      let some bytes ← shellNext | break
      if let some shell := String.fromUTF8? bytes then out := out.push shell
    return out
  finally shellEnd

def getgroups : IO (List Nat) := do
  for _ in [:8] do
    let (count, _) ← groups 0
    check count
    let (result, values) ← groups (count.toNat + 1).toUInt32
    if result >= 0 then return values.toList
    if result != -(errnoValue (Posix.EINVAL ())) then failErrno result
  failErrno (errnoValue (Posix.EINVAL ()))

def nssNotFound (rc : Int) : Bool :=
  rc == 0 || rc == errnoValue (Posix.ENOENT ()) || rc == errnoValue (Posix.ESRCH ()) ||
    rc == errnoValue (Posix.EBADF ()) || rc == errnoValue (Posix.EPERM ())

partial def lookupLoop (call : UInt32 → IO NssResult) (size : Nat) :
    IO (Option (Array ByteArray × Array Nat)) := do
  let (rc, strings, ids) ← call size.toUInt32
  if rc == errnoValue (Posix.ERANGE ()) && size < 64 * 1024 * 1024 then
    return ← lookupLoop call (size * 2)
  if rc == errnoValue (Posix.EINTR ()) then return ← lookupLoop call size
  if ids.isEmpty then
    if nssNotFound rc then return none
    failErrno rc
  else return some (strings, ids)

def lookup (group : Bool) (call : UInt32 → IO NssResult) :
    IO (Option (Array ByteArray × Array Nat)) := do
  let selector := if group then Posix._SC_GETGR_R_SIZE_MAX () else Posix._SC_GETPW_R_SIZE_MAX ()
  let size ← nssSize selector
  lookupLoop call (if size <= 0 || size > 1024 * 1024 then 4096 else size.toNat)

private partial def groupListLoop (user : String) (gid : UInt32) (capacity : Nat) :
    IO (List Nat) := do
  let (rc, count, groups) ← groupList user gid capacity.toUInt32
  if rc >= 0 then return groups.toList
  if rc == -(errnoValue (Posix.ENOMEM ())) then failErrno rc
  let next := if count > capacity then count.toNat else capacity * 2
  if next > 1024 * 1024 then throw (IO.userError "getgrouplist: too many groups")
  groupListLoop user gid next

def getgrouplist (user : String) (gid : UInt32) : IO (List Nat) := do
  checkString user
  groupListLoop user gid 64

initialize localeState : IO.Ref (Bool × Option ByteArray) ← IO.mkRef (false, none)

def initializeLocale : IO Unit := do
  let (initialized, _) ← localeState.get
  unless initialized do localeState.set (true, ← getenv "TZ")
  check (← unsetenv "TZ")
  tzset
  setlocale

def parseEnvironmentEntry (entry : ByteArray) : Option (String × String) := Id.run do
  for i in [:entry.size] do
    if entry[i]! == 61 then
      return do
        let key ← String.fromUTF8? (entry.extract 0 i)
        let value ← String.fromUTF8? (entry.extract (i + 1) entry.size)
        pure (key, value)
  return none

partial def environ : IO (List (String × String)) := do
  let (initialized, tz) ← localeState.get
  let mut cursor ← environment
  let stride := (Posix.SIZEOF_POINTER ()).toUSize
  let mut out := #[]
  repeat
    let some bytes ← environmentEntry cursor | break
    if let some (key, value) := parseEnvironmentEntry bytes then
      unless initialized && key == "TZ" do out := out.push (key, value)
    cursor := cursor + stride
  if let some bytes := tz then
    if let some value := String.fromUTF8? bytes then out := out.push ("TZ", value)
  return out.toList

def readCap : Nat := 16 * 1024 * 1024

def fileAccepted (mode : Nat) (size : Int) : Bool :=
  (mode &&& (Posix.S_IFMT ()).toNat) == (Posix.S_IFREG ()).toNat &&
    decide (0 <= size) && decide (size <= readCap)

theorem fileAccepted_regular (mode : Nat) (size : Int) (h : fileAccepted mode size = true) :
    mode &&& (Posix.S_IFMT ()).toNat = (Posix.S_IFREG ()).toNat := by
  simp only [fileAccepted, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact h.1.1

theorem fileAccepted_bounded (mode : Nat) (size : Int) (h : fileAccepted mode size = true) :
    0 <= size ∧ size <= readCap := by
  simp only [fileAccepted, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.2, h.2⟩

private def formattedErrorText (text : String) : String :=
  if text.utf8ByteSize <= 1023 then text
  else decodeLossy (text.toUTF8.extract 0 1023)

private def formattedError {α : Type} (text : String) : IO α :=
  throw (IO.userError (formattedErrorText text))

def pathError {α : Type} (what path : String) (error : Int) : IO α := do
  formattedError s!"{what} {path}: {← strerror error.natAbs.toUInt32}"

partial def openRetry (path : String) (flags : UInt32) : IO Int := do
  let fd ← openFile path flags
  if fd == -(errnoValue (Posix.EINTR ())) then openRetry path flags else pure fd

partial def readLoop (fd : UInt32) (path : String) (bytes : ByteArray)
    (capacity : Nat) : IO ByteArray := do
  let capacity ← if bytes.size == capacity then
      if capacity > readCap then formattedError s!"{path}: file too large"
      else pure (min (capacity * 2) (readCap + 1))
    else pure capacity
  let (rc, chunk) ← read fd (capacity - bytes.size).toUInt32
  if rc == -(errnoValue (Posix.EINTR ())) then return ← readLoop fd path bytes capacity
  if rc < 0 then pathError "unable to read" path rc
  if rc == 0 then
    if bytes.size > readCap then formattedError s!"{path}: file too large"
    return bytes
  readLoop fd path (bytes ++ chunk) capacity

def readFile (path : String) (follow : Bool) : IO (Array Int × String) := do
  checkString path
  let fd ← openRetry path (readOpenFlags () ||| if follow then 0 else Posix.O_NOFOLLOW ())
  if fd < 0 then pathError "unable to open" path fd
  let fd := fd.toNat.toUInt32
  let (st, bytes) ← try
    let (rc, st) ← fstat fd
    if rc < 0 then pathError "unable to stat" path rc
    if (st[2]!.toNat &&& (Posix.S_IFMT ()).toNat) != (Posix.S_IFREG ()).toNat then
      formattedError s!"{path} is not a regular file"
    unless fileAccepted st[2]!.toNat st[5]! do
      formattedError s!"{path}: file too large"
    let bytes ← readLoop fd path ByteArray.empty (st[5]!.toNat + 1)
    pure (st, bytes)
  finally discard (close fd)
  return (st, ← decode bytes (formattedErrorText s!"{path}: file is not valid UTF-8"))

partial def listDir (path : String) : IO (List String) := do
  checkString path
  let fd ← openFile path (Posix.O_RDONLY () ||| Posix.O_DIRECTORY () ||| Posix.O_CLOEXEC ())
  if fd < 0 then pathError "unable to open" path fd
  let (rc, handle) ← fdopendir fd.toNat.toUInt32
  if rc < 0 then
    discard (close fd.toNat.toUInt32)
    pathError "unable to open" path rc
  try
    let mut out := #[]
    repeat
      let (rc, entry) ← readdir handle
      if rc < 0 then pathError "unable to read" path rc
      let some bytes := entry | break
      let name ← decode bytes
        (formattedErrorText s!"{path}: directory entry name is not valid UTF-8")
      unless name == "." || name == ".." do out := out.push name
    return out.toList
  finally discard (closedir handle)

def openReadOnly (path : String) (regular : Bool) : IO (Nat × Array Int) := do
  checkString path
  let fd ← openFile path (readOpenFlags ())
  if fd < 0 then pathError "unable to open" path fd
  let (rc, st) ← fstat fd.toNat.toUInt32
  if rc < 0 then
    discard (close fd.toNat.toUInt32)
    pathError "unable to stat" path rc
  if regular && (st[2]!.toNat &&& (Posix.S_IFMT ()).toNat) != (Posix.S_IFREG ()).toNat then
    discard (close fd.toNat.toUInt32)
    throw (IO.userError "command is not a regular file")
  if fd < 3 then
    let copy ← dup fd.toNat.toUInt32
    discard (close fd.toNat.toUInt32)
    check copy
    return (copy.toNat, st)
  return (fd.toNat, st)

def closeDescriptor (fd : UInt32) : IO Unit := do
  if fd < 3 || fd > Posix.INT_MAX () then throw (IO.userError "invalid file descriptor")
  check (← close fd)

partial def writeStderr (bytes : ByteArray) (offset : Nat := 0) : IO Unit := do
  if offset >= bytes.size then return
  let rc ← write (Posix.STDERR_FILENO ()) bytes offset.toUSize
  if rc == -(errnoValue (Posix.EINTR ())) then return ← writeStderr bytes offset
  if rc == 0 then failErrno (errnoValue (Posix.EIO ()))
  check rc
  writeStderr bytes (offset + rc.toNat)

end LeanSudo.Sys.Prim.CoreFacts
