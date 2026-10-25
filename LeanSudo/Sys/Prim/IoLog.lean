namespace LeanSudo.Sys.Prim.IoLog

structure Constants where
  readOnly : UInt32
  writeOnly : UInt32
  readWrite : UInt32
  create : UInt32
  noFollow : UInt32
  closeExec : UInt32
  nonblock : UInt32
  directory : UInt32
  noControllingTty : UInt32
  ownerAll : UInt32
  ownerReadWrite : UInt32
  groupReadWrite : UInt32
  groupExecute : UInt32
  otherReadWrite : UInt32
  otherExecute : UInt32
  permissions : UInt32
  fileType : UInt32
  regularFile : UInt32
  writePermissions : UInt32
  alreadyExists : UInt32
  interrupted : UInt32
  realtime : UInt32
  monotonic : UInt32
  sigCont : UInt32
  sigTstp : UInt32
  sigTtin : UInt32
  sigTtou : UInt32
  currentDirectory : UInt32
  intMax : UInt32
  lockExclusive : UInt32
  loadNow : UInt32
  loadLocal : UInt32
  regexExtended : UInt32
  regexNoSub : UInt32
  syncFlush : UInt32
  deriving Inhabited

@[extern "leansudo_iop_constants"] private opaque constantsRaw : IO Constants
private initialize cachedConstants : IO.Ref (Option Constants) ← IO.mkRef none

def constants : IO Constants := do
  if let some value ← cachedConstants.get then return value
  let value ← constantsRaw
  cachedConstants.set (some value)
  return value

@[extern "leansudo_iop_openat"] private opaque openatRaw (dir : UInt32) (path : @& String)
    (flags mode : UInt32) : IO (UInt32 × UInt32)
@[extern "leansudo_iop_mkdirat"] opaque mkdirat (dir : UInt32) (path : @& String)
    (mode : UInt32) : IO UInt32
@[extern "leansudo_iop_close"] private opaque closeRaw (fd : UInt32) : IO UInt32
@[extern "leansudo_iop_chown"] private opaque chownRaw (fd uid gid : UInt32) : IO UInt32
@[extern "leansudo_iop_chmod"] private opaque chmodRaw (fd mode : UInt32) : IO UInt32
@[extern "leansudo_iop_truncate"] private opaque truncateRaw (fd : UInt32) (size : UInt64) : IO UInt32
@[extern "leansudo_iop_stat"] private opaque statRaw (fd : UInt32) : IO (UInt32 × Nat × Nat × Nat)
@[extern "leansudo_iop_lock"] private opaque lockRaw (fd command : UInt32) : IO UInt32
@[extern "leansudo_iop_pread"] private opaque preadRaw (fd count : UInt32)
    (offset : UInt64) : IO (UInt32 × ByteArray)
@[extern "leansudo_iop_pwrite"] private opaque pwriteRaw (fd : UInt32) (bytes : @& ByteArray)
    (offset : UInt64) : IO (UInt32 × Nat)
@[extern "leansudo_iop_write"] opaque write (fd : UInt32) (bytes : @& ByteArray)
    (offset : UInt64) : IO (Nat × UInt32)
@[extern "leansudo_iop_error_text"] opaque errorText (error : UInt32) : IO String
@[extern "leansudo_iop_clock"] private opaque clockRaw (kind : UInt32) : IO (UInt32 × Nat × Nat)
@[extern "leansudo_iop_winsize"] private opaque winsizeRaw (fd : UInt32) : IO (UInt32 × Nat × Nat)
@[extern "leansudo_iop_dlopen"] opaque dlopen (path : @& String) (flags : UInt32) : IO UInt64
@[extern "leansudo_iop_dlsym"] opaque dlsym (handle : UInt64) (name : @& String) : IO UInt64
@[extern "leansudo_iop_gzdopen"] opaque gzdopen (fn : UInt64) (fd : UInt32)
    (mode : @& String) : IO UInt64
@[extern "leansudo_iop_gzwrite"] opaque gzwrite (fn stream : UInt64)
    (bytes : @& ByteArray) : IO UInt32
@[extern "leansudo_iop_gzflush"] opaque gzflush (fn stream : UInt64) (mode : UInt32) : IO UInt32
@[extern "leansudo_iop_gzclose"] opaque gzclose (fn stream : UInt64) : IO UInt32
@[extern "leansudo_iop_regex_alloc"] private opaque regexAllocRaw : IO (UInt32 × UInt64)
@[extern "leansudo_iop_regex_compile"] opaque regexCompile (regex : UInt64)
    (pattern : @& String) (flags : UInt32) : IO UInt32
@[extern "leansudo_iop_regex_match"] opaque regexMatch (regex : UInt64)
    (bytes : @& ByteArray) (flags : UInt32) : IO UInt32
@[extern "leansudo_iop_regex_release"] opaque regexRelease (regex : UInt64) : IO Unit
@[extern "leansudo_iop_free"] opaque free (pointer : UInt64) : IO Unit

private def check (error : UInt32) : IO Unit := do
  if error != 0 then throw (IO.userError (← errorText error))

private def checked (result : UInt32 × α) : IO α := do
  check result.1
  return result.2

def openat (dir : UInt32) (path : String) (flags mode : UInt32) : IO UInt32 := do
  checked (← openatRaw dir path flags mode)

def close (fd : UInt32) : IO Unit := do
  check (← closeRaw fd)

def chown (fd uid gid : UInt32) : IO Unit := do
  check (← chownRaw fd uid gid)

def chmod (fd mode : UInt32) : IO Unit := do
  check (← chmodRaw fd mode)

def truncate (fd : UInt32) (size : UInt64) : IO Unit := do
  check (← truncateRaw fd size)

def stat (fd : UInt32) : IO (Nat × Nat × Nat) := do
  checked (← statRaw fd)

def lock (fd command : UInt32) : IO Unit := do
  check (← lockRaw fd command)

def pread (fd count : UInt32) (offset : UInt64) : IO ByteArray := do
  checked (← preadRaw fd count offset)

def pwrite (fd : UInt32) (bytes : ByteArray) (offset : UInt64) : IO Nat := do
  checked (← pwriteRaw fd bytes offset)

def clock (kind : UInt32) : IO (Nat × Nat) := do
  checked (← clockRaw kind)

def winsize (fd : UInt32) : IO (Nat × Nat) := do
  checked (← winsizeRaw fd)

def regexAlloc : IO UInt64 := do
  checked (← regexAllocRaw)

end LeanSudo.Sys.Prim.IoLog
