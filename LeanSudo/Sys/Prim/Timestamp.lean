namespace LeanSudo.Sys.Prim.Timestamp

abbrev Result (α : Type) := Except UInt32 α

structure Constants where
  openReadOnly : UInt64
  openReadWrite : UInt64
  openCloexec : UInt64
  openDirectory : UInt64
  openNofollow : UInt64
  openNonblock : UInt64
  openCreate : UInt64
  currentDirectory : UInt64
  interrupted : UInt64
  noEntry : UInt64
  alreadyExists : UInt64
  notDirectory : UInt64
  denied : UInt64
  invalid : UInt64
  overflow : UInt64
  badFd : UInt64
  ioError : UInt64
  symlinkLoop : UInt64
  writeLock : UInt64
  unlock : UInt64
  realtime : UInt64
  boottime : UInt64
  sigInt : UInt64
  sigQuit : UInt64
  typeMask : UInt64
  directory : UInt64
  regular : UInt64
  groupWrite : UInt64
  otherWrite : UInt64
  privateDir : UInt64
  traverseDir : UInt64
  privateFile : UInt64
  pathMax : UInt64
  nameMax : UInt64
  fdMax : UInt64
  uidInvalid : UInt64
  gidInvalid : UInt64
  offsetMax : UInt64
  timeMax : UInt64
  ssizeMax : UInt64
  sysconfError : UInt64
  longMax : UInt64
  deriving Inhabited

@[extern "lean_sudo_prim_ts_constants"]
opaque constants : IO Constants

structure Stat where
  mode : UInt64
  uid : UInt64
  gid : UInt64
  size : UInt64
  mtime : UInt64

structure Time where
  seconds : UInt64
  fraction : UInt64

@[extern "lean_sudo_prim_ts_error"]
opaque errorText (error : UInt32) : IO String
@[extern "lean_sudo_prim_ts_openat"]
opaque openAt (dir : UInt32) (name : @& String) (flags mode : UInt32) : IO (Result UInt32)
@[extern "lean_sudo_prim_ts_mkdirat"]
opaque mkdirAt (dir : UInt32) (name : @& String) (mode : UInt32) : IO (Result Unit)
@[extern "lean_sudo_prim_ts_unlinkat"]
opaque unlinkAt (dir : UInt32) (name : @& String) : IO (Result Unit)
@[extern "lean_sudo_prim_ts_fstat"]
opaque stat (fd : UInt32) : IO (Result Stat)
@[extern "lean_sudo_prim_ts_fchmod"]
opaque chmod (fd mode : UInt32) : IO (Result Unit)
@[extern "lean_sudo_prim_ts_fchown"]
opaque chown (fd uid gid : UInt32) : IO (Result Unit)
@[extern "lean_sudo_prim_ts_geteuid"]
opaque geteuid : IO UInt32
@[extern "lean_sudo_prim_ts_seteuid"]
opaque seteuid (uid : UInt32) : IO (Result Unit)
@[extern "lean_sudo_prim_ts_close"]
opaque close (fd : UInt32) : IO (Result Unit)
@[extern "lean_sudo_prim_ts_pread"]
opaque pread (fd : UInt32) (offset : UInt64) (length : UInt32) : IO (Result ByteArray)
@[extern "lean_sudo_prim_ts_pwrite"]
opaque pwrite (fd : UInt32) (offset : UInt64) (bytes : @& ByteArray)
  (start length : UInt64) : IO (Result UInt64)
@[extern "lean_sudo_prim_ts_truncate"]
opaque truncate (fd : UInt32) (length : UInt64) : IO (Result Unit)
@[extern "lean_sudo_prim_ts_lock"]
opaque lock (fd : UInt32) (offset length : UInt64) (type : UInt32) : IO (Result Unit)

structure LockResult where
  status : UInt32
  error : UInt32
  signal : UInt32

@[extern "lean_sudo_prim_ts_wait_lock"]
opaque waitLock (fd : UInt32) (offset length : UInt64) (type first second : UInt32) :
  IO LockResult

@[extern "lean_sudo_prim_ts_clock"]
opaque clock (clock : UInt32) : IO (Result Time)
@[extern "lean_sudo_prim_ts_timeofday"]
opaque timeofday : IO (Result Time)
@[extern "lean_sudo_prim_ts_monotonic"]
opaque monotonic : IO UInt64
@[extern "lean_sudo_prim_ts_ticks"]
opaque ticks : IO (Result UInt64)
@[extern "lean_sudo_prim_ts_getsid"]
opaque getsid : IO (Result UInt32)
@[extern "lean_sudo_prim_ts_getppid"]
opaque getppid : IO UInt32

end LeanSudo.Sys.Prim.Timestamp
