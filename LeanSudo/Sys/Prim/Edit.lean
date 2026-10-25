namespace LeanSudo.Sys.Prim.Edit

abbrev Result (α : Type) := Except UInt32 α

structure Packet where
  bytes : ByteArray
  control : ByteArray
  flags : UInt32

structure Time where
  seconds : UInt64
  nanos : UInt64

structure Platform where
  atFdcwd : Nat
  pathMax : Nat
  eAccess : Nat
  eReadOnly : Nat
  eNameTooLong : Nat
  xOk : Nat
  wOk : Nat
  msgTrunc : Nat
  msgCtrunc : Nat
  solSocket : Nat
  scmRights : Nat
  cmsgSpace : Nat
  cmsgLength : Nat
  cmsgDataOffset : Nat
  cmsgLengthOffset : Nat
  cmsgLengthWidth : Nat
  cmsgLevelOffset : Nat
  cmsgLevelWidth : Nat
  cmsgTypeOffset : Nat
  cmsgTypeWidth : Nat
  intWidth : Nat
  littleEndian : Nat
  createMode : Nat
  modeMask : Nat
  maxOffset : Nat
  deriving Inhabited

@[extern "leansudo_prim_edit_platform"]
opaque platform : IO Platform
@[extern "leansudo_prim_edit_default_mask"]
opaque defaultMask : Unit → UInt32

@[extern "leansudo_prim_edit_socketpair"]
opaque socketPair : IO (Result (UInt32 × UInt32))
@[extern "leansudo_prim_edit_sendmsg"]
opaque sendMsg (fd : UInt32) (bytes control : @& ByteArray) : IO (Result UInt64)
@[extern "leansudo_prim_edit_recvmsg"]
opaque recvMsg (fd : UInt32) : IO (Result Packet)
@[extern "leansudo_prim_edit_openat"]
opaque openAt (dir : UInt32) (path : @& String) (flags mode : UInt32) : IO (Result UInt32)
@[extern "leansudo_prim_edit_faccessat"]
opaque accessAt (dir : UInt32) (path : @& String) (mode : UInt32) : IO (Result Unit)
@[extern "leansudo_prim_edit_unlinkat"]
opaque unlinkAt (dir : UInt32) (path : @& String) : IO (Result Unit)
@[extern "leansudo_prim_edit_mkostemps"]
opaque makeTemp (path : @& String) (suffix : UInt32) : IO (Result (String × UInt32))
@[extern "leansudo_prim_edit_fstat"]
opaque stat (fd : UInt32) : IO (Result (Array Nat))
@[extern "leansudo_prim_edit_pread"]
opaque pread (fd : UInt32) (offset : UInt64) (count : UInt32) : IO (Result ByteArray)
@[extern "leansudo_prim_edit_pwrite"]
opaque pwrite (fd : UInt32) (bytes : @& ByteArray) (offset count : UInt64) : IO (Result UInt64)
@[extern "leansudo_prim_edit_ftruncate"]
opaque truncate (fd : UInt32) (size : UInt64) : IO (Result Unit)
@[extern "leansudo_prim_edit_fsync"]
opaque sync (fd : UInt32) : IO (Result Unit)
@[extern "leansudo_prim_edit_futimens"]
opaque setTimes (fd : UInt32) (seconds nanos : UInt64) : IO (Result Unit)
@[extern "leansudo_prim_edit_clock"]
opaque clock : IO (Result Time)

end LeanSudo.Sys.Prim.Edit
