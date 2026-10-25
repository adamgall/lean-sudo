import LeanSudo.Sys.Prim.ExecConstants

namespace LeanSudo.Sys.Prim.Exec

@[extern "ls_exec_rt_min"] opaque realtimeMin : Unit → UInt32
@[extern "ls_exec_rt_kernel_min"] opaque kernelRealtimeMin : Unit → UInt32
@[extern "ls_exec_sig_default"] opaque defaultHandler : Unit → USize
@[extern "ls_exec_sig_ignore"] opaque ignoreHandler : Unit → USize

def supportedSignal (signal : Nat) : Bool :=
  signal < (kernelRealtimeMin ()).toNat || signal ≥ (realtimeMin ()).toNat

def supportedMask (mask : UInt64) : UInt64 := Id.run do
  let mut result := mask
  for signal in [(kernelRealtimeMin ()).toNat:(realtimeMin ()).toNat] do
    result := result &&& ~~~((1 : UInt64) <<< (signal - 1).toUInt64)
  return result

@[extern "leansudo_prim_exec_signal_fd"]
private opaque signalFdRaw (mask : UInt64) : IO UInt32

def signalFd (mask : UInt64 := 0xFFFFFFFFFFFFFFFF) : IO UInt32 :=
  signalFdRaw (supportedMask mask)

@[extern "leansudo_prim_exec_signal_mask"]
private opaque signalMaskRaw (mask : UInt64) : IO Unit

def signalMask (mask : UInt64) : IO Unit :=
  signalMaskRaw (supportedMask mask)

@[extern "leansudo_prim_exec_startup_mask"]
opaque startupMask : IO UInt64

@[extern "leansudo_prim_exec_binary_fd"]
opaque binaryFd : IO UInt32

@[extern "leansudo_prim_exec_read"]
opaque read (fd size : UInt32) : IO (UInt32 × ByteArray)

@[extern "leansudo_prim_exec_write"]
opaque write (fd : UInt32) (bytes : @& ByteArray) (offset size : UInt32) : IO (UInt32 × UInt32)

@[extern "leansudo_prim_exec_close"]
opaque close (fd : UInt32) : IO Unit

@[extern "leansudo_prim_exec_strerror"]
opaque strerror (error : UInt32) : IO String

structure SignalInfo where
  signo : UInt32
  code : Int32
  pid : UInt32
  deriving Inhabited

def word32 (bytes : ByteArray) (offset : Nat) : UInt32 :=
  (bytes[offset]!.toUInt32) ||| (bytes[offset + 1]!.toUInt32 <<< 8) |||
    (bytes[offset + 2]!.toUInt32 <<< 16) ||| (bytes[offset + 3]!.toUInt32 <<< 24)

def nativeWord32 (bytes : ByteArray) (offset : Nat) : UInt32 :=
  if K.littleEndian () != 0 then word32 bytes offset
  else (bytes[offset]!.toUInt32 <<< 24) ||| (bytes[offset + 1]!.toUInt32 <<< 16) |||
    (bytes[offset + 2]!.toUInt32 <<< 8) ||| bytes[offset + 3]!.toUInt32

def readSignal (fd : UInt32) : IO (Option SignalInfo) := do
  let (error, bytes) ← read fd (K.signalInfoSize ())
  if error == (K.EAGAIN ()) || error == (K.EINTR ()) then return none
  if error != 0 then throw (IO.userError (← strerror error))
  if bytes.size != (K.signalInfoSize ()).toNat then
    throw (IO.userError "invalid signal descriptor record")
  return some {
    signo := nativeWord32 bytes (K.signalInfoSigno ())
    code := (nativeWord32 bytes (K.signalInfoCode ())).toInt32
    pid := nativeWord32 bytes (K.signalInfoPid ()) }

partial def writeAll (fd : UInt32) (bytes : ByteArray) (offset : Nat := 0) : IO Unit := do
  if offset >= bytes.size then return
  let (error, count) ← write fd bytes offset.toUInt32 (bytes.size - offset).toUInt32
  if error == (K.EINTR ()) then return ← writeAll fd bytes offset
  if error != 0 then throw (IO.userError (← strerror error))
  if count == 0 then throw (IO.userError "short write")
  writeAll fd bytes (offset + count.toNat)

@[extern "leansudo_prim_exec_open"]
opaque openFile (path : @& String) (flags mode : UInt32) : IO Int64

@[extern "leansudo_prim_exec_fcntl"]
opaque fcntl (fd op arg : UInt32) : IO Int64

@[extern "leansudo_prim_exec_dup2"]
opaque dup2 (source target : UInt32) : IO Unit

@[extern "leansudo_prim_exec_pipe"]
opaque pipe (flags : UInt32 := (K.O_CLOEXEC ())) : IO (UInt32 × UInt32)

@[extern "leansudo_prim_exec_socketpair"]
opaque socketpair : IO (UInt32 × UInt32)

@[extern "leansudo_prim_exec_peer_credentials"]
opaque peerCredentials (fd : UInt32) : IO (UInt32 × UInt32 × UInt32)

@[extern "leansudo_prim_exec_fork_helper"]
opaque forkHelper (executable plan : UInt32) (keep : @& Array UInt32) : IO UInt32

@[extern "leansudo_prim_exec_getpid"] opaque getpid : IO UInt32
@[extern "leansudo_prim_exec_getppid"] opaque getppid : IO UInt32
@[extern "leansudo_prim_exec_getuid"] opaque getuid : IO UInt32
@[extern "leansudo_prim_exec_geteuid"] opaque geteuid : IO UInt32
@[extern "leansudo_prim_exec_getgid"] opaque getgid : IO UInt32

@[extern "leansudo_prim_exec_stat"]
opaque stat (path : @& String) : IO (Array UInt64)

@[extern "leansudo_prim_exec_fstat"]
opaque fstat (fd : UInt32) : IO (Array UInt64)

@[extern "leansudo_prim_exec_getresuid"] opaque getresuid : IO (UInt32 × UInt32 × UInt32)
@[extern "leansudo_prim_exec_getresgid"] opaque getresgid : IO (UInt32 × UInt32 × UInt32)
@[extern "leansudo_prim_exec_setresuid"] opaque setresuid (r e s : UInt32) : IO Unit
@[extern "leansudo_prim_exec_setresgid"] opaque setresgid (r e s : UInt32) : IO Unit
@[extern "leansudo_prim_exec_setuid"] opaque setuid (uid : UInt32) : IO UInt32
@[extern "leansudo_prim_exec_setgid"] opaque setgid (gid : UInt32) : IO UInt32
@[extern "leansudo_prim_exec_fsuid"] opaque fsuid : IO UInt32
@[extern "leansudo_prim_exec_fsgid"] opaque fsgid : IO UInt32

@[extern "leansudo_prim_exec_getgroups"]
opaque getgroupsRaw (capacity : UInt32) : IO (UInt32 × Array UInt32)

def getgroups : IO (Array UInt32) := do
  let (count, _) ← getgroupsRaw 0
  if count > 65536 then throw (IO.userError "too many supplementary groups")
  return (← getgroupsRaw count).2

@[extern "leansudo_prim_exec_setgroups"]
opaque setgroups (groups : @& Array UInt32) : IO Unit

@[extern "leansudo_prim_exec_waitpid"]
opaque waitpid (pid flags : UInt32) : IO (Int64 × UInt32)

@[extern "leansudo_prim_exec_thread_setresuid"]
opaque threadSetresuid (r e s : UInt32) : IO Unit

@[extern "leansudo_prim_exec_thread_setgroups"]
opaque threadSetgroups (groups : @& Array UInt32) : IO Unit

@[extern "leansudo_prim_exec_thread_setresgid"]
opaque threadSetresgid (r e s : UInt32) : IO Unit

@[extern "leansudo_prim_exec_thread_setuid"]
opaque threadSetuid (uid : UInt32) : IO UInt32

@[extern "leansudo_prim_exec_thread_setgid"]
opaque threadSetgid (gid : UInt32) : IO UInt32

@[extern "leansudo_prim_exec_execve"]
opaque execve (path : @& String) (args env : @& Array String) : IO UInt32

@[extern "leansudo_prim_exec_fexecve"]
opaque fexecve (fd : UInt32) (args env : @& Array String) : IO UInt32

@[extern "leansudo_prim_exec_close_range"]
opaque closeRange (first last flags : UInt32) : IO UInt32

@[extern "leansudo_prim_exec_kill"]
opaque kill (pid signal : UInt32) : IO UInt32

@[extern "leansudo_prim_exec_exit"]
opaque exit (code : UInt32) : IO Unit

@[extern "leansudo_prim_exec_chdir"] opaque chdir (path : @& String) : IO UInt32
@[extern "leansudo_prim_exec_chroot"] opaque chroot (path : @& String) : IO UInt32
@[extern "leansudo_prim_exec_umask"] opaque umask (mask : UInt32) : IO UInt32
@[extern "leansudo_prim_exec_getrlimit"]
opaque getrlimit (resource : UInt32) : IO (UInt64 × UInt64)
@[extern "leansudo_prim_exec_setrlimit"]
opaque setrlimit (resource : UInt32) (current maximum : UInt64) : IO UInt32
@[extern "leansudo_prim_exec_prctl"]
opaque prctl (op : UInt32) (a b c d : UInt64 := 0) : IO Int64
@[extern "leansudo_prim_exec_seccomp"] opaque seccomp (bytes : @& ByteArray) : IO UInt32
@[extern "leansudo_prim_exec_signal_action"]
opaque signalAction (signal : UInt32) (handler : USize) (flags : UInt32 := 0)
  (mask : UInt64 := 0) (query : Bool := false) : IO (Array UInt64)
@[extern "leansudo_prim_exec_raise"] opaque raise (signal : UInt32) : IO UInt32
@[extern "leansudo_prim_exec_setsid"] opaque setsid : IO Int64
@[extern "leansudo_prim_exec_setpgid"] opaque setpgid (pid group : UInt32) : IO UInt32
@[extern "leansudo_prim_exec_getpgid"] opaque getpgid (pid : UInt32) : IO Int64
@[extern "leansudo_prim_exec_getsid"] opaque getsid (pid : UInt32) : IO Int64
@[extern "leansudo_prim_exec_poll"]
opaque poll (fds : @& Array (UInt32 × UInt32)) (timeout : UInt32) :
    IO (UInt32 × Array UInt32)
@[extern "leansudo_prim_exec_isatty"] opaque isatty (fd : UInt32) : IO Bool
@[extern "leansudo_prim_exec_tcgetattr"] opaque tcgetattr (fd : UInt32) : IO ByteArray
@[extern "leansudo_prim_exec_cfmakeraw"] opaque cfmakeraw (bytes : @& ByteArray) : IO ByteArray
@[extern "leansudo_prim_exec_tcsetattr"]
opaque tcsetattr (fd action : UInt32) (bytes : @& ByteArray) : IO UInt32
@[extern "leansudo_prim_exec_tcgetpgrp"] opaque tcgetpgrp (fd : UInt32) : IO Int64
@[extern "leansudo_prim_exec_tcsetpgrp"] opaque tcsetpgrp (fd group : UInt32) : IO UInt32
@[extern "leansudo_prim_exec_winsize"] opaque winsize (fd : UInt32) : IO (UInt32 × UInt32)
@[extern "leansudo_prim_exec_set_winsize"]
opaque setWinsize (fd rows cols : UInt32) : IO UInt32
@[extern "leansudo_prim_exec_ctty"] opaque ctty (fd : UInt32) : IO UInt32
@[extern "leansudo_prim_exec_openpty"]
opaque openpty (termios : @& ByteArray) (rows cols : UInt32) : IO (UInt32 × UInt32)

@[extern "leansudo_prim_exec_utmp_start"] opaque utmpStart : IO Unit
@[extern "leansudo_prim_exec_utmp_end"] opaque utmpEnd : IO Unit
@[extern "leansudo_prim_exec_utmp_get"]
opaque utmpGet (bytes : @& ByteArray) : IO (Option ByteArray)
@[extern "leansudo_prim_exec_utmp_put"] opaque utmpPut (bytes : @& ByteArray) : IO Bool
@[extern "leansudo_prim_exec_time"] opaque unixTime : IO UInt64

@[extern "leansudo_prim_exec_fchdir"] opaque fchdir (fd : UInt32) : IO UInt32
@[extern "leansudo_prim_exec_clearenv"] opaque clearenv : IO UInt32
@[extern "leansudo_prim_exec_setenv"]
opaque setenv (name value : @& String) : IO UInt32

end LeanSudo.Sys.Prim.Exec
