namespace LeanSudo.Sys.Prim.Plugins

abbrev Result := UInt32 × Option String
abbrev Callback := UInt32 → USize → USize → USize → USize → USize → IO USize

@[extern "lean_sudo_pp_constant"] private opaque constant (index : UInt32) : USize

@[extern "lean_sudo_pp_pointerSize"] opaque pointerSize : Unit → USize
@[extern "lean_sudo_pp_messageSize"] opaque messageSize : Unit → USize
@[extern "lean_sudo_pp_messageType"] opaque messageType : Unit → USize
@[extern "lean_sudo_pp_messageTimeout"] opaque messageTimeout : Unit → USize
@[extern "lean_sudo_pp_messageText"] opaque messageText : Unit → USize
@[extern "lean_sudo_pp_replySize"] opaque replySize : Unit → USize
@[extern "lean_sudo_pp_replyValue"] opaque replyValue : Unit → USize
@[extern "lean_sudo_pp_hookVersion"] opaque hookVersion : Unit → USize
@[extern "lean_sudo_pp_hookType"] opaque hookType : Unit → USize
@[extern "lean_sudo_pp_hookFunction"] opaque hookFunction : Unit → USize
@[extern "lean_sudo_pp_hookClosure"] opaque hookClosure : Unit → USize
@[extern "lean_sudo_pp_conversationVersion"] opaque conversationVersion : Unit → USize
@[extern "lean_sudo_pp_pluginType"] opaque pluginType : Unit → USize
@[extern "lean_sudo_pp_pluginVersion"] opaque pluginVersion : Unit → USize
def methodOffset (type : UInt32) (index : Nat) : USize :=
  constant ((if type == 2 then 14 else if type == 3 then 27 else 36) + index.toUInt32)
@[extern "lean_sudo_pp_unsupported"] opaque unsupported : Unit → UInt32
@[extern "lean_sudo_pp_pollIn"] opaque pollIn : Unit → UInt32
@[extern "lean_sudo_pp_pollOut"] opaque pollOut : Unit → UInt32
@[extern "lean_sudo_pp_pollFailed"] opaque pollFailed : Unit → UInt32
@[extern "lean_sudo_pp_signalCount"] opaque signalCount : Unit → UInt32
def limitResource (index : Nat) : UInt32 := (constant (45 + index.toUInt32)).toUInt32
@[extern "lean_sudo_pp_limitInfinity"] opaque limitInfinity : Unit → UInt64
@[extern "lean_sudo_pp_ptySlaveMajor"] opaque ptySlaveMajor : Unit → UInt32
@[extern "lean_sudo_pp_ptyMajorCount"] opaque ptyMajorCount : Unit → UInt32
@[extern "lean_sudo_pp_ttyMajor"] opaque ttyMajor : Unit → UInt32
@[extern "lean_sudo_pp_linuxDevices"] opaque linuxDevices : Unit → Bool
@[extern "lean_sudo_pp_ptyMinorCount"] opaque ptyMinorCount : Unit → UInt32
@[extern "lean_sudo_pp_ttySerialBase"] opaque ttySerialBase : Unit → UInt32
@[extern "lean_sudo_pp_groupsFallback"] opaque groupsFallback : Unit → UInt32

@[extern "lean_sudo_pp_timespec_get"] opaque timespecGet (ptr : USize) : IO (UInt64 × UInt64)
@[extern "lean_sudo_pp_timespec_set"] opaque timespecSet (ptr : USize)
    (seconds nanos : UInt64) : IO Unit
@[extern "lean_sudo_pp_dev_major"] opaque deviceMajor (dev : UInt64) : UInt32
@[extern "lean_sudo_pp_dev_minor"] opaque deviceMinor (dev : UInt64) : UInt32

@[extern "lean_sudo_pp_install"] opaque install (callback : Callback) : IO Unit
@[extern "lean_sudo_pp_dlopen"] opaque dlopen (path : @& String) : IO USize
@[extern "lean_sudo_pp_dlsym"] opaque dlsym (handle : USize) (name : @& String) : IO USize
@[extern "lean_sudo_pp_dlerror"] private opaque dlerrorRaw : IO (Option String)

def dlerror : IO String := return (← dlerrorRaw).getD "unknown error"

@[extern "lean_sudo_pp_dlclose"] opaque dlclose (handle : USize) : IO UInt32
@[extern "lean_sudo_pp_alloc"] opaque alloc (size : USize) : IO USize
@[extern "lean_sudo_pp_free"] opaque free (ptr : USize) : IO Unit
@[extern "lean_sudo_pp_erase"] opaque erase (ptr size : USize) : IO Unit
@[extern "lean_sudo_pp_dup"] opaque dup (text : @& String) : IO USize
@[extern "lean_sudo_pp_dup_bytes"] opaque dupBytes (data : @& ByteArray) : IO USize
@[extern "lean_sudo_pp_string"] opaque string (ptr : USize) : IO String
@[extern "lean_sudo_pp_length"] opaque length (ptr : USize) : IO USize
@[extern "lean_sudo_pp_read_ptr"] opaque readPtr (ptr offset : USize) : IO USize
@[extern "lean_sudo_pp_write_ptr"] opaque writePtr (ptr offset value : USize) : IO Unit
@[extern "lean_sudo_pp_read_u32"] opaque readU32 (ptr offset : USize) : IO UInt32
@[extern "lean_sudo_pp_errno"] opaque setErrno (value : UInt32) : IO Unit
@[extern "lean_sudo_pp_write"] opaque write (fd : UInt32) (ptr size : USize) : IO USize
@[extern "lean_sudo_pp_open_tty"] opaque openTty (flags : UInt32) : IO UInt32
@[extern "lean_sudo_pp_close_fd"] opaque closeFd (fd : UInt32) : IO UInt32
@[extern "lean_sudo_pp_now"] private opaque nowRaw : IO (UInt32 × UInt64 × UInt64)
@[extern "lean_sudo_pp_poll"] private opaque pollRaw (fd events : UInt32) : IO (UInt32 × UInt32)
@[extern "lean_sudo_pp_strerror"] private opaque errorText (error : UInt32) : IO String

def now : IO UInt64 := do
  let (error, seconds, nanos) ← nowRaw
  if error != 0 then throw (IO.userError (← errorText error))
  return seconds * 1000000000 + nanos

def poll (fd events : UInt32) : IO UInt32 := do
  let (error, result) ← pollRaw fd events
  if error != 0 then throw (IO.userError (← errorText error))
  return result

@[extern "lean_sudo_pp_getpid"] opaque getpid : IO UInt32
@[extern "lean_sudo_pp_getppid"] opaque getppid : IO UInt32
@[extern "lean_sudo_pp_getpgrp"] opaque getpgrp : IO UInt32
@[extern "lean_sudo_pp_getsid"] opaque getsid : IO UInt32
@[extern "lean_sudo_pp_tcgetpgrp"] opaque tcgetpgrp (fd : UInt32) : IO UInt32
@[extern "lean_sudo_pp_winsize"] private opaque winsizeRaw (fd : UInt32) :
  IO (Option (UInt32 × UInt32))

def winsize (fd : UInt32) : IO (UInt32 × UInt32) :=
  return (← winsizeRaw fd).getD (0, 0)

@[extern "lean_sudo_pp_ttydev"] opaque ttydev (fd : UInt32) : IO (Option UInt32)
@[extern "lean_sudo_pp_group_max"] opaque groupMax : IO USize
@[extern "lean_sudo_pp_rlimit"] opaque rlimit (resource : UInt32) : IO (Option (UInt64 × UInt64))
@[extern "lean_sudo_pp_clone"] opaque clone (fn : USize) : IO USize
@[extern "lean_sudo_pp_hooks"] opaque hooks (fn : USize) (add : Bool) : IO Unit
@[extern "lean_sudo_pp_open_common"] opaque openCommon (fn s u : USize) (index : UInt32)
    (a e o : USize) : IO Result
@[extern "lean_sudo_pp_open_io0"] opaque openIo0 (fn s u : USize) (count : UInt32)
    (a e : USize) : IO Result
@[extern "lean_sudo_pp_open_io1"] opaque openIo1 (fn s u info : USize) (count : UInt32)
    (a e : USize) : IO Result
@[extern "lean_sudo_pp_open_io2"] opaque openIo2 (fn s u info : USize) (count : UInt32)
    (a e o : USize) : IO Result
@[extern "lean_sudo_pp_open_io"] opaque openIo (fn s u info : USize) (count : UInt32)
    (a e o : USize) : IO Result
@[extern "lean_sudo_pp_accept"] opaque accept (fn : USize) (name : @& String)
    (type : UInt32) (info a e : USize) : IO Result
@[extern "lean_sudo_pp_message"] opaque message (fn : USize) (name : @& String)
    (type : UInt32) (message : @& String) (info : USize) : IO Result
@[extern "lean_sudo_pp_check"] opaque check (fn info a e : USize) : IO Result
@[extern "lean_sudo_pp_close"] opaque close (fn : USize) (a b : UInt32) : IO Unit
@[extern "lean_sudo_pp_close0"] opaque close0 (fn : USize) : IO Unit
@[extern "lean_sudo_pp_int"] opaque callInt (fn : USize) (arg : UInt32) : IO UInt32
@[extern "lean_sudo_pp_log"] opaque log (fn : USize) (data : @& ByteArray) : IO Result
@[extern "lean_sudo_pp_log_old"] opaque logOld (fn : USize) (data : @& ByteArray) : IO Result
@[extern "lean_sudo_pp_suspend"] opaque suspend (fn : USize) (signo : UInt32) : IO Result
@[extern "lean_sudo_pp_window"] opaque window (fn : USize) (rows cols : UInt32) : IO Result
@[extern "lean_sudo_pp_window_old"] opaque windowOld (fn : USize) (rows cols : UInt32) : IO UInt32
@[extern "lean_sudo_pp_event_alloc"] opaque eventAlloc : IO USize
@[extern "lean_sudo_pp_event_setter"] opaque eventSetter (slot : USize) : IO Unit
@[extern "lean_sudo_pp_event"] opaque event (fn : USize) (fd what : UInt32)
    (closure : USize) : IO Unit
@[extern "lean_sudo_pp_hook_get"] opaque hookGet (fn name closure : USize) : IO (UInt32 × USize)
@[extern "lean_sudo_pp_hook_set"] opaque hookSet (fn name value : USize)
    (overwrite : UInt32) (closure : USize) : IO UInt32
@[extern "lean_sudo_pp_hook_unset"] opaque hookUnset (fn name closure : USize) : IO UInt32
@[extern "lean_sudo_pp_real_get"] opaque realGet (name : USize) : IO USize
@[extern "lean_sudo_pp_real_set"] opaque realSet (name value : USize)
    (overwrite : UInt32) : IO UInt32
@[extern "lean_sudo_pp_real_unset"] opaque realUnset (name : USize) : IO UInt32
@[extern "lean_sudo_pp_real_put"] opaque realPut (value : USize) : IO UInt32

end LeanSudo.Sys.Prim.Plugins
