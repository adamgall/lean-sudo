import LeanSudo.Sys.Prim.Posix
import LeanSudo.Sys.Prim.Plugins
import LeanSudo.Sys.Prim.Store
import LeanSudo.Sys.Prim.CoreLogs

namespace LeanSudo.Sys.Prim.Pam

@[extern "lean_pam_const_ECHO"] opaque ECHO : Unit → UInt32
@[extern "lean_pam_const_ECHONL"] opaque ECHONL : Unit → UInt32
@[extern "lean_pam_const_ICANON"] opaque ICANON : Unit → UInt32
@[extern "lean_pam_const_IEXTEN"] opaque IEXTEN : Unit → UInt32
@[extern "lean_pam_const_VMIN"] opaque VMIN : Unit → UInt32
@[extern "lean_pam_const_VTIME"] opaque VTIME : Unit → UInt32
@[extern "lean_pam_const_VERASE"] opaque VERASE : Unit → UInt32
@[extern "lean_pam_const_VKILL"] opaque VKILL : Unit → UInt32
@[extern "lean_pam_const_VEOF"] opaque VEOF : Unit → UInt32
@[extern "lean_pam_const_TCSANOW"] opaque TCSANOW : Unit → UInt32
@[extern "lean_pam_const_TCSADRAIN"] opaque TCSADRAIN : Unit → UInt32
@[extern "lean_pam_const_PAM_SUCCESS"] opaque PAM_SUCCESS : Unit → UInt32
@[extern "lean_pam_const_PAM_BUF_ERR"] opaque PAM_BUF_ERR : Unit → UInt32
@[extern "lean_pam_const_PAM_AUTH_ERR"] opaque PAM_AUTH_ERR : Unit → UInt32
@[extern "lean_pam_const_PAM_CONV_ERR"] opaque PAM_CONV_ERR : Unit → UInt32
@[extern "lean_pam_const_PAM_MAX_RESP_SIZE"] opaque PAM_MAX_RESP_SIZE : Unit → UInt32
@[extern "lean_pam_const_PAM_SILENT"] opaque PAM_SILENT : Unit → UInt32
@[extern "lean_pam_const_PAM_CHANGE_EXPIRED_AUTHTOK"]
opaque PAM_CHANGE_EXPIRED_AUTHTOK : Unit → UInt32
@[extern "lean_pam_const_PAM_REINITIALIZE_CRED"] opaque PAM_REINITIALIZE_CRED : Unit → UInt32
@[extern "lean_pam_const_PAM_DELETE_CRED"] opaque PAM_DELETE_CRED : Unit → UInt32
@[extern "lean_pam_const_PAM_TTY"] opaque PAM_TTY : Unit → UInt32
@[extern "lean_pam_const_PAM_RUSER"] opaque PAM_RUSER : Unit → UInt32
@[extern "lean_pam_const_PAM_RHOST"] opaque PAM_RHOST : Unit → UInt32
@[extern "lean_pam_const_PAM_USER"] opaque PAM_USER : Unit → UInt32
@[extern "lean_pam_const_PAM_PROMPT_ECHO_OFF"] opaque PAM_PROMPT_ECHO_OFF : Unit → UInt32
@[extern "lean_pam_const_PAM_PROMPT_ECHO_ON"] opaque PAM_PROMPT_ECHO_ON : Unit → UInt32
@[extern "lean_pam_const_PAM_ERROR_MSG"] opaque PAM_ERROR_MSG : Unit → UInt32
@[extern "lean_pam_const_PAM_TEXT_INFO"] opaque PAM_TEXT_INFO : Unit → UInt32
@[extern "lean_pam_const_SUDO_CONV_PROMPT_MASK"] opaque SUDO_CONV_PROMPT_MASK : Unit → UInt32
@[extern "lean_pam_const_SUDO_CONV_PROMPT_ECHO_OK"] opaque SUDO_CONV_PROMPT_ECHO_OK : Unit → UInt32
@[extern "lean_pam_const_SUDO_CONV_PROMPT_ECHO_ON"] opaque SUDO_CONV_PROMPT_ECHO_ON : Unit → UInt32
@[extern "lean_pam_const_SUDO_CONV_TYPE_MASK"] opaque SUDO_CONV_TYPE_MASK : Unit → UInt32
@[extern "lean_pam_const_signalInfoSize"] opaque signalInfoSize : Unit → UInt32
@[extern "lean_pam_const_invalidFd"] opaque invalidFd : Unit → UInt32
@[extern "lean_pam_const_callbackSuspendOffset"]
private opaque callbackSuspendOffset : Unit → UInt32
@[extern "lean_pam_const_callbackResumeOffset"]
private opaque callbackResumeOffset : Unit → UInt32
@[extern "lean_pam_const_callbackClosureOffset"]
private opaque callbackClosureOffset : Unit → UInt32
@[extern "lean_pam_const_messageTypeOffset"] opaque messageTypeOffset : Unit → UInt32
@[extern "lean_pam_const_messageTextOffset"] opaque messageTextOffset : Unit → UInt32
@[extern "lean_pam_const_responseSize"] opaque responseSize : Unit → UInt32
@[extern "lean_pam_const_responseTextOffset"] opaque responseTextOffset : Unit → UInt32

def errorCode (code : UInt32) : Int := -Int.ofNat code.toNat

@[extern "lean_pam_sigemptyset"] opaque sigemptyset : IO ByteArray
@[extern "lean_pam_sigaddset"] opaque sigaddset (mask : ByteArray) (signal : UInt32) : IO ByteArray
@[extern "lean_pam_read_signal"] opaque readSignal (fd : UInt32) : IO (Int × UInt32)

@[extern "lean_pam_open"] opaque «open» (path : @& String) (flags : UInt32) : IO Int
@[extern "lean_pam_close"] opaque close (fd : UInt32) : IO Int
@[extern "lean_pam_read"] opaque read (fd size : UInt32) : IO (Int × ByteArray)
@[extern "lean_pam_write"] opaque write (fd : UInt32) (bytes : @& ByteArray)
    (offset : UInt32) : IO Int
@[extern "lean_pam_poll"] opaque poll (fd timeout : UInt32) (unblock : @& ByteArray) : IO Int
@[extern "lean_pam_catch_handler"] opaque catchHandler : Unit → USize
@[extern "lean_pam_caught"] opaque caught (signal : UInt32) : IO Bool

@[extern "lean_pam_tcgetattr"] opaque tcgetattr (fd : UInt32) : IO (Int × ByteArray)
@[extern "lean_pam_tcsetattr"] opaque tcsetattr (fd action : UInt32)
    (attrs : @& ByteArray) : IO Int
@[extern "lean_pam_termios_lflag"] opaque termiosLflag (attrs : @& ByteArray) : IO UInt32
@[extern "lean_pam_termios_set_lflag"] opaque termiosSetLflag
    (attrs : ByteArray) (value : UInt32) : IO ByteArray
@[extern "lean_pam_termios_cc"] opaque termiosCC
    (attrs : @& ByteArray) (index : UInt32) : IO UInt32
@[extern "lean_pam_termios_set_cc"] opaque termiosSetCC
    (attrs : ByteArray) (index value : UInt32) : IO ByteArray
@[extern "lean_pam_sigmask"] opaque sigmask (action : UInt32)
    (mask : @& ByteArray) : IO (Int × ByteArray)
@[extern "lean_pam_signalfd"] opaque signalfd (mask : @& ByteArray) : IO Int
@[extern "lean_pam_kill"] opaque kill (pid signal : UInt32) : IO Int
@[extern "lean_pam_dgettext"] opaque dgettext (text : @& String) : IO ByteArray
@[extern "lean_pam_callback_call"] private opaque callbackCall (fn : USize)
    (signal : UInt32) (closure : USize) : IO Int

private def callback (ptr : USize) (offset signal : UInt32) : IO Int := do
  if ptr == 0 then return 0
  let fn ← Plugins.readPtr ptr offset.toUSize
  if fn == 0 then return 0
  callbackCall fn signal (← Plugins.readPtr ptr (callbackClosureOffset ()).toUSize)

def callbackSuspend (ptr : USize) (signal : UInt32) : IO Int :=
  callback ptr (callbackSuspendOffset ()) signal

def callbackResume (ptr : USize) (signal : UInt32) : IO Int :=
  callback ptr (callbackResumeOffset ()) signal

partial def writeAll (fd : UInt32) (bytes : ByteArray) (offset : Nat := 0) : IO Unit := do
  if offset >= bytes.size then return
  let count ← write fd bytes offset.toUInt32
  if count == errorCode (Posix.EINTR ()) then writeAll fd bytes offset
  else if count > 0 then writeAll fd bytes (offset + count.toNat)

opaque HandlePointed : NonemptyType
def Handle : Type := HandlePointed.type
instance : Nonempty Handle := HandlePointed.property

@[extern "lean_pam_context"] opaque context
    (callback : UInt32 → USize → USize → BaseIO UInt32) : IO Handle
@[extern "lean_pam_start"] opaque start (fn : USize) (handle : @& Handle)
    (service user : @& String) : IO Int
@[extern "lean_pam_call"] opaque call (fn : USize) (handle : @& Handle) (flags : UInt32) : IO Int
@[extern "lean_pam_set_item"] opaque setItem (fn : USize) (handle : @& Handle)
    (item : UInt32) (value : @& String) : IO Int
@[extern "lean_pam_get_item"] opaque getItem (fn : USize) (handle : @& Handle)
    (item : UInt32) : IO (Int × Option ByteArray)
@[extern "lean_pam_environment"] opaque environment (fn : USize)
    (handle : @& Handle) : IO USize
@[extern "lean_pam_handle_pointer"] opaque handlePointer (handle : @& Handle) : IO USize
@[extern "lean_pam_strerror"] private opaque strerrorRaw (fn : USize) (handle : @& Handle)
    (code : UInt32) : IO USize

def strerror (fn : USize) (handle : Handle) (code : UInt32) : IO String := do
  let ptr ← strerrorRaw fn handle code
  if ptr == 0 then return "Unknown PAM error"
  return CoreLogs.decodeLossyUTF8 (← Store.bytes ptr.toUInt64)
@[extern "lean_pam_end"] opaque finish (fn : USize) (handle : @& Handle)
    (status : UInt32) : IO Int

end LeanSudo.Sys.Prim.Pam
