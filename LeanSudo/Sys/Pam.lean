namespace LeanSudo.Sys

opaque PamHandlePointed : NonemptyType

def PamHandle : Type := PamHandlePointed.type

instance : Nonempty PamHandle := PamHandlePointed.property

structure ConvConfig where
  useStdin : Bool := false
  nonInteractive : Bool := false
  visiblepw : Bool := false
  prompt : String := "Password: "
  override : Bool := false
  pwfeedback : Bool := false
  timeout : Nat := 0
  deriving Repr, Inhabited

@[extern "lean_sudo_pam_start"]
private opaque pamStartRaw (service : @& String) (user : @& String) (useStdin : Bool)
    (nonInteractive : Bool) (prompt : @& String) (override : Bool) (pwfeedback : Bool)
    (timeout : UInt32) (ruser : @& String) (tty : @& Option String) (visiblepw : Bool) : IO PamHandle

def pamStart (service : String) (user : String) (cfg : ConvConfig) (ruser : String)
    (tty : Option String) : IO PamHandle :=
  pamStartRaw service user cfg.useStdin cfg.nonInteractive cfg.prompt cfg.override
    cfg.pwfeedback (min cfg.timeout (UInt32.size - 1)).toUInt32 ruser tty cfg.visiblepw

@[extern "lean_sudo_pam_configure"]
opaque pamConfigure (h : @& PamHandle) (silent sessionSilent bell : Bool)
    (askpass rhost promptUser : @& String) : IO Unit

@[extern "lean_sudo_pam_lecture"] opaque pamLecture (h : @& PamHandle) (text : @& String) : IO Unit
@[extern "lean_sudo_pam_lectured"] opaque pamLectured (h : @& PamHandle) : IO Bool

@[extern "lean_sudo_pam_authenticate"] opaque pamAuthenticate (h : @& PamHandle) : IO Int
@[extern "lean_sudo_pam_acct_mgmt"] opaque pamAcctMgmt (h : @& PamHandle) : IO Int
@[extern "lean_sudo_pam_chauthtok"] opaque pamChauthtok (h : @& PamHandle) : IO Int
@[extern "lean_sudo_pam_setcred"] opaque pamSetcred (h : @& PamHandle) (establish : Bool) : IO Int
@[extern "lean_sudo_pam_open_session"] opaque pamOpenSession (h : @& PamHandle) : IO Int
@[extern "lean_sudo_pam_close_session"] opaque pamCloseSession (h : @& PamHandle) : IO Int
@[extern "lean_sudo_pam_set_user"] opaque pamSetUser (h : @& PamHandle) (user : @& String) : IO Int

@[extern "lean_sudo_pam_getenv"] private opaque pamGetEnvRaw (h : @& PamHandle) : IO (Array (String × String))

def pamGetEnv (h : PamHandle) : IO (List (String × String)) :=
  return (← pamGetEnvRaw h).toList

@[extern "lean_sudo_pam_strerror"] opaque pamStrerror (h : @& PamHandle) (code : @& Int) : IO String

@[extern "lean_sudo_pam_end"] opaque pamEnd (h : @& PamHandle) (status : @& Int) : IO Unit

@[extern "lean_sudo_pam_available"] opaque pamAvailable : IO Bool

@[extern "lean_sudo_pam_last_conv_error"] opaque pamLastConvError (h : @& PamHandle) : IO (Option String)

@[extern "lean_sudo_pam_interrupted"] opaque pamInterrupted (h : @& PamHandle) : IO UInt32

end LeanSudo.Sys
