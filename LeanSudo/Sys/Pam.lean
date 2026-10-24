/-!
# `LeanSudo.Sys.Pam` — PAM via `dlopen("libpam.so.0")` (C side in `c/core.c`)

A `PamHandle` is an external object owning a C struct with the `pam_handle_t *` and C
copies of the conversation settings (the PAM conversation's `appdata_ptr` points to that
struct, never to Lean objects). Its finalizer calls `pam_end` unless `pamEnd` already did.

Flags used (as sudo does with its defaults): `pam_authenticate(PAM_SILENT)`,
`pam_acct_mgmt(PAM_SILENT)`, `pam_chauthtok(PAM_CHANGE_EXPIRED_AUTHTOK)`,
`pam_setcred(PAM_ESTABLISH_CRED)` / `pam_setcred(PAM_DELETE_CRED|PAM_SILENT)`,
`pam_open_session(0)`, `pam_close_session(PAM_SILENT)`.

Conversation:
* `PAM_PROMPT_ECHO_OFF`/`ECHO_ON`: with `nonInteractive` the conversation fails
  (`PAM_CONV_ERR`). With `useStdin` the prompt goes to stderr and a line is read from
  fd 0; otherwise `/dev/tty` is opened (failure ⇒ conversation error). For echo-off
  prompts echo is disabled while reading (restored on return and before any
  terminating/stopping signal is acted upon), with `pwfeedback` a `*` is printed per
  character and erase/kill characters are honoured; a newline is printed afterwards.
  `timeout > 0` bounds the wait for input. For echo-off prompts `prompt` replaces PAM's
  prompt when `override` is set or PAM's prompt starts with `Password`.
* `PAM_ERROR_MSG`/`PAM_TEXT_INFO`: written to stderr followed by a newline.
Why a conversation failed is available from `pamLastConvError`.
-/

namespace LeanSudo.Sys

opaque PamHandlePointed : NonemptyType

/-- An open PAM transaction (external object). -/
def PamHandle : Type := PamHandlePointed.type

instance : Nonempty PamHandle := PamHandlePointed.property

structure ConvConfig where
  /-- `-S`: read from stdin instead of /dev/tty -/
  useStdin : Bool := false
  /-- `-n`: any prompt fails the conversation -/
  nonInteractive : Bool := false
  /-- expanded passprompt; replaces PAM's "Password: " style prompts when
  `override` is true or the PAM prompt is the generic one -/
  prompt : String := "Password: "
  override : Bool := false
  pwfeedback : Bool := false
  /-- seconds, 0 = none -/
  timeout : Nat := 0
  deriving Repr, Inhabited

@[extern "lean_sudo_pam_start"]
private opaque pamStartRaw (service : @& String) (user : @& String) (useStdin : Bool)
    (nonInteractive : Bool) (prompt : @& String) (override : Bool) (pwfeedback : Bool)
    (timeout : UInt32) (ruser : @& String) (tty : @& Option String) : IO PamHandle

/-- `pam_start(service, user)` with our conversation, then sets `PAM_RUSER` to `ruser` and
`PAM_TTY` to `tty` (if given). Errors: `unable to initialize PAM: <pam_strerror>`, or
`unable to load libpam.so.0: …` when PAM is unavailable. -/
def pamStart (service : String) (user : String) (cfg : ConvConfig) (ruser : String)
    (tty : Option String) : IO PamHandle :=
  pamStartRaw service user cfg.useStdin cfg.nonInteractive cfg.prompt cfg.override
    cfg.pwfeedback (min cfg.timeout (UInt32.size - 1)).toUInt32 ruser tty

/-! Each of the following returns the raw PAM return code (0 = `PAM_SUCCESS`). They
throw only if the handle was already ended with `pamEnd`. -/

@[extern "lean_sudo_pam_authenticate"] opaque pamAuthenticate (h : @& PamHandle) : IO Int
@[extern "lean_sudo_pam_acct_mgmt"] opaque pamAcctMgmt (h : @& PamHandle) : IO Int
/-- `pam_chauthtok(PAM_CHANGE_EXPIRED_AUTHTOK)` -/
@[extern "lean_sudo_pam_chauthtok"] opaque pamChauthtok (h : @& PamHandle) : IO Int
/-- `establish = true`: `PAM_ESTABLISH_CRED`; `false`: `PAM_DELETE_CRED|PAM_SILENT`. -/
@[extern "lean_sudo_pam_setcred"] opaque pamSetcred (h : @& PamHandle) (establish : Bool) : IO Int
@[extern "lean_sudo_pam_open_session"] opaque pamOpenSession (h : @& PamHandle) : IO Int
@[extern "lean_sudo_pam_close_session"] opaque pamCloseSession (h : @& PamHandle) : IO Int
/-- `pam_set_item(PAM_USER, user)` (e.g. switch to the target user before
`pamSetcred`/`pamOpenSession`, as sudo does). Returns the raw PAM return code. -/
@[extern "lean_sudo_pam_set_user"] opaque pamSetUser (h : @& PamHandle) (user : @& String) : IO Int

@[extern "lean_sudo_pam_getenv"] private opaque pamGetEnvRaw (h : @& PamHandle) : IO (Array (String × String))

/-- `pam_getenvlist` as `(name, value)` pairs; entries without `=`, with an empty name
or not valid UTF-8 are dropped. -/
def pamGetEnv (h : PamHandle) : IO (List (String × String)) :=
  return (← pamGetEnvRaw h).toList

/-- `pam_strerror`. -/
@[extern "lean_sudo_pam_strerror"] opaque pamStrerror (h : @& PamHandle) (code : @& Int) : IO String

/-- `pam_end(h, status)`. Idempotent; after it every other call on `h` (except
`pamStrerror`/`pamLastConvError`) throws `PAM handle already ended`. -/
@[extern "lean_sudo_pam_end"] opaque pamEnd (h : @& PamHandle) (status : @& Int) : IO Unit

/-- Whether `libpam.so.0` could be loaded with all needed symbols. -/
@[extern "lean_sudo_pam_available"] opaque pamAvailable : IO Bool

/-- Why the conversation failed during the most recent `pamAuthenticate`/`pamAcctMgmt`/
`pamChauthtok`/`pamSetcred`/`pam*Session` call on `h` (reset at the start of each call).
`none` if it did not fail. Messages (without the `sudo: ` prefix):
* `a password is required` — a prompt arrived while `nonInteractive`
* `a terminal is required to read the password; either use the -S option to read from
  standard input or configure an askpass helper` — `/dev/tty` could not be opened
* `timed out reading password`
* `no password was provided` — end of input before any character
* `unable to read password`, `unable to allocate memory`,
  `unsupported PAM conversation message` -/
@[extern "lean_sudo_pam_last_conv_error"] opaque pamLastConvError (h : @& PamHandle) : IO (Option String)

end LeanSudo.Sys
