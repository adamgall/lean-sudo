import LeanSudo.Sys.Core
import LeanSudo.Sys.Prim.Pam
import LeanSudo.Sys.Prim.Store

namespace LeanSudo.Sys

open Prim.Posix Prim.Pam

private abbrev PamNative := Prim.Pam.Handle

structure ConvConfig where
  useStdin : Bool := false
  nonInteractive : Bool := false
  visiblepw : Bool := false
  prompt : String := "Password: "
  override : Bool := false
  pwfeedback : Bool := false
  timeout : Nat := 0
  deriving Repr, Inhabited

private structure Conversation where
  cfg : ConvConfig
  user : String
  bell : Bool := false
  askpass : String := ""
  uid : UInt32 := 0
  gid : UInt32 := 0
  groups : Array UInt32 := #[]
  lecture : String := ""
  lectured : Bool := false
  error : Int := 0
  interrupted : UInt32 := 0
  deriving Inhabited

private structure PamState where
  ended : Bool := false
  status : Int := 0
  silent : Bool := true
  sessionSilent : Bool := true
  deriving Inhabited

structure PamHandle where
  private native : PamNative
  private conversation : IO.Ref Conversation
  private functions : Array USize
  private user : String
  private state : IO.Ref PamState



private def signalMask (signals : List UInt32) : IO ByteArray := do
  let mut bytes ← Prim.Pam.sigemptyset
  for signal in signals do bytes ← Prim.Pam.sigaddset bytes signal
  return bytes

private initialize ttySignalMask : IO.Ref (Option ByteArray) ← IO.mkRef none

private def ttySignals : IO ByteArray := do
  if let some mask ← ttySignalMask.get then return mask
  let mask ← signalMask [SIGHUP (), SIGINT (), SIGQUIT (), SIGTERM (),
    SIGTSTP (), SIGTTIN (), SIGTTOU ()]
  ttySignalMask.set (some mask)
  return mask

private def tell (text : ByteArray) : IO Unit := do
  let fd ← Prim.Pam.open "/dev/tty" (O_WRONLY () ||| O_NOCTTY () ||| O_CLOEXEC ())
  try Prim.Pam.writeAll (if fd < 0 then STDERR_FILENO () else fd.toNat.toUInt32) text
  finally if fd >= 0 then let _ ← Prim.Pam.close fd.toNat.toUInt32; pure ()

private def convErrorMessage (code : Int) : IO (Option String) := do
  let ssh ← IO.getEnv "SSH_CONNECTION"
  let tty ← IO.getEnv "SSH_TTY"
  return match code with
  | 1 => some "a password is required"
  | 2 => some (if ssh.isSome && tty.isNone then
      "a terminal is required to read the password; either use ssh's -t option or " ++
        "configure an askpass helper"
    else "a terminal is required to read the password; either use the -S option to " ++
      "read from standard input or configure an askpass helper")
  | 3 => some "timed out reading password"
  | 4 => some "no password was provided"
  | 5 => some "unable to read password"
  | 6 => some "unable to allocate memory"
  | 7 => some "unsupported PAM conversation message"
  | _ => none

private def genericPrompt (prompt : ByteArray) : Bool :=
  prompt == "Password:".toUTF8 || prompt == "Password: ".toUTF8

def pamSelectPrompt (cfg : ConvConfig) (user : String)
    (prompt translated translatedSpace : ByteArray) : ByteArray :=
  if cfg.override || (!genericPrompt cfg.prompt.toUTF8 &&
      (genericPrompt prompt || prompt == translated || prompt == translatedSpace ||
        prompt == (user ++ "'s Password:").toUTF8 ||
        prompt == (user ++ "'s Password: ").toUTF8)) then cfg.prompt.toUTF8
  else prompt

theorem pamSelectPrompt_override (cfg : ConvConfig) (user : String)
    (prompt translated space : ByteArray) (h : cfg.override = true) :
    pamSelectPrompt cfg user prompt translated space = cfg.prompt.toUTF8 := by
  simp [pamSelectPrompt, h]

private def erasePassword (bytes : ByteArray) : ByteArray := Id.run do
  let mut size := bytes.size
  for _ in [:bytes.size] do
    if size > 0 && bytes[size - 1]! &&& 192 == 128 then size := size - 1
  return bytes.extract 0 (size - 1)

private partial def setTerminal (fd action : UInt32) (attrs : ByteArray) : IO Int := do
  let result ← Prim.Pam.tcsetattr fd action attrs
  if result == errorCode (EINTR ()) then setTerminal fd action attrs else pure result

private structure ReadState where
  input : UInt32
  output : UInt32
  signals : UInt32
  saved : ByteArray
  hidden : ByteArray
  erase : UInt32
  kill : UInt32
  eof : UInt32
  noecho : Bool
  feedback : Bool
  deadline : Nat
  callback : USize

private partial def passwordLoop (st : ReadState) (bytes : ByteArray := ByteArray.empty)
    (gotAny : Bool := false) : IO (Int × ByteArray × UInt32) := do
  let now ← IO.monoMsNow
  if st.deadline != 0 && now >= st.deadline then return (3, ByteArray.empty, 0)
  let timeout := if st.deadline == 0 then invalidFd ()
    else (min (st.deadline - now) (INT_MAX ()).toNat).toUInt32
  let ready ← Prim.Pam.poll st.input st.signals timeout
  if ready == errorCode (EINTR ()) then return ← passwordLoop st bytes gotAny
  if ready < 0 then return (5, ByteArray.empty, 0)
  if ready == 0 then return (3, ByteArray.empty, 0)
  if ready.toNat &&& 2 != 0 then
    let (count, signo) ← Prim.Pam.readSignal st.signals
    if count == errorCode (EAGAIN ()) || count == errorCode (EINTR ()) then
      return ← passwordLoop st bytes gotAny
    if count != Int.ofNat (signalInfoSize ()).toNat then return (5, ByteArray.empty, 0)
    if signo == SIGINT () || signo == SIGQUIT () then return (4, ByteArray.empty, signo)
    if st.noecho then let _ ← setTerminal st.input (TCSANOW ()) st.saved; pure ()
    let suspend := signo == SIGTSTP () || signo == SIGTTIN () || signo == SIGTTOU ()
    let before ← if suspend then Prim.Pam.callbackSuspend st.callback signo else pure 0
    let one ← signalMask [signo]
    let _ ← Prim.Pam.kill (← Prim.Pam.getpid) signo
    let _ ← Prim.Pam.sigmask (SIG_UNBLOCK ()) one
    let _ ← Prim.Pam.sigmask (SIG_BLOCK ()) one
    let after ← if suspend then Prim.Pam.callbackResume st.callback signo else pure 0
    if before == -1 || after == -1 then return (5, ByteArray.empty, 0)
    if st.noecho && (← setTerminal st.input (TCSANOW ()) st.hidden) != 0 then
      return (5, ByteArray.empty, 0)
    return ← passwordLoop st bytes gotAny
  let (count, input) ← Prim.Pam.read st.input 1
  if count == errorCode (EINTR ()) || count == errorCode (EAGAIN ()) then
    return ← passwordLoop st bytes gotAny
  if count < 0 then return (5, ByteArray.empty, 0)
  if count == 0 then return (if gotAny then 0 else 4, bytes, 0)
  let byte := input[0]!
  if byte == 10 || (st.feedback && byte == 13) then return (0, bytes, 0)
  if st.feedback then
    if byte.toUInt32 == st.erase || byte == 127 || byte == 8 then
      if !bytes.isEmpty then Prim.Pam.writeAll st.output "\u0008 \u0008".toUTF8
      return ← passwordLoop st (erasePassword bytes) true
    if byte.toUInt32 == st.kill then
      let mut remaining := bytes
      for _ in [:bytes.size] do
        if !remaining.isEmpty then
          remaining := erasePassword remaining
          Prim.Pam.writeAll st.output "\u0008 \u0008".toUTF8
      return ← passwordLoop st ByteArray.empty true
    if byte.toUInt32 == st.eof then
      return (if bytes.isEmpty then 4 else 0, bytes, 0)
  if bytes.size < 1023 then
    if st.feedback && byte &&& 192 != 128 then Prim.Pam.writeAll st.output "*".toUTF8
    return ← passwordLoop st (bytes.push byte) true
  passwordLoop st bytes true

private def readPassword (st : Conversation) (prompt : ByteArray) (echo : Bool)
    (callback : USize := 0) (plugin : Bool := false) : IO (Int × ByteArray × UInt32) := do
  if !st.askpass.isEmpty then
    let (error, bytes) ← PamHelpers.readAskpass st.askpass prompt st.uid st.gid st.groups
      (min st.cfg.timeout (UInt32.size - 1)).toUInt32
    return (error, bytes, 0)
  let own ← if st.cfg.useStdin then pure (-1)
    else Prim.Pam.open "/dev/tty" (O_RDWR () ||| O_NOCTTY () ||| O_CLOEXEC ())
  if !st.cfg.useStdin && own < 0 && !echo && !st.cfg.visiblepw then
    return (2, ByteArray.empty, 0)
  let input := if own < 0 then STDIN_FILENO () else own.toNat.toUInt32
  let output := if own < 0 then STDERR_FILENO () else own.toNat.toUInt32
  try
    let mask ← ttySignals
    let (error, oldmask) ← Prim.Pam.sigmask (SIG_BLOCK ()) mask
    if error != 0 then return (5, ByteArray.empty, 0)
    try
      let signals ← Prim.Pam.signalfd mask
      if signals < 0 then return (5, ByteArray.empty, 0)
      try
        let (error, saved) ← if echo then pure (-1, ByteArray.empty) else Prim.Pam.tcgetattr input
        let mut hidden := saved
        let mut noecho := false
        let feedback := st.cfg.pwfeedback && own >= 0
        if error == 0 then
          hidden ← termiosSetLflag hidden ((← termiosLflag hidden) &&& ~~~(ECHO () ||| ECHONL ()))
          if feedback then
            hidden ← termiosSetLflag hidden
              ((← termiosLflag hidden) &&& ~~~(ICANON () ||| IEXTEN ()))
            hidden ← termiosSetCC hidden (VMIN ()) 1
            hidden ← termiosSetCC hidden (VTIME ()) 0
          noecho := (← setTerminal input (TCSADRAIN ()) hidden) == 0
        if plugin && !echo && !noecho && !st.cfg.useStdin && !st.cfg.visiblepw then
          return (5, ByteArray.empty, 0)
        try
          if st.bell && own >= 0 then Prim.Pam.writeAll output "\u0007".toUTF8
          Prim.Pam.writeAll output prompt
          let deadline ← if st.cfg.timeout == 0 then pure 0
            else pure ((← IO.monoMsNow) + st.cfg.timeout * 1000)
          passwordLoop {
            input := input
            output := output
            signals := signals.toNat.toUInt32
            saved := saved
            hidden := hidden
            erase := ← if feedback && noecho then termiosCC saved (VERASE ()) else pure 0
            kill := ← if feedback && noecho then termiosCC saved (VKILL ()) else pure 0
            eof := ← if feedback && noecho then termiosCC saved (VEOF ()) else pure 0
            noecho := noecho
            feedback := feedback && noecho
            deadline := deadline
            callback := callback }
        finally
          if noecho then
            let _ ← setTerminal input (TCSADRAIN ()) saved
            Prim.Pam.writeAll output "\n".toUTF8
      finally let _ ← Prim.Pam.close signals.toNat.toUInt32; pure ()
    finally let _ ← Prim.Pam.sigmask (SIG_SETMASK ()) oldmask; pure ()
  finally if own >= 0 then let _ ← Prim.Pam.close own.toNat.toUInt32; pure ()

private def conversation (state : IO.Ref Conversation)
    (messages : Array (Int × Option ByteArray)) : IO (Int × Array (Option ByteArray)) := do
  let mut answers := #[]
  for (style, text) in messages do
    if style == Int.ofNat (PAM_PROMPT_ECHO_OFF ()).toNat ||
        style == Int.ofNat (PAM_PROMPT_ECHO_ON ()).toNat then
      let st ← state.get
      if st.cfg.nonInteractive then
        state.modify fun s => { s with error := 1 }
        return (Int.ofNat (PAM_CONV_ERR ()).toNat, #[])
      if !st.lecture.isEmpty && !st.lectured then
        tell st.lecture.toUTF8
        state.modify fun s => { s with lectured := true }
      let prompt := pamSelectPrompt st.cfg st.user (text.getD ByteArray.empty)
        (← Prim.Pam.dgettext "Password:") (← Prim.Pam.dgettext "Password: ")
      let (error, bytes, interrupted) ← readPassword st prompt
        (style == Int.ofNat (PAM_PROMPT_ECHO_ON ()).toNat)
      state.modify fun s => { s with error, interrupted }
      if error != 0 then return (Int.ofNat (PAM_CONV_ERR ()).toNat, #[])
      answers := answers.push (some bytes)
    else if style == Int.ofNat (PAM_ERROR_MSG ()).toNat ||
        style == Int.ofNat (PAM_TEXT_INFO ()).toNat then
      if let some text := text then tell (text.push 10)
      answers := answers.push none
    else
      state.modify fun s => { s with error := 7 }
      return (Int.ofNat (PAM_CONV_ERR ()).toNat, #[])
  return (Int.ofNat (PAM_SUCCESS ()).toNat, answers)

def pamMessageCountValid (count : Int) : Bool := 0 < count && count ≤ 32

theorem pamMessageCountValid_bounds (count : Int) (h : pamMessageCountValid count = true) :
    0 < count ∧ count ≤ 32 := by
  simpa [pamMessageCountValid] using h

private def conversationNative (state : IO.Ref Conversation) (count : UInt32)
    (messages answers : USize) : IO UInt32 := do
  if messages == 0 || answers == 0 || !pamMessageCountValid count.toInt32.toInt then
    return PAM_CONV_ERR ()
  Prim.Plugins.writePtr answers 0 0
  let size := (responseSize ()).toUSize
  let responses ← Prim.Plugins.alloc (count.toUSize * size)
  if responses == 0 then
    state.modify fun st => { st with error := 6 }
    return PAM_BUF_ERR ()
  let transferred ← IO.mkRef false
  try
    let mut input := #[]
    for i in [:count.toNat] do
      let message ← Prim.Plugins.readPtr messages (i.toUSize * Prim.Plugins.pointerSize ())
      if message == 0 then return PAM_CONV_ERR ()
      let style ← Prim.Plugins.readU32 message (messageTypeOffset ()).toUSize
      let text ← Prim.Plugins.readPtr message (messageTextOffset ()).toUSize
      let bytes ← if text == 0 then pure none
        else pure (some (← Prim.Store.bytes text.toUInt64))
      input := input.push (style.toInt32.toInt, bytes)
    let (status, output) ← conversation state input
    if status != Int.ofNat (PAM_SUCCESS ()).toNat then return status.toInt32.toUInt32
    for i in [:count.toNat] do
      if let some bytes := output[i]! then
        let text ← Prim.Plugins.dupBytes bytes
        if text == 0 then
          state.modify fun st => { st with error := 6 }
          return PAM_BUF_ERR ()
        Prim.Plugins.writePtr responses
          (i.toUSize * size + (responseTextOffset ()).toUSize) text
    Prim.Plugins.writePtr answers 0 responses
    transferred.set true
    return PAM_SUCCESS ()
  finally
    unless ← transferred.get do
      for i in [:count.toNat] do
        let text ← Prim.Plugins.readPtr responses
          (i.toUSize * size + (responseTextOffset ()).toUSize)
        if text != 0 then
          Prim.Plugins.erase text (← Prim.Plugins.length text)
          Prim.Plugins.free text
      Prim.Plugins.free responses

private def conversationTrampoline (state : IO.Ref Conversation) (count : UInt32)
    (messages answers : USize) : BaseIO UInt32 := do
  match ← (conversationNative state count messages answers).toBaseIO with
  | .ok status => return status
  | .error _ => return PAM_CONV_ERR ()

private initialize pamLibrary : IO.Ref (Option (Except String (Array USize))) ← IO.mkRef none

private def pamFunctions : IO (Array USize) := do
  if let some cached ← pamLibrary.get then
    return ← IO.ofExcept cached
  let result ← try
    let library ← Prim.Store.dlopen "libpam.so.0" (RTLD_NOW ())
    if library == 0 then
      throw (IO.userError ("unable to load libpam.so.0: " ++ (← Prim.Store.dlerror)))
    let mut functions := #[]
    for name in #["pam_start", "pam_end", "pam_authenticate", "pam_acct_mgmt",
        "pam_chauthtok", "pam_setcred", "pam_open_session", "pam_close_session",
        "pam_getenvlist", "pam_strerror", "pam_set_item", "pam_get_item"] do
      let function ← Prim.Store.dlsym library name
      if function == 0 then
        Prim.Store.dlclose library
        throw (IO.userError ("libpam.so.0: missing symbol " ++ name))
      functions := functions.push function.toUSize
    pure (.ok functions)
  catch e => pure (.error e.toString)
  pamLibrary.set (some result)
  IO.ofExcept result

private def checkString (text : String) : IO Unit :=
  if text.contains '\x00' then throw (IO.userError "argument contains a NUL byte") else pure ()

private def requirePam (h : PamHandle) : IO Unit := do
  if (← h.state.get).ended then throw (IO.userError "PAM handle already ended")

def pamStart (service : String) (user : String) (cfg : ConvConfig) (ruser : String)
    (tty : Option String) : IO PamHandle := do
  for text in #[service, user, cfg.prompt, ruser, tty.getD ""] do checkString text
  let functions ← pamFunctions
  let cfg := { cfg with timeout := min cfg.timeout (UInt32.size - 1) }
  let conversationState ← IO.mkRef { cfg, user := ruser : Conversation }
  let native ← Prim.Pam.context (conversationTrampoline conversationState)
  let state ← IO.mkRef ({} : PamState)
  let transferred ← IO.mkRef false
  try
    let status ← Prim.Pam.start functions[0]! native service user
    state.modify fun st => { st with status }
    if status != Int.ofNat (PAM_SUCCESS ()).toNat then
      let message ← Prim.Pam.strerror functions[9]! native status.toInt32.toUInt32
      throw (IO.userError ("unable to initialize PAM: " ++ message))
    if !ruser.isEmpty then
      let status ← Prim.Pam.setItem functions[10]! native (PAM_RUSER ()) ruser
      state.modify fun st => { st with status }
    if let some tty := tty then
      let status ← Prim.Pam.setItem functions[10]! native (PAM_TTY ()) tty
      state.modify fun st => { st with status }
    transferred.set true
    return { native, conversation := conversationState, functions, user, state }
  finally
    unless ← transferred.get do
      if (← Prim.Pam.handlePointer native) != 0 then
        let _ ← Prim.Pam.finish functions[1]! native (← state.get).status.toInt32.toUInt32
        pure ()

private def configureConversation (state : IO.Ref Conversation) (bell : Bool)
    (askpass user : String) : IO Unit := do
  if askpass.isEmpty then
    state.modify fun st => { st with bell, askpass, user }
  else
    let uid := (← getuid).toUInt32
    let gid := (← getgid).toUInt32
    let groups := (← getgroups).toArray.map Nat.toUInt32
    state.modify fun st => { st with bell, askpass, user, uid, gid, groups }

def pamConfigure (h : PamHandle) (silent sessionSilent bell : Bool)
    (askpass rhost promptUser : String) : IO Unit := do
  requirePam h
  for text in #[askpass, rhost, promptUser] do checkString text
  configureConversation h.conversation bell askpass promptUser
  h.state.modify fun st => { st with silent, sessionSilent }
  if !rhost.isEmpty then
    let _ ← Prim.Pam.setItem h.functions[10]! h.native (PAM_RHOST ()) rhost
    pure ()

def pamLecture (h : PamHandle) (text : String) : IO Unit := do
  requirePam h
  checkString text
  h.conversation.modify fun st => { st with lecture := text }

def pamLectured (h : PamHandle) : IO Bool := return (← h.conversation.get).lectured

def pamUserAccepted (expected : String) (status : Int) (actual : Option String) : Bool :=
  status == Int.ofNat (PAM_SUCCESS ()).toNat && actual == some expected

theorem pamUserAccepted_identity (expected : String) (status : Int) (actual : Option String)
    (h : pamUserAccepted expected status actual = true) : actual = some expected := by
  simp [pamUserAccepted] at h
  exact h.2

private def pamCall (h : PamHandle) (function : Nat) (flags : UInt32)
    (checkUser : Bool := false) : IO Int := do
  requirePam h
  h.conversation.modify fun st => { st with error := 0, interrupted := 0 }
  let mut status ← Prim.Pam.call h.functions[function]! h.native flags
  if status == Int.ofNat (PAM_SUCCESS ()).toNat && checkUser then
    let (code, user) ← Prim.Pam.getItem h.functions[11]! h.native (PAM_USER ())
    let user := user.bind String.fromUTF8?
    if !pamUserAccepted h.user code user then status := Int.ofNat (PAM_AUTH_ERR ()).toNat
  h.state.modify fun st => { st with status }
  return status

def pamAuthenticate (h : PamHandle) : IO Int := do
  pamCall h 2 (if (← h.state.get).silent then PAM_SILENT () else 0) true
def pamAcctMgmt (h : PamHandle) : IO Int := pamCall h 3 (PAM_SILENT ())
def pamChauthtok (h : PamHandle) : IO Int := pamCall h 4 (PAM_CHANGE_EXPIRED_AUTHTOK ())
def pamSetcred (h : PamHandle) (establish : Bool) : IO Int :=
  pamCall h 5 (if establish then PAM_REINITIALIZE_CRED () else PAM_DELETE_CRED () ||| PAM_SILENT ())
def pamOpenSession (h : PamHandle) : IO Int := do
  pamCall h 6 (if (← h.state.get).sessionSilent then PAM_SILENT () else 0)
def pamCloseSession (h : PamHandle) : IO Int := pamCall h 7 (PAM_SILENT ())

def pamSetUser (h : PamHandle) (user : String) : IO Int := do
  requirePam h
  checkString user
  let status ← Prim.Pam.setItem h.functions[10]! h.native (PAM_USER ()) user
  h.state.modify fun st => { st with status }
  return status

private partial def collectPamEnv (pointer : USize)
    (result : Array (String × String) := #[]) : IO (Array (String × String)) := do
  let entry ← Prim.Plugins.readPtr pointer 0
  if entry == 0 then return result
  let bytes ← try Prim.Store.bytes entry.toUInt64
    finally
      Prim.Plugins.erase entry (← Prim.Plugins.length entry)
      Prim.Plugins.free entry
      Prim.Plugins.writePtr pointer 0 0
  let mut result := result
  if let some text := String.fromUTF8? bytes then
    let parts := text.splitOn "="
    if let name :: value :: rest := parts then
      if !name.isEmpty then result := result.push (name, String.intercalate "=" (value :: rest))
  collectPamEnv (pointer + Prim.Plugins.pointerSize ()) result

def pamGetEnv (h : PamHandle) : IO (List (String × String)) := do
  requirePam h
  let pointer ← Prim.Pam.environment h.functions[8]! h.native
  if pointer == 0 then return []
  try return (← collectPamEnv pointer).toList
  finally Prim.Plugins.free pointer

private def validPamStatus (status : Int) : Bool :=
  (INT_MIN ()).toInt32.toInt ≤ status && status ≤ Int.ofNat (INT_MAX ()).toNat

def pamStrerror (h : PamHandle) (code : Int) : IO String := do
  if !validPamStatus code then return "Unknown PAM error"
  Prim.Pam.strerror h.functions[9]! h.native code.toInt32.toUInt32

def pamEnd (h : PamHandle) (status : Int) : IO Unit := do
  let st ← h.state.get
  if st.ended then return
  let status := if validPamStatus status then status else st.status
  let _ ← Prim.Pam.finish h.functions[1]! h.native status.toInt32.toUInt32
  h.state.modify fun st => { st with ended := true }

def pamAvailable : IO Bool := do
  try let _ ← pamFunctions; pure true catch _ => pure false

def pamLastConvError (h : PamHandle) : IO (Option String) := do
  convErrorMessage (← h.conversation.get).error

def pamInterrupted (h : PamHandle) : IO UInt32 := return (← h.conversation.get).interrupted

private initialize pluginConversation : IO.Ref Conversation ←
  IO.mkRef { cfg := {}, user := "" }
private initialize pluginReading : IO.Ref Bool ← IO.mkRef false

def pluginConfigureConversation (bell : Bool) (askpass : String) : IO Unit := do
  checkString askpass
  configureConversation pluginConversation bell askpass ""

def pluginReadReply (prompt : String) (msgType timeout : UInt32) (useStdin : Bool)
    (callback : USize) : IO (Option ByteArray) := do
  if ← pluginReading.get then return none
  pluginReading.set true
  try
    let st ← pluginConversation.get
    let cfg := { st.cfg with
      useStdin := useStdin
      timeout := timeout.toNat
      pwfeedback := msgType &&& SUDO_CONV_TYPE_MASK () == SUDO_CONV_PROMPT_MASK ()
      visiblepw := msgType &&& SUDO_CONV_PROMPT_ECHO_OK () != 0 }
    let echo := msgType &&& SUDO_CONV_TYPE_MASK () == SUDO_CONV_PROMPT_ECHO_ON ()
    let (error, bytes, _) ← readPassword { st with cfg } prompt.toUTF8 echo callback true
    if error == 0 then return some bytes
    if let some text ← convErrorMessage error then writeStderr ("sudo: " ++ text ++ "\n")
    return none
  finally pluginReading.set false

end LeanSudo.Sys
