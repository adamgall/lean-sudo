import LeanSudo.Sys.Core
import LeanSudo.Sys.Prim.Pam
import LeanSudo.Sys.Prim.Store
import LeanSudo.I18n.Load
import LeanSudo.Sys.FrontSignals

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

private def caughtSignals : List UInt32 :=
  [SIGHUP (), SIGINT (), SIGQUIT (), Prim.Exec.K.SIGALRM (), SIGTERM (), SIGTSTP (), SIGTTIN (),
    SIGTTOU ()]

private initialize ttySignalMask : IO.Ref (Option ByteArray) ← IO.mkRef none

private def ttySignals : IO ByteArray := do
  if let some mask ← ttySignalMask.get then return mask
  let mask ← signalMask caughtSignals
  ttySignalMask.set (some mask)
  return mask

private initialize suspendHooks : IO.Ref (IO Unit × IO Bool) ← IO.mkRef (pure (), pure true)

def withAuthSuspend (suspend : IO Unit) (resume : IO Bool) (action : IO α) : IO α := do
  let saved ← suspendHooks.get
  suspendHooks.set (suspend, resume)
  try action finally suspendHooks.set saved

private def catching (action : IO α) : IO (α × Array UInt32) := do
  let mut saved := #[]
  for signal in caughtSignals do
    let _ ← Prim.Pam.caught signal
    saved := saved.push (signal, ← Prim.Exec.signalAction signal (Prim.Pam.catchHandler ()))
  let result ← try
      let result ← action
      let (_, old) ← Prim.Pam.sigmask (SIG_UNBLOCK ()) (← ttySignals)
      let _ ← Prim.Pam.sigmask (SIG_SETMASK ()) old
      pure result
    finally
      for (signal, old) in saved do
        if old[0]! == 0 then
          discard <| Prim.Exec.signalAction signal old[1]!.toUSize old[2]!.toUInt32 old[3]!
  let caught ← caughtSignals.filterM Prim.Pam.caught
  return (result, caught.toArray.qsort (· < ·))

private def suspendFor (callback : USize) (plugin : Bool) (signo : UInt32) : IO Bool := do
  let (onSuspend, onResume) ← suspendHooks.get
  let before ← if callback != 0 then
      (· != -1) <$> Prim.Pam.callbackSuspend callback signo
    else onSuspend *> pure true
  if plugin && signo == SIGTSTP () then FrontSignals.mark signo else
    let forced := signo == SIGTSTP ()
    let old ← if forced then Prim.Exec.signalAction signo (Prim.Exec.defaultHandler ())
      else pure #[]
    let one ← signalMask [signo]
    let _ ← Prim.Pam.kill (← Prim.Exec.getpid) signo
    let _ ← Prim.Pam.sigmask (SIG_UNBLOCK ()) one
    let _ ← Prim.Pam.sigmask (SIG_BLOCK ()) one
    if forced && old[0]! == 0 then
      discard <| Prim.Exec.signalAction signo old[1]!.toUSize old[2]!.toUInt32 old[3]!
  let after ← if callback != 0 then (· != -1) <$> Prim.Pam.callbackResume callback signo
    else onResume
  return before && after

private def tell (useStdin info : Bool) (text : ByteArray) : IO Unit := do
  let fd ← if useStdin then pure (-1)
    else Prim.Pam.open "/dev/tty" (O_WRONLY () ||| O_NOCTTY () ||| O_CLOEXEC ())
  let fallback := if info then STDOUT_FILENO () else STDERR_FILENO ()
  try Prim.Pam.writeAll (if fd < 0 then fallback else fd.toNat.toUInt32) text
  finally if fd >= 0 then let _ ← Prim.Pam.close fd.toNat.toUInt32; pure ()

private initialize readErrno : IO.Ref UInt32 ← IO.mkRef 0

private def convErrorMessage (code : Int) : IO (Option String) := do
  let ssh ← IO.getEnv "SSH_CONNECTION"
  let tty ← IO.getEnv "SSH_TTY"
  let errno ← readErrno.get
  let reason ← if errno == 0 then pure "" else
    pure (": " ++ (← Prim.CoreLogs.strerror errno))
  return match code with
  | 1 => some "a password is required"
  | 2 => some (if ssh.isSome && tty.isNone then
      "a terminal is required to read the password; either use ssh's -t option or " ++
        "configure an askpass helper"
    else "a terminal is required to read the password; either use the -S option to " ++
      "read from standard input or configure an askpass helper")
  | 3 => some "timed out reading password"
  | 4 => some "no password was provided"
  | 5 => some ("unable to read password" ++ reason)
  | 6 => some "unable to allocate memory"
  | 7 => some "unsupported PAM conversation message"
  | 8 => some ""
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

private partial def setTerminal (fd action : UInt32) (attrs : ByteArray) : IO Int := do
  let result ← Prim.Pam.tcsetattr fd action attrs
  if result == errorCode (EINTR ()) then setTerminal fd action attrs else pure result

private def restoreTerminal (fd : UInt32) (saved : ByteArray) : IO Unit := do
  let result ← setTerminal fd (TCSADRAIN ()) saved
  if result == 0 then return
  let offset ← Prim.CoreLogs.seek fd 0 (SEEK_SET ())
  let error := if offset < 0 then offset else result
  writeStderr ("sudo: " ++ (← I18n.translate "unable to restore terminal settings" false) ++
    ": " ++ (← Prim.CoreLogs.strerror error.natAbs.toUInt32) ++ "\n")

private partial def writeNewline (fd : UInt32) : IO Bool := do
  let count ← Prim.Pam.write fd "\n".toUTF8 0
  if count == errorCode (EINTR ()) then writeNewline fd else pure (count == 1)

private partial def writeOnce (fd : UInt32) (bytes : ByteArray) : IO Int := do
  let count ← Prim.Pam.write fd bytes 0
  if count == errorCode (EINTR ()) then writeOnce fd bytes else pure count

private partial def abortSignalPending (fd : UInt32) (found : Bool := false) : IO Bool := do
  let (count, signo) ← Prim.Pam.readSignal fd
  if count == errorCode (EINTR ()) then return ← abortSignalPending fd found
  if count != Int.ofNat (signalInfoSize ()).toNat then return found
  FrontSignals.mark signo
  abortSignalPending fd true

private structure ReadState where
  input : UInt32
  output : UInt32
  unblock : ByteArray
  erase : UInt32
  kill : UInt32
  eof : UInt32
  feedback : Bool
  deadline : Nat

private def eraseFeedback (st : ReadState) (count : Nat) : IO Unit := do
  for _ in [:count] do
    if (← Prim.Pam.write st.output "\u0008 \u0008".toUTF8 0) != 3 then return

private partial def readLoop (st : ReadState) (bytes : ByteArray) :
    IO (Int × ByteArray) := do
  let now ← IO.monoMsNow
  if st.deadline != 0 && now >= st.deadline then return (3, bytes)
  let timeout := if st.deadline == 0 then invalidFd ()
    else (min (st.deadline - now) (INT_MAX ()).toNat).toUInt32
  let ready ← Prim.Pam.poll st.input timeout st.unblock
  if ready == errorCode (EINTR ()) then return (8, bytes)
  if ready < 0 then return (5, bytes)
  if ready == 0 then return (3, bytes)
  let (count, input) ← Prim.Pam.read st.input 1
  if count == errorCode (EINTR ()) || count == errorCode (EAGAIN ()) then
    return ← readLoop st bytes
  if count < 0 then
    readErrno.set count.natAbs.toUInt32
    return (5, bytes)
  let eof := fun (bytes : ByteArray) =>
    ((if bytes.isEmpty || bytes[0]! == 0 then 4 else 0 : Int), bytes)
  if count == 0 then return eof bytes
  let byte := input[0]!
  if byte == 10 || byte == 13 then return (0, bytes)
  if st.feedback then
    if byte.toUInt32 == st.eof then return eof bytes
    if byte.toUInt32 == st.kill then
      eraseFeedback st bytes.size
      return ← readLoop st ByteArray.empty
    if byte.toUInt32 == st.erase then
      if bytes.isEmpty then return ← readLoop st bytes
      eraseFeedback st 1
      return ← readLoop st (bytes.extract 0 (bytes.size - 1))
    Prim.Pam.writeAll st.output "*".toUTF8
  let bytes := bytes.push byte
  if bytes.size >= 1023 then return (0, bytes)
  readLoop st bytes

private def passwordLoop (st : ReadState) : IO (Int × ByteArray) := do
  let (error, bytes) ← readLoop st ByteArray.empty
  if st.feedback then eraseFeedback st bytes.size
  return (error, if error == 0 then bytes else ByteArray.empty)

private def readAttempt (st : Conversation) (prompt : ByteArray) (echo : Bool)
    (callback : USize) (plugin : Bool) : IO ((Int × ByteArray) × Bool) := do
  let own ← if st.cfg.useStdin then pure (-1)
    else Prim.Pam.open "/dev/tty" (O_RDWR () ||| O_NOCTTY () ||| O_CLOEXEC ())
  if !st.cfg.useStdin && own < 0 && !echo && !st.cfg.visiblepw then
    return ((2, ByteArray.empty), false)
  let input := if own < 0 then STDIN_FILENO () else own.toNat.toUInt32
  let output := if own < 0 then STDERR_FILENO () else own.toNat.toUInt32
  try
    let mask ← ttySignals
    let (error, oldmask) ← Prim.Pam.sigmask (SIG_BLOCK ()) mask
    if error != 0 then return ((5, ByteArray.empty), false)
    try
      let aborts ← Prim.Pam.signalfd
        (← signalMask [SIGINT (), SIGQUIT (), SIGHUP (), SIGTERM ()])
      if aborts < 0 then return ((5, ByteArray.empty), false)
      try
        let (error, saved) ← if echo then pure (-1, ByteArray.empty)
          else Prim.Pam.tcgetattr input
        let mut hidden := saved
        let mut noecho := false
        let feedback := st.cfg.pwfeedback && own >= 0
        if error == 0 then
          hidden ← termiosSetLflag hidden
            ((← termiosLflag hidden) &&& ~~~(ECHO () ||| ECHONL ()))
          if feedback then
            hidden ← termiosSetLflag hidden
              ((← termiosLflag hidden) &&& ~~~(ICANON () ||| IEXTEN ()))
            hidden ← termiosSetCC hidden (VMIN ()) 1
            hidden ← termiosSetCC hidden (VTIME ()) 0
          noecho := (← setTerminal input (TCSADRAIN ()) hidden) == 0
        if plugin && !echo && !noecho && !st.cfg.useStdin && !st.cfg.visiblepw then
          return ((5, ByteArray.empty), false)
        FrontSignals.collect
        let ((error, bytes, shown), caught) ← try
            catching do
              let bell ← if st.bell && own >= 0 then writeOnce output "\u0007".toUTF8 else pure 1
              let written ← if bell != 1 then pure (-1) else writeOnce output prompt
              if written < 0 then pure (9, ByteArray.empty, true) else do
                let deadline ← if st.cfg.timeout == 0 then pure 0
                  else pure ((← IO.monoMsNow) + st.cfg.timeout * 1000)
                let (error, bytes) ← passwordLoop {
                  input := input
                  output := output
                  unblock := mask
                  erase := ← if feedback && noecho then termiosCC saved (VERASE ()) else pure 0
                  kill := ← if feedback && noecho then termiosCC saved (VKILL ()) else pure 0
                  eof := ← if feedback && noecho then termiosCC saved (VEOF ()) else pure 0
                  feedback := feedback && noecho
                  deadline := deadline }
                let shown ← if noecho || error != 0 then writeNewline output else pure true
                pure (error, bytes, shown)
          catch e =>
            if noecho then let _ ← setTerminal input (TCSADRAIN ()) saved; pure ()
            throw e
        if noecho then restoreTerminal input saved
        let mut restart := false
        for signal in caught do
          if signal == SIGTSTP () || signal == SIGTTIN () || signal == SIGTTOU () then
            if ← suspendFor callback plugin signal then restart := true
          else if signal != Prim.Exec.K.SIGALRM () then FrontSignals.mark signal
        let _ ← abortSignalPending aborts.toNat.toUInt32
        let error := if error == 8 && caught.contains (Prim.Exec.K.SIGALRM ()) then 3 else error
        if error == 9 || (error != 0 && !shown) then return ((8, ByteArray.empty), restart)
        return ((error, bytes), restart)
      finally let _ ← Prim.Pam.close aborts.toNat.toUInt32; pure ()
    finally let _ ← Prim.Pam.sigmask (SIG_SETMASK ()) oldmask; pure ()
  finally if own >= 0 then let _ ← Prim.Pam.close own.toNat.toUInt32; pure ()

private partial def readPassword (st : Conversation) (prompt : ByteArray) (echo : Bool)
    (callback : USize := 0) (plugin : Bool := false) : IO (Int × ByteArray) := do
  readErrno.set 0
  if !st.askpass.isEmpty then
    let failure := "sudo: " ++ (← I18n.translate ("unable to run " ++ st.askpass) false)
    return ← PamHelpers.readAskpass st.askpass prompt st.uid st.gid st.groups
      (min st.cfg.timeout (UInt32.size - 1)).toUInt32 failure
  let (result, restart) ← readAttempt st prompt echo callback plugin
  if restart then readPassword st prompt echo callback plugin else return result

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
        tell st.cfg.useStdin false st.lecture.toUTF8
        state.modify fun s => { s with lectured := true }
      let prompt := pamSelectPrompt st.cfg st.user (text.getD ByteArray.empty)
        (← Prim.Pam.dgettext "Password:") (← Prim.Pam.dgettext "Password: ")
      let (error, bytes) ← readPassword st prompt
        (style == Int.ofNat (PAM_PROMPT_ECHO_ON ()).toNat)
      state.modify fun s => { s with error }
      if error != 0 then return (Int.ofNat (PAM_CONV_ERR ()).toNat, #[])
      if (bytes.data.toList.takeWhile (· != 0)).length >= (PAM_MAX_RESP_SIZE ()).toNat then
        return (Int.ofNat (PAM_CONV_ERR ()).toNat, #[])
      answers := answers.push (some bytes)
    else if style == Int.ofNat (PAM_ERROR_MSG ()).toNat ||
        style == Int.ofNat (PAM_TEXT_INFO ()).toNat then
      if let some text := text then
        tell (← state.get).cfg.useStdin (style == Int.ofNat (PAM_TEXT_INFO ()).toNat)
          (text.push 10)
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
  h.conversation.modify fun st => { st with error := 0 }
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

def pamTell (h : PamHandle) (text : String) : IO Unit := do
  tell (← h.conversation.get).cfg.useStdin false text.toUTF8

def pamSetGroups (groups : List Nat) : IO Unit := do
  try Prim.Exec.setgroups (groups.toArray.map Nat.toUInt32)
  catch _ => throw (IO.userError "unable to set supplementary group IDs")

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
    let (error, bytes) ← readPassword { st with cfg } prompt.toUTF8 echo callback true
    if error == 0 then return some bytes
    if let some text ← convErrorMessage error then
      if !text.isEmpty then writeStderr ("sudo: " ++ text ++ "\n")
    return none
  finally pluginReading.set false

end LeanSudo.Sys
