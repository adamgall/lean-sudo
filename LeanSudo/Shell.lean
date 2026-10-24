import LeanSudo.Core
import LeanSudo.Sudoedit
import LeanSudo.Sudoers.Load
import LeanSudo.Policy.Defaults
import LeanSudo.Prompt
import LeanSudo.Sys.Core
import LeanSudo.Sys.Pam
import LeanSudo.Sys.Exec
import LeanSudo.Sys.Timestamp
import LeanSudo.Sys.Extra
import LeanSudo.SudoConf
import LeanSudo.Util.Sha2
import LeanSudo.Insults
import LeanSudo.EventLog
import LeanSudo.Sys.IoLog

/-! Linux IO boundary: collect facts, execute the verified decision, and bracket PAM
resources. Policy decisions belong to `Core.decide`, not this module. -/
namespace LeanSudo.Shell

private def warn (msg : String) : IO Unit := Sys.writeStderr ("sudo: " ++ msg ++ "\n")

private def fromExcept (x : Except String α) : IO α :=
  match x with
  | .ok a => pure a
  | .error e => throw (IO.userError e)

private def groupNames (gids : List Nat) : IO (List (String × Nat)) :=
  gids.eraseDups.mapM fun gid => do
    let g ← Sys.getgrgid gid
    return (g.map (·.name) |>.getD ("#" ++ toString gid), gid)

private def principal (pw : Sys.Passwd) (gids : List Nat) : IO Principal := do
  return {
    name := pw.name, uid := pw.uid, gid := pw.gid
    groups := ← groupNames (pw.gid :: gids), home := pw.home, shell := pw.shell }

private def user (name : String) : IO Principal := do
  let pw ← if name.startsWith "#" then
      match (name.drop 1).toString.toNat? with
      | some uid => Sys.getpwuid uid
      | none => pure none
    else Sys.getpwnam name
  let some pw := pw | throw (IO.userError ("unknown user " ++ name))
  principal pw (← Sys.getgrouplist pw.name pw.gid)

private def group (name : String) : IO GroupInfo := do
  let g ← if name.startsWith "#" then
      match (name.drop 1).toString.toNat? with
      | some gid => Sys.getgrgid gid
      | none => pure none
    else Sys.getgrnam name
  let some g := g | throw (IO.userError ("unknown group " ++ name))
  return g

private def absolute (cwd path : String) : String :=
  if path.startsWith "/" then path else cwd ++ "/" ++ path

private def executable (path : String) : IO Bool := do
  let some st ← Sys.stat path | return false
  return st.isReg && (← Sys.access path 1)

private def resolvePath (cwd search name : String) : IO (Option String) := do
  if name.contains '/' then
    let path := absolute cwd name
    return if ← executable path then some path else none
  for dir in search.splitOn ":" do
    if dir != "" && dir != "." then
      let path := absolute cwd (dir ++ "/" ++ name)
      if ← executable path then return some path
  return none

private def resolveCommand (opts : Cli.Options) (invoking target : Principal)
    (env : EnvList) (cwd : String) (st : Settings) : IO (Option Core.ResolvedCmd) := do
  if opts.mode != .run && opts.mode != .list then return none
  let search := st.securePath.getD ((env.lookup "PATH").getD "/usr/bin:/bin")
  let (name, argv) := if opts.shell || opts.login then
      let shell := Cli.userShell (if opts.login then none else env.lookup "SHELL")
        (if opts.login then target.shell else invoking.shell)
      let cmd := Cli.shellCommand shell opts.login opts.command
      (cmd.path, cmd.argv)
    else (opts.command.headD "", opts.command)
  if name.isEmpty then return none
  let some path ← resolvePath cwd search name | return none
  return some {
    path, canonical := (← Sys.realpath (Policy.dirOf path)).getD (Policy.dirOf path) ++ "/" ++ Policy.baseOf path
    argv0 := argv.headD name, args := argv.drop 1 }

private def atomPaths : Sudoers.CmndAtom → List String
  | .command path _ => [path]
  | .digest _ atom => atomPaths atom
  | _ => []

private def commandAtoms : Sudoers.Entry → List Sudoers.CmndAtom
  | .cmndAlias _ ms => ms.map (·.atom)
  | .defaults (.cmnd ms) _ => ms.map (·.atom)
  | .userSpec us => us.entries.flatMap (fun h => h.cmnds.map (·.cmnd.atom))
  | _ => []

private def userNetgroups (ms : List (Sudoers.Member Sudoers.UserAtom)) : List String :=
  ms.filterMap fun m => match m.atom with | .netgroup n => some n | _ => none

private def hostNetgroups (ms : List (Sudoers.Member Sudoers.HostAtom)) : List String :=
  ms.filterMap fun m => match m.atom with | .netgroup n => some n | _ => none

private def netgroupNames : Sudoers.Entry → List String
  | .userAlias _ ms | .runasAlias _ ms => userNetgroups ms
  | .hostAlias _ ms => hostNetgroups ms
  | .defaults (.user ms) _ | .defaults (.runas ms) _ => userNetgroups ms
  | .defaults (.host ms) _ => hostNetgroups ms
  | .userSpec us => userNetgroups us.users ++ us.entries.flatMap (fun h =>
      hostNetgroups h.hosts ++ h.cmnds.flatMap (fun c =>
        c.runas.toList.flatMap (fun r => userNetgroups (r.users.getD []))))
  | _ => []

private def regexPatterns : Sudoers.CmndAtom → List String
  | .commandRegex re a => re :: (match a with | .regex r => [r] | _ => [])
  | .command _ a | .sudoedit a => match a with | .regex r => [r] | _ => []
  | .digest _ a => regexPatterns a
  | _ => []

private def digestAlgos : Sudoers.CmndAtom → List Sudoers.DigestAlgo
  | .digest ds a => ds.map (·.algo) ++ digestAlgos a
  | _ => []

private def ttyFor (device : Option Nat) (search : String) : IO (Option String) := do
  let some device := device | return none
  for fd in [0, 1, 2] do
    if let some name ← Sys.ttyname fd then
      if let some st ← Sys.stat name then
        if st.rdev == device then return some name
  for dir in search.splitOn ":" do
    let names ← try Sys.listDir dir catch _ => pure []
    for name in names do
      let path := dir ++ "/" ++ name
      if let some st ← Sys.lstat path then
        if st.mode / 4096 == 2 && st.rdev == device then return some path
  return none

private def readEnvFile (path : Option String) : IO EnvList := do
  let some path := path | return []
  if (← Sys.stat path).isNone then return []
  let (_, text) ← Sys.readFileFollow path
  return (text.splitOn "\n").filterMap fun line => Id.run do
    let line := line.trimAscii.toString
    let line := if line.startsWith "export " then (line.drop 7).toString.trimAscii.toString else line
    if line.startsWith "#" then return none
    let parts := line.splitOn "="
    if parts.length < 2 then return none
    let key := (parts.headD "").trimAscii.toString
    if key.isEmpty || key.any (fun c => !(c.isAlphanum || c == '_')) then return none
    let value := ("=".intercalate (parts.drop 1)).trimAscii.toString
    let value := if (value.startsWith "\"" && value.endsWith "\"") ||
        (value.startsWith "'" && value.endsWith "'") then
        (value.drop 1).toString.dropEnd 1 |>.toString else value
    return some (key, value)

private def gatherFacts (policy : Sudoers.Sudoers) (r : Request)
    (otherUsers : List String := []) : IO Request := do
  let atoms := policy.flatMap commandAtoms
  let paths := (atoms.flatMap atomPaths).eraseDups
  let globPaths ← (paths.filter Glob.hasGlob).mapM fun p => return (p, ← Sys.globPaths p)
  let expanded := paths ++ globPaths.flatMap (·.2)
  let requested := match r.command with | .run p _ _ => [p] | _ => []
  let names := expanded ++ (expanded.filter (·.endsWith "/")).flatMap
    (fun dir => requested.map (fun p => dir ++ Policy.baseOf p)) ++ requested
  let names := (names ++ names.map Policy.dirOf).eraseDups
  let table ← names.mapM fun p => return (p, (← Sys.realpath p).getD p)
  let canon := fun p => (table.lookup p).getD p
  let fileIds ← names.filterMapM fun p => do
    return (← Sys.stat p).map (fun s => (p, s.dev, s.ino))
  let subjects := match r.command with
    | .run p _ args => [p, canon (Policy.dirOf p) ++ "/" ++ Policy.baseOf p, " ".intercalate args]
    | .sudoedit args => [" ".intercalate args]
    | _ => []
  let regexMatches ← ((atoms.flatMap regexPatterns).eraseDups.flatMap
    (fun p => subjects.map (p, ·))).mapM fun (p, s) => return (p, s, ← Sys.regexMatches p s)
  let users := ([none, some r.user.name, some r.runasUser.name, some "root"] ++
    otherUsers.map some).eraseDups
  let hosts := [none, some r.lhost, some r.host]
  let queries := (policy.flatMap netgroupNames).eraseDups.flatMap fun n =>
    users.flatMap fun u => hosts.map fun h => (n, u, h)
  let domain ← Sys.domainName
  let netgroups ← queries.mapM fun (n, u, h) => return (n, u, h, ← Sys.inNetgroup n h u domain)
  return { r with canon, fileIds, globPaths, regexMatches, netgroups }

private def defaults (policy : Sudoers.Sudoers) (invoking : Principal) (host : String)
    (runas : Option Principal) (cmd : Option Command) (facts : Request)
    (emitWarnings : Bool := false) : IO Settings := do
  let (settings, warnings) ← fromExcept
    (Policy.resolveDefaults policy invoking host runas cmd facts.canon (some facts))
  if emitWarnings then for warning in warnings do warn warning
  return settings

private def context (progname : String) (opts : Cli.Options) (conf : SudoConf.Config) : IO Core.Context := do
  let uid ← Sys.getuid
  let some pw ← Sys.getpwuid uid | throw (IO.userError "you do not exist in the passwd database")
  let kernelGroups ← Sys.getgroups
  let gids ← if conf.groupSource == "dynamic" ||
      (conf.groupSource == "adaptive" && kernelGroups.length >= conf.maxGroups) then
      Sys.getgrouplist pw.name pw.gid else pure kernelGroups
  let invoking ← principal pw gids
  let rawHost ← Sys.gethostname
  let canonicalHost := (← Sys.canonicalHostname rawHost).getD rawHost
  let longHost := opts.host.getD canonicalHost
  let host := (longHost.splitOn ".").headD "localhost"
  let cwd ← Sys.getcwd
  let mask ← Sys.umask 0
  let _ ← Sys.umask mask
  let ttyDevice ← Sys.ttyDevice
  let ttyName ← ttyFor ttyDevice conf.devsearch
  let userEnv ← Sys.environ
  let locatedSudoers ← Sudoers.load host
  let policy := locatedSudoers.map (·.entry)
  let _ ← fromExcept (Policy.validate policy)
  let addresses ← if conf.probeInterfaces then Sys.interfaceAddresses else pure #[]
  let interfaces := addresses.toList.filterMap fun (a, m) =>
    (Sudoers.Parser.ipAddress a).bind fun ip =>
      (Sudoers.Parser.ipAddress m).map fun mask => (ip, mask)
  let wallTime ← Sys.unixTime
  let utcOffset ← Sys.utcOffset
  let base : Request := {
    user := invoking, host, lhost := longHost, interfaces
    runasUser := invoking, runasGroup := none, runasUserExplicit := opts.user.isSome
    command := .list, now := wallTime, utcOffset }
  let preliminary ← gatherFacts policy base
  let initial ← defaults policy invoking host none none preliminary
  let longHost := opts.host.getD (if initial.fqdn then canonicalHost else rawHost)
  let host := (longHost.splitOn ".").headD "localhost"
  let target ← user (opts.user.getD (if opts.group.isSome then invoking.name else initial.runasDefault))
  let targetGroup ← opts.group.mapM group
  let listUser ← opts.otherUser.mapM user
  let command ← resolveCommand opts invoking target userEnv cwd initial
  let policyCommand := if opts.mode == .edit then some (.sudoedit opts.command) else
    command.map (fun c => .run c.path c.canonical
      (if opts.shell || opts.login then opts.command else c.args))
  let facts ← gatherFacts policy { base with
    host := host
    lhost := longHost
    runasUser := target
    runasGroup := targetGroup
    command := policyCommand.getD .list } (listUser.toList.map (·.name))
  let algos := ((policy.flatMap commandAtoms).flatMap digestAlgos).eraseDups
  let beforeDigest ← defaults policy invoking host (some target) policyCommand facts
  let pinned ← match command with
    | some c => do
      if algos.isEmpty && beforeDigest.fdexec != "always" then pure none
      else pure (some (← Sys.openCommand c.canonical))
    | none => pure none
  let execFd := pinned.map (·.1)
  let digests ← if algos.isEmpty then pure [] else
    match execFd with
    | some fd => do
      let bytes ← IO.FS.readBinFile s!"/proc/self/fd/{fd}"
      pure (algos.map fun algo => { algo, bytes := (Sha2.digest algo bytes).data.toList : Sudoers.Digest })
    | none => pure []
  let fileIds := match pinned, command with
    | some (_, s), some c => (c.path, s.dev, s.ino) :: facts.fileIds.filter (·.1 != c.path)
    | _, _ => facts.fileIds
  let facts := { facts with digests, fileIds }
  let settings ← defaults policy invoking host (some target) policyCommand facts true
  let settings := { settings with noexecFile := some ((settings.noexecFile.or conf.noexec).getD "") }
  let sid ← Sys.getsid
  let ppid ← Sys.getppid
  let sidStart ← Sys.processStartTime sid
  let ppidStart ← Sys.processStartTime ppid
  if sidStart.isNone || ppidStart.isNone then
    throw (IO.userError "unable to determine timestamp process identity")
  let tsScope := Timestamp.scopeFor settings.timestampType ttyDevice
    sid (sidStart.getD 0) ppid (ppidStart.getD 0)
  let tsRecords ← try
      Sys.withTimestampFile uid (fun bytes => pure (none, Timestamp.load bytes))
    catch _ => pure []
  let homeNames := policy.flatMap fun e => match e with
    | .userSpec us => us.entries.flatMap fun h => h.cmnds.filterMap fun c =>
      (c.options.cwd.bind id).filter (·.startsWith "~") |>.map
        (fun p => ((p.drop 1).toString.splitOn "/").headD "")
    | _ => []
  let homes ← homeNames.eraseDups.filterMapM fun n => do
    return (← Sys.getpwnam n).map (fun pw => (n, pw.home))
  let previousUser ← if uid == 0 then
      match userEnv.lookup "SUDO_USER" with
      | some name => do
        if name == "root" then pure none
        else try pure (some (← user name)) catch _ => pure none
      | none => pure none
    else pure none
  return {
    progname, opts, invoking, host, longHost, sudoers := policy, locatedSudoers, settings, target
    targetGroup, listUser, command, userEnv, cwd, userUmask := mask.toNat
    ttyName, canon := facts.canon, now := ← Sys.bootTimeNanos, tsScope, tsRecords
    interfaces, netgroups := facts.netgroups, regexMatches := facts.regexMatches,
    digests, wallTime, utcOffset, fileIds, globPaths := facts.globPaths, execFd, homes
    envFile := ← readEnvFile settings.envFile, restrictedEnvFile := ← readEnvFile settings.restrictedEnvFile
    selinuxEnabled := (← Sys.stat "/sys/fs/selinux/enforce").isSome
    root := ← user "root"
    listColumns := ← Sys.terminalColumns 1
    previousUser
    mailerAvailable := ← match settings.mailerpath with | some p => executable p | none => pure false }

private def logLine (ctx : Core.Context) (line : Core.LogLine) : IO Unit := do
  let name := (ctx.previousUser.getD ctx.invoking).name
  let body := EventLog.messageBody name line.msg
  if line.priority != "none" then
    if let some facility := ctx.settings.syslog then
      for bytes in EventLog.splitSyslogBytes name body ctx.settings.syslogMaxlen do
        Sys.syslogBytes facility line.priority bytes ctx.settings.syslogPid
  if let some path := ctx.settings.logfile then
    try
      Sys.appendLog path (EventLog.formatFile (← Sys.logTime ctx.settings.logYear)
        ctx.longHost name body ctx.settings.logHost ctx.settings.loglinelen)
    catch e =>
      if ctx.settings.ignoreLogfileErrors then warn e.toString else throw e

private def mail (ctx : Core.Context) (line : Core.LogLine) : IO Unit := do
  if !ctx.mailerAvailable then return
  let some path := ctx.settings.mailerpath | return
  let some recipient := ctx.settings.mailto | return
  let name := (ctx.previousUser.getD ctx.invoking).name
  let sender := ctx.settings.mailfrom.getD name
  let subject := (ctx.settings.mailsub.replace "%h" ctx.longHost).replace "%u" name
  for field in [recipient, sender, subject] do
    if field.contains '\n' || field.contains '\r' then
      throw (IO.userError "invalid newline in mail header")
  let body := EventLog.messageBody name line.msg
  let text := s!"To: {recipient}\nFrom: {sender}\nAuto-Submitted: auto-generated\nSubject: {subject}\n\n" ++
    s!"{ctx.longHost} : {← Sys.logTime ctx.settings.logYear} : {name} : {body}\n\n"
  let flags := (ctx.settings.mailerflags.getD "").splitOn " " |>.flatMap (·.splitOn "\t") |>.filter (!·.isEmpty)
  Sys.sendMail path flags.toArray text

private def lecture (ctx : Core.Context) : IO String := do
  if ctx.settings.lecture == "never" || ctx.opts.nonInteractive then return ""
  if ctx.settings.lecture == "once" then
    let seen ← try Sys.stateMarker ctx.settings.lectureStatusDir ctx.invoking.uid false
      catch _ => pure false
    if seen then return ""
  if let some file := ctx.settings.lectureFile then
    try
      let (_, text) ← Sys.readFileFollow file
      return text
    catch _ => pure ()
  return "\nWe trust you have received the usual lecture from the local System\n" ++
    "Administrator. It usually boils down to these three things:\n\n" ++
    "    #1) Respect the privacy of others.\n" ++
    "    #2) Think before you type.\n" ++
    "    #3) With great power comes great responsibility.\n\n" ++
    (if ctx.settings.pwfeedback then "" else
      "For security reasons, the password you type will not be visible.\n\n")

private def authenticate (ctx : Core.Context) (h : Sys.PamHandle) : IO (Option String) := do
  for attempt in List.range ctx.settings.passwdTries do
    let rc ← Sys.pamAuthenticate h
    if rc == 0 then return none
    if let some err ← Sys.pamLastConvError h then
      warn err
      if err.startsWith "a terminal is required" then warn "a password is required"
      return some (if ctx.opts.nonInteractive then "a password is required" else err)
    if ![6, 7, 9, 11].contains rc then
      let err := "PAM authentication error: " ++ (← Sys.pamStrerror h rc)
      warn err
      return some err
    if attempt + 1 < ctx.settings.passwdTries then
      let seed ← Sys.bootTimeNanos
      let message := if ctx.settings.insults then
        Insults.select seed else ctx.settings.badpassMessage
      Sys.writeStderr (message ++ "\n")
  let n := ctx.settings.passwdTries
  let message := s!"{n} incorrect password attempt{if n == 1 then "" else "s"}"
  warn (Core.authFailureMessage ctx n)
  return some message

private def checkPam (h : Sys.PamHandle) (operation : String) (result : IO Int) : IO Unit := do
  let rc ← result
  if rc != 0 then throw (IO.userError (operation ++ ": " ++ (← Sys.pamStrerror h rc)))

private def account (ctx : Core.Context) (h : Sys.PamHandle) : IO Unit := do
  if !ctx.settings.pamAcctMgmt then return
  let rc ← Sys.pamAcctMgmt h
  let exempt := !ctx.settings.authenticate || ctx.settings.exemptGroup.any fun group =>
    ctx.invoking.groups.any fun g => if ctx.settings.caseInsensitiveGroup then
      g.1.toLower == group.toLower else g.1 == group
  if exempt && (rc == 12 || rc == 27) then return
  match rc with
  | 0 => pure ()
  | 7 => throw (IO.userError "account validation failure, is your account locked?")
  | 12 =>
    warn "Account or password is expired, reset your password and try again"
    checkPam h "unable to change expired password" (Sys.pamChauthtok h)
  | 27 => throw (IO.userError "Password expired, contact your system administrator")
  | 13 => throw (IO.userError "Account expired or PAM config lacks an \"account\" section for sudo, contact your system administrator")
  | _ => throw (IO.userError ("PAM account management error: " ++ (← Sys.pamStrerror h rc)))

-- Cleanup must preserve the command's status, even if reporting the warning fails.
private def cleanup (action : IO Unit) : IO Unit := do
  try action
  catch e =>
    try warn e.toString
    catch _ => pure ()

private def environment (input : EnvInput) (h : Sys.PamHandle) : IO (Array String) := do
  let pamEnv ← Sys.pamGetEnv h
  return envToArray (← fromExcept (buildEnv { input with pamEnv }))

private def session (ctx : Core.Context) (h : Sys.PamHandle) (setcred openSession : Bool)
    (run : IO Sys.ExitStatus) : IO Sys.ExitStatus := do
  let _ ← Sys.pamSetUser h ctx.target.name
  let credentials ← if setcred then do pure ((← Sys.pamSetcred h true) == 0) else pure false
  try
    let opened ← if openSession then do
        let rc ← Sys.pamOpenSession h
        if rc != 0 && rc != 14 then
          throw (IO.userError ("pam_open_session: " ++ (← Sys.pamStrerror h rc)))
        pure (rc == 0)
      else pure false
    try run
    finally
      if opened then cleanup (checkPam h "unable to close session" (Sys.pamCloseSession h))
  finally
    if credentials then cleanup (checkPam h "unable to delete credentials" (Sys.pamSetcred h false))

private def executeAction (ctx : Core.Context) (decision : Core.Decision)
    (h : Option Sys.PamHandle) : IO Sys.ExitStatus := do
  if let some line := decision.log then logLine ctx line
  if decision.mail then mail ctx (decision.log.getD (Core.logLine ctx none))
  if let some path := decision.adminFlag then
    cleanup (Sys.createAdminFlag path ctx.invoking.uid ctx.invoking.gid (ctx.invoking.groups.map (·.2)))
  match decision.action with
  | .exec plan =>
    let some h := h | throw (IO.userError "missing PAM transaction")
    session ctx h plan.pamSetcred plan.pamSession do
      if !(← Sys.auditCommand (Core.commandText ctx) (ctx.ttyName.getD "unknown") true) &&
          !ctx.settings.ignoreAuditErrors then
        throw (IO.userError "unable to send audit message")
      if let some iolog := plan.iolog then
        let group := (ctx.invoking.groups.find? (·.2 == ctx.invoking.gid)).map (·.1) |>.getD ""
        let runasGroup := (← Sys.getgrgid plan.gid).map (·.name) |>.getD ("#" ++ toString plan.gid)
        Sys.IoLog.open iolog {
          user := ctx.invoking.name, group, runasUser := ctx.target.name, runasGroup
          hostname := ctx.longHost, command := plan.path, cwd := ctx.cwd
          tty := ctx.ttyName.getD "unknown", argv := plan.argv.toArray }
      Sys.runCommand {
        path := plan.path, argv := plan.argv.toArray
        env := ← environment plan.envInput h, uid := plan.uid, gid := plan.gid
        groups := plan.groups.toArray, cwd := plan.cwd, umask := plan.umask
        usePty := plan.usePty, background := plan.background, closeFrom := plan.closeFrom
        cwdOptional := plan.cwdOptional, timeout := plan.timeout, noexecFile := plan.noexecFile
        apparmorProfile := plan.apparmorProfile, rlimits := plan.rlimits.toArray,
        utmpUser := plan.utmpUser, execFd := plan.execFd, execBackground := plan.execBackground }
  | .edit plan =>
    let some h := h | throw (IO.userError "missing PAM transaction")
    session ctx h plan.pamSetcred plan.pamSession do
      Sudoedit.run plan (← environment plan.envInput h)
  | .print text code =>
    (← IO.getStdout).putStr text
    return .exited code.toNat
  | .fail text code =>
    Sys.writeStderr text
    return .exited code.toNat
  | .validate => return .exited 0
  | .resetTimestamp =>
    Sys.withTimestampFile ctx.invoking.uid fun bytes =>
      pure (some (Timestamp.encode (Timestamp.invalidate (Timestamp.load bytes))), ())
    return .exited 0
  | .removeTimestamp =>
    Sys.removeTimestampFile ctx.invoking.uid
    return .exited 0

private def execute (ctx : Core.Context) (decision : Core.Decision)
    (conf : SudoConf.Config) : IO Sys.ExitStatus := do
  let needsSession := match decision.action with | .exec _ | .edit _ => true | _ => false
  let authUser := match decision.auth with
    | .required u => u
    | .none => Core.authUser ctx
  -- A pre-lock timestamp snapshot cannot waive authentication on its own.
  -- Early failures and timestamp-reset actions never enter policy authentication.
  let needsAuth := match decision.auth with
    | .required _ => true
    | .none => (Core.earlyAction ctx).isNone &&
      Core.policyNeedsAuth ctx (Core.authJudgement ctx
        (Policy.evaluate ctx.sudoers ctx.settings (Core.request ctx)))
  if !needsSession && !needsAuth && !decision.updateTimestamp then
    return ← executeAction ctx decision none
  let askpass := ((ctx.userEnv.lookup "SUDO_ASKPASS").filter (!·.isEmpty)).or conf.askpass
  let useAskpass := ctx.opts.askpass || (!ctx.opts.stdin && ctx.ttyName.isNone &&
    (ctx.userEnv.lookup "DISPLAY").isSome && askpass.isSome)
  if useAskpass && askpass.isNone then
    throw (IO.userError "no askpass program specified, try setting SUDO_ASKPASS")
  let service := if useAskpass && ctx.settings.pamAskpassService.isSome then
      ctx.settings.pamAskpassService.getD ctx.settings.pamService
    else if ctx.opts.login then ctx.settings.pamLoginService else ctx.settings.pamService
  let promptFormat := (ctx.opts.prompt.or (ctx.userEnv.lookup "SUDO_PROMPT")).getD ctx.settings.passprompt
  let prompt := expandPrompt promptFormat ctx.invoking.name ctx.target.name ctx.longHost authUser.name
  let h ← Sys.pamStart service authUser.name {
    useStdin := ctx.opts.stdin, nonInteractive := ctx.opts.nonInteractive,
    prompt, override := ctx.settings.passpromptOverride,
    pwfeedback := ctx.settings.pwfeedback, timeout := ctx.settings.passwdTimeout.getD 0 }
    (if ctx.settings.pamRuser then ctx.invoking.name else "") ctx.ttyName
  try
    Sys.pamConfigure h ctx.settings.pamSilent (!(ctx.opts.shell || ctx.opts.login))
      ctx.opts.bell (if useAskpass then askpass.getD "" else "")
      (if ctx.settings.pamRhost then ctx.longHost else "") ctx.invoking.name
    Sys.pamLecture h (← lecture ctx)
    let authorized : IO Bool := do
      if !needsAuth && !decision.updateTimestamp then
        if needsSession then account ctx h
        return true
      Sys.withTimestampFile ctx.invoking.uid fun bytes => do
        let records := Timestamp.load bytes
        let cached := !ctx.opts.resetTimestamp && Timestamp.lookup (← Sys.bootTimeNanos)
          ctx.settings.timestampTimeout ctx.tsScope authUser.uid records
        let failure ← if !needsAuth || cached then pure none else authenticate ctx h
        if let some reason := failure then
          logLine ctx (Core.logLine ctx (some reason))
          if ctx.settings.mailBadpass || ctx.settings.mailAlways then
            mail ctx (Core.logLine ctx (some reason))
          return (none, false)
        if ← Sys.pamLectured h then
          cleanup do
            let _ ← Sys.stateMarker ctx.settings.lectureStatusDir ctx.invoking.uid true
            pure ()
        if needsSession then account ctx h
        let out ← if decision.updateTimestamp then do
            pure (some (Timestamp.encode (Timestamp.update (← Sys.bootTimeNanos)
              ctx.tsScope authUser.uid records)))
          else pure none
        return (out, true)
    if !(← authorized) then
      return .exited 1
    executeAction ctx decision (some h)
  finally
    cleanup (Sys.pamEnd h 0)

/-- `/proc/self/cmdline` preserves argv[0] (unlike the executable's realpath) and
lets us reject invalid UTF-8 before decoded Lean arguments reach policy. -/
def run (args : List String) : IO UInt32 := do
  try
    Sys.initializeProcess false
    let conf ← if (← Sys.stat "/etc/sudo.conf").isSome then do
        let (_, text) ← Sys.readFileFollow "/etc/sudo.conf"
        fromExcept (SudoConf.parse text)
      else pure {}
    Sys.initializeProcess conf.disableCoredump
    if (← Sys.geteuid) != 0 then
      if ← Sys.noNewPrivs then
        warn "The \"no new privileges\" flag is set, which prevents sudo from running as root."
        warn "If sudo is running in a container, you may need to adjust the container configuration to disable the flag."
      else if let some path ← Sys.realpath "/proc/self/exe" then
        if let some st ← Sys.stat path then
          if st.uid != 0 || st.mode &&& 0o4000 == 0 then
            warn s!"{path} must be owned by uid 0 and have the setuid bit set"
          else
            warn s!"effective uid is not 0, is {path} on a file system with the 'nosuid' option set or an NFS file system without root privileges?"
        else warn "effective uid is not 0, is sudo installed setuid root?"
      else warn "effective uid is not 0, is sudo installed setuid root?"
      return 1
    if (← Sys.getpwuid (← Sys.getuid)).isNone then
      warn "you do not exist in the passwd database"
      return 1
    let raw ← IO.FS.readBinFile "/proc/self/cmdline"
    let valid := (String.fromUTF8? raw).isSome
    let first := ByteArray.mk ((raw.data.toList.takeWhile (· != 0)).toArray)
    let progname := Cli.programName ((String.fromUTF8? first).getD "sudo")
    let opts ← match Cli.parseArgs progname args with
      | .ok opts => pure opts
      | .error err =>
        Sys.writeStderr (Cli.formatError progname err)
        return 1
    if opts.mode == .help then
      (← IO.getStdout).putStr (Cli.helpFor progname)
      return 0
    if opts.mode == .version then
      if (← Sys.getuid) == 0 then
        let ctx ← context progname opts conf
        let interfaces := (← Sys.interfaceAddresses).toList.map (fun (a, m) => a ++ "/" ++ m)
        (← IO.getStdout).putStr (Cli.versionFor true ctx.settings interfaces (← Sys.architecture))
      else
        (← IO.getStdout).putStr Cli.versionText
      return 0
    if !valid || args.any (fun a => a.contains '\ufffd') then
      warn "non-UTF-8 command-line arguments are not supported"
      return 1
    if opts.chroot.isSome then warn "the -R option will be removed in a future version of sudo"
    let opts ← if opts.mode == .run && opts.command.head? == some "sudoedit" then do
        warn "sudoedit doesn't need to be run via sudo"
        pure { opts with mode := .edit, command := opts.command.drop 1 }
      else pure opts
    let ctx ← context progname opts conf
    let status ← try execute ctx (Core.decide ctx) conf
      finally
        if let some fd := ctx.execFd then cleanup (Sys.closeCommand fd.toUInt32)
    Sys.exitWith status
  catch e =>
    warn e.toString
    return 1

end LeanSudo.Shell
