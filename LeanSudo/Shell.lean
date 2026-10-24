import LeanSudo.Core
import LeanSudo.Sudoedit
import LeanSudo.Sudoers.Load
import LeanSudo.Policy.Defaults
import LeanSudo.Prompt
import LeanSudo.Sys.Core
import LeanSudo.Sys.Pam
import LeanSudo.Sys.Exec
import LeanSudo.Sys.Timestamp

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
      let shell := if opts.login then target.shell else (env.lookup "SHELL").getD invoking.shell
      let cmd := Cli.shellCommand shell opts.login opts.command
      (cmd.path, cmd.argv)
    else (opts.command.headD "", opts.command)
  if name.isEmpty then return none
  let some path ← resolvePath cwd search name | return none
  return some {
    path, canonical := (← Sys.realpath path).getD path
    argv0 := argv.headD name, args := argv.drop 1 }

private def atomPaths : Sudoers.CmndAtom → List String
  | .command path _ => [path]
  | _ => []

private def policyPaths : Sudoers.Entry → List String
  | .cmndAlias _ ms => ms.flatMap (fun m => atomPaths m.atom)
  | .defaults (.cmnd ms) _ => ms.flatMap (fun m => atomPaths m.atom)
  | .userSpec us => us.entries.flatMap (fun h => h.cmnds.flatMap (fun c => atomPaths c.cmnd.atom))
  | _ => []

private def canonTable (policy : Sudoers.Sudoers) : IO (List (String × String)) :=
  (policy.flatMap policyPaths).eraseDups.mapM fun p => do
    return (p, (← Sys.realpath p).getD p)

private def defaults (policy : Sudoers.Sudoers) (invoking : Principal) (host : String)
    (runas : Option Principal) (cmd : Option Command) (canon : String → String) : IO Settings := do
  let (settings, warnings) ← fromExcept (Policy.resolveDefaults policy invoking host runas cmd canon)
  for warning in warnings do
    if !warning.startsWith "ignoring unsupported defaults entry" then warn warning
  return settings

private def context (progname : String) (opts : Cli.Options) : IO Core.Context := do
  let uid ← Sys.getuid
  let some pw ← Sys.getpwuid uid | throw (IO.userError s!"unknown user #{uid}")
  let invoking ← principal pw (← Sys.getgroups)
  let host := ((← Sys.gethostname).splitOn ".").headD "localhost"
  let cwd ← Sys.getcwd
  let mask ← Sys.umask 0
  let _ ← Sys.umask mask
  let ttyDevice ← Sys.ttyDevice
  let mut ttyName := none
  if let some device := ttyDevice then
    for fd in [0, 1, 2] do
      if ttyName.isNone then
        if let some name ← Sys.ttyname fd then
          if let some st ← Sys.stat name then
            if st.rdev == device then ttyName := some name
  let userEnv ← Sys.environ
  let policy := (← Sudoers.load host).map (·.entry)
  let _ ← fromExcept (Policy.validate policy)
  let table ← canonTable policy
  let canon := fun p => (table.lookup p).getD p
  let initial ← defaults policy invoking host none none canon
  let target ← user (opts.user.getD (if opts.group.isSome then invoking.name else initial.runasDefault))
  let targetGroup ← opts.group.mapM group
  let listUser ← opts.otherUser.mapM user
  let command ← resolveCommand opts invoking target userEnv cwd initial
  let policyCommand := if opts.mode == .edit then some (.sudoedit opts.command) else
    command.map (fun c => .run c.path c.canonical c.args)
  let settings ← defaults policy invoking host (some target) policyCommand canon
  let sid ← Sys.getsid
  let ppid ← Sys.getppid
  let sidStart ← Sys.processStartTime sid
  let ppidStart ← Sys.processStartTime ppid
  -- Missing process identity must not reuse an unbound cache entry.
  if sidStart.isNone || ppidStart.isNone then
    throw (IO.userError "unable to determine timestamp process identity")
  let tsScope := Timestamp.scopeFor settings.timestampType ttyDevice
    sid (sidStart.getD 0) ppid (ppidStart.getD 0)
  let tsRecords ← try
      Sys.withTimestampFile uid (fun bytes => pure (none, Timestamp.load bytes))
    catch _ => pure []
  return {
    progname, opts, invoking, host, sudoers := policy, settings, target
    targetGroup, listUser, command, userEnv, cwd, userUmask := mask.toNat
    ttyName, canon, now := ← Sys.bootTimeNanos, tsScope, tsRecords }

private def logLine (ctx : Core.Context) (line : Core.LogLine) : IO Unit := do
  if let some facility := ctx.settings.syslog then
    Sys.syslog facility line.priority line.msg

private def authenticate (ctx : Core.Context) (h : Sys.PamHandle) : IO Bool := do
  for attempt in List.range ctx.settings.passwdTries do
    let rc ← Sys.pamAuthenticate h
    if rc == 0 then return true
    if let some err ← Sys.pamLastConvError h then
      warn err
      if err.startsWith "a terminal is required" then warn "a password is required"
      return false
    if attempt + 1 < ctx.settings.passwdTries then
      Sys.writeStderr (ctx.settings.badpassMessage ++ "\n")
  let n := ctx.settings.passwdTries
  warn s!"{n} incorrect password attempt{if n == 1 then "" else "s"}"
  return false

private def checkPam (h : Sys.PamHandle) (operation : String) (result : IO Int) : IO Unit := do
  let rc ← result
  if rc != 0 then throw (IO.userError (operation ++ ": " ++ (← Sys.pamStrerror h rc)))

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
  checkPam h "unable to set PAM user" (Sys.pamSetUser h ctx.target.name)
  if setcred then checkPam h "unable to establish credentials" (Sys.pamSetcred h true)
  try
    if openSession then checkPam h "unable to open session" (Sys.pamOpenSession h)
    try run
    finally
      if openSession then cleanup (checkPam h "unable to close session" (Sys.pamCloseSession h))
  finally
    if setcred then cleanup (checkPam h "unable to delete credentials" (Sys.pamSetcred h false))

private def executeAction (ctx : Core.Context) (decision : Core.Decision)
    (h : Option Sys.PamHandle) : IO Sys.ExitStatus := do
  if let some line := decision.log then logLine ctx line
  match decision.action with
  | .exec plan =>
    let some h := h | throw (IO.userError "missing PAM transaction")
    session ctx h plan.pamSetcred plan.pamSession do
      Sys.runCommand {
        path := plan.path, argv := plan.argv.toArray
        env := ← environment plan.envInput h, uid := plan.uid, gid := plan.gid
        groups := plan.groups.toArray, cwd := plan.cwd, umask := plan.umask
        usePty := plan.usePty, background := plan.background, closeFrom := plan.closeFrom }
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

private def execute (ctx : Core.Context) (decision : Core.Decision) : IO Sys.ExitStatus := do
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
  let service := if ctx.opts.login then ctx.settings.pamLoginService else ctx.settings.pamService
  let prompt := expandPrompt (ctx.opts.prompt.getD ctx.settings.passprompt)
    ctx.invoking.name ctx.target.name ctx.host authUser.name
  let h ← Sys.pamStart service authUser.name {
    useStdin := ctx.opts.stdin, nonInteractive := ctx.opts.nonInteractive,
    prompt := (if ctx.opts.bell then "\x07" else "") ++ prompt,
    override := ctx.opts.prompt.isSome || ctx.settings.passpromptOverride,
    pwfeedback := ctx.settings.pwfeedback } ctx.invoking.name ctx.ttyName
  try
    let authorized : IO Bool := do
      if !needsAuth && !decision.updateTimestamp then
        if needsSession then checkPam h "PAM account management error" (Sys.pamAcctMgmt h)
        return true
      Sys.withTimestampFile ctx.invoking.uid fun bytes => do
        let records := Timestamp.load bytes
        let cached := !ctx.opts.resetTimestamp && Timestamp.lookup (← Sys.bootTimeNanos)
          ctx.settings.timestampTimeout ctx.tsScope authUser.uid records
        let success ← if !needsAuth || cached then pure true else authenticate ctx h
        if !success then return (none, false)
        if needsSession then checkPam h "PAM account management error" (Sys.pamAcctMgmt h)
        let out ← if decision.updateTimestamp then do
            pure (some (Timestamp.encode (Timestamp.update (← Sys.bootTimeNanos)
              ctx.tsScope authUser.uid records)))
          else pure none
        return (out, true)
    if !(← authorized) then
      logLine ctx { priority := "alert", msg := ctx.invoking.name ++ " : authentication failure" }
      return .exited 1
    executeAction ctx decision (some h)
  finally
    cleanup (Sys.pamEnd h 0)

/-- `/proc/self/cmdline` preserves argv[0] (unlike the executable's realpath) and
lets us reject invalid UTF-8 before decoded Lean arguments reach policy. -/
def run (args : List String) : IO UInt32 := do
  try
    let raw ← IO.FS.readBinFile "/proc/self/cmdline"
    let valid := (String.fromUTF8? raw).isSome
    let first := ByteArray.mk ((raw.data.toList.takeWhile (· != 0)).toArray)
    let progname := Cli.basename ((String.fromUTF8? first).getD "sudo")
    let opts ← match Cli.parseArgs progname args with
      | .ok opts => pure opts
      | .error err =>
        Sys.writeStderr (Cli.formatError progname err)
        return 1
    if opts.mode == .help then
      (← IO.getStdout).putStr (Cli.helpFor progname)
      return 0
    if opts.mode == .version then
      (← IO.getStdout).putStr Cli.versionText
      return 0
    if (← Sys.geteuid) != 0 then
      warn "effective uid is not 0"
      return 1
    if !valid || args.any (fun a => a.contains '\ufffd') then
      warn "non-UTF-8 command-line arguments are not supported"
      return 1
    let ctx ← context progname opts
    let status ← execute ctx (Core.decide ctx)
    Sys.exitWith status
  catch e =>
    warn e.toString
    return 1

end LeanSudo.Shell
