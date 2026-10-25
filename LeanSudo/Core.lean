import LeanSudo.Core.Types
import LeanSudo.Policy.Eval
import LeanSudo.Policy.List
import LeanSudo.Sudoedit.Check

/-!
# Pure decision core

The shell supplies facts; only this total function authorizes execution. Unsupported
deciding restrictions fail closed after authentication. Listing another user's
privileges requires root, the list pseudo-command, or suitable ALL privileges.
Authentication for `-l command` follows the listing policy even when that command
is not permitted; the command check itself is silent, as in sudo 1.9.17p2.
Authentication exemptions include exempt_group and unchanged uid/gid/security contexts.
Enabled run-as shell checks and unknown-ID restrictions are enforced from shell facts.
Sudoedit policy sees the original file operands. The runtime receives those same
operands made absolute against the invoking directory and traverses pinned directory
descriptors without lexically folding symlink-sensitive parent components.
Execution preserves the requested basename beneath the lookup-time canonical parent.
Digest rules and fdexec=always instead use the descriptor pinned before authentication.
Command displays and SUDO_COMMAND retain the lookup path and unescaped shell arguments.
-/
namespace LeanSudo.Core

open Policy

def displayUser (ctx : Context) : Principal :=
  if ctx.invoking.uid == 0 && (ctx.opts.mode == .run || ctx.opts.mode == .edit) then
    ctx.previousUser.getD ctx.invoking else ctx.invoking

def files (ctx : Context) : List String :=
  ctx.opts.command.map fun p => if p.startsWith "/" then p
    else ctx.cwd ++ (if ctx.cwd.endsWith "/" then "" else "/") ++ p

/-- Paths handed to descriptor-relative traversal are absolute and C-string-safe.
Dot, parent and repeated-slash components retain their kernel resolution semantics. -/
def normalizedEditFile (p : String) : Bool :=
  p.startsWith "/" && !p.contains '\x00'

def invalidEditFile (ctx : Context) : Option String :=
  (files ctx).find? (fun p => !normalizedEditFile p)

/-- Policy/logging see the unescaped shell command; exec retains escaped argv. -/
def policyArgs (ctx : Context) (rc : ResolvedCmd) : List String :=
  if ctx.opts.shell || ctx.opts.login then
    if ctx.opts.command.isEmpty then [] else ["-c", String.intercalate " " ctx.opts.command]
  else rc.args

def runCommand (ctx : Context) : Command :=
  match ctx.command with
  | some rc => .run rc.path rc.canonical (policyArgs ctx rc)
  | none => let typed := ctx.opts.command.headD ""; .run typed typed ctx.opts.command.tail

/-- A rooted authorization uses only its own lookup result and actual execution
arguments. A missing/malformed rooted result never falls back to the host root. -/
def resolvedFor (ctx : Context) (a : Allowed) : Option ResolvedCmd :=
  match a.selection with
  | none => ctx.command
  | some selected =>
    if selected.found then
      match selected.command, selected.argv with
      | .run path canonical _, argv0 :: args => some { path, canonical, argv0, args }
      | _, _ => none
    else none

/-- A selected root's missing descriptor must not reuse a host-root descriptor. -/
def descriptorFor (ctx : Context) (a : Allowed) : Option Nat :=
  match a.selection with
  | none => ctx.execFd
  | some selected => selected.execFd

def commandSetidFor (ctx : Context) (a : Allowed) : Bool :=
  (a.selection.map (·.setid)).getD ctx.commandSetid

def authorizationSettings (ctx : Context) : Settings :=
  ctx.policySettings.getD ctx.settings

def request (ctx : Context) : Request :=
  { user := if ctx.opts.mode == .list then ctx.listUser.getD ctx.invoking else ctx.invoking
    host := ctx.opts.host.getD ctx.host, runasUser := ctx.policyTarget.getD ctx.target,
    runasGroup := ctx.targetGroup, runasUserExplicit := ctx.opts.user.isSome, canon := ctx.canon,
    lhost := ctx.opts.host.getD ctx.longHost, interfaces := ctx.interfaces,
    netgroups := ctx.netgroups, regexMatches := ctx.regexMatches, digests := ctx.digests,
    pluginGroups := ctx.pluginGroups,
    now := ctx.wallTime, utcOffset := ctx.utcOffset, fileIds := ctx.fileIds, globPaths := ctx.globPaths,
    fastGlob := (authorizationSettings ctx).fastGlob,
    rootFacts := ctx.rootFacts, requestedChroot := ctx.opts.chroot,
    defaultChroot := (authorizationSettings ctx).runchroot,
    canonPaths := ctx.canonPaths,
    command := match ctx.opts.mode with
      | .edit => .sudoedit ctx.opts.command
      | .list => if ctx.opts.command.isEmpty then .list else runCommand ctx
      | .validate => .validate
      | _ => runCommand ctx }

def authUser (ctx : Context) : Principal :=
  if ctx.opts.mode == .list then ctx.invoking
  else if ctx.settings.rootpw then ctx.root
  else if ctx.settings.runaspw then ctx.runasDefaultUser.getD ctx.root
  else if ctx.settings.targetpw then ctx.target else ctx.invoking

/-- sudo's user-facing host is the resolved full name, unlike its short matcher key. -/
def displayHost (ctx : Context) : String :=
  ctx.opts.host.getD (if ctx.longHost.isEmpty then ctx.host else ctx.longHost)

/-- Listing headers and NO_HOST/NO_CHECK diagnostics use runas.shost. -/
def displayShortHost (ctx : Context) : String :=
  ((ctx.opts.host.getD ctx.host).splitOn ".").headD ctx.host

def listOtherDenied (ctx : Context) : Bool :=
  ctx.opts.mode == .list && ctx.opts.otherUser.isSome &&
    !canListOther ctx.sudoers (authorizationSettings ctx) { request ctx with user := ctx.invoking }
      (ctx.listUser.getD ctx.invoking) ctx.root

/-- Listing another user is an authorization decision, not a pre-authentication error. -/
def policyJudgement (ctx : Context) : Judgement :=
  if listOtherDenied ctx then .deny else evaluate ctx.sudoers (authorizationSettings ctx) (request ctx)

def sameIdentity (ctx : Context) : Bool :=
  ctx.target.uid == ctx.invoking.uid &&
    (ctx.opts.group.isNone || match ctx.targetGroup with
      | none => false
      | some g => ctx.invoking.groups.any (fun x => x.2 == g.gid))

/-- Changing a security context is not "running as yourself", even with identical IDs. -/
def sameSecurityContext (ctx : Context) (a : Allowed) : Bool :=
  (ctx.opts.role.or (a.role.or ctx.settings.role)).isNone &&
  (ctx.opts.type.or (a.type.or ctx.settings.type)).isNone &&
  (a.apparmorProfile.or ctx.settings.apparmorProfile).isNone &&
  (a.privs.or ctx.settings.privs).isNone &&
  (a.limitprivs.or ctx.settings.limitprivs).isNone

def policyNeedsAuth (ctx : Context) (j : Judgement) : Bool :=
  ctx.invoking.uid != 0 && !userIsExempt ctx.settings ctx.invoking && match j with
    | .deny => ctx.settings.authenticate
    | .allow a => a.needsAuth && !(sameIdentity ctx && sameSecurityContext ctx a)

def tsValid (ctx : Context) : Bool :=
  !ctx.opts.resetTimestamp && Timestamp.lookup ctx.now ctx.settings.timestampTimeout
    ctx.tsScope (authUser ctx).uid ctx.tsRecords

def authentication (ctx : Context) (j : Judgement) : AuthReq :=
  if policyNeedsAuth ctx j && !tsValid ctx then .required (authUser ctx) else .none

def targetGid (ctx : Context) : Nat := (ctx.targetGroup.map (·.gid)).getD ctx.target.gid

/-- On Linux stay_setuid retains the invoking real gid as all three command gids. -/
def commandGid (ctx : Context) : Nat :=
  if ctx.settings.staySetuid then ctx.invokingRealGid.getD ctx.invoking.gid else targetGid ctx

def targetGroups (ctx : Context) : List Nat :=
  (if ctx.opts.preserveGroups || ctx.settings.preserveGroups then ctx.invoking.groups
   else ctx.target.groups).map (·.2)

def commandUmask (ctx : Context) : Nat :=
  (if ctx.settings.umask == 0o777 then ctx.userUmask
   else if ctx.settings.umaskOverride then ctx.settings.umask
   else ctx.settings.umask ||| ctx.userUmask) &&& 0o777

def commandText (ctx : Context) : String :=
  match (request ctx).command with
  | .run p _ args => String.intercalate " " (p :: args)
  | .sudoedit fs => String.intercalate " " ("sudoedit" :: fs)
  | .list => "list"
  | .validate => "validate"
  | .checkList => "list"


/-- env.c limits the argument portion of SUDO_COMMAND to 4096 bytes. -/
def sudoCommand (ctx : Context) : String :=
  let text := commandText ctx
  let path := match (request ctx).command with
    | .run p _ _ => p
    | .sudoedit _ => "sudoedit"
    | _ => text
  if text.utf8ByteSize ≤ path.utf8ByteSize + 1 + 4096 then text
  else String.fromUTF8! (text.toUTF8.extract 0 (path.utf8ByteSize + 1 + 4096))

/-- Expand home paths from passwd facts gathered before privilege transition. -/
def expandHomePath (targetHome : String) (homes : List (String × String))
    (p : String) : Option String :=
  if p == "~" then some targetHome
  else if p.startsWith "~/" then some (targetHome ++ String.ofList (p.toList.drop 1))
  else if p.startsWith "~" then
    let name := String.ofList ((p.toList.drop 1).takeWhile (· != '/'))
    (homes.find? (·.1 == name)).map fun kv =>
      kv.2 ++ String.ofList (p.toList.drop (name.length + 1))
  else some p

def expandHome (ctx : Context) (p : String) : Option String :=
  expandHomePath ctx.target.home ctx.homes p

def effectiveCwd (ctx : Context) (a : Allowed) : Option String :=
  match a.cwd with
  | none => ctx.settings.runcwd
  | some none => some "*"
  | some (some path) => some path

def cwdPermitted (ctx : Context) (a : Allowed) : Bool :=
  ctx.opts.chdir.isNone || effectiveCwd ctx a == some "*"

def configuredCwd (ctx : Context) (a : Allowed) : Option String :=
  (ctx.opts.chdir.or (effectiveCwd ctx a)).filter (· != "*")

/-- Run commands use their deciding CHROOT option; sudoedit ignores that option
and applies only Defaults runchroot to its editor child, as sudo.ws does. -/
def effectiveChroot (ctx : Context) (a : Allowed) : Option String :=
  (if ctx.opts.mode == .edit then none else a.chroot).or (authorizationSettings ctx).runchroot

/-- Even an identical fixed root does not authorize the command-line -R option. -/
def chrootPermitted (ctx : Context) (a : Allowed) : Bool :=
  ctx.opts.chroot.isNone || effectiveChroot ctx a == some "*"

/-- The wildcard permits -R; by itself it does not select a new process root. -/
def configuredChroot (ctx : Context) (a : Allowed) : Option String :=
  (ctx.opts.chroot.or (effectiveChroot ctx a)).filter (· != "*")

/-- Preserve the winning lookup's root across post-authorization runtime options. -/
def selectedChroot (ctx : Context) (a : Allowed) : Option String :=
  if ctx.opts.mode == .edit then configuredChroot ctx a
  else match a.selection with
    | some selected => (some selected.root).filter (· != "*")
    | none => configuredChroot ctx a

def commandChroot (ctx : Context) (a : Allowed) : Option String :=
  let home := if ctx.opts.mode == .edit then ctx.target.home
    else (ctx.policyTarget.getD ctx.target).home
  (selectedChroot ctx a).bind (expandHomePath home ctx.homes)

def environment (ctx : Context) (a : Allowed) : EnvInput :=
  { userEnv := ctx.userEnv, settings := ctx.settings, invoking := ctx.invoking,
    target := ctx.target, command := sudoCommand { ctx with command := resolvedFor ctx a },
    preserve := ctx.opts.preserveEnv,
    setenvAllowed := a.setenv, cmdlineVars := ctx.opts.envVars, loginShell := ctx.opts.login,
    setHome := ctx.opts.setHome, pamEnv := [], shellMode := ctx.opts.shell,
    invokingRealGid := ctx.invokingRealGid,
    ttyName := ctx.ttyName, envFile := ctx.envFile, restrictedEnvFile := ctx.restrictedEnvFile }

def pamService (ctx : Context) : String :=
  if ctx.opts.login then ctx.settings.pamLoginService else ctx.settings.pamService

/-- Match and execution preserve the final name (including multicall dispatch),
while resolving its parent directory once, before policy and authentication. -/
def executionPath (ctx : Context) (rc : ResolvedCmd) : String :=
  let parent := ctx.canon (dirOf rc.path)
  parent ++ (if parent.endsWith "/" then "" else "/") ++ baseOf rc.path

def selectedExecutionPath (ctx : Context) (a : Allowed) (rc : ResolvedCmd) : String :=
  (a.selection.map (·.executionPath)).getD (executionPath ctx rc)

/-- A user timeout can shorten, but never extend, the deciding rule's limit. -/
def commandTimeout (ctx : Context) (a : Allowed) : Nat :=
  let policy := a.timeout.getD ctx.settings.commandTimeout
  match ctx.opts.timeout with
  | none => policy
  | some user => if user == 0 then policy else if policy == 0 then user else min user policy

def execPlan (ctx : Context) (a : Allowed) (rc : ResolvedCmd) : ExecPlan :=
  { path := selectedExecutionPath ctx a rc, argv := rc.argv0 :: rc.args, envInput := environment ctx a,
    uid := ctx.target.uid, gid := commandGid ctx, groups := targetGroups ctx,
    cwd := ((configuredCwd ctx a).bind (expandHome ctx)).or (if ctx.opts.login then some ctx.target.home else none),
    umask := commandUmask ctx,
    usePty := ctx.settings.usePty, background := ctx.opts.background,
    closeFrom := ctx.opts.closeFrom.getD ctx.settings.closefrom.toNat,
    pamService := pamService ctx, pamSession := ctx.settings.pamSession,
    pamSetcred := ctx.settings.pamSetcred, cwdOptional := ctx.opts.login && (configuredCwd ctx a).isNone,
    execBackground := ctx.settings.execBackground,
    staySetuid := ctx.settings.staySetuid,
    intercept := a.intercept.getD ctx.settings.intercept,
    logSubcmds := ctx.settings.logSubcmds,
    chroot := commandChroot ctx a,
    timeout := commandTimeout ctx a,
    noexecFile := if a.noexec.getD ctx.settings.noexec then
      some (ctx.settings.noexecFile.getD "/usr/libexec/sudo/sudo_noexec.so") else none,
    apparmorProfile := a.apparmorProfile.or ctx.settings.apparmorProfile,
    utmpUser := if ctx.settings.setUtmp then
      some (if ctx.settings.utmpRunas then ctx.target.name else ctx.invoking.name) else none,
    execFd := if ctx.settings.fdexec != "never" &&
      (a.usesDigest || ctx.settings.fdexec == "always") then descriptorFor ctx a else none,
    rlimits := ctx.settings.resourceLimits,
    iolog := IoLog.plan ctx.settings { logInput := a.logInput, logOutput := a.logOutput } }

def editorWords (s : String) : List String := Sudoedit.editorWords s

def environmentEditors (ctx : Context) : List String :=
  (["SUDO_EDITOR", "VISUAL", "EDITOR"].filterMap (lookup ctx.userEnv)).filter (!·.isEmpty)

def editorCandidates (ctx : Context) : List (String × List String) :=
  (environmentEditors ctx ++ ctx.settings.editor.splitOn ":").filterMap fun source =>
    let words := editorWords source
    if words.isEmpty then none else some (source, words)

def editors (ctx : Context) : List (List String) := (editorCandidates ctx).map (·.2)

def editPlan (ctx : Context) (a : Allowed) : EditPlan :=
  let candidates := editorCandidates ctx
  { files := files ctx, policyFiles := ctx.opts.command, editors := candidates.map (·.2), editUid := (displayUser ctx).uid,
    editGid := (displayUser ctx).gid, editGroups := (displayUser ctx).groups.map (·.2),
    fileUid := ctx.target.uid, fileGid := targetGid ctx, fileGroups := targetGroups ctx,
    envInput := environment ctx a, umask := commandUmask ctx, pamService := pamService ctx,
    pamSession := ctx.settings.pamSession, pamSetcred := ctx.settings.pamSetcred,
    follow := a.follow.getD ctx.settings.sudoeditFollow, checkdir := ctx.settings.sudoeditCheckdir,
    chroot := commandChroot ctx a,
    cwd := (configuredCwd ctx a).bind (expandHome ctx), cwdOptional := false,
    usePty := ctx.settings.usePty,
    iolog := IoLog.plan ctx.settings {},
    timeout := ctx.settings.commandTimeout, rlimits := ctx.settings.resourceLimits,
    utmpUser := if ctx.settings.setUtmp then
      some (if ctx.settings.utmpRunas then ctx.target.name else ctx.invoking.name) else none,
    closeFrom := ctx.opts.closeFrom.getD ctx.settings.closefrom.toNat,
    execBackground := ctx.settings.execBackground,
    noexecFile := if ctx.settings.noexec then
      some (ctx.settings.noexecFile.getD "/usr/libexec/sudo/sudo_noexec.so") else none,
    apparmorProfile := ctx.settings.apparmorProfile,
    editorSources := candidates.map (·.1),
    editorNotFound := (environmentEditors ctx).getLast?.getD ctx.settings.editor,
    editorPath := (if userIsExempt ctx.settings ctx.invoking then none else ctx.settings.securePath).getD
      ((lookup ctx.userEnv "PATH").getD stdPath) }

def notFoundText (ctx : Context) : String :=
  let command := ctx.opts.command.headD ""
  if ctx.commandFoundInDot then
    s!"sudo: ignoring \"{command}\" found in '.'\nUse \"sudo ./{command}\" if this is the \"{command}\" you wish to run.\n"
  else
    s!"sudo: {command}: command not found\n" ++
      if command == "cd" then
        "sudo: \"cd\" is a shell built-in command, it cannot be run directly.\n" ++
        "sudo: the -s option may be used to run a privileged shell.\n" ++
        "sudo: the -D option may be used to run a command in a specific directory.\n" else ""

def notFound (ctx : Context) : Action := .fail (notFoundText ctx) 1

/-- A failing policy check carries its actual warning/rejection/audit effects,
not an inferred accept event or a classification parsed from diagnostic text. -/
structure FailureInfo where
  message : String
  prefixed : Bool := true
  reason : Option String := none
  denial : Bool := false
  raw : Bool := false
  commandReady : Bool := true
  lookupComplete : Bool := true
  rootApplied : Bool := false
  cwdApplied : Bool := false
  auditReason : Option String := none
  adminFlag : Bool := false

def FailureInfo.action (f : FailureInfo) : Action :=
  .fail (if f.prefixed then "sudo: " ++ f.message ++ "\n" else f.message) 1

def warningInfo (message reason : String) : FailureInfo :=
  { message, reason := some reason, auditReason := some reason }

def permissionCommand (ctx : Context) (a : Allowed) : String :=
  if ctx.opts.mode == .edit then "sudoedit"
  else ((resolvedFor ctx a).map (·.path)).getD (ctx.opts.command.headD "")

def permissionFailure (ctx : Context) (a : Allowed) : Option FailureInfo :=
  if !chrootPermitted ctx a then
    some (warningInfo s!"you are not permitted to use the -R option with {permissionCommand ctx a}"
      s!"user not allowed to change root directory to {ctx.opts.chroot.getD ""}")
  else if !cwdPermitted ctx a then
    some { (warningInfo s!"you are not permitted to use the -D option with {permissionCommand ctx a}"
      s!"user not allowed to change directory to {ctx.opts.chdir.getD ""}") with rootApplied := true }
  else none

def preCommandFailure (ctx : Context) (a : Allowed) : Option FailureInfo :=
  match permissionFailure ctx a with
  | some failure => some failure
  | none =>
    if let some reason := a.selection.bind (·.refusal) then
      some { (warningInfo reason reason) with rootApplied := true, cwdApplied := true }
    else if ctx.opts.mode == .run && a.intercept.getD ctx.settings.intercept &&
        !ctx.settings.interceptAllowSetid && commandSetidFor ctx a then
      some {
        message := "setid commands are not permitted in intercept mode",
        reason := some "setid command rejected in intercept mode", denial := true,
        auditReason := some "setid command rejected in intercept mode",
        rootApplied := true, cwdApplied := true }
    else none

def postCommandFailure (ctx : Context) (a : Allowed) : Option FailureInfo :=
  if ctx.opts.timeout.getD 0 > 0 && !ctx.settings.userCommandTimeouts then
    some { (warningInfo "sorry, you are not allowed set a command timeout"
      "user not allowed to set a command timeout") with rootApplied := true, cwdApplied := true, adminFlag := true }
  else if ctx.settings.fdexec != "never" && (a.usesDigest || ctx.settings.fdexec == "always") &&
      (descriptorFor ctx a).isNone then some { message := "unable to execute command: missing command descriptor" }
  else if (selectedChroot ctx a).isSome && (commandChroot ctx a).isNone then
    some { message := s!"invalid chroot directory: {(selectedChroot ctx a).getD ""}" }
  else if ctx.selinuxEnabled && ((ctx.opts.role.or (a.role.or ctx.settings.role)).isSome ||
      (ctx.opts.type.or (a.type.or ctx.settings.type)).isSome) then
    some { message := "unable to set SELinux security context" }
  else if (configuredCwd ctx a).isSome && ((configuredCwd ctx a).bind (expandHome ctx)).isNone then
    some { message := "unknown user in working directory" }
  else none

/-- Command enforcement failures, independent of their display and event classification. -/
def enforcementError (ctx : Context) (a : Allowed) : Option String :=
  ((preCommandFailure ctx a).orElse (fun _ => postCommandFailure ctx a)).map (·.message)

def postLookupFailure (ctx : Context) (a : Allowed) : Option FailureInfo :=
  match postCommandFailure ctx a with
  | some failure => some failure
  | none =>
    if ctx.opts.mode == .run || ctx.opts.mode == .edit then
      match buildEnv (environment ctx a) with
      | .ok _ => none
      | .error message =>
        if ctx.opts.preserveEnv == .all && !a.setenv then
          some { (warningInfo message "user not allowed to preserve the environment") with
            rootApplied := true, cwdApplied := true, adminFlag := true }
        else some {
          message, reason := some message, rootApplied := true,
          cwdApplied := true, adminFlag := true }
    else none

def allowedFailure (ctx : Context) (a : Allowed) : Option FailureInfo :=
  match preCommandFailure ctx a with
  | some failure => some failure
  | none =>
    if (ctx.opts.mode == .run || (ctx.opts.mode == .list && !ctx.opts.command.isEmpty)) &&
        (resolvedFor ctx a).isNone then
      some {
        message := notFoundText ctx, prefixed := false, adminFlag := true,
        auditReason := some (if ctx.commandFoundInDot then "command in current directory"
          else s!"{ctx.opts.command.headD ""}: command not found") }
    else postLookupFailure ctx a

def allowedAction (ctx : Context) (a : Allowed)
    (failure : Option FailureInfo := allowedFailure ctx a) : Action :=
  match failure, ctx.opts.mode with
  | some f, _ => f.action
  | none, .run => match resolvedFor ctx a with
    | none => notFound ctx
    | some rc => .exec (execPlan ctx a rc)
  | none, .edit => .edit (editPlan ctx a)
  | none, .list =>
    if ctx.opts.command.isEmpty then
      let located := if ctx.listingSources.isEmpty then ctx.locatedSudoers else ctx.listingSources
      let policy := if ctx.listingSources.isEmpty then ctx.sudoers else located.map (·.entry)
      .print (listPrivileges policy ctx.settings (ctx.listUser.getD ctx.invoking)
        (displayShortHost ctx) ctx.canon (ctx.opts.listVerbose > 1) located
          (some (request ctx)) ctx.listColumns) 0
    else match resolvedFor ctx a with
      | none => notFound ctx
      | some _ => .print (listCommand ctx.sudoers (authorizationSettings ctx) (request ctx)
          ctx.locatedSudoers (ctx.opts.listVerbose > 1)) 0
  | none, .validate => .validate
  | none, _ => .fail "sudo: invalid policy mode\n" 1

def userMatches (ctx : Context) : Bool :=
  let al := aliasesOf ctx.sudoers
  (specsOf ctx.sudoers).any (fun us => userListOk al al.fuel ctx.invoking us.users (authorizationSettings ctx) (some (request ctx)))

def hostMatches (ctx : Context) : Bool :=
  let al := aliasesOf ctx.sudoers
  (specsOf ctx.sudoers).any fun us =>
    userListOk al al.fuel ctx.invoking us.users (authorizationSettings ctx) (some (request ctx)) &&
    us.entries.any (fun hc => hostListOk al al.fuel ctx.host hc.hosts (authorizationSettings ctx) (some (request ctx)))

def denialReason (ctx : Context) : String :=
  if ctx.opts.mode == .list || ctx.opts.mode == .validate then "command not allowed"
  else if !userMatches ctx then "user NOT in sudoers"
  else if !hostMatches ctx then "user NOT authorized on host" else "command not allowed"

def denialMail (ctx : Context) : Bool :=
  ctx.mailerAvailable && (ctx.settings.mailAlways ||
    ((ctx.opts.mode == .run || ctx.opts.mode == .edit) && ctx.settings.mailAllCmnds) ||
    if !userMatches ctx then ctx.settings.mailNoUser
    else if !hostMatches ctx then ctx.settings.mailNoHost else ctx.settings.mailNoPerms)

def incident (ctx : Context) : String :=
  if denialMail ctx then "This incident has been reported to the administrator.\n" else ""

def deniedAction (ctx : Context) : Action :=
  if listOtherDenied ctx then
    .fail (s!"Sorry, user {ctx.invoking.name} is not allowed to execute '{if ctx.opts.command.isEmpty then "list" else "list " ++ commandText ctx}' as {(ctx.listUser.getD ctx.invoking).name} on {displayHost ctx}.\n" ++
      (ctx.settings.cmddenialMessage.map (· ++ "\n")).getD "") 1
  else if ctx.opts.mode = .list then
    if !ctx.opts.command.isEmpty then .print "" 1
    else if ctx.opts.otherUser.isSome && (ctx.listUser.getD ctx.invoking).uid != ctx.invoking.uid then
      .fail (notAllowedMessage (ctx.listUser.getD ctx.invoking).name (displayShortHost ctx) ++ "\n") 1
    else .fail s!"Sorry, user {ctx.invoking.name} may not run sudo on {displayShortHost ctx}.\n" 1
  else if ctx.opts.mode = .validate then
    .fail s!"Sorry, user {ctx.invoking.name} may not run sudo on {displayShortHost ctx}.\n" 1
  else if !userMatches ctx then .fail (s!"{(displayUser ctx).name} is not in the sudoers file.\n" ++ incident ctx) 1
  else if !hostMatches ctx then
    .fail (s!"{(displayUser ctx).name} is not allowed to run sudo on {displayShortHost ctx}.\n" ++ incident ctx) 1
  else if ctx.command.isNone && ctx.opts.mode = .run && ctx.settings.pathInfo then notFound ctx
  else
    let target := ctx.target.name ++ (ctx.targetGroup.map (fun g => ":" ++ g.name)).getD ""
    .fail (s!"Sorry, user {(displayUser ctx).name} is not allowed to execute '{commandText ctx}' as {target} on {displayHost ctx}.\n" ++
      (ctx.settings.cmddenialMessage.map (· ++ "\n")).getD "" ++ incident ctx) 1

/-- sudo's lbuf escaping: controls/blanks use #0octal; quoted argv escapes
backslashes and apostrophes without changing the command's argument boundaries. -/
def logEscape (text : String) (blanks : Bool := false) (quotes : Bool := false) : String :=
  String.join (text.toList.map fun c =>
    let n := c.toNat
    if n < 32 || n == 127 || (blanks && c == ' ') then
      "#0" ++ (if n ≥ 64 then toString (n / 64) else "") ++
        (if n ≥ 8 then toString (n / 8 % 8) else "") ++ toString (n % 8)
    else if quotes && (c == '\'' || c == '\\') then "\\" ++ c.toString else c.toString)

def logArgument (arg : String) : String :=
  if arg.contains ' ' then "'" ++ logEscape arg false true ++ "'"
  else logEscape arg true true

def logCommand (ctx : Context) : String :=
  match (request ctx).command with
  | .run p _ args =>
    let path := if p.startsWith "/" then p else (ctx.command.map (executionPath ctx)).getD p
    logEscape path true ++ String.join (args.map (" " ++ logArgument ·))
  | .sudoedit fs => "sudoedit" ++ String.join (fs.map (" " ++ logArgument ·))
  | _ => commandText ctx

/-- The frontend has already formed shell argv before set_cmnd resolves a path. -/
def unresolvedLogCommand (ctx : Context) : String × List String :=
  if ctx.opts.mode == .edit then ("sudoedit", ctx.opts.command)
  else if ctx.opts.shell || ctx.opts.login || ctx.opts.impliedShell then
    let shell := Cli.userShell (if ctx.opts.login then none else ctx.userEnv.lookup "SHELL")
      (if ctx.opts.login then ctx.target.shell else ctx.invoking.shell)
    let command := Cli.shellCommand shell ctx.opts.login ctx.opts.command
    (command.path, command.argv.tail)
  else (ctx.opts.command.headD "", ctx.opts.command.tail)

def logLine (ctx : Context) (reason : Option String) (allowed : Option Allowed := none)
    (commandOverride : Option (String × List String) := none)
    (rootApplied : Bool := true) : LogLine :=
  let tty := ctx.ttyName.map fun t =>
    logEscape (if t.startsWith "/dev/" then String.ofList (t.toList.drop 5) else t)
  let cwd := (allowed.map (configuredCwd ctx)).getD
    ((ctx.opts.chdir.or ctx.settings.runcwd).filter (· != "*"))
  let cwd := (cwd.bind (expandHome ctx)).getD (if ctx.opts.login then ctx.target.home else ctx.cwd)
  let chroot := match allowed with
    | some a =>
      if rootApplied then commandChroot ctx a
      else (configuredChroot ctx a).bind (expandHomePath
        (if ctx.opts.mode == .edit then ctx.target.home else (ctx.policyTarget.getD ctx.target).home) ctx.homes)
    | none => ((ctx.opts.chroot.or ctx.settings.runchroot).filter (· != "*")).bind (expandHome ctx)
  let commandCtx := (allowed.map (fun a => { ctx with command := resolvedFor ctx a })).getD ctx
  { format := ctx.settings.logFormat, reason,
    event := if reason.isSome then .reject else .accept,
    runcwd := some cwd, runchroot := chroot,
    priority := (if reason.isSome then ctx.settings.syslogBadpri else ctx.settings.syslogGoodpri).getD "none",
    msg := logEscape (displayUser ctx).name ++ " : " ++ (reason.map (fun s => logEscape s ++ " ; ")).getD "" ++
      (tty.map (fun t => s!"TTY={t} ; ")).getD "" ++
      (chroot.map (fun p => s!"CHROOT={logEscape p} ; ")).getD "" ++
      s!"PWD={logEscape cwd} ; USER={logEscape ctx.target.name} ; " ++
      (ctx.targetGroup.map (fun g => s!"GROUP={logEscape g.name} ; ")).getD "" ++
      (if ctx.opts.envVars.isEmpty then "" else
        "ENV=" ++ logEscape (String.intercalate " " (ctx.opts.envVars.map fun (k,v) => k ++ "=" ++ v)) ++ " ; ") ++
      "COMMAND=" ++ (match commandOverride with
        | some (path, args) => logEscape path ++
            (if args.isEmpty then "" else " " ++ String.intercalate " " (args.map logArgument))
        | none => logCommand commandCtx) }

/-- Event output follows the resolved sudoers format, including JSON. -/
theorem logLine_format (ctx : Context) (reason : Option String) (allowed : Option Allowed) :
    (logLine ctx reason allowed).format = ctx.settings.logFormat := rfl

/-- Alerts retain the stage's command and directory facts, not requested overrides
    whose permission checks have not yet succeeded. Raw alerts still name the submitter. -/
def failureLog (ctx : Context) (failure : FailureInfo)
    (allowed : Option Allowed := none) : Option LogLine := do
  let reason ← failure.reason
  if failure.denial && !ctx.settings.logDenied then none else
    let eventCtx := { ctx with
      opts := { ctx.opts with
        chroot := if failure.rootApplied then ctx.opts.chroot else none
        chdir := if failure.cwdApplied then ctx.opts.chdir else none }
      previousUser := none
      command := if failure.commandReady then ctx.command else none }
    let line := logLine eventCtx (some reason) allowed
      (if failure.commandReady then none else some (unresolvedLogCommand ctx))
      (rootApplied := failure.rootApplied)
    some { line with
      event := if failure.denial then .reject else .alert
      raw := failure.raw, commandReady := failure.commandReady
      lookupComplete := failure.lookupComplete
      msg := if failure.raw then logEscape ctx.invoking.name ++ " : " ++ logEscape reason else line.msg }

/-- Only %d and %% are special; other percent sequences pass through unchanged. -/
def formatAuthFailure (message : String) (attempts : Nat) : String :=
  String.ofList (go (toString attempts).toList message.toList)
where
  go (number : List Char) : List Char → List Char
    | '%' :: 'd' :: rest => number ++ go number rest
    | '%' :: '%' :: rest => '%' :: go number rest
    | c :: rest => c :: go number rest
    | [] => []

def authFailureMessage (ctx : Context) (attempts : Nat) : String :=
  match ctx.settings.authfailMessage with
  | some message => formatAuthFailure message attempts
  | none => s!"{attempts} incorrect password attempt{if attempts == 1 then "" else "s"}"

def authFailureLog (ctx : Context) (attempts : Nat) (noninteractive : Bool) : LogLine :=
  logLine ctx (some (if noninteractive then "a password is required"
    else authFailureMessage ctx attempts))

def successAdminFlag (ctx : Context) : Option String :=
  if (displayUser ctx).groups.any (fun g => g.1 == "sudo" || g.1 == "admin") then
    ctx.settings.adminFlag.map fun p =>
      if p.startsWith "~/" then (displayUser ctx).home ++ String.ofList (p.toList.drop 1) else p
  else none

/-- The pre-authentication checks follow sudoers_check_common: remote host,
    root_sudo, closefrom, numeric identities, implied shell, requiretty, valid shell. -/
def earlyFailure (ctx : Context) : Option FailureInfo :=
  if (Cli.timeoutError ctx.opts).isSome then
    some { message := s!"sudo: {(Cli.timeoutError ctx.opts).getD ""}\nsudo: error initializing audit plugin sudoers_audit\n", prefixed := false }
  else if ctx.opts.mode = .edit ∧ (invalidEditFile ctx).isSome then
    some { message := s!"sudoedit: {(invalidEditFile ctx).getD ""}: path is not absolute or contains a NUL byte, refusing\n", prefixed := false }
  else if ctx.opts.host.isSome && ctx.opts.mode != .list then
    some { (warningInfo "a remote host may only be specified when listing privileges."
      "user not allowed to set remote host for command") with commandReady := false, lookupComplete := false }
  else if ctx.invoking.uid == 0 && !ctx.settings.rootSudo then
    some { message := "sudoers specifies that root is not allowed to sudo" }
  else if ctx.opts.closeFrom.isSome && ctx.opts.closeFrom != some ctx.settings.closefrom.toNat &&
      !ctx.settings.closefromOverride then
    some { (warningInfo "you are not permitted to use the -C option"
      "user not allowed to override closefrom limit") with lookupComplete := false }
  else if ctx.targetUnknownUid && !ctx.settings.runasAllowUnknownId then
    let message := s!"unknown user {ctx.target.name}"
    some (warningInfo message message)
  else if ctx.targetUnknownGid && !ctx.settings.runasAllowUnknownId then
    let message := s!"unknown group {(ctx.targetGroup.map (·.name)).getD (ctx.opts.group.getD "")}"
    some (warningInfo message message)
  else if ctx.opts.impliedShell && !ctx.settings.shellNoargs then
    some { message := Cli.usageFor ctx.progname, prefixed := false }
  else if ctx.settings.requiretty && ctx.ttyName.isNone then
    some (warningInfo "sorry, you must have a tty to run sudo" "no tty")
  else if (ctx.opts.mode == .run || (ctx.opts.mode == .list && !ctx.opts.command.isEmpty)) &&
      ctx.settings.runasCheckShell && !ctx.validShells.contains ctx.target.shell then
    let message := s!"invalid shell for user {ctx.target.name}: {ctx.target.shell}"
    some { (warningInfo message message) with raw := true }
  else if ctx.opts.mode != .list && !ctx.settings.rootpw && ctx.settings.runaspw &&
      ctx.runasDefaultUser.isNone && ctx.settings.runasDefault != ctx.root.name then
    let message := s!"unknown user {ctx.settings.runasDefault}"
    some (warningInfo message message)
  else none

/-- These modes and failures cannot authorize a privileged operation. -/
def earlyAction (ctx : Context) : Option Action :=
  match ctx.opts.mode with
  | .help => some (.print (Cli.helpFor ctx.progname) 0)
  | .version => some (.print (Cli.versionFor (ctx.invoking.uid == 0) ctx.settings) 0)
  | .resetTimestamp => some .resetTimestamp
  | .removeTimestamp => some .removeTimestamp
  | _ => (earlyFailure ctx).map FailureInfo.action

/-- sudo checks listing authentication independently of `-l command` authorization. -/
def authJudgement (ctx : Context) (j : Judgement) : Judgement :=
  if ctx.opts.mode = .list then
    evaluate ctx.sudoers ctx.settings { request ctx with user := ctx.invoking, command := .list }
  else j

/-- Directory permission failures precede policy denial and command-not-found
    diagnostics, so an unauthorized -R never reveals namespace lookup facts. -/
def decisionFailure (ctx : Context) : Judgement → Option FailureInfo
  | .allow a => allowedFailure ctx a
  | .deny => permissionFailure ctx
      { needsAuth := ctx.settings.authenticate, setenv := ctx.settings.setenv, cwd := none }

def policyDecision (ctx : Context) (j : Judgement) : Decision :=
  let failure := decisionFailure ctx j
  let commandMode := ctx.opts.mode == .run || ctx.opts.mode == .edit
  let allowed := match j with | .allow a => some a | .deny => none
  let accepted := failure.isNone && commandMode && allowed.isSome
  { auth := authentication ctx (authJudgement ctx j),
    action := match j with
      | .allow a => allowedAction ctx a failure
      | .deny => (failure.map FailureInfo.action).getD (deniedAction ctx),
    updateTimestamp := policyNeedsAuth ctx (authJudgement ctx j) &&
      allowed.isSome && !ctx.opts.noUpdate && !ctx.opts.resetTimestamp,
    log := match failure with
      | some info => failureLog ctx info allowed
      | none => match j with
        | .allow a => if accepted && ctx.settings.logAllowed then some (logLine ctx none (some a)) else none
        | .deny => if ctx.settings.logDenied then some (logLine ctx (some (denialReason ctx))) else none,
    audit := match failure with
      | some info => info.auditReason.map AuditEvent.reject
      | none => match j with
        | .allow _ => if accepted && ctx.settings.logAllowed then some .accept else none
        | .deny => some (.reject (denialReason ctx)),
    adminFlag := if allowed.isSome && failure.all (·.adminFlag) then successAdminFlag ctx else none,
    mail := match failure with
      | some info => info.denial && ctx.mailerAvailable &&
          (ctx.settings.mailAlways || (commandMode && ctx.settings.mailAllCmnds) ||
            allowed.any (fun a => a.mail.getD false))
      | none => match j with
        | .deny => denialMail ctx
        | .allow a => accepted && ctx.mailerAvailable &&
            (a.mail.getD false || ctx.settings.mailAlways || ctx.settings.mailAllCmnds) }

def decide (ctx : Context) : Decision :=
  match earlyAction ctx with
  | some action =>
    let failure := match action with | .fail .. => earlyFailure ctx | _ => none
    let allowed := if failure.any (·.lookupComplete) then
      match policyJudgement ctx with | .allow a => some a | .deny => none
      else none
    { auth := .none, action, updateTimestamp := false,
      log := failure.bind (fun info => failureLog ctx info allowed),
      audit := failure.bind (fun info => info.auditReason.map AuditEvent.reject) }
  | none => policyDecision ctx (policyJudgement ctx)

end LeanSudo.Core
