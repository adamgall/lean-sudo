import LeanSudo.Core.Types
import LeanSudo.Policy.Eval
import LeanSudo.Policy.List

/-!
# Pure decision core

The shell supplies facts; only this total function authorizes execution. Unsupported
askpass/closefrom options fail closed. Listing another user's privileges is restricted
to root (unlike sudo's policy-dependent permission to use `-U`). With `runaspw`, the
shell must have resolved the default run-as account as the target; otherwise we refuse.
Authentication for `-l command` follows the listing policy, even when that command is
not permitted; the command check itself is silent, as in sudo 1.9.17p2.
Before policy evaluation, sudoedit rejects nonabsolute paths and empty, `.` or `..`
components after resolving relative operands against cwd. This deliberate fail-closed
restriction prevents textual policy matching from authorizing a different filesystem path.
Execution uses the command's lookup-time canonical path, the realpath used by policy
matching, rather than the user-controlled lookup path: repointing a lookup symlink
during authentication must not select a different executable. The original argv0
is preserved for multicall dispatch; command displays and SUDO_COMMAND retain the
lookup path. This does not pin an inode against replacement of the canonical file.
-/
namespace LeanSudo.Core

open Policy

def files (ctx : Context) : List String :=
  ctx.opts.command.map fun p => if p.startsWith "/" then p
    else ctx.cwd ++ (if ctx.cwd.endsWith "/" then "" else "/") ++ p

/-- The initial empty component denotes the root; every remaining component is literal. -/
def normalizedEditFile (p : String) : Bool :=
  p.startsWith "/" && (p.splitOn "/").tail.all (fun c => c != "" && c != "." && c != "..")

def invalidEditFile (ctx : Context) : Option String :=
  (files ctx).find? (fun p => !normalizedEditFile p)

def runCommand (ctx : Context) : Command :=
  match ctx.command with
  | some rc => .run rc.path rc.canonical rc.args
  | none => let typed := ctx.opts.command.headD ""; .run typed typed ctx.opts.command.tail

def request (ctx : Context) : Request :=
  { user := ctx.invoking, host := ctx.host, runasUser := ctx.target,
    runasGroup := ctx.targetGroup, runasUserExplicit := ctx.opts.user.isSome, canon := ctx.canon,
    command := match ctx.opts.mode with
      | .edit => .sudoedit (files ctx)
      | .list => if ctx.opts.command.isEmpty then .list else runCommand ctx
      | .validate => .validate
      | _ => runCommand ctx }

def authUser (ctx : Context) : Principal :=
  if ctx.settings.rootpw then
    { name := "root", uid := 0, gid := 0, groups := [], home := "/root", shell := "/bin/bash" }
  else if ctx.settings.runaspw || ctx.settings.targetpw then ctx.target else ctx.invoking

def sameIdentity (ctx : Context) : Bool :=
  ctx.target.uid == ctx.invoking.uid &&
    (ctx.opts.group.isNone || match ctx.targetGroup with
      | none => false
      | some g => ctx.invoking.groups.any (fun x => x.2 == g.gid))

def policyNeedsAuth (ctx : Context) (j : Judgement) : Bool :=
  ctx.invoking.uid != 0 && match j with
    | .deny => true
    | .allow a => a.needsAuth && !sameIdentity ctx

def tsValid (ctx : Context) : Bool :=
  !ctx.opts.resetTimestamp && Timestamp.lookup ctx.now ctx.settings.timestampTimeout
    ctx.tsScope (authUser ctx).uid ctx.tsRecords

def authentication (ctx : Context) (j : Judgement) : AuthReq :=
  if policyNeedsAuth ctx j && !tsValid ctx then .required (authUser ctx) else .none

def targetGid (ctx : Context) : Nat := (ctx.targetGroup.map (·.gid)).getD ctx.target.gid

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

def environment (ctx : Context) (a : Allowed) : EnvInput :=
  { userEnv := ctx.userEnv, settings := ctx.settings, invoking := ctx.invoking,
    target := ctx.target, command := commandText ctx, preserve := ctx.opts.preserveEnv,
    setenvAllowed := a.setenv, cmdlineVars := ctx.opts.envVars, loginShell := ctx.opts.login,
    setHome := ctx.opts.setHome, pamEnv := [], shellMode := ctx.opts.shell }

def pamService (ctx : Context) : String :=
  if ctx.opts.login then ctx.settings.pamLoginService else ctx.settings.pamService

def execPlan (ctx : Context) (a : Allowed) (rc : ResolvedCmd) : ExecPlan :=
  { path := rc.canonical, argv := rc.argv0 :: rc.args, envInput := environment ctx a,
    uid := ctx.target.uid, gid := targetGid ctx, groups := targetGroups ctx,
    cwd := if ctx.opts.login then some ctx.target.home else
      ctx.opts.chdir.or (a.cwd.join), umask := commandUmask ctx,
    usePty := ctx.settings.usePty, background := ctx.opts.background, closeFrom := 3,
    pamService := pamService ctx, pamSession := ctx.settings.pamSession,
    pamSetcred := ctx.settings.pamSetcred }

def editorWords (s : String) : List String :=
  (s.splitOn " ").flatMap (fun w => w.splitOn "\t") |>.filter (· != "")

def editors (ctx : Context) : List (List String) :=
  ((if ctx.settings.envEditor then
    ["SUDO_EDITOR", "VISUAL", "EDITOR"].filterMap (lookup ctx.userEnv) else []) ++
    ctx.settings.editor.splitOn ":").map editorWords |>.filter (! ·.isEmpty)

def editPlan (ctx : Context) (a : Allowed) : EditPlan :=
  { files := files ctx, editors := editors ctx, editUid := ctx.invoking.uid,
    editGid := ctx.invoking.gid, editGroups := ctx.invoking.groups.map (·.2),
    fileUid := ctx.target.uid, fileGid := targetGid ctx, fileGroups := targetGroups ctx,
    envInput := environment ctx a, umask := commandUmask ctx, pamService := pamService ctx,
    pamSession := ctx.settings.pamSession, pamSetcred := ctx.settings.pamSetcred }

def notFound (ctx : Context) : Action :=
  .fail s!"sudo: {ctx.opts.command.headD ""}: command not found\n" 1

def allowedAction (ctx : Context) (a : Allowed) : Action :=
  match ctx.opts.mode with
  | .run => match ctx.command with
    | none => notFound ctx
    | some rc =>
      if ctx.opts.chdir.isSome && a.cwd != some none then
        .fail s!"sudo: you are not permitted to use the -D option with {rc.path}\n" 1
      else match buildEnv (environment ctx a) with
        | .error e => .fail ("sudo: " ++ e ++ "\n") 1
        | .ok _ => .exec (execPlan ctx a rc)
  | .edit =>
    if ctx.opts.chdir.isSome then .fail "sudo: the -D option is not supported with sudoedit\n" 1
    else match buildEnv (environment ctx a) with
      | .error e => .fail ("sudo: " ++ e ++ "\n") 1
      | .ok _ => .edit (editPlan ctx a)
  | .list =>
    if ctx.opts.command.isEmpty then
      .print (listPrivileges ctx.sudoers ctx.settings (ctx.listUser.getD ctx.invoking)
        ctx.host ctx.canon) 0
    else match ctx.command with
      | none => notFound ctx
      | some _ => .print (commandText ctx ++ "\n") 0
  | .validate => .validate
  | _ => .fail "sudo: invalid policy mode\n" 1

def userMatches (ctx : Context) : Bool :=
  let al := aliasesOf ctx.sudoers
  (specsOf ctx.sudoers).any (fun us => userListOk al al.fuel ctx.invoking us.users)

def hostMatches (ctx : Context) : Bool :=
  let al := aliasesOf ctx.sudoers
  (specsOf ctx.sudoers).any fun us => userListOk al al.fuel ctx.invoking us.users &&
    us.entries.any (fun hc => hostListOk al al.fuel ctx.host hc.hosts)

def denialReason (ctx : Context) : String :=
  if !userMatches ctx then "user NOT in sudoers"
  else if !hostMatches ctx then "user NOT authorized on host" else "command not allowed"

def deniedAction (ctx : Context) : Action :=
  if ctx.opts.mode = .list then
    if ctx.opts.command.isEmpty then .fail (notAllowedMessage ctx.invoking.name ctx.host) 1
    else .print "" 1
  else if ctx.opts.mode = .validate then .fail (notAllowedMessage ctx.invoking.name ctx.host) 1
  else if !userMatches ctx then .fail s!"{ctx.invoking.name} is not in the sudoers file.\n" 1
  else if !hostMatches ctx then
    .fail s!"{ctx.invoking.name} is not allowed to run sudo on {ctx.host}.\n" 1
  else if ctx.command.isNone && ctx.opts.mode = .run then notFound ctx
  else
    let target := ctx.target.name ++ (ctx.targetGroup.map (fun g => ":" ++ g.name)).getD ""
    .fail s!"Sorry, user {ctx.invoking.name} is not allowed to execute '{commandText ctx}' as {target} on {ctx.host}.\n" 1

def logLine (ctx : Context) (reason : Option String) : LogLine :=
  let tty := match ctx.ttyName with
    | none => "unknown"
    | some t => if t.startsWith "/dev/" then String.ofList (t.toList.drop 5) else t
  { priority := if reason.isSome then "alert" else "notice",
    msg := ctx.invoking.name ++ " : " ++ (reason.map (· ++ " ; ")).getD "" ++
      s!"TTY={tty} ; PWD={ctx.cwd} ; USER={ctx.target.name} ; " ++
      (ctx.targetGroup.map (fun g => s!"GROUP={g.name} ; ")).getD "" ++
      "COMMAND=" ++ commandText ctx }

/-- These modes and failures cannot authorize a privileged operation. -/
def earlyAction (ctx : Context) : Option Action :=
  match ctx.opts.mode with
  | .help => some (.print (Cli.helpFor ctx.progname) 0)
  | .version => some (.print Cli.versionText 0)
  | .resetTimestamp => some .resetTimestamp
  | .removeTimestamp => some .removeTimestamp
  | _ =>
    if ctx.opts.mode = .edit ∧ (invalidEditFile ctx).isSome then
      some (.fail s!"sudoedit: {(invalidEditFile ctx).getD ""}: path is not absolute or contains empty, . or .. components, refusing\n" 1)
    else if ctx.settings.requiretty && ctx.ttyName.isNone then
      some (.fail "sudo: sorry, you must have a tty to run sudo\n" 1)
    else if ctx.opts.askpass then some (.fail "sudo: askpass is not supported\n" 1)
    else if ctx.opts.closeFrom.isSome then
      some (.fail "sudo: you are not permitted to use the -C option\n" 1)
    else if ctx.opts.otherUser.isSome && ctx.invoking.uid != 0 then
      some (.fail "sudo: only root may use the -U option\n" 1)
    else if !ctx.settings.rootpw && ctx.settings.runaspw &&
      ctx.target.name != ctx.settings.runasDefault then
      some (.fail "sudo: runaspw requires the default runas user as target\n" 1)
    else none

/-- sudo checks listing authentication independently of `-l command` authorization. -/
def authJudgement (ctx : Context) (j : Judgement) : Judgement :=
  if ctx.opts.mode = .list then
    evaluate ctx.sudoers ctx.settings { request ctx with command := .list }
  else j

def policyDecision (ctx : Context) (j : Judgement) : Decision :=
  { auth := authentication ctx (authJudgement ctx j),
    action := match j with | .allow a => allowedAction ctx a | .deny => deniedAction ctx,
    updateTimestamp := policyNeedsAuth ctx (authJudgement ctx j) &&
      (match j with | .allow _ => true | .deny => false) &&
      !ctx.opts.noUpdate && !ctx.opts.resetTimestamp,
    log := match j with
      | .allow _ => if ctx.settings.logAllowed then some (logLine ctx none) else none
      | .deny => if ctx.settings.logDenied then some (logLine ctx (some (denialReason ctx))) else none }

def decide (ctx : Context) : Decision :=
  match earlyAction ctx with
  | some action => { auth := .none, action, updateTimestamp := false, log := none }
  | none => policyDecision ctx (evaluate ctx.sudoers ctx.settings (request ctx))

end LeanSudo.Core
