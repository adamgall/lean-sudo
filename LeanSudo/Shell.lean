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
import LeanSudo.Sys.Lookup
import LeanSudo.Sys.GroupPlugin
import LeanSudo.SudoConf
import LeanSudo.Nsswitch
import LeanSudo.Sys.Sss
import LeanSudo.Util.Sha2
import LeanSudo.Insults
import LeanSudo.EventLog
import LeanSudo.Sys.IoLog
import LeanSudo.Sys.LogSrv
import LeanSudo.I18n.Load
import LeanSudo.Intercept
import LeanSudo.Sys.Intercept
import LeanSudo.Sys.Plugins

/-! Linux IO boundary: collect facts, execute the verified decision, and bracket PAM
resources. Policy decisions belong to `Core.decide`, not this module. -/
namespace LeanSudo.Shell

private def warn (msg : String) : IO Unit := do
  Sys.writeStderr ("sudo: " ++ (← I18n.translate msg) ++ "\n")

private def groupNames (gids : List Nat) : IO (List (String × Nat)) :=
  gids.eraseDups.mapM fun gid => do
    let g ← Sys.getgrgid gid
    return (g.map (·.name) |>.getD ("#" ++ toString gid), gid)

private def principal (pw : Sys.Passwd) (gids : List Nat) : IO Principal := do
  return {
    name := pw.name, uid := pw.uid, gid := pw.gid
    groups := ← groupNames (pw.gid :: gids), home := pw.home, shell := pw.shell }

private def hashId (name : String) : Option Nat :=
  if name.startsWith "#" then
    (name.drop 1).toString.toNat?.filter (· < UInt32.size - 1)
  else none

private def lookupUser (name : String) : IO (Option Sys.Passwd) :=
  if name.startsWith "#" then
    match hashId name with | some uid => Sys.getpwuid uid | none => pure none
  else Sys.getpwnam name

private def user (name : String) : IO Principal := do
  let pw ← lookupUser name
  let some pw := pw | throw (IO.userError ("unknown user " ++ name))
  principal pw (← Sys.getgrouplist pw.name pw.gid)

private def timestampOwnerIds : Option String → IO (Nat × Nat)
  | none => pure (0, 0)
  | some name => do
    let owner ← lookupUser name
    let owner ← if owner.isNone then Sys.getpwnam name else pure owner
    let some owner := owner |
      throw (IO.userError ("timestampowner: unknown user " ++ name))
    pure (owner.uid, owner.gid)

private def targetUser (name : String) (realGid : Nat) : IO (Principal × Bool) := do
  if let some pw ← lookupUser name then
    return (← principal pw (← Sys.getgrouplist pw.name pw.gid), false)
  if let some uid := hashId name then
    let groups ← groupNames [realGid]
    return ({ name, uid, gid := realGid, groups, home := "/", shell := "/bin/sh" }, true)
  throw (IO.userError ("unknown user " ++ name))

private def group (name : String) : IO (GroupInfo × Bool) := do
  if let some gid := hashId name then
    if let some g ← Sys.getgrgid gid then return (g, false)
    return ({ name, gid }, true)
  if let some g ← Sys.getgrnam name then return (g, false)
  throw (IO.userError ("unknown group " ++ name))

private def absolute (cwd path : String) : String :=
  if path.startsWith "/" then path else cwd ++ "/" ++ path

/-- Match sudo 1.9.17p2: inspect prefixed names without changing the policy
process's root or consulting NSS inside an untrusted filesystem. -/
private def rootedPath (root : Option String) (path : String) : String :=
  root.map (· ++ path) |>.getD path

private def rootRelative (root : Option String) (path fallback : String) : String :=
  match root with
  | none | some "/" => path
  | some root =>
    if path == root then "/"
    else if path.startsWith (root ++ "/") then (path.drop root.length).toString
    else fallback

private def canonicalRoot (root : Option String) : IO (Option String) := do
  root.mapM fun p => return (← Sys.realpath p).getD p

private def executable (path : String) : IO Bool := do
  let some st ← Sys.stat path | return false
  return st.isReg && (← Sys.access path 1)

private def lookupAs (paths : Array (String × Bool)) (uid gid : Nat)
    (groups : List Nat) (ignoreDot : Bool) (root : Option String := none) :
    IO (Option String × Bool) := do
  let facts ← Sys.Lookup.inspectPaths (paths.map (fun p => rootedPath root p.1)) uid gid groups.toArray
  for i in [:paths.size] do
    if let some st := facts[i]! then
      if Sys.Lookup.executable st then
        let (path, dot) := paths[i]!
        return if dot && ignoreDot then (none, true) else (some path, false)
  return (none, false)

private def resolvePath (search name : String) (ignoreDot : Bool)
    (invoking target : Principal) (realGid targetGid : Nat) (targetGroups : List Nat)
    (root : Option String := none) : IO (Option String × Bool) := do
  let paths := if name.contains '/' then #[(name, false)] else Id.run do
    let mut paths := #[]
    let mut dot := false
    for dir in search.splitOn ":" do
      if dir == "" || dir == "." then dot := true
      else paths := paths.push (dir ++ "/" ++ name, false)
    if dot then paths := paths.push ("./" ++ name, true)
    return paths
  let found ← lookupAs paths target.uid targetGid targetGroups ignoreDot root
  -- NOT_FOUND_DOT is terminal: only NOT_FOUND retries as the invoking user.
  if found.1.isSome || found.2 then return found
  lookupAs paths invoking.uid realGid (invoking.groups.map (·.2)) ignoreDot root

private def resolveCommand (opts : Cli.Options) (invoking target : Principal)
    (env : EnvList) (cwd : String) (st : Settings) (realGid : Nat)
    (targetGroup : Option GroupInfo) (root : Option String := none) :
    IO (Option Core.ResolvedCmd × Bool) := do
  if opts.mode != .run && opts.mode != .list then return (none, false)
  let search := (if userIsExempt st invoking then none else st.securePath).getD
    ((env.lookup "PATH").getD "/usr/bin:/bin")
  let (name, argv) := if opts.shell || opts.login then
      let shell := Cli.userShell (if opts.login then none else env.lookup "SHELL")
        (if opts.login then target.shell else invoking.shell)
      let cmd := Cli.shellCommand shell opts.login opts.command
      (cmd.path, cmd.argv)
    else (opts.command.headD "", opts.command)
  if name.isEmpty then return (none, false)
  let targetGid := (targetGroup.map (·.gid)).getD target.gid
  let targetGroups := (if opts.preserveGroups || st.preserveGroups then invoking.groups
    else target.groups).map (·.2)
  let (found, inDot) ← resolvePath search name st.ignoreDot invoking target realGid targetGid targetGroups root
  let some path := found | return (none, inDot)
  let directory := Policy.dirOf path
  let inspected := if root.isSome then rootedPath root directory else absolute cwd directory
  let some parent ← Sys.realpath inspected |
    throw (IO.userError ("unable to resolve command directory: " ++ directory))
  let parent := rootRelative (← canonicalRoot root) parent directory
  return (some {
    path, canonical := parent ++ "/" ++ Policy.baseOf path
    argv0 := argv.headD name, args := argv.drop 1 }, false)

private def atomPaths : Sudoers.CmndAtom → List String
  | .command path _ => [path]
  | .digest _ atom => atomPaths atom
  | _ => []

private def entryNames (u : Sudoers.UserAtom → Option String)
    (h : Sudoers.HostAtom → Option String) : Sudoers.Entry → List String
  | .userAlias _ ms | .runasAlias _ ms => ms.filterMap (u ∘ (·.atom))
  | .hostAlias _ ms => ms.filterMap (h ∘ (·.atom))
  | .defaults (.user ms) _ | .defaults (.runas ms) _ => ms.filterMap (u ∘ (·.atom))
  | .defaults (.host ms) _ => ms.filterMap (h ∘ (·.atom))
  | .userSpec us => us.users.filterMap (u ∘ (·.atom)) ++ us.entries.flatMap (fun host =>
      host.hosts.filterMap (h ∘ (·.atom)) ++ host.cmnds.flatMap (fun c =>
        c.runas.toList.flatMap (fun r => (r.users.getD []).filterMap (u ∘ (·.atom)))))
  | _ => []

private def netgroupNames := entryNames
  (fun | .netgroup n => some n | _ => none)
  (fun | .netgroup n => some n | _ => none)

private def pluginGroupNames := entryNames
  (fun | .nonunixGroup n | .group n => some n
       | .nonunixGid n | .gid n => some ("#" ++ toString n)
       | _ => none)
  (fun _ => none)

private def loadGroupPlugin (config : Option String) : IO (Option Sys.GroupPlugin.Handle) := do
  let some config := config | return none
  try Sys.GroupPlugin.load config catch e => warn e.toString; return none

private def gatherPluginFacts (policy : Sudoers.Sudoers) (r : Request)
    (plugin : Option Sys.GroupPlugin.Handle) (otherUsers : List String := []) : IO Request := do
  let some plugin := plugin | return { r with pluginGroups := [] }
  let users := ([r.user.name, r.runasUser.name, "root"] ++ otherUsers).eraseDups
  let groups := (policy.flatMap pluginGroupNames).eraseDups
  let queries := users.flatMap fun u => groups.map (u, ·)
  let pluginGroups ← queries.mapM fun (u, g) =>
    return (u, g, ← Sys.GroupPlugin.query plugin u g)
  return { r with pluginGroups }

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

private def gatherCommandFacts (policy : Sudoers.Sudoers) (r : Request)
    (policyLocale : String := "C") (root : Option String := none) : IO Request := do
  let atoms := policy.flatMap Sudoers.Parser.cmndAtoms
  let paths := (atoms.flatMap atomPaths).eraseDups
  let rootCanon ← canonicalRoot root
  let globPaths ← (paths.filter Glob.hasGlob).mapM fun p => do
    let expandedPaths ← Sys.globPaths (rootedPath root p) policyLocale
    return (p, expandedPaths.map fun q => rootRelative root q q)
  let expanded := paths ++ globPaths.flatMap (·.2)
  let commandPaths := match r.command with | .run p canonical _ => some (p, canonical) | _ => none
  let requested := commandPaths.toList.map (·.1)
  -- Keep the parent selected during lookup; do not resolve the invoking user's
  -- original directory a second time while collecting decision facts.
  let inspected := fun p => match commandPaths with
    | some (requested, canonical) =>
      if p == requested then canonical
      else if p == Policy.dirOf requested then Policy.dirOf canonical else p
    | none => p
  let names := expanded ++ (expanded.filter (·.endsWith "/")).flatMap
    (fun dir => requested.map (fun p => dir ++ Policy.baseOf p)) ++ requested
  let names := (names ++ names.map Policy.dirOf).eraseDups
  let table ← names.mapM fun p => do
    let resolved := inspected p
    if commandPaths.any (fun c => p == Policy.dirOf c.1) then return (p, resolved)
    let hostPath := rootedPath root resolved
    return (p, rootRelative rootCanon ((← Sys.realpath hostPath).getD hostPath) resolved)
  let canon := fun p => (table.lookup p).getD p
  let fileIds ← names.filterMapM fun p => do
    return (← Sys.stat (rootedPath root (inspected p))).map (fun s => (p, s.dev, s.ino))
  let subjects := match r.command with
    | .run p _ args => [p, canon (Policy.dirOf p) ++ "/" ++ Policy.baseOf p, " ".intercalate args]
    | .sudoedit args => [" ".intercalate args]
    | _ => []
  let regexMatches ← ((atoms.flatMap regexPatterns).eraseDups.flatMap
    (fun p => subjects.map (p, ·))).mapM fun (p, s) => return (p, s, ← Sys.regexMatches p s policyLocale)
  return { r with canon, canonPaths := table, fileIds, globPaths, regexMatches }

/-- An escaping symlink cannot be interpreted safely by sudo's prefix-based
lookup. Keep its diagnostic with this candidate, not an unrelated root's rule. -/
private def rootEscape (root path : String) : IO (Option String) := do
  if root == "*" then return none
  for name in [path, Policy.dirOf path] do
    if ← Sys.rootPathEscapes root name then
      return some (path ++ ": command resolves outside the chroot directory")
  return none

private def commandDigests (algos : List Sudoers.DigestAlgo) (path : String) :
    IO (List Sudoers.Digest) := do
  if algos.isEmpty then return []
  let bytes ← IO.FS.readBinFile path
  return algos.map fun algo => { algo, bytes := (Sha2.digest algo bytes).data.toList }

private def pinCommand (path : Option String) (enabled : Bool)
    (algos : List Sudoers.DigestAlgo) :
    IO (Option (Nat × Sys.FileStat) × List Sudoers.Digest) := do
  let pinned ← if enabled then path.mapM Sys.openCommand else pure none
  let digests ← match pinned with
    | some (fd, _) => commandDigests algos s!"/proc/self/fd/{fd}"
    | none => pure []
  return (pinned, digests)

private def commandSetid (pinned : Option (Nat × Sys.FileStat)) (path : Option String) :
    IO Bool := do
  let inode ← match pinned with
    | some (_, inode) => pure (some inode)
    | none => match path with
      | some path => Sys.stat path
      | none => pure none
  return inode.any (fun s => s.mode &&& 0o6000 != 0)

private def rootCommandFacts (policy : Sudoers.Sudoers) (opts : Cli.Options)
    (invoking target : Principal) (env : EnvList) (cwd : String) (st : Settings)
    (realGid : Nat) (targetGroup : Option GroupInfo) (homes : List (String × String))
    (fallback : Option Core.ResolvedCmd) (r : Request) (root : String)
    (algos : List Sudoers.DigestAlgo) (baselineRoot : Option String) : IO RootCommandFacts := do
  let expanded := Core.expandHomePath target.home homes root
  let rootPath := expanded.getD root
  let lookupRoot := Sys.commandLookupRoot (some rootPath)
  let resolved ← if baselineRoot == some root then pure fallback else do
    let result ← resolveCommand opts invoking target env cwd st realGid targetGroup lookupRoot
    pure result.1
  -- sudo retains the original command and lookup status when a rule-specific
  -- lookup fails, allowing ALL and exact-name matching to proceed.
  let chosen := if lookupRoot.isNone then resolved else resolved.or fallback
  let command := chosen.map (fun c => Command.run c.path c.canonical
    (if opts.shell || opts.login then opts.command else c.args)) |>.getD r.command
  let refusal ← if expanded.isNone then pure (some ("invalid chroot directory: " ++ root))
    else match command with
      | .run path _ _ => rootEscape rootPath path
      | _ => pure none
  let facts ← if baselineRoot == some root then pure r else
    gatherCommandFacts policy { r with command } st.sudoersLocale lookupRoot
  let pinPath := (if lookupRoot.isNone then chosen else resolved).map
    (fun c => rootedPath lookupRoot c.canonical)
  let (pinned, digests) ← pinCommand pinPath
    (refusal.isNone && (!algos.isEmpty || st.fdexec == "always")) algos
  let execFd := pinned.map (·.1)
  let fileIds := match pinned, resolved with
    | some (_, s), some c => (c.path, s.dev, s.ino) :: facts.fileIds.filter (·.1 != c.path)
    | _, _ => facts.fileIds
  let setid ← commandSetid pinned (chosen.map (fun c => rootedPath lookupRoot c.canonical))
  return {
    command, argv := chosen.map (fun c => c.argv0 :: c.args) |>.getD [],
    found := chosen.isSome || opts.mode == .edit, execFd, canonPaths := facts.canonPaths, fileIds,
    setid,
    globPaths := facts.globPaths, regexMatches := facts.regexMatches, digests, refusal }

private def gatherFacts (policy : Sudoers.Sudoers) (r : Request)
    (otherUsers : List String := []) (policyLocale : String := "C")
    (otherHosts : List String := []) (root : Option String := none) : IO Request := do
  let r ← gatherCommandFacts policy r policyLocale root
  let users := ([none, some r.user.name, some r.runasUser.name, some "root"] ++
    otherUsers.map some).eraseDups
  let hosts := ([none, some r.lhost, some r.host] ++ otherHosts.map some).eraseDups
  let queries := (policy.flatMap netgroupNames).eraseDups.flatMap fun n =>
    users.flatMap fun u => hosts.map fun h => (n, u, h)
  let domain ← Sys.domainName
  let netgroups ← queries.mapM fun (n, u, h) => return (n, u, h, ← Sys.inNetgroup n h u domain)
  return { r with netgroups }

private def defaults (policy : Sudoers.Sudoers) (invoking : Principal) (host : String)
    (runas : Option Principal) (cmd : Option Command) (facts : Request)
    (promptOverride : Bool) (emitWarnings : Bool := false) : IO Settings := do
  let (settings, warnings) ← IO.ofExcept
    (Policy.resolveDefaults policy invoking host runas cmd facts.canon (some facts)
      { passpromptOverride := promptOverride })
  if emitWarnings then for warning in warnings do warn warning
  return settings

private def identityInitializationFailure (opts : Cli.Options) (invoking : Principal)
    (tty : Option String) (cwd : String) (resolvedGroup : Option String) (message : String) : IO α := do
  -- init_vars has not populated command argv yet: sudo logs this warning but
  -- its Linux audit backend skips the null argv (there is no USER_CMD record).
  let body := Core.logEscape message ++ " ; " ++
    (tty.map (fun t => "TTY=" ++ Core.logEscape (if t.startsWith "/dev/" then (t.drop 5).toString else t) ++ " ; ")).getD "" ++
    "PWD=" ++ Core.logEscape cwd ++ " ; " ++
    (opts.user.map (fun name => "USER=" ++ Core.logEscape name ++ " ; ")).getD "" ++
    ((resolvedGroup.or opts.group).map (fun name => "GROUP=" ++ Core.logEscape name ++ " ; ")).getD ""
  for bytes in EventLog.splitSyslogBytes invoking.name body 960 do
    Sys.syslogBytes "authpriv" "alert" bytes false
  warn message
  throw (IO.userError "error initializing audit plugin sudoers_audit")

/-- The early fqdn callback precedes logfile/format Defaults callbacks. Local
lookup failure is a raw parse alert; failure resolving only `-h` is NO_LOG. -/
private def hostnameWarning (invoking : Principal) (host message : String)
    (log : Bool) : IO Unit := do
  let reason := "unable to resolve host " ++ host ++ ": " ++ message
  if log then
    let text ← I18n.translateLog "C" reason
    for bytes in EventLog.splitSyslogBytes invoking.name (Core.logEscape text) 960 do
      Sys.syslogBytes "authpriv" "alert" bytes false
  warn reason

private def loadSources (sources : List Nsswitch.Source) (host : String)
    (invoking : Principal) (other : Option Principal) :
    IO (List (Nsswitch.Source × List Sudoers.Located)) :=
  sources.mapM fun source => do
    if source.name == "files" then return (source, ← Sudoers.load host)
    let (defs, rules) ← Sys.Sss.query invoking.uid.toUInt32 invoking.name
    let rules ← match other with
      | some p => do
        if p.uid == invoking.uid then pure rules else
          let (_, extra) ← Sys.Sss.query p.uid.toUInt32 p.name
          pure ((rules.toList ++ extra.toList).eraseDups.toArray)
      | none => pure rules
    return (source, ← IO.ofExcept (Sss.convert defs rules))

private def localTimeBounds (policy : Sudoers.Sudoers) : IO (List (Nat × Nat)) := do
  let bounds := policy.flatMap fun
    | .userSpec spec => spec.entries.flatMap fun entry => entry.cmnds.flatMap fun cs =>
      (if cs.options.notBeforeLocal then cs.options.notBefore.toList else []) ++
      (if cs.options.notAfterLocal then cs.options.notAfter.toList else [])
    | _ => []
  let mut resolved := []
  for civil in bounds.eraseDups do
    if let some epoch ← Sys.localCivilEpoch civil then
      -- Pre-epoch bounds retain the parser's contemporary-clock zero model.
      resolved := (civil, epoch.toNat) :: resolved
  return resolved.reverse

private def selectSources (sources : List (Nsswitch.Source × List Sudoers.Located))
    (st : Settings) (r : Request) : List Sudoers.Located :=
  let selected := Nsswitch.select (fun entries =>
    !(Policy.candidates (entries.map (·.entry)) st r).isEmpty)
    (!Policy.isRunCmd r.command) sources false
  -- Defaults are collected from all backends before authorization lookup.
  let defs := sources.flatMap fun (_, entries) => entries.filter fun l =>
    match l.entry with | .defaults _ _ => true | _ => false
  defs ++ selected.flatten.filter (fun l =>
    match l.entry with | .defaults _ _ => false | _ => true)

private def privilegeDefaults (policy : Sudoers.Sudoers) (st : Settings)
    (r : Request) : IO Settings := do
  if !Policy.isRunCmd r.command then return st
  let some winner := (Policy.candidates policy st r).getLast? | return st
  let (st, warnings) ← IO.ofExcept
    (Policy.applySettings st (winner.spec.ldapOptions.map Sss.parseOption))
  for message in warnings do warn message
  return st

private def timestampConfig (ctx : Core.Context) : Sys.TimestampConfig := {
  directory := ctx.settings.timestampdir, uid := ctx.invoking.uid
  ownerUid := ctx.timestampOwnerUid, ownerGid := ctx.timestampOwnerGid }

private def timestampKey (ctx : Core.Context) : Sys.TimestampKey := {
  scope := ctx.tsScope, lockScope := ctx.tsLockScope
  sid := ctx.tsSessionId, authUid := (Core.authUser ctx).uid }

private def withCredentialCache (ctx : Core.Context)
    (f : List Timestamp.Record → IO (Option Timestamp.Record × α))
    (report : String → IO Unit) : IO α := do
  if ctx.opts.resetTimestamp || ctx.settings.timestampTimeout == some 0 then return (← f []).2
  Sys.withTimestampFile (timestampConfig ctx) (timestampKey ctx) f report

private def context (progname : String) (opts : Cli.Options) (conf : SudoConf.Config) : IO Core.Context := do
  if let some message := Cli.timeoutError opts then
    warn message
    throw (IO.userError "error initializing audit plugin sudoers_audit")
  let uid ← Sys.getuid
  let invokingRealGid ← Sys.getgid
  let some pw ← Sys.getpwuid uid | throw (IO.userError "you do not exist in the passwd database")
  let kernelGroups ← Sys.getgroups
  let gids ← if conf.groupSource == "dynamic" ||
      (conf.groupSource == "adaptive" && kernelGroups.length >= conf.maxGroups) then
      Sys.getgrouplist pw.name pw.gid else pure kernelGroups
  let invoking ← principal pw gids
  let rawHost ← Sys.gethostname
  let lookupHost := opts.host.getD rawHost
  let hostResult ← Sys.canonicalHostname lookupHost
  let canonicalHost := match hostResult with | .ok host => host | .error _ => lookupHost
  let longHost := canonicalHost
  let host := (longHost.splitOn ".").headD "localhost"
  let cwd ← Sys.getcwd
  let mask ← Sys.umask 0
  let _ ← Sys.umask mask
  let ttyDevice ← Sys.ttyDevice
  let ttyName ← ttyFor ttyDevice conf.devsearch
  let userEnv ← Sys.environ
  let targetGroupInfo ← try opts.group.mapM group catch e =>
    identityInitializationFailure opts invoking ttyName cwd none e.toString
  let requestedTarget ← try opts.user.mapM (fun name => targetUser name invokingRealGid) catch e =>
    identityInitializationFailure opts invoking ttyName cwd (targetGroupInfo.map (·.1.name)) e.toString
  let nss ← try IO.FS.readFile "/etc/nsswitch.conf" catch e =>
    match e with | .noFileOrDirectory _ _ _ => pure "" | _ => throw e
  let sources ← IO.ofExcept (Nsswitch.configure nss)
  let listUser ← opts.otherUser.mapM user
  let loadedSources ← loadSources sources host invoking listUser
  let ipaHost ← if sources.any (·.name == "sss") && lookupHost.toLower == rawHost.toLower then
      try pure (Sss.ipaHostname (← IO.FS.readFile "/etc/sssd/sssd.conf"))
      catch _ => pure none
    else pure none
  let ipaHosts := ipaHost.toList.flatMap fun h => [h, (h.splitOn ".").headD h]
  let locatedSudoers := loadedSources.flatMap (·.2)
  let policy := locatedSudoers.map (·.entry)
  let _ ← IO.ofExcept (Policy.validate policy)
  let addresses ← if conf.probeInterfaces then Sys.interfaceAddresses else pure #[]
  let interfaces := addresses.toList.filterMap fun (a, m) =>
    (Sudoers.Parser.ipAddress a).bind fun ip =>
      (Sudoers.Parser.ipAddress m).map fun mask => (ip, mask)
  let wallTime ← Sys.unixTime
  let localTimeBounds ← localTimeBounds policy
  let base : Request := {
    user := invoking, host, lhost := longHost, interfaces
    runasUser := invoking, runasGroup := none, runasUserExplicit := opts.user.isSome
    command := .list, now := wallTime, localTimeBounds }
  let preliminary ← gatherFacts policy base
  let initial ← defaults policy invoking host none none preliminary opts.prompt.isSome
  let plugin ← loadGroupPlugin initial.groupPlugin
  let pluginConfig := initial.groupPlugin
  let preliminary ← gatherPluginFacts policy preliminary plugin
  let initial ← defaults policy invoking host none none preliminary opts.prompt.isSome
  let submitHostResult ← if lookupHost == rawHost then pure hostResult
    else if initial.fqdn then Sys.canonicalHostname rawHost else pure (.ok rawHost)
  if initial.fqdn then
    if let .error message := hostResult then
      match submitHostResult with
      | .error _ => hostnameWarning invoking rawHost message true
      | .ok _ => hostnameWarning invoking lookupHost message false
  let submitHost := if initial.fqdn then
      some (match submitHostResult with | .ok name => name | .error _ => canonicalHost)
    else some rawHost
  let longHost := if initial.fqdn then canonicalHost else lookupHost
  let host := (longHost.splitOn ".").headD "localhost"
  let (target, targetUnknownUid) ← match requestedTarget with
    | some target => pure target
    | none =>
      if opts.group.isSome then pure (invoking, false)
      else targetUser initial.runasDefault invokingRealGid
  let targetGroup := targetGroupInfo.map (·.1)
  let targetUnknownGid := targetGroupInfo.any (·.2)
  let lookupSettings ← defaults policy invoking host (some target) none
    { preliminary with runasUser := target, runasGroup := targetGroup } opts.prompt.isSome
  let roots := (opts.chroot.toList ++ lookupSettings.runchroot.toList ++ policy.flatMap
    (fun e => match e with
      | .userSpec us => us.entries.flatMap fun h => h.cmnds.filterMap (·.options.chroot)
      | .defaults _ settings => settings.filterMap fun s =>
        if s.name == "runchroot" then match s.op with | .assign p => some p | _ => none
        else none
      | _ => [])).eraseDups
  let homePaths := roots ++ opts.chdir.toList ++ lookupSettings.runcwd.toList ++
    policy.flatMap (fun e => match e with
      | .userSpec us => us.entries.flatMap fun h => h.cmnds.filterMap (fun c => c.options.cwd.join)
      | _ => [])
  let homeNames := (homePaths.filter (·.startsWith "~")).map
    (fun p => ((p.drop 1).toString.splitOn "/").headD "")
  let homes ← homeNames.eraseDups.filterMapM fun n => do
    return (← Sys.getpwnam n).map (fun pw => (n, pw.home))
  let lookupRoot := Sys.commandLookupRoot (opts.chroot.or lookupSettings.runchroot)
  let expandedLookupRoot := lookupRoot.bind (Core.expandHomePath target.home homes)
  let (command, commandFoundInDot) ← resolveCommand opts invoking target userEnv cwd initial
    invokingRealGid targetGroup expandedLookupRoot
  let policyCommand := if opts.mode == .edit then some (.sudoedit opts.command) else
    if opts.mode == .run || (opts.mode == .list && !opts.command.isEmpty) then
      some (command.map (fun c => .run c.path c.canonical
        (if opts.shell || opts.login then opts.command else c.args)) |>.getD
        (.run (opts.command.headD "") (opts.command.headD "") opts.command.tail))
    else none
  let facts ← gatherFacts policy { base with
    host := host
    lhost := longHost
    runasUser := target
    runasGroup := targetGroup
    command := policyCommand.getD .list
    requestedChroot := opts.chroot, defaultChroot := lookupSettings.runchroot
    } (listUser.toList.map (·.name)) initial.sudoersLocale ipaHosts expandedLookupRoot
  let facts ← gatherPluginFacts policy facts plugin (listUser.toList.map (·.name))
  let algos := ((policy.flatMap Sudoers.Parser.cmndAtoms).flatMap digestAlgos).eraseDups
  let beforeDigest ← defaults policy invoking host (some target) policyCommand facts opts.prompt.isSome
  let facts ← if beforeDigest.groupPlugin == pluginConfig then pure facts else do
    for handle in plugin do Sys.GroupPlugin.close handle
    let replacement ← loadGroupPlugin beforeDigest.groupPlugin
    try gatherPluginFacts policy facts replacement (listUser.toList.map (·.name))
    finally for handle in replacement do Sys.GroupPlugin.close handle
  for handle in plugin do Sys.GroupPlugin.close handle
  let loadedSources := loadedSources.map fun (source, entries) =>
    (source, if source.name == "sss" then
      ipaHost.map (Sss.withIpaHost entries initial facts (invoking :: listUser.toList)) |>.getD entries
    else entries)
  let policy := (loadedSources.flatMap (·.2)).map (·.entry)
  let beforeDigest ← defaults policy invoking host (some target) policyCommand facts opts.prompt.isSome
  let activeRoots := match facts.command with
    | .run .. => opts.chroot.map (fun root => [root]) |>.getD roots
    | _ => []
  let needsPinnedRoot := policy.any fun e => match e with
    | .userSpec us => us.entries.any fun h => h.cmnds.any fun c =>
      c.ldapOptions.any fun option =>
        let setting := Sss.parseOption option
        setting.name == "fdexec" && setting.op == .assign "always"
    | _ => false
  let rootPinSettings := if needsPinnedRoot then { beforeDigest with fdexec := "always" } else beforeDigest
  let rootFacts ← activeRoots.mapM fun root => do
    let gathered ← rootCommandFacts policy opts invoking target userEnv cwd rootPinSettings
      invokingRealGid targetGroup homes command facts root algos lookupRoot
    return (root, gathered)
  let facts := { facts with rootFacts, defaultChroot := beforeDigest.runchroot }
  let digestPolicy := (selectSources loadedSources beforeDigest
    { facts with fastGlob := beforeDigest.fastGlob }).map (·.entry)
  let beforeDigest ← privilegeDefaults digestPolicy beforeDigest facts
  let baselineFacts := lookupRoot.bind (rootFacts.lookup ·)
  let (pinned, capturedDigests) ← pinCommand
    (command.map (fun c => rootedPath expandedLookupRoot c.canonical))
    (baselineFacts.isNone && (!algos.isEmpty || beforeDigest.fdexec == "always")) algos
  let execFd := (pinned.map (·.1)).or (baselineFacts.bind (·.execFd))
  let digests := baselineFacts.map (·.digests) |>.getD capturedDigests
  let fileIds := match pinned, command with
    | some (_, s), some c => (c.path, s.dev, s.ino) :: facts.fileIds.filter (·.1 != c.path)
    | _, _ => baselineFacts.map (·.fileIds) |>.getD facts.fileIds
  let commandSetid ← commandSetid pinned (command.map (·.canonical))
  let facts := { facts with digests, fileIds }
  let settings ← defaults policy invoking host (some target) policyCommand facts opts.prompt.isSome true
  let locatedSudoers := selectSources loadedSources settings { facts with fastGlob := settings.fastGlob }
  let policy := locatedSudoers.map (·.entry)
  let policySettings := settings
  let settings ← privilegeDefaults policy settings { facts with fastGlob := settings.fastGlob }
  let policyTarget := target
  let (target, targetUnknownUid) ← if opts.user.isNone && opts.group.isNone &&
      settings.runasDefault != policySettings.runasDefault then
      targetUser settings.runasDefault invokingRealGid
    else pure (target, targetUnknownUid)
  let settings := { settings with noexecFile := some ((settings.noexecFile.or conf.noexec).getD "") }
  let sid ← Sys.getsid
  let ppid ← Sys.getppid
  let sidStart ← Sys.processStartTime sid
  let ppidStart ← Sys.processStartTime ppid
  if sidStart.isNone || ppidStart.isNone then
    throw (IO.userError "unable to determine timestamp process identity")
  let tsScope := Timestamp.scopeFor settings.timestampType ttyDevice
    sid (sidStart.getD 0) ppid (ppidStart.getD 0)
  let tsLockScope := Timestamp.scopeFor
    (if settings.timestampType == .ppid then .ppid else .tty) ttyDevice
    sid (sidStart.getD 0) ppid (ppidStart.getD 0)
  let (timestampOwnerUid, timestampOwnerGid) ← timestampOwnerIds settings.timestampowner
  let previousUser ← if uid == 0 then
      match userEnv.lookup "SUDO_USER" with
      | some name => do
        if name == "root" then pure none
        else try pure (some (← user name)) catch _ => pure none
      | none => pure none
    else pure none
  let validShells := (← Sys.validShells).toList
  let runasDefaultUser ← if settings.runaspw then
      if target.name == settings.runasDefault then pure (some target)
      else pure (some (← user settings.runasDefault))
    else pure none
  let ctx : Core.Context := {
    progname, opts, invoking, host, longHost, sudoers := policy, locatedSudoers, settings, target
    submitHost
    policySources := loadedSources
    commandSetid
    policySettings := some policySettings
    policyTarget := some policyTarget
    targetGroup, listUser, command, userEnv, cwd, userUmask := mask.toNat
    ttyName, toFacts := facts.toFacts, now := ← Sys.bootTimeNanos, tsScope, tsRecords := []
    tsSessionId := sid, tsLockScope, timestampOwnerUid, timestampOwnerGid
    wallTime, execFd, homes
    envFile := ← readEnvFile settings.envFile, restrictedEnvFile := ← readEnvFile settings.restrictedEnvFile
    selinuxEnabled := (← Sys.stat "/sys/fs/selinux/enforce").isSome
    root := ← user "root"
    listColumns := ← Sys.terminalColumns 1
    previousUser
    invokingRealGid := some invokingRealGid
    commandFoundInDot, validShells, targetUnknownUid, targetUnknownGid, runasDefaultUser
    mailerAvailable := ← match settings.mailerpath with | some p => executable p | none => pure false }
  let tsRecords ← if opts.resetTimestamp || settings.timestampTimeout == some 0 then pure [] else
      try Sys.readTimestamp (timestampConfig ctx) (timestampKey ctx)
      catch e => match e with
        | .interrupted _ _ _ => throw e
        | _ => pure []
  return { ctx with tsRecords }

private def jsonDetails (ctx : Core.Context) (accepted : Bool)
    (commandEnv : Option (List String) := none) : IO EventLog.Details := do
  let r := Core.request ctx
  let al := Policy.aliasesOf ctx.sudoers
  let candidates := ctx.locatedSudoers.flatMap fun l =>
    match l.entry with
    | .userSpec us => (Policy.usCandidates al al.fuel (Core.authorizationSettings ctx) r us).map ((l.file, us.source), ·)
    | _ => []
  let chosen := candidates.getLast?
  let allowed := chosen.filter (·.2.allow) |>.map (Policy.allowedOf (Core.authorizationSettings ctx) ·.2)
  let cwd := (ctx.opts.chdir.or (allowed.bind (·.cwd.join))).or ctx.settings.runcwd
    |>.filter (· != "*")
  let cwd := if commandEnv.isSome then ctx.cwd else
    (cwd.bind (Core.expandHome ctx)).getD (if ctx.opts.login then ctx.target.home else ctx.cwd)
  let command := match r.command with
    | .run p _ _ => p | .sudoedit _ => "sudoedit" | _ => Core.commandText ctx
  let argv := match r.command with
    | .run _ _ _ => ctx.command.map (fun c => c.argv0 :: c.args) |>.getD ctx.opts.command
    | .sudoedit fs => "sudoedit" :: fs | _ => []
  let runenv := if accepted then commandEnv.or (allowed.bind fun a =>
      (buildEnv (Core.environment ctx a)).toOption.map (fun env => env.map fun (k, v) => k ++ "=" ++ v))
    else none
  let (columns, lines) ← Sys.terminalSize
  return {
    submituser := (Core.displayUser ctx).name, command := some command,
    runuser := some ctx.target.name, rungroup := ctx.targetGroup.map (·.name),
    runchroot := ctx.opts.chroot.or ((allowed.bind (·.chroot)).or ctx.settings.runchroot),
    runcwd := some cwd, source := chosen.bind fun ((file, pos), _) =>
      pos.map fun (line, col) => s!"{file}:{line}:{col}",
    ttyname := ctx.ttyName, submithost := some (ctx.submitHost.getD ctx.longHost), submitcwd := some ctx.cwd,
    -- sudoers_to_eventlog records the passwd primary gid, even with explicit -g.
    rungid := some ctx.target.gid, runuid := some ctx.target.uid, columns, lines,
    runargv := some argv, runenv,
    submitenv := some (ctx.userEnv.map fun (k, v) => k ++ "=" ++ v) }

private def appendLogfile (ctx : Core.Context) (append : String → IO Unit) : IO Unit := do
  if let some path := ctx.settings.logfile then
    try append path catch e =>
      if ctx.settings.ignoreLogfileErrors then warn e.toString else throw e

private def logJson (ctx : Core.Context) (priority : String) (event : EventLog.Event) : IO Unit := do
  if priority != "none" then
    if let some facility := ctx.settings.syslog then
      Sys.syslogBytes facility priority (EventLog.formatJsonSyslog event).toUTF8 ctx.settings.syslogPid
  appendLogfile ctx fun path =>
    if ctx.settings.logFormat == "json_compact" then
      Sys.appendLog path (EventLog.formatJsonLine event)
    else Sys.appendJson path (EventLog.formatJsonMember event false)

private def localizedLog (ctx : Core.Context) (line : Core.LogLine) : IO Core.LogLine := do
  let some reason := line.reason | return line
  let translated ← I18n.translateLog ctx.settings.sudoersLocale reason
  if translated == reason then return line
  let initial := Core.logEscape (Core.displayUser ctx).name ++ " : "
  let separator := if line.raw then "" else " ; "
  let original := initial ++ Core.logEscape reason ++ separator
  let msg := if line.msg.startsWith original then
      initial ++ Core.logEscape translated ++ separator ++ (line.msg.drop original.length).toString
    else line.msg
  return { line with reason := some translated, msg }

/-- Preserve the event's policy phase: warnings before command lookup retain raw
argv, and warnings before rule selection do not acquire a later rule's source. -/
private def lineDetails (ctx : Core.Context) (line : Core.LogLine)
    (commandEnv : Option (List String)) (override : Option EventLog.Details) :
    IO EventLog.Details := do
  let details ← match override with
    | some details => pure details
    | none => jsonDetails ctx (line.event == .accept) commandEnv
  let details := if line.commandReady then details else
    let (path, args) := Core.unresolvedLogCommand ctx
    { details with command := some path, runargv := some (path :: args) }
  return { details with
    source := if line.lookupComplete then details.source else none
    runcwd := line.runcwd
    runchroot := line.runchroot }

private def logLine (ctx : Core.Context) (line : Core.LogLine)
    (iologPath : Option String := none) (remote : Bool := true)
    (commandEnv : Option (List String) := none)
    (detailsOverride : Option EventLog.Details := none) : IO (Option EventLog.Event) := do
  let ctx := if line.lookupComplete then ctx else
    { ctx with settings := Core.authorizationSettings ctx }
  let sendRemote := remote && !ctx.settings.logServers.isEmpty && line.reason.isSome
  let remoteUnknownTty := line.event == .alert && line.reason == some "no tty"
  let details ← if sendRemote || line.format != "sudo" then
      some <$> lineDetails ctx line commandEnv detailsOverride
    else pure none
  let line ← localizedLog ctx line
  if sendRemote then
    if let some reason := line.reason then
      if let some details := details then
        -- The log-server warning metadata uses "unknown"; local JSON omits a
        -- missing ttyname, as eventlog_store_json does.
        let details := if remoteUnknownTty then { details with ttyname := some "unknown" } else details
        Sys.LogSrv.event ctx.settings details reason (line.event == .alert)
  if line.format != "sudo" then
    let eventTime ← Sys.eventTime ctx.settings.logYear ctx.settings.sudoersLocale
    let event : EventLog.Event := {
      kind := line.event,
      uuid := ← Sys.eventUuid, reason := line.reason,
      serverTime := ← Sys.eventTime ctx.settings.logYear ctx.settings.sudoersLocale, eventTime := some eventTime,
      details, iologPath }
    logJson ctx line.priority event
    return some event
  let name := (ctx.previousUser.getD ctx.invoking).name
  let body := EventLog.messageBody name line.msg
  if line.priority != "none" then
    if let some facility := ctx.settings.syslog then
      for bytes in EventLog.splitSyslogBytes name body ctx.settings.syslogMaxlen do
        Sys.syslogBytes facility line.priority bytes ctx.settings.syslogPid
  appendLogfile ctx fun path => do
    Sys.appendLog path (EventLog.formatFile (← Sys.logTime ctx.settings.logYear ctx.settings.sudoersLocale)
      (ctx.submitHost.getD ctx.longHost) name body ctx.settings.logHost ctx.settings.loglinelen)
  return none

private def mail (ctx : Core.Context) (line : Core.LogLine) : IO Unit := do
  if !ctx.mailerAvailable then return
  let some path := ctx.settings.mailerpath | return
  let some recipient := ctx.settings.mailto | return
  let line ← localizedLog ctx line
  let name := (ctx.previousUser.getD ctx.invoking).name
  let sender := ctx.settings.mailfrom.getD name
  let subject := (ctx.settings.mailsub.replace "%h" ctx.longHost).replace "%u" name
  for field in [recipient, sender, subject] do
    if field.contains '\n' || field.contains '\r' then
      throw (IO.userError "invalid newline in mail header")
  let body := EventLog.messageBody name line.msg
  let text := s!"To: {recipient}\nFrom: {sender}\nAuto-Submitted: auto-generated\nSubject: {subject}\n\n" ++
    s!"{ctx.longHost} : {← Sys.logTime ctx.settings.logYear ctx.settings.sudoersLocale} : {name} : {body}\n\n"
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
  let security ← if ctx.settings.pwfeedback then pure "" else
    I18n.gettext "For security reasons, the password you type will not be visible.\n\n"
  return (← I18n.gettext ("\nWe trust you have received the usual lecture from the local System\n" ++
    "Administrator. It usually boils down to these three things:\n\n" ++
    "    #1) Respect the privacy of others.\n" ++
    "    #2) Think before you type.\n" ++
    "    #3) With great power comes great responsibility.\n\n")) ++
    security

private def audit (ctx : Core.Context) (success : Bool) : IO Unit := do
  if !success && !ctx.settings.logDenied then return
  if !(← Sys.auditCommand (Core.commandText ctx) (ctx.ttyName.getD "unknown") success) &&
      !ctx.settings.ignoreAuditErrors then
    throw (IO.userError "unable to send audit message")

private def authFailure (ctx : Core.Context) (decision : Core.Decision)
    (failure : EventLog.AuthFailure) : IO Unit := do
  audit ctx false
  let allowed := match Core.policyJudgement ctx with
    | .allow _ => true | .deny => false
  let listOrValidate := ctx.opts.mode == .list || ctx.opts.mode == .validate
  let line := Core.authFailureLog ctx failure.attempts (failure.attempts == 0)
  let logit := EventLog.logAuthFailure allowed ctx.settings.logDenied listOrValidate failure
  if logit || (ctx.settings.logfile.isSome && EventLog.fileAuthFailure listOrValidate failure) then
    let _ ← logLine ctx { line with priority := if logit then line.priority else "none" }
    pure ()
  if EventLog.mailAuthFailure allowed ctx.settings.mailBadpass ctx.settings.mailAlways
      (Core.denialMail ctx) listOrValidate failure then mail ctx line
  if failure.attempts == 0 then warn "a password is required"
  else if ctx.settings.authfailMessage.isSome then
    Sys.writeStderr ("sudo: " ++ Core.authFailureMessage ctx failure.attempts ++ "\n")
  else warn (Core.authFailureMessage ctx failure.attempts)
  if !allowed && !failure.error then
    audit ctx false
    if let some line := decision.log then
      let _ ← logLine ctx line
      pure ()
    if decision.mail then mail ctx (Core.logLine ctx (some (Core.denialReason ctx)))
    if ctx.settings.passwdTries == 0 then
      if let .fail text _ := decision.action then Sys.writeStderr (← I18n.translate text)

private def authenticate (ctx : Core.Context) (h : Sys.PamHandle) : IO (Option EventLog.AuthFailure) := do
  if ctx.opts.nonInteractive && !ctx.settings.noninteractiveAuth then
    return some { noInput := true, error := true }
  for attempt in List.range ctx.settings.passwdTries do
    let rc ← Sys.pamAuthenticate h
    if rc == 0 then return none
    if let some err ← Sys.pamLastConvError h then
      let signal ← Sys.pamInterrupted h
      if signal == 0 && err != "a password is required" then warn err
      return some {
        attempts := if ctx.opts.nonInteractive then 0 else attempt
        noInput := ctx.opts.nonInteractive, error := ctx.opts.nonInteractive, signal := signal.toNat }
    if ![6, 7, 9, 11].contains rc then
      let err := "PAM authentication error: " ++ (← Sys.pamStrerror h rc)
      warn err
      return some { error := true }
    if attempt + 1 < ctx.settings.passwdTries then
      let seed ← Sys.bootTimeNanos
      let message ← if ctx.settings.insults then
        I18n.gettext (Insults.select seed)
        else if ctx.settings.badpassMessageConfigured then pure ctx.settings.badpassMessage
        else I18n.gettext ctx.settings.badpassMessage
      Sys.writeStderr (message ++ "\n")
  return some { attempts := ctx.settings.passwdTries }

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

private def withPam (ctx : Core.Context) (service user prompt : String)
    (silent : Bool) (askpass : String) (body : Sys.PamHandle → IO α) : IO α := do
  let h ← Sys.pamStart service user {
    useStdin := ctx.opts.stdin, nonInteractive := ctx.opts.nonInteractive,
    visiblepw := ctx.settings.visiblepw, prompt, override := ctx.settings.passpromptOverride,
    pwfeedback := ctx.settings.pwfeedback, timeout := ctx.settings.passwdTimeout.getD 0 }
    (if ctx.settings.pamRuser then ctx.invoking.name else "") ctx.ttyName
  try
    Sys.pamConfigure h ctx.settings.pamSilent silent ctx.opts.bell askpass
      (if ctx.settings.pamRhost then ctx.longHost else "") ctx.invoking.name
    body h
  finally cleanup (Sys.pamEnd h 0)

private def environment (input : EnvInput) (h : Sys.PamHandle) (unknownTarget : Bool) : IO (Array String) := do
  let pamEnv ← if unknownTarget then pure [] else Sys.pamGetEnv h
  return envToArray (← IO.ofExcept (buildEnv { input with pamEnv }))

private def session (ctx : Core.Context) (h : Sys.PamHandle) (setcred openSession : Bool)
    (run : IO Sys.ExitStatus) : IO Sys.ExitStatus := do
  -- pam.c ends the transaction instead of starting a session for a synthetic uid.
  if ctx.targetUnknownUid then
    cleanup (Sys.pamEnd h 0)
    return ← run
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

private def logExit (ctx : Core.Context) (event : Option EventLog.Event)
    (started : Nat) (status : Sys.ExitStatus) : IO Unit := do
  if !ctx.settings.logExitStatus && ctx.settings.logServers.isEmpty then return
  let signal ← match status with
    | .signaled n => pure (some (← Sys.signalName n.toUInt32))
    | .exited _ => pure none
  let exitValue := match status with | .exited n => n | .signaled n => 128 + n
  cleanup (Sys.LogSrv.finish exitValue (signal.getD "") (← Sys.lastDumpedCore))
  if !ctx.settings.logExitStatus then return
  let some accepted := event | return
  let elapsed := (← Sys.bootTimeNanos) - started
  let time ← Sys.eventTime ctx.settings.logYear ctx.settings.sudoersLocale
  let event : EventLog.Event := {
    kind := .exit, uuid := accepted.uuid, serverTime := ← Sys.eventTime ctx.settings.logYear ctx.settings.sudoersLocale,
    eventTime := some time, iologPath := accepted.iologPath,
    runTime := some { seconds := elapsed / 1000000000, nanoseconds := elapsed % 1000000000 },
    signal, dumpedCore := ← Sys.lastDumpedCore,
    exitValue := match status with | .exited n => n | .signaled n => 128 + n }
  logJson ctx (ctx.settings.syslogGoodpri.getD "none") event

private def withInterceptedAuthentication (ctx : Core.Context)
    (authenticate : Core.Context → IO Bool) : IO Bool := do
  withCredentialCache ctx (fun records => do
    let refreshed := { ctx with tsRecords := records, now := ← Sys.bootTimeNanos }
    let accepted ← authenticate refreshed
    let record ← if accepted && (Core.decide refreshed).updateTimestamp then
        pure (some {
          scope := ctx.tsScope, authUid := (Core.authUser ctx).uid
          time := ← Sys.bootTimeNanos, disabled := false : Timestamp.Record })
      else pure none
    return (record, accepted)) warn

private def interceptedContext (original : Core.Context) (root : Option String) (enforce : Bool)
    (req : Sys.Intercept.Request) : IO Core.Context := do
  let path := absolute req.cwd req.command
  let policy := original.policySources.flatMap (fun (_, entries) => entries.map (·.entry))
  let rootCanon ← canonicalRoot root
  let some hostParent ← Sys.realpath (rootedPath root (Policy.dirOf path)) |
    throw (IO.userError "unable to resolve intercepted command directory")
  let parent := rootRelative rootCanon hostParent (Policy.dirOf path)
  let command : Core.ResolvedCmd := {
    path, canonical := parent ++ "/" ++ Policy.baseOf path,
    argv0 := path, args := req.argv.toList.drop 1 }
  let ctx : Core.Context := { original with
    sudoers := policy, command := some command, cwd := req.cwd,
    opts := { original.opts with
      mode := .run, command := path :: command.args,
      shell := false, login := false, resetTimestamp := false,
      chdir := none, envVars := [] },
    execFd := none, rootFacts := [], policyTarget := some original.target }
  if !enforce then return ctx
  let facts ← gatherFacts ctx.sudoers { Core.request ctx with now := ← Sys.unixTime }
    [] ctx.settings.sudoersLocale [] root
  let settings ← defaults ctx.sudoers ctx.invoking ctx.host (some ctx.target)
    (some facts.command) facts ctx.opts.prompt.isSome
  let plugin ← loadGroupPlugin settings.groupPlugin
  let facts ← try gatherPluginFacts ctx.sudoers facts plugin
    finally for handle in plugin do Sys.GroupPlugin.close handle
  let algos := ((ctx.sudoers.flatMap Sudoers.Parser.cmndAtoms).flatMap digestAlgos).eraseDups
  let digests ← commandDigests algos (rootedPath root command.canonical)
  -- The subcommand inherits the selected execution root. Refresh its command
  -- facts, rather than reusing the parent's inode/digests or authorizing a rule
  -- that would require switching to a different root mid-execution.
  let roots := original.rootFacts.filterMap fun (name, _) =>
    let expanded := (Sys.commandLookupRoot (some name)).bind
      (Core.expandHomePath ctx.target.home ctx.homes)
    if expanded == root then some name else none
  let refusal ← match root with
    | some root => rootEscape root command.path
    | none => pure none
  let rootFacts := roots.map fun name => (name, {
    command := facts.command, argv := req.argv.toList, found := true,
    canonPaths := facts.canonPaths, fileIds := facts.fileIds,
    globPaths := facts.globPaths, regexMatches := facts.regexMatches,
    digests, setid := req.setid, refusal : RootCommandFacts })
  let facts := { facts with digests, rootFacts }
  let settings ← defaults ctx.sudoers ctx.invoking ctx.host (some ctx.target)
    (some facts.command) facts ctx.opts.prompt.isSome
  let locatedSudoers :=
    selectSources original.policySources settings { facts with fastGlob := settings.fastGlob }
  let policy := locatedSudoers.map (·.entry)
  let effective ← privilegeDefaults policy settings facts
  let (timestampOwnerUid, timestampOwnerGid) ←
    if !effective.interceptAuthenticate || effective.timestampowner == original.settings.timestampowner then
      pure (original.timestampOwnerUid, original.timestampOwnerGid)
    else timestampOwnerIds effective.timestampowner
  let runasDefaultUser ←
    if effective.interceptAuthenticate && effective.runaspw &&
        (effective.runasDefault != original.settings.runasDefault || original.runasDefaultUser.isNone) then
      if ctx.target.name == effective.runasDefault then pure (some ctx.target)
      else pure (some (← user effective.runasDefault))
    else pure original.runasDefaultUser
  return { ctx with
    sudoers := policy, locatedSudoers, settings := effective, policySettings := some settings,
    timestampOwnerUid, timestampOwnerGid, runasDefaultUser,
    toFacts := facts.toFacts, wallTime := facts.now }

private def interceptedAuthorize (ctx : Core.Context) (enforce plugins : Bool)
    (req : Sys.Intercept.Request) : IO Bool := do
  let decision := Intercept.decide ctx enforce req.setid
  let logCtx := { ctx with settings := { ctx.settings with runcwd := none } }
  let commandEnv := some (Intercept.environment req.env).toList
  if !decision.allowed then
    audit ctx false
    let details ← jsonDetails ctx false commandEnv
    if plugins && enforce then
      Sys.Plugins.reject "command rejected by policy" false (Sys.Plugins.rejectionInfo ctx details.source)
    Sys.LogSrv.subcommand details decision.reason
    if ctx.settings.logDenied then
      let _ ← logLine logCtx (Core.logLine logCtx decision.reason)
        (remote := false) (commandEnv := commandEnv)
      pure ()
    if req.setid && !ctx.settings.interceptAllowSetid then
      warn "setid commands are not permitted in intercept mode"
    else if let .fail text _ := Core.deniedAction ctx then
      Sys.writeStderr (← I18n.translate text)
    return false
  if let .required authUser := decision.auth then
    let prompt := expandPrompt ctx.settings.passprompt ctx.invoking.name
      ctx.target.name ctx.longHost authUser.name
    let authenticated ← withPam ctx ctx.settings.pamService authUser.name prompt true "" fun h => do
      if let some failure ← authenticate ctx h then
        authFailure ctx (Core.policyDecision ctx (Core.policyJudgement ctx)) failure
        pure false
      else
        account ctx h
        pure true
    if !authenticated then
      if plugins then Sys.Plugins.reject "authentication failure" true #[]
      return false
  if plugins then
    let mut info := #[]
    if enforce then
      let .allow allowed := Core.policyJudgement ctx | return false
      let some command := ctx.command | return false
      let plan := Core.execPlan ctx allowed command
      info := Sys.Plugins.commandInfo ctx plan (← jsonDetails ctx true commandEnv).source
      info := info.filter fun entry => !entry.startsWith "command=" && !entry.startsWith "runcwd="
    info := info ++ #["command=" ++ req.command, "runcwd=" ++ req.cwd]
    if !(← Sys.Plugins.checkSubcommand info req.argv req.env enforce) then
      return false
  audit ctx true
  Sys.LogSrv.subcommand (← jsonDetails ctx true commandEnv) none
  if ctx.settings.logAllowed then
    let _ ← logLine logCtx (Core.logLine logCtx none)
      (remote := false) (commandEnv := commandEnv)
    pure ()
  return true

private def interceptedCheck (original : Core.Context) (root : Option String) (enforce plugins : Bool)
    (req : Sys.Intercept.Request) : IO Bool := do
  try
    let ctx ← interceptedContext original root enforce req
    if enforce && ctx.settings.interceptAuthenticate then
      withInterceptedAuthentication ctx (fun fresh => interceptedAuthorize fresh enforce plugins req)
    else interceptedAuthorize ctx enforce plugins req
  catch e =>
    warn e.toString
    return false

private def executeAction (ctx : Core.Context) (decision : Core.Decision)
    (h : Option Sys.PamHandle) (plugins : Bool) : IO Sys.ExitStatus := do
  let editor ← match decision.action with
    | .edit plan => Sudoedit.select ctx.progname plan
    | _ => pure none
  if let .edit _ := decision.action then
    if editor.isNone then
      if plugins then Sys.Plugins.reject "policy plugin error" true #[]
      return .exited 1
  let editorLine := match decision.action, editor with
    | .edit plan, some editor =>
      if decision.log.isNone && !decision.mail then none else
        let allowed := match Core.policyJudgement ctx with
          | .allow allowed => some allowed | .deny => none
        some (Core.logLine ctx none allowed
          (some (editor.path, editor.words.drop 1 ++ ["--"] ++ plan.policyFiles)))
    | _, _ => none
  let executes := match decision.action with | .exec _ | .edit _ => true | _ => false
  let editorDetails ← if !ctx.settings.logServers.isEmpty || ctx.settings.logFormat != "sudo" then
      match decision.action, editor with
      | .edit plan, some editor => do
        let details ← jsonDetails ctx true
        pure (some { details with
          command := some editor.path
          runargv := some (editor.words ++ ["--"] ++ plan.policyFiles) })
      | _, _ => pure none
    else pure none
  let started ← if ctx.settings.logExitStatus then Sys.bootTimeNanos else pure 0
  if !ctx.settings.logServers.isEmpty then
    match decision.action with
    | .exec plan =>
      let details ← jsonDetails ctx true
      let details := if plan.iolog.isSome then { details with runcwd := plan.cwd } else details
      Sys.LogSrv.accept ctx.settings details plan.iolog
    | .edit plan =>
      let some details := editorDetails | throw (IO.userError "missing editor event metadata")
      Sys.LogSrv.accept ctx.settings details plan.iolog
    | _ => pure ()
  let openIolog : IO (Option String) := do
    if !ctx.settings.logServers.isEmpty then return none
    let info ← match decision.action with
      | .exec plan => pure (plan.iolog.map (·, plan.gid, plan.path, plan.argv))
      | .edit plan => do
        let some iolog := plan.iolog | pure none
        let some editor := editor | throw (IO.userError "missing selected editor")
        pure (some (iolog, plan.fileGid, editor.path, editor.words ++ ["--"] ++ plan.policyFiles))
      | _ => pure none
    let some (iolog, gid, command, argv) := info | return none
    let group := (ctx.invoking.groups.find? (·.2 == ctx.invoking.gid)).map (·.1) |>.getD ""
    let runasGroup := (← Sys.getgrgid gid).map (·.name) |>.getD ("#" ++ toString gid)
    Sys.IoLog.open iolog {
      user := ctx.invoking.name, group, runasUser := ctx.target.name, runasGroup
      hostname := ctx.longHost, command, cwd := ctx.cwd
      tty := ctx.ttyName.getD "unknown", argv := argv.toArray } ctx.settings.sudoersLocale
  let iologPath ← openIolog
  if plugins then
    let source := (← jsonDetails ctx true).source
    let approved ← match decision.action with
      | .exec plan =>
        Sys.Plugins.check (Sys.Plugins.commandInfo ctx plan source iologPath)
          plan.argv.toArray (envToArray (← IO.ofExcept (buildEnv plan.envInput)))
      | .edit plan => do
        let some editor := editor | throw (IO.userError "missing selected editor")
        Sys.Plugins.check (Sys.Plugins.editCommandInfo ctx plan editor.path source iologPath)
          (editor.words ++ ["--"] ++ plan.policyFiles).toArray
          (envToArray ctx.userEnv)
      | .fail _ _ => do
        Sys.Plugins.reject "command rejected by policy" false (Sys.Plugins.rejectionInfo ctx source)
        pure true
      | .print _ code =>
        if code == 0 then
          Sys.Plugins.accept #["command=list"] ctx.opts.command.toArray (envToArray ctx.userEnv)
        else do
          Sys.Plugins.reject "command rejected by policy" false #["command=list"]
          pure true
      | .validate =>
        Sys.Plugins.accept #["command=validate"] #[] (envToArray ctx.userEnv)
      | _ => pure true
    if executes then
      if !Sys.Plugins.approvalPermits decision approved then return .exited 1
    else if !approved then return .exited 1
  if let some (.reject _) := decision.audit then audit ctx false
  let event ← match decision.log with
    | some line => logLine ctx (editorLine.getD line) iologPath (detailsOverride := editorDetails)
    | none => do
      if !executes || ctx.settings.logFormat == "sudo" || !ctx.settings.logExitStatus then pure none
      else pure (some {
        kind := .accept, uuid := ← Sys.eventUuid,
        serverTime := ← Sys.eventTime ctx.settings.logYear ctx.settings.sudoersLocale, iologPath : EventLog.Event })
  if decision.mail then mail ctx ((editorLine.or decision.log).getD (Core.logLine ctx none))
  if let some path := decision.adminFlag then
    cleanup (Sys.createAdminFlag path ctx.invoking.uid ctx.invoking.gid (ctx.invoking.groups.map (·.2)))
  match decision.action with
  | .exec plan =>
    let some h := h | throw (IO.userError "missing PAM transaction")
    let status ← session ctx h plan.pamSetcred plan.pamSession do
      if let some .accept := decision.audit then audit ctx true
      let env ← environment plan.envInput h ctx.targetUnknownUid
      let run := Sys.runCommand {
        plan.toRunPlan.toSpec plan.path plan.argv.toArray env plan.uid plan.gid plan.groups with
        background := plan.background, execFd := plan.execFd, staySetuid := plan.staySetuid }
      if plan.intercept || plan.logSubcmds then
        if plan.intercept then
          let path := plan.execFd.map (fun fd => s!"/proc/self/fd/{fd}") |>.getD
            (plan.chroot.getD "" ++ plan.path)
          let some st ← Sys.stat path | throw (IO.userError "unable to stat intercepted command")
          if !(Intercept.decide ctx true (st.mode &&& 0o6000 != 0)).allowed then
            throw (IO.userError "setid commands are not permitted in intercept mode")
        Sys.Intercept.withMonitor (ctx.settings.interceptType == "trace")
          (plan.intercept && ctx.settings.interceptVerify) (!plan.intercept)
          (interceptedCheck ctx plan.chroot plan.intercept plugins) run
      else run
    logExit ctx event started status
    return status
  | .edit plan =>
    let some h := h | throw (IO.userError "missing PAM transaction")
    let some editor := editor | throw (IO.userError "missing selected editor")
    if let some .accept := decision.audit then audit ctx true
    -- sudo_edit permanently becomes root before preparing files and opening
    -- the PAM session; the editor child still drops to plan.editUid.
    try Sys.setUid 0 catch e =>
      throw (IO.userError ("unable to change uid to root (0): " ++ e.toString))
    let status ← session ctx h plan.pamSetcred plan.pamSession do
      Sudoedit.run ctx.progname plan editor (← environment plan.envInput h ctx.targetUnknownUid)
    logExit ctx event started status
    return status
  | .print text code =>
    (← IO.getStdout).putStr (← I18n.translate text)
    return .exited code.toNat
  | .fail text code =>
    Sys.writeStderr (← I18n.translate text)
    return .exited code.toNat
  | .validate => return .exited 0
  | .resetTimestamp =>
    -- Removal uses ts_init_key directly, unlike authentication's nonglobal
    -- key: Linux kernel-mode `-k` selects a ppid record, not its tty ticket.
    let scope ← if ctx.settings.timestampType == .kernel then do
        let ppid ← Sys.getppid
        let some start ← Sys.processStartTime ppid |
          throw (IO.userError "unable to determine timestamp process identity")
        pure (Timestamp.Scope.ppid ppid start)
      else pure ctx.tsScope
    Sys.invalidateTimestamp (timestampConfig ctx) scope
    return .exited 0
  | .removeTimestamp =>
    Sys.removeTimestampFile (timestampConfig ctx)
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
        (Core.policyJudgement ctx))
  if !needsSession && !needsAuth && !decision.updateTimestamp then
    return ← executeAction ctx decision none (!conf.plugins.isEmpty)
  let askpass := ((ctx.userEnv.lookup "SUDO_ASKPASS").filter (!·.isEmpty)).or conf.askpass
  let useAskpass := ctx.opts.askpass || (!ctx.opts.stdin && ctx.ttyName.isNone &&
    !ctx.settings.visiblepw && (ctx.userEnv.lookup "DISPLAY").isSome && askpass.isSome)
  if useAskpass && askpass.isNone then
    throw (IO.userError "no askpass program specified, try setting SUDO_ASKPASS")
  let service := if useAskpass && ctx.settings.pamAskpassService.isSome then
      ctx.settings.pamAskpassService.getD ctx.settings.pamService
    else if ctx.opts.login then ctx.settings.pamLoginService else ctx.settings.pamService
  let promptFormat ← match ctx.opts.prompt.or (ctx.userEnv.lookup "SUDO_PROMPT") with
    | some configured => pure configured
    | none => if ctx.settings.passpromptConfigured then pure ctx.settings.passprompt else I18n.gettext ctx.settings.passprompt
  let prompt := expandPrompt promptFormat ctx.invoking.name ctx.target.name ctx.longHost authUser.name
  withPam ctx service authUser.name prompt (!(ctx.opts.shell || ctx.opts.login))
      (if useAskpass then askpass.getD "" else "") fun h => do
    Sys.pamLecture h (← lecture ctx)
    let authorized : IO (Bool × Nat) := do
      if !needsAuth && !decision.updateTimestamp then
        if needsSession then
          try account ctx h catch e =>
            warn e.toString
            authFailure ctx decision { error := true }
            return (false, 0)
        return (true, 0)
      withCredentialCache ctx (fun records => do
        let cached := !ctx.opts.resetTimestamp && Timestamp.lookup (← Sys.bootTimeNanos)
          ctx.settings.timestampTimeout ctx.tsScope authUser.uid records
        let failure ← if !needsAuth || cached then pure none else authenticate ctx h
        if let some failure := failure then
          authFailure ctx decision failure
          return (none, (false, failure.signal))
        if ← Sys.pamLectured h then
          cleanup do
            let _ ← Sys.stateMarker ctx.settings.lectureStatusDir ctx.invoking.uid true
            pure ()
        -- Approval precedes timestamp renewal in validate/list modes too.
        try account ctx h catch e =>
          warn e.toString
          authFailure ctx decision { error := true }
          return (none, (false, 0))
        let out ← if decision.updateTimestamp then do
            pure (some {
              scope := ctx.tsScope, authUid := authUser.uid
              time := ← Sys.bootTimeNanos, disabled := false : Timestamp.Record })
          else pure none
        return (out, (true, 0))) warn
    let (approved, signal) ← authorized
    if !approved then
      if !conf.plugins.isEmpty then
        Sys.Plugins.reject "authentication failure" true #[]
      return if signal == 0 then .exited 1 else .signaled signal
    executeAction ctx decision (some h) (!conf.plugins.isEmpty)

private def configuration : IO SudoConf.Config := do
  let path := "/etc/sudo.conf"
  if (← Sys.stat path).isNone then return {}
  let opened ← try pure (some (← Sys.openReadOnly path)) catch e =>
    warn e.toString
    pure none
  let some (fd, st) := opened | return {}
  try
    if let some problem := SudoConf.fileProblem st.uid st.mode then
      warn (path ++ " " ++ problem)
      return ← IO.ofExcept (SudoConf.parseFile st.uid st.mode "")
    -- Read the object whose fstat was approved, never reopen the pathname.
    let (_, text) ← Sys.readFileFollow s!"/proc/self/fd/{fd}"
    IO.ofExcept (SudoConf.parseFile st.uid st.mode text)
  finally
    Sys.closeDescriptor fd.toUInt32

/-- `/proc/self/cmdline` preserves argv[0] (unlike the executable's realpath) and
lets us reject invalid UTF-8 before decoded Lean arguments reach policy. -/
def run (args : List String) : IO UInt32 := do
  let mut diagnosticProgname := "sudo"
  try
    Sys.initializeProcess false
    I18n.initializeLocale
    let conf ← configuration
    let pluginUserInfo ← if conf.plugins.isEmpty then pure #[]
      else Sys.Plugins.userInfo conf.groupSource conf.maxGroups.toUInt32
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
    let argv0 := (String.fromUTF8? first).getD "sudo"
    let progname := Cli.programName argv0
    diagnosticProgname := progname
    let parsed := Cli.parseArgs argv0 args (← Sys.environ)
    for warning in parsed.warnings do
      Sys.writeStderr (← I18n.translate (Cli.formatError argv0 { message := warning }) false)
    let opts ← match parsed.result with
      | .ok opts => pure opts
      | .error err =>
        Sys.writeStderr (← I18n.translate (Cli.formatError argv0 err) false)
        return 1
    if opts.mode == .help then
      (← IO.getStdout).putStr (Cli.helpFor progname (← I18n.catalogs).sudo)
      return 0
    let versionHeader ← if opts.mode == .version then do
        let configure ← if (← Sys.getuid) == 0 then do
            pure ("Configure options: " ++ Cli.configureOptions (← Sys.architecture) ++ "\n")
          else pure ""
        let header := "Sudo version 1.9.17p2\n" ++ configure
        (← IO.getStdout).putStr header
        (← IO.getStdout).flush
        pure header
      else pure ""
    if !conf.plugins.isEmpty then
      Sys.Plugins.load conf
      let submitEnv ← Sys.environ
      let interfaces ← if conf.probeInterfaces then
          pure ((← Sys.interfaceAddresses).toList.map (fun (a, m) => a ++ "/" ++ m))
        else pure []
      Sys.Plugins.configureConversation opts.stdin opts.nonInteractive opts.bell
        (if opts.askpass then ((submitEnv.lookup "SUDO_ASKPASS").or conf.askpass).getD "" else "")
      Sys.Plugins.openAudit (Sys.Plugins.settings progname opts conf interfaces)
        pluginUserInfo (argv0 :: args).toArray (envToArray submitEnv)
        (args.length + 1 - opts.command.length).toUInt32
    if opts.mode == .version then
      if let some message := Cli.timeoutError opts then
        -- The front-end version was printed before loading plugins.
        warn message
        throw (IO.userError "error initializing audit plugin sudoers_audit")
      let text ← if (← Sys.getuid) == 0 then do
          let ctx ← context progname opts conf
          let interfaces := (← Sys.interfaceAddresses).toList.map (fun (a, m) => a ++ "/" ++ m)
          pure (Cli.versionFor true ctx.settings interfaces (← Sys.architecture))
        else pure Cli.versionText
      let text := (text.drop versionHeader.length).toString
      let text := if conf.plugins.isEmpty then text else
        (text.replace "Sudoers I/O plugin version 1.9.17p2\n" "").replace
          "Sudoers audit plugin version 1.9.17p2\n" ""
      (← IO.getStdout).putStr (← I18n.translate text)
      if !conf.plugins.isEmpty then
        (← IO.getStdout).flush
        let builtin := fun name => (conf.plugins.find? fun p =>
          p.symbol == name && Sys.Plugins.isBuiltin conf p).map (·.line.toUInt32)
        let ioLine := (builtin "sudoers_io").getD
          (if (builtin "sudoers_policy").isSome || (← Sys.Plugins.hasIo) then 0 else 0xffffffff)
        Sys.Plugins.showVersion ((← Sys.getuid) == 0) ioLine
          ((builtin "sudoers_audit").getD 0xffffffff)
        Sys.Plugins.close 0 0
      return 0
    if !valid || args.any (fun a => a.contains '\ufffd') then
      warn "non-UTF-8 command-line arguments are not supported"
      if !conf.plugins.isEmpty then Sys.Plugins.close 3 1
      return 1
    let opts ← if opts.mode == .run && !opts.shell && !opts.login &&
        (opts.command.head?.map Policy.baseOf) == some "sudoedit" then do
        warn "sudoedit doesn't need to be run via sudo"
        pure { opts with mode := .edit, command := opts.command.drop 1 }
      else pure opts
    let ctx ← context progname opts conf
    let status ← try
      let status ← execute ctx (Core.decide ctx) conf
      if !conf.plugins.isEmpty then Sys.Plugins.close 0 0
      pure status
      finally
        cleanup Sys.LogSrv.close
        for fd in (ctx.execFd.toList ++ ctx.rootFacts.filterMap (·.2.execFd)).eraseDups do
          cleanup (Sys.closeDescriptor fd.toUInt32)
    Sys.exitWith status
  catch e =>
    if e.toString == "plugin requested usage" then
      cleanup (Sys.Plugins.close 0 0)
      Sys.writeStderr (Cli.usageFor diagnosticProgname)
    else
      cleanup (Sys.Plugins.close 3 1)
      warn e.toString
    return 1

end LeanSudo.Shell
