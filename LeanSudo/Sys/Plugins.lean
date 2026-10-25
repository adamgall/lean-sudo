import LeanSudo.Core
import LeanSudo.SudoConf

namespace LeanSudo.Sys.Plugins

@[extern "lean_sudo_plugins_load"]
private opaque loadRaw (symbol path : @& String) (line : UInt32)
    (options : @& Array String) : IO Unit

@[extern "lean_sudo_plugins_user_info"]
opaque userInfo (groupSource : @& String) (maxGroups : UInt32) : IO (Array String)

@[extern "lean_sudo_plugins_conversation"]
opaque configureConversation (useStdin nonInteractive bell : Bool) (askpass : @& String) : IO Unit

@[extern "lean_sudo_plugins_open"]
opaque openAudit (settings userInfo submitArgv submitEnv : @& Array String)
    (optind : UInt32) : IO Unit

@[extern "lean_sudo_plugins_check"]
opaque check (commandInfo argv env : @& Array String) : IO Bool

@[extern "lean_sudo_plugins_check_subcommand"]
opaque checkSubcommand (commandInfo argv env : @& Array String) (enforce : Bool) : IO Bool

@[extern "lean_sudo_plugins_accept"]
opaque accept (commandInfo argv env : @& Array String) : IO Bool

@[extern "lean_sudo_plugins_reject"]
opaque reject (message : @& String) (isError : Bool) (commandInfo : @& Array String) : IO Unit

@[extern "lean_sudo_plugins_version"]
opaque showVersion (verbose : Bool) (builtinIoLine builtinAuditLine : UInt32) : IO Unit

@[extern "lean_sudo_plugins_close"]
opaque close (statusType status : UInt32) : IO Unit

@[extern "lean_sudo_plugins_has_io"]
opaque hasIo : IO Bool

def qualifiedPath (conf : SudoConf.Config) (plugin : SudoConf.Plugin) : String :=
  if plugin.path.startsWith "/" then plugin.path else conf.pluginDir ++ plugin.path

def isBuiltin (conf : SudoConf.Config) (plugin : SudoConf.Plugin) : Bool :=
  let path := qualifiedPath conf plugin
  path.startsWith "/" && SudoConf.supportedPlugin plugin.symbol path plugin.options

def load (conf : SudoConf.Config) : IO Unit := do
  for plugin in conf.plugins do
    if isBuiltin conf plugin then continue
    let path := qualifiedPath conf plugin
    if !plugin.path.startsWith "/" && conf.pluginDir.isEmpty then
      throw (IO.userError s!"error in /etc/sudo.conf, line {plugin.line} while loading plugin \"{plugin.symbol}\"\nsudo: {plugin.path}: No such file or directory\nsudo: fatal error, unable to load plugins")
    loadRaw plugin.symbol path plugin.line.toUInt32 plugin.options.toArray

private def opt (name : String) (value : Option String) : List String :=
  value.toList.map (name ++ "=" ++ ·)

private def flag (name : String) (value : Bool) : List String :=
  if value then [name ++ "=true"] else []

def settings (progname : String) (o : Cli.Options) (conf : SudoConf.Config)
    (interfaces : List String) : Array String :=
  (flag "preserve_environment" (o.preserveEnv == .all) ++ opt "runas_group" o.group ++
    flag "set_home" o.setHome ++ flag "run_shell" (o.shell && !o.impliedShell) ++
    flag "login_shell" o.login ++ flag "ignore_ticket" (o.resetTimestamp || o.mode == .removeTimestamp) ++
    (if o.resetTimestamp || o.mode == .removeTimestamp then []
      else ["update_ticket=" ++ toString (!o.noUpdate)]) ++
    opt "prompt" o.prompt ++ opt "selinux_role" o.role ++ opt "selinux_type" o.type ++
    opt "runas_user" o.user ++ ["progname=" ++ progname] ++ flag "implied_shell" o.impliedShell ++
    flag "preserve_groups" o.preserveGroups ++ flag "noninteractive" o.nonInteractive ++
    flag "sudoedit" (o.mode == .edit) ++ opt "closefrom" (o.closeFrom.map toString) ++
    (if interfaces.isEmpty then [] else ["network_addrs=" ++ String.intercalate " " interfaces]) ++
    (if conf.maxGroups == 65536 then [] else [s!"max_groups={conf.maxGroups}"]) ++
    (if conf.pluginDir.isEmpty then [] else ["plugin_dir=" ++ conf.pluginDir]) ++
    opt "remote_host" o.host ++ opt "timeout" o.timeoutText ++ opt "cmnd_chroot" o.chroot ++
    opt "cmnd_cwd" o.chdir ++ flag "askpass" o.askpass).toArray

def executable (decision : Core.Decision) : Bool :=
  match decision.action with | .exec _ | .edit _ => true | _ => false

def approvalPermits (decision : Core.Decision) (approved : Bool) : Bool :=
  executable decision && approved

theorem approval_only_restricts (decision : Core.Decision) (approved : Bool)
    (h : approvalPermits decision approved = true) : executable decision = true := by
  cases he : executable decision <;> simp_all [approvalPermits]

theorem denied_never_approved (decision : Core.Decision) (approved : Bool)
    (h : executable decision = false) : approvalPermits decision approved = false := by
  simp [approvalPermits, h]

private def octal (n : Nat) : String :=
  "0" ++ ((Nat.repr (n / 64 % 8) ++ Nat.repr (n / 8 % 8) ++
    Nat.repr (n % 8)).dropWhile (· == '0')).toString

private def listValue (values : List String) : String :=
  String.intercalate "," (values.map fun value =>
    value.replace "\\" "\\\\" |>.replace "," "\\,")

private def ioInfo (p : Option IoLog.Plan) (path : Option String) : List String :=
  match p with
  | none => []
  | some p => opt "iolog_path" path ++ flag "iolog_stdin" p.stdin ++
    flag "iolog_stdout" p.stdout ++ flag "iolog_stderr" p.stderr ++
    flag "iolog_ttyin" p.ttyin ++ flag "iolog_ttyout" p.ttyout ++
    flag "iolog_compress" p.compress ++ flag "iolog_flush" p.flush ++
    ["log_passwords=" ++ toString p.logPasswords] ++
    (if p.passpromptRegex.isEmpty then [] else
      ["passprompt_regex=" ++ listValue p.passpromptRegex.toList])

def commandInfo (ctx : Core.Context) (p : Core.ExecPlan)
    (source iologPath : Option String := none) : Array String := Id.run do
  let s := ctx.settings
  let preserve := s.preserveGroups || ctx.opts.preserveGroups
  return (["command=" ++ (ctx.command.map Core.ResolvedCmd.path).getD p.path] ++ flag "log_subcmds" p.logSubcmds ++
    ioInfo p.iolog iologPath ++ (if p.iolog.isSome then ["maxseq=" ++ s.maxseq] else []) ++
    opt "cwd" p.cwd ++ flag "cwd_optional" p.cwdOptional ++
    ["runas_user=" ++ ctx.target.name] ++ opt "runas_group" (ctx.targetGroup.map GroupInfo.name) ++
    (if p.staySetuid then
      [s!"runas_uid={ctx.invoking.uid}", s!"runas_gid={ctx.invokingRealGid.getD ctx.invoking.gid}",
       s!"runas_euid={p.uid}", s!"runas_egid={p.gid}"]
     else [s!"runas_uid={p.uid}", s!"runas_gid={p.gid}"]) ++
    (if preserve then ["preserve_groups=true"] else
      ["runas_groups=" ++ String.intercalate "," ((p.gid :: p.groups.filter (· != p.gid)).map toString)]) ++
    [s!"closefrom={p.closeFrom}"] ++ flag "ignore_iolog_errors" s.ignoreIologErrors ++
    flag "intercept" p.intercept ++ flag "use_ptrace" (s.interceptType == "trace") ++
    flag "intercept_verify" s.interceptVerify ++ flag "noexec" p.noexecFile.isSome ++
    flag "exec_background" p.execBackground ++ flag "set_utmp" s.setUtmp ++
    flag "use_pty" p.usePty ++ (if s.utmpRunas then ["utmp_user=" ++ ctx.target.name] else []) ++
    (if s.iologMode == 0o600 then [] else ["iolog_mode=" ++ octal s.iologMode]) ++
    opt "iolog_user" s.iologUser ++ opt "iolog_group" s.iologGroup ++
    (if s.logServers.isEmpty then [] else
      ["log_servers=" ++ listValue s.logServers, s!"log_server_timeout={s.logServerTimeout}"]) ++
    ["log_server_keepalive=" ++ toString s.logServerKeepalive,
     "log_server_verify=" ++ toString s.logServerVerify] ++
    opt "log_server_cabundle" s.logServerCabundle ++ opt "log_server_peer_cert" s.logServerPeerCert ++
    opt "log_server_peer_key" s.logServerPeerKey ++
    (if p.timeout == 0 then [] else [s!"timeout={p.timeout}"]) ++ opt "chroot" p.chroot ++
    (if s.umask == 0o777 then [] else ["umask=" ++ octal p.umask]) ++
    flag "umask_override" s.umaskOverride ++ opt "execfd" (p.execFd.map toString) ++
    p.rlimits.map (fun (k, v) => k ++ "=" ++ v) ++ opt "source" source ++
    opt "apparmor_profile" p.apparmorProfile).toArray

def editCommandInfo (ctx : Core.Context) (p : Core.EditPlan) (editor : String)
    (source iologPath : Option String := none) : Array String :=
  commandInfo ctx {
    path := editor, argv := [], envInput := p.envInput, uid := p.fileUid, gid := p.fileGid
    groups := p.fileGroups, cwd := p.cwd, umask := p.umask, usePty := p.usePty
    background := false, closeFrom := p.closeFrom, pamService := p.pamService
    pamSession := p.pamSession, pamSetcred := p.pamSetcred, cwdOptional := p.cwdOptional
    timeout := p.timeout, noexecFile := p.noexecFile, apparmorProfile := p.apparmorProfile
    rlimits := p.rlimits, utmpUser := p.utmpUser, iolog := p.iolog
    execBackground := p.execBackground, chroot := p.chroot } source iologPath ++
  #["sudoedit=true", s!"sudoedit_nfiles={p.policyFiles.length}"] ++
  (if p.checkdir then #[] else #["sudoedit_checkdir=false"]) ++
  (if p.follow then #["sudoedit_follow=true"] else #[])

def rejectionInfo (ctx : Core.Context) (source : Option String := none) : Array String :=
  if ctx.opts.mode == .list then #["command=list"]
  else if ctx.opts.mode == .validate then #["command=validate"]
  else Id.run do
    let s := ctx.settings
    let gid := Core.commandGid ctx
    let groups := Core.targetGroups ctx
    let cwd := (s.runcwd.filter (· != "*")).bind (Core.expandHome ctx)
    let cwd := cwd.or (if ctx.opts.login then some ctx.target.home else none)
    let iolog := IoLog.plan s {}
    return (["command=" ++ (ctx.command.map Core.ResolvedCmd.path).getD (ctx.opts.command.headD "sudoedit")] ++
      flag "log_subcmds" s.logSubcmds ++ ioInfo iolog none ++
      (if iolog.isSome then ["maxseq=" ++ s.maxseq] else []) ++
      flag "sudoedit" (ctx.opts.mode == Cli.Mode.edit) ++ opt "cwd" cwd ++
      flag "cwd_optional" (ctx.opts.login && s.runcwd.isNone) ++
      ["runas_user=" ++ ctx.target.name] ++ opt "runas_group" (ctx.targetGroup.map GroupInfo.name) ++
      (if s.staySetuid then
        [s!"runas_uid={ctx.invoking.uid}", s!"runas_gid={ctx.invokingRealGid.getD ctx.invoking.gid}",
         s!"runas_euid={ctx.target.uid}", s!"runas_egid={gid}"]
       else [s!"runas_uid={ctx.target.uid}", s!"runas_gid={gid}"]) ++
      (if s.preserveGroups || ctx.opts.preserveGroups then ["preserve_groups=true"] else
        ["runas_groups=" ++ String.intercalate "," ((gid :: groups.filter (· != gid)).map toString)]) ++
      [s!"closefrom={ctx.opts.closeFrom.getD s.closefrom.toNat}"] ++
      flag "ignore_iolog_errors" s.ignoreIologErrors ++ flag "intercept" s.intercept ++
      flag "use_ptrace" (s.interceptType == "trace") ++ flag "intercept_verify" s.interceptVerify ++
      flag "noexec" s.noexec ++ flag "exec_background" s.execBackground ++
      flag "set_utmp" s.setUtmp ++ flag "use_pty" s.usePty ++
      (if s.utmpRunas then ["utmp_user=" ++ ctx.target.name] else []) ++
      (if s.iologMode == 0o600 then [] else ["iolog_mode=" ++ octal s.iologMode]) ++
      opt "iolog_user" s.iologUser ++ opt "iolog_group" s.iologGroup ++
      (if s.logServers.isEmpty then [] else
        ["log_servers=" ++ listValue s.logServers, s!"log_server_timeout={s.logServerTimeout}"]) ++
      ["log_server_keepalive=" ++ toString s.logServerKeepalive,
       "log_server_verify=" ++ toString s.logServerVerify] ++
      opt "log_server_cabundle" s.logServerCabundle ++ opt "log_server_peer_cert" s.logServerPeerCert ++
      opt "log_server_peer_key" s.logServerPeerKey ++
      (if s.commandTimeout == 0 then [] else [s!"timeout={s.commandTimeout}"]) ++
      opt "chroot" (s.runchroot.filter (· != "*")) ++ flag "umask_override" s.umaskOverride ++
      s.resourceLimits.map (fun (k, v) => k ++ "=" ++ v) ++ opt "source" source ++
      opt "apparmor_profile" s.apparmorProfile).toArray

end LeanSudo.Sys.Plugins
