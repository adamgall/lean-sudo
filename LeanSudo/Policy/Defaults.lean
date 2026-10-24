import LeanSudo.Policy.Eval

/-!
# `Defaults` resolution

`resolveDefaults` folds the applicable `Defaults` entries over sudo's compiled-in
`Settings` (the field defaults of `Settings`). Application order is sudo's:

1. global, host and user defaults together in file order,
2. run-as defaults,
3. command defaults.

Within each phase early options are applied before ordinary options, as in
`update_defaults`; matching uses the current settings and gathered system facts.

Value conventions (matching sudo where it has a notion of it):
* flags: `name` / `!name`; a value is an error.
* lists (`env_keep`, `env_check`, `env_delete`): `=` replaces, `+=` appends (names
  already present are not duplicated), `-=` removes, `!name` clears. Values are split
  on whitespace, so one quoted value may hold several names.
* `umask`: octal ≤ 0777. `!umask` stores `0o777`, which (as in sudo) means "do not
  change the user's umask"; the exec layer must treat `0o777` that way.
* `timestamp_timeout`: minutes, possibly fractional (`2.5`), stored as whole seconds
  (rounded down); negative ⇒ `none` (never expires); `!timestamp_timeout` ⇒ 0.
* `tty_tickets` ⇒ `timestamp_type=tty`, `!tty_tickets` ⇒ `timestamp_type=global`
  (sudo's `cb_tty_tickets`).
* `listpw`/`verifypw`: `all|always|any|never`; `!listpw` ⇒ `never`.
* `syslog`: a facility name; `!syslog` ⇒ no syslog.
* Options are checked against sudo's complete typed option table and stored.
  Unsupported actions are rejected by the decision core, not by the parser.
* Invalid typed values are fatal like syntax errors: silently substituting a
  permissive compiled-in default could widen access. Unknown option names only
  warn; `ignore_unknown_defaults` suppresses that warning in its early phase.
-/

namespace LeanSudo.Policy

open LeanSudo.Sudoers

/-! ## Value parsing -/

/-- Split on whitespace, dropping empty words. -/
def splitWords (v : String) : List String :=
  go v.toList []
where
  go : List Char → List Char → List String
    | [], cur => if cur.isEmpty then [] else [String.ofList cur.reverse]
    | c :: cs, cur =>
      if c.isWhitespace then
        if cur.isEmpty then go cs [] else String.ofList cur.reverse :: go cs []
      else go cs (c :: cur)

def digitVal (c : Char) : Nat := c.toNat - '0'.toNat

/-- Strict unsigned decimal (at least one digit, nothing else). -/
def parseDecimal (v : String) : Option Nat :=
  let cs := v.toList
  if cs.isEmpty || !cs.all Char.isDigit then none
  else some (cs.foldl (fun a c => a * 10 + digitVal c) 0)

/-- Strict octal (at least one digit `0`–`7`). -/
def parseOctal (v : String) : Option Nat :=
  let cs := v.toList
  if cs.isEmpty || !cs.all (fun c => '0' ≤ c && c ≤ '7') then none
  else some (cs.foldl (fun a c => a * 8 + digitVal c) 0)

/-- Minutes to whole seconds, rounding down. Subsecond remainders are deliberately
discarded, so cached authentication never outlives the configured duration. -/
def parseTimeout (v : String) : Option (Option Nat) :=
  let (neg, rest) : Bool × List Char :=
    match v.toList with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  let ip := rest.takeWhile (· != '.')
  let fp := (rest.dropWhile (· != '.')).drop 1
  let hasDot := rest.contains '.'
  if (ip.isEmpty && fp.isEmpty) || !ip.all Char.isDigit || !fp.all Char.isDigit
      || (hasDot && (rest.dropWhile (· != '.')).length != fp.length + 1) then none
  else
    let iv := ip.foldl (fun a c => a * 10 + digitVal c) 0
    let fv := fp.foldl (fun a c => a * 10 + digitVal c) 0
    let secs := iv * 60 + fv * 60 / 10 ^ fp.length
    if secs > 9223372036854775807 then none
    else if neg && (iv != 0 || fv != 0) then some none else some (some secs)

def parsePwPolicy : String → Option PwPolicy
  | "all" => some .all
  | "always" => some .always
  | "any" => some .any
  | "never" => some .never
  | _ => none

def parseTimestampType : String → Option TimestampType
  | "tty" => some .tty
  | "ppid" => some .ppid
  | "global" => some .global
  | "kernel" => some .kernel
  | _ => none

def syslogFacilities : List String :=
  ["authpriv", "auth", "daemon", "user", "local0", "local1", "local2", "local3", "local4",
   "local5", "local6", "local7", "cron", "kern", "lpr", "mail", "news", "syslog", "uucp", "ftp"]

/-! ## Typed option table (sudo 1.9.17p2 `def_data.in`) -/

/-- Paths are checked before storage, just as `valid_path` in sudoers. -/
inductive DefaultPath where
  | unrestricted | absolute | changeDirectory

/-- Each constructor carries a correctly typed setter. -/
inductive DefaultKind where
  | flag (set : Settings → Bool → Settings)
  | string (boolean : Bool) (path : DefaultPath) (set : Settings → Option String → Settings)
  | list (spaces : Bool) (get : Settings → List String) (set : Settings → List String → Settings)
  | unsigned (boolean : Bool) (set : Settings → Nat → Settings)
  | integer (set : Settings → Int → Settings)
  | mode (boolean : Bool) (set : Settings → Nat → Settings)
  | minutes (set : Settings → Option Nat → Settings)
  | timeout (set : Settings → Nat → Settings)
  | tuple (boolean : Bool) (values : List String) (set : Settings → String → Settings)
  | rlimit (set : Settings → Option String → Settings)
  | facility (set : Settings → Option String → Settings)
  | priority (set : Settings → Option String → Settings)

/-- All options are accepted and stored; execution support is checked by the decision core. -/
def defaultKind : String → Option DefaultKind
  | "syslog" => some (.facility (fun st v => { st with syslog := v }))
  | "syslog_goodpri" => some (.priority (fun st v => { st with syslogGoodpri := v }))
  | "syslog_badpri" => some (.priority (fun st v => { st with syslogBadpri := v }))
  | "long_otp_prompt" => some (.flag (fun st v => { st with longOtpPrompt := v }))
  | "ignore_dot" => some (.flag (fun st v => { st with ignoreDot := v }))
  | "mail_always" => some (.flag (fun st v => { st with mailAlways := v }))
  | "mail_badpass" => some (.flag (fun st v => { st with mailBadpass := v }))
  | "mail_no_user" => some (.flag (fun st v => { st with mailNoUser := v }))
  | "mail_no_host" => some (.flag (fun st v => { st with mailNoHost := v }))
  | "mail_no_perms" => some (.flag (fun st v => { st with mailNoPerms := v }))
  | "mail_all_cmnds" => some (.flag (fun st v => { st with mailAllCmnds := v }))
  | "tty_tickets" => some (.flag (fun st v => { st with timestampType := if v then .tty else .global }))
  | "lecture" => some (.tuple true ["never", "once", "always"] (fun st v => { st with lecture := v }))
  | "lecture_file" => some (.string true .absolute (fun st v => { st with lectureFile := v }))
  | "authenticate" => some (.flag (fun st v => { st with authenticate := v }))
  | "root_sudo" => some (.flag (fun st v => { st with rootSudo := v }))
  | "log_host" => some (.flag (fun st v => { st with logHost := v }))
  | "log_year" => some (.flag (fun st v => { st with logYear := v }))
  | "shell_noargs" => some (.flag (fun st v => { st with shellNoargs := v }))
  | "set_home" => some (.flag (fun st v => { st with setHome := v }))
  | "always_set_home" => some (.flag (fun st v => { st with alwaysSetHome := v }))
  | "path_info" => some (.flag (fun st v => { st with pathInfo := v }))
  | "fqdn" => some (.flag (fun st v => { st with fqdn := v }))
  | "insults" => some (.flag (fun st v => { st with insults := v }))
  | "requiretty" => some (.flag (fun st v => { st with requiretty := v }))
  | "env_editor" => some (.flag (fun st v => { st with envEditor := v }))
  | "rootpw" => some (.flag (fun st v => { st with rootpw := v }))
  | "runaspw" => some (.flag (fun st v => { st with runaspw := v }))
  | "targetpw" => some (.flag (fun st v => { st with targetpw := v }))
  | "use_loginclass" => some (.flag (fun st v => { st with useLoginclass := v }))
  | "set_logname" => some (.flag (fun st v => { st with setLogname := v }))
  | "stay_setuid" => some (.flag (fun st v => { st with staySetuid := v }))
  | "preserve_groups" => some (.flag (fun st v => { st with preserveGroups := v }))
  | "loglinelen" => some (.unsigned true (fun st v => { st with loglinelen := v }))
  | "timestamp_timeout" => some (.minutes (fun st v => { st with timestampTimeout := v }))
  | "passwd_timeout" => some (.minutes (fun st v => { st with passwdTimeout := v }))
  | "passwd_tries" => some (.unsigned false (fun st v => { st with passwdTries := v }))
  | "umask" => some (.mode true (fun st v => { st with umask := v }))
  | "logfile" => some (.string true .absolute (fun st v => { st with logfile := v }))
  | "mailerpath" => some (.string true .absolute (fun st v => { st with mailerpath := v }))
  | "mailerflags" => some (.string true .unrestricted (fun st v => { st with mailerflags := v }))
  | "mailto" => some (.string true .unrestricted (fun st v => { st with mailto := v }))
  | "mailfrom" => some (.string true .unrestricted (fun st v => { st with mailfrom := v }))
  | "mailsub" => some (.string false .unrestricted (fun st v => { st with mailsub := v.getD "" }))
  | "badpass_message" => some (.string false .unrestricted (fun st v => { st with badpassMessage := v.getD "" }))
  | "lecture_status_dir" => some (.string false .absolute (fun st v => { st with lectureStatusDir := v.getD "" }))
  | "timestampdir" => some (.string false .absolute (fun st v => { st with timestampdir := v.getD "" }))
  | "timestampowner" => some (.string false .unrestricted (fun st v => { st with timestampowner := v }))
  | "exempt_group" => some (.string true .unrestricted (fun st v => { st with exemptGroup := v }))
  | "passprompt" => some (.string false .unrestricted (fun st v => { st with passprompt := v.getD "" }))
  | "passprompt_override" => some (.flag (fun st v => { st with passpromptOverride := v }))
  | "runas_default" => some (.string false .unrestricted (fun st v => { st with runasDefault := v.getD "" }))
  | "secure_path" => some (.string true .unrestricted (fun st v => { st with securePath := v }))
  | "editor" => some (.string false .absolute (fun st v => { st with editor := v.getD "" }))
  | "listpw" => some (.tuple true ["never", "any", "all", "always"] (fun st v => { st with listpw := (parsePwPolicy v).getD .never }))
  | "verifypw" => some (.tuple true ["never", "all", "any", "always"] (fun st v => { st with verifypw := (parsePwPolicy v).getD .never }))
  | "noexec" => some (.flag (fun st v => { st with noexec := v }))
  | "ignore_local_sudoers" => some (.flag (fun st v => { st with ignoreLocalSudoers := v }))
  | "closefrom" => some (.integer (fun st v => { st with closefrom := v }))
  | "closefrom_override" => some (.flag (fun st v => { st with closefromOverride := v }))
  | "setenv" => some (.flag (fun st v => { st with setenv := v }))
  | "env_reset" => some (.flag (fun st v => { st with envReset := v }))
  | "env_check" => some (.list false (·.envCheck) (fun st v => { st with envCheck := v }))
  | "env_delete" => some (.list false (·.envDelete) (fun st v => { st with envDelete := v }))
  | "env_keep" => some (.list false (·.envKeep) (fun st v => { st with envKeep := v }))
  | "role" => some (.string false .unrestricted (fun st v => { st with role := v }))
  | "type" => some (.string false .unrestricted (fun st v => { st with type := v }))
  | "env_file" => some (.string true .absolute (fun st v => { st with envFile := v }))
  | "restricted_env_file" => some (.string true .absolute (fun st v => { st with restrictedEnvFile := v }))
  | "sudoers_locale" => some (.string false .unrestricted (fun st v => { st with sudoersLocale := v.getD "" }))
  | "visiblepw" => some (.flag (fun st v => { st with visiblepw := v }))
  | "pwfeedback" => some (.flag (fun st v => { st with pwfeedback := v }))
  | "fast_glob" => some (.flag (fun st v => { st with fastGlob := v }))
  | "umask_override" => some (.flag (fun st v => { st with umaskOverride := v }))
  | "log_input" => some (.flag (fun st v => { st with logInput := v, logStdin := v, logTtyin := v }))
  | "log_stdin" => some (.flag (fun st v => { st with logStdin := v }))
  | "log_ttyin" => some (.flag (fun st v => { st with logTtyin := v }))
  | "log_output" => some (.flag (fun st v => { st with logOutput := v, logStdout := v, logStderr := v, logTtyout := v }))
  | "log_stdout" => some (.flag (fun st v => { st with logStdout := v }))
  | "log_stderr" => some (.flag (fun st v => { st with logStderr := v }))
  | "log_ttyout" => some (.flag (fun st v => { st with logTtyout := v }))
  | "compress_io" => some (.flag (fun st v => { st with compressIo := v }))
  | "use_pty" => some (.flag (fun st v => { st with usePty := v }))
  | "group_plugin" => some (.string false .unrestricted (fun st v => { st with groupPlugin := v }))
  | "iolog_dir" => some (.string false .absolute (fun st v => { st with iologDir := v.getD "" }))
  | "iolog_file" => some (.string false .unrestricted (fun st v => { st with iologFile := v.getD "" }))
  | "set_utmp" => some (.flag (fun st v => { st with setUtmp := v }))
  | "utmp_runas" => some (.flag (fun st v => { st with utmpRunas := v }))
  | "privs" => some (.string false .unrestricted (fun st v => { st with privs := v }))
  | "limitprivs" => some (.string false .unrestricted (fun st v => { st with limitprivs := v }))
  | "exec_background" => some (.flag (fun st v => { st with execBackground := v }))
  | "pam_service" => some (.string false .unrestricted (fun st v => { st with pamService := v.getD "" }))
  | "pam_login_service" => some (.string false .unrestricted (fun st v => { st with pamLoginService := v.getD "" }))
  | "pam_askpass_service" => some (.string false .unrestricted (fun st v => { st with pamAskpassService := v }))
  | "pam_setcred" => some (.flag (fun st v => { st with pamSetcred := v }))
  | "pam_session" => some (.flag (fun st v => { st with pamSession := v }))
  | "pam_acct_mgmt" => some (.flag (fun st v => { st with pamAcctMgmt := v }))
  | "pam_silent" => some (.flag (fun st v => { st with pamSilent := v }))
  | "maxseq" => some (.string false .unrestricted (fun st v => { st with maxseq := v.getD "" }))
  | "use_netgroups" => some (.flag (fun st v => { st with useNetgroups := v }))
  | "sudoedit_checkdir" => some (.flag (fun st v => { st with sudoeditCheckdir := v }))
  | "sudoedit_follow" => some (.flag (fun st v => { st with sudoeditFollow := v }))
  | "always_query_group_plugin" => some (.flag (fun st v => { st with alwaysQueryGroupPlugin := v }))
  | "netgroup_tuple" => some (.flag (fun st v => { st with netgroupTuple := v }))
  | "ignore_audit_errors" => some (.flag (fun st v => { st with ignoreAuditErrors := v }))
  | "ignore_iolog_errors" => some (.flag (fun st v => { st with ignoreIologErrors := v }))
  | "ignore_logfile_errors" => some (.flag (fun st v => { st with ignoreLogfileErrors := v }))
  | "match_group_by_gid" => some (.flag (fun st v => { st with matchGroupByGid := v }))
  | "syslog_maxlen" => some (.unsigned false (fun st v => { st with syslogMaxlen := v }))
  | "iolog_user" => some (.string true .unrestricted (fun st v => { st with iologUser := v }))
  | "iolog_group" => some (.string true .unrestricted (fun st v => { st with iologGroup := v }))
  | "iolog_mode" => some (.mode false (fun st v => { st with iologMode := v }))
  | "fdexec" => some (.tuple true ["never", "digest_only", "always"] (fun st v => { st with fdexec := v }))
  | "ignore_unknown_defaults" => some (.flag (fun st v => { st with ignoreUnknownDefaults := v }))
  | "command_timeout" => some (.timeout (fun st v => { st with commandTimeout := v }))
  | "user_command_timeouts" => some (.flag (fun st v => { st with userCommandTimeouts := v }))
  | "iolog_flush" => some (.flag (fun st v => { st with iologFlush := v }))
  | "syslog_pid" => some (.flag (fun st v => { st with syslogPid := v }))
  | "timestamp_type" => some (.tuple false ["global", "ppid", "tty", "kernel"] (fun st v => { st with timestampType := (parseTimestampType v).getD .tty }))
  | "authfail_message" => some (.string false .unrestricted (fun st v => { st with authfailMessage := v }))
  | "case_insensitive_user" => some (.flag (fun st v => { st with caseInsensitiveUser := v }))
  | "case_insensitive_group" => some (.flag (fun st v => { st with caseInsensitiveGroup := v }))
  | "log_allowed" => some (.flag (fun st v => { st with logAllowed := v }))
  | "log_denied" => some (.flag (fun st v => { st with logDenied := v }))
  | "log_servers" => some (.list false (·.logServers) (fun st v => { st with logServers := v }))
  | "log_server_timeout" => some (.timeout (fun st v => { st with logServerTimeout := v }))
  | "log_server_keepalive" => some (.flag (fun st v => { st with logServerKeepalive := v }))
  | "log_server_cabundle" => some (.string true .absolute (fun st v => { st with logServerCabundle := v }))
  | "log_server_peer_cert" => some (.string true .absolute (fun st v => { st with logServerPeerCert := v }))
  | "log_server_peer_key" => some (.string true .absolute (fun st v => { st with logServerPeerKey := v }))
  | "log_server_verify" => some (.flag (fun st v => { st with logServerVerify := v }))
  | "runas_allow_unknown_id" => some (.flag (fun st v => { st with runasAllowUnknownId := v }))
  | "runas_check_shell" => some (.flag (fun st v => { st with runasCheckShell := v }))
  | "pam_ruser" => some (.flag (fun st v => { st with pamRuser := v }))
  | "pam_rhost" => some (.flag (fun st v => { st with pamRhost := v }))
  | "runcwd" => some (.string true .changeDirectory (fun st v => { st with runcwd := v }))
  | "runchroot" => some (.string true .changeDirectory (fun st v => { st with runchroot := v }))
  | "log_format" => some (.tuple false ["sudo", "json", "json_compact", "json_pretty"] (fun st v => { st with logFormat := v }))
  | "selinux" => some (.flag (fun st v => { st with selinux := v }))
  | "admin_flag" => some (.string true .changeDirectory (fun st v => { st with adminFlag := v }))
  | "intercept" => some (.flag (fun st v => { st with intercept := v }))
  | "log_subcmds" => some (.flag (fun st v => { st with logSubcmds := v }))
  | "log_exit_status" => some (.flag (fun st v => { st with logExitStatus := v }))
  | "intercept_authenticate" => some (.flag (fun st v => { st with interceptAuthenticate := v }))
  | "intercept_allow_setid" => some (.flag (fun st v => { st with interceptAllowSetid := v }))
  | "rlimit_as" => some (.rlimit (fun st v => { st with rlimitAs := v }))
  | "rlimit_core" => some (.rlimit (fun st v => { st with rlimitCore := v }))
  | "rlimit_cpu" => some (.rlimit (fun st v => { st with rlimitCpu := v }))
  | "rlimit_data" => some (.rlimit (fun st v => { st with rlimitData := v }))
  | "rlimit_fsize" => some (.rlimit (fun st v => { st with rlimitFsize := v }))
  | "rlimit_locks" => some (.rlimit (fun st v => { st with rlimitLocks := v }))
  | "rlimit_memlock" => some (.rlimit (fun st v => { st with rlimitMemlock := v }))
  | "rlimit_nofile" => some (.rlimit (fun st v => { st with rlimitNofile := v }))
  | "rlimit_nproc" => some (.rlimit (fun st v => { st with rlimitNproc := v }))
  | "rlimit_rss" => some (.rlimit (fun st v => { st with rlimitRss := v }))
  | "rlimit_stack" => some (.rlimit (fun st v => { st with rlimitStack := v }))
  | "noninteractive_auth" => some (.flag (fun st v => { st with noninteractiveAuth := v }))
  | "log_passwords" => some (.flag (fun st v => { st with logPasswords := v }))
  | "passprompt_regex" => some (.list true (·.passpromptRegex) (fun st v => { st with passpromptRegex := v }))
  | "intercept_type" => some (.tuple false ["dso", "trace"] (fun st v => { st with interceptType := v }))
  | "intercept_verify" => some (.flag (fun st v => { st with interceptVerify := v }))
  | "apparmor_profile" => some (.string false .unrestricted (fun st v => { st with apparmorProfile := v }))
  | "cmddenial_message" => some (.string false .unrestricted (fun st v => { st with cmddenialMessage := v }))
  | _ => none

def defaultOptionNames : List String :=
  ["syslog", "syslog_goodpri", "syslog_badpri", "long_otp_prompt", "ignore_dot", "mail_always", "mail_badpass", "mail_no_user", "mail_no_host", "mail_no_perms", "mail_all_cmnds", "tty_tickets", "lecture", "lecture_file", "authenticate", "root_sudo", "log_host", "log_year", "shell_noargs", "set_home", "always_set_home", "path_info", "fqdn", "insults", "requiretty", "env_editor", "rootpw", "runaspw", "targetpw", "use_loginclass", "set_logname", "stay_setuid", "preserve_groups", "loglinelen", "timestamp_timeout", "passwd_timeout", "passwd_tries", "umask", "logfile", "mailerpath", "mailerflags", "mailto", "mailfrom", "mailsub", "badpass_message", "lecture_status_dir", "timestampdir", "timestampowner", "exempt_group", "passprompt", "passprompt_override", "runas_default", "secure_path", "editor", "listpw", "verifypw", "noexec", "ignore_local_sudoers", "closefrom", "closefrom_override", "setenv", "env_reset", "env_check", "env_delete", "env_keep", "role", "type", "env_file", "restricted_env_file", "sudoers_locale", "visiblepw", "pwfeedback", "fast_glob", "umask_override", "log_input", "log_stdin", "log_ttyin", "log_output", "log_stdout", "log_stderr", "log_ttyout", "compress_io", "use_pty", "group_plugin", "iolog_dir", "iolog_file", "set_utmp", "utmp_runas", "privs", "limitprivs", "exec_background", "pam_service", "pam_login_service", "pam_askpass_service", "pam_setcred", "pam_session", "pam_acct_mgmt", "pam_silent", "maxseq", "use_netgroups", "sudoedit_checkdir", "sudoedit_follow", "always_query_group_plugin", "netgroup_tuple", "ignore_audit_errors", "ignore_iolog_errors", "ignore_logfile_errors", "match_group_by_gid", "syslog_maxlen", "iolog_user", "iolog_group", "iolog_mode", "fdexec", "ignore_unknown_defaults", "command_timeout", "user_command_timeouts", "iolog_flush", "syslog_pid", "timestamp_type", "authfail_message", "case_insensitive_user", "case_insensitive_group", "log_allowed", "log_denied", "log_servers", "log_server_timeout", "log_server_keepalive", "log_server_cabundle", "log_server_peer_cert", "log_server_peer_key", "log_server_verify", "runas_allow_unknown_id", "runas_check_shell", "pam_ruser", "pam_rhost", "runcwd", "runchroot", "log_format", "selinux", "admin_flag", "intercept", "log_subcmds", "log_exit_status", "intercept_authenticate", "intercept_allow_setid", "rlimit_as", "rlimit_core", "rlimit_cpu", "rlimit_data", "rlimit_fsize", "rlimit_locks", "rlimit_memlock", "rlimit_nofile", "rlimit_nproc", "rlimit_rss", "rlimit_stack", "noninteractive_auth", "log_passwords", "passprompt_regex", "intercept_type", "intercept_verify", "apparmor_profile", "cmddenial_message"]

def opText : DefaultsOp → String
  | .flag true => ""
  | .flag false => "!"
  | .assign _ => "="
  | .add _ => "+="
  | .remove _ => "-="

private def invalid (name v : String) : Except String α :=
  .error s!"value \"{v}\" is invalid for option \"{name}\""

private def noValue (name : String) : Except String α :=
  .error s!"no value specified for \"{name}\""

private def badOp (name : String) (op : DefaultsOp) : Except String α :=
  .error s!"invalid operator \"{opText op}\" for \"{name}\""

private def valueOf (name : String) (boolean : Bool) : DefaultsOp → Except String (Option String)
  | .assign v => .ok (some v)
  | .flag false => if boolean then .ok none else noValue name
  | .flag true => noValue name
  | op => badOp name op

/-- Sudo command timeouts are compound decimal seconds/minutes/hours/days. -/
def parseCommandTimeout (v : String) : Option Nat :=
  go v.toList 0 0 false
where
  go : List Char → Nat → Nat → Bool → Option Nat
    | [], total, cur, digits =>
      if digits && total + cur ≤ 2147483647 then some (total + cur) else none
    | c :: cs, total, cur, digits =>
      if c.isDigit then go cs total (cur * 10 + digitVal c) true
      else
        let multiplier := match c with | 's' => 1 | 'm' => 60 | 'h' => 3600 | 'd' => 86400 | _ => 0
        let total := total + cur * multiplier
        if !digits || multiplier == 0 || total > 2147483647 then none
        else if cs.isEmpty then some total else go cs total 0 false

private def validRlimit (v : String) : Bool :=
  let atom (s : String) := s == "infinity" || (parseDecimal s).any (· ≤ 18446744073709551615)
  v == "user" || v == "default" || match v.splitOn "," with
    | [a] => atom a
    | [a,b] => atom a && atom b
    | _ => false

private def checkPath (name : String) (path : DefaultPath) (v : String) : Except String Unit := do
  match path with
  | .unrestricted => pure ()
  | _ =>
    if v.utf8ByteSize ≥ 4096 then throw s!"path name for \"{name}\" too long"
    match path with
    | .absolute =>
      if !v.startsWith "/" then throw s!"values for \"{name}\" must start with a '/'"
    | .changeDirectory =>
      if !v.startsWith "/" && !v.startsWith "~" && v != "*" then
        throw s!"values for \"{name}\" must start with a '/', '~', or '*'"
    | .unrestricted => pure ()

/-- Apply one setting. Visudo validates types without running runtime callbacks. -/
def applySetting (st : Settings) (d : DefaultsSetting) (callbacks : Bool := true)
    : Except String (Settings × Option String) := do
  let n := d.name
  let some kind := defaultKind n |
    return (st, if st.ignoreUnknownDefaults then none else some s!"unknown defaults entry \"{n}\"")
  let result ← match kind with
  | .flag set =>
    match d.op with
    | .flag b => pure (set st b)
    | .assign _ => throw s!"option \"{n}\" does not take a value"
    | op => badOp n op
  | .list spaces get set =>
    let words (v : String) := if spaces then [v] else splitWords v
    match d.op with
    | .flag false => pure (set st [])
    | .flag true => noValue n
    | .assign v => pure (set st (words v).eraseDups)
    | .add v => pure (set st ((get st) ++ (words v).filter (fun x => !(get st).contains x)).eraseDups)
    | .remove v => pure (set st ((get st).filter (fun x => !(words v).contains x)))
  | .string boolean path set => do
    let v ← valueOf n boolean d.op
    if let some text := v then checkPath n path text
    if callbacks && n == "maxseq" then
      let text := v.getD ""
      match text.toInt? with
      | none => invalid n text
      | some value =>
        let bounded := if value < 0 || value > 2176782335 then 2176782335 else value
        pure (set st (some (toString bounded)))
    else pure (set st v)
  | .rlimit set => do
    let v ← valueOf n true d.op
    if let some text := v then
      if !validRlimit text then invalid n text else pure (set st v)
    else pure (set st none)
  | .unsigned boolean set => do
    let v ← valueOf n boolean d.op
    match v with
    | none => pure (set st 0)
    | some text => match parseDecimal (if text.startsWith "+" then text.drop 1 |>.toString else text) with
      | some k => if k ≤ 4294967295 then pure (set st k) else invalid n text
      | none => invalid n text
  | .integer set => do
    let v ← valueOf n false d.op
    let text := v.getD ""
    match text.toInt? with
    | some k => if -2147483648 ≤ k && k ≤ 2147483647 then pure (set st k) else invalid n text
    | none => invalid n text
  | .mode boolean set => do
    let v ← valueOf n boolean d.op
    match v with
    | none => pure (set st 0o777)
    | some text => match parseOctal text with
      | some k => if k ≤ 0o777 then pure (set st k) else invalid n text
      | none => invalid n text
  | .minutes set => do
    let v ← valueOf n true d.op
    match v with
    | none => pure (set st (some 0))
    | some text => match parseTimeout text with
      | some seconds => pure (set st seconds)
      | none => invalid n text
  | .timeout set => do
    let v ← valueOf n true d.op
    match v with
    | none => pure (set st 0)
    | some text => match parseCommandTimeout text with
      | some seconds => pure (set st seconds)
      | none => invalid n text
  | .tuple boolean values set =>
    match d.op with
    | .flag b => if boolean then pure (set st ((values[b.toNat]?).getD "")) else noValue n
    | .assign text => if values.contains text then pure (set st text) else invalid n text
    | op => badOp n op
  | .facility set =>
    match d.op with
    | .flag true => pure (set st (some "authpriv"))
    | .flag false => pure (set st none)
    | .assign text => if syslogFacilities.contains text then pure (set st (some text)) else invalid n text
    | op => badOp n op
  | .priority set => do
    let v ← valueOf n true d.op
    match v with
    | none => pure (set st none)
    | some text =>
      if text == "none" then pure (set st none)
      else if ["emerg", "alert", "crit", "err", "warning", "notice", "info", "debug"].contains text then
        pure (set st (some text))
      else invalid n text
  return (result, none)

/-- Apply settings in order, collecting warnings. -/
def applySettings (st : Settings) (ds : List DefaultsSetting) : Except String (Settings × List String) :=
  ds.foldlM (fun (acc : Settings × List String) d => do
    let (st', w) ← applySetting acc.1 d
    pure (st', acc.2 ++ w.toList)) (st, [])

/-! ## Scoping -/

/-- `Defaults` entries of a policy, in file order. -/
def defaultsOf : Sudoers → List (DefaultsScope × List DefaultsSetting)
  | [] => []
  | .defaults sc ss :: es => (sc, ss) :: defaultsOf es
  | _ :: es => defaultsOf es

/-- Early Defaults whose callbacks affect subsequent option processing. -/
def earlyDefaults : List String :=
  ["ignore_unknown_defaults", "fqdn", "match_group_by_gid", "group_plugin",
   "runas_default", "sudoers_locale"]

private def scopePhase : DefaultsScope → Nat
  | .global | .host _ | .user _ => 0
  | .runas _ => 1
  | .cmnd _ => 2

private def scopeMatches (al : Aliases) (st : Settings) (user : Principal) (host : String)
    (runas : Option Principal) (cmd : Option Command) (canon : String → String)
    (facts : Option Request) : DefaultsScope → Bool
  | .global => true
  | .host hs => hostListOk al al.fuel host hs st facts
  | .user us => userListOk al al.fuel user us st facts
  | .runas rs => runas.any fun t => runasUserResult al al.fuel t rs st facts == some true
  | .cmnd cs => cmd.any fun cm =>
    cmndListResult al al.fuel canon cm cs
      (facts.map fun r => { r with command := cm, fastGlob := st.fastGlob }) == some true

/-- Applicable settings in phase order, with explicit matching settings and facts. -/
def applicableDefaults (s : Sudoers) (user : Principal) (host : String) (runas : Option Principal)
    (cmd : Option Command) (canon : String → String := id) (st : Settings := {})
    (facts : Option Request := none) : List DefaultsSetting :=
  let al := aliasesOf s
  [0, 1, 2].flatMap fun phase =>
    (defaultsOf s).flatMap fun (sc, ss) =>
      if scopePhase sc == phase && scopeMatches al st user host runas cmd canon facts sc then ss else []

/-- Resolve all options, rejecting invalid values and retaining unknown-option warnings. -/
def resolveDefaults (s : Sudoers) (user : Principal) (host : String) (runas : Option Principal)
    (cmd : Option Command) (canon : String → String := id) (facts : Option Request := none)
    : Except String (Settings × List String) := do
  let al := aliasesOf s
  let ds := defaultsOf s
  [0, 1, 2].foldlM (fun acc phase =>
    [true, false].foldlM (fun acc early =>
      ds.foldlM (fun (acc : Settings × List String) (sc, ss) => do
        if scopePhase sc != phase || !scopeMatches al acc.1 user host runas cmd canon facts sc then
          return acc
        let (st, warnings) ← applySettings acc.1 (ss.filter fun d => earlyDefaults.contains d.name == early)
        return (st, acc.2 ++ warnings)) acc) acc) ({}, [])

/-- Clearing an unknown option cannot mutate any setting. -/
theorem applySetting_unknown (st : Settings) (d : DefaultsSetting)
    (h : defaultKind d.name = none) :
    (applySetting st d).toOption.map Prod.fst = some st := by
  simp only [applySetting, h]
  rfl

end LeanSudo.Policy
