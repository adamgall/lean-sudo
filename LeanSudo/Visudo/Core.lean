import LeanSudo.Policy.Defaults
import LeanSudo.Sudoers.Parser

/-!
# visudo: pure parts

Command-line parsing, diagnostics rendering and the semantic checks run on a parsed
(include-resolved) policy.

visudo must reject everything lean-sudo's `sudo` would refuse to run with, otherwise
an "OK" edit could lock the administrator out. Hence, compared with sudo.ws's visudo:

* undefined alias references and alias cycles are always errors (sudo.ws only warns
  unless `-s`); `-s` is accepted and changes nothing,
* `Defaults` values are checked with the same `applySetting` the policy uses, so
  options lean-sudo refuses (`noexec`, `intercept`, ...) are errors; names unknown to
  sudo.ws too are errors as in sudo.ws; options sudo.ws knows but lean-sudo ignores
  are accepted (with a warning unless they are in `ignoredOptions`),
* `Policy.validate` runs last as the authoritative check.

Diagnostics carry `file:line` (the AST records no column for entries).
-/

namespace LeanSudo.Visudo

open LeanSudo.Sudoers LeanSudo.Policy

/-! ## Command line -/

structure Options where
  check : Bool := false
  /-- `-f file` or the single operand; `none` = `/etc/sudoers` -/
  file : Option String := none
  quiet : Bool := false
  strict : Bool := false
  noIncludes : Bool := false
  owner : Bool := false
  perms : Bool := false
  help : Bool := false
  version : Bool := false
  deriving Repr, BEq, Inhabited

def usageLine : String := "usage: visudo [-chqsV] [[-f] sudoers ]"

def helpText : String :=
  "visudo - safely edit the sudoers file\n\n" ++ usageLine ++ "\n\nOptions:\n" ++
  "  -c, --check              check-only mode\n" ++
  "  -f, --file=sudoers       specify sudoers file location\n" ++
  "  -h, --help               display help message and exit\n" ++
  "  -I, --no-includes        do not edit include files\n" ++
  "  -O, --owner              enforce the default ownership of the sudoers file\n" ++
  "  -P, --perms              enforce the default permissions of the sudoers file\n" ++
  "  -q, --quiet              less verbose (quiet) syntax error messages\n" ++
  "  -s, --strict             strict syntax checking\n" ++
  "  -V, --version            display version information and exit\n\n"

def versionText : String :=
  "visudo version 1.9.16 (lean-sudo 0.1.0)\nvisudo grammar version 50\n"

/-- Boolean short options. -/
def flagOf : Char → Option (Options → Options)
  | 'c' => some fun o => { o with check := true }
  | 'h' => some fun o => { o with help := true }
  | 'I' => some fun o => { o with noIncludes := true }
  | 'O' => some fun o => { o with owner := true }
  | 'P' => some fun o => { o with perms := true }
  | 'q' => some fun o => { o with quiet := true }
  | 's' => some fun o => { o with strict := true }
  | 'V' => some fun o => { o with version := true }
  | _ => none

def longOptions : List (String × Char) :=
  [("check", 'c'), ("file", 'f'), ("help", 'h'), ("no-includes", 'I'), ("owner", 'O'),
   ("perms", 'P'), ("quiet", 'q'), ("strict", 's'), ("version", 'V')]

/-- `getopt_long` lookup: exact name, else a unique prefix. -/
def lookupLong (name : String) : Except String Char :=
  match longOptions.find? (·.1 == name) with
  | some (_, c) => .ok c
  | none =>
    match longOptions.filter (fun (n, _) => !name.isEmpty && n.startsWith name) with
    | [(_, c)] => .ok c
    | [] => .error s!"unrecognized option '--{name}'"
    | _ => .error s!"option '--{name}' is ambiguous"

/-- Short-option bundle (`-cq`, `-ffile`, `-cf file`). Returns the updated options and,
when `f` was reached, the rest of the bundle as its value (`""` = take the next word). -/
def shortBundle : List Char → Options → Except String (Options × Option String)
  | [], o => .ok (o, none)
  | 'f' :: rest, o => .ok (o, some (String.ofList rest))
  | c :: rest, o =>
    match flagOf c with
    | some f => shortBundle rest (f o)
    | none => .error s!"invalid option -- '{c}'"

/-- The single operand is the sudoers file (only if `-f` was not given). -/
def finishArgs (o : Options) : List String → Except String Options
  | [] => .ok o
  | [f] => if o.file.isSome then .error "" else .ok { o with file := some f }
  | _ => .error ""

/-- GNU-style parsing (options may follow operands; `--` ends options). An error's text
is the diagnostic line (without `visudo: `), empty when only the usage line applies. -/
def parseArgs (args : List String) : Except String Options :=
  go args {} [] none
where
  /-- `pending = some msg`: the next word is the `-f` value (`msg` if it is missing). -/
  go : List String → Options → List String → Option String → Except String Options
  | [], _, _, some msg => .error msg
  | [], o, ops, none => finishArgs o ops.reverse
  | a :: rest, o, ops, some _ => go rest { o with file := some a } ops none
  | "--" :: rest, o, ops, none => finishArgs o (ops.reverse ++ rest)
  | a :: rest, o, ops, none =>
    match a.toList with
    | '-' :: '-' :: body =>
      let (name, val?) : List Char × Option (List Char) :=
        match body.span (· != '=') with
        | (n, []) => (n, none)
        | (n, _ :: v) => (n, some v)
      let name := String.ofList name
      match lookupLong name with
      | .error e => .error e
      | .ok 'f' =>
        match val? with
        | some v => go rest { o with file := some (String.ofList v) } ops none
        | none => go rest o ops (some "option '--file' requires an argument")
      | .ok c =>
        match val?, flagOf c with
        | some _, _ =>
          let full := ((longOptions.find? (·.2 == c)).map (·.1)).getD name
          .error s!"option '--{full}' doesn't allow an argument"
        | none, some f => go rest (f o) ops none
        | none, none => .error s!"unrecognized option '--{name}'"
    | '-' :: c :: cs =>
      match shortBundle (c :: cs) o with
      | .error e => .error e
      | .ok (o', none) => go rest o' ops none
      | .ok (o', some "") => go rest o' ops (some "option requires an argument -- 'f'")
      | .ok (o', some v) => go rest { o' with file := some v } ops none
    | _ => go rest o (a :: ops) none

/-! ## Diagnostics -/

def locPos (l : Located) : String := s!"{l.file}:{l.line}"

/-- sudo-style syntax error: the message, the offending line, and a caret under the
column (tabs in the line are kept so the caret lines up). -/
def renderSyntaxError (e : ParseError) (text : String) : String :=
  match (text.splitOn "\n")[e.line - 1]? with
  | some ln =>
    if e.line == 0 || ln.isEmpty then e.toString
    else
      let pad := (ln.toList.take (e.col - 1)).map fun c => if c == '\t' then '\t' else ' '
      s!"{e}\n{ln}\n{String.ofList pad}^"
  | none => e.toString

/-! ## Semantic checks -/

/-- Alias definitions `(kind, name, location)` in file order. -/
def aliasDefs (es : List Located) : List (String × String × Located) :=
  es.filterMap fun l =>
    match l.entry with
    | .userAlias n _ => some ("User_Alias", n, l)
    | .runasAlias n _ => some ("Runas_Alias", n, l)
    | .hostAlias n _ => some ("Host_Alias", n, l)
    | .cmndAlias n _ => some ("Cmnd_Alias", n, l)
    | _ => none

def refsByKind (r : Refs) : List (String × List String) :=
  [("User_Alias", r.user), ("Runas_Alias", r.runas), ("Host_Alias", r.host),
   ("Cmnd_Alias", r.cmnd)]

def isDefined (defs : List (String × String × Located)) (k n : String) : Bool :=
  defs.any fun (k', n', _) => k' == k && n' == n

def duplicateErrors (es : List Located) : List String :=
  go (aliasDefs es) []
where
  go : List (String × String × Located) → List (String × String × Located) → List String
  | [], _ => []
  | (k, n, l) :: ds, seen =>
    match seen.find? (fun (k', n', _) => k' == k && n' == n) with
    | some (_, _, l0) =>
      s!"{locPos l}: duplicate {k} \"{n}\", previously defined at {locPos l0}" :: go ds seen
    | none => go ds ((k, n, l) :: seen)

def undefinedErrors (es : List Located) : List String :=
  let defs := aliasDefs es
  es.flatMap fun l =>
    (refsByKind (entryRefs l.entry)).flatMap fun (k, ns) =>
      ns.eraseDups.filterMap fun n =>
        if isDefined defs k n then none
        else some s!"{locPos l}: {k} \"{n}\" referenced but not defined"

def cycleErrors (es : List Located) : List String :=
  let al := aliasesOf (es.map (·.entry))
  let defs := aliasDefs es
  let at_ (k n : String) : String :=
    ((defs.find? fun (k', n', _) => k' == k && n' == n).map fun (_, _, l) => locPos l).getD "visudo"
  let cycles : List (String × Option String) :=
    [("User_Alias", firstCycle al.user userAliasRefs),
     ("Runas_Alias", firstCycle al.runas userAliasRefs),
     ("Host_Alias", firstCycle al.host hostAliasRefs),
     ("Cmnd_Alias", firstCycle al.cmnd cmndAliasRefs)]
  cycles.filterMap fun (k, c) => c.map fun n => s!"{at_ k n}: cycle in {k} \"{n}\""

/-- Every `Defaults` option name sudo.ws 1.9.17p2 knows (from its sudoers plugin). -/
def sudoOptionNames : List String :=
  ["admin_flag", "always_query_group_plugin", "always_set_home", "apparmor_profile",
   "authenticate", "authfail_message", "badpass_message", "case_insensitive_group",
   "case_insensitive_user", "closefrom", "closefrom_override", "cmddenial_message",
   "command_timeout", "compress_io", "editor", "env_check", "env_delete", "env_editor",
   "env_file", "env_keep", "env_reset", "exec_background", "exempt_group", "fast_glob",
   "fdexec", "fqdn", "group_plugin", "ignore_audit_errors", "ignore_dot",
   "ignore_iolog_errors", "ignore_local_sudoers", "ignore_logfile_errors",
   "ignore_unknown_defaults", "insults", "intercept", "intercept_allow_setid",
   "intercept_authenticate", "intercept_type", "intercept_verify", "iolog_dir", "iolog_file",
   "iolog_flush", "iolog_group", "iolog_mode", "iolog_user", "lecture", "lecture_file",
   "lecture_status_dir", "limitprivs", "listpw", "log_allowed", "log_denied",
   "log_exit_status", "logfile", "log_format", "log_host", "log_input", "loglinelen",
   "log_output", "log_passwords", "log_server_cabundle", "log_server_keepalive",
   "log_server_peer_cert", "log_server_peer_key", "log_servers", "log_server_timeout",
   "log_server_verify", "log_stderr", "log_stdin", "log_stdout", "log_subcmds", "log_ttyin",
   "log_ttyout", "log_year", "long_otp_prompt", "mail_all_cmnds", "mail_always",
   "mail_badpass", "mailerflags", "mailerpath", "mailfrom", "mail_no_host", "mail_no_perms",
   "mail_no_user", "mailsub", "mailto", "match_group_by_gid", "maxseq", "netgroup_tuple",
   "noexec", "noninteractive_auth", "pam_acct_mgmt", "pam_askpass_service",
   "pam_login_service", "pam_rhost", "pam_ruser", "pam_service", "pam_session", "pam_setcred",
   "pam_silent", "passprompt", "passprompt_override", "passprompt_regex", "passwd_timeout",
   "passwd_tries", "path_info", "preserve_groups", "privs", "pwfeedback", "requiretty",
   "restricted_env_file", "rlimit_as", "rlimit_core", "rlimit_cpu", "rlimit_data",
   "rlimit_fsize", "rlimit_locks", "rlimit_memlock", "rlimit_nofile", "rlimit_nproc",
   "rlimit_rss", "rlimit_stack", "role", "rootpw", "root_sudo", "runas_allow_unknown_id",
   "runas_check_shell", "runas_default", "runaspw", "runchroot", "runcwd", "secure_path",
   "selinux", "setenv", "set_home", "set_logname", "set_utmp", "shell_noargs", "stay_setuid",
   "sudoedit_checkdir", "sudoedit_follow", "sudoers_locale", "syslog", "syslog_badpri",
   "syslog_goodpri", "syslog_maxlen", "syslog_pid", "targetpw", "timestampdir",
   "timestampowner", "timestamp_timeout", "timestamp_type", "tty_tickets", "type", "umask",
   "umask_override", "use_loginclass", "use_netgroups", "use_pty", "user_command_timeouts",
   "utmp_runas", "verifypw", "visiblepw"]

inductive SettingCheck where
  | ok
  | warn (msg : String)
  | err (msg : String)

/-- One `Defaults` setting, checked with the policy's own `applySetting`: its errors
(bad values, options lean-sudo refuses) are errors, and so are names sudo.ws does not
know either. Options sudo.ws knows that lean-sudo neither implements nor deliberately
ignores only warrant a warning (lean-sudo's `sudo` ignores them too). -/
def checkSetting (d : DefaultsSetting) : SettingCheck :=
  match applySetting {} d with
  | .error e => .err e
  | .ok (_, none) => .ok
  | .ok (_, some w) =>
    if ignoredOptions.contains d.name then .ok
    else if sudoOptionNames.contains d.name then
      .warn s!"defaults entry \"{d.name}\" is not supported by lean-sudo and is ignored"
    else .err w

def defaultsChecks (es : List Located) : List (Located × SettingCheck) :=
  es.flatMap fun l =>
    match l.entry with
    | .defaults _ ss => ss.map fun d => (l, checkSetting d)
    | _ => []

def defaultsErrors (es : List Located) : List String :=
  (defaultsChecks es).filterMap fun
    | (l, .err m) => some s!"{locPos l}: {m}"
    | _ => none

def defaultsWarnings (es : List Located) : List String :=
  (defaultsChecks es).filterMap fun
    | (l, .warn m) => some s!"Warning: {locPos l}: {m}"
    | _ => none

/-- All semantic errors; `Policy.validate` is the final, authoritative check. -/
def semanticErrors (es : List Located) : List String :=
  let errs := duplicateErrors es ++ undefinedErrors es ++ cycleErrors es ++ defaultsErrors es
  if !errs.isEmpty then errs
  else
    match validate (es.map (·.entry)) with
    | .error e => [s!"visudo: {e}"]
    | .ok () => []

/-- `Warning: file:line: unused <kind> "<name>"` for aliases nothing refers to. -/
def unusedWarnings (es : List Located) : List String :=
  let used := es.foldl (fun (acc : Refs) l => acc.append (entryRefs l.entry)) {}
  let usedK := refsByKind used
  (aliasDefs es).filterMap fun (k, n, l) =>
    let refs := ((usedK.find? (·.1 == k)).map (·.2)).getD []
    if refs.contains n then none else some s!"Warning: {locPos l}: unused {k} \"{n}\""

/-- Non-fatal findings: ignored `Defaults` options and unused aliases. -/
def semanticWarnings (es : List Located) : List String :=
  defaultsWarnings es ++ unusedWarnings es

/-! ## Edit mode helpers -/

/-- Editor values from the environment in sudo's order (`SUDO_EDITOR`, `VISUAL`,
`EDITOR`), skipping unset and blank ones. -/
def envEditorValues (env : List (String × String)) : List String :=
  ["SUDO_EDITOR", "VISUAL", "EDITOR"].filterMap fun k =>
    match env.lookup k with
    | some v => if (splitWords v).isEmpty then none else some v
    | none => none

/-- The `What now?` answer: first character of the line; `none` = ask again. -/
def whatNowChoice (line : String) : Option Char :=
  match line.toList with
  | c :: _ => if c == 'e' || c == 'x' || c == 'Q' then some c else none
  | [] => none

def whatNowHelp : String :=
  "Options are:\n" ++
  "  (e)dit sudoers file again\n" ++
  "  e(x)it without saving changes to sudoers file\n" ++
  "  (Q)uit and save changes to sudoers file (DANGER!)\n\n"

/-- Ensure a non-empty text ends in a newline (as sudo does for the temp copy). -/
def withFinalNewline (s : String) : String :=
  if s.isEmpty || s.endsWith "\n" then s else s ++ "\n"

end LeanSudo.Visudo
