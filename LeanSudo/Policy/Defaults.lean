import LeanSudo.Policy.Eval

/-!
# `Defaults` resolution

`resolveDefaults` folds the applicable `Defaults` entries over sudo's compiled-in
`Settings` (the field defaults of `Settings`). Application order is sudo's:

1. global `Defaults` (file order),
2. `Defaults@host` whose host list matches,
3. `Defaults:user` whose user list matches the invoking user,
4. `Defaults>runas` whose run-as list matches the target user (only if given),
5. `Defaults!cmnd` whose command list matches the command (only if given).

Within each phase entries apply in file order; later settings override earlier ones.

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
* `!secure_path` ⇒ unset; `!passprompt`/`!badpass_message` ⇒ empty string.

Fail-closed: options whose semantics restrict what may run (`noexec`, `intercept`,
SELinux/AppArmor, chroot/cwd, `env_file`, resource limits, command timeouts, ...) are
errors. Known options with no security effect that we do not implement (mail,
lecture, I/O logging, ...) and unknown options are ignored with a warning.
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

/-- `timestamp_timeout` value: minutes as `[-]digits[.digits]` ↦ seconds, `none` if negative. -/
def parseTimeout (v : String) : Option (Option Nat) :=
  let (neg, rest) : Bool × List Char :=
    match v.toList with
    | '-' :: r => (true, r)
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
    if neg && (iv != 0 || fv != 0) then some none else some (some secs)

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

/-! ## Option tables -/

def flagSetter : String → Option (Settings → Bool → Settings)
  | "env_reset" => some fun st b => { st with envReset := b }
  | "authenticate" => some fun st b => { st with authenticate := b }
  | "rootpw" => some fun st b => { st with rootpw := b }
  | "targetpw" => some fun st b => { st with targetpw := b }
  | "runaspw" => some fun st b => { st with runaspw := b }
  | "use_pty" => some fun st b => { st with usePty := b }
  | "always_set_home" => some fun st b => { st with alwaysSetHome := b }
  | "set_home" => some fun st b => { st with setHome := b }
  | "preserve_groups" => some fun st b => { st with preserveGroups := b }
  | "requiretty" => some fun st b => { st with requiretty := b }
  | "visiblepw" => some fun st b => { st with visiblepw := b }
  | "passprompt_override" => some fun st b => { st with passpromptOverride := b }
  | "pwfeedback" => some fun st b => { st with pwfeedback := b }
  | "umask_override" => some fun st b => { st with umaskOverride := b }
  | "setenv" => some fun st b => { st with setenv := b }
  | "shell_noargs" => some fun st b => { st with shellNoargs := b }
  | "env_editor" => some fun st b => { st with envEditor := b }
  | "log_allowed" => some fun st b => { st with logAllowed := b }
  | "log_denied" => some fun st b => { st with logDenied := b }
  | "pam_session" => some fun st b => { st with pamSession := b }
  | "pam_setcred" => some fun st b => { st with pamSetcred := b }
  | "tty_tickets" => some fun st b => { st with timestampType := if b then .tty else .global }
  | _ => none

def listField : String → Option ((Settings → List String) × (Settings → List String → Settings))
  | "env_keep" => some ((fun st => st.envKeep), fun st l => { st with envKeep := l })
  | "env_check" => some ((fun st => st.envCheck), fun st l => { st with envCheck := l })
  | "env_delete" => some ((fun st => st.envDelete), fun st l => { st with envDelete := l })
  | _ => none

/-- Known options we accept but do not implement (no effect on what may run). -/
def ignoredOptions : List String :=
  ["mail_badpass", "mail_always", "mail_no_user", "mail_no_host", "mail_no_perms", "mailto",
   "mailerpath", "mailerflags", "mailfrom", "mailsub", "lecture", "lecture_file", "insults",
   "fqdn", "passwd_timeout", "log_input", "log_output", "iolog_dir", "iolog_file", "logfile",
   "log_year", "log_host", "loglinelen", "syslog_goodpri", "syslog_badpri", "exempt_group",
   "match_group_by_gid", "ignore_dot", "path_info", "fdexec", "use_netgroups", "sudoers_locale"]

/-- Options whose (restricting) semantics are not implemented: refusing is fail-closed. -/
def unsupportedOptions : List String :=
  ["noexec", "noexec_file", "intercept", "intercept_allow_setid", "intercept_authenticate",
   "intercept_type", "intercept_verify", "log_subcmds", "selinux", "role", "type",
   "apparmor_profile", "privs", "limitprivs", "runchroot", "runcwd", "env_file",
   "restricted_env_file", "closefrom", "closefrom_override", "sudoers_uid", "root_sudo",
   "runas_check_shell", "command_timeout", "user_command_timeouts", "use_loginclass",
   "ignore_local_sudoers", "secure_path_override", "noninteractive_auth"]

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

/-- Apply one setting. Returns the new settings and an optional warning. -/
def applySetting (st : Settings) (d : DefaultsSetting) : Except String (Settings × Option String) :=
  let n := d.name
  if let some f := flagSetter n then
    match d.op with
    | .flag b => .ok (f st b, none)
    | .assign _ => .error s!"option \"{n}\" does not take a value"
    | op => badOp n op
  else if let some (get, set) := listField n then
    match d.op with
    | .flag false => .ok (set st [], none)
    | .flag true => noValue n
    | .assign v => .ok (set st (splitWords v).eraseDups, none)
    | .add v =>
      let cur := get st
      .ok (set st (cur ++ ((splitWords v).filter (fun w => !cur.contains w)).eraseDups), none)
    | .remove v =>
      let ws := splitWords v
      .ok (set st ((get st).filter (fun w => !ws.contains w)), none)
  else if ignoredOptions.contains n then
    .ok (st, some s!"ignoring unsupported defaults entry \"{n}\"")
  else if unsupportedOptions.contains n || (n.toList.take 7) == "rlimit_".toList then
    .error s!"defaults entry \"{n}\" is not supported"
  else
    match n, d.op with
    -- strings
    | "secure_path", .assign v => .ok ({ st with securePath := some v }, none)
    | "secure_path", .flag false => .ok ({ st with securePath := none }, none)
    | "passprompt", .assign v => .ok ({ st with passprompt := v }, none)
    | "passprompt", .flag false => .ok ({ st with passprompt := "" }, none)
    | "badpass_message", .assign v => .ok ({ st with badpassMessage := v }, none)
    | "badpass_message", .flag false => .ok ({ st with badpassMessage := "" }, none)
    | "runas_default", .assign v =>
      if v.toList.isEmpty then invalid n v else .ok ({ st with runasDefault := v }, none)
    | "editor", .assign v =>
      if v.toList.isEmpty then invalid n v else .ok ({ st with editor := v }, none)
    | "pam_service", .assign v =>
      if v.toList.isEmpty then invalid n v else .ok ({ st with pamService := v }, none)
    | "pam_login_service", .assign v =>
      if v.toList.isEmpty then invalid n v else .ok ({ st with pamLoginService := v }, none)
    | "syslog", .assign v =>
      if syslogFacilities.contains v then .ok ({ st with syslog := some v }, none) else invalid n v
    | "syslog", .flag false => .ok ({ st with syslog := none }, none)
    | "timestamp_type", .assign v =>
      match parseTimestampType v with
      | some t => .ok ({ st with timestampType := t }, none)
      | none => invalid n v
    -- integers
    | "passwd_tries", .assign v =>
      match parseDecimal v with
      | some k => .ok ({ st with passwdTries := k }, none)
      | none => invalid n v
    | "umask", .assign v =>
      match parseOctal v with
      | some k => if k ≤ 0o777 then .ok ({ st with umask := k }, none) else invalid n v
      | none => invalid n v
    | "umask", .flag false => .ok ({ st with umask := 0o777 }, none)
    | "timestamp_timeout", .assign v =>
      match parseTimeout v with
      | some t => .ok ({ st with timestampTimeout := t }, none)
      | none => invalid n v
    | "timestamp_timeout", .flag false => .ok ({ st with timestampTimeout := some 0 }, none)
    | "listpw", .assign v =>
      match parsePwPolicy v with
      | some p => .ok ({ st with listpw := p }, none)
      | none => invalid n v
    | "listpw", .flag false => .ok ({ st with listpw := .never }, none)
    | "verifypw", .assign v =>
      match parsePwPolicy v with
      | some p => .ok ({ st with verifypw := p }, none)
      | none => invalid n v
    | "verifypw", .flag false => .ok ({ st with verifypw := .never }, none)
    -- known non-flag options used with a wrong operator
    | "secure_path", op | "passprompt", op | "badpass_message", op | "runas_default", op
    | "editor", op | "pam_service", op | "pam_login_service", op | "syslog", op
    | "timestamp_type", op | "passwd_tries", op | "umask", op | "timestamp_timeout", op
    | "listpw", op | "verifypw", op =>
      match op with
      | .flag _ => noValue n
      | _ => badOp n op
    | _, _ => .ok (st, some s!"unknown defaults entry \"{n}\"")

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

/-- The settings that apply, in sudo's application order. -/
def applicableDefaults (s : Sudoers) (user : Principal) (host : String) (runas : Option Principal)
    (cmd : Option Command) (canon : String → String := id) : List DefaultsSetting :=
  let al := aliasesOf s
  let f := al.fuel
  let ds := defaultsOf s
  let g := ds.flatMap fun | (.global, ss) => ss | _ => []
  let h := ds.flatMap fun | (.host hs, ss) => if hostListOk al f host hs then ss else [] | _ => []
  let u := ds.flatMap fun | (.user us, ss) => if userListOk al f user us then ss else [] | _ => []
  let r := match runas with
    | some t => ds.flatMap fun
      | (.runas rs, ss) => if runasUserResult al f t rs == some true then ss else []
      | _ => []
    | none => []
  let c := match cmd with
    | some cm => ds.flatMap fun
      | (.cmnd cs, ss) => if cmndListResult al f canon cm cs == some true then ss else []
      | _ => []
    | none => []
  g ++ h ++ u ++ r ++ c

/-- Effective settings for a request, plus warnings (ignored/unknown options).
Errors are type errors and unsupported restricting options (fail-closed). -/
def resolveDefaults (s : Sudoers) (user : Principal) (host : String) (runas : Option Principal)
    (cmd : Option Command) (canon : String → String := id) : Except String (Settings × List String) :=
  applySettings {} (applicableDefaults s user host runas cmd canon)

end LeanSudo.Policy
