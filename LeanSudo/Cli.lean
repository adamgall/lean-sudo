import LeanSudo.Policy.Types
import LeanSudo.Sudoers.Parser

/-!
# Command-line parsing (`sudo` / `sudoedit`)

A pure re-implementation of sudo 1.9's `parse_args.c` on top of a GNU
`getopt_long`-compatible scanner (short-option bundling, `+` = stop at the first
operand, unique-prefix long options, `--`), including sudo's interleaving of
`VAR=value` operands with options.

Error convention: `parseArgs` returns `.error e` where `e` is exactly what sudo would
write to stderr *after* the leading `sudo: ` of its first line. Pure usage errors
(where sudo prints only the usage text) start with `usage:`. Use `formatError` to get
the complete stderr text.
-/

namespace LeanSudo.Cli

inductive Mode where
  | run | edit | list | validate | resetTimestamp | removeTimestamp | help | version
  deriving Repr, DecidableEq, Inhabited

inductive PreserveEnv where
  /-- no `-E` / `--preserve-env` -/
  | none
  /-- `-E` / `--preserve-env` without a list -/
  | all
  /-- `--preserve-env=a,b` (accumulated over all occurrences) -/
  | vars (vs : List String)
  deriving Repr, DecidableEq, Inhabited

structure Options where
  mode : Mode := .run
  /-- `-u user` (may be `#uid`) -/
  user : Option String := none
  /-- `-g group` (may be `#gid`) -/
  group : Option String := none
  /-- `-U user` (list mode only) -/
  otherUser : Option String := none
  /-- `-i` -/
  login : Bool := false
  /-- `-s` -/
  shell : Bool := false
  preserveEnv : PreserveEnv := .none
  /-- `-H` -/
  setHome : Bool := false
  /-- `-n` -/
  nonInteractive : Bool := false
  /-- `-S` -/
  stdin : Bool := false
  /-- `-p prompt` (may be empty) -/
  prompt : Option String := none
  /-- `-b` -/
  background : Bool := false
  /-- `-k` used as a flag together with a command, `-v`, `-l`, `-s`/`-i` or `-e` -/
  resetTimestamp : Bool := false
  /-- `-D dir` -/
  chdir : Option String := none
  /-- number of `-l` options -/
  listVerbose : Nat := 0
  /-- `-P` -/
  preserveGroups : Bool := false
  /-- `-B` (accepted; ring the bell when prompting) -/
  bell : Bool := false
  /-- `-C n`, `n ≥ 3` -/
  closeFrom : Option Nat := none
  /-- `-A` -/
  askpass : Bool := false
  /-- `-N`: do not update the timestamp -/
  noUpdate : Bool := false
  /-- `NAME=value` operands given before the command, in order -/
  envVars : List (String × String) := []
  /-- operands after option processing (the command and its arguments, or the files
  for `-e`/`sudoedit`, or the command to check for `-l`) -/
  command : List String := []
  host : Option String := none
  role : Option String := none
  type : Option String := none
  chroot : Option String := none
  timeout : Option Nat := none
  impliedShell : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-! ## Usage, help and version text -/

/-- `basename` of `argv[0]` (sudo's `getprogname()`). -/
def basename (path : String) : String :=
  String.ofList ((path.toList.reverse.takeWhile (· != '/')).reverse)

private def sudoUsage : List (List String) :=
  [ ["-h | -K | -k | -V"],
    ["-v [-ABkNnS] [-g group] [-h host] [-p prompt] [-u user]"],
    ["-l [-ABkNnS] [-g group] [-h host] [-p prompt] [-U user]",
     "[-u user] [command [arg ...]]"],
    ["[-ABbEHkNnPS] [-r role] [-t type] [-C num] [-D directory]",
     "[-g group] [-h host] [-p prompt] [-R directory] [-T timeout]",
     "[-u user] [VAR=value] [-i | -s] [command [arg ...]]"],
    ["-e [-ABkNnS] [-r role] [-t type] [-C num] [-D directory]",
     "[-g group] [-h host] [-p prompt] [-R directory] [-T timeout]",
     "[-u user] file ..."] ]

private def sudoeditUsage : List (List String) :=
  [ ["-h | -V"],
    ["[-ABkNnS] [-r role] [-t type] [-C num] [-D directory]",
     "[-g group] [-h host] [-p prompt] [-R directory] [-T timeout]",
     "[-u user] file ..."] ]

/-- sudo's `display_usage` for the given program name (`sudo` or `sudoedit`). -/
def usageFor (progname : String) : String :=
  let vecs := if progname == "sudoedit" then sudoeditUsage else sudoUsage
  let ind := String.ofList (List.replicate (progname.length + 8) ' ')
  String.join <| vecs.map fun
    | [] => ""
    | first :: rest =>
      s!"usage: {progname} {first}\n" ++ String.join (rest.map fun l => ind ++ l ++ "\n")

def usageText : String := usageFor "sudo"

/-- Word wrapping as done by sudo's `sudo_lbuf_println` (80 columns, continuation
lines indented by `indent`). `fuel` bounds the number of output lines. -/
private def wrapAux (indent : Nat) : Nat → Nat → List Char → List Char
  | 0, _, _ => []
  | fuel + 1, avail, cs =>
    if cs.length ≤ avail then cs ++ ['\n'] else
      -- last space strictly before position `avail`, else first space after it
      let firstPart := cs.take avail
      let brk : Option Nat :=
        match (firstPart.reverse.findIdx? (· == ' ')) with
        | some j => some (avail - 1 - j)
        | none => ((cs.drop avail).findIdx? (· == ' ')).map (· + avail)
      match brk with
      | none => cs ++ ['\n']
      | some n =>
        let rest := (cs.drop n).dropWhile (fun c => c == ' ' || c == '\t')
        if rest.isEmpty then cs.take n ++ ['\n'] else
        cs.take n ++ ['\n'] ++ List.replicate indent ' ' ++ wrapAux indent fuel (80 - indent) rest

private def wrapLine (s : String) : String :=
  String.ofList (wrapAux 32 (s.length + 1) 80 s.toList)

private def helpEntries (sudoedit : Bool) : List String :=
  let both (l : String) := [l]
  let sudoOnly (l : String) := if sudoedit then [] else [l]
  both     "  -A, --askpass                 use a helper program for password prompting" ++
  sudoOnly "  -b, --background              run command in the background" ++
  both     "  -B, --bell                    ring bell when prompting" ++
  both     "  -C, --close-from=num          close all file descriptors >= num" ++
  both     "  -D, --chdir=directory         change the working directory before running command" ++
  sudoOnly "  -E, --preserve-env            preserve user environment when running command" ++
  sudoOnly "      --preserve-env=list       preserve specific environment variables" ++
  sudoOnly "  -e, --edit                    edit files instead of running a command" ++
  both     "  -g, --group=group             run command as the specified group name or ID" ++
  sudoOnly "  -H, --set-home                set HOME variable to target user's home dir" ++
  both     "  -h, --help                    display help message and exit" ++
  both     "  -h, --host=host               run command on host (if supported by plugin)" ++
  sudoOnly "  -i, --login                   run login shell as the target user; a command may also be specified" ++
  sudoOnly "  -K, --remove-timestamp        remove timestamp file completely" ++
  both     "  -k, --reset-timestamp         invalidate timestamp file" ++
  sudoOnly "  -l, --list                    list user's privileges or check a specific command; use twice for longer format" ++
  both     "  -n, --non-interactive         non-interactive mode, no prompts are used" ++
  sudoOnly "  -P, --preserve-groups         preserve group vector instead of setting to target's" ++
  both     "  -p, --prompt=prompt           use the specified password prompt" ++
  both     "  -R, --chroot=directory        change the root directory before running command" ++
  both     "  -r, --role=role               create SELinux security context with specified role" ++
  both     "  -S, --stdin                   read password from standard input" ++
  sudoOnly "  -s, --shell                   run shell as the target user; a command may also be specified" ++
  both     "  -t, --type=type               create SELinux security context with specified type" ++
  both     "  -T, --command-timeout=timeout terminate command after the specified time limit" ++
  sudoOnly "  -U, --other-user=user         in list mode, display privileges for user" ++
  both     "  -u, --user=user               run command (or edit file) as specified user name or ID" ++
  both     "  -V, --version                 display version information and exit" ++
  sudoOnly "  -v, --validate                update user's timestamp without running a command" ++
  both     "  --                            stop processing command line arguments"

/-- Output of `sudo -h` (to stdout, exit status 0). -/
def helpFor (progname : String) : String :=
  let sudoedit := progname == "sudoedit"
  let header := if sudoedit then s!"{progname} - edit files as another user\n\n"
    else s!"{progname} - execute a command as another user\n\n"
  header ++ usageFor progname ++ "\nOptions:\n" ++
    String.join ((helpEntries sudoedit).map wrapLine)

def helpText : String := helpFor "sudo"

/-- Output of `sudo -V`. -/
def versionText : String :=
  "Sudo version 1.9.17p2\n" ++
  "Sudoers policy plugin version 1.9.17p2\n" ++
  "Sudoers file grammar version 50\n" ++
  "Sudoers I/O plugin version 1.9.17p2\n" ++
  "Sudoers audit plugin version 1.9.17p2\n"

/-- Ubuntu's configured sudo.ws feature set, with the native Debian multiarch tuple. -/
def configureOptions (architecture : String) : String :=
  let triplet := architecture ++ "-linux-gnu"
  "--build=" ++ triplet ++ " --prefix=/usr --includedir=${prefix}/include --mandir=${prefix}/share/man --infodir=${prefix}/share/info --sysconfdir=/etc --localstatedir=/var --disable-option-checking --disable-silent-rules --libdir=${prefix}/lib/" ++ triplet ++
  " --runstatedir=/run --disable-maintainer-mode --disable-dependency-tracking --with-all-insults --with-pam --with-pam-login --with-fqdn --with-logging=syslog --with-logfac=authpriv --with-devel --with-env-editor --with-editor=/usr/bin/editor --with-timeout=15 --with-password-timeout=0 --with-passprompt=[sudo] password for %p:  --with-tty-tickets --without-lecture --disable-root-mailer --with-sendmail=/usr/sbin/sendmail --with-rundir=/run/sudo --with-sssd --with-sssd-lib=/usr/lib/" ++ triplet ++
  " --enable-zlib=system --enable-admin-flag --with-apparmor --with-selinux --with-linux-audit --enable-tmpfiles.d=/usr/lib/tmpfiles.d MVPROG=/bin/mv --with-exampledir=/usr/share/doc/sudo/examples"

private def pwPolicyText : PwPolicy → String
  | .all => "all" | .always => "always" | .any => "any" | .never => "never"

private def timestampTypeText : TimestampType → String
  | .tty => "tty" | .ppid => "ppid" | .global => "global" | .kernel => "kernel"

private def minutesText (seconds : Option Nat) : String :=
  match seconds with
  | none => "-1.0"
  | some n => s!"{n / 60}.{(n % 60) * 10 / 60}"

private def octalText (n : Nat) : String :=
  String.ofList [Char.ofNat (48 + n / 64 % 8), Char.ofNat (48 + n / 8 % 8), Char.ofNat (48 + n % 8)]

/-- Root's verbose plugin report is computed from effective Defaults, not the
invoker's environment or an external sudo binary. Interface strings are OS facts. -/
def versionFor (root : Bool) (s : Settings := {}) (interfaces : List String := [])
    (architecture : String := "aarch64") : String :=
  if !root then versionText else
  let line (label value : String) := label ++ ": " ++ value ++ "\n"
  let flag (enabled : Bool) (text : String) := if enabled then text ++ "\n" else ""
  let opt (label : String) (value : Option String) := value.map (line label) |>.getD ""
  let entries (label : String) (values : List String) :=
    if values.isEmpty then "" else label ++ ":\n" ++ String.join (values.reverse.map ("\t" ++ · ++ "\n"))
  "Sudo version 1.9.17p2\nConfigure options: " ++ configureOptions architecture ++ "\n" ++
  "Sudoers policy plugin version 1.9.17p2\nSudoers file grammar version 50\n\n" ++
  "Sudoers path: /etc/sudoers\nAuthentication methods: 'pam'\n" ++
  opt "Syslog facility if syslog is being used for logging" s.syslog ++
  opt "Syslog priority to use when user authenticates successfully" s.syslogGoodpri ++
  opt "Syslog priority to use when user authenticates unsuccessfully" s.syslogBadpri ++
  flag s.ignoreDot "Ignore '.' in $PATH" ++
  flag s.mailAlways "Send mail if the user runs sudo" ++
  flag s.mailBadpass "Send mail if user authentication fails" ++
  flag s.mailNoUser "Send mail if the user is not in sudoers" ++
  flag s.mailNoHost "Send mail if the user is not in sudoers for this host" ++
  flag s.mailNoPerms "Send mail if the user is not allowed to run a command" ++
  -- Upstream's tuple description has no substitution: printed even for "never".
  "Lecture user the first time they run sudo\n" ++
  flag s.authenticate "Require users to authenticate by default" ++
  flag s.rootSudo "Root may run sudo" ++
  flag s.pathInfo "Allow some information gathering to give useful error messages" ++
  flag s.fqdn "Require fully-qualified hostnames in the sudoers file" ++
  flag s.insults "Insult the user when they enter an incorrect password" ++
  flag s.requiretty "Only allow the user to run sudo if they have a tty" ++
  flag s.envEditor "Visudo will honor the EDITOR environment variable" ++
  flag s.setLogname "Set the LOGNAME and USER environment variables" ++
  flag s.rootpw "Prompt for root's password, not the user's" ++
  flag s.runaspw "Prompt for the runas_default user's password, not the user's" ++
  flag s.targetpw "Prompt for the target user's password, not the user's" ++
  line "Length at which to wrap log file lines (0 for no wrap)" (toString s.loglinelen) ++
  line "Authentication timestamp timeout" (minutesText s.timestampTimeout ++ " minutes") ++
  line "Password prompt timeout" (minutesText s.passwdTimeout ++ " minutes") ++
  line "Number of tries to enter a password" (toString s.passwdTries) ++
  line "Umask to use or 0777 to use user's" (octalText s.umask) ++
  opt "Path to mail program" s.mailerpath ++ opt "Flags for mail program" s.mailerflags ++
  opt "Address to send mail to" s.mailto ++ opt "Address to send mail from" s.mailfrom ++
  line "Subject line for mail messages" s.mailsub ++
  line "Incorrect password message" s.badpassMessage ++
  line "Path to lecture status dir" s.lectureStatusDir ++
  line "Path to authentication timestamp dir" s.timestampdir ++
  line "Default password prompt" s.passprompt ++
  line "Default user to run commands as" s.runasDefault ++
  opt "Value to override user's $PATH with" s.securePath ++
  line "Path to the editor for use by visudo" s.editor ++
  line "When to require a password for 'list' pseudocommand" (pwPolicyText s.listpw) ++
  line "When to require a password for 'verify' pseudocommand" (pwPolicyText s.verifypw) ++
  s!"File descriptors >= {s.closefrom} will be closed before executing a command\n" ++
  flag s.envReset "Reset the environment to a default set of variables" ++
  entries "Environment variables to check for safety" s.envCheck ++
  entries "Environment variables to remove" s.envDelete ++
  entries "Environment variables to preserve" s.envKeep ++
  line "Locale to use while parsing sudoers" s.sudoersLocale ++
  flag s.compressIo "Compress I/O logs using zlib" ++
  flag s.usePty "Always run commands in a pseudo-tty" ++
  line "Directory in which to store input/output logs" s.iologDir ++
  line "File in which to store the input/output log" s.iologFile ++
  flag s.setUtmp "Add an entry to the utmp/utmpx file when allocating a pty" ++
  line "PAM service name to use" s.pamService ++
  line "PAM service name to use for login shells" s.pamLoginService ++
  flag s.pamSetcred "Attempt to establish PAM credentials for the target user" ++
  flag s.pamSession "Create a new PAM session for the command to run in" ++
  flag s.pamAcctMgmt "Perform PAM account validation management" ++
  flag s.pamSilent "Do not allow PAM authentication modules to generate output" ++
  flag s.useNetgroups "Enable sudoers netgroup support" ++
  flag s.sudoeditCheckdir "Check parent directories for writability when editing files with sudoedit" ++
  flag s.ignoreAuditErrors "Allow commands to be run even if sudo cannot write to the audit log" ++
  flag s.ignoreLogfileErrors "Allow commands to be run even if sudo cannot write to the log file" ++
  line "Log entries larger than this value will be split into multiple syslog messages" (toString s.syslogMaxlen) ++
  line "File mode to use for the I/O log files" ("0" ++ octalText s.iologMode) ++
  line "Execute commands by file descriptor instead of by path" s.fdexec ++
  line "Type of authentication timestamp record" (timestampTypeText s.timestampType) ++
  flag s.caseInsensitiveUser "Ignore case when matching user names" ++
  flag s.caseInsensitiveGroup "Ignore case when matching group names" ++
  flag s.logAllowed "Log when a command is allowed by sudoers" ++
  flag s.logDenied "Log when a command is denied by sudoers" ++
  line "Sudo log server timeout in seconds" (toString s.logServerTimeout) ++
  flag s.logServerKeepalive "Enable SO_KEEPALIVE socket option on the socket connected to the logserver" ++
  flag s.logServerVerify "Verify that the log server's certificate is valid" ++
  flag s.pamRuser "Set the pam remote user to the user running sudo" ++
  line "The format of logs to produce" s.logFormat ++
  flag s.selinux "Enable SELinux RBAC support" ++
  opt "Path to the file that is created the first time sudo is run" s.adminFlag ++
  flag s.interceptAllowSetid "Allow an intercepted command to run set setuid or setgid programs" ++
  opt "The largest size core dump file that may be created (in bytes)" s.rlimitCore ++
  flag s.logPasswords "Store plaintext passwords in I/O log input" ++
  (if s.passpromptRegex.isEmpty then "" else
    "List of regular expressions to use when matching a password prompt\n" ++
      String.join (s.passpromptRegex.reverse.map ("\t" ++ · ++ "\n"))) ++
  line "The mechanism used by the intercept and log_subcmds options" s.interceptType ++
  flag s.interceptVerify "Attempt to verify the command and arguments after execution" ++
  (if interfaces.isEmpty then "" else
    "\nLocal IP address and netmask pairs:\n" ++ String.join (interfaces.map ("\t" ++ · ++ "\n"))) ++
  "\nSudoers I/O plugin version 1.9.17p2\nSudoers audit plugin version 1.9.17p2\n"

/-- Complete stderr text for a `parseArgs` error. -/
def formatError (progname : String) (e : String) : String :=
  let body := if "usage:".toList.isPrefixOf e.toList then e else progname ++ ": " ++ e
  if body.toList.getLast? == some '\n' then body else body ++ "\n"

/-! ## Option scanner -/

/-- Argument requirement of an option. -/
inductive ArgSpec where
  | no | req | opt
  deriving Repr, DecidableEq, Inhabited

/-- sudo's short option string `+Aa:BbC:c:D:Eeg:Hh::iKklNnPp:R:r:SsT:t:U:u:Vv`
(and the restricted `sudoedit` one). `none` = not an option. -/
def shortSpec (sudoedit : Bool) (c : Char) : Option ArgSpec :=
  match c with
  | 'A' | 'B' | 'K' | 'k' | 'N' | 'n' | 'S' | 'V' => some .no
  | 'a' | 'C' | 'c' | 'D' | 'g' | 'p' | 'R' | 'r' | 'T' | 't' | 'u' => some .req
  | 'h' => some .opt
  | 'b' | 'E' | 'e' | 'H' | 'i' | 'l' | 'P' | 's' | 'v' => if sudoedit then none else some .no
  | 'U' => if sudoedit then none else some .req
  | _ => none

structure LongOpt where
  name : String
  spec : ArgSpec
  /-- equivalent short option; `#` stands for sudo's `OPT_HOSTNAME` (`--host`) -/
  key : Char
  /-- not available as `sudoedit` -/
  sudoOnly : Bool

/-- sudo's `sudo_long_opts` table, in order. -/
def longOpts : List LongOpt :=
  [ ⟨"background", .no, 'b', true⟩, ⟨"preserve-env", .opt, 'E', true⟩,
    ⟨"edit", .no, 'e', true⟩, ⟨"set-home", .no, 'H', true⟩, ⟨"login", .no, 'i', true⟩,
    ⟨"remove-timestamp", .no, 'K', true⟩, ⟨"list", .no, 'l', true⟩,
    ⟨"preserve-groups", .no, 'P', true⟩, ⟨"shell", .no, 's', true⟩,
    ⟨"other-user", .req, 'U', true⟩, ⟨"validate", .no, 'v', true⟩,
    ⟨"askpass", .no, 'A', false⟩, ⟨"auth-type", .req, 'a', false⟩, ⟨"bell", .no, 'B', false⟩,
    ⟨"close-from", .req, 'C', false⟩, ⟨"login-class", .req, 'c', false⟩,
    ⟨"chdir", .req, 'D', false⟩, ⟨"group", .req, 'g', false⟩, ⟨"help", .no, 'h', false⟩,
    ⟨"host", .req, '#', false⟩, ⟨"reset-timestamp", .no, 'k', false⟩,
    ⟨"no-update", .no, 'N', false⟩, ⟨"non-interactive", .no, 'n', false⟩,
    ⟨"prompt", .req, 'p', false⟩, ⟨"chroot", .req, 'R', false⟩, ⟨"role", .req, 'r', false⟩,
    ⟨"stdin", .no, 'S', false⟩, ⟨"command-timeout", .req, 'T', false⟩,
    ⟨"type", .req, 't', false⟩, ⟨"user", .req, 'u', false⟩, ⟨"version", .no, 'V', false⟩ ]

/-- sudo's `is_envar`: does not start with `/` or `=` and contains `=`. -/
def isEnvarL : List Char → Bool
  | [] => false
  | '/' :: _ => false
  | '=' :: _ => false
  | l => l.contains '='

def isEnvar (s : String) : Bool := isEnvarL s.toList

/-- Parser state (the settings sudo's `parse_args` accumulates). -/
structure Raw where
  progname : String
  sudoedit : Bool
  mode : Option Mode := none
  lcount : Nat := 0
  /-- `-k` or `-K` seen (`ARG_IGNORE_TICKET`) -/
  ignoreTicket : Bool := false
  noUpdate : Bool := false
  background : Bool := false
  preserveAll : Bool := false
  preserveVars : List String := []
  resetHome : Bool := false
  login : Bool := false
  nonInteractive : Bool := false
  preserveGroups : Bool := false
  shell : Bool := false
  envVars : List (String × String) := []
  user : Option String := none
  group : Option String := none
  otherUser : Option String := none
  prompt : Option String := none
  chdir : Option String := none
  closeFrom : Option Nat := none
  askpass : Bool := false
  stdin : Bool := false
  bell : Bool := false
  host : Option String := none
  role : Option String := none
  type : Option String := none
  chroot : Option String := none
  timeout : Option Nat := none

def Raw.init (progname : String) : Raw :=
  let se := progname == "sudoedit"
  { progname, sudoedit := se, mode := if se then some .edit else none }

/-- `msg` followed by the usage text (sudo's `sudo_warnx(msg); usage()`). -/
def usageErr (r : Raw) (msg : String) : String := msg ++ "\n" ++ usageFor r.progname

def exclMsg : String :=
  "Only one of the -e, -h, -i, -K, -l, -s, -v or -V options may be specified"

def exclTicketMsg : String := "Only one of the -K, -k or -N options may be specified"

/-- Split `NAME=value` at the first `=`. -/
def splitEnvar (s : String) : String × String :=
  let l := s.toList
  (String.ofList (l.takeWhile (· != '=')), String.ofList ((l.dropWhile (· != '=')).drop 1))

/-- `strtok(list, ",")`: comma separated, empty tokens skipped. -/
def splitCommas (s : String) : List String :=
  (s.splitOn ",").filter (fun t => !t.isEmpty)

/-- `sudo_strtonum(s, 3, INT_MAX)` restricted to plain decimal digits. -/
def parseCloseFrom (s : String) : Option Nat :=
  if !s.isEmpty && s.toList.all Char.isDigit then
    let n := s.toNat!
    if 3 ≤ n && n ≤ 2147483647 then some n else none
  else none

/-- Apply one recognised option (`key` as in sudo's `switch (ch)`). -/
def applyOpt (r : Raw) (key : Char) (arg : Option String) : Except String Raw :=
  let usage : Except String Raw := .error (usageFor r.progname)
  let excl : Except String Raw := .error (usageErr r exclMsg)
  let exclTicket : Except String Raw := .error (usageErr r exclTicketMsg)
  let nonEmpty (k : String → Except String Raw) : Except String Raw :=
    match arg with
    | some a => if a.isEmpty then usage else k a
    | none => usage
  match key with
  | 'A' => .ok { r with askpass := true }
  | 'b' => .ok { r with background := true }
  | 'B' => .ok { r with bell := true }
  | 'C' =>
    match arg.bind parseCloseFrom with
    | none => .error (usageErr r "the argument to -C must be a number greater than or equal to 3")
    | some n => if r.closeFrom.isSome then usage else .ok { r with closeFrom := some n }
  | 'D' => nonEmpty fun a => if r.chdir.isSome then usage else .ok { r with chdir := some a }
  | 'E' =>
    match arg with
    | none => .ok { r with preserveAll := true }
    | some l =>
      let names := splitCommas l
      match names.find? (fun n => n.toList.contains '=') with
      | some bad => .error (usageErr r s!"invalid environment variable name: {bad}")
      | none => .ok { r with preserveVars := r.preserveVars ++ names }
  | 'e' =>
    if r.mode.isSome && r.mode != some .edit then excl else .ok { r with mode := some .edit }
  | 'g' => nonEmpty fun a => if r.group.isSome then usage else .ok { r with group := some a }
  | 'H' => .ok { r with resetHome := true }
  | 'h' =>
    match arg with
    | some a => if r.host.isSome then usage else .ok { r with host := some a }
    | none =>
      if r.mode.isSome && r.mode != some .help && !r.sudoedit then excl
      else .ok { r with mode := some .help }
  | '#' => nonEmpty fun a => if r.host.isSome then usage else .ok { r with host := some a }
  | 'i' => .ok { r with login := true }
  | 'K' =>
    if r.mode.isSome && r.mode != some .removeTimestamp then excl
    else if r.noUpdate then exclTicket
    else .ok { r with mode := some .removeTimestamp, ignoreTicket := true }
  | 'k' => if r.noUpdate then exclTicket else .ok { r with ignoreTicket := true }
  | 'l' =>
    if r.mode.isSome && r.mode != some .list then excl
    else .ok { r with mode := some .list, lcount := r.lcount + 1 }
  | 'N' => if r.ignoreTicket then exclTicket else .ok { r with noUpdate := true }
  | 'n' => .ok { r with nonInteractive := true }
  | 'P' => .ok { r with preserveGroups := true }
  | 'p' =>
    match arg with
    | some a => if r.prompt.isSome then usage else .ok { r with prompt := some a }
    | none => usage
  | 'R' => nonEmpty fun a => if r.chroot.isSome then usage else .ok { r with chroot := some a }
  | 'r' => nonEmpty fun a => if r.role.isSome then usage else .ok { r with role := some a }
  | 't' => nonEmpty fun a => if r.type.isSome then usage else .ok { r with type := some a }
  | 'T' => nonEmpty fun a =>
    match Sudoers.Parser.parseTimeout a with
    | some n => if r.timeout.isSome then usage else .ok { r with timeout := some n }
    | none => .error s!"{a}: invalid timeout value"
  | 'S' => .ok { r with stdin := true }
  | 's' => .ok { r with shell := true }
  | 'U' => nonEmpty fun a => if r.otherUser.isSome then usage else .ok { r with otherUser := some a }
  | 'u' => nonEmpty fun a => if r.user.isSome then usage else .ok { r with user := some a }
  | 'v' =>
    if r.mode.isSome && r.mode != some .validate then excl else .ok { r with mode := some .validate }
  | 'V' =>
    if r.mode.isSome && r.mode != some .version && !r.sudoedit then excl
    else .ok { r with mode := some .version }
  -- BSD authentication and login classes are not compiled in.
  | _ => usage

/-- Process a bundle of short options (the characters after the leading `-`).
`next` is the following command-line argument, `alone` whether the whole argument
was exactly `-h`. Returns the new state and whether `next` was consumed. -/
def shortCluster (r : Raw) (next : Option String) (alone : Bool) :
    List Char → Except String (Raw × Bool)
  | [] => .ok (r, false)
  | c :: cs =>
    match shortSpec r.sudoedit c with
    | none => .error (usageErr r s!"invalid option -- '{c}'")
    | some .no => do
      let r' ← applyOpt r c none
      shortCluster r' next alone cs
    | some .req =>
      if cs.isEmpty then
        match next with
        | some a => do return (← applyOpt r c (some a), true)
        | none => .error (usageErr r s!"option requires an argument -- '{c}'")
      else do return (← applyOpt r c (some (String.ofList cs)), false)
    | some .opt =>
      -- only `-h` has an optional argument; it must be attached (`-hhost`), except
      -- that a lone `-h` followed by a non-option, non-`VAR=value` word takes it
      if cs.isEmpty then
        match next with
        | some a =>
          if alone && a.toList.head? != some '-' && !isEnvar a then
            do return (← applyOpt r c (some a), true)
          else do return (← applyOpt r c none, false)
        | none => do return (← applyOpt r c none, false)
      else do return (← applyOpt r c (some (String.ofList cs)), false)

/-- Process `--name[=value]` (`body` = the characters after `--`). -/
def longOpt (r : Raw) (next : Option String) (body : List Char) : Except String (Raw × Bool) :=
  let name := body.takeWhile (· != '=')
  let hasArg := body.contains '='
  let value := String.ofList ((body.dropWhile (· != '=')).drop 1)
  let visible := longOpts.filter (fun o => !(r.sudoedit && o.sudoOnly))
  let cands :=
    match visible.find? (fun o => o.name.toList == name) with
    | some o => [o]
    | none => visible.filter (fun o => name.isPrefixOf o.name.toList)
  let full := "--" ++ String.ofList body
  match cands with
  | [] => .error (usageErr r s!"unrecognized option '{full}'")
  | [o] =>
    match o.spec with
    | .no =>
      if hasArg then .error (usageErr r s!"option '--{o.name}' doesn't allow an argument")
      else do return (← applyOpt r o.key none, false)
    | .opt => do return (← applyOpt r o.key (if hasArg then some value else none), false)
    | .req =>
      if hasArg then do return (← applyOpt r o.key (some value), false)
      else match next with
        | some a => do return (← applyOpt r o.key (some a), true)
        | none => .error (usageErr r s!"option '--{o.name}' requires an argument")
  | os =>
    .error (usageErr r (s!"option '{full}' is ambiguous; possibilities:" ++
      String.join (os.map fun o => s!" '--{o.name}'")))

/-- getopt_long loop with sudo's `VAR=value` interleaving. Returns the final state and
the operands. -/
def scan : List String → Raw → Except String (Raw × List String)
  | [], r => .ok (r, [])
  | a :: rest, r =>
    match a.toList with
    | ['-', '-'] => .ok (r, rest)
    | '-' :: '-' :: body =>
      match longOpt r rest.head? body with
      | .error e => .error e
      | .ok (r', true) => scan rest.tail r'
      | .ok (r', false) => scan rest r'
    | '-' :: c :: cs =>
      match shortCluster r rest.head? (a.toList == ['-', 'h']) (c :: cs) with
      | .error e => .error e
      | .ok (r', true) => scan rest.tail r'
      | .ok (r', false) => scan rest r'
    | l =>
      if isEnvarL l then scan rest { r with envVars := r.envVars ++ [splitEnvar a] }
      else .ok (r, a :: rest)
termination_by args => args.length
decreasing_by all_goals (simp only [List.length_tail, List.length_cons]; omega)

/-! ## Validation (the tail of sudo's `parse_args`) -/

/-- The mode sudo settles on (`-k` alone becomes `resetTimestamp`). -/
def Raw.effMode (r : Raw) (ops : List String) : Mode :=
  match r.mode with
  | some m => m
  | none => if r.ignoreTicket && ops.isEmpty && !(r.shell || r.login) then .resetTimestamp else .run

/-- sudo's `(flags & valid_flags) != flags` check. Flags: `-b -E -H -i -n -P -s`
and the second `-l`. -/
def Raw.flagsValid (r : Raw) (m : Mode) : Bool :=
  match m with
  | .run => true
  | .edit | .validate => !(r.background || r.preserveAll || r.resetHome || r.login ||
      r.preserveGroups || r.shell)
  | .list => !(r.background || r.preserveAll || r.resetHome || r.login ||
      r.preserveGroups || r.shell)
  | _ => !(r.background || r.preserveAll || r.resetHome || r.login || r.nonInteractive ||
      r.preserveGroups || r.shell || r.lcount > 1)

/-- sudo's post-scan checks, in order: (violated?, error text). -/
def Raw.rules (r : Raw) (ops : List String) : List (Bool × String) :=
  let m := r.effMode ops
  let usage := usageFor r.progname
  let editEnv := !(r.envVars.isEmpty && r.preserveVars.isEmpty)
  [ (r.login && r.shell, usageErr r "you may not specify both the -i and -s options"),
    (r.login && r.preserveAll, usageErr r "you may not specify both the -i and -E options"),
    (!r.flagsValid m, usage),
    (m == .edit && editEnv, usageErr r "you may not specify environment variables in edit mode"),
    ((r.user.isSome || r.group.isSome) &&
      !(m == .edit || m == .run || m == .validate || (m == .list && !ops.isEmpty)), usage),
    (r.otherUser.isSome && m != .list,
      usageErr r "the -U option may only be used with the -l option"),
    (r.stdin && r.askpass, usageErr r "the -A and -S options may not be used together"),
    ((ops.isEmpty && m == .edit) || (!ops.isEmpty && !(m == .run || m == .edit || m == .list)),
      usage) ]

/-- First validation error, if any. -/
def Raw.check (r : Raw) (ops : List String) : Option String :=
  ((r.rules ops).find? (·.1)).map (·.2)

def Raw.build (r : Raw) (ops : List String) : Options :=
  let m := r.effMode ops
  { mode := m
    user := r.user
    group := r.group
    otherUser := r.otherUser
    login := r.login
    shell := r.shell || (m == .run && ops.isEmpty && !r.login)
    preserveEnv := if r.preserveAll then .all
      else if r.preserveVars.isEmpty then .none else .vars r.preserveVars
    setHome := r.resetHome
    nonInteractive := r.nonInteractive
    stdin := r.stdin
    prompt := r.prompt
    background := r.background
    resetTimestamp := r.ignoreTicket && m != .resetTimestamp && m != .removeTimestamp
    chdir := r.chdir
    listVerbose := r.lcount
    preserveGroups := r.preserveGroups
    bell := r.bell
    closeFrom := r.closeFrom
    askpass := r.askpass
    noUpdate := r.noUpdate
    envVars := r.envVars
    command := ops
    host := r.host, role := r.role, type := r.type, chroot := r.chroot, timeout := r.timeout
    impliedShell := m == .run && ops.isEmpty && !(r.shell || r.login) }

def finish (r : Raw) (ops : List String) : Except String Options :=
  match r.check ops with
  | some e => .error e
  | none => .ok (r.build ops)

/-- Parse sudo's command line. `progname` is the basename of `argv[0]`, `args` are
`argv[1..]`. -/
def parseArgs (progname : String) (args : List String) : Except String Options :=
  match scan args (Raw.init progname) with
  | .error e => .error e
  | .ok (r, ops) => finish r ops

/-! ## Shell mode (`-s` / `-i`) -/

/-- Characters sudo leaves unescaped when building `shell -c "..."`. -/
def shellSafe (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '-' || c == '$'

/-- Backslash-escape every character that is not `shellSafe`. -/
def escapeChars : List Char → List Char
  | [] => []
  | c :: cs => if shellSafe c then c :: escapeChars cs else '\\' :: c :: escapeChars cs

/-- Escape every word and join them with single spaces. -/
def escapeJoin : List String → List Char
  | [] => []
  | [w] => escapeChars w.toList
  | w :: ws => escapeChars w.toList ++ ' ' :: escapeJoin ws

/-- The `-c` argument sudo builds from the command words. -/
def shellEscape (command : List String) : String := String.ofList (escapeJoin command)

structure ShellCmd where
  /-- path to execute -/
  path : String
  /-- full argv including argv[0] -/
  argv : List String
  deriving Repr, DecidableEq, Inhabited

/-- The command executed for `-s` (`login = false`) or `-i` (`login = true`).
`shell` is the shell path (`-s`: the invoking user's `$SHELL` or passwd shell;
`-i`: the target user's passwd shell). -/
def shellCommand (shell : String) (login : Bool) (command : List String) : ShellCmd :=
  let argv0 := if login then "-" ++ basename shell else shell
  { path := shell
    argv := if command.isEmpty then [argv0] else
      [argv0] ++ (if login && basename shell == "bash" then ["--login"] else []) ++
        ["-c", shellEscape command] }

/-- Empty environment and passwd shells fall back exactly as sudo's get_user_info. -/
def userShell (envShell : Option String) (passwdShell : String) : String :=
  match envShell with
  | some s => if s.isEmpty then (if passwdShell.isEmpty then "/bin/sh" else passwdShell) else s
  | none => if passwdShell.isEmpty then "/bin/sh" else passwdShell

/-- Only sudoedit changes the front-end identity, regardless of the executable name. -/
def programName (argv0 : String) : String :=
  if basename argv0 == "sudoedit" then "sudoedit" else "sudo"

end LeanSudo.Cli
