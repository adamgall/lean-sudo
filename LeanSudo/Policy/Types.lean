import LeanSudo.Sudoers.Ast

/-!
# Policy contract types

Shared between the policy engine (`LeanSudo.Policy.Eval`, `LeanSudo.Policy.Defaults`),
the environment builder (`LeanSudo.Env`), the decision core (`LeanSudo.Core`) and the
IO shell (`Main`). Everything here is pure data.
-/

namespace LeanSudo

/-- A resolved account (from `getpwnam`/`getpwuid` + `getgrouplist`). -/
structure Principal where
  name : String
  uid : Nat
  /-- primary gid -/
  gid : Nat
  /-- all groups the account is a member of, including the primary group, as (name, gid) -/
  groups : List (String × Nat)
  home : String
  shell : String
  deriving Repr, BEq, DecidableEq, Inhabited

structure GroupInfo where
  name : String
  gid : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Command where
  /-- run a command. `path` is the absolute path found by PATH lookup (as the user
  named it), `canonical` its `realpath`, `args` are argv[1..]. -/
  | run (path : String) (canonical : String) (args : List String)
  /-- `sudo -e` / `sudoedit` on the given files -/
  | sudoedit (files : List String)
  /-- `sudo -l` without a command (any matching rule) -/
  | list
  /-- Permission check for listing another user's privileges. -/
  | checkList
  /-- `sudo -v` (any matching rule) -/
  | validate
  deriving Repr, BEq, DecidableEq, Inhabited

structure Request where
  /-- the invoking user -/
  user : Principal
  /-- short host name -/
  host : String
  /-- target user (for `-g` alone with a `(:group)` rule this is the invoking user) -/
  runasUser : Principal
  /-- target group given with `-g`, if any -/
  runasGroup : Option GroupInfo
  /-- whether `-u` was given explicitly -/
  runasUserExplicit : Bool
  command : Command
  /-- Canonical paths and parent directories, precomputed by the shell. -/
  canon : String → String := id
  lhost : String := ""
  interfaces : List (Sudoers.IpAddr × Sudoers.IpAddr) := []
  /-- (netgroup, user, host, innetgr result). -/
  netgroups : List (String × Option String × Option String × Bool) := []
  /-- (user, plugin group spelling, provider answered exactly 1). -/
  pluginGroups : List (String × String × Bool) := []
  regexMatches : List (String × String × Bool) := []
  digests : List Sudoers.Digest := []
  now : Nat := 0
  /-- Local civil-time offset, seconds east of UTC. -/
  utcOffset : Int := 0
  /-- stat results keyed by absolute path: device and inode. -/
  fileIds : List (String × Nat × Nat) := []
  /-- glob(3) expansions keyed by policy pattern. -/
  globPaths : List (String × List String) := []
  fastGlob : Bool := false

inductive TimestampType where
  | tty | ppid | global | kernel
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Policy for `listpw` / `verifypw`. -/
inductive PwPolicy where
  | all | always | any | never
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Effective `Defaults` settings. Field defaults are sudo's compiled-in defaults. -/
structure Settings where
  envReset : Bool := true
  /-- variables preserved when `env_reset` is on (patterns may end in `*`) -/
  envKeep : List String := ["COLORS", "DISPLAY", "DPKG_COLORS", "HOSTNAME", "KRB5CCNAME",
    "LS_COLORS", "PATH", "PS1", "PS2", "XAUTHORITY", "XAUTHORIZATION", "XDG_CURRENT_DESKTOP"]
  /-- variables preserved only if their value contains no `%` or `/` -/
  envCheck : List String := ["COLORTERM", "LANG", "LANGUAGE", "LC_*", "LINGUAS", "TERM", "TZ"]
  /-- variables removed when `env_reset` is off (patterns may end in `*`) -/
  envDelete : List String := ["IFS", "CDPATH", "LOCALDOMAIN", "RES_OPTIONS", "HOSTALIASES",
    "NLSPATH", "PATH_LOCALE", "LD_*", "_RLD*", "TERMINFO", "TERMINFO_DIRS", "TERMPATH",
    "TERMCAP", "ENV", "BASH_ENV", "PS4", "GLOBIGNORE", "BASHOPTS", "SHELLOPTS",
    "JAVA_TOOL_OPTIONS", "PERLIO_DEBUG", "PERLLIB", "PERL5LIB", "PERL5OPT", "PERL5DB",
    "FPATH", "NULLCMD", "READNULLCMD", "ZDOTDIR", "TMPPREFIX", "PYTHONHOME", "PYTHONPATH",
    "PYTHONINSPECT", "PYTHONUSERBASE", "RUBYLIB", "RUBYOPT", "*=()*"]
  securePath : Option String := none
  /-- seconds; `none` = never expires (negative `timestamp_timeout`) -/
  timestampTimeout : Option Nat := some 900
  timestampType : TimestampType := .tty
  passwdTries : Nat := 3
  authenticate : Bool := true
  rootpw : Bool := false
  targetpw : Bool := false
  runaspw : Bool := false
  usePty : Bool := true
  alwaysSetHome : Bool := false
  setHome : Bool := false
  preserveGroups : Bool := false
  requiretty : Bool := false
  visiblepw : Bool := false
  passprompt : String := "[sudo] password for %p: "
  /-- Explicit sudoers text is not translated as a compiled-in message. -/
  passpromptConfigured : Bool := false
  passpromptOverride : Bool := false
  badpassMessage : String := "Sorry, try again."
  badpassMessageConfigured : Bool := false
  pwfeedback : Bool := false
  runasDefault : String := "root"
  umask : Nat := 0o022
  umaskOverride : Bool := false
  /-- global equivalent of the SETENV tag -/
  setenv : Bool := false
  shellNoargs : Bool := false
  /-- colon separated list -/
  editor : String := "/usr/bin/editor"
  envEditor : Bool := true
  /-- syslog facility name, `none` disables syslog -/
  syslog : Option String := some "authpriv"
  logAllowed : Bool := true
  logDenied : Bool := true
  listpw : PwPolicy := .any
  verifypw : PwPolicy := .all
  pamService : String := "sudo"
  pamLoginService : String := "sudo-i"
  pamSession : Bool := true
  pamSetcred : Bool := true
  fqdn : Bool := true
  caseInsensitiveUser : Bool := true
  caseInsensitiveGroup : Bool := true
  setLogname : Bool := true
  pamSilent : Bool := true
  pamAcctMgmt : Bool := true
  pamRuser : Bool := true
  pamRhost : Bool := false
  pamAskpassService : Option String := none
  execBackground : Bool := false
  ignoreUnknownDefaults : Bool := false
  authfailMessage : Option String := none
  cmddenialMessage : Option String := none
  adminFlag : Option String := some "~/.sudo_as_admin_successful"
  useNetgroups : Bool := true
  netgroupTuple : Bool := false
  matchGroupByGid : Bool := false
  noexec : Bool := false
  noexecFile : Option String := none
  closefrom : Int := 3
  closefromOverride : Bool := false
  commandTimeout : Nat := 0
  userCommandTimeouts : Bool := false
  runcwd : Option String := none
  runchroot : Option String := none
  rlimitAs : Option String := none
  rlimitCore : Option String := some "0,0"
  rlimitCpu : Option String := none
  rlimitData : Option String := none
  rlimitFsize : Option String := none
  rlimitLocks : Option String := none
  rlimitMemlock : Option String := none
  rlimitNofile : Option String := none
  rlimitNproc : Option String := none
  rlimitRss : Option String := none
  rlimitStack : Option String := none
  rootSudo : Bool := true
  runasCheckShell : Bool := false
  runasAllowUnknownId : Bool := false
  logfile : Option String := none
  logFormat : String := "sudo"
  logYear : Bool := false
  logHost : Bool := false
  loglinelen : Nat := 80
  logInput : Bool := false
  logOutput : Bool := false
  iologDir : String := "/var/log/sudo-io"
  iologFile : String := "%{seq}"
  iologUser : Option String := none
  iologGroup : Option String := none
  iologMode : Nat := 0o600
  iologFlush : Bool := false
  compressIo : Bool := true
  maxseq : String := "ZZZZZZ"
  logExitStatus : Bool := false
  logStdin : Bool := false
  logStdout : Bool := false
  logStderr : Bool := false
  logTtyin : Bool := false
  logTtyout : Bool := false
  logPasswords : Bool := true
  passpromptRegex : List String := ["[Pp]assword[: ]*"]
  mailBadpass : Bool := false
  mailAlways : Bool := false
  mailNoUser : Bool := true
  mailNoHost : Bool := false
  mailNoPerms : Bool := false
  mailAllCmnds : Bool := false
  mailto : Option String := some "root"
  mailerpath : Option String := some "/usr/sbin/sendmail"
  mailerflags : Option String := some "-t"
  mailfrom : Option String := none
  mailsub : String := "*** SECURITY information for %h ***"
  lecture : String := "never"
  lectureFile : Option String := none
  lectureStatusDir : String := "/var/lib/sudo/lectured"
  insults : Bool := false
  /-- Password prompt timeout in seconds; none denotes a negative timeout. -/
  passwdTimeout : Option Nat := some 0
  syslogGoodpri : Option String := some "notice"
  syslogBadpri : Option String := some "alert"
  syslogPid : Bool := false
  syslogMaxlen : Nat := 960
  apparmorProfile : Option String := none
  selinux : Bool := true
  role : Option String := none
  type : Option String := none
  exemptGroup : Option String := none
  fastGlob : Bool := false
  sudoeditCheckdir : Bool := true
  sudoeditFollow : Bool := false
  setUtmp : Bool := true
  utmpRunas : Bool := false
  envFile : Option String := none
  restrictedEnvFile : Option String := none
  timestampdir : String := "/run/sudo/ts"
  timestampowner : Option String := none
  intercept : Bool := false
  interceptAuthenticate : Bool := false
  interceptAllowSetid : Bool := true
  interceptType : String := "trace"
  interceptVerify : Bool := true
  logSubcmds : Bool := false
  groupPlugin : Option String := none
  alwaysQueryGroupPlugin : Bool := false
  ignoreAuditErrors : Bool := true
  ignoreIologErrors : Bool := false
  ignoreLogfileErrors : Bool := true
  longOtpPrompt : Bool := false
  ignoreDot : Bool := true
  pathInfo : Bool := true
  staySetuid : Bool := false
  useLoginclass : Bool := false
  ignoreLocalSudoers : Bool := false
  noninteractiveAuth : Bool := false
  privs : Option String := none
  limitprivs : Option String := none
  sudoersLocale : String := "C"
  fdexec : String := "digest_only"
  logServers : List String := []
  logServerTimeout : Nat := 30
  logServerKeepalive : Bool := true
  logServerVerify : Bool := true
  logServerCabundle : Option String := none
  logServerPeerCert : Option String := none
  logServerPeerKey : Option String := none
  deriving Repr, Inhabited

/-- Resource-limit settings passed without reinterpretation to the execution layer. -/
def Settings.resourceLimits (st : Settings) : List (String × String) :=
  [("rlimit_as", st.rlimitAs), ("rlimit_core", st.rlimitCore),
   ("rlimit_cpu", st.rlimitCpu), ("rlimit_data", st.rlimitData),
   ("rlimit_fsize", st.rlimitFsize), ("rlimit_locks", st.rlimitLocks),
   ("rlimit_memlock", st.rlimitMemlock), ("rlimit_nofile", st.rlimitNofile),
   ("rlimit_nproc", st.rlimitNproc), ("rlimit_rss", st.rlimitRss),
   ("rlimit_stack", st.rlimitStack)].filterMap fun (name, value) =>
     value.map (name, ·)

/-- What the policy permits for an allowed request. -/
structure Allowed where
  /-- the matching rule requires authentication (PASSWD tag / `authenticate`) -/
  needsAuth : Bool
  /-- the user may preserve/set environment variables (`SETENV` tag, `setenv`
  default, or the command was matched by `ALL`) -/
  setenv : Bool
  /-- `CWD=` option of the matching rule -/
  cwd : Option (Option String)
  noexec : Option Bool := none
  intercept : Option Bool := none
  logInput : Option Bool := none
  logOutput : Option Bool := none
  mail : Option Bool := none
  follow : Option Bool := none
  chroot : Option String := none
  timeout : Option Nat := none
  role : Option String := none
  type : Option String := none
  apparmorProfile : Option String := none
  privs : Option String := none
  limitprivs : Option String := none
  /-- The deciding command match verified a digest (including through aliases). -/
  usesDigest : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Judgement where
  | allow (a : Allowed)
  | deny
  deriving Repr, BEq, DecidableEq, Inhabited

end LeanSudo
