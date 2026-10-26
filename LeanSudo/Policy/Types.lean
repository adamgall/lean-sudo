import LeanSudo.Sudoers.Ast

namespace LeanSudo

structure Principal where
  name : String
  uid : Nat
  gid : Nat
  groups : List (String × Nat)
  home : String
  shell : String
  deriving Repr, BEq, DecidableEq, Inhabited

structure GroupInfo where
  name : String
  gid : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Command where
  | run (path : String) (canonical : String) (args : List String)
  | sudoedit (files : List String)
  | list
  | checkList
  | validate
  deriving Repr, BEq, DecidableEq, Inhabited

def Command.text : Command → String
  | .run p _ args => String.intercalate " " (p :: args)
  | .sudoedit fs => String.intercalate " " ("sudoedit" :: fs)
  | .validate => "validate"
  | .list | .checkList => "list"

namespace Policy

def dirOf (s : String) : String :=
  let d := String.ofList ((s.toList.reverse.dropWhile (· != '/')).drop 1).reverse
  if d.isEmpty && s.startsWith "/" then "/" else d

def baseOf (s : String) : String :=
  String.ofList (s.toList.reverse.takeWhile (· != '/')).reverse

end Policy

structure CommandFacts where
  canonPaths : List (String × String) := []
  fileIds : List (String × Nat × Nat) := []
  globPaths : List (String × List String) := []
  regexMatches : List (String × String × Bool) := []
  digests : List Sudoers.Digest := []
  deriving Repr, BEq, DecidableEq, Inhabited

structure RootCommandFacts extends CommandFacts where
  command : Command
  argv : List String := []
  found : Bool := true
  execFd : Option Nat := none
  refusal : Option String := none
  setid : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

structure CommandSelection where
  root : String
  command : Command
  executionPath : String
  argv : List String := []
  found : Bool := true
  execFd : Option Nat := none
  refusal : Option String := none
  setid : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

structure Facts extends CommandFacts where
  canon : String → String := id
  interfaces : List (Sudoers.IpAddr × Sudoers.IpAddr) := []
  netgroups : List (String × Option String × Option String × Bool) := []
  pluginGroups : List (String × String × Bool) := []
  localTimeBounds : List (Nat × Nat) := []
  rootFacts : List (String × RootCommandFacts) := []

structure Request extends Facts where
  user : Principal
  host : String
  runasUser : Principal
  runasGroup : Option GroupInfo
  runasUserExplicit : Bool
  command : Command
  lhost : String := ""
  now : Nat := 0
  fastGlob : Bool := false
  requestedChroot : Option String := none
  defaultChroot : Option String := none

inductive TimestampType where
  | tty | ppid | global | kernel
  deriving Repr, BEq, DecidableEq, Inhabited

inductive PwPolicy where
  | all | always | any | never
  deriving Repr, BEq, DecidableEq, Inhabited

structure Settings where
  envReset : Bool := true
  envKeep : List String := ["COLORS", "DISPLAY", "DPKG_COLORS", "HOSTNAME", "KRB5CCNAME",
    "LS_COLORS", "PATH", "PS1", "PS2", "XAUTHORITY", "XAUTHORIZATION", "XDG_CURRENT_DESKTOP"]
  envCheck : List String := ["COLORTERM", "LANG", "LANGUAGE", "LC_*", "LINGUAS", "TERM", "TZ"]
  envDelete : List String := ["IFS", "CDPATH", "LOCALDOMAIN", "RES_OPTIONS", "HOSTALIASES",
    "NLSPATH", "PATH_LOCALE", "LD_*", "_RLD*", "TERMINFO", "TERMINFO_DIRS", "TERMPATH",
    "TERMCAP", "ENV", "BASH_ENV", "PS4", "GLOBIGNORE", "BASHOPTS", "SHELLOPTS",
    "JAVA_TOOL_OPTIONS", "PERLIO_DEBUG", "PERLLIB", "PERL5LIB", "PERL5OPT", "PERL5DB",
    "FPATH", "NULLCMD", "READNULLCMD", "ZDOTDIR", "TMPPREFIX", "PYTHONHOME", "PYTHONPATH",
    "PYTHONINSPECT", "PYTHONUSERBASE", "RUBYLIB", "RUBYOPT", "*=()*"]
  securePath : Option String := none
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
  passpromptConfigured : Bool := false
  passpromptOverride : Bool := false
  badpassMessage : String := "Sorry, try again."
  badpassMessageConfigured : Bool := false
  pwfeedback : Bool := false
  runasDefault : String := "root"
  umask : Nat := 0o022
  umaskOverride : Bool := false
  umaskExplicit : Bool := false
  setenv : Bool := false
  shellNoargs : Bool := false
  editor : String := "/usr/bin/editor"
  envEditor : Bool := true
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
  interceptAllowSetidConfigured : Bool := false
  interceptType : String := "trace"
  interceptVerify : Bool := true
  logSubcmds : Bool := false
  groupPlugin : Option String := none
  alwaysQueryGroupPlugin : Bool := false
  ignoreAuditErrors : Bool := true
  ignoreIologErrors : Bool := false
  ignoreLogfileErrors : Bool := true
  ignoreDot : Bool := true
  pathInfo : Bool := true
  staySetuid : Bool := false
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

def Settings.resourceLimits (st : Settings) : List (String × String) :=
  [("rlimit_as", st.rlimitAs), ("rlimit_core", st.rlimitCore),
   ("rlimit_cpu", st.rlimitCpu), ("rlimit_data", st.rlimitData),
   ("rlimit_fsize", st.rlimitFsize), ("rlimit_locks", st.rlimitLocks),
   ("rlimit_memlock", st.rlimitMemlock), ("rlimit_nofile", st.rlimitNofile),
   ("rlimit_nproc", st.rlimitNproc), ("rlimit_rss", st.rlimitRss),
   ("rlimit_stack", st.rlimitStack)].filterMap fun (name, value) =>
     value.map (name, ·)

structure Allowed extends Sudoers.TagEffects, Sudoers.ExecutionOptions where
  needsAuth : Bool
  setenv : Bool
  usesDigest : Bool := false
  selection : Option CommandSelection := none
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Judgement where
  | allow (a : Allowed)
  | deny
  deriving Repr, BEq, DecidableEq, Inhabited

end LeanSudo
