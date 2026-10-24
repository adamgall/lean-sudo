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
  /-- `realpath` oracle for command paths appearing in sudoers, precomputed by the IO
  layer (identity for paths that do not resolve). Used so that `/bin/ls` in sudoers
  matches `/usr/bin/ls` on usr-merged systems, mirroring sudo's inode comparison. -/
  canon : String → String := id

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
  envKeep : List String := ["COLORS", "DISPLAY", "HOSTNAME", "KRB5CCNAME", "LS_COLORS",
    "PS1", "PS2", "XAUTHORITY", "XAUTHORIZATION", "XDG_CURRENT_DESKTOP"]
  /-- variables preserved only if their value contains no `%` or `/` -/
  envCheck : List String := ["COLORTERM", "LANG", "LANGUAGE", "LC_*", "LINGUAS", "TERM", "TZ"]
  /-- variables removed when `env_reset` is off (patterns may end in `*`) -/
  envDelete : List String := ["IFS", "CDPATH", "LOCALDOMAIN", "RES_OPTIONS", "HOSTALIASES",
    "NLSPATH", "PATH_LOCALE", "LD_*", "_RLD*", "TERMINFO", "TERMINFO_DIRS", "TERMPATH",
    "TERMCAP", "ENV", "BASH_ENV", "PS4", "GLOBIGNORE", "BASHOPTS", "SHELLOPTS",
    "JAVA_TOOL_OPTIONS", "PERLIO_DEBUG", "PERLLIB", "PERL5LIB", "PERL5OPT", "PERL5DB",
    "FPATH", "NULLCMD", "READNULLCMD", "ZDOTDIR", "TMPPREFIX", "PYTHONHOME", "PYTHONPATH",
    "PYTHONINSPECT", "PYTHONUSERBASE", "RUBYLIB", "RUBYOPT"]
  securePath : Option String := none
  /-- seconds; `none` = never expires (negative `timestamp_timeout`) -/
  timestampTimeout : Option Nat := some 900
  timestampType : TimestampType := .tty
  passwdTries : Nat := 3
  authenticate : Bool := true
  rootpw : Bool := false
  targetpw : Bool := false
  runaspw : Bool := false
  usePty : Bool := false
  alwaysSetHome : Bool := false
  setHome : Bool := false
  preserveGroups : Bool := false
  requiretty : Bool := false
  visiblepw : Bool := false
  passprompt : String := "[sudo] password for %p: "
  passpromptOverride : Bool := false
  badpassMessage : String := "Sorry, try again."
  pwfeedback : Bool := false
  runasDefault : String := "root"
  umask : Nat := 0o022
  umaskOverride : Bool := false
  /-- global equivalent of the SETENV tag -/
  setenv : Bool := false
  shellNoargs : Bool := false
  /-- colon separated list -/
  editor : String := "/usr/bin/editor:/usr/bin/vi"
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
  deriving Repr, Inhabited

/-- What the policy permits for an allowed request. -/
structure Allowed where
  /-- the matching rule requires authentication (PASSWD tag / `authenticate`) -/
  needsAuth : Bool
  /-- the user may preserve/set environment variables (`SETENV` tag, `setenv`
  default, or the command was matched by `ALL`) -/
  setenv : Bool
  /-- `CWD=` option of the matching rule -/
  cwd : Option (Option String)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Judgement where
  | allow (a : Allowed)
  | deny
  deriving Repr, BEq, DecidableEq, Inhabited

end LeanSudo
