import LeanSudo.Policy.Types
import LeanSudo.Cli
import LeanSudo.Env
import LeanSudo.Timestamp

/-!
# Decision-core contract (frozen)

The IO shell (`Main`) gathers every fact into a `Context`, calls the pure
`LeanSudo.Core.decide : Context → Decision`, and executes the `Decision`:

1. if `auth = .required u`: re-check the timestamp; if invalid, authenticate `u` with PAM
   (up to `settings.passwdTries` attempts); on failure stop (exit 1);
2. run PAM account management (always, also when `auth = .none`, for `exec`/`edit`);
3. if `updateTimestamp` and authentication (or a valid timestamp) succeeded: record it;
4. log `log` to syslog (if `settings.syslog` is set);
5. perform `action`.

Every security theorem is stated about `decide` (`LeanSudo.CoreProofs`).
-/

namespace LeanSudo.Core

open LeanSudo.Sudoers

/-- A command resolved by the IO shell (PATH search, or the shell for `-s`/`-i`). -/
structure ResolvedCmd where
  /-- absolute path handed to `execve`: the path *as found* (not the realpath), so
  multicall binaries dispatch on the name -/
  path : String
  /-- `realpath` of `path` (used for policy matching only) -/
  canonical : String
  /-- `argv[0]`: as typed by the user; `-<basename>` for `-i` -/
  argv0 : String
  /-- `argv[1..]` -/
  args : List String
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Everything `decide` may depend on. -/
structure Context where
  /-- `sudo` or `sudoedit` (basename of argv[0]) -/
  progname : String
  opts : Cli.Options
  /-- getuid + getpwuid; `groups` = the PROCESS groups (getgroups) with names, plus the
  primary group, as sudo uses for `%group` matching -/
  invoking : Principal
  /-- short hostname -/
  host : String
  /-- include-resolved policy; `Policy.validate` has already passed -/
  sudoers : Sudoers
  /-- `resolveDefaults` with the run-as user and the command (phase 2) -/
  settings : Settings
  /-- run-as user: `-u` user / `#uid`; `-g` without `-u` ⇒ the invoking user; otherwise
  `runas_default`. `groups` = getgrouplist of that user. -/
  target : Principal
  /-- `-g` group, resolved -/
  targetGroup : Option GroupInfo
  /-- `-U` user for `-l`, resolved -/
  listUser : Option Principal
  /-- the command for `run` mode (and `-l cmd`); `none` = not found by PATH lookup
  (`opts.command.head?` is what the user typed). For `-s`/`-i` it is the shell
  command built with `Cli.shellCommand`. Unused for `-e`, `-v`, `-k`, `-K`, `-l`. -/
  command : Option ResolvedCmd
  /-- the invoking user's environment (UTF-8 entries only) -/
  userEnv : EnvList
  /-- current working directory -/
  cwd : String
  /-- the invoking process's umask -/
  userUmask : Nat
  /-- `ttyname` of the controlling terminal (for logging and PAM_TTY), if any -/
  ttyName : Option String
  /-- realpath oracle for literal command paths written in sudoers (identity when a
  path does not resolve) -/
  canon : String → String
  /-- `CLOCK_BOOTTIME` nanoseconds -/
  now : Nat
  /-- timestamp scope of this invocation (`Timestamp.scopeFor settings.timestampType …`) -/
  tsScope : Timestamp.Scope
  /-- records of the invoking uid's timestamp file (`Timestamp.load`; `[]` on any error) -/
  tsRecords : List Timestamp.Record

/-- Whose credentials must be checked before `action` may happen. -/
inductive AuthReq where
  | none
  /-- the invoking user, or root (`rootpw`) / the target (`targetpw`) /
  `runas_default` (`runaspw`) -/
  | required (authUser : Principal)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- How to run the command. The environment is `buildEnv { envInput with pamEnv }`
where `pamEnv` is `pam_getenvlist` after `pam_open_session`; `decide` has already checked
that `buildEnv envInput` succeeds (its success does not depend on `pamEnv`). -/
structure ExecPlan where
  path : String
  /-- full argv including argv[0] -/
  argv : List String
  envInput : EnvInput
  uid : Nat
  gid : Nat
  /-- supplementary groups for `setgroups` -/
  groups : List Nat
  /-- `chdir` target after the privilege drop (`none`: stay in the current directory) -/
  cwd : Option String
  /-- umask for the command, `≤ 0o777` -/
  umask : Nat
  usePty : Bool
  background : Bool
  closeFrom : Nat
  /-- PAM service: `pamLoginService` for `-i`, else `pamService` -/
  pamService : String
  pamSession : Bool
  pamSetcred : Bool

/-- `sudoedit` (`-e`): files are copied to temporary files owned by the invoking user,
the editor runs as the invoking user, and changed files are written back as the target
(`LeanSudo.Sudoedit`). -/
structure EditPlan where
  /-- the files to edit, made absolute against `Context.cwd`, in the order given -/
  files : List String
  /-- candidate editor command lines in order of preference (`SUDO_EDITOR`, `VISUAL`,
  `EDITOR` when `env_editor`, then the `editor` setting's entries), each split into
  words; the IO shell uses the first whose first word resolves to an executable -/
  editors : List (List String)
  /-- identity the editor runs as (the invoking user) -/
  editUid : Nat
  editGid : Nat
  editGroups : List Nat
  /-- identity used to read and write back the files (the run-as target) -/
  fileUid : Nat
  fileGid : Nat
  fileGroups : List Nat
  /-- environment of the editor: `buildEnv { envInput with pamEnv }` -/
  envInput : EnvInput
  umask : Nat
  pamService : String
  pamSession : Bool
  pamSetcred : Bool

inductive Action where
  | exec (plan : ExecPlan)
  | edit (plan : EditPlan)
  /-- write `stdout` verbatim, exit with `code` (`-l` output, `-l cmd`) -/
  | print (stdout : String) (code : UInt32)
  /-- write `stderr` verbatim (complete text, including any `sudo: ` prefix and the
  trailing newline), exit with `code` -/
  | fail (stderr : String) (code : UInt32)
  /-- `-v`: authentication refreshed the timestamp; exit 0 -/
  | validate
  /-- `-k` alone: invalidate every record of the invoking uid; exit 0 -/
  | resetTimestamp
  /-- `-K`: remove the invoking uid's timestamp file; exit 0 -/
  | removeTimestamp
  deriving Inhabited

structure LogLine where
  /-- syslog priority name (`notice` for allowed, `alert` for denied) -/
  priority : String
  /-- e.g. `alice : TTY=pts/0 ; PWD=/home/alice ; USER=root ; COMMAND=/usr/bin/id` or
  `carol : command not allowed ; TTY=… ; PWD=… ; USER=root ; COMMAND=…` -/
  msg : String
  deriving Repr, BEq, DecidableEq, Inhabited

structure Decision where
  auth : AuthReq
  action : Action
  /-- record a successful authentication in the timestamp file -/
  updateTimestamp : Bool
  log : Option LogLine
  deriving Inhabited

end LeanSudo.Core
