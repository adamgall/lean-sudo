/-!
# Sudoers abstract syntax

This is the shared contract between the parser (`LeanSudo.Sudoers.Parser`) and the
policy engine (`LeanSudo.Policy.Eval`).

Design rules:
* The parser is **fail-closed**: any sudoers construct whose semantics we do not
  implement (netgroups, IP/netmask hosts, digests, regex arguments, NOEXEC,
  INTERCEPT, CHROOT, TIMEOUT, NOTBEFORE/NOTAFTER, SELinux/AppArmor options, ...)
  is a parse error, never silently ignored. Silently ignoring a *restricting*
  construct would widen what is permitted.
* Negation parity is normalised: `!!x` is stored as `negated := false`.
* Run-as specs and tags are *inherited* within one `Cmnd_Spec_List`
  (`(root) NOPASSWD: /a, /b` applies to both commands). The parser resolves that
  inheritance, so every `CmndSpec` carries its effective run-as spec and tags.
* `#include`/`@include`/`#includedir`/`@includedir` are emitted as entries; the IO
  layer resolves them and splices the included entries in place (order matters
  because the policy is last-match-wins).
-/

namespace LeanSudo.Sudoers

/-- A possibly negated list element. -/
structure Member (α : Type) where
  negated : Bool
  atom : α
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Elements of User lists and Runas lists.

In the *group* half of a run-as spec (`(users : groups)`), `name n` denotes the
group named `n` and `id n` denotes gid `n`. -/
inductive UserAtom where
  | all
  /-- user name (or group name, in a run-as group list) -/
  | name (n : String)
  /-- `#123`: numeric uid (or gid, in a run-as group list) -/
  | id (n : Nat)
  /-- `%group` -/
  | group (n : String)
  /-- `%#123` -/
  | gid (n : Nat)
  /-- reference to a `User_Alias` (in user lists) or `Runas_Alias` (in run-as lists) -/
  | alias (n : String)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive HostAtom where
  | all
  | name (n : String)
  | alias (n : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Argument constraint of a command. -/
inductive CmndArgs where
  /-- no arguments given in sudoers: any arguments allowed -/
  | any
  /-- `""` in sudoers: the command must be run with no arguments -/
  | none
  /-- arguments given: the user's arguments, joined by single spaces, must match
  this pattern (fnmatch semantics without FNM_PATHNAME; plain string equality when
  the pattern has no glob metacharacters). Escapes (`\,` `\:` `\=` `\\` `\ `) are
  already removed by the parser. -/
  | pattern (p : String)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive CmndAtom where
  | all
  | alias (n : String)
  /-- an absolute path, a glob over absolute paths, or a directory ending in `/` -/
  | command (path : String) (args : CmndArgs)
  /-- the `sudoedit` pseudo-command -/
  | sudoedit (args : CmndArgs)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `(users : groups)`. `none` means the half was not written. -/
structure RunasSpec where
  users : Option (List (Member UserAtom))
  groups : Option (List (Member UserAtom))
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Tags; `none` = not specified (the corresponding Defaults flag decides). -/
structure Tags where
  /-- `PASSWD:` = `some true`, `NOPASSWD:` = `some false` -/
  passwd : Option Bool := Option.none
  /-- `SETENV:` = `some true`, `NOSETENV:` = `some false` -/
  setenv : Option Bool := Option.none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Per-command options. -/
structure CmndOptions where
  /-- `CWD=path` (`some (some p)`) or `CWD=*` (`some none`: user may pick with `-D`) -/
  cwd : Option (Option String) := Option.none
  deriving Repr, BEq, DecidableEq, Inhabited

structure CmndSpec where
  /-- effective (inherited) run-as spec; `none` = no spec anywhere before it in the list -/
  runas : Option RunasSpec
  options : CmndOptions
  tags : Tags
  cmnd : Member CmndAtom
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `Host_List = Cmnd_Spec_List` -/
structure HostCmnds where
  hosts : List (Member HostAtom)
  cmnds : List CmndSpec
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `User_List Host_List = Cmnd_Spec_List (: Host_List = Cmnd_Spec_List)*` -/
structure UserSpec where
  users : List (Member UserAtom)
  entries : List HostCmnds
  deriving Repr, BEq, DecidableEq, Inhabited

inductive DefaultsScope where
  | global
  /-- `Defaults@host_list` -/
  | host (hs : List (Member HostAtom))
  /-- `Defaults:user_list` -/
  | user (us : List (Member UserAtom))
  /-- `Defaults>runas_list` -/
  | runas (rs : List (Member UserAtom))
  /-- `Defaults!cmnd_list` -/
  | cmnd (cs : List (Member CmndAtom))
  deriving Repr, BEq, DecidableEq, Inhabited

inductive DefaultsOp where
  /-- `name` (true) or `!name` (false) -/
  | flag (on : Bool)
  /-- `name=value` (quotes removed) -/
  | assign (v : String)
  /-- `name+=value` -/
  | add (v : String)
  /-- `name-=value` -/
  | remove (v : String)
  deriving Repr, BEq, DecidableEq, Inhabited

structure DefaultsSetting where
  name : String
  op : DefaultsOp
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Entry where
  | userAlias (name : String) (members : List (Member UserAtom))
  | runasAlias (name : String) (members : List (Member UserAtom))
  | hostAlias (name : String) (members : List (Member HostAtom))
  | cmndAlias (name : String) (members : List (Member CmndAtom))
  | defaults (scope : DefaultsScope) (settings : List DefaultsSetting)
  | userSpec (spec : UserSpec)
  /-- `#include path` / `@include path` (path as written, `%h` not yet expanded) -/
  | include (path : String)
  /-- `#includedir dir` / `@includedir dir` -/
  | includeDir (path : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- An entry with the file and 1-based line where it starts (for diagnostics). -/
structure Located where
  file : String
  line : Nat
  entry : Entry
  deriving Repr, BEq, Inhabited

/-- A fully include-resolved sudoers policy, in file order. -/
abbrev Sudoers := List Entry

end LeanSudo.Sudoers
