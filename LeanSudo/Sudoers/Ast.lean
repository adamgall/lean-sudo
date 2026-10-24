/-!
# Sudoers abstract syntax

This is the shared contract between the parser (`LeanSudo.Sudoers.Parser`) and the
policy engine (`LeanSudo.Policy.Eval`).

Design rules:
* The parser accepts the full sudoers(5) grammar of sudo 1.9.17. Constructs whose
  semantics lean-sudo does not implement are still represented here; the decision
  core refuses a request whose deciding rule uses them (fail-closed at decision
  time, so an unsupported feature in someone else's rule does not lock everyone out).
  Syntax that is not valid sudoers is a parse error.
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
  /-- `%:group` (non-Unix group, via `group_plugin`) -/
  | nonunixGroup (n : String)
  /-- `%:#123` -/
  | nonunixGid (n : Nat)
  /-- `+netgroup` -/
  | netgroup (n : String)
  /-- the empty run-as list `()` / `(:)`: the invoking user only (sudo's `MYSELF`) -/
  | myself
  /-- reference to a `User_Alias` (in user lists) or `Runas_Alias` (in run-as lists) -/
  | alias (n : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- An IPv4 (4 bytes) or IPv6 (16 bytes) address, network byte order. -/
inductive IpAddr where
  | v4 (bytes : List UInt8)
  | v6 (bytes : List UInt8)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive HostAtom where
  | all
  | name (n : String)
  /-- `+netgroup` -/
  | netgroup (n : String)
  /-- `ip`, `ip/bits` or `ip/netmask`; masks have the same family as the address.
  Empty bytes mean a bare address (match the interface or its network); `[0]`
  marks an invalid prefix length (accepted syntax but never matches). Explicit
  valid masks are normalized to 4/16 bytes, including all-zero dotted masks. -/
  | network (addr : IpAddr) (mask : IpAddr)
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
  /-- `^…$`: POSIX extended regular expression over the joined arguments -/
  | regex (re : String)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive DigestAlgo where
  | sha224 | sha256 | sha384 | sha512
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `sha256:…` (hex or base64 in sudoers; stored decoded) -/
structure Digest where
  algo : DigestAlgo
  bytes : List UInt8
  /-- Original hex/base64 spelling for sudo -l; never part of digest matching. -/
  spelling : String := ""
  deriving Repr, BEq, DecidableEq, Inhabited

inductive CmndAtom where
  | all
  | alias (n : String)
  /-- an absolute path, a glob over absolute paths, or a directory ending in `/` -/
  | command (path : String) (args : CmndArgs)
  /-- `^…$` path: POSIX extended regular expression over the command path -/
  | commandRegex (re : String) (args : CmndArgs)
  /-- the `sudoedit` pseudo-command -/
  | sudoedit (args : CmndArgs)
  /-- the `list` pseudo-command (permits `sudo -l -U user`) -/
  | list
  /-- `digest_list command`: a command or pseudo-command (never an alias),
  constrained by one of the digests. Negation belongs outside this atom. -/
  | digest (ds : List Digest) (cmd : CmndAtom)
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
  /-- `NOEXEC:` = `some true`, `EXEC:` = `some false` -/
  noexec : Option Bool := Option.none
  /-- `INTERCEPT:` / `NOINTERCEPT:` -/
  intercept : Option Bool := Option.none
  /-- `LOG_INPUT:` / `NOLOG_INPUT:` -/
  logInput : Option Bool := Option.none
  /-- `LOG_OUTPUT:` / `NOLOG_OUTPUT:` -/
  logOutput : Option Bool := Option.none
  /-- `MAIL:` / `NOMAIL:` -/
  mail : Option Bool := Option.none
  /-- `FOLLOW:` / `NOFOLLOW:` -/
  follow : Option Bool := Option.none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Per-command options. -/
structure CmndOptions where
  /-- `CWD=path` (`some (some p)`), `CWD=*` (`some none`: user may pick with `-D`);
  `~` / `~user` are kept verbatim and expanded by the decision core -/
  cwd : Option (Option String) := Option.none
  /-- `CHROOT=dir` (`*` kept verbatim) -/
  chroot : Option String := Option.none
  /-- `TIMEOUT=` in seconds -/
  timeout : Option Nat := Option.none
  /-- `NOTBEFORE=` / `NOTAFTER=` as Unix time (seconds, UTC) -/
  notBefore : Option Nat := Option.none
  notAfter : Option Nat := Option.none
  /-- Zone-less Generalized Time values need the machine-local UTC offset.
  The stored seconds are computed as UTC; negative epoch values are clamped to
  zero (equivalent for authorization at contemporary positive wall clocks). -/
  notBeforeLocal : Bool := false
  notAfterLocal : Bool := false
  /-- SELinux `ROLE=` / `TYPE=` -/
  role : Option String := Option.none
  type : Option String := Option.none
  /-- `APPARMOR_PROFILE=` -/
  apparmorProfile : Option String := Option.none
  /-- Solaris `PRIVS=` / `LIMITPRIVS=` (no effect on Linux) -/
  privs : Option String := Option.none
  limitprivs : Option String := Option.none
  deriving Repr, BEq, DecidableEq, Inhabited

structure CmndSpec where
  /-- effective (inherited) run-as spec; `none` = no spec anywhere before it in the list -/
  runas : Option RunasSpec
  options : CmndOptions
  tags : Tags
  cmnd : Member CmndAtom
  /-- Explicit run-as syntax starts a new listing group even when equal to its predecessor. -/
  runasExplicit : Bool := false
  /-- String-valued options written here, for pointer-sensitive sudo -l rendering. -/
  optionsExplicit : List String := []
  /-- SSSD privilege metadata; options remain separate from global Defaults. -/
  ldapRole : Option String := none
  ldapOptions : List String := []
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
  /-- Terminator line/column recorded by sudo's parser for event log source. -/
  source : Option (Nat × Nat) := none
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
