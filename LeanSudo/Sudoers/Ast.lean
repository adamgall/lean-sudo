namespace LeanSudo.Sudoers

structure Member (α : Type) where
  negated : Bool
  atom : α
  deriving Repr, BEq, DecidableEq, Inhabited

inductive UserAtom where
  | all
  | name (n : String)
  | id (n : Nat)
  | group (n : String)
  | gid (n : Nat)
  | nonunixGroup (n : String)
  | nonunixGid (n : Nat)
  | netgroup (n : String)
  | myself
  | alias (n : String)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive IpAddr where
  | v4 (bytes : List UInt8)
  | v6 (bytes : List UInt8)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive HostAtom where
  | all
  | name (n : String)
  | netgroup (n : String)
  | network (addr : IpAddr) (mask : IpAddr)
  | alias (n : String)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive CmndArgs where
  | any
  | none
  | pattern (p : String)
  | regex (re : String)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive DigestAlgo where
  | sha224 | sha256 | sha384 | sha512
  deriving Repr, BEq, DecidableEq, Inhabited

structure Digest where
  algo : DigestAlgo
  bytes : List UInt8
  spelling : String := ""
  deriving Repr, BEq, DecidableEq, Inhabited

inductive CmndAtom where
  | all
  | alias (n : String)
  | command (path : String) (args : CmndArgs)
  | commandRegex (re : String) (args : CmndArgs)
  | sudoedit (args : CmndArgs)
  | list
  | digest (ds : List Digest) (cmd : CmndAtom)
  deriving Repr, BEq, DecidableEq, Inhabited

structure RunasSpec where
  users : Option (List (Member UserAtom))
  groups : Option (List (Member UserAtom))
  deriving Repr, BEq, DecidableEq, Inhabited

structure TagEffects where
  noexec : Option Bool := Option.none
  intercept : Option Bool := Option.none
  logInput : Option Bool := Option.none
  logOutput : Option Bool := Option.none
  mail : Option Bool := Option.none
  follow : Option Bool := Option.none
  deriving Repr, BEq, DecidableEq, Inhabited

structure Tags extends TagEffects where
  passwd : Option Bool := Option.none
  setenv : Option Bool := Option.none
  deriving Repr, BEq, DecidableEq, Inhabited

structure ExecutionOptions where
  cwd : Option (Option String) := Option.none
  chroot : Option String := Option.none
  timeout : Option Nat := Option.none
  role : Option String := Option.none
  type : Option String := Option.none
  apparmorProfile : Option String := Option.none
  privs : Option String := Option.none
  limitprivs : Option String := Option.none
  deriving Repr, BEq, DecidableEq, Inhabited

structure CmndOptions extends ExecutionOptions where
  notBefore : Option Nat := Option.none
  notAfter : Option Nat := Option.none
  notBeforeLocal : Bool := false
  notAfterLocal : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

structure CmndSpec where
  runas : Option RunasSpec
  options : CmndOptions
  tags : Tags
  cmnd : Member CmndAtom
  runasExplicit : Bool := false
  optionsExplicit : List String := []
  ldapRole : Option String := none
  ldapOptions : List String := []
  deriving Repr, BEq, DecidableEq, Inhabited

structure HostCmnds where
  hosts : List (Member HostAtom)
  cmnds : List CmndSpec
  deriving Repr, BEq, DecidableEq, Inhabited

structure UserSpec where
  users : List (Member UserAtom)
  entries : List HostCmnds
  source : Option (Nat × Nat) := none
  deriving Repr, BEq, DecidableEq, Inhabited

inductive DefaultsScope where
  | global
  | host (hs : List (Member HostAtom))
  | user (us : List (Member UserAtom))
  | runas (rs : List (Member UserAtom))
  | cmnd (cs : List (Member CmndAtom))
  deriving Repr, BEq, DecidableEq, Inhabited

inductive DefaultsOp where
  | flag (on : Bool)
  | assign (v : String)
  | add (v : String)
  | remove (v : String)
  deriving Repr, BEq, DecidableEq, Inhabited

structure DefaultsSetting where
  name : String
  op : DefaultsOp
  source : Option (String × Nat × Nat) := none
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Entry where
  | userAlias (name : String) (members : List (Member UserAtom))
  | runasAlias (name : String) (members : List (Member UserAtom))
  | hostAlias (name : String) (members : List (Member HostAtom))
  | cmndAlias (name : String) (members : List (Member CmndAtom))
  | defaults (scope : DefaultsScope) (settings : List DefaultsSetting)
  | userSpec (spec : UserSpec)
  | include (path : String)
  | includeDir (path : String)
  deriving Repr, BEq, DecidableEq, Inhabited

structure Located where
  file : String
  line : Nat
  entry : Entry
  warnings : List String := []
  deriving Repr, BEq, Inhabited

abbrev Sudoers := List Entry

end LeanSudo.Sudoers
