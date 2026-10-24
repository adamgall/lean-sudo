import LeanSudo.Policy.Types
import LeanSudo.Util.Glob

/-!
# Policy evaluation

`evaluate s st r` decides a `Request` against an include-resolved sudoers policy.

## List semantics (sudo's last-match-wins)

Every list (user, host, run-as, command, and alias member lists) is scanned in order;
the result is decided by the **last** member with a non-`none` result.
Alias atoms preserve their own member list's tri-state result recursively.
Member negation flips `some b` to `some (!b)`; `none` stays `none`.

Alias recursion is bounded by fuel `Aliases.fuel` = number of alias definitions + 1.
`validate` rejects alias cycles, undefined alias references and duplicate alias
names, so on validated policies the fuel never runs out. On unvalidated input,
running out of fuel or an undefined alias makes the alias atom *not match*. That is
the conservative choice for non-negated members but not for negated ones (a
`!BADALIAS` that silently does not match widens the policy), which is why **callers
must run `validate` first** (Main does). The proofs in `LeanSudo.Policy.Proofs` do not
depend on this: soundness is stated in terms of the same matching functions.

## Decision

`candidates` walks all user specifications in file order and collects one
`Candidate` per command spec whose user list, host list, run-as spec and command
member all match (for `-l`/`-v` only user and host lists are checked). For running a
command the last candidate decides (`judge`); no candidate ⇒ `.deny`.
For `-l`/`-v`, every spec of a matching user/host entry remains a candidate,
with `allow := !cs.cmnd.negated`: listing does not evaluate command aliases or run-as.
-/

namespace LeanSudo.Policy

open LeanSudo.Sudoers
open LeanSudo.Glob (fnmatch hasGlob)

/-! ## Generic list matching -/

/-- Last non-UNSPEC result wins; member negation flips ALLOW and DENY. -/
def matchList {α : Type} (m : α → Option Bool) : List (Member α) → Option Bool
  | [] => none
  | x :: xs =>
    match matchList m xs with
    | some b => some b
    | none => (m x.atom).map (fun b => b != x.negated)

/-! ## Aliases and user specifications -/

/-- Alias definitions of a policy, by kind, in file order. -/
structure Aliases where
  user : List (String × List (Member UserAtom)) := []
  runas : List (String × List (Member UserAtom)) := []
  host : List (String × List (Member HostAtom)) := []
  cmnd : List (String × List (Member CmndAtom)) := []
  deriving Repr, Inhabited

def aliasesOf : Sudoers → Aliases
  | [] => {}
  | .userAlias n ms :: es => let a := aliasesOf es; { a with user := (n, ms) :: a.user }
  | .runasAlias n ms :: es => let a := aliasesOf es; { a with runas := (n, ms) :: a.runas }
  | .hostAlias n ms :: es => let a := aliasesOf es; { a with host := (n, ms) :: a.host }
  | .cmndAlias n ms :: es => let a := aliasesOf es; { a with cmnd := (n, ms) :: a.cmnd }
  | _ :: es => aliasesOf es

/-- Fuel for alias expansion: enough for any acyclic alias graph. -/
def Aliases.fuel (a : Aliases) : Nat :=
  a.user.length + a.runas.length + a.host.length + a.cmnd.length + 1

/-- The user specifications of a policy, in file order. -/
def specsOf : Sudoers → List UserSpec
  | [] => []
  | .userSpec u :: es => u :: specsOf es
  | _ :: es => specsOf es

/-- First definition of an alias (duplicates are rejected by `validate`). -/
def lookupAlias {β : Type} (l : List (String × β)) (n : String) : Option β :=
  (l.find? (·.1 == n)).map (·.2)

def UserAtom.aliasName : UserAtom → Option String
  | .alias n => some n
  | _ => none

def HostAtom.aliasName : HostAtom → Option String
  | .alias n => some n
  | _ => none

def CmndAtom.aliasName : CmndAtom → Option String
  | .alias n => some n
  | _ => none

/-- Alias-aware tri-state matching. Undefined aliases / exhausted fuel give `none`. -/
def atomMatches {α : Type} (aliasName : α → Option String)
    (defs : List (String × List (Member α))) (base : α → Bool) : Nat → α → Option Bool
  | 0, a => if (aliasName a).isNone && base a then some true else none
  | f + 1, a =>
    match aliasName a with
    | some n =>
      match lookupAlias defs n with
      | some ms => matchList (atomMatches aliasName defs base f) ms
      | none => none
    | none => if base a then some true else none

/-! ## Users, groups, hosts -/

/-- A user-list atom against a principal (`%group`/`%#gid` = membership, including the
primary group). Alias atoms are handled by `atomMatches`. -/
def userBase (p : Principal) : UserAtom → Bool
  | .all => true
  | .name n => n == p.name
  | .id n => n == p.uid
  | .group n => p.groups.any (·.1 == n)
  | .gid n => n == p.gid || p.groups.any (·.2 == n)
  | .alias _ => false

/-- A run-as *group* list atom against a group (`name` = group name, `id` = gid). -/
def groupBase (g : GroupInfo) : UserAtom → Bool
  | .all => true
  | .name n => n == g.name
  | .id n => n == g.gid
  | _ => false

/-- ASCII case-insensitive host comparison, or case-insensitive glob. -/
def hostBase (host : String) : HostAtom → Bool
  | .all => true
  | .name n => if hasGlob n then fnmatch n host false true else n.toLower == host.toLower
  | .alias _ => false

/-- Result of a user list (with `User_Alias`es) for the invoking user. -/
def userListResult (al : Aliases) (fuel : Nat) (p : Principal) (l : List (Member UserAtom)) :
    Option Bool :=
  matchList (atomMatches UserAtom.aliasName al.user (userBase p) fuel) l

def userListOk (al : Aliases) (fuel : Nat) (p : Principal) (l : List (Member UserAtom)) : Bool :=
  userListResult al fuel p l == some true

def hostListOk (al : Aliases) (fuel : Nat) (host : String) (l : List (Member HostAtom)) : Bool :=
  matchList (atomMatches HostAtom.aliasName al.host (hostBase host) fuel) l == some true

/-- Result of a run-as user list (with `Runas_Alias`es) for the target user. -/
def runasUserResult (al : Aliases) (fuel : Nat) (t : Principal) (l : List (Member UserAtom)) :
    Option Bool :=
  matchList (atomMatches UserAtom.aliasName al.runas (userBase t) fuel) l

/-- Result of a run-as group list (with `Runas_Alias`es) for the requested group. -/
def runasGroupResult (al : Aliases) (fuel : Nat) (g : GroupInfo) (l : List (Member UserAtom)) :
    Option Bool :=
  matchList (atomMatches UserAtom.aliasName al.runas (groupBase g) fuel) l

/-! ## Run-as -/

/-- Is `t` the `runas_default` user (`#uid` form allowed)? -/
def isRunasDefault (st : Settings) (t : Principal) : Bool :=
  match st.runasDefault.toList with
  | '#' :: ds =>
    match (String.ofList ds).toNat? with
    | some n => n == t.uid
    | none => false
  | _ => st.runasDefault == t.name

/-- Group half of a run-as check. No `-g` ⇒ fine. Otherwise the group list's last
match decides; if it has none (or there is no group list) the requested group must be
the target user's primary group. -/
def runasGroupOk (al : Aliases) (fuel : Nat) (r : Request) (gs : Option (List (Member UserAtom))) :
    Bool :=
  match r.runasGroup with
  | none => true
  | some g =>
    match gs.bind (runasGroupResult al fuel g) with
    | some b => b
    | none => g.gid == r.runasUser.gid

/-- Does a command spec's effective run-as spec permit the requested target? -/
def runasOk (al : Aliases) (fuel : Nat) (st : Settings) (r : Request) : Option RunasSpec → Bool
  | none | some ⟨none, none⟩ =>
    isRunasDefault st r.runasUser && runasGroupOk al fuel r none
  | some ⟨some us, gs⟩ =>
    let userPart :=
      match runasUserResult al fuel r.runasUser us with
      | some b => b
      -- sudo: no run-as user matched at all ⇒ running as yourself is fine
      | none => r.runasUser.uid == r.user.uid
    userPart && runasGroupOk al fuel r gs
  | some ⟨none, some gs⟩ =>
    r.runasUser.uid == r.user.uid && runasGroupOk al fuel r (some gs)

/-! ## Commands -/

/-- Directory part of a path, without the trailing slash (`/usr/bin/ls` ↦ `/usr/bin`). -/
def dirOf (s : String) : String :=
  String.ofList ((s.toList.reverse.dropWhile (· != '/')).drop 1).reverse

def endsWithSlash (p : String) : Bool := p.toList.getLast? == some '/'

def dropLastChar (p : String) : String := String.ofList p.toList.dropLast

/-- Last path component (`/usr/bin/ls` ↦ `ls`). -/
def baseOf (s : String) : String :=
  String.ofList (s.toList.reverse.takeWhile (· != '/')).reverse

/-- Argument constraint. -/
def argsMatch : CmndArgs → List String → Bool
  | .any, _ => true
  | .none, as => as.isEmpty
  | .pattern q, as =>
    let j := " ".intercalate as
    if hasGlob q then fnmatch q j false else q == j

/-- Path part of a command atom against the requested `path` (as found by PATH lookup)
and its `canonical` realpath. `canon` is the realpath oracle for sudoers paths.

* directory `d/`: `path` lies directly in `d`, or the canonical directory of `path`
  equals the canonical `d` (usr-merge: `/bin/` vs `/usr/bin/`);
* glob: matched against `path` only;
* literal: `p == path`, or the basenames agree and `p` resolves to `canonical`.

Like sudo, a realpath/inode comparison is only made between files with the same
basename: on multicall systems (`/usr/bin/id` and `/usr/bin/rm` both symlinks to one
binary) a rule for `id` must not permit `rm`. The canonical target of the requested
file itself is never compared against a directory rule for the same reason. -/
def pathMatches (canon : String → String) (p path canonical : String) : Bool :=
  if endsWithSlash p then
    let pd := dropLastChar p
    dirOf path == pd || canon (dirOf path) == canon pd
  else if hasGlob p then
    fnmatch p path true
  else
    p == path || (baseOf p == baseOf path && canon p == canonical)

/-- A command atom against the requested command (aliases via `atomMatches`). -/
def cmndBase (canon : String → String) : Command → CmndAtom → Bool
  | .run _ _ _, .all => true
  | .sudoedit _, .all => true
  | .run path canonical args, .command p a => pathMatches canon p path canonical && argsMatch a args
  | .sudoedit files, .sudoedit a => argsMatch a files
  | _, _ => false

def cmndListResult (al : Aliases) (fuel : Nat) (canon : String → String) (cmd : Command)
    (l : List (Member CmndAtom)) : Option Bool :=
  matchList (atomMatches CmndAtom.aliasName al.cmnd (cmndBase canon cmd) fuel) l

def cmndMemberResult (al : Aliases) (fuel : Nat) (canon : String → String) (cmd : Command)
    (m : Member CmndAtom) : Option Bool :=
  cmndListResult al fuel canon cmd [m]

/-! ## Decision -/

/-- Running a command or sudoedit (as opposed to `-l` / `-v`). -/
def isRunCmd : Command → Bool
  | .run _ _ _ | .sudoedit _ => true
  | .list | .validate => false

/-- A matching command spec, retaining its command member's ALLOW or DENY result. -/
structure Candidate where
  spec : CmndSpec
  allow : Bool
  deriving Repr, BEq, Inhabited

/-- Does a command spec apply to the request? For `-l`/`-v` every spec does (only the
user and host lists are relevant); otherwise run-as and the command member must match. -/
def specApplies (al : Aliases) (fuel : Nat) (st : Settings) (r : Request) (cs : CmndSpec) : Bool :=
  !isRunCmd r.command ||
    (runasOk al fuel st r cs.runas && (cmndMemberResult al fuel r.canon r.command cs.cmnd).isSome)

/-- Listing retains syntactic negation; run requests retain the tri-state result. -/
def specAllow (al : Aliases) (fuel : Nat) (r : Request) (cs : CmndSpec) : Bool :=
  if isRunCmd r.command then (cmndMemberResult al fuel r.canon r.command cs.cmnd).getD false
  else !cs.cmnd.negated

def hcCandidates (al : Aliases) (fuel : Nat) (st : Settings) (r : Request) (hc : HostCmnds) :
    List Candidate :=
  if hostListOk al fuel r.host hc.hosts then
    (hc.cmnds.filter (specApplies al fuel st r)).map fun cs => ⟨cs, specAllow al fuel r cs⟩
  else []

def usCandidates (al : Aliases) (fuel : Nat) (st : Settings) (r : Request) (us : UserSpec) :
    List Candidate :=
  if userListOk al fuel r.user us.users then us.entries.flatMap (hcCandidates al fuel st r) else []

def candidatesCore (al : Aliases) (specs : List UserSpec) (st : Settings) (r : Request) :
    List Candidate :=
  specs.flatMap (usCandidates al al.fuel st r)

/-- All candidates of a policy for a request, in file order. -/
def candidates (s : Sudoers) (st : Settings) (r : Request) : List Candidate :=
  candidatesCore (aliasesOf s) (specsOf s) st r

/-- Does a spec require authentication (PASSWD/NOPASSWD tag, else `authenticate`)? -/
def specNeedsAuth (st : Settings) (cs : CmndSpec) : Bool := cs.tags.passwd.getD st.authenticate

def allowedOf (st : Settings) (c : Candidate) : Allowed :=
  { needsAuth := specNeedsAuth st c.spec
    -- `ALL` (written directly in the spec) implies SETENV, like sudo's parser does
    setenv := c.spec.tags.setenv.getD (st.setenv || c.spec.cmnd.atom == .all)
    cwd := c.spec.options.cwd }

/-- `listpw`/`verifypw` over the allowing specs. -/
def pwNeedsAuth (pol : PwPolicy) (st : Settings) (ok : List Candidate) : Bool :=
  match pol with
  | .never => false
  | .always => true
  -- authenticate unless every one is NOPASSWD
  | .all => ok.any (specNeedsAuth st ·.spec)
  -- authenticate unless at least one is NOPASSWD
  | .any => ok.all (specNeedsAuth st ·.spec)

def judgeListing (pol : PwPolicy) (st : Settings) (cands : List Candidate) : Judgement :=
  if (cands.filter (·.allow)).isEmpty then .deny
  else .allow { needsAuth := pwNeedsAuth pol st (cands.filter (·.allow)), setenv := false, cwd := none }

/-- Running a command: the last candidate decides. -/
def judgeRun (st : Settings) (cands : List Candidate) : Judgement :=
  match cands.getLast? with
  | some c => if c.allow then .allow (allowedOf st c) else .deny
  | none => .deny

/-- `listpw` for `-l`, `verifypw` for `-v`. -/
def pwPolicyFor (st : Settings) : Command → PwPolicy
  | .list => st.listpw
  | _ => st.verifypw

def judge (st : Settings) (cmd : Command) (cands : List Candidate) : Judgement :=
  if isRunCmd cmd then judgeRun st cands else judgeListing (pwPolicyFor st cmd) st cands

/-- Decide a request. Callers must have checked the policy with `validate`. -/
def evaluate (s : Sudoers) (st : Settings) (r : Request) : Judgement :=
  judge st r.command (candidates s st r)

/-! ## Static checks -/

def userAliasRefs (l : List (Member UserAtom)) : List String :=
  l.filterMap fun m => UserAtom.aliasName m.atom
def hostAliasRefs (l : List (Member HostAtom)) : List String :=
  l.filterMap fun m => HostAtom.aliasName m.atom
def cmndAliasRefs (l : List (Member CmndAtom)) : List String :=
  l.filterMap fun m => CmndAtom.aliasName m.atom

/-- Alias references by kind: (user, runas, host, cmnd). -/
structure Refs where
  user : List String := []
  runas : List String := []
  host : List String := []
  cmnd : List String := []

def Refs.append (a b : Refs) : Refs :=
  ⟨a.user ++ b.user, a.runas ++ b.runas, a.host ++ b.host, a.cmnd ++ b.cmnd⟩

def runasSpecRefs : Option RunasSpec → List String
  | none => []
  | some ⟨us, gs⟩ => (us.map userAliasRefs).getD [] ++ (gs.map userAliasRefs).getD []

def entryRefs : Entry → Refs
  | .userAlias _ ms => { user := userAliasRefs ms }
  | .runasAlias _ ms => { runas := userAliasRefs ms }
  | .hostAlias _ ms => { host := hostAliasRefs ms }
  | .cmndAlias _ ms => { cmnd := cmndAliasRefs ms }
  | .defaults (.host hs) _ => { host := hostAliasRefs hs }
  | .defaults (.user us) _ => { user := userAliasRefs us }
  | .defaults (.runas rs) _ => { runas := userAliasRefs rs }
  | .defaults (.cmnd cs) _ => { cmnd := cmndAliasRefs cs }
  | .defaults .global _ => {}
  | .userSpec us =>
    { user := userAliasRefs us.users
      host := us.entries.flatMap (hostAliasRefs ·.hosts)
      runas := us.entries.flatMap fun hc => hc.cmnds.flatMap (runasSpecRefs ·.runas)
      cmnd := us.entries.flatMap fun hc => hc.cmnds.flatMap fun cs => cmndAliasRefs [cs.cmnd] }
  | .include _ | .includeDir _ => {}

/-- First name occurring twice. -/
def firstDup : List String → Option String
  | [] => none
  | n :: ns => if ns.contains n then some n else firstDup ns

/-- Names reachable from `start` by following alias references (bounded). -/
def closure (refs : String → List String) : Nat → List String → List String
  | 0, acc => acc
  | f + 1, acc =>
    let nxt := ((acc.flatMap refs).filter (fun x => !acc.contains x)).eraseDups
    if nxt.isEmpty then acc else closure refs f (acc ++ nxt)

def firstCycle {α : Type} (defs : List (String × List (Member α))) (refsOf : List (Member α) → List String) :
    Option String :=
  let refs := fun n => ((lookupAlias defs n).map refsOf).getD []
  (defs.find? fun (n, ms) => (closure refs (defs.length + 1) (refsOf ms)).contains n).map (·.1)

def checkKind {α : Type} (kind : String) (defs : List (String × List (Member α)))
    (refsOf : List (Member α) → List String) (used : List String) : Except String Unit := do
  if let some n := firstDup (defs.map (·.1)) then
    throw s!"duplicate {kind} \"{n}\""
  if let some n := used.find? (fun n => (lookupAlias defs n).isNone) then
    throw s!"{kind} \"{n}\" referenced but not defined"
  if let some n := firstCycle defs refsOf then
    throw s!"cycle in {kind} \"{n}\""

/-- Reject duplicate alias names, references to undefined aliases and alias cycles
(sudo's/visudo's alias checks). Must pass before `evaluate`/`resolveDefaults` are used. -/
def validate (s : Sudoers) : Except String Unit := do
  let al := aliasesOf s
  let refs : Refs := s.foldl (fun (acc : Refs) e => acc.append (entryRefs e)) {}
  checkKind "User_Alias" al.user userAliasRefs refs.user
  checkKind "Runas_Alias" al.runas userAliasRefs refs.runas
  checkKind "Host_Alias" al.host hostAliasRefs refs.host
  checkKind "Cmnd_Alias" al.cmnd cmndAliasRefs refs.cmnd

end LeanSudo.Policy
