import LeanSudo.Policy.Types
import LeanSudo.Util.Glob

namespace LeanSudo.Policy

open LeanSudo.Sudoers
open LeanSudo.Glob (fnmatch hasGlob)

def matchList {α : Type} (m : α → Option Bool) : List (Member α) → Option Bool
  | [] => none
  | x :: xs =>
    match matchList m xs with
    | some b => some b
    | none => (m x.atom).map (fun b => b != x.negated)

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

def Aliases.fuel (a : Aliases) : Nat :=
  a.user.length + a.runas.length + a.host.length + a.cmnd.length + 1

def specsOf : Sudoers → List UserSpec
  | [] => []
  | .userSpec u :: es => u :: specsOf es
  | _ :: es => specsOf es

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

def nameEq (foldCase : Bool) (a b : String) : Bool :=
  if foldCase then a.toLower == b.toLower else a == b

def netgroupMatch (st : Settings) (facts : Option Request) (n : String)
    (user host : Option String) : Bool :=
  st.useNetgroups && (facts.any fun r =>
    r.netgroups.any fun (ng, u, h, yes) =>
      ng == n && u == user && (h == host || (host.isSome && h == some r.host)) && yes)

def pluginGroupMatch (st : Settings) (facts : Option Request) (user group : String) : Bool :=
  st.groupPlugin.isSome && facts.any (fun r =>
    r.pluginGroups.any fun (u, g, yes) => u == user && g == group && yes)

theorem pluginGroupMatch_requires_yes (st : Settings) (facts : Option Request)
    (user group : String) (h : pluginGroupMatch st facts user group = true) :
    ∃ r, facts = some r ∧ (user, group, true) ∈ r.pluginGroups := by
  cases facts with
  | none => simp [pluginGroupMatch] at h
  | some r =>
    simp only [pluginGroupMatch, Option.any_some, Bool.and_eq_true] at h
    obtain ⟨⟨u, g, yes⟩, hm, he⟩ := List.any_eq_true.mp h.2
    simp only [Bool.and_eq_true, beq_iff_eq] at he
    rcases he with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨r, rfl, hm⟩

def userBase (p : Principal) (st : Settings) (facts : Option Request) : UserAtom → Bool
  | .all => true
  | .name n => nameEq st.caseInsensitiveUser n p.name
  | .id n => n == p.uid
  | .group n => p.groups.any (fun g => nameEq st.caseInsensitiveGroup n g.1) ||
      (st.alwaysQueryGroupPlugin && pluginGroupMatch st facts p.name n)
  | .gid n => n == p.gid || p.groups.any (·.2 == n) ||
      (st.alwaysQueryGroupPlugin && pluginGroupMatch st facts p.name ("#" ++ toString n))
  | .nonunixGroup n => pluginGroupMatch st facts p.name n
  | .nonunixGid n => pluginGroupMatch st facts p.name ("#" ++ toString n)
  | .netgroup n => netgroupMatch st facts n (some p.name)
      (if st.netgroupTuple then facts.map (fun r => if r.lhost.isEmpty then r.host else r.lhost) else none)
  | _ => false

def groupBase (g : GroupInfo) (st : Settings) : UserAtom → Bool
  | .all => true
  | .name n => nameEq st.caseInsensitiveGroup n g.name
  | .id n => n == g.gid
  | _ => false

def maskedEq (a b mask : IpAddr) : Bool :=
  match a, b, mask with
  | .v4 a, .v4 b, .v4 m | .v6 a, .v6 b, .v6 m =>
    a.length == b.length && a.length == m.length &&
      ((a.zip b).zip m).all (fun ((x, y), z) => x &&& z == y &&& z)
  | _, _, _ => false

def maskedAddress (ip mask : IpAddr) : Option IpAddr :=
  match ip, mask with
  | .v4 a, .v4 m => if a.length == 4 && m.length == 4 then
      some (.v4 ((a.zip m).map (fun (x, y) => x &&& y))) else none
  | .v6 a, .v6 m => if a.length == 16 && m.length == 16 then
      some (.v6 ((a.zip m).map (fun (x, y) => x &&& y))) else none
  | _, _ => none

def networkMatches (interfaces : List (IpAddr × IpAddr)) (addr mask : IpAddr) : Bool :=
  let implicitMask := match mask with
    | .v4 [] | .v6 [] => true
    | _ => false
  interfaces.any fun (ip, localMask) =>
    if implicitMask then ip == addr || maskedAddress ip localMask == some addr
    else maskedEq ip addr mask

def hostBase (host : String) (st : Settings) (facts : Option Request) : HostAtom → Bool
  | .all => true
  | .name n =>
    let h := if n.contains '.' then
      (facts.map (fun r => if r.lhost.isEmpty then host else r.lhost)).getD host else host
    if hasGlob n then fnmatch n h false true else n.toLower == h.toLower
  | .netgroup n => netgroupMatch st facts n
      (if st.netgroupTuple then facts.map (·.user.name) else none)
      (some ((facts.map (fun r => if r.lhost.isEmpty then host else r.lhost)).getD host))
  | .network addr mask => facts.any fun r => networkMatches r.interfaces addr mask
  | _ => false

def userListResult (al : Aliases) (fuel : Nat) (p : Principal) (l : List (Member UserAtom))
    (st : Settings) (facts : Option Request) : Option Bool :=
  matchList (atomMatches UserAtom.aliasName al.user (userBase p st facts) fuel) l

def userListOk (al : Aliases) (fuel : Nat) (p : Principal) (l : List (Member UserAtom))
    (st : Settings) (facts : Option Request) : Bool :=
  userListResult al fuel p l st facts == some true

def hostListOk (al : Aliases) (fuel : Nat) (host : String) (l : List (Member HostAtom))
    (st : Settings) (facts : Option Request) : Bool :=
  matchList (atomMatches HostAtom.aliasName al.host (hostBase host st facts) fuel) l == some true

def runasUserResult (al : Aliases) (fuel : Nat) (t : Principal) (l : List (Member UserAtom))
    (st : Settings) (facts : Option Request) : Option Bool :=
  matchList (atomMatches UserAtom.aliasName al.runas (fun a =>
    if a == .myself then facts.any (fun r => t.name == r.user.name)
    else userBase t st facts a) fuel) l

def runasGroupResult (al : Aliases) (fuel : Nat) (g : GroupInfo) (l : List (Member UserAtom))
    (st : Settings) : Option Bool :=
  matchList (atomMatches UserAtom.aliasName al.runas (groupBase g st) fuel) l

def isRunasDefault (st : Settings) (t : Principal) : Bool :=
  match st.runasDefault.toList with
  | '#' :: ds =>
    match (String.ofList ds).toNat? with
    | some n => n == t.uid
    | none => false
  | _ => nameEq st.caseInsensitiveUser st.runasDefault t.name

def runasGroupOk (al : Aliases) (fuel : Nat) (r : Request) (gs : Option (List (Member UserAtom)))
    (st : Settings) : Bool :=
  match r.runasGroup with
  | none => true
  | some g =>
    let p := if st.preserveGroups then r.user else r.runasUser
    let fallback := g.gid == r.runasUser.gid || p.groups.any (·.2 == g.gid)
    let result := gs.bind (groupResult g fallback fuel)
    result.getD fallback
where
  groupResult (g : GroupInfo) (fallback : Bool) : Nat → List (Member UserAtom) → Option Bool
    | fuel, ms =>
      let result := matchList (fun a =>
        match a with
        | .alias n =>
          match fuel with
          | 0 => none
          | f + 1 => (lookupAlias al.runas n).bind (groupResult g fallback f)
        | _ => if groupBase g st a then some true else none) ms
      result.orElse (fun _ => if fallback then some true else none)

def runasOk (al : Aliases) (fuel : Nat) (st : Settings) (r : Request) (rs : Option RunasSpec) : Bool :=
  let (userResult, gs) := match rs with
    | none =>
      (if isRunasDefault st r.runasUser then some true else none, none)
    | some ⟨some us, gs⟩ => (runasUserResult al fuel r.runasUser us st (some r), gs)
    | some ⟨none, gs⟩ =>
      (if r.runasUser.name == r.user.name then some true else none, gs)
  match userResult with
  | some true => runasGroupOk al fuel r gs st
  | some false => false
  | none =>
    match r.runasGroup with
    | none => false
    | some g =>
      r.runasUser.name == r.user.name &&
        (gs.bind (fun ms => runasGroupResult al fuel g ms st) == some true)

def endsWithSlash (p : String) : Bool := p.toList.getLast? == some '/'

def dropLastChar (p : String) : String := String.ofList p.toList.dropLast

def regexMatch (facts : Option Request) (pattern subject : String) : Bool :=
  facts.any fun r => r.regexMatches.any fun (p, s, yes) => p == pattern && s == subject && yes

def argsMatch (pathname : Bool) (a : CmndArgs) (args : List String)
    (facts : Option Request) : Bool :=
  match a with
  | .any => true
  | .none => args.isEmpty
  | .pattern q => fnmatch q (" ".intercalate args) pathname
  | .regex q => regexMatch facts q (" ".intercalate args)

def fileIdMatch (fallback : Bool) (facts : Option Request) (p path : String) : Bool :=
  match facts with
  | none => p == path
  | some r =>
    match r.fileIds.find? (·.1 == p), r.fileIds.find? (·.1 == path) with
    | some (_, d, i), some (_, d', i') => d == d' && i == i'
    | _, _ => fallback && p == path

def sameFile := fileIdMatch false

def literalFileMatches := fileIdMatch true

def pathNamesMatch (canon : String → String) (p path : String) : Bool :=
  baseOf p == baseOf path && canon (dirOf p) == canon (dirOf path)

def literalPathMatches (canon : String → String) (facts : Option Request) (p path : String) : Bool :=
  pathNamesMatch canon p path && literalFileMatches facts p path

def directoryMatches (canon : String → String) (facts : Option Request) (p path : String) : Bool :=
  canon (if p == "/" then "/" else dropLastChar p) == canon (dirOf path) &&
    sameFile facts (p ++ baseOf path) path

def pathMatches (canon : String → String) (p path _canonical : String)
    (facts : Option Request) : Bool :=
  if hasGlob p then
    if facts.any (·.fastGlob) then
      (fnmatch p path true || fnmatch p (canon (dirOf path) ++ "/" ++ baseOf path) true) &&
        sameFile facts path path
    else
      facts.any fun r =>
        ((r.globPaths.find? (·.1 == p)).map (·.2)).getD [] |>.any fun q =>
          if endsWithSlash q then directoryMatches canon facts q path
          else pathNamesMatch canon q path && sameFile facts q path
  else if endsWithSlash p then directoryMatches canon facts p path
  else literalPathMatches canon facts p path

def digestMatches (a b : Digest) : Bool := a.algo == b.algo && a.bytes == b.bytes

def isPseudoAtom : CmndAtom → Bool
  | .list | .sudoedit _ => true
  | _ => false

def cmndBase (canon : String → String) (cmd : Command) (atom : CmndAtom)
    (facts : Option Request) : Bool :=
  match atom with
  | .digest ds atom =>
      (isPseudoAtom atom || ds.any (fun d => facts.any (fun r => r.digests.any (digestMatches d)))) &&
        cmndBase canon cmd atom facts
  | .all => match cmd with
    | .run _ _ _ | .sudoedit _ | .checkList => true
    | _ => false
  | .list => cmd == .checkList
  | .command p a => match cmd with
    | .run path canonical args => pathMatches canon p path canonical facts && argsMatch false a args facts
    | _ => false
  | .commandRegex re a => match cmd with
    | .run path _ args =>
      (regexMatch facts re path ||
        regexMatch facts re (canon (dirOf path) ++ "/" ++ baseOf path)) &&
        sameFile facts path path && argsMatch false a args facts
    | _ => false
  | .sudoedit a => match cmd with
    | .sudoedit files => argsMatch true a files facts
    | _ => false
  | .alias _ => false

def cmndListResult (al : Aliases) (fuel : Nat) (canon : String → String) (cmd : Command)
    (l : List (Member CmndAtom)) (facts : Option Request) : Option Bool :=
  matchList (atomMatches CmndAtom.aliasName al.cmnd (fun a => cmndBase canon cmd a facts) fuel) l

def cmndMemberResult (al : Aliases) (fuel : Nat) (canon : String → String) (cmd : Command)
    (m : Member CmndAtom) (facts : Option Request) : Option Bool :=
  cmndListResult al fuel canon cmd [m] facts

def cmndUsesDigest (al : Aliases) (r : Request) : Nat → CmndAtom → Bool
  | _, .digest _ atom => !isPseudoAtom atom
  | 0, _ => false
  | fuel + 1, .alias name =>
    let members := (lookupAlias al.cmnd name).getD []
    let last := members.reverse.find? fun m =>
      (cmndMemberResult al fuel r.canon r.command m (some r)).isSome
    last.any (fun m => cmndUsesDigest al r fuel m.atom)
  | _ + 1, _ => false

def isRunCmd : Command → Bool
  | .run _ _ _ | .sudoedit _ | .checkList => true
  | .list | .validate => false

def specRoot (r : Request) (cs : CmndSpec) : Option (Option String) :=
  match r.command with
  | .sudoedit _ => some none
  | _ =>
    match r.requestedChroot with
    | some root =>
      if cs.options.chroot.any (fun p => p != "*" && p != root) then none
      else some (some root)
    | none =>
      match cs.options.chroot with
      | some root => some (some root)
      | none => some (r.defaultChroot.filter (· != "*"))

def rootedCommand (command : Command) (facts : RootCommandFacts) : Command :=
  match command, facts.command with
  | .run _ _ args, .run path canonical _ => .run path canonical args
  | command, _ => command

def rootCanon (facts : RootCommandFacts) (path : String) : String :=
  ((facts.canonPaths.find? (·.1 == path)).map (·.2)).getD path

def withRootFacts (r : Request) (facts : RootCommandFacts) : Request :=
  { r with
    command := rootedCommand r.command facts, canon := rootCanon facts,
    toCommandFacts := facts.toCommandFacts }

def specRequest (r : Request) (cs : CmndSpec) : Option Request :=
  match specRoot r cs with
  | none => none
  | some none => some r
  | some (some root) =>
    (r.rootFacts.find? (·.1 == root)).map (fun (_, facts) => withRootFacts r facts)

def rootExecutionPath (r : Request) (facts : RootCommandFacts) : String :=
  match rootedCommand r.command facts with
  | .run path _ _ =>
    let parent := rootCanon facts (dirOf path)
    parent ++ (if parent.endsWith "/" then "" else "/") ++ baseOf path
  | _ => ""

def specSelection (r : Request) (cs : CmndSpec) : Option CommandSelection := do
  if !isRunCmd r.command then none else
  let root ← (specRoot r cs).bind id
  let (_, facts) ← r.rootFacts.find? (·.1 == root)
  pure
    { root := root
      command := rootedCommand r.command facts
      executionPath := rootExecutionPath r facts
      argv := facts.argv
      found := facts.found
      execFd := facts.execFd
      refusal := facts.refusal
      setid := facts.setid }

def specCmndResult (al : Aliases) (fuel : Nat) (r : Request) (cs : CmndSpec) : Option Bool :=
  match specRoot r cs with
  | none => none
  | some _ =>
    match specRequest r cs with
    | none => some false
    | some selected =>
      cmndMemberResult al fuel selected.canon selected.command cs.cmnd (some selected)

def specUsesDigest (al : Aliases) (fuel : Nat) (r : Request) (cs : CmndSpec) : Bool :=
  isRunCmd r.command && (specRequest r cs).any (fun selected =>
    cmndUsesDigest al selected fuel cs.cmnd.atom)

structure Candidate where
  spec : CmndSpec
  allow : Bool
  usesDigest : Bool := false
  selection : Option CommandSelection := none
  deriving Repr, BEq, Inhabited

def resolveTimeBound (localTimeBounds : List (Nat × Nat)) (localTime : Bool)
    (n : Nat) : Option Nat :=
  if localTime then (localTimeBounds.find? (·.1 == n)).map (·.2) else some n

def inTimeWindow (now : Nat) (cs : CmndSpec) (localTimeBounds : List (Nat × Nat)) : Bool :=
  cs.options.notBefore.all (fun n =>
    (resolveTimeBound localTimeBounds cs.options.notBeforeLocal n).any (· ≤ now)) &&
  cs.options.notAfter.all (fun n =>
    (resolveTimeBound localTimeBounds cs.options.notAfterLocal n).any (now ≤ ·))

def specApplies (al : Aliases) (fuel : Nat) (st : Settings) (r : Request) (cs : CmndSpec) : Bool :=
  !isRunCmd r.command || (inTimeWindow r.now cs r.localTimeBounds &&
    (runasOk al fuel st r cs.runas && (specCmndResult al fuel r cs).isSome))

def specAllow (al : Aliases) (fuel : Nat) (r : Request) (cs : CmndSpec) : Bool :=
  if isRunCmd r.command then (specCmndResult al fuel r cs).getD false
  else true

def candidateOf (al : Aliases) (fuel : Nat) (r : Request) (cs : CmndSpec) : Candidate :=
  ⟨cs, specAllow al fuel r cs, specUsesDigest al fuel r cs, specSelection r cs⟩

def hcCandidates (al : Aliases) (fuel : Nat) (st : Settings) (r : Request) (hc : HostCmnds) :
    List Candidate :=
  if hostListOk al fuel r.host hc.hosts st (some r) then
    (hc.cmnds.filter (specApplies al fuel st r)).map (candidateOf al fuel r)
  else []

def usCandidates (al : Aliases) (fuel : Nat) (st : Settings) (r : Request) (us : UserSpec) :
    List Candidate :=
  if userListOk al fuel r.user us.users st (some r) then us.entries.flatMap (hcCandidates al fuel st r) else []

def candidatesCore (al : Aliases) (specs : List UserSpec) (st : Settings) (r : Request) :
    List Candidate :=
  specs.flatMap (usCandidates al al.fuel st r)

def candidates (s : Sudoers) (st : Settings) (r : Request) : List Candidate :=
  candidatesCore (aliasesOf s) (specsOf s) st r

def specNeedsAuth (st : Settings) (cs : CmndSpec) : Bool := cs.tags.passwd.getD st.authenticate

def commandImpliesSetenv : CmndAtom → Bool
  | .all => true
  | .digest _ atom => commandImpliesSetenv atom
  | _ => false

def allowedOf (st : Settings) (c : Candidate) : Allowed :=
  { needsAuth := specNeedsAuth st c.spec
    setenv := c.spec.tags.setenv.getD (st.setenv || commandImpliesSetenv c.spec.cmnd.atom)
    toTagEffects := c.spec.tags.toTagEffects
    toExecutionOptions := c.spec.options.toExecutionOptions
    usesDigest := c.usesDigest
    selection := c.selection }

def pwNeedsAuth (pol : PwPolicy) (st : Settings) (ok : List Candidate) : Bool :=
  match pol with
  | .never => false
  | .always => true
  | .all => ok.any (specNeedsAuth st ·.spec)
  | .any => ok.all (specNeedsAuth st ·.spec)

def judgeListing (pol : PwPolicy) (st : Settings) (cands : List Candidate) : Judgement :=
  if (cands.filter (·.allow)).isEmpty then .deny
  else .allow { needsAuth := pwNeedsAuth pol st (cands.filter (·.allow)), setenv := false, cwd := none }

def judgeRun (st : Settings) (cands : List Candidate) : Judgement :=
  match cands.getLast? with
  | some c => if c.allow then .allow (allowedOf st c) else .deny
  | none => .deny

def pwPolicyFor (st : Settings) : Command → PwPolicy
  | .list => st.listpw
  | _ => st.verifypw

def judge (st : Settings) (cmd : Command) (cands : List Candidate) : Judgement :=
  if isRunCmd cmd then judgeRun st cands else judgeListing (pwPolicyFor st cmd) st cands

def evaluate (s : Sudoers) (st : Settings) (r : Request) : Judgement :=
  judge st r.command (candidates s st r)

def listingRunasResult (al : Aliases) (st : Settings) (r : Request) (p : Principal)
    (cs : CmndSpec) : Option Bool :=
  match cs.runas with
  | some ⟨some us, _⟩ =>
    matchList (atomMatches UserAtom.aliasName al.runas (userBase p st (some r)) al.fuel) us
  | none | some ⟨none, none⟩ => if isRunasDefault st p then some true else none
  | _ => none

def canListOther (s : Sudoers) (st : Settings) (r : Request) (other root : Principal) : Bool :=
  if r.user.uid == 0 || r.user.uid == other.uid then true else
  let al := aliasesOf s
  let specs := (specsOf s).flatMap fun us =>
    if userListOk al al.fuel r.user us.users st (some r) then
      us.entries.flatMap fun hc =>
        if hostListOk al al.fuel r.host hc.hosts st (some r) then hc.cmnds else []
    else []
  let results := specs.filterMap fun cs =>
    if !inTimeWindow r.now cs r.localTimeBounds then none else
    let base := match listingRunasResult al st r other cs with
      | some true => some (fun a => cmndBase r.canon .checkList a (some r))
      | some false => none
      | none => if listingRunasResult al st r root cs == some true then
          some (fun a => a == CmndAtom.all)
        else none
    base.bind fun base =>
      matchList (atomMatches CmndAtom.aliasName al.cmnd base al.fuel) [cs.cmnd]
  results.getLast?.getD false

def userAliasRefs (l : List (Member UserAtom)) : List String :=
  l.filterMap fun m => UserAtom.aliasName m.atom
def hostAliasRefs (l : List (Member HostAtom)) : List String :=
  l.filterMap fun m => HostAtom.aliasName m.atom
def cmndAliasRefs (l : List (Member CmndAtom)) : List String :=
  l.filterMap fun m => CmndAtom.aliasName m.atom

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

def firstDup : List String → Option String
  | [] => none
  | n :: ns => if ns.contains n then some n else firstDup ns

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

def validate (s : Sudoers) : Except String Unit := do
  let al := aliasesOf s
  let refs : Refs := s.foldl (fun (acc : Refs) e => acc.append (entryRefs e)) {}
  checkKind "User_Alias" al.user userAliasRefs refs.user
  checkKind "Runas_Alias" al.runas userAliasRefs refs.runas
  checkKind "Host_Alias" al.host hostAliasRefs refs.host
  checkKind "Cmnd_Alias" al.cmnd cmndAliasRefs refs.cmnd

end LeanSudo.Policy
