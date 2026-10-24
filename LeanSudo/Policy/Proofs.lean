import LeanSudo.Policy.Eval

/-!
# Policy theorems

Properties of `LeanSudo.Policy.evaluate`, stated in terms of the matching functions of
`LeanSudo.Policy.Eval`:

1. `evaluate_nil` — default deny on the empty policy;
2. `evaluate_sound` / `evaluate_sound_run` — an allow is backed by a user spec in the
   policy whose user, host and command conditions match; for run requests the
   command member's tri-state result allows, the *last* matching spec decides,
   and its permissions are used;
3. `evaluate_no_user_match` — no user spec matches the invoking user ⇒ deny;
4. `evaluate_append_negated`, `evaluate_append_deny_all` — last match wins: a final
   matching negated rule denies;
5. `evaluate_noauth_run`, `evaluate_noauth_listing` — no authentication only through
   `NOPASSWD`/`!authenticate` (or `listpw`/`verifypw=never`);
6. `evaluate_irrelevant`, `evaluate_congr` — entries other than aliases and user specs
   (Defaults, includes) do not influence the judgement;
7. `pathMatches_literal_basename`, `cmndBase_literal_basename` — a literal sudoers
   path never matches a command with a different basename (multicall binaries).
-/

namespace LeanSudo.Policy

open LeanSudo.Sudoers

/-- All match conditions for a (user spec, host entry, command spec) triple. -/
def SpecMatches (s : Sudoers) (st : Settings) (r : Request) (us : UserSpec) (hc : HostCmnds)
    (cs : CmndSpec) : Prop :=
  userListOk (aliasesOf s) (aliasesOf s).fuel r.user us.users = true ∧
  hostListOk (aliasesOf s) (aliasesOf s).fuel r.host hc.hosts = true ∧
  specApplies (aliasesOf s) (aliasesOf s).fuel st r cs = true

/-! ## Structural lemmas -/

theorem mem_specsOf {s : Sudoers} {us : UserSpec} : us ∈ specsOf s ↔ Entry.userSpec us ∈ s := by
  induction s with
  | nil => simp [specsOf]
  | cons e es ih =>
    cases e <;> simp [specsOf, ih, eq_comm]

theorem mem_hcCandidates {al : Aliases} {f : Nat} {st : Settings} {r : Request} {hc : HostCmnds}
    {c : Candidate} :
    c ∈ hcCandidates al f st r hc ↔ hostListOk al f r.host hc.hosts = true ∧
      ∃ cs, cs ∈ hc.cmnds ∧ specApplies al f st r cs = true ∧ c = ⟨cs, specAllow al f r cs⟩ := by
  unfold hcCandidates
  by_cases h : hostListOk al f r.host hc.hosts = true
  · simp only [h, ↓reduceIte, true_and]
    constructor
    · intro hm
      obtain ⟨cs, hcs, rfl⟩ := List.mem_map.mp hm
      obtain ⟨hcs, ha⟩ := List.mem_filter.mp hcs
      exact ⟨cs, hcs, ha, rfl⟩
    · rintro ⟨cs, hcs, ha, rfl⟩
      exact List.mem_map.mpr ⟨cs, List.mem_filter.mpr ⟨hcs, ha⟩, rfl⟩
  · simp [h]

theorem mem_usCandidates {al : Aliases} {f : Nat} {st : Settings} {r : Request} {us : UserSpec}
    {c : Candidate} :
    c ∈ usCandidates al f st r us ↔ userListOk al f r.user us.users = true ∧
      ∃ hc, hc ∈ us.entries ∧ c ∈ hcCandidates al f st r hc := by
  unfold usCandidates
  by_cases h : userListOk al f r.user us.users = true
  · simp only [h, ↓reduceIte, true_and, List.mem_flatMap]
  · simp [h]

theorem mem_candidates {s : Sudoers} {st : Settings} {r : Request} {c : Candidate} :
    c ∈ candidates s st r ↔
      ∃ us hc cs, Entry.userSpec us ∈ s ∧ hc ∈ us.entries ∧ cs ∈ hc.cmnds ∧
        SpecMatches s st r us hc cs ∧ c = ⟨cs, specAllow (aliasesOf s) (aliasesOf s).fuel r cs⟩ := by
  simp only [candidates, candidatesCore, List.mem_flatMap]
  constructor
  · rintro ⟨us, hus, hmem⟩
    obtain ⟨hu, hc, hhc, hmem⟩ := mem_usCandidates.mp hmem
    obtain ⟨hh, cs, hcs, ha, rfl⟩ := mem_hcCandidates.mp hmem
    exact ⟨us, hc, cs, mem_specsOf.mp hus, hhc, hcs, ⟨hu, hh, ha⟩, rfl⟩
  · rintro ⟨us, hc, cs, hus, hhc, hcs, ⟨hu, hh, ha⟩, rfl⟩
    exact ⟨us, mem_specsOf.mpr hus,
      mem_usCandidates.mpr ⟨hu, hc, hhc, mem_hcCandidates.mpr ⟨hh, cs, hcs, ha, rfl⟩⟩⟩

theorem judge_run {st : Settings} {cmd : Command} {cands : List Candidate}
    (h : isRunCmd cmd = true) : judge st cmd cands = judgeRun st cands := by
  simp [judge, h]

theorem judge_listing {st : Settings} {cmd : Command} {cands : List Candidate}
    (h : isRunCmd cmd = false) :
    judge st cmd cands = judgeListing (pwPolicyFor st cmd) st cands := by
  simp [judge, h]

theorem specApplies_run {al : Aliases} {f : Nat} {st : Settings} {r : Request} {cs : CmndSpec}
    (h : isRunCmd r.command = true) :
    specApplies al f st r cs =
      (runasOk al f st r cs.runas && (cmndMemberResult al f r.canon r.command cs.cmnd).isSome) := by
  simp [specApplies, h]

theorem judge_nil (st : Settings) (cmd : Command) : judge st cmd [] = .deny := by
  cases cmd <;> rfl

theorem judgeRun_allow {st : Settings} {cands : List Candidate} {a : Allowed}
    (h : judgeRun st cands = .allow a) :
    ∃ c, cands.getLast? = some c ∧ c.allow = true ∧ a = allowedOf st c := by
  unfold judgeRun at h
  cases hc : cands.getLast? with
  | none => rw [hc] at h; cases h
  | some c =>
    rw [hc] at h
    by_cases ha : c.allow = true
    · simp only [ha, ↓reduceIte, Judgement.allow.injEq] at h
      exact ⟨c, rfl, ha, h.symm⟩
    · simp [ha] at h

theorem judgeListing_allow {pol : PwPolicy} {st : Settings} {cands : List Candidate} {a : Allowed}
    (h : judgeListing pol st cands = .allow a) :
    cands.filter (·.allow) ≠ [] ∧ a.needsAuth = pwNeedsAuth pol st (cands.filter (·.allow)) := by
  unfold judgeListing at h
  split at h
  · cases h
  · rename_i hne
    cases h
    exact ⟨fun h0 => hne (by rw [h0]; rfl), rfl⟩

/-- An allow always comes from an allowing candidate. -/
theorem judge_allow_mem {st : Settings} {cmd : Command} {cands : List Candidate} {a : Allowed}
    (h : judge st cmd cands = .allow a) : ∃ c ∈ cands, c.allow = true := by
  cases hr : isRunCmd cmd
  · rw [judge_listing hr] at h
    obtain ⟨hne, _⟩ := judgeListing_allow h
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨hc, hca⟩ := List.mem_filter.mp hc
    exact ⟨c, hc, by simpa using hca⟩
  · rw [judge_run hr] at h
    obtain ⟨c, hc, hca, _⟩ := judgeRun_allow h
    exact ⟨c, List.mem_of_getLast? hc, hca⟩

/-! ## (1) Default deny -/

theorem evaluate_nil (st : Settings) (r : Request) : evaluate [] st r = .deny := by
  simp [evaluate, candidates, specsOf, candidatesCore, judge_nil]

/-! ## (3) No matching user spec ⇒ deny -/

theorem evaluate_no_user_match {s : Sudoers} {st : Settings} {r : Request}
    (h : ∀ us, Entry.userSpec us ∈ s →
      userListOk (aliasesOf s) (aliasesOf s).fuel r.user us.users = false) :
    evaluate s st r = .deny := by
  have : candidates s st r = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro c hc
    obtain ⟨us, _, _, hus, _, _, ⟨hu, _⟩, _⟩ := mem_candidates.mp hc
    simp [h us hus] at hu
  simp [evaluate, this, judge_nil]

/-! ## (2) Soundness -/

/-- Every allow is backed by an allowing spec: command semantics for run requests,
syntactic negation for listing/validation. -/
theorem evaluate_sound {s : Sudoers} {st : Settings} {r : Request} {a : Allowed}
    (h : evaluate s st r = .allow a) :
    ∃ us hc cs, Entry.userSpec us ∈ s ∧ hc ∈ us.entries ∧ cs ∈ hc.cmnds ∧
      SpecMatches s st r us hc cs ∧
      (if isRunCmd r.command then
        cmndMemberResult (aliasesOf s) (aliasesOf s).fuel r.canon r.command cs.cmnd = some true
       else cs.cmnd.negated = false) := by
  obtain ⟨c, hc, hca⟩ := judge_allow_mem h
  obtain ⟨us, hcm, cs, hus, hhc, hcs, hm, rfl⟩ := mem_candidates.mp hc
  refine ⟨us, hcm, cs, hus, hhc, hcs, hm, ?_⟩
  cases hr : isRunCmd r.command <;> simp [specAllow, hr] at hca ⊢
  · exact hca
  · cases he : cmndMemberResult (aliasesOf s) (aliasesOf s).fuel r.canon r.command cs.cmnd <;>
      simp_all

/-- For a run request (command or sudoedit), the allow is decided by the **last**
candidate, whose run-as spec matches and whose command member result allows;
permissions are taken from it. -/
theorem evaluate_sound_run {s : Sudoers} {st : Settings} {r : Request} {a : Allowed}
    (hrun : isRunCmd r.command = true) (h : evaluate s st r = .allow a) :
    ∃ c, (candidates s st r).getLast? = some c ∧ c.allow = true ∧ a = allowedOf st c ∧
      ∃ us hc, Entry.userSpec us ∈ s ∧ hc ∈ us.entries ∧ c.spec ∈ hc.cmnds ∧
        userListOk (aliasesOf s) (aliasesOf s).fuel r.user us.users = true ∧
        hostListOk (aliasesOf s) (aliasesOf s).fuel r.host hc.hosts = true ∧
        runasOk (aliasesOf s) (aliasesOf s).fuel st r c.spec.runas = true ∧
        cmndMemberResult (aliasesOf s) (aliasesOf s).fuel r.canon r.command c.spec.cmnd = some true := by
  unfold evaluate at h
  rw [judge_run hrun] at h
  obtain ⟨c, hc, hca, rfl⟩ := judgeRun_allow h
  refine ⟨c, hc, hca, rfl, ?_⟩
  obtain ⟨us, hcm, cs, hus, hhc, hcs, ⟨hu, hh, ha⟩, rfl⟩ :=
    mem_candidates.mp (List.mem_of_getLast? hc)
  rw [specApplies_run hrun, Bool.and_eq_true] at ha
  refine ⟨us, hcm, hus, hhc, hcs, hu, hh, ha.1, ?_⟩
  simp only [specAllow, hrun, ↓reduceIte] at hca
  cases he : cmndMemberResult (aliasesOf s) (aliasesOf s).fuel r.canon r.command cs.cmnd <;>
    simp_all

/-- A last candidate whose command member denies makes a run request denied. -/
theorem evaluate_last_deny {s : Sudoers} {st : Settings} {r : Request} {c : Candidate}
    (hrun : isRunCmd r.command = true)
    (hlast : (candidates s st r).getLast? = some c)
    (hdeny : cmndMemberResult (aliasesOf s) (aliasesOf s).fuel r.canon r.command c.spec.cmnd = some false) :
    evaluate s st r = .deny := by
  obtain ⟨us, hc, cs, hus, hhc, hcs, hm, rfl⟩ :=
    mem_candidates.mp (List.mem_of_getLast? hlast)
  simp [evaluate, judge, hrun, judgeRun, hlast, specAllow, hdeny]

/-- A non-negated command alias inherits an internal DENY at the last candidate. -/
theorem evaluate_last_alias_deny {s : Sudoers} {st : Settings} {r : Request}
    {c : Candidate} {name : String} {ms : List (Member CmndAtom)} {f : Nat}
    (hrun : isRunCmd r.command = true)
    (hlast : (candidates s st r).getLast? = some c)
    (hmember : c.spec.cmnd = ⟨false, .alias name⟩)
    (hf : (aliasesOf s).fuel = f + 1)
    (hlookup : lookupAlias (aliasesOf s).cmnd name = some ms)
    (hinner : matchList (atomMatches CmndAtom.aliasName (aliasesOf s).cmnd
      (cmndBase r.canon r.command) f) ms = some false) :
    evaluate s st r = .deny := by
  apply evaluate_last_deny hrun hlast
  simp [cmndMemberResult, cmndListResult, matchList, hmember, hf,
    atomMatches, CmndAtom.aliasName, hlookup, hinner]

theorem matchList_negation {α : Type} (m : α → Option Bool) (a : α) :
    matchList m [⟨true, a⟩] = (m a).map (!·) := by
  simp [matchList]

/-! ## (4) Negation: last match wins -/

theorem aliasesOf_append_userSpec (s : Sudoers) (u : UserSpec) :
    aliasesOf (s ++ [.userSpec u]) = aliasesOf s := by
  induction s with
  | nil => rfl
  | cons e es ih => cases e <;> simp [aliasesOf, ih]

theorem specsOf_append (s t : Sudoers) : specsOf (s ++ t) = specsOf s ++ specsOf t := by
  induction s with
  | nil => rfl
  | cons e es ih => cases e <;> simp [specsOf, ih]

theorem candidates_append_userSpec (s : Sudoers) (st : Settings) (r : Request) (u : UserSpec) :
    candidates (s ++ [.userSpec u]) st r =
      candidates s st r ++ usCandidates (aliasesOf s) (aliasesOf s).fuel st r u := by
  simp [candidates, candidatesCore, aliasesOf_append_userSpec, specsOf_append, specsOf]

/-- Appending a matching rule with a DENY command result denies, including a
DENY inherited from inside an alias. -/
theorem evaluate_append_negated (s : Sudoers) (st : Settings) (r : Request)
    (users : List (Member UserAtom)) (hosts : List (Member HostAtom)) (cs : CmndSpec)
    (hrun : isRunCmd r.command = true)
    (hu : userListOk (aliasesOf s) (aliasesOf s).fuel r.user users = true)
    (hh : hostListOk (aliasesOf s) (aliasesOf s).fuel r.host hosts = true)
    (hra : runasOk (aliasesOf s) (aliasesOf s).fuel st r cs.runas = true)
    (hcm : cmndMemberResult (aliasesOf s) (aliasesOf s).fuel r.canon r.command cs.cmnd = some false) :
    evaluate (s ++ [.userSpec ⟨users, [⟨hosts, [cs]⟩]⟩]) st r = .deny := by
  have happ : specApplies (aliasesOf s) (aliasesOf s).fuel st r cs = true := by
    simp [specApplies_run hrun, hra, hcm]
  have hlast : (candidates (s ++ [.userSpec ⟨users, [⟨hosts, [cs]⟩]⟩]) st r).getLast? =
      some ⟨cs, false⟩ := by
    rw [candidates_append_userSpec]
    simp [usCandidates, hcCandidates, hu, hh, happ, specAllow, hrun, hcm]
  unfold evaluate
  rw [judge_run hrun]
  simp [judgeRun, hlast]

theorem atomMatches_nonAlias {α : Type} (aliasName : α → Option String)
    (defs : List (String × List (Member α))) (base : α → Bool) (f : Nat) (a : α)
    (h : aliasName a = none) :
    atomMatches aliasName defs base f a = (if base a then some true else none) := by
  cases f <;> simp [atomMatches, h]

theorem atomMatches_user_all (defs : List (String × List (Member UserAtom))) (base : UserAtom → Bool)
    (f : Nat) : atomMatches UserAtom.aliasName defs base f .all = (if base .all then some true else none) :=
  atomMatches_nonAlias _ _ _ _ _ rfl

theorem atomMatches_user_name (defs : List (String × List (Member UserAtom))) (base : UserAtom → Bool)
    (f : Nat) (n : String) :
    atomMatches UserAtom.aliasName defs base f (.name n) = (if base (.name n) then some true else none) :=
  atomMatches_nonAlias _ _ _ _ _ rfl

theorem atomMatches_host_all (defs : List (String × List (Member HostAtom))) (base : HostAtom → Bool)
    (f : Nat) : atomMatches HostAtom.aliasName defs base f .all = (if base .all then some true else none) :=
  atomMatches_nonAlias _ _ _ _ _ rfl

/-- Concrete alias body `ALL, !path`: its internal negated last match denies even
when the referencing command member itself is not negated. -/
theorem evaluate_last_alias_negated_path {s : Sudoers} {st : Settings} {r : Request}
    {c : Candidate} {name path : String} {f : Nat}
    (hrun : isRunCmd r.command = true)
    (hlast : (candidates s st r).getLast? = some c)
    (hmember : c.spec.cmnd = ⟨false, .alias name⟩)
    (hf : (aliasesOf s).fuel = f + 1)
    (hlookup : lookupAlias (aliasesOf s).cmnd name =
      some [⟨false, .all⟩, ⟨true, .command path .any⟩])
    (hpath : cmndBase r.canon r.command (.command path .any) = true) :
    evaluate s st r = .deny := by
  apply evaluate_last_alias_deny hrun hlast hmember hf hlookup
  simp [matchList, atomMatches_nonAlias CmndAtom.aliasName _ _ f
    (.command path .any) rfl, hpath]

/-- `<user> ALL = (ALL : ALL) !ALL` -/
def denyAllRule (user : String) : Entry :=
  .userSpec ⟨[⟨false, .name user⟩],
    [⟨[⟨false, .all⟩], [CmndSpec.mk (some ⟨some [⟨false, .all⟩], some [⟨false, .all⟩]⟩) {} {} ⟨true, .all⟩]⟩]⟩

/-- Concrete instance: `<user> ALL = (ALL : ALL) !ALL` appended at the end of any policy
denies every command (and sudoedit) the invoking user could ask for. -/
theorem evaluate_append_deny_all (s : Sudoers) (st : Settings) (r : Request)
    (hrun : isRunCmd r.command = true) :
    evaluate (s ++ [denyAllRule r.user.name]) st r = .deny := by
  apply evaluate_append_negated s st r _ _ _ hrun
  · simp [userListOk, userListResult, matchList, atomMatches_user_name, userBase]
  · simp [hostListOk, matchList, atomMatches_host_all, hostBase]
  · unfold runasOk runasGroupOk
    cases r.runasGroup <;>
      simp [runasUserResult, runasGroupResult, matchList, atomMatches_user_all, userBase, groupBase]
  · simp only [cmndMemberResult, cmndListResult, matchList]
    rw [atomMatches_nonAlias _ _ _ _ _ rfl]
    cases hc : r.command <;> simp_all [isRunCmd, cmndBase]

/-! ## (5) Authentication -/

/-- A run request is allowed without authentication only if the deciding (last) rule
is tagged `NOPASSWD`, or it is untagged and `authenticate` is off. -/
theorem evaluate_noauth_run {s : Sudoers} {st : Settings} {r : Request} {a : Allowed}
    (hrun : isRunCmd r.command = true) (h : evaluate s st r = .allow a)
    (hna : a.needsAuth = false) :
    ∃ c, (candidates s st r).getLast? = some c ∧ c.allow = true ∧
      (c.spec.tags.passwd = some false ∨ (c.spec.tags.passwd = none ∧ st.authenticate = false)) := by
  obtain ⟨c, hc, hca, rfl, _⟩ := evaluate_sound_run hrun h
  refine ⟨c, hc, hca, ?_⟩
  simp only [allowedOf, specNeedsAuth] at hna
  cases hp : c.spec.tags.passwd with
  | none => simp_all
  | some b => simp_all

theorem pwNeedsAuth_false {pol : PwPolicy} {st : Settings} {ok : List Candidate}
    (hne : ok ≠ []) (h : pwNeedsAuth pol st ok = false) :
    pol = .never ∨ ∃ c ∈ ok, specNeedsAuth st c.spec = false := by
  cases pol with
  | never => exact .inl rfl
  | always => simp [pwNeedsAuth] at h
  | all =>
    right
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hne
    simp only [pwNeedsAuth, List.any_eq_false] at h
    exact ⟨c, hc, by simpa using h c hc⟩
  | any =>
    right
    simp only [pwNeedsAuth, List.all_eq_false] at h
    obtain ⟨c, hc, hn⟩ := h
    exact ⟨c, hc, by simpa using hn⟩

/-- `-l`/`-v` are allowed without authentication only if the applicable `listpw`/
`verifypw` is `never`, or some allowing spec is NOPASSWD (or untagged with
`!authenticate`). -/
theorem evaluate_noauth_listing {s : Sudoers} {st : Settings} {r : Request} {a : Allowed}
    (hl : isRunCmd r.command = false) (h : evaluate s st r = .allow a)
    (hna : a.needsAuth = false) :
    pwPolicyFor st r.command = .never ∨
      ∃ c ∈ candidates s st r, c.allow = true ∧ specNeedsAuth st c.spec = false := by
  unfold evaluate at h
  rw [judge_listing hl] at h
  obtain ⟨hne, ha⟩ := judgeListing_allow h
  have hpw : pwNeedsAuth (pwPolicyFor st r.command) st ((candidates s st r).filter (·.allow)) = false := by
    rw [← ha]; exact hna
  rcases pwNeedsAuth_false hne hpw with hp | ⟨c, hc, hn⟩
  · exact .inl hp
  · obtain ⟨hc, hca⟩ := List.mem_filter.mp hc
    exact .inr ⟨c, hc, by simpa using hca, hn⟩

/-! ## (6) Irrelevant entries -/

/-- Alias definitions and user specifications; everything else (Defaults, include
directives) is irrelevant to `evaluate`. -/
def isPolicyRelevant : Entry → Bool
  | .userAlias _ _ | .runasAlias _ _ | .hostAlias _ _ | .cmndAlias _ _ | .userSpec _ => true
  | .defaults _ _ | .include _ | .includeDir _ => false

/-- The judgement only depends on the alias definitions and the user specs. -/
theorem evaluate_congr {s t : Sudoers} (ha : aliasesOf s = aliasesOf t) (hs : specsOf s = specsOf t)
    (st : Settings) (r : Request) : evaluate s st r = evaluate t st r := by
  simp [evaluate, candidates, ha, hs]

theorem aliasesOf_erase (s₁ s₂ : Sudoers) (e : Entry) (he : isPolicyRelevant e = false) :
    aliasesOf (s₁ ++ e :: s₂) = aliasesOf (s₁ ++ s₂) := by
  induction s₁ with
  | nil => cases e <;> simp_all [isPolicyRelevant, aliasesOf]
  | cons x xs ih => cases x <;> simp [aliasesOf, ih]

theorem specsOf_erase (s₁ s₂ : Sudoers) (e : Entry) (he : isPolicyRelevant e = false) :
    specsOf (s₁ ++ e :: s₂) = specsOf (s₁ ++ s₂) := by
  simp only [specsOf_append]
  cases e <;> simp_all [isPolicyRelevant, specsOf]

/-- Inserting a `Defaults` line or an (already resolved) include directive anywhere does
not change any judgement. -/
theorem evaluate_irrelevant (s₁ s₂ : Sudoers) (e : Entry) (he : isPolicyRelevant e = false)
    (st : Settings) (r : Request) :
    evaluate (s₁ ++ e :: s₂) st r = evaluate (s₁ ++ s₂) st r :=
  evaluate_congr (aliasesOf_erase s₁ s₂ e he) (specsOf_erase s₁ s₂ e he) st r

/-! ## (7) Literal command paths never match a different basename -/

/-- A literal (non-directory, non-glob) sudoers path never matches a requested path
with a different basename, whatever the realpath oracle says (multicall binaries). -/
theorem pathMatches_literal_basename {canon : String → String} {p path canonical : String}
    (hd : endsWithSlash p = false) (hg : Glob.hasGlob p = false)
    (hb : baseOf p ≠ baseOf path) : pathMatches canon p path canonical = false := by
  have hne : p ≠ path := fun h => hb (h ▸ rfl)
  simp [pathMatches, hd, hg, hne, hb]

/-- Atom-level form: `command p args` with a literal `p` does not match running a
command whose basename differs from `p`'s. -/
theorem cmndBase_literal_basename {canon : String → String} {p path canonical : String}
    {a : CmndArgs} {args : List String}
    (hd : endsWithSlash p = false) (hg : Glob.hasGlob p = false)
    (hb : baseOf p ≠ baseOf path) :
    cmndBase canon (.run path canonical args) (.command p a) = false := by
  simp [cmndBase, pathMatches_literal_basename hd hg hb]

end LeanSudo.Policy
