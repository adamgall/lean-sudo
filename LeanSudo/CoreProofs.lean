import LeanSudo.Core
import LeanSudo.Policy.Proofs

namespace LeanSudo.Core
open Policy

theorem privilege_defaults_preserve_authorization (ctx : Context)
    (before after : Settings) :
    policyJudgement { ctx with settings := after, policySettings := some before } =
      policyJudgement { ctx with settings := before, policySettings := some before } := rfl

theorem privilege_runas_default_preserves_lookup (ctx : Context)
    (matched runtime : Principal) :
    policyJudgement { ctx with target := runtime, policyTarget := some matched } =
      policyJudgement { ctx with target := matched, policyTarget := some matched } := rfl

private theorem branch_of_ite_eq {α : Type} {p : Prop} [Decidable p] {a b c : α}
    (h : (if p then a else b) = c) : a = c ∨ b = c := by
  split at h
  · exact Or.inl h
  · exact Or.inr h

private theorem early_safe (ctx : Context) (act : Action)
    (h : earlyAction ctx = some act) :
    (∀ p, act ≠ .exec p) ∧ (∀ p, act ≠ .edit p) := by
  cases hm : ctx.opts.mode <;> cases hf : earlyFailure ctx <;>
    simp only [earlyAction, hm, hf, Option.map] at h <;> cases h <;>
    constructor <;> intro p hp <;> simp [FailureInfo.action] at hp

private theorem denied_safe (ctx : Context) :
    (∀ p, deniedAction ctx ≠ .exec p) ∧ (∀ p, deniedAction ctx ≠ .edit p) := by
  constructor <;> intro p h
  all_goals
    unfold deniedAction at h
    repeat' first | contradiction | (rcases branch_of_ite_eq h with h | h)

private theorem denied_policy_safe (ctx : Context) :
    (∀ p, (policyDecision ctx .deny).action ≠ .exec p) ∧
    (∀ p, (policyDecision ctx .deny).action ≠ .edit p) := by
  cases hf : decisionFailure ctx .deny with
  | none => simpa [policyDecision, hf] using denied_safe ctx
  | some failure => simp [policyDecision, hf, FailureInfo.action]

private theorem allowedFailure_checks (ctx : Context) (a : Allowed)
    (h : allowedFailure ctx a = none) :
    preCommandFailure ctx a = none ∧ postCommandFailure ctx a = none := by
  cases hp : preCommandFailure ctx a with
  | some failure => simp [allowedFailure, hp] at h
  | none =>
    simp only [allowedFailure, hp] at h
    split at h
    · cases h
    · cases ht : postCommandFailure ctx a with
      | some failure => simp [postLookupFailure, ht] at h
      | none => exact ⟨rfl, rfl⟩

private theorem allowedFailure_env (ctx : Context) (a : Allowed)
    (h : allowedFailure ctx a = none)
    (hm : ctx.opts.mode = .run ∨ ctx.opts.mode = .edit) :
    ∃ env, buildEnv (environment ctx a) = .ok env := by
  have checks := allowedFailure_checks ctx a h
  cases hb : buildEnv (environment ctx a) with
  | ok env => exact ⟨env, rfl⟩
  | error message =>
    rcases hm with hm | hm <;>
      simp [allowedFailure, postLookupFailure, checks.1, checks.2, hm, hb] at h
    all_goals repeat first | contradiction | split at h

private theorem policyJudgement_allow (ctx : Context) (a : Allowed)
    (h : policyJudgement ctx = .allow a) :
    evaluate ctx.sudoers (authorizationSettings ctx) (request ctx) = .allow a := by
  unfold policyJudgement at h
  split at h
  · cases h
  · exact h

private theorem authJudgement_policyJudgement (ctx : Context) :
    authJudgement ctx (policyJudgement ctx) =
      authJudgement ctx (evaluate ctx.sudoers (authorizationSettings ctx) (request ctx)) := by
  by_cases hm : ctx.opts.mode = .list <;>
    simp [authJudgement, policyJudgement, listOtherDenied, hm]

def CommandLineage (ctx : Context) (a : Allowed) (rc : ResolvedCmd) : Prop :=
  (a.selection = none ∧
    (request ctx).command = .run rc.path rc.canonical (policyArgs ctx rc)) ∨
  ∃ selected args, a.selection = some selected ∧ selected.found = true ∧
    selected.command = .run rc.path rc.canonical args ∧
    selected.argv = rc.argv0 :: rc.args

private theorem resolvedFor_lineage (ctx : Context) (a : Allowed) (rc : ResolvedCmd)
    (hm : ctx.opts.mode = .run) (hc : resolvedFor ctx a = some rc) :
    CommandLineage ctx a rc := by
  cases hs : a.selection with
  | none =>
    have hc' : ctx.command = some rc := by simpa [resolvedFor, hs] using hc
    exact Or.inl ⟨hs, by simp [request, hm, runCommand, hc']⟩
  | some selected =>
    cases hf : selected.found with
    | false => simp [resolvedFor, hs, hf] at hc
    | true =>
      cases hcmd : selected.command <;> cases hargv : selected.argv <;>
        simp [resolvedFor, hs, hf, hcmd, hargv] at hc
      case run.cons path canonical args argv0 actual =>
        cases hc
        exact Or.inr ⟨selected, args, hs, hf, hcmd, hargv⟩

private theorem decide_allowed_action (ctx : Context) (p : ExecPlan ⊕ EditPlan)
    (h : (decide ctx).action = p.elim Action.exec Action.edit) :
    ∃ a, evaluate ctx.sudoers (authorizationSettings ctx) (request ctx) = .allow a ∧
      earlyAction ctx = none ∧ allowedFailure ctx a = none ∧
      allowedAction ctx a = p.elim Action.exec Action.edit ∧
      decide ctx = policyDecision ctx (.allow a) := by
  cases he : earlyAction ctx with
  | some act =>
    have hs := early_safe ctx act he
    cases p with
    | inl p => exact False.elim (hs.1 p (by simpa [decide, he] using h))
    | inr p => exact False.elim (hs.2 p (by simpa [decide, he] using h))
  | none =>
    cases hj : policyJudgement ctx with
    | deny =>
      have hs := denied_policy_safe ctx
      cases p with
      | inl p => exact False.elim (hs.1 p (by simpa [decide, he, hj] using h))
      | inr p => exact False.elim (hs.2 p (by simpa [decide, he, hj] using h))
    | allow a =>
      have hh : allowedAction ctx a = p.elim Action.exec Action.edit := by
        simpa [decide, he, hj, policyDecision, decisionFailure] using h
      cases hf : allowedFailure ctx a with
      | some failure => cases p <;> simp [allowedAction, hf, FailureInfo.action] at hh
      | none =>
        exact ⟨a, policyJudgement_allow ctx a hj, rfl, hf, hh, by simp [decide, he, hj]⟩

theorem exec_origin (ctx : Context) (p : ExecPlan) (h : (decide ctx).action = .exec p) :
    ∃ a rc, evaluate ctx.sudoers (authorizationSettings ctx) (request ctx) = .allow a ∧
      ctx.opts.mode = .run ∧ resolvedFor ctx a = some rc ∧ p = execPlan ctx a rc ∧
      (∃ env, buildEnv (environment ctx a) = .ok env) ∧
      decide ctx = policyDecision ctx (.allow a) ∧
      CommandLineage ctx a rc ∧ p.argv.tail = rc.args := by
  obtain ⟨a, ha, _, hf, hh, hd⟩ := decide_allowed_action ctx (.inl p) h
  cases hm : ctx.opts.mode <;> simp only [allowedAction, hf, hm, Sum.elim] at hh
  case run =>
    cases hc : resolvedFor ctx a with
    | none => simp [hc, notFound] at hh
    | some rc =>
      have hp : execPlan ctx a rc = p := by simpa [hc] using hh
      exact ⟨a, rc, ha, rfl, hc, hp.symm,
        allowedFailure_env ctx a hf (Or.inl hm), hd,
        resolvedFor_lineage ctx a rc hm hc, by simp [← hp, execPlan]⟩
  all_goals repeat first | split at hh | cases hh

theorem edit_origin (ctx : Context) (p : EditPlan) (h : (decide ctx).action = .edit p) :
    ∃ a, evaluate ctx.sudoers (authorizationSettings ctx) (request ctx) = .allow a ∧
      ctx.opts.mode = .edit ∧ p = editPlan ctx a ∧
      (∃ env, buildEnv (environment ctx a) = .ok env) ∧
      decide ctx = policyDecision ctx (.allow a) := by
  obtain ⟨a, ha, _, hf, hh, hd⟩ := decide_allowed_action ctx (.inr p) h
  cases hm : ctx.opts.mode <;> simp only [allowedAction, hf, hm, Sum.elim] at hh
  case edit =>
    have hp : editPlan ctx a = p := by simpa using hh
    exact ⟨a, ha, rfl, hp.symm, allowedFailure_env ctx a hf (Or.inr hm), hd⟩
  all_goals repeat first | split at hh | cases hh

theorem exec_allowed (ctx : Context) (p : ExecPlan) (h : (decide ctx).action = .exec p) :
    ∃ a rc, evaluate ctx.sudoers (authorizationSettings ctx) (request ctx) = .allow a ∧
      resolvedFor ctx a = some rc ∧ CommandLineage ctx a rc ∧
      p.path = selectedExecutionPath ctx a rc ∧ p.argv = rc.argv0 :: rc.args := by
  obtain ⟨a, rc, ha, _, hc, hp, _, _, hr, _⟩ := exec_origin ctx p h
  exact ⟨a, rc, ha, hc, hr, by simp [hp, execPlan], by simp [hp, execPlan]⟩

theorem exec_path_is_canonical (ctx : Context) (p : ExecPlan)
    (h : (decide ctx).action = .exec p) :
    ∃ a rc, evaluate ctx.sudoers (authorizationSettings ctx) (request ctx) = .allow a ∧
      resolvedFor ctx a = some rc ∧
      ((a.selection = none ∧
        p.path = ctx.canon (dirOf rc.path) ++
          (if (ctx.canon (dirOf rc.path)).endsWith "/" then "" else "/") ++ baseOf rc.path) ∨
       ∃ root facts, (root, facts) ∈ ctx.rootFacts ∧
         a.selection.map (·.root) = some root ∧
         p.path = rootCanon facts (dirOf rc.path) ++
           (if (rootCanon facts (dirOf rc.path)).endsWith "/" then "" else "/") ++ baseOf rc.path) := by
  obtain ⟨a, rc, ha, _, hc, rfl, _, _, hl, _⟩ := exec_origin ctx p h
  refine ⟨a, rc, ha, hc, ?_⟩
  rcases hl with ⟨hs, _⟩ | ⟨selected, args, hs, _, hcommand, _⟩
  · exact Or.inl ⟨hs, by simp [execPlan, selectedExecutionPath, hs, executionPath]⟩
  · obtain ⟨root, facts, hm, hroot, hcmd, hpath, _⟩ := evaluate_selection_origin ha hs
    refine Or.inr ⟨root, facts, hm, by simp [hs, hroot], ?_⟩
    change selectedExecutionPath ctx a rc = _
    simp only [selectedExecutionPath, hs, Option.map_some, Option.getD_some]
    rw [hpath]
    unfold rootExecutionPath
    rw [← hcmd, hcommand]

theorem edit_allowed (ctx : Context) (p : EditPlan) (h : (decide ctx).action = .edit p) :
    ∃ a, evaluate ctx.sudoers (authorizationSettings ctx) (request ctx) = .allow a ∧
      (request ctx).command = .sudoedit p.policyFiles := by
  obtain ⟨a, ha, hm, rfl, _, _⟩ := edit_origin ctx p h
  exact ⟨a, ha, by simp [request, hm, editPlan]⟩

theorem edit_files_normalized (ctx : Context) (p : EditPlan)
    (h : (decide ctx).action = .edit p) :
    ∀ file ∈ p.files, file.startsWith "/" = true ∧ file.contains '\x00' = false := by
  obtain ⟨_, _, he, _⟩ := decide_allowed_action ctx (.inr p) h
  obtain ⟨a, _, hm, rfl, _, _⟩ := edit_origin ctx p h
  have hb : invalidEditFile ctx = none := by
    cases hx : invalidEditFile ctx with
    | none => rfl
    | some bad =>
      simp [earlyAction, earlyFailure, hm, hx] at he
      repeat first | contradiction | split at he
  simp only [invalidEditFile, List.find?_eq_none] at hb
  simpa [editPlan, normalizedEditFile] using hb

theorem edit_files_match_policy (ctx : Context) (p : EditPlan)
    (h : (decide ctx).action = .edit p) :
    (request ctx).command = .sudoedit p.policyFiles ∧
    p.files = p.policyFiles.map (fun f => if f.startsWith "/" then f
      else ctx.cwd ++ (if ctx.cwd.endsWith "/" then "" else "/") ++ f) := by
  obtain ⟨a, _, hm, rfl, _, _⟩ := edit_origin ctx p h
  simp [editPlan, request, hm, files]

theorem commandTimeout_policy_bound (ctx : Context) (a : Allowed)
    (h : a.timeout.getD ctx.settings.commandTimeout ≠ 0) :
    commandTimeout ctx a ≤ a.timeout.getD ctx.settings.commandTimeout := by
  unfold commandTimeout
  split
  · exact Nat.le_refl _
  · split
    · exact Nat.le_refl _
    · simp only [h, beq_iff_eq, ↓reduceIte]
      exact Nat.min_le_right _ _

theorem exec_identity (ctx : Context) (p : ExecPlan) (h : (decide ctx).action = .exec p) :
    p.uid = ctx.target.uid ∧ p.gid =
      (if ctx.settings.staySetuid then ctx.invokingRealGid.getD ctx.invoking.gid
       else (ctx.targetGroup.map (·.gid)).getD ctx.target.gid) ∧
    p.groups = (if ctx.opts.preserveGroups || ctx.settings.preserveGroups then
      ctx.invoking.groups else ctx.target.groups).map (·.2) := by
  obtain ⟨a, rc, _, _, _, rfl, _, _⟩ := exec_origin ctx p h
  exact ⟨rfl, rfl, rfl⟩

theorem edit_identity (ctx : Context) (p : EditPlan) (h : (decide ctx).action = .edit p) :
    p.fileUid = ctx.target.uid ∧ p.editUid = (displayUser ctx).uid ∧
    p.fileGid = targetGid ctx ∧ p.fileGroups = targetGroups ctx ∧
    p.editGid = (displayUser ctx).gid ∧ p.editGroups = (displayUser ctx).groups.map (·.2) := by
  obtain ⟨a, _, _, rfl, _, _⟩ := edit_origin ctx p h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def AuthExemption (ctx : Context) (a : Allowed) : Prop :=
  ctx.invoking.uid = 0 ∨ a.needsAuth = false ∨ userIsExempt ctx.settings ctx.invoking = true ∨
    (Timestamp.lookup ctx.now ctx.settings.timestampTimeout ctx.tsScope
      (authUser ctx).uid ctx.tsRecords = true ∧ ctx.opts.resetTimestamp = false) ∨
    (ctx.target.uid = ctx.invoking.uid ∧
      (ctx.opts.group.isNone = true ∨ ∃ g, ctx.targetGroup = some g ∧
        ctx.invoking.groups.any (fun x => x.2 == g.gid) = true) ∧
      sameSecurityContext ctx a = true)

theorem invalid_runas_shell_no_exec (ctx : Context)
    (hs : ctx.settings.runasCheckShell = true)
    (hv : ctx.validShells.contains ctx.target.shell = false) :
    ∀ p, (decide ctx).action ≠ .exec p := by
  intro p hp
  obtain ⟨_, _, he, _⟩ := decide_allowed_action ctx (.inl p) hp
  obtain ⟨a, rc, _, hm, _⟩ := exec_origin ctx p hp
  have hv' : ctx.target.shell ∉ ctx.validShells := by simpa using hv
  simp [earlyAction, earlyFailure, hm, hs, hv'] at he
  repeat' first | contradiction | (rcases branch_of_ite_eq he with he | he)

theorem exempt_user_no_auth (ctx : Context) (j : Judgement)
    (h : userIsExempt ctx.settings ctx.invoking = true) :
    authentication ctx j = .none := by
  simp [authentication, policyNeedsAuth, h]

theorem denied_authentication_disabled (ctx : Context)
    (h : ctx.settings.authenticate = false) :
    authentication ctx .deny = .none := by
  simp [authentication, policyNeedsAuth, deniedNeedsAuth, h]

private theorem authentication_none (ctx : Context) (a : Allowed)
    (h : authentication ctx (.allow a) = .none) : AuthExemption ctx a := by
  simp only [authentication, policyNeedsAuth] at h
  unfold tsValid sameIdentity at h
  unfold AuthExemption
  cases hg : ctx.targetGroup <;> cases ho : ctx.opts.group <;> simp_all <;> grind

private theorem noauth_of_decision (ctx : Context) (a : Allowed)
    (hm : ctx.opts.mode ≠ .list) (hd : decide ctx = policyDecision ctx (.allow a))
    (hn : (decide ctx).auth = .none) : AuthExemption ctx a := by
  rw [hd] at hn
  exact authentication_none ctx a
    (by simpa only [policyDecision, authJudgement, hm, ↓reduceIte] using hn)

theorem exec_noauth (ctx : Context) (p : ExecPlan)
    (h : (decide ctx).action = .exec p) (hn : (decide ctx).auth = .none) :
    ∃ a, evaluate ctx.sudoers (authorizationSettings ctx) (request ctx) = .allow a ∧ AuthExemption ctx a := by
  obtain ⟨a, rc, ha, hm, _, _, _, hd, _⟩ := exec_origin ctx p h
  exact ⟨a, ha, noauth_of_decision ctx a (by simp [hm]) hd hn⟩

theorem edit_noauth (ctx : Context) (p : EditPlan)
    (h : (decide ctx).action = .edit p) (hn : (decide ctx).auth = .none) :
    ∃ a, evaluate ctx.sudoers (authorizationSettings ctx) (request ctx) = .allow a ∧ AuthExemption ctx a := by
  obtain ⟨a, ha, hm, _, _, hd⟩ := edit_origin ctx p h
  exact ⟨a, ha, noauth_of_decision ctx a (by simp [hm]) hd hn⟩

theorem exec_environment (ctx : Context) (p : ExecPlan) (h : (decide ctx).action = .exec p) :
    ∃ a env, evaluate ctx.sudoers (authorizationSettings ctx) (request ctx) = .allow a ∧
      buildEnv p.envInput = .ok env ∧ p.envInput.pamEnv = [] ∧
      p.envInput.settings = ctx.settings ∧ p.envInput.target = ctx.target ∧
      p.envInput.invoking = ctx.invoking ∧ p.envInput.setenvAllowed = a.setenv := by
  obtain ⟨a, rc, ha, _, _, rfl, ⟨env, hb⟩, _⟩ := exec_origin ctx p h
  exact ⟨a, env, ha, hb, rfl, rfl, rfl, rfl, rfl⟩

theorem edit_environment (ctx : Context) (p : EditPlan) (h : (decide ctx).action = .edit p) :
    ∃ a env, evaluate ctx.sudoers (authorizationSettings ctx) (request ctx) = .allow a ∧
      buildEnv p.envInput = .ok env ∧ p.envInput.pamEnv = [] ∧
      p.envInput.settings = ctx.settings ∧ p.envInput.target = ctx.target ∧
      p.envInput.invoking = ctx.invoking ∧ p.envInput.setenvAllowed = a.setenv := by
  obtain ⟨a, ha, _, rfl, ⟨env, hb⟩, _⟩ := edit_origin ctx p h
  exact ⟨a, env, ha, hb, rfl, rfl, rfl, rfl, rfl⟩

theorem deny_no_execution (ctx : Context)
    (h : evaluate ctx.sudoers (authorizationSettings ctx) (request ctx) = .deny) :
    (∀ p, (decide ctx).action ≠ .exec p) ∧ (∀ p, (decide ctx).action ≠ .edit p) := by
  constructor
  · intro p hp; obtain ⟨a, _, ha, _⟩ := exec_allowed ctx p hp; rw [h] at ha; cases ha
  · intro p hp; obtain ⟨a, ha, _⟩ := edit_allowed ctx p hp; rw [h] at ha; cases ha

theorem command_not_found_no_exec (ctx : Context)
    (h : ∀ a, evaluate ctx.sudoers (authorizationSettings ctx) (request ctx) = .allow a →
      resolvedFor ctx a = none) :
    ∀ p, (decide ctx).action ≠ .exec p := by
  intro p hp
  obtain ⟨a, rc, ha, _, hc, _⟩ := exec_origin ctx p hp
  rw [h a ha] at hc
  cases hc

private theorem buildEnv_success_iff (i : EnvInput) :
    (∃ env, buildEnv i = .ok env) ↔
      (wantsPreserveAll i && !i.setenvAllowed) = false ∧
      ((extraVars i).filter (fun kv => !extraAllowed i (resetMode i) kv.1 kv.2)).isEmpty = true := by
  unfold buildEnv
  split <;> simp_all
  split <;> simp_all

theorem buildEnv_success_pam_independent (i : EnvInput) (pam : EnvList) :
    (∃ env, buildEnv { i with pamEnv := pam } = .ok env) ↔
      (∃ env, buildEnv i = .ok env) := by
  rw [buildEnv_success_iff, buildEnv_success_iff]
  rfl

theorem timestamp_update_allowed (ctx : Context) (h : (decide ctx).updateTimestamp = true) :
    (∃ a, evaluate ctx.sudoers (authorizationSettings ctx) (request ctx) = .allow a) ∧
      ctx.opts.noUpdate = false ∧ ctx.opts.resetTimestamp = false := by
  unfold decide at h
  split at h
  · cases h
  · unfold policyDecision at h
    cases hj : policyJudgement ctx with
    | deny => simp [hj] at h
    | allow a =>
      have ha := policyJudgement_allow ctx a hj
      simp_all

theorem reset_never_waives_auth (ctx : Context) (j : Judgement)
    (hk : ctx.opts.resetTimestamp = true) (hn : policyNeedsAuth ctx j = true) :
    authentication ctx j = .required (authUser ctx) := by
  simp [authentication, tsValid, hk, hn]

theorem decide_reset_requires_auth (ctx : Context) (he : earlyAction ctx = none)
    (hk : ctx.opts.resetTimestamp = true)
    (hn : policyNeedsAuth ctx (authJudgement ctx
      (evaluate ctx.sudoers (authorizationSettings ctx) (request ctx))) = true) :
    (decide ctx).auth = .required (authUser ctx) := by
  simp only [decide, he, policyDecision, authJudgement_policyJudgement]
  exact reset_never_waives_auth ctx _ hk hn

theorem required_auth_identity (ctx : Context) (u : Principal)
    (h : (decide ctx).auth = .required u)
    (hr : ctx.settings.rootpw = false) (ha : ctx.settings.runaspw = false)
    (ht : ctx.settings.targetpw = false) : u = ctx.invoking := by
  unfold decide at h
  split at h
  · cases h
  · simp only [policyDecision, authentication] at h
    split at h
    · simp [authUser, hr, ha, ht] at h; exact h.symm
    · cases h

theorem administrative_modes_no_execution (ctx : Context)
    (hm : ctx.opts.mode = .help ∨ ctx.opts.mode = .version ∨
      ctx.opts.mode = .resetTimestamp ∨ ctx.opts.mode = .removeTimestamp) :
    (∀ p, (decide ctx).action ≠ .exec p) ∧ (∀ p, (decide ctx).action ≠ .edit p) := by
  rcases hm with h | h | h | h <;> simp [decide, earlyAction, h]

theorem administrative_modes_no_auth_or_update (ctx : Context)
    (hm : ctx.opts.mode = .help ∨ ctx.opts.mode = .version ∨
      ctx.opts.mode = .resetTimestamp ∨ ctx.opts.mode = .removeTimestamp) :
    (decide ctx).auth = .none ∧ (decide ctx).updateTimestamp = false := by
  rcases hm with h | h | h | h <;> simp [decide, earlyAction, h]

theorem exec_fd_is_pinned (ctx : Context) (p : ExecPlan)
    (h : (decide ctx).action = .exec p) {fd : Nat} (hf : p.execFd = some fd) :
    ctx.execFd = some fd ∨
      ∃ root facts, (root, facts) ∈ ctx.rootFacts ∧ facts.execFd = some fd := by
  obtain ⟨a, rc, ha, _, _, rfl, _⟩ := exec_origin ctx p h
  have hd : descriptorFor ctx a = some fd := by
    simp only [execPlan] at hf
    split at hf
    · exact hf
    · cases hf
  cases hs : a.selection with
  | none => exact Or.inl (by simpa [descriptorFor, hs] using hd)
  | some selected =>
    obtain ⟨root, facts, hm, _, _, _, _, _, hfd, _⟩ := evaluate_selection_origin ha hs
    refine Or.inr ⟨root, facts, hm, ?_⟩
    rw [← hfd]
    simpa [descriptorFor, hs] using hd

theorem enforcement_error_no_exec (ctx : Context) (a : Allowed)
    (ha : evaluate ctx.sudoers (authorizationSettings ctx) (request ctx) = .allow a)
    (he : (enforcementError ctx a).isSome = true) :
    ∀ p, (decide ctx).action ≠ .exec p := by
  intro p hp
  obtain ⟨b, hb, _, hf, _⟩ := decide_allowed_action ctx (.inl p) hp
  rw [ha] at hb
  cases hb
  have checks := allowedFailure_checks ctx a hf
  simp [enforcementError, checks.1, checks.2] at he

theorem enforcement_error_no_edit (ctx : Context) (a : Allowed)
    (ha : evaluate ctx.sudoers (authorizationSettings ctx) (request ctx) = .allow a)
    (he : (enforcementError ctx a).isSome = true) :
    ∀ p, (decide ctx).action ≠ .edit p := by
  intro p hp
  obtain ⟨b, hb, _, hf, _⟩ := decide_allowed_action ctx (.inr p) hp
  rw [ha] at hb
  cases hb
  have checks := allowedFailure_checks ctx a hf
  simp [enforcementError, checks.1, checks.2] at he

theorem selected_refusal_no_execution (ctx : Context) (a : Allowed)
    (ha : evaluate ctx.sudoers (authorizationSettings ctx) (request ctx) = .allow a)
    (href : (a.selection.bind (·.refusal)).isSome = true) :
    (∀ p, (decide ctx).action ≠ .exec p) ∧
    (∀ p, (decide ctx).action ≠ .edit p) := by
  have he : (enforcementError ctx a).isSome = true := by
    cases hp : permissionFailure ctx a <;> cases hs : a.selection.bind (·.refusal) <;>
      simp [enforcementError, preCommandFailure, hp, hs] at *
  exact ⟨enforcement_error_no_exec ctx a ha he, enforcement_error_no_edit ctx a ha he⟩

theorem intercept_setid_no_exec (ctx : Context) (a : Allowed)
    (ha : evaluate ctx.sudoers (authorizationSettings ctx) (request ctx) = .allow a)
    (hm : ctx.opts.mode = .run)
    (hi : a.intercept.getD ctx.settings.intercept = true)
    (hs : ctx.settings.interceptAllowSetid = false)
    (hmode : commandSetidFor ctx a = true) :
    ∀ p, (decide ctx).action ≠ .exec p := by
  apply enforcement_error_no_exec ctx a ha
  cases hp : permissionFailure ctx a <;> cases href : a.selection.bind (·.refusal) <;>
    simp [enforcementError, preCommandFailure, hp, href, hm, hi, hs, hmode]

theorem exec_chroot_selection (ctx : Context) (p : ExecPlan)
    (h : (decide ctx).action = .exec p) :
    ∃ a, evaluate ctx.sudoers (authorizationSettings ctx) (request ctx) = .allow a ∧
      chrootPermitted ctx a = true ∧ p.chroot = commandChroot ctx a := by
  obtain ⟨a, rc, ha, _, _, rfl, _⟩ := exec_origin ctx p h
  refine ⟨a, ha, ?_, rfl⟩
  cases hp : chrootPermitted ctx a with
  | true => rfl
  | false =>
    have he : (enforcementError ctx a).isSome = true := by
      simp [enforcementError, preCommandFailure, permissionFailure, hp]
    exact False.elim (enforcement_error_no_exec ctx a ha he _ h)

theorem exec_user_chroot_requires_wildcard (ctx : Context) (p : ExecPlan)
    (h : (decide ctx).action = .exec p) {root : String}
    (hr : ctx.opts.chroot = some root) :
    ∃ a, evaluate ctx.sudoers (authorizationSettings ctx) (request ctx) = .allow a ∧
      effectiveChroot ctx a = some "*" := by
  obtain ⟨a, ha, hp, _⟩ := exec_chroot_selection ctx p h
  exact ⟨a, ha, by simpa [chrootPermitted, hr] using hp⟩

theorem exec_selected_root (ctx : Context) (p : ExecPlan)
    (h : (decide ctx).action = .exec p) (a : Allowed) (selected : CommandSelection)
    (ha : evaluate ctx.sudoers (authorizationSettings ctx) (request ctx) = .allow a)
    (hs : a.selection = some selected) :
    p.chroot = ((some selected.root).filter (· != "*")).bind
      (expandHomePath (ctx.policyTarget.getD ctx.target).home ctx.homes) := by
  obtain ⟨b, rc, hb, hm, _, rfl, _⟩ := exec_origin ctx p h
  rw [ha] at hb
  cases hb
  simp [execPlan, runPlan, commandChroot, selectedChroot, hm, hs]

theorem edit_chroot_uses_defaults (ctx : Context) (p : EditPlan)
    (h : (decide ctx).action = .edit p) :
    p.chroot = ((ctx.opts.chroot.or (authorizationSettings ctx).runchroot).filter (· != "*")).bind
      (expandHome ctx) := by
  obtain ⟨a, _, hm, rfl, _⟩ := edit_origin ctx p h
  simp [editPlan, runPlan, commandChroot, selectedChroot, configuredChroot, effectiveChroot, hm]
  rfl

theorem edit_user_chroot_requires_wildcard (ctx : Context) (p : EditPlan)
    (h : (decide ctx).action = .edit p) {root : String}
    (hr : ctx.opts.chroot = some root) :
    (authorizationSettings ctx).runchroot = some "*" := by
  obtain ⟨a, ha, hm, _, _⟩ := edit_origin ctx p h
  by_cases hn : (authorizationSettings ctx).runchroot = some "*"
  · exact hn
  · have hp : chrootPermitted ctx a = false := by
      simp [chrootPermitted, effectiveChroot, hm, hr, hn]
    have he : (enforcementError ctx a).isSome = true := by
      simp [enforcementError, preCommandFailure, permissionFailure, hp]
    exact False.elim (enforcement_error_no_edit ctx a ha he p h)

theorem enforcementError_logServers (ctx : Context) (a : Allowed) (servers : List String) :
    enforcementError { ctx with settings := { ctx.settings with logServers := servers } } a =
      enforcementError ctx a := by
  have he : effectiveChroot { ctx with settings := { ctx.settings with logServers := servers } } a =
      effectiveChroot ctx a := by
    cases hp : ctx.policySettings <;> simp [effectiveChroot, authorizationSettings, hp]
  simp only [enforcementError, preCommandFailure, postCommandFailure, permissionFailure,
    chrootPermitted, commandChroot, selectedChroot, configuredChroot, he]
  rfl

theorem exec_intercept_matches_policy (ctx : Context) (p : ExecPlan)
    (h : (decide ctx).action = .exec p) :
    ∃ a, evaluate ctx.sudoers (authorizationSettings ctx) (request ctx) = .allow a ∧
      p.intercept = a.intercept.getD ctx.settings.intercept ∧
      p.logSubcmds = ctx.settings.logSubcmds := by
  obtain ⟨a, rc, ha, _, _, rfl, _⟩ := exec_origin ctx p h
  exact ⟨a, ha, rfl, rfl⟩

theorem group_plugin_requires_yes (ctx : Context) (p : Principal) (group : String)
    (h : userBase p ctx.settings (some (request ctx)) (.nonunixGroup group) = true) :
    (p.name, group, true) ∈ ctx.pluginGroups := by
  obtain ⟨r, hr, hm⟩ := pluginGroupMatch_requires_yes ctx.settings
    (some (request ctx)) p.name group h
  cases Option.some.inj hr
  exact hm

theorem invalid_timeout_no_execution (ctx : Context)
    (h : (Cli.timeoutError ctx.opts).isSome = true) :
    (∀ p, (decide ctx).action ≠ .exec p) ∧
    (∀ p, (decide ctx).action ≠ .edit p) := by
  cases hm : ctx.opts.mode <;> simp [decide, earlyAction, earlyFailure, FailureInfo.action, hm, h]

theorem configured_cwd_required (ctx : Context) (a : Allowed) (rc : ResolvedCmd)
    (path resolved : String) (hp : configuredCwd ctx a = some path)
    (hr : expandHome ctx path = some resolved) :
    (execPlan ctx a rc).cwd = some resolved ∧ (execPlan ctx a rc).cwdOptional = false := by
  simp [execPlan, hp, hr]

theorem list_other_denied_no_execution (ctx : Context) (h : listOtherDenied ctx = true) :
    (∀ p, (decide ctx).action ≠ .exec p) ∧ (∀ p, (decide ctx).action ≠ .edit p) := by
  cases he : earlyAction ctx with
  | some action => simpa [decide, he] using early_safe ctx action he
  | none => simpa [decide, he, policyJudgement, h] using denied_policy_safe ctx

theorem editor_variables_preserve_files (ctx : Context) (a : Allowed) (env : EnvList) :
    (editPlan { ctx with userEnv := env } a).files = (editPlan ctx a).files ∧
    (editPlan { ctx with userEnv := env } a).policyFiles = (editPlan ctx a).policyFiles :=
  ⟨rfl, rfl⟩

theorem failureLog_ne_accept (ctx : Context) (failure : FailureInfo)
    (allowed : Option Allowed) (line : LogLine)
    (h : failureLog ctx failure allowed = some line) :
    line.event ≠ .accept := by
  cases hr : failure.reason with
  | none => simp [failureLog, hr] at h
  | some reason =>
    simp only [failureLog, hr] at h
    split at h
    · cases h
    · cases h
      change (if failure.denial then EventLog.EventType.reject else .alert) ≠ .accept
      split <;> decide

theorem policy_failure_ne_accept (ctx : Context) (j : Judgement)
    (failure : FailureInfo) (hf : decisionFailure ctx j = some failure)
    (line : LogLine) (hl : (policyDecision ctx j).log = some line) :
    line.event ≠ .accept := by
  apply failureLog_ne_accept ctx failure _ line
  simpa only [policyDecision, hf] using hl

theorem policy_warning_no_mail (ctx : Context) (j : Judgement)
    (failure : FailureInfo) (hf : decisionFailure ctx j = some failure)
    (hw : failure.denial = false) :
    (policyDecision ctx j).mail = false := by
  simp [policyDecision, hf, hw]

end LeanSudo.Core
