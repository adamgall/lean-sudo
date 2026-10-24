import LeanSudo.Core

/-! End-to-end authorization, identity, environment and authentication invariants.
The IO shell must successfully perform the returned authentication before execution. -/
namespace LeanSudo.Core
open Policy

private theorem early_safe (ctx : Context) (act : Action)
    (h : earlyAction ctx = some act) :
    (∀ p, act ≠ .exec p) ∧ (∀ p, act ≠ .edit p) := by
  unfold earlyAction at h
  split at h <;> repeat' first | split at h | cases h
  all_goals simp

private theorem denied_safe (ctx : Context) :
    (∀ p, deniedAction ctx ≠ .exec p) ∧ (∀ p, deniedAction ctx ≠ .edit p) := by
  unfold deniedAction
  repeat' split
  all_goals simp [notFound]

/-- Every executable plan comes from an allowed resolved run with a checked environment. -/
theorem exec_origin (ctx : Context) (p : ExecPlan) (h : (decide ctx).action = .exec p) :
    ∃ a rc, evaluate ctx.sudoers ctx.settings (request ctx) = .allow a ∧
      ctx.opts.mode = .run ∧ ctx.command = some rc ∧ p = execPlan ctx a rc ∧
      (∃ env, buildEnv (environment ctx a) = .ok env) ∧
      decide ctx = policyDecision ctx (.allow a) ∧
      (request ctx).command = .run rc.path p.path rc.args ∧ p.argv.tail = rc.args := by
  unfold decide at h ⊢
  cases he : earlyAction ctx with
  | some act => simp only [he] at h; exact False.elim ((early_safe ctx act he).1 p h)
  | none =>
    simp only [he] at h ⊢
    cases hj : evaluate ctx.sudoers ctx.settings (request ctx) with
    | deny => simp only [hj, policyDecision] at h; exact False.elim ((denied_safe ctx).1 p h)
    | allow a =>
      simp only [hj, policyDecision] at h
      unfold allowedAction at h
      split at h
      · rename_i hm
        cases hc : ctx.command with
        | none => simp [hc, notFound] at h
        | some rc =>
          simp only [hc] at h
          split at h
          · cases h
          · cases hb : buildEnv (environment ctx a) with
            | error e => simp [hb] at h
            | ok env =>
              simp only [hb, Action.exec.injEq] at h
              refine ⟨a, rc, rfl, hm, rfl, h.symm, ⟨env, hb⟩, rfl, ?_, ?_⟩
              · simp [← h, request, hm, runCommand, hc, execPlan]
              · simp [← h, execPlan]
      all_goals repeat' first | split at h | cases h

/-- Editing is authorized for precisely the absolute file list in the returned plan. -/
theorem edit_origin (ctx : Context) (p : EditPlan) (h : (decide ctx).action = .edit p) :
    ∃ a, evaluate ctx.sudoers ctx.settings (request ctx) = .allow a ∧
      ctx.opts.mode = .edit ∧ p = editPlan ctx a ∧
      (∃ env, buildEnv (environment ctx a) = .ok env) ∧
      decide ctx = policyDecision ctx (.allow a) := by
  unfold decide at h ⊢
  cases he : earlyAction ctx with
  | some act => simp only [he] at h; exact False.elim ((early_safe ctx act he).2 p h)
  | none =>
    simp only [he] at h ⊢
    cases hj : evaluate ctx.sudoers ctx.settings (request ctx) with
    | deny => simp only [hj, policyDecision] at h; exact False.elim ((denied_safe ctx).2 p h)
    | allow a =>
      simp only [hj, policyDecision] at h
      unfold allowedAction at h
      split at h
      · repeat' first | split at h | cases h
      · rename_i hm
        split at h
        · cases h
        · cases hb : buildEnv (environment ctx a) with
          | error e => simp [hb] at h
          | ok env =>
            simp only [hb, Action.edit.injEq] at h
            exact ⟨a, rfl, hm, h.symm, ⟨env, hb⟩, rfl⟩
      all_goals repeat' first | split at h | cases h

theorem exec_allowed (ctx : Context) (p : ExecPlan) (h : (decide ctx).action = .exec p) :
    ∃ a path args, evaluate ctx.sudoers ctx.settings (request ctx) = .allow a ∧
      (request ctx).command = .run path p.path args ∧ p.argv.tail = args := by
  obtain ⟨a, rc, ha, _, _, _, _, _, hr, ht⟩ := exec_origin ctx p h
  exact ⟨a, rc.path, rc.args, ha, hr, ht⟩

/-- Execution uses the lookup-time realpath, never the user-controlled lookup alias. -/
theorem exec_path_is_canonical (ctx : Context) (p : ExecPlan)
    (h : (decide ctx).action = .exec p) :
    ∃ rc, ctx.command = some rc ∧ p.path = rc.canonical := by
  obtain ⟨a, rc, _, _, hc, rfl, _⟩ := exec_origin ctx p h
  exact ⟨rc, hc, rfl⟩

theorem edit_allowed (ctx : Context) (p : EditPlan) (h : (decide ctx).action = .edit p) :
    ∃ a, evaluate ctx.sudoers ctx.settings (request ctx) = .allow a ∧
      (request ctx).command = .sudoedit p.files := by
  obtain ⟨a, ha, hm, rfl, _, _⟩ := edit_origin ctx p h
  exact ⟨a, ha, by simp [request, hm, editPlan]⟩

/-- Every edit path is absolute, with no empty, dot or parent-directory components. -/
theorem edit_files_normalized (ctx : Context) (p : EditPlan)
    (h : (decide ctx).action = .edit p) :
    ∀ file ∈ p.files, file.startsWith "/" = true ∧
      ∀ component ∈ (file.splitOn "/").tail,
        component ≠ "" ∧ component ≠ "." ∧ component ≠ ".." := by
  have he : earlyAction ctx = none := by
    cases hx : earlyAction ctx with
    | none => rfl
    | some act =>
      have ha : act = .edit p := by simpa [decide, hx] using h
      exact False.elim ((early_safe ctx act hx).2 p ha)
  obtain ⟨a, _, hm, rfl, _, _⟩ := edit_origin ctx p h
  have hb : invalidEditFile ctx = none := by
    cases hx : invalidEditFile ctx with
    | none => rfl
    | some bad => simp [earlyAction, hm, hx] at he
  simp only [invalidEditFile, List.find?_eq_none] at hb
  simpa [editPlan, normalizedEditFile] using hb

theorem exec_identity (ctx : Context) (p : ExecPlan) (h : (decide ctx).action = .exec p) :
    p.uid = ctx.target.uid ∧ p.gid = (ctx.targetGroup.map (·.gid)).getD ctx.target.gid ∧
    p.groups = (if ctx.opts.preserveGroups || ctx.settings.preserveGroups then
      ctx.invoking.groups else ctx.target.groups).map (·.2) := by
  obtain ⟨a, rc, _, _, _, rfl, _, _⟩ := exec_origin ctx p h
  exact ⟨rfl, rfl, rfl⟩

theorem edit_identity (ctx : Context) (p : EditPlan) (h : (decide ctx).action = .edit p) :
    p.fileUid = ctx.target.uid ∧ p.editUid = ctx.invoking.uid ∧
    p.fileGid = targetGid ctx ∧ p.fileGroups = targetGroups ctx ∧
    p.editGid = ctx.invoking.gid ∧ p.editGroups = ctx.invoking.groups.map (·.2) := by
  obtain ⟨a, _, _, rfl, _, _⟩ := edit_origin ctx p h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The alternatives which can legitimately waive a password check. -/
def AuthExemption (ctx : Context) (a : Allowed) : Prop :=
  ctx.invoking.uid = 0 ∨ a.needsAuth = false ∨
    (Timestamp.lookup ctx.now ctx.settings.timestampTimeout ctx.tsScope
      (authUser ctx).uid ctx.tsRecords = true ∧ ctx.opts.resetTimestamp = false) ∨
    (ctx.target.uid = ctx.invoking.uid ∧
      (ctx.opts.group.isNone = true ∨ ∃ g, ctx.targetGroup = some g ∧
        ctx.invoking.groups.any (fun x => x.2 == g.gid) = true))

private theorem authentication_none (ctx : Context) (a : Allowed)
    (h : authentication ctx (.allow a) = .none) : AuthExemption ctx a := by
  simp only [authentication, policyNeedsAuth] at h
  unfold tsValid sameIdentity at h
  unfold AuthExemption
  cases hg : ctx.targetGroup <;> cases ho : ctx.opts.group <;> simp_all <;> grind

theorem exec_noauth (ctx : Context) (p : ExecPlan)
    (h : (decide ctx).action = .exec p) (hn : (decide ctx).auth = .none) :
    ∃ a, evaluate ctx.sudoers ctx.settings (request ctx) = .allow a ∧ AuthExemption ctx a := by
  obtain ⟨a, rc, ha, hm, _, _, _, hd, _⟩ := exec_origin ctx p h
  rw [hd] at hn
  simp only [policyDecision, authJudgement, hm, reduceCtorEq, ↓reduceIte] at hn
  exact ⟨a, ha, authentication_none ctx a hn⟩

theorem edit_noauth (ctx : Context) (p : EditPlan)
    (h : (decide ctx).action = .edit p) (hn : (decide ctx).auth = .none) :
    ∃ a, evaluate ctx.sudoers ctx.settings (request ctx) = .allow a ∧ AuthExemption ctx a := by
  obtain ⟨a, ha, hm, _, _, hd⟩ := edit_origin ctx p h
  rw [hd] at hn
  simp only [policyDecision, authJudgement, hm, reduceCtorEq, ↓reduceIte] at hn
  exact ⟨a, ha, authentication_none ctx a hn⟩

theorem exec_environment (ctx : Context) (p : ExecPlan) (h : (decide ctx).action = .exec p) :
    ∃ a env, evaluate ctx.sudoers ctx.settings (request ctx) = .allow a ∧
      buildEnv p.envInput = .ok env ∧ p.envInput.pamEnv = [] ∧
      p.envInput.settings = ctx.settings ∧ p.envInput.target = ctx.target ∧
      p.envInput.invoking = ctx.invoking ∧ p.envInput.setenvAllowed = a.setenv := by
  obtain ⟨a, rc, ha, _, _, rfl, ⟨env, hb⟩, _⟩ := exec_origin ctx p h
  exact ⟨a, env, ha, hb, rfl, rfl, rfl, rfl, rfl⟩

theorem edit_environment (ctx : Context) (p : EditPlan) (h : (decide ctx).action = .edit p) :
    ∃ a env, evaluate ctx.sudoers ctx.settings (request ctx) = .allow a ∧
      buildEnv p.envInput = .ok env ∧ p.envInput.pamEnv = [] ∧
      p.envInput.settings = ctx.settings ∧ p.envInput.target = ctx.target ∧
      p.envInput.invoking = ctx.invoking ∧ p.envInput.setenvAllowed = a.setenv := by
  obtain ⟨a, ha, _, rfl, ⟨env, hb⟩, _⟩ := edit_origin ctx p h
  exact ⟨a, env, ha, hb, rfl, rfl, rfl, rfl, rfl⟩

theorem deny_no_execution (ctx : Context)
    (h : evaluate ctx.sudoers ctx.settings (request ctx) = .deny) :
    (∀ p, (decide ctx).action ≠ .exec p) ∧ (∀ p, (decide ctx).action ≠ .edit p) := by
  constructor
  · intro p hp; obtain ⟨a, _, _, ha, _⟩ := exec_allowed ctx p hp; rw [h] at ha; cases ha
  · intro p hp; obtain ⟨a, ha, _⟩ := edit_allowed ctx p hp; rw [h] at ha; cases ha

theorem command_not_found_no_exec (ctx : Context) (h : ctx.command = none) :
    ∀ p, (decide ctx).action ≠ .exec p := by
  intro p hp
  obtain ⟨_, rc, _, _, hc, _⟩ := exec_origin ctx p hp
  rw [h] at hc
  cases hc

private theorem buildEnv_success_iff (i : EnvInput) :
    (∃ env, buildEnv i = .ok env) ↔
      (wantsPreserveAll i && !i.setenvAllowed) = false ∧
      ((extraVars i).filter (fun kv => !extraAllowed i (resetMode i) kv.1 kv.2)).isEmpty = true := by
  unfold buildEnv
  split <;> simp_all
  split <;> simp_all

/-- PAM contributes values only after validation, and cannot turn rejection into success. -/
theorem buildEnv_success_pam_independent (i : EnvInput) (pam : EnvList) :
    (∃ env, buildEnv { i with pamEnv := pam } = .ok env) ↔
      (∃ env, buildEnv i = .ok env) := by
  rw [buildEnv_success_iff, buildEnv_success_iff]
  rfl

theorem timestamp_update_allowed (ctx : Context) (h : (decide ctx).updateTimestamp = true) :
    (∃ a, evaluate ctx.sudoers ctx.settings (request ctx) = .allow a) ∧
      ctx.opts.noUpdate = false ∧ ctx.opts.resetTimestamp = false := by
  unfold decide at h
  split at h
  · cases h
  · unfold policyDecision at h
    cases hj : evaluate ctx.sudoers ctx.settings (request ctx) <;> simp_all

theorem reset_never_waives_auth (ctx : Context) (j : Judgement)
    (hk : ctx.opts.resetTimestamp = true) (hn : policyNeedsAuth ctx j = true) :
    authentication ctx j = .required (authUser ctx) := by
  simp [authentication, tsValid, hk, hn]

/-- On every policy path, `-k` forces the requested password regardless of cached records. -/
theorem decide_reset_requires_auth (ctx : Context) (he : earlyAction ctx = none)
    (hk : ctx.opts.resetTimestamp = true)
    (hn : policyNeedsAuth ctx (authJudgement ctx
      (evaluate ctx.sudoers ctx.settings (request ctx))) = true) :
    (decide ctx).auth = .required (authUser ctx) := by
  simp only [decide, he, policyDecision]
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

end LeanSudo.Core
