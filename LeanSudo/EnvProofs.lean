import LeanSudo.Env

/-!
# Environment theorems

Headline properties of `buildEnv` (DESIGN.md, verified property 6):

* `buildEnv_nodup`: no duplicate keys.
* `buildEnv_reset_whitelist`: in reset mode without SETENV-granted extra variables,
  every variable is set by sudo, comes from PAM, or is whitelisted (`env_keep`, or
  `env_check` with a safe value).
* `buildEnv_delete_respected` / `buildEnv_no_LD`: without SETENV, a variable matching
  `env_delete` (e.g. `LD_*`) only survives if sudo sets it itself or an `env_keep` /
  `env_check` pattern whitelists it in reset mode.
* `buildEnv_no_bash_fn`: a bash-function value only appears under a key sudo sets
  itself from trusted data (`sudoValues`).
* `buildEnv_securePath`: `PATH = secure_path` and it is the only `PATH`.
* `buildEnv_sudo_vars`: `SUDO_COMMAND`, `SUDO_USER`, `SUDO_UID`, `SUDO_GID` are present
  with the invoking user's values (and unique by `buildEnv_unique`).
-/

namespace LeanSudo

/-! ## List lemmas -/

abbrev NodupKeys (e : EnvList) : Prop := (e.map Prod.fst).Nodup

theorem mem_setVar {e : EnvList} {k v : String} {kv : String × String} :
    kv ∈ setVar e k v ↔ (kv ∈ e ∧ kv.1 ≠ k) ∨ kv = (k, v) := by
  simp [setVar, List.mem_filter]

theorem mem_setVar_self (e : EnvList) (k v : String) : (k, v) ∈ setVar e k v :=
  mem_setVar.2 (Or.inr rfl)

theorem mem_setVar_of_ne {e : EnvList} {k v : String} {kv : String × String}
    (h : kv ∈ e) (hk : kv.1 ≠ k) : kv ∈ setVar e k v :=
  mem_setVar.2 (Or.inl ⟨h, hk⟩)

theorem mem_setDefault {e : EnvList} {k v : String} {kv : String × String}
    (h : kv ∈ setDefault e k v) : kv ∈ e ∨ kv = (k, v) := by
  unfold setDefault at h
  split at h
  · exact Or.inl h
  · simpa using h

theorem mem_setDefault_of_mem {e : EnvList} {k v : String} {kv : String × String}
    (h : kv ∈ e) : kv ∈ setDefault e k v := by
  unfold setDefault
  split
  · exact h
  · simp [h]

theorem mem_setAll {e l : EnvList} {kv : String × String} (h : kv ∈ setAll e l) :
    kv ∈ e ∨ kv ∈ l := by
  induction l generalizing e with
  | nil => exact Or.inl h
  | cons x rest ih =>
    obtain ⟨k, v⟩ := x
    rcases ih h with h' | h'
    · rcases mem_setVar.1 h' with ⟨h'', _⟩ | h''
      · exact Or.inl h''
      · exact Or.inr (by simp [h''])
    · exact Or.inr (List.mem_cons_of_mem _ h')

theorem mem_addDefaults {e l : EnvList} {kv : String × String} (h : kv ∈ addDefaults e l) :
    kv ∈ e ∨ kv ∈ l := by
  induction l generalizing e with
  | nil => exact Or.inl h
  | cons x rest ih =>
    obtain ⟨k, v⟩ := x
    rcases ih h with h' | h'
    · rcases mem_setDefault h' with h'' | h''
      · exact Or.inl h''
      · exact Or.inr (by simp [h''])
    · exact Or.inr (List.mem_cons_of_mem _ h')

theorem mem_addDefaults_of_mem {e l : EnvList} {kv : String × String} (h : kv ∈ e) :
    kv ∈ addDefaults e l := by
  induction l generalizing e with
  | nil => exact h
  | cons x rest ih =>
    obtain ⟨k, v⟩ := x
    exact ih (mem_setDefault_of_mem h)

theorem lookup_mem {e : EnvList} {k v : String} (h : lookup e k = some v) : (k, v) ∈ e := by
  unfold lookup at h
  cases hf : e.find? (fun kv => kv.1 == k) with
  | none => simp [hf] at h
  | some kv =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    have hm := List.mem_of_find?_eq_some hf
    have hk := List.find?_some hf
    obtain ⟨k', v'⟩ := kv
    simp at hk h
    subst hk h
    exact hm

theorem nodup_setVar {e : EnvList} (k v : String) (h : NodupKeys e) :
    NodupKeys (setVar e k v) := by
  unfold NodupKeys setVar
  rw [List.map_append, List.nodup_append]
  refine ⟨?_, by simp, ?_⟩
  · exact (List.filter_sublist.map _).nodup h
  · intro a ha b hb
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
    simp only [List.mem_map, List.mem_filter] at ha
    obtain ⟨kv, ⟨_, hne⟩, rfl⟩ := ha
    subst hb
    simpa using hne

theorem nodup_setDefault {e : EnvList} (k v : String) (h : NodupKeys e) :
    NodupKeys (setDefault e k v) := by
  unfold setDefault
  split
  · exact h
  · rename_i hk
    unfold NodupKeys
    rw [List.map_append, List.nodup_append]
    refine ⟨h, by simp, ?_⟩
    intro a ha b hb
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
    subst hb
    intro hab
    subst hab
    simp only [List.mem_map] at ha
    obtain ⟨kv, hkv, rfl⟩ := ha
    exact hk (List.any_eq_true.2 ⟨kv, hkv, by simp⟩)

theorem nodup_setAll {e : EnvList} (l : EnvList) (h : NodupKeys e) : NodupKeys (setAll e l) := by
  induction l generalizing e with
  | nil => exact h
  | cons x rest ih => obtain ⟨k, v⟩ := x; exact ih (nodup_setVar k v h)

theorem nodup_addDefaults {e : EnvList} (l : EnvList) (h : NodupKeys e) :
    NodupKeys (addDefaults e l) := by
  induction l generalizing e with
  | nil => exact h
  | cons x rest ih => obtain ⟨k, v⟩ := x; exact ih (nodup_setDefault k v h)

theorem nodup_unique {e : EnvList} (h : NodupKeys e) {k v₁ v₂ : String}
    (h₁ : (k, v₁) ∈ e) (h₂ : (k, v₂) ∈ e) : v₁ = v₂ := by
  induction e with
  | nil => simp at h₁
  | cons x rest ih =>
    simp only [NodupKeys, List.map_cons, List.nodup_cons, List.mem_map] at h
    obtain ⟨hx, hr⟩ := h
    simp only [List.mem_cons] at h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · subst h₁; cases h₂; rfl
    · subst h₁; exact absurd ⟨_, h₂, rfl⟩ hx
    · subst h₂; exact absurd ⟨_, h₁, rfl⟩ hx
    · exact ih hr h₁ h₂

/-! ## Invariants over the construction steps -/

/-- Every entry satisfies `P`. -/
def Inv (P : String × String → Prop) (e : EnvList) : Prop := ∀ kv ∈ e, P kv

theorem inv_nil (P : String × String → Prop) : Inv P [] := by simp [Inv]

theorem inv_setVar {P : String × String → Prop} {e : EnvList} {k v : String}
    (h : Inv P e) (hkv : P (k, v)) : Inv P (setVar e k v) := by
  intro kv hm
  rcases mem_setVar.1 hm with ⟨hm', _⟩ | rfl
  · exact h kv hm'
  · exact hkv

theorem inv_setDefault {P : String × String → Prop} {e : EnvList} {k v : String}
    (h : Inv P e) (hkv : P (k, v)) : Inv P (setDefault e k v) := by
  intro kv hm
  rcases mem_setDefault hm with hm' | rfl
  · exact h kv hm'
  · exact hkv

theorem inv_setAll {P : String × String → Prop} {e l : EnvList}
    (h : Inv P e) (hl : ∀ kv ∈ l, P kv) : Inv P (setAll e l) := by
  intro kv hm
  rcases mem_setAll hm with hm' | hm'
  · exact h kv hm'
  · exact hl kv hm'

theorem inv_addDefaults {P : String × String → Prop} {e l : EnvList}
    (h : Inv P e) (hl : ∀ kv ∈ l, P kv) : Inv P (addDefaults e l) := by
  intro kv hm
  rcases mem_addDefaults hm with hm' | hm'
  · exact h kv hm'
  · exact hl kv hm'

/-! ## Provenance of every output entry -/

/-- The values sudo sets itself, from trusted data (passwd entries, the resolved
command, `secure_path`, constants). -/
def sudoValues (i : EnvInput) : EnvList :=
  [("HOME", i.target.home), ("LOGNAME", i.target.name), ("USER", i.target.name),
   ("MAIL", "/var/mail/" ++ i.target.name), ("SHELL", i.target.shell), ("TERM", "unknown"),
   ("PATH", stdPath), ("PATH", loginPath), ("SUDO_COMMAND", i.command),
   ("SUDO_USER", i.invoking.name), ("SUDO_UID", toString i.invoking.uid),
   ("SUDO_GID", toString i.invoking.gid)] ++
  (match i.settings.securePath with
   | some p => [("PATH", p)]
   | none => [])

/-- Where an entry of `assemble i reset extra` can come from. -/
def Origin (i : EnvInput) (reset : Bool) (extra : EnvList) (kv : String × String) : Prop :=
  -- a user variable that passed the filter
  (kv ∈ i.userEnv ∧ userPass i reset kv.1 kv.2 = true) ∨
  -- LOGNAME/USER copied from a preserved LOGNAME/USER
  (kv.1 ∈ ["LOGNAME", "USER"] ∧ ∃ k', (k', kv.2) ∈ i.userEnv ∧ userPass i reset k' kv.2 = true) ∨
  -- PS1 from SUDO_PS1
  (kv.1 = "PS1" ∧ ("SUDO_PS1", kv.2) ∈ i.userEnv ∧ entryOk "SUDO_PS1" kv.2 = true) ∨
  -- a command-line / --preserve-env=list variable
  kv ∈ extra ∨
  -- a PAM variable that passed the filter
  (kv ∈ i.pamEnv ∧ pamPass i kv.1 kv.2 = true) ∨
  -- set by sudo
  kv ∈ sudoValues i

theorem inv_baseEnv (i : EnvInput) (reset : Bool) (extra : EnvList) :
    Inv (Origin i reset extra) (baseEnv i reset) := by
  unfold baseEnv
  refine inv_setAll (inv_nil _) ?_
  intro kv hm
  rw [List.mem_filter] at hm
  exact Or.inl hm

theorem baseEnv_user {i : EnvInput} {reset : Bool} {kv : String × String}
    (h : kv ∈ baseEnv i reset) : kv ∈ i.userEnv ∧ userPass i reset kv.1 kv.2 = true := by
  unfold baseEnv at h
  rcases mem_setAll h with h | h
  · simp at h
  · exact List.mem_filter.1 h

theorem inv_defaultsReset (i : EnvInput) (reset : Bool) (extra : EnvList) :
    Inv (Origin i reset extra) (defaultsReset i (baseEnv i reset)) := by
  have hb := inv_baseEnv i reset extra
  have sv : ∀ kv ∈ sudoValues i, Origin i reset extra kv := fun kv h => by
    simp only [Origin]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  have copy : ∀ k k' v, k ∈ ["LOGNAME", "USER"] → (k', v) ∈ baseEnv i reset →
      Origin i reset extra (k, v) := fun k k' v hk hm => by
    have := baseEnv_user hm
    exact Or.inr (Or.inl ⟨hk, k', this.1, this.2⟩)
  have h1 : Inv (Origin i reset extra)
      (if i.loginShell then
        setVar (setVar (setVar (baseEnv i reset) "SHELL" i.target.shell) "LOGNAME" i.target.name)
          "USER" i.target.name
      else lognameReset i (baseEnv i reset)) := by
    split
    · exact inv_setVar (inv_setVar (inv_setVar hb (sv _ (by simp [sudoValues])))
        (sv _ (by simp [sudoValues]))) (sv _ (by simp [sudoValues]))
    · unfold lognameReset
      split
      · exact inv_setVar (inv_setVar hb (sv _ (by simp [sudoValues]))) (sv _ (by simp [sudoValues]))
      · rename_i l _ hl _
        exact inv_setVar hb (copy _ _ _ (by simp) (lookup_mem hl))
      · rename_i u _ hu
        exact inv_setVar hb (copy _ _ _ (by simp) (lookup_mem hu))
      · exact hb
  unfold defaultsReset
  simp only
  split <;> split
  all_goals first
    | exact inv_setVar (inv_setVar h1 (sv _ (by simp [sudoValues]))) (sv _ (by simp [sudoValues]))
    | exact inv_setVar h1 (sv _ (by simp [sudoValues]))
    | exact h1

theorem inv_defaultsCopy (i : EnvInput) (reset : Bool) (extra : EnvList) :
    Inv (Origin i reset extra) (defaultsCopy i (baseEnv i reset)) := by
  have hb := inv_baseEnv i reset extra
  have sv : ∀ kv ∈ sudoValues i, Origin i reset extra kv := fun kv h => by
    simp only [Origin]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  unfold defaultsCopy
  simp only
  have h1 := inv_setVar (inv_setVar hb (sv ("LOGNAME", i.target.name) (by simp [sudoValues])))
    (sv ("USER", i.target.name) (by simp [sudoValues]))
  split
  · exact inv_setVar h1 (sv _ (by simp [sudoValues]))
  · exact h1

theorem inv_commonDefaults (i : EnvInput) (reset : Bool) (extra : EnvList) {e : EnvList}
    (he : Inv (Origin i reset extra) e) : Inv (Origin i reset extra) (commonDefaults i e) := by
  have sv : ∀ kv ∈ sudoValues i, Origin i reset extra kv := fun kv h => by
    simp only [Origin]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  unfold commonDefaults
  simp only
  have h2 := inv_setDefault (inv_setDefault he (sv ("SHELL", i.target.shell) (by simp [sudoValues])))
    (sv ("TERM", "unknown") (by simp [sudoValues]))
  have h3 : Inv (Origin i reset extra)
      (if i.loginShell = true then setVar (setDefault (setDefault e "SHELL" i.target.shell) "TERM" "unknown") "PATH" loginPath
       else setDefault (setDefault (setDefault e "SHELL" i.target.shell) "TERM" "unknown") "PATH" stdPath) := by
    split
    · exact inv_setVar h2 (sv _ (by simp [sudoValues]))
    · exact inv_setDefault h2 (sv _ (by simp [sudoValues]))
  split
  · rename_i ps1 hps
    refine inv_setVar h3 ?_
    have hm := List.mem_filter.1 (lookup_mem hps)
    exact Or.inr (Or.inr (Or.inl ⟨rfl, hm.1, hm.2⟩))
  · exact h3

theorem mem_assemble_origin {i : EnvInput} {reset : Bool} {extra : EnvList} {kv : String × String}
    (h : kv ∈ assemble i reset extra) : Origin i reset extra kv := by
  have sv : ∀ kv ∈ sudoValues i, Origin i reset extra kv := fun kv h => by
    simp only [Origin]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  have h1 : Inv (Origin i reset extra)
      (if reset then defaultsReset i (baseEnv i reset) else defaultsCopy i (baseEnv i reset)) := by
    split
    · exact inv_defaultsReset i reset extra
    · exact inv_defaultsCopy i reset extra
  have h2 := inv_commonDefaults i reset extra h1
  have h3 := inv_setAll (l := extra) h2 (fun kv hm => Or.inr (Or.inr (Or.inr (Or.inl hm))))
  have h4 : Inv (Origin i reset extra) (applySecurePath i (setAll (commonDefaults i
      (if reset then defaultsReset i (baseEnv i reset) else defaultsCopy i (baseEnv i reset))) extra)) := by
    unfold applySecurePath
    split
    · rename_i p hp
      exact inv_setVar h3 (sv _ (by simp [sudoValues, hp]))
    · exact h3
  have h5 := inv_setVar (inv_setVar (inv_setVar (inv_setVar h4
    (sv ("SUDO_COMMAND", i.command) (by simp [sudoValues])))
    (sv ("SUDO_USER", i.invoking.name) (by simp [sudoValues])))
    (sv ("SUDO_UID", toString i.invoking.uid) (by simp [sudoValues])))
    (sv ("SUDO_GID", toString i.invoking.gid) (by simp [sudoValues]))
  have h6 := inv_addDefaults (l := pamVars i) h5 (fun kv hm => by
    have := List.mem_filter.1 hm
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl this)))))
  exact h6 kv h

theorem nodup_assemble (i : EnvInput) (reset : Bool) (extra : EnvList) :
    NodupKeys (assemble i reset extra) := by
  have h0 : NodupKeys (baseEnv i reset) := nodup_setAll _ (by simp [NodupKeys])
  have h1 : NodupKeys
      (if reset then defaultsReset i (baseEnv i reset) else defaultsCopy i (baseEnv i reset)) := by
    split
    · unfold defaultsReset lognameReset
      simp only
      split <;> split <;> (try split) <;> (try split)
      all_goals
        repeat first
          | exact h0
          | apply nodup_setVar
    · unfold defaultsCopy
      simp only
      split <;> repeat first | exact h0 | apply nodup_setVar
  unfold assemble commonDefaults applySecurePath sudoVars
  simp only
  apply nodup_addDefaults
  repeat apply nodup_setVar
  split
  all_goals first
    | apply nodup_setVar
    | skip
  all_goals apply nodup_setAll
  all_goals (try split) <;> (try apply nodup_setVar)
  all_goals (try split) <;> (try apply nodup_setVar) <;> (try apply nodup_setDefault)
  all_goals repeat first | exact h1 | apply nodup_setDefault

/-! ## `buildEnv` -/

theorem buildEnv_ok {i : EnvInput} {out : EnvList} (h : buildEnv i = .ok out) :
    out = assemble i (resetMode i) (extraVars i) ∧
    (∀ kv ∈ extraVars i, extraAllowed i (resetMode i) kv.1 kv.2 = true) ∧
    (wantsPreserveAll i = true → i.setenvAllowed = true) := by
  unfold buildEnv at h
  cases hpre : (wantsPreserveAll i && !i.setenvAllowed) with
  | true => simp only [hpre, ↓reduceIte] at h; cases h
  | false =>
    simp only [hpre, Bool.false_eq_true, ↓reduceIte] at h
    cases hb : (List.filter (fun kv => !extraAllowed i (resetMode i) kv.1 kv.2) (extraVars i)).isEmpty with
    | false =>
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
      cases h
    | true =>
      simp only [hb, ↓reduceIte] at h
      cases h
      refine ⟨rfl, ?_, ?_⟩
      · intro kv hm
        have := List.filter_eq_nil_iff.1 (List.isEmpty_iff.1 hb) kv hm
        simpa using this
      · intro hall
        revert hpre hall
        unfold wantsPreserveAll
        cases i.preserve <;> cases i.setenvAllowed <;> simp

/-- (a) No duplicate keys. -/
theorem buildEnv_nodup {i : EnvInput} {out : EnvList} (h : buildEnv i = .ok out) :
    (out.map Prod.fst).Nodup := by
  obtain ⟨rfl, -, -⟩ := buildEnv_ok h
  exact nodup_assemble _ _ _

/-- Each key has a single value. -/
theorem buildEnv_unique {i : EnvInput} {out : EnvList} (h : buildEnv i = .ok out)
    {k v₁ v₂ : String} (h₁ : (k, v₁) ∈ out) (h₂ : (k, v₂) ∈ out) : v₁ = v₂ :=
  nodup_unique (buildEnv_nodup h) h₁ h₂

theorem buildEnv_origin {i : EnvInput} {out : EnvList} (h : buildEnv i = .ok out)
    {kv : String × String} (hm : kv ∈ out) : Origin i (resetMode i) (extraVars i) kv := by
  obtain ⟨rfl, -, -⟩ := buildEnv_ok h
  exact mem_assemble_origin hm

theorem sudoValues_key {i : EnvInput} {kv : String × String} (h : kv ∈ sudoValues i) :
    kv.1 ∈ sudoKeys := by
  obtain ⟨k, v⟩ := kv
  unfold sudoValues at h
  rw [List.mem_append] at h
  simp only [sudoKeys, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with h | h
  · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
      ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  · split at h
    · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
      obtain ⟨rfl, -⟩ := h
      simp
    · simp at h

/-- (b) In reset mode, when no extra variables were granted through SETENV, every
variable is set by sudo, is a filtered PAM variable, or is whitelisted: it matches
`env_check` and has a safe value, or it matches no `env_check` pattern but an
`env_keep` pattern. -/
theorem buildEnv_reset_whitelist {i : EnvInput} {out : EnvList} (h : buildEnv i = .ok out)
    (hr : resetMode i = true) (hx : i.setenvAllowed = false ∨ extraVars i = [])
    {kv : String × String} (hm : kv ∈ out) :
    kv.1 ∈ sudoKeys ∨ (kv ∈ i.pamEnv ∧ pamPass i kv.1 kv.2 = true) ∨
    ((∃ p ∈ i.settings.envCheck, patMatch p kv.1 = true) ∧ checkSafe kv.1 kv.2 = true) ∨
    ((∀ p ∈ i.settings.envCheck, patMatch p kv.1 = false) ∧
      ∃ p ∈ i.settings.envKeep, patMatch p kv.1 = true) := by
  obtain ⟨_, hallowed, _⟩ := buildEnv_ok h
  have hkeep : ∀ k v, keepReset i k v = true → k ∈ sudoKeys ∨
      ((∃ p ∈ i.settings.envCheck, patMatch p k = true) ∧ checkSafe k v = true) ∨
      ((∀ p ∈ i.settings.envCheck, patMatch p k = false) ∧
        ∃ p ∈ i.settings.envKeep, patMatch p k = true) := by
    intro k v hk
    unfold keepReset matchesAny at hk
    split at hk
    · rename_i hc
      exact Or.inr (Or.inl ⟨List.any_eq_true.1 hc, hk⟩)
    · rename_i hc
      simp only [Bool.not_eq_true, List.any_eq_false] at hc
      simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq, Bool.and_eq_true] at hk
      rcases hk with (hk | hk) | ⟨_, hk⟩
      · exact Or.inr (Or.inr ⟨fun p hp => by simpa using hc p hp, hk⟩)
      · exact Or.inl (by simp [hk, sudoKeys])
      · exact Or.inl (by simp [hk, sudoKeys])
  rcases buildEnv_origin h hm with ⟨_, hu⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | hx' | hp | hs
  · simp only [userPass, hr, ↓reduceIte, Bool.and_eq_true] at hu
    rcases hkeep _ _ hu.2 with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr h')
  · left; simp at hk; rcases hk with hk | hk <;> simp [hk, sudoKeys]
  · left; simp [hk, sudoKeys]
  · rcases hx with hs | hnil
    · have := hallowed kv hx'
      simp only [extraAllowed, hs, hr, ↓reduceIte, Bool.false_or, Bool.and_eq_true] at this
      rcases hkeep _ _ this.2.2 with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')
    · rw [hnil] at hx'; simp at hx'
  · exact Or.inr (Or.inl hp)
  · exact Or.inl (sudoValues_key hs)

/-- (c) Without SETENV, a variable whose name matches `env_delete` survives only if sudo
sets it itself, or in reset mode when it is explicitly whitelisted. -/
theorem buildEnv_delete_respected {i : EnvInput} {out : EnvList} (h : buildEnv i = .ok out)
    (hs : i.setenvAllowed = false) {kv : String × String} (hm : kv ∈ out)
    (hd : matchesAny i.settings.envDelete kv.1 = true) :
    kv.1 ∈ sudoKeys ∨ (resetMode i = true ∧ keepReset i kv.1 kv.2 = true) := by
  obtain ⟨_, hallowed, _⟩ := buildEnv_ok h
  rcases buildEnv_origin h hm with ⟨_, hu⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | hx' | hp | hsv
  · unfold userPass at hu
    cases hr : resetMode i
    · simp [hr, deleteCopy, hd] at hu
    · simp only [hr, ↓reduceIte, Bool.and_eq_true] at hu
      exact Or.inr ⟨rfl, hu.2⟩
  · left; simp at hk; rcases hk with hk | hk <;> simp [hk, sudoKeys]
  · left; simp [hk, sudoKeys]
  · have := hallowed kv hx'
    unfold extraAllowed at this
    cases hr : resetMode i
    · simp [hr, hs, deleteCopy, hd] at this
    · simp only [hr, hs, ↓reduceIte, Bool.false_or, Bool.and_eq_true] at this
      exact Or.inr ⟨rfl, this.2.2⟩
  · simp [pamPass, hd] at hp
  · exact Or.inl (sudoValues_key hsv)

theorem patMatch_LD_sudoKeys {k : String} (hk : k ∈ sudoKeys) : patMatch "LD_*" k = false := by
  simp only [sudoKeys, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- (c) `LD_*`: when `env_delete` contains `LD_*` (sudo's default) and the user has no
SETENV permission, an `LD_` variable is present only in reset mode and only if an
`env_keep` pattern, or an `env_check` pattern with a safe value, names it. -/
theorem buildEnv_no_LD {i : EnvInput} {out : EnvList} (h : buildEnv i = .ok out)
    (hdel : "LD_*" ∈ i.settings.envDelete) (hs : i.setenvAllowed = false)
    {k v : String} (hm : (k, v) ∈ out) (hld : patMatch "LD_*" k = true) :
    resetMode i = true ∧
    ((∃ p ∈ i.settings.envCheck, patMatch p k = true) ∧ checkSafe k v = true ∨
     ∃ p ∈ i.settings.envKeep, patMatch p k = true) := by
  have hd : matchesAny i.settings.envDelete k = true := List.any_eq_true.2 ⟨_, hdel, hld⟩
  rcases buildEnv_delete_respected h hs hm hd with hk | ⟨hr, hkeep⟩
  · rw [patMatch_LD_sudoKeys hk] at hld; cases hld
  · refine ⟨hr, ?_⟩
    unfold keepReset matchesAny at hkeep
    split at hkeep
    · exact Or.inl ⟨List.any_eq_true.1 (by assumption), hkeep⟩
    · simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq, Bool.and_eq_true] at hkeep
      rcases hkeep with (hk | rfl) | ⟨_, rfl⟩
      · exact Or.inr hk
      · cases hld
      · cases hld

/-- `patMatch "LD_*" k` is exactly "`k` starts with `LD_`". -/
theorem patMatch_LD_iff (k : String) :
    patMatch "LD_*" k = true ↔ ∃ r, k.toList = 'L' :: 'D' :: '_' :: r := by
  unfold patMatch
  have : "LD_*".toList = ['L', 'D', '_', '*'] := by decide
  rw [this]
  match k.toList with
  | [] => simp [patMatchL]
  | [_] => simp [patMatchL]
  | [_, _] => simp [patMatchL]
  | a :: b :: c :: r =>
    simp [patMatchL]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩; simp
    · rintro ⟨rfl, rfl, rfl⟩; simp

/-- (c) Bash function exports never come from the user's environment, the command line
or PAM: a value starting with `()` can only be one sudo set from trusted data. -/
theorem buildEnv_no_bash_fn {i : EnvInput} {out : EnvList} (h : buildEnv i = .ok out)
    {kv : String × String} (hm : kv ∈ out) (hf : isBashFn kv.2 = true) :
    kv ∈ sudoValues i := by
  obtain ⟨_, hallowed, _⟩ := buildEnv_ok h
  rcases buildEnv_origin h hm with ⟨_, hu⟩ | ⟨_, k', _, hu⟩ | ⟨_, _, he⟩ | hx' | hp | hsv
  · simp [userPass, entryOk, hf] at hu
  · simp [userPass, entryOk, hf] at hu
  · simp [entryOk, hf] at he
  · have := hallowed kv hx'
    simp [extraAllowed, entryOk, hf] at this
  · simp [pamPass, entryOk, hf] at hp
  · exact hsv

/-- (d) `secure_path` is the one and only `PATH`. -/
theorem buildEnv_securePath {i : EnvInput} {out : EnvList} (h : buildEnv i = .ok out)
    {p : String} (hp : i.settings.securePath = some p) :
    ("PATH", p) ∈ out ∧ ∀ v, ("PATH", v) ∈ out → v = p := by
  have hmem : ("PATH", p) ∈ out := by
    obtain ⟨rfl, -, -⟩ := buildEnv_ok h
    unfold assemble sudoVars applySecurePath
    simp only [hp]
    apply mem_addDefaults_of_mem
    refine mem_setVar_of_ne (mem_setVar_of_ne (mem_setVar_of_ne (mem_setVar_of_ne
      (mem_setVar_self _ _ _) ?_) ?_) ?_) ?_ <;> (dsimp only; decide)
  exact ⟨hmem, fun v hv => buildEnv_unique h hv hmem⟩

/-- (e) `SUDO_COMMAND`, `SUDO_USER`, `SUDO_UID` and `SUDO_GID` carry the command and the
invoking user's name, uid and gid (and, by `buildEnv_unique`, no other value). -/
theorem buildEnv_sudo_vars {i : EnvInput} {out : EnvList} (h : buildEnv i = .ok out) :
    ("SUDO_COMMAND", i.command) ∈ out ∧ ("SUDO_USER", i.invoking.name) ∈ out ∧
    ("SUDO_UID", toString i.invoking.uid) ∈ out ∧ ("SUDO_GID", toString i.invoking.gid) ∈ out := by
  obtain ⟨rfl, -, -⟩ := buildEnv_ok h
  unfold assemble sudoVars
  simp only
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply mem_addDefaults_of_mem
  · refine mem_setVar_of_ne (mem_setVar_of_ne (mem_setVar_of_ne (mem_setVar_self _ _ _) ?_) ?_) ?_ <;>
      (dsimp only; decide)
  · refine mem_setVar_of_ne (mem_setVar_of_ne (mem_setVar_self _ _ _) ?_) ?_ <;> (dsimp only; decide)
  · exact mem_setVar_of_ne (mem_setVar_self _ _ _) (by dsimp only; decide)
  · exact mem_setVar_self _ _ _

/-- `-E` without SETENV permission is refused. -/
theorem buildEnv_preserve_denied {i : EnvInput} (hp : i.preserve = .all)
    (hs : i.setenvAllowed = false) : buildEnv i = .error preserveDeniedMsg := by
  simp [buildEnv, wantsPreserveAll, hp, hs]

/-- A command-line variable that is not allowed makes `buildEnv` fail. -/
theorem buildEnv_extra_denied {i : EnvInput} {kv : String × String} (hm : kv ∈ extraVars i)
    (hna : extraAllowed i (resetMode i) kv.1 kv.2 = false) : ∀ out, buildEnv i ≠ .ok out := by
  intro out h
  have := (buildEnv_ok h).2.1 kv hm
  rw [hna] at this
  cases this

end LeanSudo
