import LeanSudo.Core

namespace LeanSudo.Intercept

structure Decision where
  allowed : Bool
  auth : Core.AuthReq := .none
  reason : Option String := none
  deriving Repr, BEq

def decide (ctx : Core.Context) (enforce setid : Bool) : Decision :=
  if !enforce then { allowed := true }
  else match Core.policyJudgement ctx with
  | .deny => { allowed := false, reason := some (Core.denialReason ctx) }
  | .allow a =>
    if setid && !ctx.settings.interceptAllowSetid then
      { allowed := false, reason := some "setid command rejected in intercept mode" }
    else { allowed := true, auth := if ctx.settings.interceptAuthenticate then
      Core.authentication ctx (.allow a) else .none }

def environment (env : Array String) : Array String := env

@[simp] theorem environment_preserved (env : Array String) : environment env = env := rfl

theorem allowed_only_by_policy (ctx : Core.Context) (setid : Bool)
    (h : (decide ctx true setid).allowed = true) :
    ∃ a, Core.policyJudgement ctx = .allow a := by
  unfold decide at h
  cases hj : Core.policyJudgement ctx with
  | deny => simp [hj] at h
  | allow a => exact ⟨a, rfl⟩

theorem request_identities (ctx : Core.Context) (run : ctx.opts.mode = .run) :
    (Core.request ctx).user = ctx.invoking ∧
    (Core.request ctx).runasUser = ctx.policyTarget.getD ctx.target := by
  simp [Core.request, run]

end LeanSudo.Intercept
