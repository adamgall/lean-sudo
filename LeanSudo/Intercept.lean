import LeanSudo.Core

/-! Policy for an exec requested by an already-running command.  Unlike a new sudo
invocation, intercepted commands keep their supplied environment and the original
invoking/run-as identities.  Log-only interception does not authorize commands. -/
namespace LeanSudo.Intercept

structure Decision where
  allowed : Bool
  auth : Core.AuthReq := .none
  reason : Option String := none
  deriving Repr, BEq

/-- The callback's context contains refreshed command facts, but the identity of
both principals comes from the original sudo invocation, never from the tracee. -/
def decide (ctx : Core.Context) (enforce setid : Bool) : Decision :=
  if !enforce then { allowed := true }
  else match Core.policyJudgement ctx with
  | .deny => { allowed := false, reason := some (Core.denialReason ctx) }
  | .allow a =>
    if setid && !ctx.settings.interceptAllowSetid then
      { allowed := false, reason := some "setid command rejected in intercept mode" }
    else { allowed := true, auth := if ctx.settings.interceptAuthenticate then
      Core.authentication ctx (.allow a) else .none }

/-- Upstream's intercepted check deliberately does not rebuild or validate the
sub-command environment: exec_intercept.c copies the supplied envp unchanged. -/
def environment (env : Array String) : Array String := env

@[simp] theorem environment_preserved (env : Array String) : environment env = env := rfl

/-- Enforcement can allow an intercepted exec only if the policy allows that
exact request, with the original caller and run-as identities. -/
theorem allowed_only_by_policy (ctx : Core.Context) (setid : Bool)
    (h : (decide ctx true setid).allowed = true) :
    ∃ a, Core.policyJudgement ctx = .allow a := by
  unfold decide at h
  cases hj : Core.policyJudgement ctx with
  | deny => simp [hj] at h
  | allow a => exact ⟨a, rfl⟩

/-- Neither an intercepted command nor its environment can select a new caller
or target: those are fields of the captured invocation context. -/
theorem request_identities (ctx : Core.Context) (run : ctx.opts.mode = .run) :
    (Core.request ctx).user = ctx.invoking ∧
    (Core.request ctx).runasUser = ctx.policyTarget.getD ctx.target := by
  simp [Core.request, run]

end LeanSudo.Intercept
