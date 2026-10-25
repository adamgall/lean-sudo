import LeanSudo
import Lean

/-!
Axiom audit. Every declaration (theorems, definitions, instances, private and
auto-generated ones included) defined in a `LeanSudo.*` module may depend only on Lean's
three standard axioms (`propext`, `Quot.sound`, `Classical.choice`). Any other axiom,
in particular `sorryAx` (from `sorry`/`admit`) or `Lean.ofReduceBool` (from
`native_decide`), makes this file fail to elaborate.

  lake build LeanSudo && lake env lean scripts/AxiomAudit.lean

Complements the source-level grep (no `sorry`/`admit`/`native_decide`/`implemented_by`).
-/

open Lean Elab Command

def allowedAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- Declarations whose defining module is `LeanSudo` or `LeanSudo.*`. -/
def inLeanSudo (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (`LeanSudo).isPrefixOf (env.header.moduleNames[idx.toNat]!)
  | none => false

elab "#audit_axioms" : command => do
  let env ← getEnv
  let mut decls : Nat := 0
  let mut thms : Nat := 0
  let mut bad : Array (Name × Name) := #[]
  for (n, ci) in env.constants.toList do
    unless inLeanSudo env n do continue
    decls := decls + 1
    if ci matches .thmInfo _ then thms := thms + 1
    for a in ← liftCoreM (Lean.collectAxioms n) do
      unless allowedAxioms.contains a do bad := bad.push (n, a)
  if bad.isEmpty then
    logInfo m!"{decls} declarations ({thms} theorems) checked; axioms used ⊆ propext, Quot.sound, Classical.choice"
  else
    throwError m!"non-standard axioms: {bad.toList}"

#audit_axioms
