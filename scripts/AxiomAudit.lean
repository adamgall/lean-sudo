import LeanSudo
import Lean

/-!
Proof audit: every theorem in the `LeanSudo` namespace may depend only on Lean's three
standard axioms (`propext`, `Quot.sound`, `Classical.choice`). Any other axiom (including
`sorryAx`, or `Lean.ofReduceBool` from `native_decide`) makes this file fail to elaborate.

  lake build LeanSudo && lake env lean scripts/AxiomAudit.lean
-/

open Lean Elab Command

def allowedAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

elab "#audit_axioms" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  let mut bad : Array (Name × Name) := #[]
  for (n, ci) in env.constants.toList do
    unless (`LeanSudo).isPrefixOf n do continue
    let .thmInfo _ := ci | continue
    if n.isInternal then continue
    count := count + 1
    let axs ← liftCoreM <| Lean.collectAxioms n
    for a in axs do
      unless allowedAxioms.contains a do bad := bad.push (n, a)
  if bad.isEmpty then
    logInfo m!"{count} theorems checked; axioms used ⊆ propext, Quot.sound, Classical.choice"
  else
    throwError m!"non-standard axioms: {bad.toList}"

#audit_axioms
