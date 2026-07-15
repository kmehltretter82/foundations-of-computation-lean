import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseEmbedding

set_option doc.verso true

/-!
# Retargetable phase embeddings

Exact and unbounded run lifting when an enclosing machine retargets an inner
phase endpoint.
-/

namespace FoC
namespace Computability
namespace TuringMachine
namespace PhaseRetarget

open PhaseEmbedding

/-- Lift an exact run when only actual inner steps need matching outer
steps. No condition is imposed on the reached endpoint. -/
theorem runConfigExact?_lift_active_of_eq_some
    {inner : TuringMachine symbol innerState}
    {outer : TuringMachine symbol outerState}
    (embed : innerState -> outerState)
    (hstep : forall
      (c d : Configuration symbol innerState),
      inner.stepConfig c = some d ->
        outer.stepConfig (liftConfig embed c) =
          some (liftConfig embed d)) :
    forall {steps : Nat}
      {source target : Configuration symbol innerState},
      inner.runConfigExact? steps source = some target ->
        outer.runConfigExact? steps (liftConfig embed source) =
          some (liftConfig embed target) := by
  intro steps
  induction steps with
  | zero =>
      intro source target hrun
      simp only [TuringMachine.runConfigExact?] at hrun ⊢
      cases hrun
      rfl
  | succ steps ih =>
      intro source target hrun
      rw [TuringMachine.runConfigExact?] at hrun ⊢
      cases hnext : inner.stepConfig source with
      | none =>
          rw [hnext] at hrun
          contradiction
      | some next =>
          rw [hnext] at hrun
          rw [hstep source next hnext]
          simp only
          exact ih hrun

end PhaseRetarget
end TuringMachine
end Computability
end FoC
