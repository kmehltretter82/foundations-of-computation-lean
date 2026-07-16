import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseEmbedding

namespace FoC
namespace Computability
namespace TuringMachine
namespace PhaseExitProjection

open PhaseEmbedding

/-- Project the initial embedded portion of an outer halting run back into its
inner phase.  Before the exit predicate holds, every outer step must invert to
an inner step with an embedded endpoint, and an embedded active configuration
must not already be the outer halt state. -/
theorem exists_bounded_inner_exit_of_haltsFromIn_lift
    {inner : TuringMachine symbol innerState}
    {outer : TuringMachine symbol outerState}
    (embed : innerState -> outerState)
    (exit : Configuration symbol innerState -> Prop)
    (hstep : forall
      (source : Configuration symbol innerState)
      (target : Configuration symbol outerState),
        ¬ exit source ->
        Step outer (liftConfig embed source) target ->
        exists innerTarget : Configuration symbol innerState,
          Step inner source innerTarget ∧
          target = liftConfig embed innerTarget)
    (hactive : forall source : Configuration symbol innerState,
      ¬ exit source -> ¬ Halted outer (liftConfig embed source)) :
    forall {steps : Nat} {source : Configuration symbol innerState},
      HaltsFromIn outer steps (liftConfig embed source) ->
      exists innerSteps : Nat,
      exists target : Configuration symbol innerState,
        innerSteps ≤ steps ∧
        ComputesIn inner innerSteps source target ∧
        exit target := by
  classical
  intro steps
  induction steps with
  | zero =>
      intro source hhalts
      by_cases hexit : exit source
      · exact ⟨0, source, Nat.le_refl 0, ComputesIn.zero source, hexit⟩
      · have hhalted : Halted outer (liftConfig embed source) :=
          haltsFromIn_zero_iff.mp hhalts
        exact False.elim (hactive source hexit hhalted)
  | succ steps ih =>
      intro source hhalts
      by_cases hexit : exit source
      · exact ⟨0, source, Nat.zero_le _, ComputesIn.zero source, hexit⟩
      · rcases haltsFromIn_succ_iff.mp hhalts with
          ⟨outerNext, houterStep, htail⟩
        rcases hstep source outerNext hexit houterStep with
          ⟨innerNext, hinnerStep, rfl⟩
        rcases ih htail with
          ⟨innerSteps, target, hsteps, hrun, htargetExit⟩
        exact
          ⟨innerSteps + 1, target, Nat.add_le_add_right hsteps 1,
            ComputesIn.succ hinnerStep hrun, htargetExit⟩

/-- Unbounded-reachability form of
{name}`exists_bounded_inner_exit_of_haltsFromIn_lift`. -/
theorem exists_inner_exit_of_haltsFromIn_lift
    {inner : TuringMachine symbol innerState}
    {outer : TuringMachine symbol outerState}
    (embed : innerState -> outerState)
    (exit : Configuration symbol innerState -> Prop)
    (hstep : forall
      (source : Configuration symbol innerState)
      (target : Configuration symbol outerState),
        ¬ exit source ->
        Step outer (liftConfig embed source) target ->
        exists innerTarget : Configuration symbol innerState,
          Step inner source innerTarget ∧
          target = liftConfig embed innerTarget)
    (hactive : forall source : Configuration symbol innerState,
      ¬ exit source -> ¬ Halted outer (liftConfig embed source))
    {steps : Nat}
    {source : Configuration symbol innerState}
    (hhalts : HaltsFromIn outer steps (liftConfig embed source)) :
    exists target : Configuration symbol innerState,
      Computes inner source target ∧ exit target := by
  rcases exists_bounded_inner_exit_of_haltsFromIn_lift embed exit hstep hactive
      hhalts with
    ⟨_innerSteps, target, _hsteps, hrun, htargetExit⟩
  exact ⟨target, computesIn_to_computes hrun, htargetExit⟩


end PhaseExitProjection
end TuringMachine
end Computability
end FoC
