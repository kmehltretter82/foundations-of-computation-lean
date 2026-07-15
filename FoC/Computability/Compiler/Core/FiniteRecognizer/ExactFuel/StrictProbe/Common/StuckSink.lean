import FoC.Computability.TuringMachine

set_option doc.verso true

/-!
# Stuck non-halt endpoints

Inversion principles for deterministic computations that reach a
transitionless non-halt configuration.
-/

namespace FoC
namespace Computability
namespace TuringMachine
namespace StuckSink

/-- If a deterministic computation reaches a stuck non-halt configuration,
then its source cannot halt. -/
theorem not_haltsFrom_of_computes_to_stuck_nonhalt
    {M : TuringMachine symbol state}
    (hstop : HaltingTransitionsDisabled M)
    {source stuck : Configuration symbol state}
    (hrun : Computes M source stuck)
    (hnotHalt : ¬ Halted M stuck)
    (hstuck : forall next, ¬ Step M stuck next) :
    ¬ HaltsFrom M source := by
  induction hrun with
  | refl source =>
      intro hhalt
      rcases hhalt with ⟨final, hfinal, hhalted⟩
      cases hfinal with
      | refl =>
          exact hnotHalt hhalted
      | step hstep _ =>
          exact hstuck _ hstep
  | step hstep htail ih =>
      intro hhalt
      rcases hhalt with ⟨final, hfinal, hhalted⟩
      cases hfinal with
      | refl =>
          exact no_step_from_halted hstop hhalted hstep
      | step hstep' hfinalTail =>
          have hnext := step_deterministic hstep hstep'
          cases hnext
          exact ih hnotHalt hstuck ⟨final, hfinalTail, hhalted⟩

end StuckSink
end TuringMachine
end Computability
end FoC
