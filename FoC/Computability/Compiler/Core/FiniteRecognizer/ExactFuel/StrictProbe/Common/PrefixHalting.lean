import FoC.Computability.TuringMachine

set_option doc.verso true

/-!
# Halting across known prefixes

Halting equivalences across deterministic finite computation prefixes.
-/

namespace FoC
namespace Computability
namespace TuringMachine
namespace PrefixHalting

/-- Under the halt-disabled convention, taking one deterministic step neither
creates nor destroys eventual halting. -/
theorem haltsFrom_iff_of_step
    {M : TuringMachine symbol state}
    (hstop : HaltingTransitionsDisabled M)
    {source target : Configuration symbol state}
    (hstep : Step M source target) :
    HaltsFrom M source <-> HaltsFrom M target := by
  constructor
  · intro hhalt
    rcases hhalt with ⟨final, hrun, hfinal⟩
    cases hrun with
    | refl _ =>
        exact False.elim (no_step_from_halted hstop hfinal hstep)
    | step hfirst htail =>
        have htarget := step_deterministic hstep hfirst
        cases htarget
        exact ⟨final, htail, hfinal⟩
  · intro hhalt
    exact halts_from_of_computes_prefix
      (computes_of_step hstep) hhalt

/-- Eventual halting is invariant across a known finite prefix when the halt
state has no outgoing transitions. -/
theorem haltsFrom_iff_of_computes
    {M : TuringMachine symbol state}
    (hstop : HaltingTransitionsDisabled M)
    {source target : Configuration symbol state}
    (hrun : Computes M source target) :
    HaltsFrom M source <-> HaltsFrom M target := by
  induction hrun with
  | refl _ =>
      rfl
  | step hstep _ ih =>
      exact Iff.trans (haltsFrom_iff_of_step hstop hstep) ih

end PrefixHalting
end TuringMachine
end Computability
end FoC
