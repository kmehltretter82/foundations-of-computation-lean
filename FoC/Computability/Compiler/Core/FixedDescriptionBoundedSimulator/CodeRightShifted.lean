import FoC.Computability.Compiler.Core.ConstructionTargets

set_option doc.verso true

/-!
# Right-shifted fixed-description simulator code construction target

This module keeps the finite-machine leaf for compiling
{name}`FoC.Computability.FixedDescriptionBoundedSimulatorCode` with the other
fixed-description simulator construction targets.  Downstream config-runner
modules should consume this target as an input and remain adapter glue.

The bounded-layout config runner imports this file while assembling its
closed-handoff construction, so the construction here must remain independent
of that downstream assembly.
-/

namespace FoC
namespace Computability

/-- Finite-machine leaf for the right-shifted fixed-description simulator. -/
theorem fixedDescriptionBoundedSimulatorCodeRightShiftedConstruction_scaffold :
    FixedDescriptionBoundedSimulatorCodeRightShiftedConstruction := by
  sorry

end Computability
end FoC
