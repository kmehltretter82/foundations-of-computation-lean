import FoC.Computability.Compiler.Core.ConstructionTargets

set_option doc.verso true

/-!
# Right-shifted fixed-description simulator code construction target

This module keeps the finite-machine leaf for compiling
{name}`FoC.Computability.FixedDescriptionBoundedSimulatorCode` with the other
fixed-description simulator construction targets.  Downstream config-runner
modules should consume this target as an input and remain adapter glue.
-/

namespace FoC
namespace Computability

open Languages

theorem fixedDescriptionBoundedSimulatorCodeRightShiftedConstruction_scaffold :
    FixedDescriptionBoundedSimulatorCodeRightShiftedConstruction := by
  sorry

end Computability
end FoC
