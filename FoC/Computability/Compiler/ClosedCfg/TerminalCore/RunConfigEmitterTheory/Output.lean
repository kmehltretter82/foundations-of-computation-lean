import FoC.Computability.Compiler.ClosedCfg.TerminalCore.Core
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterTheory.Iteration

set_option doc.verso true

/-!
# Run-loop output bridge

These lemmas identify the exact field and padded-tape targets of #18 with the
result of the executable iteration loop.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterTheory

theorem fieldOutputBits_eq_iterateStep
    (D : MachineDescription) (L : SimulatorLayout) :
    FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner
        D L =
      SimulatorLayout.asBoolInput
        (iterateStep D L.stage (seedHit D L)) := by
  rw [iterateStep_seedHit_eq_run]
  rfl

theorem scratchTape_eq_iterateStep_output
    (D : MachineDescription) (L : SimulatorLayout) :
    FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner D L =
      FixedDescriptionBoundedSimulatorPaddedTape
        (SimulatorLayout.asBoolInput
          (iterateStep D L.stage (seedHit D L)))
        (Tape.contextLength
          (Tape.input (FixedDescriptionBoundedSimulatorInput L))) := by
  rw [iterateStep_seedHit_eq_run]
  rfl

end RunConfigEmitterTheory
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
