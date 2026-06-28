import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Simulator.PaddedEmitter.Cleanup

set_option doc.verso true

/-!
# Padded simulator scaffold emitter post-scanner assembly
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

theorem fixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalConstruction_configRunner :
    FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalConstruction_configRunner := by
  intro D
  rcases
      fixedDescriptionBoundedSimulatorPaddedEmitterRunLoopConstruction_configRunner
        D with
    ⟨runLoop, hrunLoop⟩
  exact ⟨runLoop, hrunLoop⟩

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
