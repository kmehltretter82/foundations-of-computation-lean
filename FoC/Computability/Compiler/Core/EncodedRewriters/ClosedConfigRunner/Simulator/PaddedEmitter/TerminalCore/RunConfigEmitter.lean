import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedEmitter.TerminalCore.Specs

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

/-!
# Terminal run-config field emitter

This module isolates the finite-machine leaf that must turn terminal simulator
source fields into the field-FST target containing the fixed description run
result.
-/

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalSourceConstruction_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalSourceConstruction_configRunner := by
  intro D
  sorry

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
