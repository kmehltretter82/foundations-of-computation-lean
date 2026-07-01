import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedEmitter.TerminalCore.Adapters
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedEmitter.TerminalCore.FieldTapes

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

/-!
# Terminal run-config field emitter

This module isolates the finite-machine leaf that must turn the FST source
encoding of terminal simulator fields into the field-FST target containing the
fixed description run result.  Terminal source tapes are adapted to that FST
source shape by exact tape equality.
-/

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetConstruction_core_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetConstruction_configRunner := by
  intro D
  sorry

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalSourceConstruction_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalSourceConstruction_configRunner :=
  fixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalSourceConstruction_of_FSTSourceToField_configRunner
    fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetConstruction_core_configRunner

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
