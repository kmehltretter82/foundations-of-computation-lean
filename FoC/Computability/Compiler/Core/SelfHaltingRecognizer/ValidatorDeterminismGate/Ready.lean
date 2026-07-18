import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorDeterminismGate.Basic

set_option doc.verso true

/-!
# Exact-code validator: determinism-gate readiness

The finite table is intentionally kept separate from its structural readiness
certificate. Logical run modules import the table only; final physical
contracts import this module when they need
{lit}`SubroutineReady`.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
namespace ValidatorDeterminismGate

open MachineDescription

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem description_subroutineReady : Description.SubroutineReady := by
  simpa [Description, physicalCoreDescription] using
    withValidatorFourLeftEntry_compileValidatorBlockDescription_subroutineReady
      blockDescription (by decide) (by decide) (by decide)

end ValidatorDeterminismGate
end SelfHaltingRecognizer
end Computability
end FoC
