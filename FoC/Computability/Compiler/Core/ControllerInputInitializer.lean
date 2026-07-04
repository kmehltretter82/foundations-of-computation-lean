import FoC.Computability.Compiler.Core.CommonGround.BoolWordQuoters
import FoC.Computability.Compiler.Core.ConstructionTargets

set_option doc.verso true

/-!
# Controller Input Initializer

This module isolates the finite-machine leaf for initializing the controller
input tape.  The construction below is the forward run for
{name (full := FoC.Computability.PairedRecognizerDovetailControllerInitialCode)}`PairedRecognizerDovetailControllerInitialCode`;
it adapts the shared bool-word quoter into the controller initializer contract.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

/-- Public controller input initializer construction, kept as thin adapter glue. -/
theorem controllerInputInitializerConstruction_scaffold :
    exists initializer : MachineDescription,
      PairedRecognizerDovetailControllerInputInitializerRealizes initializer := by
  rcases
      CommonGround.BoolWordQuoters.controllerInitialRawBoolWordHeaderEmitterConstruction with
    ⟨initializer, hspec⟩
  refine ⟨initializer, hspec.left, ?_⟩
  intro w
  simpa [CommonGround.ControllerLayouts.initialCode_eq_header_boolWordAppend]
    using hspec.right w

end Computability
end FoC
