import FoC.Computability.Compiler.Core.CommonGround.BoolWordQuoters
import FoC.Computability.Compiler.Core.ConstructionTargets

set_option doc.verso true

/-!
# Controller Input Initializer

This module isolates the finite-machine leaf for initializing the controller
input tape.  The remaining obligation is the forward run for
{name (full := FoC.Computability.PairedRecognizerDovetailControllerInitialCode)}`PairedRecognizerDovetailControllerInitialCode`;
the public construction theorem below is just an adapter to the controller
initializer contract.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

/-- Forward behavior required of a controller input initializer machine. -/
def ControllerInputInitializerForwardSpec
    (initializer : MachineDescription) : Prop :=
  forall w : Word Bool,
    initializer.HaltsWithOutput w
      (encodeCodeWordAsInput
        (PairedRecognizerDovetailControllerInitialCode w))

def ControllerInputInitializerConstructionData : Prop :=
  exists initializer : MachineDescription,
    initializer.SubroutineReady ∧
      ControllerInputInitializerForwardSpec initializer

def ControllerInputInitializerRawBoolWordHeaderEmitterConstruction :
    Prop :=
  CommonGround.BoolWordQuoters.RawBoolWordHeaderEmitterConstruction
    CommonGround.ControllerLayouts.initialSuffix

/--
Use the reusable raw Bool-word header emitter contract to package the controller
input initializer.  The only controller-specific work here is the canonical
encoding identity for the initial layout.
-/
theorem controllerInputInitializerConstructionData_of_rawBoolWordHeaderEmitter
    (h : ControllerInputInitializerRawBoolWordHeaderEmitterConstruction) :
    ControllerInputInitializerConstructionData := by
  rcases h with ⟨initializer, hspec⟩
  refine ⟨initializer, hspec.left, ?_⟩
  intro w
  simpa [CommonGround.ControllerLayouts.initialCode_eq_header_boolWordAppend]
    using hspec.right w

/-- Package the local forward spec as the public initializer realization. -/
theorem controllerInputInitializerConstruction_of_data
    (h : ControllerInputInitializerConstructionData) :
    exists initializer : MachineDescription,
      PairedRecognizerDovetailControllerInputInitializerRealizes initializer := by
  rcases h with ⟨initializer, hready, hforward⟩
  exact ⟨initializer, hready, hforward⟩

theorem controllerInputInitializerRawBoolWordHeaderEmitterConstruction_scaffold :
    ControllerInputInitializerRawBoolWordHeaderEmitterConstruction := by
  exact
    CommonGround.BoolWordQuoters.controllerInitialRawBoolWordHeaderEmitterConstruction

theorem controllerInputInitializerConstructionData_scaffold :
    ControllerInputInitializerConstructionData := by
  exact
    controllerInputInitializerConstructionData_of_rawBoolWordHeaderEmitter
      controllerInputInitializerRawBoolWordHeaderEmitterConstruction_scaffold

/-- Public controller input initializer construction, kept as thin adapter glue. -/
theorem controllerInputInitializerConstruction_scaffold :
    exists initializer : MachineDescription,
      PairedRecognizerDovetailControllerInputInitializerRealizes initializer := by
  exact
    controllerInputInitializerConstruction_of_data
      controllerInputInitializerConstructionData_scaffold

end Computability
end FoC
