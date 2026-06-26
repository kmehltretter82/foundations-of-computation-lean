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

/-- Forward behavior required of a controller input initializer machine. -/
def ControllerInputInitializerForwardSpec
    (initializer : MachineDescription) : Prop :=
  forall w : Word Bool,
    initializer.HaltsWithOutput w
      (MachineDescription.encodeCodeWordAsInput
        (PairedRecognizerDovetailControllerInitialCode w))

def ControllerInputInitializerConstructionData : Prop :=
  exists initializer : MachineDescription,
    initializer.SubroutineReady ∧
      ControllerInputInitializerForwardSpec initializer

/-- Package the local forward spec as the public initializer realization. -/
theorem controllerInputInitializerConstruction_of_data
    (h : ControllerInputInitializerConstructionData) :
    exists initializer : MachineDescription,
      PairedRecognizerDovetailControllerInputInitializerRealizes initializer := by
  rcases h with ⟨initializer, hready, hforward⟩
  exact ⟨initializer, hready, hforward⟩

theorem controllerInputInitializerConstructionData_scaffold :
    ControllerInputInitializerConstructionData := by
  sorry

/-- Public controller input initializer construction, kept as thin adapter glue. -/
theorem controllerInputInitializerConstruction_scaffold :
    exists initializer : MachineDescription,
      PairedRecognizerDovetailControllerInputInitializerRealizes initializer := by
  exact
    controllerInputInitializerConstruction_of_data
      controllerInputInitializerConstructionData_scaffold

end Computability
end FoC
