import FoC.Computability.Compiler.Core.ConstructionTargets
set_option doc.verso true

/-!
# Controller Input Initializer

This module defines the machine component that initializes the controller input tape before execution.
-/


set_option doc.verso true

namespace FoC
namespace Computability

open Languages

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

theorem controllerInputInitializerConstruction_of_data
    (h : ControllerInputInitializerConstructionData) :
    exists initializer : MachineDescription,
      PairedRecognizerDovetailControllerInputInitializerRealizes initializer := by
  rcases h with ⟨initializer, hready, hforward⟩
  exact ⟨initializer, hready, hforward⟩

theorem controllerInputInitializerConstructionData_scaffold :
    ControllerInputInitializerConstructionData := by
  sorry

theorem controllerInputInitializerConstruction_scaffold :
    exists initializer : MachineDescription,
      PairedRecognizerDovetailControllerInputInitializerRealizes initializer := by
  exact
    controllerInputInitializerConstruction_of_data
      controllerInputInitializerConstructionData_scaffold

end Computability
end FoC
