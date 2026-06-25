import FoC.Computability.Compiler.Core.ConstructionTargets
set_option doc.verso true

/-!
# Controller Result Continuation

This module provides the machine component that handles continuing execution after a controller result.
-/


set_option doc.verso true

namespace FoC
namespace Computability

open Languages

def ControllerResultContinueConstructionData : Prop :=
  exists continuer : MachineDescription,
    continuer.SubroutineReady ∧
      (forall code out : Word MachineCodeSymbol,
        PairedRecognizerDovetailControllerResultContinueCode.transform code = some out ->
          continuer.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput code)
            (MachineDescription.encodeCodeWordAsInput out)) ∧
      (forall code out : Word MachineCodeSymbol,
        continuer.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput code)
            (MachineDescription.encodeCodeWordAsInput out) ->
          PairedRecognizerDovetailControllerResultContinueCode.transform code = some out)

def ControllerResultContinueForwardConstructionData : Prop :=
  exists continuer : MachineDescription,
    continuer.SubroutineReady ∧
      (forall code out : Word MachineCodeSymbol,
        PairedRecognizerDovetailControllerResultContinueCode.transform code = some out ->
          continuer.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput code)
            (MachineDescription.encodeCodeWordAsInput out))

def ControllerResultContinueClosedConstructionData : Prop :=
  forall continuer : MachineDescription,
    continuer.SubroutineReady ->
    (forall code out : Word MachineCodeSymbol,
      PairedRecognizerDovetailControllerResultContinueCode.transform code = some out ->
        continuer.HaltsWithOutput
          (MachineDescription.encodeCodeWordAsInput code)
          (MachineDescription.encodeCodeWordAsInput out)) ->
    forall code out : Word MachineCodeSymbol,
      continuer.HaltsWithOutput
          (MachineDescription.encodeCodeWordAsInput code)
          (MachineDescription.encodeCodeWordAsInput out) ->
        PairedRecognizerDovetailControllerResultContinueCode.transform code = some out

theorem controllerResultContinueConstructionData_of_forward_closed
    (hforward : ControllerResultContinueForwardConstructionData)
    (hclosed : ControllerResultContinueClosedConstructionData) :
    ControllerResultContinueConstructionData := by
  rcases hforward with ⟨continuer, hready, hforwardSpec⟩
  exact
    ⟨continuer, hready, hforwardSpec,
      hclosed continuer hready hforwardSpec⟩

theorem controllerResultContinueForwardConstructionData_scaffold :
    ControllerResultContinueForwardConstructionData := by
  sorry

theorem controllerResultContinueClosedConstructionData_scaffold :
    ControllerResultContinueClosedConstructionData := by
  sorry

theorem controllerResultContinueConstruction_scaffold :
    ControllerResultContinueConstructionData := by
  exact
    controllerResultContinueConstructionData_of_forward_closed
      controllerResultContinueForwardConstructionData_scaffold
      controllerResultContinueClosedConstructionData_scaffold

end Computability
end FoC
