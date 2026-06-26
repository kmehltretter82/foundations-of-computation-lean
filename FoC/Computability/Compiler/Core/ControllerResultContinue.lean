import FoC.Computability.Compiler.Core.CommonGround
import FoC.Computability.Compiler.Core.ConstructionTargets

set_option doc.verso true

/-!
# Controller Result Continuation

This module isolates the finite-machine leaf for the controller continuation
subroutine.  The machine recognizes successful
{name (full := FoC.Computability.PairedRecognizerDovetailControllerResultContinueCode)}`PairedRecognizerDovetailControllerResultContinueCode`
transforms over canonical encoded code words.
-/

namespace FoC
namespace Computability

open Languages

/--
Construction data for the controller continuation subroutine, stated directly
against the code-word transform.  Later scaffolds adapt this data to the public
controller-loop contract.
-/
def ControllerResultContinueConstructionData : Prop :=
  exists continuer : MachineDescription,
    continuer.SubroutineReady ∧
      (forall code out : Word MachineCodeSymbol,
        PairedRecognizerDovetailControllerResultContinueCode.transform code =
            some out ->
          continuer.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput code)
            (MachineDescription.encodeCodeWordAsInput out)) ∧
      (forall code out : Word MachineCodeSymbol,
        continuer.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput code)
            (MachineDescription.encodeCodeWordAsInput out) ->
          PairedRecognizerDovetailControllerResultContinueCode.transform code = some out)

def ControllerResultContinueForwardSpec
    (continuer : MachineDescription) : Prop :=
  forall code out : Word MachineCodeSymbol,
    PairedRecognizerDovetailControllerResultContinueCode.transform code =
        some out ->
      continuer.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out)

def ControllerResultContinueClosedSpec
    (continuer : MachineDescription) : Prop :=
  forall code out : Word MachineCodeSymbol,
    continuer.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) ->
      PairedRecognizerDovetailControllerResultContinueCode.transform code =
        some out

def ControllerResultContinueSpec
    (continuer : MachineDescription) : Prop :=
  continuer.SubroutineReady ∧
    ControllerResultContinueForwardSpec continuer ∧
      ControllerResultContinueClosedSpec continuer

def ControllerResultContinueCanonicalForwardSpec
    (continuer : MachineDescription) : Prop :=
  forall C : MachineDescription.DovetailControllerLayout,
    PairedRecognizerDovetailControllerRawOutput C.result = none ->
      continuer.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.DovetailControllerLayout.encode C))
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.DovetailControllerLayout.encode
            (MachineDescription.DovetailControllerLayout.nextStage C)))

def ControllerResultContinueClosedLayoutSpec
    (continuer : MachineDescription) : Prop :=
  forall code out : Word MachineCodeSymbol,
    continuer.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) ->
      exists C : MachineDescription.DovetailControllerLayout,
        code = MachineDescription.DovetailControllerLayout.encode C ∧
          PairedRecognizerDovetailControllerRawOutput C.result = none ∧
            out =
              MachineDescription.DovetailControllerLayout.encode
                (MachineDescription.DovetailControllerLayout.nextStage C)

def ControllerResultContinueComponentSpec
    (continuer : MachineDescription) : Prop :=
  continuer.SubroutineReady ∧
    ControllerResultContinueCanonicalForwardSpec continuer ∧
      ControllerResultContinueClosedLayoutSpec continuer

def ControllerResultContinueComponentConstruction : Prop :=
  exists continuer : MachineDescription,
    ControllerResultContinueComponentSpec continuer

theorem controllerResultContinueForwardSpec_of_canonical
    {continuer : MachineDescription}
    (hforward :
      ControllerResultContinueCanonicalForwardSpec continuer) :
    ControllerResultContinueForwardSpec continuer := by
  intro code out htransform
  rcases
      (CommonGround.ControllerLayouts.resultContinue_transform_eq_some_iff
        code out).mp htransform with
    ⟨C, rfl, hraw, rfl⟩
  exact hforward C hraw

theorem controllerResultContinueClosedSpec_of_layout
    {continuer : MachineDescription}
    (hclosed :
      ControllerResultContinueClosedLayoutSpec continuer) :
    ControllerResultContinueClosedSpec continuer := by
  intro code out hhalt
  rcases hclosed code out hhalt with
    ⟨C, rfl, hraw, rfl⟩
  exact
    (CommonGround.ControllerLayouts.resultContinue_encode_nextStage_iff
      (C := C)).mpr hraw

theorem controllerResultContinueSpec_of_components
    {continuer : MachineDescription}
    (h : ControllerResultContinueComponentSpec continuer) :
    ControllerResultContinueSpec continuer := by
  rcases h with ⟨hready, hforward, hclosed⟩
  exact
    ⟨hready,
      controllerResultContinueForwardSpec_of_canonical hforward,
      controllerResultContinueClosedSpec_of_layout hclosed⟩

theorem controllerResultContinueConstructionData_of_spec
    {continuer : MachineDescription}
    (h : ControllerResultContinueSpec continuer) :
    ControllerResultContinueConstructionData := by
  rcases h with ⟨hready, hforward, hclosed⟩
  exact ⟨continuer, hready, hforward, hclosed⟩

theorem controllerResultContinueConstructionData_of_components
    (h : ControllerResultContinueComponentConstruction) :
    ControllerResultContinueConstructionData := by
  rcases h with ⟨continuer, hcomponents⟩
  exact
    controllerResultContinueConstructionData_of_spec
      (controllerResultContinueSpec_of_components hcomponents)

theorem controllerResultContinueComponentConstruction_scaffold :
    ControllerResultContinueComponentConstruction := by
  sorry

theorem controllerResultContinueConstruction_scaffold :
    ControllerResultContinueConstructionData := by
  exact
    controllerResultContinueConstructionData_of_components
      controllerResultContinueComponentConstruction_scaffold

end Computability
end FoC
