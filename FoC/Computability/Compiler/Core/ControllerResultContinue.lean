import FoC.Computability.Compiler.Core.ControllerResultContinue.StageInputContinue

set_option doc.verso true

/-!
# Controller Result Continuation

This module keeps the public controller result-continuation construction target stable.
The concrete guard/projection prefix lives in submodules so new finite leaves can be
added without growing this wrapper past the repository size limit.
-/

namespace FoC
namespace Computability

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
