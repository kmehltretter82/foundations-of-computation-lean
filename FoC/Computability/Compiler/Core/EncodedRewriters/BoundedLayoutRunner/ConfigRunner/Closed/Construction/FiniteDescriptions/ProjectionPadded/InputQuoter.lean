import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.FiniteDescriptions.ProjectionPadded.Shape

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace BoundedLayoutRunner

def SelectedProjectionInputQuoterExactSourceTape
    (L : MachineDescription.DovetailLayout) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells []
    (List.append
      ((List.append
        (MachineDescription.encodeCodeSymbolAsInput
          MachineCodeSymbol.transition)
        (List.append
          (DovetailInitialLayoutInitializer.stageInputBits
            L.input L.stage)
          (SelectedProjectionTailProjector.sourceRestFieldBits L))).map
        some)
      [none])

def SelectedProjectionInputQuoterExactTargetTape
    (L : MachineDescription.DovetailLayout) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells
    ((SelectedProjectionTailProjector.outputPrefixStageInputSourceRestFieldBits
      L).reverse.map some)
    ((List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        L.stage)
      (SelectedProjectionTailProjector.sourceRestFieldBits L)).map some)

theorem parsedLayoutCheckedTape_eq_inputQuoterExactSourceTape
    (L : MachineDescription.DovetailLayout) :
    ParsedLayoutCheckedTape L =
      SelectedProjectionInputQuoterExactSourceTape L := by
  rw [SelectedProjectionInputQuoterExactSourceTape,
    SelectedProjectionTailProjector.parsedLayoutCheckedTape_eq_transition_stageInput_sourceRestFieldBits]

theorem sourceTape_outputPrefix_eq_inputQuoterExactTargetTape
    (L : MachineDescription.DovetailLayout) :
    SelectedProjectionTailProjector.sourceTape L
        ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
          some) =
      SelectedProjectionInputQuoterExactTargetTape L := by
  rw [SelectedProjectionInputQuoterExactTargetTape,
    SelectedProjectionTailProjector.sourceTape_outputPrefix_eq_stageInputSourceRestFieldBits]

def SelectedProjectionInputQuoterExactShapeSpec
    (quoter : MachineDescription) : Prop :=
  quoter.SubroutineReady ∧
    forall L : MachineDescription.DovetailLayout,
      quoter.HaltsFromTape
        (SelectedProjectionInputQuoterExactSourceTape L)
        (SelectedProjectionInputQuoterExactTargetTape L)

def SelectedProjectionInputQuoterExactShapeConstruction : Prop :=
  exists quoter : MachineDescription,
    SelectedProjectionInputQuoterExactShapeSpec quoter

theorem selectedProjectionInputQuoterSpec_of_exactShape
    {quoter : MachineDescription}
    (hquoter : SelectedProjectionInputQuoterExactShapeSpec quoter) :
    SelectedProjectionInputQuoterSpec quoter := by
  constructor
  · exact hquoter.left
  · intro L
    have hrun := hquoter.right L
    rw [parsedLayoutCheckedTape_eq_inputQuoterExactSourceTape L]
    rw [sourceTape_outputPrefix_eq_inputQuoterExactTargetTape L]
    exact hrun

theorem selectedProjectionInputQuoterConstruction_of_exactShape
    (h : SelectedProjectionInputQuoterExactShapeConstruction) :
    SelectedProjectionInputQuoterConstruction := by
  rcases h with ⟨quoter, hquoter⟩
  exact
    ⟨quoter,
      selectedProjectionInputQuoterSpec_of_exactShape hquoter⟩

/--
Finite-machine leaf for selected projection under the equivalence-based phase
contract.  The checked parser supplies the canonical checked parsed-layout
input.  This first phase quotes the input field and positions the remaining
layout fields for the selected padded tail emitter.
-/
theorem selectedProjectionInputQuoterExactShapeConstruction_scaffold :
    SelectedProjectionInputQuoterExactShapeConstruction := by
  sorry

theorem selectedProjectionInputQuoterConstruction_scaffold :
    SelectedProjectionInputQuoterConstruction :=
  selectedProjectionInputQuoterConstruction_of_exactShape
    selectedProjectionInputQuoterExactShapeConstruction_scaffold

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
