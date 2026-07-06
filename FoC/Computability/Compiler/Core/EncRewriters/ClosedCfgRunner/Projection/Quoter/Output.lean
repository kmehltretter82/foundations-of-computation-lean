import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Quoter.Main

set_option doc.verso true

/-!
# Selected-projection quoter output route

The exact selected-projection input quoter must produce a positioned source
tape for the padded tail emitter.  The source-rest and raw-cell layers also
provide normalized-output endpoints.  This module lifts those endpoints through
the top-level assembly prefix and exposes a checked-input output construction
parallel to the exact scaffold construction.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

/-! ## Output word and tape views -/

def SelectedProjectionInputQuoterOutput
    (L : DovetailLayout) : Word Bool :=
  SelectedProjectionInputQuoterFiniteLeaf.selectedProjectionInputQuoterRawCellQuoteOutput
    L

theorem SelectedProjectionInputQuoterOutput_eq_rawCellQuoteOutput
    (L : DovetailLayout) :
    SelectedProjectionInputQuoterOutput L =
      SelectedProjectionInputQuoterFiniteLeaf.selectedProjectionInputQuoterRawCellQuoteOutput
        L := by
  rfl

theorem SelectedProjectionInputQuoterOutput_eq_outputPrefixStageInputSourceRestFieldBits
    (L : DovetailLayout) :
    SelectedProjectionInputQuoterOutput L =
      List.append
        (SelectedProjectionTailProjector.outputPrefixStageInputSourceRestFieldBits
          L)
        (SelectedProjectionTailProjector.sourceFieldBits L) := by
  rfl

theorem SelectedProjectionInputQuoterOutput_eq_outputPrefixBits_sourceField
    (L : DovetailLayout) :
    SelectedProjectionInputQuoterOutput L =
      List.append
        (SelectedProjectionTailProjector.outputPrefixBits L)
        (SelectedProjectionTailProjector.sourceFieldBits L) := by
  rw [SelectedProjectionInputQuoterOutput_eq_outputPrefixStageInputSourceRestFieldBits]
  rw [←
    SelectedProjectionTailProjector.outputPrefixBits_eq_stageInputSourceRestFieldBits]

theorem SelectedProjectionInputQuoterOutput_eq_encodedHeaderInputSourceSuffix
    (L : DovetailLayout) :
    SelectedProjectionInputQuoterOutput L =
      encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          encodeBoolWordAppend
            (ParsedLayoutBits L)
            (SelectedProjectionTailProjector.sourceSuffix L)) := by
  rw [SelectedProjectionInputQuoterOutput_eq_outputPrefixBits_sourceField]
  exact SelectedProjectionTailProjector.outputPrefixBits_append_sourceFieldBits
    L

theorem SelectedProjectionInputQuoterOutput_eq_exactTargetTape_normalizedOutput
    (L : DovetailLayout) :
    SelectedProjectionInputQuoterOutput L =
      Tape.normalizedOutput
        (SelectedProjectionInputQuoterExactTargetTape L) := by
  rw [SelectedProjectionInputQuoterOutput]
  rw [
    SelectedProjectionInputQuoterFiniteLeaf.selectedProjectionInputQuoterExactTargetTape_normalizedOutput_output]

theorem SelectedProjectionInputQuoterOutput_eq_sourceTape_outputPrefix_normalizedOutput
    (L : DovetailLayout) :
    SelectedProjectionInputQuoterOutput L =
      Tape.normalizedOutput
        (SelectedProjectionTailProjector.sourceTape L
          ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
            some)) := by
  rw [SelectedProjectionInputQuoterOutput_eq_outputPrefixBits_sourceField]
  rw [SelectedProjectionTailProjector.sourceTape_normalizedOutput_outputPrefix]

theorem SelectedProjectionInputQuoterExactTargetTape_normalizedOutput_eq_output
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (SelectedProjectionInputQuoterExactTargetTape L) =
      SelectedProjectionInputQuoterOutput L := by
  rw [SelectedProjectionInputQuoterOutput_eq_exactTargetTape_normalizedOutput]

theorem selectedProjectionInputQuoterSourceTapeOutputPrefix_normalizedOutput_eq_output
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (SelectedProjectionTailProjector.sourceTape L
          ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
            some)) =
      SelectedProjectionInputQuoterOutput L := by
  rw [SelectedProjectionInputQuoterOutput_eq_sourceTape_outputPrefix_normalizedOutput]

theorem SelectedProjectionInputQuoterOutput_eq_rawCellTargetTape_normalizedOutput
    (L : DovetailLayout) :
    SelectedProjectionInputQuoterOutput L =
      Tape.normalizedOutput
        (SelectedProjectionInputQuoterFiniteLeaf.selectedProjectionInputQuoterRawCellQuoteTargetTape
          L) := by
  rw [SelectedProjectionInputQuoterOutput]
  rw [
    SelectedProjectionInputQuoterFiniteLeaf.selectedProjectionInputQuoterRawCellQuoteTargetTape_normalizedOutput_output]

theorem SelectedProjectionInputQuoterOutput_eq_rawCellShapeTargetTape_normalizedOutput
    (L : DovetailLayout) :
    SelectedProjectionInputQuoterOutput L =
      Tape.normalizedOutput
        (SelectedProjectionInputQuoterFiniteLeaf.selectedProjectionInputQuoterRawCellQuoteTargetShapeTape
          L) := by
  rw [SelectedProjectionInputQuoterOutput]
  rw [
    SelectedProjectionInputQuoterFiniteLeaf.selectedProjectionInputQuoterRawCellQuoteTargetShapeTape_normalizedOutput]

theorem SelectedProjectionInputQuoterOutput_eq_sourceRestFinishOutput_selected
    (L : DovetailLayout) :
    SelectedProjectionInputQuoterOutput L =
      SelectedProjectionInputQuoterFiniteLeaf.assemblySourceRestFinishOutput
        L.input
        (SelectedProjectionTailProjector.sourceRestFieldBits L)
        L.stage := by
  rw [SelectedProjectionInputQuoterOutput]
  rw [
    SelectedProjectionInputQuoterFiniteLeaf.assemblySourceRestFinishOutput_selected_eq_rawCellQuoteOutput]

/-! ## Output contracts -/

def SelectedProjectionInputQuoterExactShapeOutputSpec
    (quoter : MachineDescription) : Prop :=
  quoter.SubroutineReady ∧
    forall L : DovetailLayout,
      quoter.HaltsFromTapeWithOutput
        (SelectedProjectionInputQuoterExactSourceTape L)
        (SelectedProjectionInputQuoterOutput L)

def SelectedProjectionInputQuoterExactShapeOutputConstruction :
    Prop :=
  exists quoter : MachineDescription,
    SelectedProjectionInputQuoterExactShapeOutputSpec quoter

def SelectedProjectionInputQuoterCheckedOutputSpec
    (quoter : MachineDescription) : Prop :=
  quoter.SubroutineReady ∧
    forall L : DovetailLayout,
      quoter.HaltsFromTapeWithOutput
        (ParsedLayoutCheckedTape L)
        (SelectedProjectionInputQuoterOutput L)

def SelectedProjectionInputQuoterCheckedOutputConstruction :
    Prop :=
  exists quoter : MachineDescription,
    SelectedProjectionInputQuoterCheckedOutputSpec quoter

def SelectedProjectionInputQuoterOutputSpec
    (quoter : MachineDescription) : Prop :=
  SelectedProjectionInputQuoterCheckedOutputSpec quoter

def SelectedProjectionInputQuoterOutputConstruction : Prop :=
  exists quoter : MachineDescription,
    SelectedProjectionInputQuoterOutputSpec quoter

def SelectedProjectionInputQuoterPostBoundaryOutputComponentConstruction :
    Prop :=
  SelectedProjectionInputQuoterFiniteLeaf.SelectedProjectionInputQuoterPostBoundaryOutputConstruction

/-! ## Spec accessors -/

theorem SelectedProjectionInputQuoterExactShapeOutputSpec.subroutineReady
    {quoter : MachineDescription}
    (hquoter :
      SelectedProjectionInputQuoterExactShapeOutputSpec quoter) :
    quoter.SubroutineReady :=
  hquoter.left

theorem SelectedProjectionInputQuoterExactShapeOutputSpec.haltsFromTapeWithOutput
    {quoter : MachineDescription}
    (hquoter :
      SelectedProjectionInputQuoterExactShapeOutputSpec quoter)
    (L : DovetailLayout) :
    quoter.HaltsFromTapeWithOutput
      (SelectedProjectionInputQuoterExactSourceTape L)
      (SelectedProjectionInputQuoterOutput L) :=
  hquoter.right L

theorem SelectedProjectionInputQuoterExactShapeOutputSpec.haltsFromTapeWithExactTargetOutput
    {quoter : MachineDescription}
    (hquoter :
      SelectedProjectionInputQuoterExactShapeOutputSpec quoter)
    (L : DovetailLayout) :
    quoter.HaltsFromTapeWithOutput
      (SelectedProjectionInputQuoterExactSourceTape L)
      (Tape.normalizedOutput
        (SelectedProjectionInputQuoterExactTargetTape L)) := by
  rw [← SelectedProjectionInputQuoterOutput_eq_exactTargetTape_normalizedOutput]
  exact hquoter.haltsFromTapeWithOutput L

theorem SelectedProjectionInputQuoterExactShapeOutputSpec.haltsFromTapeWithSourceTapeOutput
    {quoter : MachineDescription}
    (hquoter :
      SelectedProjectionInputQuoterExactShapeOutputSpec quoter)
    (L : DovetailLayout) :
    quoter.HaltsFromTapeWithOutput
      (SelectedProjectionInputQuoterExactSourceTape L)
      (Tape.normalizedOutput
        (SelectedProjectionTailProjector.sourceTape L
          ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
            some))) := by
  rw [
    ← SelectedProjectionInputQuoterOutput_eq_sourceTape_outputPrefix_normalizedOutput]
  exact hquoter.haltsFromTapeWithOutput L

theorem SelectedProjectionInputQuoterCheckedOutputSpec.subroutineReady
    {quoter : MachineDescription}
    (hquoter : SelectedProjectionInputQuoterCheckedOutputSpec quoter) :
    quoter.SubroutineReady :=
  hquoter.left

theorem SelectedProjectionInputQuoterCheckedOutputSpec.haltsFromTapeWithOutput
    {quoter : MachineDescription}
    (hquoter : SelectedProjectionInputQuoterCheckedOutputSpec quoter)
    (L : DovetailLayout) :
    quoter.HaltsFromTapeWithOutput
      (ParsedLayoutCheckedTape L)
      (SelectedProjectionInputQuoterOutput L) :=
  hquoter.right L

theorem SelectedProjectionInputQuoterCheckedOutputSpec.haltsFromTapeWithExactTargetOutput
    {quoter : MachineDescription}
    (hquoter : SelectedProjectionInputQuoterCheckedOutputSpec quoter)
    (L : DovetailLayout) :
    quoter.HaltsFromTapeWithOutput
      (ParsedLayoutCheckedTape L)
      (Tape.normalizedOutput
        (SelectedProjectionInputQuoterExactTargetTape L)) := by
  rw [← SelectedProjectionInputQuoterOutput_eq_exactTargetTape_normalizedOutput]
  exact hquoter.haltsFromTapeWithOutput L

theorem SelectedProjectionInputQuoterCheckedOutputSpec.haltsFromTapeWithSourceTapeOutput
    {quoter : MachineDescription}
    (hquoter : SelectedProjectionInputQuoterCheckedOutputSpec quoter)
    (L : DovetailLayout) :
    quoter.HaltsFromTapeWithOutput
      (ParsedLayoutCheckedTape L)
      (Tape.normalizedOutput
        (SelectedProjectionTailProjector.sourceTape L
          ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
            some))) := by
  rw [
    ← SelectedProjectionInputQuoterOutput_eq_sourceTape_outputPrefix_normalizedOutput]
  exact hquoter.haltsFromTapeWithOutput L

theorem SelectedProjectionInputQuoterOutputSpec.subroutineReady
    {quoter : MachineDescription}
    (hquoter : SelectedProjectionInputQuoterOutputSpec quoter) :
    quoter.SubroutineReady :=
  hquoter.left

theorem SelectedProjectionInputQuoterOutputSpec.haltsFromTapeWithOutput
    {quoter : MachineDescription}
    (hquoter : SelectedProjectionInputQuoterOutputSpec quoter)
    (L : DovetailLayout) :
    quoter.HaltsFromTapeWithOutput
      (ParsedLayoutCheckedTape L)
      (SelectedProjectionInputQuoterOutput L) :=
  hquoter.right L

theorem SelectedProjectionInputQuoterOutputSpec.haltsFromTapeWithEncodedOutput
    {quoter : MachineDescription}
    (hquoter : SelectedProjectionInputQuoterOutputSpec quoter)
    (L : DovetailLayout) :
    quoter.HaltsFromTapeWithOutput
      (ParsedLayoutCheckedTape L)
      (encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          encodeBoolWordAppend
            (ParsedLayoutBits L)
            (SelectedProjectionTailProjector.sourceSuffix L))) := by
  rw [← SelectedProjectionInputQuoterOutput_eq_encodedHeaderInputSourceSuffix]
  exact hquoter.haltsFromTapeWithOutput L

/-! ## Exact-to-output adapters -/

private theorem haltsFromTapeWithOutput_of_haltsFromTape_target
    {D : MachineDescription} {Tin Tout : Tape Bool}
    (h : D.HaltsFromTape Tin Tout) :
    D.HaltsFromTapeWithOutput Tin (Tape.normalizedOutput Tout) :=
  MachineDescription.haltsFromTapeWithOutput_of_haltsFromTape h

theorem SelectedProjectionInputQuoterExactShapeSpec.toOutputSpec
    {quoter : MachineDescription}
    (hquoter : SelectedProjectionInputQuoterExactShapeSpec quoter) :
    SelectedProjectionInputQuoterExactShapeOutputSpec quoter := by
  constructor
  · exact hquoter.left
  · intro L
    simpa [SelectedProjectionInputQuoterOutput_eq_exactTargetTape_normalizedOutput
      L] using
      haltsFromTapeWithOutput_of_haltsFromTape_target
        (hquoter.right L)

theorem SelectedProjectionInputQuoterExactShapeOutputConstruction_of_exactShape
    (h : exists quoter : MachineDescription,
      SelectedProjectionInputQuoterExactShapeSpec quoter) :
    SelectedProjectionInputQuoterExactShapeOutputConstruction := by
  rcases h with ⟨quoter, hquoter⟩
  exact ⟨quoter, hquoter.toOutputSpec⟩

theorem SelectedProjectionInputQuoterSpec.toCheckedOutputSpec
    {quoter : MachineDescription}
    (hquoter : SelectedProjectionInputQuoterSpec quoter) :
    SelectedProjectionInputQuoterCheckedOutputSpec quoter := by
  constructor
  · exact hquoter.left
  · intro L
    simpa [
      SelectedProjectionInputQuoterOutput_eq_sourceTape_outputPrefix_normalizedOutput
        L] using
      haltsFromTapeWithOutput_of_haltsFromTape_target
        (hquoter.right L)

theorem SelectedProjectionInputQuoterSpec.toOutputSpec
    {quoter : MachineDescription}
    (hquoter : SelectedProjectionInputQuoterSpec quoter) :
    SelectedProjectionInputQuoterOutputSpec quoter :=
  hquoter.toCheckedOutputSpec

theorem SelectedProjectionInputQuoterConstruction.toOutputConstruction
    (h : SelectedProjectionInputQuoterConstruction) :
    SelectedProjectionInputQuoterOutputConstruction := by
  rcases h with ⟨quoter, hquoter⟩
  exact ⟨quoter, hquoter.toOutputSpec⟩

theorem SelectedProjectionInputQuoterExactShapeOutputSpec.toCheckedOutputSpec
    {quoter : MachineDescription}
    (hquoter :
      SelectedProjectionInputQuoterExactShapeOutputSpec quoter) :
    SelectedProjectionInputQuoterCheckedOutputSpec quoter := by
  constructor
  · exact hquoter.subroutineReady
  · intro L
    rw [parsedLayoutCheckedTape_eq_inputQuoterExactSourceTape]
    exact hquoter.haltsFromTapeWithOutput L

theorem SelectedProjectionInputQuoterExactShapeOutputSpec.toOutputSpec
    {quoter : MachineDescription}
    (hquoter :
      SelectedProjectionInputQuoterExactShapeOutputSpec quoter) :
    SelectedProjectionInputQuoterOutputSpec quoter :=
  hquoter.toCheckedOutputSpec

theorem SelectedProjectionInputQuoterExactShapeOutputConstruction.toCheckedOutputConstruction
    (h : SelectedProjectionInputQuoterExactShapeOutputConstruction) :
    SelectedProjectionInputQuoterCheckedOutputConstruction := by
  rcases h with ⟨quoter, hquoter⟩
  exact ⟨quoter, hquoter.toCheckedOutputSpec⟩

theorem SelectedProjectionInputQuoterExactShapeOutputConstruction.toOutputConstruction
    (h : SelectedProjectionInputQuoterExactShapeOutputConstruction) :
    SelectedProjectionInputQuoterOutputConstruction := by
  rcases h with ⟨quoter, hquoter⟩
  exact ⟨quoter, hquoter.toOutputSpec⟩

theorem SelectedProjectionInputQuoterCheckedOutputConstruction.toOutputConstruction
    (h : SelectedProjectionInputQuoterCheckedOutputConstruction) :
    SelectedProjectionInputQuoterOutputConstruction := by
  rcases h with ⟨quoter, hquoter⟩
  exact ⟨quoter, hquoter⟩

/-! ## Prefix composition -/

def SelectedProjectionInputQuoterOutputScaffold
    (post : MachineDescription) : MachineDescription :=
  SeqViaCanonical
    SelectedProjectionInputQuoterFiniteLeaf.AssemblyPrefixDescription
    post

theorem SelectedProjectionInputQuoterOutputScaffold_subroutineReady
    {post : MachineDescription}
    (hpost :
      SelectedProjectionInputQuoterFiniteLeaf.SelectedProjectionInputQuoterPostBoundaryOutputSpec
        post) :
    (SelectedProjectionInputQuoterOutputScaffold post).SubroutineReady := by
  exact
    SeqViaCanonical_subroutineReady
      SelectedProjectionInputQuoterFiniteLeaf.assemblyPrefixDescription_subroutineReady
      hpost.subroutineReady

theorem SelectedProjectionInputQuoterOutputScaffold_haltsFromTapeWithOutput
    {post : MachineDescription}
    (hpost :
      SelectedProjectionInputQuoterFiniteLeaf.SelectedProjectionInputQuoterPostBoundaryOutputSpec
        post)
    (L : DovetailLayout) :
    (SelectedProjectionInputQuoterOutputScaffold post).HaltsFromTapeWithOutput
      (SelectedProjectionInputQuoterExactSourceTape L)
      (SelectedProjectionInputQuoterOutput L) := by
  exact
    SeqViaCanonical_haltsFromTapeWithOutput_of_haltsFromTape_eq
      SelectedProjectionInputQuoterFiniteLeaf.assemblyPrefixDescription_subroutineReady
      hpost.subroutineReady
      (SelectedProjectionInputQuoterFiniteLeaf.assemblyPrefixDescription_haltsFrom_exactSourceTape_to_prefixBoundary
        L)
      (by rfl)
      (by
        simpa [SelectedProjectionInputQuoterOutput] using
          hpost.haltsFromTapeWithOutput L)

theorem selectedProjectionInputQuoterExactShapeOutputSpec_of_postBoundary
    {post : MachineDescription}
    (hpost :
      SelectedProjectionInputQuoterFiniteLeaf.SelectedProjectionInputQuoterPostBoundaryOutputSpec
        post) :
    SelectedProjectionInputQuoterExactShapeOutputSpec
      (SelectedProjectionInputQuoterOutputScaffold post) := by
  constructor
  · exact SelectedProjectionInputQuoterOutputScaffold_subroutineReady hpost
  · intro L
    exact
      SelectedProjectionInputQuoterOutputScaffold_haltsFromTapeWithOutput
        hpost L

theorem selectedProjectionInputQuoterExactShapeOutputConstruction_of_postBoundary
    (hpost :
      SelectedProjectionInputQuoterFiniteLeaf.SelectedProjectionInputQuoterPostBoundaryOutputConstruction) :
    SelectedProjectionInputQuoterExactShapeOutputConstruction := by
  rcases hpost with ⟨post, hpost⟩
  exact
    ⟨SelectedProjectionInputQuoterOutputScaffold post,
      selectedProjectionInputQuoterExactShapeOutputSpec_of_postBoundary
        hpost⟩

theorem selectedProjectionInputQuoterOutputConstruction_of_postBoundary
    (hpost :
      SelectedProjectionInputQuoterFiniteLeaf.SelectedProjectionInputQuoterPostBoundaryOutputConstruction) :
    SelectedProjectionInputQuoterOutputConstruction :=
  (selectedProjectionInputQuoterExactShapeOutputConstruction_of_postBoundary
    hpost).toOutputConstruction

theorem selectedProjectionInputQuoterCheckedOutputConstruction_of_postBoundary
    (hpost :
      SelectedProjectionInputQuoterFiniteLeaf.SelectedProjectionInputQuoterPostBoundaryOutputConstruction) :
    SelectedProjectionInputQuoterCheckedOutputConstruction :=
  (selectedProjectionInputQuoterExactShapeOutputConstruction_of_postBoundary
    hpost).toCheckedOutputConstruction

theorem selectedProjectionInputQuoterExactShapeOutputConstruction_scaffold :
    SelectedProjectionInputQuoterExactShapeOutputConstruction :=
  selectedProjectionInputQuoterExactShapeOutputConstruction_of_postBoundary
    SelectedProjectionInputQuoterFiniteLeaf.selectedProjectionInputQuoterPostBoundaryOutputConstruction

theorem selectedProjectionInputQuoterCheckedOutputConstruction_scaffold :
    SelectedProjectionInputQuoterCheckedOutputConstruction :=
  selectedProjectionInputQuoterCheckedOutputConstruction_of_postBoundary
    SelectedProjectionInputQuoterFiniteLeaf.selectedProjectionInputQuoterPostBoundaryOutputConstruction

theorem selectedProjectionInputQuoterOutputConstruction_scaffold :
    SelectedProjectionInputQuoterOutputConstruction :=
  selectedProjectionInputQuoterOutputConstruction_of_postBoundary
    SelectedProjectionInputQuoterFiniteLeaf.selectedProjectionInputQuoterPostBoundaryOutputConstruction

/-! ## Compatibility adapters for existing exact constructions -/

theorem selectedProjectionInputQuoterOutputConstruction_of_scaffoldExact :
    SelectedProjectionInputQuoterOutputConstruction :=
  SelectedProjectionInputQuoterConstruction.toOutputConstruction
    selectedProjectionInputQuoterConstruction_scaffold

theorem selectedProjectionInputQuoterCheckedOutputConstruction_of_output
    (h : SelectedProjectionInputQuoterOutputConstruction) :
    SelectedProjectionInputQuoterCheckedOutputConstruction := by
  rcases h with ⟨quoter, hquoter⟩
  exact ⟨quoter, hquoter⟩

theorem selectedProjectionInputQuoterCheckedOutputConstruction_of_scaffoldExact :
    SelectedProjectionInputQuoterCheckedOutputConstruction :=
  selectedProjectionInputQuoterCheckedOutputConstruction_of_output
    selectedProjectionInputQuoterOutputConstruction_of_scaffoldExact

theorem selectedProjectionInputQuoterPostBoundaryOutputComponentConstruction_scaffold :
    SelectedProjectionInputQuoterPostBoundaryOutputComponentConstruction :=
  SelectedProjectionInputQuoterFiniteLeaf.selectedProjectionInputQuoterPostBoundaryOutputConstruction

theorem selectedProjectionInputQuoterExactShapeOutputConstruction_of_componentScaffold :
    SelectedProjectionInputQuoterExactShapeOutputConstruction :=
  selectedProjectionInputQuoterExactShapeOutputConstruction_of_postBoundary
    selectedProjectionInputQuoterPostBoundaryOutputComponentConstruction_scaffold

theorem selectedProjectionInputQuoterCheckedOutputConstruction_of_componentScaffold :
    SelectedProjectionInputQuoterCheckedOutputConstruction :=
  selectedProjectionInputQuoterCheckedOutputConstruction_of_postBoundary
    selectedProjectionInputQuoterPostBoundaryOutputComponentConstruction_scaffold

theorem selectedProjectionInputQuoterOutputConstruction_of_componentScaffold :
    SelectedProjectionInputQuoterOutputConstruction :=
  selectedProjectionInputQuoterOutputConstruction_of_postBoundary
    selectedProjectionInputQuoterPostBoundaryOutputComponentConstruction_scaffold

theorem selectedProjectionInputQuoterOutputConstruction_scaffold_of_checked :
    SelectedProjectionInputQuoterOutputConstruction :=
  selectedProjectionInputQuoterCheckedOutputConstruction_scaffold.toOutputConstruction

theorem selectedProjectionInputQuoterOutputConstruction_scaffold_of_exactShape :
    SelectedProjectionInputQuoterOutputConstruction :=
  selectedProjectionInputQuoterExactShapeOutputConstruction_scaffold.toOutputConstruction

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
