import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.Main
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup

set_option doc.verso true

/-!
This module assembles the padded selected-projection emitter from the input
quoter and tail-cleanup components. It states the checked padded emitter
contract and proves the bridge from component constructions to the public
selected-projection construction.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

def SelectedProjectionCheckedEquivPaddedEmitterSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall L : DovetailLayout,
      emitter.HaltsFromTapeEquiv
        (ParsedLayoutCheckedTape L)
        (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L)

def SelectedProjectionCheckedEquivPaddedEmitterConstruction : Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedProjectionCheckedEquivPaddedEmitterSpec useAccept emitter



def SelectedProjectionCheckedEquivPaddedEmitterComponentConstruction :
    Prop :=
  SelectedProjectionInputQuoterConstruction ∧
    SelectedProjectionPaddedTailEmitterConstruction

def SelectedProjectionCheckedEquivPaddedEmitterFromComponents
    (quoter tail : MachineDescription) : MachineDescription :=
  SeqViaCanonical quoter tail

theorem selectedProjectionCheckedEquivPaddedEmitterSpec_of_components
    {useAccept : Bool}
    {quoter tail : MachineDescription}
    (hquoter : SelectedProjectionInputQuoterSpec quoter)
    (htail : SelectedProjectionPaddedTailEmitterSpec useAccept tail) :
    SelectedProjectionCheckedEquivPaddedEmitterSpec useAccept
      (SelectedProjectionCheckedEquivPaddedEmitterFromComponents
        quoter tail) := by
  let baseLeft :=
    fun L : DovetailLayout =>
      (SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
        some
  constructor
  · exact SeqViaCanonical_subroutineReady hquoter.left htail.left
  · intro L
    have hquoterRun :
        quoter.HaltsFromTape
          (ParsedLayoutCheckedTape L)
          (SelectedProjectionTailProjector.sourceTape L
            (baseLeft L)) :=
      hquoter.right L
    have hbridge :
        Tape.Equiv
          (Tape.move Direction.left
            (Tape.move Direction.right
              (SelectedProjectionTailProjector.sourceTape L
                (baseLeft L))))
          (SelectedProjectionTailProjector.sourceTape L
            (baseLeft L)) :=
      by
        rw [
          SelectedProjectionTailProjector.sourceTape_move_left_move_right
            L (baseLeft L)]
        exact Tape.Equiv.refl _
    simpa [SelectedProjectionCheckedEquivPaddedEmitterFromComponents] using
      SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
        hquoter.left htail.left hquoterRun.toEquiv hbridge
        (htail.right L)

theorem selectedProjectionCheckedEquivPaddedEmitterSpec_haltsToOutput
    {useAccept : Bool} {emitter : MachineDescription}
    (hemits :
      SelectedProjectionCheckedEquivPaddedEmitterSpec useAccept emitter)
    (L : DovetailLayout) :
    emitter.HaltsFromTapeEquiv
      (ParsedLayoutCheckedTape L)
      (SelectedProjectionOutputTape useAccept L) := by
  rcases hemits.right L with ⟨Tactual, hactual, hTequiv⟩
  exact
    ⟨Tactual, hactual,
      Tape.Equiv.trans hTequiv
        (SelectedProjectionEquivEmitterPaddedOutputTape_equiv
          useAccept L)⟩

theorem closedFromTapeEquiv_of_haltsFromTapeEquiv
    {D : MachineDescription} {Tin Tpadded Tout : Tape Bool}
    (hD : D.SubroutineReady)
    (hhalt : D.HaltsFromTapeEquiv Tin Tpadded)
    (hequiv : Tape.Equiv Tpadded Tout) :
    D.ClosedFromTapeEquiv Tin Tout := by
  intro T hT
  rcases hhalt with ⟨Tactual, hactual, hTactual⟩
  have hsame :
      T = Tactual :=
    MachineDescription.haltsFromTape_functional_of_haltTransitionFree
      hD.right hT hactual
  rw [hsame]
  exact Tape.Equiv.trans hTactual hequiv

theorem selectedProjectionCheckedEquivPaddedEmitterConstruction_of_components
    (hcomponents :
      SelectedProjectionCheckedEquivPaddedEmitterComponentConstruction) :
    SelectedProjectionCheckedEquivPaddedEmitterConstruction := by
  intro useAccept
  rcases hcomponents with ⟨⟨quoter, hquoter⟩, htailConstruction⟩
  rcases htailConstruction useAccept with ⟨tail, htail⟩
  exact
    ⟨SelectedProjectionCheckedEquivPaddedEmitterFromComponents quoter tail,
      selectedProjectionCheckedEquivPaddedEmitterSpec_of_components
        hquoter htail⟩

theorem selectedProjectionCheckedEquivEmitterSpec_of_padded
    {useAccept : Bool} {emitter : MachineDescription}
    (hemits :
      SelectedProjectionCheckedEquivPaddedEmitterSpec useAccept emitter) :
    SelectedProjectionCheckedEquivEmitterSpec useAccept emitter := by
  constructor
  · exact hemits.left
  constructor
  · intro L
    exact
      selectedProjectionCheckedEquivPaddedEmitterSpec_haltsToOutput
        hemits L
  · intro L T hhalt
    exact
      closedFromTapeEquiv_of_haltsFromTapeEquiv
        hemits.left (hemits.right L)
        (SelectedProjectionEquivEmitterPaddedOutputTape_equiv
          useAccept L) T hhalt

theorem selectedProjectionCheckedEquivEmitterConstruction_of_padded
    (h : SelectedProjectionCheckedEquivPaddedEmitterConstruction) :
    SelectedProjectionCheckedEquivEmitterConstruction := by
  intro useAccept
  rcases h useAccept with ⟨emitter, hemits⟩
  exact
    ⟨emitter, selectedProjectionCheckedEquivEmitterSpec_of_padded hemits⟩

theorem selectedProjectionFiniteDescriptionConstruction_scaffold_of_tailEmitter
    (htail : SelectedProjectionPaddedTailEmitterConstruction) :
    SelectedProjectionFiniteDescriptionConstruction :=
  selectedProjectionFiniteDescriptionConstruction_of_checkedEquivEmitter
    (selectedProjectionCheckedEquivEmitterConstruction_of_padded
      (selectedProjectionCheckedEquivPaddedEmitterConstruction_of_components
        ⟨selectedProjectionInputQuoterConstruction_scaffold,
          htail⟩))

theorem selectedProjectionFiniteDescriptionConstruction_scaffold_of_postErase
    (hpostEraseConstruction :
      SelectedProjectionPaddedTailCleanup.SelectedProjectionPaddedTailCleanupPostEraseConstruction) :
    SelectedProjectionFiniteDescriptionConstruction :=
  selectedProjectionFiniteDescriptionConstruction_scaffold_of_tailEmitter
    (selectedProjectionPaddedTailEmitterConstruction_scaffold_of_postErase
      hpostEraseConstruction)

theorem selectedProjectionFiniteDescriptionConstruction_scaffold_of_prefixAndFootprintCases
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    SelectedProjectionFiniteDescriptionConstruction :=
  selectedProjectionFiniteDescriptionConstruction_scaffold_of_tailEmitter
    (selectedProjectionPaddedTailEmitterConstruction_scaffold_of_prefixAndFootprintCases
      hprefix hcases)

theorem selectedProjectionFiniteDescriptionConstruction_scaffold_of_prefixAndFootprintBitPaddingCases
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionFiniteDescriptionConstruction :=
  selectedProjectionFiniteDescriptionConstruction_scaffold_of_tailEmitter
    (selectedProjectionPaddedTailEmitterConstruction_scaffold_of_prefixAndFootprintBitPaddingCases
      hprefix hcases)

theorem selectedProjectionFiniteDescriptionConstruction_scaffold_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
    (heraser :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionFiniteDescriptionConstruction :=
  selectedProjectionFiniteDescriptionConstruction_scaffold_of_tailEmitter
    (selectedProjectionPaddedTailEmitterConstruction_scaffold_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
      heraser hcases)

theorem selectedProjectionFiniteDescriptionConstruction_scaffold :
    SelectedProjectionFiniteDescriptionConstruction :=
  selectedProjectionFiniteDescriptionConstruction_scaffold_of_tailEmitter
    selectedProjectionPaddedTailEmitterConstruction_scaffold

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
