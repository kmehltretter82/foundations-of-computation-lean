import FoC.Computability.Compiler.ClosedCfg.ProjTail.PostPaddingCloseout

set_option doc.verso true

/-!
# Post-padding output endpoints

This module records normalized-output views for the post-padding and post-erase
tail-cleanup boundaries.  The exact/equivalence closeout remains the executable
contract used by the scaffold; these views let downstream routes depend only on
the emitted word when exact cursor placement is not relevant.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionPaddedTailCleanup

open CanonicalLayouts.DovetailLayoutScanner

private theorem haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
    {D : MachineDescription} {Tin Tout : Tape Bool}
    (h : D.HaltsFromTapeEquiv Tin Tout) :
    D.HaltsFromTapeWithOutput Tin (Tape.normalizedOutput Tout) :=
  MachineDescription.haltsFromTapeWithOutput_of_haltsFromTapeEquiv h

private theorem haltsFromTapeWithOutput_of_haltsFromTape_target
    {D : MachineDescription} {Tin Tout : Tape Bool}
    (h : D.HaltsFromTape Tin Tout) :
    D.HaltsFromTapeWithOutput Tin (Tape.normalizedOutput Tout) :=
  MachineDescription.haltsFromTapeWithOutput_of_haltsFromTape h

def SelectedProjectionPaddedTailCleanupPostPaddingBaseSourceMaterializerOutputSpec
    (useAccept : Bool) (materializer : MachineDescription) : Prop :=
  materializer.SubroutineReady ∧
    forall L : DovetailLayout,
      materializer.HaltsFromTapeWithOutput
        (selectedHitOtherFlagErasedAfterPaddingTape useAccept L)
        (Tape.normalizedOutput
          (selectedProjectionPaddedTailCleanupBaseSourceTape useAccept L))

def SelectedProjectionPaddedTailCleanupPostPaddingSourceMaterializerOutputSpec
    (useAccept : Bool) (materializer : MachineDescription) : Prop :=
  materializer.SubroutineReady ∧
    forall L : DovetailLayout,
      materializer.HaltsFromTapeWithOutput
        (selectedHitOtherFlagErasedAfterPaddingTape useAccept L)
        (Tape.normalizedOutput
          (selectedProjectionPaddedTailCleanupLayoutScratchSourceTape
            useAccept L))

def SelectedProjectionPaddedTailCleanupPostPaddingOutputSpec
    (useAccept : Bool) (postPadding : MachineDescription) : Prop :=
  postPadding.SubroutineReady ∧
    forall L : DovetailLayout,
      postPadding.HaltsFromTapeWithOutput
        (selectedHitOtherFlagErasedAfterPaddingTape useAccept L)
        (Tape.normalizedOutput
          (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L))

def SelectedProjectionPaddedTailCleanupPostEraseOutputSpec
    (useAccept : Bool) (postErase : MachineDescription) : Prop :=
  postErase.SubroutineReady ∧
    forall L : DovetailLayout,
      postErase.HaltsFromTapeWithOutput
        (selectedHitOtherFlagErasedRightLeftHandoffTape useAccept L)
        (Tape.normalizedOutput
          (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L))

def SelectedProjectionPaddedTailCleanupOutputSpec
    (useAccept : Bool) (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall L : DovetailLayout,
      cleanup.HaltsFromTapeWithOutput
        (SelectedProjectionTailProjector.sourceScannerRightHandoffTape L
          ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
            some))
        (Tape.normalizedOutput
          (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L))

def SelectedProjectionPaddedTailCleanupExactShapeOutputSpec
    (useAccept : Bool) (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall L : DovetailLayout,
      cleanup.HaltsFromTapeWithOutput
        (SelectedProjectionTailProjector.sourceScannerRightHandoffTape L
          ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
            some))
        (Tape.normalizedOutput
          (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L))

def SelectedProjectionPaddedTailEmitterOutputSpec
    (useAccept : Bool) (tail : MachineDescription) : Prop :=
  tail.SubroutineReady ∧
    forall L : DovetailLayout,
      tail.HaltsFromTapeWithOutput
        (SelectedProjectionTailProjector.sourceTape L
          ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
            some))
        (Tape.normalizedOutput
          (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L))

def SelectedProjectionPaddedTailCleanupPostPaddingOutputConstruction :
    Prop :=
  forall useAccept : Bool,
    exists postPadding : MachineDescription,
      SelectedProjectionPaddedTailCleanupPostPaddingOutputSpec
        useAccept postPadding

def SelectedProjectionPaddedTailCleanupPostEraseOutputConstruction :
    Prop :=
  forall useAccept : Bool,
    exists postErase : MachineDescription,
      SelectedProjectionPaddedTailCleanupPostEraseOutputSpec
        useAccept postErase

def SelectedProjectionPaddedTailCleanupOutputConstruction : Prop :=
  forall useAccept : Bool,
    exists cleanup : MachineDescription,
      SelectedProjectionPaddedTailCleanupOutputSpec useAccept cleanup

def SelectedProjectionPaddedTailCleanupExactShapeOutputConstruction :
    Prop :=
  forall useAccept : Bool,
    exists cleanup : MachineDescription,
      SelectedProjectionPaddedTailCleanupExactShapeOutputSpec
        useAccept cleanup

def SelectedProjectionPaddedTailEmitterOutputConstruction : Prop :=
  forall useAccept : Bool,
    exists tail : MachineDescription,
      SelectedProjectionPaddedTailEmitterOutputSpec useAccept tail

theorem selectedProjectionPaddedTailCleanupPostPaddingBaseSourceMaterializerOutputSpec_of_exact
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      SelectedProjectionPaddedTailCleanupPostPaddingBaseSourceMaterializerSpec
        useAccept materializer) :
    SelectedProjectionPaddedTailCleanupPostPaddingBaseSourceMaterializerOutputSpec
      useAccept materializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro L
  exact haltsFromTapeWithOutput_of_haltsFromTape_target (hrun L)

theorem selectedProjectionPaddedTailCleanupPostPaddingSourceMaterializerOutputSpec_of_exact
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      SelectedProjectionPaddedTailCleanupPostPaddingSourceMaterializerSpec
        useAccept materializer) :
    SelectedProjectionPaddedTailCleanupPostPaddingSourceMaterializerOutputSpec
      useAccept materializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro L
  exact haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target (hrun L)

theorem selectedProjectionPaddedTailCleanupPostPaddingOutputSpec_of_exact
    {useAccept : Bool} {postPadding : MachineDescription}
    (hpostPadding :
      SelectedProjectionPaddedTailCleanupPostPaddingSpec
        useAccept postPadding) :
    SelectedProjectionPaddedTailCleanupPostPaddingOutputSpec
      useAccept postPadding := by
  rcases hpostPadding with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro L
  exact haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target (hrun L)

theorem selectedProjectionPaddedTailCleanupPostPaddingOutputConstruction_of_exact
    (h :
      SelectedProjectionPaddedTailCleanupPostPaddingConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingOutputConstruction := by
  intro useAccept
  rcases h useAccept with ⟨postPadding, hpostPadding⟩
  exact
    ⟨postPadding,
      selectedProjectionPaddedTailCleanupPostPaddingOutputSpec_of_exact
        hpostPadding⟩

theorem selectedProjectionPaddedTailCleanupPostEraseOutputSpec_of_exact
    {useAccept : Bool} {postErase : MachineDescription}
    (hpostErase :
      SelectedProjectionPaddedTailCleanupPostEraseSpec
        useAccept postErase) :
    SelectedProjectionPaddedTailCleanupPostEraseOutputSpec
      useAccept postErase := by
  rcases hpostErase with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro L
  exact haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target (hrun L)

theorem selectedProjectionPaddedTailCleanupPostEraseOutputConstruction_of_exact
    (h :
      SelectedProjectionPaddedTailCleanupPostEraseConstruction) :
    SelectedProjectionPaddedTailCleanupPostEraseOutputConstruction := by
  intro useAccept
  rcases h useAccept with ⟨postErase, hpostErase⟩
  exact
    ⟨postErase,
      selectedProjectionPaddedTailCleanupPostEraseOutputSpec_of_exact
        hpostErase⟩

theorem selectedProjectionPaddedTailCleanupOutputSpec_of_exact
    {useAccept : Bool} {cleanup : MachineDescription}
    (hcleanup :
      SelectedProjectionPaddedTailCleanupSpec useAccept cleanup) :
    SelectedProjectionPaddedTailCleanupOutputSpec
      useAccept cleanup := by
  rcases hcleanup with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro L
  exact haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target (hrun L)

theorem selectedProjectionPaddedTailCleanupOutputConstruction_of_exact
    (h :
      SelectedProjectionPaddedTailCleanupConstruction) :
    SelectedProjectionPaddedTailCleanupOutputConstruction := by
  intro useAccept
  rcases h useAccept with ⟨cleanup, hcleanup⟩
  exact
    ⟨cleanup,
      selectedProjectionPaddedTailCleanupOutputSpec_of_exact hcleanup⟩

theorem selectedProjectionPaddedTailCleanupExactShapeOutputSpec_of_exact
    {useAccept : Bool} {cleanup : MachineDescription}
    (hcleanup :
      SelectedProjectionPaddedTailCleanupExactShapeSpec
        useAccept cleanup) :
    SelectedProjectionPaddedTailCleanupExactShapeOutputSpec
      useAccept cleanup := by
  rcases hcleanup with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro L
  exact haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target (hrun L)

theorem selectedProjectionPaddedTailCleanupExactShapeOutputConstruction_of_exact
    (h :
      SelectedProjectionPaddedTailCleanupExactShapeConstruction) :
    SelectedProjectionPaddedTailCleanupExactShapeOutputConstruction := by
  intro useAccept
  rcases h useAccept with ⟨cleanup, hcleanup⟩
  exact
    ⟨cleanup,
      selectedProjectionPaddedTailCleanupExactShapeOutputSpec_of_exact
        hcleanup⟩

theorem selectedProjectionPaddedTailCleanupOutputSpec_of_exactShapeOutputSpec
    {useAccept : Bool} {cleanup : MachineDescription}
    (hcleanup :
      SelectedProjectionPaddedTailCleanupExactShapeOutputSpec
        useAccept cleanup) :
    SelectedProjectionPaddedTailCleanupOutputSpec useAccept cleanup :=
  hcleanup

theorem selectedProjectionPaddedTailCleanupOutputConstruction_of_exactShapeOutput
    (h :
      SelectedProjectionPaddedTailCleanupExactShapeOutputConstruction) :
    SelectedProjectionPaddedTailCleanupOutputConstruction := by
  intro useAccept
  rcases h useAccept with ⟨cleanup, hcleanup⟩
  exact
    ⟨cleanup,
      selectedProjectionPaddedTailCleanupOutputSpec_of_exactShapeOutputSpec
        hcleanup⟩

theorem selectedProjectionPaddedTailEmitterOutputSpec_of_exact
    {useAccept : Bool} {tail : MachineDescription}
    (htail :
      SelectedProjectionPaddedTailEmitterSpec useAccept tail) :
    SelectedProjectionPaddedTailEmitterOutputSpec useAccept tail := by
  rcases htail with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro L
  exact haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target (hrun L)

theorem selectedProjectionPaddedTailEmitterOutputConstruction_of_exact
    (h :
      SelectedProjectionPaddedTailEmitterConstruction) :
    SelectedProjectionPaddedTailEmitterOutputConstruction := by
  intro useAccept
  rcases h useAccept with ⟨tail, htail⟩
  exact
    ⟨tail,
      selectedProjectionPaddedTailEmitterOutputSpec_of_exact htail⟩

theorem selectedProjectionPaddedTailCleanupPostPaddingSourceMaterializerOutputSpec_of_baseAndScratch
    {useAccept : Bool}
    {baseMaterializer allocator : MachineDescription}
    (hbase :
      SelectedProjectionPaddedTailCleanupPostPaddingBaseSourceMaterializerSpec
        useAccept baseMaterializer)
    (hallocator :
      SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorSpec
        useAccept allocator) :
    SelectedProjectionPaddedTailCleanupPostPaddingSourceMaterializerOutputSpec
      useAccept (canonicalSeqDescription baseMaterializer allocator) :=
  selectedProjectionPaddedTailCleanupPostPaddingSourceMaterializerOutputSpec_of_exact
    (selectedProjectionPaddedTailCleanupPostPaddingSourceMaterializerSpec_of_baseAndScratch
      hbase hallocator)

theorem selectedProjectionPaddedTailCleanupPostPaddingOutputConstruction_of_sourceMaterializer
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      SelectedProjectionPaddedTailCleanupPostPaddingSourceMaterializerSpec
        useAccept materializer) :
    exists postPadding : MachineDescription,
      SelectedProjectionPaddedTailCleanupPostPaddingOutputSpec
        useAccept postPadding := by
  rcases
      selectedProjectionPaddedTailCleanupPostPaddingConstruction_of_sourceMaterializer
        hmaterializer with
    ⟨postPadding, hpostPadding⟩
  exact
    ⟨postPadding,
      selectedProjectionPaddedTailCleanupPostPaddingOutputSpec_of_exact
        hpostPadding⟩

theorem selectedProjectionPaddedTailCleanupPostPaddingOutputConstruction_of_scratchAllocators
    (h :
      SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingOutputConstruction := by
  intro useAccept
  rcases h useAccept with ⟨allocator, hallocator⟩
  cases useAccept
  · exact
      selectedProjectionPaddedTailCleanupPostPaddingOutputConstruction_of_sourceMaterializer
        (selectedProjectionPaddedTailCleanupPostPaddingSourceMaterializerSpec_of_baseAndScratch
          selectedProjectionPaddedTailCleanupRejectBaseSourceMaterializerSpec
          hallocator)
  · exact
      selectedProjectionPaddedTailCleanupPostPaddingOutputConstruction_of_sourceMaterializer
        (selectedProjectionPaddedTailCleanupPostPaddingSourceMaterializerSpec_of_baseAndScratch
          selectedProjectionPaddedTailCleanupAcceptBaseSourceMaterializerSpec
          hallocator)

theorem selectedProjectionPaddedTailCleanupPostEraseOutputSpec_of_postPadding
    {useAccept : Bool} {postPadding : MachineDescription}
    (hpostPadding :
      SelectedProjectionPaddedTailCleanupPostPaddingSpec
        useAccept postPadding) :
    SelectedProjectionPaddedTailCleanupPostEraseOutputSpec useAccept
      (selectedHitOtherFlagErasedPostEraseFromPostPadding
        useAccept postPadding) :=
  selectedProjectionPaddedTailCleanupPostEraseOutputSpec_of_exact
    (selectedProjectionPaddedTailCleanupPostEraseSpec_of_postPadding
      hpostPadding)

theorem selectedProjectionPaddedTailCleanupPostEraseOutputConstruction_of_postPadding
    (h :
      SelectedProjectionPaddedTailCleanupPostPaddingConstruction) :
    SelectedProjectionPaddedTailCleanupPostEraseOutputConstruction :=
  selectedProjectionPaddedTailCleanupPostEraseOutputConstruction_of_exact
    (selectedProjectionPaddedTailCleanupPostEraseConstruction_of_postPadding h)

theorem selectedProjectionPaddedTailCleanupPostEraseOutputConstruction_of_scratchAllocators
    (h :
      SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction) :
    SelectedProjectionPaddedTailCleanupPostEraseOutputConstruction := by
  intro useAccept
  rcases h useAccept with ⟨allocator, hallocator⟩
  cases useAccept
  · rcases
        selectedProjectionPaddedTailCleanupPostPaddingConstruction_of_sourceMaterializer
          (selectedProjectionPaddedTailCleanupPostPaddingSourceMaterializerSpec_of_baseAndScratch
            selectedProjectionPaddedTailCleanupRejectBaseSourceMaterializerSpec
            hallocator) with
      ⟨postPadding, hpostPadding⟩
    exact
      ⟨selectedHitOtherFlagErasedPostEraseFromPostPadding
          false postPadding,
        selectedProjectionPaddedTailCleanupPostEraseOutputSpec_of_postPadding
          hpostPadding⟩
  · rcases
        selectedProjectionPaddedTailCleanupPostPaddingConstruction_of_sourceMaterializer
          (selectedProjectionPaddedTailCleanupPostPaddingSourceMaterializerSpec_of_baseAndScratch
            selectedProjectionPaddedTailCleanupAcceptBaseSourceMaterializerSpec
            hallocator) with
      ⟨postPadding, hpostPadding⟩
    exact
      ⟨selectedHitOtherFlagErasedPostEraseFromPostPadding
          true postPadding,
        selectedProjectionPaddedTailCleanupPostEraseOutputSpec_of_postPadding
          hpostPadding⟩

theorem selectedProjectionPaddedTailCleanupExactShapeOutputConstruction_of_postErase
    (hpostEraseConstruction :
      SelectedProjectionPaddedTailCleanupPostEraseConstruction) :
    SelectedProjectionPaddedTailCleanupExactShapeOutputConstruction := by
  intro useAccept
  rcases hpostEraseConstruction useAccept with
    ⟨postErase, hpostErase⟩
  refine
    ⟨SeqViaCanonical
      (selectedHitOtherFlagErasedFromScannerDescription useAccept)
      postErase, ?_⟩
  exact
    selectedProjectionPaddedTailCleanupExactShapeOutputSpec_of_exact
      (by
        constructor
        · exact
            SeqViaCanonical_subroutineReady
              (selectedHitOtherFlagErasedFromScannerDescription_subroutineReady
                useAccept)
              hpostErase.left
        · intro L
          exact
            SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
              (selectedHitOtherFlagErasedFromScannerDescription_subroutineReady
                useAccept)
              hpostErase.left
              (selectedHitOtherFlagErasedFromScannerDescription_haltsFrom_sourceScannerRightHandoffTape
                useAccept L).toEquiv
              (by exact Tape.Equiv.refl _)
              (hpostErase.right L))

theorem selectedProjectionPaddedTailCleanupOutputConstruction_of_postErase
    (hpostEraseConstruction :
      SelectedProjectionPaddedTailCleanupPostEraseConstruction) :
    SelectedProjectionPaddedTailCleanupOutputConstruction :=
  selectedProjectionPaddedTailCleanupOutputConstruction_of_exactShapeOutput
    (selectedProjectionPaddedTailCleanupExactShapeOutputConstruction_of_postErase
      hpostEraseConstruction)

theorem selectedProjectionPaddedTailCleanupPostPaddingOutputConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingOutputConstruction :=
  selectedProjectionPaddedTailCleanupPostPaddingOutputConstruction_of_exact
    selectedProjectionPaddedTailCleanupPostPaddingConstruction

theorem selectedProjectionPaddedTailCleanupPostPaddingOutputConstruction_of_prefixAndFootprintCases
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingOutputConstruction :=
  selectedProjectionPaddedTailCleanupPostPaddingOutputConstruction_of_scratchAllocators
    (selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction_of_prefixAndFootprintCases
      hprefix hcases)

theorem selectedProjectionPaddedTailCleanupPostPaddingOutputConstruction_of_prefixAndFootprintBitPaddingCases
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingOutputConstruction :=
  selectedProjectionPaddedTailCleanupPostPaddingOutputConstruction_of_scratchAllocators
    (selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction_of_prefixAndFootprintBitPaddingCases
      hprefix hcases)

theorem selectedProjectionPaddedTailCleanupPostPaddingOutputConstruction_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
    (heraser :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingOutputConstruction :=
  selectedProjectionPaddedTailCleanupPostPaddingOutputConstruction_of_scratchAllocators
    (scratchAllocatorConstruction_ofBranchFootprintCases
      heraser hcases)

theorem selectedProjectionPaddedTailCleanupPostEraseOutputConstruction :
    SelectedProjectionPaddedTailCleanupPostEraseOutputConstruction :=
  selectedProjectionPaddedTailCleanupPostEraseOutputConstruction_of_exact
    selectedProjectionPaddedTailCleanupPostEraseConstruction

theorem selectedProjectionPaddedTailCleanupPostEraseOutputConstruction_of_prefixAndFootprintCases
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    SelectedProjectionPaddedTailCleanupPostEraseOutputConstruction :=
  selectedProjectionPaddedTailCleanupPostEraseOutputConstruction_of_scratchAllocators
    (selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction_of_prefixAndFootprintCases
      hprefix hcases)

theorem selectedProjectionPaddedTailCleanupPostEraseOutputConstruction_of_prefixAndFootprintBitPaddingCases
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionPaddedTailCleanupPostEraseOutputConstruction :=
  selectedProjectionPaddedTailCleanupPostEraseOutputConstruction_of_scratchAllocators
    (selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction_of_prefixAndFootprintBitPaddingCases
      hprefix hcases)

theorem selectedProjectionPaddedTailCleanupPostEraseOutputConstruction_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
    (heraser :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionPaddedTailCleanupPostEraseOutputConstruction :=
  selectedProjectionPaddedTailCleanupPostEraseOutputConstruction_of_scratchAllocators
    (scratchAllocatorConstruction_ofBranchFootprintCases
      heraser hcases)

theorem selectedProjectionPaddedTailCleanupExactShapeOutputConstruction :
    SelectedProjectionPaddedTailCleanupExactShapeOutputConstruction :=
  selectedProjectionPaddedTailCleanupExactShapeOutputConstruction_of_postErase
    selectedProjectionPaddedTailCleanupPostEraseConstruction

theorem selectedProjectionPaddedTailCleanupOutputConstruction :
    SelectedProjectionPaddedTailCleanupOutputConstruction :=
  selectedProjectionPaddedTailCleanupOutputConstruction_of_exactShapeOutput
    selectedProjectionPaddedTailCleanupExactShapeOutputConstruction

end SelectedProjectionPaddedTailCleanup

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
