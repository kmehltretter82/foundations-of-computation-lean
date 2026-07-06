import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.PhaseOutputAdapters
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.Output
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.ScaffoldOutput

set_option doc.verso true

/-!
# Hybrid output composition for padded selected projection

The padded emitter needs the input quoter to hand off an exact source tape for
the tail phase.  It does not, however, need the tail phase to provide an exact
final tape when the caller only consumes normalized output.  This module records
that hybrid route explicitly: exact quoter handoff plus tail-output endpoint.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

/-! ## Hybrid component contracts -/

def SelectedProjectionCheckedEquivPaddedEmitterHybridOutputComponentConstruction :
    Prop :=
  SelectedProjectionInputQuoterConstruction ∧
    SelectedProjectionPaddedTailEmitterOutputConstruction

def SelectedProjectionCheckedEquivPaddedEmitterHybridOutputSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  SelectedProjectionCheckedEquivPaddedEmitterOutputSpec useAccept emitter

def SelectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction :
    Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedProjectionCheckedEquivPaddedEmitterHybridOutputSpec
        useAccept emitter

def SelectedProjectionCheckedEquivEmitterHybridOutputConstruction : Prop :=
  SelectedProjectionCheckedEquivEmitterOutputConstruction

def SelectedProjectionFiniteDescriptionForwardHybridOutputConstruction :
    Prop :=
  SelectedProjectionFiniteDescriptionForwardOutputConstruction

/-! ## Accessors for existing output specs -/

theorem SelectedProjectionPaddedTailEmitterOutputSpec.subroutineReady
    {useAccept : Bool} {tail : MachineDescription}
    (htail : SelectedProjectionPaddedTailEmitterOutputSpec useAccept tail) :
    tail.SubroutineReady :=
  htail.left

theorem SelectedProjectionPaddedTailEmitterOutputSpec.haltsFromTapeWithOutput
    {useAccept : Bool} {tail : MachineDescription}
    (htail : SelectedProjectionPaddedTailEmitterOutputSpec useAccept tail)
    (L : DovetailLayout) :
    tail.HaltsFromTapeWithOutput
      (SelectedProjectionTailProjector.sourceTape L
        ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
          some))
      (Tape.normalizedOutput
        (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L)) :=
  htail.right L

theorem SelectedProjectionCheckedEquivPaddedEmitterHybridOutputSpec.subroutineReady
    {useAccept : Bool} {emitter : MachineDescription}
    (hemits :
      SelectedProjectionCheckedEquivPaddedEmitterHybridOutputSpec
        useAccept emitter) :
    emitter.SubroutineReady :=
  hemits.left

theorem SelectedProjectionCheckedEquivPaddedEmitterHybridOutputSpec.haltsFromTapeWithOutput
    {useAccept : Bool} {emitter : MachineDescription}
    (hemits :
      SelectedProjectionCheckedEquivPaddedEmitterHybridOutputSpec
        useAccept emitter)
    (L : DovetailLayout) :
    emitter.HaltsFromTapeWithOutput
      (ParsedLayoutCheckedTape L)
      (Tape.normalizedOutput
        (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L)) :=
  hemits.right L

theorem SelectedProjectionCheckedEquivPaddedEmitterHybridOutputSpec.toPaddedOutputSpec
    {useAccept : Bool} {emitter : MachineDescription}
    (hemits :
      SelectedProjectionCheckedEquivPaddedEmitterHybridOutputSpec
        useAccept emitter) :
    SelectedProjectionCheckedEquivPaddedEmitterOutputSpec
      useAccept emitter :=
  hemits

theorem SelectedProjectionCheckedEquivPaddedEmitterOutputSpec.toHybridOutputSpec
    {useAccept : Bool} {emitter : MachineDescription}
    (hemits :
      SelectedProjectionCheckedEquivPaddedEmitterOutputSpec
        useAccept emitter) :
    SelectedProjectionCheckedEquivPaddedEmitterHybridOutputSpec
      useAccept emitter :=
  hemits

/-! ## Direct hybrid composition -/

def SelectedProjectionCheckedEquivPaddedEmitterFromHybridOutputComponents
    (quoter tail : MachineDescription) : MachineDescription :=
  SelectedProjectionCheckedEquivPaddedEmitterFromComponents quoter tail

theorem selectedProjectionCheckedEquivPaddedEmitterHybridOutputSpec_of_components
    {useAccept : Bool}
    {quoter tail : MachineDescription}
    (hquoter : SelectedProjectionInputQuoterSpec quoter)
    (htail : SelectedProjectionPaddedTailEmitterOutputSpec useAccept tail) :
    SelectedProjectionCheckedEquivPaddedEmitterHybridOutputSpec useAccept
      (SelectedProjectionCheckedEquivPaddedEmitterFromHybridOutputComponents
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
        Tape.move Direction.left
            (Tape.move Direction.right
              (SelectedProjectionTailProjector.sourceTape L
                (baseLeft L))) =
          SelectedProjectionTailProjector.sourceTape L
            (baseLeft L) := by
      exact
        SelectedProjectionTailProjector.sourceTape_move_left_move_right
          L (baseLeft L)
    simpa [SelectedProjectionCheckedEquivPaddedEmitterFromHybridOutputComponents,
      SelectedProjectionCheckedEquivPaddedEmitterFromComponents] using
      SeqViaCanonical_haltsFromTapeWithOutput_of_haltsFromTape_eq
        hquoter.left htail.left hquoterRun hbridge
        (htail.haltsFromTapeWithOutput L)

theorem selectedProjectionCheckedEquivPaddedEmitterOutputSpec_of_hybridComponents
    {useAccept : Bool}
    {quoter tail : MachineDescription}
    (hquoter : SelectedProjectionInputQuoterSpec quoter)
    (htail : SelectedProjectionPaddedTailEmitterOutputSpec useAccept tail) :
    SelectedProjectionCheckedEquivPaddedEmitterOutputSpec useAccept
      (SelectedProjectionCheckedEquivPaddedEmitterFromHybridOutputComponents
        quoter tail) :=
  (selectedProjectionCheckedEquivPaddedEmitterHybridOutputSpec_of_components
    hquoter htail).toPaddedOutputSpec

theorem selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_of_components
    (hcomponents :
      SelectedProjectionCheckedEquivPaddedEmitterHybridOutputComponentConstruction) :
    SelectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction := by
  intro useAccept
  rcases hcomponents with ⟨⟨quoter, hquoter⟩, htailConstruction⟩
  rcases htailConstruction useAccept with ⟨tail, htail⟩
  exact
    ⟨SelectedProjectionCheckedEquivPaddedEmitterFromHybridOutputComponents
        quoter tail,
      selectedProjectionCheckedEquivPaddedEmitterHybridOutputSpec_of_components
        hquoter htail⟩

theorem selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_of_hybridComponents
    (hcomponents :
      SelectedProjectionCheckedEquivPaddedEmitterHybridOutputComponentConstruction) :
    SelectedProjectionCheckedEquivPaddedEmitterOutputConstruction := by
  intro useAccept
  rcases
      selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_of_components
        hcomponents useAccept with
    ⟨emitter, hemits⟩
  exact ⟨emitter, hemits.toPaddedOutputSpec⟩

/-! ## Component constructors -/

theorem selectedProjectionCheckedEquivPaddedEmitterHybridOutputComponentConstruction_of_exactTail
    (hcomponents :
      SelectedProjectionCheckedEquivPaddedEmitterComponentConstruction) :
    SelectedProjectionCheckedEquivPaddedEmitterHybridOutputComponentConstruction := by
  rcases hcomponents with ⟨hquoter, htail⟩
  exact ⟨hquoter, selectedProjectionPaddedTailEmitterOutputConstruction_of_exact htail⟩

theorem selectedProjectionCheckedEquivPaddedEmitterHybridOutputComponentConstruction_of_tailOutput
    (htail :
      SelectedProjectionPaddedTailEmitterOutputConstruction) :
    SelectedProjectionCheckedEquivPaddedEmitterHybridOutputComponentConstruction :=
  ⟨selectedProjectionInputQuoterConstruction_scaffold, htail⟩

theorem selectedProjectionCheckedEquivPaddedEmitterHybridOutputComponentConstruction_scaffold :
    SelectedProjectionCheckedEquivPaddedEmitterHybridOutputComponentConstruction :=
  selectedProjectionCheckedEquivPaddedEmitterHybridOutputComponentConstruction_of_tailOutput
    selectedProjectionPaddedTailEmitterOutputConstruction_scaffold

theorem selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_of_tailOutput
    (htail :
      SelectedProjectionPaddedTailEmitterOutputConstruction) :
    SelectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction :=
  selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_of_components
    (selectedProjectionCheckedEquivPaddedEmitterHybridOutputComponentConstruction_of_tailOutput
      htail)

theorem selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_of_tailOutput
    (htail :
      SelectedProjectionPaddedTailEmitterOutputConstruction) :
    SelectedProjectionCheckedEquivPaddedEmitterOutputConstruction :=
  selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_of_hybridComponents
    (selectedProjectionCheckedEquivPaddedEmitterHybridOutputComponentConstruction_of_tailOutput
      htail)

theorem selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_scaffold :
    SelectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction :=
  selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_of_tailOutput
    selectedProjectionPaddedTailEmitterOutputConstruction_scaffold

theorem selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_hybrid_scaffold :
    SelectedProjectionCheckedEquivPaddedEmitterOutputConstruction :=
  selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_of_tailOutput
    selectedProjectionPaddedTailEmitterOutputConstruction_scaffold

theorem selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_of_exactComponents_viaHybrid
    (hcomponents :
      SelectedProjectionCheckedEquivPaddedEmitterComponentConstruction) :
    SelectedProjectionCheckedEquivPaddedEmitterOutputConstruction :=
  selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_of_hybridComponents
    (selectedProjectionCheckedEquivPaddedEmitterHybridOutputComponentConstruction_of_exactTail
      hcomponents)

/-! ## Downstream output wrappers -/

theorem selectedProjectionCheckedEquivEmitterHybridOutputConstruction_of_padded
    (h :
      SelectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction) :
    SelectedProjectionCheckedEquivEmitterHybridOutputConstruction :=
  selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_haltsToOutput
    (by
      intro useAccept
      rcases h useAccept with ⟨emitter, hemits⟩
      exact ⟨emitter, hemits.toPaddedOutputSpec⟩)

theorem selectedProjectionCheckedEquivEmitterOutputConstruction_of_hybrid
    (h :
      SelectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction) :
    SelectedProjectionCheckedEquivEmitterOutputConstruction :=
  selectedProjectionCheckedEquivEmitterHybridOutputConstruction_of_padded h

theorem selectedProjectionCheckedEquivEmitterHybridOutputConstruction_scaffold :
    SelectedProjectionCheckedEquivEmitterHybridOutputConstruction :=
  selectedProjectionCheckedEquivEmitterHybridOutputConstruction_of_padded
    selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_scaffold

theorem selectedProjectionCheckedEquivEmitterOutputConstruction_hybrid_scaffold :
    SelectedProjectionCheckedEquivEmitterOutputConstruction :=
  selectedProjectionCheckedEquivEmitterOutputConstruction_of_hybrid
    selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_scaffold

theorem selectedProjectionFiniteDescriptionForwardHybridOutputConstruction_of_padded
    (h :
      SelectedProjectionCheckedEquivPaddedEmitterConstruction) :
    SelectedProjectionFiniteDescriptionForwardHybridOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_exact
    (selectedProjectionFiniteDescriptionConstruction_of_checkedEquivEmitter
      (selectedProjectionCheckedEquivEmitterConstruction_of_padded h))

theorem selectedProjectionFiniteDescriptionForwardHybridOutputConstruction_of_exactTail
    (hcomponents :
      SelectedProjectionCheckedEquivPaddedEmitterComponentConstruction) :
    SelectedProjectionFiniteDescriptionForwardHybridOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_exact
    (selectedProjectionFiniteDescriptionConstruction_of_checkedEquivEmitter
      (selectedProjectionCheckedEquivEmitterConstruction_of_padded
        (selectedProjectionCheckedEquivPaddedEmitterConstruction_of_components
          hcomponents)))

theorem selectedProjectionFiniteDescriptionForwardHybridOutputConstruction_scaffold :
    SelectedProjectionFiniteDescriptionForwardHybridOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_scaffold

/-! ## Named scaffold variants -/

theorem selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_scaffold_of_postErase
    (hpostEraseConstruction :
      SelectedProjectionPaddedTailCleanup.SelectedProjectionPaddedTailCleanupPostEraseConstruction) :
    SelectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction :=
  selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_of_tailOutput
    (selectedProjectionPaddedTailEmitterOutputConstruction_scaffold_of_postErase
      hpostEraseConstruction)

theorem selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_hybrid_scaffold_of_postErase
    (hpostEraseConstruction :
      SelectedProjectionPaddedTailCleanup.SelectedProjectionPaddedTailCleanupPostEraseConstruction) :
    SelectedProjectionCheckedEquivPaddedEmitterOutputConstruction :=
  selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_of_tailOutput
    (selectedProjectionPaddedTailEmitterOutputConstruction_scaffold_of_postErase
      hpostEraseConstruction)

theorem selectedProjectionCheckedEquivEmitterHybridOutputConstruction_scaffold_of_postErase
    (hpostEraseConstruction :
      SelectedProjectionPaddedTailCleanup.SelectedProjectionPaddedTailCleanupPostEraseConstruction) :
    SelectedProjectionCheckedEquivEmitterHybridOutputConstruction :=
  selectedProjectionCheckedEquivEmitterHybridOutputConstruction_of_padded
    (selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_scaffold_of_postErase
      hpostEraseConstruction)

theorem selectedProjectionCheckedEquivEmitterOutputConstruction_hybrid_scaffold_of_postErase
    (hpostEraseConstruction :
      SelectedProjectionPaddedTailCleanup.SelectedProjectionPaddedTailCleanupPostEraseConstruction) :
    SelectedProjectionCheckedEquivEmitterOutputConstruction :=
  selectedProjectionCheckedEquivEmitterOutputConstruction_of_hybrid
    (selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_scaffold_of_postErase
      hpostEraseConstruction)

theorem SelectedProjectionCheckedEquivPaddedEmitterHybridOutputSpec.haltsToSelectedProjectionOutput
    {useAccept : Bool} {emitter : MachineDescription}
    (hemits :
      SelectedProjectionCheckedEquivPaddedEmitterHybridOutputSpec
        useAccept emitter)
    (L : DovetailLayout) :
    emitter.HaltsFromTapeWithOutput
      (ParsedLayoutCheckedTape L)
      (Tape.normalizedOutput
        (SelectedProjectionOutputTape useAccept L)) := by
  have hnorm :
      Tape.normalizedOutput
          (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L) =
        Tape.normalizedOutput
          (SelectedProjectionOutputTape useAccept L) :=
    Tape.Equiv.normalizedOutput_eq
      (SelectedProjectionEquivEmitterPaddedOutputTape_equiv
        useAccept L)
  simpa [hnorm] using hemits.haltsFromTapeWithOutput L

theorem SelectedProjectionCheckedEquivPaddedEmitterHybridOutputSpec.toCheckedEquivEmitterOutputSpec
    {useAccept : Bool} {emitter : MachineDescription}
    (hemits :
      SelectedProjectionCheckedEquivPaddedEmitterHybridOutputSpec
        useAccept emitter) :
    SelectedProjectionCheckedEquivEmitterOutputSpec useAccept emitter := by
  constructor
  · exact hemits.subroutineReady
  · intro L
    exact hemits.haltsToSelectedProjectionOutput L

theorem selectedProjectionCheckedEquivEmitterOutputConstruction_of_hybridOutputConstruction
    (h :
      SelectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction) :
    SelectedProjectionCheckedEquivEmitterOutputConstruction := by
  intro useAccept
  rcases h useAccept with ⟨emitter, hemits⟩
  exact ⟨emitter, hemits.toCheckedEquivEmitterOutputSpec⟩

theorem selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_scaffold_of_prefixAndFootprintCases
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    SelectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction :=
  selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_of_tailOutput
    (selectedProjectionPaddedTailEmitterOutputConstruction_scaffold_of_prefixAndFootprintCases
      hprefix hcases)

theorem selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_hybrid_scaffold_of_prefixAndFootprintCases
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    SelectedProjectionCheckedEquivPaddedEmitterOutputConstruction :=
  selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_of_tailOutput
    (selectedProjectionPaddedTailEmitterOutputConstruction_scaffold_of_prefixAndFootprintCases
      hprefix hcases)

theorem selectedProjectionCheckedEquivEmitterOutputConstruction_hybrid_scaffold_of_prefixAndFootprintCases
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    SelectedProjectionCheckedEquivEmitterOutputConstruction :=
  selectedProjectionCheckedEquivEmitterOutputConstruction_of_hybridOutputConstruction
    (selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_scaffold_of_prefixAndFootprintCases
      hprefix hcases)

theorem selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_scaffold_of_prefixAndFootprintBitPaddingCases
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction :=
  selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_of_tailOutput
    (selectedProjectionPaddedTailEmitterOutputConstruction_scaffold_of_prefixAndFootprintBitPaddingCases
      hprefix hcases)

theorem selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_hybrid_scaffold_of_prefixAndFootprintBitPaddingCases
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionCheckedEquivPaddedEmitterOutputConstruction :=
  selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_of_tailOutput
    (selectedProjectionPaddedTailEmitterOutputConstruction_scaffold_of_prefixAndFootprintBitPaddingCases
      hprefix hcases)

theorem selectedProjectionCheckedEquivEmitterOutputConstruction_hybrid_scaffold_of_prefixAndFootprintBitPaddingCases
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionCheckedEquivEmitterOutputConstruction :=
  selectedProjectionCheckedEquivEmitterOutputConstruction_of_hybridOutputConstruction
    (selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_scaffold_of_prefixAndFootprintBitPaddingCases
      hprefix hcases)

theorem selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_scaffold_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
    (heraser :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction :=
  selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_of_tailOutput
    (selectedProjectionPaddedTailEmitterOutputConstruction_scaffold_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
      heraser hcases)

theorem selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_hybrid_scaffold_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
    (heraser :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionCheckedEquivPaddedEmitterOutputConstruction :=
  selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_of_tailOutput
    (selectedProjectionPaddedTailEmitterOutputConstruction_scaffold_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
      heraser hcases)

theorem selectedProjectionCheckedEquivEmitterOutputConstruction_hybrid_scaffold_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
    (heraser :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionCheckedEquivEmitterOutputConstruction :=
  selectedProjectionCheckedEquivEmitterOutputConstruction_of_hybridOutputConstruction
    (selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_scaffold_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
      heraser hcases)

theorem selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_of_postPadding
    (hpostPadding :
      SelectedProjectionPaddedTailCleanup.SelectedProjectionPaddedTailCleanupPostPaddingConstruction) :
    SelectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction :=
  selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_of_tailOutput
    (selectedProjectionPaddedTailEmitterOutputConstruction_of_postPadding
      hpostPadding)

theorem selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_hybrid_of_postPadding
    (hpostPadding :
      SelectedProjectionPaddedTailCleanup.SelectedProjectionPaddedTailCleanupPostPaddingConstruction) :
    SelectedProjectionCheckedEquivPaddedEmitterOutputConstruction :=
  selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_of_tailOutput
    (selectedProjectionPaddedTailEmitterOutputConstruction_of_postPadding
      hpostPadding)

theorem selectedProjectionCheckedEquivEmitterOutputConstruction_hybrid_of_postPadding
    (hpostPadding :
      SelectedProjectionPaddedTailCleanup.SelectedProjectionPaddedTailCleanupPostPaddingConstruction) :
    SelectedProjectionCheckedEquivEmitterOutputConstruction :=
  selectedProjectionCheckedEquivEmitterOutputConstruction_of_hybridOutputConstruction
    (selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_of_postPadding
      hpostPadding)

theorem selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_of_prefixAndFootprintCases
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    SelectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction :=
  selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_of_tailOutput
    (selectedProjectionPaddedTailEmitterOutputConstruction_of_prefixAndFootprintCases
      hprefix hcases)

theorem selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_of_prefixAndFootprintBitPaddingCases
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction :=
  selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_of_tailOutput
    (selectedProjectionPaddedTailEmitterOutputConstruction_of_prefixAndFootprintBitPaddingCases
      hprefix hcases)

theorem selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
    (heraser :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction :=
  selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_of_tailOutput
    (selectedProjectionPaddedTailEmitterOutputConstruction_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
      heraser hcases)

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
