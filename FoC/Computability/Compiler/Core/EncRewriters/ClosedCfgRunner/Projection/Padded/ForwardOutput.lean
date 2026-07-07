import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.PhaseOutputAdapters
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.OutputHybrid

set_option doc.verso true

/-!
# Selected-projection finite-description forward output

The public selected-projection construction keeps closedness and tape
equivalence.  The output contracts only need the forward normalized word.  This
module composes the checked-layout parser with any checked-emitter output
construction, so output-only consumers do not have to pass through the exact
finite-description construction.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

/-! ## Component contracts -/

def SelectedProjectionFiniteDescriptionForwardCheckedOutputComponentConstruction :
    Prop :=
  LayoutCheckedParserConstruction ∧
    SelectedProjectionCheckedEquivEmitterOutputConstruction

def SelectedProjectionFiniteDescriptionForwardPaddedOutputComponentConstruction :
    Prop :=
  LayoutCheckedParserConstruction ∧
    SelectedProjectionCheckedEquivPaddedEmitterOutputConstruction

def SelectedProjectionFiniteDescriptionForwardHybridOutputComponentConstruction :
    Prop :=
  LayoutCheckedParserConstruction ∧
    SelectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction

def SelectedProjectionFiniteDescriptionForwardTailOutputComponentConstruction :
    Prop :=
  LayoutCheckedParserConstruction ∧
    SelectedProjectionCheckedEquivPaddedEmitterHybridOutputComponentConstruction

def SelectedProjectionFiniteDescriptionForwardFromCheckedEmitter
    (parser emitter : MachineDescription) : MachineDescription :=
  SeqViaCanonical parser emitter

/-! ## Spec accessors -/

theorem SelectedProjectionFiniteDescriptionForwardOutputSpec.subroutineReady
    {useAccept : Bool} {runner : MachineDescription}
    (hrunner :
      SelectedProjectionFiniteDescriptionForwardOutputSpec
        useAccept runner) :
    runner.SubroutineReady :=
  hrunner.left

theorem SelectedProjectionFiniteDescriptionForwardOutputSpec.haltsFromTapeWithOutput
    {useAccept : Bool} {runner : MachineDescription}
    (hrunner :
      SelectedProjectionFiniteDescriptionForwardOutputSpec
        useAccept runner)
    (L : DovetailLayout) :
    runner.HaltsFromTapeWithOutput
      (Tape.input (ParsedLayoutBits L))
      (Tape.normalizedOutput
        (SelectedProjectionOutputTape useAccept L)) :=
  hrunner.right L

theorem SelectedProjectionFiniteDescriptionForwardOutputSpec.haltsWithOutput
    {useAccept : Bool} {runner : MachineDescription}
    (hrunner :
      SelectedProjectionFiniteDescriptionForwardOutputSpec
        useAccept runner)
    (L : DovetailLayout) :
    runner.HaltsWithOutput
      (ParsedLayoutBits L)
      (Tape.normalizedOutput
        (SelectedProjectionOutputTape useAccept L)) := by
  rcases hrunner.haltsFromTapeWithOutput L with ⟨n, hn⟩
  exact
    ⟨n, by
      simpa [HaltsWithOutputIn, HaltsFromTapeWithOutputIn,
        MachineDescription.initial] using hn⟩

theorem SelectedProjectionCheckedEquivEmitterOutputSpec.subroutineReady
    {useAccept : Bool} {emitter : MachineDescription}
    (hemits :
      SelectedProjectionCheckedEquivEmitterOutputSpec
        useAccept emitter) :
    emitter.SubroutineReady :=
  hemits.left

theorem SelectedProjectionCheckedEquivEmitterOutputSpec.haltsFromTapeWithOutput
    {useAccept : Bool} {emitter : MachineDescription}
    (hemits :
      SelectedProjectionCheckedEquivEmitterOutputSpec
        useAccept emitter)
    (L : DovetailLayout) :
    emitter.HaltsFromTapeWithOutput
      (ParsedLayoutCheckedTape L)
      (Tape.normalizedOutput
        (SelectedProjectionOutputTape useAccept L)) :=
  hemits.right L

/-! ## Direct checked-emitter composition -/

theorem selectedProjectionFiniteDescriptionForwardOutputSpec_of_parser_checkedEmitterOutput
    {useAccept : Bool} {parser emitter : MachineDescription}
    (hparser : LayoutCheckedParserSpec parser)
    (hemits :
      SelectedProjectionCheckedEquivEmitterOutputSpec useAccept emitter) :
    SelectedProjectionFiniteDescriptionForwardOutputSpec useAccept
      (SelectedProjectionFiniteDescriptionForwardFromCheckedEmitter
        parser emitter) := by
  constructor
  · exact SeqViaCanonical_subroutineReady hparser.left hemits.left
  · intro L
    have hparserFrom :
        parser.HaltsFromTape
          (Tape.input (ParsedLayoutBits L))
          (ParsedLayoutCheckedTape L) := by
      simpa [HaltsWithTape,
        HaltsWithTapeIn,
        HaltsFromTape,
        HaltsFromTapeIn,
        initial] using hparser.right.left L
    exact
      SeqViaCanonical_haltsFromTapeWithOutput_of_haltsFromTape_eq
        hparser.left hemits.left
        hparserFrom
        (parsedLayoutCheckedTape_move_left_move_right L)
        (hemits.haltsFromTapeWithOutput L)

theorem selectedProjectionFiniteDescriptionForwardOutputSpec_of_parser_paddedEmitterOutput
    {useAccept : Bool} {parser emitter : MachineDescription}
    (hparser : LayoutCheckedParserSpec parser)
    (hemits :
      SelectedProjectionCheckedEquivPaddedEmitterOutputSpec
        useAccept emitter) :
    SelectedProjectionFiniteDescriptionForwardOutputSpec useAccept
      (SelectedProjectionFiniteDescriptionForwardFromCheckedEmitter
        parser emitter) :=
  selectedProjectionFiniteDescriptionForwardOutputSpec_of_parser_checkedEmitterOutput
    hparser
    (selectedProjectionCheckedEquivPaddedEmitterOutputSpec_haltsToOutput
      hemits)

theorem selectedProjectionFiniteDescriptionForwardOutputSpec_of_parser_hybridEmitterOutput
    {useAccept : Bool} {parser emitter : MachineDescription}
    (hparser : LayoutCheckedParserSpec parser)
    (hemits :
      SelectedProjectionCheckedEquivPaddedEmitterHybridOutputSpec
        useAccept emitter) :
    SelectedProjectionFiniteDescriptionForwardOutputSpec useAccept
      (SelectedProjectionFiniteDescriptionForwardFromCheckedEmitter
        parser emitter) :=
  selectedProjectionFiniteDescriptionForwardOutputSpec_of_parser_checkedEmitterOutput
    hparser
    hemits.toCheckedEquivEmitterOutputSpec

/-! ## Construction from checked-emitter output -/

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_of_checkedOutputComponents
    (hcomponents :
      SelectedProjectionFiniteDescriptionForwardCheckedOutputComponentConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction := by
  intro useAccept
  rcases hcomponents with ⟨⟨parser, hparser⟩, hemitsConstruction⟩
  rcases hemitsConstruction useAccept with ⟨emitter, hemits⟩
  exact
    ⟨SelectedProjectionFiniteDescriptionForwardFromCheckedEmitter
        parser emitter,
      selectedProjectionFiniteDescriptionForwardOutputSpec_of_parser_checkedEmitterOutput
        hparser hemits⟩

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_of_checkedEmitterOutput
    (hemits :
      SelectedProjectionCheckedEquivEmitterOutputConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_checkedOutputComponents
    ⟨layoutCheckedParserConstruction_scaffold, hemits⟩

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_of_paddedOutputComponents
    (hcomponents :
      SelectedProjectionFiniteDescriptionForwardPaddedOutputComponentConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction := by
  rcases hcomponents with ⟨hparser, hpadded⟩
  exact
    selectedProjectionFiniteDescriptionForwardOutputConstruction_of_checkedOutputComponents
      ⟨hparser,
        selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_haltsToOutput
          hpadded⟩

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_of_paddedEmitterOutput
    (hpadded :
      SelectedProjectionCheckedEquivPaddedEmitterOutputConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_paddedOutputComponents
    ⟨layoutCheckedParserConstruction_scaffold, hpadded⟩

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_of_hybridOutputComponents
    (hcomponents :
      SelectedProjectionFiniteDescriptionForwardHybridOutputComponentConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction := by
  rcases hcomponents with ⟨hparser, hhybrid⟩
  exact
    selectedProjectionFiniteDescriptionForwardOutputConstruction_of_checkedOutputComponents
      ⟨hparser,
        selectedProjectionCheckedEquivEmitterOutputConstruction_of_hybridOutputConstruction
          hhybrid⟩

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_of_hybridOutput
    (hhybrid :
      SelectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_hybridOutputComponents
    ⟨layoutCheckedParserConstruction_scaffold, hhybrid⟩

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_of_tailOutputComponents
    (hcomponents :
      SelectedProjectionFiniteDescriptionForwardTailOutputComponentConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction := by
  rcases hcomponents with ⟨hparser, htailComponents⟩
  exact
    selectedProjectionFiniteDescriptionForwardOutputConstruction_of_hybridOutputComponents
      ⟨hparser,
        selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_of_components
          htailComponents⟩

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_of_tailOutput
    (htail :
      SelectedProjectionPaddedTailEmitterOutputConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_hybridOutput
    (selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_of_tailOutput
      htail)

/-! ## Component adapters -/

theorem selectedProjectionFiniteDescriptionForwardCheckedOutputComponentConstruction_of_checkedEmitterOutput
    (hemits :
      SelectedProjectionCheckedEquivEmitterOutputConstruction) :
    SelectedProjectionFiniteDescriptionForwardCheckedOutputComponentConstruction :=
  ⟨layoutCheckedParserConstruction_scaffold, hemits⟩

theorem selectedProjectionFiniteDescriptionForwardCheckedOutputComponentConstruction_of_paddedEmitterOutput
    (hpadded :
      SelectedProjectionCheckedEquivPaddedEmitterOutputConstruction) :
    SelectedProjectionFiniteDescriptionForwardCheckedOutputComponentConstruction :=
  ⟨layoutCheckedParserConstruction_scaffold,
    selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_haltsToOutput
      hpadded⟩

theorem selectedProjectionFiniteDescriptionForwardCheckedOutputComponentConstruction_of_hybridEmitterOutput
    (hhybrid :
      SelectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction) :
    SelectedProjectionFiniteDescriptionForwardCheckedOutputComponentConstruction :=
  ⟨layoutCheckedParserConstruction_scaffold,
    selectedProjectionCheckedEquivEmitterOutputConstruction_of_hybridOutputConstruction
      hhybrid⟩

theorem selectedProjectionFiniteDescriptionForwardCheckedOutputComponentConstruction_of_tailEmitterOutput
    (htail :
      SelectedProjectionPaddedTailEmitterOutputConstruction) :
    SelectedProjectionFiniteDescriptionForwardCheckedOutputComponentConstruction :=
  selectedProjectionFiniteDescriptionForwardCheckedOutputComponentConstruction_of_hybridEmitterOutput
    (selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_of_tailOutput
      htail)

theorem selectedProjectionFiniteDescriptionForwardPaddedOutputComponentConstruction_of_paddedEmitterOutput
    (hpadded :
      SelectedProjectionCheckedEquivPaddedEmitterOutputConstruction) :
    SelectedProjectionFiniteDescriptionForwardPaddedOutputComponentConstruction :=
  ⟨layoutCheckedParserConstruction_scaffold, hpadded⟩

theorem selectedProjectionFiniteDescriptionForwardPaddedOutputComponentConstruction_of_tailEmitterOutput
    (htail :
      SelectedProjectionPaddedTailEmitterOutputConstruction) :
    SelectedProjectionFiniteDescriptionForwardPaddedOutputComponentConstruction :=
  ⟨layoutCheckedParserConstruction_scaffold,
    selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_of_tailOutput
      htail⟩

theorem selectedProjectionFiniteDescriptionForwardHybridOutputComponentConstruction_of_hybridEmitterOutput
    (hhybrid :
      SelectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction) :
    SelectedProjectionFiniteDescriptionForwardHybridOutputComponentConstruction :=
  ⟨layoutCheckedParserConstruction_scaffold, hhybrid⟩

theorem selectedProjectionFiniteDescriptionForwardHybridOutputComponentConstruction_of_tailEmitterOutput
    (htail :
      SelectedProjectionPaddedTailEmitterOutputConstruction) :
    SelectedProjectionFiniteDescriptionForwardHybridOutputComponentConstruction :=
  ⟨layoutCheckedParserConstruction_scaffold,
    selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_of_tailOutput
      htail⟩

theorem selectedProjectionFiniteDescriptionForwardTailOutputComponentConstruction_of_tailEmitterOutput
    (htail :
      SelectedProjectionPaddedTailEmitterOutputConstruction) :
    SelectedProjectionFiniteDescriptionForwardTailOutputComponentConstruction :=
  ⟨layoutCheckedParserConstruction_scaffold,
    selectedProjectionCheckedEquivPaddedEmitterHybridOutputComponentConstruction_of_tailOutput
      htail⟩

theorem selectedProjectionFiniteDescriptionForwardTailOutputComponentConstruction_of_exactTailComponents
    (hcomponents :
      SelectedProjectionCheckedEquivPaddedEmitterComponentConstruction) :
    SelectedProjectionFiniteDescriptionForwardTailOutputComponentConstruction :=
  ⟨layoutCheckedParserConstruction_scaffold,
    selectedProjectionCheckedEquivPaddedEmitterHybridOutputComponentConstruction_of_exactTail
      hcomponents⟩

theorem selectedProjectionFiniteDescriptionForwardTailOutputComponentConstruction_of_tailEmitter
    (htail :
      SelectedProjectionPaddedTailEmitterConstruction) :
    SelectedProjectionFiniteDescriptionForwardTailOutputComponentConstruction :=
  selectedProjectionFiniteDescriptionForwardTailOutputComponentConstruction_of_tailEmitterOutput
    (selectedProjectionPaddedTailEmitterOutputConstruction_of_exact
      htail)

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_via_checkedEmitterOutputComponents
    (hemits :
      SelectedProjectionCheckedEquivEmitterOutputConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_checkedOutputComponents
    (selectedProjectionFiniteDescriptionForwardCheckedOutputComponentConstruction_of_checkedEmitterOutput
      hemits)

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_via_paddedEmitterOutputComponents
    (hpadded :
      SelectedProjectionCheckedEquivPaddedEmitterOutputConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_paddedOutputComponents
    (selectedProjectionFiniteDescriptionForwardPaddedOutputComponentConstruction_of_paddedEmitterOutput
      hpadded)

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_via_hybridEmitterOutputComponents
    (hhybrid :
      SelectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_hybridOutputComponents
    (selectedProjectionFiniteDescriptionForwardHybridOutputComponentConstruction_of_hybridEmitterOutput
      hhybrid)

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_via_tailEmitterOutputComponents
    (htail :
      SelectedProjectionPaddedTailEmitterOutputConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_tailOutputComponents
    (selectedProjectionFiniteDescriptionForwardTailOutputComponentConstruction_of_tailEmitterOutput
      htail)

/-! ## Compatibility with exact routes -/

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_of_checkedEquivEmitter
    (hemits :
      SelectedProjectionCheckedEquivEmitterConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_exact
    (selectedProjectionFiniteDescriptionConstruction_of_checkedEquivEmitter
      hemits)

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_of_paddedEmitter
    (hpadded :
      SelectedProjectionCheckedEquivPaddedEmitterConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_paddedEmitterOutput
    (selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_of_exact
      hpadded)

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_of_tailEmitter
    (htail :
      SelectedProjectionPaddedTailEmitterConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_tailOutput
    (selectedProjectionPaddedTailEmitterOutputConstruction_of_exact
      htail)

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_of_exactComponents_direct
    (hcomponents :
      SelectedProjectionCheckedEquivPaddedEmitterComponentConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_paddedEmitter
    (selectedProjectionCheckedEquivPaddedEmitterConstruction_of_components
      hcomponents)

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_of_hybridComponents_direct
    (hcomponents :
      SelectedProjectionCheckedEquivPaddedEmitterHybridOutputComponentConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_hybridOutput
    (selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_of_components
      hcomponents)

/-! ## Scaffold routes -/

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_scaffold_from_checkedOutput :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_checkedEmitterOutput
    selectedProjectionCheckedEquivEmitterOutputConstruction_scaffold

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_scaffold_from_paddedOutput :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_paddedEmitterOutput
    selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_scaffold

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_scaffold_from_hybridOutput :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_hybridOutput
    selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_scaffold

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_scaffold_from_tailOutput :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_tailOutput
    selectedProjectionPaddedTailEmitterOutputConstruction_scaffold

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_scaffold_from_tailExact :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_tailEmitter
    selectedProjectionPaddedTailEmitterConstruction_scaffold

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_scaffold_direct :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_tailOutputComponents
    ⟨layoutCheckedParserConstruction_scaffold,
      selectedProjectionCheckedEquivPaddedEmitterHybridOutputComponentConstruction_scaffold⟩

/-! ## Post-erase and post-padding routes -/

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_scaffold_of_postErase_direct
    (hpostEraseConstruction :
      SelectedProjectionPaddedTailCleanup.SelectedProjectionPaddedTailCleanupPostEraseConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_hybridOutput
    (selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_scaffold_of_postErase
      hpostEraseConstruction)

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_scaffold_of_postErase_checked
    (hpostEraseConstruction :
      SelectedProjectionPaddedTailCleanup.SelectedProjectionPaddedTailCleanupPostEraseConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_checkedEmitterOutput
    (selectedProjectionCheckedEquivEmitterOutputConstruction_hybrid_scaffold_of_postErase
      hpostEraseConstruction)

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_of_postPadding_direct
    (hpostPadding :
      SelectedProjectionPaddedTailCleanup.SelectedProjectionPaddedTailCleanupPostPaddingConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_hybridOutput
    (selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_of_postPadding
      hpostPadding)

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_of_postPadding_checked
    (hpostPadding :
      SelectedProjectionPaddedTailCleanup.SelectedProjectionPaddedTailCleanupPostPaddingConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_checkedEmitterOutput
    (selectedProjectionCheckedEquivEmitterOutputConstruction_hybrid_of_postPadding
      hpostPadding)

/-! ## Branch-case routes -/

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_scaffold_of_prefixAndFootprintCases_direct
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_hybridOutput
    (selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_scaffold_of_prefixAndFootprintCases
      hprefix hcases)

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_scaffold_of_prefixAndFootprintCases_checked
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_checkedEmitterOutput
    (selectedProjectionCheckedEquivEmitterOutputConstruction_hybrid_scaffold_of_prefixAndFootprintCases
      hprefix hcases)

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_scaffold_of_prefixAndFootprintBitPaddingCases_direct
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_hybridOutput
    (selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_scaffold_of_prefixAndFootprintBitPaddingCases
      hprefix hcases)

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_scaffold_of_prefixAndFootprintBitPaddingCases_checked
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_checkedEmitterOutput
    (selectedProjectionCheckedEquivEmitterOutputConstruction_hybrid_scaffold_of_prefixAndFootprintBitPaddingCases
      hprefix hcases)

theorem forwardOutputConstruction_scaffold_ofBranchFootprintCases_direct
    (heraser :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_hybridOutput
    (checkedHybridOutputConstruction_scaffold_ofBranchFootprintCases
      heraser hcases)

theorem forwardOutputConstruction_scaffold_ofBranchFootprintCases_checked
    (heraser :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_checkedEmitterOutput
    (emitterOutputConstruction_hybrid_scaffold_ofBranchFootprintCases
      heraser hcases)

/-! ## Non-scaffold branch wrappers -/

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_of_prefixAndFootprintCases_direct
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_hybridOutput
    (selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_of_prefixAndFootprintCases
      hprefix hcases)

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_of_prefixAndFootprintBitPaddingCases_direct
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_hybridOutput
    (selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_of_prefixAndFootprintBitPaddingCases
      hprefix hcases)

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases_direct
    (heraser :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_hybridOutput
    (selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
      heraser hcases)

/-! ## Checked aliases for non-scaffold branch routes -/

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_of_prefixAndFootprintCases_checked
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_checkedEmitterOutput
    (selectedProjectionCheckedEquivEmitterOutputConstruction_of_hybridOutputConstruction
      (selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_of_prefixAndFootprintCases
        hprefix hcases))

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_of_prefixAndFootprintBitPaddingCases_checked
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_checkedEmitterOutput
    (selectedProjectionCheckedEquivEmitterOutputConstruction_of_hybridOutputConstruction
      (selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_of_prefixAndFootprintBitPaddingCases
        hprefix hcases))

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases_checked
    (heraser :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_checkedEmitterOutput
    (selectedProjectionCheckedEquivEmitterOutputConstruction_of_hybridOutputConstruction
      (selectedProjectionCheckedEquivPaddedEmitterHybridOutputConstruction_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
        heraser hcases))

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
