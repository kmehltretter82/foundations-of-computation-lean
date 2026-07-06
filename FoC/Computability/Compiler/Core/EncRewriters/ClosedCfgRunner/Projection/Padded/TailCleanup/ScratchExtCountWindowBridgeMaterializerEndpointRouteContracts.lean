import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.ScratchExtCountWindowBridgeMaterializerBranchRouteContracts

set_option doc.verso true

/-!
# Count-window materializer endpoint route contracts

This module bundles the count-window structured-input materializer endpoint
facts under the exact and output route APIs.  The endpoint facts are purely
shape-level, but carrying them with route witnesses keeps downstream bridge
proofs from destructuring the large materializer route and unfolding the
count-window input layout at every accept/reject branch.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

open CanonicalLayouts.DovetailLayoutScanner
open CountWindowPostFieldDecodedPrefixStructuredMaterializerEndpoint
open CountWindowPostFieldDecodedPrefixStructuredMaterializerRouteContracts
open CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts
open CountWindowPostFieldDecodedPrefixStructuredMaterializerBranchRouteContracts

namespace CountWindowPostFieldDecodedPrefixStructuredMaterializerEndpointRouteContracts

/-!
## Per-input endpoint shape
-/

structure EndpointShape
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : Prop where
  bitsEq :
    bits useAccept input = ParsedLayoutBits input.L
  suffixTailEq :
    suffixTail useAccept input =
      countWindowPostFieldDecodedPrefixStructuredSuffixTail
        useAccept input.L
  sourcePaddingEq :
    sourcePadding useAccept input =
      countWindowPostFieldDecodedPrefixStructuredSourcePadding
        useAccept input.L input.deletedTail
  outputPaddingEq :
    outputPadding useAccept input =
      postFieldDecodedPrefixScanPadding useAccept input.L
  inputSourceEq :
    inputSource useAccept input =
      countWindowPostFieldDecodedPrefixStructuredInputMaterializerSource
        useAccept input
  boolWordSourceEq :
    boolWordSource useAccept input =
      countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
        useAccept input
  outputTapeEq :
    outputTape useAccept input =
      countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputTape
        useAccept input
  encodedInputTapeEq :
    encodedInputTape useAccept input =
      countWindowPostFieldDecodedPrefixStructuredEncodedInputTape
        useAccept input.L input.pref input.leftBit input.deletedTail
  inputSourceEqBoolWord :
    inputSource useAccept input = boolWordSource useAccept input
  boolWordSourceEqIndexed :
    boolWordSource useAccept input =
      BoolWordRawBitsDecoderInputMaterializerEndpoint.indexedSource
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
          useAccept)
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail
          useAccept)
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding
          useAccept)
        input
  outputTapeEqIndexed :
    outputTape useAccept input =
      BoolWordRawBitsDecoderInputMaterializerEndpoint.indexedOutput
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
          useAccept)
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordOutputPadding
          useAccept)
        input
  inputTargetEqMaterializerTarget :
    inputTarget useAccept input =
      structured3InputMaterializerTargetTape
        (inputSource useAccept input)
        (outputTape useAccept input)
  inputTargetEqEncodedInput :
    inputTarget useAccept input = encodedInputTape useAccept input
  boolWordTargetEqIndexed :
    boolWordTarget useAccept input =
      BoolWordRawBitsDecoderInputMaterializerEndpoint.indexedTarget
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
          useAccept)
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail
          useAccept)
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding
          useAccept)
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordOutputPadding
          useAccept)
        input
  boolWordTargetEqInput :
    boolWordTarget useAccept input = inputTarget useAccept input
  boolWordTargetEqEncodedInput :
    boolWordTarget useAccept input = encodedInputTape useAccept input
  boolWordSourceCells :
    Tape.cells (boolWordSource useAccept input) =
      none ::
        List.append
          ((List.append boolWordRawBitsDecoderHeaderBits
            (List.append
              (boolWordRawBitsDecoderEncodedFieldBits
                (bits useAccept input))
              (false :: suffixTail useAccept input))).map some)
          (none :: sourcePadding useAccept input)
  inputSourceCells :
    Tape.cells (inputSource useAccept input) =
      none ::
        List.append
          ((List.append boolWordRawBitsDecoderHeaderBits
            (List.append
              (boolWordRawBitsDecoderEncodedFieldBits
                (bits useAccept input))
              (false :: suffixTail useAccept input))).map some)
          (none :: sourcePadding useAccept input)
  outputTapeCells :
    Tape.cells (outputTape useAccept input) =
      none ::
        List.append
          (List.replicate ((bits useAccept input).length + 1)
            (none : Option Bool))
          (outputPadding useAccept input)
  inputTargetRead :
    Tape.read (inputTarget useAccept input) = none
  boolWordTargetRead :
    Tape.read (boolWordTarget useAccept input) = none
  encodedInputTapeRead :
    Tape.read (encodedInputTape useAccept input) = none
  inputTargetCells :
    Tape.cells (inputTarget useAccept input) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode
            (guardLogicalTape (inputSource useAccept input)))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode
                (guardLogicalTape Tape.blank))
              (List.append tapeSeparatorCells
                (List.append (logicalTapeCode
                    (guardLogicalTape (outputTape useAccept input)))
                  tapeSeparatorCells)))))
  boolWordTargetCells :
    Tape.cells (boolWordTarget useAccept input) =
      Tape.cells (inputTarget useAccept input)
  encodedInputTapeCells :
    Tape.cells (encodedInputTape useAccept input) =
      Tape.cells (inputTarget useAccept input)
  inputTargetNormalizedOutput :
    Tape.normalizedOutput (inputTarget useAccept input) =
      List.append
        (logicalTapeBits (guardedInputSourceTape useAccept input))
        (List.append
          (logicalTapeBits guardedScratchTape)
          (logicalTapeBits (guardedOutputTape useAccept input)))
  boolWordTargetNormalizedOutput :
    Tape.normalizedOutput (boolWordTarget useAccept input) =
      Tape.normalizedOutput (inputTarget useAccept input)
  encodedInputTapeNormalizedOutput :
    Tape.normalizedOutput (encodedInputTape useAccept input) =
      Tape.normalizedOutput (inputTarget useAccept input)
  logicalTapesEq :
    logicalTapes useAccept input =
      [inputSource useAccept input, Tape.blank, outputTape useAccept input]
  guardedLogicalTapesEq :
    guardedLogicalTapes useAccept input =
      [guardedInputSourceTape useAccept input,
        guardedScratchTape,
        guardedOutputTape useAccept input]
  guardedInputSourceEquiv :
    Tape.Equiv
      (guardedInputSourceTape useAccept input)
      (inputSource useAccept input)
  guardedBoolWordSourceEquiv :
    Tape.Equiv
      (guardedBoolWordSourceTape useAccept input)
      (boolWordSource useAccept input)
  guardedOutputEquiv :
    Tape.Equiv
      (guardedOutputTape useAccept input)
      (outputTape useAccept input)
  guardedScratchEquiv :
    Tape.Equiv guardedScratchTape Tape.blank
  guardedLogicalTapesHaveGuardCells :
    LogicalTapesHaveGuardCells (guardedLogicalTapes useAccept input)
  inputTargetStructuredEncoded :
    StructuredEncodedTapes
      (guardedLogicalTapes useAccept input)
      (inputTarget useAccept input)
  inputTargetStructuredGuardedEncoded :
    StructuredGuardedEncodedTapes
      (logicalTapes useAccept input)
      (inputTarget useAccept input)
  inputTargetStructuredLogicalEquivEncoded :
    StructuredLogicalEquivEncodedTapes
      (logicalTapes useAccept input)
      (inputTarget useAccept input)
  atSeparator0 :
    AtTapeSeparator
      (guardedLogicalTapes useAccept input) 0
      (inputTarget useAccept input)
  atSeparator1 :
    AtTapeSeparator
      (guardedLogicalTapes useAccept input) 1
      (separator1Tape useAccept input)
  atSeparator2 :
    AtTapeSeparator
      (guardedLogicalTapes useAccept input) 2
      (separator2Tape useAccept input)
  atExistingSeparator0 :
    AtExistingTapeSeparator
      (guardedLogicalTapes useAccept input) 0
      (inputTarget useAccept input)
  atExistingSeparator1 :
    AtExistingTapeSeparator
      (guardedLogicalTapes useAccept input) 1
      (separator1Tape useAccept input)
  atExistingSeparator2 :
    AtExistingTapeSeparator
      (guardedLogicalTapes useAccept input) 2
      (separator2Tape useAccept input)
  atHeadMarker0 :
    AtTapeHeadMarker
      (guardedLogicalTapes useAccept input) 0
      (headMarker0Tape useAccept input)
  atHeadMarker1 :
    AtTapeHeadMarker
      (guardedLogicalTapes useAccept input) 1
      (headMarker1Tape useAccept input)
  atHeadMarker2 :
    AtTapeHeadMarker
      (guardedLogicalTapes useAccept input) 2
      (headMarker2Tape useAccept input)
  atHeadCell0 :
    AtTapeHeadCellCode
      (guardedLogicalTapes useAccept input) 0
      (headCell0Tape useAccept input)
  atHeadCell1 :
    AtTapeHeadCellCode
      (guardedLogicalTapes useAccept input) 1
      (headCell1Tape useAccept input)
  atHeadCell2 :
    AtTapeHeadCellCode
      (guardedLogicalTapes useAccept input) 2
      (headCell2Tape useAccept input)
  atSegmentEnd0 :
    AtTapeSegmentEnd
      (guardedLogicalTapes useAccept input) 0
      (segmentEnd0Tape useAccept input)
  atSegmentEnd1 :
    AtTapeSegmentEnd
      (guardedLogicalTapes useAccept input) 1
      (segmentEnd1Tape useAccept input)
  atSegmentEnd2 :
    AtTapeSegmentEnd
      (guardedLogicalTapes useAccept input) 2
      (segmentEnd2Tape useAccept input)

theorem endpointShape
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    EndpointShape useAccept input :=
  { bitsEq := bits_eq useAccept input
    suffixTailEq := suffixTail_eq useAccept input
    sourcePaddingEq := sourcePadding_eq useAccept input
    outputPaddingEq := outputPadding_eq useAccept input
    inputSourceEq := inputSource_eq useAccept input
    boolWordSourceEq := boolWordSource_eq useAccept input
    outputTapeEq := outputTape_eq useAccept input
    encodedInputTapeEq := encodedInputTape_eq useAccept input
    inputSourceEqBoolWord := inputSource_eq_boolWordSource useAccept input
    boolWordSourceEqIndexed := boolWordSource_eq_indexedSource useAccept input
    outputTapeEqIndexed := outputTape_eq_indexedOutput useAccept input
    inputTargetEqMaterializerTarget :=
      inputTarget_eq_materializerTargetTape useAccept input
    inputTargetEqEncodedInput :=
      inputTarget_eq_encodedInputTape useAccept input
    boolWordTargetEqIndexed := boolWordTarget_eq_indexedTarget useAccept input
    boolWordTargetEqInput := boolWordTarget_eq_inputTarget useAccept input
    boolWordTargetEqEncodedInput :=
      boolWordTarget_eq_encodedInputTape useAccept input
    boolWordSourceCells := boolWordSource_cells useAccept input
    inputSourceCells := inputSource_cells useAccept input
    outputTapeCells := outputTape_cells useAccept input
    inputTargetRead := inputTarget_read useAccept input
    boolWordTargetRead := boolWordTarget_read useAccept input
    encodedInputTapeRead := encodedInputTape_read useAccept input
    inputTargetCells := inputTarget_cells useAccept input
    boolWordTargetCells := boolWordTarget_cells useAccept input
    encodedInputTapeCells := encodedInputTape_cells useAccept input
    inputTargetNormalizedOutput :=
      inputTarget_normalizedOutput_eq_guardedLogicalBits useAccept input
    boolWordTargetNormalizedOutput :=
      boolWordTarget_normalizedOutput_eq_inputTarget useAccept input
    encodedInputTapeNormalizedOutput :=
      encodedInputTape_normalizedOutput_eq_inputTarget useAccept input
    logicalTapesEq := logicalTapes_eq useAccept input
    guardedLogicalTapesEq := guardedLogicalTapes_eq useAccept input
    guardedInputSourceEquiv := guardedInputSourceTape_equiv useAccept input
    guardedBoolWordSourceEquiv :=
      guardedBoolWordSourceTape_equiv useAccept input
    guardedOutputEquiv := guardedOutputTape_equiv useAccept input
    guardedScratchEquiv := guardedScratchTape_equiv
    guardedLogicalTapesHaveGuardCells :=
      guardedLogicalTapes_haveGuardCells useAccept input
    inputTargetStructuredEncoded :=
      inputTarget_structuredEncodedTapes useAccept input
    inputTargetStructuredGuardedEncoded :=
      inputTarget_structuredGuardedEncodedTapes useAccept input
    inputTargetStructuredLogicalEquivEncoded :=
      inputTarget_structuredLogicalEquivEncodedTapes useAccept input
    atSeparator0 := atSeparator0 useAccept input
    atSeparator1 := atSeparator1 useAccept input
    atSeparator2 := atSeparator2 useAccept input
    atExistingSeparator0 := atExistingSeparator0 useAccept input
    atExistingSeparator1 := atExistingSeparator1 useAccept input
    atExistingSeparator2 := atExistingSeparator2 useAccept input
    atHeadMarker0 := atHeadMarker0 useAccept input
    atHeadMarker1 := atHeadMarker1 useAccept input
    atHeadMarker2 := atHeadMarker2 useAccept input
    atHeadCell0 := atHeadCell0 useAccept input
    atHeadCell1 := atHeadCell1 useAccept input
    atHeadCell2 := atHeadCell2 useAccept input
    atSegmentEnd0 := atSegmentEnd0 useAccept input
    atSegmentEnd1 := atSegmentEnd1 useAccept input
    atSegmentEnd2 := atSegmentEnd2 useAccept input }

/-!
## Route-level endpoint packages
-/

structure ExactEndpointRouteSpec
    (useAccept : Bool) (materializer : MachineDescription) : Prop where
  route : ExactRouteSpec useAccept materializer
  endpoint :
    forall input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept,
      EndpointShape useAccept input

def ExactEndpointRouteConstruction : Prop :=
  forall useAccept : Bool,
    exists materializer : MachineDescription,
      ExactEndpointRouteSpec useAccept materializer

theorem exactEndpointRouteSpec_of_exactRouteSpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hroute : ExactRouteSpec useAccept materializer) :
    ExactEndpointRouteSpec useAccept materializer :=
  { route := hroute
    endpoint := fun input => endpointShape useAccept input }

theorem exactRouteSpec_of_exactEndpointRouteSpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hroute : ExactEndpointRouteSpec useAccept materializer) :
    ExactRouteSpec useAccept materializer :=
  hroute.route

theorem exactEndpointRouteConstruction_of_exactRouteConstruction
    (hroute : ExactRouteConstruction) :
    ExactEndpointRouteConstruction := by
  intro useAccept
  rcases hroute useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      exactEndpointRouteSpec_of_exactRouteSpec hspec⟩

theorem exactRouteConstruction_of_exactEndpointRouteConstruction
    (hroute : ExactEndpointRouteConstruction) :
    ExactRouteConstruction := by
  intro useAccept
  rcases hroute useAccept with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.route⟩

theorem exactEndpointRouteConstruction_iff_exactRouteConstruction :
    ExactEndpointRouteConstruction ↔ ExactRouteConstruction := by
  constructor
  · exact exactRouteConstruction_of_exactEndpointRouteConstruction
  · exact exactEndpointRouteConstruction_of_exactRouteConstruction

theorem exactEndpointRouteConstruction_core :
    ExactEndpointRouteConstruction :=
  exactEndpointRouteConstruction_of_exactRouteConstruction
    exactRouteConstruction_core

structure OutputEndpointRouteSpec
    (useAccept : Bool) (materializer : MachineDescription) : Prop where
  route : OutputRouteSpec useAccept materializer
  endpoint :
    forall input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept,
      EndpointShape useAccept input

def OutputEndpointRouteConstruction : Prop :=
  forall useAccept : Bool,
    exists materializer : MachineDescription,
      OutputEndpointRouteSpec useAccept materializer

theorem outputEndpointRouteSpec_of_outputRouteSpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hroute : OutputRouteSpec useAccept materializer) :
    OutputEndpointRouteSpec useAccept materializer :=
  { route := hroute
    endpoint := fun input => endpointShape useAccept input }

theorem outputRouteSpec_of_outputEndpointRouteSpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hroute : OutputEndpointRouteSpec useAccept materializer) :
    OutputRouteSpec useAccept materializer :=
  hroute.route

theorem outputEndpointRouteConstruction_of_outputRouteConstruction
    (hroute : OutputRouteConstruction) :
    OutputEndpointRouteConstruction := by
  intro useAccept
  rcases hroute useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      outputEndpointRouteSpec_of_outputRouteSpec hspec⟩

theorem outputRouteConstruction_of_outputEndpointRouteConstruction
    (hroute : OutputEndpointRouteConstruction) :
    OutputRouteConstruction := by
  intro useAccept
  rcases hroute useAccept with ⟨materializer, hspec⟩
  exact ⟨materializer, hspec.route⟩

theorem outputEndpointRouteConstruction_iff_outputRouteConstruction :
    OutputEndpointRouteConstruction ↔ OutputRouteConstruction := by
  constructor
  · exact outputRouteConstruction_of_outputEndpointRouteConstruction
  · exact outputEndpointRouteConstruction_of_outputRouteConstruction

theorem outputEndpointRouteSpec_of_exactEndpointRouteSpec
    {useAccept : Bool} {materializer : MachineDescription}
    (hroute : ExactEndpointRouteSpec useAccept materializer) :
    OutputEndpointRouteSpec useAccept materializer :=
  { route := outputRouteSpec_of_exactRouteSpec hroute.route
    endpoint := hroute.endpoint }

theorem outputEndpointRouteConstruction_of_exactEndpointRouteConstruction
    (hroute : ExactEndpointRouteConstruction) :
    OutputEndpointRouteConstruction := by
  intro useAccept
  rcases hroute useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      outputEndpointRouteSpec_of_exactEndpointRouteSpec hspec⟩

theorem outputEndpointRouteConstruction_of_exactRouteConstruction
    (hroute : ExactRouteConstruction) :
    OutputEndpointRouteConstruction :=
  outputEndpointRouteConstruction_of_exactEndpointRouteConstruction
    (exactEndpointRouteConstruction_of_exactRouteConstruction hroute)

theorem outputEndpointRouteConstruction_core :
    OutputEndpointRouteConstruction :=
  outputEndpointRouteConstruction_of_exactRouteConstruction
    exactRouteConstruction_core

/-!
## Branch and pair wrappers
-/

def AcceptExactEndpointRouteSpec
    (materializer : MachineDescription) : Prop :=
  ExactEndpointRouteSpec true materializer

def RejectExactEndpointRouteSpec
    (materializer : MachineDescription) : Prop :=
  ExactEndpointRouteSpec false materializer

def AcceptExactEndpointRouteConstruction : Prop :=
  exists materializer : MachineDescription,
    AcceptExactEndpointRouteSpec materializer

def RejectExactEndpointRouteConstruction : Prop :=
  exists materializer : MachineDescription,
    RejectExactEndpointRouteSpec materializer

def ExactEndpointRouteBranchConstruction : Prop :=
  AcceptExactEndpointRouteConstruction ∧
    RejectExactEndpointRouteConstruction

theorem exactEndpointRouteBranchConstruction_of_construction
    (hroute : ExactEndpointRouteConstruction) :
    ExactEndpointRouteBranchConstruction :=
  ⟨hroute true, hroute false⟩

theorem exactEndpointRouteConstruction_of_branchConstruction
    (hroute : ExactEndpointRouteBranchConstruction) :
    ExactEndpointRouteConstruction := by
  intro useAccept
  cases useAccept
  · exact hroute.right
  · exact hroute.left

theorem exactEndpointRouteConstruction_iff_branchConstruction :
    ExactEndpointRouteConstruction ↔
      ExactEndpointRouteBranchConstruction := by
  constructor
  · exact exactEndpointRouteBranchConstruction_of_construction
  · exact exactEndpointRouteConstruction_of_branchConstruction

theorem exactEndpointRouteBranchConstruction_core :
    ExactEndpointRouteBranchConstruction :=
  exactEndpointRouteBranchConstruction_of_construction
    exactEndpointRouteConstruction_core

def AcceptOutputEndpointRouteSpec
    (materializer : MachineDescription) : Prop :=
  OutputEndpointRouteSpec true materializer

def RejectOutputEndpointRouteSpec
    (materializer : MachineDescription) : Prop :=
  OutputEndpointRouteSpec false materializer

def OutputEndpointRouteBranchConstruction : Prop :=
  (exists materializer : MachineDescription,
    AcceptOutputEndpointRouteSpec materializer) ∧
  (exists materializer : MachineDescription,
    RejectOutputEndpointRouteSpec materializer)

theorem outputEndpointRouteBranchConstruction_of_construction
    (hroute : OutputEndpointRouteConstruction) :
    OutputEndpointRouteBranchConstruction :=
  ⟨hroute true, hroute false⟩

theorem outputEndpointRouteConstruction_of_branchConstruction
    (hroute : OutputEndpointRouteBranchConstruction) :
    OutputEndpointRouteConstruction := by
  intro useAccept
  cases useAccept
  · exact hroute.right
  · exact hroute.left

theorem outputEndpointRouteBranchConstruction_of_exactBranchConstruction
    (hroute : ExactEndpointRouteBranchConstruction) :
    OutputEndpointRouteBranchConstruction := by
  constructor
  · rcases hroute.left with ⟨materializer, hspec⟩
    exact
      ⟨materializer,
        outputEndpointRouteSpec_of_exactEndpointRouteSpec hspec⟩
  · rcases hroute.right with ⟨materializer, hspec⟩
    exact
      ⟨materializer,
        outputEndpointRouteSpec_of_exactEndpointRouteSpec hspec⟩

structure ExactEndpointRoutePairSpec
    (acceptMaterializer rejectMaterializer : MachineDescription) : Prop where
  accept : AcceptExactEndpointRouteSpec acceptMaterializer
  reject : RejectExactEndpointRouteSpec rejectMaterializer

def ExactEndpointRoutePairConstruction : Prop :=
  exists acceptMaterializer : MachineDescription,
    exists rejectMaterializer : MachineDescription,
      ExactEndpointRoutePairSpec acceptMaterializer rejectMaterializer

theorem exactEndpointRoutePairConstruction_of_branchConstruction
    (hroute : ExactEndpointRouteBranchConstruction) :
    ExactEndpointRoutePairConstruction := by
  rcases hroute.left with ⟨acceptMaterializer, haccept⟩
  rcases hroute.right with ⟨rejectMaterializer, hreject⟩
  exact
    ⟨acceptMaterializer, rejectMaterializer,
      { accept := haccept, reject := hreject }⟩

theorem exactEndpointRouteBranchConstruction_of_pairConstruction
    (hroute : ExactEndpointRoutePairConstruction) :
    ExactEndpointRouteBranchConstruction := by
  rcases hroute with
    ⟨acceptMaterializer, rejectMaterializer, hspec⟩
  exact
    ⟨⟨acceptMaterializer, hspec.accept⟩,
      ⟨rejectMaterializer, hspec.reject⟩⟩

theorem exactEndpointRoutePairConstruction_core :
    ExactEndpointRoutePairConstruction :=
  exactEndpointRoutePairConstruction_of_branchConstruction
    exactEndpointRouteBranchConstruction_core

/-!
## Endpoint field projections
-/

theorem endpointShape_of_exactRouteConstruction
    (hroute : ExactEndpointRouteConstruction)
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    EndpointShape useAccept input := by
  rcases hroute useAccept with ⟨_materializer, hspec⟩
  exact hspec.endpoint input

theorem endpointShape_of_outputRouteConstruction
    (hroute : OutputEndpointRouteConstruction)
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    EndpointShape useAccept input := by
  rcases hroute useAccept with ⟨_materializer, hspec⟩
  exact hspec.endpoint input

theorem endpointShape_core
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    EndpointShape useAccept input :=
  endpointShape_of_exactRouteConstruction
    exactEndpointRouteConstruction_core useAccept input

theorem inputTarget_read_core
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    Tape.read (inputTarget useAccept input) = none :=
  (endpointShape_core useAccept input).inputTargetRead

theorem encodedInputTape_read_core
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    Tape.read (encodedInputTape useAccept input) = none :=
  (endpointShape_core useAccept input).encodedInputTapeRead

theorem inputTarget_structuredLogicalEquivEncodedTapes_core
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    StructuredLogicalEquivEncodedTapes
      (logicalTapes useAccept input)
      (inputTarget useAccept input) :=
  (endpointShape_core useAccept input).inputTargetStructuredLogicalEquivEncoded

theorem atSeparator0_core
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    AtTapeSeparator
      (guardedLogicalTapes useAccept input) 0
      (inputTarget useAccept input) :=
  (endpointShape_core useAccept input).atSeparator0

theorem atSeparator2_core
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    AtTapeSeparator
      (guardedLogicalTapes useAccept input) 2
      (separator2Tape useAccept input) :=
  (endpointShape_core useAccept input).atSeparator2

theorem atSegmentEnd2_core
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    AtTapeSegmentEnd
      (guardedLogicalTapes useAccept input) 2
      (segmentEnd2Tape useAccept input) :=
  (endpointShape_core useAccept input).atSegmentEnd2

end CountWindowPostFieldDecodedPrefixStructuredMaterializerEndpointRouteContracts

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters
end Computability
end FoC
