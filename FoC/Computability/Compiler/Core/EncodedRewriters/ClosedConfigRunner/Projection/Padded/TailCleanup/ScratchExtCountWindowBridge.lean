import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.BoolWordRawBitsDecoder
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.ScratchExtCountWindowConstructions

set_option doc.verso true

/-!
# Structured count-window bridge

This module records the lowered three-tape route for the count-window
decoded-prefix materializer.  The existing one-tape materializer contract
remains in
{module}`FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.ScratchExtCountWindowConstructions`;
the bridge isolates the shared decoded-prefix extraction and the remaining
adapter obligation from the structured three-tape layout back to that one-tape
contract.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncodedRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

open CanonicalLayouts.DovetailLayoutScanner

theorem selectedProjectionPaddedTailCleanupPrefixBits_eq_rawBitsDecoderPrefix
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupPrefixBits L =
      List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.header)
        (List.append
          (boolWordRawBitsDecoderEncodedFieldBits (ParsedLayoutBits L))
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage)) := by
  rw [selectedProjectionPaddedTailCleanupPrefixBits,
    SelectedProjectionTailProjector.outputPrefixBits]
  rw [boolWordBits_eq_encodeBoolWordAppend]
  simp [boolWordRawBitsDecoderEncodedFieldBits, encodeCodeWordAsInput,
    List.append_assoc]

def countWindowPostFieldDecodedPrefixStructuredSuffixTail
    (useAccept : Bool) (L : DovetailLayout) : Word Bool :=
  List.append
    (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
      L.stage).tail
    (countWindowPostFieldDecodedPrefixMaterializerPayload useAccept L)

def countWindowPostFieldDecodedPrefixStructuredSourcePadding
    (useAccept : Bool) (L : DovetailLayout)
    (deletedTail : Word Bool) : List (Option Bool) :=
  if useAccept then
    none ::
      none ::
      leadingBlankLeftShiftTargetVisiblePadding
        (postFieldHandoffAfterSentinelGapPadding
          deletedTail [none, none, none, none, none])
  else
    rejectPostFieldHandoffRewindPadding L deletedTail

def structuredCountWindowPostFieldDecodedPrefixOutputTape
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  postFieldDecodedPrefixScanSourceTape useAccept L

theorem countWindowPostFieldDecodedPrefixMaterializerSourceTape_eq_boolWordSource
    (useAccept : Bool) (L : DovetailLayout) (pref : Word Bool)
    (leftBit : Bool) (deletedTail : Word Bool)
    (hpayload :
      countWindowPostFieldDecodedPrefixMaterializerPayload useAccept L =
        List.append pref [leftBit]) :
    countWindowPostFieldDecodedPrefixMaterializerSourceTape
        useAccept L pref leftBit deletedTail =
      boolWordRawBitsDecoderSourceTape
        (ParsedLayoutBits L)
        (countWindowPostFieldDecodedPrefixStructuredSuffixTail
          useAccept L)
        (countWindowPostFieldDecodedPrefixStructuredSourcePadding
          useAccept L deletedTail) := by
  rcases
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_false_false_tail
        L.stage with
    ⟨stageTail, hstage⟩
  cases useAccept
  · have hpayloadReject :
        selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayload
            L =
          List.append pref [leftBit] := by
      simpa [countWindowPostFieldDecodedPrefixMaterializerPayload] using
        hpayload
    simp [countWindowPostFieldDecodedPrefixMaterializerSourceTape,
      countWindowPostFieldDecodedPrefixMaterializerPayload,
      countWindowPostFieldDecodedPrefixStructuredSuffixTail,
      countWindowPostFieldDecodedPrefixStructuredSourcePadding,
      rejectPostFieldDecodedPrefixRestorerSourceTape,
      rejectPostFieldHandoffRewoundTape,
      rejectPostFieldHandoffRewindBits,
      boolWordRawBitsDecoderSourceTape,
      boolWordRawBitsDecoderHeaderBits,
      selectedProjectionPaddedTailCleanupPrefixBits_eq_rawBitsDecoderPrefix,
      hpayloadReject, hstage, rightEdgeRewindTargetTape,
      rightEdgeRewindTargetTapeWithBase, List.map_append,
      List.append_assoc]
  · have hpayloadAccept :
        selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload
            L =
          List.append pref [leftBit] := by
      simpa [countWindowPostFieldDecodedPrefixMaterializerPayload] using
        hpayload
    simp [countWindowPostFieldDecodedPrefixMaterializerSourceTape,
      countWindowPostFieldDecodedPrefixMaterializerPayload,
      countWindowPostFieldDecodedPrefixStructuredSuffixTail,
      countWindowPostFieldDecodedPrefixStructuredSourcePadding,
      acceptPostFieldHandoffAfterRightEdgeRewindTape,
      boolWordRawBitsDecoderSourceTape,
      boolWordRawBitsDecoderHeaderBits,
      selectedProjectionPaddedTailCleanupPrefixBits_eq_rawBitsDecoderPrefix,
      hpayloadAccept, hstage, rightEdgeRewindTargetTape,
      List.map_append, List.append_assoc]

theorem structuredCountWindowPostFieldDecodedPrefixExtractor_run
    (useAccept : Bool) (L : DovetailLayout) (pref : Word Bool)
    (leftBit : Bool) (deletedTail : Word Bool)
    (hpayload :
      countWindowPostFieldDecodedPrefixMaterializerPayload useAccept L =
        List.append pref [leftBit]) :
    structuredBoolWordRawBitsDecoderDescription.runConfig
        (9 * (ParsedLayoutBits L).length + 11)
        { state := structuredBoolWordRawBitsDecoderDescription.start
          tapes :=
            [ countWindowPostFieldDecodedPrefixMaterializerSourceTape
                useAccept L pref leftBit deletedTail
            , Tape.blank
            , structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
                (ParsedLayoutBits L).length
                (postFieldDecodedPrefixScanPadding useAccept L) ] } =
      { state := structuredBoolWordRawBitsDecoderDescription.halt
        tapes :=
          [ structuredBoolWordRawBitsDecoderSourceTargetTape
              (ParsedLayoutBits L)
              (countWindowPostFieldDecodedPrefixStructuredSuffixTail
                useAccept L)
              (countWindowPostFieldDecodedPrefixStructuredSourcePadding
                useAccept L deletedTail)
          , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
              ((ParsedLayoutBits L).length + 1)
          , structuredCountWindowPostFieldDecodedPrefixOutputTape
              useAccept L ] } := by
  rw [
    countWindowPostFieldDecodedPrefixMaterializerSourceTape_eq_boolWordSource
      useAccept L pref leftBit deletedTail hpayload]
  simpa [structuredCountWindowPostFieldDecodedPrefixOutputTape] using
    structuredBoolWordRawBitsDecoderDescription_run_withOutputPadding
      (ParsedLayoutBits L)
      (countWindowPostFieldDecodedPrefixStructuredSuffixTail useAccept L)
      (countWindowPostFieldDecodedPrefixStructuredSourcePadding
        useAccept L deletedTail)
      (postFieldDecodedPrefixScanPadding useAccept L)

theorem structuredRejectPostFieldDecodedPrefixExtractor_run
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool)
    (hpayload :
      selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayload
          L =
        List.append pref [leftBit]) :
    structuredBoolWordRawBitsDecoderDescription.runConfig
        (9 * (ParsedLayoutBits L).length + 11)
        { state := structuredBoolWordRawBitsDecoderDescription.start
          tapes :=
            [ rejectPostFieldDecodedPrefixRestorerSourceTape
                L pref leftBit deletedTail
            , Tape.blank
            , structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
                (ParsedLayoutBits L).length
                (postFieldDecodedPrefixScanPadding false L) ] } =
      { state := structuredBoolWordRawBitsDecoderDescription.halt
        tapes :=
          [ structuredBoolWordRawBitsDecoderSourceTargetTape
              (ParsedLayoutBits L)
              (countWindowPostFieldDecodedPrefixStructuredSuffixTail
                false L)
              (countWindowPostFieldDecodedPrefixStructuredSourcePadding
                false L deletedTail)
          , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
              ((ParsedLayoutBits L).length + 1)
          , structuredCountWindowPostFieldDecodedPrefixOutputTape
              false L ] } := by
  simpa [countWindowPostFieldDecodedPrefixMaterializerPayload_false,
    countWindowPostFieldDecodedPrefixMaterializerSourceTape_false] using
    structuredCountWindowPostFieldDecodedPrefixExtractor_run
      false L pref leftBit deletedTail
      (by
        simpa [countWindowPostFieldDecodedPrefixMaterializerPayload] using
          hpayload)

theorem structuredAcceptPostFieldDecodedPrefixExtractor_run
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool)
    (hpayload :
      selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload
          L =
        List.append pref [leftBit]) :
    structuredBoolWordRawBitsDecoderDescription.runConfig
        (9 * (ParsedLayoutBits L).length + 11)
        { state := structuredBoolWordRawBitsDecoderDescription.start
          tapes :=
            [ acceptPostFieldHandoffAfterRightEdgeRewindTape
                L pref leftBit deletedTail
            , Tape.blank
            , structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
                (ParsedLayoutBits L).length
                (postFieldDecodedPrefixScanPadding true L) ] } =
      { state := structuredBoolWordRawBitsDecoderDescription.halt
        tapes :=
          [ structuredBoolWordRawBitsDecoderSourceTargetTape
              (ParsedLayoutBits L)
              (countWindowPostFieldDecodedPrefixStructuredSuffixTail
                true L)
              (countWindowPostFieldDecodedPrefixStructuredSourcePadding
                true L deletedTail)
          , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
              ((ParsedLayoutBits L).length + 1)
          , structuredCountWindowPostFieldDecodedPrefixOutputTape
              true L ] } := by
  simpa [countWindowPostFieldDecodedPrefixMaterializerPayload_true,
    countWindowPostFieldDecodedPrefixMaterializerSourceTape_true] using
    structuredCountWindowPostFieldDecodedPrefixExtractor_run
      true L pref leftBit deletedTail
      (by
        simpa [countWindowPostFieldDecodedPrefixMaterializerPayload] using
          hpayload)

def LoweredStructuredCountWindowPostFieldDecodedPrefixExtractorSpec
    (extractor : MachineDescription) : Prop :=
  extractor.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout) (pref : Word Bool)
      (leftBit : Bool) (deletedTail : Word Bool),
      configurationFieldBits L.acceptConfig [] = false :: deletedTail ->
      countWindowPostFieldDecodedPrefixMaterializerPayload useAccept L =
          List.append pref [leftBit] ->
      extractor.HaltsFromTapeEquiv
        (Structured.MultiTapeLowering.encodedGuardedStructuredTapes
          [ countWindowPostFieldDecodedPrefixMaterializerSourceTape
              useAccept L pref leftBit deletedTail
          , Tape.blank
          , structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
              (ParsedLayoutBits L).length
              (postFieldDecodedPrefixScanPadding useAccept L) ])
        (Structured.MultiTapeLowering.encodedGuardedStructuredTapes
          [ structuredBoolWordRawBitsDecoderSourceTargetTape
              (ParsedLayoutBits L)
              (countWindowPostFieldDecodedPrefixStructuredSuffixTail
                useAccept L)
              (countWindowPostFieldDecodedPrefixStructuredSourcePadding
                useAccept L deletedTail)
          , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
              ((ParsedLayoutBits L).length + 1)
          , postFieldDecodedPrefixScanSourceTape useAccept L ])

def LoweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction :
    Prop :=
  exists extractor : MachineDescription,
    LoweredStructuredCountWindowPostFieldDecodedPrefixExtractorSpec extractor

theorem loweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction_core :
    LoweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction := by
  refine
    ⟨loweredStructuredBoolWordRawBitsDecoderDescription,
      loweredStructuredBoolWordRawBitsDecoderDescription_subroutineReady,
      ?_⟩
  intro useAccept L pref leftBit deletedTail _hdeleted hpayload
  rw [
    countWindowPostFieldDecodedPrefixMaterializerSourceTape_eq_boolWordSource
      useAccept L pref leftBit deletedTail hpayload]
  simpa [postFieldDecodedPrefixScanSourceTape] using
    loweredStructuredBoolWordRawBitsDecoderDescription_haltsFromTapeWithOutputPadding
      (ParsedLayoutBits L)
      (countWindowPostFieldDecodedPrefixStructuredSuffixTail useAccept L)
      (countWindowPostFieldDecodedPrefixStructuredSourcePadding
        useAccept L deletedTail)
      (postFieldDecodedPrefixScanPadding useAccept L)

theorem countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_of_loweredStructuredExtractor
    (_hextractor :
      LoweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction) :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction := by
  sorry

theorem countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_bridgeCore :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction :=
  countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_of_loweredStructuredExtractor
    loweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction_core

theorem selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction_bridgeCore :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction := by
  let hmaterializer :
      CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction :=
    countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_bridgeCore
  let hrejectScan :
      RejectPostFieldDecodedPrefixScanSourceConstruction :=
    rejectPostFieldDecodedPrefixScanSourceConstruction_of_countWindowMaterializer
      hmaterializer
  let hrejectRestorer :
      RejectPostFieldDecodedPrefixRestorerConstruction :=
    rejectPostFieldDecodedPrefixRestorerConstruction_of_scanSource
      hrejectScan
  let hrejectRemaining :
      RejectPostFieldRemainingGapsConstruction :=
    rejectPostFieldRemainingGapsConstruction_of_rewinderAndRestorer
      rejectPostFieldHandoffRightEdgeRewinderConstruction_core
      hrejectRestorer
  let hacceptScan :
      AcceptPostFieldRewoundToDecodedPrefixScanSourceConstruction :=
    acceptPostFieldRewoundToDecodedPrefixScanSourceConstruction_of_countWindowMaterializer
      hmaterializer
  let hacceptRewound :
      AcceptPostFieldRewoundToDecodedPrefixConstruction :=
    acceptPostFieldRewoundToDecodedPrefixConstruction_of_scanSource
      hacceptScan
      acceptPostFieldDecodedPrefixScanToRewindConstruction_core
  let hacceptReposition :
      AcceptPostFieldRepositionToDecodedPrefixConstruction :=
    acceptPostFieldRepositionToDecodedPrefixConstruction_of_rewinderAndRestorer
      acceptPostFieldRepositionRightEdgeRewinderConstruction_core
      hacceptRewound
  let hacceptBoundary :
      AcceptPostFieldBoundaryToDecodedPrefixConstruction :=
    acceptPostFieldBoundaryToDecodedPrefixConstruction_of_reposition
      hacceptReposition
  exact
    selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction_of_openConstructions
      ⟨hacceptBoundary, hrejectRemaining⟩

theorem selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction_bridgeCore :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction :=
  selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction_of_parts
    selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction_bridgeCore
    selectedProjectionPaddedTailCleanupScratchCountWindowRestorerConstruction_core

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction :=
  selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction_of_countWindowMaterializers
    selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction_bridgeCore

theorem selectedProjectionPaddedTailCleanupScratchExtConstruction :
    SelectedProjectionPaddedTailCleanupScratchExtConstruction :=
  selectedProjectionPaddedTailCleanupScratchExtConstruction_of_countExtenders
    selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction :=
  selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction_of_extenders
    selectedProjectionPaddedTailCleanupScratchExtConstruction

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncodedRewriters
end Computability
end FoC
