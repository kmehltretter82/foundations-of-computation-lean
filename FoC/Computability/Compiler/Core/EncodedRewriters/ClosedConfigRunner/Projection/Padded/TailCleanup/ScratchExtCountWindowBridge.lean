import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.BoolWordRawBitsDecoder
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.Composition
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.Projection
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
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

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

def countWindowPostFieldDecodedPrefixStructuredEncodedInputTape
    (useAccept : Bool) (L : DovetailLayout) (pref : Word Bool)
    (leftBit : Bool) (deletedTail : Word Bool) : Tape Bool :=
  Structured.MultiTapeLowering.encodedGuardedStructured3Tapes
    (countWindowPostFieldDecodedPrefixMaterializerSourceTape
      useAccept L pref leftBit deletedTail)
    Tape.blank
    (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
      (ParsedLayoutBits L).length
      (postFieldDecodedPrefixScanPadding useAccept L))

def countWindowPostFieldDecodedPrefixStructuredEncodedOutputTape
    (useAccept : Bool) (L : DovetailLayout)
    (deletedTail : Word Bool) : Tape Bool :=
  Structured.MultiTapeLowering.encodedGuardedStructured3Tapes
    (structuredBoolWordRawBitsDecoderSourceTargetTape
      (ParsedLayoutBits L)
      (countWindowPostFieldDecodedPrefixStructuredSuffixTail
        useAccept L)
      (countWindowPostFieldDecodedPrefixStructuredSourcePadding
        useAccept L deletedTail))
    (structuredBoolWordRawBitsDecoderCounterDecodeTape 0
      ((ParsedLayoutBits L).length + 1))
    (postFieldDecodedPrefixScanSourceTape useAccept L)

theorem logicalTapeBits_guard_rightEdgeScanSourceTapeFromLeft_nil
    (padding : List (Option Bool)) :
    logicalTapeBits
        (guardLogicalTape
          (rightEdgeScanSourceTapeFromLeft [none] [] padding)) =
      List.append (logicalCellBits (none : Option Bool))
        (List.append (logicalCellBits (none : Option Bool))
          (List.append [true, true]
            (List.append (logicalCellBits (none : Option Bool))
              (logicalCellListBits
                (List.append padding [none]))))) := by
  simp [rightEdgeScanSourceTapeFromLeft, tapeAtCells,
    guardLogicalTape, logicalTapeBits, logicalCellListBits,
    List.append_assoc]

theorem logicalTapeBits_guard_rightEdgeScanSourceTapeFromLeft_cons
    (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    logicalTapeBits
        (guardLogicalTape
          (rightEdgeScanSourceTapeFromLeft [none]
            (bit :: rest) padding)) =
      List.append (logicalCellBits (none : Option Bool))
        (List.append (logicalCellBits (none : Option Bool))
          (List.append [true, true]
            (List.append (logicalCellBits (some bit))
              (logicalCellListBits
                (List.append (rest.map some)
                  (none :: List.append padding [none])))))) := by
  simp [rightEdgeScanSourceTapeFromLeft, tapeAtCells,
    guardLogicalTape, logicalTapeBits, logicalCellListBits,
    List.append_assoc]

theorem selectedSegmentLogicalTapeDecoder_cells_guard_rightEdgeScanSourceTapeFromLeft_nil
    (padding : List (Option Bool)) :
    statefulOptionCellsFrom selectedSegmentLogicalTapeDecoderNext
        selectedSegmentLogicalTapeDecoderEmit 0
        (logicalTapeBits
          (guardLogicalTape
            (rightEdgeScanSourceTapeFromLeft [none] [] padding))) =
      List.append
        (selectedSegmentLogicalTapeDecoderCellCells (none : Option Bool))
        (List.append
          (selectedSegmentLogicalTapeDecoderCellCells (none : Option Bool))
          (List.append [none, none]
            (List.append
              (selectedSegmentLogicalTapeDecoderCellCells
                (none : Option Bool))
              (List.map selectedSegmentLogicalTapeDecoderCellCells
                (List.append padding [none])).flatten))) := by
  rw [logicalTapeBits_guard_rightEdgeScanSourceTapeFromLeft_nil]
  rw [statefulOptionCellsFrom_append]
  rw [selectedSegmentLogicalTapeDecoder_cells_logicalCellBits_zero]
  rw [selectedSegmentLogicalTapeDecoder_after_logicalCellBits_zero]
  rw [statefulOptionCellsFrom_append]
  rw [selectedSegmentLogicalTapeDecoder_cells_logicalCellBits_zero]
  rw [selectedSegmentLogicalTapeDecoder_after_logicalCellBits_zero]
  rw [statefulOptionCellsFrom_append]
  rw [selectedSegmentLogicalTapeDecoder_cells_headMarker_zero]
  rw [selectedSegmentLogicalTapeDecoder_after_headMarker_zero]
  rw [statefulOptionCellsFrom_append]
  rw [selectedSegmentLogicalTapeDecoder_cells_logicalCellBits_zero]
  rw [selectedSegmentLogicalTapeDecoder_after_logicalCellBits_zero]
  rw [selectedSegmentLogicalTapeDecoder_cells_logicalCellListBits_zero]

theorem selectedSegmentLogicalTapeDecoder_cells_guard_rightEdgeScanSourceTapeFromLeft_cons
    (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    statefulOptionCellsFrom selectedSegmentLogicalTapeDecoderNext
        selectedSegmentLogicalTapeDecoderEmit 0
        (logicalTapeBits
          (guardLogicalTape
            (rightEdgeScanSourceTapeFromLeft [none]
              (bit :: rest) padding))) =
      List.append
        (selectedSegmentLogicalTapeDecoderCellCells (none : Option Bool))
        (List.append
          (selectedSegmentLogicalTapeDecoderCellCells (none : Option Bool))
          (List.append [none, none]
            (List.append
              (selectedSegmentLogicalTapeDecoderCellCells (some bit))
              (List.map selectedSegmentLogicalTapeDecoderCellCells
                (List.append (rest.map some)
                  (none :: List.append padding [none]))).flatten))) := by
  rw [logicalTapeBits_guard_rightEdgeScanSourceTapeFromLeft_cons]
  rw [statefulOptionCellsFrom_append]
  rw [selectedSegmentLogicalTapeDecoder_cells_logicalCellBits_zero]
  rw [selectedSegmentLogicalTapeDecoder_after_logicalCellBits_zero]
  rw [statefulOptionCellsFrom_append]
  rw [selectedSegmentLogicalTapeDecoder_cells_logicalCellBits_zero]
  rw [selectedSegmentLogicalTapeDecoder_after_logicalCellBits_zero]
  rw [statefulOptionCellsFrom_append]
  rw [selectedSegmentLogicalTapeDecoder_cells_headMarker_zero]
  rw [selectedSegmentLogicalTapeDecoder_after_headMarker_zero]
  rw [statefulOptionCellsFrom_append]
  rw [selectedSegmentLogicalTapeDecoder_cells_logicalCellBits_zero]
  rw [selectedSegmentLogicalTapeDecoder_after_logicalCellBits_zero]
  rw [selectedSegmentLogicalTapeDecoder_cells_logicalCellListBits_zero]

theorem selectedSegmentLogicalTapeDecoderTargetTape_cells_rightEdgeScanSourceTapeFromLeft_nil
    (encodedPrefix padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTargetTape
          (rightEdgeScanSourceTapeFromLeft [none] [] padding)
          encodedPrefix) =
      List.append encodedPrefix
        (none ::
          List.append
            (List.append
              (selectedSegmentLogicalTapeDecoderCellCells
                (none : Option Bool))
              (List.append
                (selectedSegmentLogicalTapeDecoderCellCells
                  (none : Option Bool))
                (List.append [none, none]
                  (List.append
                    (selectedSegmentLogicalTapeDecoderCellCells
                      (none : Option Bool))
                    (List.map selectedSegmentLogicalTapeDecoderCellCells
                      (List.append padding [none])).flatten))))
            [none, none]) := by
  rw [selectedSegmentLogicalTapeDecoderTargetTape_cells]
  simp [selectedSegmentLogicalTapeDecoderStart,
    selectedSegmentLogicalTapeDecoder_cells_guard_rightEdgeScanSourceTapeFromLeft_nil]

theorem selectedSegmentLogicalTapeDecoderTargetTape_cells_rightEdgeScanSourceTapeFromLeft_cons
    (bit : Bool) (rest : Word Bool)
    (encodedPrefix padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTargetTape
          (rightEdgeScanSourceTapeFromLeft [none] (bit :: rest) padding)
          encodedPrefix) =
      List.append encodedPrefix
        (none ::
          List.append
            (List.append
              (selectedSegmentLogicalTapeDecoderCellCells
                (none : Option Bool))
              (List.append
                (selectedSegmentLogicalTapeDecoderCellCells
                  (none : Option Bool))
                (List.append [none, none]
                  (List.append
                    (selectedSegmentLogicalTapeDecoderCellCells
                      (some bit))
                    (List.map selectedSegmentLogicalTapeDecoderCellCells
                      (List.append (rest.map some)
                        (none :: List.append padding [none]))).flatten))))
            [none, none]) := by
  rw [selectedSegmentLogicalTapeDecoderTargetTape_cells]
  simp [selectedSegmentLogicalTapeDecoderStart,
    selectedSegmentLogicalTapeDecoder_cells_guard_rightEdgeScanSourceTapeFromLeft_cons]

theorem postFieldDecodedPrefixScanSourceTape_cells
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.cells (postFieldDecodedPrefixScanSourceTape useAccept L) =
      List.append [none]
        (List.append ((ParsedLayoutBits L).map some)
          (none :: postFieldDecodedPrefixScanPadding useAccept L)) := by
  rw [postFieldDecodedPrefixScanSourceTape,
    rightEdgeScanSourceTapeFromLeft_cells]
  rfl

theorem selectedSegmentLogicalTapeDecoderTargetTape_cells_postFieldDecodedPrefixScanSourceTape_nil
    (useAccept : Bool) (L : DovetailLayout)
    (encodedPrefix : List (Option Bool))
    (hbits : ParsedLayoutBits L = []) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTargetTape
          (postFieldDecodedPrefixScanSourceTape useAccept L)
          encodedPrefix) =
      List.append encodedPrefix
        (none ::
          List.append
            (List.append
              (selectedSegmentLogicalTapeDecoderCellCells
                (none : Option Bool))
              (List.append
                (selectedSegmentLogicalTapeDecoderCellCells
                  (none : Option Bool))
                (List.append [none, none]
                  (List.append
                    (selectedSegmentLogicalTapeDecoderCellCells
                      (none : Option Bool))
                    (List.map selectedSegmentLogicalTapeDecoderCellCells
                      (List.append
                        (postFieldDecodedPrefixScanPadding useAccept L)
                        [none])).flatten))))
            [none, none]) := by
  rw [postFieldDecodedPrefixScanSourceTape, hbits]
  exact
    selectedSegmentLogicalTapeDecoderTargetTape_cells_rightEdgeScanSourceTapeFromLeft_nil
      encodedPrefix (postFieldDecodedPrefixScanPadding useAccept L)

theorem selectedSegmentLogicalTapeDecoderTargetTape_cells_postFieldDecodedPrefixScanSourceTape_cons
    (useAccept : Bool) (L : DovetailLayout)
    (bit : Bool) (rest : Word Bool)
    (encodedPrefix : List (Option Bool))
    (hbits : ParsedLayoutBits L = bit :: rest) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTargetTape
          (postFieldDecodedPrefixScanSourceTape useAccept L)
          encodedPrefix) =
      List.append encodedPrefix
        (none ::
          List.append
            (List.append
              (selectedSegmentLogicalTapeDecoderCellCells
                (none : Option Bool))
              (List.append
                (selectedSegmentLogicalTapeDecoderCellCells
                  (none : Option Bool))
                (List.append [none, none]
                  (List.append
                    (selectedSegmentLogicalTapeDecoderCellCells
                      (some bit))
                    (List.map selectedSegmentLogicalTapeDecoderCellCells
                      (List.append (rest.map some)
                        (none :: List.append
                          (postFieldDecodedPrefixScanPadding useAccept L)
                          [none]))).flatten))))
            [none, none]) := by
  rw [postFieldDecodedPrefixScanSourceTape, hbits]
  exact
    selectedSegmentLogicalTapeDecoderTargetTape_cells_rightEdgeScanSourceTapeFromLeft_cons
      bit rest encodedPrefix (postFieldDecodedPrefixScanPadding useAccept L)

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
        (countWindowPostFieldDecodedPrefixStructuredEncodedInputTape
          useAccept L pref leftBit deletedTail)
        (countWindowPostFieldDecodedPrefixStructuredEncodedOutputTape
          useAccept L deletedTail)

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
  simpa [countWindowPostFieldDecodedPrefixStructuredEncodedInputTape,
    countWindowPostFieldDecodedPrefixStructuredEncodedOutputTape,
    Structured.MultiTapeLowering.encodedGuardedStructured3Tapes,
    postFieldDecodedPrefixScanSourceTape,
    countWindowPostFieldDecodedPrefixMaterializerSourceTape_eq_boolWordSource
      useAccept L pref leftBit deletedTail hpayload] using
    loweredStructuredBoolWordRawBitsDecoderDescription_haltsFromTapeWithOutputPadding
      (ParsedLayoutBits L)
      (countWindowPostFieldDecodedPrefixStructuredSuffixTail useAccept L)
      (countWindowPostFieldDecodedPrefixStructuredSourcePadding
        useAccept L deletedTail)
      (postFieldDecodedPrefixScanPadding useAccept L)

def CountWindowPostFieldDecodedPrefixStructuredInputInitializerSpec
    (useAccept : Bool) (initializer : MachineDescription) : Prop :=
  initializer.SubroutineReady ∧
    forall (L : DovetailLayout) (pref : Word Bool)
      (leftBit : Bool) (deletedTail : Word Bool),
      configurationFieldBits L.acceptConfig [] = false :: deletedTail ->
      countWindowPostFieldDecodedPrefixMaterializerPayload useAccept L =
          List.append pref [leftBit] ->
      initializer.HaltsFromTapeEquiv
        (countWindowPostFieldDecodedPrefixMaterializerSourceTape
          useAccept L pref leftBit deletedTail)
        (countWindowPostFieldDecodedPrefixStructuredEncodedInputTape
          useAccept L pref leftBit deletedTail)

def CountWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction :
    Prop :=
  forall useAccept : Bool,
    exists initializer : MachineDescription,
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerSpec
        useAccept initializer

theorem countWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction_of_rawBitsInitializer
    (hinitializer :
      StructuredBoolWordRawBitsDecoderInputInitializerConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction := by
  rcases hinitializer with ⟨initializer, hinitializerReady, hinitializerRun⟩
  intro useAccept
  refine ⟨initializer, hinitializerReady, ?_⟩
  intro L pref leftBit deletedTail _hdeleted hpayload
  simpa [countWindowPostFieldDecodedPrefixStructuredEncodedInputTape,
    countWindowPostFieldDecodedPrefixMaterializerSourceTape_eq_boolWordSource
      useAccept L pref leftBit deletedTail hpayload] using
    hinitializerRun
      (ParsedLayoutBits L)
      (countWindowPostFieldDecodedPrefixStructuredSuffixTail useAccept L)
      (countWindowPostFieldDecodedPrefixStructuredSourcePadding
        useAccept L deletedTail)
      (postFieldDecodedPrefixScanPadding useAccept L)

theorem countWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction := by
  exact
    countWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction_of_rawBitsInitializer
      structuredBoolWordRawBitsDecoderInputInitializerConstruction_core

/--
Count-window-specific output projection from the lowered structured extractor.

This is intentionally narrower than the reusable
{name}`Structured.MultiTapeLowering.StructuredTape2ProjectorSpec`: the bridge
only needs to extract the third tape from the concrete structured output shape
produced by the decoded-prefix extractor.
-/
def CountWindowPostFieldDecodedPrefixStructuredOutputProjectorSpec
    (projector : MachineDescription) : Prop :=
  projector.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout)
      (deletedTail : Word Bool),
      projector.HaltsFromTapeEquiv
        (countWindowPostFieldDecodedPrefixStructuredEncodedOutputTape
          useAccept L deletedTail)
        (postFieldDecodedPrefixScanSourceTape useAccept L)

def CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction :
    Prop :=
  exists projector : MachineDescription,
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorSpec projector

/--
Count-window-specific normalizer for the selected guarded tape-2 segment.

The input cursor has already been moved to the separator before the third
logical tape in the lowered structured output.  This is narrower than
{name}`Structured.MultiTapeLowering.StructuredTape2SegmentNormalizerSpec`
because it only has to decode the concrete right-edge scan-source tape shape
used by this bridge.
-/
def CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerSpec
    (normalizer : MachineDescription) : Prop :=
  normalizer.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout)
      (deletedTail : Word Bool) (physical : Tape Bool),
      AtTapeSeparator
        (guardLogicalTapes
          [ structuredBoolWordRawBitsDecoderSourceTargetTape
              (ParsedLayoutBits L)
              (countWindowPostFieldDecodedPrefixStructuredSuffixTail
                useAccept L)
              (countWindowPostFieldDecodedPrefixStructuredSourcePadding
                useAccept L deletedTail)
          , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
              ((ParsedLayoutBits L).length + 1)
          , postFieldDecodedPrefixScanSourceTape useAccept L ])
        2 physical ->
        normalizer.HaltsFromTapeEquiv physical
          (postFieldDecodedPrefixScanSourceTape useAccept L)

def CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction :
    Prop :=
  exists normalizer : MachineDescription,
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerSpec
      normalizer

/--
Count-window-specific decoder for the selected canonical tape-2 segment.

This is the concrete output-side finite-machine target from the bridge plan:
starting at the selected segment separator, decode the guarded structured
encoding of the right-edge scan-source tape back to that plain tape.  The
encoded prefix to the left is arbitrary because the tape-2 seeker leaves the
previous structured segments there.
-/
def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderSpec
    (decoder : MachineDescription) : Prop :=
  decoder.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout)
      (encodedPrefix : List (Option Bool)),
      decoder.HaltsFromTapeEquiv
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells
            [guardLogicalTape
              (postFieldDecodedPrefixScanSourceTape useAccept L)]))
        (postFieldDecodedPrefixScanSourceTape useAccept L)

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction :
    Prop :=
  exists decoder : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderSpec decoder

/--
Count-window-specific cleanup after the selected-segment bit scan.

The generic arbitrary-tape cleanup is too strong for the simple bit scanner:
after scanning, the marker position has to be recovered from the concrete
right-edge scan-source layout.  This narrowed contract is the remaining
output-side adapter obligation for this bridge.
-/
def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout)
      (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTargetTape
          (postFieldDecodedPrefixScanSourceTape useAccept L)
          encodedPrefix)
        (postFieldDecodedPrefixScanSourceTape useAccept L)

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupConstruction :
    Prop :=
  exists cleanup : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupSpec cleanup

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction_of_cleanup
    (hcleanup :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction := by
  rcases hcleanup with
    ⟨cleanup, hcleanupReady, hcleanupRun⟩
  refine
    ⟨selectedSegmentLogicalTapeDecoderPipelineDescription cleanup,
      ?_⟩
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderPipelineDescription_subroutineReady
        hcleanupReady
  · intro useAccept L encodedPrefix
    have hmove :
        (cursorMoveOnceDescription Direction.right).HaltsFromTapeEquiv
          (tapeAtEncodedSplit encodedPrefix
            (encodedStructuredTapeCells
              [guardLogicalTape
                (postFieldDecodedPrefixScanSourceTape useAccept L)]))
          (Tape.move Direction.right
            (tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells
                [guardLogicalTape
                  (postFieldDecodedPrefixScanSourceTape useAccept L)]))) :=
      (cursorMoveOnceDescription_haltsFromTape Direction.right
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells
            [guardLogicalTape
              (postFieldDecodedPrefixScanSourceTape useAccept L)]))).toEquiv
    have hscan :
        selectedSegmentLogicalTapeDecoderDescription.HaltsFromTapeEquiv
          (Tape.move Direction.right
            (tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells
                [guardLogicalTape
                  (postFieldDecodedPrefixScanSourceTape useAccept L)])))
          (selectedSegmentLogicalTapeDecoderTargetTape
            (postFieldDecodedPrefixScanSourceTape useAccept L)
            encodedPrefix) :=
      (selectedSegmentLogicalTapeDecoderDescription_haltsFrom_selectedSingletonPayload
        (postFieldDecodedPrefixScanSourceTape useAccept L)
        encodedPrefix).toEquiv
    have hpipelineScan :
        (canonicalPrimitiveSeqDescription
          (cursorMoveOnceDescription Direction.right)
          selectedSegmentLogicalTapeDecoderDescription).HaltsFromTapeEquiv
            (tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells
                [guardLogicalTape
                  (postFieldDecodedPrefixScanSourceTape useAccept L)]))
            (selectedSegmentLogicalTapeDecoderTargetTape
              (postFieldDecodedPrefixScanSourceTape useAccept L)
              encodedPrefix) :=
      canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        (cursorMoveOnceDescription_subroutineReady Direction.right)
        selectedSegmentLogicalTapeDecoderDescription_subroutineReady
        hmove
        hscan
    exact
      canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        (canonicalPrimitiveSeqDescription_subroutineReady
          (cursorMoveOnceDescription_subroutineReady Direction.right)
          selectedSegmentLogicalTapeDecoderDescription_subroutineReady)
        hcleanupReady
        hpipelineScan
        (hcleanupRun useAccept L encodedPrefix)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction_of_singletonDecoder
    (hdecoder :
      StructuredSelectedSingletonSegmentDecoderConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction := by
  unfold StructuredSelectedSingletonSegmentDecoderConstruction at hdecoder
  rcases hdecoder with ⟨decoder, hdecoderReady, hdecoderRun⟩
  refine ⟨decoder, hdecoderReady, ?_⟩
  intro useAccept L encodedPrefix
  exact hdecoderRun (postFieldDecodedPrefixScanSourceTape useAccept L)
    encodedPrefix

theorem countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_of_selectedSegmentDecoder
    (hdecoder :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction := by
  rcases hdecoder with ⟨decoder, hdecoderReady, hdecoderRun⟩
  refine ⟨decoder, hdecoderReady, ?_⟩
  intro useAccept L deletedTail physical hseparator
  rcases hseparator with ⟨_hindex, hphysical⟩
  rw [hphysical]
  simpa [encodedSuffixFromTape, guardLogicalTapes] using
    hdecoderRun useAccept L
      (encodedPrefixBeforeTape
        (guardLogicalTapes
          [ structuredBoolWordRawBitsDecoderSourceTargetTape
              (ParsedLayoutBits L)
              (countWindowPostFieldDecodedPrefixStructuredSuffixTail
                useAccept L)
              (countWindowPostFieldDecodedPrefixStructuredSourcePadding
                useAccept L deletedTail)
          , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
              ((ParsedLayoutBits L).length + 1)
          , postFieldDecodedPrefixScanSourceTape useAccept L ])
        2)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupConstruction_core :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupConstruction := by
  sorry

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction_core :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction :=
  countWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction_of_cleanup
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupConstruction_core

theorem countWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction_of_countWindowSegmentNormalizer
    (hnormalizer :
      CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction := by
  rcases hnormalizer with
    ⟨normalizer, hnormalizerReady, hnormalizerRun⟩
  refine
    ⟨structuredTape2ProjectorDescription normalizer, ?_⟩
  constructor
  · exact
      structuredTape2ProjectorDescription_subroutineReady
        hnormalizerReady
  · intro useAccept L deletedTail
    let T0 :=
      structuredBoolWordRawBitsDecoderSourceTargetTape
        (ParsedLayoutBits L)
        (countWindowPostFieldDecodedPrefixStructuredSuffixTail
          useAccept L)
        (countWindowPostFieldDecodedPrefixStructuredSourcePadding
          useAccept L deletedTail)
    let T1 :=
      structuredBoolWordRawBitsDecoderCounterDecodeTape 0
        ((ParsedLayoutBits L).length + 1)
    let T2 := postFieldDecodedPrefixScanSourceTape useAccept L
    have hsource :
        exists A : Tape Bool, exists B : Tape Bool, exists C : Tape Bool,
          guardLogicalTapes [T0, T1, T2] = [A, B, C] ∧
            AtEncodedBlockStart (guardLogicalTapes [T0, T1, T2])
              (countWindowPostFieldDecodedPrefixStructuredEncodedOutputTape
                useAccept L deletedTail) := by
      refine
        ⟨guardLogicalTape T0, guardLogicalTape T1,
          guardLogicalTape T2, ?_, ?_⟩
      · simp [guardLogicalTapes]
      · simpa [T0, T1, T2,
          countWindowPostFieldDecodedPrefixStructuredEncodedOutputTape] using
          atEncodedBlockStart_self (guardLogicalTapes [T0, T1, T2])
    rcases
        seekTape2Description_contract_three.realizes
          (guardLogicalTapes [T0, T1, T2])
          (countWindowPostFieldDecodedPrefixStructuredEncodedOutputTape
            useAccept L deletedTail)
          hsource with
      ⟨Tmid, hseek, hseparator⟩
    exact
      canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        seekTape2Description_subroutineReady
        hnormalizerReady
        hseek.toEquiv
        (hnormalizerRun useAccept L deletedTail Tmid
          (by
            simpa [T0, T1, T2] using hseparator))

theorem countWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction_of_selectedSegmentDecoder
    (hdecoder :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction :=
  countWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction_of_countWindowSegmentNormalizer
    (countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_of_selectedSegmentDecoder
      hdecoder)

theorem countWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction_of_segmentNormalizer
    (hnormalizer :
      Structured.MultiTapeLowering.StructuredTape2SegmentNormalizerConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction := by
  rcases
      structuredTape2ProjectorConstruction_of_segmentNormalizerConstruction
        hnormalizer with
    ⟨projector, hprojectorReady, hprojectorRun⟩
  refine ⟨projector, hprojectorReady, ?_⟩
  intro useAccept L deletedTail
  exact
    hprojectorRun
      (structuredBoolWordRawBitsDecoderSourceTargetTape
        (ParsedLayoutBits L)
        (countWindowPostFieldDecodedPrefixStructuredSuffixTail useAccept L)
        (countWindowPostFieldDecodedPrefixStructuredSourcePadding
          useAccept L deletedTail))
      (structuredBoolWordRawBitsDecoderCounterDecodeTape 0
        ((ParsedLayoutBits L).length + 1))
      (postFieldDecodedPrefixScanSourceTape useAccept L)

theorem countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_of_segmentNormalizer
    (hnormalizer :
      Structured.MultiTapeLowering.StructuredTape2SegmentNormalizerConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction := by
  rcases hnormalizer with ⟨normalizer, hnormalizerReady, hnormalizerRun⟩
  refine ⟨normalizer, hnormalizerReady, ?_⟩
  intro useAccept L deletedTail physical hseparator
  exact
    hnormalizerRun
      (structuredBoolWordRawBitsDecoderSourceTargetTape
        (ParsedLayoutBits L)
        (countWindowPostFieldDecodedPrefixStructuredSuffixTail useAccept L)
        (countWindowPostFieldDecodedPrefixStructuredSourcePadding
          useAccept L deletedTail))
      (structuredBoolWordRawBitsDecoderCounterDecodeTape 0
        ((ParsedLayoutBits L).length + 1))
      (postFieldDecodedPrefixScanSourceTape useAccept L)
      physical hseparator

theorem countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction := by
  exact
    countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_of_selectedSegmentDecoder
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction_core

theorem countWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction := by
  exact
    countWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction_of_countWindowSegmentNormalizer
      countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_core

theorem countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_of_structuredParts
    (hinitializer :
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction)
    (hextractor :
      LoweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction)
    (hprojector :
      CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction) :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction := by
  intro useAccept
  rcases hinitializer useAccept with ⟨initializer, hinitializerSpec⟩
  rcases hextractor with ⟨extractor, hextractorReady, hextractorRun⟩
  rcases hprojector with ⟨projector, hprojectorSpec⟩
  refine
    ⟨structured3EndpointBridgeDescription
        initializer extractor projector,
      ?_⟩
  constructor
  · exact
      structured3EndpointBridgeDescription_subroutineReady
        hinitializerSpec.left hextractorReady
        hprojectorSpec.left
  · intro L pref leftBit deletedTail hdeleted hpayload
    have hinitializerRun :
        initializer.HaltsFromTapeEquiv
          (countWindowPostFieldDecodedPrefixMaterializerSourceTape
            useAccept L pref leftBit deletedTail)
          (countWindowPostFieldDecodedPrefixStructuredEncodedInputTape
            useAccept L pref leftBit deletedTail) :=
      hinitializerSpec.right L pref leftBit deletedTail hdeleted hpayload
    have hextractorRun :
        extractor.HaltsFromTapeEquiv
          (countWindowPostFieldDecodedPrefixStructuredEncodedInputTape
            useAccept L pref leftBit deletedTail)
          (countWindowPostFieldDecodedPrefixStructuredEncodedOutputTape
            useAccept L deletedTail) :=
      hextractorRun
        useAccept L pref leftBit deletedTail hdeleted hpayload
    have hprojectorRun :
        projector.HaltsFromTapeEquiv
          (countWindowPostFieldDecodedPrefixStructuredEncodedOutputTape
            useAccept L deletedTail)
          (postFieldDecodedPrefixScanSourceTape useAccept L) :=
      hprojectorSpec.right useAccept L deletedTail
    simpa [countWindowPostFieldDecodedPrefixStructuredEncodedInputTape,
      countWindowPostFieldDecodedPrefixStructuredEncodedOutputTape] using
      structured3EndpointBridgeDescription_haltsFromTapeEquiv
        hinitializerSpec.left hextractorReady hprojectorSpec.left
        hinitializerRun hextractorRun hprojectorRun

theorem countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_of_loweredStructuredExtractor
    (hextractor :
      LoweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction) :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction :=
  countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_of_structuredParts
    countWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction_core
    hextractor
    countWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction_core

theorem countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_of_selectedSegmentDecoder
    (hdecoder :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction)
    (hextractor :
      LoweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction) :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction :=
  countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_of_structuredParts
    countWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction_core
    hextractor
    (countWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction_of_selectedSegmentDecoder
      hdecoder)

theorem countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_bridgeCore :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction :=
  countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_of_loweredStructuredExtractor
    loweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction_core

theorem countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_bridgeCore_of_selectedSegmentDecoder
    (hdecoder :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction) :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction :=
  countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_of_selectedSegmentDecoder
    hdecoder
    loweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction_core

theorem selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction_of_scanSourceMaterializer
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction := by
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

theorem selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction_bridgeCore :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction :=
  selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction_of_scanSourceMaterializer
    countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_bridgeCore

theorem selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction_bridgeCore_of_selectedSegmentDecoder
    (hdecoder :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction :=
  selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction_of_scanSourceMaterializer
    (countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_bridgeCore_of_selectedSegmentDecoder
      hdecoder)

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
