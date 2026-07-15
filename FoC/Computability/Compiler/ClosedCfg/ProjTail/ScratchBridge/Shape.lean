import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.BoolWordRawBitsDecoder
import FoC.Computability.Compiler.Structured.Lowering.Composition
import FoC.Computability.Compiler.Structured.Lowering.Projection
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchExtCountWindowConstructions

set_option doc.verso true

/-!
# Structured count-window bridge

This module records the lowered three-tape route for the count-window
decoded-prefix materializer.  The existing one-tape materializer contract
remains in
{module}`FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchExtCountWindowConstructions`;
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

namespace EncRewriters
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

def countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
    (useAccept : Bool) (L : DovetailLayout)
    (deletedTail : Word Bool) : List (Option Bool) :=
  encodedPrefixBeforeTape
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
    2

theorem countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix_eq_prefixCells
    (useAccept : Bool) (L : DovetailLayout)
    (deletedTail : Word Bool) :
    countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
        useAccept L deletedTail =
      encodedStructuredTapeCellsPrefix
        [ guardLogicalTape
            (structuredBoolWordRawBitsDecoderSourceTargetTape
              (ParsedLayoutBits L)
              (countWindowPostFieldDecodedPrefixStructuredSuffixTail
                useAccept L)
              (countWindowPostFieldDecodedPrefixStructuredSourcePadding
                useAccept L deletedTail))
        , guardLogicalTape
            (structuredBoolWordRawBitsDecoderCounterDecodeTape 0
              ((ParsedLayoutBits L).length + 1)) ] := by
  simp [countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix,
    encodedPrefixBeforeTape, guardLogicalTapes]

theorem countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix_accept_eq_prefixCells
    (L : DovetailLayout) (deletedTail : Word Bool) :
    countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
        true L deletedTail =
      encodedStructuredTapeCellsPrefix
        [ guardLogicalTape
            (structuredBoolWordRawBitsDecoderSourceTargetTape
              (ParsedLayoutBits L)
              (countWindowPostFieldDecodedPrefixStructuredSuffixTail
                true L)
              (countWindowPostFieldDecodedPrefixStructuredSourcePadding
                true L deletedTail))
        , guardLogicalTape
            (structuredBoolWordRawBitsDecoderCounterDecodeTape 0
              ((ParsedLayoutBits L).length + 1)) ] := by
  exact
    countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix_eq_prefixCells
      true L deletedTail

theorem countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix_reject_eq_prefixCells
    (L : DovetailLayout) (deletedTail : Word Bool) :
    countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
        false L deletedTail =
      encodedStructuredTapeCellsPrefix
        [ guardLogicalTape
            (structuredBoolWordRawBitsDecoderSourceTargetTape
              (ParsedLayoutBits L)
              (countWindowPostFieldDecodedPrefixStructuredSuffixTail
                false L)
              (countWindowPostFieldDecodedPrefixStructuredSourcePadding
                false L deletedTail))
        , guardLogicalTape
            (structuredBoolWordRawBitsDecoderCounterDecodeTape 0
              ((ParsedLayoutBits L).length + 1)) ] := by
  exact
    countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix_eq_prefixCells
      false L deletedTail

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

def selectedSegmentLogicalTapeDecoderDensifierFootprintCells
    (bits : Word Bool) (padding : List (Option Bool)) :
    List (Option Bool) :=
  List.append
    (selectedSegmentLogicalTapeDecoderCellCells (none : Option Bool))
    (List.append
      (selectedSegmentLogicalTapeDecoderCellCells (none : Option Bool))
      (List.append [none, none]
        (match bits with
        | [] =>
            List.append
              (selectedSegmentLogicalTapeDecoderCellCells
                (none : Option Bool))
              (List.map selectedSegmentLogicalTapeDecoderCellCells
                (List.append padding [none])).flatten
        | bit :: rest =>
            List.append
              (selectedSegmentLogicalTapeDecoderCellCells (some bit))
              (List.map selectedSegmentLogicalTapeDecoderCellCells
                (List.append (rest.map some)
                  (none :: List.append padding [none]))).flatten)))

def selectedSegmentLogicalTapeDecoderDensifierSourceCells
    (encodedPrefix : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) : List (Option Bool) :=
  List.append encodedPrefix
    (none ::
      List.append
        (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
          bits padding)
        [none, none])

def selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
    (bits : Word Bool) (padding : List (Option Bool)) :
    List (Option Bool) :=
  none ::
    List.append
      (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
        bits padding)
      [none]



def selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
    (bits : Word Bool) (padding : List (Option Bool)) : Tape Bool :=
  selectedSegmentLogicalTapeDecoderTargetTape
    (rightEdgeScanSourceTapeFromLeft [none] bits padding)
    []

def selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
    (bits : Word Bool) (padding : List (Option Bool)) : Tape Bool :=
  rightEdgeRewindSourceTape bits padding


theorem selectedSegmentLogicalTapeDecoder_cells_guard_rightEdgeScanSourceTapeFromLeft_eq_footprint
    (bits : Word Bool) (padding : List (Option Bool)) :
    statefulOptionCellsFrom selectedSegmentLogicalTapeDecoderNext
        selectedSegmentLogicalTapeDecoderEmit 0
        (logicalTapeBits
          (guardLogicalTape
            (rightEdgeScanSourceTapeFromLeft [none] bits padding))) =
      selectedSegmentLogicalTapeDecoderDensifierFootprintCells
        bits padding := by
  cases bits with
  | nil =>
      simpa [selectedSegmentLogicalTapeDecoderDensifierFootprintCells] using
        selectedSegmentLogicalTapeDecoder_cells_guard_rightEdgeScanSourceTapeFromLeft_nil
          padding
  | cons bit rest =>
      simpa [selectedSegmentLogicalTapeDecoderDensifierFootprintCells] using
        selectedSegmentLogicalTapeDecoder_cells_guard_rightEdgeScanSourceTapeFromLeft_cons
          bit rest padding



theorem selectedSegmentLogicalTapeDecoderTargetTape_cells_rightEdgeScanSourceTapeFromLeft_eq_densifierSource
    (encodedPrefix : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTargetTape
          (rightEdgeScanSourceTapeFromLeft [none] bits padding)
          encodedPrefix) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        encodedPrefix bits padding := by
  rw [selectedSegmentLogicalTapeDecoderTargetTape_cells]
  simp [selectedSegmentLogicalTapeDecoderStart,
    selectedSegmentLogicalTapeDecoderDensifierSourceCells,
    selectedSegmentLogicalTapeDecoder_cells_guard_rightEdgeScanSourceTapeFromLeft_eq_footprint]

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          bits padding) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        [] bits padding := by
  exact
    selectedSegmentLogicalTapeDecoderTargetTape_cells_rightEdgeScanSourceTapeFromLeft_eq_densifierSource
      [] bits padding

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        bits padding =
      rightEndCompactionSourceTape
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          bits padding) := by
  simp [selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape,
    selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells,
    selectedSegmentLogicalTapeDecoderTargetTape,
    FSTStatefulOptionAppendTargetTapeFromLeft,
    statefulOptionAppendWriteTargetTapeAtBlank, rightEndCompactionSourceTape,
    tapeAtCells, selectedSegmentLogicalTapeDecoderStart,
    selectedSegmentLogicalTapeDecoder_cells_guard_rightEdgeScanSourceTapeFromLeft_eq_footprint,
    List.reverse_append]

theorem rightEdgeScanSourceTapeFromLeft_singleBlank_normalizedOutput
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (rightEdgeScanSourceTapeFromLeft [none] bits padding) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [Tape.normalizedOutput, rightEdgeScanSourceTapeFromLeft_cells]
  simp [List.filterMap_append, Function.comp_def]

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_normalizedOutput
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          bits padding) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape,
    selectedSegmentLogicalTapeDecoderTargetTape_normalizedOutput,
    rightEdgeScanSourceTapeFromLeft_singleBlank_normalizedOutput]
  rfl






def countWindowPostFieldDecodedPrefixStructuredPrefixSelectedSegmentTargetTape
    (useAccept : Bool) (L : DovetailLayout)
    (deletedTail : Word Bool) : Tape Bool :=
  selectedSegmentLogicalTapeDecoderTargetTape
    (postFieldDecodedPrefixScanSourceTape useAccept L)
    (countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
      useAccept L deletedTail)

def countWindowPostFieldDecodedPrefixStructuredPrefixEraserSourceTape
    (useAccept : Bool) (L : DovetailLayout)
    (deletedTail : Word Bool) : Tape Bool :=
  countWindowPostFieldDecodedPrefixStructuredPrefixSelectedSegmentTargetTape
    useAccept L deletedTail

def countWindowPostFieldDecodedPrefixStructuredPrefixEraserTargetTape
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  selectedSegmentLogicalTapeDecoderTargetTape
    (postFieldDecodedPrefixScanSourceTape useAccept L)
    []




def countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorSourceTape
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  selectedSegmentLogicalTapeDecoderTargetTape
    (postFieldDecodedPrefixScanSourceTape useAccept L)
    []

/-- Repaired live ingress for the selected-footprint compactor.

The marker-preserving structured-prefix eraser leaves the adjacent
{lit}`[true, false]` sentinel before the alignment blank. Decoder pairs never
contain adjacent represented cells, so the sentinel gives the downstream
finite machine a detectable left boundary without strengthening the false
unmarked arbitrary-payload contract. -/
def countWindowPostFieldDecodedPrefixSelectedSegmentMarkedFootprintCompactorSourceTape
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  rightEndCompactionSourceTape
    ([some true, some false, none] ++
      selectedSegmentLogicalTapeDecoderDensifierFootprintCells
        (ParsedLayoutBits L)
        (postFieldDecodedPrefixScanPadding useAccept L) ++
      [none])

def countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorTargetTape
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  rightEdgeRewindSourceTape (ParsedLayoutBits L)
    (postFieldDecodedPrefixScanPadding useAccept L)










theorem selectedSegmentLogicalTapeDecoderTargetTape_move_left_move_right_equiv
    (target : Tape Bool) (encodedPrefix : List (Option Bool)) :
    Tape.Equiv
      (selectedSegmentLogicalTapeDecoderTargetTape
        target encodedPrefix)
      (Tape.move Direction.left
        (Tape.move Direction.right
          (selectedSegmentLogicalTapeDecoderTargetTape
            target encodedPrefix))) := by
  simp [selectedSegmentLogicalTapeDecoderTargetTape,
    FSTStatefulOptionAppendTargetTapeFromLeft,
    statefulOptionAppendWriteTargetTapeAtBlank, tapeAtCells,
    Tape.Equiv, Tape.dropTrailingNone, Tape.move, Tape.moveLeft,
    Tape.moveRight]

theorem selectedSegmentLogicalTapeDecoderCellCells_filterMap
    (cell : Option Bool) :
    (selectedSegmentLogicalTapeDecoderCellCells cell).filterMap
        (fun cell => cell) =
      cell.toList := by
  cases cell with
  | none =>
      rfl
  | some bit =>
      cases bit <;> rfl

theorem option_toList_flatten_eq_filterMap
    (cells : List (Option Bool)) :
    (cells.map (fun cell => cell.toList)).flatten =
      cells.filterMap (fun cell => cell) := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      cases cell <;> simp [ih]

theorem selectedSegmentLogicalTapeDecoderCellCells_flatten_filterMap
    (cells : List (Option Bool)) :
    ((cells.map selectedSegmentLogicalTapeDecoderCellCells).flatten).filterMap
        (fun cell => cell) =
      cells.filterMap (fun cell => cell) := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      cases cell <;>
        simp [selectedSegmentLogicalTapeDecoderCellCells_filterMap,
          List.filterMap_append, ih]

theorem bool_singleton_map_flatten (bits : Word Bool) :
    (bits.map (fun bit => [bit])).flatten = bits := by
  induction bits with
  | nil =>
      rfl
  | cons bit rest ih =>
      simp [ih]

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintCells_filterMap
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
        bits padding).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  cases bits with
  | nil =>
      simp [selectedSegmentLogicalTapeDecoderDensifierFootprintCells,
        selectedSegmentLogicalTapeDecoderCellCells_filterMap,
        option_toList_flatten_eq_filterMap,
        List.filterMap_append, Function.comp_def]
  | cons bit rest =>
      cases bit <;>
        simp [selectedSegmentLogicalTapeDecoderDensifierFootprintCells,
          selectedSegmentLogicalTapeDecoderCellCells_filterMap,
          option_toList_flatten_eq_filterMap, bool_singleton_map_flatten,
          List.filterMap_append, Function.comp_def]

theorem selectedSegmentLogicalTapeDecoderDensifierSourceCells_filterMap
    (encodedPrefix : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderDensifierSourceCells
        encodedPrefix bits padding).filterMap (fun cell => cell) =
      List.append (encodedPrefix.filterMap (fun cell => cell))
        (List.append bits (padding.filterMap (fun cell => cell))) := by
  simp [selectedSegmentLogicalTapeDecoderDensifierSourceCells,
    selectedSegmentLogicalTapeDecoderDensifierFootprintCells_filterMap,
    List.filterMap_append]










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


end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
