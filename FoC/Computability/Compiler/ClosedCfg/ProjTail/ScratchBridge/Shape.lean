import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.BoolWordRawBitsDecoder
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.Composition
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.Projection
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

theorem countWindowPostFieldDecodedPrefixStructuredEncodedInputTape_eq_materializerTargetTape
    (useAccept : Bool) (L : DovetailLayout) (pref : Word Bool)
    (leftBit : Bool) (deletedTail : Word Bool) :
    countWindowPostFieldDecodedPrefixStructuredEncodedInputTape
        useAccept L pref leftBit deletedTail =
      structured3InputMaterializerTargetTape
        (countWindowPostFieldDecodedPrefixMaterializerSourceTape
          useAccept L pref leftBit deletedTail)
        (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
          (ParsedLayoutBits L).length
          (postFieldDecodedPrefixScanPadding useAccept L)) := by
  rfl

theorem countWindowPostFieldDecodedPrefixStructuredEncodedInputTape_read
    (useAccept : Bool) (L : DovetailLayout) (pref : Word Bool)
    (leftBit : Bool) (deletedTail : Word Bool) :
    Tape.read
        (countWindowPostFieldDecodedPrefixStructuredEncodedInputTape
          useAccept L pref leftBit deletedTail) =
      none := by
  rfl

theorem countWindowPostFieldDecodedPrefixStructuredEncodedInputTape_cells_eq_materializerTargetTape_cells
    (useAccept : Bool) (L : DovetailLayout) (pref : Word Bool)
    (leftBit : Bool) (deletedTail : Word Bool) :
    Tape.cells
        (countWindowPostFieldDecodedPrefixStructuredEncodedInputTape
          useAccept L pref leftBit deletedTail) =
      Tape.cells
        (structured3InputMaterializerTargetTape
          (countWindowPostFieldDecodedPrefixMaterializerSourceTape
            useAccept L pref leftBit deletedTail)
          (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
            (ParsedLayoutBits L).length
            (postFieldDecodedPrefixScanPadding useAccept L))) := by
  rw [
    countWindowPostFieldDecodedPrefixStructuredEncodedInputTape_eq_materializerTargetTape]

theorem countWindowPostFieldDecodedPrefixStructuredEncodedInputTape_normalizedOutput_eq_materializerTargetTape
    (useAccept : Bool) (L : DovetailLayout) (pref : Word Bool)
    (leftBit : Bool) (deletedTail : Word Bool) :
    Tape.normalizedOutput
        (countWindowPostFieldDecodedPrefixStructuredEncodedInputTape
          useAccept L pref leftBit deletedTail) =
      Tape.normalizedOutput
        (structured3InputMaterializerTargetTape
          (countWindowPostFieldDecodedPrefixMaterializerSourceTape
            useAccept L pref leftBit deletedTail)
          (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
            (ParsedLayoutBits L).length
            (postFieldDecodedPrefixScanPadding useAccept L))) := by
  rw [
    countWindowPostFieldDecodedPrefixStructuredEncodedInputTape_eq_materializerTargetTape]

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

def selectedSegmentLogicalTapeDecoderDensifierTargetCells
    (bits : Word Bool) (padding : List (Option Bool)) :
    List (Option Bool) :=
  List.append (bits.map some) (none :: padding)

def selectedSegmentLogicalTapeDecoderDensifierPaddingPreservingCells
    (bits : Word Bool) (padding : List (Option Bool)) :
    List (Option Bool) :=
  List.append (bits.map some) (none :: padding)

def selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
    (bits : Word Bool) (padding : List (Option Bool)) : Tape Bool :=
  selectedSegmentLogicalTapeDecoderTargetTape
    (rightEdgeScanSourceTapeFromLeft [none] bits padding)
    []

def selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
    (bits : Word Bool) (padding : List (Option Bool)) : Tape Bool :=
  rightEdgeRewindSourceTape bits padding

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintVisibleCells_eq_sourceCells
    (bits : Word Bool) (padding : List (Option Bool)) :
    rightEndCompactionVisibleCells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          bits padding) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        [] bits padding := by
  simp [rightEndCompactionVisibleCells,
    selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells,
    selectedSegmentLogicalTapeDecoderDensifierSourceCells,
    List.append_assoc]

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

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          bits padding) =
      selectedSegmentLogicalTapeDecoderDensifierPaddingPreservingCells
        bits padding := by
  rw [selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape,
    selectedSegmentLogicalTapeDecoderDensifierPaddingPreservingCells]
  exact rightEdgeRewindSourceTape_cells bits padding

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_normalizedOutput
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          bits padding) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape]
  exact rightEdgeRewindSourceTape_normalizedOutput bits padding

theorem selectedSegmentLogicalTapeDecoderDensifierFootprint_normalizedOutput_eq
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          bits padding) =
      Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          bits padding) := by
  rw [
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_normalizedOutput,
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_normalizedOutput]

theorem postFieldDecodedPrefixScanSourceTape_cells
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.cells (postFieldDecodedPrefixScanSourceTape useAccept L) =
      List.append [none]
        (List.append ((ParsedLayoutBits L).map some)
          (none :: postFieldDecodedPrefixScanPadding useAccept L)) := by
  rw [postFieldDecodedPrefixScanSourceTape,
    rightEdgeScanSourceTapeFromLeft_cells]
  rfl

theorem selectedSegmentLogicalTapeDecoderTargetTape_cells_postFieldDecodedPrefixScanSourceTape_eq_densifierSource
    (useAccept : Bool) (L : DovetailLayout)
    (encodedPrefix : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTargetTape
          (postFieldDecodedPrefixScanSourceTape useAccept L)
          encodedPrefix) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        encodedPrefix (ParsedLayoutBits L)
        (postFieldDecodedPrefixScanPadding useAccept L) := by
  rw [postFieldDecodedPrefixScanSourceTape]
  exact
    selectedSegmentLogicalTapeDecoderTargetTape_cells_rightEdgeScanSourceTapeFromLeft_eq_densifierSource
      encodedPrefix (ParsedLayoutBits L)
      (postFieldDecodedPrefixScanPadding useAccept L)

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

theorem countWindowPostFieldDecodedPrefixStructuredPrefixSelectedSegmentTargetTape_cells
    (useAccept : Bool) (L : DovetailLayout)
    (deletedTail : Word Bool) :
    Tape.cells
        (countWindowPostFieldDecodedPrefixStructuredPrefixSelectedSegmentTargetTape
          useAccept L deletedTail) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        (countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
          useAccept L deletedTail)
        (ParsedLayoutBits L)
        (postFieldDecodedPrefixScanPadding useAccept L) := by
  exact
    selectedSegmentLogicalTapeDecoderTargetTape_cells_postFieldDecodedPrefixScanSourceTape_eq_densifierSource
      useAccept L
      (countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
        useAccept L deletedTail)

theorem countWindowPostFieldDecodedPrefixStructuredPrefixEraserSourceTape_cells
    (useAccept : Bool) (L : DovetailLayout)
    (deletedTail : Word Bool) :
    Tape.cells
        (countWindowPostFieldDecodedPrefixStructuredPrefixEraserSourceTape
          useAccept L deletedTail) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        (countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
          useAccept L deletedTail)
        (ParsedLayoutBits L)
        (postFieldDecodedPrefixScanPadding useAccept L) := by
  exact
    countWindowPostFieldDecodedPrefixStructuredPrefixSelectedSegmentTargetTape_cells
      useAccept L deletedTail

theorem countWindowPostFieldDecodedPrefixStructuredPrefixEraserTargetTape_cells
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.cells
        (countWindowPostFieldDecodedPrefixStructuredPrefixEraserTargetTape
          useAccept L) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        [] (ParsedLayoutBits L)
        (postFieldDecodedPrefixScanPadding useAccept L) := by
  exact
    selectedSegmentLogicalTapeDecoderTargetTape_cells_postFieldDecodedPrefixScanSourceTape_eq_densifierSource
      useAccept L []

def countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorSourceTape
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  selectedSegmentLogicalTapeDecoderTargetTape
    (postFieldDecodedPrefixScanSourceTape useAccept L)
    []

def countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorTargetTape
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  rightEdgeRewindSourceTape (ParsedLayoutBits L)
    (postFieldDecodedPrefixScanPadding useAccept L)

def countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorLeftCells
    (useAccept : Bool) (L : DovetailLayout) : List (Option Bool) :=
  none ::
    List.append
      (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
        (ParsedLayoutBits L)
        (postFieldDecodedPrefixScanPadding useAccept L))
      [none]

theorem countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorVisibleCells_eq_sourceCells
    (useAccept : Bool) (L : DovetailLayout) :
    rightEndCompactionVisibleCells
        (countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorLeftCells
          useAccept L) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        [] (ParsedLayoutBits L)
        (postFieldDecodedPrefixScanPadding useAccept L) := by
  simpa [
    countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorLeftCells,
    selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells] using
    selectedSegmentLogicalTapeDecoderDensifierFootprintVisibleCells_eq_sourceCells
      (ParsedLayoutBits L)
      (postFieldDecodedPrefixScanPadding useAccept L)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorSourceTape_cells
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.cells
        (countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorSourceTape
          useAccept L) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        [] (ParsedLayoutBits L)
        (postFieldDecodedPrefixScanPadding useAccept L) := by
  exact
    selectedSegmentLogicalTapeDecoderTargetTape_cells_postFieldDecodedPrefixScanSourceTape_eq_densifierSource
      useAccept L []

theorem countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorSourceTape_eq_rightEndCompactionSourceTape
    (useAccept : Bool) (L : DovetailLayout) :
    countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorSourceTape
        useAccept L =
      rightEndCompactionSourceTape
        (countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorLeftCells
          useAccept L) := by
  simpa [countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorSourceTape,
    countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorLeftCells,
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape,
    selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells,
    postFieldDecodedPrefixScanSourceTape] using
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape
      (ParsedLayoutBits L)
      (postFieldDecodedPrefixScanPadding useAccept L)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorTargetTape_cells
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.cells
        (countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorTargetTape
          useAccept L) =
      selectedSegmentLogicalTapeDecoderDensifierTargetCells
        (ParsedLayoutBits L)
        (postFieldDecodedPrefixScanPadding useAccept L) := by
  rw [countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorTargetTape,
    selectedSegmentLogicalTapeDecoderDensifierTargetCells]
  exact
    rightEdgeRewindSourceTape_cells
      (ParsedLayoutBits L)
      (postFieldDecodedPrefixScanPadding useAccept L)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorTargetTape_cells_eq_paddingPreserving
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.cells
        (countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorTargetTape
          useAccept L) =
      selectedSegmentLogicalTapeDecoderDensifierPaddingPreservingCells
        (ParsedLayoutBits L)
        (postFieldDecodedPrefixScanPadding useAccept L) := by
  rw [countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorTargetTape_cells]
  rfl

theorem countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorSourceTape_normalizedOutput
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.normalizedOutput
        (countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorSourceTape
          useAccept L) =
      List.append (ParsedLayoutBits L)
        ((postFieldDecodedPrefixScanPadding useAccept L).filterMap
          (fun cell => cell)) := by
  simpa [
    countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorSourceTape] using
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_normalizedOutput
      (ParsedLayoutBits L)
      (postFieldDecodedPrefixScanPadding useAccept L)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorTargetTape_normalizedOutput
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.normalizedOutput
        (countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorTargetTape
          useAccept L) =
      List.append (ParsedLayoutBits L)
        ((postFieldDecodedPrefixScanPadding useAccept L).filterMap
          (fun cell => cell)) := by
  simpa [
    countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorTargetTape] using
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_normalizedOutput
      (ParsedLayoutBits L)
      (postFieldDecodedPrefixScanPadding useAccept L)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactor_normalizedOutput_eq
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.normalizedOutput
        (countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorSourceTape
          useAccept L) =
      Tape.normalizedOutput
        (countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorTargetTape
          useAccept L) := by
  rw [
    countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorSourceTape_normalizedOutput,
    countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorTargetTape_normalizedOutput]

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

theorem countWindowPostFieldDecodedPrefixStructuredPrefixEraserSourceTape_cells_filterMap
    (useAccept : Bool) (L : DovetailLayout)
    (deletedTail : Word Bool) :
    (Tape.cells
        (countWindowPostFieldDecodedPrefixStructuredPrefixEraserSourceTape
          useAccept L deletedTail)).filterMap (fun cell => cell) =
      List.append
        ((countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
          useAccept L deletedTail).filterMap (fun cell => cell))
        (List.append (ParsedLayoutBits L)
          ((postFieldDecodedPrefixScanPadding useAccept L).filterMap
            (fun cell => cell))) := by
  rw [countWindowPostFieldDecodedPrefixStructuredPrefixEraserSourceTape_cells]
  exact
    selectedSegmentLogicalTapeDecoderDensifierSourceCells_filterMap
      (countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
        useAccept L deletedTail)
      (ParsedLayoutBits L)
      (postFieldDecodedPrefixScanPadding useAccept L)

theorem countWindowPostFieldDecodedPrefixStructuredPrefixEraserTargetTape_cells_filterMap
    (useAccept : Bool) (L : DovetailLayout) :
    (Tape.cells
        (countWindowPostFieldDecodedPrefixStructuredPrefixEraserTargetTape
          useAccept L)).filterMap (fun cell => cell) =
      List.append (ParsedLayoutBits L)
        ((postFieldDecodedPrefixScanPadding useAccept L).filterMap
          (fun cell => cell)) := by
  rw [countWindowPostFieldDecodedPrefixStructuredPrefixEraserTargetTape_cells]
  simpa using
    selectedSegmentLogicalTapeDecoderDensifierSourceCells_filterMap
      [] (ParsedLayoutBits L)
      (postFieldDecodedPrefixScanPadding useAccept L)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells_filterMap
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
        bits padding).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  simp [selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells,
    selectedSegmentLogicalTapeDecoderDensifierFootprintCells_filterMap,
    List.filterMap_append]

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintVisibleCells_filterMap
    (bits : Word Bool) (padding : List (Option Bool)) :
    (rightEndCompactionVisibleCells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          bits padding)).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  simp [rightEndCompactionVisibleCells,
    selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells_filterMap,
    List.filterMap_append]

theorem countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorLeftCells_filterMap
    (useAccept : Bool) (L : DovetailLayout) :
    (countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorLeftCells
        useAccept L).filterMap (fun cell => cell) =
      List.append (ParsedLayoutBits L)
        ((postFieldDecodedPrefixScanPadding useAccept L).filterMap
          (fun cell => cell)) := by
  simpa [
    countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorLeftCells,
    selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells] using
    selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells_filterMap
      (ParsedLayoutBits L)
      (postFieldDecodedPrefixScanPadding useAccept L)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorVisibleCells_filterMap
    (useAccept : Bool) (L : DovetailLayout) :
    (rightEndCompactionVisibleCells
        (countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorLeftCells
          useAccept L)).filterMap (fun cell => cell) =
      List.append (ParsedLayoutBits L)
        ((postFieldDecodedPrefixScanPadding useAccept L).filterMap
          (fun cell => cell)) := by
  simpa [
    countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorLeftCells,
    selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells] using
    selectedSegmentLogicalTapeDecoderDensifierFootprintVisibleCells_filterMap
      (ParsedLayoutBits L)
      (postFieldDecodedPrefixScanPadding useAccept L)

theorem selectedSegmentLogicalTapeDecoderDensifierTargetCells_filterMap
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderDensifierTargetCells
        bits padding).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  simp [selectedSegmentLogicalTapeDecoderDensifierTargetCells,
    List.filterMap_append, Function.comp_def]

theorem selectedSegmentLogicalTapeDecoderDensifierPaddingPreservingCells_filterMap
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderDensifierPaddingPreservingCells
        bits padding).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  simp [selectedSegmentLogicalTapeDecoderDensifierPaddingPreservingCells,
    List.filterMap_append, Function.comp_def]

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintCells_filterMap_eq_paddingPreserving
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
        bits padding).filterMap (fun cell => cell) =
      (selectedSegmentLogicalTapeDecoderDensifierPaddingPreservingCells
        bits padding).filterMap (fun cell => cell) := by
  rw [selectedSegmentLogicalTapeDecoderDensifierFootprintCells_filterMap,
    selectedSegmentLogicalTapeDecoderDensifierPaddingPreservingCells_filterMap]

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


end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
