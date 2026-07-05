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

theorem selectedSegmentLogicalTapeDecoderDensifierTargetCells_eq_paddingPreservingCells
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierTargetCells bits padding =
      selectedSegmentLogicalTapeDecoderDensifierPaddingPreservingCells
        bits padding := by
  rfl

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

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_nil
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] padding) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        [] [] padding := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells
      [] padding

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_cons
    (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) padding) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        [] (bit :: rest) padding := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells
      (bit :: rest) padding

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

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape_nil
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] padding =
      rightEndCompactionSourceTape
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          [] padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape
      [] padding

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape_cons
    (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        (bit :: rest) padding =
      rightEndCompactionSourceTape
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          (bit :: rest) padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape
      (bit :: rest) padding

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

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_nil
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] padding) =
      selectedSegmentLogicalTapeDecoderDensifierPaddingPreservingCells
        [] padding := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells
      [] padding

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_cons
    (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) padding) =
      selectedSegmentLogicalTapeDecoderDensifierPaddingPreservingCells
        (bit :: rest) padding := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells
      (bit :: rest) padding

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

theorem countWindowPostFieldDecodedPrefixStructuredPrefixSelectedSegmentTargetTape_normalizedOutput
    (useAccept : Bool) (L : DovetailLayout)
    (deletedTail : Word Bool) :
    Tape.normalizedOutput
        (countWindowPostFieldDecodedPrefixStructuredPrefixSelectedSegmentTargetTape
          useAccept L deletedTail) =
      List.append
        ((countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
          useAccept L deletedTail).filterMap (fun cell => cell))
        (List.append (ParsedLayoutBits L)
          ((postFieldDecodedPrefixScanPadding useAccept L).filterMap
            (fun cell => cell))) := by
  rw [countWindowPostFieldDecodedPrefixStructuredPrefixSelectedSegmentTargetTape]
  rw [selectedSegmentLogicalTapeDecoderTargetTape_normalizedOutput]
  rw [postFieldDecodedPrefixScanSourceTape_normalizedOutput]

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
  exact
    selectedSegmentLogicalTapeDecoderDensifierTargetCells_eq_paddingPreservingCells
      (ParsedLayoutBits L)
      (postFieldDecodedPrefixScanPadding useAccept L)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorSourceTape_normalizedOutput
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.normalizedOutput
        (countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorSourceTape
          useAccept L) =
      List.append (ParsedLayoutBits L)
        ((postFieldDecodedPrefixScanPadding useAccept L).filterMap
          (fun cell => cell)) := by
  rw [countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorSourceTape]
  rw [selectedSegmentLogicalTapeDecoderTargetTape_normalizedOutput]
  rw [postFieldDecodedPrefixScanSourceTape_normalizedOutput]
  rfl

theorem countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorTargetTape_normalizedOutput
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.normalizedOutput
        (countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorTargetTape
          useAccept L) =
      List.append (ParsedLayoutBits L)
        ((postFieldDecodedPrefixScanPadding useAccept L).filterMap
          (fun cell => cell)) := by
  rw [countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorTargetTape]
  exact
    rightEdgeRewindSourceTape_normalizedOutput
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

theorem rightEdgeRewindSourceTape_cells_eq_densifierTarget
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.cells (rightEdgeRewindSourceTape bits padding) =
      selectedSegmentLogicalTapeDecoderDensifierTargetCells
        bits padding := by
  rw [selectedSegmentLogicalTapeDecoderDensifierTargetCells]
  exact rightEdgeRewindSourceTape_cells bits padding

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

theorem selectedSegmentLogicalTapeDecoderCellCells_filterMap_flatten
    (cells : List (Option Bool)) :
    (cells.map
        (fun cell =>
          (selectedSegmentLogicalTapeDecoderCellCells cell).filterMap
            (fun cell => cell))).flatten =
      cells.filterMap (fun cell => cell) := by
  simpa [selectedSegmentLogicalTapeDecoderCellCells_filterMap] using
    option_toList_flatten_eq_filterMap cells

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

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixSpec
    (decoder : MachineDescription) : Prop :=
  decoder.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout)
      (deletedTail : Word Bool),
      decoder.HaltsFromTapeEquiv
        (tapeAtEncodedSplit
          (countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
            useAccept L deletedTail)
          (encodedStructuredTapeCells
            [guardLogicalTape
              (postFieldDecodedPrefixScanSourceTape useAccept L)]))
        (postFieldDecodedPrefixScanSourceTape useAccept L)

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction :
    Prop :=
  exists decoder : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixSpec
      decoder

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

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout)
      (deletedTail : Word Bool),
      cleanup.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTargetTape
          (postFieldDecodedPrefixScanSourceTape useAccept L)
          (countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
            useAccept L deletedTail))
        (postFieldDecodedPrefixScanSourceTape useAccept L)

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction :
    Prop :=
  exists cleanup : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupSpec
      cleanup

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierSpec
    (densifier : MachineDescription) : Prop :=
  densifier.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout)
      (encodedPrefix : List (Option Bool)),
      densifier.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTargetTape
          (postFieldDecodedPrefixScanSourceTape useAccept L)
          encodedPrefix)
        (rightEdgeRewindSourceTape (ParsedLayoutBits L)
          (postFieldDecodedPrefixScanPadding useAccept L))

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierConstruction :
    Prop :=
  exists densifier : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierSpec
      densifier

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierSpec
    (densifier : MachineDescription) : Prop :=
  densifier.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout)
      (deletedTail : Word Bool),
      densifier.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTargetTape
          (postFieldDecodedPrefixScanSourceTape useAccept L)
          (countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
            useAccept L deletedTail))
        (rightEdgeRewindSourceTape (ParsedLayoutBits L)
          (postFieldDecodedPrefixScanPadding useAccept L))

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction :
    Prop :=
  exists densifier : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierSpec
      densifier

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout)
      (encodedPrefix : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTargetTape
          (postFieldDecodedPrefixScanSourceTape useAccept L)
          encodedPrefix)
        (selectedSegmentLogicalTapeDecoderTargetTape
          (postFieldDecodedPrefixScanSourceTape useAccept L)
          [])

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction :
    Prop :=
  exists eraser : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserSpec
      eraser

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout)
      (deletedTail : Word Bool),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTargetTape
          (postFieldDecodedPrefixScanSourceTape useAccept L)
          (countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
            useAccept L deletedTail))
        (selectedSegmentLogicalTapeDecoderTargetTape
          (postFieldDecodedPrefixScanSourceTape useAccept L)
          [])

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserConstruction :
    Prop :=
  exists eraser : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserSpec
      eraser

def SelectedSegmentLogicalTapeDecoderFootprintCompactorSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    forall (bits : Word Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          bits padding)
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          bits padding)

def SelectedSegmentLogicalTapeDecoderFootprintCompactorConstruction :
    Prop :=
  exists compactor : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintCompactorSpec compactor

def SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    (forall padding : List (Option Bool),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] padding)
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] padding)) ∧
    forall (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) padding)
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) padding)

def SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction :
    Prop :=
  exists compactor : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseSpec compactor

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout),
      compactor.HaltsFromTapeEquiv
        (countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorSourceTape
          useAccept L)
        (countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorTargetTape
          useAccept L)

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction :
    Prop :=
  exists compactor : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorSpec
      compactor

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierComponentsConstruction :
    Prop :=
  CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction ∧
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierComponentsConstruction :
    Prop :=
  CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserConstruction ∧
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction

def countWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierDescription
    (eraser compactor : MachineDescription) : MachineDescription :=
  canonicalSeqDescription eraser compactor

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierDescription_subroutineReady
    {eraser compactor : MachineDescription}
    (heraser : eraser.SubroutineReady)
    (hcompactor : compactor.SubroutineReady) :
    (countWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierDescription
      eraser compactor).SubroutineReady :=
  canonicalSeqDescription_subroutineReady heraser hcompactor

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierConstruction_of_components
    (hcomponents :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierComponentsConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierConstruction := by
  rcases hcomponents with
    ⟨⟨eraser, heraserReady, heraserRun⟩,
      ⟨compactor, hcompactorReady, hcompactorRun⟩⟩
  refine
    ⟨countWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierDescription
      eraser compactor, ?_⟩
  constructor
  · exact
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierDescription_subroutineReady
        heraserReady hcompactorReady
  · intro useAccept L encodedPrefix
    let Tmid :=
      selectedSegmentLogicalTapeDecoderTargetTape
        (postFieldDecodedPrefixScanSourceTape useAccept L)
        []
    have hcompactorFromBridge :
        compactor.HaltsFromTapeEquiv
          (Tape.move Direction.left (Tape.move Direction.right Tmid))
          (rightEdgeRewindSourceTape (ParsedLayoutBits L)
            (postFieldDecodedPrefixScanPadding useAccept L)) := by
      rcases hcompactorRun useAccept L with
        ⟨Tactual, hactual, hactualEquiv⟩
      rcases
        HaltsFromTapeEquiv_of_input_equiv
          (D := compactor)
          (Tin := Tmid)
          (Tin' :=
            Tape.move Direction.left (Tape.move Direction.right Tmid))
          (selectedSegmentLogicalTapeDecoderTargetTape_move_left_move_right_equiv
            (postFieldDecodedPrefixScanSourceTape useAccept L) [])
          hactual with
        ⟨Ttransported, htransported, htransportedEquiv⟩
      exact
        ⟨Ttransported, htransported,
          Tape.Equiv.trans htransportedEquiv hactualEquiv⟩
    exact
      canonicalSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv
        heraserReady
        hcompactorReady
        (heraserRun useAccept L encodedPrefix)
        rfl
        hcompactorFromBridge

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction_of_components
    (hcomponents :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierComponentsConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction := by
  rcases hcomponents with
    ⟨⟨eraser, heraserReady, heraserRun⟩,
      ⟨compactor, hcompactorReady, hcompactorRun⟩⟩
  refine
    ⟨countWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierDescription
      eraser compactor, ?_⟩
  constructor
  · exact
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierDescription_subroutineReady
        heraserReady hcompactorReady
  · intro useAccept L deletedTail
    let Tmid :=
      selectedSegmentLogicalTapeDecoderTargetTape
        (postFieldDecodedPrefixScanSourceTape useAccept L)
        []
    have hcompactorFromBridge :
        compactor.HaltsFromTapeEquiv
          (Tape.move Direction.left (Tape.move Direction.right Tmid))
          (rightEdgeRewindSourceTape (ParsedLayoutBits L)
            (postFieldDecodedPrefixScanPadding useAccept L)) := by
      rcases hcompactorRun useAccept L with
        ⟨Tactual, hactual, hactualEquiv⟩
      rcases
        HaltsFromTapeEquiv_of_input_equiv
          (D := compactor)
          (Tin := Tmid)
          (Tin' :=
            Tape.move Direction.left (Tape.move Direction.right Tmid))
          (selectedSegmentLogicalTapeDecoderTargetTape_move_left_move_right_equiv
            (postFieldDecodedPrefixScanSourceTape useAccept L) [])
          hactual with
        ⟨Ttransported, htransported, htransportedEquiv⟩
      exact
        ⟨Ttransported, htransported,
          Tape.Equiv.trans htransportedEquiv hactualEquiv⟩
    exact
      canonicalSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv
        heraserReady
        hcompactorReady
        (heraserRun useAccept L deletedTail)
        rfl
        hcompactorFromBridge

def countWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupDescription
    (densifier : MachineDescription) : MachineDescription :=
  canonicalSeqDescription densifier rightEdgeRewindDescription

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupDescription_subroutineReady
    {densifier : MachineDescription}
    (hdensifier : densifier.SubroutineReady) :
    (countWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupDescription
      densifier).SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    hdensifier rightEdgeRewindDescription_subroutineReady

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupConstruction_of_densifier
    (hdensifier :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupConstruction := by
  rcases hdensifier with
    ⟨densifier, hdensifierReady, hdensifierRun⟩
  refine
    ⟨countWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupDescription
      densifier, ?_⟩
  constructor
  · exact
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupDescription_subroutineReady
        hdensifierReady
  · intro useAccept L encodedPrefix
    have hbridge :
        Tape.move Direction.left
            (Tape.move Direction.right
              (rightEdgeRewindSourceTape (ParsedLayoutBits L)
                (postFieldDecodedPrefixScanPadding useAccept L))) =
          rightEdgeRewindSourceTape (ParsedLayoutBits L)
            (postFieldDecodedPrefixScanPadding useAccept L) := by
      simpa [postFieldDecodedPrefixScanPadding] using
        rightEdgeRewindSourceTape_move_left_move_right_padding_cons
          (ParsedLayoutBits L) (none : Option Bool)
          (List.append
            (List.replicate
              (selectedProjectionPaddedTailCleanupScratchCountBits
                useAccept L).length
              (none : Option Bool))
            (selectedProjectionPaddedTailCleanupPostCountTailCells
              useAccept L 0))
    have hrewind :
        rightEdgeRewindDescription.HaltsFromTapeEquiv
          (rightEdgeRewindSourceTape (ParsedLayoutBits L)
            (postFieldDecodedPrefixScanPadding useAccept L))
          (postFieldDecodedPrefixScanSourceTape useAccept L) := by
      simpa [postFieldDecodedPrefixScanSourceTape,
        rightEdgeRewindTargetTape, rightEdgeScanSourceTapeFromLeft] using
        (rightEdgeRewindDescription_haltsFromTape
          (ParsedLayoutBits L)
          (postFieldDecodedPrefixScanPadding useAccept L)).toEquiv
    exact
      canonicalSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv
        hdensifierReady
        rightEdgeRewindDescription_subroutineReady
        (hdensifierRun useAccept L encodedPrefix)
        hbridge
        hrewind

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction_of_densifier
    (hdensifier :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction := by
  rcases hdensifier with
    ⟨densifier, hdensifierReady, hdensifierRun⟩
  refine
    ⟨countWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupDescription
      densifier, ?_⟩
  constructor
  · exact
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupDescription_subroutineReady
        hdensifierReady
  · intro useAccept L deletedTail
    have hbridge :
        Tape.move Direction.left
            (Tape.move Direction.right
              (rightEdgeRewindSourceTape (ParsedLayoutBits L)
                (postFieldDecodedPrefixScanPadding useAccept L))) =
          rightEdgeRewindSourceTape (ParsedLayoutBits L)
            (postFieldDecodedPrefixScanPadding useAccept L) := by
      simpa [postFieldDecodedPrefixScanPadding] using
        rightEdgeRewindSourceTape_move_left_move_right_padding_cons
          (ParsedLayoutBits L) (none : Option Bool)
          (List.append
            (List.replicate
              (selectedProjectionPaddedTailCleanupScratchCountBits
                useAccept L).length
              (none : Option Bool))
            (selectedProjectionPaddedTailCleanupPostCountTailCells
              useAccept L 0))
    have hrewind :
        rightEdgeRewindDescription.HaltsFromTapeEquiv
          (rightEdgeRewindSourceTape (ParsedLayoutBits L)
            (postFieldDecodedPrefixScanPadding useAccept L))
          (postFieldDecodedPrefixScanSourceTape useAccept L) := by
      simpa [postFieldDecodedPrefixScanSourceTape,
        rightEdgeRewindTargetTape, rightEdgeScanSourceTapeFromLeft] using
        (rightEdgeRewindDescription_haltsFromTape
          (ParsedLayoutBits L)
          (postFieldDecodedPrefixScanPadding useAccept L)).toEquiv
    exact
      canonicalSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv
        hdensifierReady
        rightEdgeRewindDescription_subroutineReady
        (hdensifierRun useAccept L deletedTail)
        hbridge
        hrewind

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

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction_of_cleanup
    (hcleanup :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction := by
  rcases hcleanup with
    ⟨cleanup, hcleanupReady, hcleanupRun⟩
  refine
    ⟨selectedSegmentLogicalTapeDecoderPipelineDescription cleanup,
      ?_⟩
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderPipelineDescription_subroutineReady
        hcleanupReady
  · intro useAccept L deletedTail
    let encodedPrefix :=
      countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
        useAccept L deletedTail
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
        (hcleanupRun useAccept L deletedTail)

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

theorem countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_of_structuredPrefixSelectedSegmentDecoder
    (hdecoder :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction := by
  rcases hdecoder with ⟨decoder, hdecoderReady, hdecoderRun⟩
  refine ⟨decoder, hdecoderReady, ?_⟩
  intro useAccept L deletedTail physical hseparator
  rcases hseparator with ⟨_hindex, hphysical⟩
  rw [hphysical]
  simpa [encodedSuffixFromTape, guardLogicalTapes,
    countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix] using
    hdecoderRun useAccept L deletedTail

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierComponentsConstruction_of_parts
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hfootprint :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierComponentsConstruction :=
  ⟨hprefix, hfootprint⟩

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction_of_generic
    (hgeneric :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction := by
  rcases hgeneric with ⟨compactor, hready, hrun⟩
  refine ⟨compactor, hready, ?_⟩
  intro useAccept L
  simpa [
    countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorSourceTape,
    countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorTargetTape,
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape,
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape,
    postFieldDecodedPrefixScanSourceTape] using
    hrun (ParsedLayoutBits L)
      (postFieldDecodedPrefixScanPadding useAccept L)

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorConstruction_of_cases
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorConstruction := by
  rcases hcases with ⟨compactor, hready, hnil, hcons⟩
  refine ⟨compactor, hready, ?_⟩
  intro bits padding
  cases bits with
  | nil =>
      exact hnil padding
  | cons bit rest =>
      exact hcons bit rest padding

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction_core :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction := by
  sorry

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorConstruction_core :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorConstruction := by
  exact
    selectedSegmentLogicalTapeDecoderFootprintCompactorConstruction_of_cases
      selectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction_core


theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction_core :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction := by
  exact
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction_of_generic
      selectedSegmentLogicalTapeDecoderFootprintCompactorConstruction_core

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserConstruction_core :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserConstruction := by
  sorry

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierComponentsConstruction_core :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierComponentsConstruction := by
  exact
    ⟨countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserConstruction_core,
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction_core⟩

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction_core :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction := by
  exact
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction_of_components
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierComponentsConstruction_core

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction_core :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction := by
  exact
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction_of_densifier
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction_core

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction_core :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction :=
  countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction_of_cleanup
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction_core

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
    countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_of_structuredPrefixSelectedSegmentDecoder
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction_core

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
