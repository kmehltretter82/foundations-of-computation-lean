import FoC.Computability.ListLemmas
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.FixedSkips
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawEncoder.RawBoundaryRightEdgeEmitter.EndpointSupport

set_option doc.verso true

/-!
# Raw-boundary right-edge cell-suffix loop support

This module packages the reusable one-step shape for the raw-boundary
cell-suffix loop.  It starts at the left edge of an already-emitted cell suffix,
pulls the nearest remaining raw bit across the scratch gap, emits that bit's
cell chunk immediately before the suffix, and halts at the new suffix left edge.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf

namespace CommonGround
namespace FiniteTransducers
namespace CountWindowRawSourceEncoder
namespace RawBoundaryRightEdgeEmitter

def cellSuffixLeftEdgeWithBase
    (baseLeft : List (Option Bool)) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells baseLeft
    (List.append
      ((preservingCellPassCellBits cellSuffix).map some)
      (some tailFirst :: tail))

def cellSuffixRightEdgeWithBase
    (baseLeft : List (Option Bool)) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append
      ((preservingCellPassCellBits cellSuffix).reverse.map some)
      baseLeft)
    (some tailFirst :: tail)

def tailHeadEmittedCellSuffixLeftEdgeTape
    (pref count cellSuffix : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate count.length (none : Option Bool))
      (List.append (pref.reverse.map some) [none]))
    (List.append
      ((preservingCellPassCellBits cellSuffix).map some)
      (some tailFirst :: tail))

def tailHeadEmittedCellSuffixRightEdgeScratchTape
    (pref : Word Bool) (scratchTail : Nat) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) : Tape Bool :=
  cellSuffixRightEdgeWithBase
    (List.append
      (List.replicate scratchTail (none : Option Bool))
      (List.append (pref.reverse.map some) [none]))
    cellSuffix tailFirst tail

def tailHeadEmittedCellSuffixLeftEdgeScratchTape
    (pref : Word Bool) (scratchTail : Nat) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate scratchTail (none : Option Bool))
      (List.append (pref.reverse.map some) [none]))
    (List.append
      ((preservingCellPassCellBits cellSuffix).map some)
      (some tailFirst :: tail))

theorem tailHeadEmittedCellSuffixLeftEdgeScratchTape_eq_cellSuffixLeftEdgeWithBase
    (pref : Word Bool) (scratchTail : Nat) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    tailHeadEmittedCellSuffixLeftEdgeScratchTape
        pref scratchTail cellSuffix tailFirst tail =
      cellSuffixLeftEdgeWithBase
        (List.append
          (List.replicate scratchTail (none : Option Bool))
          (List.append (pref.reverse.map some) [none]))
        cellSuffix tailFirst tail := by
  rfl

theorem tailHeadEmittedCellSuffixLeftEdgeTape_cells
    (pref count cellSuffix : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.cells
        (tailHeadEmittedCellSuffixLeftEdgeTape
          pref count cellSuffix tailFirst tail) =
      none ::
        List.append (pref.map some)
          (List.append
            (List.replicate count.length (none : Option Bool))
              (List.append
              ((preservingCellPassCellBits cellSuffix).map some)
              (some tailFirst :: tail))) := by
  cases cellSuffix with
  | nil =>
      simp [tailHeadEmittedCellSuffixLeftEdgeTape, Tape.cells, tapeAtCells,
        preservingCellPassCellBits, List.map_reverse, List.append_assoc]
  | cons bit rest =>
      cases bit <;>
        simp [tailHeadEmittedCellSuffixLeftEdgeTape, Tape.cells,
          tapeAtCells, preservingCellPassCellBits,
          preservingCellPassZeroBits, preservingCellPassOneBits,
          List.map_reverse, List.append_assoc]

theorem tailHeadEmittedCellSuffixLeftEdgeScratchTape_cells
    (pref : Word Bool) (scratchTail : Nat) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    Tape.cells
        (tailHeadEmittedCellSuffixLeftEdgeScratchTape
          pref scratchTail cellSuffix tailFirst tail) =
      none ::
        List.append (pref.map some)
          (List.append
            (List.replicate scratchTail (none : Option Bool))
              (List.append
              ((preservingCellPassCellBits cellSuffix).map some)
              (some tailFirst :: tail))) := by
  cases cellSuffix with
  | nil =>
      simp [tailHeadEmittedCellSuffixLeftEdgeScratchTape, Tape.cells,
        tapeAtCells, preservingCellPassCellBits, List.map_reverse,
        List.append_assoc]
  | cons bit rest =>
      cases bit <;>
        simp [tailHeadEmittedCellSuffixLeftEdgeScratchTape, Tape.cells,
          tapeAtCells, preservingCellPassCellBits,
          preservingCellPassZeroBits, preservingCellPassOneBits,
          List.map_reverse, List.append_assoc]

theorem tailHeadEmittedCellSuffixLeftEdgeScratchTape_left_length
    (pref : Word Bool) (scratchTail : Nat) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    (tailHeadEmittedCellSuffixLeftEdgeScratchTape
      pref scratchTail cellSuffix tailFirst tail).left.length =
      scratchTail + pref.length + 1 := by
  cases cellSuffix with
  | nil =>
      simp [tailHeadEmittedCellSuffixLeftEdgeScratchTape, tapeAtCells,
        preservingCellPassCellBits, List.length_append, Nat.add_assoc]
  | cons bit rest =>
      cases bit <;>
        simp [tailHeadEmittedCellSuffixLeftEdgeScratchTape, tapeAtCells,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, List.length_append, Nat.add_assoc]

theorem tailHeadEmittedNearestRawBitCellLeftEdgeTape_eq_cellSuffixLeftEdge_singleton
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    tailHeadEmittedNearestRawBitCellLeftEdgeTape
        pref count rawBit tailFirst tail =
      tailHeadEmittedCellSuffixLeftEdgeTape
        pref count [rawBit] tailFirst tail := by
  cases rawBit <;>
    simp [tailHeadEmittedNearestRawBitCellLeftEdgeTape,
      tailHeadEmittedCellSuffixLeftEdgeTape,
      preservingCellPassCellBits, preservingCellPassZeroBits,
      preservingCellPassOneBits, pulledRawBitCellChunkBits]

theorem tailHeadEmittedThirdRawBitCellBeforeTwoEmittedCellsLeftEdgeTape_eq_cellSuffixLeftEdgeScratch
    (pref : Word Bool) (scratchTail : Nat)
    (thirdRawBit secondRawBit firstRawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    tailHeadEmittedThirdRawBitCellBeforeTwoEmittedCellsLeftEdgeTape
        pref scratchTail thirdRawBit secondRawBit firstRawBit
        tailFirst tail =
      tailHeadEmittedCellSuffixLeftEdgeScratchTape
        pref scratchTail [thirdRawBit, secondRawBit, firstRawBit]
        tailFirst tail := by
  cases thirdRawBit <;> cases secondRawBit <;> cases firstRawBit <;>
    simp [tailHeadEmittedThirdRawBitCellBeforeTwoEmittedCellsLeftEdgeTape,
      tailHeadEmittedCellSuffixLeftEdgeScratchTape,
      preservingCellPassCellBits, preservingCellPassZeroBits,
      preservingCellPassOneBits, pulledRawBitCellChunkBits]

theorem tailHeadHandoffTape_moveLeft_eq_localGapCompactorSource
    (skipped count pref : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) :
    Tape.move Direction.left
        (tailHeadHandoffTape skipped count tailFirst tail) =
      rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
        ([] : List (Option Bool)) rawBit pref.reverse
        (count.length + 2) (some tailFirst :: tail) := by
  rw [tailHeadHandoffTape_eq_tapeAtCells_scratchBase]
  rw [tailHeadRawBaseLeft_eq_splitLast skipped count pref rawBit hlayout]
  simp [tailHeadImmediateScratchCellCount,
    rightBlankLocalGapCompactorSourceTapeWithBaseAndRight,
    tapeAtCells, Tape.move, Tape.moveLeft, List.replicate_succ]

def tailHeadOneGapCompactedTape
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  leadingBlankLeftShiftTargetTapeWithPadding
    ([] : List (Option Bool)) (List.append pref [rawBit])
    (List.append
      (List.replicate (count.length + 2) (none : Option Bool))
      (some tailFirst :: tail))

theorem tailHeadOneGapCompactedTape_cells
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.cells
        (tailHeadOneGapCompactedTape
          pref count rawBit tailFirst tail) =
      List.append ((List.append pref [rawBit]).map some)
        (List.append [none, none]
          (List.append
            (List.replicate (count.length + 2)
              (none : Option Bool))
            (some tailFirst :: tail))) := by
  rw [tailHeadOneGapCompactedTape,
    leadingBlankLeftShiftTargetTapeWithPadding_cells]
  rw [show count.length + 2 = Nat.succ (count.length + 1) by
    lia]
  simp [leadingBlankLeftShiftTargetCellsWithPadding,
    leadingBlankLeftShiftTargetVisiblePadding, List.replicate_succ,
    List.append_assoc]

theorem tailHeadOneGapCompactedTape_normalizedOutput
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.normalizedOutput
        (tailHeadOneGapCompactedTape
          pref count rawBit tailFirst tail) =
      List.append (List.append pref [rawBit])
        (tailFirst :: tail.filterMap (fun cell => cell)) := by
  rw [tailHeadOneGapCompactedTape,
    leadingBlankLeftShiftTargetTapeWithPadding_normalizedOutput]
  simp [List.filterMap_append]

def tailHeadLocalGapCompactorDescription : MachineDescription :=
  canonicalSeqDescription
    leftMoveOnceDescription
    rightBlankLocalGapCompactorDescription

theorem tailHeadLocalGapCompactorDescription_subroutineReady :
    tailHeadLocalGapCompactorDescription.SubroutineReady := by
  rw [tailHeadLocalGapCompactorDescription]
  exact
    canonicalSeqDescription_subroutineReady
      leftMoveOnceDescription_subroutineReady
      rightBlankLocalGapCompactorDescription_subroutineReady

theorem tailHeadLocalGapCompactorDescription_haltsFrom_tailHeadHandoffTape
    (skipped count pref : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) :
    tailHeadLocalGapCompactorDescription.HaltsFromTape
      (tailHeadHandoffTape skipped count tailFirst tail)
      (tailHeadOneGapCompactedTape pref count rawBit tailFirst tail) := by
  rw [tailHeadLocalGapCompactorDescription]
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      leftMoveOnceDescription_subroutineReady
      rightBlankLocalGapCompactorDescription_subroutineReady
      (leftMoveOnceDescription_haltsFromTape
        (tailHeadHandoffTape skipped count tailFirst tail))
      (by
        rw [tailHeadHandoffTape_moveLeft_eq_localGapCompactorSource
          skipped count pref rawBit tailFirst tail hlayout])
      (by
        have hcompact :=
          rightBlankLocalGapCompactorDescription_haltsFromTapeWithBase_leftStack_rightPadding
            ([] : List (Option Bool)) rawBit pref.reverse
            (count.length + 2) (some tailFirst) tail
        simpa [tailHeadOneGapCompactedTape, List.reverse_cons,
          List.append_assoc] using hcompact)

theorem sourceFirstThreeRawBitCellsLeftEdgeEmissionDescription_haltsFrom_sourceTape_cellSuffixLeftEdge_of_count_lengths
    (skipped count pref : Word Bool) (scratchOne scratchTail : Nat)
    (thirdRawBit secondRawBit firstRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count =
        List.append
          (List.append (List.append pref [thirdRawBit]) [secondRawBit])
          [firstRawBit])
    (hcount : count.length = scratchOne + 3)
    (hscratch : scratchOne = scratchTail + 3) :
    sourceFirstThreeRawBitCellsLeftEdgeEmissionDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape
        pref scratchTail [thirdRawBit, secondRawBit, firstRawBit]
        tailFirst tail) := by
  simpa
      [tailHeadEmittedThirdRawBitCellBeforeTwoEmittedCellsLeftEdgeTape_eq_cellSuffixLeftEdgeScratch]
    using
      sourceFirstThreeRawBitCellsLeftEdgeEmissionDescription_haltsFrom_sourceTape_of_count_lengths
        skipped count pref scratchOne scratchTail thirdRawBit secondRawBit
        firstRawBit tailFirst tail hlayout hcount hscratch

theorem pullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_cellSuffixLeftEdge_of_count_length
    (pref count cellSuffix : Word Bool) (scratchTail : Nat)
    (rawBit tailFirst : Bool) (tail : List (Option Bool))
    (hcount : count.length = scratchTail + 3) :
    pullEmitAndMoveRawBitCellLeftEdgeDescription.HaltsFromTape
      (tailHeadEmittedCellSuffixLeftEdgeTape
        (List.append pref [rawBit]) count cellSuffix tailFirst tail)
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape
        pref scratchTail (rawBit :: cellSuffix) tailFirst tail) := by
  cases cellSuffix with
  | nil =>
      cases rawBit <;> cases tailFirst
      · simpa [tailHeadEmittedCellSuffixLeftEdgeTape,
          tailHeadEmittedCellSuffixLeftEdgeScratchTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          hcount, List.reverse_append, List.map_reverse,
          List.append_assoc] using
          pullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_headGap
            scratchTail
            (List.append (pref.reverse.map some) [none])
            false false tail
      · simpa [tailHeadEmittedCellSuffixLeftEdgeTape,
          tailHeadEmittedCellSuffixLeftEdgeScratchTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          hcount, List.reverse_append, List.map_reverse,
          List.append_assoc] using
          pullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_headGap
            scratchTail
            (List.append (pref.reverse.map some) [none])
            false true tail
      · simpa [tailHeadEmittedCellSuffixLeftEdgeTape,
          tailHeadEmittedCellSuffixLeftEdgeScratchTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          hcount, List.reverse_append, List.map_reverse,
          List.append_assoc] using
          pullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_headGap
            scratchTail
            (List.append (pref.reverse.map some) [none])
            true false tail
      · simpa [tailHeadEmittedCellSuffixLeftEdgeTape,
          tailHeadEmittedCellSuffixLeftEdgeScratchTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          hcount, List.reverse_append, List.map_reverse,
          List.append_assoc] using
          pullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_headGap
            scratchTail
            (List.append (pref.reverse.map some) [none])
            true true tail
  | cons suffixHead suffixRest =>
      cases rawBit <;> cases suffixHead
      · simpa [tailHeadEmittedCellSuffixLeftEdgeTape,
          tailHeadEmittedCellSuffixLeftEdgeScratchTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          hcount, List.reverse_append, List.map_reverse,
          List.append_assoc] using
          pullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_headGap
            scratchTail
            (List.append (pref.reverse.map some) [none])
            false false
            (some true :: some false :: some true ::
              List.append ((preservingCellPassCellBits suffixRest).map some)
              (some tailFirst :: tail))
      · simpa [tailHeadEmittedCellSuffixLeftEdgeTape,
          tailHeadEmittedCellSuffixLeftEdgeScratchTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          hcount, List.reverse_append, List.map_reverse,
          List.append_assoc] using
          pullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_headGap
            scratchTail
            (List.append (pref.reverse.map some) [none])
            false false
            (some true :: some true :: some false ::
              List.append ((preservingCellPassCellBits suffixRest).map some)
              (some tailFirst :: tail))
      · simpa [tailHeadEmittedCellSuffixLeftEdgeTape,
          tailHeadEmittedCellSuffixLeftEdgeScratchTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          hcount, List.reverse_append, List.map_reverse,
          List.append_assoc] using
          pullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_headGap
            scratchTail
            (List.append (pref.reverse.map some) [none])
            true false
            (some true :: some false :: some true ::
              List.append ((preservingCellPassCellBits suffixRest).map some)
              (some tailFirst :: tail))
      · simpa [tailHeadEmittedCellSuffixLeftEdgeTape,
          tailHeadEmittedCellSuffixLeftEdgeScratchTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          hcount, List.reverse_append, List.map_reverse,
          List.append_assoc] using
          pullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_headGap
            scratchTail
            (List.append (pref.reverse.map some) [none])
            true false
            (some true :: some true :: some false ::
              List.append ((preservingCellPassCellBits suffixRest).map some)
              (some tailFirst :: tail))

theorem pullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_cellSuffixLeftEdgeScratch_of_scratch_length
    (pref cellSuffix : Word Bool) (currentScratch scratchTail : Nat)
    (rawBit tailFirst : Bool) (tail : List (Option Bool))
    (hscratch : currentScratch = scratchTail + 3) :
    pullEmitAndMoveRawBitCellLeftEdgeDescription.HaltsFromTape
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape
        (List.append pref [rawBit]) currentScratch cellSuffix tailFirst tail)
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape
        pref scratchTail (rawBit :: cellSuffix) tailFirst tail) := by
  have hcount :
      (List.replicate currentScratch false : Word Bool).length =
        scratchTail + 3 := by
    simp [hscratch]
  simpa [tailHeadEmittedCellSuffixLeftEdgeTape,
    tailHeadEmittedCellSuffixLeftEdgeScratchTape] using
    pullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_cellSuffixLeftEdge_of_count_length
      pref (List.replicate currentScratch false : Word Bool) cellSuffix
      scratchTail rawBit tailFirst tail hcount

theorem tailHeadEmittedCellSuffixLeftEdgeScratchTape_moveLeftRight
    (pref : Word Bool) (scratchTail : Nat) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tailHeadEmittedCellSuffixLeftEdgeScratchTape
            pref scratchTail cellSuffix tailFirst tail)) =
      tailHeadEmittedCellSuffixLeftEdgeScratchTape
        pref scratchTail cellSuffix tailFirst tail := by
  rw [tailHeadEmittedCellSuffixLeftEdgeScratchTape]
  simpa [List.append_assoc] using
    tapeAtCells_move_right_move_left_append_singleton
      (List.append (List.replicate scratchTail (none : Option Bool))
        (pref.reverse.map some))
      none
      (List.append ((preservingCellPassCellBits cellSuffix).map some)
        (some tailFirst :: tail))

theorem cellSuffixLeftEdgeWithBase_moveLeftRight_after_cell
    (baseLeft : List (Option Bool)) (bit : Bool) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (cellSuffixLeftEdgeWithBase
            (List.append
              ((pulledRawBitCellChunkBits bit).reverse.map some)
              baseLeft)
            cellSuffix tailFirst tail)) =
      cellSuffixLeftEdgeWithBase
        (List.append
          ((pulledRawBitCellChunkBits bit).reverse.map some)
          baseLeft)
        cellSuffix tailFirst tail := by
  cases bit
  · simpa [cellSuffixLeftEdgeWithBase, pulledRawBitCellChunkBits,
      preservingCellPassZeroBits, List.append_assoc] using
      tapeAtCells_move_right_move_left_append_cons
        ([] : List (Option Bool))
        (some false :: some true :: some false :: baseLeft)
        (List.append ((preservingCellPassCellBits cellSuffix).map some)
          (some tailFirst :: tail))
        (some true)
  · simpa [cellSuffixLeftEdgeWithBase, pulledRawBitCellChunkBits,
      preservingCellPassOneBits, List.append_assoc] using
      tapeAtCells_move_right_move_left_append_cons
        ([] : List (Option Bool))
        (some true :: some true :: some false :: baseLeft)
        (List.append ((preservingCellPassCellBits cellSuffix).map some)
          (some tailFirst :: tail))
        (some false)

theorem rightMoveAcrossFourBitsDescription_haltsFrom_cellSuffixLeftEdgeWithBase_cons
    (baseLeft : List (Option Bool)) (bit : Bool) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    rightMoveAcrossFourBitsDescription.HaltsFromTape
      (cellSuffixLeftEdgeWithBase
        baseLeft (bit :: cellSuffix) tailFirst tail)
      (cellSuffixLeftEdgeWithBase
        (List.append
          ((pulledRawBitCellChunkBits bit).reverse.map some)
          baseLeft)
        cellSuffix tailFirst tail) := by
  cases bit
  · simpa [cellSuffixLeftEdgeWithBase, preservingCellPassCellBits,
      preservingCellPassZeroBits, pulledRawBitCellChunkBits,
      List.map_append, List.append_assoc] using
      rightMoveAcrossFourBitsDescription_haltsFromTape_bits
        false true false true baseLeft
        (List.append ((preservingCellPassCellBits cellSuffix).map some)
          (some tailFirst :: tail))
  · simpa [cellSuffixLeftEdgeWithBase, preservingCellPassCellBits,
      preservingCellPassOneBits, pulledRawBitCellChunkBits,
      List.map_append, List.append_assoc] using
      rightMoveAcrossFourBitsDescription_haltsFromTape_bits
        false true true false baseLeft
        (List.append ((preservingCellPassCellBits cellSuffix).map some)
          (some tailFirst :: tail))

def rightMoveAcrossCellSuffixDescription :
    Word Bool -> MachineDescription
  | [] => ExactIdentityDescription
  | _ :: rest =>
      CommonGround.SameHeadComposition.leftRightSeqDescription
        rightMoveAcrossFourBitsDescription
        (rightMoveAcrossCellSuffixDescription rest)

theorem rightMoveAcrossCellSuffixDescription_subroutineReady
    (cellSuffix : Word Bool) :
    (rightMoveAcrossCellSuffixDescription cellSuffix).SubroutineReady := by
  induction cellSuffix with
  | nil =>
      simpa [rightMoveAcrossCellSuffixDescription] using
        CommonGround.Identity.exactIdentityDescription_subroutineReady
  | cons bit rest ih =>
      simpa [rightMoveAcrossCellSuffixDescription] using
        CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
          rightMoveAcrossFourBitsDescription_subroutineReady
          ih

theorem rightMoveAcrossCellSuffixDescription_haltsFrom_cellSuffixLeftEdgeWithBase
    (cellSuffix : Word Bool) (baseLeft : List (Option Bool))
    (tailFirst : Bool) (tail : List (Option Bool)) :
    (rightMoveAcrossCellSuffixDescription cellSuffix).HaltsFromTape
      (cellSuffixLeftEdgeWithBase baseLeft cellSuffix tailFirst tail)
      (cellSuffixRightEdgeWithBase baseLeft cellSuffix tailFirst tail) := by
  induction cellSuffix generalizing baseLeft with
  | nil =>
      simpa [rightMoveAcrossCellSuffixDescription, cellSuffixLeftEdgeWithBase,
        cellSuffixRightEdgeWithBase, preservingCellPassCellBits] using
        CommonGround.Identity.exactIdentityDescription_haltsFromTape
          (cellSuffixLeftEdgeWithBase baseLeft [] tailFirst tail)
  | cons bit rest ih =>
      exact
        CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
          rightMoveAcrossFourBitsDescription_subroutineReady
          (rightMoveAcrossCellSuffixDescription_subroutineReady rest)
          (rightMoveAcrossFourBitsDescription_haltsFrom_cellSuffixLeftEdgeWithBase_cons
            baseLeft bit rest tailFirst tail)
          (cellSuffixLeftEdgeWithBase_moveLeftRight_after_cell
            baseLeft bit rest tailFirst tail)
          (by
            cases bit
            · simpa [cellSuffixRightEdgeWithBase, pulledRawBitCellChunkBits,
                preservingCellPassCellBits, preservingCellPassZeroBits,
                List.reverse_append, List.map_append, List.append_assoc] using
                ih
                  (List.append
                    ((pulledRawBitCellChunkBits false).reverse.map some)
                    baseLeft)
            · simpa [cellSuffixRightEdgeWithBase, pulledRawBitCellChunkBits,
                preservingCellPassCellBits, preservingCellPassOneBits,
                List.reverse_append, List.map_append, List.append_assoc] using
                ih
                  (List.append
                    ((pulledRawBitCellChunkBits true).reverse.map some)
                    baseLeft))

theorem rightMoveAcrossCellSuffixDescription_haltsFrom_tailHeadEmittedCellSuffixLeftEdgeScratchTape
    (pref : Word Bool) (scratchTail : Nat) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    (rightMoveAcrossCellSuffixDescription cellSuffix).HaltsFromTape
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape
        pref scratchTail cellSuffix tailFirst tail)
      (tailHeadEmittedCellSuffixRightEdgeScratchTape
        pref scratchTail cellSuffix tailFirst tail) := by
  simpa [tailHeadEmittedCellSuffixLeftEdgeScratchTape_eq_cellSuffixLeftEdgeWithBase,
    tailHeadEmittedCellSuffixRightEdgeScratchTape] using
    rightMoveAcrossCellSuffixDescription_haltsFrom_cellSuffixLeftEdgeWithBase
      cellSuffix
      (List.append
        (List.replicate scratchTail (none : Option Bool))
        (List.append (pref.reverse.map some) [none]))
      tailFirst tail

theorem tailHeadEmittedCellSuffixRightEdgeScratchTape_moveLeftRight
    (pref : Word Bool) (scratchTail : Nat) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tailHeadEmittedCellSuffixRightEdgeScratchTape
            pref scratchTail cellSuffix tailFirst tail)) =
      tailHeadEmittedCellSuffixRightEdgeScratchTape
        pref scratchTail cellSuffix tailFirst tail := by
  rw [tailHeadEmittedCellSuffixRightEdgeScratchTape, cellSuffixRightEdgeWithBase]
  simpa [List.append_assoc] using
    tapeAtCells_move_right_move_left_append_singleton
      (List.append
        ((preservingCellPassCellBits cellSuffix).reverse.map some)
        (List.append
          (List.replicate scratchTail (none : Option Bool))
          (pref.reverse.map some)))
      none
      (some tailFirst :: tail)

def prependLengthAndHeaderLeftOfCellSuffixDescription
    (layout : Word Bool) : MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    (prependLengthChunksLeftOfHeadDescription layout.length)
    prependHeaderChunkLeftOfHeadDescription

theorem prependLengthAndHeaderLeftOfCellSuffixDescription_subroutineReady
    (layout : Word Bool) :
    (prependLengthAndHeaderLeftOfCellSuffixDescription
      layout).SubroutineReady :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    (prependLengthChunksLeftOfHeadDescription_subroutineReady
      layout.length)
    prependHeaderChunkLeftOfHeadDescription_subroutineReady

theorem prependLengthAndHeaderLeftOfCellSuffixDescription_haltsFrom_cellSuffix_withScratch
    (layout : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (prependLengthAndHeaderLeftOfCellSuffixDescription
      layout).HaltsFromTape
      (tapeAtCells
        (List.append
          ((preservingCellPassCellBits layout).reverse.map some)
          (List.replicate (4 * (layout.length + 1) + 4)
            (none : Option Bool)))
        (some tailFirst :: tail))
      (tapeAtCells ((encodedLayoutBits layout).reverse.map some)
        (some tailFirst :: tail)) := by
  rw [prependLengthAndHeaderLeftOfCellSuffixDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
      (prependLengthChunksLeftOfHeadDescription_subroutineReady
        layout.length)
      prependHeaderChunkLeftOfHeadDescription_subroutineReady
      (by
        have hA :=
          prependLengthChunksLeftOfHeadDescription_haltsFrom_cellSuffix_withScratch
            layout (List.replicate 4 (none : Option Bool)) tailFirst tail
        have hsource :
            tapeAtCells
                (List.append
                  ((preservingCellPassCellBits layout).reverse.map some)
                  (List.append
                    (List.replicate (4 * (layout.length + 1))
                      (none : Option Bool))
                    (List.replicate 4 (none : Option Bool))))
                (some tailFirst :: tail) =
              tapeAtCells
                (List.append
                  ((preservingCellPassCellBits layout).reverse.map some)
                  (List.replicate (4 * (layout.length + 1) + 4)
                    (none : Option Bool)))
                (some tailFirst :: tail) := by
          have hrep :
              List.append
                  (List.replicate (4 * (layout.length + 1))
                    (none : Option Bool))
                  (List.replicate 4 (none : Option Bool)) =
                List.replicate (4 * (layout.length + 1) + 4)
                  (none : Option Bool) := by
            simpa using
              (list_replicate_add_append (none : Option Bool)
                (4 * (layout.length + 1)) 4
                ([] : List (Option Bool))).symm
          rw [hrep]
        rw [hsource] at hA
        simpa [List.append_assoc] using hA)
      (prependLengthChunksLeftOfHeadDescription_target_moveLeftRight_withScratch
        layout.length (preservingCellPassCellBits layout)
        ([] : List (Option Bool)) tailFirst tail)
      (by
        simpa [encodedLayoutBits_eq_header_length_cells,
          List.append_assoc] using
          prependHeaderChunkLeftOfHeadDescription_haltsFrom_prepend_withScratch
            (List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                layout.length)
              (preservingCellPassCellBits layout))
            ([] : List (Option Bool)) tailFirst tail)

theorem prependLengthAndHeaderLeftOfCellSuffixDescription_haltsFrom_cellSuffix
    (layout : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (prependLengthAndHeaderLeftOfCellSuffixDescription
      layout).HaltsFromTape
      (tapeAtCells
        ((preservingCellPassCellBits layout).reverse.map some)
        (some tailFirst :: tail))
      (tapeAtCells ((encodedLayoutBits layout).reverse.map some)
        (some tailFirst :: tail)) := by
  rw [prependLengthAndHeaderLeftOfCellSuffixDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
      (prependLengthChunksLeftOfHeadDescription_subroutineReady
        layout.length)
      prependHeaderChunkLeftOfHeadDescription_subroutineReady
      (prependLengthChunksLeftOfHeadDescription_haltsFrom_cellSuffix
        layout tailFirst tail)
      (prependLengthChunksLeftOfHeadDescription_target_moveLeftRight
        layout.length (preservingCellPassCellBits layout)
        tailFirst tail)
      (by
        simpa [encodedLayoutBits_eq_header_length_cells,
          List.append_assoc] using
          prependHeaderChunkLeftOfHeadDescription_haltsFrom_prepend
            (List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                layout.length)
              (preservingCellPassCellBits layout))
            tailFirst tail)

theorem cellSuffixRightEdge_equiv_tailHeadEmittedCellSuffixRightEdgeScratchTape
    (layout : Word Bool) (scratchTail : Nat)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    Tape.Equiv
      (tapeAtCells
        ((preservingCellPassCellBits layout).reverse.map some)
        (some tailFirst :: tail))
      (tailHeadEmittedCellSuffixRightEdgeScratchTape
        ([] : Word Bool) scratchTail layout tailFirst tail) := by
  constructor
  · simp [tailHeadEmittedCellSuffixRightEdgeScratchTape,
      cellSuffixRightEdgeWithBase, tapeAtCells]
    let xs :=
      (List.map some (preservingCellPassCellBits layout)).reverse
    have hrep :
        List.append (List.replicate scratchTail (none : Option Bool))
            [none] =
          List.replicate (scratchTail + 1) (none : Option Bool) := by
      simpa using
        (list_replicate_add_append (none : Option Bool)
          scratchTail 1 ([] : List (Option Bool))).symm
    change Tape.dropTrailingNone xs =
      Tape.dropTrailingNone
        (List.append xs
          (List.append
            (List.replicate scratchTail (none : Option Bool)) [none]))
    have happ :
        List.append xs
            (List.append
              (List.replicate scratchTail (none : Option Bool)) [none]) =
          List.append xs
            (List.replicate (scratchTail + 1)
              (none : Option Bool)) := by
      rw [hrep]
    rw [happ]
    exact
      (FoC.Computability.dropTrailingNone_append_replicate_none
        xs (scratchTail + 1)).symm
  · constructor <;> rfl

theorem prependLengthAndHeaderLeftOfCellSuffixDescription_haltsFrom_cellSuffix_equiv_withScratch
    (layout : Word Bool) (scratchTail : Nat)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    (prependLengthAndHeaderLeftOfCellSuffixDescription
      layout).HaltsFromTapeEquiv
      (tailHeadEmittedCellSuffixRightEdgeScratchTape
        ([] : Word Bool) scratchTail layout tailFirst tail)
      (tapeAtCells ((encodedLayoutBits layout).reverse.map some)
        (some tailFirst :: tail)) := by
  exact
    MachineDescription.HaltsFromTapeEquiv_of_input_equiv
      (D := prependLengthAndHeaderLeftOfCellSuffixDescription layout)
      (cellSuffixRightEdge_equiv_tailHeadEmittedCellSuffixRightEdgeScratchTape
        layout scratchTail tailFirst tail)
      (prependLengthAndHeaderLeftOfCellSuffixDescription_haltsFrom_cellSuffix
        layout tailFirst tail)

theorem tailHeadEmittedFullCellSuffixTape_eq_tailHeadEmittedCellSuffixRightEdgeScratchTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    tailHeadEmittedFullCellSuffixTape skipped count tailFirst tail =
      tailHeadEmittedCellSuffixRightEdgeScratchTape
        ([] : Word Bool) count.length (List.append skipped count)
        tailFirst tail := by
  rfl

theorem prependLengthAndHeaderLeftOfCellSuffixDescription_haltsFrom_fullCellSuffix_equiv
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (prependLengthAndHeaderLeftOfCellSuffixDescription
      (List.append skipped count)).HaltsFromTapeEquiv
      (tailHeadEmittedFullCellSuffixTape skipped count tailFirst tail)
      (rightEdgeTape skipped count tailFirst tail) := by
  rw [tailHeadEmittedFullCellSuffixTape_eq_tailHeadEmittedCellSuffixRightEdgeScratchTape]
  simpa [rightEdgeTape] using
    prependLengthAndHeaderLeftOfCellSuffixDescription_haltsFrom_cellSuffix_equiv_withScratch
      (List.append skipped count) count.length tailFirst tail

def emittedCellSuffixLeftEdgeToRightEdgeDescription
    (layout : Word Bool) : MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    (rightMoveAcrossCellSuffixDescription layout)
    (prependLengthAndHeaderLeftOfCellSuffixDescription layout)

theorem emittedCellSuffixLeftEdgeToRightEdgeDescription_subroutineReady
    (layout : Word Bool) :
    (emittedCellSuffixLeftEdgeToRightEdgeDescription
      layout).SubroutineReady :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    (rightMoveAcrossCellSuffixDescription_subroutineReady layout)
    (prependLengthAndHeaderLeftOfCellSuffixDescription_subroutineReady
      layout)

theorem tailHeadEmittedCellSuffixRightEdgeScratchTape_eq_lengthHeaderScratchSource
    (layout : Word Bool) (scratchTail : Nat)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hscratch : scratchTail + 1 = 4 * (layout.length + 1) + 4) :
    tailHeadEmittedCellSuffixRightEdgeScratchTape
        ([] : Word Bool) scratchTail layout tailFirst tail =
      tapeAtCells
        (List.append
          ((preservingCellPassCellBits layout).reverse.map some)
          (List.replicate (4 * (layout.length + 1) + 4)
            (none : Option Bool)))
        (some tailFirst :: tail) := by
  have hbase :
      List.append
          (List.replicate scratchTail (none : Option Bool))
          [none] =
        List.replicate (scratchTail + 1) (none : Option Bool) := by
    simpa using
      (list_replicate_add_append (none : Option Bool)
        scratchTail 1 ([] : List (Option Bool))).symm
  simp [tailHeadEmittedCellSuffixRightEdgeScratchTape,
    cellSuffixRightEdgeWithBase]
  congr 1
  exact
    congrArg
      (fun xs =>
        List.append
          (((preservingCellPassCellBits layout).map some).reverse)
          xs)
      (hbase.trans (by rw [hscratch]))

theorem emittedCellSuffixLeftEdgeToRightEdgeDescription_haltsFrom_tailHeadEmittedCellSuffixLeftEdgeScratchTape
    (layout : Word Bool) (scratchTail : Nat)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hscratch : scratchTail + 1 = 4 * (layout.length + 1) + 4) :
    (emittedCellSuffixLeftEdgeToRightEdgeDescription
      layout).HaltsFromTape
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail layout tailFirst tail)
      (tapeAtCells ((encodedLayoutBits layout).reverse.map some)
        (some tailFirst :: tail)) := by
  rw [emittedCellSuffixLeftEdgeToRightEdgeDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
      (rightMoveAcrossCellSuffixDescription_subroutineReady layout)
      (prependLengthAndHeaderLeftOfCellSuffixDescription_subroutineReady
        layout)
      (rightMoveAcrossCellSuffixDescription_haltsFrom_tailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail layout tailFirst tail)
      (by
        calc
          Tape.move Direction.right
              (Tape.move Direction.left
                (tailHeadEmittedCellSuffixRightEdgeScratchTape
                  ([] : Word Bool) scratchTail layout tailFirst tail)) =
            tailHeadEmittedCellSuffixRightEdgeScratchTape
              ([] : Word Bool) scratchTail layout tailFirst tail :=
              tailHeadEmittedCellSuffixRightEdgeScratchTape_moveLeftRight
                ([] : Word Bool) scratchTail layout tailFirst tail
          _ =
            tapeAtCells
              (List.append
                ((preservingCellPassCellBits layout).reverse.map some)
                (List.replicate (4 * (layout.length + 1) + 4)
                  (none : Option Bool)))
              (some tailFirst :: tail) :=
              tailHeadEmittedCellSuffixRightEdgeScratchTape_eq_lengthHeaderScratchSource
                layout scratchTail tailFirst tail hscratch)
      (prependLengthAndHeaderLeftOfCellSuffixDescription_haltsFrom_cellSuffix_withScratch
        layout tailFirst tail)

theorem emittedCellSuffixLeftEdgeToRightEdgeDescription_haltsFrom_tailHeadEmittedCellSuffixLeftEdgeScratchTape_rightEdgeTape
    (skipped count : Word Bool) (scratchTail : Nat)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hscratch :
      scratchTail + 1 =
        4 * ((List.append skipped count).length + 1) + 4) :
    (emittedCellSuffixLeftEdgeToRightEdgeDescription
      (List.append skipped count)).HaltsFromTape
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail (List.append skipped count)
        tailFirst tail)
      (rightEdgeTape skipped count tailFirst tail) := by
  simpa [rightEdgeTape] using
    emittedCellSuffixLeftEdgeToRightEdgeDescription_haltsFrom_tailHeadEmittedCellSuffixLeftEdgeScratchTape
      (List.append skipped count) scratchTail tailFirst tail hscratch

theorem emittedCellSuffixLeftEdgeToRightEdgeDescription_haltsFrom_tailHeadEmittedCellSuffixLeftEdgeScratchTape_equiv
    (layout : Word Bool) (scratchTail : Nat)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    (emittedCellSuffixLeftEdgeToRightEdgeDescription
      layout).HaltsFromTapeEquiv
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail layout tailFirst tail)
      (tapeAtCells ((encodedLayoutBits layout).reverse.map some)
        (some tailFirst :: tail)) := by
  rw [emittedCellSuffixLeftEdgeToRightEdgeDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTapeEquiv_of_haltsFromTape
      (rightMoveAcrossCellSuffixDescription_subroutineReady layout)
      (prependLengthAndHeaderLeftOfCellSuffixDescription_subroutineReady
        layout)
      (rightMoveAcrossCellSuffixDescription_haltsFrom_tailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail layout tailFirst tail)
      (tailHeadEmittedCellSuffixRightEdgeScratchTape_moveLeftRight
        ([] : Word Bool) scratchTail layout tailFirst tail)
      (prependLengthAndHeaderLeftOfCellSuffixDescription_haltsFrom_cellSuffix_equiv_withScratch
        layout scratchTail tailFirst tail)

theorem emittedCellSuffixLeftEdgeToRightEdgeDescription_haltsFrom_tailHeadEmittedCellSuffixLeftEdgeScratchTape_rightEdgeTapeEquiv
    (skipped count : Word Bool) (scratchTail : Nat)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    (emittedCellSuffixLeftEdgeToRightEdgeDescription
      (List.append skipped count)).HaltsFromTapeEquiv
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail (List.append skipped count)
        tailFirst tail)
      (rightEdgeTape skipped count tailFirst tail) := by
  simpa [rightEdgeTape] using
    emittedCellSuffixLeftEdgeToRightEdgeDescription_haltsFrom_tailHeadEmittedCellSuffixLeftEdgeScratchTape_equiv
      (List.append skipped count) scratchTail tailFirst tail

def sourceSingleRawBitToRightEdgeDescription
    (rawBit : Bool) : MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    sourceFirstRawBitCellLeftEdgeEmissionDescription
    (emittedCellSuffixLeftEdgeToRightEdgeDescription [rawBit])

theorem sourceSingleRawBitToRightEdgeDescription_subroutineReady
    (rawBit : Bool) :
    (sourceSingleRawBitToRightEdgeDescription rawBit).SubroutineReady :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    sourceFirstRawBitCellLeftEdgeEmissionDescription_subroutineReady
    (emittedCellSuffixLeftEdgeToRightEdgeDescription_subroutineReady
      [rawBit])

theorem tailHeadEmittedNearestRawBitCellLeftEdgeTape_eq_cellSuffixLeftEdgeScratch_singleton
    (count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    tailHeadEmittedNearestRawBitCellLeftEdgeTape
        ([] : Word Bool) count rawBit tailFirst tail =
      tailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) count.length [rawBit] tailFirst tail := by
  simpa [tailHeadEmittedCellSuffixLeftEdgeTape,
    tailHeadEmittedCellSuffixLeftEdgeScratchTape] using
    tailHeadEmittedNearestRawBitCellLeftEdgeTape_eq_cellSuffixLeftEdge_singleton
      ([] : Word Bool) count rawBit tailFirst tail

theorem sourceSingleRawBitToRightEdgeDescription_haltsFrom_sourceTape_equiv
    (skipped count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout : List.append skipped count = [rawBit]) :
    (sourceSingleRawBitToRightEdgeDescription rawBit).HaltsFromTapeEquiv
      (sourceTape skipped count (some tailFirst :: tail))
      (rightEdgeTape skipped count tailFirst tail) := by
  rw [sourceSingleRawBitToRightEdgeDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTapeEquiv_of_haltsFromTape
      sourceFirstRawBitCellLeftEdgeEmissionDescription_subroutineReady
      (emittedCellSuffixLeftEdgeToRightEdgeDescription_subroutineReady
        [rawBit])
      (sourceFirstRawBitCellLeftEdgeEmissionDescription_haltsFrom_sourceTape
        skipped count ([] : Word Bool) rawBit tailFirst tail
        (by simpa using hlayout))
      (by
        calc
          Tape.move Direction.right
              (Tape.move Direction.left
                (tailHeadEmittedNearestRawBitCellLeftEdgeTape
                  ([] : Word Bool) count rawBit tailFirst tail)) =
            tailHeadEmittedNearestRawBitCellLeftEdgeTape
              ([] : Word Bool) count rawBit tailFirst tail :=
              tailHeadEmittedNearestRawBitCellLeftEdgeTape_moveLeftRight
                ([] : Word Bool) count rawBit tailFirst tail
          _ =
            tailHeadEmittedCellSuffixLeftEdgeScratchTape
              ([] : Word Bool) count.length [rawBit] tailFirst tail :=
              tailHeadEmittedNearestRawBitCellLeftEdgeTape_eq_cellSuffixLeftEdgeScratch_singleton
                count rawBit tailFirst tail)
      (by
        have hB :=
          emittedCellSuffixLeftEdgeToRightEdgeDescription_haltsFrom_tailHeadEmittedCellSuffixLeftEdgeScratchTape_rightEdgeTapeEquiv
            skipped count count.length tailFirst tail
        rw [hlayout] at hB
        exact hB)

theorem sourceSingleRawBitToRightEdgeDescription_haltsFrom_sourceTape_exists_of_layout_length_one
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool))
    (hlength : (List.append skipped count).length = 1) :
    exists rawBit : Bool,
      List.append skipped count = [rawBit] ∧
        (sourceSingleRawBitToRightEdgeDescription rawBit).HaltsFromTapeEquiv
          (sourceTape skipped count (some tailFirst :: tail))
          (rightEdgeTape skipped count tailFirst tail) := by
  rcases
      FoC.Computability.list_exists_singleton_of_length_eq_one
        (List.append skipped count) hlength with
    ⟨rawBit, hlayout⟩
  exact
    ⟨rawBit, hlayout,
      sourceSingleRawBitToRightEdgeDescription_haltsFrom_sourceTape_equiv
        skipped count rawBit tailFirst tail hlayout⟩

def sourceTwoRawBitsToRightEdgeDescription
    (nextRawBit emittedRawBit : Bool) : MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    sourceFirstTwoRawBitCellsLeftEdgeEmissionDescription
    (emittedCellSuffixLeftEdgeToRightEdgeDescription
      [nextRawBit, emittedRawBit])

theorem sourceTwoRawBitsToRightEdgeDescription_subroutineReady
    (nextRawBit emittedRawBit : Bool) :
    (sourceTwoRawBitsToRightEdgeDescription
      nextRawBit emittedRawBit).SubroutineReady :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    sourceFirstTwoRawBitCellsLeftEdgeEmissionDescription_subroutineReady
    (emittedCellSuffixLeftEdgeToRightEdgeDescription_subroutineReady
      [nextRawBit, emittedRawBit])

theorem tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_eq_cellSuffixLeftEdgeScratch_pair
    (scratchTail : Nat) (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
        ([] : Word Bool) scratchTail nextRawBit emittedRawBit
        tailFirst tail =
      tailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail [nextRawBit, emittedRawBit]
        tailFirst tail := by
  cases nextRawBit <;> cases emittedRawBit <;>
    simp [tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape,
      tailHeadEmittedCellSuffixLeftEdgeScratchTape,
      preservingCellPassCellBits, preservingCellPassZeroBits,
      preservingCellPassOneBits, pulledRawBitCellChunkBits]

theorem sourceTwoRawBitsToRightEdgeDescription_haltsFrom_sourceTape_equiv_of_count_length
    (skipped count : Word Bool) (scratchTail : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout : List.append skipped count = [nextRawBit, emittedRawBit])
    (hcount : count.length = scratchTail + 3) :
    (sourceTwoRawBitsToRightEdgeDescription
      nextRawBit emittedRawBit).HaltsFromTapeEquiv
      (sourceTape skipped count (some tailFirst :: tail))
      (rightEdgeTape skipped count tailFirst tail) := by
  rw [sourceTwoRawBitsToRightEdgeDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTapeEquiv_of_haltsFromTape
      sourceFirstTwoRawBitCellsLeftEdgeEmissionDescription_subroutineReady
      (emittedCellSuffixLeftEdgeToRightEdgeDescription_subroutineReady
        [nextRawBit, emittedRawBit])
      (sourceFirstTwoRawBitCellsLeftEdgeEmissionDescription_haltsFrom_sourceTape_of_count_length
        skipped count ([] : Word Bool) scratchTail nextRawBit
        emittedRawBit tailFirst tail (by simpa using hlayout) hcount)
      (by
        calc
          Tape.move Direction.right
              (Tape.move Direction.left
                (tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
                  ([] : Word Bool) scratchTail nextRawBit emittedRawBit
                  tailFirst tail)) =
            tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
              ([] : Word Bool) scratchTail nextRawBit emittedRawBit
              tailFirst tail :=
              tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_moveLeftRight
                ([] : Word Bool) scratchTail nextRawBit emittedRawBit
                tailFirst tail
          _ =
            tailHeadEmittedCellSuffixLeftEdgeScratchTape
              ([] : Word Bool) scratchTail [nextRawBit, emittedRawBit]
              tailFirst tail :=
              tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_eq_cellSuffixLeftEdgeScratch_pair
                scratchTail nextRawBit emittedRawBit tailFirst tail)
      (by
        have hB :=
          emittedCellSuffixLeftEdgeToRightEdgeDescription_haltsFrom_tailHeadEmittedCellSuffixLeftEdgeScratchTape_rightEdgeTapeEquiv
            skipped count scratchTail tailFirst tail
        rw [hlayout] at hB
        exact hB)

theorem sourceTwoRawBitsToRightEdgeDescription_haltsFrom_sourceTape_equiv_of_count_enough
    (skipped count : Word Bool)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout : List.append skipped count = [nextRawBit, emittedRawBit])
    (hcount : 3 <= count.length) :
    exists scratchTail : Nat,
      count.length = scratchTail + 3 ∧
        (sourceTwoRawBitsToRightEdgeDescription
          nextRawBit emittedRawBit).HaltsFromTapeEquiv
          (sourceTape skipped count (some tailFirst :: tail))
          (rightEdgeTape skipped count tailFirst tail) := by
  rcases nat_exists_eq_add_of_le hcount with ⟨scratchTail, hscratch⟩
  exact
    ⟨scratchTail, hscratch,
      sourceTwoRawBitsToRightEdgeDescription_haltsFrom_sourceTape_equiv_of_count_length
        skipped count scratchTail nextRawBit emittedRawBit tailFirst tail
        hlayout hscratch⟩

theorem sourceTwoRawBitsToRightEdgeDescription_haltsFrom_sourceTape_exists_of_layout_length_two_count_enough
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool))
    (hlength : (List.append skipped count).length = 2)
    (hcount : 3 <= count.length) :
    exists nextRawBit : Bool, exists emittedRawBit : Bool,
      exists scratchTail : Nat,
        List.append skipped count = [nextRawBit, emittedRawBit] ∧
          count.length = scratchTail + 3 ∧
            (sourceTwoRawBitsToRightEdgeDescription
              nextRawBit emittedRawBit).HaltsFromTapeEquiv
              (sourceTape skipped count (some tailFirst :: tail))
              (rightEdgeTape skipped count tailFirst tail) := by
  rcases
      FoC.Computability.list_exists_pair_of_length_eq_two
        (List.append skipped count) hlength with
    ⟨nextRawBit, emittedRawBit, hlayout⟩
  rcases
      sourceTwoRawBitsToRightEdgeDescription_haltsFrom_sourceTape_equiv_of_count_enough
        skipped count nextRawBit emittedRawBit tailFirst tail
        hlayout hcount with
    ⟨scratchTail, hscratch, hroute⟩
  exact
    ⟨nextRawBit, emittedRawBit, scratchTail, hlayout, hscratch,
      hroute⟩

def pullRemainingRawBitsCellSuffixLeftEdgeDescription :
    Word Bool -> MachineDescription
  | [] => ExactIdentityDescription
  | _ :: rest =>
      CommonGround.SameHeadComposition.leftRightSeqDescription
        (pullRemainingRawBitsCellSuffixLeftEdgeDescription rest)
        pullEmitAndMoveRawBitCellLeftEdgeDescription

theorem pullRemainingRawBitsCellSuffixLeftEdgeDescription_subroutineReady
    (remaining : Word Bool) :
    (pullRemainingRawBitsCellSuffixLeftEdgeDescription
      remaining).SubroutineReady := by
  induction remaining with
  | nil =>
      simpa [pullRemainingRawBitsCellSuffixLeftEdgeDescription] using
        CommonGround.Identity.exactIdentityDescription_subroutineReady
  | cons bit rest ih =>
      simpa [pullRemainingRawBitsCellSuffixLeftEdgeDescription] using
        CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
          ih
          pullEmitAndMoveRawBitCellLeftEdgeDescription_subroutineReady

theorem pullRemainingRawBitsCellSuffixLeftEdgeDescription_haltsFrom
    (base remaining cellSuffix : Word Bool)
    (currentScratch finalScratch : Nat)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hscratch : currentScratch = finalScratch + 3 * remaining.length) :
    (pullRemainingRawBitsCellSuffixLeftEdgeDescription
      remaining).HaltsFromTape
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape
        (List.append base remaining) currentScratch cellSuffix tailFirst tail)
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape
        base finalScratch (List.append remaining cellSuffix) tailFirst tail) := by
  induction remaining generalizing base cellSuffix currentScratch finalScratch with
  | nil =>
      have hcurrent : currentScratch = finalScratch := by
        simpa using hscratch
      subst currentScratch
      simpa [pullRemainingRawBitsCellSuffixLeftEdgeDescription] using
        CommonGround.Identity.exactIdentityDescription_haltsFromTape
          (tailHeadEmittedCellSuffixLeftEdgeScratchTape
            base finalScratch cellSuffix tailFirst tail)
  | cons bit rest ih =>
      have hrest :
          currentScratch = (finalScratch + 3) + 3 * rest.length := by
        rw [hscratch]
        simp
        lia
      exact
        CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
          (pullRemainingRawBitsCellSuffixLeftEdgeDescription_subroutineReady
            rest)
          pullEmitAndMoveRawBitCellLeftEdgeDescription_subroutineReady
          (by
            simpa [List.append_assoc] using
              ih (List.append base [bit]) cellSuffix currentScratch
                (finalScratch + 3) hrest)
          (tailHeadEmittedCellSuffixLeftEdgeScratchTape_moveLeftRight
            (List.append base [bit]) (finalScratch + 3)
            (List.append rest cellSuffix) tailFirst tail)
          (by
            simpa using
              pullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_cellSuffixLeftEdgeScratch_of_scratch_length
                base (List.append rest cellSuffix) (finalScratch + 3)
                finalScratch bit tailFirst tail (by simp))

def sourceFirstThreeThenRemainingRawBitsCellSuffixLeftEdgeDescription
    (remaining : Word Bool) : MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    sourceFirstThreeRawBitCellsLeftEdgeEmissionDescription
    (pullRemainingRawBitsCellSuffixLeftEdgeDescription remaining)

theorem sourceFirstThreeThenRemainingRawBitsCellSuffixLeftEdgeDescription_subroutineReady
    (remaining : Word Bool) :
    (sourceFirstThreeThenRemainingRawBitsCellSuffixLeftEdgeDescription
      remaining).SubroutineReady :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    sourceFirstThreeRawBitCellsLeftEdgeEmissionDescription_subroutineReady
    (pullRemainingRawBitsCellSuffixLeftEdgeDescription_subroutineReady
      remaining)

theorem sourceFirstThreeThenRemainingRawBitsCellSuffixLeftEdgeDescription_haltsFrom_sourceTape_of_count_lengths
    (skipped count remaining : Word Bool)
    (scratchOne scratchAfterThree finalScratch : Nat)
    (thirdRawBit secondRawBit firstRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count =
        List.append
          (List.append
            (List.append remaining [thirdRawBit])
            [secondRawBit])
          [firstRawBit])
    (hcount : count.length = scratchOne + 3)
    (hfirstThreeScratch : scratchOne = scratchAfterThree + 3)
    (hremainingScratch :
      scratchAfterThree = finalScratch + 3 * remaining.length) :
    (sourceFirstThreeThenRemainingRawBitsCellSuffixLeftEdgeDescription
      remaining).HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) finalScratch
        (List.append remaining [thirdRawBit, secondRawBit, firstRawBit])
        tailFirst tail) := by
  rw [sourceFirstThreeThenRemainingRawBitsCellSuffixLeftEdgeDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
      sourceFirstThreeRawBitCellsLeftEdgeEmissionDescription_subroutineReady
      (pullRemainingRawBitsCellSuffixLeftEdgeDescription_subroutineReady
        remaining)
      (sourceFirstThreeRawBitCellsLeftEdgeEmissionDescription_haltsFrom_sourceTape_cellSuffixLeftEdge_of_count_lengths
        skipped count remaining scratchOne scratchAfterThree thirdRawBit
        secondRawBit firstRawBit tailFirst tail hlayout hcount
        hfirstThreeScratch)
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape_moveLeftRight
        remaining scratchAfterThree
        [thirdRawBit, secondRawBit, firstRawBit] tailFirst tail)
      (by
        simpa using
          pullRemainingRawBitsCellSuffixLeftEdgeDescription_haltsFrom
            ([] : Word Bool) remaining
            [thirdRawBit, secondRawBit, firstRawBit]
            scratchAfterThree finalScratch tailFirst tail
            hremainingScratch)

theorem sourceFirstThreeThenRemainingRawBitsCellSuffixLeftEdgeDescription_haltsFrom_sourceTape_exists_of_count_length
    (skipped count remaining : Word Bool)
    (thirdRawBit secondRawBit firstRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count =
        List.append
          (List.append
            (List.append remaining [thirdRawBit])
            [secondRawBit])
          [firstRawBit])
    (hcountEnough : 3 * remaining.length + 6 <= count.length) :
    exists finalScratch : Nat,
      (sourceFirstThreeThenRemainingRawBitsCellSuffixLeftEdgeDescription
        remaining).HaltsFromTape
        (sourceTape skipped count (some tailFirst :: tail))
        (tailHeadEmittedCellSuffixLeftEdgeScratchTape
          ([] : Word Bool) finalScratch
          (List.append remaining [thirdRawBit, secondRawBit, firstRawBit])
          tailFirst tail) := by
  rcases nat_exists_eq_add_of_le hcountEnough with
    ⟨finalScratch, hlength⟩
  let scratchAfterThree := finalScratch + 3 * remaining.length
  let scratchOne := scratchAfterThree + 3
  have hcount : count.length = scratchOne + 3 := by
    dsimp [scratchOne, scratchAfterThree]
    rw [hlength]
    lia
  have hfirstThreeScratch : scratchOne = scratchAfterThree + 3 := rfl
  have hremainingScratch :
      scratchAfterThree = finalScratch + 3 * remaining.length := rfl
  exact
    ⟨finalScratch,
      sourceFirstThreeThenRemainingRawBitsCellSuffixLeftEdgeDescription_haltsFrom_sourceTape_of_count_lengths
        skipped count remaining scratchOne scratchAfterThree finalScratch
        thirdRawBit secondRawBit firstRawBit tailFirst tail hlayout hcount
        hfirstThreeScratch hremainingScratch⟩

def sourceFirstThreeThenRemainingRawBitsToRightEdgeDescription
    (remaining : Word Bool)
    (thirdRawBit secondRawBit firstRawBit : Bool) :
    MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    (sourceFirstThreeThenRemainingRawBitsCellSuffixLeftEdgeDescription
      remaining)
    (emittedCellSuffixLeftEdgeToRightEdgeDescription
      (List.append remaining [thirdRawBit, secondRawBit, firstRawBit]))

theorem sourceFirstThreeThenRemainingRawBitsToRightEdgeDescription_subroutineReady
    (remaining : Word Bool)
    (thirdRawBit secondRawBit firstRawBit : Bool) :
    (sourceFirstThreeThenRemainingRawBitsToRightEdgeDescription
      remaining thirdRawBit secondRawBit firstRawBit).SubroutineReady :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    (sourceFirstThreeThenRemainingRawBitsCellSuffixLeftEdgeDescription_subroutineReady
      remaining)
    (emittedCellSuffixLeftEdgeToRightEdgeDescription_subroutineReady
      (List.append remaining [thirdRawBit, secondRawBit, firstRawBit]))

theorem sourceFirstThreeThenRemainingRawBitsToRightEdgeDescription_haltsFrom_sourceTape_of_count_lengths
    (skipped count remaining : Word Bool)
    (scratchOne scratchAfterThree finalScratch : Nat)
    (thirdRawBit secondRawBit firstRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count =
        List.append
          (List.append
            (List.append remaining [thirdRawBit])
            [secondRawBit])
          [firstRawBit])
    (hcount : count.length = scratchOne + 3)
    (hfirstThreeScratch : scratchOne = scratchAfterThree + 3)
    (hremainingScratch :
      scratchAfterThree = finalScratch + 3 * remaining.length)
    (hpostScratch :
      finalScratch + 1 =
        4 *
          ((List.append remaining
            [thirdRawBit, secondRawBit, firstRawBit]).length + 1) + 4) :
    (sourceFirstThreeThenRemainingRawBitsToRightEdgeDescription
      remaining thirdRawBit secondRawBit firstRawBit).HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (rightEdgeTape skipped count tailFirst tail) := by
  have hlayoutFlat :
      List.append skipped count =
        List.append remaining
          [thirdRawBit, secondRawBit, firstRawBit] := by
    simpa [List.append_assoc] using hlayout
  rw [sourceFirstThreeThenRemainingRawBitsToRightEdgeDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
      (sourceFirstThreeThenRemainingRawBitsCellSuffixLeftEdgeDescription_subroutineReady
        remaining)
      (emittedCellSuffixLeftEdgeToRightEdgeDescription_subroutineReady
        (List.append remaining
          [thirdRawBit, secondRawBit, firstRawBit]))
      (sourceFirstThreeThenRemainingRawBitsCellSuffixLeftEdgeDescription_haltsFrom_sourceTape_of_count_lengths
        skipped count remaining scratchOne scratchAfterThree finalScratch
        thirdRawBit secondRawBit firstRawBit tailFirst tail hlayout hcount
        hfirstThreeScratch hremainingScratch)
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape_moveLeftRight
        ([] : Word Bool) finalScratch
        (List.append remaining
          [thirdRawBit, secondRawBit, firstRawBit])
        tailFirst tail)
      (by
        rw [rightEdgeTape, hlayoutFlat]
        exact
          emittedCellSuffixLeftEdgeToRightEdgeDescription_haltsFrom_tailHeadEmittedCellSuffixLeftEdgeScratchTape
            (List.append remaining
              [thirdRawBit, secondRawBit, firstRawBit])
            finalScratch tailFirst tail hpostScratch)

theorem sourceFirstThreeThenRemainingRawBitsToRightEdgeDescription_haltsFrom_sourceTape_of_count_lengths_equiv
    (skipped count remaining : Word Bool)
    (scratchOne scratchAfterThree finalScratch : Nat)
    (thirdRawBit secondRawBit firstRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count =
        List.append
          (List.append
            (List.append remaining [thirdRawBit])
            [secondRawBit])
          [firstRawBit])
    (hcount : count.length = scratchOne + 3)
    (hfirstThreeScratch : scratchOne = scratchAfterThree + 3)
    (hremainingScratch :
      scratchAfterThree = finalScratch + 3 * remaining.length) :
    (sourceFirstThreeThenRemainingRawBitsToRightEdgeDescription
      remaining thirdRawBit secondRawBit firstRawBit).HaltsFromTapeEquiv
      (sourceTape skipped count (some tailFirst :: tail))
      (rightEdgeTape skipped count tailFirst tail) := by
  have hlayoutFlat :
      List.append skipped count =
        List.append remaining
          [thirdRawBit, secondRawBit, firstRawBit] := by
    simpa [List.append_assoc] using hlayout
  rw [sourceFirstThreeThenRemainingRawBitsToRightEdgeDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTapeEquiv_of_haltsFromTape
      (sourceFirstThreeThenRemainingRawBitsCellSuffixLeftEdgeDescription_subroutineReady
        remaining)
      (emittedCellSuffixLeftEdgeToRightEdgeDescription_subroutineReady
        (List.append remaining
          [thirdRawBit, secondRawBit, firstRawBit]))
      (sourceFirstThreeThenRemainingRawBitsCellSuffixLeftEdgeDescription_haltsFrom_sourceTape_of_count_lengths
        skipped count remaining scratchOne scratchAfterThree finalScratch
        thirdRawBit secondRawBit firstRawBit tailFirst tail hlayout hcount
        hfirstThreeScratch hremainingScratch)
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape_moveLeftRight
        ([] : Word Bool) finalScratch
        (List.append remaining
          [thirdRawBit, secondRawBit, firstRawBit])
        tailFirst tail)
      (by
        have hB :=
          emittedCellSuffixLeftEdgeToRightEdgeDescription_haltsFrom_tailHeadEmittedCellSuffixLeftEdgeScratchTape_rightEdgeTapeEquiv
            skipped count finalScratch tailFirst tail
        rw [hlayoutFlat] at hB
        exact hB)

theorem sourceFirstThreeThenRemainingRawBitsToRightEdgeDescription_haltsFrom_sourceTape_of_count_enough_equiv
    (skipped count remaining : Word Bool)
    (thirdRawBit secondRawBit firstRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count =
        List.append
          (List.append
            (List.append remaining [thirdRawBit])
            [secondRawBit])
          [firstRawBit])
    (hcountEnough : 3 * remaining.length + 6 <= count.length) :
    (sourceFirstThreeThenRemainingRawBitsToRightEdgeDescription
      remaining thirdRawBit secondRawBit firstRawBit).HaltsFromTapeEquiv
      (sourceTape skipped count (some tailFirst :: tail))
      (rightEdgeTape skipped count tailFirst tail) := by
  rcases nat_exists_eq_add_of_le hcountEnough with
    ⟨finalScratch, hlength⟩
  let scratchAfterThree := finalScratch + 3 * remaining.length
  let scratchOne := scratchAfterThree + 3
  have hcount : count.length = scratchOne + 3 := by
    dsimp [scratchOne, scratchAfterThree]
    rw [hlength]
    lia
  have hfirstThreeScratch : scratchOne = scratchAfterThree + 3 := rfl
  have hremainingScratch :
      scratchAfterThree = finalScratch + 3 * remaining.length := rfl
  exact
    sourceFirstThreeThenRemainingRawBitsToRightEdgeDescription_haltsFrom_sourceTape_of_count_lengths_equiv
      skipped count remaining scratchOne scratchAfterThree finalScratch
      thirdRawBit secondRawBit firstRawBit tailFirst tail hlayout hcount
      hfirstThreeScratch hremainingScratch

def sourceThreeRawBitsToRightEdgeDescription
    (thirdRawBit secondRawBit firstRawBit : Bool) :
    MachineDescription :=
  sourceFirstThreeThenRemainingRawBitsToRightEdgeDescription
    ([] : Word Bool) thirdRawBit secondRawBit firstRawBit

theorem sourceThreeRawBitsToRightEdgeDescription_subroutineReady
    (thirdRawBit secondRawBit firstRawBit : Bool) :
    (sourceThreeRawBitsToRightEdgeDescription
      thirdRawBit secondRawBit firstRawBit).SubroutineReady := by
  exact
    sourceFirstThreeThenRemainingRawBitsToRightEdgeDescription_subroutineReady
      ([] : Word Bool) thirdRawBit secondRawBit firstRawBit

theorem sourceThreeRawBitsToRightEdgeDescription_haltsFrom_sourceTape_equiv_of_count_enough
    (skipped count : Word Bool)
    (thirdRawBit secondRawBit firstRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count =
        [thirdRawBit, secondRawBit, firstRawBit])
    (hcount : 6 <= count.length) :
    (sourceThreeRawBitsToRightEdgeDescription
      thirdRawBit secondRawBit firstRawBit).HaltsFromTapeEquiv
      (sourceTape skipped count (some tailFirst :: tail))
      (rightEdgeTape skipped count tailFirst tail) := by
  rw [sourceThreeRawBitsToRightEdgeDescription]
  exact
    sourceFirstThreeThenRemainingRawBitsToRightEdgeDescription_haltsFrom_sourceTape_of_count_enough_equiv
      skipped count ([] : Word Bool)
      thirdRawBit secondRawBit firstRawBit tailFirst tail
      (by simpa using hlayout)
      (by simpa using hcount)

theorem sourceThreeRawBitsToRightEdgeDescription_haltsFrom_sourceTape_exists_of_layout_length_three_count_enough
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool))
    (hlength : (List.append skipped count).length = 3)
    (hcount : 6 <= count.length) :
    exists thirdRawBit : Bool, exists secondRawBit : Bool,
      exists firstRawBit : Bool,
        List.append skipped count =
          [thirdRawBit, secondRawBit, firstRawBit] ∧
          (sourceThreeRawBitsToRightEdgeDescription
            thirdRawBit secondRawBit firstRawBit).HaltsFromTapeEquiv
            (sourceTape skipped count (some tailFirst :: tail))
            (rightEdgeTape skipped count tailFirst tail) := by
  rcases
      FoC.Computability.list_exists_triple_of_length_eq_three
        (List.append skipped count) hlength with
    ⟨thirdRawBit, secondRawBit, firstRawBit, hlayout⟩
  exact
    ⟨thirdRawBit, secondRawBit, firstRawBit, hlayout,
      sourceThreeRawBitsToRightEdgeDescription_haltsFrom_sourceTape_equiv_of_count_enough
        skipped count thirdRawBit secondRawBit firstRawBit tailFirst tail
        hlayout hcount⟩

theorem sourceFirstThreeThenRemainingRawBitsToRightEdgeDescription_haltsFrom_sourceTape_of_count_length
    (skipped count remaining : Word Bool)
    (thirdRawBit secondRawBit firstRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count =
        List.append
          (List.append
            (List.append remaining [thirdRawBit])
            [secondRawBit])
          [firstRawBit])
    (hcountLength : count.length = 7 * remaining.length + 25) :
    (sourceFirstThreeThenRemainingRawBitsToRightEdgeDescription
      remaining thirdRawBit secondRawBit firstRawBit).HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (rightEdgeTape skipped count tailFirst tail) := by
  let finalScratch := 4 * remaining.length + 19
  let scratchAfterThree := finalScratch + 3 * remaining.length
  let scratchOne := scratchAfterThree + 3
  have hcount : count.length = scratchOne + 3 := by
    dsimp [scratchOne, scratchAfterThree, finalScratch]
    rw [hcountLength]
    lia
  have hfirstThreeScratch : scratchOne = scratchAfterThree + 3 := rfl
  have hremainingScratch :
      scratchAfterThree = finalScratch + 3 * remaining.length := rfl
  have hpostScratch :
      finalScratch + 1 =
        4 *
          ((List.append remaining
            [thirdRawBit, secondRawBit, firstRawBit]).length + 1) + 4 := by
    dsimp [finalScratch]
    simp [List.length_append]
    lia
  exact
    sourceFirstThreeThenRemainingRawBitsToRightEdgeDescription_haltsFrom_sourceTape_of_count_lengths
      skipped count remaining scratchOne scratchAfterThree finalScratch
      thirdRawBit secondRawBit firstRawBit tailFirst tail hlayout hcount
      hfirstThreeScratch hremainingScratch hpostScratch

theorem sourceFirstThreeThenRemainingRawBitsToRightEdgeDescription_haltsFrom_sourceTape_exists_of_layout_length_count_enough
    (skipped count : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hlayoutLength : 3 <= (List.append skipped count).length)
    (hcountEnough :
      3 * ((List.append skipped count).length - 3) + 6 <=
        count.length) :
    exists remaining : Word Bool, exists thirdRawBit : Bool,
      exists secondRawBit : Bool, exists firstRawBit : Bool,
        List.append skipped count =
            List.append
              (List.append
                (List.append remaining [thirdRawBit])
                [secondRawBit])
              [firstRawBit] ∧
          (sourceFirstThreeThenRemainingRawBitsToRightEdgeDescription
            remaining thirdRawBit secondRawBit firstRawBit).HaltsFromTapeEquiv
            (sourceTape skipped count (some tailFirst :: tail))
            (rightEdgeTape skipped count tailFirst tail) := by
  rcases
      FoC.Computability.list_exists_append_three_of_three_le_length
        (List.append skipped count) hlayoutLength with
    ⟨remaining, thirdRawBit, secondRawBit, firstRawBit, hlayoutBase⟩
  have hlayout :
      List.append skipped count =
        List.append
          (List.append
            (List.append remaining [thirdRawBit])
            [secondRawBit])
          [firstRawBit] := by
    simpa [List.append_assoc] using hlayoutBase
  have hremainingLength :
      (List.append skipped count).length - 3 = remaining.length := by
    rw [hlayout]
    simp [List.length_append]
  have hcountRemaining :
      3 * remaining.length + 6 <= count.length := by
    rw [← hremainingLength]
    exact hcountEnough
  exact
    ⟨remaining, thirdRawBit, secondRawBit, firstRawBit, hlayout,
      sourceFirstThreeThenRemainingRawBitsToRightEdgeDescription_haltsFrom_sourceTape_of_count_enough_equiv
        skipped count remaining thirdRawBit secondRawBit firstRawBit
        tailFirst tail hlayout hcountRemaining⟩

theorem sourceFirstThreeThenRemainingRawBitsToRightEdgeDescription_haltsFrom_sourceTape_exists_of_layout_length_count_length
    (skipped count : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hlayoutLength : 3 <= (List.append skipped count).length)
    (hcountLength :
      count.length =
        7 * ((List.append skipped count).length - 3) + 25) :
    exists remaining : Word Bool, exists thirdRawBit : Bool,
      exists secondRawBit : Bool, exists firstRawBit : Bool,
        List.append skipped count =
            List.append
              (List.append
                (List.append remaining [thirdRawBit])
                [secondRawBit])
              [firstRawBit] ∧
          (sourceFirstThreeThenRemainingRawBitsToRightEdgeDescription
            remaining thirdRawBit secondRawBit firstRawBit).HaltsFromTape
            (sourceTape skipped count (some tailFirst :: tail))
            (rightEdgeTape skipped count tailFirst tail) := by
  rcases
      FoC.Computability.list_exists_append_three_of_three_le_length
        (List.append skipped count) hlayoutLength with
    ⟨remaining, thirdRawBit, secondRawBit, firstRawBit, hlayoutBase⟩
  have hlayout :
      List.append skipped count =
        List.append
          (List.append
            (List.append remaining [thirdRawBit])
            [secondRawBit])
          [firstRawBit] := by
    simpa [List.append_assoc] using hlayoutBase
  have hremainingLength :
      (List.append skipped count).length - 3 = remaining.length := by
    rw [hlayout]
    simp [List.length_append]
  have hcountRemaining :
      count.length = 7 * remaining.length + 25 := by
    rw [hcountLength, hremainingLength]
  exact
    ⟨remaining, thirdRawBit, secondRawBit, firstRawBit, hlayout,
      sourceFirstThreeThenRemainingRawBitsToRightEdgeDescription_haltsFrom_sourceTape_of_count_length
        skipped count remaining thirdRawBit secondRawBit firstRawBit
        tailFirst tail hlayout hcountRemaining⟩

def sourceBranchRouteCountBound
    (skipped count : Word Bool) : Prop :=
  (List.append skipped count).length = 1 ∨
    ((List.append skipped count).length = 2 ∧
      3 <= count.length) ∨
    (3 <= (List.append skipped count).length ∧
      3 * ((List.append skipped count).length - 3) + 6 <=
        count.length)

theorem sourceBranchRouteDescription_exists_haltsFrom_sourceTape_equiv
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool))
    (hbound : sourceBranchRouteCountBound skipped count) :
    exists emitter : MachineDescription,
      emitter.SubroutineReady ∧
        emitter.HaltsFromTapeEquiv
          (sourceTape skipped count (some tailFirst :: tail))
          (rightEdgeTape skipped count tailFirst tail) := by
  rcases hbound with hlenOne | hrest
  · rcases
        sourceSingleRawBitToRightEdgeDescription_haltsFrom_sourceTape_exists_of_layout_length_one
          skipped count tailFirst tail hlenOne with
      ⟨rawBit, _hlayout, hroute⟩
    exact
      ⟨sourceSingleRawBitToRightEdgeDescription rawBit,
        sourceSingleRawBitToRightEdgeDescription_subroutineReady rawBit,
        hroute⟩
  · rcases hrest with hlenTwoAndCount | hlenThreeAndCount
    · rcases hlenTwoAndCount with ⟨hlenTwo, hcount⟩
      rcases
          sourceTwoRawBitsToRightEdgeDescription_haltsFrom_sourceTape_exists_of_layout_length_two_count_enough
            skipped count tailFirst tail hlenTwo hcount with
        ⟨nextRawBit, emittedRawBit, _scratchTail, _hlayout,
          _hscratch, hroute⟩
      exact
        ⟨sourceTwoRawBitsToRightEdgeDescription
            nextRawBit emittedRawBit,
          sourceTwoRawBitsToRightEdgeDescription_subroutineReady
            nextRawBit emittedRawBit,
          hroute⟩
    · rcases hlenThreeAndCount with ⟨hlayoutLength, hcountEnough⟩
      rcases
          sourceFirstThreeThenRemainingRawBitsToRightEdgeDescription_haltsFrom_sourceTape_exists_of_layout_length_count_enough
            skipped count tailFirst tail hlayoutLength hcountEnough with
        ⟨remaining, thirdRawBit, secondRawBit, firstRawBit,
          _hlayout, hroute⟩
      exact
        ⟨sourceFirstThreeThenRemainingRawBitsToRightEdgeDescription
            remaining thirdRawBit secondRawBit firstRawBit,
          sourceFirstThreeThenRemainingRawBitsToRightEdgeDescription_subroutineReady
            remaining thirdRawBit secondRawBit firstRawBit,
          hroute⟩

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
