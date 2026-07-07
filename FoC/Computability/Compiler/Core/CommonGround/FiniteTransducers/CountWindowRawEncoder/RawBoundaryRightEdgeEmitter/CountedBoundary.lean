import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountedSuffixExtraBlankRestorer
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountedSuffixBoundaryLocator
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.FixedSkips
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.SentinelGapCompactor
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawEncoder.RawBoundaryRightEdgeEmitter.EndpointSupport
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawEncoder.RawBoundaryRightEdgeEmitter.MarkerAwarePull

set_option doc.verso true

/-!
# Raw-boundary counted-suffix bridge

This module adapts the fixed counted-suffix boundary locator to the
raw-boundary emitter shape after a guard bit has been installed immediately to
the right of the raw right-edge blank.
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

theorem sourceTape_eq_countedSuffixExtraBlankRightGapSourceTape
    (skipped suffixRest : Word Bool) (suffixFirst : Bool)
    (tail : List (Option Bool)) :
    sourceTape skipped (suffixFirst :: suffixRest) tail =
      countedSuffixExtraBlankRightGapSourceTape
        skipped suffixRest suffixFirst tail := by
  simp [sourceTape, countedSuffixExtraBlankRightGapSourceTape,
    rightEdgeRewindSourceTapeWithBase, List.replicate_succ,
    List.append_assoc]

theorem sourceStartTape_eq_countedSuffixExtraBlankRestoredSourceTape
    (skipped suffixRest : Word Bool) (suffixFirst : Bool)
    (tail : List (Option Bool)) :
    sourceStartTape skipped (suffixFirst :: suffixRest) tail =
      countedSuffixExtraBlankRestoredSourceTape
        skipped suffixRest suffixFirst tail := by
  simp [sourceStartTape, countedSuffixExtraBlankRestoredSourceTape,
    rightEdgeRewindTargetTapeWithBase, List.replicate_succ,
    List.append_assoc]

theorem countedSuffixExtraBlankRestorerDescription_haltsFrom_sourceTape_sourceStart
    (skipped suffixRest : Word Bool) (suffixFirst : Bool)
    (tail : List (Option Bool)) :
    countedSuffixExtraBlankRestorerDescription.HaltsFromTape
      (sourceTape skipped (suffixFirst :: suffixRest) tail)
      (sourceStartTape skipped (suffixFirst :: suffixRest) tail) := by
  rw [sourceTape_eq_countedSuffixExtraBlankRightGapSourceTape,
    sourceStartTape_eq_countedSuffixExtraBlankRestoredSourceTape]
  exact
    countedSuffixExtraBlankRestorerDescription_haltsFromTape
      skipped suffixRest suffixFirst tail

def rawBoundaryLeftMarkedStartTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells [some false]
    (List.append ((List.append skipped count).map some)
      (none ::
        none ::
          none ::
            List.append
              (List.replicate count.length (none : Option Bool))
              tail))

theorem rawBoundaryLeftMarkedStartTape_cells
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape.cells (rawBoundaryLeftMarkedStartTape skipped count tail) =
      some false ::
        List.append ((List.append skipped count).map some)
          (none ::
            none ::
              none ::
                List.append
                  (List.replicate count.length (none : Option Bool))
                  tail) := by
  cases skipped with
  | nil =>
      cases count with
      | nil =>
          simp [rawBoundaryLeftMarkedStartTape, Tape.cells, tapeAtCells]
      | cons bit rest =>
          cases bit <;>
            simp [rawBoundaryLeftMarkedStartTape, Tape.cells, tapeAtCells]
  | cons bit rest =>
      cases bit <;>
        simp [rawBoundaryLeftMarkedStartTape, Tape.cells, tapeAtCells,
          List.append_assoc]

def rawBoundarySourceToLeftMarkedStartDescription :
    MachineDescription :=
  restoreFalseMarkerRewindDescription

theorem rawBoundarySourceToLeftMarkedStartDescription_ready :
    rawBoundarySourceToLeftMarkedStartDescription.SubroutineReady := by
  simpa [rawBoundarySourceToLeftMarkedStartDescription] using
    restoreFalseMarkerRewindDescription_subroutineReady

theorem rawBoundarySourceToLeftMarkedStartDescription_haltsFrom_sourceTape
    (skipped count : Word Bool)
    (h : List.append skipped count ≠ [])
    (tail : List (Option Bool)) :
    rawBoundarySourceToLeftMarkedStartDescription.HaltsFromTape
      (sourceTape skipped count tail)
      (rawBoundaryLeftMarkedStartTape skipped count tail) := by
  cases hlayout : List.append skipped count with
  | nil =>
      exact False.elim (h hlayout)
  | cons first rest =>
      rw [rawBoundarySourceToLeftMarkedStartDescription]
      rw [sourceTape, rawBoundaryLeftMarkedStartTape]
      rw [hlayout]
      simpa [rightEdgeRewindSourceTapeWithBase, List.append_assoc] using
        restoreFalseMarkerRewindDescription_haltsFromTape_cons
          first rest
          (none ::
            none ::
              List.append
                (List.replicate count.length (none : Option Bool))
                tail)

theorem rawBoundaryLeftMarkedStartTape_moveLeftRight
    (skipped count : Word Bool)
    (h : List.append skipped count ≠ [])
    (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (rawBoundaryLeftMarkedStartTape skipped count tail)) =
      rawBoundaryLeftMarkedStartTape skipped count tail := by
  cases hlayout : List.append skipped count with
  | nil =>
      exact False.elim (h hlayout)
  | cons first rest =>
      rw [rawBoundaryLeftMarkedStartTape, hlayout]
      cases first <;> cases rest <;> cases tail <;>
        simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

def rawBoundaryLeftMarkedRawRightEdgeTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells
    (List.append ((List.append skipped count).reverse.map some)
      [some false])
    (none ::
      none ::
        none ::
          List.append
            (List.replicate count.length (none : Option Bool))
            tail)

def rawBoundaryLeftMarkedTailLeftHandoffTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate (count.length + 2) (none : Option Bool))
      (List.append ((List.append skipped count).reverse.map some)
        [some false]))
    (none :: some tailFirst :: tail)

def rawBoundaryLeftMarkedTailHeadHandoffTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  Tape.move Direction.right
    (rawBoundaryLeftMarkedTailLeftHandoffTape
      skipped count tailFirst tail)

def rawBoundaryLeftMarkedTailHeadPulledNearestRawBitTape
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  markerAwarePullNearestRawBitTargetTape
    (count.length + 2)
    (List.append (pref.reverse.map some) [some false])
    rawBit tailFirst tail

def rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  emitPulledRawBitCellChunkTargetTape
    count.length
    (List.append (pref.reverse.map some) [some false])
    rawBit tailFirst tail

def rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate count.length (none : Option Bool))
      (List.append (pref.reverse.map some) [some false]))
    (List.append
      ((pulledRawBitCellChunkBits rawBit).map some)
      (some tailFirst :: tail))

def rawBoundaryLeftMarkedTailHeadPulledNextRawBitBeforeEmittedCellTape
    (pref count : Word Bool)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (some nextRawBit ::
      List.append
        (List.replicate count.length (none : Option Bool))
        (List.append (pref.reverse.map some) [some false]))
    (List.append
      ((pulledRawBitCellChunkBits emittedRawBit).map some)
      (some tailFirst :: tail))

def rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
    (pref : Word Bool) (scratchTail : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate scratchTail (none : Option Bool))
      (List.append (pref.reverse.map some) [some false]))
    (List.append
      ((pulledRawBitCellChunkBits nextRawBit).map some)
      (List.append
        ((pulledRawBitCellChunkBits emittedRawBit).map some)
        (some tailFirst :: tail)))

theorem rawBoundaryLeftMarkedRawRightEdgeTape_moveLeftRight
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (rawBoundaryLeftMarkedRawRightEdgeTape skipped count tail)) =
      rawBoundaryLeftMarkedRawRightEdgeTape skipped count tail := by
  rw [rawBoundaryLeftMarkedRawRightEdgeTape]
  exact
    rightEdgeScanSourceTapeFromLeft_move_left_move_right_padding_cons
      (List.append ((List.append skipped count).reverse.map some)
        [some false])
      ([] : Word Bool) (none : Option Bool)
      (none ::
        List.append
          (List.replicate count.length (none : Option Bool))
          tail)

theorem rawBoundaryLeftMarkedTailLeftHandoffTape_moveRight
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.right
        (rawBoundaryLeftMarkedTailLeftHandoffTape
          skipped count tailFirst tail) =
      rawBoundaryLeftMarkedTailHeadHandoffTape
        skipped count tailFirst tail := by
  rfl

theorem rawBoundaryLeftMarkedTailHeadHandoffTape_eq_tapeAtCells
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    rawBoundaryLeftMarkedTailHeadHandoffTape
        skipped count tailFirst tail =
      tapeAtCells
        (none ::
          List.append
            (List.replicate (count.length + 2)
              (none : Option Bool))
            (List.append ((List.append skipped count).reverse.map some)
              [some false]))
        (some tailFirst :: tail) := by
  rw [rawBoundaryLeftMarkedTailHeadHandoffTape,
    rawBoundaryLeftMarkedTailLeftHandoffTape]
  exact
    tapeAtCells_move_right_cons
      (List.append
        (List.replicate (count.length + 2) (none : Option Bool))
        (List.append ((List.append skipped count).reverse.map some)
          [some false]))
      none
      (some tailFirst :: tail)

theorem rawBoundaryLeftMarkedTailHeadHandoffTape_eq_markerAwarePullSource
    (skipped count pref : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) :
    rawBoundaryLeftMarkedTailHeadHandoffTape
        skipped count tailFirst tail =
      markerAwarePullNearestRawBitSourceTape
        (count.length + 2)
        (List.append (pref.reverse.map some) [some false])
        rawBit tailFirst tail := by
  rw [rawBoundaryLeftMarkedTailHeadHandoffTape_eq_tapeAtCells,
    markerAwarePullNearestRawBitSourceTape,
    pullNearestRawBitToTailMarkerSourceTape, hlayout]
  simp [List.reverse_append, List.map_reverse, List.replicate_succ]

theorem rawBoundaryLeftMarkedTailHeadHandoffTape_moveLeftRight
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (rawBoundaryLeftMarkedTailHeadHandoffTape
            skipped count tailFirst tail)) =
      rawBoundaryLeftMarkedTailHeadHandoffTape
        skipped count tailFirst tail := by
  rw [rawBoundaryLeftMarkedTailHeadHandoffTape_eq_tapeAtCells]
  exact
    tapeAtCells_move_right_move_left_cons
      none
      (List.append
        (List.replicate (count.length + 2) (none : Option Bool))
        (List.append ((List.append skipped count).reverse.map some)
          [some false]))
      (some tailFirst)
      tail

theorem rawBoundaryLeftMarkedTailHeadPulledNearestRawBit_haltsFrom
    (skipped count pref : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) :
    markerAwarePullNearestRawBitDescription.HaltsFromTape
      (rawBoundaryLeftMarkedTailHeadHandoffTape
        skipped count tailFirst tail)
      (rawBoundaryLeftMarkedTailHeadPulledNearestRawBitTape
        pref count rawBit tailFirst tail) := by
  have hsource :=
    rawBoundaryLeftMarkedTailHeadHandoffTape_eq_markerAwarePullSource
      skipped count pref rawBit tailFirst tail hlayout
  rw [hsource, rawBoundaryLeftMarkedTailHeadPulledNearestRawBitTape]
  cases hbase :
      List.append (pref.reverse.map some) [some false] with
  | nil =>
      have hlen := congrArg List.length hbase
      simp at hlen
  | cons head baseTail =>
      cases head with
      | none =>
          cases hrev : pref.reverse <;> simp [hrev] at hbase
      | some leftBit =>
          exact
            markerAwarePullNearestRawBitDescription_haltsFromTape_real
              (count.length + 2) leftBit rawBit baseTail tailFirst tail

theorem rawBoundaryLeftMarkedTailHeadPulledNearestRawBitTape_eq_emitSource
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    rawBoundaryLeftMarkedTailHeadPulledNearestRawBitTape
        pref count rawBit tailFirst tail =
      emitPulledRawBitCellChunkSourceTape
        count.length
        (List.append (pref.reverse.map some) [some false])
        rawBit tailFirst tail := by
  simp [rawBoundaryLeftMarkedTailHeadPulledNearestRawBitTape,
    markerAwarePullNearestRawBitTargetTape,
    pullNearestRawBitToTailMarkerTargetTape,
    emitPulledRawBitCellChunkSourceTape, Nat.add_assoc]

theorem rawBoundaryLeftMarkedTailHeadPulledNearestRawBitTape_moveLeftRight
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (rawBoundaryLeftMarkedTailHeadPulledNearestRawBitTape
            pref count rawBit tailFirst tail)) =
      rawBoundaryLeftMarkedTailHeadPulledNearestRawBitTape
        pref count rawBit tailFirst tail := by
  rw [rawBoundaryLeftMarkedTailHeadPulledNearestRawBitTape,
    markerAwarePullNearestRawBitTargetTape,
    pullNearestRawBitToTailMarkerTargetTape]
  exact
    tapeAtCells_move_right_move_left_cons
      (some rawBit)
      (List.append
        (List.replicate (count.length + 2 + 1)
          (none : Option Bool))
        (List.append (pref.reverse.map some) [some false]))
      (some tailFirst)
      tail

theorem emitPulledRawBitCellChunkDescription_haltsFrom_leftMarkedTailHeadPulled
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    emitPulledRawBitCellChunkDescription.HaltsFromTape
      (rawBoundaryLeftMarkedTailHeadPulledNearestRawBitTape
        pref count rawBit tailFirst tail)
      (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape
        pref count rawBit tailFirst tail) := by
  rw [rawBoundaryLeftMarkedTailHeadPulledNearestRawBitTape_eq_emitSource]
  simpa [rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape] using
    emitPulledRawBitCellChunkDescription_haltsFromTape
      count.length
      (List.append (pref.reverse.map some) [some false])
      rawBit tailFirst tail

def markerAwarePullAndEmitNearestRawBitCellDescription :
    MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    markerAwarePullNearestRawBitDescription
    emitPulledRawBitCellChunkDescription

theorem markerAwarePullAndEmitNearestRawBitCellDescription_subroutineReady :
    markerAwarePullAndEmitNearestRawBitCellDescription.SubroutineReady :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    markerAwarePullNearestRawBitDescription_subroutineReady
    emitPulledRawBitCellChunkDescription_subroutineReady

theorem markerAwarePullAndEmitNearestRawBitCellDescription_haltsFrom_leftMarkedTailHeadHandoff
    (skipped count pref : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) :
    markerAwarePullAndEmitNearestRawBitCellDescription.HaltsFromTape
      (rawBoundaryLeftMarkedTailHeadHandoffTape
        skipped count tailFirst tail)
      (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape
        pref count rawBit tailFirst tail) :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
    markerAwarePullNearestRawBitDescription_subroutineReady
    emitPulledRawBitCellChunkDescription_subroutineReady
    (rawBoundaryLeftMarkedTailHeadPulledNearestRawBit_haltsFrom
      skipped count pref rawBit tailFirst tail hlayout)
    (rawBoundaryLeftMarkedTailHeadPulledNearestRawBitTape_moveLeftRight
      pref count rawBit tailFirst tail)
    (emitPulledRawBitCellChunkDescription_haltsFrom_leftMarkedTailHeadPulled
      pref count rawBit tailFirst tail)

theorem rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape_cells
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.cells
        (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape
          pref count rawBit tailFirst tail) =
      some false ::
        List.append (pref.map some)
          (List.append
            (List.replicate count.length (none : Option Bool))
            (List.append
              ((pulledRawBitCellChunkBits rawBit).map some)
              (some tailFirst :: tail))) := by
  rw [rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape]
  simpa [List.reverse_append, List.map_reverse, List.append_assoc] using
    emitPulledRawBitCellChunkTargetTape_cells
      count.length
      (List.append (pref.reverse.map some) [some false])
      rawBit tailFirst tail

theorem rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape_left_length
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape
      pref count rawBit tailFirst tail).left.length =
      4 + count.length + pref.length + 1 := by
  rw [rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape]
  have h :=
    emitPulledRawBitCellChunkTargetTape_left_length
      count.length
      (List.append (pref.reverse.map some) [some false])
      rawBit tailFirst tail
  simp [List.length_append] at h
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape_moveLeftRight
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape
            pref count rawBit tailFirst tail)) =
      rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape
        pref count rawBit tailFirst tail := by
  rw [rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape]
  exact
    emitPulledRawBitCellChunkTargetTape_moveLeftRight
      count.length
      (List.append (pref.reverse.map some) [some false])
      rawBit tailFirst tail

theorem rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape_cells
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.cells
        (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape
          pref count rawBit tailFirst tail) =
      some false ::
        List.append (pref.map some)
          (List.append
            (List.replicate count.length (none : Option Bool))
            (List.append
              ((pulledRawBitCellChunkBits rawBit).map some)
              (some tailFirst :: tail))) := by
  cases rawBit <;>
    simp [rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape,
      Tape.cells, tapeAtCells, pulledRawBitCellChunkBits,
      preservingCellPassZeroBits, preservingCellPassOneBits,
      List.map_reverse, List.append_assoc]

theorem rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape_left_length
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape
      pref count rawBit tailFirst tail).left.length =
      count.length + pref.length + 1 := by
  cases rawBit <;>
    simp [rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape,
      tapeAtCells, pulledRawBitCellChunkBits,
      preservingCellPassZeroBits, preservingCellPassOneBits,
      List.length_append] <;>
    lia

theorem rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape_moveLeftRight
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape
            pref count rawBit tailFirst tail)) =
      rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape
        pref count rawBit tailFirst tail := by
  rw [rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape]
  simpa [List.append_assoc] using
    tapeAtCells_move_right_move_left_append_singleton
      (List.append (List.replicate count.length (none : Option Bool))
        (pref.reverse.map some))
      (some false)
      (List.append ((pulledRawBitCellChunkBits rawBit).map some)
        (some tailFirst :: tail))

theorem leftMoveAcrossFourNonblankCellsDescription_haltsFrom_leftMarkedTailHeadEmittedNearestRawBitCell
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    leftMoveAcrossFourNonblankCellsDescription.HaltsFromTape
      (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape
        pref count rawBit tailFirst tail)
      (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape
        pref count rawBit tailFirst tail) := by
  cases rawBit <;> cases tailFirst
  · simpa [rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape,
      rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape,
      emitPulledRawBitCellChunkTargetTape, pulledRawBitCellChunkBits,
      preservingCellPassZeroBits, List.append_assoc] using
      leftMoveAcrossFourNonblankCellsDescription_haltsFromTape
        false true false true false
        (List.append
          (List.replicate count.length (none : Option Bool))
          (List.append (pref.reverse.map some) [some false]))
        tail
  · simpa [rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape,
      rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape,
      emitPulledRawBitCellChunkTargetTape, pulledRawBitCellChunkBits,
      preservingCellPassZeroBits, List.append_assoc] using
      leftMoveAcrossFourNonblankCellsDescription_haltsFromTape
        false true false true true
        (List.append
          (List.replicate count.length (none : Option Bool))
          (List.append (pref.reverse.map some) [some false]))
        tail
  · simpa [rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape,
      rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape,
      emitPulledRawBitCellChunkTargetTape, pulledRawBitCellChunkBits,
      preservingCellPassOneBits, List.append_assoc] using
      leftMoveAcrossFourNonblankCellsDescription_haltsFromTape
        false true true false false
        (List.append
          (List.replicate count.length (none : Option Bool))
          (List.append (pref.reverse.map some) [some false]))
        tail
  · simpa [rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape,
      rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape,
      emitPulledRawBitCellChunkTargetTape, pulledRawBitCellChunkBits,
      preservingCellPassOneBits, List.append_assoc] using
      leftMoveAcrossFourNonblankCellsDescription_haltsFromTape
        false true true false true
        (List.append
          (List.replicate count.length (none : Option Bool))
          (List.append (pref.reverse.map some) [some false]))
        tail

theorem rawBoundaryLeftMarkedTailHeadPulledNextRawBitBeforeEmittedCellTape_cells
    (pref count : Word Bool)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.cells
        (rawBoundaryLeftMarkedTailHeadPulledNextRawBitBeforeEmittedCellTape
          pref count nextRawBit emittedRawBit tailFirst tail) =
      some false ::
        List.append (pref.map some)
          (List.append
            (List.replicate count.length (none : Option Bool))
            (some nextRawBit ::
              List.append
                ((pulledRawBitCellChunkBits emittedRawBit).map some)
                (some tailFirst :: tail))) := by
  cases emittedRawBit <;>
    simp [rawBoundaryLeftMarkedTailHeadPulledNextRawBitBeforeEmittedCellTape,
      Tape.cells, tapeAtCells, pulledRawBitCellChunkBits,
      preservingCellPassZeroBits, preservingCellPassOneBits,
      List.map_reverse, List.append_assoc]

theorem rawBoundaryLeftMarkedTailHeadPulledNextRawBitBeforeEmittedCellTape_left_length
    (pref count : Word Bool)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    (rawBoundaryLeftMarkedTailHeadPulledNextRawBitBeforeEmittedCellTape
      pref count nextRawBit emittedRawBit tailFirst tail).left.length =
      count.length + pref.length + 2 := by
  cases emittedRawBit <;>
    simp [rawBoundaryLeftMarkedTailHeadPulledNextRawBitBeforeEmittedCellTape,
      tapeAtCells, pulledRawBitCellChunkBits, preservingCellPassZeroBits,
      preservingCellPassOneBits, List.length_append] <;>
    lia

theorem rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_cells
    (pref : Word Bool) (scratchTail : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.cells
        (rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
          pref scratchTail nextRawBit emittedRawBit tailFirst tail) =
      some false ::
        List.append (pref.map some)
          (List.append
            (List.replicate scratchTail (none : Option Bool))
            (List.append
              ((pulledRawBitCellChunkBits nextRawBit).map some)
              (List.append
                ((pulledRawBitCellChunkBits emittedRawBit).map some)
                (some tailFirst :: tail)))) := by
  cases nextRawBit <;> cases emittedRawBit <;>
    simp [rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape,
      Tape.cells, tapeAtCells, pulledRawBitCellChunkBits,
      preservingCellPassZeroBits, preservingCellPassOneBits,
      List.map_reverse, List.append_assoc]

theorem rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_left_length
    (pref : Word Bool) (scratchTail : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    (rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
      pref scratchTail nextRawBit emittedRawBit tailFirst tail).left.length =
      scratchTail + pref.length + 1 := by
  cases nextRawBit <;> cases emittedRawBit <;>
    simp [rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape,
      tapeAtCells, pulledRawBitCellChunkBits,
      preservingCellPassZeroBits, preservingCellPassOneBits,
      List.length_append]
  all_goals lia

theorem rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_moveLeftRight
    (pref : Word Bool) (scratchTail : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
            pref scratchTail nextRawBit emittedRawBit tailFirst tail)) =
      rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
        pref scratchTail nextRawBit emittedRawBit tailFirst tail := by
  rw [rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape]
  simpa [List.append_assoc] using
    tapeAtCells_move_right_move_left_append_singleton
      (List.append (List.replicate scratchTail (none : Option Bool))
        (pref.reverse.map some))
      (some false)
      (List.append ((pulledRawBitCellChunkBits nextRawBit).map some)
        (List.append ((pulledRawBitCellChunkBits emittedRawBit).map some)
          (some tailFirst :: tail)))

theorem markerAwarePullAndEmitNearestRawBitCellDescription_haltsFrom_headGap_real
    (scratchTail : Nat) (leftBit rawBit headBit : Bool)
    (baseTail : List (Option Bool)) (right : List (Option Bool)) :
    markerAwarePullAndEmitNearestRawBitCellDescription.HaltsFromTape
      (markerAwarePullNearestRawBitToHeadMarkerSourceTape
        (scratchTail + 3) (some leftBit :: baseTail) rawBit headBit right)
      (emitPulledRawBitCellChunkTargetTape
        scratchTail (some leftBit :: baseTail) rawBit headBit right) :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
    markerAwarePullNearestRawBitDescription_subroutineReady
    emitPulledRawBitCellChunkDescription_subroutineReady
    (markerAwarePullNearestRawBitDescription_haltsFromHeadGap_real
      (scratchTail + 3) leftBit rawBit headBit baseTail right)
    (by
      simpa [markerAwarePullNearestRawBitToHeadMarkerTargetTape] using
        pullNearestRawBitToHeadMarkerTargetTape_moveLeftRight
          scratchTail (some leftBit :: baseTail) rawBit headBit right)
    (by
      simpa [markerAwarePullNearestRawBitToHeadMarkerTargetTape] using
        emitPulledRawBitCellChunkDescription_haltsFrom_headGapPulled
          scratchTail (some leftBit :: baseTail) rawBit headBit right)

def markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription :
    MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    markerAwarePullAndEmitNearestRawBitCellDescription
    leftMoveAcrossFourNonblankCellsDescription

theorem markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription_subroutineReady :
    markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription.SubroutineReady :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    markerAwarePullAndEmitNearestRawBitCellDescription_subroutineReady
    leftMoveAcrossFourNonblankCellsDescription_subroutineReady

theorem markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_headGap_real
    (scratchTail : Nat) (leftBit rawBit headBit : Bool)
    (baseTail : List (Option Bool)) (right : List (Option Bool)) :
    markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription.HaltsFromTape
      (markerAwarePullNearestRawBitToHeadMarkerSourceTape
        (scratchTail + 3) (some leftBit :: baseTail) rawBit headBit right)
      (emitPulledRawBitCellChunkLeftEdgeTargetTape
        scratchTail (some leftBit :: baseTail) rawBit headBit right) :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
    markerAwarePullAndEmitNearestRawBitCellDescription_subroutineReady
    leftMoveAcrossFourNonblankCellsDescription_subroutineReady
    (markerAwarePullAndEmitNearestRawBitCellDescription_haltsFrom_headGap_real
      scratchTail leftBit rawBit headBit baseTail right)
    (emitPulledRawBitCellChunkTargetTape_moveLeftRight
      scratchTail (some leftBit :: baseTail) rawBit headBit right)
    (leftMoveAcrossFourNonblankCellsDescription_haltsFrom_emitPulledRawBitCellChunkTarget
      scratchTail (some leftBit :: baseTail) rawBit headBit right)

theorem rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape_eq_markerAwareHeadGapSource_false
    (pref count : Word Bool) (nextRawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape
        (List.append pref [nextRawBit]) count false tailFirst tail =
      markerAwarePullNearestRawBitToHeadMarkerSourceTape
        count.length (List.append (pref.reverse.map some) [some false])
        nextRawBit false
        (some true :: some false :: some true :: some tailFirst :: tail) := by
  simp [rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape,
    markerAwarePullNearestRawBitToHeadMarkerSourceTape,
    pullNearestRawBitToHeadMarkerSourceTape,
    pulledRawBitCellChunkBits, preservingCellPassZeroBits,
    List.reverse_append, List.map_reverse]

theorem rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape_eq_markerAwareHeadGapSource_true
    (pref count : Word Bool) (nextRawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape
        (List.append pref [nextRawBit]) count true tailFirst tail =
      markerAwarePullNearestRawBitToHeadMarkerSourceTape
        count.length (List.append (pref.reverse.map some) [some false])
        nextRawBit false
        (some true :: some true :: some false :: some tailFirst :: tail) := by
  simp [rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape,
    markerAwarePullNearestRawBitToHeadMarkerSourceTape,
    pullNearestRawBitToHeadMarkerSourceTape,
    pulledRawBitCellChunkBits, preservingCellPassOneBits,
    List.reverse_append, List.map_reverse]

theorem rawBoundaryLeftMarkedTailHeadPulledNextRawBitBeforeEmittedCellTape_eq_markerAwareHeadGapTarget_false
    (pref count : Word Bool) (nextRawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    rawBoundaryLeftMarkedTailHeadPulledNextRawBitBeforeEmittedCellTape
        pref count nextRawBit false tailFirst tail =
      markerAwarePullNearestRawBitToHeadMarkerTargetTape
        count.length (List.append (pref.reverse.map some) [some false])
        nextRawBit false
        (some true :: some false :: some true :: some tailFirst :: tail) := by
  simp [rawBoundaryLeftMarkedTailHeadPulledNextRawBitBeforeEmittedCellTape,
    markerAwarePullNearestRawBitToHeadMarkerTargetTape,
    pullNearestRawBitToHeadMarkerTargetTape,
    pulledRawBitCellChunkBits, preservingCellPassZeroBits,
    List.map_reverse]

theorem rawBoundaryLeftMarkedTailHeadPulledNextRawBitBeforeEmittedCellTape_eq_markerAwareHeadGapTarget_true
    (pref count : Word Bool) (nextRawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    rawBoundaryLeftMarkedTailHeadPulledNextRawBitBeforeEmittedCellTape
        pref count nextRawBit true tailFirst tail =
      markerAwarePullNearestRawBitToHeadMarkerTargetTape
        count.length (List.append (pref.reverse.map some) [some false])
        nextRawBit false
        (some true :: some true :: some false :: some tailFirst :: tail) := by
  simp [rawBoundaryLeftMarkedTailHeadPulledNextRawBitBeforeEmittedCellTape,
    markerAwarePullNearestRawBitToHeadMarkerTargetTape,
    pullNearestRawBitToHeadMarkerTargetTape,
    pulledRawBitCellChunkBits, preservingCellPassOneBits,
    List.map_reverse]

theorem rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_eq_emitHeadGapLeftEdgeTarget_false
    (pref : Word Bool) (scratchTail : Nat)
    (nextRawBit tailFirst : Bool) (tail : List (Option Bool)) :
    rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
        pref scratchTail nextRawBit false tailFirst tail =
      emitPulledRawBitCellChunkLeftEdgeTargetTape
        scratchTail (List.append (pref.reverse.map some) [some false])
        nextRawBit false
        (some true :: some false :: some true :: some tailFirst :: tail) := by
  simp [rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape,
    emitPulledRawBitCellChunkLeftEdgeTargetTape,
    pulledRawBitCellChunkBits, preservingCellPassZeroBits,
    List.map_reverse]

theorem rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_eq_emitHeadGapLeftEdgeTarget_true
    (pref : Word Bool) (scratchTail : Nat)
    (nextRawBit tailFirst : Bool) (tail : List (Option Bool)) :
    rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
        pref scratchTail nextRawBit true tailFirst tail =
      emitPulledRawBitCellChunkLeftEdgeTargetTape
        scratchTail (List.append (pref.reverse.map some) [some false])
        nextRawBit false
        (some true :: some true :: some false :: some tailFirst :: tail) := by
  simp [rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape,
    emitPulledRawBitCellChunkLeftEdgeTargetTape,
    pulledRawBitCellChunkBits, preservingCellPassOneBits,
    List.map_reverse]

theorem markerAwarePullNearestRawBitDescription_haltsFrom_leftMarkedTailHeadEmittedNearestRawBitCellLeftEdge
    (pref count : Word Bool)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.HaltsFromTape
      (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape
        (List.append pref [nextRawBit]) count emittedRawBit tailFirst tail)
      (rawBoundaryLeftMarkedTailHeadPulledNextRawBitBeforeEmittedCellTape
        pref count nextRawBit emittedRawBit tailFirst tail) := by
  cases emittedRawBit
  · rw [
      rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape_eq_markerAwareHeadGapSource_false,
      rawBoundaryLeftMarkedTailHeadPulledNextRawBitBeforeEmittedCellTape_eq_markerAwareHeadGapTarget_false]
    cases hbase :
        List.append (pref.reverse.map some) [some false] with
    | nil =>
        have hlen := congrArg List.length hbase
        simp at hlen
    | cons head baseTail =>
        cases head with
        | none =>
            cases hrev : pref.reverse <;> simp [hrev] at hbase
        | some leftBit =>
            exact
              markerAwarePullNearestRawBitDescription_haltsFromHeadGap_real
                count.length leftBit nextRawBit false baseTail
                (some true :: some false :: some true ::
                  some tailFirst :: tail)
  · rw [
      rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape_eq_markerAwareHeadGapSource_true,
      rawBoundaryLeftMarkedTailHeadPulledNextRawBitBeforeEmittedCellTape_eq_markerAwareHeadGapTarget_true]
    cases hbase :
        List.append (pref.reverse.map some) [some false] with
    | nil =>
        have hlen := congrArg List.length hbase
        simp at hlen
    | cons head baseTail =>
        cases head with
        | none =>
            cases hrev : pref.reverse <;> simp [hrev] at hbase
        | some leftBit =>
            exact
              markerAwarePullNearestRawBitDescription_haltsFromHeadGap_real
                count.length leftBit nextRawBit false baseTail
                (some true :: some true :: some false ::
                  some tailFirst :: tail)

theorem markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_leftMarkedTailHeadEmittedNearestRawBitCellLeftEdge_of_count_length
    (pref count : Word Bool) (scratchTail : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hcount : count.length = scratchTail + 3) :
    markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription.HaltsFromTape
      (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape
        (List.append pref [nextRawBit]) count emittedRawBit tailFirst tail)
      (rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
        pref scratchTail nextRawBit emittedRawBit tailFirst tail) := by
  cases emittedRawBit
  · rw [
      rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape_eq_markerAwareHeadGapSource_false,
      rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_eq_emitHeadGapLeftEdgeTarget_false,
      hcount]
    cases hbase :
        List.append (pref.reverse.map some) [some false] with
    | nil =>
        have hlen := congrArg List.length hbase
        simp at hlen
    | cons head baseTail =>
        cases head with
        | none =>
            cases hrev : pref.reverse <;> simp [hrev] at hbase
        | some leftBit =>
            exact
              markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_headGap_real
                scratchTail leftBit nextRawBit false baseTail
                (some true :: some false :: some true ::
                  some tailFirst :: tail)
  · rw [
      rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape_eq_markerAwareHeadGapSource_true,
      rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_eq_emitHeadGapLeftEdgeTarget_true,
      hcount]
    cases hbase :
        List.append (pref.reverse.map some) [some false] with
    | nil =>
        have hlen := congrArg List.length hbase
        simp at hlen
    | cons head baseTail =>
        cases head with
        | none =>
            cases hrev : pref.reverse <;> simp [hrev] at hbase
        | some leftBit =>
            exact
              markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_headGap_real
                scratchTail leftBit nextRawBit false baseTail
                (some true :: some true :: some false ::
                  some tailFirst :: tail)

def rawBoundaryLeftMarkedStartToTailLeftHandoffDescription :
    MachineDescription :=
  seqSubroutine rightEdgeScanDescription
    rightBlankRunTailFirstLeftHandoffDescription Direction.right

theorem rawBoundaryLeftMarkedStartToTailLeftHandoffDescription_ready :
    rawBoundaryLeftMarkedStartToTailLeftHandoffDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    rightEdgeScanDescription_subroutineReady
    rightBlankRunTailFirstLeftHandoffDescription_subroutineReady

theorem rawBoundaryRightEdgeScanDescription_haltsFrom_leftMarkedStart
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    rightEdgeScanDescription.HaltsFromTape
      (rawBoundaryLeftMarkedStartTape skipped count tail)
      (rightEdgeScanTargetTapeFromLeft [some false]
        (List.append skipped count)
        (none ::
          none ::
          List.append
            (List.replicate count.length (none : Option Bool))
            tail)) := by
  simpa [rawBoundaryLeftMarkedStartTape,
    rightEdgeScanSourceTapeFromLeft, List.append_assoc] using
    rightEdgeScanDescription_haltsFromTape [some false]
      (List.append skipped count)
      (none ::
        none ::
        List.append
          (List.replicate count.length (none : Option Bool))
          tail)

theorem rawBoundaryRightEdgeScanTargetTape_moveRight_leftMarked
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape.move Direction.right
        (rightEdgeScanTargetTapeFromLeft [some false]
          (List.append skipped count)
          (none ::
            none ::
            List.append
              (List.replicate count.length (none : Option Bool))
              tail)) =
      rawBoundaryLeftMarkedRawRightEdgeTape skipped count tail := by
  rw [rightEdgeScanTargetTapeFromLeft,
    rawBoundaryLeftMarkedRawRightEdgeTape]
  exact
    tapeAtCells_move_right_move_left_append_singleton
      ((List.append skipped count).reverse.map some)
      (some false)
      (none ::
        none ::
          none ::
            List.append
              (List.replicate count.length (none : Option Bool))
              tail)

theorem rightBlankRunTailFirstLeftHandoffDescription_haltsFrom_leftMarkedRawRightEdge
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    rightBlankRunTailFirstLeftHandoffDescription.HaltsFromTape
      (rawBoundaryLeftMarkedRawRightEdgeTape
        skipped count (some tailFirst :: tail))
      (rawBoundaryLeftMarkedTailLeftHandoffTape
        skipped count tailFirst tail) := by
  have hsource :
      List.append
          (List.replicate (count.length + 2 + 1)
            (none : Option Bool))
          (some tailFirst :: tail) =
        none ::
          none ::
            none ::
              List.append
                (List.replicate count.length (none : Option Bool))
                (some tailFirst :: tail) := by
    rw [show count.length + 2 + 1 = 3 + count.length by
      lia]
    simpa [List.replicate_succ, List.append_assoc] using
      FoC.Computability.list_replicate_add_append
        (none : Option Bool) 3 count.length (some tailFirst :: tail)
  have hrun :=
    rightBlankRunTailFirstLeftHandoffDescription_haltsFromTape
      (count.length + 2)
      (List.append ((List.append skipped count).reverse.map some)
        [some false])
      tail
      tailFirst
  rw [hsource] at hrun
  simpa [rawBoundaryLeftMarkedRawRightEdgeTape,
    rawBoundaryLeftMarkedTailLeftHandoffTape,
    List.append_assoc] using hrun

theorem rawBoundaryLeftMarkedStartToTailLeftHandoffDescription_haltsFrom
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    rawBoundaryLeftMarkedStartToTailLeftHandoffDescription.HaltsFromTape
      (rawBoundaryLeftMarkedStartTape
        skipped count (some tailFirst :: tail))
      (rawBoundaryLeftMarkedTailLeftHandoffTape
        skipped count tailFirst tail) := by
  exact
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      rightEdgeScanDescription_subroutineReady
      rightBlankRunTailFirstLeftHandoffDescription_subroutineReady
      (rawBoundaryRightEdgeScanDescription_haltsFrom_leftMarkedStart
        skipped count (some tailFirst :: tail))
      (rawBoundaryRightEdgeScanTargetTape_moveRight_leftMarked
        skipped count (some tailFirst :: tail))
      (rightBlankRunTailFirstLeftHandoffDescription_haltsFrom_leftMarkedRawRightEdge
        skipped count tailFirst tail)

def rawBoundarySourceToLeftMarkedTailLeftHandoffDescription :
    MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    rawBoundarySourceToLeftMarkedStartDescription
    rawBoundaryLeftMarkedStartToTailLeftHandoffDescription

theorem rawBoundarySourceToLeftMarkedTailLeftHandoffDescription_ready :
    rawBoundarySourceToLeftMarkedTailLeftHandoffDescription.SubroutineReady :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    rawBoundarySourceToLeftMarkedStartDescription_ready
    rawBoundaryLeftMarkedStartToTailLeftHandoffDescription_ready

theorem rawBoundarySourceToLeftMarkedTailLeftHandoffDescription_haltsFrom_sourceTape
    (skipped count : Word Bool)
    (h : List.append skipped count ≠ [])
    (tailFirst : Bool) (tail : List (Option Bool)) :
    rawBoundarySourceToLeftMarkedTailLeftHandoffDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (rawBoundaryLeftMarkedTailLeftHandoffTape
        skipped count tailFirst tail) :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
    rawBoundarySourceToLeftMarkedStartDescription_ready
    rawBoundaryLeftMarkedStartToTailLeftHandoffDescription_ready
    (rawBoundarySourceToLeftMarkedStartDescription_haltsFrom_sourceTape
      skipped count h (some tailFirst :: tail))
    (rawBoundaryLeftMarkedStartTape_moveLeftRight
      skipped count h (some tailFirst :: tail))
    (rawBoundaryLeftMarkedStartToTailLeftHandoffDescription_haltsFrom
      skipped count tailFirst tail)

def rawBoundarySourceToLeftMarkedTailHeadHandoffDescription :
    MachineDescription :=
  seqSubroutine
    rawBoundarySourceToLeftMarkedTailLeftHandoffDescription
    ExactIdentityDescription Direction.right

theorem rawBoundarySourceToLeftMarkedTailHeadHandoffDescription_ready :
    rawBoundarySourceToLeftMarkedTailHeadHandoffDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    rawBoundarySourceToLeftMarkedTailLeftHandoffDescription_ready
    CommonGround.Identity.exactIdentityDescription_subroutineReady

theorem rawBoundarySourceToLeftMarkedTailHeadHandoffDescription_haltsFrom_sourceTape
    (skipped count : Word Bool)
    (h : List.append skipped count ≠ [])
    (tailFirst : Bool) (tail : List (Option Bool)) :
    rawBoundarySourceToLeftMarkedTailHeadHandoffDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (rawBoundaryLeftMarkedTailHeadHandoffTape
        skipped count tailFirst tail) :=
  CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
    rawBoundarySourceToLeftMarkedTailLeftHandoffDescription_ready
    CommonGround.Identity.exactIdentityDescription_subroutineReady
    (rawBoundarySourceToLeftMarkedTailLeftHandoffDescription_haltsFrom_sourceTape
      skipped count h tailFirst tail)
    (rawBoundaryLeftMarkedTailLeftHandoffTape_moveRight
      skipped count tailFirst tail)
    (CommonGround.Identity.exactIdentityDescription_haltsFromTape
      (rawBoundaryLeftMarkedTailHeadHandoffTape
        skipped count tailFirst tail))

def rawBoundarySourceFirstRawBitCellEmissionViaLeftMarkedBoundaryDescription :
    MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    rawBoundarySourceToLeftMarkedTailHeadHandoffDescription
    markerAwarePullAndEmitNearestRawBitCellDescription

theorem rawBoundarySourceFirstRawBitCellEmissionViaLeftMarkedBoundaryDescription_ready :
    rawBoundarySourceFirstRawBitCellEmissionViaLeftMarkedBoundaryDescription.SubroutineReady :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    rawBoundarySourceToLeftMarkedTailHeadHandoffDescription_ready
    markerAwarePullAndEmitNearestRawBitCellDescription_subroutineReady

theorem rawBoundarySourceFirstRawBitCellEmissionViaLeftMarkedBoundaryDescription_haltsFrom_sourceTape
    (skipped count pref : Word Bool)
    (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) :
    rawBoundarySourceFirstRawBitCellEmissionViaLeftMarkedBoundaryDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape
        pref count rawBit tailFirst tail) := by
  have hnonempty : List.append skipped count ≠ [] := by
    rw [hlayout]
    simp
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
      rawBoundarySourceToLeftMarkedTailHeadHandoffDescription_ready
      markerAwarePullAndEmitNearestRawBitCellDescription_subroutineReady
      (rawBoundarySourceToLeftMarkedTailHeadHandoffDescription_haltsFrom_sourceTape
        skipped count hnonempty tailFirst tail)
      (rawBoundaryLeftMarkedTailHeadHandoffTape_moveLeftRight
        skipped count tailFirst tail)
      (markerAwarePullAndEmitNearestRawBitCellDescription_haltsFrom_leftMarkedTailHeadHandoff
        skipped count pref rawBit tailFirst tail hlayout)

def rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaLeftMarkedBoundaryDescription :
    MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    rawBoundarySourceFirstRawBitCellEmissionViaLeftMarkedBoundaryDescription
    leftMoveAcrossFourNonblankCellsDescription

theorem rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaLeftMarkedBoundaryDescription_ready :
    rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaLeftMarkedBoundaryDescription.SubroutineReady :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    rawBoundarySourceFirstRawBitCellEmissionViaLeftMarkedBoundaryDescription_ready
    leftMoveAcrossFourNonblankCellsDescription_subroutineReady

theorem rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaLeftMarkedBoundaryDescription_haltsFrom_sourceTape
    (skipped count pref : Word Bool)
    (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) :
    rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaLeftMarkedBoundaryDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape
        pref count rawBit tailFirst tail) :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
    rawBoundarySourceFirstRawBitCellEmissionViaLeftMarkedBoundaryDescription_ready
    leftMoveAcrossFourNonblankCellsDescription_subroutineReady
    (rawBoundarySourceFirstRawBitCellEmissionViaLeftMarkedBoundaryDescription_haltsFrom_sourceTape
      skipped count pref rawBit tailFirst tail hlayout)
    (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape_moveLeftRight
      pref count rawBit tailFirst tail)
    (leftMoveAcrossFourNonblankCellsDescription_haltsFrom_leftMarkedTailHeadEmittedNearestRawBitCell
      pref count rawBit tailFirst tail)

theorem rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaLeftMarkedBoundaryDescription_exists
    (skipped count : Word Bool)
    (h : List.append skipped count ≠ [])
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    exists pref : Word Bool, exists rawBit : Bool,
      List.append skipped count = List.append pref [rawBit] ∧
        rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaLeftMarkedBoundaryDescription.HaltsFromTape
          (sourceTape skipped count (some tailFirst :: tail))
          (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape
            pref count rawBit tailFirst tail) := by
  rcases
      FoC.Computability.list_exists_append_singleton_of_ne_nil
        (List.append skipped count) h with
    ⟨pref, rawBit, hlayout⟩
  exact
    ⟨pref, rawBit, hlayout,
      rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaLeftMarkedBoundaryDescription_haltsFrom_sourceTape
        skipped count pref rawBit tailFirst tail hlayout⟩

def rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionViaLeftMarkedBoundaryDescription :
    MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaLeftMarkedBoundaryDescription
    markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription

theorem rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionViaLeftMarkedBoundaryDescription_ready :
    rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionViaLeftMarkedBoundaryDescription.SubroutineReady :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaLeftMarkedBoundaryDescription_ready
    markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription_subroutineReady

theorem rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionViaLeftMarkedBoundaryDescription_haltsFrom_sourceTape_of_count_length
    (skipped count pref : Word Bool) (scratchTail : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count =
        List.append (List.append pref [nextRawBit]) [emittedRawBit])
    (hcount : count.length = scratchTail + 3) :
    rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionViaLeftMarkedBoundaryDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
        pref scratchTail nextRawBit emittedRawBit tailFirst tail) :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
    rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaLeftMarkedBoundaryDescription_ready
    markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription_subroutineReady
    (rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaLeftMarkedBoundaryDescription_haltsFrom_sourceTape
      skipped count (List.append pref [nextRawBit]) emittedRawBit
      tailFirst tail hlayout)
    (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape_moveLeftRight
      (List.append pref [nextRawBit]) count emittedRawBit tailFirst tail)
    (markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_leftMarkedTailHeadEmittedNearestRawBitCellLeftEdge_of_count_length
      pref count scratchTail nextRawBit emittedRawBit tailFirst tail hcount)

theorem rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionViaLeftMarkedBoundaryDescription_haltsFrom_sourceTape_of_three_le_count_length
    (skipped count pref : Word Bool)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count =
        List.append (List.append pref [nextRawBit]) [emittedRawBit])
    (hcount : 3 <= count.length) :
    exists scratchTail : Nat,
      count.length = scratchTail + 3 ∧
        rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionViaLeftMarkedBoundaryDescription.HaltsFromTape
          (sourceTape skipped count (some tailFirst :: tail))
          (rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
            pref scratchTail nextRawBit emittedRawBit tailFirst tail) := by
  rcases nat_exists_eq_add_of_le hcount with ⟨scratchTail, hscratch⟩
  exact
    ⟨scratchTail, hscratch,
      rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionViaLeftMarkedBoundaryDescription_haltsFrom_sourceTape_of_count_length
        skipped count pref scratchTail nextRawBit emittedRawBit tailFirst
        tail hlayout hscratch⟩

theorem rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionViaLeftMarkedBoundaryDescription_haltsFrom_sourceTape_of_two_le_layout_length_three_le_count_length
    (skipped count : Word Bool)
    (hlayoutLength : 2 <= (List.append skipped count).length)
    (hcount : 3 <= count.length)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    exists pref : Word Bool, exists nextRawBit : Bool,
      exists emittedRawBit : Bool, exists scratchTail : Nat,
        List.append skipped count =
            List.append (List.append pref [nextRawBit]) [emittedRawBit] ∧
          count.length = scratchTail + 3 ∧
            rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionViaLeftMarkedBoundaryDescription.HaltsFromTape
              (sourceTape skipped count (some tailFirst :: tail))
              (rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
                pref scratchTail nextRawBit emittedRawBit tailFirst tail) := by
  rcases
      FoC.Computability.list_exists_append_two_of_two_le_length
        (List.append skipped count) hlayoutLength with
    ⟨pref, nextRawBit, emittedRawBit, hlayout⟩
  have hlayout' :
      List.append skipped count =
        List.append (List.append pref [nextRawBit]) [emittedRawBit] := by
    simpa [List.append_assoc] using hlayout
  rcases nat_exists_eq_add_of_le hcount with ⟨scratchTail, hscratch⟩
  exact
    ⟨pref, nextRawBit, emittedRawBit, scratchTail,
      hlayout', hscratch,
      rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionViaLeftMarkedBoundaryDescription_haltsFrom_sourceTape_of_count_length
        skipped count pref scratchTail nextRawBit emittedRawBit tailFirst
        tail hlayout' hscratch⟩

def rawBoundaryCountWindowStartTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells
    (none ::
      none ::
      none ::
      List.append
        ((List.append skipped count).reverse.map some)
        [none])
    (List.append
      (List.replicate count.length (none : Option Bool))
      tail)

theorem rawBoundaryCountWindowStartTape_cells_tailFirst
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.cells
        (rawBoundaryCountWindowStartTape
          skipped count (some tailFirst :: tail)) =
      none ::
        List.append (List.map some (List.append skipped count))
          (none ::
            none ::
            none ::
              List.append
                (List.replicate count.length (none : Option Bool))
                (some tailFirst :: tail)) := by
  cases count with
  | nil =>
      simp [rawBoundaryCountWindowStartTape, Tape.cells, tapeAtCells,
        List.reverse_append, List.map_reverse, List.append_assoc]
  | cons bit rest =>
      have hrep :
          List.replicate (rest.length + 1) (none : Option Bool) =
            none :: List.replicate rest.length (none : Option Bool) := by
        rw [show rest.length + 1 = Nat.succ rest.length by lia]
        rfl
      cases bit <;>
        simp [rawBoundaryCountWindowStartTape, Tape.cells, tapeAtCells,
          hrep, List.reverse_append, List.map_reverse,
          List.append_assoc]

def rawBoundaryScanToCountWindowStartDescription :
    MachineDescription :=
  seqSubroutine rightEdgeScanDescription
    rightMoveAcrossThreeBlanksDescription Direction.right

theorem rawBoundaryScanToCountWindowStartDescription_ready :
    rawBoundaryScanToCountWindowStartDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    rightEdgeScanDescription_subroutineReady
    rightMoveAcrossThreeBlanksDescription_subroutineReady

theorem rawBoundaryRightEdgeScanDescription_haltsFrom_sourceStart
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    rightEdgeScanDescription.HaltsFromTape
      (sourceStartTape skipped count tail)
      (rightEdgeScanTargetTapeFromLeft [none]
        (List.append skipped count)
        (none ::
          none ::
          List.append
            (List.replicate count.length (none : Option Bool))
            tail)) := by
  simpa [sourceStartTape, rightEdgeScanSourceTapeFromLeft,
    List.append_assoc] using
    rightEdgeScanDescription_haltsFromTape [none]
      (List.append skipped count)
      (none ::
        none ::
        List.append
          (List.replicate count.length (none : Option Bool))
          tail)

theorem rawBoundaryRightEdgeScanTargetTape_moveRight_threeBlankSource
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape.move Direction.right
        (rightEdgeScanTargetTapeFromLeft [none]
          (List.append skipped count)
          (none ::
            none ::
            List.append
              (List.replicate count.length (none : Option Bool))
              tail)) =
      tapeAtCells
        (List.append
          ((List.append skipped count).reverse.map some)
          [none])
        (none ::
          none ::
          none ::
          List.append
            (List.replicate count.length (none : Option Bool))
            tail) := by
  rw [rightEdgeScanTargetTapeFromLeft]
  exact
    tapeAtCells_move_right_move_left_append_singleton
      ((List.append skipped count).reverse.map some)
      (none : Option Bool)
      (none ::
        none ::
        none ::
        List.append
          (List.replicate count.length (none : Option Bool))
          tail)

theorem rawBoundaryScanToCountWindowStartDescription_haltsFrom_sourceStart
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    rawBoundaryScanToCountWindowStartDescription.HaltsFromTape
      (sourceStartTape skipped count tail)
      (rawBoundaryCountWindowStartTape skipped count tail) := by
  exact
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      rightEdgeScanDescription_subroutineReady
      rightMoveAcrossThreeBlanksDescription_subroutineReady
      (rawBoundaryRightEdgeScanDescription_haltsFrom_sourceStart
        skipped count tail)
      (rawBoundaryRightEdgeScanTargetTape_moveRight_threeBlankSource
        skipped count tail)
      (by
        simpa [rawBoundaryCountWindowStartTape] using
          rightMoveAcrossThreeBlanksDescription_haltsFromTape
            (List.append
              ((List.append skipped count).reverse.map some)
              [none])
            (List.append
              (List.replicate count.length (none : Option Bool))
              tail))

theorem sourceStartTape_move_left_move_right
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (sourceStartTape skipped count tail)) =
      sourceStartTape skipped count tail := by
  simpa [sourceStartTape, rightEdgeScanSourceTapeFromLeft,
    List.append_assoc] using
    rightEdgeScanSourceTapeFromLeft_move_left_move_right_padding_cons
      [none] (List.append skipped count) (none : Option Bool)
      (none ::
        List.append
          (List.replicate count.length (none : Option Bool))
          tail)

def rawBoundarySourceToCountWindowStartDescription :
    MachineDescription :=
  canonicalSeqDescription
    rightEdgeRewindDescription
    rawBoundaryScanToCountWindowStartDescription

theorem rawBoundarySourceToCountWindowStartDescription_ready :
    rawBoundarySourceToCountWindowStartDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    rightEdgeRewindDescription_subroutineReady
    rawBoundaryScanToCountWindowStartDescription_ready

theorem rawBoundarySourceToCountWindowStartDescription_haltsFrom_sourceTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    rawBoundarySourceToCountWindowStartDescription.HaltsFromTape
      (sourceTape skipped count tail)
      (rawBoundaryCountWindowStartTape skipped count tail) := by
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      rightEdgeRewindDescription_subroutineReady
      rawBoundaryScanToCountWindowStartDescription_ready
      (rightEdgeRewindDescription_haltsFrom_sourceTape_sourceStart
        skipped count tail)
      (sourceStartTape_move_left_move_right skipped count tail)
      (rawBoundaryScanToCountWindowStartDescription_haltsFrom_sourceStart
        skipped count tail)

theorem rawBoundaryCountWindowStartTape_move_left_move_right_nonempty
    (skipped countRest : Word Bool) (countFirst tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (rawBoundaryCountWindowStartTape
            skipped (countFirst :: countRest) (some tailFirst :: tail))) =
      rawBoundaryCountWindowStartTape
        skipped (countFirst :: countRest) (some tailFirst :: tail) := by
  cases countRest with
  | nil =>
      cases countFirst <;> cases tailFirst <;> cases tail <;>
        simp [rawBoundaryCountWindowStartTape, tapeAtCells,
          Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons next rest =>
      cases countFirst <;> cases next <;>
        simp [rawBoundaryCountWindowStartTape, tapeAtCells,
          Tape.move, Tape.moveLeft, Tape.moveRight,
          List.replicate_succ]

theorem rightBlankRunTailFirstLeftHandoffDescription_haltsFrom_countWindowStart
    (skipped countRest : Word Bool) (countFirst tailFirst : Bool)
    (tail : List (Option Bool)) :
    rightBlankRunTailFirstLeftHandoffDescription.HaltsFromTape
      (rawBoundaryCountWindowStartTape
        skipped (countFirst :: countRest) (some tailFirst :: tail))
      (tailLeftHandoffTape
        skipped (countFirst :: countRest) tailFirst tail) := by
  let rawBase :=
    List.append
      ((List.append skipped (countFirst :: countRest)).reverse.map some)
      [none]
  have hleft :
      List.append
          (List.replicate countRest.length (none : Option Bool))
          (none :: none :: none :: rawBase) =
        none ::
        none ::
          none ::
            List.append
              (List.replicate countRest.length (none : Option Bool))
              rawBase := by
    calc
      List.append
          (List.replicate countRest.length (none : Option Bool))
          (none :: none :: none :: rawBase)
          =
        none ::
          List.append
            (List.replicate countRest.length (none : Option Bool))
            (none :: none :: rawBase) := by
          exact
            list_replicate_append_cons_eq_cons_append
              (none : Option Bool) countRest.length
              (none :: none :: rawBase)
      _ =
        none ::
          none ::
            List.append
              (List.replicate countRest.length (none : Option Bool))
              (none :: rawBase) := by
          simp [list_replicate_append_cons_eq_cons_append]
      _ =
        none ::
          none ::
            none ::
              List.append
                (List.replicate countRest.length (none : Option Bool))
                rawBase := by
          simp [list_replicate_append_cons_eq_cons_append]
  have hrun :=
    rightBlankRunTailFirstLeftHandoffDescription_haltsFromTape
      countRest.length
      (none :: none :: none :: rawBase)
      tail
      tailFirst
  rw [hleft] at hrun
  simpa [rawBoundaryCountWindowStartTape, tailLeftHandoffTape,
    rawBase, List.replicate_succ, Nat.add_assoc,
    List.append_assoc] using hrun

def rawBoundarySourceToTailLeftHandoffDescription :
    MachineDescription :=
  canonicalSeqDescription
    rawBoundarySourceToCountWindowStartDescription
    rightBlankRunTailFirstLeftHandoffDescription

theorem rawBoundarySourceToTailLeftHandoffDescription_ready :
    rawBoundarySourceToTailLeftHandoffDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    rawBoundarySourceToCountWindowStartDescription_ready
    rightBlankRunTailFirstLeftHandoffDescription_subroutineReady

theorem rawBoundarySourceToTailLeftHandoffDescription_haltsFrom_sourceTape
    (skipped countRest : Word Bool) (countFirst tailFirst : Bool)
    (tail : List (Option Bool)) :
    rawBoundarySourceToTailLeftHandoffDescription.HaltsFromTape
      (sourceTape skipped (countFirst :: countRest) (some tailFirst :: tail))
      (tailLeftHandoffTape
        skipped (countFirst :: countRest) tailFirst tail) := by
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      rawBoundarySourceToCountWindowStartDescription_ready
      rightBlankRunTailFirstLeftHandoffDescription_subroutineReady
      (rawBoundarySourceToCountWindowStartDescription_haltsFrom_sourceTape
        skipped (countFirst :: countRest) (some tailFirst :: tail))
      (rawBoundaryCountWindowStartTape_move_left_move_right_nonempty
        skipped countRest countFirst tailFirst tail)
      (rightBlankRunTailFirstLeftHandoffDescription_haltsFrom_countWindowStart
        skipped countRest countFirst tailFirst tail)

def rawBoundarySourceToTailHeadHandoffDescription :
    MachineDescription :=
  seqSubroutine rawBoundarySourceToTailLeftHandoffDescription
    ExactIdentityDescription Direction.right

theorem rawBoundarySourceToTailHeadHandoffDescription_ready :
    rawBoundarySourceToTailHeadHandoffDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    rawBoundarySourceToTailLeftHandoffDescription_ready
    CommonGround.Identity.exactIdentityDescription_subroutineReady

theorem rawBoundarySourceToTailHeadHandoffDescription_haltsFrom_sourceTape
    (skipped countRest : Word Bool) (countFirst tailFirst : Bool)
    (tail : List (Option Bool)) :
    rawBoundarySourceToTailHeadHandoffDescription.HaltsFromTape
      (sourceTape skipped (countFirst :: countRest) (some tailFirst :: tail))
      (tailHeadHandoffTape
        skipped (countFirst :: countRest) tailFirst tail) := by
  exact
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      rawBoundarySourceToTailLeftHandoffDescription_ready
      CommonGround.Identity.exactIdentityDescription_subroutineReady
      (rawBoundarySourceToTailLeftHandoffDescription_haltsFrom_sourceTape
        skipped countRest countFirst tailFirst tail)
      (tailLeftHandoffTape_moveRight
        skipped (countFirst :: countRest) tailFirst tail)
      (CommonGround.Identity.exactIdentityDescription_haltsFromTape
        (tailHeadHandoffTape
          skipped (countFirst :: countRest) tailFirst tail))

def rawBoundarySourceFirstRawBitCellEmissionViaCountWindowDescription :
    MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    rawBoundarySourceToTailHeadHandoffDescription
    pullAndEmitNearestRawBitCellDescription

theorem rawBoundarySourceFirstRawBitCellEmissionViaCountWindowDescription_ready :
    rawBoundarySourceFirstRawBitCellEmissionViaCountWindowDescription.SubroutineReady :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    rawBoundarySourceToTailHeadHandoffDescription_ready
    pullAndEmitNearestRawBitCellDescription_subroutineReady

theorem rawBoundarySourceFirstRawBitCellEmissionViaCountWindowDescription_haltsFrom_sourceTape
    (skipped countRest pref : Word Bool)
    (countFirst rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped (countFirst :: countRest) =
        List.append pref [rawBit]) :
    rawBoundarySourceFirstRawBitCellEmissionViaCountWindowDescription.HaltsFromTape
      (sourceTape skipped (countFirst :: countRest) (some tailFirst :: tail))
      (tailHeadEmittedNearestRawBitCellTape
        pref (countFirst :: countRest) rawBit tailFirst tail) :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
    rawBoundarySourceToTailHeadHandoffDescription_ready
    pullAndEmitNearestRawBitCellDescription_subroutineReady
    (rawBoundarySourceToTailHeadHandoffDescription_haltsFrom_sourceTape
      skipped countRest countFirst tailFirst tail)
    (tailHeadHandoffTape_moveLeftRight
      skipped (countFirst :: countRest) tailFirst tail)
    (pullAndEmitNearestRawBitCellDescription_haltsFrom_tailHeadHandoffTape
      skipped (countFirst :: countRest) pref rawBit tailFirst tail hlayout)

def rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaCountWindowDescription :
    MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    rawBoundarySourceFirstRawBitCellEmissionViaCountWindowDescription
    leftMoveAcrossFourNonblankCellsDescription

theorem rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaCountWindowDescription_ready :
    rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaCountWindowDescription.SubroutineReady :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    rawBoundarySourceFirstRawBitCellEmissionViaCountWindowDescription_ready
    leftMoveAcrossFourNonblankCellsDescription_subroutineReady

theorem rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaCountWindowDescription_haltsFrom_sourceTape
    (skipped countRest pref : Word Bool)
    (countFirst rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped (countFirst :: countRest) =
        List.append pref [rawBit]) :
    rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaCountWindowDescription.HaltsFromTape
      (sourceTape skipped (countFirst :: countRest) (some tailFirst :: tail))
      (tailHeadEmittedNearestRawBitCellLeftEdgeTape
        pref (countFirst :: countRest) rawBit tailFirst tail) :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
    rawBoundarySourceFirstRawBitCellEmissionViaCountWindowDescription_ready
    leftMoveAcrossFourNonblankCellsDescription_subroutineReady
    (rawBoundarySourceFirstRawBitCellEmissionViaCountWindowDescription_haltsFrom_sourceTape
      skipped countRest pref countFirst rawBit tailFirst tail hlayout)
    (tailHeadEmittedNearestRawBitCellTape_moveLeftRight
      pref (countFirst :: countRest) rawBit tailFirst tail)
    (leftMoveAcrossFourNonblankCellsDescription_haltsFrom_tailHeadEmittedNearestRawBitCell
      pref (countFirst :: countRest) rawBit tailFirst tail)

theorem rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaCountWindowDescription_exists
    (skipped countRest : Word Bool) (countFirst tailFirst : Bool)
    (tail : List (Option Bool)) :
    exists pref : Word Bool, exists rawBit : Bool,
      List.append skipped (countFirst :: countRest) =
          List.append pref [rawBit] ∧
        rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaCountWindowDescription.HaltsFromTape
          (sourceTape skipped (countFirst :: countRest)
            (some tailFirst :: tail))
          (tailHeadEmittedNearestRawBitCellLeftEdgeTape
            pref (countFirst :: countRest) rawBit tailFirst tail) := by
  have hnonempty :
      List.append skipped (countFirst :: countRest) ≠ [] := by
    cases skipped <;> simp
  rcases
      FoC.Computability.list_exists_append_singleton_of_ne_nil
        (List.append skipped (countFirst :: countRest)) hnonempty with
    ⟨pref, rawBit, hlayout⟩
  exact
    ⟨pref, rawBit, hlayout,
      rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaCountWindowDescription_haltsFrom_sourceTape
        skipped countRest pref countFirst rawBit tailFirst tail hlayout⟩

def guardedCountBoundaryRightEdgeTape
    (skipped count : Word Bool) (guardBit tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append ((List.append skipped count).reverse.map some) [none])
    (none ::
      some guardBit ::
        List.append
          (List.replicate count.length (none : Option Bool))
          (some tailFirst :: tail))

def guardedCountBoundaryLocatedTape
    (skipped count : Word Bool) (guardBit tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  countedSuffixBoundaryLocatorTargetTape skipped count (some guardBit)
    (some tailFirst :: tail)

theorem guardedCountBoundaryRightEdgeTape_cells
    (skipped count : Word Bool) (guardBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.cells
        (guardedCountBoundaryRightEdgeTape
          skipped count guardBit tailFirst tail) =
      none ::
        List.append (List.map some (List.append skipped count))
          (none ::
            some guardBit ::
              List.append
                (List.replicate count.length (none : Option Bool))
                (some tailFirst :: tail)) := by
  simp [guardedCountBoundaryRightEdgeTape, Tape.cells, tapeAtCells,
    List.reverse_append, List.map_reverse, List.map_append,
    List.append_assoc]

theorem guardedCountBoundaryLocatedTape_cells
    (skipped count : Word Bool) (guardBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.cells
        (guardedCountBoundaryLocatedTape
          skipped count guardBit tailFirst tail) =
      List.append (skipped.map some)
        (none ::
          List.append (count.map some)
            (none ::
              some guardBit ::
                List.append
                  (List.replicate count.length (none : Option Bool))
                  (some tailFirst :: tail))) := by
  simp [guardedCountBoundaryLocatedTape,
    countedSuffixBoundaryLocatorTargetTape,
    countedSuffixBoundaryLocatorPadding,
    rightEdgeScanSourceTapeFromLeft_cells,
    List.map_reverse, List.append_assoc]

theorem guardedCountBoundaryRightEdgeTape_move_left
    (skipped count : Word Bool) (guardBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.left
        (guardedCountBoundaryRightEdgeTape
          skipped count guardBit tailFirst tail) =
      countedSuffixBoundaryLocatorSourceTape skipped count (some guardBit)
        (some tailFirst :: tail) := by
  simp [guardedCountBoundaryRightEdgeTape,
    countedSuffixBoundaryLocatorSourceTape,
    countedSuffixBoundaryLocatorPadding,
    rightEdgeScanTargetTapeFromLeft, List.append_assoc]

def guardedCountBoundaryLocatorDescription : MachineDescription :=
  canonicalSeqDescription
    leftMoveOnceDescription
    countedSuffixBoundaryLocatorDescription

theorem guardedCountBoundaryLocatorDescription_ready :
    guardedCountBoundaryLocatorDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    leftMoveOnceDescription_subroutineReady
    countedSuffixBoundaryLocatorDescription_ready

theorem guardedCountBoundaryLocatorDescription_haltsFromTape
    (skipped countRest : Word Bool)
    (countFirst guardBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    guardedCountBoundaryLocatorDescription.HaltsFromTape
      (guardedCountBoundaryRightEdgeTape
        skipped (countFirst :: countRest) guardBit tailFirst tail)
      (guardedCountBoundaryLocatedTape
        skipped (countFirst :: countRest) guardBit tailFirst tail) := by
  have hLeft :
      leftMoveOnceDescription.HaltsFromTape
        (guardedCountBoundaryRightEdgeTape
          skipped (countFirst :: countRest) guardBit tailFirst tail)
        (Tape.move Direction.left
          (guardedCountBoundaryRightEdgeTape
            skipped (countFirst :: countRest) guardBit tailFirst tail)) :=
    leftMoveOnceDescription_haltsFromTape
      (guardedCountBoundaryRightEdgeTape
        skipped (countFirst :: countRest) guardBit tailFirst tail)
  have hLocator :
      countedSuffixBoundaryLocatorDescription.HaltsFromTape
        (countedSuffixBoundaryLocatorSourceTape
          skipped (countFirst :: countRest) (some guardBit)
          (some tailFirst :: tail))
        (guardedCountBoundaryLocatedTape
          skipped (countFirst :: countRest) guardBit tailFirst tail) := by
    simpa [guardedCountBoundaryLocatedTape] using
      countedSuffixBoundaryLocatorDescription_haltsFromTape
        skipped countRest countFirst guardBit tailFirst tail
  refine
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      leftMoveOnceDescription_subroutineReady
      countedSuffixBoundaryLocatorDescription_ready
      hLeft ?_ hLocator
  rw [guardedCountBoundaryRightEdgeTape_move_left]
  simpa [countedSuffixBoundaryLocatorSourceTape] using
    rightEdgeScanTargetTapeFromLeft_move_left_move_right
      [none] (List.append skipped (countFirst :: countRest))
      (countedSuffixBoundaryLocatorPadding
        (some guardBit) (countFirst :: countRest)
        (some tailFirst :: tail))

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround
end Computability
end FoC
