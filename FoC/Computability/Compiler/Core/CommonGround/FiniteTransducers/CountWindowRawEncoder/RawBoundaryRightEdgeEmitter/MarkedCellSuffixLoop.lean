import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.BoundaryEraser
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawEncoder.RawBoundaryRightEdgeEmitter.CellSuffixLoop
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawEncoder.RawBoundaryRightEdgeEmitter.CountedBoundary
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawEncoder.RawBoundaryRightEdgeEmitter.EndpointSupport
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.DispatcherAssembly.Runs

set_option doc.verso true

/-!
# Marked raw-boundary right-edge cell-suffix loop support

This module packages the marker-preserving variant of the reusable
raw-boundary cell-suffix loop.  The left marker stays in the base-left stack
while each step pulls the nearest remaining raw bit across the scratch gap,
emits that bit's cell chunk immediately before the already-emitted suffix, and
halts at the new suffix left edge.
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

def rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
    (pref : Word Bool) (scratchTail : Nat) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate scratchTail (none : Option Bool))
      (List.append (pref.reverse.map some) [some false]))
    (List.append
      ((preservingCellPassCellBits cellSuffix).map some)
      (some tailFirst :: tail))

theorem rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape_cells
    (pref : Word Bool) (scratchTail : Nat) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    Tape.cells
        (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
          pref scratchTail cellSuffix tailFirst tail) =
      some false ::
        List.append (pref.map some)
          (List.append
            (List.replicate scratchTail (none : Option Bool))
            (List.append
              ((preservingCellPassCellBits cellSuffix).map some)
              (some tailFirst :: tail))) := by
  cases cellSuffix with
  | nil =>
      simp [rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
        Tape.cells, tapeAtCells, preservingCellPassCellBits,
        List.map_reverse, List.append_assoc]
  | cons bit rest =>
      cases bit <;>
        simp [rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
          Tape.cells, tapeAtCells, preservingCellPassCellBits,
          preservingCellPassZeroBits, preservingCellPassOneBits,
          List.map_reverse, List.append_assoc]

theorem rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape_left_length
    (pref : Word Bool) (scratchTail : Nat) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
      pref scratchTail cellSuffix tailFirst tail).left.length =
      scratchTail + pref.length + 1 := by
  cases cellSuffix with
  | nil =>
      simp [rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
        tapeAtCells, preservingCellPassCellBits, List.length_append]
      lia
  | cons bit rest =>
      cases bit <;>
        simp [rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
          tapeAtCells, preservingCellPassCellBits,
          preservingCellPassZeroBits, preservingCellPassOneBits,
          List.length_append] <;>
        lia

theorem rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape_moveLeftRight
    (pref : Word Bool) (scratchTail : Nat) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
            pref scratchTail cellSuffix tailFirst tail)) =
      rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        pref scratchTail cellSuffix tailFirst tail := by
  rw [rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape]
  simpa [List.append_assoc] using
    tapeAtCells_move_right_move_left_append_singleton
      (List.append (List.replicate scratchTail (none : Option Bool))
        (pref.reverse.map some))
      (some false)
      (List.append ((preservingCellPassCellBits cellSuffix).map some)
        (some tailFirst :: tail))

theorem rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_eq_markedCellSuffixLeftEdgeScratch_pair
    (pref : Word Bool) (scratchTail : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
        pref scratchTail nextRawBit emittedRawBit tailFirst tail =
      rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        pref scratchTail [nextRawBit, emittedRawBit] tailFirst tail := by
  cases nextRawBit <;> cases emittedRawBit <;>
    simp [rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape,
      rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
      preservingCellPassCellBits, preservingCellPassZeroBits,
      preservingCellPassOneBits, pulledRawBitCellChunkBits]

theorem markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_headGap_leftMarkedBase
    (scratchTail : Nat) (pref : Word Bool)
    (rawBit headBit : Bool) (right : List (Option Bool)) :
    markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription.HaltsFromTape
      (markerAwarePullNearestRawBitToHeadMarkerSourceTape
        (scratchTail + 3) (List.append (pref.reverse.map some) [some false])
        rawBit headBit right)
      (emitPulledRawBitCellChunkLeftEdgeTargetTape
        scratchTail (List.append (pref.reverse.map some) [some false])
        rawBit headBit right) := by
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
              scratchTail leftBit rawBit headBit baseTail right

theorem markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_markedCellSuffixLeftEdgeScratch_of_scratch_length
    (pref cellSuffix : Word Bool) (currentScratch scratchTail : Nat)
    (rawBit tailFirst : Bool) (tail : List (Option Bool))
    (hscratch : currentScratch = scratchTail + 3) :
    markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription.HaltsFromTape
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        (List.append pref [rawBit]) currentScratch cellSuffix tailFirst tail)
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        pref scratchTail (rawBit :: cellSuffix) tailFirst tail) := by
  cases cellSuffix with
  | nil =>
      cases rawBit <;> cases tailFirst
      · simpa [rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
          markerAwarePullNearestRawBitToHeadMarkerSourceTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          hscratch, List.reverse_append, List.map_reverse,
          List.append_assoc] using
          markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_headGap_leftMarkedBase
            scratchTail pref false false tail
      · simpa [rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
          markerAwarePullNearestRawBitToHeadMarkerSourceTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          hscratch, List.reverse_append, List.map_reverse,
          List.append_assoc] using
          markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_headGap_leftMarkedBase
            scratchTail pref false true tail
      · simpa [rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
          markerAwarePullNearestRawBitToHeadMarkerSourceTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          hscratch, List.reverse_append, List.map_reverse,
          List.append_assoc] using
          markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_headGap_leftMarkedBase
            scratchTail pref true false tail
      · simpa [rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
          markerAwarePullNearestRawBitToHeadMarkerSourceTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          hscratch, List.reverse_append, List.map_reverse,
          List.append_assoc] using
          markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_headGap_leftMarkedBase
            scratchTail pref true true tail
  | cons suffixHead suffixRest =>
      cases rawBit <;> cases suffixHead
      · simpa [rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
          markerAwarePullNearestRawBitToHeadMarkerSourceTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          hscratch, List.reverse_append, List.map_reverse,
          List.append_assoc] using
          markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_headGap_leftMarkedBase
            scratchTail pref false false
            (some true :: some false :: some true ::
              List.append ((preservingCellPassCellBits suffixRest).map some)
              (some tailFirst :: tail))
      · simpa [rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
          markerAwarePullNearestRawBitToHeadMarkerSourceTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          hscratch, List.reverse_append, List.map_reverse,
          List.append_assoc] using
          markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_headGap_leftMarkedBase
            scratchTail pref false false
            (some true :: some true :: some false ::
              List.append ((preservingCellPassCellBits suffixRest).map some)
              (some tailFirst :: tail))
      · simpa [rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
          markerAwarePullNearestRawBitToHeadMarkerSourceTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          hscratch, List.reverse_append, List.map_reverse,
          List.append_assoc] using
          markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_headGap_leftMarkedBase
            scratchTail pref true false
            (some true :: some false :: some true ::
              List.append ((preservingCellPassCellBits suffixRest).map some)
              (some tailFirst :: tail))
      · simpa [rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
          markerAwarePullNearestRawBitToHeadMarkerSourceTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          hscratch, List.reverse_append, List.map_reverse,
          List.append_assoc] using
          markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_headGap_leftMarkedBase
            scratchTail pref true false
            (some true :: some true :: some false ::
              List.append ((preservingCellPassCellBits suffixRest).map some)
              (some tailFirst :: tail))

theorem markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_markedCellSuffixLeftEdgeScratch_succ3
    (pref cellSuffix : Word Bool) (scratchTail : Nat)
    (rawBit tailFirst : Bool) (tail : List (Option Bool)) :
    markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription.HaltsFromTape
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        (List.append pref [rawBit]) (scratchTail + 3) cellSuffix
        tailFirst tail)
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        pref scratchTail (rawBit :: cellSuffix) tailFirst tail) :=
  markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_markedCellSuffixLeftEdgeScratch_of_scratch_length
    pref cellSuffix (scratchTail + 3) scratchTail rawBit tailFirst tail rfl

def markerAwarePullRemainingRawBitsCellSuffixLeftEdgeDescription :
    Word Bool -> MachineDescription
  | [] => ExactIdentityDescription
  | _ :: rest =>
      CommonGround.SameHeadComposition.leftRightSeqDescription
        (markerAwarePullRemainingRawBitsCellSuffixLeftEdgeDescription rest)
        markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription

theorem markerAwarePullRemainingRawBitsCellSuffixLeftEdgeDescription_subroutineReady
    (remaining : Word Bool) :
    (markerAwarePullRemainingRawBitsCellSuffixLeftEdgeDescription
      remaining).SubroutineReady := by
  induction remaining with
  | nil =>
      simpa [markerAwarePullRemainingRawBitsCellSuffixLeftEdgeDescription] using
        CommonGround.Identity.exactIdentityDescription_subroutineReady
  | cons bit rest ih =>
      simpa [markerAwarePullRemainingRawBitsCellSuffixLeftEdgeDescription] using
        CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
          ih
          markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription_subroutineReady

theorem markerAwarePullRemainingRawBitsCellSuffixLeftEdgeDescription_haltsFrom
    (base remaining cellSuffix : Word Bool)
    (currentScratch finalScratch : Nat)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hscratch : currentScratch = finalScratch + 3 * remaining.length) :
    (markerAwarePullRemainingRawBitsCellSuffixLeftEdgeDescription
      remaining).HaltsFromTape
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        (List.append base remaining) currentScratch cellSuffix tailFirst tail)
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        base finalScratch (List.append remaining cellSuffix) tailFirst tail) := by
  induction remaining generalizing base cellSuffix currentScratch finalScratch with
  | nil =>
      have hcurrent : currentScratch = finalScratch := by
        simpa using hscratch
      subst currentScratch
      simpa [markerAwarePullRemainingRawBitsCellSuffixLeftEdgeDescription] using
        CommonGround.Identity.exactIdentityDescription_haltsFromTape
          (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
            base finalScratch cellSuffix tailFirst tail)
  | cons bit rest ih =>
      have hrest :
          currentScratch = (finalScratch + 3) + 3 * rest.length := by
        rw [hscratch]
        simp
        lia
      exact
        CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
          (markerAwarePullRemainingRawBitsCellSuffixLeftEdgeDescription_subroutineReady
            rest)
          markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription_subroutineReady
          (by
            simpa [List.append_assoc] using
              ih (List.append base [bit]) cellSuffix currentScratch
                (finalScratch + 3) hrest)
          (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape_moveLeftRight
            (List.append base [bit]) (finalScratch + 3)
            (List.append rest cellSuffix) tailFirst tail)
          (by
            simpa using
              markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_markedCellSuffixLeftEdgeScratch_succ3
                base (List.append rest cellSuffix) finalScratch bit
                tailFirst tail)

def rawBoundarySourceFirstTwoThenRemainingRawBitsCellSuffixLeftEdgeEmissionViaLeftMarkedBoundaryDescription
    (remaining : Word Bool) : MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionViaLeftMarkedBoundaryDescription
    (markerAwarePullRemainingRawBitsCellSuffixLeftEdgeDescription
      remaining)

theorem rawBoundarySourceFirstTwoThenRemainingRawBitsCellSuffixLeftEdgeEmissionViaLeftMarkedBoundaryDescription_ready
    (remaining : Word Bool) :
    (rawBoundarySourceFirstTwoThenRemainingRawBitsCellSuffixLeftEdgeEmissionViaLeftMarkedBoundaryDescription
      remaining).SubroutineReady :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionViaLeftMarkedBoundaryDescription_ready
    (markerAwarePullRemainingRawBitsCellSuffixLeftEdgeDescription_subroutineReady
      remaining)

theorem remainingCellSuffix_haltsFrom_sourceTape_ofCountLengths
    (skipped count remaining : Word Bool)
    (scratchAfterTwo finalScratch : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count =
        List.append (List.append remaining [nextRawBit]) [emittedRawBit])
    (hcount : count.length = scratchAfterTwo + 3)
    (hremainingScratch :
      scratchAfterTwo = finalScratch + 3 * remaining.length) :
    (rawBoundarySourceFirstTwoThenRemainingRawBitsCellSuffixLeftEdgeEmissionViaLeftMarkedBoundaryDescription
      remaining).HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) finalScratch
        (List.append remaining [nextRawBit, emittedRawBit])
        tailFirst tail) := by
  rw [rawBoundarySourceFirstTwoThenRemainingRawBitsCellSuffixLeftEdgeEmissionViaLeftMarkedBoundaryDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
      rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionViaLeftMarkedBoundaryDescription_ready
      (markerAwarePullRemainingRawBitsCellSuffixLeftEdgeDescription_subroutineReady
        remaining)
      (rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionViaLeftMarkedBoundaryDescription_haltsFrom_sourceTape_of_count_length
        skipped count remaining scratchAfterTwo nextRawBit emittedRawBit
        tailFirst tail hlayout hcount)
      (by
        calc
          Tape.move Direction.right
              (Tape.move Direction.left
                (rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
                  remaining scratchAfterTwo nextRawBit emittedRawBit
                  tailFirst tail)) =
            rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
              remaining scratchAfterTwo nextRawBit emittedRawBit
              tailFirst tail :=
              rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_moveLeftRight
                remaining scratchAfterTwo nextRawBit emittedRawBit
                tailFirst tail
          _ =
            rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
              remaining scratchAfterTwo [nextRawBit, emittedRawBit]
              tailFirst tail :=
              rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_eq_markedCellSuffixLeftEdgeScratch_pair
                remaining scratchAfterTwo nextRawBit emittedRawBit
                tailFirst tail)
      (by
        simpa [List.append_assoc] using
          markerAwarePullRemainingRawBitsCellSuffixLeftEdgeDescription_haltsFrom
            ([] : Word Bool) remaining [nextRawBit, emittedRawBit]
            scratchAfterTwo finalScratch tailFirst tail hremainingScratch)

theorem remainingCellSuffix_haltsFrom_sourceTape_ofCountEnough
    (skipped count remaining : Word Bool)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count =
        List.append (List.append remaining [nextRawBit]) [emittedRawBit])
    (hcountEnough : 3 * remaining.length + 3 <= count.length) :
    exists scratchAfterTwo : Nat, exists finalScratch : Nat,
      count.length = scratchAfterTwo + 3 ∧
        scratchAfterTwo = finalScratch + 3 * remaining.length ∧
          (rawBoundarySourceFirstTwoThenRemainingRawBitsCellSuffixLeftEdgeEmissionViaLeftMarkedBoundaryDescription
            remaining).HaltsFromTape
            (sourceTape skipped count (some tailFirst :: tail))
            (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
              ([] : Word Bool) finalScratch
              (List.append remaining [nextRawBit, emittedRawBit])
              tailFirst tail) := by
  rcases nat_exists_eq_add_of_le hcountEnough with
    ⟨finalScratch, hlength⟩
  let scratchAfterTwo := finalScratch + 3 * remaining.length
  have hcount : count.length = scratchAfterTwo + 3 := by
    dsimp [scratchAfterTwo]
    rw [hlength]
    lia
  have hremainingScratch :
      scratchAfterTwo = finalScratch + 3 * remaining.length := rfl
  exact
    ⟨scratchAfterTwo, finalScratch, hcount, hremainingScratch,
      remainingCellSuffix_haltsFrom_sourceTape_ofCountLengths
        skipped count remaining scratchAfterTwo finalScratch nextRawBit
        emittedRawBit tailFirst tail hlayout hcount hremainingScratch⟩

theorem remainingCellSuffix_exists_ofLayoutCountEnough
    (skipped count : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hlayoutLength : 2 <= (List.append skipped count).length)
    (hcountEnough :
      3 * ((List.append skipped count).length - 2) + 3 <=
        count.length) :
    exists remaining : Word Bool, exists nextRawBit : Bool,
      exists emittedRawBit : Bool, exists scratchAfterTwo : Nat,
        exists finalScratch : Nat,
          List.append skipped count =
              List.append (List.append remaining [nextRawBit])
                [emittedRawBit] ∧
            count.length = scratchAfterTwo + 3 ∧
              scratchAfterTwo =
                finalScratch + 3 * remaining.length ∧
                (rawBoundarySourceFirstTwoThenRemainingRawBitsCellSuffixLeftEdgeEmissionViaLeftMarkedBoundaryDescription
                  remaining).HaltsFromTape
                  (sourceTape skipped count (some tailFirst :: tail))
                  (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
                    ([] : Word Bool) finalScratch
                    (List.append remaining [nextRawBit, emittedRawBit])
                    tailFirst tail) := by
  rcases
      FoC.Computability.list_exists_append_two_of_two_le_length
        (List.append skipped count) hlayoutLength with
    ⟨remaining, nextRawBit, emittedRawBit, hlayoutBase⟩
  have hlayout :
      List.append skipped count =
        List.append (List.append remaining [nextRawBit])
          [emittedRawBit] := by
    simpa [List.append_assoc] using hlayoutBase
  have hremainingLength :
      (List.append skipped count).length - 2 = remaining.length := by
    rw [hlayout]
    simp [List.length_append]
  have hcountRemaining :
      3 * remaining.length + 3 <= count.length := by
    rw [← hremainingLength]
    exact hcountEnough
  rcases
      remainingCellSuffix_haltsFrom_sourceTape_ofCountEnough
        skipped count remaining nextRawBit emittedRawBit tailFirst tail
        hlayout hcountRemaining with
    ⟨scratchAfterTwo, finalScratch, hcount, hscratch, hroute⟩
  exact
    ⟨remaining, nextRawBit, emittedRawBit, scratchAfterTwo, finalScratch,
      hlayout, hcount, hscratch, hroute⟩

def rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape
    (scratchTail : Nat) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells [none]
    (some false ::
      List.append
        (List.replicate scratchTail (none : Option Bool))
        (List.append
          ((preservingCellPassCellBits cellSuffix).map some)
          (some tailFirst :: tail)))

def rawBoundaryLeftMarkedCellSuffixMarkerErasedTape
    (scratchTail : Nat) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells [none]
    (none ::
      List.append
        (List.replicate scratchTail (none : Option Bool))
        (List.append
          ((preservingCellPassCellBits cellSuffix).map some)
          (some tailFirst :: tail)))

def rawBoundaryLeftMarkedCellSuffixMarkerErasedReturnedTape
    (scratchTail : Nat) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (none ::
      List.append
        (List.replicate scratchTail (none : Option Bool)) [none])
    (List.append
      ((preservingCellPassCellBits cellSuffix).map some)
      (some tailFirst :: tail))

def rawBoundaryCellSuffixRightAfterHead
    (cellFirst : Bool) (cellRest : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    List (Option Bool) :=
  match cellFirst with
  | false =>
      some true :: some false :: some true ::
        List.append ((preservingCellPassCellBits cellRest).map some)
          (some tailFirst :: tail)
  | true =>
      some true :: some true :: some false ::
        List.append ((preservingCellPassCellBits cellRest).map some)
          (some tailFirst :: tail)

private theorem dropTrailingNone_append_some_none_eq
    (xs : List (Option Bool)) (bit : Bool) :
    Tape.dropTrailingNone (List.append xs [some bit]) =
      Tape.dropTrailingNone (List.append xs [some bit, none]) := by
  simpa [List.append_assoc] using
    (FoC.Computability.dropTrailingNone_append_none
      (List.append xs [some bit])).symm

private theorem dropTrailingNone_replicate_none_append_none
    (n : Nat) :
    Tape.dropTrailingNone
        (List.append (List.replicate n (none : Option Bool)) [none]) =
      [] := by
  calc
    Tape.dropTrailingNone
        (List.append (List.replicate n (none : Option Bool)) [none]) =
      Tape.dropTrailingNone (List.replicate n (none : Option Bool)) := by
        simpa using
          FoC.Computability.dropTrailingNone_append_replicate_none
            (List.replicate n (none : Option Bool)) 1
    _ = [] :=
      FoC.Computability.dropTrailingNone_replicate_none n

private theorem dropTrailingNone_cons_replicate_none_append_none
    (n : Nat) :
    Tape.dropTrailingNone
        (none ::
          List.append (List.replicate n (none : Option Bool)) [none]) =
      [] := by
  rw [show none ::
        List.append (List.replicate n (none : Option Bool)) [none] =
      List.append
        (List.replicate (n + 1) (none : Option Bool)) [none] by
    rw [show n + 1 = Nat.succ n by lia]
    rfl]
  exact dropTrailingNone_replicate_none_append_none (n + 1)

theorem rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape_equiv_markerAwareBoundarySource_cons
    (scratchTail : Nat) (cellFirst : Bool) (cellRest : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    Tape.Equiv
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail (cellFirst :: cellRest)
        tailFirst tail)
      (markerAwarePullNearestRawBitToHeadMarkerSourceTape
        scratchTail ([none] : List (Option Bool)) false false
        (rawBoundaryCellSuffixRightAfterHead
          cellFirst cellRest tailFirst tail)) := by
  cases cellFirst <;>
    simp [Tape.Equiv,
      rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
      markerAwarePullNearestRawBitToHeadMarkerSourceTape,
      pullNearestRawBitToHeadMarkerSourceTape, tapeAtCells,
      rawBoundaryCellSuffixRightAfterHead,
      preservingCellPassCellBits, preservingCellPassZeroBits,
      preservingCellPassOneBits]
  · exact dropTrailingNone_append_some_none_eq
      (List.replicate scratchTail (none : Option Bool)) false
  · exact dropTrailingNone_append_some_none_eq
      (List.replicate scratchTail (none : Option Bool)) false

theorem markerAwarePullNearestRawBitDescription_haltsFrom_markedCellSuffixLeftEdge_boundary_cons
    (scratchTail : Nat) (cellFirst : Bool) (cellRest : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.HaltsFromTapeEquiv
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail (cellFirst :: cellRest)
        tailFirst tail)
      (rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape
        scratchTail (cellFirst :: cellRest) tailFirst tail) := by
  cases cellFirst
  · exact
      MachineDescription.HaltsFromTapeEquiv_of_input_equiv
        (D := markerAwarePullNearestRawBitDescription)
        (Tape.Equiv.symm
          (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape_equiv_markerAwareBoundarySource_cons
            scratchTail false cellRest tailFirst tail))
        (by
          simpa [rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape,
            rawBoundaryCellSuffixRightAfterHead, preservingCellPassCellBits,
            preservingCellPassZeroBits, preservingCellPassOneBits,
            List.append_assoc] using
            markerAwarePullNearestRawBitDescription_haltsFromHeadGap_boundary
              scratchTail ([] : List (Option Bool)) false false
              (rawBoundaryCellSuffixRightAfterHead
                false cellRest tailFirst tail))
  · exact
      MachineDescription.HaltsFromTapeEquiv_of_input_equiv
        (D := markerAwarePullNearestRawBitDescription)
        (Tape.Equiv.symm
          (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape_equiv_markerAwareBoundarySource_cons
            scratchTail true cellRest tailFirst tail))
        (by
          simpa [rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape,
            rawBoundaryCellSuffixRightAfterHead, preservingCellPassCellBits,
            preservingCellPassZeroBits, preservingCellPassOneBits,
            List.append_assoc] using
            markerAwarePullNearestRawBitDescription_haltsFromHeadGap_boundary
              scratchTail ([] : List (Option Bool)) false false
              (rawBoundaryCellSuffixRightAfterHead
                true cellRest tailFirst tail))

theorem markerAwarePullNearestRawBitDescription_haltsFrom_markedCellSuffixLeftEdge_boundary_nonempty
    (scratchTail : Nat) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hnonempty : cellSuffix ≠ []) :
    markerAwarePullNearestRawBitDescription.HaltsFromTapeEquiv
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail cellSuffix tailFirst tail)
      (rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape
        scratchTail cellSuffix tailFirst tail) := by
  cases cellSuffix with
  | nil =>
      exact False.elim (hnonempty rfl)
  | cons cellFirst cellRest =>
      exact
        markerAwarePullNearestRawBitDescription_haltsFrom_markedCellSuffixLeftEdge_boundary_cons
          scratchTail cellFirst cellRest tailFirst tail

theorem leftBoundaryEraserDescription_haltsFrom_markedCellSuffixBoundaryMarker_cons
    (scratchTail : Nat) (cellFirst : Bool) (cellRest : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    leftBoundaryEraserDescription.HaltsFromTape
      (rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape
        scratchTail (cellFirst :: cellRest) tailFirst tail)
      (rawBoundaryLeftMarkedCellSuffixMarkerErasedTape
        scratchTail (cellFirst :: cellRest) tailFirst tail) := by
  cases scratchTail with
  | zero =>
      cases cellFirst
      · simpa [rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape,
          rawBoundaryLeftMarkedCellSuffixMarkerErasedTape,
          leftBoundaryEraserSourceTape, leftBoundaryEraserTargetTape,
          rawBoundaryCellSuffixRightAfterHead, preservingCellPassCellBits,
          preservingCellPassZeroBits, preservingCellPassOneBits,
          tapeAtCells, Tape.move, Tape.moveLeft, List.append_assoc] using
          leftBoundaryEraserDescription_haltsFromTape
            ([] : List (Option Bool)) [false] (some false)
            (rawBoundaryCellSuffixRightAfterHead
              false cellRest tailFirst tail)
      · simpa [rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape,
          rawBoundaryLeftMarkedCellSuffixMarkerErasedTape,
          leftBoundaryEraserSourceTape, leftBoundaryEraserTargetTape,
          rawBoundaryCellSuffixRightAfterHead, preservingCellPassCellBits,
          preservingCellPassZeroBits, preservingCellPassOneBits,
          tapeAtCells, Tape.move, Tape.moveLeft, List.append_assoc] using
          leftBoundaryEraserDescription_haltsFromTape
            ([] : List (Option Bool)) [false] (some false)
            (rawBoundaryCellSuffixRightAfterHead
              true cellRest tailFirst tail)
  | succ scratchTail =>
      cases cellFirst
      · simpa [rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape,
          rawBoundaryLeftMarkedCellSuffixMarkerErasedTape,
          leftBoundaryEraserSourceTape, leftBoundaryEraserTargetTape,
          rawBoundaryCellSuffixRightAfterHead, preservingCellPassCellBits,
          preservingCellPassZeroBits, preservingCellPassOneBits,
          tapeAtCells, Tape.move, Tape.moveLeft, List.replicate_succ,
          List.append_assoc] using
          leftBoundaryEraserDescription_haltsFromTape
            ([] : List (Option Bool)) [false] none
            (List.append
              (List.replicate scratchTail (none : Option Bool))
              (some false ::
                rawBoundaryCellSuffixRightAfterHead
                  false cellRest tailFirst tail))
      · simpa [rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape,
          rawBoundaryLeftMarkedCellSuffixMarkerErasedTape,
          leftBoundaryEraserSourceTape, leftBoundaryEraserTargetTape,
          rawBoundaryCellSuffixRightAfterHead, preservingCellPassCellBits,
          preservingCellPassZeroBits, preservingCellPassOneBits,
          tapeAtCells, Tape.move, Tape.moveLeft, List.replicate_succ,
          List.append_assoc] using
          leftBoundaryEraserDescription_haltsFromTape
            ([] : List (Option Bool)) [false] none
            (List.append
              (List.replicate scratchTail (none : Option Bool))
              (some false ::
                rawBoundaryCellSuffixRightAfterHead
                  true cellRest tailFirst tail))

theorem leftBoundaryEraserDescription_haltsFrom_markedCellSuffixBoundaryMarker_nonempty
    (scratchTail : Nat) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hnonempty : cellSuffix ≠ []) :
    leftBoundaryEraserDescription.HaltsFromTape
      (rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape
        scratchTail cellSuffix tailFirst tail)
      (rawBoundaryLeftMarkedCellSuffixMarkerErasedTape
        scratchTail cellSuffix tailFirst tail) := by
  cases cellSuffix with
  | nil =>
      exact False.elim (hnonempty rfl)
  | cons cellFirst cellRest =>
      exact
        leftBoundaryEraserDescription_haltsFrom_markedCellSuffixBoundaryMarker_cons
          scratchTail cellFirst cellRest tailFirst tail

theorem rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape_moveLeftRight
    (scratchTail : Nat) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape
            scratchTail cellSuffix tailFirst tail)) =
      rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape
        scratchTail cellSuffix tailFirst tail := by
  simp [rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape, tapeAtCells,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem rawBoundaryLeftMarkedCellSuffixMarkerErasedTape_moveLeftRight
    (scratchTail : Nat) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (rawBoundaryLeftMarkedCellSuffixMarkerErasedTape
            scratchTail cellSuffix tailFirst tail)) =
      rawBoundaryLeftMarkedCellSuffixMarkerErasedTape
        scratchTail cellSuffix tailFirst tail := by
  simp [rawBoundaryLeftMarkedCellSuffixMarkerErasedTape, tapeAtCells,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem rawBoundaryLeftMarkedCellSuffixMarkerErasedReturnedTape_equiv_unmarked_cons
    (scratchTail : Nat) (cellFirst : Bool) (cellRest : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    Tape.Equiv
      (rawBoundaryLeftMarkedCellSuffixMarkerErasedReturnedTape
        scratchTail (cellFirst :: cellRest) tailFirst tail)
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail (cellFirst :: cellRest)
        tailFirst tail) := by
  cases cellFirst <;>
    simp [Tape.Equiv,
      rawBoundaryLeftMarkedCellSuffixMarkerErasedReturnedTape,
      tailHeadEmittedCellSuffixLeftEdgeScratchTape, tapeAtCells,
      preservingCellPassCellBits, preservingCellPassZeroBits,
      preservingCellPassOneBits]
  · exact
      (dropTrailingNone_cons_replicate_none_append_none
        scratchTail).trans
        (dropTrailingNone_replicate_none_append_none scratchTail).symm
  · exact
      (dropTrailingNone_cons_replicate_none_append_none
        scratchTail).trans
        (dropTrailingNone_replicate_none_append_none scratchTail).symm

def rawBoundaryMarkedCellSuffixTailHandoffReturnDescription :
    MachineDescription :=
  seqSubroutine rightBlankRunTailFirstLeftHandoffDescription
    ExactIdentityDescription Direction.right

theorem rawBoundaryMarkedCellSuffixTailHandoffReturnDescription_subroutineReady :
    rawBoundaryMarkedCellSuffixTailHandoffReturnDescription.SubroutineReady := by
  rw [rawBoundaryMarkedCellSuffixTailHandoffReturnDescription]
  exact
    seqSubroutine_subroutineReady
      rightBlankRunTailFirstLeftHandoffDescription_subroutineReady
      CommonGround.Identity.exactIdentityDescription_subroutineReady

theorem rawBoundaryMarkedCellSuffixTailHandoffReturnDescription_haltsFrom_erasedMarker_cons
    (scratchTail : Nat) (cellFirst : Bool) (cellRest : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    rawBoundaryMarkedCellSuffixTailHandoffReturnDescription.HaltsFromTapeEquiv
      (rawBoundaryLeftMarkedCellSuffixMarkerErasedTape
        scratchTail (cellFirst :: cellRest) tailFirst tail)
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail (cellFirst :: cellRest)
        tailFirst tail) := by
  rw [rawBoundaryMarkedCellSuffixTailHandoffReturnDescription]
  cases cellFirst
  · refine
      ⟨rawBoundaryLeftMarkedCellSuffixMarkerErasedReturnedTape
          scratchTail (false :: cellRest) tailFirst tail,
        ?_, rawBoundaryLeftMarkedCellSuffixMarkerErasedReturnedTape_equiv_unmarked_cons
          scratchTail false cellRest tailFirst tail⟩
    exact
      CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
        rightBlankRunTailFirstLeftHandoffDescription_subroutineReady
        CommonGround.Identity.exactIdentityDescription_subroutineReady
        (by
          simpa [rawBoundaryLeftMarkedCellSuffixMarkerErasedTape,
            rawBoundaryCellSuffixRightAfterHead,
            preservingCellPassCellBits, preservingCellPassZeroBits,
            preservingCellPassOneBits, List.replicate_succ,
            List.append_assoc] using
            rightBlankRunTailFirstLeftHandoffDescription_haltsFromTape
              scratchTail ([none] : List (Option Bool))
              (rawBoundaryCellSuffixRightAfterHead
                false cellRest tailFirst tail) false)
        (by
          simpa [rawBoundaryLeftMarkedCellSuffixMarkerErasedReturnedTape,
            rawBoundaryCellSuffixRightAfterHead,
            preservingCellPassCellBits, preservingCellPassZeroBits,
            preservingCellPassOneBits, List.append_assoc] using
            rightBlankRunTailFirstLeftHandoffDescription_handoff_right
              scratchTail ([none] : List (Option Bool))
              (rawBoundaryCellSuffixRightAfterHead
                false cellRest tailFirst tail) false)
        (CommonGround.Identity.exactIdentityDescription_haltsFromTape
          (rawBoundaryLeftMarkedCellSuffixMarkerErasedReturnedTape
            scratchTail (false :: cellRest) tailFirst tail))
  · refine
      ⟨rawBoundaryLeftMarkedCellSuffixMarkerErasedReturnedTape
          scratchTail (true :: cellRest) tailFirst tail,
        ?_, rawBoundaryLeftMarkedCellSuffixMarkerErasedReturnedTape_equiv_unmarked_cons
          scratchTail true cellRest tailFirst tail⟩
    exact
      CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
        rightBlankRunTailFirstLeftHandoffDescription_subroutineReady
        CommonGround.Identity.exactIdentityDescription_subroutineReady
        (by
          simpa [rawBoundaryLeftMarkedCellSuffixMarkerErasedTape,
            rawBoundaryCellSuffixRightAfterHead,
            preservingCellPassCellBits, preservingCellPassZeroBits,
            preservingCellPassOneBits, List.replicate_succ,
            List.append_assoc] using
            rightBlankRunTailFirstLeftHandoffDescription_haltsFromTape
              scratchTail ([none] : List (Option Bool))
              (rawBoundaryCellSuffixRightAfterHead
                true cellRest tailFirst tail) false)
        (by
          simpa [rawBoundaryLeftMarkedCellSuffixMarkerErasedReturnedTape,
            rawBoundaryCellSuffixRightAfterHead,
            preservingCellPassCellBits, preservingCellPassZeroBits,
            preservingCellPassOneBits, List.append_assoc] using
            rightBlankRunTailFirstLeftHandoffDescription_handoff_right
              scratchTail ([none] : List (Option Bool))
              (rawBoundaryCellSuffixRightAfterHead
                true cellRest tailFirst tail) false)
        (CommonGround.Identity.exactIdentityDescription_haltsFromTape
          (rawBoundaryLeftMarkedCellSuffixMarkerErasedReturnedTape
            scratchTail (true :: cellRest) tailFirst tail))

def rawBoundaryMarkedCellSuffixEraseThenReturnDescription :
    MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    leftBoundaryEraserDescription
    rawBoundaryMarkedCellSuffixTailHandoffReturnDescription

theorem rawBoundaryMarkedCellSuffixEraseThenReturnDescription_subroutineReady :
    rawBoundaryMarkedCellSuffixEraseThenReturnDescription.SubroutineReady := by
  rw [rawBoundaryMarkedCellSuffixEraseThenReturnDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
      leftBoundaryEraserDescription_subroutineReady
      rawBoundaryMarkedCellSuffixTailHandoffReturnDescription_subroutineReady

theorem rawBoundaryMarkedCellSuffixEraseThenReturnDescription_haltsFrom_boundaryMarker_cons
    (scratchTail : Nat) (cellFirst : Bool) (cellRest : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    rawBoundaryMarkedCellSuffixEraseThenReturnDescription.HaltsFromTapeEquiv
      (rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape
        scratchTail (cellFirst :: cellRest) tailFirst tail)
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail (cellFirst :: cellRest)
        tailFirst tail) := by
  rw [rawBoundaryMarkedCellSuffixEraseThenReturnDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTapeEquiv_of_haltsFromTape
      leftBoundaryEraserDescription_subroutineReady
      rawBoundaryMarkedCellSuffixTailHandoffReturnDescription_subroutineReady
      (leftBoundaryEraserDescription_haltsFrom_markedCellSuffixBoundaryMarker_cons
        scratchTail cellFirst cellRest tailFirst tail)
      (rawBoundaryLeftMarkedCellSuffixMarkerErasedTape_moveLeftRight
        scratchTail (cellFirst :: cellRest) tailFirst tail)
      (rawBoundaryMarkedCellSuffixTailHandoffReturnDescription_haltsFrom_erasedMarker_cons
        scratchTail cellFirst cellRest tailFirst tail)

theorem rawBoundaryMarkedCellSuffixEraseThenReturnDescription_haltsFrom_boundaryMarker_nonempty
    (scratchTail : Nat) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hnonempty : cellSuffix ≠ []) :
    rawBoundaryMarkedCellSuffixEraseThenReturnDescription.HaltsFromTapeEquiv
      (rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape
        scratchTail cellSuffix tailFirst tail)
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail cellSuffix tailFirst tail) := by
  cases cellSuffix with
  | nil =>
      exact False.elim (hnonempty rfl)
  | cons cellFirst cellRest =>
      exact
        rawBoundaryMarkedCellSuffixEraseThenReturnDescription_haltsFrom_boundaryMarker_cons
          scratchTail cellFirst cellRest tailFirst tail

def rawBoundaryPostPullBranchHalt : Nat := 2

def rawBoundaryPostPullRealBranchOffset : Nat := 3

def rawBoundaryPostPullBoundaryBranchOffset : Nat :=
  rawBoundaryPostPullRealBranchOffset +
    emitPulledRawBitCellChunkThenMoveLeftEdgeDescription.stateCount

def rawBoundaryPostPullRealBranchTarget : Nat :=
  rawBoundaryPostPullRealBranchOffset +
    emitPulledRawBitCellChunkThenMoveLeftEdgeDescription.start

def rawBoundaryPostPullBoundaryBranchTarget : Nat :=
  rawBoundaryPostPullBoundaryBranchOffset +
    rawBoundaryMarkedCellSuffixEraseThenReturnDescription.start

def rawBoundaryPostPullBranchDescription : MachineDescription where
  stateCount :=
    rawBoundaryPostPullBoundaryBranchOffset +
      rawBoundaryMarkedCellSuffixEraseThenReturnDescription.stateCount
  start := 0
  halt := rawBoundaryPostPullBranchHalt
  transitions :=
    [ transition 0 (some false) (some false) Direction.left 1
    , transition 0 (some true) (some true) Direction.left 1
    , transition 1 none none Direction.right
        rawBoundaryPostPullBoundaryBranchTarget
    , transition 1 (some false) (some false) Direction.right
        rawBoundaryPostPullRealBranchTarget
    , transition 1 (some true) (some true) Direction.right
        rawBoundaryPostPullRealBranchTarget ] ++
    (MachineDescription.offsetExitRetargetDescription
      rawBoundaryPostPullRealBranchOffset
      emitPulledRawBitCellChunkThenMoveLeftEdgeDescription.halt
      rawBoundaryPostPullBranchHalt
      emitPulledRawBitCellChunkThenMoveLeftEdgeDescription).transitions ++
    (MachineDescription.offsetExitRetargetDescription
      rawBoundaryPostPullBoundaryBranchOffset
      rawBoundaryMarkedCellSuffixEraseThenReturnDescription.halt
      rawBoundaryPostPullBranchHalt
      rawBoundaryMarkedCellSuffixEraseThenReturnDescription).transitions

theorem rawBoundaryPostPullBranchDescription_wellFormed :
    rawBoundaryPostPullBranchDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := rawBoundaryPostPullBranchDescription.transitions)
      (stateCount := rawBoundaryPostPullBranchDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := rawBoundaryPostPullBranchDescription.transitions)
      (by decide)

theorem rawBoundaryPostPullBranchDescription_haltTransitionFree :
    rawBoundaryPostPullBranchDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := rawBoundaryPostPullBranchDescription.transitions)
    (state := rawBoundaryPostPullBranchDescription.halt)
    (by decide)

theorem rawBoundaryPostPullBranchDescription_subroutineReady :
    rawBoundaryPostPullBranchDescription.SubroutineReady :=
  ⟨rawBoundaryPostPullBranchDescription_wellFormed,
    rawBoundaryPostPullBranchDescription_haltTransitionFree⟩

theorem rawBoundaryPostPullBranchDescription_run_dispatch_real
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool) (right : List (Option Bool)) :
    rawBoundaryPostPullBranchDescription.runConfig 2
        { state := rawBoundaryPostPullBranchDescription.start
          tape :=
            pullNearestRawBitToHeadMarkerTargetTape
              (scratchTail + 3) baseLeft rawBit headBit right } =
      { state := rawBoundaryPostPullRealBranchTarget
        tape :=
          pullNearestRawBitToHeadMarkerTargetTape
            (scratchTail + 3) baseLeft rawBit headBit right } := by
  cases rawBit <;> cases headBit <;>
    simp [rawBoundaryPostPullBranchDescription,
      rawBoundaryPostPullRealBranchTarget,
      pullNearestRawBitToHeadMarkerTargetTape, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem rawBoundaryPostPullBranchDescription_run_dispatch_boundary
    (gap : Nat) (baseTail : List (Option Bool))
    (markerBit headBit : Bool) (right : List (Option Bool)) :
    rawBoundaryPostPullBranchDescription.runConfig 2
        { state := rawBoundaryPostPullBranchDescription.start
          tape :=
            markerAwarePullNearestBoundaryToHeadMarkerTargetTape
              gap baseTail markerBit headBit right } =
      { state := rawBoundaryPostPullBoundaryBranchTarget
        tape :=
          markerAwarePullNearestBoundaryToHeadMarkerTargetTape
            gap baseTail markerBit headBit right } := by
  cases markerBit <;> cases headBit <;>
    simp [rawBoundaryPostPullBranchDescription,
      rawBoundaryPostPullBoundaryBranchTarget,
      markerAwarePullNearestBoundaryToHeadMarkerTargetTape, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem rawBoundaryPostPullBranchDescription_runsFrom_realTarget
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool) (right : List (Option Bool)) :
    Structured.MultiTapeLowering.RunsFromStateTapeEquiv
      rawBoundaryPostPullBranchDescription
      rawBoundaryPostPullRealBranchTarget
      rawBoundaryPostPullBranchHalt
      (pullNearestRawBitToHeadMarkerTargetTape
        (scratchTail + 3) baseLeft rawBit headBit right)
      (emitPulledRawBitCellChunkLeftEdgeTargetTape
        scratchTail baseLeft rawBit headBit right) := by
  let branch :=
    MachineDescription.offsetExitRetargetDescription
      rawBoundaryPostPullRealBranchOffset
      emitPulledRawBitCellChunkThenMoveLeftEdgeDescription.halt
      rawBoundaryPostPullBranchHalt
      emitPulledRawBitCellChunkThenMoveLeftEdgeDescription
  have hlocal :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        emitPulledRawBitCellChunkThenMoveLeftEdgeDescription
        emitPulledRawBitCellChunkThenMoveLeftEdgeDescription.start
        emitPulledRawBitCellChunkThenMoveLeftEdgeDescription.halt
        (pullNearestRawBitToHeadMarkerTargetTape
          (scratchTail + 3) baseLeft rawBit headBit right)
        (emitPulledRawBitCellChunkLeftEdgeTargetTape
          scratchTail baseLeft rawBit headBit right) := by
    rcases
        runConfig_eq_halt_of_haltsFromTape
          (emitPulledRawBitCellChunkThenMoveLeftEdgeDescription_haltsFrom_headGapPulled
            scratchTail baseLeft rawBit headBit right) with
      ⟨n, hrun⟩
    exact
      ⟨n,
        emitPulledRawBitCellChunkLeftEdgeTargetTape
          scratchTail baseLeft rawBit headBit right,
        hrun,
        Tape.Equiv.refl
          (emitPulledRawBitCellChunkLeftEdgeTargetTape
            scratchTail baseLeft rawBit headBit right)⟩
  have hfree :
      emitPulledRawBitCellChunkThenMoveLeftEdgeDescription.TransitionFreeAt
        emitPulledRawBitCellChunkThenMoveLeftEdgeDescription.halt := by
    intro t ht
    exact
      emitPulledRawBitCellChunkThenMoveLeftEdgeDescription_subroutineReady.right
        t ht
  have hretarget :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        branch
        rawBoundaryPostPullRealBranchTarget
        rawBoundaryPostPullBranchHalt
        (pullNearestRawBitToHeadMarkerTargetTape
          (scratchTail + 3) baseLeft rawBit headBit right)
        (emitPulledRawBitCellChunkLeftEdgeTargetTape
          scratchTail baseLeft rawBit headBit right) := by
    have hstart_ne :
        emitPulledRawBitCellChunkThenMoveLeftEdgeDescription.start ≠
          emitPulledRawBitCellChunkThenMoveLeftEdgeDescription.halt := by
      decide
    have h :=
      Structured.MultiTapeLowering.runsFromStateTapeEquiv_offsetExitRetargetDescription
        (offset := rawBoundaryPostPullRealBranchOffset)
        (localExit :=
          emitPulledRawBitCellChunkThenMoveLeftEdgeDescription.halt)
        (target := rawBoundaryPostPullBranchHalt)
        (by decide)
        hfree
        hlocal
    simpa [branch, rawBoundaryPostPullRealBranchTarget, hstart_ne] using h
  have hsubset :
      forall t : TransitionDescription,
        t ∈ branch.transitions ->
          t ∈ rawBoundaryPostPullBranchDescription.transitions := by
    intro t ht
    simp [branch, rawBoundaryPostPullBranchDescription, ht]
  have hdet : rawBoundaryPostPullBranchDescription.Deterministic :=
    rawBoundaryPostPullBranchDescription_wellFormed.right.right.right.right
  have hbranchFree :
      branch.TransitionFreeAt rawBoundaryPostPullBranchHalt := by
    have hhalt :
        branch.HaltTransitionFree := by
      simpa [branch] using
        MachineDescription.offsetExitRetargetDescription_haltTransitionFree
          (offset := rawBoundaryPostPullRealBranchOffset)
          (localExit :=
            emitPulledRawBitCellChunkThenMoveLeftEdgeDescription.halt)
          (target := rawBoundaryPostPullBranchHalt)
          (by decide)
          emitPulledRawBitCellChunkThenMoveLeftEdgeDescription
    intro t ht
    simpa [branch, MachineDescription.offsetExitRetargetDescription] using
      hhalt t ht
  exact
    Structured.MultiTapeLowering.StaticDispatcherReaderAssembly.runsFromStateTapeEquiv_of_subset_deterministic_of_transitionFree
      hsubset hdet hbranchFree hretarget

theorem rawBoundaryPostPullBranchDescription_haltsFrom_real
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool) (right : List (Option Bool)) :
    rawBoundaryPostPullBranchDescription.HaltsFromTapeEquiv
      (pullNearestRawBitToHeadMarkerTargetTape
        (scratchTail + 3) baseLeft rawBit headBit right)
      (emitPulledRawBitCellChunkLeftEdgeTargetTape
        scratchTail baseLeft rawBit headBit right) := by
  let Tin :=
    pullNearestRawBitToHeadMarkerTargetTape
      (scratchTail + 3) baseLeft rawBit headBit right
  have hprefix :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        rawBoundaryPostPullBranchDescription
        rawBoundaryPostPullBranchDescription.start
        rawBoundaryPostPullRealBranchTarget
        Tin Tin := by
    refine ⟨2, Tin, ?_, Tape.Equiv.refl Tin⟩
    simpa [Tin] using
      rawBoundaryPostPullBranchDescription_run_dispatch_real
        scratchTail baseLeft rawBit headBit right
  have hbody :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        rawBoundaryPostPullBranchDescription
        rawBoundaryPostPullRealBranchTarget
        rawBoundaryPostPullBranchHalt
        Tin
        (emitPulledRawBitCellChunkLeftEdgeTargetTape
          scratchTail baseLeft rawBit headBit right) := by
    simpa [Tin] using
      rawBoundaryPostPullBranchDescription_runsFrom_realTarget
        scratchTail baseLeft rawBit headBit right
  have hrun :=
    Structured.MultiTapeLowering.runsFromStateTapeEquiv_trans
      hprefix hbody
  exact
    Structured.MultiTapeLowering.RunsFromStateTapeEquiv.toHaltsFromTapeEquiv
      hrun rfl (by rfl)

theorem rawBoundaryPostPullBranchDescription_runsFrom_boundaryTarget
    (scratchTail : Nat) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hnonempty : cellSuffix ≠ []) :
    Structured.MultiTapeLowering.RunsFromStateTapeEquiv
      rawBoundaryPostPullBranchDescription
      rawBoundaryPostPullBoundaryBranchTarget
      rawBoundaryPostPullBranchHalt
      (rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape
        scratchTail cellSuffix tailFirst tail)
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail cellSuffix tailFirst tail) := by
  let branch :=
    MachineDescription.offsetExitRetargetDescription
      rawBoundaryPostPullBoundaryBranchOffset
      rawBoundaryMarkedCellSuffixEraseThenReturnDescription.halt
      rawBoundaryPostPullBranchHalt
      rawBoundaryMarkedCellSuffixEraseThenReturnDescription
  have hlocal :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        rawBoundaryMarkedCellSuffixEraseThenReturnDescription
        rawBoundaryMarkedCellSuffixEraseThenReturnDescription.start
        rawBoundaryMarkedCellSuffixEraseThenReturnDescription.halt
        (rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape
          scratchTail cellSuffix tailFirst tail)
        (tailHeadEmittedCellSuffixLeftEdgeScratchTape
          ([] : Word Bool) scratchTail cellSuffix tailFirst tail) := by
    rcases
        rawBoundaryMarkedCellSuffixEraseThenReturnDescription_haltsFrom_boundaryMarker_nonempty
          scratchTail cellSuffix tailFirst tail hnonempty with
      ⟨actual, hactual, hequiv⟩
    rcases runConfig_eq_halt_of_haltsFromTape hactual with ⟨n, hrun⟩
    exact ⟨n, actual, hrun, hequiv⟩
  have hfree :
      rawBoundaryMarkedCellSuffixEraseThenReturnDescription.TransitionFreeAt
        rawBoundaryMarkedCellSuffixEraseThenReturnDescription.halt := by
    intro t ht
    exact
      rawBoundaryMarkedCellSuffixEraseThenReturnDescription_subroutineReady.right
        t ht
  have hretarget :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        branch
        rawBoundaryPostPullBoundaryBranchTarget
        rawBoundaryPostPullBranchHalt
        (rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape
          scratchTail cellSuffix tailFirst tail)
        (tailHeadEmittedCellSuffixLeftEdgeScratchTape
          ([] : Word Bool) scratchTail cellSuffix tailFirst tail) := by
    have hstart_ne :
        rawBoundaryMarkedCellSuffixEraseThenReturnDescription.start ≠
          rawBoundaryMarkedCellSuffixEraseThenReturnDescription.halt := by
      decide
    have h :=
      Structured.MultiTapeLowering.runsFromStateTapeEquiv_offsetExitRetargetDescription
        (offset := rawBoundaryPostPullBoundaryBranchOffset)
        (localExit :=
          rawBoundaryMarkedCellSuffixEraseThenReturnDescription.halt)
        (target := rawBoundaryPostPullBranchHalt)
        (by decide)
        hfree
        hlocal
    simpa [branch, rawBoundaryPostPullBoundaryBranchTarget, hstart_ne]
      using h
  have hsubset :
      forall t : TransitionDescription,
        t ∈ branch.transitions ->
          t ∈ rawBoundaryPostPullBranchDescription.transitions := by
    intro t ht
    simp [branch, rawBoundaryPostPullBranchDescription, ht]
  have hdet : rawBoundaryPostPullBranchDescription.Deterministic :=
    rawBoundaryPostPullBranchDescription_wellFormed.right.right.right.right
  have hbranchFree :
      branch.TransitionFreeAt rawBoundaryPostPullBranchHalt := by
    have hhalt :
        branch.HaltTransitionFree := by
      simpa [branch] using
        MachineDescription.offsetExitRetargetDescription_haltTransitionFree
          (offset := rawBoundaryPostPullBoundaryBranchOffset)
          (localExit :=
            rawBoundaryMarkedCellSuffixEraseThenReturnDescription.halt)
          (target := rawBoundaryPostPullBranchHalt)
          (by decide)
          rawBoundaryMarkedCellSuffixEraseThenReturnDescription
    intro t ht
    simpa [branch, MachineDescription.offsetExitRetargetDescription] using
      hhalt t ht
  exact
    Structured.MultiTapeLowering.StaticDispatcherReaderAssembly.runsFromStateTapeEquiv_of_subset_deterministic_of_transitionFree
      hsubset hdet hbranchFree hretarget

theorem rawBoundaryPostPullBranchDescription_haltsFrom_boundary
    (scratchTail : Nat) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hnonempty : cellSuffix ≠ []) :
    rawBoundaryPostPullBranchDescription.HaltsFromTapeEquiv
      (rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape
        scratchTail cellSuffix tailFirst tail)
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail cellSuffix tailFirst tail) := by
  let Tin :=
    rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape
      scratchTail cellSuffix tailFirst tail
  have hprefix :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        rawBoundaryPostPullBranchDescription
        rawBoundaryPostPullBranchDescription.start
        rawBoundaryPostPullBoundaryBranchTarget
        Tin Tin := by
    cases cellSuffix with
    | nil =>
        exact False.elim (hnonempty rfl)
    | cons cellFirst cellRest =>
        refine ⟨2, Tin, ?_, Tape.Equiv.refl Tin⟩
        cases cellFirst
        · simpa [Tin, rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape,
            markerAwarePullNearestBoundaryToHeadMarkerTargetTape,
            rawBoundaryCellSuffixRightAfterHead, preservingCellPassCellBits,
            preservingCellPassZeroBits, preservingCellPassOneBits,
            List.append_assoc] using
            rawBoundaryPostPullBranchDescription_run_dispatch_boundary
              scratchTail ([] : List (Option Bool)) false false
              (rawBoundaryCellSuffixRightAfterHead
                false cellRest tailFirst tail)
        · simpa [Tin, rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape,
            markerAwarePullNearestBoundaryToHeadMarkerTargetTape,
            rawBoundaryCellSuffixRightAfterHead, preservingCellPassCellBits,
            preservingCellPassZeroBits, preservingCellPassOneBits,
            List.append_assoc] using
            rawBoundaryPostPullBranchDescription_run_dispatch_boundary
              scratchTail ([] : List (Option Bool)) false false
              (rawBoundaryCellSuffixRightAfterHead
                true cellRest tailFirst tail)
  have hbody :
      Structured.MultiTapeLowering.RunsFromStateTapeEquiv
        rawBoundaryPostPullBranchDescription
        rawBoundaryPostPullBoundaryBranchTarget
        rawBoundaryPostPullBranchHalt
        Tin
        (tailHeadEmittedCellSuffixLeftEdgeScratchTape
          ([] : Word Bool) scratchTail cellSuffix tailFirst tail) := by
    simpa [Tin] using
      rawBoundaryPostPullBranchDescription_runsFrom_boundaryTarget
        scratchTail cellSuffix tailFirst tail hnonempty
  have hrun :=
    Structured.MultiTapeLowering.runsFromStateTapeEquiv_trans
      hprefix hbody
  exact
    Structured.MultiTapeLowering.RunsFromStateTapeEquiv.toHaltsFromTapeEquiv
      hrun rfl (by rfl)

def rawBoundaryMarkerAwarePullThenPostPullBranchDescription :
    MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    markerAwarePullNearestRawBitDescription
    rawBoundaryPostPullBranchDescription

theorem rawBoundaryMarkerAwarePullThenPostPullBranchDescription_subroutineReady :
    rawBoundaryMarkerAwarePullThenPostPullBranchDescription.SubroutineReady := by
  rw [rawBoundaryMarkerAwarePullThenPostPullBranchDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
      markerAwarePullNearestRawBitDescription_subroutineReady
      rawBoundaryPostPullBranchDescription_subroutineReady

theorem rawBoundaryMarkerAwarePullThenPostPullBranchDescription_haltsFrom_headGap_real
    (scratchTail : Nat) (leftBit rawBit headBit : Bool)
    (baseTail : List (Option Bool)) (right : List (Option Bool)) :
    rawBoundaryMarkerAwarePullThenPostPullBranchDescription.HaltsFromTapeEquiv
      (markerAwarePullNearestRawBitToHeadMarkerSourceTape
        (scratchTail + 3) (some leftBit :: baseTail)
        rawBit headBit right)
      (emitPulledRawBitCellChunkLeftEdgeTargetTape
        scratchTail (some leftBit :: baseTail) rawBit headBit right) := by
  rw [rawBoundaryMarkerAwarePullThenPostPullBranchDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTapeEquiv_of_haltsFromTape
      markerAwarePullNearestRawBitDescription_subroutineReady
      rawBoundaryPostPullBranchDescription_subroutineReady
      (markerAwarePullNearestRawBitDescription_haltsFromHeadGap_real
        (scratchTail + 3) leftBit rawBit headBit baseTail right)
      (by
        simpa [markerAwarePullNearestRawBitToHeadMarkerTargetTape] using
          pullNearestRawBitToHeadMarkerTargetTape_moveLeftRight
            scratchTail (some leftBit :: baseTail) rawBit headBit right)
      (rawBoundaryPostPullBranchDescription_haltsFrom_real
        scratchTail (some leftBit :: baseTail) rawBit headBit right)

theorem rawBoundaryMarkerAwarePullThenPostPullBranchDescription_haltsFrom_markedCellSuffixLeftEdge_boundary_nonempty
    (scratchTail : Nat) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hnonempty : cellSuffix ≠ []) :
    rawBoundaryMarkerAwarePullThenPostPullBranchDescription.HaltsFromTapeEquiv
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail cellSuffix tailFirst tail)
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail cellSuffix tailFirst tail) := by
  rw [rawBoundaryMarkerAwarePullThenPostPullBranchDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv
      markerAwarePullNearestRawBitDescription_subroutineReady
      rawBoundaryPostPullBranchDescription_subroutineReady
      (markerAwarePullNearestRawBitDescription_haltsFrom_markedCellSuffixLeftEdge_boundary_nonempty
        scratchTail cellSuffix tailFirst tail hnonempty)
      (rawBoundaryLeftMarkedCellSuffixBoundaryMarkerTape_moveLeftRight
        scratchTail cellSuffix tailFirst tail)
      (rawBoundaryPostPullBranchDescription_haltsFrom_boundary
        scratchTail cellSuffix tailFirst tail hnonempty)

theorem rawBoundaryMarkerAwarePullThenPostPullBranchDescription_haltsFrom_headGap_leftMarkedBase
    (scratchTail : Nat) (pref : Word Bool)
    (rawBit headBit : Bool) (right : List (Option Bool)) :
    rawBoundaryMarkerAwarePullThenPostPullBranchDescription.HaltsFromTapeEquiv
      (markerAwarePullNearestRawBitToHeadMarkerSourceTape
        (scratchTail + 3) (List.append (pref.reverse.map some) [some false])
        rawBit headBit right)
      (emitPulledRawBitCellChunkLeftEdgeTargetTape
        scratchTail (List.append (pref.reverse.map some) [some false])
        rawBit headBit right) := by
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
            rawBoundaryMarkerAwarePullThenPostPullBranchDescription_haltsFrom_headGap_real
              scratchTail leftBit rawBit headBit baseTail right

theorem rawBoundaryMarkerAwarePullThenPostPullBranchDescription_haltsFrom_markedCellSuffixLeftEdgeScratch_of_scratch_length
    (pref cellSuffix : Word Bool) (currentScratch scratchTail : Nat)
    (rawBit tailFirst : Bool) (tail : List (Option Bool))
    (hscratch : currentScratch = scratchTail + 3) :
    rawBoundaryMarkerAwarePullThenPostPullBranchDescription.HaltsFromTapeEquiv
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        (List.append pref [rawBit]) currentScratch cellSuffix tailFirst tail)
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        pref scratchTail (rawBit :: cellSuffix) tailFirst tail) := by
  cases cellSuffix with
  | nil =>
      cases rawBit <;> cases tailFirst
      · simpa [rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
          markerAwarePullNearestRawBitToHeadMarkerSourceTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          hscratch, List.reverse_append, List.map_reverse,
          List.append_assoc] using
          rawBoundaryMarkerAwarePullThenPostPullBranchDescription_haltsFrom_headGap_leftMarkedBase
            scratchTail pref false false tail
      · simpa [rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
          markerAwarePullNearestRawBitToHeadMarkerSourceTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          hscratch, List.reverse_append, List.map_reverse,
          List.append_assoc] using
          rawBoundaryMarkerAwarePullThenPostPullBranchDescription_haltsFrom_headGap_leftMarkedBase
            scratchTail pref false true tail
      · simpa [rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
          markerAwarePullNearestRawBitToHeadMarkerSourceTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          hscratch, List.reverse_append, List.map_reverse,
          List.append_assoc] using
          rawBoundaryMarkerAwarePullThenPostPullBranchDescription_haltsFrom_headGap_leftMarkedBase
            scratchTail pref true false tail
      · simpa [rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
          markerAwarePullNearestRawBitToHeadMarkerSourceTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          hscratch, List.reverse_append, List.map_reverse,
          List.append_assoc] using
          rawBoundaryMarkerAwarePullThenPostPullBranchDescription_haltsFrom_headGap_leftMarkedBase
            scratchTail pref true true tail
  | cons suffixHead suffixRest =>
      cases rawBit <;> cases suffixHead
      · simpa [rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
          markerAwarePullNearestRawBitToHeadMarkerSourceTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          hscratch, List.reverse_append, List.map_reverse,
          List.append_assoc] using
          rawBoundaryMarkerAwarePullThenPostPullBranchDescription_haltsFrom_headGap_leftMarkedBase
            scratchTail pref false false
            (some true :: some false :: some true ::
              List.append ((preservingCellPassCellBits suffixRest).map some)
              (some tailFirst :: tail))
      · simpa [rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
          markerAwarePullNearestRawBitToHeadMarkerSourceTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          hscratch, List.reverse_append, List.map_reverse,
          List.append_assoc] using
          rawBoundaryMarkerAwarePullThenPostPullBranchDescription_haltsFrom_headGap_leftMarkedBase
            scratchTail pref false false
            (some true :: some true :: some false ::
              List.append ((preservingCellPassCellBits suffixRest).map some)
              (some tailFirst :: tail))
      · simpa [rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
          markerAwarePullNearestRawBitToHeadMarkerSourceTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          hscratch, List.reverse_append, List.map_reverse,
          List.append_assoc] using
          rawBoundaryMarkerAwarePullThenPostPullBranchDescription_haltsFrom_headGap_leftMarkedBase
            scratchTail pref true false
            (some true :: some false :: some true ::
              List.append ((preservingCellPassCellBits suffixRest).map some)
              (some tailFirst :: tail))
      · simpa [rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape,
          markerAwarePullNearestRawBitToHeadMarkerSourceTape,
          pullNearestRawBitToHeadMarkerSourceTape,
          emitPulledRawBitCellChunkLeftEdgeTargetTape,
          preservingCellPassCellBits, preservingCellPassZeroBits,
          preservingCellPassOneBits, pulledRawBitCellChunkBits,
          hscratch, List.reverse_append, List.map_reverse,
          List.append_assoc] using
          rawBoundaryMarkerAwarePullThenPostPullBranchDescription_haltsFrom_headGap_leftMarkedBase
            scratchTail pref true false
            (some true :: some true :: some false ::
              List.append ((preservingCellPassCellBits suffixRest).map some)
              (some tailFirst :: tail))

theorem rawBoundaryMarkerAwarePullThenPostPullBranchDescription_haltsFrom_markedCellSuffixLeftEdgeScratch_succ3
    (pref cellSuffix : Word Bool) (scratchTail : Nat)
    (rawBit tailFirst : Bool) (tail : List (Option Bool)) :
    rawBoundaryMarkerAwarePullThenPostPullBranchDescription.HaltsFromTapeEquiv
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        (List.append pref [rawBit]) (scratchTail + 3) cellSuffix
        tailFirst tail)
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        pref scratchTail (rawBit :: cellSuffix) tailFirst tail) :=
  rawBoundaryMarkerAwarePullThenPostPullBranchDescription_haltsFrom_markedCellSuffixLeftEdgeScratch_of_scratch_length
    pref cellSuffix (scratchTail + 3) scratchTail rawBit tailFirst tail rfl

def rawBoundaryBranchingRemainingRawBitsCellSuffixLeftEdgeDescription :
    Word Bool -> MachineDescription
  | [] => ExactIdentityDescription
  | _ :: rest =>
      CommonGround.SameHeadComposition.leftRightSeqDescription
        (rawBoundaryBranchingRemainingRawBitsCellSuffixLeftEdgeDescription
          rest)
        rawBoundaryMarkerAwarePullThenPostPullBranchDescription

theorem rawBoundaryBranchingRemainingRawBitsCellSuffixLeftEdgeDescription_subroutineReady
    (remaining : Word Bool) :
    (rawBoundaryBranchingRemainingRawBitsCellSuffixLeftEdgeDescription
      remaining).SubroutineReady := by
  induction remaining with
  | nil =>
      simpa [rawBoundaryBranchingRemainingRawBitsCellSuffixLeftEdgeDescription] using
        CommonGround.Identity.exactIdentityDescription_subroutineReady
  | cons bit rest ih =>
      simpa [rawBoundaryBranchingRemainingRawBitsCellSuffixLeftEdgeDescription] using
        CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
          ih
          rawBoundaryMarkerAwarePullThenPostPullBranchDescription_subroutineReady

theorem rawBoundaryBranchingRemainingRawBitsCellSuffixLeftEdgeDescription_haltsFrom
    (base remaining cellSuffix : Word Bool)
    (currentScratch finalScratch : Nat)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hscratch : currentScratch = finalScratch + 3 * remaining.length) :
    (rawBoundaryBranchingRemainingRawBitsCellSuffixLeftEdgeDescription
      remaining).HaltsFromTapeEquiv
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        (List.append base remaining) currentScratch cellSuffix tailFirst tail)
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        base finalScratch (List.append remaining cellSuffix) tailFirst tail) := by
  induction remaining generalizing base cellSuffix currentScratch finalScratch with
  | nil =>
      have hcurrent : currentScratch = finalScratch := by
        simpa using hscratch
      subst currentScratch
      simpa [rawBoundaryBranchingRemainingRawBitsCellSuffixLeftEdgeDescription] using
        (CommonGround.Identity.exactIdentityDescription_haltsFromTape
          (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
            base finalScratch cellSuffix tailFirst tail)).toEquiv
  | cons bit rest ih =>
      have hrest :
          currentScratch = (finalScratch + 3) + 3 * rest.length := by
        rw [hscratch]
        simp
        lia
      exact
        CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv
          (rawBoundaryBranchingRemainingRawBitsCellSuffixLeftEdgeDescription_subroutineReady
            rest)
          rawBoundaryMarkerAwarePullThenPostPullBranchDescription_subroutineReady
          (by
            simpa [List.append_assoc] using
              ih (List.append base [bit]) cellSuffix currentScratch
                (finalScratch + 3) hrest)
          (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape_moveLeftRight
            (List.append base [bit]) (finalScratch + 3)
            (List.append rest cellSuffix) tailFirst tail)
          (by
            simpa using
              rawBoundaryMarkerAwarePullThenPostPullBranchDescription_haltsFrom_markedCellSuffixLeftEdgeScratch_succ3
                base (List.append rest cellSuffix) finalScratch bit
                tailFirst tail)

def rawBoundaryMarkedCellSuffixLeftEdgeToUnmarkedDescription :
    MachineDescription :=
  rawBoundaryMarkerAwarePullThenPostPullBranchDescription

theorem rawBoundaryMarkedCellSuffixLeftEdgeToUnmarkedDescription_subroutineReady :
    rawBoundaryMarkedCellSuffixLeftEdgeToUnmarkedDescription.SubroutineReady := by
  rw [rawBoundaryMarkedCellSuffixLeftEdgeToUnmarkedDescription]
  exact rawBoundaryMarkerAwarePullThenPostPullBranchDescription_subroutineReady

theorem rawBoundaryMarkedCellSuffixLeftEdgeToUnmarkedDescription_haltsFrom_cons
    (scratchTail : Nat) (cellFirst : Bool) (cellRest : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    rawBoundaryMarkedCellSuffixLeftEdgeToUnmarkedDescription.HaltsFromTapeEquiv
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail (cellFirst :: cellRest) tailFirst tail)
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail (cellFirst :: cellRest)
        tailFirst tail) := by
  rw [rawBoundaryMarkedCellSuffixLeftEdgeToUnmarkedDescription]
  exact
    rawBoundaryMarkerAwarePullThenPostPullBranchDescription_haltsFrom_markedCellSuffixLeftEdge_boundary_nonempty
      scratchTail (cellFirst :: cellRest) tailFirst tail (by simp)

theorem rawBoundaryMarkedCellSuffixLeftEdgeToUnmarkedDescription_haltsFrom_nonempty
    (scratchTail : Nat) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hnonempty : cellSuffix ≠ []) :
    rawBoundaryMarkedCellSuffixLeftEdgeToUnmarkedDescription.HaltsFromTapeEquiv
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail cellSuffix tailFirst tail)
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail cellSuffix tailFirst tail) := by
  cases cellSuffix with
  | nil =>
      exact False.elim (hnonempty rfl)
  | cons cellFirst cellRest =>
      exact
        rawBoundaryMarkedCellSuffixLeftEdgeToUnmarkedDescription_haltsFrom_cons
          scratchTail cellFirst cellRest tailFirst tail

theorem rawBoundaryMarkedCellSuffixLeftEdgeToUnmarkedDescription_haltsFrom_append_pair
    (scratchTail : Nat) (remaining : Word Bool)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    rawBoundaryMarkedCellSuffixLeftEdgeToUnmarkedDescription.HaltsFromTapeEquiv
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail
        (List.append remaining [nextRawBit, emittedRawBit])
        tailFirst tail)
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail
        (List.append remaining [nextRawBit, emittedRawBit])
        tailFirst tail) := by
  exact
    rawBoundaryMarkedCellSuffixLeftEdgeToUnmarkedDescription_haltsFrom_nonempty
      scratchTail (List.append remaining [nextRawBit, emittedRawBit])
      tailFirst tail
      (by
        intro hnil
        have hlen := congrArg List.length hnil
        simp at hlen)

def rawBoundaryMarkedRemainingRawBitsToRightEdgeDescription
    (remaining cellSuffix : Word Bool) : MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    (CommonGround.SameHeadComposition.leftRightSeqDescription
      (rawBoundaryBranchingRemainingRawBitsCellSuffixLeftEdgeDescription
        remaining)
      rawBoundaryMarkedCellSuffixLeftEdgeToUnmarkedDescription)
    (emittedCellSuffixLeftEdgeToRightEdgeDescription
      (List.append remaining cellSuffix))

theorem rawBoundaryMarkedRemainingRawBitsToRightEdgeDescription_ready
    (remaining cellSuffix : Word Bool) :
    (rawBoundaryMarkedRemainingRawBitsToRightEdgeDescription
      remaining cellSuffix).SubroutineReady := by
  rw [rawBoundaryMarkedRemainingRawBitsToRightEdgeDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
      (CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
        (rawBoundaryBranchingRemainingRawBitsCellSuffixLeftEdgeDescription_subroutineReady
          remaining)
        rawBoundaryMarkedCellSuffixLeftEdgeToUnmarkedDescription_subroutineReady)
      (emittedCellSuffixLeftEdgeToRightEdgeDescription_subroutineReady
        (List.append remaining cellSuffix))

theorem rawBoundaryMarkedRemainingRawBitsToRightEdgeDescription_haltsFrom_markedCellSuffix
    (remaining cellSuffix : Word Bool)
    (currentScratch finalScratch : Nat)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hscratch : currentScratch = finalScratch + 3 * remaining.length)
    (hnonempty : List.append remaining cellSuffix ≠ []) :
    (rawBoundaryMarkedRemainingRawBitsToRightEdgeDescription
      remaining cellSuffix).HaltsFromTapeEquiv
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        remaining currentScratch cellSuffix tailFirst tail)
      (tapeAtCells
        ((encodedLayoutBits (List.append remaining cellSuffix)).reverse.map
          some)
        (some tailFirst :: tail)) := by
  rw [rawBoundaryMarkedRemainingRawBitsToRightEdgeDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv
      (CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
        (rawBoundaryBranchingRemainingRawBitsCellSuffixLeftEdgeDescription_subroutineReady
          remaining)
        rawBoundaryMarkedCellSuffixLeftEdgeToUnmarkedDescription_subroutineReady)
      (emittedCellSuffixLeftEdgeToRightEdgeDescription_subroutineReady
        (List.append remaining cellSuffix))
      (CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv
        (rawBoundaryBranchingRemainingRawBitsCellSuffixLeftEdgeDescription_subroutineReady
          remaining)
        rawBoundaryMarkedCellSuffixLeftEdgeToUnmarkedDescription_subroutineReady
        (by
          simpa using
            rawBoundaryBranchingRemainingRawBitsCellSuffixLeftEdgeDescription_haltsFrom
              ([] : Word Bool) remaining cellSuffix currentScratch
              finalScratch tailFirst tail hscratch)
        (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape_moveLeftRight
          ([] : Word Bool) finalScratch
          (List.append remaining cellSuffix) tailFirst tail)
        (rawBoundaryMarkedCellSuffixLeftEdgeToUnmarkedDescription_haltsFrom_nonempty
          finalScratch (List.append remaining cellSuffix) tailFirst tail
          hnonempty))
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape_moveLeftRight
        ([] : Word Bool) finalScratch
        (List.append remaining cellSuffix) tailFirst tail)
      (emittedCellSuffixLeftEdgeToRightEdgeDescription_haltsFrom_tailHeadEmittedCellSuffixLeftEdgeScratchTape_equiv
        (List.append remaining cellSuffix) finalScratch tailFirst tail)

def rawBoundarySourceFirstTwoThenMarkedRemainingRawBitsToRightEdgeDescription
    (remaining : Word Bool) (nextRawBit emittedRawBit : Bool) :
    MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionViaLeftMarkedBoundaryDescription
    (rawBoundaryMarkedRemainingRawBitsToRightEdgeDescription
      remaining [nextRawBit, emittedRawBit])

theorem rawBoundarySourceFirstTwoThenMarkedRemainingRawBitsToRightEdgeDescription_ready
    (remaining : Word Bool) (nextRawBit emittedRawBit : Bool) :
    (rawBoundarySourceFirstTwoThenMarkedRemainingRawBitsToRightEdgeDescription
      remaining nextRawBit emittedRawBit).SubroutineReady := by
  rw [rawBoundarySourceFirstTwoThenMarkedRemainingRawBitsToRightEdgeDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
      rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionViaLeftMarkedBoundaryDescription_ready
      (rawBoundaryMarkedRemainingRawBitsToRightEdgeDescription_ready
        remaining [nextRawBit, emittedRawBit])

theorem rawBoundarySourceFirstTwoThenMarkedRemainingRawBitsToRightEdgeDescription_haltsFrom_sourceTape_of_count_lengths
    (skipped count remaining : Word Bool)
    (scratchAfterTwo finalScratch : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count =
        List.append (List.append remaining [nextRawBit]) [emittedRawBit])
    (hcount : count.length = scratchAfterTwo + 3)
    (hremainingScratch :
      scratchAfterTwo = finalScratch + 3 * remaining.length) :
    (rawBoundarySourceFirstTwoThenMarkedRemainingRawBitsToRightEdgeDescription
      remaining nextRawBit emittedRawBit).HaltsFromTapeEquiv
      (sourceTape skipped count (some tailFirst :: tail))
      (rightEdgeTape skipped count tailFirst tail) := by
  have hlayoutFlat :
      List.append skipped count =
        List.append remaining [nextRawBit, emittedRawBit] := by
    simpa [List.append_assoc] using hlayout
  rw [rawBoundarySourceFirstTwoThenMarkedRemainingRawBitsToRightEdgeDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTapeEquiv_of_haltsFromTape
      rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionViaLeftMarkedBoundaryDescription_ready
      (rawBoundaryMarkedRemainingRawBitsToRightEdgeDescription_ready
        remaining [nextRawBit, emittedRawBit])
      (rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionViaLeftMarkedBoundaryDescription_haltsFrom_sourceTape_of_count_length
        skipped count remaining scratchAfterTwo nextRawBit emittedRawBit
        tailFirst tail hlayout hcount)
      (by
        calc
          Tape.move Direction.right
              (Tape.move Direction.left
                (rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
                  remaining scratchAfterTwo nextRawBit emittedRawBit
                  tailFirst tail)) =
            rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
              remaining scratchAfterTwo nextRawBit emittedRawBit
              tailFirst tail :=
              rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_moveLeftRight
                remaining scratchAfterTwo nextRawBit emittedRawBit
                tailFirst tail
          _ =
            rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
              remaining scratchAfterTwo [nextRawBit, emittedRawBit]
              tailFirst tail :=
              rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_eq_markedCellSuffixLeftEdgeScratch_pair
                remaining scratchAfterTwo nextRawBit emittedRawBit
                tailFirst tail)
      (by
        have htail :=
          rawBoundaryMarkedRemainingRawBitsToRightEdgeDescription_haltsFrom_markedCellSuffix
            remaining [nextRawBit, emittedRawBit] scratchAfterTwo
            finalScratch tailFirst tail hremainingScratch (by simp)
        rw [← hlayoutFlat] at htail
        simpa [rightEdgeTape, List.map_reverse] using htail)

def rawBoundarySourceFirstTwoThenRemainingRawBitsToRightEdgeViaLeftMarkedBoundaryDescription
    (remaining : Word Bool) (nextRawBit emittedRawBit : Bool) :
    MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    (CommonGround.SameHeadComposition.leftRightSeqDescription
      (rawBoundarySourceFirstTwoThenRemainingRawBitsCellSuffixLeftEdgeEmissionViaLeftMarkedBoundaryDescription
        remaining)
      rawBoundaryMarkedCellSuffixLeftEdgeToUnmarkedDescription)
    (emittedCellSuffixLeftEdgeToRightEdgeDescription
      (List.append remaining [nextRawBit, emittedRawBit]))

theorem rawBoundarySourceFirstTwoThenRemainingRawBitsToRightEdgeViaLeftMarkedBoundaryDescription_ready
    (remaining : Word Bool) (nextRawBit emittedRawBit : Bool) :
    (rawBoundarySourceFirstTwoThenRemainingRawBitsToRightEdgeViaLeftMarkedBoundaryDescription
      remaining nextRawBit emittedRawBit).SubroutineReady := by
  rw [rawBoundarySourceFirstTwoThenRemainingRawBitsToRightEdgeViaLeftMarkedBoundaryDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
      (CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
        (rawBoundarySourceFirstTwoThenRemainingRawBitsCellSuffixLeftEdgeEmissionViaLeftMarkedBoundaryDescription_ready
          remaining)
        rawBoundaryMarkedCellSuffixLeftEdgeToUnmarkedDescription_subroutineReady)
      (emittedCellSuffixLeftEdgeToRightEdgeDescription_subroutineReady
        (List.append remaining [nextRawBit, emittedRawBit]))

theorem rawBoundarySourceFirstTwoThenRemainingRawBitsToRightEdgeViaLeftMarkedBoundaryDescription_haltsFrom_sourceTape_of_count_lengths
    (skipped count remaining : Word Bool)
    (scratchAfterTwo finalScratch : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count =
        List.append (List.append remaining [nextRawBit]) [emittedRawBit])
    (hcount : count.length = scratchAfterTwo + 3)
    (hremainingScratch :
      scratchAfterTwo = finalScratch + 3 * remaining.length) :
    (rawBoundarySourceFirstTwoThenRemainingRawBitsToRightEdgeViaLeftMarkedBoundaryDescription
      remaining nextRawBit emittedRawBit).HaltsFromTapeEquiv
      (sourceTape skipped count (some tailFirst :: tail))
      (rightEdgeTape skipped count tailFirst tail) := by
  have hlayoutFlat :
      List.append skipped count =
        List.append remaining [nextRawBit, emittedRawBit] := by
    simpa [List.append_assoc] using hlayout
  rw [rawBoundarySourceFirstTwoThenRemainingRawBitsToRightEdgeViaLeftMarkedBoundaryDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv
      (CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
        (rawBoundarySourceFirstTwoThenRemainingRawBitsCellSuffixLeftEdgeEmissionViaLeftMarkedBoundaryDescription_ready
          remaining)
        rawBoundaryMarkedCellSuffixLeftEdgeToUnmarkedDescription_subroutineReady)
      (emittedCellSuffixLeftEdgeToRightEdgeDescription_subroutineReady
        (List.append remaining [nextRawBit, emittedRawBit]))
      (CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTapeEquiv_of_haltsFromTape
        (rawBoundarySourceFirstTwoThenRemainingRawBitsCellSuffixLeftEdgeEmissionViaLeftMarkedBoundaryDescription_ready
          remaining)
        rawBoundaryMarkedCellSuffixLeftEdgeToUnmarkedDescription_subroutineReady
        (remainingCellSuffix_haltsFrom_sourceTape_ofCountLengths
          skipped count remaining scratchAfterTwo finalScratch nextRawBit
          emittedRawBit tailFirst tail hlayout hcount hremainingScratch)
        (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape_moveLeftRight
          ([] : Word Bool) finalScratch
          (List.append remaining [nextRawBit, emittedRawBit]) tailFirst tail)
        (rawBoundaryMarkedCellSuffixLeftEdgeToUnmarkedDescription_haltsFrom_append_pair
          finalScratch remaining nextRawBit emittedRawBit tailFirst tail))
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape_moveLeftRight
        ([] : Word Bool) finalScratch
        (List.append remaining [nextRawBit, emittedRawBit])
        tailFirst tail)
      (by
        have hfinal :=
          emittedCellSuffixLeftEdgeToRightEdgeDescription_haltsFrom_tailHeadEmittedCellSuffixLeftEdgeScratchTape_rightEdgeTapeEquiv
            skipped count finalScratch tailFirst tail
        rw [hlayoutFlat] at hfinal
        exact hfinal)

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
