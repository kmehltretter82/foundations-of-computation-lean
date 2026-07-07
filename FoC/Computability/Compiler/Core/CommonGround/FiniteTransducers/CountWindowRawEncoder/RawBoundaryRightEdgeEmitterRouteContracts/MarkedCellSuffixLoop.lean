import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawEncoder.RawBoundaryRightEdgeEmitter.MarkedCellSuffixLoop

set_option doc.verso true

/-!
# Marked cell-suffix loop route contracts

This module exposes the reusable route facts for the marker-preserving
raw-boundary cell-suffix loop without requiring downstream proofs to unfold
the detailed machine composition.
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

structure RawBoundaryLeftMarkedTailHeadCellSuffixLeftEdgeShape
    (pref : Word Bool) (scratchTail : Nat) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) : Prop where
  cells :
    Tape.cells
        (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
          pref scratchTail cellSuffix tailFirst tail) =
      some false ::
        List.append (pref.map some)
          (List.append
            (List.replicate scratchTail (none : Option Bool))
            (List.append
              ((preservingCellPassCellBits cellSuffix).map some)
              (some tailFirst :: tail)))
  leftLength :
    (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
      pref scratchTail cellSuffix tailFirst tail).left.length =
      scratchTail + pref.length + 1
  moveLeftRight :
    Tape.move Direction.right
        (Tape.move Direction.left
          (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
            pref scratchTail cellSuffix tailFirst tail)) =
      rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        pref scratchTail cellSuffix tailFirst tail

theorem rawBoundaryLeftMarkedTailHeadCellSuffixLeftEdgeShape
    (pref : Word Bool) (scratchTail : Nat) (cellSuffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    RawBoundaryLeftMarkedTailHeadCellSuffixLeftEdgeShape
      pref scratchTail cellSuffix tailFirst tail :=
  { cells :=
      rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape_cells
        pref scratchTail cellSuffix tailFirst tail
    leftLength :=
      rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape_left_length
        pref scratchTail cellSuffix tailFirst tail
    moveLeftRight :=
      rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape_moveLeftRight
        pref scratchTail cellSuffix tailFirst tail }

structure RawBoundaryMarkedRemainingCellSuffixLoopRoute
    (base remaining cellSuffix : Word Bool)
    (currentScratch finalScratch : Nat)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hscratch :
      currentScratch = finalScratch + 3 * remaining.length) : Prop where
  routeReady :
    (markerAwarePullRemainingRawBitsCellSuffixLeftEdgeDescription
      remaining).SubroutineReady
  routeHalts :
    (markerAwarePullRemainingRawBitsCellSuffixLeftEdgeDescription
      remaining).HaltsFromTape
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        (List.append base remaining) currentScratch cellSuffix tailFirst tail)
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        base finalScratch (List.append remaining cellSuffix) tailFirst tail)
  sourceShape :
    RawBoundaryLeftMarkedTailHeadCellSuffixLeftEdgeShape
      (List.append base remaining) currentScratch cellSuffix tailFirst tail
  targetShape :
    RawBoundaryLeftMarkedTailHeadCellSuffixLeftEdgeShape
      base finalScratch (List.append remaining cellSuffix) tailFirst tail

theorem rawBoundaryMarkedRemainingCellSuffixLoopRoute
    (base remaining cellSuffix : Word Bool)
    (currentScratch finalScratch : Nat)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hscratch :
      currentScratch = finalScratch + 3 * remaining.length) :
    RawBoundaryMarkedRemainingCellSuffixLoopRoute
      base remaining cellSuffix currentScratch finalScratch tailFirst tail
      hscratch :=
  { routeReady :=
      markerAwarePullRemainingRawBitsCellSuffixLeftEdgeDescription_subroutineReady
        remaining
    routeHalts :=
      markerAwarePullRemainingRawBitsCellSuffixLeftEdgeDescription_haltsFrom
        base remaining cellSuffix currentScratch finalScratch tailFirst tail
        hscratch
    sourceShape :=
      rawBoundaryLeftMarkedTailHeadCellSuffixLeftEdgeShape
        (List.append base remaining) currentScratch cellSuffix tailFirst tail
    targetShape :=
      rawBoundaryLeftMarkedTailHeadCellSuffixLeftEdgeShape
        base finalScratch (List.append remaining cellSuffix) tailFirst tail }

theorem rawBoundary_markedRemainingCellSuffixLoop_halts
    (base remaining cellSuffix : Word Bool)
    (currentScratch finalScratch : Nat)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hscratch :
      currentScratch = finalScratch + 3 * remaining.length) :
    (markerAwarePullRemainingRawBitsCellSuffixLeftEdgeDescription
      remaining).HaltsFromTape
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        (List.append base remaining) currentScratch cellSuffix tailFirst tail)
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        base finalScratch (List.append remaining cellSuffix) tailFirst tail) :=
  (rawBoundaryMarkedRemainingCellSuffixLoopRoute
    base remaining cellSuffix currentScratch finalScratch tailFirst tail
    hscratch).routeHalts

structure RawBoundaryMarkedRemainingRightEdgeRoute
    (remaining cellSuffix : Word Bool)
    (currentScratch finalScratch : Nat)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hscratch :
      currentScratch = finalScratch + 3 * remaining.length)
    (hnonempty : List.append remaining cellSuffix ≠ []) : Prop where
  routeReady :
    (rawBoundaryMarkedRemainingRawBitsToRightEdgeDescription
      remaining cellSuffix).SubroutineReady
  routeHalts :
    (rawBoundaryMarkedRemainingRawBitsToRightEdgeDescription
      remaining cellSuffix).HaltsFromTapeEquiv
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        remaining currentScratch cellSuffix tailFirst tail)
      (tapeAtCells
        ((encodedLayoutBits (List.append remaining cellSuffix)).reverse.map
          some)
        (some tailFirst :: tail))
  sourceShape :
    RawBoundaryLeftMarkedTailHeadCellSuffixLeftEdgeShape
      remaining currentScratch cellSuffix tailFirst tail

theorem rawBoundaryMarkedRemainingRightEdgeRoute
    (remaining cellSuffix : Word Bool)
    (currentScratch finalScratch : Nat)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hscratch :
      currentScratch = finalScratch + 3 * remaining.length)
    (hnonempty : List.append remaining cellSuffix ≠ []) :
    RawBoundaryMarkedRemainingRightEdgeRoute
      remaining cellSuffix currentScratch finalScratch tailFirst tail
      hscratch hnonempty :=
  { routeReady :=
      rawBoundaryMarkedRemainingRawBitsToRightEdgeDescription_ready
        remaining cellSuffix
    routeHalts :=
      rawBoundaryMarkedRemainingRawBitsToRightEdgeDescription_haltsFrom_markedCellSuffix
        remaining cellSuffix currentScratch finalScratch tailFirst tail
        hscratch hnonempty
    sourceShape :=
      rawBoundaryLeftMarkedTailHeadCellSuffixLeftEdgeShape
        remaining currentScratch cellSuffix tailFirst tail }

theorem rawBoundary_markedRemainingRightEdge_halts
    (remaining cellSuffix : Word Bool)
    (currentScratch finalScratch : Nat)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hscratch :
      currentScratch = finalScratch + 3 * remaining.length)
    (hnonempty : List.append remaining cellSuffix ≠ []) :
    (rawBoundaryMarkedRemainingRawBitsToRightEdgeDescription
      remaining cellSuffix).HaltsFromTapeEquiv
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        remaining currentScratch cellSuffix tailFirst tail)
      (tapeAtCells
        ((encodedLayoutBits (List.append remaining cellSuffix)).reverse.map
          some)
        (some tailFirst :: tail)) :=
  (rawBoundaryMarkedRemainingRightEdgeRoute
    remaining cellSuffix currentScratch finalScratch tailFirst tail
    hscratch hnonempty).routeHalts

structure RawBoundarySourceFirstTwoThenRemainingMarkedCellSuffixRoute
    (skipped count remaining : Word Bool)
    (scratchAfterTwo finalScratch : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count =
        List.append (List.append remaining [nextRawBit]) [emittedRawBit])
    (hcount : count.length = scratchAfterTwo + 3)
    (hremainingScratch :
      scratchAfterTwo = finalScratch + 3 * remaining.length) : Prop where
  routeReady :
    (rawBoundarySourceFirstTwoThenRemainingRawBitsCellSuffixLeftEdgeEmissionViaLeftMarkedBoundaryDescription
      remaining).SubroutineReady
  routeHalts :
    (rawBoundarySourceFirstTwoThenRemainingRawBitsCellSuffixLeftEdgeEmissionViaLeftMarkedBoundaryDescription
      remaining).HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) finalScratch
        (List.append remaining [nextRawBit, emittedRawBit])
        tailFirst tail)
  outputShape :
    RawBoundaryLeftMarkedTailHeadCellSuffixLeftEdgeShape
      ([] : Word Bool) finalScratch
      (List.append remaining [nextRawBit, emittedRawBit]) tailFirst tail

theorem rawBoundarySourceFirstTwoThenRemainingMarkedCellSuffixRoute
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
    RawBoundarySourceFirstTwoThenRemainingMarkedCellSuffixRoute
      skipped count remaining scratchAfterTwo finalScratch nextRawBit
      emittedRawBit tailFirst tail hlayout hcount hremainingScratch :=
  { routeReady :=
      rawBoundarySourceFirstTwoThenRemainingRawBitsCellSuffixLeftEdgeEmissionViaLeftMarkedBoundaryDescription_ready
        remaining
    routeHalts :=
      remainingCellSuffix_haltsFrom_sourceTape_ofCountLengths
        skipped count remaining scratchAfterTwo finalScratch nextRawBit
        emittedRawBit tailFirst tail hlayout hcount hremainingScratch
    outputShape :=
      rawBoundaryLeftMarkedTailHeadCellSuffixLeftEdgeShape
        ([] : Word Bool) finalScratch
        (List.append remaining [nextRawBit, emittedRawBit]) tailFirst tail }

theorem rawBoundary_sourceFirstTwoThenRemainingMarkedCellSuffix_halts
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
        tailFirst tail) :=
  (rawBoundarySourceFirstTwoThenRemainingMarkedCellSuffixRoute
    skipped count remaining scratchAfterTwo finalScratch nextRawBit
    emittedRawBit tailFirst tail hlayout hcount hremainingScratch).routeHalts

theorem rawBoundary_sourceFirstTwoThenRemainingMarkedCellSuffix_exists_of_two_le_layout_length_count_enough
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
                    tailFirst tail) :=
  remainingCellSuffix_exists_ofLayoutCountEnough
    skipped count tailFirst tail hlayoutLength hcountEnough

structure RawBoundaryMarkedCellSuffixCleanupRoute
    (scratchTail : Nat) (cellFirst : Bool) (cellRest : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) : Prop where
  routeReady :
    rawBoundaryMarkedCellSuffixLeftEdgeToUnmarkedDescription.SubroutineReady
  routeHalts :
    rawBoundaryMarkedCellSuffixLeftEdgeToUnmarkedDescription.HaltsFromTapeEquiv
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail (cellFirst :: cellRest) tailFirst tail)
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail (cellFirst :: cellRest)
        tailFirst tail)
  sourceShape :
    RawBoundaryLeftMarkedTailHeadCellSuffixLeftEdgeShape
      ([] : Word Bool) scratchTail (cellFirst :: cellRest) tailFirst tail

theorem rawBoundaryMarkedCellSuffixCleanupRoute
    (scratchTail : Nat) (cellFirst : Bool) (cellRest : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    RawBoundaryMarkedCellSuffixCleanupRoute
      scratchTail cellFirst cellRest tailFirst tail :=
  { routeReady :=
      rawBoundaryMarkedCellSuffixLeftEdgeToUnmarkedDescription_subroutineReady
    routeHalts :=
      rawBoundaryMarkedCellSuffixLeftEdgeToUnmarkedDescription_haltsFrom_cons
        scratchTail cellFirst cellRest tailFirst tail
    sourceShape :=
      rawBoundaryLeftMarkedTailHeadCellSuffixLeftEdgeShape
        ([] : Word Bool) scratchTail (cellFirst :: cellRest) tailFirst tail }

theorem rawBoundary_markedCellSuffixCleanup_halts
    (scratchTail : Nat) (cellFirst : Bool) (cellRest : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    rawBoundaryMarkedCellSuffixLeftEdgeToUnmarkedDescription.HaltsFromTapeEquiv
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail (cellFirst :: cellRest) tailFirst tail)
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) scratchTail (cellFirst :: cellRest)
        tailFirst tail) :=
  (rawBoundaryMarkedCellSuffixCleanupRoute
    scratchTail cellFirst cellRest tailFirst tail).routeHalts

structure RawBoundarySourceFirstTwoThenRemainingMarkedRightEdgeRoute
    (skipped count remaining : Word Bool)
    (scratchAfterTwo finalScratch : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count =
        List.append (List.append remaining [nextRawBit]) [emittedRawBit])
    (hcount : count.length = scratchAfterTwo + 3)
    (hremainingScratch :
      scratchAfterTwo = finalScratch + 3 * remaining.length) : Prop where
  routeReady :
    (rawBoundarySourceFirstTwoThenRemainingRawBitsToRightEdgeViaLeftMarkedBoundaryDescription
      remaining nextRawBit emittedRawBit).SubroutineReady
  routeHalts :
    (rawBoundarySourceFirstTwoThenRemainingRawBitsToRightEdgeViaLeftMarkedBoundaryDescription
      remaining nextRawBit emittedRawBit).HaltsFromTapeEquiv
      (sourceTape skipped count (some tailFirst :: tail))
      (rightEdgeTape skipped count tailFirst tail)

theorem rawBoundarySourceFirstTwoThenRemainingMarkedRightEdgeRoute
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
    RawBoundarySourceFirstTwoThenRemainingMarkedRightEdgeRoute
      skipped count remaining scratchAfterTwo finalScratch nextRawBit
      emittedRawBit tailFirst tail hlayout hcount hremainingScratch :=
  { routeReady :=
      rawBoundarySourceFirstTwoThenRemainingRawBitsToRightEdgeViaLeftMarkedBoundaryDescription_ready
        remaining nextRawBit emittedRawBit
    routeHalts :=
      rawBoundarySourceFirstTwoThenRemainingRawBitsToRightEdgeViaLeftMarkedBoundaryDescription_haltsFrom_sourceTape_of_count_lengths
        skipped count remaining scratchAfterTwo finalScratch nextRawBit
        emittedRawBit tailFirst tail hlayout hcount hremainingScratch }

theorem rawBoundary_sourceFirstTwoThenRemainingMarkedRightEdge_halts
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
      (rightEdgeTape skipped count tailFirst tail) :=
  (rawBoundarySourceFirstTwoThenRemainingMarkedRightEdgeRoute
    skipped count remaining scratchAfterTwo finalScratch nextRawBit
    emittedRawBit tailFirst tail hlayout hcount hremainingScratch).routeHalts

theorem rawBoundary_sourceFirstTwoThenMarkedRemainingRightEdge_halts
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
      (rightEdgeTape skipped count tailFirst tail) :=
  rawBoundarySourceFirstTwoThenMarkedRemainingRawBitsToRightEdgeDescription_haltsFrom_sourceTape_of_count_lengths
    skipped count remaining scratchAfterTwo finalScratch nextRawBit
    emittedRawBit tailFirst tail hlayout hcount hremainingScratch

theorem rawBoundary_sourceFirstTwoThenRemainingMarkedRightEdge_exists_of_two_le_layout_length_count_enough
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
                (rawBoundarySourceFirstTwoThenRemainingRawBitsToRightEdgeViaLeftMarkedBoundaryDescription
                  remaining nextRawBit emittedRawBit).HaltsFromTapeEquiv
                  (sourceTape skipped count (some tailFirst :: tail))
                  (rightEdgeTape skipped count tailFirst tail) := by
  rcases
      remainingCellSuffix_exists_ofLayoutCountEnough
        skipped count tailFirst tail hlayoutLength hcountEnough with
    ⟨remaining, nextRawBit, emittedRawBit, scratchAfterTwo,
      finalScratch, hlayout, hcount, hscratch, _hroute⟩
  exact
    ⟨remaining, nextRawBit, emittedRawBit, scratchAfterTwo, finalScratch,
      hlayout, hcount, hscratch,
      rawBoundarySourceFirstTwoThenRemainingRawBitsToRightEdgeViaLeftMarkedBoundaryDescription_haltsFrom_sourceTape_of_count_lengths
        skipped count remaining scratchAfterTwo finalScratch nextRawBit
        emittedRawBit tailFirst tail hlayout hcount hscratch⟩

theorem rawBoundary_sourceFirstTwoThenMarkedRemainingRightEdge_exists_of_two_le_layout_length_count_enough
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
                (rawBoundarySourceFirstTwoThenMarkedRemainingRawBitsToRightEdgeDescription
                  remaining nextRawBit emittedRawBit).HaltsFromTapeEquiv
                  (sourceTape skipped count (some tailFirst :: tail))
                  (rightEdgeTape skipped count tailFirst tail) := by
  rcases
      remainingCellSuffix_exists_ofLayoutCountEnough
        skipped count tailFirst tail hlayoutLength hcountEnough with
    ⟨remaining, nextRawBit, emittedRawBit, scratchAfterTwo,
      finalScratch, hlayout, hcount, hscratch, _hroute⟩
  exact
    ⟨remaining, nextRawBit, emittedRawBit, scratchAfterTwo, finalScratch,
      hlayout, hcount, hscratch,
      rawBoundary_sourceFirstTwoThenMarkedRemainingRightEdge_halts
        skipped count remaining scratchAfterTwo finalScratch nextRawBit
        emittedRawBit tailFirst tail hlayout hcount hscratch⟩

theorem rawBoundary_sourceFirstTwoThenRemainingMarkedRightEdgeRoute_exists_of_two_le_layout_length_count_enough
    (skipped count : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hlayoutLength : 2 <= (List.append skipped count).length)
    (hcountEnough :
      3 * ((List.append skipped count).length - 2) + 3 <=
        count.length) :
    exists remaining : Word Bool, exists nextRawBit : Bool,
      exists emittedRawBit : Bool, exists scratchAfterTwo : Nat,
        exists finalScratch : Nat,
          exists hlayout :
            List.append skipped count =
              List.append (List.append remaining [nextRawBit])
                [emittedRawBit],
            exists hcount : count.length = scratchAfterTwo + 3,
              exists hremainingScratch :
                scratchAfterTwo =
                  finalScratch + 3 * remaining.length,
                RawBoundarySourceFirstTwoThenRemainingMarkedRightEdgeRoute
                  skipped count remaining scratchAfterTwo finalScratch
                  nextRawBit emittedRawBit tailFirst tail hlayout hcount
                  hremainingScratch := by
  rcases
      rawBoundary_sourceFirstTwoThenRemainingMarkedRightEdge_exists_of_two_le_layout_length_count_enough
        skipped count tailFirst tail hlayoutLength hcountEnough with
    ⟨remaining, nextRawBit, emittedRawBit, scratchAfterTwo,
      finalScratch, hlayout, hcount, hscratch, _hhalts⟩
  exact
    ⟨remaining, nextRawBit, emittedRawBit, scratchAfterTwo, finalScratch,
      hlayout, hcount, hscratch,
      rawBoundarySourceFirstTwoThenRemainingMarkedRightEdgeRoute
        skipped count remaining scratchAfterTwo finalScratch nextRawBit
        emittedRawBit tailFirst tail hlayout hcount hscratch⟩

def RawBoundaryParameterizedRightEdgeRoute
    (skipped count : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) : Prop :=
  exists routeDescription : MachineDescription,
    routeDescription.SubroutineReady ∧
      routeDescription.HaltsFromTapeEquiv
        (sourceTape skipped count (some tailFirst :: tail))
        (rightEdgeTape skipped count tailFirst tail)

theorem rawBoundary_parameterizedRightEdgeRoute_exists_of_nonempty_count_enough
    (skipped count : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hnonempty : List.append skipped count ≠ [])
    (hcountEnough :
      2 <= (List.append skipped count).length ->
        3 * ((List.append skipped count).length - 2) + 3 <=
          count.length) :
    RawBoundaryParameterizedRightEdgeRoute
      skipped count tailFirst tail := by
  by_cases hlengthOne : (List.append skipped count).length = 1
  · rcases
      sourceSingleRawBitToRightEdgeDescription_haltsFrom_sourceTape_exists_of_layout_length_one
        skipped count tailFirst tail hlengthOne with
      ⟨rawBit, _hlayout, hhalts⟩
    exact
      ⟨sourceSingleRawBitToRightEdgeDescription rawBit,
          sourceSingleRawBitToRightEdgeDescription_subroutineReady rawBit
        , hhalts⟩
  · have hlayoutLength : 2 <= (List.append skipped count).length := by
      cases hlayout : List.append skipped count with
      | nil =>
          exact False.elim (hnonempty hlayout)
      | cons bit rest =>
          cases rest with
          | nil =>
              have hlength :
                  (List.append skipped count).length = 1 := by
                simpa using congrArg List.length hlayout
              exact False.elim (hlengthOne hlength)
          | cons next rest =>
              simp
    rcases
      rawBoundary_sourceFirstTwoThenMarkedRemainingRightEdge_exists_of_two_le_layout_length_count_enough
        skipped count tailFirst tail hlayoutLength
        (hcountEnough hlayoutLength) with
      ⟨remaining, nextRawBit, emittedRawBit, scratchAfterTwo,
        finalScratch, hlayout, hcount, hscratch, hroute⟩
    exact
      ⟨rawBoundarySourceFirstTwoThenMarkedRemainingRawBitsToRightEdgeDescription
          remaining nextRawBit emittedRawBit,
        rawBoundarySourceFirstTwoThenMarkedRemainingRawBitsToRightEdgeDescription_ready
          remaining nextRawBit emittedRawBit,
        hroute⟩

theorem rawBoundary_parameterizedRightEdge_halts_exists_of_nonempty_count_enough
    (skipped count : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hnonempty : List.append skipped count ≠ [])
    (hcountEnough :
      2 <= (List.append skipped count).length ->
        3 * ((List.append skipped count).length - 2) + 3 <=
          count.length) :
    exists routeDescription : MachineDescription,
      routeDescription.SubroutineReady ∧
        routeDescription.HaltsFromTapeEquiv
          (sourceTape skipped count (some tailFirst :: tail))
          (rightEdgeTape skipped count tailFirst tail) :=
  rawBoundary_parameterizedRightEdgeRoute_exists_of_nonempty_count_enough
    skipped count tailFirst tail hnonempty hcountEnough

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
