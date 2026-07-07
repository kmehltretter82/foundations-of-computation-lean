import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawEncoder.RawBoundaryRightEdgeEmitter.FixedBranchLoop

set_option doc.verso true

/-!
# Fixed raw-boundary branch loop route contracts

This module exposes the reusable fixed-table route facts for consuming the
marked remaining raw-bit suffix and exiting through the boundary marker.
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

structure RawBoundaryFixedBranchLoopRoute
    (remaining cellSuffix : Word Bool)
    (currentScratch finalScratch : Nat)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hscratch :
      currentScratch = finalScratch + 3 * remaining.length)
    (hnonempty : List.append remaining cellSuffix ≠ []) : Prop where
  routeReady :
    rawBoundaryFixedBranchLoopDescription.SubroutineReady
  routeHalts :
    rawBoundaryFixedBranchLoopDescription.HaltsFromTapeEquiv
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        remaining currentScratch cellSuffix tailFirst tail)
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) finalScratch (List.append remaining cellSuffix)
        tailFirst tail)
  loopRun :
    Structured.MultiTapeLowering.RunsFromStateTapeEquiv
      rawBoundaryFixedBranchLoopDescription
      rawBoundaryFixedBranchLoopStart
      rawBoundaryFixedBranchLoopStart
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        remaining currentScratch cellSuffix tailFirst tail)
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) finalScratch (List.append remaining cellSuffix)
        tailFirst tail)

theorem rawBoundaryFixedBranchLoopRoute
    (remaining cellSuffix : Word Bool)
    (currentScratch finalScratch : Nat)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hscratch :
      currentScratch = finalScratch + 3 * remaining.length)
    (hnonempty : List.append remaining cellSuffix ≠ []) :
    RawBoundaryFixedBranchLoopRoute
      remaining cellSuffix currentScratch finalScratch tailFirst tail
      hscratch hnonempty :=
  { routeReady := rawBoundaryFixedBranchLoopDescription_subroutineReady
    routeHalts :=
      rawBoundaryFixedBranchLoopDescription_haltsFrom_markedCellSuffix
        remaining cellSuffix currentScratch finalScratch tailFirst tail
        hscratch hnonempty
    loopRun := by
      simpa using
        rawBoundaryFixedBranchLoopDescription_runsFrom_remaining
          ([] : Word Bool) remaining cellSuffix currentScratch
          finalScratch tailFirst tail hscratch }

theorem rawBoundary_fixedBranchLoop_haltsFrom_markedCellSuffix
    (remaining cellSuffix : Word Bool)
    (currentScratch finalScratch : Nat)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hscratch :
      currentScratch = finalScratch + 3 * remaining.length)
    (hnonempty : List.append remaining cellSuffix ≠ []) :
    rawBoundaryFixedBranchLoopDescription.HaltsFromTapeEquiv
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        remaining currentScratch cellSuffix tailFirst tail)
      (tailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) finalScratch (List.append remaining cellSuffix)
        tailFirst tail) :=
  (rawBoundaryFixedBranchLoopRoute
    remaining cellSuffix currentScratch finalScratch tailFirst tail
    hscratch hnonempty).routeHalts

theorem rawBoundary_fixedBranchLoop_runsFrom_remaining
    (remaining cellSuffix : Word Bool)
    (currentScratch finalScratch : Nat)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hscratch :
      currentScratch = finalScratch + 3 * remaining.length)
    (hnonempty : List.append remaining cellSuffix ≠ []) :
    Structured.MultiTapeLowering.RunsFromStateTapeEquiv
      rawBoundaryFixedBranchLoopDescription
      rawBoundaryFixedBranchLoopStart
      rawBoundaryFixedBranchLoopStart
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        remaining currentScratch cellSuffix tailFirst tail)
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        ([] : Word Bool) finalScratch (List.append remaining cellSuffix)
        tailFirst tail) :=
  (rawBoundaryFixedBranchLoopRoute
    remaining cellSuffix currentScratch finalScratch tailFirst tail
    hscratch hnonempty).loopRun

structure RawBoundaryFixedMarkedRemainingRightEdgeRoute
    (remaining cellSuffix : Word Bool)
    (currentScratch finalScratch : Nat)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hscratch :
      currentScratch = finalScratch + 3 * remaining.length)
    (hnonempty : List.append remaining cellSuffix ≠ []) : Prop where
  routeReady :
    (rawBoundaryFixedMarkedRemainingRawBitsToRightEdgeDescription
      remaining cellSuffix).SubroutineReady
  routeHalts :
    (rawBoundaryFixedMarkedRemainingRawBitsToRightEdgeDescription
      remaining cellSuffix).HaltsFromTapeEquiv
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        remaining currentScratch cellSuffix tailFirst tail)
      (tapeAtCells
        ((encodedLayoutBits (List.append remaining cellSuffix)).reverse.map
          some)
        (some tailFirst :: tail))

theorem rawBoundaryFixedMarkedRemainingRightEdgeRoute
    (remaining cellSuffix : Word Bool)
    (currentScratch finalScratch : Nat)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hscratch :
      currentScratch = finalScratch + 3 * remaining.length)
    (hnonempty : List.append remaining cellSuffix ≠ []) :
    RawBoundaryFixedMarkedRemainingRightEdgeRoute
      remaining cellSuffix currentScratch finalScratch tailFirst tail
      hscratch hnonempty :=
  { routeReady :=
      rawBoundaryFixedMarkedRemainingRawBitsToRightEdgeDescription_ready
        remaining cellSuffix
    routeHalts :=
      rawBoundaryFixedMarkedRemainingRawBitsToRightEdgeDescription_haltsFrom_markedCellSuffix
        remaining cellSuffix currentScratch finalScratch tailFirst tail
        hscratch hnonempty }

theorem rawBoundary_fixedMarkedRemainingRightEdge_halts
    (remaining cellSuffix : Word Bool)
    (currentScratch finalScratch : Nat)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hscratch :
      currentScratch = finalScratch + 3 * remaining.length)
    (hnonempty : List.append remaining cellSuffix ≠ []) :
    (rawBoundaryFixedMarkedRemainingRawBitsToRightEdgeDescription
      remaining cellSuffix).HaltsFromTapeEquiv
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        remaining currentScratch cellSuffix tailFirst tail)
      (tapeAtCells
        ((encodedLayoutBits (List.append remaining cellSuffix)).reverse.map
          some)
        (some tailFirst :: tail)) :=
  (rawBoundaryFixedMarkedRemainingRightEdgeRoute
    remaining cellSuffix currentScratch finalScratch tailFirst tail
    hscratch hnonempty).routeHalts

structure RawBoundaryFixedMarkedRemainingRightEdgeOutputRoute
    (remaining cellSuffix : Word Bool)
    (currentScratch finalScratch : Nat)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hscratch :
      currentScratch = finalScratch + 3 * remaining.length)
    (hnonempty : List.append remaining cellSuffix ≠ []) : Prop where
  routeReady :
    (rawBoundaryFixedMarkedRemainingRawBitsToRightEdgeDescription
      remaining cellSuffix).SubroutineReady
  routeHaltsWithOutput :
    (rawBoundaryFixedMarkedRemainingRawBitsToRightEdgeDescription
      remaining cellSuffix).HaltsFromTapeWithOutput
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        remaining currentScratch cellSuffix tailFirst tail)
      (rightEdgeOutputWord remaining cellSuffix tailFirst tail)

theorem rawBoundary_fixedMarkedRemainingRightEdge_haltsWithOutput
    (remaining cellSuffix : Word Bool)
    (currentScratch finalScratch : Nat)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hscratch :
      currentScratch = finalScratch + 3 * remaining.length)
    (hnonempty : List.append remaining cellSuffix ≠ []) :
    (rawBoundaryFixedMarkedRemainingRawBitsToRightEdgeDescription
      remaining cellSuffix).HaltsFromTapeWithOutput
      (rawBoundaryLeftMarkedTailHeadEmittedCellSuffixLeftEdgeScratchTape
        remaining currentScratch cellSuffix tailFirst tail)
      (rightEdgeOutputWord remaining cellSuffix tailFirst tail) := by
  have hrun :=
    MachineDescription.haltsFromTapeWithOutput_of_haltsFromTapeEquiv
      (rawBoundary_fixedMarkedRemainingRightEdge_halts
        remaining cellSuffix currentScratch finalScratch tailFirst tail
        hscratch hnonempty)
  have htarget :
      tapeAtCells
          (List.map some
            (List.reverse
              (encodedLayoutBits (List.append remaining cellSuffix))))
          (some tailFirst :: tail) =
        rightEdgeTape remaining cellSuffix tailFirst tail := by
    simp [rightEdgeTape]
  rw [htarget] at hrun
  simpa [rightEdgeTape_normalizedOutput] using hrun

theorem rawBoundaryFixedMarkedRemainingRightEdgeOutputRoute
    (remaining cellSuffix : Word Bool)
    (currentScratch finalScratch : Nat)
    (tailFirst : Bool) (tail : List (Option Bool))
    (hscratch :
      currentScratch = finalScratch + 3 * remaining.length)
    (hnonempty : List.append remaining cellSuffix ≠ []) :
    RawBoundaryFixedMarkedRemainingRightEdgeOutputRoute
      remaining cellSuffix currentScratch finalScratch tailFirst tail
      hscratch hnonempty :=
  { routeReady :=
      rawBoundaryFixedMarkedRemainingRawBitsToRightEdgeDescription_ready
        remaining cellSuffix
    routeHaltsWithOutput :=
      rawBoundary_fixedMarkedRemainingRightEdge_haltsWithOutput
        remaining cellSuffix currentScratch finalScratch tailFirst tail
        hscratch hnonempty }

structure RawBoundarySourceFirstRawBitThenFixedRightEdgeRoute
    (skipped count : Word Bool)
    (rawBit tailFirst : Bool) (tail : List (Option Bool))
    (hlayout : List.append skipped count = [rawBit]) : Prop where
  routeReady :
    (rawBoundarySourceFirstRawBitThenFixedRightEdgeDescription
      rawBit).SubroutineReady
  routeHalts :
    (rawBoundarySourceFirstRawBitThenFixedRightEdgeDescription
      rawBit).HaltsFromTapeEquiv
      (sourceTape skipped count (some tailFirst :: tail))
      (rightEdgeTape skipped count tailFirst tail)

theorem rawBoundarySourceFirstRawBitThenFixedRightEdgeRoute
    (skipped count : Word Bool)
    (rawBit tailFirst : Bool) (tail : List (Option Bool))
    (hlayout : List.append skipped count = [rawBit]) :
    RawBoundarySourceFirstRawBitThenFixedRightEdgeRoute
      skipped count rawBit tailFirst tail hlayout :=
  { routeReady :=
      rawBoundarySourceFirstRawBitThenFixedRightEdgeDescription_ready
        rawBit
    routeHalts :=
      rawBoundarySourceFirstRawBitThenFixedRightEdgeDescription_haltsFrom_sourceTape
        skipped count rawBit tailFirst tail hlayout }

theorem rawBoundary_sourceFirstRawBitThenFixedRightEdge_halts
    (skipped count : Word Bool)
    (rawBit tailFirst : Bool) (tail : List (Option Bool))
    (hlayout : List.append skipped count = [rawBit]) :
    (rawBoundarySourceFirstRawBitThenFixedRightEdgeDescription
      rawBit).HaltsFromTapeEquiv
      (sourceTape skipped count (some tailFirst :: tail))
      (rightEdgeTape skipped count tailFirst tail) :=
  (rawBoundarySourceFirstRawBitThenFixedRightEdgeRoute
    skipped count rawBit tailFirst tail hlayout).routeHalts

theorem rawBoundary_sourceFirstRawBitThenFixedRightEdge_halts_exists
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool))
    (hlength : (List.append skipped count).length = 1) :
    exists rawBit : Bool,
      List.append skipped count = [rawBit] ∧
        (rawBoundarySourceFirstRawBitThenFixedRightEdgeDescription
          rawBit).HaltsFromTapeEquiv
          (sourceTape skipped count (some tailFirst :: tail))
          (rightEdgeTape skipped count tailFirst tail) :=
  rawBoundarySourceFirstRawBitThenFixedRightEdgeDescription_haltsFrom_sourceTape_exists_of_layout_length_one
    skipped count tailFirst tail hlength

structure RawBoundarySourceFirstTwoThenFixedRemainingRightEdgeRoute
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
    (rawBoundarySourceFirstTwoThenFixedRemainingRawBitsToRightEdgeDescription
      remaining nextRawBit emittedRawBit).SubroutineReady
  routeHalts :
    (rawBoundarySourceFirstTwoThenFixedRemainingRawBitsToRightEdgeDescription
      remaining nextRawBit emittedRawBit).HaltsFromTapeEquiv
      (sourceTape skipped count (some tailFirst :: tail))
      (rightEdgeTape skipped count tailFirst tail)

theorem rawBoundarySourceFirstTwoThenFixedRemainingRightEdgeRoute
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
    RawBoundarySourceFirstTwoThenFixedRemainingRightEdgeRoute
      skipped count remaining scratchAfterTwo finalScratch nextRawBit
      emittedRawBit tailFirst tail hlayout hcount hremainingScratch :=
  { routeReady :=
      rawBoundarySourceFirstTwoThenFixedRemainingRawBitsToRightEdgeDescription_ready
        remaining nextRawBit emittedRawBit
    routeHalts :=
      rawBoundarySourceFirstTwoThenFixedRemainingRawBitsToRightEdgeDescription_haltsFrom_sourceTape_of_count_lengths
        skipped count remaining scratchAfterTwo finalScratch nextRawBit
        emittedRawBit tailFirst tail hlayout hcount hremainingScratch }

theorem rawBoundary_sourceFirstTwoThenFixedRemainingRightEdge_halts
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
    (rawBoundarySourceFirstTwoThenFixedRemainingRawBitsToRightEdgeDescription
      remaining nextRawBit emittedRawBit).HaltsFromTapeEquiv
      (sourceTape skipped count (some tailFirst :: tail))
      (rightEdgeTape skipped count tailFirst tail) :=
  (rawBoundarySourceFirstTwoThenFixedRemainingRightEdgeRoute
    skipped count remaining scratchAfterTwo finalScratch nextRawBit
    emittedRawBit tailFirst tail hlayout hcount hremainingScratch).routeHalts

theorem rawBoundary_sourceFirstTwoThenFixedRemainingRightEdge_halts_exists
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
                (rawBoundarySourceFirstTwoThenFixedRemainingRawBitsToRightEdgeDescription
                  remaining nextRawBit emittedRawBit).HaltsFromTapeEquiv
                  (sourceTape skipped count (some tailFirst :: tail))
                  (rightEdgeTape skipped count tailFirst tail) :=
  firstTwoThenFixedRemaining_toRightEdge_exists_ofLayoutCount
    skipped count tailFirst tail hlayoutLength hcountEnough

def RawBoundaryFixedSourceBranchRoute
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) : Prop :=
  exists routeDescription : MachineDescription,
    routeDescription.SubroutineReady ∧
      routeDescription.HaltsFromTapeEquiv
        (sourceTape skipped count (some tailFirst :: tail))
        (rightEdgeTape skipped count tailFirst tail)

def RawBoundaryFixedSourceBranchOutputRoute
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) : Prop :=
  exists routeDescription : MachineDescription,
    routeDescription.SubroutineReady ∧
      routeDescription.HaltsFromTapeWithOutput
        (sourceTape skipped count (some tailFirst :: tail))
        (rightEdgeOutputWord skipped count tailFirst tail)

theorem rawBoundaryFixedSourceBranchRoute
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool))
    (hbound : sourceBranchRouteCountBound skipped count) :
    RawBoundaryFixedSourceBranchRoute
      skipped count tailFirst tail :=
  fixedSourceBranchRouteDescription_exists_haltsFrom_sourceTape_equiv
    skipped count tailFirst tail hbound

theorem rawBoundary_fixedSourceBranchRoute_halts_exists
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool))
    (hbound : sourceBranchRouteCountBound skipped count) :
    exists routeDescription : MachineDescription,
      routeDescription.SubroutineReady ∧
        routeDescription.HaltsFromTapeEquiv
          (sourceTape skipped count (some tailFirst :: tail))
          (rightEdgeTape skipped count tailFirst tail) :=
  fixedSourceBranchRouteDescription_exists_haltsFrom_sourceTape_equiv
    skipped count tailFirst tail hbound

theorem rawBoundary_fixedSourceBranchRoute_haltsWithOutput_exists
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool))
    (hbound : sourceBranchRouteCountBound skipped count) :
    exists routeDescription : MachineDescription,
      routeDescription.SubroutineReady ∧
        routeDescription.HaltsFromTapeWithOutput
          (sourceTape skipped count (some tailFirst :: tail))
        (rightEdgeOutputWord skipped count tailFirst tail) := by
  rcases
      rawBoundary_fixedSourceBranchRoute_halts_exists
        skipped count tailFirst tail hbound with
    ⟨routeDescription, hready, hrun⟩
  refine ⟨routeDescription, hready, ?_⟩
  have houtput :=
    MachineDescription.haltsFromTapeWithOutput_of_haltsFromTapeEquiv hrun
  simpa [rightEdgeTape_normalizedOutput] using houtput

theorem rawBoundaryFixedSourceBranchOutputRoute
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool))
    (hbound : sourceBranchRouteCountBound skipped count) :
    RawBoundaryFixedSourceBranchOutputRoute
      skipped count tailFirst tail :=
  rawBoundary_fixedSourceBranchRoute_haltsWithOutput_exists
    skipped count tailFirst tail hbound

theorem sourceBranchRouteCountBound_of_nonempty_count_enough
    (skipped count : Word Bool)
    (hnonempty : List.append skipped count ≠ [])
    (hcountEnough :
      2 <= (List.append skipped count).length ->
        3 * ((List.append skipped count).length - 2) + 3 <=
          count.length) :
    sourceBranchRouteCountBound skipped count := by
  cases hlayout : List.append skipped count with
  | nil =>
      exact False.elim (hnonempty hlayout)
  | cons bit rest =>
      cases rest with
      | nil =>
          left
          simpa using congrArg List.length hlayout
      | cons next rest =>
          right
          cases rest with
          | nil =>
              left
              have hlength :
                  (List.append skipped count).length = 2 := by
                simpa using congrArg List.length hlayout
              constructor
              · exact hlength
              · have htwo :
                    2 <= (List.append skipped count).length := by
                  rw [hlength]
                  decide
                have hcount := hcountEnough htwo
                rw [hlength] at hcount
                simpa using hcount
          | cons third rest =>
              right
              have hge :
                  3 <= (List.append skipped count).length := by
                rw [hlayout]
                simp
              constructor
              · exact hge
              · have htwo :
                    2 <= (List.append skipped count).length :=
                  Nat.le_trans (by decide) hge
                have hcount := hcountEnough htwo
                have heq :
                    3 * ((List.append skipped count).length - 3) + 6 =
                      3 * ((List.append skipped count).length - 2) + 3 := by
                  lia
                rw [heq]
                exact hcount

theorem sourceBranchRouteCountBound_of_nonempty_count_ge_three_pred
    (skipped count : Word Bool)
    (hnonempty : List.append skipped count ≠ [])
    (hcountEnough :
      3 * ((List.append skipped count).length - 1) <= count.length) :
    sourceBranchRouteCountBound skipped count := by
  refine
    sourceBranchRouteCountBound_of_nonempty_count_enough
      skipped count hnonempty ?_
  intro htwo
  have heq :
      3 * ((List.append skipped count).length - 2) + 3 =
        3 * ((List.append skipped count).length - 1) := by
    lia
  rw [heq]
  exact hcountEnough

theorem rawBoundaryFixedSourceBranchRoute_of_nonempty_count_enough
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool))
    (hnonempty : List.append skipped count ≠ [])
    (hcountEnough :
      2 <= (List.append skipped count).length ->
        3 * ((List.append skipped count).length - 2) + 3 <=
          count.length) :
    RawBoundaryFixedSourceBranchRoute
      skipped count tailFirst tail :=
  rawBoundaryFixedSourceBranchRoute
    skipped count tailFirst tail
    (sourceBranchRouteCountBound_of_nonempty_count_enough
      skipped count hnonempty hcountEnough)

theorem rawBoundaryFixedSourceBranchOutputRoute_of_nonempty_count_enough
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool))
    (hnonempty : List.append skipped count ≠ [])
    (hcountEnough :
      2 <= (List.append skipped count).length ->
        3 * ((List.append skipped count).length - 2) + 3 <=
          count.length) :
    RawBoundaryFixedSourceBranchOutputRoute
      skipped count tailFirst tail :=
  rawBoundaryFixedSourceBranchOutputRoute
    skipped count tailFirst tail
    (sourceBranchRouteCountBound_of_nonempty_count_enough
      skipped count hnonempty hcountEnough)

theorem rawBoundaryFixedSourceBranchRoute_of_nonempty_count_ge_three_pred
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool))
    (hnonempty : List.append skipped count ≠ [])
    (hcountEnough :
      3 * ((List.append skipped count).length - 1) <= count.length) :
    RawBoundaryFixedSourceBranchRoute
      skipped count tailFirst tail :=
  rawBoundaryFixedSourceBranchRoute
    skipped count tailFirst tail
    (sourceBranchRouteCountBound_of_nonempty_count_ge_three_pred
      skipped count hnonempty hcountEnough)

theorem rawBoundaryFixedSourceBranchOutputRoute_of_nonempty_count_ge_three_pred
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool))
    (hnonempty : List.append skipped count ≠ [])
    (hcountEnough :
      3 * ((List.append skipped count).length - 1) <= count.length) :
    RawBoundaryFixedSourceBranchOutputRoute
      skipped count tailFirst tail :=
  rawBoundaryFixedSourceBranchOutputRoute
    skipped count tailFirst tail
    (sourceBranchRouteCountBound_of_nonempty_count_ge_three_pred
      skipped count hnonempty hcountEnough)

theorem rawBoundary_fixedSourceBranchRoute_halts_exists_of_nonempty_count_enough
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool))
    (hnonempty : List.append skipped count ≠ [])
    (hcountEnough :
      2 <= (List.append skipped count).length ->
        3 * ((List.append skipped count).length - 2) + 3 <=
          count.length) :
    exists routeDescription : MachineDescription,
      routeDescription.SubroutineReady ∧
        routeDescription.HaltsFromTapeEquiv
          (sourceTape skipped count (some tailFirst :: tail))
          (rightEdgeTape skipped count tailFirst tail) := by
  apply rawBoundary_fixedSourceBranchRoute_halts_exists
  exact
    sourceBranchRouteCountBound_of_nonempty_count_enough
      skipped count hnonempty hcountEnough

theorem rawBoundary_fixedSourceBranchRoute_haltsWithOutput_exists_of_nonempty_count_enough
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool))
    (hnonempty : List.append skipped count ≠ [])
    (hcountEnough :
      2 <= (List.append skipped count).length ->
        3 * ((List.append skipped count).length - 2) + 3 <=
          count.length) :
    exists routeDescription : MachineDescription,
      routeDescription.SubroutineReady ∧
        routeDescription.HaltsFromTapeWithOutput
          (sourceTape skipped count (some tailFirst :: tail))
          (rightEdgeOutputWord skipped count tailFirst tail) := by
  apply rawBoundary_fixedSourceBranchRoute_haltsWithOutput_exists
  exact
    sourceBranchRouteCountBound_of_nonempty_count_enough
      skipped count hnonempty hcountEnough

theorem rawBoundary_fixedSourceBranchRoute_halts_exists_of_nonempty_count_ge_three_pred
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool))
    (hnonempty : List.append skipped count ≠ [])
    (hcountEnough :
      3 * ((List.append skipped count).length - 1) <= count.length) :
    exists routeDescription : MachineDescription,
      routeDescription.SubroutineReady ∧
        routeDescription.HaltsFromTapeEquiv
          (sourceTape skipped count (some tailFirst :: tail))
          (rightEdgeTape skipped count tailFirst tail) := by
  apply rawBoundary_fixedSourceBranchRoute_halts_exists
  exact
    sourceBranchRouteCountBound_of_nonempty_count_ge_three_pred
      skipped count hnonempty hcountEnough

theorem rawBoundary_fixedSourceBranchRoute_haltsWithOutput_exists_of_nonempty_count_ge_three_pred
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool))
    (hnonempty : List.append skipped count ≠ [])
    (hcountEnough :
      3 * ((List.append skipped count).length - 1) <= count.length) :
    exists routeDescription : MachineDescription,
      routeDescription.SubroutineReady ∧
        routeDescription.HaltsFromTapeWithOutput
          (sourceTape skipped count (some tailFirst :: tail))
          (rightEdgeOutputWord skipped count tailFirst tail) := by
  apply rawBoundary_fixedSourceBranchRoute_haltsWithOutput_exists
  exact
    sourceBranchRouteCountBound_of_nonempty_count_ge_three_pred
      skipped count hnonempty hcountEnough

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
