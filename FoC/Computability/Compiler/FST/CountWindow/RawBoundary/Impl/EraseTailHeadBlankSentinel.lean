import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.EndpointSupport
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.BoundaryEraser
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.FixedBlankMoves

set_option doc.verso true

/-!
# Raw-boundary tail-head blanker

This module contains the tiny adapter that remembers the live tail-head bit in
finite control, erases that head to a blank sentinel, and halts back on the
same physical cell.  It is the first executable bridge toward routes whose
remaining left footprint can be cleared before invoking the blank-sentinel
encoded-layout finalizer.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace CountWindowRawSourceEncoder
namespace RawBoundaryRightEdgeEmitter

def tailHeadBlankSentinelRawLeftTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate (tailHeadImmediateScratchCellCount count)
        (none : Option Bool))
      (tailHeadRawBaseLeft skipped count))
    (none :: tail)

def tailHeadBlankSentinelRawBaseEdgeTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells (tailHeadRawBaseLeft skipped count)
    (List.append
      (List.replicate (tailHeadImmediateScratchCellCount count)
        (none : Option Bool))
      (none :: tail))

theorem tailHeadBlankSentinelRawLeftTape_left_length
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    (tailHeadBlankSentinelRawLeftTape skipped count tail).left.length =
      tailHeadImmediateScratchCellCount count +
        (tailHeadRawBaseLeft skipped count).length := by
  simp [tailHeadBlankSentinelRawLeftTape, tapeAtCells]

theorem tailHeadBlankSentinelRawLeftTape_left_length_eq_tailHeadHandoffTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (tailHeadBlankSentinelRawLeftTape skipped count tail).left.length =
      (tailHeadHandoffTape skipped count tailFirst tail).left.length := by
  rw [tailHeadBlankSentinelRawLeftTape_left_length]
  rw [tailHeadHandoffTape_eq_tapeAtCells_scratchBase]
  simp [tapeAtCells]

theorem leftMoveAcrossBlanksDescription_haltsFrom_tailHeadBlankSentinelRawLeftTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    (leftMoveAcrossBlanksDescription
      (tailHeadImmediateScratchCellCount count)).HaltsFromTape
      (tailHeadBlankSentinelRawLeftTape skipped count tail)
      (tailHeadBlankSentinelRawBaseEdgeTape skipped count tail) := by
  simpa [tailHeadBlankSentinelRawLeftTape,
    tailHeadBlankSentinelRawBaseEdgeTape] using
    leftMoveAcrossBlanksDescription_haltsFromTape
      (tailHeadImmediateScratchCellCount count)
      (tailHeadRawBaseLeft skipped count)
      (none : Option Bool) tail

theorem tailHeadBlankSentinelRawBaseEdgeTape_moveLeft_eq_boundaryEraserSource
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape.move Direction.left
        (tailHeadBlankSentinelRawBaseEdgeTape skipped count tail) =
      leftBoundaryEraserSourceTape
        ([] : List (Option Bool))
        (List.append skipped count)
        none
        (List.append
          (List.replicate (count.length + 2) (none : Option Bool))
          (none :: tail)) := by
  simp [tailHeadBlankSentinelRawBaseEdgeTape,
    leftBoundaryEraserSourceTape, tailHeadRawBaseLeft,
    tailHeadImmediateScratchCellCount, List.replicate_succ,
    List.append_assoc]

def tailHeadRawBaseErasedLeftBoundaryTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape Bool :=
  leftBoundaryEraserTargetTape
    ([] : List (Option Bool))
    (List.append skipped count)
    none
    (List.append
      (List.replicate (count.length + 2) (none : Option Bool))
      (none :: tail))

def eraseTailHeadRawBaseFromEdgeDescription : MachineDescription :=
  seqSubroutine ExactIdentityDescription
    leftBoundaryEraserDescription Direction.left

theorem eraseTailHeadRawBaseFromEdgeDescription_subroutineReady :
    eraseTailHeadRawBaseFromEdgeDescription.SubroutineReady := by
  rw [eraseTailHeadRawBaseFromEdgeDescription]
  exact
    seqSubroutine_subroutineReady
      CommonGround.Identity.exactIdentityDescription_subroutineReady
      leftBoundaryEraserDescription_subroutineReady

theorem eraseTailHeadRawBaseFromEdgeDescription_haltsFrom_rawBaseEdge
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    eraseTailHeadRawBaseFromEdgeDescription.HaltsFromTape
      (tailHeadBlankSentinelRawBaseEdgeTape skipped count tail)
      (tailHeadRawBaseErasedLeftBoundaryTape skipped count tail) := by
  rw [eraseTailHeadRawBaseFromEdgeDescription]
  exact
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      CommonGround.Identity.exactIdentityDescription_subroutineReady
      leftBoundaryEraserDescription_subroutineReady
      (CommonGround.Identity.exactIdentityDescription_haltsFromTape
        (tailHeadBlankSentinelRawBaseEdgeTape skipped count tail))
      (tailHeadBlankSentinelRawBaseEdgeTape_moveLeft_eq_boundaryEraserSource
        skipped count tail)
      (leftBoundaryEraserDescription_haltsFromTape
        ([] : List (Option Bool))
        (List.append skipped count)
        none
        (List.append
          (List.replicate (count.length + 2) (none : Option Bool))
          (none :: tail)))

def eraseTailHeadToBlankSentinelDescription
    (tailFirst : Bool) : MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ transition 0 (some tailFirst) none Direction.left 1
    , transition 1 none none Direction.right 2
    , transition 1 (some false) (some false) Direction.right 2
    , transition 1 (some true) (some true) Direction.right 2 ]

theorem eraseTailHeadToBlankSentinelDescription_wellFormed
    (tailFirst : Bool) :
    (eraseTailHeadToBlankSentinelDescription tailFirst).WellFormed := by
  refine
    ⟨by simp [eraseTailHeadToBlankSentinelDescription],
      by simp [eraseTailHeadToBlankSentinelDescription],
      by simp [eraseTailHeadToBlankSentinelDescription], ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := (eraseTailHeadToBlankSentinelDescription
        tailFirst).transitions)
      (stateCount := (eraseTailHeadToBlankSentinelDescription
        tailFirst).stateCount)
      (by cases tailFirst <;> decide)
  · exact transition_deterministic_of_all
      (l := (eraseTailHeadToBlankSentinelDescription
        tailFirst).transitions)
      (by cases tailFirst <;> decide)

theorem eraseTailHeadToBlankSentinelDescription_haltTransitionFree
    (tailFirst : Bool) :
    (eraseTailHeadToBlankSentinelDescription
      tailFirst).HaltTransitionFree := by
  exact transition_notFrom_of_all
    (l := (eraseTailHeadToBlankSentinelDescription
      tailFirst).transitions)
    (state := (eraseTailHeadToBlankSentinelDescription tailFirst).halt)
    (by cases tailFirst <;> decide)

theorem eraseTailHeadToBlankSentinelDescription_subroutineReady
    (tailFirst : Bool) :
    (eraseTailHeadToBlankSentinelDescription tailFirst).SubroutineReady :=
  ⟨eraseTailHeadToBlankSentinelDescription_wellFormed tailFirst,
    eraseTailHeadToBlankSentinelDescription_haltTransitionFree tailFirst⟩

theorem eraseTailHeadToBlankSentinelDescription_run
    (tailFirst : Bool) (cell : Option Bool)
    (leftRevTail tail : List (Option Bool)) :
    (eraseTailHeadToBlankSentinelDescription tailFirst).runConfig 2
        { state := (eraseTailHeadToBlankSentinelDescription
            tailFirst).start
          tape := tapeAtCells (cell :: leftRevTail)
            (some tailFirst :: tail) } =
      { state := (eraseTailHeadToBlankSentinelDescription tailFirst).halt
        tape := tapeAtCells (cell :: leftRevTail) (none :: tail) } := by
  cases tailFirst <;> cases cell with
  | none =>
      simp [eraseTailHeadToBlankSentinelDescription, runConfig,
        stepConfig, lookupTransition, Matches, transition, Tape.read,
        Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells]
  | some bit =>
      cases bit <;>
        simp [eraseTailHeadToBlankSentinelDescription, runConfig,
          stepConfig, lookupTransition, Matches, transition, Tape.read,
          Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells]

theorem eraseTailHeadToBlankSentinelDescription_haltsFrom
    (tailFirst : Bool) (cell : Option Bool)
    (leftRevTail tail : List (Option Bool)) :
    (eraseTailHeadToBlankSentinelDescription tailFirst).HaltsFromTape
      (tapeAtCells (cell :: leftRevTail) (some tailFirst :: tail))
      (tapeAtCells (cell :: leftRevTail) (none :: tail)) := by
  refine ⟨2, ?_⟩
  constructor <;>
    rw [eraseTailHeadToBlankSentinelDescription_run]

theorem eraseTailHeadToBlankSentinelDescription_haltsFrom_of_nonempty
    (tailFirst : Bool) (left tail : List (Option Bool))
    (hleft : left ≠ []) :
    (eraseTailHeadToBlankSentinelDescription tailFirst).HaltsFromTape
      (tapeAtCells left (some tailFirst :: tail))
      (tapeAtCells left (none :: tail)) := by
  cases left with
  | nil =>
      exact False.elim (hleft rfl)
  | cons cell rest =>
      exact
        eraseTailHeadToBlankSentinelDescription_haltsFrom
          tailFirst cell rest tail

theorem eraseTailHeadToBlankSentinelDescription_haltsFrom_tailHeadHandoffTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (eraseTailHeadToBlankSentinelDescription tailFirst).HaltsFromTape
      (tailHeadHandoffTape skipped count tailFirst tail)
      (tailHeadBlankSentinelRawLeftTape skipped count tail) := by
  rw [tailHeadHandoffTape_eq_tapeAtCells_scratchBase]
  rw [tailHeadBlankSentinelRawLeftTape]
  exact
    eraseTailHeadToBlankSentinelDescription_haltsFrom_of_nonempty
      tailFirst
      (List.append
        (List.replicate (tailHeadImmediateScratchCellCount count)
          (none : Option Bool))
        (tailHeadRawBaseLeft skipped count))
      tail
      (by simp [tailHeadImmediateScratchCellCount])

def sourceToTailHeadBlankSentinelDescription
    (tailFirst : Bool) : MachineDescription :=
  seqSubroutine rightBlankRunTailFirstLeftHandoffDescription
    (eraseTailHeadToBlankSentinelDescription tailFirst) Direction.right

theorem sourceToTailHeadBlankSentinelDescription_subroutineReady
    (tailFirst : Bool) :
    (sourceToTailHeadBlankSentinelDescription tailFirst).SubroutineReady := by
  rw [sourceToTailHeadBlankSentinelDescription]
  exact
    seqSubroutine_subroutineReady
      rightBlankRunTailFirstLeftHandoffDescription_subroutineReady
      (eraseTailHeadToBlankSentinelDescription_subroutineReady tailFirst)

theorem sourceToTailHeadBlankSentinelDescription_haltsFrom_sourceTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (sourceToTailHeadBlankSentinelDescription tailFirst).HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (tailHeadBlankSentinelRawLeftTape skipped count tail) := by
  rw [sourceToTailHeadBlankSentinelDescription]
  exact
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      rightBlankRunTailFirstLeftHandoffDescription_subroutineReady
      (eraseTailHeadToBlankSentinelDescription_subroutineReady tailFirst)
      (rightBlankRunTailFirstLeftHandoffDescription_haltsFrom_sourceTape
        skipped count tailFirst tail)
      (tailLeftHandoffTape_moveRight skipped count tailFirst tail)
      (eraseTailHeadToBlankSentinelDescription_haltsFrom_tailHeadHandoffTape
        skipped count tailFirst tail)

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
