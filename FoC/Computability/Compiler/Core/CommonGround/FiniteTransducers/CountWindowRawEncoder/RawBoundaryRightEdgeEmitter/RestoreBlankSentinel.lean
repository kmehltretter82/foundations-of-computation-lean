import FoC.Computability.Compiler.Core.TransitionTableChecks
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.TapeLemmas

set_option doc.verso true

/-!
# Raw-boundary blank-sentinel restorer

This module contains the tiny one-tape adapter that restores a remembered live
tail bit at a blank right-boundary sentinel and halts back on the restored bit.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace CountWindowRawSourceEncoder
namespace RawBoundaryRightEdgeEmitter

def restoreBlankSentinelTailHeadDescription
    (tailFirst : Bool) : MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ transition 0 none (some tailFirst) Direction.left 1
    , transition 1 none none Direction.right 2
    , transition 1 (some false) (some false) Direction.right 2
    , transition 1 (some true) (some true) Direction.right 2 ]

theorem restoreBlankSentinelTailHeadDescription_wellFormed
    (tailFirst : Bool) :
    (restoreBlankSentinelTailHeadDescription tailFirst).WellFormed := by
  refine
    ⟨by simp [restoreBlankSentinelTailHeadDescription],
      by simp [restoreBlankSentinelTailHeadDescription],
      by simp [restoreBlankSentinelTailHeadDescription], ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := (restoreBlankSentinelTailHeadDescription
        tailFirst).transitions)
      (stateCount := (restoreBlankSentinelTailHeadDescription
        tailFirst).stateCount)
      (by cases tailFirst <;> decide)
  · exact transition_deterministic_of_all
      (l := (restoreBlankSentinelTailHeadDescription
        tailFirst).transitions)
      (by cases tailFirst <;> decide)

theorem restoreBlankSentinelTailHeadDescription_haltTransitionFree
    (tailFirst : Bool) :
    (restoreBlankSentinelTailHeadDescription
      tailFirst).HaltTransitionFree := by
  exact transition_notFrom_of_all
    (l := (restoreBlankSentinelTailHeadDescription
      tailFirst).transitions)
    (state := (restoreBlankSentinelTailHeadDescription tailFirst).halt)
    (by cases tailFirst <;> decide)

theorem restoreBlankSentinelTailHeadDescription_subroutineReady
    (tailFirst : Bool) :
    (restoreBlankSentinelTailHeadDescription tailFirst).SubroutineReady :=
  ⟨restoreBlankSentinelTailHeadDescription_wellFormed tailFirst,
    restoreBlankSentinelTailHeadDescription_haltTransitionFree tailFirst⟩

theorem restoreBlankSentinelTailHeadDescription_run
    (tailFirst : Bool) (cell : Option Bool)
    (leftRevTail tail : List (Option Bool)) :
    (restoreBlankSentinelTailHeadDescription tailFirst).runConfig 2
        { state := (restoreBlankSentinelTailHeadDescription tailFirst).start
          tape := tapeAtCells (cell :: leftRevTail) (none :: tail) } =
      { state := (restoreBlankSentinelTailHeadDescription tailFirst).halt
        tape := tapeAtCells (cell :: leftRevTail)
          (some tailFirst :: tail) } := by
  cases tailFirst <;> cases cell with
  | none =>
      simp [restoreBlankSentinelTailHeadDescription, runConfig,
        stepConfig, lookupTransition, Matches, transition, Tape.read,
        Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells]
  | some bit =>
      cases bit <;>
        simp [restoreBlankSentinelTailHeadDescription, runConfig,
          stepConfig, lookupTransition, Matches, transition, Tape.read,
          Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells]

theorem restoreBlankSentinelTailHeadDescription_haltsFrom
    (tailFirst : Bool) (cell : Option Bool)
    (leftRevTail tail : List (Option Bool)) :
    (restoreBlankSentinelTailHeadDescription tailFirst).HaltsFromTape
      (tapeAtCells (cell :: leftRevTail) (none :: tail))
      (tapeAtCells (cell :: leftRevTail) (some tailFirst :: tail)) := by
  refine ⟨2, ?_⟩
  constructor <;>
    rw [restoreBlankSentinelTailHeadDescription_run]

theorem restoreBlankSentinelTailHeadDescription_haltsFrom_cons_some
    (tailFirst bit : Bool) (leftRevTail tail : List (Option Bool)) :
    (restoreBlankSentinelTailHeadDescription tailFirst).HaltsFromTape
      (tapeAtCells (some bit :: leftRevTail) (none :: tail))
      (tapeAtCells (some bit :: leftRevTail)
        (some tailFirst :: tail)) :=
  restoreBlankSentinelTailHeadDescription_haltsFrom
    tailFirst (some bit) leftRevTail tail

theorem restoreBlankSentinelTailHeadDescription_haltsFrom_of_nonempty
    (tailFirst : Bool) (left tail : List (Option Bool))
    (hleft : left ≠ []) :
    (restoreBlankSentinelTailHeadDescription tailFirst).HaltsFromTape
      (tapeAtCells left (none :: tail))
      (tapeAtCells left (some tailFirst :: tail)) := by
  cases left with
  | nil =>
      exact False.elim (hleft rfl)
  | cons cell rest =>
      exact
        restoreBlankSentinelTailHeadDescription_haltsFrom
          tailFirst cell rest tail

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
