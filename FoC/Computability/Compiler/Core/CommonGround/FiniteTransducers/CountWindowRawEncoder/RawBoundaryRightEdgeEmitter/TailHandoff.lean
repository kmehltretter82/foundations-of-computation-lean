import FoC.Computability.Compiler.Core.TransitionTableChecks
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.TapeLemmas

set_option doc.verso true

/-!
# Raw-boundary right-edge tail handoff

This module contains the small one-tape scanner that crosses a nonempty run of
blank gap cells to the live tail head and halts one blank to its left.  A
following sequential handoff to the right lands exactly on the live tail head,
including when the tail after that head is empty.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace CountWindowRawSourceEncoder
namespace RawBoundaryRightEdgeEmitter

def rightBlankRunTailFirstLeftHandoffDescription : MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ transition 0 none none Direction.right 0
    , transition 0 (some false) (some false) Direction.left 1
    , transition 0 (some true) (some true) Direction.left 1 ]

theorem rightBlankRunTailFirstLeftHandoffDescription_wellFormed :
    rightBlankRunTailFirstLeftHandoffDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := rightBlankRunTailFirstLeftHandoffDescription.transitions)
      (stateCount :=
        rightBlankRunTailFirstLeftHandoffDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := rightBlankRunTailFirstLeftHandoffDescription.transitions)
      (by decide)

theorem rightBlankRunTailFirstLeftHandoffDescription_haltTransitionFree :
    rightBlankRunTailFirstLeftHandoffDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := rightBlankRunTailFirstLeftHandoffDescription.transitions)
    (state := rightBlankRunTailFirstLeftHandoffDescription.halt)
    (by decide)

theorem rightBlankRunTailFirstLeftHandoffDescription_subroutineReady :
    rightBlankRunTailFirstLeftHandoffDescription.SubroutineReady :=
  ⟨rightBlankRunTailFirstLeftHandoffDescription_wellFormed,
    rightBlankRunTailFirstLeftHandoffDescription_haltTransitionFree⟩

theorem rightBlankRunTailFirstLeftHandoffDescription_step_blank
    (left right : List (Option Bool)) :
    rightBlankRunTailFirstLeftHandoffDescription.runConfig 1
        { state := rightBlankRunTailFirstLeftHandoffDescription.start
          tape := tapeAtCells left (none :: right) } =
      { state := rightBlankRunTailFirstLeftHandoffDescription.start
        tape := tapeAtCells (none :: left) right } := by
  cases right <;>
    simp [rightBlankRunTailFirstLeftHandoffDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem rightBlankRunTailFirstLeftHandoffDescription_step_tailFirst
    (left tail : List (Option Bool)) (tailFirst : Bool) :
    rightBlankRunTailFirstLeftHandoffDescription.runConfig 1
        { state := rightBlankRunTailFirstLeftHandoffDescription.start
          tape := tapeAtCells (none :: left) (some tailFirst :: tail) } =
      { state := rightBlankRunTailFirstLeftHandoffDescription.halt
        tape := tapeAtCells left (none :: some tailFirst :: tail) } := by
  cases tailFirst <;> cases tail <;>
    simp [rightBlankRunTailFirstLeftHandoffDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft]

private theorem replicate_none_append_cons
    (blankCount : Nat) (left : List (Option Bool)) :
    List.append
        (List.replicate blankCount (none : Option Bool))
        (none :: left) =
      none ::
        List.append
          (List.replicate blankCount (none : Option Bool))
          left := by
  induction blankCount with
  | zero =>
      rfl
  | succ blankCount ih =>
      simpa [List.replicate_succ, List.append_assoc] using
        congrArg (fun cells => none :: cells) ih

theorem rightBlankRunTailFirstLeftHandoffDescription_run_blanks
    (blankCount : Nat) (left tail : List (Option Bool))
    (tailFirst : Bool) :
    rightBlankRunTailFirstLeftHandoffDescription.runConfig
        blankCount
        { state := rightBlankRunTailFirstLeftHandoffDescription.start
          tape :=
            tapeAtCells left
              (List.append
                (List.replicate blankCount (none : Option Bool))
                (some tailFirst :: tail)) } =
      { state := rightBlankRunTailFirstLeftHandoffDescription.start
        tape :=
          tapeAtCells
            (List.append
              (List.replicate blankCount (none : Option Bool))
              left)
            (some tailFirst :: tail) } := by
  induction blankCount generalizing left with
  | zero =>
      simp [runConfig]
  | succ blankCount ih =>
      rw [show blankCount + 1 = 1 + blankCount by lia]
      rw [runConfig_add]
      rw [show List.replicate (1 + blankCount)
          (none : Option Bool) =
            none :: List.replicate blankCount none by
        rw [show 1 + blankCount = Nat.succ blankCount by lia]
        rfl]
      change
        rightBlankRunTailFirstLeftHandoffDescription.runConfig
            blankCount
            (rightBlankRunTailFirstLeftHandoffDescription.runConfig 1
              { state := rightBlankRunTailFirstLeftHandoffDescription.start
                tape :=
                  tapeAtCells left
                    (none ::
                      List.append
                        (List.replicate blankCount
                          (none : Option Bool))
                        (some tailFirst :: tail)) }) =
          { state := rightBlankRunTailFirstLeftHandoffDescription.start
            tape :=
              tapeAtCells
                (List.append
                  (none :: List.replicate blankCount
                    (none : Option Bool))
                  left)
                (some tailFirst :: tail) }
      rw [rightBlankRunTailFirstLeftHandoffDescription_step_blank]
      rw [ih (none :: left)]
      rw [replicate_none_append_cons]
      rfl

theorem rightBlankRunTailFirstLeftHandoffDescription_run
    (blankCount : Nat) (left tail : List (Option Bool))
    (tailFirst : Bool) :
    rightBlankRunTailFirstLeftHandoffDescription.runConfig
        (blankCount + 2)
        { state := rightBlankRunTailFirstLeftHandoffDescription.start
          tape :=
            tapeAtCells left
              (List.append
                (List.replicate (blankCount + 1)
                  (none : Option Bool))
                (some tailFirst :: tail)) } =
      { state := rightBlankRunTailFirstLeftHandoffDescription.halt
        tape :=
          tapeAtCells
            (List.append
              (List.replicate blankCount (none : Option Bool))
              left)
            (none :: some tailFirst :: tail) } := by
  rw [show blankCount + 2 = (blankCount + 1) + 1 by lia]
  rw [runConfig_add]
  rw [rightBlankRunTailFirstLeftHandoffDescription_run_blanks]
  simpa [List.replicate_succ, Nat.add_comm, List.append_assoc] using
    rightBlankRunTailFirstLeftHandoffDescription_step_tailFirst
      (List.append
        (List.replicate blankCount (none : Option Bool))
        left)
      tail tailFirst

theorem rightBlankRunTailFirstLeftHandoffDescription_haltsFromTape
    (blankCount : Nat) (left tail : List (Option Bool))
    (tailFirst : Bool) :
    rightBlankRunTailFirstLeftHandoffDescription.HaltsFromTape
      (tapeAtCells left
        (List.append
          (List.replicate (blankCount + 1) (none : Option Bool))
          (some tailFirst :: tail)))
      (tapeAtCells
        (List.append
          (List.replicate blankCount (none : Option Bool))
          left)
        (none :: some tailFirst :: tail)) := by
  refine ⟨blankCount + 2, ?_⟩
  constructor <;>
    rw [rightBlankRunTailFirstLeftHandoffDescription_run]

theorem rightBlankRunTailFirstLeftHandoffDescription_handoff_right
    (blankCount : Nat) (left tail : List (Option Bool))
    (tailFirst : Bool) :
    Tape.move Direction.right
        (tapeAtCells
          (List.append
            (List.replicate blankCount (none : Option Bool))
            left)
          (none :: some tailFirst :: tail)) =
      tapeAtCells
        (none ::
          List.append
            (List.replicate blankCount (none : Option Bool))
            left)
        (some tailFirst :: tail) := by
  exact
    tapeAtCells_move_right_cons
      (List.append
        (List.replicate blankCount (none : Option Bool))
        left)
      none
      (some tailFirst :: tail)

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
