import FoC.Computability.Compiler.Core.TransitionTableChecks
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.TapeLemmas

set_option doc.verso true

/-!
# Raw-boundary nearest-bit puller

This module provides the first fixed one-tape primitive needed by the
nonempty raw-boundary emitter loop.  Starting on the live tail head, it scans
left across a nonempty blank gap to the nearest raw layout bit, erases that
source bit, returns right across the same blank gap, and leaves the remembered
bit as a one-cell marker immediately to the left of the live tail head.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace CountWindowRawSourceEncoder
namespace RawBoundaryRightEdgeEmitter

def pullNearestRawBitToTailMarkerDescription : MachineDescription where
  stateCount := 7
  start := 0
  halt := 6
  transitions :=
    [ transition 0 (some false) (some false) Direction.left 1
    , transition 0 (some true) (some true) Direction.left 1
    , transition 1 none none Direction.left 1
    , transition 1 (some false) none Direction.right 2
    , transition 1 (some true) none Direction.right 3
    , transition 2 none none Direction.right 2
    , transition 2 (some false) (some false) Direction.left 4
    , transition 2 (some true) (some true) Direction.left 4
    , transition 3 none none Direction.right 3
    , transition 3 (some false) (some false) Direction.left 5
    , transition 3 (some true) (some true) Direction.left 5
    , transition 4 none (some false) Direction.right 6
    , transition 5 none (some true) Direction.right 6 ]

theorem pullNearestRawBitToTailMarkerDescription_wellFormed :
    pullNearestRawBitToTailMarkerDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := pullNearestRawBitToTailMarkerDescription.transitions)
      (stateCount :=
        pullNearestRawBitToTailMarkerDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := pullNearestRawBitToTailMarkerDescription.transitions)
      (by decide)

theorem pullNearestRawBitToTailMarkerDescription_haltTransitionFree :
    pullNearestRawBitToTailMarkerDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := pullNearestRawBitToTailMarkerDescription.transitions)
    (state := pullNearestRawBitToTailMarkerDescription.halt)
    (by decide)

theorem pullNearestRawBitToTailMarkerDescription_subroutineReady :
    pullNearestRawBitToTailMarkerDescription.SubroutineReady :=
  ⟨pullNearestRawBitToTailMarkerDescription_wellFormed,
    pullNearestRawBitToTailMarkerDescription_haltTransitionFree⟩

def pullNearestRawBitToTailMarkerSourceTape
    (blankCount : Nat) (baseLeft : List (Option Bool))
    (rawBit tailFirst : Bool) (tail : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate (blankCount + 1) (none : Option Bool))
      (some rawBit :: baseLeft))
    (some tailFirst :: tail)

def pullNearestRawBitToTailMarkerTargetTape
    (blankCount : Nat) (baseLeft : List (Option Bool))
    (rawBit tailFirst : Bool) (tail : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells
    (some rawBit ::
      List.append
        (List.replicate (blankCount + 1) (none : Option Bool))
        baseLeft)
    (some tailFirst :: tail)

def pullNearestRawBitToHeadMarkerSourceTape
    (gap : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool) (right : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate gap (none : Option Bool))
      (some rawBit :: baseLeft))
    (some headBit :: right)

def pullNearestRawBitToHeadMarkerTargetTape
    (gap : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool) (right : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells
    (some rawBit ::
      List.append
        (List.replicate gap (none : Option Bool))
        baseLeft)
    (some headBit :: right)

theorem pullNearestRawBitToHeadMarkerSourceTape_cells
    (gap : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool) (right : List (Option Bool)) :
    Tape.cells
        (pullNearestRawBitToHeadMarkerSourceTape
          gap baseLeft rawBit headBit right) =
      List.append baseLeft.reverse
        (some rawBit ::
          List.append (List.replicate gap (none : Option Bool))
            (some headBit :: right)) := by
  simp [pullNearestRawBitToHeadMarkerSourceTape, Tape.cells,
    tapeAtCells, List.reverse_append, List.append_assoc]

theorem pullNearestRawBitToHeadMarkerTargetTape_cells
    (gap : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool) (right : List (Option Bool)) :
    Tape.cells
        (pullNearestRawBitToHeadMarkerTargetTape
          gap baseLeft rawBit headBit right) =
      List.append baseLeft.reverse
        (List.append (List.replicate gap (none : Option Bool))
          (some rawBit :: some headBit :: right)) := by
  simp [pullNearestRawBitToHeadMarkerTargetTape, Tape.cells,
    tapeAtCells, List.reverse_append, List.append_assoc]

theorem pullNearestRawBitToHeadMarkerSourceTape_left_length
    (gap : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool) (right : List (Option Bool)) :
    (pullNearestRawBitToHeadMarkerSourceTape
      gap baseLeft rawBit headBit right).left.length =
      gap + baseLeft.length + 1 := by
  simp [pullNearestRawBitToHeadMarkerSourceTape, tapeAtCells,
    List.length_append]
  lia

theorem pullNearestRawBitToHeadMarkerTargetTape_left_length
    (gap : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool) (right : List (Option Bool)) :
    (pullNearestRawBitToHeadMarkerTargetTape
      gap baseLeft rawBit headBit right).left.length =
      gap + baseLeft.length + 1 := by
  simp [pullNearestRawBitToHeadMarkerTargetTape, tapeAtCells,
    List.length_append]

private theorem replicate_none_append_none_cons
    (blankCount : Nat) (baseLeft : List (Option Bool)) :
    List.append (List.replicate blankCount (none : Option Bool))
        (none :: none :: baseLeft) =
      none ::
        List.append (List.replicate blankCount (none : Option Bool))
          (none :: baseLeft) := by
  induction blankCount with
  | zero =>
      rfl
  | succ blankCount ih =>
      simpa [List.replicate_succ, List.append_assoc] using
        congrArg (fun cells => none :: cells) ih

private theorem replicate_none_append_cons_eq
    (blankCount : Nat) (baseLeft : List (Option Bool)) :
    List.append (List.replicate blankCount (none : Option Bool))
        (none :: baseLeft) =
      List.append
        (List.replicate (blankCount + 1) (none : Option Bool))
        baseLeft := by
  induction blankCount with
  | zero =>
      rfl
  | succ blankCount ih =>
      rw [show Nat.succ blankCount + 1 =
        Nat.succ (blankCount + 1) by lia]
      simpa [List.replicate_succ] using
        congrArg (fun cells => none :: cells) ih

private theorem cons_replicate_none_append_none_cons_eq
    (blankCount : Nat) (right : List (Option Bool)) :
    none ::
        List.append (List.replicate blankCount (none : Option Bool))
          (none :: right) =
      List.append
        (List.replicate (1 + (blankCount + 1)) (none : Option Bool))
        right := by
  induction blankCount with
  | zero =>
      rfl
  | succ blankCount ih =>
      rw [show 1 + (Nat.succ blankCount + 1) =
        Nat.succ (1 + (blankCount + 1)) by lia]
      simpa [List.replicate_succ] using
        congrArg (fun cells => none :: cells) ih

theorem pullNearestRawBitToTailMarkerDescription_step_start
    (left : List (Option Bool)) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    pullNearestRawBitToTailMarkerDescription.runConfig 1
        { state := pullNearestRawBitToTailMarkerDescription.start
          tape := tapeAtCells (none :: left) (some tailFirst :: tail) } =
      { state := 1
        tape := tapeAtCells left (none :: some tailFirst :: tail) } := by
  cases tailFirst <;> cases left <;> cases tail <;>
    simp [pullNearestRawBitToTailMarkerDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem pullNearestRawBitToTailMarkerDescription_step_start_adjacent
    (baseLeft : List (Option Bool)) (rawBit headBit : Bool)
    (right : List (Option Bool)) :
    pullNearestRawBitToTailMarkerDescription.runConfig 1
        { state := pullNearestRawBitToTailMarkerDescription.start
          tape := tapeAtCells (some rawBit :: baseLeft)
            (some headBit :: right) } =
      { state := 1
        tape := tapeAtCells baseLeft
          (some rawBit :: some headBit :: right) } := by
  cases rawBit <;> cases headBit <;> cases baseLeft <;>
    cases right <;>
      simp [pullNearestRawBitToTailMarkerDescription, runConfig,
        stepConfig, lookupTransition, Matches, transition, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem pullNearestRawBitToTailMarkerDescription_step_scan_blank
    (cell : Option Bool) (left right : List (Option Bool)) :
    pullNearestRawBitToTailMarkerDescription.runConfig 1
        { state := 1
          tape := tapeAtCells (cell :: left) (none :: right) } =
      { state := 1
        tape := tapeAtCells left (cell :: none :: right) } := by
  cases cell <;> cases left <;> cases right <;>
    simp [pullNearestRawBitToTailMarkerDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem pullNearestRawBitToTailMarkerDescription_run_scan_blanks
    (blankCount : Nat) (baseLeft right : List (Option Bool))
    (rawBit : Bool) :
    pullNearestRawBitToTailMarkerDescription.runConfig
        (blankCount + 1)
        { state := 1
          tape :=
            tapeAtCells
              (List.append
                (List.replicate blankCount (none : Option Bool))
                (some rawBit :: baseLeft))
              (none :: right) } =
      { state := 1
        tape :=
          tapeAtCells baseLeft
            (some rawBit ::
              List.append
                (List.replicate (blankCount + 1)
                  (none : Option Bool))
                right) } := by
  induction blankCount generalizing baseLeft right with
  | zero =>
      simpa using
        pullNearestRawBitToTailMarkerDescription_step_scan_blank
          (some rawBit) baseLeft right
  | succ blankCount ih =>
      rw [show Nat.succ blankCount + 1 =
        1 + (blankCount + 1) by lia]
      rw [runConfig_add]
      rw [show
          List.replicate (blankCount + 1) (none : Option Bool) =
            none :: List.replicate blankCount none by
        rw [show blankCount + 1 = Nat.succ blankCount by lia]
        rfl]
      rw [show
          List.append
              (none :: List.replicate blankCount (none : Option Bool))
              (some rawBit :: baseLeft) =
            none ::
              List.append (List.replicate blankCount none)
                (some rawBit :: baseLeft) by
        rfl]
      change
        pullNearestRawBitToTailMarkerDescription.runConfig
            (blankCount + 1)
            (pullNearestRawBitToTailMarkerDescription.runConfig 1
              { state := 1
                tape :=
                  tapeAtCells
                    (none ::
                      List.append
                        (List.replicate blankCount
                          (none : Option Bool))
                        (some rawBit :: baseLeft))
                    (none :: right) }) =
          { state := 1
            tape :=
              tapeAtCells baseLeft
                (some rawBit ::
                  List.append
                    (List.replicate (1 + (blankCount + 1))
                      (none : Option Bool))
                    right) }
      rw [pullNearestRawBitToTailMarkerDescription_step_scan_blank]
      rw [ih baseLeft (none :: right)]
      rw [replicate_none_append_cons_eq (blankCount + 1) right]
      rw [show blankCount + 1 + 1 = 1 + (blankCount + 1) by
        lia]

theorem pullNearestRawBitToTailMarkerDescription_step_raw_false
    (baseLeft right : List (Option Bool)) :
    pullNearestRawBitToTailMarkerDescription.runConfig 1
        { state := 1
          tape := tapeAtCells baseLeft (some false :: right) } =
      { state := 2
        tape := tapeAtCells (none :: baseLeft) right } := by
  cases right <;>
    simp [pullNearestRawBitToTailMarkerDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem pullNearestRawBitToTailMarkerDescription_step_raw_true
    (baseLeft right : List (Option Bool)) :
    pullNearestRawBitToTailMarkerDescription.runConfig 1
        { state := 1
          tape := tapeAtCells baseLeft (some true :: right) } =
      { state := 3
        tape := tapeAtCells (none :: baseLeft) right } := by
  cases right <;>
    simp [pullNearestRawBitToTailMarkerDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem pullNearestRawBitToTailMarkerDescription_step_return_blank_false
    (left right : List (Option Bool)) :
    pullNearestRawBitToTailMarkerDescription.runConfig 1
        { state := 2
          tape := tapeAtCells left (none :: right) } =
      { state := 2
        tape := tapeAtCells (none :: left) right } := by
  cases right <;>
    simp [pullNearestRawBitToTailMarkerDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem pullNearestRawBitToTailMarkerDescription_step_return_blank_true
    (left right : List (Option Bool)) :
    pullNearestRawBitToTailMarkerDescription.runConfig 1
        { state := 3
          tape := tapeAtCells left (none :: right) } =
      { state := 3
        tape := tapeAtCells (none :: left) right } := by
  cases right <;>
    simp [pullNearestRawBitToTailMarkerDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem pullNearestRawBitToTailMarkerDescription_run_return_blanks_false
    (blankCount : Nat) (baseLeft : List (Option Bool))
    (tailFirst : Bool) (tail : List (Option Bool)) :
    pullNearestRawBitToTailMarkerDescription.runConfig blankCount
        { state := 2
          tape :=
            tapeAtCells (none :: baseLeft)
              (List.append
                (List.replicate blankCount (none : Option Bool))
                (some tailFirst :: tail)) } =
      { state := 2
        tape :=
          tapeAtCells
            (List.append
              (List.replicate blankCount (none : Option Bool))
              (none :: baseLeft))
            (some tailFirst :: tail) } := by
  induction blankCount generalizing baseLeft with
  | zero =>
      simp [runConfig]
  | succ blankCount ih =>
      rw [show blankCount + 1 =
        1 + blankCount by lia]
      rw [runConfig_add]
      rw [show
          List.replicate (1 + blankCount) (none : Option Bool) =
            none :: List.replicate blankCount none by
        rw [show 1 + blankCount = Nat.succ blankCount by lia]
        rfl]
      change
        pullNearestRawBitToTailMarkerDescription.runConfig blankCount
            (pullNearestRawBitToTailMarkerDescription.runConfig 1
              { state := 2
                tape :=
                  tapeAtCells (none :: baseLeft)
                    (none ::
                      List.append
                        (List.replicate blankCount
                          (none : Option Bool))
                        (some tailFirst :: tail)) }) =
          { state := 2
            tape :=
              tapeAtCells
                (List.append
                  (List.replicate (Nat.succ blankCount)
                    (none : Option Bool))
                  (none :: baseLeft))
                (some tailFirst :: tail) }
      rw [pullNearestRawBitToTailMarkerDescription_step_return_blank_false]
      rw [ih (none :: baseLeft)]
      rw [replicate_none_append_none_cons]
      rw [show
          List.replicate (Nat.succ blankCount) (none : Option Bool) =
            none :: List.replicate blankCount none by
        rfl]
      rfl

theorem pullNearestRawBitToTailMarkerDescription_run_return_blanks_true
    (blankCount : Nat) (baseLeft : List (Option Bool))
    (tailFirst : Bool) (tail : List (Option Bool)) :
    pullNearestRawBitToTailMarkerDescription.runConfig blankCount
        { state := 3
          tape :=
            tapeAtCells (none :: baseLeft)
              (List.append
                (List.replicate blankCount (none : Option Bool))
                (some tailFirst :: tail)) } =
      { state := 3
        tape :=
          tapeAtCells
            (List.append
              (List.replicate blankCount (none : Option Bool))
              (none :: baseLeft))
            (some tailFirst :: tail) } := by
  induction blankCount generalizing baseLeft with
  | zero =>
      simp [runConfig]
  | succ blankCount ih =>
      rw [show blankCount + 1 =
        1 + blankCount by lia]
      rw [runConfig_add]
      rw [show
          List.replicate (1 + blankCount) (none : Option Bool) =
            none :: List.replicate blankCount none by
        rw [show 1 + blankCount = Nat.succ blankCount by lia]
        rfl]
      change
        pullNearestRawBitToTailMarkerDescription.runConfig blankCount
            (pullNearestRawBitToTailMarkerDescription.runConfig 1
              { state := 3
                tape :=
                  tapeAtCells (none :: baseLeft)
                    (none ::
                      List.append
                        (List.replicate blankCount
                          (none : Option Bool))
                        (some tailFirst :: tail)) }) =
          { state := 3
            tape :=
              tapeAtCells
                (List.append
                  (List.replicate (Nat.succ blankCount)
                    (none : Option Bool))
                  (none :: baseLeft))
                (some tailFirst :: tail) }
      rw [pullNearestRawBitToTailMarkerDescription_step_return_blank_true]
      rw [ih (none :: baseLeft)]
      rw [replicate_none_append_none_cons]
      rw [show
          List.replicate (Nat.succ blankCount) (none : Option Bool) =
            none :: List.replicate blankCount none by
        rfl]
      rfl

theorem pullNearestRawBitToTailMarkerDescription_step_tail_false
    (left : List (Option Bool)) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    pullNearestRawBitToTailMarkerDescription.runConfig 1
        { state := 2
          tape := tapeAtCells (none :: left) (some tailFirst :: tail) } =
      { state := 4
        tape := tapeAtCells left (none :: some tailFirst :: tail) } := by
  cases tailFirst <;> cases left <;> cases tail <;>
    simp [pullNearestRawBitToTailMarkerDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem pullNearestRawBitToTailMarkerDescription_step_tail_true
    (left : List (Option Bool)) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    pullNearestRawBitToTailMarkerDescription.runConfig 1
        { state := 3
          tape := tapeAtCells (none :: left) (some tailFirst :: tail) } =
      { state := 5
        tape := tapeAtCells left (none :: some tailFirst :: tail) } := by
  cases tailFirst <;> cases left <;> cases tail <;>
    simp [pullNearestRawBitToTailMarkerDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem pullNearestRawBitToTailMarkerDescription_step_write_false
    (left : List (Option Bool)) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    pullNearestRawBitToTailMarkerDescription.runConfig 1
        { state := 4
          tape := tapeAtCells left (none :: some tailFirst :: tail) } =
      { state := pullNearestRawBitToTailMarkerDescription.halt
        tape := tapeAtCells (some false :: left)
          (some tailFirst :: tail) } := by
  cases tailFirst <;> cases tail <;>
    simp [pullNearestRawBitToTailMarkerDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem pullNearestRawBitToTailMarkerDescription_step_write_true
    (left : List (Option Bool)) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    pullNearestRawBitToTailMarkerDescription.runConfig 1
        { state := 5
          tape := tapeAtCells left (none :: some tailFirst :: tail) } =
      { state := pullNearestRawBitToTailMarkerDescription.halt
        tape := tapeAtCells (some true :: left)
          (some tailFirst :: tail) } := by
  cases tailFirst <;> cases tail <;>
    simp [pullNearestRawBitToTailMarkerDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem pullNearestRawBitToTailMarkerDescription_run_false
    (blankCount : Nat) (baseLeft : List (Option Bool))
    (tailFirst : Bool) (tail : List (Option Bool)) :
    pullNearestRawBitToTailMarkerDescription.runConfig
        (2 * (blankCount + 1) + 4)
        { state := pullNearestRawBitToTailMarkerDescription.start
          tape :=
            pullNearestRawBitToTailMarkerSourceTape
              blankCount baseLeft false tailFirst tail } =
      { state := pullNearestRawBitToTailMarkerDescription.halt
        tape :=
          pullNearestRawBitToTailMarkerTargetTape
            blankCount baseLeft false tailFirst tail } := by
  rw [show 2 * (blankCount + 1) + 4 =
    1 + ((blankCount + 1) + (1 + ((blankCount + 1) + (1 + 1)))) by
      lia]
  rw [runConfig_add]
  change
    pullNearestRawBitToTailMarkerDescription.runConfig
        ((blankCount + 1) + (1 + ((blankCount + 1) + (1 + 1))))
        (pullNearestRawBitToTailMarkerDescription.runConfig 1
          { state := pullNearestRawBitToTailMarkerDescription.start
            tape :=
              tapeAtCells
                (List.append
                  (List.replicate (blankCount + 1)
                    (none : Option Bool))
                  (some false :: baseLeft))
                (some tailFirst :: tail) }) =
      { state := pullNearestRawBitToTailMarkerDescription.halt
        tape :=
          pullNearestRawBitToTailMarkerTargetTape
            blankCount baseLeft false tailFirst tail }
  rw [show
      List.replicate (blankCount + 1) (none : Option Bool) =
        none :: List.replicate blankCount none by
    rw [show blankCount + 1 = Nat.succ blankCount by lia]
    rfl]
  rw [show
      List.append
          (none :: List.replicate blankCount (none : Option Bool))
          (some false :: baseLeft) =
        none ::
          List.append (List.replicate blankCount none)
            (some false :: baseLeft) by
    rfl]
  rw [pullNearestRawBitToTailMarkerDescription_step_start]
  rw [runConfig_add]
  rw [pullNearestRawBitToTailMarkerDescription_run_scan_blanks]
  rw [runConfig_add]
  rw [pullNearestRawBitToTailMarkerDescription_step_raw_false]
  rw [runConfig_add]
  rw [pullNearestRawBitToTailMarkerDescription_run_return_blanks_false]
  rw [runConfig_add]
  rw [show
      List.replicate (blankCount + 1) (none : Option Bool) =
        none :: List.replicate blankCount none by
    rw [show blankCount + 1 = Nat.succ blankCount by lia]
    rfl]
  rw [show
      List.append
          (none :: List.replicate blankCount (none : Option Bool))
          (none :: baseLeft) =
        none ::
          List.append (List.replicate blankCount none)
            (none :: baseLeft) by
    rfl]
  rw [pullNearestRawBitToTailMarkerDescription_step_tail_false]
  rw [pullNearestRawBitToTailMarkerDescription_step_write_false]
  rw [replicate_none_append_cons_eq]
  simp [pullNearestRawBitToTailMarkerTargetTape]

theorem pullNearestRawBitToTailMarkerDescription_run_true
    (blankCount : Nat) (baseLeft : List (Option Bool))
    (tailFirst : Bool) (tail : List (Option Bool)) :
    pullNearestRawBitToTailMarkerDescription.runConfig
        (2 * (blankCount + 1) + 4)
        { state := pullNearestRawBitToTailMarkerDescription.start
          tape :=
            pullNearestRawBitToTailMarkerSourceTape
              blankCount baseLeft true tailFirst tail } =
      { state := pullNearestRawBitToTailMarkerDescription.halt
        tape :=
          pullNearestRawBitToTailMarkerTargetTape
            blankCount baseLeft true tailFirst tail } := by
  rw [show 2 * (blankCount + 1) + 4 =
    1 + ((blankCount + 1) + (1 + ((blankCount + 1) + (1 + 1)))) by
      lia]
  rw [runConfig_add]
  change
    pullNearestRawBitToTailMarkerDescription.runConfig
        ((blankCount + 1) + (1 + ((blankCount + 1) + (1 + 1))))
        (pullNearestRawBitToTailMarkerDescription.runConfig 1
          { state := pullNearestRawBitToTailMarkerDescription.start
            tape :=
              tapeAtCells
                (List.append
                  (List.replicate (blankCount + 1)
                    (none : Option Bool))
                  (some true :: baseLeft))
                (some tailFirst :: tail) }) =
      { state := pullNearestRawBitToTailMarkerDescription.halt
        tape :=
          pullNearestRawBitToTailMarkerTargetTape
            blankCount baseLeft true tailFirst tail }
  rw [show
      List.replicate (blankCount + 1) (none : Option Bool) =
        none :: List.replicate blankCount none by
    rw [show blankCount + 1 = Nat.succ blankCount by lia]
    rfl]
  rw [show
      List.append
          (none :: List.replicate blankCount (none : Option Bool))
          (some true :: baseLeft) =
        none ::
          List.append (List.replicate blankCount none)
            (some true :: baseLeft) by
    rfl]
  rw [pullNearestRawBitToTailMarkerDescription_step_start]
  rw [runConfig_add]
  rw [pullNearestRawBitToTailMarkerDescription_run_scan_blanks]
  rw [runConfig_add]
  rw [pullNearestRawBitToTailMarkerDescription_step_raw_true]
  rw [runConfig_add]
  rw [pullNearestRawBitToTailMarkerDescription_run_return_blanks_true]
  rw [runConfig_add]
  rw [show
      List.replicate (blankCount + 1) (none : Option Bool) =
        none :: List.replicate blankCount none by
    rw [show blankCount + 1 = Nat.succ blankCount by lia]
    rfl]
  rw [show
      List.append
          (none :: List.replicate blankCount (none : Option Bool))
          (none :: baseLeft) =
        none ::
          List.append (List.replicate blankCount none)
            (none :: baseLeft) by
    rfl]
  rw [pullNearestRawBitToTailMarkerDescription_step_tail_true]
  rw [pullNearestRawBitToTailMarkerDescription_step_write_true]
  rw [replicate_none_append_cons_eq]
  simp [pullNearestRawBitToTailMarkerTargetTape]

theorem pullNearestRawBitToTailMarkerDescription_haltsFromTape
    (blankCount : Nat) (baseLeft : List (Option Bool))
    (rawBit tailFirst : Bool) (tail : List (Option Bool)) :
    pullNearestRawBitToTailMarkerDescription.HaltsFromTape
      (pullNearestRawBitToTailMarkerSourceTape
        blankCount baseLeft rawBit tailFirst tail)
      (pullNearestRawBitToTailMarkerTargetTape
        blankCount baseLeft rawBit tailFirst tail) := by
  cases rawBit
  · refine ⟨2 * (blankCount + 1) + 4, ?_⟩
    constructor <;>
      rw [pullNearestRawBitToTailMarkerDescription_run_false]
  · refine ⟨2 * (blankCount + 1) + 4, ?_⟩
    constructor <;>
      rw [pullNearestRawBitToTailMarkerDescription_run_true]

theorem pullNearestRawBitToTailMarkerDescription_run_headGapZero_false
    (baseLeft : List (Option Bool))
    (headBit : Bool) (right : List (Option Bool)) :
    pullNearestRawBitToTailMarkerDescription.runConfig 4
        { state := pullNearestRawBitToTailMarkerDescription.start
          tape :=
            pullNearestRawBitToHeadMarkerSourceTape
              0 baseLeft false headBit right } =
      { state := pullNearestRawBitToTailMarkerDescription.halt
        tape :=
          pullNearestRawBitToHeadMarkerTargetTape
            0 baseLeft false headBit right } := by
  rw [show 4 = 1 + (1 + (1 + 1)) by decide]
  rw [runConfig_add]
  rw [pullNearestRawBitToHeadMarkerSourceTape]
  change
    pullNearestRawBitToTailMarkerDescription.runConfig (1 + (1 + 1))
      (pullNearestRawBitToTailMarkerDescription.runConfig 1
        { state := pullNearestRawBitToTailMarkerDescription.start
          tape := tapeAtCells (some false :: baseLeft)
            (some headBit :: right) }) =
      { state := pullNearestRawBitToTailMarkerDescription.halt
        tape :=
          pullNearestRawBitToHeadMarkerTargetTape
            0 baseLeft false headBit right }
  rw [pullNearestRawBitToTailMarkerDescription_step_start_adjacent]
  rw [runConfig_add]
  rw [pullNearestRawBitToTailMarkerDescription_step_raw_false]
  rw [runConfig_add]
  rw [pullNearestRawBitToTailMarkerDescription_step_tail_false]
  rw [pullNearestRawBitToTailMarkerDescription_step_write_false]
  simp [pullNearestRawBitToHeadMarkerTargetTape]

theorem pullNearestRawBitToTailMarkerDescription_run_headGapZero_true
    (baseLeft : List (Option Bool))
    (headBit : Bool) (right : List (Option Bool)) :
    pullNearestRawBitToTailMarkerDescription.runConfig 4
        { state := pullNearestRawBitToTailMarkerDescription.start
          tape :=
            pullNearestRawBitToHeadMarkerSourceTape
              0 baseLeft true headBit right } =
      { state := pullNearestRawBitToTailMarkerDescription.halt
        tape :=
          pullNearestRawBitToHeadMarkerTargetTape
            0 baseLeft true headBit right } := by
  rw [show 4 = 1 + (1 + (1 + 1)) by decide]
  rw [runConfig_add]
  rw [pullNearestRawBitToHeadMarkerSourceTape]
  change
    pullNearestRawBitToTailMarkerDescription.runConfig (1 + (1 + 1))
      (pullNearestRawBitToTailMarkerDescription.runConfig 1
        { state := pullNearestRawBitToTailMarkerDescription.start
          tape := tapeAtCells (some true :: baseLeft)
            (some headBit :: right) }) =
      { state := pullNearestRawBitToTailMarkerDescription.halt
        tape :=
          pullNearestRawBitToHeadMarkerTargetTape
            0 baseLeft true headBit right }
  rw [pullNearestRawBitToTailMarkerDescription_step_start_adjacent]
  rw [runConfig_add]
  rw [pullNearestRawBitToTailMarkerDescription_step_raw_true]
  rw [runConfig_add]
  rw [pullNearestRawBitToTailMarkerDescription_step_tail_true]
  rw [pullNearestRawBitToTailMarkerDescription_step_write_true]
  simp [pullNearestRawBitToHeadMarkerTargetTape]

theorem pullNearestRawBitToTailMarkerDescription_haltsFromHeadGap
    (gap : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool) (right : List (Option Bool)) :
    pullNearestRawBitToTailMarkerDescription.HaltsFromTape
      (pullNearestRawBitToHeadMarkerSourceTape
        gap baseLeft rawBit headBit right)
      (pullNearestRawBitToHeadMarkerTargetTape
        gap baseLeft rawBit headBit right) := by
  cases gap with
  | zero =>
      cases rawBit
      · refine ⟨4, ?_⟩
        constructor <;>
          rw [pullNearestRawBitToTailMarkerDescription_run_headGapZero_false]
      · refine ⟨4, ?_⟩
        constructor <;>
          rw [pullNearestRawBitToTailMarkerDescription_run_headGapZero_true]
  | succ blankCount =>
      simpa [pullNearestRawBitToHeadMarkerSourceTape,
        pullNearestRawBitToHeadMarkerTargetTape,
        pullNearestRawBitToTailMarkerSourceTape,
        pullNearestRawBitToTailMarkerTargetTape] using
        pullNearestRawBitToTailMarkerDescription_haltsFromTape
          blankCount baseLeft rawBit headBit right

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
