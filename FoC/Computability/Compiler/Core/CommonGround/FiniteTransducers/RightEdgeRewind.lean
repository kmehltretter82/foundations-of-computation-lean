import FoC.Computability.TapeLemmas
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StatefulOptionAppend
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredLowering

set_option doc.verso true

/-!
# Right-edge rewind adapter

This module factors out the common finite-machine pattern that starts at the
right edge of an emitted Boolean word, rewinds left to the blank before the
word, and halts on the first output cell with the left boundary blank preserved.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

def leftMoveOnceDescription : MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ transition 0 none none Direction.left 1
    , transition 0 (some false) (some false) Direction.left 1
    , transition 0 (some true) (some true) Direction.left 1 ]

theorem leftMoveOnceDescription_wellFormed :
    leftMoveOnceDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := leftMoveOnceDescription.transitions)
      (stateCount := leftMoveOnceDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := leftMoveOnceDescription.transitions)
      (by decide)

theorem leftMoveOnceDescription_haltTransitionFree :
    leftMoveOnceDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := leftMoveOnceDescription.transitions)
    (state := leftMoveOnceDescription.halt)
    (by decide)

theorem leftMoveOnceDescription_subroutineReady :
    leftMoveOnceDescription.SubroutineReady :=
  ⟨leftMoveOnceDescription_wellFormed,
    leftMoveOnceDescription_haltTransitionFree⟩

theorem leftMoveOnceDescription_run
    (T : Tape Bool) :
    leftMoveOnceDescription.runConfig 1
        { state := leftMoveOnceDescription.start
          tape := T } =
      { state := leftMoveOnceDescription.halt
        tape := Tape.move Direction.left T } := by
  cases T with
  | mk left head right =>
      cases head with
      | none =>
          simp [leftMoveOnceDescription, runConfig, stepConfig,
            lookupTransition, Matches, transition, Tape.read, Tape.write]
      | some bit =>
          cases bit <;>
            simp [leftMoveOnceDescription, runConfig, stepConfig,
              lookupTransition, Matches, transition, Tape.read, Tape.write]

theorem leftMoveOnceDescription_haltsFromTape
    (T : Tape Bool) :
    leftMoveOnceDescription.HaltsFromTape T
      (Tape.move Direction.left T) := by
  refine ⟨1, ?_⟩
  constructor <;>
    rw [leftMoveOnceDescription_run]

/--
Structured source for {lit}`rightEdgeScanDescription`.  The lowered machine
keeps scanning right over Boolean cells, then backs up one cell when it sees the
right-edge blank.
-/
def structuredRightEdgeScanDescription : Structured.Description where
  tapeCount := 1
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ Structured.OneTape.preserve 0 (some false)
        Structured.HeadMove.right 0
    , Structured.OneTape.preserve 0 (some true)
        Structured.HeadMove.right 0
    , Structured.OneTape.preserve 0 none
        Structured.HeadMove.left 1 ]

def rightEdgeScanDescription : MachineDescription :=
  Structured.Lowering.toMachineDescription
    structuredRightEdgeScanDescription

def rightEdgeScanSourceTapeFromLeft
    (left : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells left (List.append (bits.map some) (none :: padding))

def rightEdgeScanTargetTapeFromLeft
    (left : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) : Tape Bool :=
  Tape.move Direction.left
    (tapeAtCells
      (List.append (bits.reverse.map some) left)
      (none :: padding))

private theorem structuredRightEdgeScanDescription_step_bit
    (left right : List (Option Bool)) (bit : Bool) :
    structuredRightEdgeScanDescription.runConfig 1
        { state := structuredRightEdgeScanDescription.start
          tapes := [tapeAtCells left (some bit :: right)] } =
      { state := structuredRightEdgeScanDescription.start
        tapes := [tapeAtCells (some bit :: left) right] } := by
  cases bit <;> cases right <;>
    simp [structuredRightEdgeScanDescription,
      Structured.Description.runConfig,
      Structured.Description.stepConfig,
      Structured.Description.lookupTransition,
      Structured.Description.Matches,
      Structured.TapeAction.apply,
      Structured.HeadMove.apply,
      tapeAtCells, Tape.read, Tape.move, Tape.moveRight]

private theorem structuredRightEdgeScanDescription_step_finish
    (left padding : List (Option Bool)) :
    structuredRightEdgeScanDescription.runConfig 1
        { state := structuredRightEdgeScanDescription.start
          tapes := [tapeAtCells left (none :: padding)] } =
      { state := structuredRightEdgeScanDescription.halt
        tapes :=
          [Tape.move Direction.left
            (tapeAtCells left (none :: padding))] } := by
  cases left <;> cases padding <;>
    simp [structuredRightEdgeScanDescription,
      Structured.Description.runConfig,
      Structured.Description.stepConfig,
      Structured.Description.lookupTransition,
      Structured.Description.Matches,
      Structured.TapeAction.apply,
      Structured.HeadMove.apply,
      tapeAtCells, Tape.read, Tape.move, Tape.moveLeft]

private theorem structuredRightEdgeScanDescription_run_scan
    (bits : Word Bool) (left padding : List (Option Bool)) :
    structuredRightEdgeScanDescription.runConfig bits.length
        { state := structuredRightEdgeScanDescription.start
          tapes :=
            [tapeAtCells left
              (List.append (bits.map some) (none :: padding))] } =
      { state := structuredRightEdgeScanDescription.start
        tapes :=
          [tapeAtCells
            (List.append (bits.reverse.map some) left)
            (none :: padding)] } := by
  induction bits generalizing left with
  | nil =>
      simp [Structured.Description.runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        lia]
      rw [Structured.Description.runConfig_add]
      change
        structuredRightEdgeScanDescription.runConfig rest.length
            (structuredRightEdgeScanDescription.runConfig 1
              { state := structuredRightEdgeScanDescription.start
                tapes :=
                  [tapeAtCells left
                    (some bit ::
                      List.append (rest.map some)
                        (none :: padding))] }) =
          { state := structuredRightEdgeScanDescription.start
            tapes :=
              [tapeAtCells
                (List.append ((bit :: rest).reverse.map some) left)
                (none :: padding)] }
      rw [structuredRightEdgeScanDescription_step_bit left
        (List.append (rest.map some) (none :: padding)) bit]
      simpa [List.reverse_cons, List.map_append,
        List.append_assoc] using ih (some bit :: left)

private theorem structuredRightEdgeScanDescription_run_to_target
    (left : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    structuredRightEdgeScanDescription.runConfig (bits.length + 1)
        { state := structuredRightEdgeScanDescription.start
          tapes :=
            [rightEdgeScanSourceTapeFromLeft left bits padding] } =
      { state := structuredRightEdgeScanDescription.halt
        tapes :=
          [rightEdgeScanTargetTapeFromLeft left bits padding] } := by
  rw [rightEdgeScanSourceTapeFromLeft,
    rightEdgeScanTargetTapeFromLeft]
  rw [Structured.Description.runConfig_add]
  rw [structuredRightEdgeScanDescription_run_scan]
  rw [structuredRightEdgeScanDescription_step_finish]

/--
For a nonempty scanned word, the source shape of
{name}`rightEdgeScanDescription` is stable under the right-then-left bridge
used by sequential machine composition.
-/
theorem rightEdgeScanSourceTapeFromLeft_move_left_move_right_cons
    (left padding : List (Option Bool)) (current : Bool)
    (rest : Word Bool) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (rightEdgeScanSourceTapeFromLeft left (current :: rest)
            padding)) =
      rightEdgeScanSourceTapeFromLeft left (current :: rest) padding := by
  cases current <;> cases rest <;> cases padding <;>
    simp [rightEdgeScanSourceTapeFromLeft, tapeAtCells, Tape.move,
      Tape.moveLeft, Tape.moveRight]

/--
The source shape of {name}`rightEdgeScanDescription` is stable under the
right-then-left bridge whenever the visible padding has a first cell.
-/
theorem rightEdgeScanSourceTapeFromLeft_move_left_move_right_padding_cons
    (left : List (Option Bool)) (bits : Word Bool)
    (pad : Option Bool) (padding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (rightEdgeScanSourceTapeFromLeft left bits (pad :: padding))) =
      rightEdgeScanSourceTapeFromLeft left bits (pad :: padding) := by
  cases bits with
  | nil =>
      cases left <;> cases pad <;> cases padding <;>
        simp [rightEdgeScanSourceTapeFromLeft, tapeAtCells,
          Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons current rest =>
      exact
        rightEdgeScanSourceTapeFromLeft_move_left_move_right_cons
          left (pad :: padding) current rest

/--
The target shape of {name}`rightEdgeScanDescription` is stable under the
right-then-left bridge inserted before a following subroutine.
-/
theorem rightEdgeScanTargetTapeFromLeft_move_left_move_right
    (left : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (rightEdgeScanTargetTapeFromLeft left bits padding)) =
      rightEdgeScanTargetTapeFromLeft left bits padding := by
  unfold rightEdgeScanTargetTapeFromLeft
  cases hleft : List.append (bits.reverse.map some) left with
  | nil =>
      cases padding <;>
        simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons cell rest =>
      cases padding <;>
        simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

private theorem rightEdgeScanDescription_wellFormed :
    rightEdgeScanDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := rightEdgeScanDescription.transitions)
      (stateCount := rightEdgeScanDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := rightEdgeScanDescription.transitions)
      (by decide)

private theorem rightEdgeScanDescription_haltTransitionFree :
    rightEdgeScanDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := rightEdgeScanDescription.transitions)
    (state := rightEdgeScanDescription.halt)
    (by decide)

theorem rightEdgeScanDescription_subroutineReady :
    rightEdgeScanDescription.SubroutineReady :=
  ⟨rightEdgeScanDescription_wellFormed,
    rightEdgeScanDescription_haltTransitionFree⟩

private theorem rightEdgeScanDescription_step_bit
    (left right : List (Option Bool)) (bit : Bool) :
    rightEdgeScanDescription.runConfig 1
        { state := rightEdgeScanDescription.start
          tape := tapeAtCells left (some bit :: right) } =
      { state := rightEdgeScanDescription.start
        tape := tapeAtCells (some bit :: left) right } := by
  cases bit <;> cases right <;>
    simp [rightEdgeScanDescription, structuredRightEdgeScanDescription,
      tapeAtCells, runConfig,
      stepConfig, lookupTransition, Matches, Tape.read,
      Tape.write, Tape.move, Tape.moveRight]

private theorem rightEdgeScanDescription_step_finish
    (left padding : List (Option Bool)) :
    rightEdgeScanDescription.runConfig 1
        { state := rightEdgeScanDescription.start
          tape := tapeAtCells left (none :: padding) } =
      { state := rightEdgeScanDescription.halt
        tape :=
          Tape.move Direction.left
            (tapeAtCells left (none :: padding)) } := by
  cases left <;> cases padding <;>
    simp [rightEdgeScanDescription, structuredRightEdgeScanDescription,
      tapeAtCells, runConfig,
      stepConfig, lookupTransition, Matches, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft]

private theorem rightEdgeScanDescription_run_scan
    (bits : Word Bool) (left padding : List (Option Bool)) :
    rightEdgeScanDescription.runConfig bits.length
        { state := rightEdgeScanDescription.start
          tape :=
            tapeAtCells left
              (List.append (bits.map some) (none :: padding)) } =
      { state := rightEdgeScanDescription.start
        tape :=
          tapeAtCells
            (List.append (bits.reverse.map some) left)
            (none :: padding) } := by
  induction bits generalizing left with
  | nil =>
      simp [runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        lia]
      rw [runConfig_add]
      change
        rightEdgeScanDescription.runConfig rest.length
            (rightEdgeScanDescription.runConfig 1
              { state := rightEdgeScanDescription.start
                tape :=
                  tapeAtCells left
                    (some bit ::
                      List.append (rest.map some)
                        (none :: padding)) }) =
          { state := rightEdgeScanDescription.start
            tape :=
              tapeAtCells
                (List.append ((bit :: rest).reverse.map some) left)
                (none :: padding) }
      rw [rightEdgeScanDescription_step_bit left
        (List.append (rest.map some) (none :: padding)) bit]
      simpa [List.reverse_cons, List.map_append,
        List.append_assoc] using ih (some bit :: left)

private theorem rightEdgeScanDescription_run_to_target
    (left : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    rightEdgeScanDescription.runConfig (bits.length + 1)
        { state := rightEdgeScanDescription.start
          tape :=
            rightEdgeScanSourceTapeFromLeft left bits padding } =
      { state := rightEdgeScanDescription.halt
        tape :=
          rightEdgeScanTargetTapeFromLeft left bits padding } := by
  rw [rightEdgeScanSourceTapeFromLeft,
    rightEdgeScanTargetTapeFromLeft]
  rw [runConfig_add]
  rw [rightEdgeScanDescription_run_scan]
  rw [rightEdgeScanDescription_step_finish]

theorem rightEdgeScanDescription_haltsFromTape
    (left : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    rightEdgeScanDescription.HaltsFromTape
      (rightEdgeScanSourceTapeFromLeft left bits padding)
      (rightEdgeScanTargetTapeFromLeft left bits padding) := by
  refine ⟨bits.length + 1, ?_⟩
  constructor <;>
    rw [rightEdgeScanDescription_run_to_target]

def rightEdgeRewindDescription : MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ transition 0 none none Direction.left 1
    , transition 0 (some false) (some false) Direction.left 1
    , transition 0 (some true) (some true) Direction.left 1
    , transition 1 (some false) (some false) Direction.left 1
    , transition 1 (some true) (some true) Direction.left 1
    , transition 1 none none Direction.right 2 ]

def rightEdgeRewindSourceTape
    (bits : Word Bool) (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells (bits.reverse.map some) (none :: padding)

def rightEdgeRewindTargetTape
    (bits : Word Bool) (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells [none] (List.append (bits.map some) (none :: padding))

theorem rightEdgeRewindTargetTape_cells
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.cells (rightEdgeRewindTargetTape bits padding) =
      none ::
        List.append (bits.map some) (none :: padding) := by
  cases bits <;>
    simp [rightEdgeRewindTargetTape, tapeAtCells, Tape.cells]

theorem rightEdgeRewindTargetTape_normalizedOutput
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (rightEdgeRewindTargetTape bits padding) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [Tape.normalizedOutput, rightEdgeRewindTargetTape_cells]
  simp [Function.comp_def, List.filterMap_append]

private theorem rightEdgeRewindTargetTape_equiv_paddedInput
    (bits : Word Bool) (padding : Nat) :
    Tape.Equiv
      (rightEdgeRewindTargetTape bits
        (List.replicate padding (none : Option Bool)))
      (inputWithTrailingBlankPadding bits (padding + 1)) := by
  cases bits with
  | nil =>
      simp [rightEdgeRewindTargetTape, inputWithTrailingBlankPadding,
        tapeAtCells, Tape.Equiv, Tape.dropTrailingNone,
        FoC.Computability.dropTrailingNone_replicate_none]
  | cons bit rest =>
      constructor
      · simp [rightEdgeRewindTargetTape, inputWithTrailingBlankPadding,
          tapeAtCells, Tape.dropTrailingNone]
      · constructor
        · rfl
        · change
            Tape.dropTrailingNone
                (List.append (rest.map some)
                  (none :: List.replicate padding (none : Option Bool))) =
              Tape.dropTrailingNone
                (List.append (rest.map some)
                  (List.replicate (padding + 1) (none : Option Bool)))
          simp [List.replicate_succ]

theorem rightEdgeRewindTargetTape_moveRight_equiv_FSTTargetTape
    (bits : Word Bool) (padding : Nat) :
    Tape.Equiv
      (Tape.move Direction.right
        (rightEdgeRewindTargetTape bits
          (List.replicate padding (none : Option Bool))))
      (FSTTargetTape bits (padding + 1)) := by
  simpa [FSTTargetTape] using
    Tape.Equiv.move
      (rightEdgeRewindTargetTape_equiv_paddedInput bits padding)
      Direction.right

private theorem rightEdgeRewindDescription_wellFormed :
    rightEdgeRewindDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := rightEdgeRewindDescription.transitions)
      (stateCount := rightEdgeRewindDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := rightEdgeRewindDescription.transitions)
      (by decide)

private theorem rightEdgeRewindDescription_haltTransitionFree :
    rightEdgeRewindDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := rightEdgeRewindDescription.transitions)
    (state := rightEdgeRewindDescription.halt)
    (by decide)

theorem rightEdgeRewindDescription_subroutineReady :
    rightEdgeRewindDescription.SubroutineReady :=
  ⟨rightEdgeRewindDescription_wellFormed,
    rightEdgeRewindDescription_haltTransitionFree⟩

private theorem rightEdgeRewindDescription_run_scan
    (leftBits : Word Bool) (current : Bool)
    (rightCells : List (Option Bool)) :
    rightEdgeRewindDescription.runConfig (leftBits.length + 1)
        { state := 1
          tape :=
            tapeAtCells
              (leftBits.map some)
              (some current :: rightCells) } =
      { state := 1
        tape :=
          tapeAtCells []
            (none ::
              List.append
                ((List.append leftBits.reverse [current]).map some)
                rightCells) } := by
  induction leftBits generalizing current rightCells with
  | nil =>
      cases current <;>
        simp [rightEdgeRewindDescription, tapeAtCells, runConfig,
          stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.move, Tape.moveLeft, Tape.write]
  | cons next rest ih =>
      rw [show (next :: rest).length + 1 = 1 + (rest.length + 1) by
        simp
        lia]
      rw [runConfig_add]
      have hstep :
          rightEdgeRewindDescription.runConfig 1
              { state := 1
                tape :=
                  tapeAtCells
                    ((next :: rest).map some)
                    (some current :: rightCells) } =
            { state := 1
              tape :=
                tapeAtCells
                  (rest.map some)
                  (some next :: some current :: rightCells) } := by
        cases current <;>
          simp [rightEdgeRewindDescription, tapeAtCells, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.move, Tape.moveLeft, Tape.write]
      rw [hstep]
      simpa [List.append_assoc] using
        ih next (some current :: rightCells)

private theorem rightEdgeRewindDescription_run_scan_withBoundary
    (leftBits : Word Bool) (current : Bool)
    (rightCells : List (Option Bool)) :
    rightEdgeRewindDescription.runConfig (leftBits.length + 1)
        { state := 1
          tape :=
            tapeAtCells
              (List.append (leftBits.map some) [none])
              (some current :: rightCells) } =
      { state := 1
        tape :=
          tapeAtCells []
            (none ::
              List.append
                ((List.append leftBits.reverse [current]).map some)
                rightCells) } := by
  induction leftBits generalizing current rightCells with
  | nil =>
      cases current <;>
        simp [rightEdgeRewindDescription, tapeAtCells, runConfig,
          stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.move, Tape.moveLeft, Tape.write]
  | cons next rest ih =>
      rw [show (next :: rest).length + 1 = 1 + (rest.length + 1) by
        simp
        lia]
      rw [runConfig_add]
      have hstep :
          rightEdgeRewindDescription.runConfig 1
              { state := 1
                tape :=
                  tapeAtCells
                    (List.append ((next :: rest).map some) [none])
                    (some current :: rightCells) } =
            { state := 1
              tape :=
                tapeAtCells
                  (List.append (rest.map some) [none])
                  (some next :: some current :: rightCells) } := by
        cases current <;> cases next <;>
          simp [rightEdgeRewindDescription, tapeAtCells, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.move, Tape.moveLeft, Tape.write]
      rw [hstep]
      simpa [List.append_assoc] using
        ih next (some current :: rightCells)

private theorem rightEdgeRewindDescription_step_finish
    (bits : Word Bool) (padding : List (Option Bool)) :
    rightEdgeRewindDescription.runConfig 1
        { state := 1
          tape :=
            tapeAtCells []
              (none ::
                List.append (bits.map some) (none :: padding)) } =
      { state := rightEdgeRewindDescription.halt
        tape := rightEdgeRewindTargetTape bits padding } := by
  cases bits with
  | nil =>
      simp [rightEdgeRewindDescription, rightEdgeRewindTargetTape,
        tapeAtCells, runConfig, stepConfig, lookupTransition,
        Matches, transition, Tape.read, Tape.move, Tape.moveRight,
        Tape.write]
  | cons bit rest =>
      cases bit <;>
        simp [rightEdgeRewindDescription, rightEdgeRewindTargetTape,
          tapeAtCells, runConfig, stepConfig, lookupTransition,
          Matches, transition, Tape.read, Tape.move, Tape.moveRight,
          Tape.write]

private theorem rightEdgeRewindDescription_step_finish_noDelimiter
    (baseLeft : List (Option Bool))
    (bits : Word Bool) (right : List (Option Bool)) :
    rightEdgeRewindDescription.runConfig 1
        { state := 1
          tape :=
            tapeAtCells baseLeft
              (none :: List.append (bits.map some) right) } =
      { state := rightEdgeRewindDescription.halt
        tape :=
          tapeAtCells (none :: baseLeft)
            (List.append (bits.map some) right) } := by
  cases bits <;> cases right <;> cases baseLeft <;>
    simp [rightEdgeRewindDescription, tapeAtCells, runConfig,
      stepConfig, lookupTransition, Matches, transition, Tape.read,
      Tape.move, Tape.moveRight, Tape.write]

private theorem rightEdgeRewindDescription_run_scan_withBoundaryBase_core
    (baseLeft : List (Option Bool))
    (leftBits : Word Bool) (current : Bool)
    (rightCells : List (Option Bool)) :
    rightEdgeRewindDescription.runConfig (leftBits.length + 1)
        { state := 1
          tape :=
            tapeAtCells
              (List.append (leftBits.map some) (none :: baseLeft))
              (some current :: rightCells) } =
      { state := 1
        tape :=
          tapeAtCells baseLeft
            (none ::
              List.append
                ((List.append leftBits.reverse [current]).map some)
                rightCells) } := by
  induction leftBits generalizing current rightCells with
  | nil =>
      cases current <;> cases baseLeft <;> cases rightCells <;>
        simp [rightEdgeRewindDescription, tapeAtCells, runConfig,
          stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.move, Tape.moveLeft, Tape.write]
  | cons next rest ih =>
      rw [show (next :: rest).length + 1 =
        1 + (rest.length + 1) by
        simp
        lia]
      rw [runConfig_add]
      have hstep :
          rightEdgeRewindDescription.runConfig 1
              { state := 1
                tape :=
                  tapeAtCells
                    (List.append ((next :: rest).map some)
                      (none :: baseLeft))
                    (some current :: rightCells) } =
            { state := 1
              tape :=
                tapeAtCells
                  (List.append (rest.map some) (none :: baseLeft))
                  (some next :: some current :: rightCells) } := by
        cases current <;> cases next <;>
          simp [rightEdgeRewindDescription, tapeAtCells, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.move, Tape.moveLeft, Tape.write]
      rw [hstep]
      simpa [List.append_assoc] using
        ih next (some current :: rightCells)

private theorem rightEdgeRewindDescription_run_from_leftStack
    (leftStack : Word Bool) (padding : List (Option Bool)) :
    rightEdgeRewindDescription.runConfig (leftStack.length + 2)
        { state := rightEdgeRewindDescription.start
          tape := tapeAtCells (leftStack.map some) (none :: padding) } =
      { state := rightEdgeRewindDescription.halt
        tape :=
          tapeAtCells [none]
            (List.append (leftStack.reverse.map some) (none :: padding)) } := by
  cases leftStack with
  | nil =>
      simp [rightEdgeRewindDescription, tapeAtCells, runConfig,
        stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.move, Tape.moveLeft, Tape.moveRight,
        Tape.write]
  | cons current rest =>
      rw [show (current :: rest).length + 2 =
        1 + ((rest.length + 1) + 1) by
        simp
        lia]
      rw [runConfig_add]
      have hstart :
          rightEdgeRewindDescription.runConfig 1
              { state := rightEdgeRewindDescription.start
                tape :=
                  tapeAtCells
                    ((current :: rest).map some)
                    (none :: padding) } =
            { state := 1
              tape :=
                tapeAtCells
                  (rest.map some)
                  (some current :: none :: padding) } := by
        cases current <;>
          simp [rightEdgeRewindDescription, tapeAtCells, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.move, Tape.moveLeft, Tape.write]
      rw [hstart]
      rw [show (rest.length + 1) + 1 = (rest.length + 1) + 1 by rfl]
      rw [runConfig_add]
      rw [rightEdgeRewindDescription_run_scan rest current
        (none :: padding)]
      simpa [rightEdgeRewindTargetTape, List.map_append,
        List.append_assoc] using
        rightEdgeRewindDescription_step_finish
          (List.append rest.reverse [current]) padding

private theorem rightEdgeRewindDescription_run_from_leftStack_noDelimiter
    (leftStack : Word Bool) (rightHead : Bool)
    (rightTail : List (Option Bool)) :
    rightEdgeRewindDescription.runConfig (leftStack.length + 2)
        { state := rightEdgeRewindDescription.start
          tape :=
            tapeAtCells (leftStack.map some)
              (some rightHead :: rightTail) } =
      { state := rightEdgeRewindDescription.halt
        tape :=
          tapeAtCells [none]
            (List.append (leftStack.reverse.map some)
              (some rightHead :: rightTail)) } := by
  cases leftStack with
  | nil =>
      cases rightHead <;> cases rightTail <;>
        simp [rightEdgeRewindDescription, tapeAtCells, runConfig,
          stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.move, Tape.moveLeft, Tape.moveRight,
          Tape.write]
  | cons current rest =>
      rw [show (current :: rest).length + 2 =
        1 + ((rest.length + 1) + 1) by
        simp
        lia]
      rw [runConfig_add]
      have hstart :
          rightEdgeRewindDescription.runConfig 1
              { state := rightEdgeRewindDescription.start
                tape :=
                  tapeAtCells ((current :: rest).map some)
                    (some rightHead :: rightTail) } =
            { state := 1
              tape :=
                tapeAtCells (rest.map some)
                  (some current :: some rightHead :: rightTail) } := by
        cases current <;> cases rightHead <;> cases rightTail <;>
          simp [rightEdgeRewindDescription, tapeAtCells, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.move, Tape.moveLeft, Tape.write]
      rw [hstart]
      rw [show (rest.length + 1) + 1 = (rest.length + 1) + 1 by rfl]
      rw [runConfig_add]
      rw [rightEdgeRewindDescription_run_scan rest current
        (some rightHead :: rightTail)]
      simpa [List.map_append, List.append_assoc] using
        rightEdgeRewindDescription_step_finish_noDelimiter []
          (List.append rest.reverse [current])
          (some rightHead :: rightTail)

private theorem rightEdgeRewindDescription_haltsFrom_leftStack_noDelimiter
    (leftStack : Word Bool) (rightHead : Bool)
    (rightTail : List (Option Bool)) :
    rightEdgeRewindDescription.HaltsFromTape
      (tapeAtCells (leftStack.map some)
        (some rightHead :: rightTail))
      (tapeAtCells [none]
        (List.append (leftStack.reverse.map some)
          (some rightHead :: rightTail))) := by
  refine ⟨leftStack.length + 2, ?_⟩
  constructor <;>
    rw [rightEdgeRewindDescription_run_from_leftStack_noDelimiter]

theorem rightEdgeRewindDescription_haltsFrom_rightEdge_noDelimiter
    (bits : Word Bool) (rightHead : Bool)
    (rightTail : List (Option Bool)) :
    rightEdgeRewindDescription.HaltsFromTape
      (tapeAtCells (bits.reverse.map some)
        (some rightHead :: rightTail))
      (tapeAtCells [none]
        (List.append (bits.map some)
          (some rightHead :: rightTail))) := by
  simpa [List.map_reverse] using
    rightEdgeRewindDescription_haltsFrom_leftStack_noDelimiter
      bits.reverse rightHead rightTail

private theorem rightEdgeRewindDescription_run_from_lastBitStack
    (leftStack : Word Bool) (current : Bool)
    (padding : List (Option Bool)) :
    rightEdgeRewindDescription.runConfig (leftStack.length + 2)
        { state := rightEdgeRewindDescription.start
          tape :=
            tapeAtCells (leftStack.map some)
              (some current :: none :: padding) } =
      { state := rightEdgeRewindDescription.halt
        tape :=
          rightEdgeRewindTargetTape
            (List.append leftStack.reverse [current]) padding } := by
  cases leftStack with
  | nil =>
      cases current <;>
        simp [rightEdgeRewindDescription, rightEdgeRewindTargetTape,
          tapeAtCells, runConfig, stepConfig, lookupTransition,
          Matches, transition, Tape.read, Tape.move, Tape.moveLeft,
          Tape.moveRight, Tape.write]
  | cons next rest =>
      rw [show (next :: rest).length + 2 =
        1 + ((rest.length + 1) + 1) by
        simp
        lia]
      rw [runConfig_add]
      have hstart :
          rightEdgeRewindDescription.runConfig 1
              { state := rightEdgeRewindDescription.start
                tape :=
                  tapeAtCells
                    ((next :: rest).map some)
                    (some current :: none :: padding) } =
            { state := 1
              tape :=
                tapeAtCells
                  (rest.map some)
                  (some next :: some current :: none :: padding) } := by
        cases current <;> cases next <;>
          simp [rightEdgeRewindDescription, tapeAtCells, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.move, Tape.moveLeft, Tape.write]
      rw [hstart]
      rw [show (rest.length + 1) + 1 = (rest.length + 1) + 1 by rfl]
      rw [runConfig_add]
      rw [rightEdgeRewindDescription_run_scan rest next
        (some current :: none :: padding)]
      simpa [rightEdgeRewindTargetTape, List.map_append,
        List.append_assoc] using
        rightEdgeRewindDescription_step_finish
          (List.append (List.append rest.reverse [next]) [current])
          padding

private theorem rightEdgeRewindDescription_run_from_lastBitBoundary
    (leftStack : Word Bool) (current : Bool)
    (padding : List (Option Bool)) :
    rightEdgeRewindDescription.runConfig (leftStack.length + 2)
        { state := rightEdgeRewindDescription.start
          tape :=
            tapeAtCells
              (List.append (leftStack.map some) [none])
              (some current :: none :: padding) } =
      { state := rightEdgeRewindDescription.halt
        tape :=
          rightEdgeRewindTargetTape
            (List.append leftStack.reverse [current]) padding } := by
  cases leftStack with
  | nil =>
      cases current <;>
        simp [rightEdgeRewindDescription, rightEdgeRewindTargetTape,
          tapeAtCells, runConfig, stepConfig, lookupTransition,
          Matches, transition, Tape.read, Tape.move, Tape.moveLeft,
          Tape.moveRight, Tape.write]
  | cons next rest =>
      rw [show (next :: rest).length + 2 =
        1 + ((rest.length + 1) + 1) by
        simp
        lia]
      rw [runConfig_add]
      have hstart :
          rightEdgeRewindDescription.runConfig 1
              { state := rightEdgeRewindDescription.start
                tape :=
                  tapeAtCells
                    (List.append ((next :: rest).map some) [none])
                    (some current :: none :: padding) } =
            { state := 1
              tape :=
                tapeAtCells
                  (List.append (rest.map some) [none])
                  (some next :: some current :: none :: padding) } := by
        cases current <;> cases next <;>
          simp [rightEdgeRewindDescription, tapeAtCells, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.move, Tape.moveLeft, Tape.write]
      rw [hstart]
      rw [show (rest.length + 1) + 1 = (rest.length + 1) + 1 by rfl]
      rw [runConfig_add]
      rw [rightEdgeRewindDescription_run_scan_withBoundary rest next
        (some current :: none :: padding)]
      simpa [rightEdgeRewindTargetTape, List.map_append,
        List.append_assoc] using
        rightEdgeRewindDescription_step_finish
          (List.append (List.append rest.reverse [next]) [current])
          padding

private theorem rightEdgeRewindDescription_run_from_lastBitBoundaryBase_noDelimiter
    (baseLeft : List (Option Bool))
    (leftStack : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    rightEdgeRewindDescription.runConfig (leftStack.length + 2)
        { state := rightEdgeRewindDescription.start
          tape :=
            tapeAtCells
              (List.append (leftStack.map some) (none :: baseLeft))
              (some current :: right) } =
      { state := rightEdgeRewindDescription.halt
        tape :=
          tapeAtCells (none :: baseLeft)
            (List.append
              ((List.append leftStack.reverse [current]).map some)
              right) } := by
  cases leftStack with
  | nil =>
      cases current <;> cases baseLeft <;> cases right <;>
        simp [rightEdgeRewindDescription, tapeAtCells, runConfig,
          stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.move, Tape.moveLeft, Tape.moveRight,
          Tape.write]
  | cons next rest =>
      rw [show (next :: rest).length + 2 =
        1 + ((rest.length + 1) + 1) by
        simp
        lia]
      rw [runConfig_add]
      have hstart :
          rightEdgeRewindDescription.runConfig 1
              { state := rightEdgeRewindDescription.start
                tape :=
                  tapeAtCells
                    (List.append ((next :: rest).map some)
                      (none :: baseLeft))
                    (some current :: right) } =
            { state := 1
              tape :=
                tapeAtCells
                  (List.append (rest.map some) (none :: baseLeft))
                  (some next :: some current :: right) } := by
        cases current <;> cases next <;> cases baseLeft <;> cases right <;>
          simp [rightEdgeRewindDescription, tapeAtCells, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.move, Tape.moveLeft, Tape.write]
      rw [hstart]
      rw [show (rest.length + 1) + 1 = (rest.length + 1) + 1 by rfl]
      rw [runConfig_add]
      rw [rightEdgeRewindDescription_run_scan_withBoundaryBase_core
        baseLeft rest next (some current :: right)]
      simpa [List.map_append, List.append_assoc] using
        rightEdgeRewindDescription_step_finish_noDelimiter
          baseLeft
          (List.append (List.append rest.reverse [next]) [current])
          right

theorem rightEdgeRewindDescription_haltsFrom_lastBitBoundaryBase_noDelimiter
    (baseLeft : List (Option Bool))
    (leftStack : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    rightEdgeRewindDescription.HaltsFromTape
      (tapeAtCells
        (List.append (leftStack.map some) (none :: baseLeft))
        (some current :: right))
      (tapeAtCells (none :: baseLeft)
        (List.append
          ((List.append leftStack.reverse [current]).map some)
          right)) := by
  refine ⟨leftStack.length + 2, ?_⟩
  constructor <;>
    rw [rightEdgeRewindDescription_run_from_lastBitBoundaryBase_noDelimiter]

theorem rightEdgeRewindDescription_run_from_emptyBoundaryBase_noDelimiter
    (baseLeft right : List (Option Bool)) :
    rightEdgeRewindDescription.runConfig 2
        { state := rightEdgeRewindDescription.start
          tape := tapeAtCells (none :: baseLeft) (none :: right) } =
      { state := rightEdgeRewindDescription.halt
        tape := tapeAtCells (none :: baseLeft) (none :: right) } := by
  cases baseLeft <;> cases right <;>
    simp [rightEdgeRewindDescription, tapeAtCells, runConfig,
      stepConfig, lookupTransition, Matches, transition, Tape.read,
      Tape.move, Tape.moveLeft, Tape.moveRight, Tape.write]

theorem rightEdgeRewindDescription_haltsFrom_emptyBoundaryBase_noDelimiter
    (baseLeft right : List (Option Bool)) :
    rightEdgeRewindDescription.HaltsFromTape
      (tapeAtCells (none :: baseLeft) (none :: right))
      (tapeAtCells (none :: baseLeft) (none :: right)) := by
  refine ⟨2, ?_⟩
  constructor <;>
    rw [rightEdgeRewindDescription_run_from_emptyBoundaryBase_noDelimiter]

theorem rightEdgeRewindDescription_run_from_rightBoundaryBase_noDelimiter
    (baseLeft : List (Option Bool))
    (leftBits : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    rightEdgeRewindDescription.runConfig (leftBits.length + 3)
        { state := rightEdgeRewindDescription.start
          tape :=
            tapeAtCells
              (some current ::
                List.append (leftBits.map some) (none :: baseLeft))
              (none :: right) } =
      { state := rightEdgeRewindDescription.halt
        tape :=
          tapeAtCells (none :: baseLeft)
            (List.append
              ((List.append leftBits.reverse [current]).map some)
              (none :: right)) } := by
  rw [show leftBits.length + 3 =
      1 + ((leftBits.length + 1) + 1) by lia]
  rw [runConfig_add]
  have hstart :
      rightEdgeRewindDescription.runConfig 1
          { state := rightEdgeRewindDescription.start
            tape :=
              tapeAtCells
                (some current ::
                  List.append (leftBits.map some) (none :: baseLeft))
                (none :: right) } =
        { state := 1
          tape :=
            tapeAtCells
              (List.append (leftBits.map some) (none :: baseLeft))
              (some current :: none :: right) } := by
    cases current <;>
      simp [rightEdgeRewindDescription, tapeAtCells, runConfig,
        stepConfig, lookupTransition, Matches, transition, Tape.read,
        Tape.move, Tape.moveLeft, Tape.write]
  rw [hstart]
  rw [runConfig_add]
  rw [rightEdgeRewindDescription_run_scan_withBoundaryBase_core
    baseLeft leftBits current (none :: right)]
  simpa [List.append_assoc] using
    rightEdgeRewindDescription_step_finish_noDelimiter
      baseLeft (List.append leftBits.reverse [current])
      (none :: right)

theorem rightEdgeRewindDescription_haltsFrom_rightBoundaryBase_noDelimiter
    (baseLeft : List (Option Bool))
    (leftBits : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    rightEdgeRewindDescription.HaltsFromTape
      (tapeAtCells
        (some current ::
          List.append (leftBits.map some) (none :: baseLeft))
        (none :: right))
      (tapeAtCells (none :: baseLeft)
        (List.append
          ((List.append leftBits.reverse [current]).map some)
          (none :: right))) := by
  refine ⟨leftBits.length + 3, ?_⟩
  constructor <;>
    rw [rightEdgeRewindDescription_run_from_rightBoundaryBase_noDelimiter]

theorem rightEdgeRewindDescription_run
    (bits : Word Bool) (padding : List (Option Bool)) :
    rightEdgeRewindDescription.runConfig (bits.length + 2)
        { state := rightEdgeRewindDescription.start
          tape := rightEdgeRewindSourceTape bits padding } =
      { state := rightEdgeRewindDescription.halt
        tape := rightEdgeRewindTargetTape bits padding } := by
  simpa [rightEdgeRewindSourceTape, rightEdgeRewindTargetTape] using
    rightEdgeRewindDescription_run_from_leftStack bits.reverse padding

theorem rightEdgeRewindDescription_haltsFromTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    rightEdgeRewindDescription.HaltsFromTape
      (rightEdgeRewindSourceTape bits padding)
      (rightEdgeRewindTargetTape bits padding) := by
  refine ⟨bits.length + 2, ?_⟩
  constructor <;>
    rw [rightEdgeRewindDescription_run]

theorem rightEdgeRewindDescription_haltsFrom_lastBitStack
    (leftStack : Word Bool) (current : Bool)
    (padding : List (Option Bool)) :
    rightEdgeRewindDescription.HaltsFromTape
      (tapeAtCells (leftStack.map some)
        (some current :: none :: padding))
      (rightEdgeRewindTargetTape
        (List.append leftStack.reverse [current]) padding) := by
  refine ⟨leftStack.length + 2, ?_⟩
  constructor <;>
    rw [rightEdgeRewindDescription_run_from_lastBitStack]

theorem rightEdgeRewindDescription_haltsFrom_lastBitBoundary
    (leftStack : Word Bool) (current : Bool)
    (padding : List (Option Bool)) :
    rightEdgeRewindDescription.HaltsFromTape
      (tapeAtCells
        (List.append (leftStack.map some) [none])
        (some current :: none :: padding))
      (rightEdgeRewindTargetTape
        (List.append leftStack.reverse [current]) padding) := by
  refine ⟨leftStack.length + 2, ?_⟩
  constructor <;>
    rw [rightEdgeRewindDescription_run_from_lastBitBoundary]

theorem FSTStatefulOptionAppendTargetTape_moveLeft_eq_rewindSource
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (start : Nat) (input output : Word Bool)
    (hcells :
      statefulOptionCellsFrom next emit start input =
        output.map some) :
    Tape.move Direction.left
        (FSTStatefulOptionAppendTargetTape
          next emit start input [] 0) =
      rightEdgeRewindSourceTape output [none] := by
  rw [FSTStatefulOptionAppendTargetTape,
    statefulOptionAppendWriteTargetTapeAtBlank, hcells]
  simp [rightEdgeRewindSourceTape, tapeAtCells, Tape.move,
    Tape.moveLeft, List.map_reverse]

theorem FSTStatefulOptionAppendPrefixedTargetTape_moveLeft_eq_rewindSource
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (start : Nat) (pref input output : Word Bool)
    (hcells :
      statefulOptionCellsFrom next emit start input =
        output.map some) :
    Tape.move Direction.left
        (FSTStatefulOptionAppendPrefixedTargetTape
          next emit start pref input [] 0) =
      rightEdgeRewindSourceTape (List.append pref output) [none] := by
  rw [FSTStatefulOptionAppendPrefixedTargetTape,
    FSTStatefulOptionAppendTargetTapeFromLeft,
    statefulOptionAppendWriteTargetTapeAtBlank, hcells]
  simp [rightEdgeRewindSourceTape, tapeAtCells, Tape.move,
    Tape.moveLeft, List.reverse_append, List.map_reverse]

theorem rightEdgeRewindDescription_haltsFrom_movedLeft_statefulTarget
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (start : Nat) (input output : Word Bool)
    (hcells :
      statefulOptionCellsFrom next emit start input =
        output.map some) :
    rightEdgeRewindDescription.HaltsFromTape
      (Tape.move Direction.left
        (FSTStatefulOptionAppendTargetTape
          next emit start input [] 0))
      (rightEdgeRewindTargetTape output [none]) := by
  rw [FSTStatefulOptionAppendTargetTape_moveLeft_eq_rewindSource
    next emit start input output hcells]
  exact rightEdgeRewindDescription_haltsFromTape output [none]

theorem rightEdgeRewindDescription_haltsFrom_movedLeft_prefixedTarget
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (start : Nat) (pref input output : Word Bool)
    (hcells :
      statefulOptionCellsFrom next emit start input =
        output.map some) :
    rightEdgeRewindDescription.HaltsFromTape
      (Tape.move Direction.left
        (FSTStatefulOptionAppendPrefixedTargetTape
          next emit start pref input [] 0))
      (rightEdgeRewindTargetTape (List.append pref output) [none]) := by
  rw [FSTStatefulOptionAppendPrefixedTargetTape_moveLeft_eq_rewindSource
    next emit start pref input output hcells]
  exact rightEdgeRewindDescription_haltsFromTape
    (List.append pref output) [none]

end FiniteTransducers
end CommonGround

end Computability
end FoC
