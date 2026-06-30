import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StatefulOptionAppend

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

def rightEdgeScanDescription : MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ transition 0 (some false) (some false) Direction.right 0
    , transition 0 (some true) (some true) Direction.right 0
    , transition 0 none none Direction.left 1 ]

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

theorem rightEdgeScanDescription_wellFormed :
    rightEdgeScanDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := rightEdgeScanDescription.transitions)
      (stateCount := rightEdgeScanDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := rightEdgeScanDescription.transitions)
      (by decide)

theorem rightEdgeScanDescription_haltTransitionFree :
    rightEdgeScanDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := rightEdgeScanDescription.transitions)
    (state := rightEdgeScanDescription.halt)
    (by decide)

theorem rightEdgeScanDescription_subroutineReady :
    rightEdgeScanDescription.SubroutineReady :=
  ⟨rightEdgeScanDescription_wellFormed,
    rightEdgeScanDescription_haltTransitionFree⟩

theorem rightEdgeScanDescription_step_bit
    (left right : List (Option Bool)) (bit : Bool) :
    rightEdgeScanDescription.runConfig 1
        { state := rightEdgeScanDescription.start
          tape := tapeAtCells left (some bit :: right) } =
      { state := rightEdgeScanDescription.start
        tape := tapeAtCells (some bit :: left) right } := by
  cases bit <;> cases right <;>
    simp [rightEdgeScanDescription, tapeAtCells, runConfig,
      stepConfig, lookupTransition, Matches, transition, Tape.read,
      Tape.write, Tape.move, Tape.moveRight]

theorem rightEdgeScanDescription_step_finish
    (left padding : List (Option Bool)) :
    rightEdgeScanDescription.runConfig 1
        { state := rightEdgeScanDescription.start
          tape := tapeAtCells left (none :: padding) } =
      { state := rightEdgeScanDescription.halt
        tape :=
          Tape.move Direction.left
            (tapeAtCells left (none :: padding)) } := by
  cases left <;> cases padding <;>
    simp [rightEdgeScanDescription, tapeAtCells, runConfig,
      stepConfig, lookupTransition, Matches, transition, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft]

theorem rightEdgeScanDescription_run_scan
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
        omega]
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

theorem rightEdgeScanDescription_run_to_target
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

theorem dropTrailingNone_replicate_none
    (padding : Nat) :
    Tape.dropTrailingNone
        (List.replicate padding (none : Option Bool)) = [] := by
  induction padding with
  | zero =>
      rfl
  | succ padding ih =>
      simp [List.replicate, Tape.dropTrailingNone, ih]

theorem dropTrailingNone_append_none
    (xs : List (Option Bool)) :
    Tape.dropTrailingNone (xs ++ [none]) =
      Tape.dropTrailingNone xs := by
  induction xs with
  | nil => rfl
  | cons cell rest ih =>
      rw [List.cons_append, Tape.dropTrailingNone_cons,
        Tape.dropTrailingNone_cons, ih]

theorem dropTrailingNone_append_replicate_none
    (xs : List (Option Bool)) (padding : Nat) :
    Tape.dropTrailingNone
        (xs ++ List.replicate padding (none : Option Bool)) =
      Tape.dropTrailingNone xs := by
  induction padding generalizing xs with
  | zero =>
      simp
  | succ padding ih =>
      calc
        Tape.dropTrailingNone
            (xs ++ List.replicate (padding + 1) (none : Option Bool)) =
          Tape.dropTrailingNone
            ((xs ++ [none]) ++
              List.replicate padding (none : Option Bool)) := by
            simp [List.replicate_succ, List.append_assoc]
        _ = Tape.dropTrailingNone (xs ++ [none]) :=
          ih (xs ++ [none])
        _ = Tape.dropTrailingNone xs :=
          dropTrailingNone_append_none xs

theorem rightEdgeRewindTargetTape_equiv_paddedInput
    (bits : Word Bool) (padding : Nat) :
    Tape.Equiv
      (rightEdgeRewindTargetTape bits
        (List.replicate padding (none : Option Bool)))
      (inputWithTrailingBlankPadding bits (padding + 1)) := by
  cases bits with
  | nil =>
      simp [rightEdgeRewindTargetTape, inputWithTrailingBlankPadding,
        tapeAtCells, Tape.Equiv, Tape.dropTrailingNone,
        dropTrailingNone_replicate_none]
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

theorem rightEdgeRewindDescription_wellFormed :
    rightEdgeRewindDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := rightEdgeRewindDescription.transitions)
      (stateCount := rightEdgeRewindDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := rightEdgeRewindDescription.transitions)
      (by decide)

theorem rightEdgeRewindDescription_haltTransitionFree :
    rightEdgeRewindDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := rightEdgeRewindDescription.transitions)
    (state := rightEdgeRewindDescription.halt)
    (by decide)

theorem rightEdgeRewindDescription_subroutineReady :
    rightEdgeRewindDescription.SubroutineReady :=
  ⟨rightEdgeRewindDescription_wellFormed,
    rightEdgeRewindDescription_haltTransitionFree⟩

theorem rightEdgeRewindDescription_run_scan
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
        omega]
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

theorem rightEdgeRewindDescription_run_scan_withBoundary
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
        omega]
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

theorem rightEdgeRewindDescription_step_finish
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

theorem rightEdgeRewindDescription_run_from_leftStack
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
        omega]
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

theorem rightEdgeRewindDescription_run_from_lastBitStack
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
        omega]
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

theorem rightEdgeRewindDescription_run_from_lastBitBoundary
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
        omega]
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
