import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.LeftShiftCompactor
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.PaddedIdentity
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.RightEdgeRewind
import FoC.Computability.Compiler.Core.CommonGround.Identity
import FoC.Computability.Compiler.Core.CommonGround.SeqComposition

set_option doc.verso true

/-!
# One-gap right-edge compactor

This module composes the right-edge rewind adapter with the executable
leading-blank left-shift core.  It closes one physical blank gap immediately
before a contiguous Boolean payload and halts at the right edge of the shifted
payload.  This is a fixed finite-machine slice used on the path toward the full
right-end compactor.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

def canonicalSeqDescription
    (A B : MachineDescription) : MachineDescription :=
  seqSubroutine
    (seqSubroutine A ExactIdentityDescription Direction.right)
    B Direction.left

theorem canonicalSeqDescription_subroutineReady
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady) :
    (canonicalSeqDescription A B).SubroutineReady := by
  exact
    seqSubroutine_subroutineReady
      (seqSubroutine_subroutineReady hA
        CommonGround.Identity.exactIdentityDescription_subroutineReady)
      hB

theorem canonicalSeqDescription_haltsFromTape_of_haltsFromTape
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin Tmid Tnext Tout : Tape Bool}
    (hAhalts : A.HaltsFromTape Tin Tmid)
    (hbridge :
      Tape.move Direction.left (Tape.move Direction.right Tmid) =
        Tnext)
    (hBhalts : B.HaltsFromTape Tnext Tout) :
    (canonicalSeqDescription A B).HaltsFromTape Tin Tout := by
  have hid : ExactIdentityDescription.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  have hAid :
      (seqSubroutine A ExactIdentityDescription Direction.right).HaltsFromTape
        Tin (Tape.move Direction.right Tmid) :=
    SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      hA hid hAhalts rfl
      (CommonGround.Identity.exactIdentityDescription_haltsFromTape
        (Tape.move Direction.right Tmid))
  exact
    SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      (seqSubroutine_subroutineReady hA hid)
      hB hAid hbridge hBhalts

def oneGapRightEndCompactorDescription : MachineDescription :=
  canonicalSeqDescription
    (canonicalSeqDescription
      rightEdgeRewindDescription
      leftMoveOnceDescription)
    leadingBlankLeftShiftDescription

theorem oneGapRightEndCompactorDescription_subroutineReady :
    oneGapRightEndCompactorDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    (canonicalSeqDescription_subroutineReady
      rightEdgeRewindDescription_subroutineReady
      leftMoveOnceDescription_subroutineReady)
    leadingBlankLeftShiftDescription_subroutineReady

theorem rightEdgeRewindTargetTape_move_left
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.move Direction.left
        (rightEdgeRewindTargetTape bits padding) =
      leadingBlankLeftShiftSourceTapeWithPadding [] bits padding := by
  cases bits <;> cases padding <;>
    simp [rightEdgeRewindTargetTape,
      leadingBlankLeftShiftSourceTapeWithPadding,
      tapeAtCells, Tape.move, Tape.moveLeft]

theorem rightEdgeRewindTargetTape_move_left_move_right_cons
    (first : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (rightEdgeRewindTargetTape (first :: rest) padding)) =
      rightEdgeRewindTargetTape (first :: rest) padding := by
  cases first <;> cases rest <;> cases padding <;>
    simp [rightEdgeRewindTargetTape, tapeAtCells, Tape.move,
      Tape.moveLeft, Tape.moveRight]

theorem leadingBlankLeftShiftSourceTapeWithPadding_move_left_move_right
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (leadingBlankLeftShiftSourceTapeWithPadding [] bits padding)) =
      leadingBlankLeftShiftSourceTapeWithPadding [] bits padding := by
  cases bits <;> cases padding <;>
    simp [leadingBlankLeftShiftSourceTapeWithPadding, tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]

theorem rewindThenLeftMoveDescription_haltsFromTape_cons
    (first : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    (canonicalSeqDescription
      rightEdgeRewindDescription
      leftMoveOnceDescription).HaltsFromTape
      (rightEdgeRewindSourceTape (first :: rest) padding)
      (leadingBlankLeftShiftSourceTapeWithPadding
        [] (first :: rest) padding) := by
  rw [← rightEdgeRewindTargetTape_move_left]
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      rightEdgeRewindDescription_subroutineReady
      leftMoveOnceDescription_subroutineReady
      (rightEdgeRewindDescription_haltsFromTape (first :: rest) padding)
      (rightEdgeRewindTargetTape_move_left_move_right_cons
        first rest padding)
      (leftMoveOnceDescription_haltsFromTape
        (rightEdgeRewindTargetTape (first :: rest) padding))

theorem oneGapRightEndCompactorDescription_haltsFromTape_cons
    (first : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    oneGapRightEndCompactorDescription.HaltsFromTape
      (rightEdgeRewindSourceTape (first :: rest) padding)
      (leadingBlankLeftShiftTargetTapeWithPadding
        [] (first :: rest) padding) := by
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      (canonicalSeqDescription_subroutineReady
        rightEdgeRewindDescription_subroutineReady
        leftMoveOnceDescription_subroutineReady)
      leadingBlankLeftShiftDescription_subroutineReady
      (rewindThenLeftMoveDescription_haltsFromTape_cons
        first rest padding)
      (leadingBlankLeftShiftSourceTapeWithPadding_move_left_move_right
        (first :: rest) padding)
      (leadingBlankLeftShiftDescription_haltsFromTape_withPadding
        [] (first :: rest) padding)

def rightEdgeRewindSourceTapeWithBase
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (bits.reverse.map some) (none :: baseLeft))
    (none :: padding)

def rightEdgeRewindTargetTapeWithBase
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells (none :: baseLeft)
    (List.append (bits.map some) (none :: padding))

theorem rightEdgeRewindDescription_run_scan_withBoundaryBase
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
        omega]
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

theorem rightEdgeRewindDescription_step_finish_withBase
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    rightEdgeRewindDescription.runConfig 1
        { state := 1
          tape :=
            tapeAtCells baseLeft
              (none ::
                List.append (bits.map some) (none :: padding)) } =
      { state := rightEdgeRewindDescription.halt
        tape :=
          rightEdgeRewindTargetTapeWithBase
            baseLeft bits padding } := by
  cases bits <;> cases baseLeft <;> cases padding <;>
    simp [rightEdgeRewindDescription,
      rightEdgeRewindTargetTapeWithBase, tapeAtCells, runConfig,
      stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.move, Tape.moveRight, Tape.write]

theorem rightEdgeRewindDescription_run_from_boundaryStack
    (baseLeft : List (Option Bool)) (leftStack : Word Bool)
    (padding : List (Option Bool)) :
    rightEdgeRewindDescription.runConfig (leftStack.length + 2)
        { state := rightEdgeRewindDescription.start
          tape :=
            tapeAtCells
              (List.append (leftStack.map some) (none :: baseLeft))
              (none :: padding) } =
      { state := rightEdgeRewindDescription.halt
        tape :=
          rightEdgeRewindTargetTapeWithBase
            baseLeft leftStack.reverse padding } := by
  cases leftStack with
  | nil =>
      cases baseLeft <;> cases padding <;>
        simp [rightEdgeRewindDescription,
          rightEdgeRewindTargetTapeWithBase, tapeAtCells, runConfig,
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
                    (List.append ((current :: rest).map some)
                      (none :: baseLeft))
                    (none :: padding) } =
            { state := 1
              tape :=
                tapeAtCells
                  (List.append (rest.map some) (none :: baseLeft))
                  (some current :: none :: padding) } := by
        cases current <;>
          simp [rightEdgeRewindDescription, tapeAtCells, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.move, Tape.moveLeft, Tape.write]
      rw [hstart]
      rw [show (rest.length + 1) + 1 =
        (rest.length + 1) + 1 by rfl]
      rw [runConfig_add]
      rw [rightEdgeRewindDescription_run_scan_withBoundaryBase
        baseLeft rest current (none :: padding)]
      simpa [rightEdgeRewindTargetTapeWithBase, List.map_append,
        List.append_assoc] using
        rightEdgeRewindDescription_step_finish_withBase
          baseLeft (List.append rest.reverse [current]) padding

theorem rightEdgeRewindDescription_haltsFromTapeWithBase
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    rightEdgeRewindDescription.HaltsFromTape
      (rightEdgeRewindSourceTapeWithBase baseLeft bits padding)
      (rightEdgeRewindTargetTapeWithBase baseLeft bits padding) := by
  refine ⟨bits.length + 2, ?_⟩
  have hrun :=
    rightEdgeRewindDescription_run_from_boundaryStack
      baseLeft bits.reverse padding
  constructor
  · simpa [rightEdgeRewindSourceTapeWithBase,
      rightEdgeRewindTargetTapeWithBase, List.map_reverse] using
      congrArg (fun c : Configuration => c.state) hrun
  · simpa [rightEdgeRewindSourceTapeWithBase,
      rightEdgeRewindTargetTapeWithBase, List.map_reverse] using
      congrArg (fun c : Configuration => c.tape) hrun

theorem rightEdgeRewindTargetTapeWithBase_move_left
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.move Direction.left
        (rightEdgeRewindTargetTapeWithBase baseLeft bits padding) =
      leadingBlankLeftShiftSourceTapeWithPadding
        baseLeft bits padding := by
  cases bits <;> cases baseLeft <;> cases padding <;>
    simp [rightEdgeRewindTargetTapeWithBase,
      leadingBlankLeftShiftSourceTapeWithPadding,
      tapeAtCells, Tape.move, Tape.moveLeft]

theorem rightEdgeRewindTargetTapeWithBase_move_left_move_right_cons
    (baseLeft : List (Option Bool)) (first : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (rightEdgeRewindTargetTapeWithBase
            baseLeft (first :: rest) padding)) =
      rightEdgeRewindTargetTapeWithBase
        baseLeft (first :: rest) padding := by
  cases first <;> cases rest <;> cases baseLeft <;>
    cases padding <;>
      simp [rightEdgeRewindTargetTapeWithBase, tapeAtCells,
        Tape.move, Tape.moveLeft, Tape.moveRight]

theorem leadingBlankLeftShiftSourceTapeWithPadding_move_left_move_right_base
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (leadingBlankLeftShiftSourceTapeWithPadding
            baseLeft bits padding)) =
      leadingBlankLeftShiftSourceTapeWithPadding
        baseLeft bits padding := by
  cases bits <;> cases baseLeft <;> cases padding <;>
    simp [leadingBlankLeftShiftSourceTapeWithPadding, tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]

theorem rewindThenLeftMoveDescription_haltsFromTapeWithBase_cons
    (baseLeft : List (Option Bool)) (first : Bool)
    (rest : Word Bool) (padding : List (Option Bool)) :
    (canonicalSeqDescription
      rightEdgeRewindDescription
      leftMoveOnceDescription).HaltsFromTape
      (rightEdgeRewindSourceTapeWithBase
        baseLeft (first :: rest) padding)
      (leadingBlankLeftShiftSourceTapeWithPadding
        baseLeft (first :: rest) padding) := by
  rw [← rightEdgeRewindTargetTapeWithBase_move_left]
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      rightEdgeRewindDescription_subroutineReady
      leftMoveOnceDescription_subroutineReady
      (rightEdgeRewindDescription_haltsFromTapeWithBase
        baseLeft (first :: rest) padding)
      (rightEdgeRewindTargetTapeWithBase_move_left_move_right_cons
        baseLeft first rest padding)
      (leftMoveOnceDescription_haltsFromTape
        (rightEdgeRewindTargetTapeWithBase
          baseLeft (first :: rest) padding))

theorem oneGapRightEndCompactorDescription_haltsFromTapeWithBase_cons
    (baseLeft : List (Option Bool)) (first : Bool)
    (rest : Word Bool) (padding : List (Option Bool)) :
    oneGapRightEndCompactorDescription.HaltsFromTape
      (rightEdgeRewindSourceTapeWithBase
        baseLeft (first :: rest) padding)
      (leadingBlankLeftShiftTargetTapeWithPadding
        baseLeft (first :: rest) padding) := by
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      (canonicalSeqDescription_subroutineReady
        rightEdgeRewindDescription_subroutineReady
        leftMoveOnceDescription_subroutineReady)
      leadingBlankLeftShiftDescription_subroutineReady
      (rewindThenLeftMoveDescription_haltsFromTapeWithBase_cons
        baseLeft first rest padding)
      (leadingBlankLeftShiftSourceTapeWithPadding_move_left_move_right_base
        baseLeft (first :: rest) padding)
      (leadingBlankLeftShiftDescription_haltsFromTape_withPadding
        baseLeft (first :: rest) padding)

theorem rightEdgeRewindSourceTapeWithBase_cells
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (rightEdgeRewindSourceTapeWithBase
          baseLeft bits padding) =
      leadingBlankLeftShiftSourceCellsWithPadding
        baseLeft bits padding := by
  simp [rightEdgeRewindSourceTapeWithBase,
    leadingBlankLeftShiftSourceCellsWithPadding,
    tapeAtCells, Tape.cells, List.reverse_append,
    List.map_reverse, List.append_assoc]

theorem oneGapRightEndCompactorDescription_normalizedOutput_preserved_withBase
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (leadingBlankLeftShiftTargetTapeWithPadding
          baseLeft bits padding) =
      Tape.normalizedOutput
        (rightEdgeRewindSourceTapeWithBase
          baseLeft bits padding) := by
  rw [leadingBlankLeftShiftTargetTapeWithPadding_normalizedOutput,
    Tape.normalizedOutput, rightEdgeRewindSourceTapeWithBase_cells,
    leadingBlankLeftShiftSourceCellsWithPadding_filterMap]

def rightBlankRewindDescription : MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ transition 0 none none Direction.left 0
    , transition 0 (some false) (some false) Direction.right 1
    , transition 0 (some true) (some true) Direction.right 1 ]

theorem rightBlankRewindDescription_wellFormed :
    rightBlankRewindDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := rightBlankRewindDescription.transitions)
      (stateCount := rightBlankRewindDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := rightBlankRewindDescription.transitions)
      (by decide)

theorem rightBlankRewindDescription_haltTransitionFree :
    rightBlankRewindDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := rightBlankRewindDescription.transitions)
    (state := rightBlankRewindDescription.halt)
    (by decide)

theorem rightBlankRewindDescription_subroutineReady :
    rightBlankRewindDescription.SubroutineReady :=
  ⟨rightBlankRewindDescription_wellFormed,
    rightBlankRewindDescription_haltTransitionFree⟩

theorem rightBlankRewindDescription_run_to_gap_from_leftStack
    (baseLeft : List (Option Bool)) (current : Bool)
    (leftRest : Word Bool) (paddingScratch : Nat)
    (rightPadding : List (Option Bool)) :
    rightBlankRewindDescription.runConfig (paddingScratch + 2)
        { state := rightBlankRewindDescription.start
          tape :=
            tapeAtCells
              (List.append
                (List.replicate paddingScratch (none : Option Bool))
                (List.append ((current :: leftRest).map some)
                  (none :: baseLeft)))
              (none :: rightPadding) } =
      { state := rightBlankRewindDescription.halt
        tape :=
          rightEdgeRewindSourceTapeWithBase
            baseLeft (current :: leftRest).reverse
            (List.append
              (List.replicate paddingScratch (none : Option Bool))
              rightPadding) } := by
  induction paddingScratch generalizing rightPadding with
  | zero =>
      cases current <;> cases rightPadding <;>
        simp [rightBlankRewindDescription,
          rightEdgeRewindSourceTapeWithBase, tapeAtCells,
          runConfig, stepConfig, lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight, List.reverse_append]
  | succ paddingScratch ih =>
      rw [show paddingScratch + 1 + 2 =
        1 + (paddingScratch + 2) by omega]
      rw [runConfig_add]
      have hstep :
          rightBlankRewindDescription.runConfig 1
              { state := rightBlankRewindDescription.start
                tape :=
                  tapeAtCells
                    (List.append
                      (List.replicate (paddingScratch + 1)
                        (none : Option Bool))
                      (List.append ((current :: leftRest).map some)
                        (none :: baseLeft)))
                    (none :: rightPadding) } =
            { state := rightBlankRewindDescription.start
              tape :=
                tapeAtCells
                  (List.append
                    (List.replicate paddingScratch
                      (none : Option Bool))
                    (List.append ((current :: leftRest).map some)
                      (none :: baseLeft)))
                  (none :: none :: rightPadding) } := by
        simp [rightBlankRewindDescription, tapeAtCells, runConfig,
          stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          List.replicate_succ]
      rw [hstep]
      simpa [List.replicate_succ', List.append_assoc] using
        ih (none :: rightPadding)

theorem rightBlankRewindDescription_haltsFromTape_from_leftStack
    (baseLeft : List (Option Bool)) (first : Bool)
    (leftRest : Word Bool) (paddingScratch : Nat)
    (rightPadding : List (Option Bool)) :
    rightBlankRewindDescription.HaltsFromTape
      (tapeAtCells
        (List.append
          (List.replicate paddingScratch (none : Option Bool))
          (List.append ((first :: leftRest).map some)
            (none :: baseLeft)))
        (none :: rightPadding))
      (rightEdgeRewindSourceTapeWithBase
        baseLeft (first :: leftRest).reverse
        (List.append
          (List.replicate paddingScratch (none : Option Bool))
          rightPadding)) := by
  refine ⟨paddingScratch + 2, ?_⟩
  constructor
  · simpa using
      congrArg (fun c : Configuration => c.state)
        (rightBlankRewindDescription_run_to_gap_from_leftStack
          baseLeft first leftRest paddingScratch rightPadding)
  · simpa using
      congrArg (fun c : Configuration => c.tape)
        (rightBlankRewindDescription_run_to_gap_from_leftStack
          baseLeft first leftRest paddingScratch rightPadding)

theorem oneGapRightEndCompactorDescription_haltsFromTapeWithBase_leftStack
    (baseLeft : List (Option Bool)) (current : Bool)
    (leftRest : Word Bool) (padding : List (Option Bool)) :
    oneGapRightEndCompactorDescription.HaltsFromTape
      (rightEdgeRewindSourceTapeWithBase
        baseLeft (current :: leftRest).reverse padding)
      (leadingBlankLeftShiftTargetTapeWithPadding
        baseLeft (current :: leftRest).reverse padding) := by
  cases hbits : (current :: leftRest).reverse with
  | nil =>
      simp at hbits
  | cons first rest =>
      simpa [hbits] using
        oneGapRightEndCompactorDescription_haltsFromTapeWithBase_cons
          baseLeft first rest padding

def rightBlankLocalGapCompactorSourceTapeWithBase
    (baseLeft : List (Option Bool)) (current : Bool)
    (leftRest : Word Bool) (paddingScratch : Nat) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate (Nat.succ paddingScratch) (none : Option Bool))
      (List.append ((current :: leftRest).map some)
        (none :: baseLeft)))
    [none]

def rightBlankLocalGapCompactorDescription : MachineDescription :=
  canonicalSeqDescription
    rightBlankRewindDescription
    oneGapRightEndCompactorDescription

theorem rightBlankLocalGapCompactorDescription_subroutineReady :
    rightBlankLocalGapCompactorDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    rightBlankRewindDescription_subroutineReady
    oneGapRightEndCompactorDescription_subroutineReady

theorem rightEdgeRewindSourceTapeWithBase_move_left_move_right_padding_cons
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (pad : Option Bool) (padding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (rightEdgeRewindSourceTapeWithBase
            baseLeft bits (pad :: padding))) =
      rightEdgeRewindSourceTapeWithBase
        baseLeft bits (pad :: padding) := by
  cases bits <;> cases baseLeft <;> cases pad <;> cases padding <;>
    simp [rightEdgeRewindSourceTapeWithBase, tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]

theorem rightEdgeRewindSourceTapeWithBase_move_left_move_right_padding_append_cons
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (paddingScratch : Nat) (pad : Option Bool)
    (padding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (rightEdgeRewindSourceTapeWithBase
            baseLeft bits
            (List.append
              (List.replicate paddingScratch (none : Option Bool))
              (pad :: padding)))) =
      rightEdgeRewindSourceTapeWithBase
        baseLeft bits
        (List.append
          (List.replicate paddingScratch (none : Option Bool))
          (pad :: padding)) := by
  cases paddingScratch with
  | zero =>
      simpa using
        rightEdgeRewindSourceTapeWithBase_move_left_move_right_padding_cons
          baseLeft bits pad padding
  | succ paddingScratch =>
      simpa [List.replicate_succ, List.append_assoc] using
        rightEdgeRewindSourceTapeWithBase_move_left_move_right_padding_cons
          baseLeft bits (none : Option Bool)
          (List.append
            (List.replicate paddingScratch (none : Option Bool))
            (pad :: padding))

def rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
    (baseLeft : List (Option Bool)) (current : Bool)
    (leftRest : Word Bool) (paddingScratch : Nat)
    (rightPadding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate paddingScratch (none : Option Bool))
      (List.append ((current :: leftRest).map some)
        (none :: baseLeft)))
    (none :: rightPadding)

theorem rightBlankLocalGapCompactorSourceTapeWithBase_eq_sourceWithBaseAndRight_nil
    (baseLeft : List (Option Bool)) (current : Bool)
    (leftRest : Word Bool) (paddingScratch : Nat) :
    rightBlankLocalGapCompactorSourceTapeWithBase
        baseLeft current leftRest paddingScratch =
      rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
        baseLeft current leftRest (Nat.succ paddingScratch) [] := by
  simp [rightBlankLocalGapCompactorSourceTapeWithBase,
    rightBlankLocalGapCompactorSourceTapeWithBaseAndRight]

theorem rightBlankLocalGapCompactorSourceTapeWithBaseAndRight_cells
    (baseLeft : List (Option Bool)) (current : Bool)
    (leftRest : Word Bool) (paddingScratch : Nat)
    (rightPadding : List (Option Bool)) :
    Tape.cells
        (rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
          baseLeft current leftRest paddingScratch rightPadding) =
      List.append baseLeft.reverse
        (none ::
          List.append (((current :: leftRest).reverse).map some)
            (List.append
              (List.replicate paddingScratch (none : Option Bool))
              (none :: rightPadding))) := by
  simp [rightBlankLocalGapCompactorSourceTapeWithBaseAndRight,
    tapeAtCells, Tape.cells, List.reverse_append,
    List.map_reverse, List.append_assoc]

theorem rightBlankLocalGapCompactorSourceTapeWithBaseAndRight_normalizedOutput
    (baseLeft : List (Option Bool)) (current : Bool)
    (leftRest : Word Bool) (paddingScratch : Nat)
    (rightPadding : List (Option Bool)) :
    Tape.normalizedOutput
        (rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
          baseLeft current leftRest paddingScratch rightPadding) =
      List.append
        (baseLeft.reverse.filterMap (fun cell => cell))
        (List.append (current :: leftRest).reverse
          (rightPadding.filterMap (fun cell => cell))) := by
  rw [Tape.normalizedOutput,
    rightBlankLocalGapCompactorSourceTapeWithBaseAndRight_cells]
  simp [List.filterMap_append, Function.comp_def]

theorem rightBlankLocalGapCompactorDescription_haltsFromTapeWithBase_leftStack_rightPadding
    (baseLeft : List (Option Bool)) (current : Bool)
    (leftRest : Word Bool) (paddingScratch : Nat)
    (pad : Option Bool) (rightPadding : List (Option Bool)) :
    rightBlankLocalGapCompactorDescription.HaltsFromTape
      (rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
        baseLeft current leftRest paddingScratch
        (pad :: rightPadding))
      (leadingBlankLeftShiftTargetTapeWithPadding
        baseLeft (current :: leftRest).reverse
        (List.append
          (List.replicate paddingScratch (none : Option Bool))
          (pad :: rightPadding))) := by
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      rightBlankRewindDescription_subroutineReady
      oneGapRightEndCompactorDescription_subroutineReady
      (by
        simpa [rightBlankLocalGapCompactorSourceTapeWithBaseAndRight] using
          rightBlankRewindDescription_haltsFromTape_from_leftStack
            baseLeft current leftRest paddingScratch
            (pad :: rightPadding))
      (rightEdgeRewindSourceTapeWithBase_move_left_move_right_padding_append_cons
        baseLeft (current :: leftRest).reverse paddingScratch pad
        rightPadding)
      (oneGapRightEndCompactorDescription_haltsFromTapeWithBase_leftStack
        baseLeft current leftRest
        (List.append
          (List.replicate paddingScratch (none : Option Bool))
          (pad :: rightPadding)))

theorem rightBlankLocalGapCompactorDescription_normalizedOutput_preserved_leftStack_rightPadding
    (baseLeft : List (Option Bool)) (current : Bool)
    (leftRest : Word Bool) (paddingScratch : Nat)
    (pad : Option Bool) (rightPadding : List (Option Bool)) :
    Tape.normalizedOutput
        (leadingBlankLeftShiftTargetTapeWithPadding
          baseLeft (current :: leftRest).reverse
          (List.append
            (List.replicate paddingScratch (none : Option Bool))
            (pad :: rightPadding))) =
      Tape.normalizedOutput
        (rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
          baseLeft current leftRest paddingScratch
          (pad :: rightPadding)) := by
  rw [leadingBlankLeftShiftTargetTapeWithPadding_normalizedOutput,
    rightBlankLocalGapCompactorSourceTapeWithBaseAndRight_normalizedOutput]
  simp [List.filterMap_append]

theorem leadingBlankLeftShiftTargetTapeWithPadding_eq_nextRightBlankLocalGapSource
    (baseTail : List (Option Bool)) (current : Bool)
    (leftRest : Word Bool) (rightPadding : List (Option Bool)) :
    leadingBlankLeftShiftTargetTapeWithPadding
        (none :: baseTail) (current :: leftRest).reverse
        (none :: rightPadding) =
      rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
        baseTail current leftRest 2 rightPadding := by
  simp [leadingBlankLeftShiftTargetTapeWithPadding,
    rightBlankLocalGapCompactorSourceTapeWithBaseAndRight,
    tapeAtCells, List.replicate, List.reverse_append]

theorem replicate_none_append_none_cons
    (n : Nat) (tail : List (Option Bool)) :
    List.append (List.replicate n (none : Option Bool))
        (none :: tail) =
      none :: List.append
        (List.replicate n (none : Option Bool)) tail := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [List.replicate_succ]
      exact ih

def rightBlankLocalGapBaseLeft
    (gap : Nat) (baseTail : List (Option Bool)) :
    List (Option Bool) :=
  List.append (List.replicate gap (none : Option Bool)) baseTail

theorem rightBlankLocalGapBaseLeft_succ
    (gap : Nat) (baseTail : List (Option Bool)) :
    rightBlankLocalGapBaseLeft (Nat.succ gap) baseTail =
      none :: rightBlankLocalGapBaseLeft gap baseTail := by
  simp [rightBlankLocalGapBaseLeft, List.replicate_succ]

theorem leadingBlankLeftShiftTargetTapeWithPadding_eq_nextRightBlankLocalGapSource_append
    (baseTail : List (Option Bool)) (current : Bool)
    (leftRest : Word Bool) (paddingScratch : Nat)
    (rightPadding : List (Option Bool)) :
    leadingBlankLeftShiftTargetTapeWithPadding
        (none :: baseTail) (current :: leftRest).reverse
        (List.append
          (List.replicate paddingScratch (none : Option Bool))
          (none :: rightPadding)) =
      rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
        baseTail current leftRest 2
        (List.append
          (List.replicate paddingScratch (none : Option Bool))
          rightPadding) := by
  rw [replicate_none_append_none_cons]
  exact
    leadingBlankLeftShiftTargetTapeWithPadding_eq_nextRightBlankLocalGapSource
      baseTail current leftRest
      (List.append
        (List.replicate paddingScratch (none : Option Bool))
        rightPadding)

theorem leadingBlankLeftShiftTargetTapeWithPadding_eq_nextRightBlankLocalGapSource_gapBase_succ
    (gap : Nat) (baseTail : List (Option Bool))
    (current : Bool) (leftRest : Word Bool)
    (paddingScratch : Nat) (rightPadding : List (Option Bool)) :
    leadingBlankLeftShiftTargetTapeWithPadding
        (rightBlankLocalGapBaseLeft (Nat.succ gap) baseTail)
        (current :: leftRest).reverse
        (List.append
          (List.replicate paddingScratch (none : Option Bool))
          (none :: rightPadding)) =
      rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
        (rightBlankLocalGapBaseLeft gap baseTail)
        current leftRest 2
        (List.append
          (List.replicate paddingScratch (none : Option Bool))
          rightPadding) := by
  rw [rightBlankLocalGapBaseLeft_succ]
  exact
    leadingBlankLeftShiftTargetTapeWithPadding_eq_nextRightBlankLocalGapSource_append
      (rightBlankLocalGapBaseLeft gap baseTail)
      current leftRest paddingScratch rightPadding

theorem rightBlankLocalGapCompactorDescription_haltsFrom_gapBase_succ_to_nextSource
    (gap : Nat) (baseTail : List (Option Bool))
    (current : Bool) (leftRest : Word Bool)
    (paddingScratch : Nat) (rightPadding : List (Option Bool)) :
    rightBlankLocalGapCompactorDescription.HaltsFromTape
      (rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
        (rightBlankLocalGapBaseLeft (Nat.succ gap) baseTail)
        current leftRest paddingScratch
        (none :: rightPadding))
      (rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
        (rightBlankLocalGapBaseLeft gap baseTail)
        current leftRest 2
        (List.append
          (List.replicate paddingScratch (none : Option Bool))
          rightPadding)) := by
  rw [←
    leadingBlankLeftShiftTargetTapeWithPadding_eq_nextRightBlankLocalGapSource_gapBase_succ
      gap baseTail current leftRest paddingScratch rightPadding]
  exact
    rightBlankLocalGapCompactorDescription_haltsFromTapeWithBase_leftStack_rightPadding
      (rightBlankLocalGapBaseLeft (Nat.succ gap) baseTail)
      current leftRest paddingScratch (none : Option Bool) rightPadding

theorem leadingBlankLeftShiftTargetTapeWithPadding_eq_nextRightBlankLocalGapSource_replicate
    (baseTail : List (Option Bool)) (current : Bool)
    (leftRest : Word Bool) (paddingScratch : Nat) :
    leadingBlankLeftShiftTargetTapeWithPadding
        (none :: baseTail) (current :: leftRest).reverse
        (List.replicate (Nat.succ paddingScratch)
          (none : Option Bool)) =
      rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
        baseTail current leftRest 2
        (List.replicate paddingScratch
          (none : Option Bool)) := by
  simpa [List.replicate_succ] using
    leadingBlankLeftShiftTargetTapeWithPadding_eq_nextRightBlankLocalGapSource
      baseTail current leftRest
      (List.replicate paddingScratch (none : Option Bool))

theorem leadingBlankLeftShiftTargetTapeWithPadding_move_left_move_right_padding_cons_cons
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (pad nextPad : Option Bool) (padding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (leadingBlankLeftShiftTargetTapeWithPadding
            baseLeft bits (pad :: nextPad :: padding))) =
      leadingBlankLeftShiftTargetTapeWithPadding
        baseLeft bits (pad :: nextPad :: padding) := by
  cases bits <;> cases baseLeft <;> cases pad <;>
    cases nextPad <;> cases padding <;>
    simp [leadingBlankLeftShiftTargetTapeWithPadding, tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]

def twoRightBlankLocalGapCompactorDescription : MachineDescription :=
  canonicalSeqDescription
    rightBlankLocalGapCompactorDescription
    rightBlankLocalGapCompactorDescription

def repeatedRightBlankLocalGapCompactorDescription :
    Nat -> MachineDescription
  | 0 => ExactIdentityDescription
  | n + 1 =>
      canonicalSeqDescription
        rightBlankLocalGapCompactorDescription
        (repeatedRightBlankLocalGapCompactorDescription n)

theorem repeatedRightBlankLocalGapCompactorDescription_subroutineReady
    (passes : Nat) :
    (repeatedRightBlankLocalGapCompactorDescription passes).SubroutineReady := by
  induction passes with
  | zero =>
      exact CommonGround.Identity.exactIdentityDescription_subroutineReady
  | succ passes ih =>
      exact canonicalSeqDescription_subroutineReady
        rightBlankLocalGapCompactorDescription_subroutineReady ih

theorem twoRightBlankLocalGapCompactorDescription_subroutineReady :
    twoRightBlankLocalGapCompactorDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    rightBlankLocalGapCompactorDescription_subroutineReady
    rightBlankLocalGapCompactorDescription_subroutineReady

theorem twoRightBlankLocalGapCompactorDescription_haltsFromTapeWithBase_leftStack
    (baseTail : List (Option Bool)) (current : Bool)
    (leftRest : Word Bool) (nextPad : Option Bool)
    (rightPadding : List (Option Bool)) :
    twoRightBlankLocalGapCompactorDescription.HaltsFromTape
      (rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
        (none :: baseTail) current leftRest 0
        (none :: nextPad :: rightPadding))
      (leadingBlankLeftShiftTargetTapeWithPadding
        baseTail (current :: leftRest).reverse
        (none :: none :: nextPad :: rightPadding)) := by
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      rightBlankLocalGapCompactorDescription_subroutineReady
      rightBlankLocalGapCompactorDescription_subroutineReady
      (rightBlankLocalGapCompactorDescription_haltsFromTapeWithBase_leftStack_rightPadding
        (none :: baseTail) current leftRest 0
        (none : Option Bool) (nextPad :: rightPadding))
      (by
        calc
          Tape.move Direction.left
              (Tape.move Direction.right
                (leadingBlankLeftShiftTargetTapeWithPadding
                  (none :: baseTail) (current :: leftRest).reverse
                  (List.append (List.replicate 0 (none : Option Bool))
                    (none :: nextPad :: rightPadding)))) =
            Tape.move Direction.left
              (Tape.move Direction.right
                (leadingBlankLeftShiftTargetTapeWithPadding
                  (none :: baseTail) (current :: leftRest).reverse
                  (none :: nextPad :: rightPadding))) := by
              simp
          _ =
            leadingBlankLeftShiftTargetTapeWithPadding
              (none :: baseTail) (current :: leftRest).reverse
              (none :: nextPad :: rightPadding) :=
              leadingBlankLeftShiftTargetTapeWithPadding_move_left_move_right_padding_cons_cons
                (none :: baseTail) (current :: leftRest).reverse
                (none : Option Bool) nextPad rightPadding
          _ =
            rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
              baseTail current leftRest 2 (nextPad :: rightPadding) :=
              leadingBlankLeftShiftTargetTapeWithPadding_eq_nextRightBlankLocalGapSource
                baseTail current leftRest (nextPad :: rightPadding))
      (rightBlankLocalGapCompactorDescription_haltsFromTapeWithBase_leftStack_rightPadding
        baseTail current leftRest 2
        nextPad rightPadding)

theorem twoRightBlankLocalGapCompactorDescription_haltsFromTapeWithBase_leftStack_replicate
    (baseTail : List (Option Bool)) (current : Bool)
    (leftRest : Word Bool) (paddingScratch : Nat) :
    twoRightBlankLocalGapCompactorDescription.HaltsFromTape
      (rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
        (none :: baseTail) current leftRest 0
        (List.replicate (Nat.succ (Nat.succ paddingScratch))
          (none : Option Bool)))
      (leadingBlankLeftShiftTargetTapeWithPadding
        baseTail (current :: leftRest).reverse
        (List.replicate (paddingScratch + 3)
          (none : Option Bool))) := by
  simpa [List.replicate_succ, Nat.add_assoc] using
    twoRightBlankLocalGapCompactorDescription_haltsFromTapeWithBase_leftStack
      baseTail current leftRest (none : Option Bool)
      (List.replicate paddingScratch (none : Option Bool))

theorem rightBlankLocalGapCompactorDescription_haltsFromTapeWithBase_leftStack
    (baseLeft : List (Option Bool)) (current : Bool)
    (leftRest : Word Bool) (paddingScratch : Nat) :
    rightBlankLocalGapCompactorDescription.HaltsFromTape
      (rightBlankLocalGapCompactorSourceTapeWithBase
        baseLeft current leftRest paddingScratch)
      (leadingBlankLeftShiftTargetTapeWithPadding
        baseLeft (current :: leftRest).reverse
        (List.replicate (Nat.succ paddingScratch)
          (none : Option Bool))) := by
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      rightBlankRewindDescription_subroutineReady
      oneGapRightEndCompactorDescription_subroutineReady
      (by
        simpa [rightBlankLocalGapCompactorSourceTapeWithBase] using
          rightBlankRewindDescription_haltsFromTape_from_leftStack
            baseLeft current leftRest (Nat.succ paddingScratch) [])
      (by
        simpa [List.replicate_succ] using
          rightEdgeRewindSourceTapeWithBase_move_left_move_right_padding_cons
            baseLeft (current :: leftRest).reverse
            (none : Option Bool)
            (List.replicate paddingScratch (none : Option Bool)))
      (oneGapRightEndCompactorDescription_haltsFromTapeWithBase_leftStack
        baseLeft current leftRest
        (List.replicate (Nat.succ paddingScratch)
          (none : Option Bool)))

theorem twoRightBlankLocalGapCompactorDescription_haltsFromRightEndSourceWithBase_leftStack_replicate
    (baseTail : List (Option Bool)) (current : Bool)
    (leftRest : Word Bool) (paddingScratch : Nat) :
    twoRightBlankLocalGapCompactorDescription.HaltsFromTape
      (rightBlankLocalGapCompactorSourceTapeWithBase
        (none :: baseTail) current leftRest
        (Nat.succ paddingScratch))
      (leadingBlankLeftShiftTargetTapeWithPadding
        baseTail (current :: leftRest).reverse
        (List.replicate (paddingScratch + 3)
          (none : Option Bool))) := by
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      rightBlankLocalGapCompactorDescription_subroutineReady
      rightBlankLocalGapCompactorDescription_subroutineReady
      (rightBlankLocalGapCompactorDescription_haltsFromTapeWithBase_leftStack
        (none :: baseTail) current leftRest
        (Nat.succ paddingScratch))
      (by
        calc
          Tape.move Direction.left
              (Tape.move Direction.right
                (leadingBlankLeftShiftTargetTapeWithPadding
                  (none :: baseTail) (current :: leftRest).reverse
                  (List.replicate (Nat.succ (Nat.succ paddingScratch))
                    (none : Option Bool)))) =
            leadingBlankLeftShiftTargetTapeWithPadding
              (none :: baseTail) (current :: leftRest).reverse
              (List.replicate (Nat.succ (Nat.succ paddingScratch))
                (none : Option Bool)) := by
              simpa [List.replicate_succ] using
                leadingBlankLeftShiftTargetTapeWithPadding_move_left_move_right_padding_cons_cons
                  (none :: baseTail) (current :: leftRest).reverse
                  (none : Option Bool) (none : Option Bool)
                  (List.replicate paddingScratch (none : Option Bool))
          _ =
            rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
              baseTail current leftRest 2
              (List.replicate (Nat.succ paddingScratch)
                (none : Option Bool)) :=
              leadingBlankLeftShiftTargetTapeWithPadding_eq_nextRightBlankLocalGapSource_replicate
                baseTail current leftRest
                (Nat.succ paddingScratch))
      (rightBlankLocalGapCompactorDescription_haltsFromTapeWithBase_leftStack_rightPadding
        baseTail current leftRest 2
        (none : Option Bool)
        (List.replicate paddingScratch (none : Option Bool)))

theorem repeatedRightBlankLocalGapCompactorDescription_two_haltsFromRightEndSourceWithBase_leftStack_replicate
    (baseTail : List (Option Bool)) (current : Bool)
    (leftRest : Word Bool) (paddingScratch : Nat) :
    (repeatedRightBlankLocalGapCompactorDescription 2).HaltsFromTape
      (rightBlankLocalGapCompactorSourceTapeWithBase
        (none :: baseTail) current leftRest
        (Nat.succ paddingScratch))
      (leadingBlankLeftShiftTargetTapeWithPadding
        baseTail (current :: leftRest).reverse
        (List.replicate (paddingScratch + 3)
          (none : Option Bool))) := by
  have hsecond :
      (repeatedRightBlankLocalGapCompactorDescription 1).HaltsFromTape
        (rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
          baseTail current leftRest 2
          (List.replicate (Nat.succ paddingScratch)
            (none : Option Bool)))
        (leadingBlankLeftShiftTargetTapeWithPadding
          baseTail (current :: leftRest).reverse
          (List.replicate (paddingScratch + 3)
            (none : Option Bool))) := by
    exact
      canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        rightBlankLocalGapCompactorDescription_subroutineReady
        CommonGround.Identity.exactIdentityDescription_subroutineReady
        (rightBlankLocalGapCompactorDescription_haltsFromTapeWithBase_leftStack_rightPadding
          baseTail current leftRest 2
          (none : Option Bool)
          (List.replicate paddingScratch (none : Option Bool)))
        (by
          simpa [List.replicate_succ, Nat.add_assoc] using
            leadingBlankLeftShiftTargetTapeWithPadding_move_left_move_right_padding_cons_cons
              baseTail (current :: leftRest).reverse
              (none : Option Bool) (none : Option Bool)
              (List.replicate (paddingScratch + 1)
                (none : Option Bool)))
        (CommonGround.Identity.exactIdentityDescription_haltsFromTape
          (leadingBlankLeftShiftTargetTapeWithPadding
            baseTail (current :: leftRest).reverse
            (List.replicate (paddingScratch + 3)
              (none : Option Bool))))
  simpa [repeatedRightBlankLocalGapCompactorDescription] using
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      rightBlankLocalGapCompactorDescription_subroutineReady
      (repeatedRightBlankLocalGapCompactorDescription_subroutineReady 1)
      (rightBlankLocalGapCompactorDescription_haltsFromTapeWithBase_leftStack
        (none :: baseTail) current leftRest
        (Nat.succ paddingScratch))
      (by
        calc
          Tape.move Direction.left
              (Tape.move Direction.right
                (leadingBlankLeftShiftTargetTapeWithPadding
                  (none :: baseTail) (current :: leftRest).reverse
                  (List.replicate (Nat.succ (Nat.succ paddingScratch))
                    (none : Option Bool)))) =
            leadingBlankLeftShiftTargetTapeWithPadding
              (none :: baseTail) (current :: leftRest).reverse
              (List.replicate (Nat.succ (Nat.succ paddingScratch))
                (none : Option Bool)) := by
              simpa [List.replicate_succ] using
                leadingBlankLeftShiftTargetTapeWithPadding_move_left_move_right_padding_cons_cons
                  (none :: baseTail) (current :: leftRest).reverse
                  (none : Option Bool) (none : Option Bool)
                  (List.replicate paddingScratch (none : Option Bool))
          _ =
            rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
              baseTail current leftRest 2
              (List.replicate (Nat.succ paddingScratch)
                (none : Option Bool)) :=
              leadingBlankLeftShiftTargetTapeWithPadding_eq_nextRightBlankLocalGapSource_replicate
                baseTail current leftRest
                (Nat.succ paddingScratch))
      hsecond

theorem rightBlankLocalGapCompactorSourceTapeWithBase_eq_rightEndCompactionSourceTape
    (baseLeft : List (Option Bool)) (current : Bool)
    (leftRest : Word Bool) (paddingScratch : Nat) :
    rightBlankLocalGapCompactorSourceTapeWithBase
        baseLeft current leftRest paddingScratch =
      rightEndCompactionSourceTape
        (List.append baseLeft.reverse
          (none ::
            List.append (((current :: leftRest).reverse).map some)
              (List.replicate (Nat.succ paddingScratch)
                (none : Option Bool)))) := by
  simp [rightBlankLocalGapCompactorSourceTapeWithBase,
    rightEndCompactionSourceTape, tapeAtCells, List.reverse_append,
    List.map_reverse, List.append_assoc]

def fiveBlankLocalGapCompactorSourceTapeWithBase
    (baseLeft : List (Option Bool)) (bits : Word Bool) : Tape Bool :=
  tapeAtCells
    (none :: none :: none :: none :: none ::
      List.append (bits.reverse.map some) (none :: baseLeft))
    [none]

def fiveBlankLocalGapCompactorDescription : MachineDescription :=
  canonicalSeqDescription
    leftMoveAcrossFiveBlanksDescription
    oneGapRightEndCompactorDescription

theorem fiveBlankLocalGapCompactorDescription_subroutineReady :
    fiveBlankLocalGapCompactorDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    leftMoveAcrossFiveBlanksDescription_subroutineReady
    oneGapRightEndCompactorDescription_subroutineReady

theorem leftMoveAcrossFiveBlanksDescription_haltsFrom_localGapSource
    (baseLeft : List (Option Bool)) (bits : Word Bool) :
    leftMoveAcrossFiveBlanksDescription.HaltsFromTape
      (fiveBlankLocalGapCompactorSourceTapeWithBase baseLeft bits)
      (rightEdgeRewindSourceTapeWithBase
        baseLeft bits
        (List.replicate 5 (none : Option Bool))) := by
  simpa [fiveBlankLocalGapCompactorSourceTapeWithBase,
    rightEdgeRewindSourceTapeWithBase, List.replicate] using
    leftMoveAcrossFiveBlanksDescription_haltsFromTape
      (List.append (bits.reverse.map some) (none :: baseLeft))
      []

theorem fiveBlankLocalGapCompactorDescription_haltsFromTapeWithBase_cons
    (baseLeft : List (Option Bool)) (first : Bool)
    (rest : Word Bool) :
    fiveBlankLocalGapCompactorDescription.HaltsFromTape
      (fiveBlankLocalGapCompactorSourceTapeWithBase
        baseLeft (first :: rest))
      (leadingBlankLeftShiftTargetTapeWithPadding
        baseLeft (first :: rest)
        (List.replicate 5 (none : Option Bool))) := by
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      leftMoveAcrossFiveBlanksDescription_subroutineReady
      oneGapRightEndCompactorDescription_subroutineReady
      (leftMoveAcrossFiveBlanksDescription_haltsFrom_localGapSource
        baseLeft (first :: rest))
      (by
        simpa [List.replicate] using
          rightEdgeRewindSourceTapeWithBase_move_left_move_right_padding_cons
            baseLeft (first :: rest) (none : Option Bool)
            (List.replicate 4 (none : Option Bool)))
      (oneGapRightEndCompactorDescription_haltsFromTapeWithBase_cons
        baseLeft first rest
        (List.replicate 5 (none : Option Bool)))

theorem fiveBlankLocalGapCompactorSourceTapeWithBase_eq_rightEndCompactionSourceTape
    (baseLeft : List (Option Bool)) (bits : Word Bool) :
    fiveBlankLocalGapCompactorSourceTapeWithBase baseLeft bits =
      rightEndCompactionSourceTape
        (List.append baseLeft.reverse
          (none ::
            List.append (bits.map some)
              (List.replicate 5 (none : Option Bool)))) := by
  simp [fiveBlankLocalGapCompactorSourceTapeWithBase,
    rightEndCompactionSourceTape, tapeAtCells, List.reverse_append,
    List.map_reverse, List.replicate, List.append_assoc]

theorem rightEdgeRewindSourceTape_cells
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.cells (rightEdgeRewindSourceTape bits padding) =
      List.append (bits.map some) (none :: padding) := by
  simp [rightEdgeRewindSourceTape, tapeAtCells, Tape.cells,
    List.map_reverse]

theorem rightEdgeRewindSourceTape_normalizedOutput
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (rightEdgeRewindSourceTape bits padding) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [Tape.normalizedOutput, rightEdgeRewindSourceTape_cells]
  simp [List.filterMap_append, Function.comp_def]

theorem oneGapRightEndCompactorTargetTape_cells
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.cells
        (leadingBlankLeftShiftTargetTapeWithPadding
          [] bits padding) =
      List.append (bits.map some)
        (List.append [none, none]
          (leadingBlankLeftShiftTargetVisiblePadding padding)) := by
  rw [leadingBlankLeftShiftTargetTapeWithPadding_cells]
  simp [leadingBlankLeftShiftTargetCellsWithPadding]

theorem oneGapRightEndCompactorDescription_normalizedOutput_preserved_cons
    (first : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (leadingBlankLeftShiftTargetTapeWithPadding
          [] (first :: rest) padding) =
      Tape.normalizedOutput
        (rightEdgeRewindSourceTape (first :: rest) padding) := by
  rw [leadingBlankLeftShiftTargetTapeWithPadding_normalizedOutput,
    rightEdgeRewindSourceTape_normalizedOutput]
  simp

theorem oneGapRightEndCompactorTargetTape_cells_eq_compacted_source_nil
    (first : Bool) (rest : Word Bool) :
    Tape.cells
        (leadingBlankLeftShiftTargetTapeWithPadding
          [] (first :: rest) []) =
      compactedCellsWithScratch
        (Tape.cells (rightEdgeRewindSourceTape (first :: rest) []))
        2 := by
  rw [oneGapRightEndCompactorTargetTape_cells,
    rightEdgeRewindSourceTape_cells]
  simp [leadingBlankLeftShiftTargetVisiblePadding,
    compactedCellsWithScratch, rightScratchOutputCells,
    List.filterMap_append, Function.comp_def]

theorem oneGapRightEndCompactorTargetTape_cells_eq_compacted_source_replicate_none_succ
    (first : Bool) (rest : Word Bool) (paddingScratch : Nat) :
    Tape.cells
        (leadingBlankLeftShiftTargetTapeWithPadding
          [] (first :: rest)
          (List.replicate (Nat.succ paddingScratch)
            (none : Option Bool))) =
      compactedCellsWithScratch
        (Tape.cells
          (rightEdgeRewindSourceTape (first :: rest)
            (List.replicate (Nat.succ paddingScratch)
              (none : Option Bool))))
        1 := by
  rw [oneGapRightEndCompactorTargetTape_cells,
    rightEdgeRewindSourceTape_cells]
  simp [leadingBlankLeftShiftTargetVisiblePadding,
    compactedCellsWithScratch, rightScratchOutputCells,
    List.filterMap_append, Function.comp_def, List.replicate_succ]

end FiniteTransducers
end CommonGround

end Computability
end FoC
