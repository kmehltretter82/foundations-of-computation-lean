import FoC.Computability.Compiler.ClosedCfg.PostTrans.Specs

set_option doc.verso true

/-!
# Contextual nested-layout scanner

The contextual nested-layout handoff retains the outer simulator suffix and
inserts a second transition remainder between the outer transition marker and
the nested layout body.  The finite machine below performs that insertion in
place.  A rolling three-bit buffer shifts the arbitrary remaining suffix to
the right; a temporary blank marker at the first cell lets the final rewind
restore the exact source head without introducing extra represented padding.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

private def nestedLayoutScannerQueueState (a b c : Bool) : Nat :=
  match a, b, c with
  | false, false, false => 4
  | false, false, true => 5
  | false, true, false => 6
  | false, true, true => 7
  | true, false, false => 8
  | true, false, true => 9
  | true, true, false => 10
  | true, true, true => 11

/--
Insert the three-bit transition remainder after a complete transition prefix.
-/
def nestedLayoutTransitionRemainderInserterDescription :
    MachineDescription where
  stateCount := 22
  start := 0
  halt := 21
  transitions :=
    [ transition 0 (some false) none Direction.right 1
    , transition 1 (some false) (some false) Direction.right 2
    , transition 1 (some true) (some true) Direction.right 2
    , transition 2 (some false) (some false) Direction.right 3
    , transition 2 (some true) (some true) Direction.right 3
    , transition 3 (some false) (some false) Direction.right 5
    , transition 3 (some true) (some true) Direction.right 5
    , transition 4 (some false) (some false) Direction.right 4
    , transition 4 (some true) (some false) Direction.right 5
    , transition 4 none (some false) Direction.right 12
    , transition 5 (some false) (some false) Direction.right 6
    , transition 5 (some true) (some false) Direction.right 7
    , transition 5 none (some false) Direction.right 13
    , transition 6 (some false) (some false) Direction.right 8
    , transition 6 (some true) (some false) Direction.right 9
    , transition 6 none (some false) Direction.right 14
    , transition 7 (some false) (some false) Direction.right 10
    , transition 7 (some true) (some false) Direction.right 11
    , transition 7 none (some false) Direction.right 15
    , transition 8 (some false) (some true) Direction.right 4
    , transition 8 (some true) (some true) Direction.right 5
    , transition 8 none (some true) Direction.right 12
    , transition 9 (some false) (some true) Direction.right 6
    , transition 9 (some true) (some true) Direction.right 7
    , transition 9 none (some true) Direction.right 13
    , transition 10 (some false) (some true) Direction.right 8
    , transition 10 (some true) (some true) Direction.right 9
    , transition 10 none (some true) Direction.right 14
    , transition 11 (some false) (some true) Direction.right 10
    , transition 11 (some true) (some true) Direction.right 11
    , transition 11 none (some true) Direction.right 15
    , transition 12 none (some false) Direction.right 16
    , transition 13 none (some false) Direction.right 17
    , transition 14 none (some true) Direction.right 16
    , transition 15 none (some true) Direction.right 17
    , transition 16 none (some false) Direction.left 18
    , transition 17 none (some true) Direction.left 18
    , transition 18 (some false) (some false) Direction.right 19
    , transition 18 (some true) (some true) Direction.right 19
    , transition 19 (some false) (some false) Direction.left 19
    , transition 19 (some true) (some true) Direction.left 19
    , transition 19 none (some false) Direction.right 20
    , transition 20 (some false) (some false) Direction.left 21
    , transition 20 (some true) (some true) Direction.left 21 ]

theorem nestedLayoutTransitionRemainderInserterDescription_subroutineReady :
    nestedLayoutTransitionRemainderInserterDescription.SubroutineReady := by
  constructor
  · refine ⟨by decide, by decide, by decide, ?_, ?_⟩
    · exact transition_wellFormed_of_all (by decide)
    · exact transition_deterministic_of_all (by decide)
  · exact transition_notFrom_of_all (by decide)

private theorem nestedLayoutTransitionRemainderInserterDescription_step_queue_bit
    (a b c d : Bool) (left right : List (Option Bool)) :
    nestedLayoutTransitionRemainderInserterDescription.runConfig 1
        { state := nestedLayoutScannerQueueState a b c
          tape := DovetailInitialLayoutInitializer.tapeAtCells left
            (some d :: right) } =
      { state := nestedLayoutScannerQueueState b c d
        tape := DovetailInitialLayoutInitializer.tapeAtCells
          (some a :: left) right } := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases right <;>
    simp [nestedLayoutTransitionRemainderInserterDescription,
      nestedLayoutScannerQueueState,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem nestedLayoutTransitionRemainderInserterDescription_flush
    (a b c : Bool) (left : List (Option Bool)) :
    nestedLayoutTransitionRemainderInserterDescription.runConfig 4
        { state := nestedLayoutScannerQueueState a b c
          tape := DovetailInitialLayoutInitializer.tapeAtCells left [] } =
      { state := 19
        tape := DovetailInitialLayoutInitializer.tapeAtCells
          (some b :: some a :: left) [some c] } := by
  cases a <;> cases b <;> cases c <;>
    simp [nestedLayoutTransitionRemainderInserterDescription,
      nestedLayoutScannerQueueState,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

private def nestedLayoutScannerRightEndTapeWithBase
    (baseLeft : List (Option Bool)) (output : List Bool) : Tape Bool :=
  match output.reverse with
  | [] => DovetailInitialLayoutInitializer.tapeAtCells baseLeft []
  | last :: reverseInit =>
      DovetailInitialLayoutInitializer.tapeAtCells
        (List.append (reverseInit.map some) baseLeft) [some last]

private def nestedLayoutScannerQueueOutput
    (a b c : Bool) (tail : List Bool) : List Bool :=
  a :: b :: c :: tail

private theorem nestedLayoutScannerRightEndTapeWithBase_queue_cons
    (a b c d : Bool) (rest : List Bool)
    (left : List (Option Bool)) :
    nestedLayoutScannerRightEndTapeWithBase (some a :: left)
        (nestedLayoutScannerQueueOutput b c d rest) =
      nestedLayoutScannerRightEndTapeWithBase left
        (nestedLayoutScannerQueueOutput a b c (d :: rest)) := by
  cases hrev : rest.reverse <;>
    simp [nestedLayoutScannerRightEndTapeWithBase,
      nestedLayoutScannerQueueOutput, List.reverse_cons,
      List.map_append, List.append_assoc, hrev]

private theorem nestedLayoutTransitionRemainderInserterDescription_run_queue
    (a b c : Bool) (tail : List Bool)
    (left : List (Option Bool)) :
    nestedLayoutTransitionRemainderInserterDescription.runConfig
        (tail.length + 4)
        { state := nestedLayoutScannerQueueState a b c
          tape := DovetailInitialLayoutInitializer.tapeAtCells left
            (tail.map some) } =
      { state := 19
        tape := nestedLayoutScannerRightEndTapeWithBase left
          (nestedLayoutScannerQueueOutput a b c tail) } := by
  induction tail generalizing a b c left with
  | nil =>
      have hflush :=
        nestedLayoutTransitionRemainderInserterDescription_flush a b c left
      cases a <;> cases b <;> cases c <;>
        simpa [nestedLayoutScannerQueueOutput,
          nestedLayoutScannerRightEndTapeWithBase] using hflush
  | cons d rest ih =>
      simp only [List.length_cons]
      rw [show rest.length + 1 + 4 = 1 + (rest.length + 4) by lia]
      rw [runConfig_add]
      simp only [List.map_cons]
      rw [nestedLayoutTransitionRemainderInserterDescription_step_queue_bit]
      rw [ih b c d (some a :: left)]
      rw [nestedLayoutScannerRightEndTapeWithBase_queue_cons]

private theorem nestedLayoutTransitionRemainderInserterDescription_step_rewind
    (bit current : Bool) (left : List (Option Bool))
    (right : List (Option Bool)) :
    nestedLayoutTransitionRemainderInserterDescription.runConfig 1
        { state := 19
          tape := DovetailInitialLayoutInitializer.tapeAtCells
            (some bit :: left) (some current :: right) } =
      { state := 19
        tape := DovetailInitialLayoutInitializer.tapeAtCells
          left (some bit :: some current :: right) } := by
  cases bit <;> cases current <;> cases left <;> cases right <;>
    simp [nestedLayoutTransitionRemainderInserterDescription,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft]

private theorem nestedLayoutTransitionRemainderInserterDescription_run_rewind
    (leftBits : List Bool) (current : Bool) (rightBits : List Bool) :
    nestedLayoutTransitionRemainderInserterDescription.runConfig
        (leftBits.length + 3)
        { state := 19
          tape := DovetailInitialLayoutInitializer.tapeAtCells
            (List.append (leftBits.map some) [none])
            (some current :: rightBits.map some) } =
      { state := nestedLayoutTransitionRemainderInserterDescription.halt
        tape := DovetailInitialLayoutInitializer.tapeAtCells []
          ((false :: List.append leftBits.reverse
            (current :: rightBits)).map some) } := by
  induction leftBits generalizing current rightBits with
  | nil =>
      cases current <;> cases rightBits <;>
        simp [nestedLayoutTransitionRemainderInserterDescription,
          DovetailInitialLayoutInitializer.tapeAtCells,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons bit rest ih =>
      simp only [List.length_cons]
      rw [show rest.length + 1 + 3 = 1 + (rest.length + 3) by lia]
      rw [runConfig_add]
      simp only [List.map_cons]
      change
        nestedLayoutTransitionRemainderInserterDescription.runConfig
            (rest.length + 3)
            (nestedLayoutTransitionRemainderInserterDescription.runConfig 1
              { state := 19
                tape := DovetailInitialLayoutInitializer.tapeAtCells
                  (some bit :: List.append (rest.map some) [none])
                  (some current :: rightBits.map some) }) = _
      rw [nestedLayoutTransitionRemainderInserterDescription_step_rewind]
      simpa [List.reverse_cons, List.append_assoc] using
        ih bit (current :: rightBits)

private theorem nestedLayoutTransitionRemainderInserterDescription_run_rightEnd
    (bits : List Bool) (hbits : bits ≠ []) :
    nestedLayoutTransitionRemainderInserterDescription.runConfig
        (bits.length + 2)
        { state := 19
          tape := nestedLayoutScannerRightEndTapeWithBase [none] bits } =
      { state := nestedLayoutTransitionRemainderInserterDescription.halt
        tape := DovetailInitialLayoutInitializer.tapeAtCells []
          ((false :: bits).map some) } := by
  cases hrev : bits.reverse with
  | nil =>
      have hnil : bits = [] := by
        have := congrArg List.reverse hrev
        simpa using this
      exact False.elim (hbits hnil)
  | cons current leftBits =>
      have hbitsEq :
          bits = List.append leftBits.reverse [current] := by
        have := congrArg List.reverse hrev
        simpa [List.reverse_cons] using this
      rw [hbitsEq]
      simpa [nestedLayoutScannerRightEndTapeWithBase, hrev,
        List.length_append] using
        nestedLayoutTransitionRemainderInserterDescription_run_rewind
          leftBits current []

/-- The complete transition-code prefix consumed by the contextual scanner. -/
def nestedLayoutScannerSourcePrefix : List Bool :=
  [false, false, false, true]

/-- Bits following the temporary first-cell marker after insertion. -/
def nestedLayoutScannerInsertedTail (tail : List Bool) : List Bool :=
  List.append [false, false, true, false, false, true] tail

private theorem nestedLayoutTransitionRemainderInserterDescription_run_prefix
    (tail : List Bool) :
    nestedLayoutTransitionRemainderInserterDescription.runConfig 4
        { state := nestedLayoutTransitionRemainderInserterDescription.start
          tape := DovetailInitialLayoutInitializer.tapeAtCells []
            ((List.append nestedLayoutScannerSourcePrefix tail).map some) } =
      { state := nestedLayoutScannerQueueState false false true
        tape := DovetailInitialLayoutInitializer.tapeAtCells
          [some true, some false, some false, none] (tail.map some) } := by
  cases tail <;>
    simp [nestedLayoutTransitionRemainderInserterDescription,
      nestedLayoutScannerQueueState, nestedLayoutScannerSourcePrefix,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem nestedLayoutScannerRightEndTapeWithBase_initialQueue
    (tail : List Bool) :
    nestedLayoutScannerRightEndTapeWithBase
        [some true, some false, some false, none]
        (nestedLayoutScannerQueueOutput false false true tail) =
      nestedLayoutScannerRightEndTapeWithBase [none]
        (nestedLayoutScannerInsertedTail tail) := by
  cases hrev : tail.reverse <;>
    simp [nestedLayoutScannerRightEndTapeWithBase,
      nestedLayoutScannerQueueOutput, nestedLayoutScannerInsertedTail,
      List.reverse_cons, List.map_append, List.append_assoc, hrev]

/--
The contextual inserter preserves an arbitrary suffix while duplicating the
transition remainder and returning the head to the restored first bit.
-/
theorem nestedLayoutTransitionRemainderInserterDescription_haltsFrom_insert
    (tail : List Bool) :
    nestedLayoutTransitionRemainderInserterDescription.HaltsFromTape
      (DovetailInitialLayoutInitializer.tapeAtCells []
        ((List.append nestedLayoutScannerSourcePrefix tail).map some))
      (DovetailInitialLayoutInitializer.tapeAtCells []
        ((false :: nestedLayoutScannerInsertedTail tail).map some)) := by
  let afterMarker := nestedLayoutScannerInsertedTail tail
  let steps := 4 + (tail.length + 4) + (afterMarker.length + 2)
  have hprefix :=
    nestedLayoutTransitionRemainderInserterDescription_run_prefix tail
  have hqueue :=
    nestedLayoutTransitionRemainderInserterDescription_run_queue
      false false true tail
      [some true, some false, some false, none]
  have hrewind :=
    nestedLayoutTransitionRemainderInserterDescription_run_rightEnd
      afterMarker (by
        simp [afterMarker, nestedLayoutScannerInsertedTail])
  have hrun :
      nestedLayoutTransitionRemainderInserterDescription.runConfig steps
          { state := nestedLayoutTransitionRemainderInserterDescription.start
            tape := DovetailInitialLayoutInitializer.tapeAtCells []
              ((List.append nestedLayoutScannerSourcePrefix tail).map some) } =
        { state := nestedLayoutTransitionRemainderInserterDescription.halt
          tape := DovetailInitialLayoutInitializer.tapeAtCells []
            ((false :: nestedLayoutScannerInsertedTail tail).map some) } := by
    rw [show steps =
        4 + ((tail.length + 4) + (afterMarker.length + 2)) by
      simp [steps, Nat.add_assoc]]
    rw [runConfig_add, runConfig_add]
    rw [hprefix, hqueue]
    rw [nestedLayoutScannerRightEndTapeWithBase_initialQueue]
    exact hrewind
  refine ⟨steps, ?_⟩
  exact ⟨congrArg Configuration.state hrun,
    congrArg Configuration.tape hrun⟩

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
