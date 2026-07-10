import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.PullNearestRawBit

set_option doc.verso true

/-!
# Raw-boundary marker-aware nearest-bit puller

This module refines the nearest-bit puller with a one-cell left-boundary
check.  If the nearest nonblank cell is preceded by another nonblank cell, the
machine treats it as a real raw bit, erases it, and copies it to the marker
cell immediately left of the live head.  If the nearest nonblank cell is
preceded by a blank, the machine leaves it in place and halts on that boundary
cell; callers can use that endpoint as the "no raw bits remain" branch.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace CountWindowRawSourceEncoder
namespace RawBoundaryRightEdgeEmitter

def markerAwarePullNearestRawBitDescription : MachineDescription where
  stateCount := 11
  start := 0
  halt := 10
  transitions :=
    [ transition 0 (some false) (some false) Direction.left 1
    , transition 0 (some true) (some true) Direction.left 1
    , transition 1 none none Direction.left 1
    , transition 1 (some false) (some false) Direction.left 2
    , transition 1 (some true) (some true) Direction.left 3
    , transition 2 none none Direction.right 10
    , transition 2 (some false) (some false) Direction.right 4
    , transition 2 (some true) (some true) Direction.right 4
    , transition 3 none none Direction.right 10
    , transition 3 (some false) (some false) Direction.right 5
    , transition 3 (some true) (some true) Direction.right 5
    , transition 4 (some false) none Direction.right 6
    , transition 5 (some true) none Direction.right 7
    , transition 6 none none Direction.right 6
    , transition 6 (some false) (some false) Direction.left 8
    , transition 6 (some true) (some true) Direction.left 8
    , transition 7 none none Direction.right 7
    , transition 7 (some false) (some false) Direction.left 9
    , transition 7 (some true) (some true) Direction.left 9
    , transition 8 none (some false) Direction.right 10
    , transition 9 none (some true) Direction.right 10 ]

theorem markerAwarePullNearestRawBitDescription_wellFormed :
    markerAwarePullNearestRawBitDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := markerAwarePullNearestRawBitDescription.transitions)
      (stateCount := markerAwarePullNearestRawBitDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := markerAwarePullNearestRawBitDescription.transitions)
      (by decide)

theorem markerAwarePullNearestRawBitDescription_haltTransitionFree :
    markerAwarePullNearestRawBitDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := markerAwarePullNearestRawBitDescription.transitions)
    (state := markerAwarePullNearestRawBitDescription.halt)
    (by decide)

theorem markerAwarePullNearestRawBitDescription_subroutineReady :
    markerAwarePullNearestRawBitDescription.SubroutineReady :=
  ⟨markerAwarePullNearestRawBitDescription_wellFormed,
    markerAwarePullNearestRawBitDescription_haltTransitionFree⟩

def markerAwarePullNearestRawBitSourceTape
    (blankCount : Nat) (baseLeft : List (Option Bool))
    (rawBit tailFirst : Bool) (tail : List (Option Bool)) :
    Tape Bool :=
  pullNearestRawBitToTailMarkerSourceTape
    blankCount baseLeft rawBit tailFirst tail

def markerAwarePullNearestRawBitTargetTape
    (blankCount : Nat) (baseLeft : List (Option Bool))
    (rawBit tailFirst : Bool) (tail : List (Option Bool)) :
    Tape Bool :=
  pullNearestRawBitToTailMarkerTargetTape
    blankCount baseLeft rawBit tailFirst tail

def markerAwarePullNearestBoundaryTargetTape
    (blankCount : Nat) (baseTail : List (Option Bool))
    (markerBit tailFirst : Bool) (tail : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells (none :: baseTail)
    (some markerBit ::
      List.append
        (List.replicate (blankCount + 1) (none : Option Bool))
        (some tailFirst :: tail))

def markerAwarePullNearestRawBitToHeadMarkerSourceTape
    (gap : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool) (right : List (Option Bool)) :
    Tape Bool :=
  pullNearestRawBitToHeadMarkerSourceTape
    gap baseLeft rawBit headBit right

def markerAwarePullNearestRawBitToHeadMarkerTargetTape
    (gap : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool) (right : List (Option Bool)) :
    Tape Bool :=
  pullNearestRawBitToHeadMarkerTargetTape
    gap baseLeft rawBit headBit right

def markerAwarePullNearestBoundaryToHeadMarkerTargetTape
    (gap : Nat) (baseTail : List (Option Bool))
    (markerBit headBit : Bool) (right : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells (none :: baseTail)
    (some markerBit ::
      List.append
        (List.replicate gap (none : Option Bool))
        (some headBit :: right))

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

theorem markerAwarePullNearestRawBitDescription_step_start
    (left : List (Option Bool)) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.runConfig 1
        { state := markerAwarePullNearestRawBitDescription.start
          tape := tapeAtCells (none :: left) (some tailFirst :: tail) } =
      { state := 1
        tape := tapeAtCells left (none :: some tailFirst :: tail) } := by
  cases tailFirst <;> cases left <;> cases tail <;>
    simp [markerAwarePullNearestRawBitDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem markerAwarePullNearestRawBitDescription_step_start_adjacent
    (baseLeft : List (Option Bool)) (rawBit headBit : Bool)
    (right : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.runConfig 1
        { state := markerAwarePullNearestRawBitDescription.start
          tape := tapeAtCells (some rawBit :: baseLeft)
            (some headBit :: right) } =
      { state := 1
        tape := tapeAtCells baseLeft
          (some rawBit :: some headBit :: right) } := by
  cases rawBit <;> cases headBit <;> cases baseLeft <;>
    cases right <;>
      simp [markerAwarePullNearestRawBitDescription, runConfig,
        stepConfig, lookupTransition, Matches, transition, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem markerAwarePullNearestRawBitDescription_step_scan_blank
    (cell : Option Bool) (left right : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.runConfig 1
        { state := 1
          tape := tapeAtCells (cell :: left) (none :: right) } =
      { state := 1
        tape := tapeAtCells left (cell :: none :: right) } := by
  cases cell <;> cases left <;> cases right <;>
    simp [markerAwarePullNearestRawBitDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem markerAwarePullNearestRawBitDescription_run_scan_blanks
    (blankCount : Nat) (baseLeft right : List (Option Bool))
    (rawBit : Bool) :
    markerAwarePullNearestRawBitDescription.runConfig
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
        markerAwarePullNearestRawBitDescription_step_scan_blank
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
        markerAwarePullNearestRawBitDescription.runConfig
            (blankCount + 1)
            (markerAwarePullNearestRawBitDescription.runConfig 1
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
      rw [markerAwarePullNearestRawBitDescription_step_scan_blank]
      rw [ih baseLeft (none :: right)]
      rw [replicate_none_append_cons_eq (blankCount + 1) right]
      rw [show blankCount + 1 + 1 = 1 + (blankCount + 1) by
        lia]

theorem markerAwarePullNearestRawBitDescription_step_candidate_false
    (neighbor : Option Bool) (baseTail right : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.runConfig 1
        { state := 1
          tape := tapeAtCells (neighbor :: baseTail) (some false :: right) } =
      { state := 2
        tape := tapeAtCells baseTail (neighbor :: some false :: right) } := by
  cases neighbor <;> cases baseTail <;> cases right <;>
    simp [markerAwarePullNearestRawBitDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem markerAwarePullNearestRawBitDescription_step_candidate_true
    (neighbor : Option Bool) (baseTail right : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.runConfig 1
        { state := 1
          tape := tapeAtCells (neighbor :: baseTail) (some true :: right) } =
      { state := 3
        tape := tapeAtCells baseTail (neighbor :: some true :: right) } := by
  cases neighbor <;> cases baseTail <;> cases right <;>
    simp [markerAwarePullNearestRawBitDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem markerAwarePullNearestRawBitDescription_step_boundary_false
    (baseTail right : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.runConfig 1
        { state := 2
          tape := tapeAtCells baseTail (none :: some false :: right) } =
      { state := markerAwarePullNearestRawBitDescription.halt
        tape := tapeAtCells (none :: baseTail) (some false :: right) } := by
  cases baseTail <;> cases right <;>
    simp [markerAwarePullNearestRawBitDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem markerAwarePullNearestRawBitDescription_step_boundary_true
    (baseTail right : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.runConfig 1
        { state := 3
          tape := tapeAtCells baseTail (none :: some true :: right) } =
      { state := markerAwarePullNearestRawBitDescription.halt
        tape := tapeAtCells (none :: baseTail) (some true :: right) } := by
  cases baseTail <;> cases right <;>
    simp [markerAwarePullNearestRawBitDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem markerAwarePullNearestRawBitDescription_step_real_false
    (leftBit : Bool) (baseTail right : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.runConfig 1
        { state := 2
          tape := tapeAtCells baseTail
            (some leftBit :: some false :: right) } =
      { state := 4
        tape := tapeAtCells (some leftBit :: baseTail)
          (some false :: right) } := by
  cases leftBit <;> cases baseTail <;> cases right <;>
    simp [markerAwarePullNearestRawBitDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem markerAwarePullNearestRawBitDescription_step_real_true
    (leftBit : Bool) (baseTail right : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.runConfig 1
        { state := 3
          tape := tapeAtCells baseTail
            (some leftBit :: some true :: right) } =
      { state := 5
        tape := tapeAtCells (some leftBit :: baseTail)
          (some true :: right) } := by
  cases leftBit <;> cases baseTail <;> cases right <;>
    simp [markerAwarePullNearestRawBitDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem markerAwarePullNearestRawBitDescription_step_erase_false
    (left : List (Option Bool)) (right : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.runConfig 1
        { state := 4
          tape := tapeAtCells left (some false :: right) } =
      { state := 6
        tape := tapeAtCells (none :: left) right } := by
  cases left <;> cases right <;>
    simp [markerAwarePullNearestRawBitDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem markerAwarePullNearestRawBitDescription_step_erase_true
    (left : List (Option Bool)) (right : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.runConfig 1
        { state := 5
          tape := tapeAtCells left (some true :: right) } =
      { state := 7
        tape := tapeAtCells (none :: left) right } := by
  cases left <;> cases right <;>
    simp [markerAwarePullNearestRawBitDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem markerAwarePullNearestRawBitDescription_step_return_blank_false
    (left right : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.runConfig 1
        { state := 6
          tape := tapeAtCells left (none :: right) } =
      { state := 6
        tape := tapeAtCells (none :: left) right } := by
  cases right <;>
    simp [markerAwarePullNearestRawBitDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem markerAwarePullNearestRawBitDescription_step_return_blank_true
    (left right : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.runConfig 1
        { state := 7
          tape := tapeAtCells left (none :: right) } =
      { state := 7
        tape := tapeAtCells (none :: left) right } := by
  cases right <;>
    simp [markerAwarePullNearestRawBitDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem markerAwarePullNearestRawBitDescription_run_return_blanks_false
    (blankCount : Nat) (baseLeft : List (Option Bool))
    (tailFirst : Bool) (tail : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.runConfig blankCount
        { state := 6
          tape :=
            tapeAtCells (none :: baseLeft)
              (List.append
                (List.replicate blankCount (none : Option Bool))
                (some tailFirst :: tail)) } =
      { state := 6
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
      rw [show blankCount + 1 = 1 + blankCount by lia]
      rw [runConfig_add]
      rw [show
          List.replicate (1 + blankCount) (none : Option Bool) =
            none :: List.replicate blankCount none by
        rw [show 1 + blankCount = Nat.succ blankCount by lia]
        rfl]
      change
        markerAwarePullNearestRawBitDescription.runConfig blankCount
            (markerAwarePullNearestRawBitDescription.runConfig 1
              { state := 6
                tape :=
                  tapeAtCells (none :: baseLeft)
                    (none ::
                      List.append
                        (List.replicate blankCount
                          (none : Option Bool))
                        (some tailFirst :: tail)) }) =
          { state := 6
            tape :=
              tapeAtCells
                (List.append
                  (List.replicate (Nat.succ blankCount)
                    (none : Option Bool))
                  (none :: baseLeft))
                (some tailFirst :: tail) }
      rw [markerAwarePullNearestRawBitDescription_step_return_blank_false]
      rw [ih (none :: baseLeft)]
      rw [replicate_none_append_none_cons]
      rw [show
          List.replicate (Nat.succ blankCount) (none : Option Bool) =
            none :: List.replicate blankCount none by
        rfl]
      rfl

theorem markerAwarePullNearestRawBitDescription_run_return_blanks_true
    (blankCount : Nat) (baseLeft : List (Option Bool))
    (tailFirst : Bool) (tail : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.runConfig blankCount
        { state := 7
          tape :=
            tapeAtCells (none :: baseLeft)
              (List.append
                (List.replicate blankCount (none : Option Bool))
                (some tailFirst :: tail)) } =
      { state := 7
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
      rw [show blankCount + 1 = 1 + blankCount by lia]
      rw [runConfig_add]
      rw [show
          List.replicate (1 + blankCount) (none : Option Bool) =
            none :: List.replicate blankCount none by
        rw [show 1 + blankCount = Nat.succ blankCount by lia]
        rfl]
      change
        markerAwarePullNearestRawBitDescription.runConfig blankCount
            (markerAwarePullNearestRawBitDescription.runConfig 1
              { state := 7
                tape :=
                  tapeAtCells (none :: baseLeft)
                    (none ::
                      List.append
                        (List.replicate blankCount
                          (none : Option Bool))
                        (some tailFirst :: tail)) }) =
          { state := 7
            tape :=
              tapeAtCells
                (List.append
                  (List.replicate (Nat.succ blankCount)
                    (none : Option Bool))
                  (none :: baseLeft))
                (some tailFirst :: tail) }
      rw [markerAwarePullNearestRawBitDescription_step_return_blank_true]
      rw [ih (none :: baseLeft)]
      rw [replicate_none_append_none_cons]
      rw [show
          List.replicate (Nat.succ blankCount) (none : Option Bool) =
            none :: List.replicate blankCount none by
        rfl]
      rfl

theorem markerAwarePullNearestRawBitDescription_step_tail_false
    (left : List (Option Bool)) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.runConfig 1
        { state := 6
          tape := tapeAtCells (none :: left) (some tailFirst :: tail) } =
      { state := 8
        tape := tapeAtCells left (none :: some tailFirst :: tail) } := by
  cases tailFirst <;> cases left <;> cases tail <;>
    simp [markerAwarePullNearestRawBitDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem markerAwarePullNearestRawBitDescription_step_tail_true
    (left : List (Option Bool)) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.runConfig 1
        { state := 7
          tape := tapeAtCells (none :: left) (some tailFirst :: tail) } =
      { state := 9
        tape := tapeAtCells left (none :: some tailFirst :: tail) } := by
  cases tailFirst <;> cases left <;> cases tail <;>
    simp [markerAwarePullNearestRawBitDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem markerAwarePullNearestRawBitDescription_step_write_false
    (left : List (Option Bool)) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.runConfig 1
        { state := 8
          tape := tapeAtCells left (none :: some tailFirst :: tail) } =
      { state := markerAwarePullNearestRawBitDescription.halt
        tape := tapeAtCells (some false :: left)
          (some tailFirst :: tail) } := by
  cases tailFirst <;> cases tail <;>
    simp [markerAwarePullNearestRawBitDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem markerAwarePullNearestRawBitDescription_step_write_true
    (left : List (Option Bool)) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.runConfig 1
        { state := 9
          tape := tapeAtCells left (none :: some tailFirst :: tail) } =
      { state := markerAwarePullNearestRawBitDescription.halt
        tape := tapeAtCells (some true :: left)
          (some tailFirst :: tail) } := by
  cases tailFirst <;> cases tail <;>
    simp [markerAwarePullNearestRawBitDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem markerAwarePullNearestRawBitDescription_run_boundary_false
    (blankCount : Nat) (baseTail : List (Option Bool))
    (tailFirst : Bool) (tail : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.runConfig
        (blankCount + 4)
        { state := markerAwarePullNearestRawBitDescription.start
          tape :=
            markerAwarePullNearestRawBitSourceTape
              blankCount (none :: baseTail) false tailFirst tail } =
      { state := markerAwarePullNearestRawBitDescription.halt
        tape :=
          markerAwarePullNearestBoundaryTargetTape
            blankCount baseTail false tailFirst tail } := by
  rw [show blankCount + 4 =
    1 + ((blankCount + 1) + (1 + 1)) by lia]
  rw [runConfig_add]
  change
    markerAwarePullNearestRawBitDescription.runConfig
        ((blankCount + 1) + (1 + 1))
        (markerAwarePullNearestRawBitDescription.runConfig 1
          { state := markerAwarePullNearestRawBitDescription.start
            tape :=
              tapeAtCells
                (List.append
                  (List.replicate (blankCount + 1)
                    (none : Option Bool))
                  (some false :: none :: baseTail))
                (some tailFirst :: tail) }) =
      { state := markerAwarePullNearestRawBitDescription.halt
        tape :=
          markerAwarePullNearestBoundaryTargetTape
            blankCount baseTail false tailFirst tail }
  rw [show
      List.replicate (blankCount + 1) (none : Option Bool) =
        none :: List.replicate blankCount none by
    rw [show blankCount + 1 = Nat.succ blankCount by lia]
    rfl]
  rw [show
      List.append
          (none :: List.replicate blankCount (none : Option Bool))
          (some false :: none :: baseTail) =
        none ::
          List.append (List.replicate blankCount none)
            (some false :: none :: baseTail) by
    rfl]
  rw [markerAwarePullNearestRawBitDescription_step_start]
  rw [runConfig_add]
  rw [markerAwarePullNearestRawBitDescription_run_scan_blanks]
  rw [runConfig_add]
  rw [markerAwarePullNearestRawBitDescription_step_candidate_false]
  rw [markerAwarePullNearestRawBitDescription_step_boundary_false]
  rfl

theorem markerAwarePullNearestRawBitDescription_run_boundary_true
    (blankCount : Nat) (baseTail : List (Option Bool))
    (tailFirst : Bool) (tail : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.runConfig
        (blankCount + 4)
        { state := markerAwarePullNearestRawBitDescription.start
          tape :=
            markerAwarePullNearestRawBitSourceTape
              blankCount (none :: baseTail) true tailFirst tail } =
      { state := markerAwarePullNearestRawBitDescription.halt
        tape :=
          markerAwarePullNearestBoundaryTargetTape
            blankCount baseTail true tailFirst tail } := by
  rw [show blankCount + 4 =
    1 + ((blankCount + 1) + (1 + 1)) by lia]
  rw [runConfig_add]
  change
    markerAwarePullNearestRawBitDescription.runConfig
        ((blankCount + 1) + (1 + 1))
        (markerAwarePullNearestRawBitDescription.runConfig 1
          { state := markerAwarePullNearestRawBitDescription.start
            tape :=
              tapeAtCells
                (List.append
                  (List.replicate (blankCount + 1)
                    (none : Option Bool))
                  (some true :: none :: baseTail))
                (some tailFirst :: tail) }) =
      { state := markerAwarePullNearestRawBitDescription.halt
        tape :=
          markerAwarePullNearestBoundaryTargetTape
            blankCount baseTail true tailFirst tail }
  rw [show
      List.replicate (blankCount + 1) (none : Option Bool) =
        none :: List.replicate blankCount none by
    rw [show blankCount + 1 = Nat.succ blankCount by lia]
    rfl]
  rw [show
      List.append
          (none :: List.replicate blankCount (none : Option Bool))
          (some true :: none :: baseTail) =
        none ::
          List.append (List.replicate blankCount none)
            (some true :: none :: baseTail) by
    rfl]
  rw [markerAwarePullNearestRawBitDescription_step_start]
  rw [runConfig_add]
  rw [markerAwarePullNearestRawBitDescription_run_scan_blanks]
  rw [runConfig_add]
  rw [markerAwarePullNearestRawBitDescription_step_candidate_true]
  rw [markerAwarePullNearestRawBitDescription_step_boundary_true]
  rfl

theorem markerAwarePullNearestRawBitDescription_run_real_false
    (blankCount : Nat) (leftBit : Bool)
    (baseTail : List (Option Bool))
    (tailFirst : Bool) (tail : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.runConfig
        (2 * (blankCount + 1) + 6)
        { state := markerAwarePullNearestRawBitDescription.start
          tape :=
            markerAwarePullNearestRawBitSourceTape
              blankCount (some leftBit :: baseTail) false
              tailFirst tail } =
      { state := markerAwarePullNearestRawBitDescription.halt
        tape :=
          markerAwarePullNearestRawBitTargetTape
            blankCount (some leftBit :: baseTail) false tailFirst tail } := by
  rw [show 2 * (blankCount + 1) + 6 =
    1 + ((blankCount + 1) + (1 + (1 + (1 +
      ((blankCount + 1) + (1 + 1)))))) by lia]
  rw [runConfig_add]
  change
    markerAwarePullNearestRawBitDescription.runConfig
        ((blankCount + 1) + (1 + (1 + (1 +
          ((blankCount + 1) + (1 + 1))))))
        (markerAwarePullNearestRawBitDescription.runConfig 1
          { state := markerAwarePullNearestRawBitDescription.start
            tape :=
              tapeAtCells
                (List.append
                  (List.replicate (blankCount + 1)
                    (none : Option Bool))
                  (some false :: some leftBit :: baseTail))
                (some tailFirst :: tail) }) =
      { state := markerAwarePullNearestRawBitDescription.halt
        tape :=
          markerAwarePullNearestRawBitTargetTape
            blankCount (some leftBit :: baseTail) false tailFirst tail }
  rw [show
      List.replicate (blankCount + 1) (none : Option Bool) =
        none :: List.replicate blankCount none by
    rw [show blankCount + 1 = Nat.succ blankCount by lia]
    rfl]
  rw [show
      List.append
          (none :: List.replicate blankCount (none : Option Bool))
          (some false :: some leftBit :: baseTail) =
        none ::
          List.append (List.replicate blankCount none)
            (some false :: some leftBit :: baseTail) by
    rfl]
  rw [markerAwarePullNearestRawBitDescription_step_start]
  rw [runConfig_add]
  rw [markerAwarePullNearestRawBitDescription_run_scan_blanks]
  rw [runConfig_add]
  rw [markerAwarePullNearestRawBitDescription_step_candidate_false]
  rw [runConfig_add]
  rw [markerAwarePullNearestRawBitDescription_step_real_false]
  rw [runConfig_add]
  rw [markerAwarePullNearestRawBitDescription_step_erase_false]
  rw [runConfig_add]
  rw [markerAwarePullNearestRawBitDescription_run_return_blanks_false]
  rw [runConfig_add]
  rw [show
      List.replicate (blankCount + 1) (none : Option Bool) =
        none :: List.replicate blankCount none by
    rw [show blankCount + 1 = Nat.succ blankCount by lia]
    rfl]
  rw [show
      List.append
          (none :: List.replicate blankCount (none : Option Bool))
          (none :: some leftBit :: baseTail) =
        none ::
          List.append (List.replicate blankCount none)
            (none :: some leftBit :: baseTail) by
    rfl]
  rw [markerAwarePullNearestRawBitDescription_step_tail_false]
  rw [markerAwarePullNearestRawBitDescription_step_write_false]
  rw [replicate_none_append_cons_eq]
  simp [markerAwarePullNearestRawBitTargetTape,
    pullNearestRawBitToTailMarkerTargetTape]

theorem markerAwarePullNearestRawBitDescription_run_real_true
    (blankCount : Nat) (leftBit : Bool)
    (baseTail : List (Option Bool))
    (tailFirst : Bool) (tail : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.runConfig
        (2 * (blankCount + 1) + 6)
        { state := markerAwarePullNearestRawBitDescription.start
          tape :=
            markerAwarePullNearestRawBitSourceTape
              blankCount (some leftBit :: baseTail) true
              tailFirst tail } =
      { state := markerAwarePullNearestRawBitDescription.halt
        tape :=
          markerAwarePullNearestRawBitTargetTape
            blankCount (some leftBit :: baseTail) true tailFirst tail } := by
  rw [show 2 * (blankCount + 1) + 6 =
    1 + ((blankCount + 1) + (1 + (1 + (1 +
      ((blankCount + 1) + (1 + 1)))))) by lia]
  rw [runConfig_add]
  change
    markerAwarePullNearestRawBitDescription.runConfig
        ((blankCount + 1) + (1 + (1 + (1 +
          ((blankCount + 1) + (1 + 1))))))
        (markerAwarePullNearestRawBitDescription.runConfig 1
          { state := markerAwarePullNearestRawBitDescription.start
            tape :=
              tapeAtCells
                (List.append
                  (List.replicate (blankCount + 1)
                    (none : Option Bool))
                  (some true :: some leftBit :: baseTail))
                (some tailFirst :: tail) }) =
      { state := markerAwarePullNearestRawBitDescription.halt
        tape :=
          markerAwarePullNearestRawBitTargetTape
            blankCount (some leftBit :: baseTail) true tailFirst tail }
  rw [show
      List.replicate (blankCount + 1) (none : Option Bool) =
        none :: List.replicate blankCount none by
    rw [show blankCount + 1 = Nat.succ blankCount by lia]
    rfl]
  rw [show
      List.append
          (none :: List.replicate blankCount (none : Option Bool))
          (some true :: some leftBit :: baseTail) =
        none ::
          List.append (List.replicate blankCount none)
            (some true :: some leftBit :: baseTail) by
    rfl]
  rw [markerAwarePullNearestRawBitDescription_step_start]
  rw [runConfig_add]
  rw [markerAwarePullNearestRawBitDescription_run_scan_blanks]
  rw [runConfig_add]
  rw [markerAwarePullNearestRawBitDescription_step_candidate_true]
  rw [runConfig_add]
  rw [markerAwarePullNearestRawBitDescription_step_real_true]
  rw [runConfig_add]
  rw [markerAwarePullNearestRawBitDescription_step_erase_true]
  rw [runConfig_add]
  rw [markerAwarePullNearestRawBitDescription_run_return_blanks_true]
  rw [runConfig_add]
  rw [show
      List.replicate (blankCount + 1) (none : Option Bool) =
        none :: List.replicate blankCount none by
    rw [show blankCount + 1 = Nat.succ blankCount by lia]
    rfl]
  rw [show
      List.append
          (none :: List.replicate blankCount (none : Option Bool))
          (none :: some leftBit :: baseTail) =
        none ::
          List.append (List.replicate blankCount none)
            (none :: some leftBit :: baseTail) by
    rfl]
  rw [markerAwarePullNearestRawBitDescription_step_tail_true]
  rw [markerAwarePullNearestRawBitDescription_step_write_true]
  rw [replicate_none_append_cons_eq]
  simp [markerAwarePullNearestRawBitTargetTape,
    pullNearestRawBitToTailMarkerTargetTape]

theorem markerAwarePullNearestRawBitDescription_haltsFromTape_real
    (blankCount : Nat) (leftBit rawBit : Bool)
    (baseTail : List (Option Bool))
    (tailFirst : Bool) (tail : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.HaltsFromTape
      (markerAwarePullNearestRawBitSourceTape
        blankCount (some leftBit :: baseTail) rawBit tailFirst tail)
      (markerAwarePullNearestRawBitTargetTape
        blankCount (some leftBit :: baseTail) rawBit tailFirst tail) := by
  cases rawBit
  · refine ⟨2 * (blankCount + 1) + 6, ?_⟩
    constructor <;>
      rw [markerAwarePullNearestRawBitDescription_run_real_false]
  · refine ⟨2 * (blankCount + 1) + 6, ?_⟩
    constructor <;>
      rw [markerAwarePullNearestRawBitDescription_run_real_true]

theorem markerAwarePullNearestRawBitDescription_haltsFromTape_boundary
    (blankCount : Nat) (baseTail : List (Option Bool))
    (markerBit tailFirst : Bool) (tail : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.HaltsFromTape
      (markerAwarePullNearestRawBitSourceTape
        blankCount (none :: baseTail) markerBit tailFirst tail)
      (markerAwarePullNearestBoundaryTargetTape
        blankCount baseTail markerBit tailFirst tail) := by
  cases markerBit
  · refine ⟨blankCount + 4, ?_⟩
    constructor <;>
      rw [markerAwarePullNearestRawBitDescription_run_boundary_false]
  · refine ⟨blankCount + 4, ?_⟩
    constructor <;>
      rw [markerAwarePullNearestRawBitDescription_run_boundary_true]

theorem markerAwarePullNearestRawBitDescription_run_headGapZero_real_false
    (leftBit : Bool) (baseTail : List (Option Bool))
    (headBit : Bool) (right : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.runConfig 6
        { state := markerAwarePullNearestRawBitDescription.start
          tape :=
            markerAwarePullNearestRawBitToHeadMarkerSourceTape
              0 (some leftBit :: baseTail) false headBit right } =
      { state := markerAwarePullNearestRawBitDescription.halt
        tape :=
          markerAwarePullNearestRawBitToHeadMarkerTargetTape
            0 (some leftBit :: baseTail) false headBit right } := by
  rw [show 6 = 1 + (1 + (1 + (1 + (1 + 1)))) by decide]
  rw [runConfig_add]
  rw [markerAwarePullNearestRawBitToHeadMarkerSourceTape,
    pullNearestRawBitToHeadMarkerSourceTape]
  change
    markerAwarePullNearestRawBitDescription.runConfig
        (1 + (1 + (1 + (1 + 1))))
        (markerAwarePullNearestRawBitDescription.runConfig 1
          { state := markerAwarePullNearestRawBitDescription.start
            tape := tapeAtCells (some false :: some leftBit :: baseTail)
              (some headBit :: right) }) =
      { state := markerAwarePullNearestRawBitDescription.halt
        tape :=
          markerAwarePullNearestRawBitToHeadMarkerTargetTape
            0 (some leftBit :: baseTail) false headBit right }
  rw [markerAwarePullNearestRawBitDescription_step_start_adjacent]
  rw [runConfig_add]
  rw [markerAwarePullNearestRawBitDescription_step_candidate_false]
  rw [runConfig_add]
  rw [markerAwarePullNearestRawBitDescription_step_real_false]
  rw [runConfig_add]
  rw [markerAwarePullNearestRawBitDescription_step_erase_false]
  rw [runConfig_add]
  rw [markerAwarePullNearestRawBitDescription_step_tail_false]
  rw [markerAwarePullNearestRawBitDescription_step_write_false]
  simp [markerAwarePullNearestRawBitToHeadMarkerTargetTape,
    pullNearestRawBitToHeadMarkerTargetTape]

theorem markerAwarePullNearestRawBitDescription_run_headGapZero_real_true
    (leftBit : Bool) (baseTail : List (Option Bool))
    (headBit : Bool) (right : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.runConfig 6
        { state := markerAwarePullNearestRawBitDescription.start
          tape :=
            markerAwarePullNearestRawBitToHeadMarkerSourceTape
              0 (some leftBit :: baseTail) true headBit right } =
      { state := markerAwarePullNearestRawBitDescription.halt
        tape :=
          markerAwarePullNearestRawBitToHeadMarkerTargetTape
            0 (some leftBit :: baseTail) true headBit right } := by
  rw [show 6 = 1 + (1 + (1 + (1 + (1 + 1)))) by decide]
  rw [runConfig_add]
  rw [markerAwarePullNearestRawBitToHeadMarkerSourceTape,
    pullNearestRawBitToHeadMarkerSourceTape]
  change
    markerAwarePullNearestRawBitDescription.runConfig
        (1 + (1 + (1 + (1 + 1))))
        (markerAwarePullNearestRawBitDescription.runConfig 1
          { state := markerAwarePullNearestRawBitDescription.start
            tape := tapeAtCells (some true :: some leftBit :: baseTail)
              (some headBit :: right) }) =
      { state := markerAwarePullNearestRawBitDescription.halt
        tape :=
          markerAwarePullNearestRawBitToHeadMarkerTargetTape
            0 (some leftBit :: baseTail) true headBit right }
  rw [markerAwarePullNearestRawBitDescription_step_start_adjacent]
  rw [runConfig_add]
  rw [markerAwarePullNearestRawBitDescription_step_candidate_true]
  rw [runConfig_add]
  rw [markerAwarePullNearestRawBitDescription_step_real_true]
  rw [runConfig_add]
  rw [markerAwarePullNearestRawBitDescription_step_erase_true]
  rw [runConfig_add]
  rw [markerAwarePullNearestRawBitDescription_step_tail_true]
  rw [markerAwarePullNearestRawBitDescription_step_write_true]
  simp [markerAwarePullNearestRawBitToHeadMarkerTargetTape,
    pullNearestRawBitToHeadMarkerTargetTape]

theorem markerAwarePullNearestRawBitDescription_run_headGapZero_boundary_false
    (baseTail : List (Option Bool))
    (headBit : Bool) (right : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.runConfig 3
        { state := markerAwarePullNearestRawBitDescription.start
          tape :=
            markerAwarePullNearestRawBitToHeadMarkerSourceTape
              0 (none :: baseTail) false headBit right } =
      { state := markerAwarePullNearestRawBitDescription.halt
        tape :=
          markerAwarePullNearestBoundaryToHeadMarkerTargetTape
            0 baseTail false headBit right } := by
  rw [show 3 = 1 + (1 + 1) by decide]
  rw [runConfig_add]
  rw [markerAwarePullNearestRawBitToHeadMarkerSourceTape,
    pullNearestRawBitToHeadMarkerSourceTape]
  change
    markerAwarePullNearestRawBitDescription.runConfig (1 + 1)
        (markerAwarePullNearestRawBitDescription.runConfig 1
          { state := markerAwarePullNearestRawBitDescription.start
            tape := tapeAtCells (some false :: none :: baseTail)
              (some headBit :: right) }) =
      { state := markerAwarePullNearestRawBitDescription.halt
        tape :=
          markerAwarePullNearestBoundaryToHeadMarkerTargetTape
            0 baseTail false headBit right }
  rw [markerAwarePullNearestRawBitDescription_step_start_adjacent]
  rw [runConfig_add]
  rw [markerAwarePullNearestRawBitDescription_step_candidate_false]
  rw [markerAwarePullNearestRawBitDescription_step_boundary_false]
  rfl

theorem markerAwarePullNearestRawBitDescription_run_headGapZero_boundary_true
    (baseTail : List (Option Bool))
    (headBit : Bool) (right : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.runConfig 3
        { state := markerAwarePullNearestRawBitDescription.start
          tape :=
            markerAwarePullNearestRawBitToHeadMarkerSourceTape
              0 (none :: baseTail) true headBit right } =
      { state := markerAwarePullNearestRawBitDescription.halt
        tape :=
          markerAwarePullNearestBoundaryToHeadMarkerTargetTape
            0 baseTail true headBit right } := by
  rw [show 3 = 1 + (1 + 1) by decide]
  rw [runConfig_add]
  rw [markerAwarePullNearestRawBitToHeadMarkerSourceTape,
    pullNearestRawBitToHeadMarkerSourceTape]
  change
    markerAwarePullNearestRawBitDescription.runConfig (1 + 1)
        (markerAwarePullNearestRawBitDescription.runConfig 1
          { state := markerAwarePullNearestRawBitDescription.start
            tape := tapeAtCells (some true :: none :: baseTail)
              (some headBit :: right) }) =
      { state := markerAwarePullNearestRawBitDescription.halt
        tape :=
          markerAwarePullNearestBoundaryToHeadMarkerTargetTape
            0 baseTail true headBit right }
  rw [markerAwarePullNearestRawBitDescription_step_start_adjacent]
  rw [runConfig_add]
  rw [markerAwarePullNearestRawBitDescription_step_candidate_true]
  rw [markerAwarePullNearestRawBitDescription_step_boundary_true]
  rfl

theorem markerAwarePullNearestRawBitDescription_haltsFromHeadGap_real
    (gap : Nat) (leftBit rawBit headBit : Bool)
    (baseTail : List (Option Bool))
    (right : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.HaltsFromTape
      (markerAwarePullNearestRawBitToHeadMarkerSourceTape
        gap (some leftBit :: baseTail) rawBit headBit right)
      (markerAwarePullNearestRawBitToHeadMarkerTargetTape
        gap (some leftBit :: baseTail) rawBit headBit right) := by
  cases gap with
  | zero =>
      cases rawBit
      · refine ⟨6, ?_⟩
        constructor <;>
          rw [markerAwarePullNearestRawBitDescription_run_headGapZero_real_false]
      · refine ⟨6, ?_⟩
        constructor <;>
          rw [markerAwarePullNearestRawBitDescription_run_headGapZero_real_true]
  | succ blankCount =>
      simpa [markerAwarePullNearestRawBitToHeadMarkerSourceTape,
        markerAwarePullNearestRawBitToHeadMarkerTargetTape,
        pullNearestRawBitToHeadMarkerSourceTape,
        pullNearestRawBitToHeadMarkerTargetTape,
        markerAwarePullNearestRawBitSourceTape,
        markerAwarePullNearestRawBitTargetTape] using!
        markerAwarePullNearestRawBitDescription_haltsFromTape_real
          blankCount leftBit rawBit baseTail headBit right

theorem markerAwarePullNearestRawBitDescription_haltsFromHeadGap_boundary
    (gap : Nat) (baseTail : List (Option Bool))
    (markerBit headBit : Bool) (right : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.HaltsFromTape
      (markerAwarePullNearestRawBitToHeadMarkerSourceTape
        gap (none :: baseTail) markerBit headBit right)
      (markerAwarePullNearestBoundaryToHeadMarkerTargetTape
        gap baseTail markerBit headBit right) := by
  cases gap with
  | zero =>
      cases markerBit
      · refine ⟨3, ?_⟩
        constructor <;>
          rw [markerAwarePullNearestRawBitDescription_run_headGapZero_boundary_false]
      · refine ⟨3, ?_⟩
        constructor <;>
          rw [markerAwarePullNearestRawBitDescription_run_headGapZero_boundary_true]
  | succ blankCount =>
      simpa [markerAwarePullNearestRawBitToHeadMarkerSourceTape,
        markerAwarePullNearestBoundaryToHeadMarkerTargetTape,
        pullNearestRawBitToHeadMarkerSourceTape,
        markerAwarePullNearestRawBitSourceTape,
        markerAwarePullNearestBoundaryTargetTape] using!
        markerAwarePullNearestRawBitDescription_haltsFromTape_boundary
          blankCount baseTail markerBit headBit right

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
