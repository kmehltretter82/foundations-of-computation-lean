import FoC.Computability.Compiler.ClosedCfg.ProjTail.SelectedFootprintCompactionShape
import FoC.Computability.Compiler.Structured.Lowering.PairEncodedOptionCellCompactor.Base

set_option doc.verso true

/-!
# Marker-delimited selected-footprint compactor

This finite machine compacts the live pair-encoded selected footprint after
the preceding structured-prefix eraser has installed the collision-safe
{lit}`[true, false]` left sentinel. It builds the decoded cell stream from
right to left between moving markers, erases all temporary markers, and halts
on the payload separator. The result is stated modulo tape equivalence, the
contract currency used by the downstream right-edge rewind phase.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup
namespace LiveIngress
namespace MarkerCompactor

def reversePairs : List (Option Bool) -> List (Option Bool)
  | [] => []
  | cell :: rest => cell :: none :: reversePairs rest

def storedState : Option Bool -> Nat
  | none => 20
  | some false => 21
  | some true => 22

def toOldMarkerState : Option Bool -> Nat
  | none => 23
  | some false => 24
  | some true => 25

def eraseOldMarkerOneState : Option Bool -> Nat
  | none => 26
  | some false => 27
  | some true => 28

def eraseOldMarkerTwoState : Option Bool -> Nat
  | none => 29
  | some false => 30
  | some true => 31

def scanGapState : Option Bool -> Nat
  | none => 32
  | some false => 33
  | some true => 34

def atOutputMarkerTwoState : Option Bool -> Nat
  | none => 35
  | some false => 36
  | some true => 37

def atOutputMarkerOneState : Option Bool -> Nat
  | none => 38
  | some false => 39
  | some true => 40

def atOutputGapState : Option Bool -> Nat
  | none => 41
  | some false => 42
  | some true => 43

def shiftedOutputMarkerOneState : Option Bool -> Nat
  | none => 44
  | some false => 45
  | some true => 46

def oldOutputMarkerTwoState : Option Bool -> Nat
  | none => 47
  | some false => 48
  | some true => 49

def description : MachineDescription where
  stateCount := 71
  start := 0
  halt := 70
  transitions :=
    [ transition 0 none (some true) Direction.left 1
    , transition 1 none (some true) Direction.left 2
    , transition 2 none none Direction.right 3
    , transition 2 (some false) (some false) Direction.right 3
    , transition 2 (some true) (some true) Direction.right 3
    , transition 3 (some true) (some true) Direction.right 4
    , transition 4 (some true) (some true) Direction.right 5
    , transition 5 none none Direction.right 6
    , transition 6 none (some true) Direction.right 7
    , transition 7 none (some true) Direction.left 8
    , transition 8 (some true) (some true) Direction.left 9
    , transition 9 none none Direction.left 10
    , transition 10 (some true) (some true) Direction.left 11
    , transition 11 (some true) (some true) Direction.left 12

    , transition 12 none (some true) Direction.left 20
    , transition 12 (some false) (some true) Direction.left 21
    , transition 12 (some true) (some true) Direction.left 22
    , transition 20 none (some true) Direction.right 23
    , transition 21 none (some true) Direction.right 24
    , transition 22 none (some true) Direction.right 25
    , transition 23 (some true) (some true) Direction.right 26
    , transition 24 (some true) (some true) Direction.right 27
    , transition 25 (some true) (some true) Direction.right 28
    , transition 26 (some true) none Direction.right 29
    , transition 27 (some true) none Direction.right 30
    , transition 28 (some true) none Direction.right 31
    , transition 29 (some true) none Direction.right 32
    , transition 30 (some true) none Direction.right 33
    , transition 31 (some true) none Direction.right 34
    , transition 32 none none Direction.right 32
    , transition 33 none none Direction.right 33
    , transition 34 none none Direction.right 34
    , transition 32 (some true) (some true) Direction.right 35
    , transition 33 (some true) (some true) Direction.right 36
    , transition 34 (some true) (some true) Direction.right 37
    , transition 35 (some true) (some true) Direction.left 38
    , transition 36 (some true) (some true) Direction.left 39
    , transition 37 (some true) (some true) Direction.left 40
    , transition 38 (some true) (some true) Direction.left 41
    , transition 39 (some true) (some true) Direction.left 42
    , transition 40 (some true) (some true) Direction.left 43
    , transition 41 none (some true) Direction.right 44
    , transition 42 none (some true) Direction.right 45
    , transition 43 none (some true) Direction.right 46
    , transition 44 (some true) (some true) Direction.right 47
    , transition 45 (some true) (some true) Direction.right 48
    , transition 46 (some true) (some true) Direction.right 49
    , transition 47 (some true) none Direction.left 50
    , transition 48 (some true) (some false) Direction.left 50
    , transition 49 (some true) (some true) Direction.left 50
    , transition 50 (some true) (some true) Direction.left 51
    , transition 51 (some true) (some true) Direction.left 52
    , transition 52 none none Direction.left 52
    , transition 52 (some true) (some true) Direction.left 53
    , transition 53 (some true) (some true) Direction.left 54
    , transition 54 none none Direction.left 55
    , transition 54 (some false) (some false) Direction.left 56
    , transition 54 (some true) (some true) Direction.left 56
    , transition 55 none none Direction.right 12
    , transition 55 (some false) none Direction.left 60
    , transition 56 none none Direction.right 12

    , transition 60 (some true) none Direction.right 61
    , transition 61 none none Direction.right 62
    , transition 62 none none Direction.right 63
    , transition 63 (some true) none Direction.right 64
    , transition 64 (some true) none Direction.right 65
    , transition 65 none none Direction.right 65
    , transition 65 (some true) none Direction.right 66
    , transition 66 (some true) none Direction.right 67
    , transition 67 none none Direction.right 67
    , transition 67 (some false) (some false) Direction.right 68
    , transition 67 (some true) (some true) Direction.right 68
    , transition 68 (some false) (some false) Direction.right 68
    , transition 68 (some true) (some true) Direction.right 68
    , transition 68 none none Direction.right 69
    , transition 69 none none Direction.left 70
    , transition 69 (some false) (some false) Direction.left 70
    , transition 69 (some true) (some true) Direction.left 70 ]

theorem description_wellFormed : description.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := description.transitions)
      (stateCount := description.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := description.transitions)
      (by decide)

theorem description_haltTransitionFree : description.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := description.transitions)
    (state := description.halt)
    (by decide)

theorem description_subroutineReady : description.SubroutineReady :=
  ⟨description_wellFormed, description_haltTransitionFree⟩

def markerSourceTape (cells : List (Option Bool)) : Tape Bool :=
  rightEndCompactionSourceTape
    ([some true, some false, none] ++
      PairEncodedOptionCellCompactor.encodedCells cells ++ [none])

def retainedCells (bits : Word Bool)
    (padding : List (Option Bool)) : List (Option Bool) :=
  [none, none, none] ++ bits.map some ++ none :: padding

def liveCells (bits : Word Bool)
    (padding : List (Option Bool)) : List (Option Bool) :=
  retainedCells bits padding ++ [none]

theorem reversePairs_append (left right : List (Option Bool)) :
    reversePairs (left ++ right) =
      reversePairs left ++ reversePairs right := by
  induction left with
  | nil =>
      rfl
  | cons cell rest ih =>
      simp [reversePairs, ih]

theorem encodedCells_reverse (cells : List (Option Bool)) :
    (PairEncodedOptionCellCompactor.encodedCells cells).reverse =
      reversePairs cells.reverse := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      simp [PairEncodedOptionCellCompactor.encodedCells_cons,
        List.reverse_cons, reversePairs_append, reversePairs, ih,
        List.append_assoc]

theorem markerSourceTape_shape (bits : Word Bool)
    (padding : List (Option Bool)) :
    markerSourceTape (liveCells bits padding) =
      { left := none :: none :: none ::
          reversePairs (retainedCells bits padding).reverse ++
            [none, some false, some true]
        head := none
        right := [] } := by
  simp [markerSourceTape, liveCells,
    PairEncodedOptionCellCompactor.encodedCells_append,
    encodedCells_reverse, retainedCells,
    rightEndCompactionSourceTape, tapeAtCells,
    List.reverse_append, reversePairs_append, reversePairs,
    List.append_assoc]

def cycleTape (current : Option Bool)
    (remainingRev : List (Option Bool)) (gap : Nat)
    (output : List (Option Bool)) : Tape Bool :=
  { left := none :: reversePairs remainingRev ++
      [none, some false, some true]
    head := current
    right := [some true, some true] ++
      List.replicate gap none ++ [some true, some true] ++ output }

theorem frame_run (current : Option Bool)
    (remainingRev : List (Option Bool)) :
    description.runConfig 12
        { state := description.start
          tape :=
            { left := none :: current :: none :: reversePairs remainingRev ++
                [none, some false, some true]
              head := none
              right := [] } } =
      { state := 12
        tape := cycleTape current remainingRev 1 [] } := by
  cases current with
  | none =>
      simp [description, cycleTape, runConfig, stepConfig,
        lookupTransition, Matches, transition, Tape.read, Tape.write,
        Tape.move, Tape.moveLeft, Tape.moveRight]
  | some bit =>
      cases bit <;>
        simp [description, cycleTape, runConfig, stepConfig,
          lookupTransition, Matches, transition, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft, Tape.moveRight]

theorem frame_live_run (bits : Word Bool)
    (padding : List (Option Bool)) :
    description.runConfig 12
        { state := description.start
          tape := markerSourceTape (liveCells bits padding) } =
      { state := 12
        tape := cycleTape none (retainedCells bits padding).reverse 1 [] } := by
  rw [markerSourceTape_shape]
  exact frame_run none (retainedCells bits padding).reverse

theorem scan_gap_run (cell : Option Bool) (n : Nat)
    (left output : List (Option Bool)) :
    description.runConfig (n + 2)
        { state := scanGapState cell
          tape :=
            { left := left
              head := none
              right := List.replicate n none ++
                [some true, some true] ++ output } } =
      { state := atOutputMarkerTwoState cell
        tape :=
          { left := some true :: List.replicate (n + 1) none ++ left
            head := some true
            right := output } } := by
  induction n generalizing left with
  | zero =>
      cases cell with
      | none =>
          simp [description, scanGapState, atOutputMarkerTwoState,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveRight]
      | some bit =>
          cases bit <;>
            simp [description, scanGapState, atOutputMarkerTwoState,
              runConfig, stepConfig, lookupTransition, Matches, transition,
              Tape.read, Tape.write, Tape.move, Tape.moveRight]
  | succ n ih =>
      rw [show n + 1 + 2 = 1 + (n + 2) by lia]
      rw [runConfig_add]
      cases cell with
      | none =>
          simp only [scanGapState]
          rw [show description.runConfig 1
              { state := 32
                tape :=
                  { left := left
                    head := none
                    right := List.replicate (n + 1) none ++
                      [some true, some true] ++ output } } =
              { state := 32
                tape :=
                  { left := none :: left
                    head := none
                    right := List.replicate n none ++
                      [some true, some true] ++ output } } by
                simp [description, runConfig, stepConfig, lookupTransition,
                  Matches, transition, Tape.read, Tape.write, Tape.move,
                  Tape.moveRight, List.replicate_succ]]
          simp only [atOutputMarkerTwoState]
          have hih := ih (none :: left)
          simp only [scanGapState, atOutputMarkerTwoState] at hih
          rw [hih]
          congr 2
          exact
            congrArg (fun xs => some true :: xs)
              (list_replicate_append_self
                (none : Option Bool) (n + 1) left)
      | some bit =>
          cases bit with
          | false =>
              simp only [scanGapState]
              rw [show description.runConfig 1
                  { state := 33
                    tape :=
                      { left := left
                        head := none
                        right := List.replicate (n + 1) none ++
                          [some true, some true] ++ output } } =
                  { state := 33
                    tape :=
                      { left := none :: left
                        head := none
                        right := List.replicate n none ++
                          [some true, some true] ++ output } } by
                    simp [description, runConfig, stepConfig,
                      lookupTransition, Matches, transition, Tape.read,
                      Tape.write, Tape.move, Tape.moveRight,
                      List.replicate_succ]]
              simp only [atOutputMarkerTwoState]
              have hih := ih (none :: left)
              simp only [scanGapState, atOutputMarkerTwoState] at hih
              rw [hih]
              congr 2
              exact
                congrArg (fun xs => some true :: xs)
                  (list_replicate_append_self
                    (none : Option Bool) (n + 1) left)
          | true =>
              simp only [scanGapState]
              rw [show description.runConfig 1
                  { state := 34
                    tape :=
                      { left := left
                        head := none
                        right := List.replicate (n + 1) none ++
                          [some true, some true] ++ output } } =
                  { state := 34
                    tape :=
                      { left := none :: left
                        head := none
                        right := List.replicate n none ++
                          [some true, some true] ++ output } } by
                    simp [description, runConfig, stepConfig,
                      lookupTransition, Matches, transition, Tape.read,
                      Tape.write, Tape.move, Tape.moveRight,
                      List.replicate_succ]]
              simp only [atOutputMarkerTwoState]
              have hih := ih (none :: left)
              simp only [scanGapState, atOutputMarkerTwoState] at hih
              rw [hih]
              congr 2
              exact
                congrArg (fun xs => some true :: xs)
                  (list_replicate_append_self
                    (none : Option Bool) (n + 1) left)

theorem enter_gap_run (cell : Option Bool)
    (remainingRev : List (Option Bool)) (n : Nat)
    (output : List (Option Bool)) :
    description.runConfig 5
        { state := 12
          tape := cycleTape cell remainingRev (n + 1) output } =
      { state := scanGapState cell
        tape :=
          { left := [none, none, some true, some true] ++
              reversePairs remainingRev ++
                [none, some false, some true]
            head := none
            right := List.replicate n none ++
              [some true, some true] ++ output } } := by
  cases cell with
  | none =>
      simp [description, cycleTape, scanGapState,
        runConfig, stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
        List.replicate_succ, List.append_assoc]
  | some bit =>
      cases bit <;>
        simp [description, cycleTape, scanGapState,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
          List.replicate_succ, List.append_assoc]

theorem shift_output_run (cell : Option Bool) (n : Nat)
    (base output : List (Option Bool)) :
    description.runConfig 5
        { state := atOutputMarkerTwoState cell
          tape :=
            { left := some true :: List.replicate (n + 1) none ++ base
              head := some true
              right := output } } =
      { state := 50
        tape :=
          { left := some true :: List.replicate n none ++ base
            head := some true
            right := cell :: output } } := by
  cases cell with
  | none =>
      simp [description, atOutputMarkerTwoState,
        runConfig, stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
        List.replicate_succ]
  | some bit =>
      cases bit <;>
        simp [description, atOutputMarkerTwoState,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
          List.replicate_succ]

theorem return_scan_run (candidate : Option Bool) (n : Nat)
    (rest right : List (Option Bool)) :
    description.runConfig (n + 3)
        { state := 52
          tape :=
            { left := List.replicate n none ++
                [some true, some true, candidate] ++ rest
              head := none
              right := right } } =
      { state := 54
        tape :=
          { left := rest
            head := candidate
            right := [some true, some true] ++
              List.replicate (n + 1) none ++ right } } := by
  induction n generalizing rest right with
  | zero =>
      simp [description, runConfig, stepConfig, lookupTransition,
        Matches, transition, Tape.read, Tape.write, Tape.move,
        Tape.moveLeft]
  | succ n ih =>
      rw [show n + 1 + 3 = 1 + (n + 3) by lia]
      rw [runConfig_add]
      rw [show description.runConfig 1
          { state := 52
            tape :=
              { left := List.replicate (n + 1) none ++
                  [some true, some true, candidate] ++ rest
                head := none
                right := right } } =
          { state := 52
            tape :=
              { left := List.replicate n none ++
                  [some true, some true, candidate] ++ rest
                head := none
                right := none :: right } } by
            simp [description, runConfig, stepConfig, lookupTransition,
              Matches, transition, Tape.read, Tape.write, Tape.move,
              Tape.moveLeft, List.replicate_succ]]
      rw [ih rest (none :: right)]
      congr 2
      exact
        congrArg (fun xs => [some true, some true] ++ xs)
          (list_replicate_append_self
            (none : Option Bool) (n + 1) right)

theorem enter_return_scan_run (n : Nat)
    (base right : List (Option Bool)) :
    description.runConfig 2
        { state := 50
          tape :=
            { left := some true :: List.replicate (n + 1) none ++ base
              head := some true
              right := right } } =
      { state := 52
        tape :=
          { left := List.replicate n none ++ base
            head := none
            right := [some true, some true] ++ right } } := by
  simp [description, runConfig, stepConfig, lookupTransition,
    Matches, transition, Tape.read, Tape.write, Tape.move,
    Tape.moveLeft, List.replicate_succ]

theorem cycle_to_candidate_run (cell candidate : Option Bool)
    (rest : List (Option Bool)) (n : Nat)
    (output : List (Option Bool)) :
    description.runConfig (2 * n + 18)
        { state := 12
          tape := cycleTape cell (candidate :: rest) (n + 1) output } =
      { state := 54
        tape :=
          { left := none :: reversePairs rest ++
              [none, some false, some true]
            head := candidate
            right := [some true, some true] ++
              List.replicate (n + 2) none ++
                [some true, some true] ++ cell :: output } } := by
  rw [show 2 * n + 18 =
      5 + ((n + 2) + (5 + (2 + (n + 4)))) by lia]
  rw [runConfig_add]
  rw [enter_gap_run]
  rw [runConfig_add]
  rw [scan_gap_run]
  rw [runConfig_add]
  rw [shift_output_run]
  rw [runConfig_add]
  have henter :=
    enter_return_scan_run (n + 1)
      ([some true, some true, candidate, none] ++
        reversePairs rest ++ [none, some false, some true])
      (cell :: output)
  simp [list_replicate_add_append] at henter
  simp only [reversePairs, List.cons_append, List.append_assoc,
    List.nil_append]
  rw [henter]
  have hreturn :=
    return_scan_run candidate (n + 1)
      (none :: reversePairs rest ++ [none, some false, some true])
      ([some true, some true] ++ cell :: output)
  simpa [list_replicate_append_self,
    List.append_assoc] using hreturn

theorem dispatch_pair_run (candidate : Option Bool)
    (rest : List (Option Bool)) (gap : Nat)
    (output : List (Option Bool)) :
    description.runConfig 2
        { state := 54
          tape :=
            { left := none :: reversePairs rest ++
                [none, some false, some true]
              head := candidate
              right := [some true, some true] ++
                List.replicate gap none ++
                  [some true, some true] ++ output } } =
      { state := 12
        tape := cycleTape candidate rest gap output } := by
  cases candidate with
  | none =>
      simp [description, cycleTape, runConfig, stepConfig,
        lookupTransition, Matches, transition, Tape.read, Tape.write,
        Tape.move, Tape.moveLeft, Tape.moveRight]
  | some bit =>
      cases bit <;>
        simp [description, cycleTape, runConfig, stepConfig,
          lookupTransition, Matches, transition, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft, Tape.moveRight]

theorem cycle_run_cons (cell candidate : Option Bool)
    (rest : List (Option Bool)) (n : Nat)
    (output : List (Option Bool)) :
    description.runConfig (2 * n + 20)
        { state := 12
          tape := cycleTape cell (candidate :: rest) (n + 1) output } =
      { state := 12
        tape := cycleTape candidate rest (n + 2) (cell :: output) } := by
  rw [show 2 * n + 20 = (2 * n + 18) + 2 by lia]
  rw [runConfig_add]
  rw [cycle_to_candidate_run]
  exact dispatch_pair_run candidate rest (n + 2) (cell :: output)

theorem cycle_to_boundary_run (cell : Option Bool) (n : Nat)
    (output : List (Option Bool)) :
    description.runConfig (2 * n + 18)
        { state := 12
          tape := cycleTape cell [] (n + 1) output } =
      { state := 54
        tape :=
          { left := [some false, some true]
            head := none
            right := [some true, some true] ++
              List.replicate (n + 2) none ++
                [some true, some true] ++ cell :: output } } := by
  rw [show 2 * n + 18 =
      5 + ((n + 2) + (5 + (2 + (n + 4)))) by lia]
  rw [runConfig_add]
  rw [enter_gap_run]
  rw [runConfig_add]
  rw [scan_gap_run]
  rw [runConfig_add]
  rw [shift_output_run]
  rw [runConfig_add]
  have henter :=
    enter_return_scan_run (n + 1)
      [some true, some true, none, some false, some true]
      (cell :: output)
  simp [list_replicate_add_append] at henter
  simp only [reversePairs, List.append_nil, List.cons_append,
    List.append_assoc, List.nil_append]
  rw [henter]
  have hreturn :=
    return_scan_run none (n + 1)
      [some false, some true]
      ([some true, some true] ++ cell :: output)
  simpa [list_replicate_append_self,
    List.append_assoc] using hreturn

theorem boundary_enter_cleanup_run (n : Nat)
    (output : List (Option Bool)) :
    description.runConfig 7
        { state := 54
          tape :=
            { left := [some false, some true]
              head := none
              right := [some true, some true] ++
                List.replicate (n + 1) none ++
                  [some true, some true] ++ output } } =
      { state := 65
        tape :=
          { left := List.replicate 5 none
            head := none
            right := List.replicate n none ++
              [some true, some true] ++ output } } := by
  simp [description, runConfig, stepConfig, lookupTransition,
    Matches, transition, Tape.read, Tape.write, Tape.move,
    Tape.moveLeft, Tape.moveRight, List.replicate_succ,
    List.append_assoc]

theorem cleanup_scan_run (n : Nat) (left : List (Option Bool))
    (first : Option Bool) (rest : List (Option Bool)) :
    description.runConfig (n + 3)
        { state := 65
          tape :=
            { left := left
              head := none
              right := List.replicate n none ++
                [some true, some true, first] ++ rest } } =
      { state := 67
        tape :=
          { left := List.replicate (n + 3) none ++ left
            head := first
            right := rest } } := by
  induction n generalizing left with
  | zero =>
      simp [description, runConfig, stepConfig, lookupTransition,
        Matches, transition, Tape.read, Tape.write, Tape.move,
        Tape.moveRight]
  | succ n ih =>
      rw [show n + 1 + 3 = 1 + (n + 3) by lia]
      rw [runConfig_add]
      rw [show description.runConfig 1
          { state := 65
            tape :=
              { left := left
                head := none
                right := List.replicate (n + 1) none ++
                  [some true, some true, first] ++ rest } } =
          { state := 65
            tape :=
              { left := none :: left
                head := none
                right := List.replicate n none ++
                  [some true, some true, first] ++ rest } } by
            simp [description, runConfig, stepConfig, lookupTransition,
              Matches, transition, Tape.read, Tape.write, Tape.move,
              Tape.moveRight, List.replicate_succ]]
      have hih := ih (none :: left)
      rw [hih]
      congr 2
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (list_replicate_append_self
          (none : Option Bool) (n + 3) left)

theorem scan_output_bits_run (bits : Word Bool)
    (left padding : List (Option Bool)) :
    description.runConfig (bits.length + 2)
        { state := 68
          tape := tapeAtCells left (bits.map some ++ none :: padding) } =
      { state := 70
        tape := Tape.move Direction.left
          (Tape.move Direction.right
            (tapeAtCells (bits.reverse.map some ++ left)
              (none :: padding))) } := by
  induction bits generalizing left with
  | nil =>
      cases padding with
      | nil =>
          simp [description, tapeAtCells, runConfig, stepConfig,
            lookupTransition, Matches, transition, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft, Tape.moveRight]
      | cons cell padding =>
          cases cell with
          | none =>
              simp [description, tapeAtCells, runConfig, stepConfig,
                lookupTransition, Matches, transition, Tape.read,
                Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
          | some bit =>
              cases bit <;>
                simp [description, tapeAtCells, runConfig, stepConfig,
                  lookupTransition, Matches, transition, Tape.read,
                  Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 2 =
          1 + (rest.length + 2) by simp; lia]
      rw [runConfig_add]
      rw [show description.runConfig 1
          { state := 68
            tape := tapeAtCells left
              ((bit :: rest).map some ++ none :: padding) } =
          { state := 68
            tape := tapeAtCells (some bit :: left)
              (rest.map some ++ none :: padding) } by
            cases bit <;> cases rest <;>
              simp [description, tapeAtCells, runConfig, stepConfig,
                lookupTransition, Matches, transition, Tape.read,
                Tape.write, Tape.move, Tape.moveRight]]
      rw [ih (some bit :: left)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem start_output_bits_run (first : Bool) (rest : Word Bool)
    (left padding : List (Option Bool)) :
    description.runConfig (rest.length + 3)
        { state := 67
          tape := tapeAtCells left
            ((first :: rest).map some ++ none :: padding) } =
      { state := 70
        tape := Tape.move Direction.left
          (Tape.move Direction.right
            (tapeAtCells ((first :: rest).reverse.map some ++ left)
              (none :: padding))) } := by
  rw [show rest.length + 3 = 1 + (rest.length + 2) by lia]
  rw [runConfig_add]
  rw [show description.runConfig 1
      { state := 67
        tape := tapeAtCells left
          ((first :: rest).map some ++ none :: padding) } =
      { state := 68
        tape := tapeAtCells (some first :: left)
          (rest.map some ++ none :: padding) } by
        cases first <;> cases rest <;>
          simp [description, tapeAtCells, runConfig, stepConfig,
            lookupTransition, Matches, transition, Tape.read, Tape.write,
            Tape.move, Tape.moveRight]]
  rw [scan_output_bits_run rest (some first :: left) padding]
  simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem leading_three_blank_run (left : List (Option Bool))
    (first : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    description.runConfig 3
        { state := 67
          tape := tapeAtCells left
            ([none, none, none] ++
              (first :: rest).map some ++ none :: padding) } =
      { state := 67
        tape := tapeAtCells (List.replicate 3 none ++ left)
          ((first :: rest).map some ++ none :: padding) } := by
  simp [description, tapeAtCells, runConfig, stepConfig,
    lookupTransition, Matches, transition, Tape.read, Tape.write,
    Tape.move, Tape.moveRight]

theorem boundary_to_halt_run (first : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) (n : Nat) :
    description.runConfig (n + rest.length + 17)
        { state := 54
          tape :=
            { left := [some false, some true]
              head := none
              right := [some true, some true] ++
                List.replicate (n + 2) none ++
                  [some true, some true] ++
                    [none, none, none] ++
                      (first :: rest).map some ++
                        none :: padding ++ [none] } } =
      { state := 70
        tape := Tape.move Direction.left
          (Tape.move Direction.right
            (tapeAtCells
              ((first :: rest).reverse.map some ++
                List.replicate (n + 12) none)
              (none :: padding ++ [none]))) } := by
  rw [show n + rest.length + 17 =
      7 + ((n + 4) + (3 + (rest.length + 3))) by lia]
  rw [runConfig_add]
  have hboundary :=
    boundary_enter_cleanup_run (n + 1)
      ([none, none, none] ++
        (first :: rest).map some ++ none :: padding ++ [none])
  simp [Nat.add_assoc, List.append_assoc] at hboundary
  simp only [List.cons_append, List.nil_append, List.map_cons,
    List.append_assoc]
  rw [hboundary]
  rw [runConfig_add]
  have hcleanup :=
    cleanup_scan_run (n + 1) (List.replicate 5 none) none
      (none :: none :: some first ::
        (rest.map some ++ none :: (padding ++ [none])))
  simp [Nat.add_assoc, List.append_assoc] at hcleanup
  rw [hcleanup]
  rw [runConfig_add]
  have hlead :=
    leading_three_blank_run
      (List.replicate (n + 4) none ++ List.replicate 5 none)
      first rest (padding ++ [none])
  simp [tapeAtCells] at hlead
  rw [hlead]
  have hstart :=
    start_output_bits_run first rest
      (List.replicate 3 none ++
        (List.replicate (n + 4) none ++ List.replicate 5 none))
      (padding ++ [none])
  have hblanks :
      List.replicate 3 (none : Option Bool) ++
          (List.replicate (n + 4) none ++ List.replicate 5 none) =
        List.replicate (n + 12) none := by
    calc
      List.replicate 3 (none : Option Bool) ++
          (List.replicate (n + 4) none ++ List.replicate 5 none) =
        List.replicate (3 + (n + 4)) none ++
          List.replicate 5 none := by
            symm
            exact list_replicate_add_append
              (none : Option Bool) 3 (n + 4) (List.replicate 5 none)
      _ = List.replicate ((3 + (n + 4)) + 5) none := by
            symm
            simpa using list_replicate_add_append
              (none : Option Bool) (3 + (n + 4)) 5 []
      _ = List.replicate (n + 12) none := by congr 1 <;> lia
  have hleft :
      none :: none :: none ::
          (List.replicate (n + 4) none ++
            [none, none, none, none, none]) =
        List.replicate (n + 12) (none : Option Bool) := by
    simpa using hblanks
  rw [hleft]
  rw [hblanks] at hstart
  simpa [tapeAtCells, List.reverse_cons, List.map_append,
    List.append_assoc] using hstart

def cycleStepsFrom : Nat -> List (Option Bool) -> Nat
  | n, [] => 2 * n + 18
  | n, _ :: rest => 2 * n + 20 + cycleStepsFrom (n + 1) rest

def boundaryConfig (n : Nat) (output : List (Option Bool)) :
    Configuration :=
  { state := 54
    tape :=
      { left := [some false, some true]
        head := none
        right := [some true, some true] ++
          List.replicate (n + 2) none ++
            [some true, some true] ++ output } }

theorem process_to_boundary_run (current : Option Bool)
    (remainingRev : List (Option Bool)) (n : Nat)
    (output : List (Option Bool)) :
    description.runConfig (cycleStepsFrom n remainingRev)
        { state := 12
          tape := cycleTape current remainingRev (n + 1) output } =
      boundaryConfig (n + remainingRev.length)
        ((current :: remainingRev).reverse ++ output) := by
  induction remainingRev generalizing current n output with
  | nil =>
      simpa [cycleStepsFrom, boundaryConfig] using
        cycle_to_boundary_run current n output
  | cons next rest ih =>
      rw [cycleStepsFrom]
      rw [runConfig_add]
      rw [cycle_run_cons]
      have hih := ih next (n + 1) (current :: output)
      simpa [boundaryConfig, List.reverse_cons, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hih

def finalTape (bits : Word Bool)
    (padding : List (Option Bool)) : Tape Bool :=
  Tape.move Direction.left
    (Tape.move Direction.right
      (tapeAtCells
        (bits.reverse.map some ++
          List.replicate ((retainedCells bits padding).length + 12) none)
        (none :: padding ++ [none])))

theorem full_run (first : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    description.runConfig
        (12 +
          (cycleStepsFrom 0
              (retainedCells (first :: rest) padding).reverse +
            ((retainedCells (first :: rest) padding).length +
              rest.length + 17)))
        { state := description.start
          tape := markerSourceTape (liveCells (first :: rest) padding) } =
      { state := description.halt
        tape := finalTape (first :: rest) padding } := by
  rw [runConfig_add]
  rw [frame_live_run]
  rw [runConfig_add]
  have hprocess :=
    process_to_boundary_run none
      (retainedCells (first :: rest) padding).reverse 0 []
  simp [boundaryConfig, List.reverse_cons,
    List.append_assoc] at hprocess
  rw [hprocess]
  simpa [description, finalTape, retainedCells, Nat.succ_eq_add_one,
    Nat.add_assoc] using
    boundary_to_halt_run first rest padding
      (retainedCells (first :: rest) padding).length

theorem padded_target_equiv (bits : Word Bool)
    (padding : List (Option Bool)) (n : Nat) :
    Tape.Equiv
      (tapeAtCells
        (bits.reverse.map some ++ List.replicate n none)
        (none :: padding ++ [none]))
      (rightEdgeRewindSourceTape bits padding) := by
  simp [rightEdgeRewindSourceTape, tapeAtCells, Tape.Equiv,
    dropTrailingNone_append_replicate_none,
    FoC.Computability.dropTrailingNone_append_none]

theorem finalTape_equiv (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.Equiv (finalTape bits padding)
      (rightEdgeRewindSourceTape bits padding) := by
  exact Tape.Equiv.trans
    (moveLeft_moveRight_equiv_self
      (tapeAtCells
        (bits.reverse.map some ++
          List.replicate ((retainedCells bits padding).length + 12) none)
        (none :: padding ++ [none])))
    (padded_target_equiv bits padding
      ((retainedCells bits padding).length + 12))

theorem haltsFrom_markerSource (first : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    description.HaltsFromTapeEquiv
      (markerSourceTape (liveCells (first :: rest) padding))
      (rightEdgeRewindSourceTape (first :: rest) padding) := by
  refine ⟨finalTape (first :: rest) padding, ?_,
    finalTape_equiv (first :: rest) padding⟩
  refine
    ⟨12 +
        (cycleStepsFrom 0
            (retainedCells (first :: rest) padding).reverse +
          ((retainedCells (first :: rest) padding).length +
            rest.length + 17)),
      ?_⟩
  have hrun := full_run first rest padding
  exact ⟨congrArg (fun c => c.state) hrun,
    congrArg (fun c => c.tape) hrun⟩

theorem encodedCells_liveCells (first : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    PairEncodedOptionCellCompactor.encodedCells
        (liveCells (first :: rest) padding) =
      selectedSegmentLogicalTapeDecoderDensifierFootprintCells
        (first :: rest) padding := by
  simp [liveCells, retainedCells,
    PairEncodedOptionCellCompactor.encodedCells,
    selectedSegmentLogicalTapeDecoderDensifierFootprintCells,
    List.append_assoc]

theorem markerSourceTape_liveCells
    (useAccept : Bool) (L : DovetailLayout)
    (first : Bool) (rest : Word Bool)
    (hbits : ParsedLayoutBits L = first :: rest) :
    markerSourceTape
        (liveCells (ParsedLayoutBits L)
          (postFieldDecodedPrefixScanPadding useAccept L)) =
      countWindowPostFieldDecodedPrefixSelectedSegmentMarkedFootprintCompactorSourceTape
        useAccept L := by
  simp [hbits, markerSourceTape,
    countWindowPostFieldDecodedPrefixSelectedSegmentMarkedFootprintCompactorSourceTape,
    encodedCells_liveCells]

theorem description_liveSpec :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorSpec
      description := by
  refine ⟨description_subroutineReady, ?_⟩
  intro useAccept L
  rcases parsedLayoutBits_eq_false_false_tail L with ⟨tail, hbits⟩
  have hsource :=
    markerSourceTape_liveCells useAccept L false (false :: tail) hbits
  rw [← hsource]
  rw [hbits]
  simpa [countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorTargetTape,
    hbits] using
    haltsFrom_markerSource false (false :: tail)
      (postFieldDecodedPrefixScanPadding useAccept L)

end MarkerCompactor
end LiveIngress
end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
