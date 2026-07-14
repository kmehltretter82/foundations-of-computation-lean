import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.FieldDecomposition.CfgHitClose
import FoC.Computability.Compiler.Structured.Lowering.FiniteMachineTactics
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.OneGapCompactor

set_option doc.verso true

/-!
# Marked represented-boundary repair

This finite table consumes the temporary tape-0 boundary sentinel emitted by
{name (full := FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore.FieldDecomposition.MetadataPrefix.ConfigTapeAndHit.description)}`ConfigTapeAndHit.description`.  It erases the obsolete guarded tape-0
prefix, turns the sentinel into the canonical left guard, and removes encoded
blank residue beyond the two canonical tape-2 right guards.  It returns to the
new opening separator and exposes the canonical classified-loop encoding up to
ordinary physical tape equivalence.
-/

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
namespace FieldDecomposition.MetadataPrefix.ConfigTapeAndHit
namespace RepresentedBoundaryRepair

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open StructuredConstructionTargets.FuelOutputCore

/-- Physical boundary repair.  States 1--3 consume the tape-0 sentinel;
states 5--16 seek and prune the tape-2 tail; states 17--21 return to the new
opening separator. -/
def description : MachineDescription where
  stateCount := 23
  start := 0
  halt := 22
  transitions :=
    [ transition 0 none none Direction.right 1
    , transition 1 (some false) none Direction.right 2
    , transition 2 (some false) none Direction.right 1
    , transition 2 (some true) (some false) Direction.left 3
    , transition 3 none (some false) Direction.left 4
    , transition 4 none none Direction.right 5
    , transition 5 (some false) (some false) Direction.right 5
    , transition 5 (some true) (some true) Direction.right 5
    , transition 5 none none Direction.right 6
    , transition 6 (some false) (some false) Direction.right 6
    , transition 6 (some true) (some true) Direction.right 6
    , transition 6 none none Direction.right 7
    , transition 7 (some false) (some false) Direction.right 8
    , transition 7 (some true) (some true) Direction.right 9
    , transition 8 (some false) (some false) Direction.right 7
    , transition 8 (some true) (some true) Direction.right 7
    , transition 9 (some false) (some false) Direction.right 7
    , transition 9 (some true) (some true) Direction.right 10
    , transition 10 (some false) (some false) Direction.right 11
    , transition 10 (some true) (some true) Direction.right 11
    , transition 11 (some false) (some false) Direction.right 12
    , transition 11 (some true) (some true) Direction.right 12
    , transition 12 (some false) (some false) Direction.right 13
    , transition 13 (some false) (some false) Direction.right 14
    , transition 14 (some false) (some false) Direction.right 15
    , transition 15 (some false) (some false) Direction.right 16
    , transition 16 (some false) none Direction.right 16
    , transition 16 none none Direction.left 17
    , transition 17 none none Direction.left 17
    , transition 17 (some false) (some false) Direction.left 18
    , transition 17 (some true) (some true) Direction.left 18
    , transition 18 (some false) (some false) Direction.left 18
    , transition 18 (some true) (some true) Direction.left 18
    , transition 18 none none Direction.left 19
    , transition 19 (some false) (some false) Direction.left 19
    , transition 19 (some true) (some true) Direction.left 19
    , transition 19 none none Direction.left 20
    , transition 20 (some false) (some false) Direction.left 20
    , transition 20 (some true) (some true) Direction.left 20
    , transition 20 none none Direction.right 21
    , transition 21 (some false) (some false) Direction.left 22
    , transition 21 (some true) (some true) Direction.left 22 ]

theorem description_wellFormed : description.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := description.transitions) (stateCount := description.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := description.transitions) (by decide)

theorem description_haltTransitionFree : description.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := description.transitions) (state := description.halt) (by decide)

theorem description_subroutineReady : description.SubroutineReady :=
  ⟨description_wellFormed, description_haltTransitionFree⟩

private theorem run_open
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := description.start
          tape := tapeAtCells left (none :: right) } =
      { state := 1
        tape := tapeAtCells (none :: left) right } := by
  cases right <;> machine_step [description]

private theorem run_erase_pair
    (left suffix : List (Option Bool)) :
    description.runConfig 2
        { state := 1
          tape := tapeAtCells left
            (some false :: some false :: suffix) } =
      { state := 1
        tape := tapeAtCells (none :: none :: left) suffix } := by
  cases suffix <;> machine_step [description]

private def erasedPairLeft : Nat → List (Option Bool) → List (Option Bool)
  | 0, left => left
  | n + 1, left => erasedPairLeft n (none :: none :: left)

private theorem run_erase_pairs
    (n : Nat) (left suffix : List (Option Bool)) :
    description.runConfig (2 * n)
        { state := 1
          tape := tapeAtCells left
            (List.append
              (List.replicate (2 * n) (some false : Option Bool))
              suffix) } =
      { state := 1
        tape := tapeAtCells (erasedPairLeft n left) suffix } := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
      rw [show 2 * (n + 1) = 2 + 2 * n by lia]
      rw [MachineDescription.runConfig_add]
      have hrep :
          List.replicate (2 + 2 * n) (some false : Option Bool) =
            some false :: some false ::
              List.replicate (2 * n) (some false : Option Bool) := by
        simpa using
          (FoC.Computability.list_replicate_add_append
            (some false : Option Bool) 2 (2 * n) [])
      rw [hrep]
      change
        description.runConfig (2 * n)
            (description.runConfig 2
              { state := 1
                tape := tapeAtCells left
                  (some false :: some false ::
                    List.append
                      (List.replicate (2 * n)
                        (some false : Option Bool)) suffix) }) = _
      rw [run_erase_pair]
      exact ih (none :: none :: left)

private theorem logicalCellListCode_eq_replicate_false_of_allNone
    (cells : List (Option Bool)) (h : AllNone cells) :
    logicalCellListCode cells =
      List.replicate (2 * cells.length) (some false : Option Bool) := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
      have hcell : cell = none := h cell (List.mem_cons.mpr (Or.inl rfl))
      have hrest : AllNone rest := by
        intro other hother
        exact h other (List.mem_cons.mpr (Or.inr hother))
      subst cell
      rw [logicalCellListCode_cons, logicalCellCode_none, ih hrest]
      simp [List.replicate_succ, Nat.mul_add]

private theorem run_sentinel_and_enter
    (older suffix : List (Option Bool)) :
    description.runConfig 4
        { state := 1
          tape := tapeAtCells (none :: older)
            (some false :: some true :: suffix) } =
      { state := 5
        tape := tapeAtCells (none :: older)
          (some false :: some false :: suffix) } := by
  cases older <;> cases suffix <;> machine_step [description]

private theorem run_scan_tape0
    (bits : Word Bool) (left suffix : List (Option Bool)) :
    description.runConfig (bits.length + 1)
        { state := 5
          tape := tapeAtCells left
            (List.append (bits.map some) (none :: suffix)) } =
      { state := 6
        tape := tapeAtCells
          (none :: List.append (bits.reverse.map some) left)
          suffix } := by
  induction bits generalizing left with
  | nil =>
      cases suffix <;> machine_step [description]
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 =
          1 + (rest.length + 1) by simp; lia]
      rw [MachineDescription.runConfig_add]
      have hstep :
          description.runConfig 1
              { state := 5
                tape := tapeAtCells left
                  (List.append ((bit :: rest).map some)
                    (none :: suffix)) } =
            { state := 5
              tape := tapeAtCells (some bit :: left)
                (List.append (rest.map some) (none :: suffix)) } := by
        cases bit <;> cases rest <;> cases suffix <;>
          machine_step [description]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: left)

private theorem run_scan_tape1
    (bits : Word Bool) (left suffix : List (Option Bool)) :
    description.runConfig (bits.length + 1)
        { state := 6
          tape := tapeAtCells left
            (List.append (bits.map some) (none :: suffix)) } =
      { state := 7
        tape := tapeAtCells
          (none :: List.append (bits.reverse.map some) left)
          suffix } := by
  induction bits generalizing left with
  | nil =>
      cases suffix <;> machine_step [description]
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 =
          1 + (rest.length + 1) by simp; lia]
      rw [MachineDescription.runConfig_add]
      have hstep :
          description.runConfig 1
              { state := 6
                tape := tapeAtCells left
                  (List.append ((bit :: rest).map some)
                    (none :: suffix)) } =
            { state := 6
              tape := tapeAtCells (some bit :: left)
                (List.append (rest.map some) (none :: suffix)) } := by
        cases bit <;> cases rest <;> cases suffix <;>
          machine_step [description]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: left)

private theorem run_tape2_cell
    (cell : Option Bool) (left suffix : List (Option Bool)) :
    description.runConfig 2
        { state := 7
          tape := tapeAtCells left
            (List.append (logicalCellCode cell) suffix) } =
      { state := 7
        tape := tapeAtCells
          (List.append (logicalCellCode cell).reverse left) suffix } := by
  cases cell with
  | none =>
      simp only [logicalCellCode_none]
      cases suffix <;> machine_step [description]
  | some bit =>
      cases bit with
      | false =>
          simp only [logicalCellCode_some_false]
          cases suffix <;> machine_step [description]
      | true =>
          simp only [logicalCellCode_some_true]
          cases suffix <;> machine_step [description]

private theorem run_tape2_cells
    (cells : List (Option Bool))
    (left suffix : List (Option Bool)) :
    description.runConfig (2 * cells.length)
        { state := 7
          tape := tapeAtCells left
            (List.append (logicalCellListCode cells) suffix) } =
      { state := 7
        tape := tapeAtCells
          (List.append (logicalCellListCode cells).reverse left) suffix } := by
  induction cells generalizing left with
  | nil => rfl
  | cons cell rest ih =>
      rw [show 2 * (cell :: rest).length =
          2 + 2 * rest.length by simp [Nat.mul_add]; lia]
      rw [MachineDescription.runConfig_add]
      simp only [logicalCellListCode_cons]
      have hassoc :
          List.append
              (List.append (logicalCellCode cell)
                (logicalCellListCode rest)) suffix =
            List.append (logicalCellCode cell)
              (List.append (logicalCellListCode rest) suffix) := by
        simp [List.append_assoc]
      rw [hassoc]
      rw [run_tape2_cell]
      simpa [List.reverse_append, List.append_assoc] using
        ih (List.append (logicalCellCode cell).reverse left)

private theorem run_tape2_marker
    (left suffix : List (Option Bool)) :
    description.runConfig 2
        { state := 7
          tape := tapeAtCells left
            (List.append headMarkerCells suffix) } =
      { state := 10
        tape := tapeAtCells
          (List.append headMarkerCells.reverse left) suffix } := by
  simp only [headMarkerCells]
  cases suffix <;> machine_step [description]

private theorem run_scan_tape2_to_head
    (cells : List (Option Bool))
    (left suffix : List (Option Bool)) :
    description.runConfig (2 * cells.length + 2)
        { state := 7
          tape := tapeAtCells left
            (List.append (logicalCellListCode cells)
              (List.append headMarkerCells suffix)) } =
      { state := 10
        tape := tapeAtCells
          (List.append headMarkerCells.reverse
            (List.append (logicalCellListCode cells).reverse left))
          suffix } := by
  rw [MachineDescription.runConfig_add]
  rw [run_tape2_cells]
  exact run_tape2_marker _ _

private theorem run_skip_head_and_guards
    (head : Option Bool) (left suffix : List (Option Bool)) :
    description.runConfig 6
        { state := 10
          tape := tapeAtCells left
            (List.append (logicalCellCode head)
              (some false :: some false :: some false :: some false ::
                suffix)) } =
      { state := 16
        tape := tapeAtCells
          (some false :: some false :: some false :: some false ::
            List.append (logicalCellCode head).reverse left)
          suffix } := by
  cases head with
  | none =>
      simp only [logicalCellCode_none]
      cases suffix <;> machine_step [description]
  | some bit =>
      cases bit with
      | false =>
          simp only [logicalCellCode_some_false]
          cases suffix <;> machine_step [description]
      | true =>
          simp only [logicalCellCode_some_true]
          cases suffix <;> machine_step [description]

private def erasedCellLeft : Nat → List (Option Bool) → List (Option Bool)
  | 0, left => left
  | n + 1, left => erasedCellLeft n (none :: left)

private theorem run_erase_false_step
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := 16
          tape := tapeAtCells left (some false :: right) } =
      { state := 16
        tape := tapeAtCells (none :: left) right } := by
  cases right <;> machine_step [description]

private theorem run_erase_false_cells
    (n : Nat) (left suffix : List (Option Bool)) :
    description.runConfig n
        { state := 16
          tape := tapeAtCells left
            (List.append
              (List.replicate n (some false : Option Bool)) suffix) } =
      { state := 16
        tape := tapeAtCells (erasedCellLeft n left) suffix } := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
      rw [show n + 1 = 1 + n by lia]
      rw [MachineDescription.runConfig_add]
      have hrep :
          List.replicate (1 + n) (some false : Option Bool) =
            some false ::
              List.replicate n (some false : Option Bool) := by
        simpa using
          (FoC.Computability.list_replicate_add_append
            (some false : Option Bool) 1 n [])
      rw [hrep]
      change
        description.runConfig n
            (description.runConfig 1
              { state := 16
                tape := tapeAtCells left
                  (some false ::
                    List.append
                      (List.replicate n (some false : Option Bool))
                      suffix) }) = _
      rw [run_erase_false_step]
      have herased :
          erasedCellLeft (1 + n) left =
            erasedCellLeft n (none :: left) := by
        rw [show 1 + n = n + 1 by lia]
        rfl
      rw [herased]
      exact ih (none :: left)

private theorem erasedCellLeft_eq
    (n : Nat) (left : List (Option Bool)) :
    erasedCellLeft n left =
      List.append (List.replicate n none) left := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
      rw [erasedCellLeft, ih]
      exact
        FoC.Computability.list_replicate_append_self
          (none : Option Bool) n left

private theorem run_state16_blank_left
    (full right : List (Option Bool)) (hfull : full ≠ []) :
    description.runConfig 1
        { state := 16
          tape := tapeAtCells full (none :: right) } =
      { state := 17
        tape := headTape full (none :: right) } := by
  cases full with
  | nil => contradiction
  | cons previous rest =>
      cases previous <;> cases rest <;> cases right <;>
        machine_step [description, headTape]

private theorem run_state17_blank_left
    (full right : List (Option Bool)) (hfull : full ≠ []) :
    description.runConfig 1
        { state := 17
          tape := tapeAtCells full (none :: right) } =
      { state := 17
        tape := headTape full (none :: right) } := by
  cases full with
  | nil => contradiction
  | cons previous rest =>
      cases previous <;> cases rest <;> cases right <;>
        machine_step [description, headTape]

private theorem run_rewind_state17
    (n : Nat) (last current : Bool)
    (earlier padding : List (Option Bool)) :
    description.runConfig (n + 1)
        { state := 17
          tape := headTape
            (List.append (List.replicate n none)
              (some last :: some current :: earlier))
            (none :: padding) } =
      { state := 18
        tape := tapeAtCells earlier
          (some current :: some last ::
            List.append (List.replicate (n + 1) none) padding) } := by
  induction n generalizing padding with
  | zero =>
      cases last <;> cases current <;> cases earlier <;> cases padding <;>
        machine_step [description, headTape]
  | succ n ih =>
      rw [show n + 1 + 1 = 1 + (n + 1) by lia]
      rw [MachineDescription.runConfig_add]
      have hsource :
          headTape
              (List.append (List.replicate (n + 1) none)
                (some last :: some current :: earlier))
              (none :: padding) =
            tapeAtCells
              (List.append (List.replicate n none)
                (some last :: some current :: earlier))
              (none :: none :: padding) := by
        simp [headTape, List.replicate_succ]
      rw [hsource]
      have hstep :
          description.runConfig 1
              { state := 17
                tape := tapeAtCells
                  (List.append (List.replicate n none)
                    (some last :: some current :: earlier))
                  (none :: none :: padding) } =
            { state := 17
              tape := headTape
                (List.append (List.replicate n none)
                  (some last :: some current :: earlier))
                (none :: none :: padding) } := by
        exact run_state17_blank_left _ _ (by simp)
      rw [hstep]
      have hpadding :
          List.append (List.replicate (n + 1) none) (none :: padding) =
            List.append (List.replicate (1 + (n + 1)) none) padding := by
        calc
          List.append (List.replicate (n + 1) none) (none :: padding) =
              List.append (List.replicate ((n + 1) + 1) none) padding :=
            FoC.Computability.list_replicate_append_self
              (none : Option Bool) (n + 1) padding
          _ = List.append (List.replicate (1 + (n + 1)) none) padding := by
            congr 2
            lia
      have hrun := ih (none :: padding)
      rw [hpadding] at hrun
      exact hrun

private theorem run_finish_tail_and_rewind
    (n : Nat) (last current : Bool)
    (earlier padding : List (Option Bool)) :
    description.runConfig (2 * n + 2)
        { state := 16
          tape := tapeAtCells
            (some last :: some current :: earlier)
            (List.append
              (List.replicate n (some false : Option Bool))
              (none :: padding)) } =
      { state := 18
        tape := tapeAtCells earlier
          (some current :: some last ::
            List.append (List.replicate (n + 1) none) padding) } := by
  rw [show 2 * n + 2 = n + (n + 2) by lia]
  rw [MachineDescription.runConfig_add]
  rw [run_erase_false_cells]
  rw [erasedCellLeft_eq]
  rw [show n + 2 = 1 + (n + 1) by lia]
  rw [MachineDescription.runConfig_add]
  have hstep :
      description.runConfig 1
          { state := 16
            tape := tapeAtCells
              (List.append (List.replicate n none)
                (some last :: some current :: earlier))
              (none :: padding) } =
        { state := 17
          tape := headTape
            (List.append (List.replicate n none)
              (some last :: some current :: earlier))
            (none :: padding) } := by
    exact run_state16_blank_left _ _ (by simp)
  rw [hstep]
  exact run_rewind_state17 n last current earlier padding

private theorem run_scan_left_tape2
    (leftStack : Word Bool) (current : Bool)
    (baseLeft right : List (Option Bool)) (hbase : baseLeft ≠ []) :
    description.runConfig (leftStack.length + 2)
        { state := 18
          tape := tapeAtCells
            (List.append (leftStack.map some) (none :: baseLeft))
            (some current :: right) } =
      { state := 19
        tape := headTape baseLeft
          (none ::
            List.append
              ((List.append leftStack.reverse [current]).map some) right) } := by
  induction leftStack generalizing current right with
  | nil =>
      cases baseLeft with
      | nil => contradiction
      | cons previous rest =>
          cases previous <;> cases current <;> cases rest <;> cases right <;>
            machine_step [description, headTape]
  | cons next rest ih =>
      rw [show (next :: rest).length + 2 =
          1 + (rest.length + 2) by simp; lia]
      rw [MachineDescription.runConfig_add]
      have hstep :
          description.runConfig 1
              { state := 18
                tape := tapeAtCells
                  (List.append ((next :: rest).map some)
                    (none :: baseLeft))
                  (some current :: right) } =
            { state := 18
              tape := tapeAtCells
                (List.append (rest.map some) (none :: baseLeft))
                (some next :: some current :: right) } := by
        cases next <;> cases current <;> cases rest <;> cases right <;>
          machine_step [description]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih next (some current :: right)

private theorem run_scan_left_tape1
    (leftStack : Word Bool) (current : Bool)
    (baseLeft right : List (Option Bool)) (hbase : baseLeft ≠ []) :
    description.runConfig (leftStack.length + 2)
        { state := 19
          tape := tapeAtCells
            (List.append (leftStack.map some) (none :: baseLeft))
            (some current :: right) } =
      { state := 20
        tape := headTape baseLeft
          (none ::
            List.append
              ((List.append leftStack.reverse [current]).map some) right) } := by
  induction leftStack generalizing current right with
  | nil =>
      cases baseLeft with
      | nil => contradiction
      | cons previous rest =>
          cases previous <;> cases current <;> cases rest <;> cases right <;>
            machine_step [description, headTape]
  | cons next rest ih =>
      rw [show (next :: rest).length + 2 =
          1 + (rest.length + 2) by simp; lia]
      rw [MachineDescription.runConfig_add]
      have hstep :
          description.runConfig 1
              { state := 19
                tape := tapeAtCells
                  (List.append ((next :: rest).map some)
                    (none :: baseLeft))
                  (some current :: right) } =
            { state := 19
              tape := tapeAtCells
                (List.append (rest.map some) (none :: baseLeft))
                (some next :: some current :: right) } := by
        cases next <;> cases current <;> cases rest <;> cases right <;>
          machine_step [description]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih next (some current :: right)

private theorem run_scan_left_tape0_and_halt
    (leftStack : Word Bool) (current : Bool)
    (blankLeft right : List (Option Bool)) :
    description.runConfig (leftStack.length + 3)
        { state := 20
          tape := tapeAtCells
            (List.append (leftStack.map some) (none :: blankLeft))
            (some current :: right) } =
      { state := description.halt
        tape := tapeAtCells blankLeft
          (none ::
            List.append
              ((List.append leftStack.reverse [current]).map some) right) } := by
  induction leftStack generalizing current right with
  | nil =>
      cases current <;> cases blankLeft <;> cases right <;>
        machine_step [description]
  | cons next rest ih =>
      rw [show (next :: rest).length + 3 =
          1 + (rest.length + 3) by simp; lia]
      rw [MachineDescription.runConfig_add]
      have hstep :
          description.runConfig 1
              { state := 20
                tape := tapeAtCells
                  (List.append ((next :: rest).map some)
                    (none :: blankLeft))
                  (some current :: right) } =
            { state := 20
              tape := tapeAtCells
                (List.append (rest.map some) (none :: blankLeft))
                (some next :: some current :: right) } := by
        cases next <;> cases current <;> cases rest <;> cases right <;>
          machine_step [description]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih next (some current :: right)

private theorem erasedPairLeft_eq
    (n : Nat) (left : List (Option Bool)) :
    erasedPairLeft n left =
      List.append (List.replicate (2 * n) none) left := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
      rw [erasedPairLeft, ih]
      have hadd :=
        FoC.Computability.list_replicate_add_append
          (none : Option Bool) (2 * n) 2 left
      have hcount : 2 * (n + 1) = 2 * n + 2 := by lia
      rw [hcount]
      calc
        List.append (List.replicate (2 * n) none) (none :: none :: left) =
            List.append (List.replicate (2 * n) none)
              (List.append (List.replicate 2 none) left) := by rfl
        _ = List.append (List.replicate (2 * n + 2) none) left := hadd.symm

/-- Logical blank cells physically preceding the temporary tape-0 sentinel. -/
def tape0ObsoletePadding (L : SimulatorLayout) : List (Option Bool) :=
  none :: (reconstructionBaseLeft L).reverse

/-- Canonical tape-0 payload after its left guard and before tape 1. -/
def tape0RestBits (L : SimulatorLayout) : Word Bool :=
  List.append (logicalCellListBits L.config.tape.left.reverse)
    (List.append [true, true]
      (List.append (logicalCellBits L.config.tape.head)
        (logicalCellListBits (List.append L.config.tape.right [none]))))

/-- Complete guarded stage-counter segment. -/
def tape1Bits (L : SimulatorLayout) : Word Bool :=
  logicalTapeBits
    (guardLogicalTape (FieldDecomposition.stageCounterTape L.stage))

/-- Logical tape-2 cells to the left of its head marker. -/
def tape2LeftCells
    (D : MachineDescription) (L : SimulatorLayout) :
    List (Option Bool) :=
  none :: (ClassifiedBoundary.classifiedMetadataLeft D L).reverse

/-- Canonical tape-2 payload through its encoded head cell. -/
def tape2PrefixBits
    (D : MachineDescription) (L : SimulatorLayout) : Word Bool :=
  List.append (logicalCellListBits (tape2LeftCells D L))
    (List.append [true, true] (logicalCellBits (some L.hit)))

private theorem marked_tape0_code_eq
    (L : SimulatorLayout) :
    logicalTapeCode (guardLogicalTape (markedActualConfigTape L)) =
      List.append (logicalCellListCode (tape0ObsoletePadding L))
        (List.append (logicalCellCode (some false))
          ((tape0RestBits L).map some)) := by
  simp [markedActualConfigTape, tape0ObsoletePadding, tape0RestBits,
    guardLogicalTape, logicalTapeCode, tapeAtCells,
    emittedCells_eq_reverse_append, List.reverse_append,
    logicalCellListBits_append, logicalCellListBits, logicalCellBits,
    headMarkerCells, List.map_append, List.append_assoc]
  done

private theorem canonical_tape0_code_eq
    (L : SimulatorLayout) :
    logicalTapeCode (guardLogicalTape L.config.tape) =
      List.append (logicalCellCode none) ((tape0RestBits L).map some) := by
  simp [tape0RestBits, guardLogicalTape, logicalTapeCode,
    logicalCellListBits_append, logicalCellListBits, logicalCellBits,
    headMarkerCells, List.reverse_append, List.map_append]
  done

private theorem tape0RestBits_ne_nil (L : SimulatorLayout) :
    tape0RestBits L ≠ [] := by
  intro h
  have hlength := congrArg List.length h
  simp [tape0RestBits] at hlength

private theorem tape1_code_eq (L : SimulatorLayout) :
    logicalTapeCode
        (guardLogicalTape (FieldDecomposition.stageCounterTape L.stage)) =
      (tape1Bits L).map some := by
  exact logicalTapeCode_eq_map_some _

private theorem tape1Bits_ne_nil (L : SimulatorLayout) :
    tape1Bits L ≠ [] := by
  rcases logicalTapeBits_exists_cons
      (guardLogicalTape (FieldDecomposition.stageCounterTape L.stage)) with
    ⟨bit, rest, hbits⟩
  simp [tape1Bits, hbits]

private theorem marked_tape2_code_eq
    (D : MachineDescription) (L : SimulatorLayout) :
    logicalTapeCode (guardLogicalTape (actualMetadataTape D L)) =
      List.append (logicalCellListCode (tape2LeftCells D L))
        (List.append headMarkerCells
          (List.append (logicalCellCode (some L.hit))
            (logicalCellListCode
              (List.append (finalErasedRight L) [none])))) := by
  simp [actualMetadataTape, tape2LeftCells, guardLogicalTape,
    logicalTapeCode, tapeAtCells, List.reverse_append]
  done

private theorem canonical_tape2_code_eq
    (D : MachineDescription) (L : SimulatorLayout) :
    logicalTapeCode
        (guardLogicalTape
          (ClassifiedBoundary.metadataHitTapeWithSelector D L)) =
      List.append (logicalCellListCode (tape2LeftCells D L))
        (List.append headMarkerCells
          (List.append (logicalCellCode (some L.hit))
            (logicalCellListCode [none, none]))) := by
  simp [ClassifiedBoundary.metadataHitTapeWithSelector, tape2LeftCells,
    guardLogicalTape, logicalTapeCode, tapeAtCells,
    List.reverse_append]
  done

private theorem tape2PrefixBits_code_eq
    (D : MachineDescription) (L : SimulatorLayout) :
    List.append (logicalCellListCode (tape2LeftCells D L))
        (List.append headMarkerCells (logicalCellCode (some L.hit))) =
      (tape2PrefixBits D L).map some := by
  simp [tape2PrefixBits, headMarkerCells, List.map_append]
  done

def sourceShape
    (obsolete : List (Option Bool)) (tape0 tape1 : Word Bool)
    (tape2Left : List (Option Bool)) (head : Option Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells []
    (none ::
      List.append (logicalCellListCode obsolete)
        (List.append (logicalCellCode (some false))
          (List.append (tape0.map some)
            (none ::
              List.append (tape1.map some)
                (none ::
                  List.append (logicalCellListCode tape2Left)
                    (List.append headMarkerCells
                      (List.append (logicalCellCode head)
                        (some false :: some false ::
                          some false :: some false ::
                            List.append (logicalCellListCode tail)
                              [none]))))))))

def canonicalShape
    (tape0 tape1 : Word Bool)
    (tape2Left : List (Option Bool)) (head : Option Bool) : Tape Bool :=
  tapeAtCells []
    (none :: some false :: some false ::
      List.append (tape0.map some)
        (none ::
          List.append (tape1.map some)
            (none ::
              List.append (logicalCellListCode tape2Left)
                (List.append headMarkerCells
                  (List.append (logicalCellCode head)
                    [some false, some false, some false, some false, none])))))

private def outputShape
    (obsolete : List (Option Bool)) (tape0 tape1 : Word Bool)
    (tape2Left : List (Option Bool)) (head : Option Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells (List.replicate (2 * obsolete.length) none)
    (none :: some false :: some false ::
      List.append (tape0.map some)
        (none ::
          List.append (tape1.map some)
            (none ::
              List.append (logicalCellListCode tape2Left)
                (List.append headMarkerCells
                  (List.append (logicalCellCode head)
                    (some false :: some false :: some false :: some false ::
                      List.replicate (2 * tail.length + 1) none))))))

private def runSteps
    (obsolete : List (Option Bool)) (tape0 tape1 : Word Bool)
    (tape2Left : List (Option Bool)) (head : Option Bool)
    (tail : List (Option Bool))
    (tape0Init tape1Init : Word Bool) : Nat :=
  1 +
    (2 * obsolete.length +
      (4 +
        ((Word.Length
              (Word.Concat ([false, false] : Word Bool) tape0) + 1) +
          ((Word.Length tape1 + 1) +
            ((2 * tape2Left.length + 2) +
              (6 +
                ((2 * (2 * tail.length) + 2) +
                  ((Word.Length
                        (Word.Reverse
                          (Word.Concat
                            (Word.Concat
                              (logicalCellListBits tape2Left)
                              (Word.Concat ([true, true] : Word Bool)
                                (logicalCellBits head)))
                            ([false, false] : Word Bool))) + 2) +
                    ((Word.Length (Word.Reverse tape1Init) + 2) +
                      (Word.Length (Word.Reverse tape0Init) + 3))))))))))

private theorem outputShape_equiv_canonicalShape
    (obsolete : List (Option Bool)) (tape0 tape1 : Word Bool)
    (tape2Left : List (Option Bool)) (head : Option Bool)
    (tail : List (Option Bool)) :
    Tape.Equiv
      (outputShape obsolete tape0 tape1 tape2Left head tail)
      (canonicalShape tape0 tape1 tape2Left head) := by
  unfold outputShape canonicalShape
  unfold Tape.Equiv
  simp only [tapeAtCells]
  let body : List (Option Bool) :=
    some false :: some false ::
      List.append (tape0.map some)
        (none ::
          List.append (tape1.map some)
            (none ::
              List.append (logicalCellListCode tape2Left)
                (List.append headMarkerCells
                  (List.append (logicalCellCode head)
                    [some false, some false, some false, some false]))))
  refine ⟨dropTrailingNone_eq_nil_of_allNone _
      (allNone_replicate _), trivial, ?_⟩
  calc
    Tape.dropTrailingNone
        (some false :: some false ::
          List.append (tape0.map some)
            (none ::
              List.append (tape1.map some)
                (none ::
                  List.append (logicalCellListCode tape2Left)
                    (List.append headMarkerCells
                      (List.append (logicalCellCode head)
                        (some false :: some false :: some false :: some false ::
                          List.replicate (2 * tail.length + 1) none)))))) =
      Tape.dropTrailingNone body := by
        simpa [body, List.append_assoc] using
          (dropTrailingNone_append_replicate_none body
            (2 * tail.length + 1))
    _ = Tape.dropTrailingNone
        (some false :: some false ::
          List.append (tape0.map some)
            (none ::
              List.append (tape1.map some)
                (none ::
                  List.append (logicalCellListCode tape2Left)
                    (List.append headMarkerCells
                      (List.append (logicalCellCode head)
                        [some false, some false, some false, some false, none]))))) := by
        symm
        simpa [body, List.append_assoc] using
          (dropTrailingNone_append_replicate_none body 1)

private theorem run_shape
    (obsolete : List (Option Bool)) (tape0 tape1 : Word Bool)
    (tape2Left : List (Option Bool)) (head : Option Bool)
    (tail : List (Option Bool))
    (hobsolete : AllNone obsolete) (htail : AllNone tail)
    (htape1 : tape1 ≠ []) :
    exists steps : Nat,
      description.runConfig steps
          { state := description.start
            tape := sourceShape obsolete tape0 tape1 tape2Left head tail } =
        { state := description.halt
          tape := outputShape obsolete tape0 tape1 tape2Left head tail } := by
  let tape0Full : Word Bool :=
    List.append ([false, false] : List Bool) tape0
  have htape0Full : tape0Full ≠ [] := by simp [tape0Full]
  obtain ⟨tape0Init, tape0Last, htape0⟩ :=
    FoC.Computability.list_exists_append_singleton_of_ne_nil
      tape0Full htape0Full
  obtain ⟨tape1Init, tape1Last, htape1split⟩ :=
    FoC.Computability.list_exists_append_singleton_of_ne_nil
      tape1 htape1
  let tape2Prefix : Word Bool :=
    List.append (logicalCellListBits tape2Left)
      (List.append [true, true] (logicalCellBits head))
  refine ⟨runSteps obsolete tape0 tape1 tape2Left head tail
      tape0Init tape1Init, ?_⟩
  have hobsoleteCode :=
    logicalCellListCode_eq_replicate_false_of_allNone obsolete hobsolete
  have htailCode :=
    logicalCellListCode_eq_replicate_false_of_allNone tail htail
  let afterTape1 : List (Option Bool) :=
    List.append (logicalCellListCode tape2Left)
      (List.append headMarkerCells
        (List.append (logicalCellCode head)
          (some false :: some false :: some false :: some false ::
            List.append
              (List.replicate (2 * tail.length)
                (some false : Option Bool)) [none])))
  let afterTape0 : List (Option Bool) :=
    List.append (tape1.map some) (none :: afterTape1)
  let afterSentinel : List (Option Bool) :=
    List.append (tape0.map some) (none :: afterTape0)
  have hsource :
      sourceShape obsolete tape0 tape1 tape2Left head tail =
        tapeAtCells []
          (none ::
            List.append
              (List.replicate (2 * obsolete.length)
                (some false : Option Bool))
              (some false :: some true :: afterSentinel)) := by
    unfold sourceShape
    rw [hobsoleteCode, htailCode]
    simp [afterSentinel, afterTape0, afterTape1, logicalCellBits]
  rw [hsource]
  unfold runSteps
  rw [MachineDescription.runConfig_add]
  rw [run_open]
  rw [MachineDescription.runConfig_add]
  rw [run_erase_pairs]
  rw [erasedPairLeft_eq]
  have hleft :=
    FoC.Computability.list_replicate_append_cons_eq_cons_append
      (none : Option Bool) (2 * obsolete.length) []
  have hleft' :
      List.append
          (List.replicate (2 * obsolete.length) (none : Option Bool))
          [none] =
        (none : Option Bool) ::
          List.replicate (2 * obsolete.length) none := by
    simpa using hleft
  rw [hleft']
  rw [MachineDescription.runConfig_add]
  rw [run_sentinel_and_enter]
  have hafterSentinel :
      some false :: some false :: afterSentinel =
        List.append (tape0Full.map some) (none :: afterTape0) := by
    simp [afterSentinel, tape0Full]
  rw [hafterSentinel]
  have htape0Length :
      Word.Length (Word.Concat ([false, false] : Word Bool) tape0) =
        tape0Full.length := by
    rfl
  rw [htape0Length]
  rw [MachineDescription.runConfig_add]
  rw [run_scan_tape0]
  have hafterTape0 :
      afterTape0 = List.append (tape1.map some) (none :: afterTape1) := by
    rfl
  rw [hafterTape0]
  have htape1Length : Word.Length tape1 = tape1.length := by
    rfl
  rw [htape1Length]
  rw [MachineDescription.runConfig_add]
  rw [run_scan_tape1]
  have hafterTape1 :
      afterTape1 =
        List.append (logicalCellListCode tape2Left)
          (List.append headMarkerCells
            (List.append (logicalCellCode head)
              (some false :: some false :: some false :: some false ::
                List.append
                  (List.replicate (2 * tail.length)
                    (some false : Option Bool)) [none]))) := by
    rfl
  rw [hafterTape1]
  rw [MachineDescription.runConfig_add]
  rw [run_scan_tape2_to_head]
  rw [MachineDescription.runConfig_add]
  rw [run_skip_head_and_guards]
  rw [MachineDescription.runConfig_add]
  rw [run_finish_tail_and_rewind]
  have htape2Length :
      Word.Length
          (Word.Reverse
            (Word.Concat
              (Word.Concat
                (logicalCellListBits tape2Left)
                (Word.Concat ([true, true] : Word Bool)
                  (logicalCellBits head)))
              ([false, false] : Word Bool))) =
        (List.append tape2Prefix [false, false]).reverse.length := by
    rfl
  rw [htape2Length]
  rw [MachineDescription.runConfig_add]
  let tape1Base : List (Option Bool) :=
    List.append (tape1.reverse.map some)
      (none ::
        List.append (tape0Full.reverse.map some)
          (none :: List.replicate (2 * obsolete.length) none))
  have hstate18Left :
      some false :: some false ::
          List.append (logicalCellCode head).reverse
            (List.append headMarkerCells.reverse
              (List.append (logicalCellListCode tape2Left).reverse
                (none :: tape1Base))) =
        List.append
          ((List.append tape2Prefix [false, false]).reverse.map some)
          (none :: tape1Base) := by
    simp [tape2Prefix, logicalCellListCode_eq_map_some,
      logicalCellCode_eq_map_some, headMarkerCells, List.reverse_append,
      List.map_append, List.append_assoc]
  rw [hstate18Left]
  have htape1Base : tape1Base ≠ [] := by
    simp [tape1Base, htape1split]
  rw [run_scan_left_tape2 _ _ _ _ htape1Base]
  let tape0Base : List (Option Bool) :=
    List.append (tape0Full.reverse.map some)
      (none :: List.replicate (2 * obsolete.length) none)
  have htape1BaseEq :
      tape1Base =
        some tape1Last ::
          List.append (tape1Init.reverse.map some) (none :: tape0Base) := by
    simp [tape1Base, tape0Base, htape1split, List.reverse_append]
  rw [htape1BaseEq]
  simp only [headTape]
  have htape1InitLength :
      Word.Length (Word.Reverse tape1Init) = tape1Init.reverse.length := by
    rfl
  rw [htape1InitLength]
  rw [MachineDescription.runConfig_add]
  have htape0Base : tape0Base ≠ [] := by
    simp [tape0Base, htape0]
  rw [run_scan_left_tape1 _ _ _ _ htape0Base]
  have htape0BaseEq :
      tape0Base =
        some tape0Last ::
          List.append (tape0Init.reverse.map some)
            (none :: List.replicate (2 * obsolete.length) none) := by
    simp [tape0Base, htape0, List.reverse_append]
  rw [htape0BaseEq]
  simp only [headTape]
  have htape0InitLength :
      Word.Length (Word.Reverse tape0Init) = tape0Init.reverse.length := by
    rfl
  rw [htape0InitLength]
  rw [run_scan_left_tape0_and_halt]
  have htape0Rebuilt :
      List.append tape0Init.reverse.reverse [tape0Last] = tape0Full := by
    simpa using htape0.symm
  have htape1Rebuilt :
      List.append tape1Init.reverse.reverse [tape1Last] = tape1 := by
    simpa using htape1split.symm
  rw [htape0Rebuilt, htape1Rebuilt]
  simp [outputShape, tape0Full, tape2Prefix,
    logicalCellListCode_eq_map_some, logicalCellCode_eq_map_some,
    headMarkerCells, List.map_append, List.append_assoc]

private theorem erasedLeftLengthTail_starts_two
    (n : Nat) (right : List (Option Bool)) :
    exists tail : List (Option Bool),
      erasedLeftLengthTail n right = none :: none :: tail := by
  induction n generalizing right with
  | zero => exact ⟨right, rfl⟩
  | succ n ih =>
      exact ih (none :: none :: none :: none :: right)

private theorem finalErasedRight_tail
    (L : SimulatorLayout) :
    exists tail : List (Option Bool),
      List.append (finalErasedRight L) [none] = none :: none :: tail ∧
        AllNone tail := by
  rcases erasedLeftLengthTail_starts_two
      L.config.tape.left.length
      (erasedRightTail L.config.tape.left.reverse
        (none ::
          erasedRightLengthTail L.config.tape.right.length
            (erasedRightTail L.config.tape.right.reverse
              [none, none, none, none, none]))) with
    ⟨rest, hrest⟩
  have hfinal : finalErasedRight L = none :: none :: rest := by
    exact hrest
  have hnone : AllNone rest := by
    have hall := finalErasedRight_allNone L
    rw [hfinal] at hall
    intro cell hcell
    exact hall cell (List.mem_cons.mpr (Or.inr
      (List.mem_cons.mpr (Or.inr hcell))))
  refine ⟨List.append rest [none], ?_, allNone_append hnone (allNone_cons allNone_nil)⟩
  rw [hfinal]
  simp

private theorem encoded_marked_eq_sourceShape
    (D : MachineDescription) (L : SimulatorLayout)
    (tail : List (Option Bool))
    (htail :
      List.append (finalErasedRight L) [none] = none :: none :: tail) :
    encodedGuardedStructuredTapes (markedRepresentedTapes D L) =
      sourceShape (tape0ObsoletePadding L) (tape0RestBits L)
        (tape1Bits L) (tape2LeftCells D L) (some L.hit) tail := by
  unfold markedRepresentedTapes
  unfold encodedGuardedStructuredTapes encodedStructuredTapes
    guardLogicalTapes encodedStructuredTapeCells tapeSeparatorCells
  simp only [List.map, encodedStructuredTapeCells]
  rw [marked_tape0_code_eq, tape1_code_eq, marked_tape2_code_eq]
  rw [htail]
  simp [sourceShape, tapeSeparatorCells, logicalCellListBits,
    logicalCellBits, List.append_assoc]

private theorem encoded_canonical_eq_canonicalShape
    (D : MachineDescription) (L : SimulatorLayout) :
    encodedGuardedStructuredTapes
        (ClassifiedBoundary.classifiedLoopTapes D L) =
      canonicalShape (tape0RestBits L) (tape1Bits L)
        (tape2LeftCells D L) (some L.hit) := by
  unfold ClassifiedBoundary.classifiedLoopTapes
  unfold encodedGuardedStructuredTapes encodedStructuredTapes
    guardLogicalTapes encodedStructuredTapeCells tapeSeparatorCells
  simp only [List.map, encodedStructuredTapeCells]
  rw [canonical_tape0_code_eq, tape1_code_eq, canonical_tape2_code_eq]
  simp [canonicalShape, tapeSeparatorCells, logicalCellListBits,
    logicalCellBits, List.append_assoc]

/-- The physical repair consumes the marked represented endpoint and returns
the canonical classified-loop encoding up to trailing blank padding. -/
theorem description_haltsFromTapeEquiv
    (D : MachineDescription) (L : SimulatorLayout) :
    description.HaltsFromTapeEquiv
      (encodedGuardedStructuredTapes (markedRepresentedTapes D L))
      (encodedGuardedStructuredTapes
        (ClassifiedBoundary.classifiedLoopTapes D L)) := by
  rcases finalErasedRight_tail L with ⟨tail, htail, htailNone⟩
  have hobsolete : AllNone (tape0ObsoletePadding L) := by
    intro cell hcell
    rcases List.mem_cons.mp hcell with hhead | hrest
    · exact hhead
    · exact reconstructionBaseLeft_allNone L cell (by simpa using hrest)
  rw [encoded_marked_eq_sourceShape D L tail htail]
  rw [encoded_canonical_eq_canonicalShape D L]
  rcases run_shape
      (tape0ObsoletePadding L) (tape0RestBits L) (tape1Bits L)
      (tape2LeftCells D L) (some L.hit) tail
      hobsolete htailNone (tape1Bits_ne_nil L) with ⟨steps, hrun⟩
  refine ⟨outputShape
      (tape0ObsoletePadding L) (tape0RestBits L) (tape1Bits L)
      (tape2LeftCells D L) (some L.hit) tail, ?_, ?_⟩
  · refine ⟨steps, ?_⟩
    unfold MachineDescription.HaltsFromTapeIn
    exact ⟨congrArg (fun c => c.state) hrun,
      congrArg (fun c => c.tape) hrun⟩
  · exact outputShape_equiv_canonicalShape
      (tape0ObsoletePadding L) (tape0RestBits L) (tape1Bits L)
      (tape2LeftCells D L) (some L.hit) tail

end RepresentedBoundaryRepair

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

/-- The marked CfgHit lowerer followed by the finite represented-boundary
repair. -/
def canonicalDescription : MachineDescription :=
  canonicalSeqDescription loweredDescription
    RepresentedBoundaryRepair.description

theorem canonicalDescription_subroutineReady :
    canonicalDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    loweredDescription_subroutineReady
    RepresentedBoundaryRepair.description_subroutineReady

theorem canonicalDescription_haltsFromTapeEquiv
    (D : MachineDescription) (L : MachineDescription.SimulatorLayout) :
    canonicalDescription.HaltsFromTapeEquiv
      (targetTape D L)
      (encodedGuardedStructuredTapes
        (ClassifiedBoundary.classifiedLoopTapes D L)) := by
  rcases RepresentedBoundaryRepair.finalErasedRight_tail L with
    ⟨tail, htail, _⟩
  apply canonicalSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv
    (Tmid := encodedGuardedStructuredTapes (markedRepresentedTapes D L))
    (Tnext := encodedGuardedStructuredTapes (markedRepresentedTapes D L))
    loweredDescription_subroutineReady
    RepresentedBoundaryRepair.description_subroutineReady
    (loweredDescription_haltsFromMarkedTapeEquiv D L)
  · rw [RepresentedBoundaryRepair.encoded_marked_eq_sourceShape
      D L tail htail]
    simp [RepresentedBoundaryRepair.sourceShape,
      RepresentedBoundaryRepair.tape0ObsoletePadding,
      logicalCellListBits, logicalCellBits, tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]
  · exact RepresentedBoundaryRepair.description_haltsFromTapeEquiv D L

/-- Canonical configuration/hit construction in the original component
currency.  The represented family is now the canonical classified family. -/
theorem construction_core (D : MachineDescription) :
    ConfigTapeAndHitConstruction D := by
  refine ⟨canonicalDescription,
    fun L => ClassifiedBoundary.classifiedLoopTapes D L, ?_⟩
  exact ⟨canonicalDescription_subroutineReady,
    fun L => logicalTapeListEquiv_refl _,
    canonicalDescription_haltsFromTapeEquiv D⟩

/-- The cfg-side witness consumed by the full #18 pipeline, stated without an
upward import of the pipeline module. -/
theorem canonical_construction_core :
    forall D : MachineDescription,
      exists cfgHit : MachineDescription,
        cfgHit.SubroutineReady ∧
          forall L : MachineDescription.SimulatorLayout,
            cfgHit.HaltsFromTapeEquiv
              (targetTape D L)
              (encodedGuardedStructuredTapes
                (ClassifiedBoundary.classifiedLoopTapes D L)) := by
  intro D
  exact ⟨canonicalDescription, canonicalDescription_subroutineReady,
    canonicalDescription_haltsFromTapeEquiv D⟩

end FieldDecomposition.MetadataPrefix.ConfigTapeAndHit
end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
