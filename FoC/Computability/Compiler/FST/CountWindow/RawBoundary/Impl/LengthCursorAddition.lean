import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.LengthCursorLoop

set_option doc.verso true

/-!
# Generalized raw-boundary length cursor additions

These declarations extend the Boolean-cell cursor loop to generic four-bit
logical-cell tokens of the form {lit}`01xy`.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf

namespace CommonGround
namespace FiniteTransducers
namespace CountWindowRawSourceEncoder
namespace RawBoundaryRightEdgeEmitter

/-- Process one generic four-bit cell token `01xy`.  The length cursor never
interprets the two payload bits, so this single run covers blank, false, and
true logical cells. -/
theorem rawBoundaryLengthCursorLoopDescription_run_cursorCheck_cellToken
    (storedAnchor : Bool) (count : Nat) (processed remaining : Word Bool)
    (x y : Bool) (blankTail : Nat) (right : List (Option Bool)) :
    exists steps : Nat,
      rawBoundaryLengthCursorLoopDescription.runConfig steps
          { state := rawBoundaryLengthCursorLoopCursorCheck
            tape :=
              rawBoundaryLengthCursorCursorTape storedAnchor
                (List.append (rawBoundaryLengthCursorStageNatBits count)
                  processed)
                (List.append [false, true, x, y] remaining)
                blankTail right } =
        { state := rawBoundaryLengthCursorLoopCursorCheck
          tape :=
            rawBoundaryLengthCursorCursorTape false
              (List.append
                (rawBoundaryLengthCursorStageNatBits (count + 1))
                (List.append processed [false, true, x, y]))
              remaining blankTail right } := by
  let emittedPrefix : Word Bool :=
    List.append (rawBoundaryLengthCursorStageNatBits count) processed
  have hprefix_ne : emittedPrefix ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    simp [emittedPrefix] at hlen
    exact rawBoundaryLengthCursorStageNatBits_ne_nil count hlen.left
  cases hrev : emittedPrefix.reverse with
  | nil =>
      have hprefix_nil : emittedPrefix = [] := by
        have h := congrArg List.reverse hrev
        simpa using! h
      exact False.elim (hprefix_ne hprefix_nil)
  | cons last rest =>
      refine ⟨2 * emittedPrefix.length + 12, ?_⟩
      rw [show 2 * emittedPrefix.length + 12 =
          1 + (emittedPrefix.length +
            (4 + ((3 + emittedPrefix.length) + (1 + 3)))) by
        lia]
      rw [MachineDescription.runConfig_add]
      simp only [rawBoundaryLengthCursorCursorTape,
        emittedPrefix, hrev, Bool.false_eq_true, ↓reduceIte]
      rw [show
          (List.map some
              (List.append [false, true, x, y] remaining)).append
              (none ::
                List.append
                  (List.replicate (blankTail + 1) (none : Option Bool))
                  right) =
            some false :: some true :: some x :: some y ::
              List.append (remaining.map some)
                (none ::
                  List.append
                    (List.replicate (blankTail + 1)
                      (none : Option Bool))
                    right) by
        simp]
      rw [rawBoundaryLengthCursorLoopDescription_step_cursorCheck_false]
      rw [MachineDescription.runConfig_add]
      rw [show emittedPrefix.length = (last :: rest).length by
        have hlen := congrArg List.length hrev
        simp [List.length_reverse] at hlen
        exact hlen]
      rw [rawBoundaryLengthCursorLoopDescription_run_carryFalse_to_anchor]
      rw [MachineDescription.runConfig_add]
      rw [rawBoundaryLengthCursorLoopDescription_run_tickWriteFalse]
      rw [MachineDescription.runConfig_add]
      rw [show 3 + (last :: rest).length =
          (List.append [false, true, false]
            (last :: rest).reverse).length by
        simp
        lia]
      change
        rawBoundaryLengthCursorLoopDescription.runConfig (1 + 3)
            (rawBoundaryLengthCursorLoopDescription.runConfig
              (List.append [false, true, false]
                (last :: rest).reverse).length
              { state := rawBoundaryLengthCursorLoopReturnFalse
                tape :=
                  tapeAtCells [some false]
                    (List.append
                      ((List.append [false, true, false]
                        (last :: rest).reverse).map some)
                      (none :: some true :: some x :: some y ::
                        List.append (remaining.map some)
                          (none ::
                            List.append
                              (List.replicate (blankTail + 1)
                                (none : Option Bool))
                              right))) }) =
          { state := rawBoundaryLengthCursorLoopCursorCheck
            tape :=
              rawBoundaryLengthCursorCursorTape false
                (List.append
                  (rawBoundaryLengthCursorStageNatBits (count + 1))
                  (List.append processed [false, true, x, y]))
                remaining blankTail right }
      rw [rawBoundaryLengthCursorLoopDescription_run_returnFalse_scanRight]
      rw [MachineDescription.runConfig_add]
      rw [rawBoundaryLengthCursorLoopDescription_step_returnFalse_cursor]
      rw [rawBoundaryLengthCursorLoopDescription_run_advanceThree]
      have hrev_rev : (last :: rest).reverse = emittedPrefix := by
        have h := congrArg List.reverse hrev
        simpa using h.symm
      rw [hrev_rev]
      simp [rawBoundaryLengthCursorCursorTape,
        emittedPrefix, List.map_append, List.reverse_append,
        List.append_assoc]

/-- Concatenated `01xy` chunks accepted by the generic length cursor. -/
def rawBoundaryLengthCursorCellTokenBits :
    List (Bool × Bool) -> Word Bool
  | [] => []
  | (x, y) :: rest =>
      List.append [false, true, x, y]
        (rawBoundaryLengthCursorCellTokenBits rest)

/-- Exact length-and-payload block emitted for generic cell tokens. -/
def rawBoundaryLengthCursorCellTokenOutputBits
    (cells : List (Bool × Bool)) : Word Bool :=
  List.append
    (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
      cells.length)
    (rawBoundaryLengthCursorCellTokenBits cells)

/-- Separator endpoint for a generic list of logical cell tokens. -/
def rawBoundaryLengthCursorCellTokenTargetTape
    (cells : List (Bool × Bool)) (blankTail : Nat)
    (right : List (Option Bool)) : Tape Bool :=
  rawBoundaryLengthCursorSeparatorTape
    (rawBoundaryLengthCursorCellTokenOutputBits cells) blankTail right

private theorem rawBoundaryLengthCursorLoopDescription_run_cursorCheck_cellTokens
    (cells : List (Bool × Bool)) (count : Nat)
    (processed : Word Bool) (blankTail : Nat)
    (right : List (Option Bool)) :
    exists steps : Nat,
      rawBoundaryLengthCursorLoopDescription.runConfig steps
          { state := rawBoundaryLengthCursorLoopCursorCheck
            tape :=
              rawBoundaryLengthCursorCursorTape false
                (List.append (rawBoundaryLengthCursorStageNatBits count)
                  processed)
                (rawBoundaryLengthCursorCellTokenBits cells)
                blankTail right } =
        { state := rawBoundaryLengthCursorLoopHalt
          tape :=
            rawBoundaryLengthCursorCursorTape false
              (List.append
                (rawBoundaryLengthCursorStageNatBits
                  (count + cells.length))
                (List.append processed
                  (rawBoundaryLengthCursorCellTokenBits cells)))
              [] blankTail right } := by
  induction cells generalizing count processed with
  | nil =>
      simpa [rawBoundaryLengthCursorCellTokenBits,
        preservingCellPassCellBits] using
        rawBoundaryLengthCursorLoopDescription_run_cursorCheck_noAnchor
          ([] : Word Bool) count processed blankTail right
  | cons pair rest ih =>
      rcases pair with ⟨x, y⟩
      rcases
          rawBoundaryLengthCursorLoopDescription_run_cursorCheck_cellToken
            false count processed
            (rawBoundaryLengthCursorCellTokenBits rest)
            x y blankTail right with
        ⟨cellSteps, hcell⟩
      rcases ih (count + 1)
          (List.append processed [false, true, x, y]) with
        ⟨recSteps, hrec⟩
      refine ⟨cellSteps + recSteps, ?_⟩
      rw [MachineDescription.runConfig_add]
      simp only [rawBoundaryLengthCursorCellTokenBits]
      rw [hcell]
      rw [hrec]
      simp [Nat.add_comm, Nat.add_left_comm,
        List.append_assoc]

private theorem rawBoundaryLengthCursorLoopDescription_run_halts_cellTokens_cons
    (x y : Bool) (rest : List (Bool × Bool)) (blankTail : Nat)
    (right : List (Option Bool)) :
    exists steps : Nat,
      rawBoundaryLengthCursorLoopDescription.runConfig steps
          { state := rawBoundaryLengthCursorLoopStart
            tape :=
              rawBoundaryLengthCursorSeparatorTape
                (rawBoundaryLengthCursorCellTokenBits
                  ((x, y) :: rest)) blankTail right } =
        { state := rawBoundaryLengthCursorLoopHalt
          tape :=
            rawBoundaryLengthCursorCellTokenTargetTape
              ((x, y) :: rest) blankTail right } := by
  rcases
      rawBoundaryLengthCursorLoopDescription_run_cursorCheck_cellToken
        true 0 [] (rawBoundaryLengthCursorCellTokenBits rest)
        x y blankTail right with
    ⟨cellSteps, hcell⟩
  rcases
      rawBoundaryLengthCursorLoopDescription_run_cursorCheck_cellTokens
        rest 1 [false, true, x, y] blankTail right with
    ⟨recSteps, hrec⟩
  refine
    ⟨(2 * (rawBoundaryLengthCursorCellTokenBits ((x, y) :: rest)).length +
          10) +
        (((rawBoundaryLengthCursorCellTokenBits ((x, y) :: rest)).length +
            10) +
          (cellSteps + recSteps)), ?_⟩
  rw [MachineDescription.runConfig_add]
  rw [rawBoundaryLengthCursorLoopDescription_run_donePrefix]
  rw [MachineDescription.runConfig_add]
  rw [rawBoundaryLengthCursorLoopDescription_run_cursorBootstrap]
  have hbootstrap :
      rawBoundaryLengthCursorCursorTape true
          rawBoundaryLengthCursorDoneBits
          (rawBoundaryLengthCursorCellTokenBits ((x, y) :: rest))
          blankTail right =
        rawBoundaryLengthCursorCursorTape true
          (List.append (rawBoundaryLengthCursorStageNatBits 0) [])
          (List.append [false, true, x, y]
            (rawBoundaryLengthCursorCellTokenBits rest))
          blankTail right := by
    simp [rawBoundaryLengthCursorCellTokenBits,
      rawBoundaryLengthCursorDoneBits_eq,
      rawBoundaryLengthCursorStageNatBits,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_zero]
  rw [hbootstrap]
  rw [MachineDescription.runConfig_add]
  rw [hcell]
  have hrec' :
      rawBoundaryLengthCursorLoopDescription.runConfig recSteps
          { state := rawBoundaryLengthCursorLoopCursorCheck
            tape :=
              rawBoundaryLengthCursorCursorTape false
                (List.append (rawBoundaryLengthCursorStageNatBits (0 + 1))
                  (List.append [] [false, true, x, y]))
                (rawBoundaryLengthCursorCellTokenBits rest)
                blankTail right } =
        { state := rawBoundaryLengthCursorLoopHalt
          tape :=
            rawBoundaryLengthCursorCursorTape false
              (List.append
                (rawBoundaryLengthCursorStageNatBits (1 + rest.length))
                (List.append [false, true, x, y]
                  (rawBoundaryLengthCursorCellTokenBits rest)))
              [] blankTail right } := by
    simpa using hrec
  rw [hrec']
  simp [rawBoundaryLengthCursorCellTokenTargetTape,
    rawBoundaryLengthCursorCellTokenOutputBits,
    rawBoundaryLengthCursorCellTokenBits,
    rawBoundaryLengthCursorCursorTape,
    rawBoundaryLengthCursorSeparatorTape,
    rawBoundaryLengthCursorStageNatBits,
    Nat.add_comm, List.reverse_append,
    List.map_append, List.append_assoc]

/-- Exact generic-cell headline for a nonempty list of `01xy` tokens. -/
theorem rawBoundaryLengthCursorLoopDescription_haltsFrom_cellTokens_cons
    (x y : Bool) (rest : List (Bool × Bool)) (blankTail : Nat)
    (right : List (Option Bool)) :
    rawBoundaryLengthCursorLoopDescription.HaltsFromTape
      (rawBoundaryLengthCursorSeparatorTape
        (rawBoundaryLengthCursorCellTokenBits ((x, y) :: rest))
        blankTail right)
      (rawBoundaryLengthCursorCellTokenTargetTape
        ((x, y) :: rest) blankTail right) := by
  rcases
      rawBoundaryLengthCursorLoopDescription_run_halts_cellTokens_cons
        x y rest blankTail right with
    ⟨steps, hrun⟩
  refine ⟨steps, ?_⟩
  show
    (rawBoundaryLengthCursorLoopDescription.runConfig steps
        { state := rawBoundaryLengthCursorLoopStart
          tape := rawBoundaryLengthCursorSeparatorTape
            (rawBoundaryLengthCursorCellTokenBits ((x, y) :: rest))
            blankTail right }).state = rawBoundaryLengthCursorLoopHalt ∧
      (rawBoundaryLengthCursorLoopDescription.runConfig steps
        { state := rawBoundaryLengthCursorLoopStart
          tape := rawBoundaryLengthCursorSeparatorTape
            (rawBoundaryLengthCursorCellTokenBits ((x, y) :: rest))
            blankTail right }).tape =
        rawBoundaryLengthCursorCellTokenTargetTape
          ((x, y) :: rest) blankTail right
  rw [hrun]
  exact ⟨rfl, rfl⟩

/-- Uniform runtime length construction for blank/false/true cell-token
payloads.  As in the Boolean specialization, the empty case is exact only up
to far-edge blank residue. -/
theorem rawBoundaryLengthCursorLoopDescription_haltsFrom_cellTokens
    (cells : List (Bool × Bool)) (blankTail : Nat)
    (right : List (Option Bool)) :
    rawBoundaryLengthCursorLoopDescription.HaltsFromTapeEquiv
      (rawBoundaryLengthCursorSeparatorTape
        (rawBoundaryLengthCursorCellTokenBits cells) blankTail right)
      (rawBoundaryLengthCursorCellTokenTargetTape
        cells blankTail right) := by
  cases cells with
  | nil =>
      simpa [rawBoundaryLengthCursorCellTokenBits,
        rawBoundaryLengthCursorCellTokenTargetTape,
        rawBoundaryLengthCursorCellTokenOutputBits,
        rawBoundaryLengthCursorTargetTape,
        rawBoundaryLengthCursorOutputBits,
        preservingCellPassCellBits] using
        rawBoundaryLengthCursorLoopDescription_haltsFrom_separator_nil
          blankTail right
  | cons pair rest =>
      rcases pair with ⟨x, y⟩
      exact
        (rawBoundaryLengthCursorLoopDescription_haltsFrom_cellTokens_cons
          x y rest blankTail right).toEquiv

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
