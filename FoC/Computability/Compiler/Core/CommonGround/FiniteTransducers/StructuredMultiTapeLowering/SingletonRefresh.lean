import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.CursorBasic

set_option doc.verso true

/-!
# Singleton guard refresh dispatcher support

This module starts the fixed one-segment refresh dispatcher proof.  The first
piece is a raw opening-separator probe: it enters the singleton segment,
branches on the first physical bit, and restores the head to the opening
separator.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

/-!
## Opening-separator probe
-/

def singletonOpeningProbeTargetCeiling
    (falseTarget trueTarget : Nat) : Nat :=
  Nat.max falseTarget trueTarget

def singletonOpeningProbeStateCount
    (falseTarget trueTarget : Nat) : Nat :=
  singletonOpeningProbeTargetCeiling falseTarget trueTarget + 3

def singletonOpeningProbeHalt
    (falseTarget trueTarget : Nat) : Nat :=
  singletonOpeningProbeTargetCeiling falseTarget trueTarget + 2

private theorem singletonOpeningProbe_state0_lt
    (falseTarget trueTarget : Nat) :
    0 < singletonOpeningProbeStateCount falseTarget trueTarget := by
  unfold singletonOpeningProbeStateCount
  lia

private theorem singletonOpeningProbe_state1_lt
    (falseTarget trueTarget : Nat) :
    1 < singletonOpeningProbeStateCount falseTarget trueTarget := by
  unfold singletonOpeningProbeStateCount
  lia

private theorem singletonOpeningProbe_halt_lt
    (falseTarget trueTarget : Nat) :
    singletonOpeningProbeHalt falseTarget trueTarget <
      singletonOpeningProbeStateCount falseTarget trueTarget := by
  unfold singletonOpeningProbeHalt singletonOpeningProbeStateCount
  lia

private theorem singletonOpeningProbe_falseTarget_lt
    (falseTarget trueTarget : Nat) :
    falseTarget <
      singletonOpeningProbeStateCount falseTarget trueTarget := by
  have hle :
      falseTarget ≤
        singletonOpeningProbeTargetCeiling falseTarget trueTarget := by
    unfold singletonOpeningProbeTargetCeiling
    exact Nat.le_max_left _ _
  unfold singletonOpeningProbeStateCount
  lia

private theorem singletonOpeningProbe_trueTarget_lt
    (falseTarget trueTarget : Nat) :
    trueTarget <
      singletonOpeningProbeStateCount falseTarget trueTarget := by
  have hle :
      trueTarget ≤
        singletonOpeningProbeTargetCeiling falseTarget trueTarget := by
    unfold singletonOpeningProbeTargetCeiling
    exact Nat.le_max_right _ _
  unfold singletonOpeningProbeStateCount
  lia

private theorem singletonOpeningProbe_source_ne_halt
    {falseTarget trueTarget source : Nat}
    (hsource : source ≤ 1) :
    source ≠ singletonOpeningProbeHalt falseTarget trueTarget := by
  intro h
  have hlt : source < singletonOpeningProbeHalt falseTarget trueTarget := by
    unfold singletonOpeningProbeHalt
    lia
  rw [← h] at hlt
  exact Nat.lt_irrefl source hlt

/--
Branch on the first physical bit after a singleton segment's opening
separator, then return to that separator.

For the row-produced singleton endpoint shapes, {lit}`falseTarget` covers
canonical and right-boundary inputs; {lit}`trueTarget` covers left-boundary
inputs.
-/
def singletonOpeningProbeDescription
    (falseTarget trueTarget : Nat) : MachineDescription where
  stateCount := singletonOpeningProbeStateCount falseTarget trueTarget
  start := 0
  halt := singletonOpeningProbeHalt falseTarget trueTarget
  transitions :=
    [ transition 0 none none Direction.right 1
    , transition 1 (some false) (some false) Direction.left falseTarget
    , transition 1 (some true) (some true) Direction.left trueTarget ]

theorem singletonOpeningProbeDescription_wellFormed
    (falseTarget trueTarget : Nat) :
    (singletonOpeningProbeDescription
      falseTarget trueTarget).WellFormed := by
  refine ⟨
    singletonOpeningProbe_state0_lt falseTarget trueTarget,
    singletonOpeningProbe_state0_lt falseTarget trueTarget,
    singletonOpeningProbe_halt_lt falseTarget trueTarget,
    ?_,
    ?_⟩
  · intro t ht
    simp [singletonOpeningProbeDescription] at ht
    rcases ht with rfl | rfl | rfl
    · exact ⟨
        singletonOpeningProbe_state0_lt falseTarget trueTarget,
        singletonOpeningProbe_state1_lt falseTarget trueTarget⟩
    · exact ⟨
        singletonOpeningProbe_state1_lt falseTarget trueTarget,
        singletonOpeningProbe_falseTarget_lt falseTarget trueTarget⟩
    · exact ⟨
        singletonOpeningProbe_state1_lt falseTarget trueTarget,
        singletonOpeningProbe_trueTarget_lt falseTarget trueTarget⟩
  · intro t u ht hu hkey
    simp [singletonOpeningProbeDescription] at ht hu
    rcases ht with rfl | rfl | rfl <;>
      rcases hu with rfl | rfl | rfl <;>
        simp [TransitionDescription.SameKey,
          TransitionDescription.SameAction, transition] at hkey ⊢

theorem singletonOpeningProbeDescription_haltTransitionFree
    (falseTarget trueTarget : Nat) :
    (singletonOpeningProbeDescription
      falseTarget trueTarget).HaltTransitionFree := by
  intro t ht
  simp [singletonOpeningProbeDescription] at ht
  rcases ht with rfl | rfl | rfl
  · exact singletonOpeningProbe_source_ne_halt
      (falseTarget := falseTarget)
      (trueTarget := trueTarget)
      (source := 0)
      (by decide)
  · exact singletonOpeningProbe_source_ne_halt
      (falseTarget := falseTarget)
      (trueTarget := trueTarget)
      (source := 1)
      (by decide)
  · exact singletonOpeningProbe_source_ne_halt
      (falseTarget := falseTarget)
      (trueTarget := trueTarget)
      (source := 1)
      (by decide)

theorem singletonOpeningProbeDescription_subroutineReady
    (falseTarget trueTarget : Nat) :
    (singletonOpeningProbeDescription
      falseTarget trueTarget).SubroutineReady :=
  ⟨singletonOpeningProbeDescription_wellFormed falseTarget trueTarget,
    singletonOpeningProbeDescription_haltTransitionFree
      falseTarget trueTarget⟩

theorem singletonOpeningProbeDescription_runs_false
    (falseTarget trueTarget : Nat)
    (suffix : List (Option Bool)) :
    (singletonOpeningProbeDescription
      falseTarget trueTarget).runConfig 2
        { state :=
            (singletonOpeningProbeDescription
              falseTarget trueTarget).start
          tape := tapeAtCells [] (none :: some false :: suffix) } =
      { state := falseTarget
        tape := tapeAtCells [] (none :: some false :: suffix) } := by
  cases suffix <;>
    simp [singletonOpeningProbeDescription, MachineDescription.runConfig,
      MachineDescription.stepConfig, MachineDescription.lookupTransition,
      MachineDescription.Matches, transition, tapeAtCells, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem singletonOpeningProbeDescription_runs_true
    (falseTarget trueTarget : Nat)
    (suffix : List (Option Bool)) :
    (singletonOpeningProbeDescription
      falseTarget trueTarget).runConfig 2
        { state :=
            (singletonOpeningProbeDescription
              falseTarget trueTarget).start
          tape := tapeAtCells [] (none :: some true :: suffix) } =
      { state := trueTarget
        tape := tapeAtCells [] (none :: some true :: suffix) } := by
  cases suffix <;>
    simp [singletonOpeningProbeDescription, MachineDescription.runConfig,
      MachineDescription.stepConfig, MachineDescription.lookupTransition,
      MachineDescription.Matches, transition, tapeAtCells, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem singletonOpeningProbeDescription_run_false_of_reads
    (falseTarget trueTarget : Nat) (physical : Tape Bool)
    (hstart : Tape.read physical = none)
    (hread : Tape.read (Tape.moveRight physical) = some false) :
    (singletonOpeningProbeDescription
      falseTarget trueTarget).runConfig 2
        { state :=
            (singletonOpeningProbeDescription
              falseTarget trueTarget).start
          tape := physical } =
      { state := falseTarget
        tape := physical } := by
  cases physical with
  | mk left head right =>
      cases head with
      | none =>
          cases right with
          | nil =>
              simp [Tape.read, Tape.moveRight] at hread
          | cons cell rest =>
              cases cell with
              | none =>
                  simp [Tape.read, Tape.moveRight] at hread
              | some bit =>
                  cases bit
                  · simp [singletonOpeningProbeDescription,
                      MachineDescription.runConfig,
                      MachineDescription.stepConfig,
                      MachineDescription.lookupTransition,
                      MachineDescription.Matches, transition,
                      Tape.read, Tape.write, Tape.move, Tape.moveLeft,
                      Tape.moveRight]
                  · simp [Tape.read, Tape.moveRight] at hread
      | some bit =>
          cases bit <;> simp [Tape.read] at hstart

theorem singletonOpeningProbeDescription_run_true_of_reads
    (falseTarget trueTarget : Nat) (physical : Tape Bool)
    (hstart : Tape.read physical = none)
    (hread : Tape.read (Tape.moveRight physical) = some true) :
    (singletonOpeningProbeDescription
      falseTarget trueTarget).runConfig 2
        { state :=
            (singletonOpeningProbeDescription
              falseTarget trueTarget).start
          tape := physical } =
      { state := trueTarget
        tape := physical } := by
  cases physical with
  | mk left head right =>
      cases head with
      | none =>
          cases right with
          | nil =>
              simp [Tape.read, Tape.moveRight] at hread
          | cons cell rest =>
              cases cell with
              | none =>
                  simp [Tape.read, Tape.moveRight] at hread
              | some bit =>
                  cases bit
                  · simp [Tape.read, Tape.moveRight] at hread
                  · simp [singletonOpeningProbeDescription,
                      MachineDescription.runConfig,
                      MachineDescription.stepConfig,
                      MachineDescription.lookupTransition,
                      MachineDescription.Matches, transition,
                      Tape.read, Tape.write, Tape.move, Tape.moveLeft,
                      Tape.moveRight]
      | some bit =>
          cases bit <;> simp [Tape.read] at hstart

theorem SingletonGuardSlackEndpointShape.openingSeparator_read
    {target : List (Tape Bool)} {physical : Tape Bool}
    (hshape : SingletonGuardSlackEndpointShape target physical) :
    Tape.read physical = none := by
  cases hshape with
  | canonical hphysical =>
      rw [hphysical]
      exact encodedStructuredTapes_read _
  | leftBoundary head right =>
      exact encodedStructuredTapes_read _
  | rightBoundary left head =>
      exact encodedStructuredTapes_read _

theorem singletonOpeningProbeDescription_run_false_of_shape
    (falseTarget trueTarget : Nat)
    {target : List (Tape Bool)} {physical : Tape Bool}
    (hshape : SingletonGuardSlackEndpointShape target physical)
    (hread : Tape.read (Tape.moveRight physical) = some false) :
    (singletonOpeningProbeDescription
      falseTarget trueTarget).runConfig 2
        { state :=
            (singletonOpeningProbeDescription
              falseTarget trueTarget).start
          tape := physical } =
      { state := falseTarget
        tape := physical } :=
  singletonOpeningProbeDescription_run_false_of_reads
    falseTarget trueTarget physical hshape.openingSeparator_read hread

theorem singletonOpeningProbeDescription_run_true_of_shape
    (falseTarget trueTarget : Nat)
    {target : List (Tape Bool)} {physical : Tape Bool}
    (hshape : SingletonGuardSlackEndpointShape target physical)
    (hread : Tape.read (Tape.moveRight physical) = some true) :
    (singletonOpeningProbeDescription
      falseTarget trueTarget).runConfig 2
        { state :=
            (singletonOpeningProbeDescription
              falseTarget trueTarget).start
          tape := physical } =
      { state := trueTarget
        tape := physical } :=
  singletonOpeningProbeDescription_run_true_of_reads
    falseTarget trueTarget physical hshape.openingSeparator_read hread

theorem singletonOpeningProbeDescription_run_canonical
    (falseTarget trueTarget : Nat) (target : Tape Bool) :
    (singletonOpeningProbeDescription
      falseTarget trueTarget).runConfig 2
        { state :=
            (singletonOpeningProbeDescription
              falseTarget trueTarget).start
          tape := encodedGuardedStructuredTapes [target] } =
      { state := falseTarget
        tape := encodedGuardedStructuredTapes [target] } := by
  cases target with
  | mk left head right =>
      have hrun :=
        singletonOpeningProbeDescription_runs_false
          falseTarget trueTarget
          (some false ::
            List.append (logicalCellListCode left.reverse)
              (List.append headMarkerCells
                (List.append (logicalCellCode head)
                  (List.append (logicalCellListCode (right ++ [none]))
                    (encodedStructuredTapeCells [])))))
      simpa [encodedGuardedStructuredTapes, encodedStructuredTapes,
        encodedStructuredTapeCells, guardLogicalTapes, guardLogicalTape,
        logicalTapeCode, logicalCellListCode, logicalCellListCode_append,
        logicalCellListBits, logicalCellListBits_append, logicalCellBits,
        tapeSeparatorCells, tapeAtCells, List.map_append,
        List.append_assoc] using hrun

theorem singletonOpeningProbeDescription_run_leftBoundary
    (falseTarget trueTarget : Nat)
    (head : Option Bool) (right : List (Option Bool)) :
    (singletonOpeningProbeDescription
      falseTarget trueTarget).runConfig 2
        { state :=
            (singletonOpeningProbeDescription
              falseTarget trueTarget).start
          tape :=
            encodedStructuredTapes
              [({ left := [], head := head, right := right ++ [none] } :
              Tape Bool)] } =
      { state := trueTarget
        tape :=
          encodedStructuredTapes
            [({ left := [], head := head, right := right ++ [none] } :
              Tape Bool)] } := by
  have hrun :=
    singletonOpeningProbeDescription_runs_true
      falseTarget trueTarget
      (some true ::
        List.append (logicalCellCode head)
          (List.append (logicalCellListCode (right ++ [none]))
            (encodedStructuredTapeCells [])))
  simpa [encodedStructuredTapes, encodedStructuredTapeCells,
    logicalTapeCode, logicalCellListCode, logicalCellListCode_append,
    logicalCellListBits, logicalCellListBits_append, logicalCellBits,
    headMarkerCells, tapeSeparatorCells, tapeAtCells, List.map_append,
    List.append_assoc] using hrun

theorem singletonOpeningProbeDescription_run_rightBoundary
    (falseTarget trueTarget : Nat)
    (left : List (Option Bool)) (head : Option Bool) :
    (singletonOpeningProbeDescription
      falseTarget trueTarget).runConfig 2
        { state :=
            (singletonOpeningProbeDescription
              falseTarget trueTarget).start
          tape :=
            encodedStructuredTapes
              [({ left := left ++ [none], head := head, right := [] } :
              Tape Bool)] } =
      { state := falseTarget
        tape :=
          encodedStructuredTapes
            [({ left := left ++ [none], head := head, right := [] } :
              Tape Bool)] } := by
  have hrun :=
    singletonOpeningProbeDescription_runs_false
      falseTarget trueTarget
      (some false ::
        List.append (logicalCellListCode left.reverse)
          (List.append headMarkerCells
            (List.append (logicalCellCode head)
              (encodedStructuredTapeCells []))))
  simpa [encodedStructuredTapes, encodedStructuredTapeCells,
    logicalTapeCode, logicalCellListCode, logicalCellListCode_append,
    logicalCellListBits, logicalCellListBits_append, logicalCellBits,
    tapeSeparatorCells, tapeAtCells, List.reverse_append, List.map_append,
    List.append_assoc] using hrun

/-!
## Terminal-token facts for the false branch
-/

theorem logicalCellListTokens_cons_append_none_terminal
    (cell : Option Bool) (rest : List (Option Bool)) :
    exists (pfx : List PhysicalToken) (last : Option Bool),
      logicalCellListTokens (cell :: rest ++ [none]) =
        List.append pfx
          [PhysicalToken.logicalCell last,
            PhysicalToken.logicalCell none] := by
  induction rest generalizing cell with
  | nil =>
      exact ⟨[], cell, by simp [logicalCellListTokens]⟩
  | cons next tail ih =>
      rcases ih next with ⟨pfx, last, htail⟩
      refine
        ⟨PhysicalToken.logicalCell cell :: pfx, last, ?_⟩
      change
        PhysicalToken.logicalCell cell ::
            logicalCellListTokens (next :: tail ++ [none]) =
          PhysicalToken.logicalCell cell ::
            (List.append pfx
              [PhysicalToken.logicalCell last,
                PhysicalToken.logicalCell none])
      rw [htail]

theorem SingletonGuardSlackEndpointShape.canonical_singleton_tokens_terminal_cell_guard
    (target : Tape Bool) :
    exists (pfx : List PhysicalToken) (cell : Option Bool),
      logicalTapeTokens (guardLogicalTape target) =
        List.append pfx
          [PhysicalToken.logicalCell cell,
            PhysicalToken.logicalCell none] := by
  cases target with
  | mk left head right =>
      rcases
          logicalCellListTokens_cons_append_none_terminal
            head right with
        ⟨pfx, cell, htail⟩
      have hcellTail :
          PhysicalToken.logicalCell head ::
              logicalCellListTokens (right ++ [none]) =
            List.append pfx
              [PhysicalToken.logicalCell cell,
                PhysicalToken.logicalCell none] := by
        simpa [logicalCellListTokens] using htail
      refine
        ⟨List.append
          (List.append
            (logicalCellListTokens
              (List.reverse (left ++ [none])))
            [PhysicalToken.headMarker])
          pfx, cell, ?_⟩
      simp [logicalTapeTokens, guardLogicalTape,
        hcellTail, List.append_assoc]

theorem SingletonGuardSlackEndpointShape.afterOpening_read_false_terminal_pair_cases
    {target : List (Tape Bool)} {physical : Tape Bool}
    (hshape : SingletonGuardSlackEndpointShape target physical)
    (hread : Tape.read (Tape.moveRight physical) = some false) :
    (exists (targetTape : Tape Bool) (pfx : List PhysicalToken)
        (cell : Option Bool),
      target = [targetTape] ∧
        physical = encodedGuardedStructuredTapes [targetTape] ∧
        logicalTapeTokens (guardLogicalTape targetTape) =
          List.append pfx
            [PhysicalToken.logicalCell cell,
              PhysicalToken.logicalCell none]) ∨
      exists (left : List (Option Bool)) (head : Option Bool),
        target =
          [({ left := left, head := head, right := [] } : Tape Bool)] ∧
          physical =
            encodedStructuredTapes
              [({ left := left ++ [none], head := head, right := [] } :
                Tape Bool)] ∧
          logicalTapeTokens
              ({ left := left ++ [none], head := head, right := [] } :
                Tape Bool) =
            List.append
              (logicalCellListTokens (none :: left.reverse))
              [PhysicalToken.headMarker,
                PhysicalToken.logicalCell head] := by
  cases
      SingletonGuardSlackEndpointShape.afterOpening_read_false_cases
        hshape hread with
  | inl hcanonical =>
      rcases hcanonical with ⟨targetTape, htarget, hphysical⟩
      rcases
          SingletonGuardSlackEndpointShape.canonical_singleton_tokens_terminal_cell_guard
            targetTape with
        ⟨pfx, cell, htokens⟩
      exact
        Or.inl
          ⟨targetTape, pfx, cell, htarget, hphysical, htokens⟩
  | inr hright =>
      rcases hright with ⟨left, head, htarget, hphysical⟩
      exact
        Or.inr
          ⟨left, head, htarget, hphysical,
            SingletonGuardSlackEndpointShape.rightBoundary_tokens_terminal_head
              left head⟩

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
