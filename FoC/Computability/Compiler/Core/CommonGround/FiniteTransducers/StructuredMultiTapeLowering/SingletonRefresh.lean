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
## False-branch terminal-pair probe
-/

def singletonTerminalPairProbeTargetCeiling
    (canonicalTarget rightBoundaryTarget : Nat) : Nat :=
  Nat.max canonicalTarget rightBoundaryTarget

def singletonTerminalPairProbeStateCount
    (canonicalTarget rightBoundaryTarget : Nat) : Nat :=
  singletonTerminalPairProbeTargetCeiling
      canonicalTarget rightBoundaryTarget + 12

def singletonTerminalPairProbeHalt
    (canonicalTarget rightBoundaryTarget : Nat) : Nat :=
  singletonTerminalPairProbeTargetCeiling
      canonicalTarget rightBoundaryTarget + 11

private theorem singletonTerminalPairProbe_local_lt
    (canonicalTarget rightBoundaryTarget localState : Nat)
    (hlocal : localState ≤ 10) :
    localState <
      singletonTerminalPairProbeStateCount
        canonicalTarget rightBoundaryTarget := by
  unfold singletonTerminalPairProbeStateCount
  lia

private theorem singletonTerminalPairProbe_halt_lt
    (canonicalTarget rightBoundaryTarget : Nat) :
    singletonTerminalPairProbeHalt
        canonicalTarget rightBoundaryTarget <
      singletonTerminalPairProbeStateCount
        canonicalTarget rightBoundaryTarget := by
  unfold singletonTerminalPairProbeHalt
    singletonTerminalPairProbeStateCount
  lia

private theorem singletonTerminalPairProbe_canonicalTarget_lt
    (canonicalTarget rightBoundaryTarget : Nat) :
    canonicalTarget <
      singletonTerminalPairProbeStateCount
        canonicalTarget rightBoundaryTarget := by
  have hle :
      canonicalTarget ≤
        singletonTerminalPairProbeTargetCeiling
          canonicalTarget rightBoundaryTarget := by
    unfold singletonTerminalPairProbeTargetCeiling
    exact Nat.le_max_left _ _
  unfold singletonTerminalPairProbeStateCount
  lia

private theorem singletonTerminalPairProbe_rightBoundaryTarget_lt
    (canonicalTarget rightBoundaryTarget : Nat) :
    rightBoundaryTarget <
      singletonTerminalPairProbeStateCount
        canonicalTarget rightBoundaryTarget := by
  have hle :
      rightBoundaryTarget ≤
        singletonTerminalPairProbeTargetCeiling
          canonicalTarget rightBoundaryTarget := by
    unfold singletonTerminalPairProbeTargetCeiling
    exact Nat.le_max_right _ _
  unfold singletonTerminalPairProbeStateCount
  lia

private theorem singletonTerminalPairProbe_source_ne_halt
    {canonicalTarget rightBoundaryTarget source : Nat}
    (hsource : source ≤ 10) :
    source ≠
      singletonTerminalPairProbeHalt
        canonicalTarget rightBoundaryTarget := by
  intro h
  have hlt :
      source <
        singletonTerminalPairProbeHalt
          canonicalTarget rightBoundaryTarget := by
    unfold singletonTerminalPairProbeHalt
    lia
  rw [← h] at hlt
  exact Nat.lt_irrefl source hlt

/--
False-branch discriminator for singleton endpoint refresh.

Starting at the opening separator, this machine scans to the closing separator,
backs up to the first bit of the terminal token pair, and distinguishes
right-boundary slack ({lit}`11` head marker before the final head-cell token)
from canonical guarded input (a logical-cell token before the final blank guard
cell).  It then rewinds to the opening separator before jumping to the selected
caller-supplied branch target.
-/
def singletonTerminalPairProbeDescription
    (canonicalTarget rightBoundaryTarget : Nat) :
    MachineDescription where
  stateCount :=
    singletonTerminalPairProbeStateCount
      canonicalTarget rightBoundaryTarget
  start := 0
  halt :=
    singletonTerminalPairProbeHalt
      canonicalTarget rightBoundaryTarget
  transitions :=
    [ transition 0 none none Direction.right 1
    , transition 1 (some false) (some false) Direction.right 1
    , transition 1 (some true) (some true) Direction.right 1
    , transition 1 none none Direction.left 2
    , transition 2 (some false) (some false) Direction.left 3
    , transition 2 (some true) (some true) Direction.left 3
    , transition 3 (some false) (some false) Direction.left 4
    , transition 3 (some true) (some true) Direction.left 4
    , transition 4 (some false) (some false) Direction.left 5
    , transition 4 (some true) (some true) Direction.left 5
    , transition 5 (some false) (some false) Direction.left 7
    , transition 5 (some true) (some true) Direction.right 6
    , transition 6 (some false) (some false) Direction.left 7
    , transition 6 (some true) (some true) Direction.left 9
    , transition 7 (some false) (some false) Direction.left 7
    , transition 7 (some true) (some true) Direction.left 7
    , transition 7 none none Direction.right 8
    , transition 8 (some false) (some false) Direction.left
        canonicalTarget
    , transition 8 (some true) (some true) Direction.left
        canonicalTarget
    , transition 9 (some false) (some false) Direction.left 9
    , transition 9 (some true) (some true) Direction.left 9
    , transition 9 none none Direction.right 10
    , transition 10 (some false) (some false) Direction.left
        rightBoundaryTarget
    , transition 10 (some true) (some true) Direction.left
        rightBoundaryTarget ]

theorem singletonTerminalPairProbeDescription_wellFormed
    (canonicalTarget rightBoundaryTarget : Nat) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).WellFormed := by
  refine ⟨
    singletonTerminalPairProbe_local_lt
      canonicalTarget rightBoundaryTarget 0 (by decide),
    singletonTerminalPairProbe_local_lt
      canonicalTarget rightBoundaryTarget 0 (by decide),
    singletonTerminalPairProbe_halt_lt
      canonicalTarget rightBoundaryTarget,
    ?_,
    ?_⟩
  · intro t ht
    simp [singletonTerminalPairProbeDescription] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 0 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 1 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 1 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 1 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 1 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 1 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 1 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 2 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 2 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 3 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 2 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 3 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 3 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 4 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 3 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 4 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 4 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 5 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 4 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 5 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 5 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 7 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 5 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 6 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 6 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 7 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 6 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 9 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 7 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 7 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 7 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 7 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 7 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 8 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 8 (by decide),
        singletonTerminalPairProbe_canonicalTarget_lt
          canonicalTarget rightBoundaryTarget⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 8 (by decide),
        singletonTerminalPairProbe_canonicalTarget_lt
          canonicalTarget rightBoundaryTarget⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 9 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 9 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 9 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 9 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 9 (by decide),
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 10 (by decide)⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 10 (by decide),
        singletonTerminalPairProbe_rightBoundaryTarget_lt
          canonicalTarget rightBoundaryTarget⟩
    · exact ⟨
        singletonTerminalPairProbe_local_lt
          canonicalTarget rightBoundaryTarget 10 (by decide),
        singletonTerminalPairProbe_rightBoundaryTarget_lt
          canonicalTarget rightBoundaryTarget⟩
  · intro t u ht hu hkey
    simp [singletonTerminalPairProbeDescription] at ht hu
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [TransitionDescription.SameKey,
        TransitionDescription.SameAction, transition] at hkey ⊢

theorem singletonTerminalPairProbeDescription_haltTransitionFree
    (canonicalTarget rightBoundaryTarget : Nat) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).HaltTransitionFree := by
  intro t ht
  simp [singletonTerminalPairProbeDescription] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | exact singletonTerminalPairProbe_source_ne_halt
        (canonicalTarget := canonicalTarget)
        (rightBoundaryTarget := rightBoundaryTarget)
        (source := 0) (by decide)
    | exact singletonTerminalPairProbe_source_ne_halt
        (canonicalTarget := canonicalTarget)
        (rightBoundaryTarget := rightBoundaryTarget)
        (source := 1) (by decide)
    | exact singletonTerminalPairProbe_source_ne_halt
        (canonicalTarget := canonicalTarget)
        (rightBoundaryTarget := rightBoundaryTarget)
        (source := 2) (by decide)
    | exact singletonTerminalPairProbe_source_ne_halt
        (canonicalTarget := canonicalTarget)
        (rightBoundaryTarget := rightBoundaryTarget)
        (source := 3) (by decide)
    | exact singletonTerminalPairProbe_source_ne_halt
        (canonicalTarget := canonicalTarget)
        (rightBoundaryTarget := rightBoundaryTarget)
        (source := 4) (by decide)
    | exact singletonTerminalPairProbe_source_ne_halt
        (canonicalTarget := canonicalTarget)
        (rightBoundaryTarget := rightBoundaryTarget)
        (source := 5) (by decide)
    | exact singletonTerminalPairProbe_source_ne_halt
        (canonicalTarget := canonicalTarget)
        (rightBoundaryTarget := rightBoundaryTarget)
        (source := 6) (by decide)
    | exact singletonTerminalPairProbe_source_ne_halt
        (canonicalTarget := canonicalTarget)
        (rightBoundaryTarget := rightBoundaryTarget)
        (source := 7) (by decide)
    | exact singletonTerminalPairProbe_source_ne_halt
        (canonicalTarget := canonicalTarget)
        (rightBoundaryTarget := rightBoundaryTarget)
        (source := 8) (by decide)
    | exact singletonTerminalPairProbe_source_ne_halt
        (canonicalTarget := canonicalTarget)
        (rightBoundaryTarget := rightBoundaryTarget)
        (source := 9) (by decide)
    | exact singletonTerminalPairProbe_source_ne_halt
        (canonicalTarget := canonicalTarget)
        (rightBoundaryTarget := rightBoundaryTarget)
        (source := 10) (by decide)

theorem singletonTerminalPairProbeDescription_subroutineReady
    (canonicalTarget rightBoundaryTarget : Nat) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).SubroutineReady :=
  ⟨singletonTerminalPairProbeDescription_wellFormed
      canonicalTarget rightBoundaryTarget,
    singletonTerminalPairProbeDescription_haltTransitionFree
      canonicalTarget rightBoundaryTarget⟩

private theorem singletonTerminalPairProbeDescription_step_scan_bit
    (canonicalTarget rightBoundaryTarget : Nat)
    (left right : List (Option Bool)) (bit : Bool) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig 1
        { state := 1
          tape := tapeAtCells left (some bit :: right) } =
      { state := 1
        tape := tapeAtCells (some bit :: left) right } := by
  cases bit <;> cases right <;>
    simp [singletonTerminalPairProbeDescription,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

private theorem singletonTerminalPairProbeDescription_step_scan_finish
    (canonicalTarget rightBoundaryTarget : Nat)
    (left padding : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig 1
        { state := 1
          tape := tapeAtCells left (none :: padding) } =
      { state := 2
        tape :=
          Tape.move Direction.left
            (tapeAtCells left (none :: padding)) } := by
  cases left <;> cases padding <;>
    simp [singletonTerminalPairProbeDescription,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft]

theorem singletonTerminalPairProbeDescription_run_scan
    (canonicalTarget rightBoundaryTarget : Nat)
    (bits : Word Bool) (left padding : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig bits.length
        { state := 1
          tape :=
            tapeAtCells left
              (List.append (bits.map some) (none :: padding)) } =
      { state := 1
        tape :=
          tapeAtCells
            (List.append (bits.reverse.map some) left)
            (none :: padding) } := by
  induction bits generalizing left with
  | nil =>
      simp [MachineDescription.runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      change
        (singletonTerminalPairProbeDescription
          canonicalTarget rightBoundaryTarget).runConfig rest.length
            ((singletonTerminalPairProbeDescription
              canonicalTarget rightBoundaryTarget).runConfig 1
              { state := 1
                tape :=
                  tapeAtCells left
                    (some bit ::
                      List.append (rest.map some)
                        (none :: padding)) }) =
          { state := 1
            tape :=
              tapeAtCells
                (List.append ((bit :: rest).reverse.map some) left)
                (none :: padding) }
      rw [singletonTerminalPairProbeDescription_step_scan_bit
        canonicalTarget rightBoundaryTarget left
        (List.append (rest.map some) (none :: padding)) bit]
      simpa [List.reverse_cons, List.map_append,
        List.append_assoc] using ih (some bit :: left)

theorem singletonTerminalPairProbeDescription_run_scan_to_terminal
    (canonicalTarget rightBoundaryTarget : Nat)
    (bits : Word Bool) (padding : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig (bits.length + 1)
        { state := 1
          tape :=
            tapeAtCells []
              (List.append (bits.map some) (none :: padding)) } =
      { state := 2
        tape :=
          Tape.move Direction.left
            (tapeAtCells (bits.reverse.map some)
              (none :: padding)) } := by
  rw [MachineDescription.runConfig_add]
  rw [singletonTerminalPairProbeDescription_run_scan]
  rw [singletonTerminalPairProbeDescription_step_scan_finish]
  simp

theorem singletonTerminalPairProbeDescription_run_scan_to_terminal_from_left
    (canonicalTarget rightBoundaryTarget : Nat)
    (bits : Word Bool) (left padding : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig (bits.length + 1)
        { state := 1
          tape :=
            tapeAtCells left
              (List.append (bits.map some) (none :: padding)) } =
      { state := 2
        tape :=
          Tape.move Direction.left
            (tapeAtCells
              (List.append (bits.reverse.map some) left)
              (none :: padding)) } := by
  rw [MachineDescription.runConfig_add]
  rw [singletonTerminalPairProbeDescription_run_scan]
  rw [singletonTerminalPairProbeDescription_step_scan_finish]

private theorem singletonTerminalPairProbeDescription_step_start
    (canonicalTarget rightBoundaryTarget : Nat)
    (bits : Word Bool) (padding : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig 1
        { state :=
            (singletonTerminalPairProbeDescription
              canonicalTarget rightBoundaryTarget).start
          tape :=
            tapeAtCells []
              (none ::
                List.append (bits.map some) (none :: padding)) } =
      { state := 1
        tape :=
          tapeAtCells [none]
            (List.append (bits.map some) (none :: padding)) } := by
  cases bits with
  | nil =>
      cases padding <;>
        simp [singletonTerminalPairProbeDescription,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
          Tape.moveRight]
  | cons bit rest =>
      cases bit <;> cases rest <;> cases padding <;>
        simp [singletonTerminalPairProbeDescription,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
          Tape.moveRight]

private theorem singletonTerminalPairProbeDescription_step_rewind_canonical_finish
    (canonicalTarget rightBoundaryTarget : Nat)
    (current : Bool) (rightTail : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig 2
        { state := 7
          tape :=
            tapeAtCells [] (none :: some current :: rightTail) } =
      { state := canonicalTarget
        tape :=
          tapeAtCells [] (none :: some current :: rightTail) } := by
  cases current <;> cases rightTail <;>
    simp [singletonTerminalPairProbeDescription,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight]

private theorem singletonTerminalPairProbeDescription_step_rewind_right_finish
    (canonicalTarget rightBoundaryTarget : Nat)
    (current : Bool) (rightTail : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig 2
        { state := 9
          tape :=
            tapeAtCells [] (none :: some current :: rightTail) } =
      { state := rightBoundaryTarget
        tape :=
          tapeAtCells [] (none :: some current :: rightTail) } := by
  cases current <;> cases rightTail <;>
    simp [singletonTerminalPairProbeDescription,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight]

private theorem singletonTerminalPairProbeDescription_run_rewind_canonical
    (canonicalTarget rightBoundaryTarget : Nat)
    (leftStack : Word Bool) (current : Bool)
    (rightTail : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig
        (leftStack.length + 3)
        { state := 7
          tape :=
            tapeAtCells
              (List.append (leftStack.map some) [none])
              (some current :: rightTail) } =
      { state := canonicalTarget
        tape :=
          tapeAtCells []
            (none ::
              List.append
                ((List.append leftStack.reverse [current]).map some)
                rightTail) } := by
  induction leftStack generalizing current rightTail with
  | nil =>
      rw [show ([] : Word Bool).length + 3 = 1 + 2 by rfl]
      rw [MachineDescription.runConfig_add]
      have hstep :
          (singletonTerminalPairProbeDescription
            canonicalTarget rightBoundaryTarget).runConfig 1
            { state := 7
              tape :=
                tapeAtCells
                  (List.append (([] : Word Bool).map some) [none])
                  (some current :: rightTail) } =
          { state := 7
            tape :=
              tapeAtCells [] (none :: some current :: rightTail) } := by
        cases current <;> cases rightTail <;>
          simp [singletonTerminalPairProbeDescription,
            MachineDescription.runConfig, MachineDescription.stepConfig,
            MachineDescription.lookupTransition,
            MachineDescription.Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [hstep]
      simpa using
        singletonTerminalPairProbeDescription_step_rewind_canonical_finish
          canonicalTarget rightBoundaryTarget current rightTail
  | cons next rest ih =>
      rw [show (next :: rest).length + 3 =
        1 + (rest.length + 3) by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      have hstep :
          (singletonTerminalPairProbeDescription
            canonicalTarget rightBoundaryTarget).runConfig 1
            { state := 7
              tape :=
                tapeAtCells
                  (List.append ((next :: rest).map some) [none])
                  (some current :: rightTail) } =
          { state := 7
            tape :=
              tapeAtCells
                (List.append (rest.map some) [none])
                (some next :: some current :: rightTail) } := by
        cases next <;> cases current <;> cases rightTail <;>
          simp [singletonTerminalPairProbeDescription,
            MachineDescription.runConfig, MachineDescription.stepConfig,
            MachineDescription.lookupTransition,
            MachineDescription.Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc]
        using ih next (some current :: rightTail)

private theorem singletonTerminalPairProbeDescription_run_rewind_right
    (canonicalTarget rightBoundaryTarget : Nat)
    (leftStack : Word Bool) (current : Bool)
    (rightTail : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig
        (leftStack.length + 3)
        { state := 9
          tape :=
            tapeAtCells
              (List.append (leftStack.map some) [none])
              (some current :: rightTail) } =
      { state := rightBoundaryTarget
        tape :=
          tapeAtCells []
            (none ::
              List.append
                ((List.append leftStack.reverse [current]).map some)
                rightTail) } := by
  induction leftStack generalizing current rightTail with
  | nil =>
      rw [show ([] : Word Bool).length + 3 = 1 + 2 by rfl]
      rw [MachineDescription.runConfig_add]
      have hstep :
          (singletonTerminalPairProbeDescription
            canonicalTarget rightBoundaryTarget).runConfig 1
            { state := 9
              tape :=
                tapeAtCells
                  (List.append (([] : Word Bool).map some) [none])
                  (some current :: rightTail) } =
          { state := 9
            tape :=
              tapeAtCells [] (none :: some current :: rightTail) } := by
        cases current <;> cases rightTail <;>
          simp [singletonTerminalPairProbeDescription,
            MachineDescription.runConfig, MachineDescription.stepConfig,
            MachineDescription.lookupTransition,
            MachineDescription.Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [hstep]
      simpa using
        singletonTerminalPairProbeDescription_step_rewind_right_finish
          canonicalTarget rightBoundaryTarget current rightTail
  | cons next rest ih =>
      rw [show (next :: rest).length + 3 =
        1 + (rest.length + 3) by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      have hstep :
          (singletonTerminalPairProbeDescription
            canonicalTarget rightBoundaryTarget).runConfig 1
            { state := 9
              tape :=
                tapeAtCells
                  (List.append ((next :: rest).map some) [none])
                  (some current :: rightTail) } =
          { state := 9
            tape :=
              tapeAtCells
                (List.append (rest.map some) [none])
                (some next :: some current :: rightTail) } := by
        cases next <;> cases current <;> cases rightTail <;>
          simp [singletonTerminalPairProbeDescription,
            MachineDescription.runConfig, MachineDescription.stepConfig,
            MachineDescription.lookupTransition,
            MachineDescription.Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc]
        using ih next (some current :: rightTail)

private theorem singletonTerminalPairProbeDescription_run_rewind_canonical_after_left
    (canonicalTarget rightBoundaryTarget : Nat)
    (leftStack : Word Bool) (current : Bool)
    (rightTail : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig
        (leftStack.length + 2)
        { state := 7
          tape :=
            Tape.move Direction.left
              (tapeAtCells
                (List.append (leftStack.map some) [none])
                (some current :: rightTail)) } =
      { state := canonicalTarget
        tape :=
          tapeAtCells []
            (none ::
              List.append (leftStack.reverse.map some)
                (some current :: rightTail)) } := by
  cases leftStack with
  | nil =>
      simpa [Tape.move, Tape.moveLeft, tapeAtCells] using
        singletonTerminalPairProbeDescription_step_rewind_canonical_finish
          canonicalTarget rightBoundaryTarget current rightTail
  | cons next rest =>
      rw [show (next :: rest).length + 2 = rest.length + 3 by
        simp]
      simpa [Tape.move, Tape.moveLeft, tapeAtCells, List.reverse_cons,
        List.map_append, List.append_assoc] using
        singletonTerminalPairProbeDescription_run_rewind_canonical
          canonicalTarget rightBoundaryTarget rest next
          (some current :: rightTail)

private theorem singletonTerminalPairProbeDescription_run_terminal_right_from_state2
    (canonicalTarget rightBoundaryTarget : Nat)
    (pfxRev : Word Bool) (b0 b1 : Bool)
    (padding : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig
        (pfxRev.length + 8)
        { state := 2
          tape :=
            tapeAtCells
              (some b0 :: some true :: some true ::
                List.append (pfxRev.map some) [none])
              (some b1 :: none :: padding) } =
      { state := rightBoundaryTarget
        tape :=
          tapeAtCells []
            (none ::
              List.append
                ((List.append pfxRev.reverse [true]).map some)
                (some true :: some b0 :: some b1 :: none :: padding)) } := by
  rw [show pfxRev.length + 8 = 5 + (pfxRev.length + 3) by
    lia]
  rw [MachineDescription.runConfig_add]
  have hterminal :
      (singletonTerminalPairProbeDescription
        canonicalTarget rightBoundaryTarget).runConfig 5
        { state := 2
          tape :=
            tapeAtCells
              (some b0 :: some true :: some true ::
                List.append (pfxRev.map some) [none])
              (some b1 :: none :: padding) } =
      { state := 9
        tape :=
          tapeAtCells
            (List.append (pfxRev.map some) [none])
            (some true :: some true :: some b0 :: some b1 ::
              none :: padding) } := by
    cases b0 <;> cases b1 <;> cases padding <;>
      simp [singletonTerminalPairProbeDescription,
        MachineDescription.runConfig, MachineDescription.stepConfig,
        MachineDescription.lookupTransition,
        MachineDescription.Matches, transition, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft,
        Tape.moveRight]
  rw [hterminal]
  simpa [List.append_assoc] using
    singletonTerminalPairProbeDescription_run_rewind_right
      canonicalTarget rightBoundaryTarget pfxRev true
      (some true :: some b0 :: some b1 :: none :: padding)

private theorem singletonTerminalPairProbeDescription_run_terminal_canonical_false_from_state2
    (canonicalTarget rightBoundaryTarget : Nat)
    (pfxRev : Word Bool) (c1 : Bool)
    (padding : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig
        (pfxRev.length + 6)
        { state := 2
          tape :=
            tapeAtCells
              (some false :: some c1 :: some false ::
                List.append (pfxRev.map some) [none])
              (some false :: none :: padding) } =
      { state := canonicalTarget
        tape :=
          tapeAtCells []
            (none ::
              List.append (pfxRev.reverse.map some)
                (some false :: some c1 :: some false :: some false ::
                  none :: padding)) } := by
  rw [show pfxRev.length + 6 = 4 + (pfxRev.length + 2) by
    lia]
  rw [MachineDescription.runConfig_add]
  have hterminal :
      (singletonTerminalPairProbeDescription
        canonicalTarget rightBoundaryTarget).runConfig 4
        { state := 2
          tape :=
            tapeAtCells
              (some false :: some c1 :: some false ::
                List.append (pfxRev.map some) [none])
              (some false :: none :: padding) } =
      { state := 7
        tape :=
          Tape.move Direction.left
            (tapeAtCells
              (List.append (pfxRev.map some) [none])
              (some false :: some c1 :: some false :: some false ::
                none :: padding)) } := by
    cases c1 <;> cases padding <;>
      simp [singletonTerminalPairProbeDescription,
        MachineDescription.runConfig, MachineDescription.stepConfig,
        MachineDescription.lookupTransition,
        MachineDescription.Matches, transition, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft]
  rw [hterminal]
  simpa [List.append_assoc] using
    singletonTerminalPairProbeDescription_run_rewind_canonical_after_left
      canonicalTarget rightBoundaryTarget pfxRev false
      (some c1 :: some false :: some false :: none :: padding)

private theorem singletonTerminalPairProbeDescription_run_terminal_canonical_true_from_state2
    (canonicalTarget rightBoundaryTarget : Nat)
    (pfxRev : Word Bool) (padding : List (Option Bool)) :
    (singletonTerminalPairProbeDescription
      canonicalTarget rightBoundaryTarget).runConfig
        (pfxRev.length + 8)
        { state := 2
          tape :=
            tapeAtCells
              (some false :: some false :: some true ::
                List.append (pfxRev.map some) [none])
              (some false :: none :: padding) } =
      { state := canonicalTarget
        tape :=
          tapeAtCells []
            (none ::
              List.append
                ((List.append pfxRev.reverse [true]).map some)
                (some false :: some false :: some false ::
                  none :: padding)) } := by
  rw [show pfxRev.length + 8 = 5 + (pfxRev.length + 3) by
    lia]
  rw [MachineDescription.runConfig_add]
  have hterminal :
      (singletonTerminalPairProbeDescription
        canonicalTarget rightBoundaryTarget).runConfig 5
        { state := 2
          tape :=
            tapeAtCells
              (some false :: some false :: some true ::
                List.append (pfxRev.map some) [none])
              (some false :: none :: padding) } =
      { state := 7
        tape :=
          tapeAtCells
            (List.append (pfxRev.map some) [none])
            (some true :: some false :: some false :: some false ::
              none :: padding) } := by
    cases padding <;>
      simp [singletonTerminalPairProbeDescription,
        MachineDescription.runConfig, MachineDescription.stepConfig,
        MachineDescription.lookupTransition,
        MachineDescription.Matches, transition, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft,
        Tape.moveRight]
  rw [hterminal]
  simpa [List.append_assoc] using
    singletonTerminalPairProbeDescription_run_rewind_canonical
      canonicalTarget rightBoundaryTarget pfxRev true
      (some false :: some false :: some false :: none :: padding)

theorem singletonTerminalPairProbeDescription_reaches_rightBoundary_bits
    (canonicalTarget rightBoundaryTarget : Nat)
    (pfxBits : Word Bool) (head : Option Bool)
    (padding : List (Option Bool)) :
    exists steps : Nat,
      (singletonTerminalPairProbeDescription
        canonicalTarget rightBoundaryTarget).runConfig steps
        { state :=
            (singletonTerminalPairProbeDescription
              canonicalTarget rightBoundaryTarget).start
          tape :=
            tapeAtCells []
              (none ::
                List.append
                  ((List.append pfxBits
                    (List.append [true, true]
                      (logicalCellBits head))).map some)
                  (none :: padding)) } =
      { state := rightBoundaryTarget
        tape :=
          tapeAtCells []
            (none ::
              List.append
                ((List.append pfxBits
                  (List.append [true, true]
                    (logicalCellBits head))).map some)
                (none :: padding)) } := by
  cases head with
  | none =>
      let bits : Word Bool :=
        List.append pfxBits
          (List.append [true, true]
            (logicalCellBits (none : Option Bool)))
      refine ⟨(1 + (bits.length + 1)) + (pfxBits.length + 8), ?_⟩
      change
        (singletonTerminalPairProbeDescription
          canonicalTarget rightBoundaryTarget).runConfig
            ((1 + (bits.length + 1)) + (pfxBits.length + 8))
            { state :=
                (singletonTerminalPairProbeDescription
                  canonicalTarget rightBoundaryTarget).start
              tape :=
                tapeAtCells []
                  (none ::
                    List.append (bits.map some) (none :: padding)) } =
          { state := rightBoundaryTarget
            tape :=
              tapeAtCells []
                (none ::
                  List.append (bits.map some) (none :: padding)) }
      rw [MachineDescription.runConfig_add]
      have hentry :
          (singletonTerminalPairProbeDescription
            canonicalTarget rightBoundaryTarget).runConfig
              (1 + (bits.length + 1))
              { state :=
                  (singletonTerminalPairProbeDescription
                    canonicalTarget rightBoundaryTarget).start
                tape :=
                  tapeAtCells []
                    (none ::
                      List.append (bits.map some) (none :: padding)) } =
            { state := 2
              tape :=
                tapeAtCells
                  (some false :: some true :: some true ::
                    List.append (pfxBits.reverse.map some) [none])
                  (some false :: none :: padding) } := by
        rw [MachineDescription.runConfig_add]
        rw [singletonTerminalPairProbeDescription_step_start]
        rw [singletonTerminalPairProbeDescription_run_scan_to_terminal_from_left]
        simp [bits, logicalCellBits, List.reverse_append,
          tapeAtCells, Tape.move, Tape.moveLeft]
      rw [hentry]
      simpa [bits, logicalCellBits, List.map_append, List.append_assoc]
        using
          singletonTerminalPairProbeDescription_run_terminal_right_from_state2
            canonicalTarget rightBoundaryTarget pfxBits.reverse false false
            padding
  | some bit =>
      cases bit
      · let bits : Word Bool :=
          List.append pfxBits
            (List.append [true, true]
              (logicalCellBits (some false)))
        refine ⟨(1 + (bits.length + 1)) + (pfxBits.length + 8), ?_⟩
        change
          (singletonTerminalPairProbeDescription
            canonicalTarget rightBoundaryTarget).runConfig
              ((1 + (bits.length + 1)) + (pfxBits.length + 8))
              { state :=
                  (singletonTerminalPairProbeDescription
                    canonicalTarget rightBoundaryTarget).start
                tape :=
                  tapeAtCells []
                    (none ::
                      List.append (bits.map some) (none :: padding)) } =
            { state := rightBoundaryTarget
              tape :=
                tapeAtCells []
                  (none ::
                    List.append (bits.map some) (none :: padding)) }
        rw [MachineDescription.runConfig_add]
        have hentry :
            (singletonTerminalPairProbeDescription
              canonicalTarget rightBoundaryTarget).runConfig
                (1 + (bits.length + 1))
                { state :=
                    (singletonTerminalPairProbeDescription
                      canonicalTarget rightBoundaryTarget).start
                  tape :=
                    tapeAtCells []
                      (none ::
                        List.append (bits.map some) (none :: padding)) } =
              { state := 2
                tape :=
                  tapeAtCells
                    (some false :: some true :: some true ::
                      List.append (pfxBits.reverse.map some) [none])
                    (some true :: none :: padding) } := by
          rw [MachineDescription.runConfig_add]
          rw [singletonTerminalPairProbeDescription_step_start]
          rw [singletonTerminalPairProbeDescription_run_scan_to_terminal_from_left]
          simp [bits, logicalCellBits, List.reverse_append,
            tapeAtCells, Tape.move, Tape.moveLeft]
        rw [hentry]
        simpa [bits, logicalCellBits, List.map_append, List.append_assoc]
          using
            singletonTerminalPairProbeDescription_run_terminal_right_from_state2
              canonicalTarget rightBoundaryTarget pfxBits.reverse false true
              padding
      · let bits : Word Bool :=
          List.append pfxBits
            (List.append [true, true]
              (logicalCellBits (some true)))
        refine ⟨(1 + (bits.length + 1)) + (pfxBits.length + 8), ?_⟩
        change
          (singletonTerminalPairProbeDescription
            canonicalTarget rightBoundaryTarget).runConfig
              ((1 + (bits.length + 1)) + (pfxBits.length + 8))
              { state :=
                  (singletonTerminalPairProbeDescription
                    canonicalTarget rightBoundaryTarget).start
                tape :=
                  tapeAtCells []
                    (none ::
                      List.append (bits.map some) (none :: padding)) } =
            { state := rightBoundaryTarget
              tape :=
                tapeAtCells []
                  (none ::
                    List.append (bits.map some) (none :: padding)) }
        rw [MachineDescription.runConfig_add]
        have hentry :
            (singletonTerminalPairProbeDescription
              canonicalTarget rightBoundaryTarget).runConfig
                (1 + (bits.length + 1))
                { state :=
                    (singletonTerminalPairProbeDescription
                      canonicalTarget rightBoundaryTarget).start
                  tape :=
                    tapeAtCells []
                      (none ::
                        List.append (bits.map some) (none :: padding)) } =
              { state := 2
                tape :=
                  tapeAtCells
                    (some true :: some true :: some true ::
                      List.append (pfxBits.reverse.map some) [none])
                    (some false :: none :: padding) } := by
          rw [MachineDescription.runConfig_add]
          rw [singletonTerminalPairProbeDescription_step_start]
          rw [singletonTerminalPairProbeDescription_run_scan_to_terminal_from_left]
          simp [bits, logicalCellBits, List.reverse_append,
            tapeAtCells, Tape.move, Tape.moveLeft]
        rw [hentry]
        simpa [bits, logicalCellBits, List.map_append, List.append_assoc]
          using
          singletonTerminalPairProbeDescription_run_terminal_right_from_state2
            canonicalTarget rightBoundaryTarget pfxBits.reverse true false
            padding

theorem singletonTerminalPairProbeDescription_reaches_canonical_bits
    (canonicalTarget rightBoundaryTarget : Nat)
    (pfxBits : Word Bool) (cell : Option Bool)
    (padding : List (Option Bool)) :
    exists steps : Nat,
      (singletonTerminalPairProbeDescription
        canonicalTarget rightBoundaryTarget).runConfig steps
        { state :=
            (singletonTerminalPairProbeDescription
              canonicalTarget rightBoundaryTarget).start
          tape :=
            tapeAtCells []
              (none ::
                List.append
                  ((List.append pfxBits
                    (List.append (logicalCellBits cell)
                      (logicalCellBits none))).map some)
                  (none :: padding)) } =
      { state := canonicalTarget
        tape :=
          tapeAtCells []
            (none ::
              List.append
                ((List.append pfxBits
                  (List.append (logicalCellBits cell)
                    (logicalCellBits none))).map some)
                (none :: padding)) } := by
  cases cell with
  | none =>
      let bits : Word Bool :=
        List.append pfxBits
          (List.append (logicalCellBits (none : Option Bool))
            (logicalCellBits none))
      refine ⟨(1 + (bits.length + 1)) + (pfxBits.length + 6), ?_⟩
      change
        (singletonTerminalPairProbeDescription
          canonicalTarget rightBoundaryTarget).runConfig
            ((1 + (bits.length + 1)) + (pfxBits.length + 6))
            { state :=
                (singletonTerminalPairProbeDescription
                  canonicalTarget rightBoundaryTarget).start
              tape :=
                tapeAtCells []
                  (none ::
                    List.append (bits.map some) (none :: padding)) } =
          { state := canonicalTarget
            tape :=
              tapeAtCells []
                (none ::
                  List.append (bits.map some) (none :: padding)) }
      rw [MachineDescription.runConfig_add]
      have hentry :
          (singletonTerminalPairProbeDescription
            canonicalTarget rightBoundaryTarget).runConfig
              (1 + (bits.length + 1))
              { state :=
                  (singletonTerminalPairProbeDescription
                    canonicalTarget rightBoundaryTarget).start
                tape :=
                  tapeAtCells []
                    (none ::
                      List.append (bits.map some) (none :: padding)) } =
            { state := 2
              tape :=
                tapeAtCells
                  (some false :: some false :: some false ::
                    List.append (pfxBits.reverse.map some) [none])
                  (some false :: none :: padding) } := by
        rw [MachineDescription.runConfig_add]
        rw [singletonTerminalPairProbeDescription_step_start]
        rw [singletonTerminalPairProbeDescription_run_scan_to_terminal_from_left]
        simp [bits, logicalCellBits, List.reverse_append,
          tapeAtCells, Tape.move, Tape.moveLeft]
      rw [hentry]
      simpa [bits, logicalCellBits, List.map_append, List.append_assoc]
        using
          singletonTerminalPairProbeDescription_run_terminal_canonical_false_from_state2
            canonicalTarget rightBoundaryTarget pfxBits.reverse false
            padding
  | some bit =>
      cases bit
      · let bits : Word Bool :=
          List.append pfxBits
            (List.append (logicalCellBits (some false))
              (logicalCellBits none))
        refine ⟨(1 + (bits.length + 1)) + (pfxBits.length + 6), ?_⟩
        change
          (singletonTerminalPairProbeDescription
            canonicalTarget rightBoundaryTarget).runConfig
              ((1 + (bits.length + 1)) + (pfxBits.length + 6))
              { state :=
                  (singletonTerminalPairProbeDescription
                    canonicalTarget rightBoundaryTarget).start
                tape :=
                  tapeAtCells []
                    (none ::
                      List.append (bits.map some) (none :: padding)) } =
            { state := canonicalTarget
              tape :=
                tapeAtCells []
                  (none ::
                    List.append (bits.map some) (none :: padding)) }
        rw [MachineDescription.runConfig_add]
        have hentry :
            (singletonTerminalPairProbeDescription
              canonicalTarget rightBoundaryTarget).runConfig
                (1 + (bits.length + 1))
                { state :=
                    (singletonTerminalPairProbeDescription
                      canonicalTarget rightBoundaryTarget).start
                  tape :=
                    tapeAtCells []
                      (none ::
                        List.append (bits.map some) (none :: padding)) } =
              { state := 2
                tape :=
                  tapeAtCells
                    (some false :: some true :: some false ::
                      List.append (pfxBits.reverse.map some) [none])
                    (some false :: none :: padding) } := by
          rw [MachineDescription.runConfig_add]
          rw [singletonTerminalPairProbeDescription_step_start]
          rw [singletonTerminalPairProbeDescription_run_scan_to_terminal_from_left]
          simp [bits, logicalCellBits, List.reverse_append,
            tapeAtCells, Tape.move, Tape.moveLeft]
        rw [hentry]
        simpa [bits, logicalCellBits, List.map_append, List.append_assoc]
          using
            singletonTerminalPairProbeDescription_run_terminal_canonical_false_from_state2
              canonicalTarget rightBoundaryTarget pfxBits.reverse true
              padding
      · let bits : Word Bool :=
          List.append pfxBits
            (List.append (logicalCellBits (some true))
              (logicalCellBits none))
        refine ⟨(1 + (bits.length + 1)) + (pfxBits.length + 8), ?_⟩
        change
          (singletonTerminalPairProbeDescription
            canonicalTarget rightBoundaryTarget).runConfig
              ((1 + (bits.length + 1)) + (pfxBits.length + 8))
              { state :=
                  (singletonTerminalPairProbeDescription
                    canonicalTarget rightBoundaryTarget).start
                tape :=
                  tapeAtCells []
                    (none ::
                      List.append (bits.map some) (none :: padding)) } =
            { state := canonicalTarget
              tape :=
                tapeAtCells []
                  (none ::
                    List.append (bits.map some) (none :: padding)) }
        rw [MachineDescription.runConfig_add]
        have hentry :
            (singletonTerminalPairProbeDescription
              canonicalTarget rightBoundaryTarget).runConfig
                (1 + (bits.length + 1))
                { state :=
                    (singletonTerminalPairProbeDescription
                      canonicalTarget rightBoundaryTarget).start
                  tape :=
                    tapeAtCells []
                      (none ::
                        List.append (bits.map some) (none :: padding)) } =
              { state := 2
                tape :=
                  tapeAtCells
                    (some false :: some false :: some true ::
                      List.append (pfxBits.reverse.map some) [none])
                    (some false :: none :: padding) } := by
          rw [MachineDescription.runConfig_add]
          rw [singletonTerminalPairProbeDescription_step_start]
          rw [singletonTerminalPairProbeDescription_run_scan_to_terminal_from_left]
          simp [bits, logicalCellBits, List.reverse_append,
            tapeAtCells, Tape.move, Tape.moveLeft]
        rw [hentry]
        simpa [bits, logicalCellBits, List.map_append, List.append_assoc]
          using
            singletonTerminalPairProbeDescription_run_terminal_canonical_true_from_state2
              canonicalTarget rightBoundaryTarget pfxBits.reverse
              padding

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

theorem physicalTokenListCode_terminal_cell_guard
    (pfx : List PhysicalToken) (cell : Option Bool) :
    physicalTokenListCode
        (List.append pfx
          [PhysicalToken.logicalCell cell,
            PhysicalToken.logicalCell none]) =
      List.append (physicalTokenListCode pfx)
        (List.append (logicalCellCode cell)
          (logicalCellCode none)) := by
  rw [physicalTokenListCode_append]
  rfl

theorem physicalTokenListCode_terminal_head_cell
    (pfx : List PhysicalToken) (head : Option Bool) :
    physicalTokenListCode
        (List.append pfx
          [PhysicalToken.headMarker,
            PhysicalToken.logicalCell head]) =
      List.append (physicalTokenListCode pfx)
        (List.append headMarkerCells (logicalCellCode head)) := by
  rw [physicalTokenListCode_append]
  change
      List.append (physicalTokenListCode pfx)
        (List.append headMarkerCells
          (List.append (logicalCellCode head) [])) =
      List.append (physicalTokenListCode pfx)
        (List.append headMarkerCells (logicalCellCode head))
  exact
    congrArg
      (fun tail =>
        List.append (physicalTokenListCode pfx)
          (List.append headMarkerCells tail))
      (List.append_nil (logicalCellCode head))

theorem SingletonGuardSlackEndpointShape.canonical_singleton_code_terminal_cell_guard
    (target : Tape Bool) :
    exists (pfxCells : List (Option Bool)) (cell : Option Bool),
      logicalTapeCode (guardLogicalTape target) =
        List.append pfxCells
          (List.append (logicalCellCode cell)
            (logicalCellCode none)) := by
  rcases
      SingletonGuardSlackEndpointShape.canonical_singleton_tokens_terminal_cell_guard
        target with
    ⟨pfx, cell, htokens⟩
  refine ⟨physicalTokenListCode pfx, cell, ?_⟩
  have hcode := congrArg physicalTokenListCode htokens
  simp only [physicalTokenListCode_logicalTapeTokens] at hcode
  rw [physicalTokenListCode_terminal_cell_guard] at hcode
  exact hcode

theorem SingletonGuardSlackEndpointShape.rightBoundary_code_terminal_head
    (left : List (Option Bool)) (head : Option Bool) :
    logicalTapeCode
        ({ left := left ++ [none], head := head, right := [] } :
          Tape Bool) =
      List.append (logicalCellListCode (none :: left.reverse))
        (List.append headMarkerCells (logicalCellCode head)) := by
  have htokens :=
    SingletonGuardSlackEndpointShape.rightBoundary_tokens_terminal_head
      left head
  have hcode := congrArg physicalTokenListCode htokens
  rw [physicalTokenListCode_terminal_head_cell] at hcode
  simp only [physicalTokenListCode_logicalTapeTokens,
    physicalTokenListCode_logicalCellListTokens] at hcode
  exact hcode

theorem SingletonGuardSlackEndpointShape.afterOpening_read_false_terminal_code_cases
    {target : List (Tape Bool)} {physical : Tape Bool}
    (hshape : SingletonGuardSlackEndpointShape target physical)
    (hread : Tape.read (Tape.moveRight physical) = some false) :
    (exists (targetTape : Tape Bool) (pfxCells : List (Option Bool))
        (cell : Option Bool),
      target = [targetTape] ∧
        physical = encodedGuardedStructuredTapes [targetTape] ∧
        logicalTapeCode (guardLogicalTape targetTape) =
          List.append pfxCells
            (List.append (logicalCellCode cell)
              (logicalCellCode none))) ∨
      exists (left : List (Option Bool)) (head : Option Bool),
        target =
          [({ left := left, head := head, right := [] } : Tape Bool)] ∧
          physical =
            encodedStructuredTapes
              [({ left := left ++ [none], head := head, right := [] } :
                Tape Bool)] ∧
          logicalTapeCode
              ({ left := left ++ [none], head := head, right := [] } :
                Tape Bool) =
            List.append (logicalCellListCode (none :: left.reverse))
              (List.append headMarkerCells (logicalCellCode head)) := by
  cases
      SingletonGuardSlackEndpointShape.afterOpening_read_false_cases
        hshape hread with
  | inl hcanonical =>
      rcases hcanonical with ⟨targetTape, htarget, hphysical⟩
      rcases
          SingletonGuardSlackEndpointShape.canonical_singleton_code_terminal_cell_guard
            targetTape with
        ⟨pfxCells, cell, hcode⟩
      exact
        Or.inl
          ⟨targetTape, pfxCells, cell, htarget, hphysical, hcode⟩
  | inr hright =>
      rcases hright with ⟨left, head, htarget, hphysical⟩
      exact
        Or.inr
          ⟨left, head, htarget, hphysical,
            SingletonGuardSlackEndpointShape.rightBoundary_code_terminal_head
              left head⟩

theorem SingletonGuardSlackEndpointShape.canonical_singleton_physical_terminal_cell_guard
    (target : Tape Bool) :
    exists (pfxCells : List (Option Bool)) (cell : Option Bool),
      encodedGuardedStructuredTapes [target] =
        tapeAtCells []
          (List.append tapeSeparatorCells
            (List.append pfxCells
              (List.append (logicalCellCode cell)
                (List.append (logicalCellCode none)
                  tapeSeparatorCells)))) := by
  rcases
      SingletonGuardSlackEndpointShape.canonical_singleton_code_terminal_cell_guard
        target with
    ⟨pfxCells, cell, hcode⟩
  refine ⟨pfxCells, cell, ?_⟩
  change
    tapeAtCells []
        (List.append tapeSeparatorCells
          (List.append (logicalTapeCode (guardLogicalTape target))
            tapeSeparatorCells)) =
      tapeAtCells []
        (List.append tapeSeparatorCells
          (List.append pfxCells
            (List.append (logicalCellCode cell)
              (List.append (logicalCellCode none)
                tapeSeparatorCells))))
  rw [hcode]
  simp [List.append_assoc]

theorem SingletonGuardSlackEndpointShape.rightBoundary_physical_terminal_head
    (left : List (Option Bool)) (head : Option Bool) :
    encodedStructuredTapes
        [({ left := left ++ [none], head := head, right := [] } :
          Tape Bool)] =
      tapeAtCells []
        (List.append tapeSeparatorCells
          (List.append (logicalCellListCode (none :: left.reverse))
            (List.append headMarkerCells
              (List.append (logicalCellCode head)
                tapeSeparatorCells)))) := by
  simp [encodedStructuredTapes, encodedStructuredTapeCells,
    SingletonGuardSlackEndpointShape.rightBoundary_code_terminal_head,
    List.append_assoc]

theorem SingletonGuardSlackEndpointShape.afterOpening_read_false_physical_terminal_code_cases
    {target : List (Tape Bool)} {physical : Tape Bool}
    (hshape : SingletonGuardSlackEndpointShape target physical)
    (hread : Tape.read (Tape.moveRight physical) = some false) :
    (exists (targetTape : Tape Bool) (pfxCells : List (Option Bool))
        (cell : Option Bool),
      target = [targetTape] ∧
        physical =
          tapeAtCells []
            (List.append tapeSeparatorCells
              (List.append pfxCells
                (List.append (logicalCellCode cell)
                  (List.append (logicalCellCode none)
                    tapeSeparatorCells))))) ∨
      exists (left : List (Option Bool)) (head : Option Bool),
        target =
          [({ left := left, head := head, right := [] } : Tape Bool)] ∧
          physical =
            tapeAtCells []
              (List.append tapeSeparatorCells
                (List.append (logicalCellListCode (none :: left.reverse))
                  (List.append headMarkerCells
                    (List.append (logicalCellCode head)
                      tapeSeparatorCells)))) := by
  cases
      SingletonGuardSlackEndpointShape.afterOpening_read_false_terminal_code_cases
        hshape hread with
  | inl hcanonical =>
      rcases hcanonical with
        ⟨targetTape, pfxCells, cell, htarget, hphysical, hcode⟩
      left
      refine ⟨targetTape, pfxCells, cell, htarget, ?_⟩
      rw [hphysical]
      change
        tapeAtCells []
            (List.append tapeSeparatorCells
              (List.append (logicalTapeCode (guardLogicalTape targetTape))
                tapeSeparatorCells)) =
          tapeAtCells []
            (List.append tapeSeparatorCells
              (List.append pfxCells
                (List.append (logicalCellCode cell)
                  (List.append (logicalCellCode none)
                    tapeSeparatorCells))))
      rw [hcode]
      simp [List.append_assoc]
  | inr hright =>
      rcases hright with
        ⟨left, head, htarget, hphysical, hcode⟩
      right
      refine ⟨left, head, htarget, ?_⟩
      rw [hphysical]
      simp [encodedStructuredTapes, encodedStructuredTapeCells, hcode,
        List.append_assoc]

theorem logicalCellListBits_cons_append_none_terminal
    (cell : Option Bool) (rest : List (Option Bool)) :
    exists (pfx : Word Bool) (last : Option Bool),
      logicalCellListBits (cell :: rest ++ [none]) =
        List.append pfx
          (List.append (logicalCellBits last)
            (logicalCellBits none)) := by
  induction rest generalizing cell with
  | nil =>
      exact ⟨[], cell, by simp [logicalCellListBits]⟩
  | cons next tail ih =>
      rcases ih next with ⟨pfx, last, htail⟩
      refine ⟨List.append (logicalCellBits cell) pfx, last, ?_⟩
      change
        List.append (logicalCellBits cell)
            (logicalCellListBits (next :: tail ++ [none])) =
          List.append (List.append (logicalCellBits cell) pfx)
            (List.append (logicalCellBits last)
              (logicalCellBits none))
      rw [htail]
      simp [List.append_assoc]

theorem SingletonGuardSlackEndpointShape.canonical_singleton_bits_terminal_cell_guard
    (target : Tape Bool) :
    exists (pfxBits : Word Bool) (cell : Option Bool),
      logicalTapeBits (guardLogicalTape target) =
        List.append pfxBits
          (List.append (logicalCellBits cell)
            (logicalCellBits none)) := by
  cases target with
  | mk left head right =>
      rcases
          logicalCellListBits_cons_append_none_terminal
            head right with
        ⟨pfx, cell, htail⟩
      have hcellTail :
          List.append (logicalCellBits head)
              (logicalCellListBits (right ++ [none])) =
            List.append pfx
              (List.append (logicalCellBits cell)
                (logicalCellBits none)) := by
        simpa [logicalCellListBits] using htail
      refine
        ⟨List.append
          (List.append
            (logicalCellListBits
              (List.reverse (left ++ [none])))
            [true, true])
          pfx, cell, ?_⟩
      have htail' :
          List.append (logicalCellBits head)
              (List.append (logicalCellListBits right)
                (logicalCellListBits [none])) =
            List.append pfx
              (List.append (logicalCellBits cell)
                (logicalCellBits none)) := by
        simpa [logicalCellListBits_append, List.append_assoc]
          using hcellTail
      simp [logicalTapeBits, guardLogicalTape, List.append_assoc]
      exact
        congrArg
          (fun tail =>
            List.append (logicalCellListBits (none :: left.reverse))
              (true :: true :: tail))
          htail'

theorem SingletonGuardSlackEndpointShape.rightBoundary_bits_terminal_head
    (left : List (Option Bool)) (head : Option Bool) :
    logicalTapeBits
        ({ left := left ++ [none], head := head, right := [] } :
          Tape Bool) =
      List.append (logicalCellListBits (none :: left.reverse))
        (List.append [true, true] (logicalCellBits head)) := by
  simp [logicalTapeBits, logicalCellListBits, List.reverse_append,
    List.append_assoc]

theorem SingletonGuardSlackEndpointShape.canonical_singleton_physical_terminal_bits
    (target : Tape Bool) :
    exists (pfxBits : Word Bool) (cell : Option Bool),
      encodedGuardedStructuredTapes [target] =
        tapeAtCells []
          (List.append tapeSeparatorCells
            (List.append
              (List.map some
                (List.append pfxBits
                  (List.append (logicalCellBits cell)
                    (logicalCellBits none))))
              tapeSeparatorCells)) := by
  rcases
      SingletonGuardSlackEndpointShape.canonical_singleton_bits_terminal_cell_guard
        target with
    ⟨pfxBits, cell, hbits⟩
  refine ⟨pfxBits, cell, ?_⟩
  simp [encodedGuardedStructuredTapes, guardLogicalTapes,
    encodedStructuredTapes, encodedStructuredTapeCells,
    logicalTapeCode_eq_map_some, hbits]

theorem SingletonGuardSlackEndpointShape.rightBoundary_physical_terminal_bits
    (left : List (Option Bool)) (head : Option Bool) :
    encodedStructuredTapes
        [({ left := left ++ [none], head := head, right := [] } :
          Tape Bool)] =
      tapeAtCells []
        (List.append tapeSeparatorCells
          (List.append
            (List.map some
              (List.append (logicalCellListBits (none :: left.reverse))
                (List.append [true, true] (logicalCellBits head))))
            tapeSeparatorCells)) := by
  simp [encodedStructuredTapes, encodedStructuredTapeCells,
    logicalTapeCode_eq_map_some,
    SingletonGuardSlackEndpointShape.rightBoundary_bits_terminal_head]

theorem singletonTerminalPairProbeDescription_reaches_canonical
    (canonicalTarget rightBoundaryTarget : Nat)
    (target : Tape Bool) :
    exists steps : Nat,
      (singletonTerminalPairProbeDescription
        canonicalTarget rightBoundaryTarget).runConfig steps
        { state :=
            (singletonTerminalPairProbeDescription
              canonicalTarget rightBoundaryTarget).start
          tape := encodedGuardedStructuredTapes [target] } =
      { state := canonicalTarget
        tape := encodedGuardedStructuredTapes [target] } := by
  rcases
      SingletonGuardSlackEndpointShape.canonical_singleton_physical_terminal_bits
        target with
    ⟨pfxBits, cell, hphysical⟩
  rw [hphysical]
  simpa [tapeSeparatorCells, List.map_append, List.append_assoc] using
    singletonTerminalPairProbeDescription_reaches_canonical_bits
      canonicalTarget rightBoundaryTarget pfxBits cell []

theorem singletonTerminalPairProbeDescription_reaches_canonical_cons
    (canonicalTarget rightBoundaryTarget : Nat)
    (target : Tape Bool) (rest : List (Tape Bool)) :
    exists steps : Nat,
      (singletonTerminalPairProbeDescription
        canonicalTarget rightBoundaryTarget).runConfig steps
        { state :=
            (singletonTerminalPairProbeDescription
              canonicalTarget rightBoundaryTarget).start
          tape := encodedStructuredTapes (guardLogicalTape target :: rest) } =
      { state := canonicalTarget
        tape := encodedStructuredTapes (guardLogicalTape target :: rest) } := by
  rcases
      SingletonGuardSlackEndpointShape.canonical_singleton_bits_terminal_cell_guard
        target with
    ⟨pfxBits, cell, hbits⟩
  rcases encodedStructuredTapeCells_startsWith_separator rest with
    ⟨padding, hpadding⟩
  simpa [encodedStructuredTapes, encodedStructuredTapeCells,
    logicalTapeCode_eq_map_some, hbits, hpadding, tapeSeparatorCells,
    List.map_append, List.append_assoc] using
    singletonTerminalPairProbeDescription_reaches_canonical_bits
      canonicalTarget rightBoundaryTarget pfxBits cell padding

theorem singletonTerminalPairProbeDescription_reaches_rightBoundary
    (canonicalTarget rightBoundaryTarget : Nat)
    (left : List (Option Bool)) (head : Option Bool) :
    exists steps : Nat,
      (singletonTerminalPairProbeDescription
        canonicalTarget rightBoundaryTarget).runConfig steps
        { state :=
            (singletonTerminalPairProbeDescription
              canonicalTarget rightBoundaryTarget).start
          tape :=
            encodedStructuredTapes
              [({ left := left ++ [none], head := head, right := [] } :
                Tape Bool)] } =
      { state := rightBoundaryTarget
        tape :=
          encodedStructuredTapes
            [({ left := left ++ [none], head := head, right := [] } :
              Tape Bool)] } := by
  rw [
    SingletonGuardSlackEndpointShape.rightBoundary_physical_terminal_bits
      left head]
  simpa [tapeSeparatorCells, List.map_append, List.append_assoc] using
    singletonTerminalPairProbeDescription_reaches_rightBoundary_bits
      canonicalTarget rightBoundaryTarget
      (logicalCellListBits (none :: left.reverse)) head []

theorem singletonTerminalPairProbeDescription_reaches_rightBoundary_cons
    (canonicalTarget rightBoundaryTarget : Nat)
    (left : List (Option Bool)) (head : Option Bool)
    (rest : List (Tape Bool)) :
    exists steps : Nat,
      (singletonTerminalPairProbeDescription
        canonicalTarget rightBoundaryTarget).runConfig steps
        { state :=
            (singletonTerminalPairProbeDescription
              canonicalTarget rightBoundaryTarget).start
          tape :=
            encodedStructuredTapes
              (({ left := left ++ [none], head := head, right := [] } :
                Tape Bool) :: rest) } =
      { state := rightBoundaryTarget
        tape :=
          encodedStructuredTapes
            (({ left := left ++ [none], head := head, right := [] } :
              Tape Bool) :: rest) } := by
  rcases encodedStructuredTapeCells_startsWith_separator rest with
    ⟨padding, hpadding⟩
  simpa [encodedStructuredTapes, encodedStructuredTapeCells,
    logicalTapeCode_eq_map_some,
    SingletonGuardSlackEndpointShape.rightBoundary_bits_terminal_head,
    hpadding, tapeSeparatorCells, List.map_append, List.append_assoc] using
    singletonTerminalPairProbeDescription_reaches_rightBoundary_bits
      canonicalTarget rightBoundaryTarget
      (logicalCellListBits (none :: left.reverse)) head padding

theorem singletonTerminalPairProbeDescription_reaches_of_afterOpening_read_false
    (canonicalTarget rightBoundaryTarget : Nat)
    {target : List (Tape Bool)} {physical : Tape Bool}
    (hshape : SingletonGuardSlackEndpointShape target physical)
    (hread : Tape.read (Tape.moveRight physical) = some false) :
    (exists (targetTape : Tape Bool) (steps : Nat),
      target = [targetTape] ∧
        physical = encodedGuardedStructuredTapes [targetTape] ∧
        (singletonTerminalPairProbeDescription
          canonicalTarget rightBoundaryTarget).runConfig steps
          { state :=
              (singletonTerminalPairProbeDescription
                canonicalTarget rightBoundaryTarget).start
            tape := physical } =
        { state := canonicalTarget
          tape := physical }) ∨
      exists (left : List (Option Bool)) (head : Option Bool)
          (steps : Nat),
        target =
          [({ left := left, head := head, right := [] } : Tape Bool)] ∧
          physical =
            encodedStructuredTapes
              [({ left := left ++ [none], head := head, right := [] } :
                Tape Bool)] ∧
          (singletonTerminalPairProbeDescription
            canonicalTarget rightBoundaryTarget).runConfig steps
            { state :=
                (singletonTerminalPairProbeDescription
                  canonicalTarget rightBoundaryTarget).start
              tape := physical } =
          { state := rightBoundaryTarget
            tape := physical } := by
  cases
      SingletonGuardSlackEndpointShape.afterOpening_read_false_cases
        hshape hread with
  | inl hcanonical =>
      rcases hcanonical with ⟨targetTape, htarget, hphysical⟩
      rcases
          singletonTerminalPairProbeDescription_reaches_canonical
            canonicalTarget rightBoundaryTarget targetTape with
        ⟨steps, hrun⟩
      left
      refine ⟨targetTape, steps, htarget, hphysical, ?_⟩
      rw [hphysical]
      exact hrun
  | inr hright =>
      rcases hright with ⟨left, head, htarget, hphysical⟩
      rcases
          singletonTerminalPairProbeDescription_reaches_rightBoundary
            canonicalTarget rightBoundaryTarget left head with
        ⟨steps, hrun⟩
      right
      refine ⟨left, head, steps, htarget, hphysical, ?_⟩
      rw [hphysical]
      exact hrun

/-!
## Fixed singleton-shape dispatcher layout
-/

def singletonShapeRefreshFinalHalt : Nat :=
  2

def singletonShapeLeftRepairOffset : Nat :=
  3

def singletonShapeLeftRepairDescription : MachineDescription :=
  MachineDescription.offsetRetargetDescription
    singletonShapeLeftRepairOffset
    singletonShapeRefreshFinalHalt
    leftBoundaryGuardSlackRefreshDescription

def singletonShapeLeftRepairStart : Nat :=
  singletonShapeLeftRepairDescription.start

def singletonShapeLeftRepairLimit : Nat :=
  singletonShapeLeftRepairDescription.stateCount

def singletonShapeRightRepairOffset : Nat :=
  singletonShapeLeftRepairLimit

def singletonShapeRightRepairDescription : MachineDescription :=
  MachineDescription.offsetRetargetDescription
    singletonShapeRightRepairOffset
    singletonShapeRefreshFinalHalt
    rightBoundaryGuardSlackRefreshDescription

def singletonShapeRightRepairStart : Nat :=
  singletonShapeRightRepairDescription.start

def singletonShapeRightRepairLimit : Nat :=
  singletonShapeRightRepairDescription.stateCount

def singletonShapeTerminalProbeOffset : Nat :=
  singletonShapeRightRepairLimit

def singletonShapeTerminalLocalCanonicalExit : Nat :=
  11

def singletonShapeTerminalLocalRightBoundaryExit : Nat :=
  12

def singletonShapeTerminalLocalUnusedExit : Nat :=
  13

def singletonShapeTerminalLocalTarget : Option Bool -> Nat
  | none => singletonShapeTerminalLocalCanonicalExit
  | some false => singletonShapeTerminalLocalRightBoundaryExit
  | some true => singletonShapeTerminalLocalUnusedExit

def singletonShapeTerminalTarget : Option Bool -> Nat
  | none => singletonShapeRefreshFinalHalt
  | some false => singletonShapeRightRepairStart
  | some true => singletonShapeRefreshFinalHalt

def singletonShapeTerminalLocalDescription : MachineDescription :=
  singletonTerminalPairProbeDescription
    singletonShapeTerminalLocalCanonicalExit
    singletonShapeTerminalLocalRightBoundaryExit

def singletonShapeTerminalProbeDescription : MachineDescription :=
  MachineDescription.offsetReadExitRetargetDescription
    singletonShapeTerminalProbeOffset
    singletonShapeTerminalLocalTarget
    singletonShapeTerminalTarget
    singletonShapeTerminalLocalDescription

def singletonShapeTerminalProbeStart : Nat :=
  singletonShapeTerminalProbeDescription.start

def singletonShapeRefreshOpeningDescription : MachineDescription :=
  singletonOpeningProbeDescription
    singletonShapeTerminalProbeStart
    singletonShapeLeftRepairStart

def singletonShapeRefreshDescription : MachineDescription where
  stateCount := singletonShapeTerminalProbeDescription.stateCount
  start := singletonShapeRefreshOpeningDescription.start
  halt := singletonShapeRefreshFinalHalt
  transitions :=
    singletonShapeRefreshOpeningDescription.transitions ++
      singletonShapeLeftRepairDescription.transitions ++
      singletonShapeRightRepairDescription.transitions ++
      singletonShapeTerminalProbeDescription.transitions

theorem singletonShapeRefreshFinalHalt_lt_leftRepairOffset :
    singletonShapeRefreshFinalHalt < singletonShapeLeftRepairOffset := by
  decide

theorem singletonShapeRefreshFinalHalt_lt_rightRepairOffset :
    singletonShapeRefreshFinalHalt < singletonShapeRightRepairOffset := by
  unfold singletonShapeRightRepairOffset singletonShapeLeftRepairLimit
    singletonShapeLeftRepairDescription
  simp [MachineDescription.offsetRetargetDescription,
    singletonShapeLeftRepairOffset, singletonShapeRefreshFinalHalt]
  lia

theorem singletonShapeLeftRepairDescription_subroutineReady :
    singletonShapeLeftRepairDescription.SubroutineReady :=
  MachineDescription.offsetRetargetDescription_subroutineReady
    singletonShapeRefreshFinalHalt_lt_leftRepairOffset
    leftBoundaryGuardSlackRefreshDescription_subroutineReady.left

theorem singletonShapeRightRepairDescription_subroutineReady :
    singletonShapeRightRepairDescription.SubroutineReady :=
  MachineDescription.offsetRetargetDescription_subroutineReady
    singletonShapeRefreshFinalHalt_lt_rightRepairOffset
    rightBoundaryGuardSlackRefreshDescription_subroutineReady.left

theorem singletonShapeTerminalLocalDescription_subroutineReady :
    singletonShapeTerminalLocalDescription.SubroutineReady :=
  singletonTerminalPairProbeDescription_subroutineReady
    singletonShapeTerminalLocalCanonicalExit
    singletonShapeTerminalLocalRightBoundaryExit

theorem singletonShapeTerminalLocalDescription_transitionFreeAt
    (cell : Option Bool) :
    singletonShapeTerminalLocalDescription.TransitionFreeAt
      (singletonShapeTerminalLocalTarget cell) := by
  cases cell with
  | none =>
      exact
        transition_notFrom_of_all
          (l := singletonShapeTerminalLocalDescription.transitions)
          (state := singletonShapeTerminalLocalTarget none)
          (by decide)
  | some bit =>
      cases bit with
      | false =>
          exact
            transition_notFrom_of_all
              (l := singletonShapeTerminalLocalDescription.transitions)
              (state := singletonShapeTerminalLocalTarget (some false))
              (by decide)
      | true =>
          exact
            transition_notFrom_of_all
              (l := singletonShapeTerminalLocalDescription.transitions)
              (state := singletonShapeTerminalLocalTarget (some true))
              (by decide)

theorem singletonShapeTerminalTarget_lt_probeOffset :
    forall cell : Option Bool,
      singletonShapeTerminalTarget cell <
        singletonShapeTerminalProbeOffset := by
  intro cell
  cases cell with
  | none =>
      have hhalt :=
        singletonShapeRightRepairDescription_subroutineReady.left.right.right.left
      simpa [singletonShapeTerminalTarget,
        singletonShapeTerminalProbeOffset,
        singletonShapeRightRepairLimit,
        singletonShapeRightRepairDescription] using hhalt
  | some bit =>
      cases bit with
      | false =>
          have hstart :=
            singletonShapeRightRepairDescription_subroutineReady.left.right.left
          simpa [singletonShapeTerminalTarget,
            singletonShapeTerminalProbeOffset,
            singletonShapeRightRepairLimit,
            singletonShapeRightRepairStart] using hstart
      | true =>
          have hhalt :=
            singletonShapeRightRepairDescription_subroutineReady.left.right.right.left
          simpa [singletonShapeTerminalTarget,
            singletonShapeTerminalProbeOffset,
            singletonShapeRightRepairLimit,
            singletonShapeRightRepairDescription] using hhalt

theorem singletonShapeTerminalProbeDescription_subroutineReady :
    singletonShapeTerminalProbeDescription.SubroutineReady :=
  MachineDescription.offsetReadExitRetargetDescription_subroutineReady
    singletonShapeTerminalTarget_lt_probeOffset
    singletonShapeTerminalLocalDescription_subroutineReady.left

theorem singletonShapeRefreshOpeningDescription_subroutineReady :
    singletonShapeRefreshOpeningDescription.SubroutineReady :=
  singletonOpeningProbeDescription_subroutineReady
    singletonShapeTerminalProbeStart
    singletonShapeLeftRepairStart

theorem singletonShapeRefreshOpeningDescription_sources_below_leftRepairOffset :
    forall t : TransitionDescription,
      t ∈ singletonShapeRefreshOpeningDescription.transitions ->
        t.source < singletonShapeLeftRepairOffset := by
  intro t ht
  simp [singletonShapeRefreshOpeningDescription,
    singletonOpeningProbeDescription] at ht
  rcases ht with rfl | rfl | rfl <;>
    decide

theorem singletonShapeLeftRepairDescription_sources_in_block :
    forall t : TransitionDescription,
      t ∈ singletonShapeLeftRepairDescription.transitions ->
        singletonShapeLeftRepairOffset ≤ t.source ∧
          t.source < singletonShapeLeftRepairLimit := by
  intro t ht
  rcases List.mem_map.mp (by
      simpa [singletonShapeLeftRepairDescription,
        MachineDescription.offsetRetargetDescription] using ht) with
    ⟨base, hbase, rfl⟩
  have hsource :=
    (leftBoundaryGuardSlackRefreshDescription_subroutineReady.left.right.right.right.left
      base hbase).left
  constructor
  · simp [TransitionDescription.sharedExitRetargetStates]
  · simp [TransitionDescription.sharedExitRetargetStates,
      singletonShapeLeftRepairLimit, singletonShapeLeftRepairDescription,
      MachineDescription.offsetRetargetDescription]
    apply Nat.lt_of_lt_of_le
    · exact Nat.add_lt_add_left hsource singletonShapeLeftRepairOffset
    · exact Nat.le_max_left _ _

theorem singletonShapeRightRepairDescription_sources_in_block :
    forall t : TransitionDescription,
      t ∈ singletonShapeRightRepairDescription.transitions ->
        singletonShapeRightRepairOffset ≤ t.source ∧
          t.source < singletonShapeRightRepairLimit := by
  intro t ht
  rcases List.mem_map.mp (by
      simpa [singletonShapeRightRepairDescription,
        MachineDescription.offsetRetargetDescription] using ht) with
    ⟨base, hbase, rfl⟩
  have hsource :=
    (rightBoundaryGuardSlackRefreshDescription_subroutineReady.left.right.right.right.left
      base hbase).left
  constructor
  · simp [TransitionDescription.sharedExitRetargetStates]
  · simp [TransitionDescription.sharedExitRetargetStates,
      singletonShapeRightRepairLimit, singletonShapeRightRepairDescription,
      MachineDescription.offsetRetargetDescription]
    apply Nat.lt_of_lt_of_le
    · exact Nat.add_lt_add_left hsource singletonShapeRightRepairOffset
    · exact Nat.le_max_left _ _

theorem singletonShapeTerminalProbeDescription_sources_in_block :
    forall t : TransitionDescription,
      t ∈ singletonShapeTerminalProbeDescription.transitions ->
        singletonShapeTerminalProbeOffset ≤ t.source ∧
          t.source < singletonShapeTerminalProbeDescription.stateCount := by
  intro t ht
  rcases List.mem_map.mp (by
      simpa [singletonShapeTerminalProbeDescription,
        MachineDescription.offsetReadExitRetargetDescription] using ht) with
    ⟨base, hbase, rfl⟩
  have hsource :=
    (singletonShapeTerminalLocalDescription_subroutineReady.left.right.right.right.left
      base hbase).left
  constructor
  · simp [MachineDescription.readExitRetargetStates]
  · simp [MachineDescription.readExitRetargetStates,
      singletonShapeTerminalProbeDescription,
      MachineDescription.offsetReadExitRetargetDescription]
    simpa [singletonShapeTerminalLocalDescription] using
      Nat.add_lt_add_left hsource singletonShapeTerminalProbeOffset

theorem singletonShapeLeftRepairOffset_lt_rightRepairOffset :
    singletonShapeLeftRepairOffset < singletonShapeRightRepairOffset := by
  have hstart :=
    singletonShapeLeftRepairDescription_subroutineReady.left.right.left
  simpa [singletonShapeRightRepairOffset, singletonShapeLeftRepairLimit,
    singletonShapeLeftRepairDescription,
    MachineDescription.offsetRetargetDescription] using hstart

theorem singletonShapeLeftRepairOffset_le_rightRepairOffset :
    singletonShapeLeftRepairOffset ≤ singletonShapeRightRepairOffset :=
  Nat.le_of_lt singletonShapeLeftRepairOffset_lt_rightRepairOffset

theorem singletonShapeRightRepairOffset_lt_terminalProbeOffset :
    singletonShapeRightRepairOffset < singletonShapeTerminalProbeOffset := by
  have hstart :=
    singletonShapeRightRepairDescription_subroutineReady.left.right.left
  simpa [singletonShapeTerminalProbeOffset, singletonShapeRightRepairLimit,
    singletonShapeRightRepairDescription,
    MachineDescription.offsetRetargetDescription] using hstart

theorem singletonShapeRightRepairOffset_le_terminalProbeOffset :
    singletonShapeRightRepairOffset ≤ singletonShapeTerminalProbeOffset :=
  Nat.le_of_lt singletonShapeRightRepairOffset_lt_terminalProbeOffset

theorem singletonShapeLeftRepairLimit_le_terminalProbeOffset :
    singletonShapeLeftRepairLimit ≤ singletonShapeTerminalProbeOffset := by
  simpa [singletonShapeRightRepairOffset] using
    singletonShapeRightRepairOffset_le_terminalProbeOffset

theorem singletonShapeLeftRepairOffset_le_terminalProbeOffset :
    singletonShapeLeftRepairOffset ≤ singletonShapeTerminalProbeOffset :=
  Nat.le_trans singletonShapeLeftRepairOffset_le_rightRepairOffset
    singletonShapeRightRepairOffset_le_terminalProbeOffset

theorem singletonShapeRefreshFinalHalt_lt_stateCount :
    singletonShapeRefreshFinalHalt <
      singletonShapeRefreshDescription.stateCount := by
  have hhalt :=
    singletonShapeTerminalProbeDescription_subroutineReady.left.right.right.left
  simpa [singletonShapeRefreshDescription,
    singletonShapeTerminalProbeDescription,
    singletonShapeTerminalTarget] using hhalt

theorem singletonShapeTerminalProbeOffset_lt_stateCount :
    singletonShapeTerminalProbeOffset <
      singletonShapeRefreshDescription.stateCount := by
  have hpos := singletonShapeTerminalLocalDescription_subroutineReady.left.left
  simpa [singletonShapeRefreshDescription,
    singletonShapeTerminalProbeDescription,
    MachineDescription.offsetReadExitRetargetDescription] using
    Nat.lt_add_of_pos_right (n := singletonShapeTerminalProbeOffset) hpos

theorem singletonShapeLeftRepairLimit_le_stateCount :
    singletonShapeLeftRepairLimit ≤
      singletonShapeRefreshDescription.stateCount :=
  Nat.le_trans singletonShapeLeftRepairLimit_le_terminalProbeOffset
    (Nat.le_of_lt singletonShapeTerminalProbeOffset_lt_stateCount)

theorem singletonShapeRightRepairLimit_le_stateCount :
    singletonShapeRightRepairLimit ≤
      singletonShapeRefreshDescription.stateCount := by
  simpa [singletonShapeTerminalProbeOffset] using
    Nat.le_of_lt singletonShapeTerminalProbeOffset_lt_stateCount

theorem singletonShapeRefreshDescription_transitions_wellFormed :
    forall t : TransitionDescription,
      t ∈ singletonShapeRefreshDescription.transitions ->
        TransitionDescription.WellFormed
          singletonShapeRefreshDescription.stateCount t := by
  intro t ht
  simp [singletonShapeRefreshDescription] at ht
  rcases ht with hopen | hleft | hright | hterminal
  · simp [singletonShapeRefreshOpeningDescription,
      singletonOpeningProbeDescription] at hopen
    rcases hopen with rfl | rfl | rfl
    · constructor
      · exact Nat.lt_trans (by decide)
          singletonShapeRefreshFinalHalt_lt_stateCount
      · exact Nat.lt_trans (by decide)
          singletonShapeRefreshFinalHalt_lt_stateCount
    · constructor
      · exact Nat.lt_trans (by decide)
          singletonShapeRefreshFinalHalt_lt_stateCount
      · exact
          singletonShapeTerminalProbeDescription_subroutineReady.left.right.left
    · constructor
      · exact Nat.lt_trans (by decide)
          singletonShapeRefreshFinalHalt_lt_stateCount
      · exact
          Nat.lt_of_lt_of_le
            singletonShapeLeftRepairDescription_subroutineReady.left.right.left
            singletonShapeLeftRepairLimit_le_stateCount
  · have hformed :=
      singletonShapeLeftRepairDescription_subroutineReady.left.right.right.right.left
        t hleft
    exact ⟨
      Nat.lt_of_lt_of_le hformed.left
        singletonShapeLeftRepairLimit_le_stateCount,
      Nat.lt_of_lt_of_le hformed.right
        singletonShapeLeftRepairLimit_le_stateCount⟩
  · have hformed :=
      singletonShapeRightRepairDescription_subroutineReady.left.right.right.right.left
        t hright
    exact ⟨
      Nat.lt_of_lt_of_le hformed.left
        singletonShapeRightRepairLimit_le_stateCount,
      Nat.lt_of_lt_of_le hformed.right
        singletonShapeRightRepairLimit_le_stateCount⟩
  · exact
      singletonShapeTerminalProbeDescription_subroutineReady.left.right.right.right.left
        t hterminal

theorem singletonShapeRefreshDescription_deterministic :
    singletonShapeRefreshDescription.Deterministic := by
  intro t u ht hu hkey
  simp [singletonShapeRefreshDescription] at ht hu
  rcases ht with hopenT | hleftT | hrightT | hterminalT <;>
    rcases hu with hopenU | hleftU | hrightU | hterminalU
  · exact
      singletonShapeRefreshOpeningDescription_subroutineReady.left.right.right.right.right
        t u hopenT hopenU hkey
  · have htBound :=
      singletonShapeRefreshOpeningDescription_sources_below_leftRepairOffset
        t hopenT
    have huBound :=
      (singletonShapeLeftRepairDescription_sources_in_block u hleftU).left
    exact False.elim (by
      have hs := hkey.left
      lia)
  · have htBound :=
      singletonShapeRefreshOpeningDescription_sources_below_leftRepairOffset
        t hopenT
    have huBound :=
      (singletonShapeRightRepairDescription_sources_in_block u hrightU).left
    have horder := singletonShapeLeftRepairOffset_le_rightRepairOffset
    exact False.elim (by
      have hs := hkey.left
      lia)
  · have htBound :=
      singletonShapeRefreshOpeningDescription_sources_below_leftRepairOffset
        t hopenT
    have huBound :=
      (singletonShapeTerminalProbeDescription_sources_in_block
        u hterminalU).left
    have horder := singletonShapeLeftRepairOffset_le_terminalProbeOffset
    exact False.elim (by
      have hs := hkey.left
      lia)
  · have htBound :=
      singletonShapeRefreshOpeningDescription_sources_below_leftRepairOffset
        u hopenU
    have huBound :=
      (singletonShapeLeftRepairDescription_sources_in_block t hleftT).left
    exact False.elim (by
      have hs := hkey.left
      lia)
  · exact
      singletonShapeLeftRepairDescription_subroutineReady.left.right.right.right.right
        t u hleftT hleftU hkey
  · have htBound :=
      (singletonShapeLeftRepairDescription_sources_in_block t hleftT).right
    have huBound :=
      (singletonShapeRightRepairDescription_sources_in_block u hrightU).left
    exact False.elim (by
      have hs := hkey.left
      simp [singletonShapeRightRepairOffset] at huBound
      lia)
  · have htBound :=
      (singletonShapeLeftRepairDescription_sources_in_block t hleftT).right
    have huBound :=
      (singletonShapeTerminalProbeDescription_sources_in_block
        u hterminalU).left
    have horder := singletonShapeLeftRepairLimit_le_terminalProbeOffset
    exact False.elim (by
      have hs := hkey.left
      lia)
  · have htBound :=
      singletonShapeRefreshOpeningDescription_sources_below_leftRepairOffset
        u hopenU
    have huBound :=
      (singletonShapeRightRepairDescription_sources_in_block t hrightT).left
    have horder := singletonShapeLeftRepairOffset_le_rightRepairOffset
    exact False.elim (by
      have hs := hkey.left
      lia)
  · have htBound :=
      (singletonShapeLeftRepairDescription_sources_in_block u hleftU).right
    have huBound :=
      (singletonShapeRightRepairDescription_sources_in_block t hrightT).left
    exact False.elim (by
      have hs := hkey.left
      simp [singletonShapeRightRepairOffset] at huBound
      lia)
  · exact
      singletonShapeRightRepairDescription_subroutineReady.left.right.right.right.right
        t u hrightT hrightU hkey
  · have htBound :=
      (singletonShapeRightRepairDescription_sources_in_block t hrightT).right
    have huLower :=
      (singletonShapeTerminalProbeDescription_sources_in_block
        u hterminalU).left
    have huBound : singletonShapeRightRepairLimit ≤ u.source := by
      simpa [singletonShapeTerminalProbeOffset] using huLower
    exact False.elim (by
      have hs := hkey.left
      lia)
  · have htBound :=
      singletonShapeRefreshOpeningDescription_sources_below_leftRepairOffset
        u hopenU
    have huBound :=
      (singletonShapeTerminalProbeDescription_sources_in_block
        t hterminalT).left
    have horder := singletonShapeLeftRepairOffset_le_terminalProbeOffset
    exact False.elim (by
      have hs := hkey.left
      lia)
  · have htBound :=
      (singletonShapeLeftRepairDescription_sources_in_block u hleftU).right
    have huBound :=
      (singletonShapeTerminalProbeDescription_sources_in_block
        t hterminalT).left
    have horder := singletonShapeLeftRepairLimit_le_terminalProbeOffset
    exact False.elim (by
      have hs := hkey.left
      lia)
  · have htBound :=
      (singletonShapeRightRepairDescription_sources_in_block u hrightU).right
    have huLower :=
      (singletonShapeTerminalProbeDescription_sources_in_block
        t hterminalT).left
    have huBound : singletonShapeRightRepairLimit ≤ t.source := by
      simpa [singletonShapeTerminalProbeOffset] using huLower
    exact False.elim (by
      have hs := hkey.left
      lia)
  · exact
      singletonShapeTerminalProbeDescription_subroutineReady.left.right.right.right.right
        t u hterminalT hterminalU hkey

theorem singletonShapeRefreshDescription_wellFormed :
    singletonShapeRefreshDescription.WellFormed := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact
      Nat.lt_of_lt_of_le (by decide : 0 < singletonShapeRefreshFinalHalt)
        (Nat.le_of_lt singletonShapeRefreshFinalHalt_lt_stateCount)
  · exact
      Nat.lt_of_lt_of_le (by decide : 0 < singletonShapeRefreshFinalHalt)
        (Nat.le_of_lt singletonShapeRefreshFinalHalt_lt_stateCount)
  · exact singletonShapeRefreshFinalHalt_lt_stateCount
  · exact singletonShapeRefreshDescription_transitions_wellFormed
  · exact singletonShapeRefreshDescription_deterministic

theorem singletonShapeRefreshDescription_haltTransitionFree :
    singletonShapeRefreshDescription.HaltTransitionFree := by
  intro t ht
  simp [singletonShapeRefreshDescription] at ht
  rcases ht with hopening | hleft | hright | hterminal
  · simp [singletonShapeRefreshOpeningDescription,
      singletonOpeningProbeDescription] at hopening
    rcases hopening with rfl | rfl | rfl <;>
      decide
  · exact singletonShapeLeftRepairDescription_subroutineReady.right t hleft
  · exact singletonShapeRightRepairDescription_subroutineReady.right t hright
  · exact singletonShapeTerminalProbeDescription_subroutineReady.right
      t hterminal

theorem singletonShapeRefreshDescription_subroutineReady :
    singletonShapeRefreshDescription.SubroutineReady :=
  ⟨singletonShapeRefreshDescription_wellFormed,
    singletonShapeRefreshDescription_haltTransitionFree⟩

theorem singletonShapeTerminalProbeDescription_reaches_canonical
    (target : Tape Bool) :
    exists steps : Nat,
      singletonShapeTerminalProbeDescription.runConfig steps
        { state := singletonShapeTerminalProbeStart
          tape := encodedGuardedStructuredTapes [target] } =
      { state := singletonShapeRefreshFinalHalt
        tape := encodedGuardedStructuredTapes [target] } := by
  rcases
      singletonTerminalPairProbeDescription_reaches_canonical
        singletonShapeTerminalLocalCanonicalExit
        singletonShapeTerminalLocalRightBoundaryExit
        target with
    ⟨steps, hrun⟩
  refine ⟨steps, ?_⟩
  have hcopy :=
    MachineDescription.offsetReadExitRetargetDescription_runConfig_eq
      (offset := singletonShapeTerminalProbeOffset)
      (localTarget := singletonShapeTerminalLocalTarget)
      (target := singletonShapeTerminalTarget)
      singletonShapeTerminalTarget_lt_probeOffset
      singletonShapeTerminalLocalDescription_transitionFreeAt
      (n := steps)
      hrun
  simpa [singletonShapeTerminalProbeDescription,
    singletonShapeTerminalProbeStart, singletonShapeTerminalLocalDescription,
    singletonShapeTerminalLocalTarget, singletonShapeTerminalTarget,
    MachineDescription.readExitRetargetConfiguration,
    MachineDescription.retargetReadExitState] using hcopy

theorem singletonShapeTerminalProbeDescription_reaches_canonical_cons
    (target : Tape Bool) (rest : List (Tape Bool)) :
    exists steps : Nat,
      singletonShapeTerminalProbeDescription.runConfig steps
        { state := singletonShapeTerminalProbeStart
          tape := encodedStructuredTapes (guardLogicalTape target :: rest) } =
      { state := singletonShapeRefreshFinalHalt
        tape := encodedStructuredTapes (guardLogicalTape target :: rest) } := by
  rcases
      singletonTerminalPairProbeDescription_reaches_canonical_cons
        singletonShapeTerminalLocalCanonicalExit
        singletonShapeTerminalLocalRightBoundaryExit
        target rest with
    ⟨steps, hrun⟩
  refine ⟨steps, ?_⟩
  have hcopy :=
    MachineDescription.offsetReadExitRetargetDescription_runConfig_eq
      (offset := singletonShapeTerminalProbeOffset)
      (localTarget := singletonShapeTerminalLocalTarget)
      (target := singletonShapeTerminalTarget)
      singletonShapeTerminalTarget_lt_probeOffset
      singletonShapeTerminalLocalDescription_transitionFreeAt
      (n := steps)
      hrun
  simpa [singletonShapeTerminalProbeDescription,
    singletonShapeTerminalProbeStart, singletonShapeTerminalLocalDescription,
    singletonShapeTerminalLocalTarget, singletonShapeTerminalTarget,
    MachineDescription.readExitRetargetConfiguration,
    MachineDescription.retargetReadExitState] using hcopy

theorem singletonShapeTerminalProbeDescription_reaches_rightBoundary
    (left : List (Option Bool)) (head : Option Bool) :
    exists steps : Nat,
      singletonShapeTerminalProbeDescription.runConfig steps
        { state := singletonShapeTerminalProbeStart
          tape :=
            encodedStructuredTapes
              [({ left := left ++ [none], head := head, right := [] } :
                Tape Bool)] } =
      { state := singletonShapeRightRepairStart
        tape :=
          encodedStructuredTapes
            [({ left := left ++ [none], head := head, right := [] } :
              Tape Bool)] } := by
  rcases
      singletonTerminalPairProbeDescription_reaches_rightBoundary
        singletonShapeTerminalLocalCanonicalExit
        singletonShapeTerminalLocalRightBoundaryExit
        left head with
    ⟨steps, hrun⟩
  refine ⟨steps, ?_⟩
  have hcopy :=
    MachineDescription.offsetReadExitRetargetDescription_runConfig_eq
      (offset := singletonShapeTerminalProbeOffset)
      (localTarget := singletonShapeTerminalLocalTarget)
      (target := singletonShapeTerminalTarget)
      singletonShapeTerminalTarget_lt_probeOffset
      singletonShapeTerminalLocalDescription_transitionFreeAt
      (n := steps)
      hrun
  simpa [singletonShapeTerminalProbeDescription,
    singletonShapeTerminalProbeStart, singletonShapeTerminalLocalDescription,
    singletonShapeTerminalLocalTarget, singletonShapeTerminalTarget,
    MachineDescription.readExitRetargetConfiguration,
    MachineDescription.retargetReadExitState] using hcopy

theorem singletonShapeTerminalProbeDescription_reaches_rightBoundary_cons
    (left : List (Option Bool)) (head : Option Bool)
    (rest : List (Tape Bool)) :
    exists steps : Nat,
      singletonShapeTerminalProbeDescription.runConfig steps
        { state := singletonShapeTerminalProbeStart
          tape :=
            encodedStructuredTapes
              (({ left := left ++ [none], head := head, right := [] } :
                Tape Bool) :: rest) } =
      { state := singletonShapeRightRepairStart
        tape :=
          encodedStructuredTapes
            (({ left := left ++ [none], head := head, right := [] } :
              Tape Bool) :: rest) } := by
  rcases
      singletonTerminalPairProbeDescription_reaches_rightBoundary_cons
        singletonShapeTerminalLocalCanonicalExit
        singletonShapeTerminalLocalRightBoundaryExit
        left head rest with
    ⟨steps, hrun⟩
  refine ⟨steps, ?_⟩
  have hcopy :=
    MachineDescription.offsetReadExitRetargetDescription_runConfig_eq
      (offset := singletonShapeTerminalProbeOffset)
      (localTarget := singletonShapeTerminalLocalTarget)
      (target := singletonShapeTerminalTarget)
      singletonShapeTerminalTarget_lt_probeOffset
      singletonShapeTerminalLocalDescription_transitionFreeAt
      (n := steps)
      hrun
  simpa [singletonShapeTerminalProbeDescription,
    singletonShapeTerminalProbeStart, singletonShapeTerminalLocalDescription,
    singletonShapeTerminalLocalTarget, singletonShapeTerminalTarget,
    MachineDescription.readExitRetargetConfiguration,
    MachineDescription.retargetReadExitState] using hcopy

theorem singletonShapeLeftRepairDescription_haltsFrom_leftBoundary
    (head : Option Bool) (right : List (Option Bool)) :
    singletonShapeLeftRepairDescription.HaltsFromTapeEquiv
      (encodedStructuredTapes
        [({ left := [], head := head, right := right ++ [none] } :
          Tape Bool)])
      (encodedGuardedStructuredTapes
        [({ left := [], head := head, right := right } : Tape Bool)]) := by
  rcases
      leftBoundaryGuardSlackRefreshDescription_haltsFrom_leftBoundarySlackSingleton
        head (right ++ [none]) with
    ⟨actual, hhalts, hequiv⟩
  refine ⟨actual, ?_, ?_⟩
  · simpa [singletonShapeLeftRepairDescription] using
    MachineDescription.offsetRetargetDescription_haltsFromTape
      singletonShapeRefreshFinalHalt_lt_leftRepairOffset
      leftBoundaryGuardSlackRefreshDescription_subroutineReady.right
      hhalts
  · simpa [encodedGuardedStructuredTapes, guardLogicalTapes,
      guardLogicalTape] using hequiv

theorem singletonShapeRightRepairDescription_haltsFrom_rightBoundary
    (left : List (Option Bool)) (head : Option Bool) :
    singletonShapeRightRepairDescription.HaltsFromTapeEquiv
      (encodedStructuredTapes
        [({ left := left ++ [none], head := head, right := [] } :
          Tape Bool)])
      (encodedGuardedStructuredTapes
        [({ left := left, head := head, right := [] } : Tape Bool)]) := by
  refine
    ⟨encodedStructuredTapes
        [({ left := left ++ [none], head := head, right := [none] } :
          Tape Bool)],
      ?_, ?_⟩
  · simpa [singletonShapeRightRepairDescription] using
      MachineDescription.offsetRetargetDescription_haltsFromTape
        singletonShapeRefreshFinalHalt_lt_rightRepairOffset
        rightBoundaryGuardSlackRefreshDescription_subroutineReady.right
        (rightBoundaryGuardSlackRefreshDescription_haltsFrom_rightBoundarySlackSingleton
          (left ++ [none]) head)
  · exact Tape.Equiv.refl _

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
