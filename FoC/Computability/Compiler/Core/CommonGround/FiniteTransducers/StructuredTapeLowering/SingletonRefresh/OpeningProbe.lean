import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.CursorBasic

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


end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
