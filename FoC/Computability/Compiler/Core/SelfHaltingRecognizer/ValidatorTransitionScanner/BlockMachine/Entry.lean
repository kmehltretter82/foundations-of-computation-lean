import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.BlockMachine.Compiler

set_option doc.verso true

/-!
# Shared four-cell left-entry wrapper

Several validator phases begin at the first physical bit after an encoded
prefix, while their aligned block core begins at the first bit of the preceding
four-bit token.  This module adds the same four identity-write left moves to
any physical core description and proves the exact entry run once.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer

open MachineDescription

/-- One of the four fresh states preceding an aligned block core. -/
def validatorFourLeftEntryState
    (core : MachineDescription) (phase : Nat) : Nat :=
  core.stateCount + phase

/-- One identity-write row of the four-cell left entry wrapper. -/
def validatorFourLeftEntryRow
    (core : MachineDescription) (phase : Nat)
    (read : Option Bool) (target : Nat) : TransitionDescription where
  source := validatorFourLeftEntryState core phase
  read := read
  write := read
  move := Direction.left
  target := target

/-- Complete read cases for one entry state. -/
def validatorFourLeftEntryRowsAt
    (core : MachineDescription) (phase target : Nat) :
    List TransitionDescription :=
  [validatorFourLeftEntryRow core phase none target,
    validatorFourLeftEntryRow core phase (some false) target,
    validatorFourLeftEntryRow core phase (some true) target]

/-- The twelve rows implementing four unconditional left moves. -/
def validatorFourLeftEntryRows
    (core : MachineDescription) : List TransitionDescription :=
  validatorFourLeftEntryRowsAt core 0
      (validatorFourLeftEntryState core 1) ++
    validatorFourLeftEntryRowsAt core 1
      (validatorFourLeftEntryState core 2) ++
    validatorFourLeftEntryRowsAt core 2
      (validatorFourLeftEntryState core 3) ++
    validatorFourLeftEntryRowsAt core 3 core.start

/-- Add four raw left-entry states to a physical aligned-block core. -/
def withValidatorFourLeftEntry
    (core : MachineDescription) : MachineDescription where
  stateCount := core.stateCount + 4
  start := validatorFourLeftEntryState core 0
  halt := core.halt
  transitions := core.transitions ++ validatorFourLeftEntryRows core

private theorem runConfig_one_validatorFourLeftEntryRow
    (core : MachineDescription)
    (hdet : (withValidatorFourLeftEntry core).Deterministic)
    {phase target : Nat} (tape : Tape Bool)
    (hrow : forall read : Option Bool,
      validatorFourLeftEntryRow core phase read target ∈
        validatorFourLeftEntryRows core) :
    (withValidatorFourLeftEntry core).runConfig 1
        { state := validatorFourLeftEntryState core phase, tape := tape } =
      { state := target, tape := Tape.move Direction.left tape } := by
  let read := Tape.read tape
  have hrowDescription :
      validatorFourLeftEntryRow core phase read target ∈
        (withValidatorFourLeftEntry core).transitions :=
    List.mem_append_right core.transitions (hrow read)
  have hlookup :=
    lookupTransition_eq_some_of_mem_deterministic hdet hrowDescription
  change (withValidatorFourLeftEntry core).lookupTransition
      (validatorFourLeftEntryState core phase) read =
    some (validatorFourLeftEntryRow core phase read target) at hlookup
  have hread : Tape.read tape = read := rfl
  have hwrite : Tape.write read tape = tape := by
    dsimp [read]
    exact Tape.write_read_eq_self tape
  simp [MachineDescription.runConfig, MachineDescription.stepConfig,
    hread, hlookup, hwrite, validatorFourLeftEntryRow]

/-- The shared entry wrapper reaches the physical core after four left moves. -/
theorem runConfig_withValidatorFourLeftEntry
    (core : MachineDescription)
    (hdet : (withValidatorFourLeftEntry core).Deterministic)
    (tape : Tape Bool) :
    (withValidatorFourLeftEntry core).runConfig 4
        { state := (withValidatorFourLeftEntry core).start, tape := tape } =
      { state := core.start
        tape := Tape.move Direction.left
          (Tape.move Direction.left
            (Tape.move Direction.left
              (Tape.move Direction.left tape))) } := by
  let tape1 := Tape.move Direction.left tape
  let tape2 := Tape.move Direction.left tape1
  let tape3 := Tape.move Direction.left tape2
  let tape4 := Tape.move Direction.left tape3
  have hrow0 : forall read : Option Bool,
      validatorFourLeftEntryRow core 0 read
          (validatorFourLeftEntryState core 1) ∈
        validatorFourLeftEntryRows core := by
    intro read
    cases read with
    | none => simp [validatorFourLeftEntryRows,
        validatorFourLeftEntryRowsAt]
    | some bit =>
        cases bit <;> simp [validatorFourLeftEntryRows,
          validatorFourLeftEntryRowsAt]
  have hrow1 : forall read : Option Bool,
      validatorFourLeftEntryRow core 1 read
          (validatorFourLeftEntryState core 2) ∈
        validatorFourLeftEntryRows core := by
    intro read
    cases read with
    | none => simp [validatorFourLeftEntryRows,
        validatorFourLeftEntryRowsAt]
    | some bit =>
        cases bit <;> simp [validatorFourLeftEntryRows,
          validatorFourLeftEntryRowsAt]
  have hrow2 : forall read : Option Bool,
      validatorFourLeftEntryRow core 2 read
          (validatorFourLeftEntryState core 3) ∈
        validatorFourLeftEntryRows core := by
    intro read
    cases read with
    | none => simp [validatorFourLeftEntryRows,
        validatorFourLeftEntryRowsAt]
    | some bit =>
        cases bit <;> simp [validatorFourLeftEntryRows,
          validatorFourLeftEntryRowsAt]
  have hrow3 : forall read : Option Bool,
      validatorFourLeftEntryRow core 3 read core.start ∈
        validatorFourLeftEntryRows core := by
    intro read
    cases read with
    | none => simp [validatorFourLeftEntryRows,
        validatorFourLeftEntryRowsAt]
    | some bit =>
        cases bit <;> simp [validatorFourLeftEntryRows,
          validatorFourLeftEntryRowsAt]
  have hstep0 := runConfig_one_validatorFourLeftEntryRow
    core hdet tape hrow0
  have hstep1 := runConfig_one_validatorFourLeftEntryRow
    core hdet tape1 hrow1
  have hstep2 := runConfig_one_validatorFourLeftEntryRow
    core hdet tape2 hrow2
  have hstep3 := runConfig_one_validatorFourLeftEntryRow
    core hdet tape3 hrow3
  change (withValidatorFourLeftEntry core).runConfig 4
      { state := validatorFourLeftEntryState core 0, tape := tape } =
    { state := core.start, tape := tape4 }
  rw [show 4 = 1 + 3 by decide,
    MachineDescription.runConfig_add, hstep0]
  rw [show 3 = 1 + 2 by decide,
    MachineDescription.runConfig_add, hstep1]
  rw [show 2 = 1 + 1 by decide,
    MachineDescription.runConfig_add, hstep2, hstep3]

end SelfHaltingRecognizer
end Computability
end FoC
