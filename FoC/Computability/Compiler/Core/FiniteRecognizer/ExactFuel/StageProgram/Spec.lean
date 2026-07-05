import FoC.Computability.Compiler.Core.FiniteRecognizer.GeneratedCode
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.Runner

set_option doc.verso true

/-!
# Exact-fuel staged program specification

Semantic API for the normalized exact-fuel staged program.  This module keeps
the decoded unary-fuel predicate and code-machine contracts independent of
the concrete finite-table construction.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StageProgram

/-- Canonical unary-fuel stage code, independent of the Universal/Ranges API. -/
def stageCode
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    Word MachineCodeSymbol :=
  GeneratedCode.stageCode input fuel

theorem stageCode_decodeNat
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    MachineDescription.decodeNat (stageCode input fuel) =
      some (fuel, input) :=
  GeneratedCode.stageCode_decodeNat input fuel

theorem stageCode_eq_of_decodeNat
    {tokens input : Word MachineCodeSymbol} {fuel : Nat}
    (h : MachineDescription.decodeNat tokens = some (fuel, input)) :
    tokens = stageCode input fuel :=
  GeneratedCode.stageCode_eq_of_decodeNat h

/--
Parsed payload for the normalized exact-fuel staged program.
-/
structure Parsed where
  fuel : Nat
  input : Word MachineCodeSymbol

namespace Parsed

def accepts {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (p : Parsed) : Prop :=
  TuringMachine.HaltsOnInputIn M p.fuel p.input

end Parsed

/--
Executable exact-fuel recognizer predicate for a fixed finite-state machine.
It returns the conventional empty output exactly when the parsed fuel/input
pair makes the selected machine halt in exactly that many steps.
-/
def run {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match MachineDescription.decodeNat tokens with
  | none => none
  | some (fuel, input) =>
      if TuringMachine.HaltsOnInputIn M fuel input then
        some ([] : Word MachineCodeSymbol)
      else
        none

theorem run_eq_some_iff_decodeNat {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tokens : Word MachineCodeSymbol) :
    run M tokens = some ([] : Word MachineCodeSymbol) <->
      exists fuel : Nat,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens = some (fuel, input) /\
          TuringMachine.HaltsOnInputIn M fuel input := by
  constructor
  · intro hrun
    unfold run at hrun
    cases hdecode : MachineDescription.decodeNat tokens with
    | none =>
        rw [hdecode] at hrun
        cases hrun
    | some decoded =>
        rcases decoded with ⟨fuel, input⟩
        rw [hdecode] at hrun
        by_cases hhalt : TuringMachine.HaltsOnInputIn M fuel input
        · exact ⟨fuel, input, rfl, hhalt⟩
        · simp [hhalt] at hrun
  · intro h
    rcases h with ⟨fuel, input, hdecode, hhalt⟩
    simp [run, hdecode, hhalt]
    rfl

theorem run_stageCode_eq_some_iff {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    run M (stageCode input fuel) = some ([] : Word MachineCodeSymbol) <->
      TuringMachine.HaltsOnInputIn M fuel input := by
  constructor
  · intro hrun
    rcases
        (run_eq_some_iff_decodeNat M (stageCode input fuel)).mp hrun with
      ⟨fuel', input', hdecode, hhalt⟩
    rw [stageCode_decodeNat input fuel] at hdecode
    cases hdecode
    exact hhalt
  · intro hhalt
    exact
      (run_eq_some_iff_decodeNat M (stageCode input fuel)).mpr
        ⟨fuel, input, stageCode_decodeNat input fuel, hhalt⟩

def CodeMachineSpec {stateCount : Nat} {runnerState : Type}
    (runner : TuringMachine MachineCodeSymbol runnerState)
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    Prop :=
  forall tokens : Word MachineCodeSymbol,
    TuringMachine.HaltsOnInput runner tokens <->
      run M tokens = some ([] : Word MachineCodeSymbol)

def CodeMachineConstruction {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    Prop :=
  exists runnerState : Type,
  exists runner : TuringMachine MachineCodeSymbol runnerState,
    CodeMachineSpec runner M

def FinStateCodeMachineConstruction : Prop :=
  forall stateCount : Nat,
  forall M : TuringMachine MachineCodeSymbol (Fin stateCount),
    CodeMachineConstruction M

theorem runnerConstruction_of_codeMachine {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (hcode : CodeMachineConstruction M) :
    RunnerConstruction M stageCode := by
  rcases hcode with ⟨runnerState, runner, hrunner⟩
  refine ⟨runnerState, runner, ?_⟩
  intro input fuel
  exact Iff.trans (hrunner (stageCode input fuel))
    (run_stageCode_eq_some_iff M input fuel)

theorem finStateRunnerConstruction_of_codeMachine
    (hcode : FinStateCodeMachineConstruction) :
    FinStateRunnerConstruction stageCode := by
  intro stateCount M
  exact runnerConstruction_of_codeMachine (hcode stateCount M)

end StageProgram
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
