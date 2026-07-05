import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.Runner

set_option doc.verso true

/-!
# Exact-fuel staged program boundary

This module isolates the normalized code-machine boundary for exact-fuel
generated calls.  The public generated-code runner can be obtained from any
finite machine that realizes this staged predicate; the remaining concrete
transition-table work is therefore focused on one exact parser/run program.
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
  MachineDescription.encodeNatAppend fuel input

theorem stageCode_decodeNat
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    MachineDescription.decodeNat (stageCode input fuel) =
      some (fuel, input) :=
  MachineDescription.decodeNat_encodeNatAppend fuel input

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

theorem run_stageCode_eq_some_iff {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    run M (stageCode input fuel) = some ([] : Word MachineCodeSymbol) <->
      TuringMachine.HaltsOnInputIn M fuel input := by
  constructor
  · intro hrun
    by_cases hhalt : TuringMachine.HaltsOnInputIn M fuel input
    · exact hhalt
    · simp [run, stageCode, MachineDescription.decodeNat_encodeNatAppend,
        hhalt] at hrun
  · intro hhalt
    simp [run, stageCode, MachineDescription.decodeNat_encodeNatAppend,
      hhalt]
    rfl

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

/--
Remaining concrete transition-table leaf for the normalized exact-fuel staged
program.  It must parse the unary fuel prefix, protect the payload as an
encoded work layout, run the fixed selected transition table for exactly that
fuel, and halt exactly when the final selected state is the selected halt
state.
-/
theorem codeMachineFinStateFiniteLeaf :
    FinStateCodeMachineConstruction := by
  intro stateCount M
  cases stateCount with
  | zero =>
      exact False.elim (Fin.elim0 M.start)
  | succ _ =>
      sorry

theorem finStateRunnerConstructionFiniteLeaf :
    FinStateRunnerConstruction stageCode :=
  finStateRunnerConstruction_of_codeMachine codeMachineFinStateFiniteLeaf

end StageProgram
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
