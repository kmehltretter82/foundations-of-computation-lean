import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.Program
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Basic
import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.StageSearchController.GenCall.Code

set_option doc.verso true

/-!
# Generated exact-fuel calls

Exact-fuel generated-call runner definitions and semantic adapters.  The
concrete finite-state leaf remains here so later work can focus on the exact
simulator without the pair/product search algebra in scope.
-/

namespace FoC
namespace Computability

open Languages

universe uStage uDescription uSimulator

/--
Exact-fuel generated-call runner.  The concrete machine parses a generated
stage code, treats the parsed natural as the exact simulation fuel, rebuilds
the payload as the wrapped machine's input, and halts precisely when the
wrapped machine halts in that exact number of steps.
-/
def CodePrefixExactFuelRunnerConstruction
    {machineState : Type u}
    (M : TuringMachine MachineCodeSymbol machineState) : Prop :=
  exists runnerState : Type,
  exists runner : TuringMachine MachineCodeSymbol runnerState,
    forall input : Word MachineCodeSymbol,
    forall fuel : Nat,
      TuringMachine.HaltsOnInput runner
          (CodePrefixRecognizerStageCode input fuel) <->
        TuringMachine.HaltsOnInputIn M fuel input

/--
The public generated-call exact-fuel construction is the code-prefix
specialization of the generic finite-recognizer exact-fuel runner contract.
-/
theorem codePrefixExactFuelRunnerConstruction_iff_runnerConstruction
    {machineState : Type u}
    (M : TuringMachine MachineCodeSymbol machineState) :
    CodePrefixExactFuelRunnerConstruction M <->
      FiniteRecognizer.ExactFuel.RunnerConstruction M
        FiniteRecognizer.GeneratedCode.stageCode := by
  constructor
  · intro h
    rcases h with ⟨runnerState, runner, hrunner⟩
    exact ⟨runnerState, runner, by
      intro input fuel
      simpa [FiniteRecognizer.GeneratedCode.stageCode] using!
        hrunner input fuel⟩
  · intro h
    rcases h with ⟨runnerState, runner, hrunner⟩
    exact ⟨runnerState, runner, by
      intro input fuel
      simpa [FiniteRecognizer.GeneratedCode.stageCode] using!
        hrunner input fuel⟩

theorem codePrefixExactFuelRunnerConstruction_of_runnerConstruction
    {machineState : Type u}
    {M : TuringMachine MachineCodeSymbol machineState}
    (h :
      FiniteRecognizer.ExactFuel.RunnerConstruction M
        FiniteRecognizer.GeneratedCode.stageCode) :
    CodePrefixExactFuelRunnerConstruction M :=
  (codePrefixExactFuelRunnerConstruction_iff_runnerConstruction M).mpr h

/--
Concrete-state version of the exact-fuel runner leaf.  This is the remaining
finite-table target after reindexing arbitrary finite machines to {lit}`Fin n`
state spaces.
-/
def CodePrefixExactFuelRunnerFinStateConstruction : Prop :=
  forall n : Nat,
    forall M : TuringMachine MachineCodeSymbol (Fin n),
      CodePrefixExactFuelRunnerConstruction M

/--
It is enough to build the exact-fuel runner for the indexed copy of a fixed
finite-state machine.
-/
theorem codePrefixExactFuelRunnerConstruction_of_indexed
    {machineState : Type u}
    (M : TuringMachine MachineCodeSymbol machineState)
    (hindexed :
      CodePrefixExactFuelRunnerConstruction (TuringMachine.indexed M)) :
    CodePrefixExactFuelRunnerConstruction M := by
  rcases hindexed with ⟨runnerState, runner, hrunner⟩
  refine ⟨runnerState, runner, ?_⟩
  intro input fuel
  exact Iff.trans (hrunner input fuel)
    (TuringMachine.indexed_haltsOnInputIn_iff M fuel input)

/--
Consequently, a construction for all concrete {lit}`Fin n` state spaces
suffices for the general exact-fuel runner leaf.
-/
theorem codePrefixExactFuelRunnerConstruction_of_finStateConstruction
    {machineState : Type u}
    (M : TuringMachine MachineCodeSymbol machineState)
    (hFin : CodePrefixExactFuelRunnerFinStateConstruction) :
    CodePrefixExactFuelRunnerConstruction M := by
  exact
    codePrefixExactFuelRunnerConstruction_of_indexed M
      (hFin M.statesFinite.elems.length (TuringMachine.indexed M))

/--
Remaining concrete finite-table leaf for exact-fuel simulation over concrete
indexed state spaces.
-/
theorem codePrefixExactFuelRunnerFinStateFiniteLeaf :
    CodePrefixExactFuelRunnerFinStateConstruction := by
  intro n M
  have hcore :
      FiniteRecognizer.ExactFuel.RunnerConstruction M
        FiniteRecognizer.ExactFuel.StageProgram.stageCode :=
    FiniteRecognizer.ExactFuel.StageProgram.finStateRunnerConstructionFiniteLeaf
      n M
  apply codePrefixExactFuelRunnerConstruction_of_runnerConstruction
  rcases hcore with ⟨runnerState, runner, hrunner⟩
  refine ⟨runnerState, runner, ?_⟩
  exact
    FiniteRecognizer.ExactFuel.exactFuelRunnerSpec_ext
      (M := M) (runner := runner)
      (leftBuild := FiniteRecognizer.ExactFuel.StageProgram.stageCode)
      (rightBuild := FiniteRecognizer.GeneratedCode.stageCode)
      (by
        intro input fuel
        rfl)
      hrunner

/--
Finite-machine leaf for {name}`CodePrefixExactFuelRunnerConstruction`.
This is the shared exact-fuel runner promised by the generated-call helper
plan.
-/
theorem codePrefixExactFuelRunnerFiniteLeaf
    {machineState : Type u}
    (M : TuringMachine MachineCodeSymbol machineState) :
    CodePrefixExactFuelRunnerConstruction M := by
  exact
    codePrefixExactFuelRunnerConstruction_of_finStateConstruction
      M codePrefixExactFuelRunnerFinStateFiniteLeaf

theorem codePrefixExactFuelRunnerFiniteLeafDecidable
    {machineState : Type u} [DecidableEq machineState]
    (M : TuringMachine MachineCodeSymbol machineState) :
    CodePrefixExactFuelRunnerConstruction M := by
  exact codePrefixExactFuelRunnerFiniteLeaf M

/--
Specialization of an exact-fuel runner to a nested generated call.  The outer
bound is the exact fuel for the wrapped machine, and the inner generated call
is preserved as the wrapped input.
-/
theorem codePrefixExactFuelRunner_haltsOnNested_iff
    {machineState : Type u} {runnerState : Type v}
    {M : TuringMachine MachineCodeSymbol machineState}
    {runner : TuringMachine MachineCodeSymbol runnerState}
    (hrunner :
      forall input : Word MachineCodeSymbol,
      forall fuel : Nat,
        TuringMachine.HaltsOnInput runner
            (CodePrefixRecognizerStageCode input fuel) <->
          TuringMachine.HaltsOnInputIn M fuel input)
    (input : Word MachineCodeSymbol) (inner outer : Nat) :
    TuringMachine.HaltsOnInput runner
        (NestedCodePrefixRecognizerStageCode input inner outer) <->
      TuringMachine.HaltsOnInputIn M outer
        (CodePrefixRecognizerStageCode input inner) := by
  simpa [NestedCodePrefixRecognizerStageCode] using
    hrunner (CodePrefixRecognizerStageCode input inner) outer

/--
Unbounded search over generated inner inputs and exact outer fuels for a
wrapped machine.
-/
def CodePrefixNestedExactFuelSearchConstruction
    {machineState : Type u}
    (M : TuringMachine MachineCodeSymbol machineState) : Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    FiniteRecognizer.TupleSearch.UnboundedNestedExactFuelSearchSpec
      searcher M CodePrefixRecognizerStageCode

end Computability
end FoC
