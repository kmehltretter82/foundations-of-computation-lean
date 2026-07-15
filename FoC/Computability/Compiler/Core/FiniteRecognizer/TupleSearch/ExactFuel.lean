import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.Program
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Program

set_option doc.verso true

/-!
# Generated tuple exact-fuel search

Core composition layer that connects the exact-fuel generated runner to the
generated tuple-search enumerators.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace TupleSearch

universe uMachine

/--
Unbounded search over generated inner inputs and exact outer fuels for a
wrapped machine, using the core generated-code convention.
-/
def GeneratedNestedExactFuelSearchConstruction
    {machineState : Type uMachine}
    (M : TuringMachine MachineCodeSymbol machineState) : Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    GeneratedUnboundedNestedExactFuelSearchSpec searcher M

/--
Bounded search over generated inner inputs and exact outer fuels for a wrapped
machine, using the core generated-code convention.
-/
def GeneratedBoundedNestedExactFuelSearchConstruction
    {machineState : Type uMachine}
    (M : TuringMachine MachineCodeSymbol machineState) : Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    GeneratedBoundedNestedExactFuelSearchSpec searcher M

/--
Unbounded search over generated inner inputs for a wrapped machine, hiding the
exact outer fuel behind ordinary halting.
-/
def GeneratedNestedHaltingSearchConstruction
    {machineState : Type uMachine}
    (M : TuringMachine MachineCodeSymbol machineState) : Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    forall input : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput searcher input <->
        exists inner : Nat,
          TuringMachine.HaltsOnInput M
            (GeneratedCode.stageCode input inner)

theorem generatedStageProgramRunnerConstructionFiniteLeaf
    {machineState : Type uMachine}
    (M : TuringMachine MachineCodeSymbol machineState) :
    ExactFuel.RunnerConstruction M GeneratedCode.stageCode := by
  exact
    FoC.Computability.FiniteRecognizer.ExactFuel.runnerConstruction_of_finStateConstruction
      M
      FoC.Computability.FiniteRecognizer.ExactFuel.StageProgram.finStateRunnerConstructionFiniteLeaf

theorem generatedStageProgramRunnerConstructionFiniteLeafDecidable
    {machineState : Type uMachine} [DecidableEq machineState]
    (M : TuringMachine MachineCodeSymbol machineState) :
    ExactFuel.RunnerConstruction M GeneratedCode.stageCode := by
  exact generatedStageProgramRunnerConstructionFiniteLeaf M

theorem generatedNestedExactFuelSearchFiniteLeaf
    {machineState : Type uMachine}
    (M : TuringMachine MachineCodeSymbol machineState) :
    GeneratedNestedExactFuelSearchConstruction M := by
  rcases generatedStageProgramRunnerConstructionFiniteLeaf M with
    ⟨selectedState, selected, hselected⟩
  rcases generatedNestedPairEnumeratorFiniteLeaf selected with
    ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro input
  constructor
  · intro hhalt
    rcases (hsearcher input).mp hhalt with
      ⟨inner, outer, hselectedHalt⟩
    exact
      ⟨inner, outer,
        (hselected (GeneratedCode.stageCode input inner) outer).mp
          (by
            simpa [GeneratedCode.nestedStageCode] using
              hselectedHalt)⟩
  · intro htarget
    rcases htarget with ⟨inner, outer, hM⟩
    exact (hsearcher input).mpr
      ⟨inner, outer,
        by
          simpa [GeneratedCode.nestedStageCode] using
            (hselected (GeneratedCode.stageCode input inner) outer).mpr
              hM⟩

theorem generatedNestedExactFuelSearchFiniteLeafDecidable
    {machineState : Type uMachine} [DecidableEq machineState]
    (M : TuringMachine MachineCodeSymbol machineState) :
    GeneratedNestedExactFuelSearchConstruction M := by
  exact generatedNestedExactFuelSearchFiniteLeaf M

theorem generatedBoundedNestedExactFuelSearchFiniteLeaf
    {machineState : Type uMachine}
    (M : TuringMachine MachineCodeSymbol machineState) :
    GeneratedBoundedNestedExactFuelSearchConstruction M := by
  rcases generatedStageProgramRunnerConstructionFiniteLeaf M with
    ⟨selectedState, selected, hselected⟩
  rcases generatedBoundedNestedPairEnumeratorFiniteLeaf selected with
    ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro input budget
  constructor
  · intro hhalt
    rcases (hsearcher input budget).mp hhalt with
      ⟨inner, outer, hinner, houter, hselectedHalt⟩
    exact
      ⟨inner, outer, hinner, houter,
        (hselected (GeneratedCode.stageCode input inner) outer).mp
          (by
            simpa [GeneratedCode.nestedStageCode] using
              hselectedHalt)⟩
  · intro htarget
    rcases htarget with ⟨inner, outer, hinner, houter, hM⟩
    exact (hsearcher input budget).mpr
      ⟨inner, outer, hinner, houter,
        by
          simpa [GeneratedCode.nestedStageCode] using
            (hselected (GeneratedCode.stageCode input inner) outer).mpr
              hM⟩

theorem generatedBoundedNestedExactFuelSearchFiniteLeafDecidable
    {machineState : Type uMachine} [DecidableEq machineState]
    (M : TuringMachine MachineCodeSymbol machineState) :
    GeneratedBoundedNestedExactFuelSearchConstruction M := by
  exact generatedBoundedNestedExactFuelSearchFiniteLeaf M

theorem generatedNestedHaltingSearchFiniteLeaf
    {machineState : Type uMachine}
    (M : TuringMachine MachineCodeSymbol machineState) :
    GeneratedNestedHaltingSearchConstruction M := by
  rcases generatedNestedExactFuelSearchFiniteLeaf M with
    ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro input
  exact Iff.trans (hsearcher input)
    (exists_pair_haltsOnInputIn_iff_exists_haltsOnInput
      M (fun inner => GeneratedCode.stageCode input inner))

theorem generatedNestedHaltingSearchFiniteLeafDecidable
    {machineState : Type uMachine} [DecidableEq machineState]
    (M : TuringMachine MachineCodeSymbol machineState) :
    GeneratedNestedHaltingSearchConstruction M := by
  exact generatedNestedHaltingSearchFiniteLeaf M

end TupleSearch
end FiniteRecognizer

end Computability
end FoC
