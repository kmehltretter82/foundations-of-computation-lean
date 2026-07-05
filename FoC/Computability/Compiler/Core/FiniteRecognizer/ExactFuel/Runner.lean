import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.Layout

set_option doc.verso true

/-!
# Exact-fuel runner contracts

Semantic adapter layer between protected exact-fuel layouts and recognizer
construction statements.  Concrete finite tables should prove these contracts
after implementing the parser-to-layout and step-loop phases.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel

universe uState uRunner

def RunnerConstruction
    {state : Type uState}
    (M : TuringMachine MachineCodeSymbol state)
    (build :
      Word MachineCodeSymbol -> Nat -> Word MachineCodeSymbol) : Prop :=
  exists runnerState : Type,
  exists runner : TuringMachine MachineCodeSymbol runnerState,
    ExactFuelRunnerSpec runner M build

def FinStateRunnerConstruction
    (build :
      Word MachineCodeSymbol -> Nat -> Word MachineCodeSymbol) : Prop :=
  forall stateCount : Nat,
  forall M : TuringMachine MachineCodeSymbol (Fin stateCount),
    RunnerConstruction M build

def LayoutRunnerSpec {stateCount : Nat} {runnerState : Type uRunner}
    (runner : TuringMachine MachineCodeSymbol runnerState)
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (buildLayout : Layout stateCount -> Word MachineCodeSymbol) :
    Prop :=
  forall L : Layout stateCount,
    TuringMachine.HaltsOnInput runner (buildLayout L) <->
      Layout.accepts M L

def StageParserSpec {stateCount : Nat} {parserState : Type uRunner}
    (parser : TuringMachine MachineCodeSymbol parserState)
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (buildStage :
      Word MachineCodeSymbol -> Nat -> Word MachineCodeSymbol)
    (buildLayout : Layout stateCount -> Word MachineCodeSymbol) :
    Prop :=
  forall input : Word MachineCodeSymbol,
  forall fuel : Nat,
    TuringMachine.HaltsOnInput parser (buildStage input fuel) <->
      TuringMachine.HaltsOnInput parser
        (buildLayout (Layout.initial M input fuel))

theorem runnerSpec_of_layoutRunner
    {stateCount : Nat} {runnerState : Type uRunner}
    {runner : TuringMachine MachineCodeSymbol runnerState}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {buildStage :
      Word MachineCodeSymbol -> Nat -> Word MachineCodeSymbol}
    {buildLayout : Layout stateCount -> Word MachineCodeSymbol}
    (hparser :
      forall input : Word MachineCodeSymbol,
      forall fuel : Nat,
        buildStage input fuel =
          buildLayout (Layout.initial M input fuel))
    (hrunner : LayoutRunnerSpec runner M buildLayout) :
    ExactFuelRunnerSpec runner M buildStage := by
  intro input fuel
  rw [hparser input fuel]
  exact Iff.trans (hrunner (Layout.initial M input fuel))
    (Layout.accepts_initial_iff_haltsOnInputIn M input fuel)

theorem runnerConstruction_of_layoutRunner
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {buildStage :
      Word MachineCodeSymbol -> Nat -> Word MachineCodeSymbol}
    {buildLayout : Layout stateCount -> Word MachineCodeSymbol}
    (hparser :
      forall input : Word MachineCodeSymbol,
      forall fuel : Nat,
        buildStage input fuel =
          buildLayout (Layout.initial M input fuel))
    (runnerState : Type)
    (runner : TuringMachine MachineCodeSymbol runnerState)
    (hrunner : LayoutRunnerSpec runner M buildLayout) :
    RunnerConstruction M buildStage :=
  ⟨runnerState, runner,
    runnerSpec_of_layoutRunner hparser hrunner⟩

theorem runnerConstruction_of_indexed
    {state : Type uState}
    {M : TuringMachine MachineCodeSymbol state}
    {build :
      Word MachineCodeSymbol -> Nat -> Word MachineCodeSymbol}
    (hindexed :
      RunnerConstruction (TuringMachine.indexed M) build) :
    RunnerConstruction M build := by
  rcases hindexed with ⟨runnerState, runner, hrunner⟩
  refine ⟨runnerState, runner, ?_⟩
  intro input fuel
  exact Iff.trans (hrunner input fuel)
    (TuringMachine.indexed_haltsOnInputIn_iff M fuel input)

theorem runnerConstruction_of_indexedDecidable
    {state : Type uState} [DecidableEq state]
    {M : TuringMachine MachineCodeSymbol state}
    {build :
      Word MachineCodeSymbol -> Nat -> Word MachineCodeSymbol}
    (hindexed :
      RunnerConstruction (TuringMachine.indexedDecidable M) build) :
    RunnerConstruction M build := by
  rcases hindexed with ⟨runnerState, runner, hrunner⟩
  refine ⟨runnerState, runner, ?_⟩
  intro input fuel
  exact Iff.trans (hrunner input fuel)
    (TuringMachine.indexedDecidable_haltsOnInputIn_iff
      M fuel input)

theorem runnerConstruction_indexed_of
    {state : Type uState}
    (M : TuringMachine MachineCodeSymbol state)
    {build :
      Word MachineCodeSymbol -> Nat -> Word MachineCodeSymbol}
    (h :
      RunnerConstruction M build) :
    RunnerConstruction (TuringMachine.indexed M) build := by
  rcases h with ⟨runnerState, runner, hrunner⟩
  refine ⟨runnerState, runner, ?_⟩
  intro input fuel
  exact Iff.trans (hrunner input fuel)
    (Iff.symm
      (TuringMachine.indexed_haltsOnInputIn_iff
        M fuel input))

theorem runnerConstruction_indexedDecidable_of
    {state : Type uState} [DecidableEq state]
    (M : TuringMachine MachineCodeSymbol state)
    {build :
      Word MachineCodeSymbol -> Nat -> Word MachineCodeSymbol}
    (h :
      RunnerConstruction M build) :
    RunnerConstruction (TuringMachine.indexedDecidable M) build := by
  rcases h with ⟨runnerState, runner, hrunner⟩
  refine ⟨runnerState, runner, ?_⟩
  intro input fuel
  exact Iff.trans (hrunner input fuel)
    (Iff.symm
      (TuringMachine.indexedDecidable_haltsOnInputIn_iff
        M fuel input))

theorem runnerConstruction_of_finStateConstruction
    {state : Type uState}
    (M : TuringMachine MachineCodeSymbol state)
    {build :
      Word MachineCodeSymbol -> Nat -> Word MachineCodeSymbol}
    (hFin : FinStateRunnerConstruction build) :
    RunnerConstruction M build := by
  exact
    runnerConstruction_of_indexed
      (M := M)
      (hFin M.statesFinite.elems.length
        (TuringMachine.indexed M))

theorem runnerConstruction_of_finStateConstructionDecidable
    {state : Type uState} [DecidableEq state]
    (M : TuringMachine MachineCodeSymbol state)
    {build :
      Word MachineCodeSymbol -> Nat -> Word MachineCodeSymbol}
    (hFin : FinStateRunnerConstruction build) :
    RunnerConstruction M build := by
  exact
    runnerConstruction_of_indexedDecidable
      (M := M)
      (hFin M.statesFinite.elems.length
        (TuringMachine.indexedDecidable M))

theorem exactFuelRunnerSpec_ext
    {state : Type uState} {runnerState : Type uRunner}
    {runner : TuringMachine MachineCodeSymbol runnerState}
    {M : TuringMachine MachineCodeSymbol state}
    {leftBuild rightBuild :
      Word MachineCodeSymbol -> Nat -> Word MachineCodeSymbol}
    (hbuild :
      forall input : Word MachineCodeSymbol,
      forall fuel : Nat,
        leftBuild input fuel = rightBuild input fuel)
    (hspec : ExactFuelRunnerSpec runner M leftBuild) :
    ExactFuelRunnerSpec runner M rightBuild := by
  intro input fuel
  rw [← hbuild input fuel]
  exact hspec input fuel

end ExactFuel
end FiniteRecognizer

end Computability
end FoC
