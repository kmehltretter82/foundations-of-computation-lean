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
