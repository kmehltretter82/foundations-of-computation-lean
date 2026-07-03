import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.StageSearchController.GeneratedCallSearch.Basic

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

theorem codePrefixExactFuelRunnerConstruction_of_indexedDecidable
    {machineState : Type u} [DecidableEq machineState]
    (M : TuringMachine MachineCodeSymbol machineState)
    (hindexed :
      CodePrefixExactFuelRunnerConstruction
        (TuringMachine.indexedDecidable M)) :
    CodePrefixExactFuelRunnerConstruction M := by
  rcases hindexed with ⟨runnerState, runner, hrunner⟩
  refine ⟨runnerState, runner, ?_⟩
  intro input fuel
  exact Iff.trans (hrunner input fuel)
    (TuringMachine.indexedDecidable_haltsOnInputIn_iff M fuel input)

/--
Conversely, any exact-fuel runner for the original machine also serves the
indexed copy.  This keeps later constructions free to move across the indexed
boundary in either direction.
-/
theorem codePrefixExactFuelRunnerConstruction_indexed_of
    {machineState : Type u}
    (M : TuringMachine MachineCodeSymbol machineState)
    (h :
      CodePrefixExactFuelRunnerConstruction M) :
    CodePrefixExactFuelRunnerConstruction (TuringMachine.indexed M) := by
  rcases h with ⟨runnerState, runner, hrunner⟩
  refine ⟨runnerState, runner, ?_⟩
  intro input fuel
  exact Iff.trans (hrunner input fuel)
    (Iff.symm (TuringMachine.indexed_haltsOnInputIn_iff
      M fuel input))

theorem codePrefixExactFuelRunnerConstruction_indexedDecidable_of
    {machineState : Type u} [DecidableEq machineState]
    (M : TuringMachine MachineCodeSymbol machineState)
    (h :
      CodePrefixExactFuelRunnerConstruction M) :
    CodePrefixExactFuelRunnerConstruction
      (TuringMachine.indexedDecidable M) := by
  rcases h with ⟨runnerState, runner, hrunner⟩
  refine ⟨runnerState, runner, ?_⟩
  intro input fuel
  exact Iff.trans (hrunner input fuel)
    (Iff.symm (TuringMachine.indexedDecidable_haltsOnInputIn_iff
      M fuel input))

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
  cases n with
  | zero =>
      exact False.elim (Fin.elim0 M.start)
  | succ n =>
      sorry

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

theorem codePrefixExactFuelRunner_haltsOnInput_zero_iff
    {machineState : Type u} {runnerState : Type v}
    {M : TuringMachine MachineCodeSymbol machineState}
    {runner : TuringMachine MachineCodeSymbol runnerState}
    (hrunner :
      forall input : Word MachineCodeSymbol,
      forall fuel : Nat,
        TuringMachine.HaltsOnInput runner
            (CodePrefixRecognizerStageCode input fuel) <->
          TuringMachine.HaltsOnInputIn M fuel input)
    (input : Word MachineCodeSymbol) :
    TuringMachine.HaltsOnInput runner
        (CodePrefixRecognizerStageCode input 0) <->
      TuringMachine.Halted M (TuringMachine.initial M input) := by
  exact Iff.trans (hrunner input 0)
    TuringMachine.haltsOnInputIn_zero_iff

theorem codePrefixExactFuelRunner_haltsOnInput_succ_transition_iff
    {machineState : Type u} {runnerState : Type v}
    {M : TuringMachine MachineCodeSymbol machineState}
    {runner : TuringMachine MachineCodeSymbol runnerState}
    (hrunner :
      forall input : Word MachineCodeSymbol,
      forall fuel : Nat,
        TuringMachine.HaltsOnInput runner
            (CodePrefixRecognizerStageCode input fuel) <->
          TuringMachine.HaltsOnInputIn M fuel input)
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    TuringMachine.HaltsOnInput runner
        (CodePrefixRecognizerStageCode input (fuel + 1)) <->
      exists write : Option MachineCodeSymbol,
      exists dir : Direction,
      exists nextState : machineState,
        M.transition M.start (Tape.read (Tape.input input)) =
          some (write, dir, nextState) ∧
          TuringMachine.HaltsFromIn M fuel
            { state := nextState,
              tape :=
                Tape.move dir
                  (Tape.write write (Tape.input input)) } := by
  exact Iff.trans (hrunner input (fuel + 1))
    TuringMachine.haltsOnInputIn_succ_transition_iff

theorem codePrefixExactFuelRunner_haltsOnInput_succ_iff_of_transition_eq_some
    {machineState : Type u} {runnerState : Type v}
    {M : TuringMachine MachineCodeSymbol machineState}
    {runner : TuringMachine MachineCodeSymbol runnerState}
    (hrunner :
      forall input : Word MachineCodeSymbol,
      forall fuel : Nat,
        TuringMachine.HaltsOnInput runner
            (CodePrefixRecognizerStageCode input fuel) <->
          TuringMachine.HaltsOnInputIn M fuel input)
    (input : Word MachineCodeSymbol) (fuel : Nat)
    {write : Option MachineCodeSymbol} {dir : Direction}
    {nextState : machineState}
    (htransition :
      M.transition M.start (Tape.read (Tape.input input)) =
        some (write, dir, nextState)) :
    TuringMachine.HaltsOnInput runner
        (CodePrefixRecognizerStageCode input (fuel + 1)) <->
      TuringMachine.HaltsFromIn M fuel
        { state := nextState,
          tape := Tape.move dir (Tape.write write (Tape.input input)) } := by
  exact Iff.trans (hrunner input (fuel + 1))
    (TuringMachine.haltsOnInputIn_succ_iff_of_transition_eq_some
      (M := M) (n := fuel) (w := input) htransition)

theorem codePrefixExactFuelRunner_haltsOnInput_succ_iff_false_of_transition_eq_none
    {machineState : Type u} {runnerState : Type v}
    {M : TuringMachine MachineCodeSymbol machineState}
    {runner : TuringMachine MachineCodeSymbol runnerState}
    (hrunner :
      forall input : Word MachineCodeSymbol,
      forall fuel : Nat,
        TuringMachine.HaltsOnInput runner
            (CodePrefixRecognizerStageCode input fuel) <->
          TuringMachine.HaltsOnInputIn M fuel input)
    (input : Word MachineCodeSymbol) (fuel : Nat)
    (htransition :
      M.transition M.start (Tape.read (Tape.input input)) = none) :
    TuringMachine.HaltsOnInput runner
        (CodePrefixRecognizerStageCode input (fuel + 1)) <-> False := by
  exact Iff.trans (hrunner input (fuel + 1))
    (TuringMachine.haltsOnInputIn_succ_iff_false_of_transition_eq_none
      (M := M) (n := fuel) (w := input) htransition)

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

theorem codePrefixExactFuelRunner_haltsOnNested_zero_iff
    {machineState : Type u} {runnerState : Type v}
    {M : TuringMachine MachineCodeSymbol machineState}
    {runner : TuringMachine MachineCodeSymbol runnerState}
    (hrunner :
      forall input : Word MachineCodeSymbol,
      forall fuel : Nat,
        TuringMachine.HaltsOnInput runner
            (CodePrefixRecognizerStageCode input fuel) <->
          TuringMachine.HaltsOnInputIn M fuel input)
    (input : Word MachineCodeSymbol) (inner : Nat) :
    TuringMachine.HaltsOnInput runner
        (NestedCodePrefixRecognizerStageCode input inner 0) <->
      TuringMachine.Halted M
        (TuringMachine.initial M
          (CodePrefixRecognizerStageCode input inner)) := by
  simpa [NestedCodePrefixRecognizerStageCode] using
    codePrefixExactFuelRunner_haltsOnInput_zero_iff
      hrunner (CodePrefixRecognizerStageCode input inner)

theorem codePrefixExactFuelRunner_haltsOnNested_succ_transition_iff
    {machineState : Type u} {runnerState : Type v}
    {M : TuringMachine MachineCodeSymbol machineState}
    {runner : TuringMachine MachineCodeSymbol runnerState}
    (hrunner :
      forall input : Word MachineCodeSymbol,
      forall fuel : Nat,
        TuringMachine.HaltsOnInput runner
            (CodePrefixRecognizerStageCode input fuel) <->
          TuringMachine.HaltsOnInputIn M fuel input)
    (input : Word MachineCodeSymbol) (inner outerFuel : Nat) :
    TuringMachine.HaltsOnInput runner
        (NestedCodePrefixRecognizerStageCode input inner
          (outerFuel + 1)) <->
      exists write : Option MachineCodeSymbol,
      exists dir : Direction,
      exists nextState : machineState,
        M.transition M.start
            (Tape.read
              (Tape.input
                (CodePrefixRecognizerStageCode input inner))) =
          some (write, dir, nextState) ∧
          TuringMachine.HaltsFromIn M outerFuel
            { state := nextState,
              tape :=
                Tape.move dir
                  (Tape.write write
                    (Tape.input
                      (CodePrefixRecognizerStageCode input inner))) } := by
  simpa [NestedCodePrefixRecognizerStageCode] using
    codePrefixExactFuelRunner_haltsOnInput_succ_transition_iff
      hrunner (CodePrefixRecognizerStageCode input inner) outerFuel

theorem codePrefixExactFuelRunner_haltsOnNested_succ_iff_of_transition_eq_some
    {machineState : Type u} {runnerState : Type v}
    {M : TuringMachine MachineCodeSymbol machineState}
    {runner : TuringMachine MachineCodeSymbol runnerState}
    (hrunner :
      forall input : Word MachineCodeSymbol,
      forall fuel : Nat,
        TuringMachine.HaltsOnInput runner
            (CodePrefixRecognizerStageCode input fuel) <->
          TuringMachine.HaltsOnInputIn M fuel input)
    (input : Word MachineCodeSymbol) (inner outerFuel : Nat)
    {write : Option MachineCodeSymbol} {dir : Direction}
    {nextState : machineState}
    (htransition :
      M.transition M.start
          (Tape.read
            (Tape.input
              (CodePrefixRecognizerStageCode input inner))) =
        some (write, dir, nextState)) :
    TuringMachine.HaltsOnInput runner
        (NestedCodePrefixRecognizerStageCode input inner
          (outerFuel + 1)) <->
      TuringMachine.HaltsFromIn M outerFuel
        { state := nextState,
          tape :=
            Tape.move dir
              (Tape.write write
                (Tape.input
                  (CodePrefixRecognizerStageCode input inner))) } := by
  simpa [NestedCodePrefixRecognizerStageCode] using
    codePrefixExactFuelRunner_haltsOnInput_succ_iff_of_transition_eq_some
      hrunner (CodePrefixRecognizerStageCode input inner)
      outerFuel htransition

theorem codePrefixExactFuelRunner_haltsOnNested_succ_iff_false_of_transition_eq_none
    {machineState : Type u} {runnerState : Type v}
    {M : TuringMachine MachineCodeSymbol machineState}
    {runner : TuringMachine MachineCodeSymbol runnerState}
    (hrunner :
      forall input : Word MachineCodeSymbol,
      forall fuel : Nat,
        TuringMachine.HaltsOnInput runner
            (CodePrefixRecognizerStageCode input fuel) <->
          TuringMachine.HaltsOnInputIn M fuel input)
    (input : Word MachineCodeSymbol) (inner outerFuel : Nat)
    (htransition :
      M.transition M.start
          (Tape.read
            (Tape.input
              (CodePrefixRecognizerStageCode input inner))) = none) :
    TuringMachine.HaltsOnInput runner
        (NestedCodePrefixRecognizerStageCode input inner
          (outerFuel + 1)) <-> False := by
  simpa [NestedCodePrefixRecognizerStageCode] using
    codePrefixExactFuelRunner_haltsOnInput_succ_iff_false_of_transition_eq_none
      hrunner (CodePrefixRecognizerStageCode input inner)
      outerFuel htransition

/--
Unbounded search over generated inner inputs and exact outer fuels for a
wrapped machine.
-/
def CodePrefixNestedExactFuelSearchConstruction
    {machineState : Type u}
    (M : TuringMachine MachineCodeSymbol machineState) : Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    forall input : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput searcher input <->
        exists inner : Nat,
        exists outer : Nat,
          TuringMachine.HaltsOnInputIn M outer
            (CodePrefixRecognizerStageCode input inner)

/--
Nested exact-fuel search can be reduced to the indexed copy of the wrapped
machine.
-/
theorem codePrefixNestedExactFuelSearchConstruction_of_indexed
    {machineState : Type u}
    (M : TuringMachine MachineCodeSymbol machineState)
    (hindexed :
      CodePrefixNestedExactFuelSearchConstruction
        (TuringMachine.indexed M)) :
    CodePrefixNestedExactFuelSearchConstruction M := by
  rcases hindexed with ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro input
  constructor
  · intro hhalt
    rcases (hsearcher input).mp hhalt with
      ⟨inner, outer, hindexedHalt⟩
    exact
      ⟨inner, outer,
        (TuringMachine.indexed_haltsOnInputIn_iff
          M outer (CodePrefixRecognizerStageCode input inner)).mp
          hindexedHalt⟩
  · intro htarget
    rcases htarget with ⟨inner, outer, hhalt⟩
    exact (hsearcher input).mpr
      ⟨inner, outer,
        (TuringMachine.indexed_haltsOnInputIn_iff
          M outer (CodePrefixRecognizerStageCode input inner)).mpr
          hhalt⟩

theorem codePrefixNestedExactFuelSearchConstruction_of_indexedDecidable
    {machineState : Type u} [DecidableEq machineState]
    (M : TuringMachine MachineCodeSymbol machineState)
    (hindexed :
      CodePrefixNestedExactFuelSearchConstruction
        (TuringMachine.indexedDecidable M)) :
    CodePrefixNestedExactFuelSearchConstruction M := by
  rcases hindexed with ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro input
  constructor
  · intro hhalt
    rcases (hsearcher input).mp hhalt with
      ⟨inner, outer, hindexedHalt⟩
    exact
      ⟨inner, outer,
        (TuringMachine.indexedDecidable_haltsOnInputIn_iff
          M outer (CodePrefixRecognizerStageCode input inner)).mp
          hindexedHalt⟩
  · intro htarget
    rcases htarget with ⟨inner, outer, hhalt⟩
    exact (hsearcher input).mpr
      ⟨inner, outer,
        (TuringMachine.indexedDecidable_haltsOnInputIn_iff
          M outer (CodePrefixRecognizerStageCode input inner)).mpr
          hhalt⟩

end Computability
end FoC
