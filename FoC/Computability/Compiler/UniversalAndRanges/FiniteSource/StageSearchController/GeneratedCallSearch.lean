import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.StageSearchController.GeneratedCallHandoff
import FoC.Computability.Compiler.Core.CommonGround.SearchAlgebra

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

universe uStage uDescription uSimulator

/-!
# Generated stage-code calls

Shared shape lemmas for controller helpers that generate a fresh unary stage
code around an already stage-coded input.  The concrete finite drivers use
this nested form for selected generated calls, fuel-pair runners, and bounded
outer-loop attempts.
-/

/-- Nested stage code: an inner generated bound over a preserved payload, then
an outer generated bound around that whole call. -/
def NestedCodePrefixRecognizerStageCode
    (input : Word MachineCodeSymbol) (inner outer : Nat) :
    Word MachineCodeSymbol :=
  CodePrefixRecognizerStageCode
    (CodePrefixRecognizerStageCode input inner) outer

theorem nestedCodePrefixRecognizerStageCode_eq
    (input : Word MachineCodeSymbol) (inner outer : Nat) :
    NestedCodePrefixRecognizerStageCode input inner outer =
      CodePrefixRecognizerStageCode
        (CodePrefixRecognizerStageCode input inner) outer := by
  rfl

theorem nestedCodePrefixRecognizerStageCode_decodeNat_outer
    (input : Word MachineCodeSymbol) (inner outer : Nat) :
    MachineDescription.decodeNat
        (NestedCodePrefixRecognizerStageCode input inner outer) =
      some (outer, CodePrefixRecognizerStageCode input inner) := by
  simp [NestedCodePrefixRecognizerStageCode,
    codePrefixRecognizerStageCode_decodeNat]

theorem nestedCodePrefixRecognizerStageCode_decodeNat_inner
    (input : Word MachineCodeSymbol) (inner : Nat) :
    MachineDescription.decodeNat
        (CodePrefixRecognizerStageCode input inner) =
      some (inner, input) := by
  simp [codePrefixRecognizerStageCode_decodeNat]

theorem nestedCodePrefixRecognizerStageCode_eq_of_decodeNat_outer_inner
    {tokens innerCode input : Word MachineCodeSymbol}
    {inner outer : Nat}
    (houter :
      MachineDescription.decodeNat tokens =
        some (outer, innerCode))
    (hinner :
      MachineDescription.decodeNat innerCode =
        some (inner, input)) :
    tokens = NestedCodePrefixRecognizerStageCode input inner outer := by
  have htokens :
      tokens = CodePrefixRecognizerStageCode innerCode outer :=
    codePrefixRecognizerStageCode_eq_of_decodeNat houter
  have hinnerCode :
      innerCode = CodePrefixRecognizerStageCode input inner :=
    codePrefixRecognizerStageCode_eq_of_decodeNat hinner
  rw [htokens, hinnerCode]
  rfl

theorem nestedCodePrefixRecognizerStageCode_decodeNat_outer_eq_some_iff
    {tokens input : Word MachineCodeSymbol}
    {inner outer : Nat} :
    MachineDescription.decodeNat tokens =
        some (outer, CodePrefixRecognizerStageCode input inner) <->
      tokens =
        NestedCodePrefixRecognizerStageCode input inner outer := by
  constructor
  · intro h
    exact
      nestedCodePrefixRecognizerStageCode_eq_of_decodeNat_outer_inner
        h
        (nestedCodePrefixRecognizerStageCode_decodeNat_inner
          input inner)
  · intro h
    rw [h]
    exact
      nestedCodePrefixRecognizerStageCode_decodeNat_outer
        input inner outer

theorem nestedCodePrefixRecognizerStageCode_decodeNat_pair_iff
    {tokens input : Word MachineCodeSymbol}
    {inner outer : Nat} :
    (exists innerCode : Word MachineCodeSymbol,
      MachineDescription.decodeNat tokens =
          some (outer, innerCode) ∧
        MachineDescription.decodeNat innerCode =
          some (inner, input)) <->
      tokens =
        NestedCodePrefixRecognizerStageCode input inner outer := by
  constructor
  · intro h
    rcases h with ⟨innerCode, houter, hinner⟩
    exact
      nestedCodePrefixRecognizerStageCode_eq_of_decodeNat_outer_inner
        houter hinner
  · intro h
    subst tokens
    exact
      ⟨CodePrefixRecognizerStageCode input inner,
        nestedCodePrefixRecognizerStageCode_decodeNat_outer
          input inner outer,
        nestedCodePrefixRecognizerStageCode_decodeNat_inner
          input inner⟩

theorem nestedCodePrefixRecognizerStageCode_injective
    {input₁ input₂ : Word MachineCodeSymbol}
    {inner₁ inner₂ outer₁ outer₂ : Nat}
    (h :
      NestedCodePrefixRecognizerStageCode input₁ inner₁ outer₁ =
        NestedCodePrefixRecognizerStageCode input₂ inner₂ outer₂) :
    outer₁ = outer₂ ∧ inner₁ = inner₂ ∧ input₁ = input₂ := by
  rcases
      codePrefixRecognizerStageCode_injective
        (by
          simpa [NestedCodePrefixRecognizerStageCode] using h) with
    ⟨houter, hinnerCode⟩
  rcases codePrefixRecognizerStageCode_injective hinnerCode with
    ⟨hinner, hinput⟩
  exact ⟨houter, hinner, hinput⟩

theorem nestedCodePrefixRecognizerStageCode_eq_iff
    {input₁ input₂ : Word MachineCodeSymbol}
    {inner₁ inner₂ outer₁ outer₂ : Nat} :
    NestedCodePrefixRecognizerStageCode input₁ inner₁ outer₁ =
        NestedCodePrefixRecognizerStageCode input₂ inner₂ outer₂ <->
      outer₁ = outer₂ ∧ inner₁ = inner₂ ∧ input₁ = input₂ := by
  constructor
  · exact nestedCodePrefixRecognizerStageCode_injective
  · intro h
    rcases h with ⟨houter, hinner, hinput⟩
    subst outer₂
    subst inner₂
    subst input₂
    rfl

/--
Ordinary generated-call parser construction.  This is the reusable wrapper
already supplied by {module}`FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.StageSearchController.GeneratedCallHandoff`:
it parses a generated stage-code prefix and invokes the supplied runner on the
rebuilt input.  It does not expose an exact step count for the wrapped runner.
-/
def CodePrefixGeneratedCallParserConstruction
    {selectedState : Type u}
    (selected : TuringMachine MachineCodeSymbol selectedState) : Prop :=
  exists runnerState : Type,
  exists runner : TuringMachine MachineCodeSymbol runnerState,
    forall tokens : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput runner tokens <->
        exists fuel : Nat,
        exists input : Word MachineCodeSymbol,
          tokens = CodePrefixRecognizerStageCode input fuel ∧
            TuringMachine.HaltsOnInput selected
              (CodePrefixRecognizerStageCode input fuel)

/--
Named adapter for the ordinary generated-call parser.  Keep this separate from
{lit}`CodePrefixExactFuelRunnerConstruction`: the exact-fuel contract below
requires {name}`TuringMachine.HaltsOnInputIn`, while this parser preserves only
ordinary halting of the wrapped machine.
-/
theorem codePrefixGeneratedCallParserConstruction_finite
    {selectedState : Type u}
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    CodePrefixGeneratedCallParserConstruction selected := by
  rcases
      boundedSimulatorCanonicalInputParserMachine_construction selected with
    ⟨runnerState, runner, hrunner⟩
  refine
    ⟨Fin runner.statesFinite.elems.length,
      TuringMachine.indexed runner, ?_⟩
  intro tokens
  exact
    Iff.trans
      (TuringMachine.indexed_haltsOnInput_iff runner tokens)
      (hrunner tokens)

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

/--
Unbounded generated-pair enumerator.  The concrete machine preserves the raw
input, enumerates two unary natural parameters, rebuilds the nested generated
call, and invokes the supplied selected runner.
-/
def CodePrefixNestedPairEnumeratorConstruction
    {selectedState : Type u}
    (selected : TuringMachine MachineCodeSymbol selectedState) : Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    forall input : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput searcher input <->
        exists inner : Nat,
        exists outer : Nat,
          TuringMachine.HaltsOnInput selected
            (NestedCodePrefixRecognizerStageCode input inner outer)

/--
Concrete-state generated-pair enumerator target.  Proving this for all
{lit}`Fin n` selected recognizers is enough for the public arbitrary-state
leaf.
-/
def CodePrefixNestedPairEnumeratorFinStateConstruction : Prop :=
  forall n : Nat,
    forall selected : TuringMachine MachineCodeSymbol (Fin n),
      CodePrefixNestedPairEnumeratorConstruction selected

/--
It is enough to prove generated-pair enumeration for the indexed copy of the
selected recognizer.
-/
theorem codePrefixNestedPairEnumeratorConstruction_of_indexed
    {selectedState : Type u}
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (hindexed :
      CodePrefixNestedPairEnumeratorConstruction
        (TuringMachine.indexed selected)) :
    CodePrefixNestedPairEnumeratorConstruction selected := by
  rcases hindexed with ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro input
  constructor
  · intro hhalt
    rcases (hsearcher input).mp hhalt with
      ⟨inner, outer, hindexedHalt⟩
    exact
      ⟨inner, outer,
        (TuringMachine.indexed_haltsOnInput_iff selected
          (NestedCodePrefixRecognizerStageCode input inner outer)).mp
          hindexedHalt⟩
  · intro htarget
    rcases htarget with ⟨inner, outer, hhalt⟩
    exact (hsearcher input).mpr
      ⟨inner, outer,
        (TuringMachine.indexed_haltsOnInput_iff selected
          (NestedCodePrefixRecognizerStageCode input inner outer)).mpr
          hhalt⟩

/--
A generated-pair enumerator for every concrete {lit}`Fin n` recognizer state
space suffices for arbitrary selected recognizers.
-/
theorem codePrefixNestedPairEnumeratorConstruction_of_finStateConstruction
    {selectedState : Type u}
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (hFin : CodePrefixNestedPairEnumeratorFinStateConstruction) :
    CodePrefixNestedPairEnumeratorConstruction selected := by
  exact
    codePrefixNestedPairEnumeratorConstruction_of_indexed selected
      (hFin selected.statesFinite.elems.length
        (TuringMachine.indexed selected))

/--
Remaining concrete finite-table leaf for unbounded generated-pair
enumeration over indexed selected recognizers.
-/
theorem codePrefixNestedPairEnumeratorFinStateFiniteLeaf :
    CodePrefixNestedPairEnumeratorFinStateConstruction := by
  intro n selected
  sorry

/--
Finite-machine leaf for unbounded generated-pair enumeration.
-/
theorem codePrefixNestedPairEnumeratorFiniteLeaf
    {selectedState : Type u}
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    CodePrefixNestedPairEnumeratorConstruction selected := by
  exact
    codePrefixNestedPairEnumeratorConstruction_of_finStateConstruction
      selected codePrefixNestedPairEnumeratorFinStateFiniteLeaf

/--
Composition of the exact-fuel runner and unbounded generated-pair enumerator.
This is the shared helper behind raw budget/fuel searches.
-/
theorem codePrefixNestedExactFuelSearchFiniteLeaf
    {machineState : Type u}
    (M : TuringMachine MachineCodeSymbol machineState) :
    CodePrefixNestedExactFuelSearchConstruction M := by
  rcases codePrefixExactFuelRunnerFiniteLeaf M with
    ⟨selectedState, selected, hselected⟩
  rcases codePrefixNestedPairEnumeratorFiniteLeaf selected with
    ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro input
  constructor
  · intro hhalt
    rcases (hsearcher input).mp hhalt with
      ⟨inner, outer, hselectedHalt⟩
    exact
      ⟨inner, outer,
        (codePrefixExactFuelRunner_haltsOnNested_iff
          hselected input inner outer).mp hselectedHalt⟩
  · intro htarget
    rcases htarget with ⟨inner, outer, hM⟩
    exact (hsearcher input).mpr
      ⟨inner, outer,
        (codePrefixExactFuelRunner_haltsOnNested_iff
          hselected input inner outer).mpr hM⟩

/--
Bounded generated-pair enumerator.  The input carries an outer budget; the
machine enumerates pairs bounded by that budget and invokes the selected
runner on each rebuilt nested generated call.
-/
def CodePrefixBoundedNestedPairEnumeratorConstruction
    {selectedState : Type u}
    (selected : TuringMachine MachineCodeSymbol selectedState) : Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    forall input : Word MachineCodeSymbol,
    forall budget : Nat,
      TuringMachine.HaltsOnInput searcher
          (CodePrefixRecognizerStageCode input budget) <->
        exists inner : Nat,
        exists outer : Nat,
          inner ≤ budget ∧
            outer ≤ budget ∧
            TuringMachine.HaltsOnInput selected
              (NestedCodePrefixRecognizerStageCode input inner outer)

/--
Concrete-state bounded generated-pair enumerator target.  The public arbitrary
state construction follows by indexing the supplied selected recognizer.
-/
def CodePrefixBoundedNestedPairEnumeratorFinStateConstruction : Prop :=
  forall n : Nat,
    forall selected : TuringMachine MachineCodeSymbol (Fin n),
      CodePrefixBoundedNestedPairEnumeratorConstruction selected

/--
The bounded generated-pair enumerator is also stable under replacing the
selected recognizer by its indexed copy.
-/
theorem codePrefixBoundedNestedPairEnumeratorConstruction_of_indexed
    {selectedState : Type u}
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (hindexed :
      CodePrefixBoundedNestedPairEnumeratorConstruction
        (TuringMachine.indexed selected)) :
    CodePrefixBoundedNestedPairEnumeratorConstruction selected := by
  rcases hindexed with ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro input budget
  constructor
  · intro hhalt
    rcases (hsearcher input budget).mp hhalt with
      ⟨inner, outer, hinner, houter, hindexedHalt⟩
    exact
      ⟨inner, outer, hinner, houter,
        (TuringMachine.indexed_haltsOnInput_iff selected
          (NestedCodePrefixRecognizerStageCode input inner outer)).mp
          hindexedHalt⟩
  · intro htarget
    rcases htarget with ⟨inner, outer, hinner, houter, hhalt⟩
    exact (hsearcher input budget).mpr
      ⟨inner, outer, hinner, houter,
        (TuringMachine.indexed_haltsOnInput_iff selected
          (NestedCodePrefixRecognizerStageCode input inner outer)).mpr
          hhalt⟩

/--
The bounded pair enumerator can likewise be proved only for concrete
{lit}`Fin n` selected recognizers and then transported to arbitrary finite
state types.
-/
theorem codePrefixBoundedNestedPairEnumeratorConstruction_of_finStateConstruction
    {selectedState : Type u}
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (hFin : CodePrefixBoundedNestedPairEnumeratorFinStateConstruction) :
    CodePrefixBoundedNestedPairEnumeratorConstruction selected := by
  exact
    codePrefixBoundedNestedPairEnumeratorConstruction_of_indexed selected
      (hFin selected.statesFinite.elems.length
        (TuringMachine.indexed selected))

/--
Remaining concrete finite-table leaf for bounded generated-pair enumeration
over indexed selected recognizers.
-/
theorem codePrefixBoundedNestedPairEnumeratorFinStateFiniteLeaf :
    CodePrefixBoundedNestedPairEnumeratorFinStateConstruction := by
  intro n selected
  sorry

/--
Bounded search over generated inner inputs and exact outer fuels for a wrapped
machine.
-/
def CodePrefixBoundedNestedExactFuelSearchConstruction
    {machineState : Type u}
    (M : TuringMachine MachineCodeSymbol machineState) : Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    forall input : Word MachineCodeSymbol,
    forall budget : Nat,
      TuringMachine.HaltsOnInput searcher
          (CodePrefixRecognizerStageCode input budget) <->
        exists inner : Nat,
        exists outer : Nat,
          inner ≤ budget ∧
            outer ≤ budget ∧
            TuringMachine.HaltsOnInputIn M outer
              (CodePrefixRecognizerStageCode input inner)

/--
The bounded nested exact-fuel search construction is likewise stable when the
wrapped machine is replaced by its indexed copy.
-/
theorem codePrefixBoundedNestedExactFuelSearchConstruction_of_indexed
    {machineState : Type u}
    (M : TuringMachine MachineCodeSymbol machineState)
    (hindexed :
      CodePrefixBoundedNestedExactFuelSearchConstruction
        (TuringMachine.indexed M)) :
    CodePrefixBoundedNestedExactFuelSearchConstruction M := by
  rcases hindexed with ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro input budget
  constructor
  · intro hhalt
    rcases (hsearcher input budget).mp hhalt with
      ⟨inner, outer, hinner, houter, hindexedHalt⟩
    exact
      ⟨inner, outer, hinner, houter,
        (TuringMachine.indexed_haltsOnInputIn_iff
          M outer (CodePrefixRecognizerStageCode input inner)).mp
          hindexedHalt⟩
  · intro htarget
    rcases htarget with ⟨inner, outer, hinner, houter, hhalt⟩
    exact (hsearcher input budget).mpr
      ⟨inner, outer, hinner, houter,
        (TuringMachine.indexed_haltsOnInputIn_iff
          M outer (CodePrefixRecognizerStageCode input inner)).mpr
          hhalt⟩

/--
Finite-machine leaf for bounded generated-pair enumeration.
-/
theorem codePrefixBoundedNestedPairEnumeratorFiniteLeaf
    {selectedState : Type u}
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    CodePrefixBoundedNestedPairEnumeratorConstruction selected := by
  exact
    codePrefixBoundedNestedPairEnumeratorConstruction_of_finStateConstruction
      selected codePrefixBoundedNestedPairEnumeratorFinStateFiniteLeaf

/--
Composition of the exact-fuel runner and bounded generated-pair enumerator.
This is the shared helper behind bounded simulator pair loops.
-/
theorem codePrefixBoundedNestedExactFuelSearchFiniteLeaf
    {machineState : Type u}
    (M : TuringMachine MachineCodeSymbol machineState) :
    CodePrefixBoundedNestedExactFuelSearchConstruction M := by
  rcases codePrefixExactFuelRunnerFiniteLeaf M with
    ⟨selectedState, selected, hselected⟩
  rcases codePrefixBoundedNestedPairEnumeratorFiniteLeaf selected with
    ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro input budget
  constructor
  · intro hhalt
    rcases (hsearcher input budget).mp hhalt with
      ⟨inner, outer, hinner, houter, hselectedHalt⟩
    exact
      ⟨inner, outer, hinner, houter,
        (codePrefixExactFuelRunner_haltsOnNested_iff
          hselected input inner outer).mp hselectedHalt⟩
  · intro htarget
    rcases htarget with ⟨inner, outer, hinner, houter, hM⟩
    exact (hsearcher input budget).mpr
      ⟨inner, outer, hinner, houter,
        (codePrefixExactFuelRunner_haltsOnNested_iff
          hselected input inner outer).mpr hM⟩

/--
Product exact-fuel runner for recognizer intersection.  The input carries two
generated fuel parameters; the machine runs the left recognizer for the outer
fuel and the right recognizer for the inner fuel on the same preserved input.
-/
def CodePrefixExactFuelProductRunnerConstruction
    {leftState : Type uStage} {rightState : Type uDescription}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) : Prop :=
  exists selectedState : Type,
  exists selected : TuringMachine MachineCodeSymbol selectedState,
    forall input : Word MachineCodeSymbol,
    forall leftFuel : Nat,
    forall rightFuel : Nat,
      TuringMachine.HaltsOnInput selected
          (NestedCodePrefixRecognizerStageCode
            input rightFuel leftFuel) <->
        TuringMachine.HaltsOnInputIn left leftFuel input ∧
          TuringMachine.HaltsOnInputIn right rightFuel input

/--
Concrete-state product exact-fuel runner target.  This is the remaining
finite-table target after both recognizers have been reindexed to {lit}`Fin`
state spaces.
-/
def CodePrefixExactFuelProductRunnerFinStateConstruction : Prop :=
  forall leftN rightN : Nat,
    forall left : TuringMachine MachineCodeSymbol (Fin leftN),
    forall right : TuringMachine MachineCodeSymbol (Fin rightN),
      CodePrefixExactFuelProductRunnerConstruction left right

/--
The product runner can be built against indexed copies of the two input
recognizers and then transported back to the original state types.
-/
theorem codePrefixExactFuelProductRunnerConstruction_of_indexed
    {leftState : Type uStage} {rightState : Type uDescription}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState)
    (hindexed :
      CodePrefixExactFuelProductRunnerConstruction
        (TuringMachine.indexed left) (TuringMachine.indexed right)) :
    CodePrefixExactFuelProductRunnerConstruction left right := by
  rcases hindexed with ⟨selectedState, selected, hselected⟩
  refine ⟨selectedState, selected, ?_⟩
  intro input leftFuel rightFuel
  constructor
  · intro hhalt
    rcases (hselected input leftFuel rightFuel).mp hhalt with
      ⟨hleft, hright⟩
    exact
      ⟨(TuringMachine.indexed_haltsOnInputIn_iff
          left leftFuel input).mp hleft,
        (TuringMachine.indexed_haltsOnInputIn_iff
          right rightFuel input).mp hright⟩
  · intro htarget
    rcases htarget with ⟨hleft, hright⟩
    exact (hselected input leftFuel rightFuel).mpr
      ⟨(TuringMachine.indexed_haltsOnInputIn_iff
          left leftFuel input).mpr hleft,
        (TuringMachine.indexed_haltsOnInputIn_iff
          right rightFuel input).mpr hright⟩

/--
For the product exact-fuel runner, it is enough to solve the case where both
input recognizers use concrete {lit}`Fin` state spaces.
-/
theorem codePrefixExactFuelProductRunnerConstruction_of_finStateConstruction
    {leftState : Type uStage} {rightState : Type uDescription}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState)
    (hFin : CodePrefixExactFuelProductRunnerFinStateConstruction) :
    CodePrefixExactFuelProductRunnerConstruction left right := by
  exact
    codePrefixExactFuelProductRunnerConstruction_of_indexed left right
      (hFin left.statesFinite.elems.length
        right.statesFinite.elems.length
        (TuringMachine.indexed left) (TuringMachine.indexed right))

/--
Remaining concrete finite-table leaf for the product exact-fuel runner over
indexed recognizers.
-/
theorem codePrefixExactFuelProductRunnerFinStateFiniteLeaf :
    CodePrefixExactFuelProductRunnerFinStateConstruction := by
  intro leftN rightN left right
  sorry

/--
Finite-machine leaf for the product exact-fuel runner.
-/
theorem codePrefixExactFuelProductRunnerFiniteLeaf
    {leftState : Type uStage} {rightState : Type uDescription}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) :
    CodePrefixExactFuelProductRunnerConstruction left right := by
  exact
    codePrefixExactFuelProductRunnerConstruction_of_finStateConstruction
      left right codePrefixExactFuelProductRunnerFinStateFiniteLeaf

/--
Unbounded product search over exact left/right fuel witnesses for a preserved
input.
-/
def CodePrefixExactFuelProductSearchConstruction
    {leftState : Type uStage} {rightState : Type uDescription}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) : Prop :=
  exists bothState : Type,
  exists both : TuringMachine MachineCodeSymbol bothState,
    forall input : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput both input <->
        exists leftFuel : Nat,
        exists rightFuel : Nat,
          TuringMachine.HaltsOnInputIn left leftFuel input ∧
            TuringMachine.HaltsOnInputIn right rightFuel input

/--
Composition of the exact-fuel product runner and unbounded generated-pair
enumerator.  This is the shared helper behind recognizer-intersection fuel
search.
-/
theorem codePrefixExactFuelProductSearchFiniteLeaf
    {leftState : Type uStage} {rightState : Type uDescription}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) :
    CodePrefixExactFuelProductSearchConstruction left right := by
  rcases codePrefixExactFuelProductRunnerFiniteLeaf left right with
    ⟨selectedState, selected, hselected⟩
  rcases codePrefixNestedPairEnumeratorFiniteLeaf selected with
    ⟨bothState, both, hboth⟩
  refine ⟨bothState, both, ?_⟩
  intro input
  constructor
  · intro hhalt
    rcases (hboth input).mp hhalt with
      ⟨rightFuel, leftFuel, hselectedHalt⟩
    exact
      ⟨leftFuel, rightFuel,
        (hselected input leftFuel rightFuel).mp hselectedHalt⟩
  · intro htarget
    rcases htarget with ⟨leftFuel, rightFuel, hleftRight⟩
    exact (hboth input).mpr
      ⟨rightFuel, leftFuel,
        (hselected input leftFuel rightFuel).mpr hleftRight⟩

/--
Generic pair-bounding algebra for dovetail drivers: existential search over a
raw pair is equivalent to existential search under some finite outer limit.
-/
theorem exists_bounded_pair_iff_exists_pair
    (P : Nat -> Nat -> Prop) :
    (exists limit : Nat,
      exists m : Nat,
      exists n : Nat,
        m ≤ limit ∧ n ≤ limit ∧ P m n) <->
      exists m : Nat, exists n : Nat, P m n := by
  exact CommonGround.exists_bounded_pair_iff_exists_pair P

/--
Generic triple-bounding algebra for dovetail drivers: existential search over
a raw triple is equivalent to existential search under some finite outer
limit.
-/
theorem exists_bounded_triple_iff_exists_triple
    (P : Nat -> Nat -> Nat -> Prop) :
    (exists limit : Nat,
      exists m : Nat,
      exists n : Nat,
      exists fuel : Nat,
        m ≤ limit ∧ n ≤ limit ∧ fuel ≤ limit ∧ P m n fuel) <->
      exists m : Nat, exists n : Nat, exists fuel : Nat, P m n fuel := by
  exact CommonGround.exists_bounded_triple_iff_exists_triple P

/--
Search over an explicit fuel component is the same as unbounded halting for
the selected generated input.
-/
theorem exists_pair_haltsOnInputIn_iff_exists_haltsOnInput
    {symbol : Type u} {state : Type v}
    (M : TuringMachine symbol state)
    (inputOf : Nat -> Word symbol) :
    (exists m : Nat,
      exists fuel : Nat,
        TuringMachine.HaltsOnInputIn M fuel (inputOf m)) <->
      exists m : Nat,
        TuringMachine.HaltsOnInput M (inputOf m) := by
  constructor
  · intro h
    rcases h with ⟨m, fuel, hfuel⟩
    exact
      ⟨m,
        TuringMachine.halts_on_input_in_to_halts_on_input
          (n := fuel) hfuel⟩
  · intro h
    rcases h with ⟨m, hhalt⟩
    rcases
        TuringMachine.halts_on_input_to_halts_on_input_in hhalt with
      ⟨fuel, hfuel⟩
    exact ⟨m, fuel, hfuel⟩

/--
Bounded dovetailing over a generated input index and an explicit fuel is
equivalent to unbounded halting for some generated input.
-/
theorem exists_bounded_pair_haltsOnInputIn_iff_exists_haltsOnInput
    {symbol : Type u} {state : Type v}
    (M : TuringMachine symbol state)
    (inputOf : Nat -> Word symbol) :
    (exists limit : Nat,
      exists m : Nat,
      exists fuel : Nat,
        m ≤ limit ∧
          fuel ≤ limit ∧
          TuringMachine.HaltsOnInputIn M fuel (inputOf m)) <->
      exists m : Nat,
        TuringMachine.HaltsOnInput M (inputOf m) := by
  exact
    Iff.trans
      (exists_bounded_pair_iff_exists_pair
        (fun m fuel =>
          TuringMachine.HaltsOnInputIn M fuel (inputOf m)))
      (exists_pair_haltsOnInputIn_iff_exists_haltsOnInput
        M inputOf)

/--
Search over two generated indices and an explicit simulation fuel is the same
as unbounded halting for some generated pair input.
-/
theorem exists_triple_haltsOnInputIn_iff_exists_pair_haltsOnInput
    {symbol : Type u} {state : Type v}
    (M : TuringMachine symbol state)
    (inputOf : Nat -> Nat -> Word symbol) :
    (exists m : Nat,
      exists n : Nat,
      exists fuel : Nat,
        TuringMachine.HaltsOnInputIn M fuel (inputOf m n)) <->
      exists m : Nat,
      exists n : Nat,
        TuringMachine.HaltsOnInput M (inputOf m n) := by
  constructor
  · intro h
    rcases h with ⟨m, n, fuel, hfuel⟩
    exact
      ⟨m, n,
        TuringMachine.halts_on_input_in_to_halts_on_input
          (n := fuel) hfuel⟩
  · intro h
    rcases h with ⟨m, n, hhalt⟩
    rcases
        TuringMachine.halts_on_input_to_halts_on_input_in hhalt with
      ⟨fuel, hfuel⟩
    exact ⟨m, n, fuel, hfuel⟩

/--
Bounded dovetailing over two generated indices and an explicit fuel is
equivalent to unbounded halting for some generated pair input.
-/
theorem exists_bounded_triple_haltsOnInputIn_iff_exists_pair_haltsOnInput
    {symbol : Type u} {state : Type v}
    (M : TuringMachine symbol state)
    (inputOf : Nat -> Nat -> Word symbol) :
    (exists limit : Nat,
      exists m : Nat,
      exists n : Nat,
      exists fuel : Nat,
        m ≤ limit ∧
          n ≤ limit ∧
          fuel ≤ limit ∧
          TuringMachine.HaltsOnInputIn M fuel (inputOf m n)) <->
      exists m : Nat,
      exists n : Nat,
        TuringMachine.HaltsOnInput M (inputOf m n) := by
  exact
    Iff.trans
      (exists_bounded_triple_iff_exists_triple
        (fun m n fuel =>
          TuringMachine.HaltsOnInputIn M fuel (inputOf m n)))
      (exists_triple_haltsOnInputIn_iff_exists_pair_haltsOnInput
        M inputOf)

/--
For a fixed public budget on the generated indices, adding a hidden exact fuel
component is equivalent to ordinary halting of the generated pair input.
-/
theorem exists_bounded_pair_haltsOnInputIn_iff_exists_bounded_pair_haltsOnInput
    {symbol : Type u} {state : Type v}
    (M : TuringMachine symbol state)
    (inputOf : Nat -> Nat -> Word symbol)
    (budget : Nat) :
    (exists m : Nat,
      exists n : Nat,
      exists fuel : Nat,
        m ≤ budget ∧
          n ≤ budget ∧
          TuringMachine.HaltsOnInputIn M fuel (inputOf m n)) <->
      exists m : Nat,
      exists n : Nat,
        m ≤ budget ∧
          n ≤ budget ∧
          TuringMachine.HaltsOnInput M (inputOf m n) := by
  constructor
  · intro h
    rcases h with ⟨m, n, fuel, hm, hn, hfuel⟩
    exact
      ⟨m, n, hm, hn,
        TuringMachine.halts_on_input_in_to_halts_on_input
          (n := fuel) hfuel⟩
  · intro h
    rcases h with ⟨m, n, hm, hn, hhalt⟩
    rcases
        TuringMachine.halts_on_input_to_halts_on_input_in hhalt with
      ⟨fuel, hfuel⟩
    exact ⟨m, n, fuel, hm, hn, hfuel⟩

/--
Two explicit fuel witnesses for the same input are equivalent to unbounded
halting of both machines on that input.
-/
theorem exists_pair_haltsOnInputIn_and_iff_haltsOnInput_and
    {symbol : Type u}
    {leftState : Type v} {rightState : Type w}
    (left : TuringMachine symbol leftState)
    (right : TuringMachine symbol rightState)
    (input : Word symbol) :
    (exists leftFuel : Nat,
      exists rightFuel : Nat,
        TuringMachine.HaltsOnInputIn left leftFuel input ∧
          TuringMachine.HaltsOnInputIn right rightFuel input) <->
      TuringMachine.HaltsOnInput left input ∧
        TuringMachine.HaltsOnInput right input := by
  constructor
  · intro h
    rcases h with ⟨leftFuel, rightFuel, hleft, hright⟩
    exact
      ⟨TuringMachine.halts_on_input_in_to_halts_on_input
          (n := leftFuel) hleft,
        TuringMachine.halts_on_input_in_to_halts_on_input
          (n := rightFuel) hright⟩
  · intro h
    rcases h with ⟨hleft, hright⟩
    rcases TuringMachine.halts_on_input_to_halts_on_input_in
        hleft with
      ⟨leftFuel, hleftFuel⟩
    rcases TuringMachine.halts_on_input_to_halts_on_input_in
        hright with
      ⟨rightFuel, hrightFuel⟩
    exact ⟨leftFuel, rightFuel, hleftFuel, hrightFuel⟩

/--
Unbounded search over generated inner inputs for a wrapped machine, hiding the
exact simulation fuel behind ordinary halting.
-/
def CodePrefixNestedHaltingSearchConstruction
    {machineState : Type u}
    (M : TuringMachine MachineCodeSymbol machineState) : Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    forall input : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput searcher input <->
        exists inner : Nat,
          TuringMachine.HaltsOnInput M
            (CodePrefixRecognizerStageCode input inner)

/--
Composition of nested exact-fuel search with the standard equivalence between
unbounded halting and exact-step halting.
-/
theorem codePrefixNestedHaltingSearchFiniteLeaf
    {machineState : Type u}
    (M : TuringMachine MachineCodeSymbol machineState) :
    CodePrefixNestedHaltingSearchConstruction M := by
  rcases codePrefixNestedExactFuelSearchFiniteLeaf M with
    ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro input
  exact Iff.trans (hsearcher input)
    (exists_pair_haltsOnInputIn_iff_exists_haltsOnInput
      M (fun inner => CodePrefixRecognizerStageCode input inner))

/--
Unbounded product search for recognizer intersection, hiding both exact fuel
witnesses behind ordinary halting.
-/
def CodePrefixProductHaltingSearchConstruction
    {leftState : Type uStage} {rightState : Type uDescription}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) : Prop :=
  exists bothState : Type,
  exists both : TuringMachine MachineCodeSymbol bothState,
    forall input : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput both input <->
        TuringMachine.HaltsOnInput left input ∧
          TuringMachine.HaltsOnInput right input

/--
Composition of product exact-fuel search with the standard exact-step
existential equivalence.
-/
theorem codePrefixProductHaltingSearchFiniteLeaf
    {leftState : Type uStage} {rightState : Type uDescription}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) :
    CodePrefixProductHaltingSearchConstruction left right := by
  rcases codePrefixExactFuelProductSearchFiniteLeaf left right with
    ⟨bothState, both, hboth⟩
  refine ⟨bothState, both, ?_⟩
  intro input
  exact Iff.trans (hboth input)
    (exists_pair_haltsOnInputIn_and_iff_haltsOnInput_and
      left right input)

/--
Bounded dovetailing over two fuel components is equivalent to both machines
halting on the preserved input.
-/
theorem exists_bounded_pair_haltsOnInputIn_and_iff_haltsOnInput_and
    {symbol : Type u}
    {leftState : Type v} {rightState : Type w}
    (left : TuringMachine symbol leftState)
    (right : TuringMachine symbol rightState)
    (input : Word symbol) :
    (exists limit : Nat,
      exists leftFuel : Nat,
      exists rightFuel : Nat,
        leftFuel ≤ limit ∧
          rightFuel ≤ limit ∧
          (TuringMachine.HaltsOnInputIn left leftFuel input ∧
            TuringMachine.HaltsOnInputIn right rightFuel input)) <->
      TuringMachine.HaltsOnInput left input ∧
        TuringMachine.HaltsOnInput right input := by
  exact
    Iff.trans
      (exists_bounded_pair_iff_exists_pair
        (fun leftFuel rightFuel =>
          TuringMachine.HaltsOnInputIn left leftFuel input ∧
            TuringMachine.HaltsOnInputIn right rightFuel input))
      (exists_pair_haltsOnInputIn_and_iff_haltsOnInput_and
        left right input)

end Computability
end FoC
