import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.StageSearchController.GeneratedCallSearch.ExactFuel

set_option doc.verso true

/-!
# Generated nested-pair enumeration

Unbounded and bounded nested-pair enumerator interfaces plus their adapters to
exact-fuel search.
-/

namespace FoC
namespace Computability

open Languages

universe uStage uDescription uSimulator

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

theorem codePrefixNestedPairEnumeratorConstruction_of_indexedDecidable
    {selectedState : Type u} [DecidableEq selectedState]
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (hindexed :
      CodePrefixNestedPairEnumeratorConstruction
        (TuringMachine.indexedDecidable selected)) :
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
        (TuringMachine.indexedDecidable_haltsOnInput_iff selected
          (NestedCodePrefixRecognizerStageCode input inner outer)).mp
          hindexedHalt⟩
  · intro htarget
    rcases htarget with ⟨inner, outer, hhalt⟩
    exact (hsearcher input).mpr
      ⟨inner, outer,
        (TuringMachine.indexedDecidable_haltsOnInput_iff selected
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

theorem codePrefixNestedPairEnumeratorConstruction_of_finStateConstructionDecidable
    {selectedState : Type u} [DecidableEq selectedState]
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (hFin : CodePrefixNestedPairEnumeratorFinStateConstruction) :
    CodePrefixNestedPairEnumeratorConstruction selected := by
  exact
    codePrefixNestedPairEnumeratorConstruction_of_indexedDecidable selected
      (hFin selected.statesFinite.elems.length
        (TuringMachine.indexedDecidable selected))

/--
Remaining concrete finite-table leaf for unbounded generated-pair
enumeration over indexed selected recognizers.
-/
theorem codePrefixNestedPairEnumeratorFinStateFiniteLeaf :
    CodePrefixNestedPairEnumeratorFinStateConstruction := by
  intro n selected
  cases n with
  | zero =>
      exact False.elim (Fin.elim0 selected.start)
  | succ n =>
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

theorem codePrefixNestedPairEnumeratorFiniteLeafDecidable
    {selectedState : Type u} [DecidableEq selectedState]
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    CodePrefixNestedPairEnumeratorConstruction selected := by
  exact
    codePrefixNestedPairEnumeratorConstruction_of_finStateConstructionDecidable
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

theorem codePrefixNestedExactFuelSearchFiniteLeafDecidable
    {machineState : Type u} [DecidableEq machineState]
    (M : TuringMachine MachineCodeSymbol machineState) :
    CodePrefixNestedExactFuelSearchConstruction M := by
  rcases codePrefixExactFuelRunnerFiniteLeafDecidable M with
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

theorem codePrefixBoundedNestedPairEnumeratorConstruction_of_indexedDecidable
    {selectedState : Type u} [DecidableEq selectedState]
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (hindexed :
      CodePrefixBoundedNestedPairEnumeratorConstruction
        (TuringMachine.indexedDecidable selected)) :
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
        (TuringMachine.indexedDecidable_haltsOnInput_iff selected
          (NestedCodePrefixRecognizerStageCode input inner outer)).mp
          hindexedHalt⟩
  · intro htarget
    rcases htarget with ⟨inner, outer, hinner, houter, hhalt⟩
    exact (hsearcher input budget).mpr
      ⟨inner, outer, hinner, houter,
        (TuringMachine.indexedDecidable_haltsOnInput_iff selected
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

theorem codePrefixBoundedNestedPairEnumeratorConstruction_of_finStateConstructionDecidable
    {selectedState : Type u} [DecidableEq selectedState]
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (hFin : CodePrefixBoundedNestedPairEnumeratorFinStateConstruction) :
    CodePrefixBoundedNestedPairEnumeratorConstruction selected := by
  exact
    codePrefixBoundedNestedPairEnumeratorConstruction_of_indexedDecidable
      selected
      (hFin selected.statesFinite.elems.length
        (TuringMachine.indexedDecidable selected))

/--
Remaining concrete finite-table leaf for bounded generated-pair enumeration
over indexed selected recognizers.
-/
theorem codePrefixBoundedNestedPairEnumeratorFinStateFiniteLeaf :
    CodePrefixBoundedNestedPairEnumeratorFinStateConstruction := by
  intro n selected
  cases n with
  | zero =>
      exact False.elim (Fin.elim0 selected.start)
  | succ n =>
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

theorem codePrefixBoundedNestedExactFuelSearchConstruction_of_indexedDecidable
    {machineState : Type u} [DecidableEq machineState]
    (M : TuringMachine MachineCodeSymbol machineState)
    (hindexed :
      CodePrefixBoundedNestedExactFuelSearchConstruction
        (TuringMachine.indexedDecidable M)) :
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
        (TuringMachine.indexedDecidable_haltsOnInputIn_iff
          M outer (CodePrefixRecognizerStageCode input inner)).mp
          hindexedHalt⟩
  · intro htarget
    rcases htarget with ⟨inner, outer, hinner, houter, hhalt⟩
    exact (hsearcher input budget).mpr
      ⟨inner, outer, hinner, houter,
        (TuringMachine.indexedDecidable_haltsOnInputIn_iff
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

theorem codePrefixBoundedNestedPairEnumeratorFiniteLeafDecidable
    {selectedState : Type u} [DecidableEq selectedState]
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    CodePrefixBoundedNestedPairEnumeratorConstruction selected := by
  exact
    codePrefixBoundedNestedPairEnumeratorConstruction_of_finStateConstructionDecidable
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

theorem codePrefixBoundedNestedExactFuelSearchFiniteLeafDecidable
    {machineState : Type u} [DecidableEq machineState]
    (M : TuringMachine MachineCodeSymbol machineState) :
    CodePrefixBoundedNestedExactFuelSearchConstruction M := by
  rcases codePrefixExactFuelRunnerFiniteLeafDecidable M with
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

end Computability
end FoC
