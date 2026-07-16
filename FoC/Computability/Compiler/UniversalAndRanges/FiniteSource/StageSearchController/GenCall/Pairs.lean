import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.ExactFuel
import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.StageSearchController.GenCall.ExactFuel

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
    FiniteRecognizer.NestedPairEnumeratorSpec searcher selected
      (fun input inner outer =>
        NestedCodePrefixRecognizerStageCode input inner outer)

/--
Implementation-oriented unbounded pair enumerator contract.  This exposes the
hidden selected-run fuel used by the actual dovetailing search while preserving
the public ordinary-halting contract above.
-/
def CodePrefixNestedHiddenFuelPairEnumeratorConstruction
    {selectedState : Type u}
    (selected : TuringMachine MachineCodeSymbol selectedState) : Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    FiniteRecognizer.TupleSearch.UnboundedHiddenFuelPairSpec
      searcher selected
      (fun input inner outer =>
        NestedCodePrefixRecognizerStageCode input inner outer)

theorem codePrefixNestedPairEnumeratorConstruction_of_hiddenFuel
    {selectedState : Type u}
    {selected : TuringMachine MachineCodeSymbol selectedState}
    (hhidden :
      CodePrefixNestedHiddenFuelPairEnumeratorConstruction selected) :
    CodePrefixNestedPairEnumeratorConstruction selected := by
  rcases hhidden with ⟨searcherState, searcher, hsearcher⟩
  exact
    ⟨searcherState, searcher,
      FiniteRecognizer.TupleSearch.nestedPairEnumeratorSpec_of_hiddenFuel
        hsearcher⟩

/--
Finite-machine leaf for unbounded hidden-fuel generated-pair search, adapted
from the core generated-code convention to the public code-prefix names.
-/
theorem codePrefixNestedHiddenFuelPairEnumeratorFiniteLeaf
    {selectedState : Type u}
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    CodePrefixNestedHiddenFuelPairEnumeratorConstruction selected := by
  rcases
      FiniteRecognizer.TupleSearch.generatedUnboundedHiddenFuelPairFiniteLeaf
        selected with
    ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro input
  simpa [FiniteRecognizer.GeneratedCode.nestedStageCode_eq_codePrefix]
    using hsearcher input

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
Concrete finite-table leaf for unbounded generated-pair enumeration over
indexed selected recognizers.
-/
theorem codePrefixNestedPairEnumeratorFinStateFiniteLeaf :
    CodePrefixNestedPairEnumeratorFinStateConstruction := by
  intro n selected
  rcases
      FiniteRecognizer.TupleSearch.generatedNestedPairEnumeratorFinStateFiniteLeaf
        n selected with
    ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro input
  simpa [FiniteRecognizer.GeneratedCode.nestedStageCode_eq_codePrefix]
    using hsearcher input

/--
Finite-machine leaf for unbounded generated-pair enumeration.
-/
theorem codePrefixNestedPairEnumeratorFiniteLeaf
    {selectedState : Type u}
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    CodePrefixNestedPairEnumeratorConstruction selected := by
  exact
    codePrefixNestedPairEnumeratorConstruction_of_hiddenFuel
      (codePrefixNestedHiddenFuelPairEnumeratorFiniteLeaf selected)

theorem codePrefixNestedPairEnumeratorFiniteLeafDecidable
    {selectedState : Type u} [DecidableEq selectedState]
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    CodePrefixNestedPairEnumeratorConstruction selected := by
  exact
    codePrefixNestedPairEnumeratorFiniteLeaf selected

/--
Composition of the exact-fuel runner and unbounded generated-pair enumerator.
This is the shared helper behind raw budget/fuel searches.
-/
theorem codePrefixNestedExactFuelSearchFiniteLeaf
    {machineState : Type u}
    (M : TuringMachine MachineCodeSymbol machineState) :
    CodePrefixNestedExactFuelSearchConstruction M := by
  rcases
      FiniteRecognizer.TupleSearch.generatedNestedExactFuelSearchFiniteLeaf
        M with
    ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro input
  simpa [FiniteRecognizer.GeneratedCode.stageCode_eq]
    using hsearcher input

theorem codePrefixNestedExactFuelSearchFiniteLeafDecidable
    {machineState : Type u} [DecidableEq machineState]
    (M : TuringMachine MachineCodeSymbol machineState) :
    CodePrefixNestedExactFuelSearchConstruction M := by
  exact codePrefixNestedExactFuelSearchFiniteLeaf M

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
    FiniteRecognizer.BoundedNestedPairEnumeratorSpec
      searcher selected
      CodePrefixRecognizerStageCode
      (fun input inner outer =>
        NestedCodePrefixRecognizerStageCode input inner outer)

/--
Implementation-oriented bounded pair enumerator contract.  The selected fuel
is hidden and unbounded; only the generated pair parameters are bounded by the
public budget.
-/
def CodePrefixBoundedNestedHiddenFuelPairEnumeratorConstruction
    {selectedState : Type u}
    (selected : TuringMachine MachineCodeSymbol selectedState) : Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    FiniteRecognizer.TupleSearch.BoundedHiddenFuelPairSpec
      searcher selected
      CodePrefixRecognizerStageCode
      (fun input inner outer =>
        NestedCodePrefixRecognizerStageCode input inner outer)

theorem codePrefixBoundedNestedPairEnumeratorConstruction_of_hiddenFuel
    {selectedState : Type u}
    {selected : TuringMachine MachineCodeSymbol selectedState}
    (hhidden :
      CodePrefixBoundedNestedHiddenFuelPairEnumeratorConstruction
        selected) :
    CodePrefixBoundedNestedPairEnumeratorConstruction selected := by
  rcases hhidden with ⟨searcherState, searcher, hsearcher⟩
  exact
    ⟨searcherState, searcher,
      FiniteRecognizer.TupleSearch.boundedNestedPairEnumeratorSpec_of_hiddenFuel
        hsearcher⟩

/--
Finite-machine leaf for bounded hidden-fuel generated-pair search, adapted
from the core generated-code convention to the public code-prefix names.
-/
theorem codePrefixBoundedNestedHiddenFuelPairEnumeratorFiniteLeaf
    {selectedState : Type u}
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    CodePrefixBoundedNestedHiddenFuelPairEnumeratorConstruction
      selected := by
  rcases
      FiniteRecognizer.TupleSearch.generatedBoundedHiddenFuelPairFiniteLeaf
        selected with
    ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro input budget
  simpa [FiniteRecognizer.GeneratedCode.stageCode_eq,
    FiniteRecognizer.GeneratedCode.nestedStageCode_eq_codePrefix]
    using hsearcher input budget

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
Concrete finite-table leaf for bounded generated-pair enumeration over indexed
selected recognizers.
-/
theorem codePrefixBoundedNestedPairEnumeratorFinStateFiniteLeaf :
    CodePrefixBoundedNestedPairEnumeratorFinStateConstruction := by
  intro n selected
  rcases
      FiniteRecognizer.TupleSearch.generatedBoundedNestedPairEnumeratorFinStateFiniteLeaf
        n selected with
    ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro input budget
  simpa [FiniteRecognizer.GeneratedCode.stageCode_eq,
    FiniteRecognizer.GeneratedCode.nestedStageCode_eq_codePrefix]
    using hsearcher input budget

/--
Bounded search over generated inner inputs and exact outer fuels for a wrapped
machine.
-/
def CodePrefixBoundedNestedExactFuelSearchConstruction
    {machineState : Type u}
    (M : TuringMachine MachineCodeSymbol machineState) : Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    FiniteRecognizer.TupleSearch.BoundedNestedExactFuelSearchSpec
      searcher M CodePrefixRecognizerStageCode
      CodePrefixRecognizerStageCode

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
    codePrefixBoundedNestedPairEnumeratorConstruction_of_hiddenFuel
      (codePrefixBoundedNestedHiddenFuelPairEnumeratorFiniteLeaf selected)

theorem codePrefixBoundedNestedPairEnumeratorFiniteLeafDecidable
    {selectedState : Type u} [DecidableEq selectedState]
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    CodePrefixBoundedNestedPairEnumeratorConstruction selected := by
  exact
    codePrefixBoundedNestedPairEnumeratorFiniteLeaf selected

/--
Composition of the exact-fuel runner and bounded generated-pair enumerator.
This is the shared helper behind bounded simulator pair loops.
-/
theorem codePrefixBoundedNestedExactFuelSearchFiniteLeaf
    {machineState : Type u}
    (M : TuringMachine MachineCodeSymbol machineState) :
    CodePrefixBoundedNestedExactFuelSearchConstruction M := by
  rcases
      FiniteRecognizer.TupleSearch.generatedBoundedNestedExactFuelSearchFiniteLeaf
        M with
    ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro input budget
  simpa [FiniteRecognizer.GeneratedCode.stageCode_eq]
    using hsearcher input budget

theorem codePrefixBoundedNestedExactFuelSearchFiniteLeafDecidable
    {machineState : Type u} [DecidableEq machineState]
    (M : TuringMachine MachineCodeSymbol machineState) :
    CodePrefixBoundedNestedExactFuelSearchConstruction M := by
  exact codePrefixBoundedNestedExactFuelSearchFiniteLeaf M

end Computability
end FoC
