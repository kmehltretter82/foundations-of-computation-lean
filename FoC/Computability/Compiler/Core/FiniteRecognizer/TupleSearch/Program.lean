import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Algebra

set_option doc.verso true

/-!
# Generated tuple-search program boundaries

Finite-state construction leaves for generated tuple search.  This module owns
the concrete searcher obligations; downstream Universal/Ranges files should
only adapt these core contracts to their public names.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace TupleSearch

universe uSelected

/--
Concrete-state generated unbounded pair search with hidden selected-machine
fuel.
-/
def GeneratedUnboundedHiddenFuelPairFinStateConstruction : Prop :=
  forall n : Nat,
    forall selected : TuringMachine MachineCodeSymbol (Fin n),
      exists searcherState : Type,
      exists searcher : TuringMachine MachineCodeSymbol searcherState,
        GeneratedUnboundedHiddenFuelPairSpec searcher selected

/--
Concrete-state generated bounded pair search with hidden selected-machine
fuel.
-/
def GeneratedBoundedHiddenFuelPairFinStateConstruction : Prop :=
  forall n : Nat,
    forall selected : TuringMachine MachineCodeSymbol (Fin n),
      exists searcherState : Type,
      exists searcher : TuringMachine MachineCodeSymbol searcherState,
        GeneratedBoundedHiddenFuelPairSpec searcher selected

/--
Concrete-state generated unbounded pair enumerator after hiding selected
machine fuel.
-/
def GeneratedNestedPairEnumeratorFinStateConstruction : Prop :=
  forall n : Nat,
    forall selected : TuringMachine MachineCodeSymbol (Fin n),
      exists searcherState : Type,
      exists searcher : TuringMachine MachineCodeSymbol searcherState,
        NestedPairEnumeratorSpec
          searcher selected GeneratedCode.nestedStageCode

/--
Concrete-state generated bounded pair enumerator after hiding selected machine
fuel.
-/
def GeneratedBoundedNestedPairEnumeratorFinStateConstruction : Prop :=
  forall n : Nat,
    forall selected : TuringMachine MachineCodeSymbol (Fin n),
      exists searcherState : Type,
      exists searcher : TuringMachine MachineCodeSymbol searcherState,
        BoundedNestedPairEnumeratorSpec
          searcher selected
          GeneratedCode.stageCode GeneratedCode.nestedStageCode

/--
Generated unbounded pair enumerator for an arbitrary finite selected
recognizer state type.
-/
def GeneratedNestedPairEnumeratorConstruction
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState) : Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    NestedPairEnumeratorSpec
      searcher selected GeneratedCode.nestedStageCode

/--
Generated bounded pair enumerator for an arbitrary finite selected recognizer
state type.
-/
def GeneratedBoundedNestedPairEnumeratorConstruction
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState) : Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    BoundedNestedPairEnumeratorSpec
      searcher selected
      GeneratedCode.stageCode GeneratedCode.nestedStageCode

/--
Unbounded generated-pair enumeration is stable under replacing the selected
recognizer by its indexed copy.
-/
theorem generatedNestedPairEnumeratorConstruction_of_indexed
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (hindexed :
      GeneratedNestedPairEnumeratorConstruction
        (TuringMachine.indexed selected)) :
    GeneratedNestedPairEnumeratorConstruction selected := by
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
          (GeneratedCode.nestedStageCode input inner outer)).mp
          hindexedHalt⟩
  · intro htarget
    rcases htarget with ⟨inner, outer, hhalt⟩
    exact (hsearcher input).mpr
      ⟨inner, outer,
        (TuringMachine.indexed_haltsOnInput_iff selected
          (GeneratedCode.nestedStageCode input inner outer)).mpr
          hhalt⟩

theorem generatedNestedPairEnumeratorConstruction_of_indexedDecidable
    {selectedState : Type uSelected} [DecidableEq selectedState]
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (hindexed :
      GeneratedNestedPairEnumeratorConstruction
        (TuringMachine.indexedDecidable selected)) :
    GeneratedNestedPairEnumeratorConstruction selected := by
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
          (GeneratedCode.nestedStageCode input inner outer)).mp
          hindexedHalt⟩
  · intro htarget
    rcases htarget with ⟨inner, outer, hhalt⟩
    exact (hsearcher input).mpr
      ⟨inner, outer,
        (TuringMachine.indexedDecidable_haltsOnInput_iff selected
          (GeneratedCode.nestedStageCode input inner outer)).mpr
          hhalt⟩

/--
Bounded generated-pair enumeration is stable under replacing the selected
recognizer by its indexed copy.
-/
theorem generatedBoundedNestedPairEnumeratorConstruction_of_indexed
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (hindexed :
      GeneratedBoundedNestedPairEnumeratorConstruction
        (TuringMachine.indexed selected)) :
    GeneratedBoundedNestedPairEnumeratorConstruction selected := by
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
          (GeneratedCode.nestedStageCode input inner outer)).mp
          hindexedHalt⟩
  · intro htarget
    rcases htarget with ⟨inner, outer, hinner, houter, hhalt⟩
    exact (hsearcher input budget).mpr
      ⟨inner, outer, hinner, houter,
        (TuringMachine.indexed_haltsOnInput_iff selected
          (GeneratedCode.nestedStageCode input inner outer)).mpr
          hhalt⟩

theorem generatedBoundedNestedPairEnumeratorConstruction_of_indexedDecidable
    {selectedState : Type uSelected} [DecidableEq selectedState]
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (hindexed :
      GeneratedBoundedNestedPairEnumeratorConstruction
        (TuringMachine.indexedDecidable selected)) :
    GeneratedBoundedNestedPairEnumeratorConstruction selected := by
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
          (GeneratedCode.nestedStageCode input inner outer)).mp
          hindexedHalt⟩
  · intro htarget
    rcases htarget with ⟨inner, outer, hinner, houter, hhalt⟩
    exact (hsearcher input budget).mpr
      ⟨inner, outer, hinner, houter,
        (TuringMachine.indexedDecidable_haltsOnInput_iff selected
          (GeneratedCode.nestedStageCode input inner outer)).mpr
          hhalt⟩

theorem generatedNestedPairEnumeratorConstruction_of_finStateConstruction
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (hFin : GeneratedNestedPairEnumeratorFinStateConstruction) :
    GeneratedNestedPairEnumeratorConstruction selected := by
  exact
    generatedNestedPairEnumeratorConstruction_of_indexed selected
      (hFin selected.statesFinite.elems.length
        (TuringMachine.indexed selected))

theorem generatedNestedPairEnumeratorConstruction_of_finStateConstructionDecidable
    {selectedState : Type uSelected} [DecidableEq selectedState]
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (hFin : GeneratedNestedPairEnumeratorFinStateConstruction) :
    GeneratedNestedPairEnumeratorConstruction selected := by
  exact
    generatedNestedPairEnumeratorConstruction_of_indexedDecidable selected
      (hFin selected.statesFinite.elems.length
        (TuringMachine.indexedDecidable selected))

theorem generatedBoundedNestedPairEnumeratorConstruction_of_finStateConstruction
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (hFin : GeneratedBoundedNestedPairEnumeratorFinStateConstruction) :
    GeneratedBoundedNestedPairEnumeratorConstruction selected := by
  exact
    generatedBoundedNestedPairEnumeratorConstruction_of_indexed selected
      (hFin selected.statesFinite.elems.length
        (TuringMachine.indexed selected))

theorem generatedBoundedNestedPairEnumeratorConstruction_of_finStateConstructionDecidable
    {selectedState : Type uSelected} [DecidableEq selectedState]
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (hFin : GeneratedBoundedNestedPairEnumeratorFinStateConstruction) :
    GeneratedBoundedNestedPairEnumeratorConstruction selected := by
  exact
    generatedBoundedNestedPairEnumeratorConstruction_of_indexedDecidable
      selected
      (hFin selected.statesFinite.elems.length
        (TuringMachine.indexedDecidable selected))

/--
Remaining concrete finite-table leaf for generated unbounded pair search.  It
must enumerate {lit}`(inner, outer, selectedFuel)`, rebuild the nested generated
call, and run the selected recognizer for exactly {lit}`selectedFuel`.
-/
theorem generatedUnboundedHiddenFuelPairFinStateFiniteLeaf :
    GeneratedUnboundedHiddenFuelPairFinStateConstruction := by
  intro n selected
  cases n with
  | zero =>
      exact False.elim (Fin.elim0 selected.start)
  | succ _ =>
      sorry

/--
Remaining concrete finite-table leaf for generated bounded pair search.  It
must parse the public budget, enumerate bounded {lit}`(inner, outer)` pairs,
and dovetail the selected recognizer over hidden exact fuel.
-/
theorem generatedBoundedHiddenFuelPairFinStateFiniteLeaf :
    GeneratedBoundedHiddenFuelPairFinStateConstruction := by
  intro n selected
  cases n with
  | zero =>
      exact False.elim (Fin.elim0 selected.start)
  | succ _ =>
      sorry

theorem generatedNestedPairEnumeratorFinStateFiniteLeaf :
    GeneratedNestedPairEnumeratorFinStateConstruction := by
  intro n selected
  rcases generatedUnboundedHiddenFuelPairFinStateFiniteLeaf n selected with
    ⟨searcherState, searcher, hsearcher⟩
  exact
    ⟨searcherState, searcher,
      generatedNestedPairEnumeratorSpec_of_hiddenFuel hsearcher⟩

theorem generatedBoundedNestedPairEnumeratorFinStateFiniteLeaf :
    GeneratedBoundedNestedPairEnumeratorFinStateConstruction := by
  intro n selected
  rcases generatedBoundedHiddenFuelPairFinStateFiniteLeaf n selected with
    ⟨searcherState, searcher, hsearcher⟩
  exact
    ⟨searcherState, searcher,
      generatedBoundedNestedPairEnumeratorSpec_of_hiddenFuel hsearcher⟩

theorem generatedNestedPairEnumeratorFiniteLeaf
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    GeneratedNestedPairEnumeratorConstruction selected := by
  exact
    generatedNestedPairEnumeratorConstruction_of_finStateConstruction
      selected generatedNestedPairEnumeratorFinStateFiniteLeaf

theorem generatedNestedPairEnumeratorFiniteLeafDecidable
    {selectedState : Type uSelected} [DecidableEq selectedState]
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    GeneratedNestedPairEnumeratorConstruction selected := by
  exact
    generatedNestedPairEnumeratorConstruction_of_finStateConstructionDecidable
      selected generatedNestedPairEnumeratorFinStateFiniteLeaf

theorem generatedBoundedNestedPairEnumeratorFiniteLeaf
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    GeneratedBoundedNestedPairEnumeratorConstruction selected := by
  exact
    generatedBoundedNestedPairEnumeratorConstruction_of_finStateConstruction
      selected generatedBoundedNestedPairEnumeratorFinStateFiniteLeaf

theorem generatedBoundedNestedPairEnumeratorFiniteLeafDecidable
    {selectedState : Type uSelected} [DecidableEq selectedState]
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    GeneratedBoundedNestedPairEnumeratorConstruction selected := by
  exact
    generatedBoundedNestedPairEnumeratorConstruction_of_finStateConstructionDecidable
      selected generatedBoundedNestedPairEnumeratorFinStateFiniteLeaf

end TupleSearch
end FiniteRecognizer

end Computability
end FoC
