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
Concrete-state generated unbounded and bounded pair search with hidden
selected-machine fuel.
-/
def GeneratedHiddenFuelPairFinStateConstruction : Prop :=
  GeneratedUnboundedHiddenFuelPairFinStateConstruction /\
    GeneratedBoundedHiddenFuelPairFinStateConstruction

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
Generated unbounded pair search with hidden selected-machine fuel for an
arbitrary finite selected recognizer state type.
-/
def GeneratedUnboundedHiddenFuelPairConstruction
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState) : Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    GeneratedUnboundedHiddenFuelPairSpec searcher selected

/--
Generated bounded pair search with hidden selected-machine fuel for an
arbitrary finite selected recognizer state type.
-/
def GeneratedBoundedHiddenFuelPairConstruction
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState) : Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    GeneratedBoundedHiddenFuelPairSpec searcher selected

/--
Generated unbounded and bounded pair search with hidden selected-machine fuel
for an arbitrary finite selected recognizer state type.
-/
def GeneratedHiddenFuelPairConstruction
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState) : Prop :=
  GeneratedUnboundedHiddenFuelPairConstruction selected /\
    GeneratedBoundedHiddenFuelPairConstruction selected

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
Unbounded hidden-fuel generated-pair search is stable under replacing the
selected recognizer by its indexed copy.
-/
theorem generatedUnboundedHiddenFuelPairConstruction_of_indexed
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (hindexed :
      GeneratedUnboundedHiddenFuelPairConstruction
        (TuringMachine.indexed selected)) :
    GeneratedUnboundedHiddenFuelPairConstruction selected := by
  rcases hindexed with ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro input
  constructor
  · intro hhalt
    rcases (hsearcher input).mp hhalt with
      ⟨inner, outer, selectedFuel, hindexedHalt⟩
    exact
      ⟨inner, outer, selectedFuel,
        (TuringMachine.indexed_haltsOnInputIn_iff selected
          selectedFuel
          (GeneratedCode.nestedStageCode input inner outer)).mp
          hindexedHalt⟩
  · intro htarget
    rcases htarget with
      ⟨inner, outer, selectedFuel, hhalt⟩
    exact (hsearcher input).mpr
      ⟨inner, outer, selectedFuel,
        (TuringMachine.indexed_haltsOnInputIn_iff selected
          selectedFuel
          (GeneratedCode.nestedStageCode input inner outer)).mpr
          hhalt⟩

theorem generatedUnboundedHiddenFuelPairConstruction_of_indexedDecidable
    {selectedState : Type uSelected} [DecidableEq selectedState]
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (hindexed :
      GeneratedUnboundedHiddenFuelPairConstruction
        (TuringMachine.indexedDecidable selected)) :
    GeneratedUnboundedHiddenFuelPairConstruction selected := by
  rcases hindexed with ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro input
  constructor
  · intro hhalt
    rcases (hsearcher input).mp hhalt with
      ⟨inner, outer, selectedFuel, hindexedHalt⟩
    exact
      ⟨inner, outer, selectedFuel,
        (TuringMachine.indexedDecidable_haltsOnInputIn_iff selected
          selectedFuel
          (GeneratedCode.nestedStageCode input inner outer)).mp
          hindexedHalt⟩
  · intro htarget
    rcases htarget with
      ⟨inner, outer, selectedFuel, hhalt⟩
    exact (hsearcher input).mpr
      ⟨inner, outer, selectedFuel,
        (TuringMachine.indexedDecidable_haltsOnInputIn_iff selected
          selectedFuel
          (GeneratedCode.nestedStageCode input inner outer)).mpr
          hhalt⟩

/--
Bounded hidden-fuel generated-pair search is stable under replacing the
selected recognizer by its indexed copy.
-/
theorem generatedBoundedHiddenFuelPairConstruction_of_indexed
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (hindexed :
      GeneratedBoundedHiddenFuelPairConstruction
        (TuringMachine.indexed selected)) :
    GeneratedBoundedHiddenFuelPairConstruction selected := by
  rcases hindexed with ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro input budget
  constructor
  · intro hhalt
    rcases (hsearcher input budget).mp hhalt with
      ⟨inner, outer, selectedFuel, hinner, houter, hindexedHalt⟩
    exact
      ⟨inner, outer, selectedFuel, hinner, houter,
        (TuringMachine.indexed_haltsOnInputIn_iff selected
          selectedFuel
          (GeneratedCode.nestedStageCode input inner outer)).mp
          hindexedHalt⟩
  · intro htarget
    rcases htarget with
      ⟨inner, outer, selectedFuel, hinner, houter, hhalt⟩
    exact (hsearcher input budget).mpr
      ⟨inner, outer, selectedFuel, hinner, houter,
        (TuringMachine.indexed_haltsOnInputIn_iff selected
          selectedFuel
          (GeneratedCode.nestedStageCode input inner outer)).mpr
          hhalt⟩

theorem generatedBoundedHiddenFuelPairConstruction_of_indexedDecidable
    {selectedState : Type uSelected} [DecidableEq selectedState]
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (hindexed :
      GeneratedBoundedHiddenFuelPairConstruction
        (TuringMachine.indexedDecidable selected)) :
    GeneratedBoundedHiddenFuelPairConstruction selected := by
  rcases hindexed with ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro input budget
  constructor
  · intro hhalt
    rcases (hsearcher input budget).mp hhalt with
      ⟨inner, outer, selectedFuel, hinner, houter, hindexedHalt⟩
    exact
      ⟨inner, outer, selectedFuel, hinner, houter,
        (TuringMachine.indexedDecidable_haltsOnInputIn_iff selected
          selectedFuel
          (GeneratedCode.nestedStageCode input inner outer)).mp
          hindexedHalt⟩
  · intro htarget
    rcases htarget with
      ⟨inner, outer, selectedFuel, hinner, houter, hhalt⟩
    exact (hsearcher input budget).mpr
      ⟨inner, outer, selectedFuel, hinner, houter,
        (TuringMachine.indexedDecidable_haltsOnInputIn_iff selected
          selectedFuel
          (GeneratedCode.nestedStageCode input inner outer)).mpr
          hhalt⟩

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

theorem generatedUnboundedHiddenFuelPairConstruction_of_finStateConstruction
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (hFin : GeneratedUnboundedHiddenFuelPairFinStateConstruction) :
    GeneratedUnboundedHiddenFuelPairConstruction selected := by
  exact
    generatedUnboundedHiddenFuelPairConstruction_of_indexed selected
      (hFin selected.statesFinite.elems.length
        (TuringMachine.indexed selected))

theorem generatedUnboundedHiddenFuelPairConstruction_of_finStateConstructionDecidable
    {selectedState : Type uSelected} [DecidableEq selectedState]
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (hFin : GeneratedUnboundedHiddenFuelPairFinStateConstruction) :
    GeneratedUnboundedHiddenFuelPairConstruction selected := by
  exact
    generatedUnboundedHiddenFuelPairConstruction_of_indexedDecidable
      selected
      (hFin selected.statesFinite.elems.length
        (TuringMachine.indexedDecidable selected))

theorem generatedBoundedHiddenFuelPairConstruction_of_finStateConstruction
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (hFin : GeneratedBoundedHiddenFuelPairFinStateConstruction) :
    GeneratedBoundedHiddenFuelPairConstruction selected := by
  exact
    generatedBoundedHiddenFuelPairConstruction_of_indexed selected
      (hFin selected.statesFinite.elems.length
        (TuringMachine.indexed selected))

theorem generatedBoundedHiddenFuelPairConstruction_of_finStateConstructionDecidable
    {selectedState : Type uSelected} [DecidableEq selectedState]
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (hFin : GeneratedBoundedHiddenFuelPairFinStateConstruction) :
    GeneratedBoundedHiddenFuelPairConstruction selected := by
  exact
    generatedBoundedHiddenFuelPairConstruction_of_indexedDecidable
      selected
      (hFin selected.statesFinite.elems.length
        (TuringMachine.indexedDecidable selected))

theorem generatedHiddenFuelPairConstruction_of_finStateConstruction
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (hFin : GeneratedHiddenFuelPairFinStateConstruction) :
    GeneratedHiddenFuelPairConstruction selected := by
  exact
    ⟨generatedUnboundedHiddenFuelPairConstruction_of_finStateConstruction
        selected hFin.left,
      generatedBoundedHiddenFuelPairConstruction_of_finStateConstruction
        selected hFin.right⟩

theorem generatedHiddenFuelPairConstruction_of_finStateConstructionDecidable
    {selectedState : Type uSelected} [DecidableEq selectedState]
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (hFin : GeneratedHiddenFuelPairFinStateConstruction) :
    GeneratedHiddenFuelPairConstruction selected := by
  exact
    ⟨generatedUnboundedHiddenFuelPairConstruction_of_finStateConstructionDecidable
        selected hFin.left,
      generatedBoundedHiddenFuelPairConstruction_of_finStateConstructionDecidable
        selected hFin.right⟩

theorem generatedNestedPairEnumeratorFinStateConstruction_of_hiddenFuelComponents
    (hFin : GeneratedHiddenFuelPairFinStateConstruction) :
    GeneratedNestedPairEnumeratorFinStateConstruction := by
  intro n selected
  rcases hFin.left n selected with ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro input
  exact Iff.trans (hsearcher input)
    (generatedNested_exists_hiddenFuel_iff_exists_pair_haltsOnInput
      selected input)

theorem generatedBoundedNestedPairEnumeratorFinStateConstruction_of_hiddenFuelComponents
    (hFin : GeneratedHiddenFuelPairFinStateConstruction) :
    GeneratedBoundedNestedPairEnumeratorFinStateConstruction := by
  intro n selected
  rcases hFin.right n selected with ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro input budget
  exact Iff.trans (hsearcher input budget)
    (generatedNested_exists_bounded_hiddenFuel_iff_exists_bounded_pair_haltsOnInput
      selected input budget)

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

theorem generatedUnboundedHiddenFuelPairFiniteLeaf
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    GeneratedUnboundedHiddenFuelPairConstruction selected := by
  exact
    generatedUnboundedHiddenFuelPairConstruction_of_finStateConstruction
      selected generatedUnboundedHiddenFuelPairFinStateFiniteLeaf

theorem generatedUnboundedHiddenFuelPairFiniteLeafDecidable
    {selectedState : Type uSelected} [DecidableEq selectedState]
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    GeneratedUnboundedHiddenFuelPairConstruction selected := by
  exact
    generatedUnboundedHiddenFuelPairConstruction_of_finStateConstructionDecidable
      selected generatedUnboundedHiddenFuelPairFinStateFiniteLeaf

theorem generatedBoundedHiddenFuelPairFiniteLeaf
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    GeneratedBoundedHiddenFuelPairConstruction selected := by
  exact
    generatedBoundedHiddenFuelPairConstruction_of_finStateConstruction
      selected generatedBoundedHiddenFuelPairFinStateFiniteLeaf

theorem generatedBoundedHiddenFuelPairFiniteLeafDecidable
    {selectedState : Type uSelected} [DecidableEq selectedState]
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    GeneratedBoundedHiddenFuelPairConstruction selected := by
  exact
    generatedBoundedHiddenFuelPairConstruction_of_finStateConstructionDecidable
      selected generatedBoundedHiddenFuelPairFinStateFiniteLeaf

theorem generatedHiddenFuelPairFinStateFiniteLeaves :
    GeneratedHiddenFuelPairFinStateConstruction := by
  exact
    ⟨generatedUnboundedHiddenFuelPairFinStateFiniteLeaf,
      generatedBoundedHiddenFuelPairFinStateFiniteLeaf⟩

theorem generatedHiddenFuelPairFiniteLeaves
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    GeneratedHiddenFuelPairConstruction selected := by
  exact
    generatedHiddenFuelPairConstruction_of_finStateConstruction
      selected generatedHiddenFuelPairFinStateFiniteLeaves

theorem generatedHiddenFuelPairFiniteLeavesDecidable
    {selectedState : Type uSelected} [DecidableEq selectedState]
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    GeneratedHiddenFuelPairConstruction selected := by
  exact
    generatedHiddenFuelPairConstruction_of_finStateConstructionDecidable
      selected generatedHiddenFuelPairFinStateFiniteLeaves

theorem generatedNestedPairEnumeratorFinStateFiniteLeaf :
    GeneratedNestedPairEnumeratorFinStateConstruction := by
  exact
    generatedNestedPairEnumeratorFinStateConstruction_of_hiddenFuelComponents
      generatedHiddenFuelPairFinStateFiniteLeaves

theorem generatedBoundedNestedPairEnumeratorFinStateFiniteLeaf :
    GeneratedBoundedNestedPairEnumeratorFinStateConstruction := by
  exact
    generatedBoundedNestedPairEnumeratorFinStateConstruction_of_hiddenFuelComponents
      generatedHiddenFuelPairFinStateFiniteLeaves

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
