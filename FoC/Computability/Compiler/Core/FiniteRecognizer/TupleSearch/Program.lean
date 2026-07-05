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

end TupleSearch
end FiniteRecognizer

end Computability
end FoC
