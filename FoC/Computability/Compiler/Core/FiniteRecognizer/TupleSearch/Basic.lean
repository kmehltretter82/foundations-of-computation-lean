import FoC.Computability.Compiler.Core.FiniteRecognizer.GeneratedCode

set_option doc.verso true

/-!
# Tuple-search contracts for finite recognizers

Semantic contracts for tuple searchers that dovetail an ordinary selected
recognizer through hidden exact fuel.  The public pair budgets bound only the
generated tuple parameters, not the selected recognizer's runtime.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace TupleSearch

universe uSymbol uSearcher uSelected

/--
Unbounded pair search with a hidden selected-machine fuel dimension.
-/
def UnboundedHiddenFuelPairSpec
    {symbol : Type uSymbol}
    {searcherState : Type uSearcher}
    {selectedState : Type uSelected}
    (searcher : TuringMachine symbol searcherState)
    (selected : TuringMachine symbol selectedState)
    (build : Word symbol -> Nat -> Nat -> Word symbol) : Prop :=
  forall input : Word symbol,
    TuringMachine.HaltsOnInput searcher input <->
      exists inner : Nat,
      exists outer : Nat,
      exists selectedFuel : Nat,
        TuringMachine.HaltsOnInputIn selected selectedFuel
          (build input inner outer)

theorem nestedPairEnumeratorSpec_of_hiddenFuel
    {symbol : Type uSymbol}
    {searcherState : Type uSearcher}
    {selectedState : Type uSelected}
    {searcher : TuringMachine symbol searcherState}
    {selected : TuringMachine symbol selectedState}
    {build : Word symbol -> Nat -> Nat -> Word symbol}
    (hsearcher :
      UnboundedHiddenFuelPairSpec searcher selected build) :
    NestedPairEnumeratorSpec searcher selected build := by
  intro input
  rw [hsearcher input]
  constructor
  · intro h
    rcases h with ⟨inner, outer, selectedFuel, hselected⟩
    exact
      ⟨inner, outer,
        TuringMachine.halts_on_input_in_to_halts_on_input
          (n := selectedFuel) hselected⟩
  · intro h
    rcases h with ⟨inner, outer, hselected⟩
    rcases
        (FiniteRecognizer.haltsOnInput_iff_exists_exactFuel
          selected (build input inner outer)).mp hselected with
      ⟨selectedFuel, hselectedFuel⟩
    exact ⟨inner, outer, selectedFuel, hselectedFuel⟩

/--
Bounded pair search with hidden selected-machine fuel.  The public budget
bounds only {lit}`inner` and {lit}`outer`.
-/
def BoundedHiddenFuelPairSpec
    {symbol : Type uSymbol}
    {searcherState : Type uSearcher}
    {selectedState : Type uSelected}
    (searcher : TuringMachine symbol searcherState)
    (selected : TuringMachine symbol selectedState)
    (outerBuild : Word symbol -> Nat -> Word symbol)
    (nestedBuild : Word symbol -> Nat -> Nat -> Word symbol) : Prop :=
  forall input : Word symbol,
  forall budget : Nat,
    TuringMachine.HaltsOnInput searcher (outerBuild input budget) <->
      exists inner : Nat,
      exists outer : Nat,
      exists selectedFuel : Nat,
        inner <= budget /\
          outer <= budget /\
          TuringMachine.HaltsOnInputIn selected selectedFuel
            (nestedBuild input inner outer)

theorem boundedNestedPairEnumeratorSpec_of_hiddenFuel
    {symbol : Type uSymbol}
    {searcherState : Type uSearcher}
    {selectedState : Type uSelected}
    {searcher : TuringMachine symbol searcherState}
    {selected : TuringMachine symbol selectedState}
    {outerBuild : Word symbol -> Nat -> Word symbol}
    {nestedBuild : Word symbol -> Nat -> Nat -> Word symbol}
    (hsearcher :
      BoundedHiddenFuelPairSpec
        searcher selected outerBuild nestedBuild) :
    BoundedNestedPairEnumeratorSpec
      searcher selected outerBuild nestedBuild := by
  intro input budget
  rw [hsearcher input budget]
  constructor
  · intro h
    rcases h with
      ⟨inner, outer, selectedFuel, hinner, houter, hselected⟩
    exact
      ⟨inner, outer, hinner, houter,
        TuringMachine.halts_on_input_in_to_halts_on_input
          (n := selectedFuel) hselected⟩
  · intro h
    rcases h with ⟨inner, outer, hinner, houter, hselected⟩
    rcases
        (FiniteRecognizer.haltsOnInput_iff_exists_exactFuel
          selected (nestedBuild input inner outer)).mp hselected with
      ⟨selectedFuel, hselectedFuel⟩
    exact
      ⟨inner, outer, selectedFuel,
        hinner, houter, hselectedFuel⟩

def GeneratedUnboundedHiddenFuelPairSpec
    {searcherState : Type uSearcher}
    {selectedState : Type uSelected}
    (searcher : TuringMachine MachineCodeSymbol searcherState)
    (selected : TuringMachine MachineCodeSymbol selectedState) : Prop :=
  UnboundedHiddenFuelPairSpec
    searcher selected GeneratedCode.nestedStageCode

def GeneratedBoundedHiddenFuelPairSpec
    {searcherState : Type uSearcher}
    {selectedState : Type uSelected}
    (searcher : TuringMachine MachineCodeSymbol searcherState)
    (selected : TuringMachine MachineCodeSymbol selectedState) : Prop :=
  BoundedHiddenFuelPairSpec
    searcher selected
    GeneratedCode.stageCode GeneratedCode.nestedStageCode

theorem generatedNestedPairEnumeratorSpec_of_hiddenFuel
    {searcherState : Type uSearcher}
    {selectedState : Type uSelected}
    {searcher : TuringMachine MachineCodeSymbol searcherState}
    {selected : TuringMachine MachineCodeSymbol selectedState}
    (hsearcher :
      GeneratedUnboundedHiddenFuelPairSpec searcher selected) :
    NestedPairEnumeratorSpec
      searcher selected GeneratedCode.nestedStageCode :=
  nestedPairEnumeratorSpec_of_hiddenFuel hsearcher

theorem generatedBoundedNestedPairEnumeratorSpec_of_hiddenFuel
    {searcherState : Type uSearcher}
    {selectedState : Type uSelected}
    {searcher : TuringMachine MachineCodeSymbol searcherState}
    {selected : TuringMachine MachineCodeSymbol selectedState}
    (hsearcher :
      GeneratedBoundedHiddenFuelPairSpec searcher selected) :
    BoundedNestedPairEnumeratorSpec
      searcher selected
      GeneratedCode.stageCode GeneratedCode.nestedStageCode :=
  boundedNestedPairEnumeratorSpec_of_hiddenFuel hsearcher

end TupleSearch
end FiniteRecognizer

end Computability
end FoC
