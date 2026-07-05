import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Algebra
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.ExactFuel
import FoC.Computability.Compiler.Core.FiniteRecognizer.Product
import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.StageSearchController.GeneratedCallSearch.PairEnumerator
import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.StageSearchController.GeneratedCallSearch.Product

set_option doc.verso true

/-!
# Generated-call search algebra

Pure existential algebra and final halting-search adapters over the generated
exact-fuel and product runners.
-/

namespace FoC
namespace Computability

open Languages

universe uStage uDescription uSimulator

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
  exact
    FiniteRecognizer.TupleSearch.exists_bounded_pair_iff_exists_pair P

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
  exact
    FiniteRecognizer.TupleSearch.exists_bounded_triple_iff_exists_triple P

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
  exact
    FiniteRecognizer.TupleSearch.exists_pair_haltsOnInputIn_iff_exists_haltsOnInput
      M inputOf

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
    FiniteRecognizer.TupleSearch.exists_bounded_pair_haltsOnInputIn_iff_exists_haltsOnInput
      M inputOf

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
  exact
    FiniteRecognizer.TupleSearch.exists_triple_haltsOnInputIn_iff_exists_pair_haltsOnInput
      M inputOf

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
    FiniteRecognizer.TupleSearch.exists_bounded_triple_haltsOnInputIn_iff_exists_pair_haltsOnInput
      M inputOf

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
  exact
    FiniteRecognizer.TupleSearch.exists_bounded_pair_haltsOnInputIn_iff_exists_bounded_pair_haltsOnInput
      M inputOf budget

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
  exact
    FiniteRecognizer.TupleSearch.exists_pair_haltsOnInputIn_and_iff_haltsOnInput_and
      left right input

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
  rcases
      FiniteRecognizer.TupleSearch.generatedNestedHaltingSearchFiniteLeaf
        M with
    ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro input
  simpa [FiniteRecognizer.GeneratedCode.stageCode_eq]
    using hsearcher input

theorem codePrefixNestedHaltingSearchFiniteLeafDecidable
    {machineState : Type u} [DecidableEq machineState]
    (M : TuringMachine MachineCodeSymbol machineState) :
    CodePrefixNestedHaltingSearchConstruction M := by
  rcases
      FiniteRecognizer.TupleSearch.generatedNestedHaltingSearchFiniteLeafDecidable
        M with
    ⟨searcherState, searcher, hsearcher⟩
  refine ⟨searcherState, searcher, ?_⟩
  intro input
  simpa [FiniteRecognizer.GeneratedCode.stageCode_eq]
    using hsearcher input

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
  rcases FiniteRecognizer.generatedProductHaltingSearchFiniteLeaf
      left right with
    ⟨bothState, both, hboth⟩
  refine ⟨bothState, both, ?_⟩
  intro input
  exact hboth input

theorem codePrefixProductHaltingSearchFiniteLeafDecidable
    {leftState : Type uStage} {rightState : Type uDescription}
    [DecidableEq leftState] [DecidableEq rightState]
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) :
    CodePrefixProductHaltingSearchConstruction left right := by
  rcases FiniteRecognizer.generatedProductHaltingSearchFiniteLeafDecidable
      left right with
    ⟨bothState, both, hboth⟩
  refine ⟨bothState, both, ?_⟩
  intro input
  exact hboth input

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
    FiniteRecognizer.TupleSearch.exists_bounded_pair_haltsOnInputIn_and_iff_haltsOnInput_and
      left right input

end Computability
end FoC
