import FoC.Computability.Compiler.Core.FiniteRecognizer.Product
import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.StageSearchController.GeneratedCallSearch.PairEnumerator

set_option doc.verso true

/-!
# Generated product exact-fuel calls

Product exact-fuel runner and product search interfaces for generated
stage-code calls.
-/

namespace FoC
namespace Computability

open Languages

universe uStage uDescription uSimulator

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
    FiniteRecognizer.ProductExactFuelRunnerSpec selected left right
      (fun input inner outer =>
        NestedCodePrefixRecognizerStageCode input inner outer)

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

theorem codePrefixExactFuelProductRunnerConstruction_of_indexedDecidable
    {leftState : Type uStage} {rightState : Type uDescription}
    [DecidableEq leftState] [DecidableEq rightState]
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState)
    (hindexed :
      CodePrefixExactFuelProductRunnerConstruction
        (TuringMachine.indexedDecidable left)
        (TuringMachine.indexedDecidable right)) :
    CodePrefixExactFuelProductRunnerConstruction left right := by
  rcases hindexed with ⟨selectedState, selected, hselected⟩
  refine ⟨selectedState, selected, ?_⟩
  intro input leftFuel rightFuel
  constructor
  · intro hhalt
    rcases (hselected input leftFuel rightFuel).mp hhalt with
      ⟨hleft, hright⟩
    exact
      ⟨(TuringMachine.indexedDecidable_haltsOnInputIn_iff
          left leftFuel input).mp hleft,
        (TuringMachine.indexedDecidable_haltsOnInputIn_iff
          right rightFuel input).mp hright⟩
  · intro htarget
    rcases htarget with ⟨hleft, hright⟩
    exact (hselected input leftFuel rightFuel).mpr
      ⟨(TuringMachine.indexedDecidable_haltsOnInputIn_iff
          left leftFuel input).mpr hleft,
        (TuringMachine.indexedDecidable_haltsOnInputIn_iff
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

theorem codePrefixExactFuelProductRunnerConstruction_of_finStateConstructionDecidable
    {leftState : Type uStage} {rightState : Type uDescription}
    [DecidableEq leftState] [DecidableEq rightState]
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState)
    (hFin : CodePrefixExactFuelProductRunnerFinStateConstruction) :
    CodePrefixExactFuelProductRunnerConstruction left right := by
  exact
    codePrefixExactFuelProductRunnerConstruction_of_indexedDecidable
      left right
      (hFin left.statesFinite.elems.length
        right.statesFinite.elems.length
        (TuringMachine.indexedDecidable left)
        (TuringMachine.indexedDecidable right))

/--
Remaining concrete finite-table leaf for the product exact-fuel runner over
indexed recognizers.
-/
theorem codePrefixExactFuelProductRunnerFinStateFiniteLeaf :
    CodePrefixExactFuelProductRunnerFinStateConstruction := by
  intro leftN rightN left right
  rcases
      FiniteRecognizer.generatedProductExactFuelRunnerFinStateFiniteLeaf
        leftN rightN left right with
    ⟨selectedState, selected, hselected⟩
  refine ⟨selectedState, selected, ?_⟩
  intro input leftFuel rightFuel
  simpa [FiniteRecognizer.GeneratedCode.nestedStageCode_eq_codePrefix]
    using hselected input leftFuel rightFuel

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

theorem codePrefixExactFuelProductRunnerFiniteLeafDecidable
    {leftState : Type uStage} {rightState : Type uDescription}
    [DecidableEq leftState] [DecidableEq rightState]
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) :
    CodePrefixExactFuelProductRunnerConstruction left right := by
  exact
    codePrefixExactFuelProductRunnerConstruction_of_finStateConstructionDecidable
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

theorem codePrefixExactFuelProductSearchFiniteLeafDecidable
    {leftState : Type uStage} {rightState : Type uDescription}
    [DecidableEq leftState] [DecidableEq rightState]
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) :
    CodePrefixExactFuelProductSearchConstruction left right := by
  rcases codePrefixExactFuelProductRunnerFiniteLeafDecidable
      left right with
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

end Computability
end FoC
