import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Program

set_option doc.verso true

/-!
# Generated product exact-fuel program boundary

Concrete finite-state construction boundary for recognizer-product exact-fuel
calls.  The public Universal/Ranges product wrapper adapts this core generated
contract to the historical code-prefix names.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer

universe uLeft uRight

/--
Concrete-state generated exact-fuel product runner target.
-/
def GeneratedProductExactFuelRunnerFinStateConstruction : Prop :=
  forall leftN rightN : Nat,
    forall left : TuringMachine MachineCodeSymbol (Fin leftN),
    forall right : TuringMachine MachineCodeSymbol (Fin rightN),
      exists selectedState : Type,
      exists selected : TuringMachine MachineCodeSymbol selectedState,
        ProductExactFuelRunnerSpec
          selected left right GeneratedCode.nestedStageCode

/--
Remaining concrete finite-table leaf for generated product exact-fuel calls.
It must preserve the raw input while checking the left recognizer for the
outer generated fuel and the right recognizer for the inner generated fuel.
-/
theorem generatedProductExactFuelRunnerFinStateFiniteLeaf :
    GeneratedProductExactFuelRunnerFinStateConstruction := by
  intro leftN rightN left right
  cases leftN with
  | zero =>
      exact False.elim (Fin.elim0 left.start)
  | succ _ =>
      cases rightN with
      | zero =>
          exact False.elim (Fin.elim0 right.start)
      | succ _ =>
          sorry

/--
Generated product search over exact left/right fuel witnesses for a preserved
input.
-/
def GeneratedProductExactFuelSearchConstruction
    {leftState : Type uLeft} {rightState : Type uRight}
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
Concrete-state generated product search target.
-/
def GeneratedProductExactFuelSearchFinStateConstruction : Prop :=
  forall leftN rightN : Nat,
    forall left : TuringMachine MachineCodeSymbol (Fin leftN),
    forall right : TuringMachine MachineCodeSymbol (Fin rightN),
      GeneratedProductExactFuelSearchConstruction left right

theorem generatedProductExactFuelSearchConstruction_of_indexed
    {leftState : Type uLeft} {rightState : Type uRight}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState)
    (hindexed :
      GeneratedProductExactFuelSearchConstruction
        (TuringMachine.indexed left) (TuringMachine.indexed right)) :
    GeneratedProductExactFuelSearchConstruction left right := by
  rcases hindexed with ⟨bothState, both, hboth⟩
  refine ⟨bothState, both, ?_⟩
  intro input
  constructor
  · intro hhalt
    rcases (hboth input).mp hhalt with
      ⟨leftFuel, rightFuel, hleft, hright⟩
    exact
      ⟨leftFuel, rightFuel,
        (TuringMachine.indexed_haltsOnInputIn_iff
          left leftFuel input).mp hleft,
        (TuringMachine.indexed_haltsOnInputIn_iff
          right rightFuel input).mp hright⟩
  · intro htarget
    rcases htarget with ⟨leftFuel, rightFuel, hleft, hright⟩
    exact (hboth input).mpr
      ⟨leftFuel, rightFuel,
        (TuringMachine.indexed_haltsOnInputIn_iff
          left leftFuel input).mpr hleft,
        (TuringMachine.indexed_haltsOnInputIn_iff
          right rightFuel input).mpr hright⟩

theorem generatedProductExactFuelSearchConstruction_of_indexedDecidable
    {leftState : Type uLeft} {rightState : Type uRight}
    [DecidableEq leftState] [DecidableEq rightState]
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState)
    (hindexed :
      GeneratedProductExactFuelSearchConstruction
        (TuringMachine.indexedDecidable left)
        (TuringMachine.indexedDecidable right)) :
    GeneratedProductExactFuelSearchConstruction left right := by
  rcases hindexed with ⟨bothState, both, hboth⟩
  refine ⟨bothState, both, ?_⟩
  intro input
  constructor
  · intro hhalt
    rcases (hboth input).mp hhalt with
      ⟨leftFuel, rightFuel, hleft, hright⟩
    exact
      ⟨leftFuel, rightFuel,
        (TuringMachine.indexedDecidable_haltsOnInputIn_iff
          left leftFuel input).mp hleft,
        (TuringMachine.indexedDecidable_haltsOnInputIn_iff
          right rightFuel input).mp hright⟩
  · intro htarget
    rcases htarget with ⟨leftFuel, rightFuel, hleft, hright⟩
    exact (hboth input).mpr
      ⟨leftFuel, rightFuel,
        (TuringMachine.indexedDecidable_haltsOnInputIn_iff
          left leftFuel input).mpr hleft,
        (TuringMachine.indexedDecidable_haltsOnInputIn_iff
          right rightFuel input).mpr hright⟩

theorem generatedProductExactFuelSearchConstruction_of_finStateConstruction
    {leftState : Type uLeft} {rightState : Type uRight}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState)
    (hFin : GeneratedProductExactFuelSearchFinStateConstruction) :
    GeneratedProductExactFuelSearchConstruction left right := by
  exact
    generatedProductExactFuelSearchConstruction_of_indexed left right
      (hFin left.statesFinite.elems.length
        right.statesFinite.elems.length
        (TuringMachine.indexed left) (TuringMachine.indexed right))

theorem generatedProductExactFuelSearchConstruction_of_finStateConstructionDecidable
    {leftState : Type uLeft} {rightState : Type uRight}
    [DecidableEq leftState] [DecidableEq rightState]
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState)
    (hFin : GeneratedProductExactFuelSearchFinStateConstruction) :
    GeneratedProductExactFuelSearchConstruction left right := by
  exact
    generatedProductExactFuelSearchConstruction_of_indexedDecidable
      left right
      (hFin left.statesFinite.elems.length
        right.statesFinite.elems.length
        (TuringMachine.indexedDecidable left)
        (TuringMachine.indexedDecidable right))

theorem generatedProductExactFuelSearchFinStateFiniteLeaf :
    GeneratedProductExactFuelSearchFinStateConstruction := by
  intro leftN rightN left right
  rcases
      generatedProductExactFuelRunnerFinStateFiniteLeaf
        leftN rightN left right with
    ⟨selectedState, selected, hselected⟩
  rcases
      TupleSearch.generatedNestedPairEnumeratorFiniteLeaf selected with
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

theorem generatedProductExactFuelSearchFiniteLeaf
    {leftState : Type uLeft} {rightState : Type uRight}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) :
    GeneratedProductExactFuelSearchConstruction left right := by
  exact
    generatedProductExactFuelSearchConstruction_of_finStateConstruction
      left right generatedProductExactFuelSearchFinStateFiniteLeaf

theorem generatedProductExactFuelSearchFiniteLeafDecidable
    {leftState : Type uLeft} {rightState : Type uRight}
    [DecidableEq leftState] [DecidableEq rightState]
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) :
    GeneratedProductExactFuelSearchConstruction left right := by
  exact
    generatedProductExactFuelSearchConstruction_of_finStateConstructionDecidable
      left right generatedProductExactFuelSearchFinStateFiniteLeaf

end FiniteRecognizer

end Computability
end FoC
