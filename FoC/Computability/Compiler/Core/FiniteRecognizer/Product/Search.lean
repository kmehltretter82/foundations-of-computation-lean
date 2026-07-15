import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.Runner
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Program

set_option doc.verso true

/-!
# Generated product search

Tuple enumeration and unbounded-search adapters layered above the exact-fuel
product runner.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer

universe uLeft uRight

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
Generated product search for recognizer intersection, hiding both exact fuel
witnesses behind ordinary halting.
-/
def GeneratedProductHaltingSearchConstruction
    {leftState : Type uLeft} {rightState : Type uRight}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) : Prop :=
  exists bothState : Type,
  exists both : TuringMachine MachineCodeSymbol bothState,
    forall input : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput both input <->
        TuringMachine.HaltsOnInput left input ∧
          TuringMachine.HaltsOnInput right input

/-- Concrete-state generated product search target. -/
def GeneratedProductExactFuelSearchFinStateConstruction : Prop :=
  forall leftN rightN : Nat,
    forall left : TuringMachine MachineCodeSymbol (Fin leftN),
    forall right : TuringMachine MachineCodeSymbol (Fin rightN),
      GeneratedProductExactFuelSearchConstruction left right

theorem generatedProductExactFuelSearchConstruction_of_runner
    {leftState : Type uLeft} {rightState : Type uRight}
    {left : TuringMachine MachineCodeSymbol leftState}
    {right : TuringMachine MachineCodeSymbol rightState}
    (hrunner : GeneratedProductExactFuelRunnerConstruction left right) :
    GeneratedProductExactFuelSearchConstruction left right := by
  rcases hrunner with ⟨selectedState, selected, hselected⟩
  rcases TupleSearch.generatedNestedPairEnumeratorFiniteLeaf selected with
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
  exact generatedProductExactFuelSearchConstruction_of_indexed left right
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
  exact generatedProductExactFuelSearchConstruction_of_indexedDecidable
    left right
    (hFin left.statesFinite.elems.length
      right.statesFinite.elems.length
      (TuringMachine.indexedDecidable left)
      (TuringMachine.indexedDecidable right))

theorem generatedProductExactFuelSearchFinStateFiniteLeaf :
    GeneratedProductExactFuelSearchFinStateConstruction := by
  intro leftN rightN left right
  exact generatedProductExactFuelSearchConstruction_of_runner
    (generatedProductExactFuelRunnerFinStateFiniteLeaf
      leftN rightN left right)

theorem generatedProductExactFuelSearchFiniteLeaf
    {leftState : Type uLeft} {rightState : Type uRight}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) :
    GeneratedProductExactFuelSearchConstruction left right := by
  exact generatedProductExactFuelSearchConstruction_of_runner
    (generatedProductExactFuelRunnerFiniteLeaf left right)

theorem generatedProductExactFuelSearchFiniteLeafDecidable
    {leftState : Type uLeft} {rightState : Type uRight}
    [DecidableEq leftState] [DecidableEq rightState]
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) :
    GeneratedProductExactFuelSearchConstruction left right := by
  exact generatedProductExactFuelSearchConstruction_of_runner
    (generatedProductExactFuelRunnerFiniteLeafDecidable left right)

theorem generatedProductHaltingSearchFiniteLeaf
    {leftState : Type uLeft} {rightState : Type uRight}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) :
    GeneratedProductHaltingSearchConstruction left right := by
  rcases generatedProductExactFuelSearchFiniteLeaf left right with
    ⟨bothState, both, hboth⟩
  refine ⟨bothState, both, ?_⟩
  intro input
  exact Iff.trans (hboth input)
    (TupleSearch.exists_pair_haltsOnInputIn_and_iff_haltsOnInput_and
      left right input)

theorem generatedProductHaltingSearchFiniteLeafDecidable
    {leftState : Type uLeft} {rightState : Type uRight}
    [DecidableEq leftState] [DecidableEq rightState]
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) :
    GeneratedProductHaltingSearchConstruction left right := by
  rcases generatedProductExactFuelSearchFiniteLeafDecidable left right with
    ⟨bothState, both, hboth⟩
  refine ⟨bothState, both, ?_⟩
  intro input
  exact Iff.trans (hboth input)
    (TupleSearch.exists_pair_haltsOnInputIn_and_iff_haltsOnInput_and
      left right input)

end FiniteRecognizer

end Computability
end FoC
