import FoC.Computability.Compiler.Core.FiniteRecognizer.Product

set_option doc.verso true

/-!
# Product exact-fuel route contracts

This module packages the generated product exact-fuel runner around the
ordinary-halting finite-table leaf in
{module}`FoC.Computability.Compiler.Core.FiniteRecognizer.Product`. The
contracts record the semantic nested-stage shape, runner bridge, and
hidden-fuel search bridge used by later tuple-search and controller scaffolds.
Literal exact-empty-output routes are intentionally absent because their
stored input context cannot shrink.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer

universe uLeft uRight

/-!
## Nested-stage semantic shape
-/

structure GeneratedProductNestedStageShape
    {leftN rightN : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftN))
    (right : TuringMachine MachineCodeSymbol (Fin rightN))
    (input : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) : Prop where
  outerDecode :
    MachineDescription.decodeNat
        (GeneratedCode.nestedStageCode input rightFuel leftFuel) =
      some (leftFuel, GeneratedCode.stageCode input rightFuel)
  innerDecode :
    MachineDescription.decodeNat
        (GeneratedCode.stageCode input rightFuel) =
      some (rightFuel, input)
  runNestedStageCodeIff :
    generatedProductExactFuelRun left right
        (GeneratedCode.nestedStageCode input rightFuel leftFuel) =
        some ([] : Word MachineCodeSymbol) <->
      TuringMachine.HaltsOnInputIn left leftFuel input ∧
        TuringMachine.HaltsOnInputIn right rightFuel input
  runEqSomeIff :
    forall tokens output : Word MachineCodeSymbol,
      generatedProductExactFuelRun left right tokens = some output <->
        exists decodedInput : Word MachineCodeSymbol,
        exists decodedLeftFuel : Nat,
        exists decodedRightFuel : Nat,
          tokens =
              GeneratedCode.nestedStageCode
                decodedInput decodedRightFuel decodedLeftFuel /\
            output = ([] : Word MachineCodeSymbol) /\
            TuringMachine.HaltsOnInputIn
                left decodedLeftFuel decodedInput ∧
              TuringMachine.HaltsOnInputIn
                right decodedRightFuel decodedInput
  outputEmptyOfEqSome :
    forall tokens output : Word MachineCodeSymbol,
      generatedProductExactFuelRun left right tokens = some output ->
        output = ([] : Word MachineCodeSymbol)
  stageCodeLeftEqOfDecode :
    forall tokens inner : Word MachineCodeSymbol,
    forall decodedLeftFuel : Nat,
      MachineDescription.decodeNat tokens =
          some (decodedLeftFuel, inner) ->
      forall decodedRightFuel : Nat,
        MachineDescription.decodeNat inner =
            some (decodedRightFuel, input) ->
          tokens =
            GeneratedCode.nestedStageCode
              input decodedRightFuel decodedLeftFuel
  targetConjunctionLeft :
      TuringMachine.HaltsOnInputIn left leftFuel input ∧
        TuringMachine.HaltsOnInputIn right rightFuel input ->
      TuringMachine.HaltsOnInputIn left leftFuel input
  targetConjunctionRight :
      TuringMachine.HaltsOnInputIn left leftFuel input ∧
        TuringMachine.HaltsOnInputIn right rightFuel input ->
      TuringMachine.HaltsOnInputIn right rightFuel input

theorem generatedProductNestedStageShape
    {leftN rightN : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftN))
    (right : TuringMachine MachineCodeSymbol (Fin rightN))
    (input : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) :
    GeneratedProductNestedStageShape
      left right input leftFuel rightFuel :=
  { outerDecode :=
      GeneratedCode.nestedStageCode_decodeNat_outer
        input rightFuel leftFuel
    innerDecode :=
      GeneratedCode.nestedStageCode_decodeNat_inner
        input rightFuel
    runNestedStageCodeIff :=
      generatedProductExactFuelRun_nestedStageCode_eq_some_iff
        left right input leftFuel rightFuel
    runEqSomeIff :=
      generatedProductExactFuelRun_eq_some_iff left right
    outputEmptyOfEqSome := by
      intro tokens output hrun
      exact
        generatedProductExactFuelRun_eq_some_empty_of_eq_some
          left right hrun
    stageCodeLeftEqOfDecode := by
      intro tokens inner decodedLeftFuel houter decodedRightFuel hinner
      exact
        GeneratedCode.nestedStageCode_eq_of_decodeNat_outer_inner
          houter hinner
    targetConjunctionLeft := fun htarget => htarget.left
    targetConjunctionRight := fun htarget => htarget.right }

theorem generatedProductExactFuelRun_nestedStageCode_left
    {leftN rightN : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftN))
    (right : TuringMachine MachineCodeSymbol (Fin rightN))
    (input : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat)
    (hrun :
      generatedProductExactFuelRun left right
        (GeneratedCode.nestedStageCode input rightFuel leftFuel) =
        some ([] : Word MachineCodeSymbol)) :
    TuringMachine.HaltsOnInputIn left leftFuel input :=
  ((generatedProductNestedStageShape left right input leftFuel rightFuel).runNestedStageCodeIff.mp
    hrun).left

theorem generatedProductExactFuelRun_nestedStageCode_right
    {leftN rightN : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftN))
    (right : TuringMachine MachineCodeSymbol (Fin rightN))
    (input : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat)
    (hrun :
      generatedProductExactFuelRun left right
        (GeneratedCode.nestedStageCode input rightFuel leftFuel) =
        some ([] : Word MachineCodeSymbol)) :
    TuringMachine.HaltsOnInputIn right rightFuel input :=
  ((generatedProductNestedStageShape left right input leftFuel rightFuel).runNestedStageCodeIff.mp
    hrun).right

theorem generatedProductExactFuelRun_nestedStageCode_of_pair
    {leftN rightN : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftN))
    (right : TuringMachine MachineCodeSymbol (Fin rightN))
    (input : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat)
    (hleft : TuringMachine.HaltsOnInputIn left leftFuel input)
    (hright : TuringMachine.HaltsOnInputIn right rightFuel input) :
    generatedProductExactFuelRun left right
        (GeneratedCode.nestedStageCode input rightFuel leftFuel) =
      some ([] : Word MachineCodeSymbol) :=
  (generatedProductExactFuelRun_nestedStageCode_eq_some_iff
    left right input leftFuel rightFuel).mpr
    ⟨hleft, hright⟩

/-!
## Fin-state product route
-/

structure GeneratedProductFiniteRoute : Prop where
  finStateRunner :
    GeneratedProductExactFuelRunnerFinStateConstruction
  finStateSearch :
    GeneratedProductExactFuelSearchFinStateConstruction
  runnerConstruction :
    forall leftN rightN : Nat,
    forall left : TuringMachine MachineCodeSymbol (Fin leftN),
    forall right : TuringMachine MachineCodeSymbol (Fin rightN),
      GeneratedProductExactFuelRunnerConstruction left right
  searchConstruction :
    forall leftN rightN : Nat,
    forall left : TuringMachine MachineCodeSymbol (Fin leftN),
    forall right : TuringMachine MachineCodeSymbol (Fin rightN),
      GeneratedProductExactFuelSearchConstruction left right
  nestedShape :
    forall leftN rightN : Nat,
    forall left : TuringMachine MachineCodeSymbol (Fin leftN),
    forall right : TuringMachine MachineCodeSymbol (Fin rightN),
    forall input : Word MachineCodeSymbol,
    forall leftFuel rightFuel : Nat,
      GeneratedProductNestedStageShape
        left right input leftFuel rightFuel

def GeneratedProductFiniteRouteConstruction : Prop :=
  GeneratedProductFiniteRoute

theorem generatedProductFiniteRoute_of_runner
    (hrunner : GeneratedProductExactFuelRunnerFinStateConstruction) :
    GeneratedProductFiniteRoute := by
  let hsearch :
      GeneratedProductExactFuelSearchFinStateConstruction :=
    generatedProductExactFuelSearchFinStateFiniteLeaf
  exact
    { finStateRunner := hrunner
      finStateSearch := hsearch
      runnerConstruction := by
        intro leftN rightN left right
        exact hrunner leftN rightN left right
      searchConstruction := by
        intro leftN rightN left right
        exact hsearch leftN rightN left right
      nestedShape := by
        intro leftN rightN left right input leftFuel rightFuel
        exact
          generatedProductNestedStageShape
            left right input leftFuel rightFuel }

theorem generatedProductFiniteRoute_finiteLeaf :
    GeneratedProductFiniteRoute :=
  generatedProductFiniteRoute_of_runner
    generatedProductExactFuelRunnerFinStateFiniteLeaf

theorem generatedProductFiniteRouteConstruction_finiteLeaf :
    GeneratedProductFiniteRouteConstruction :=
  generatedProductFiniteRoute_finiteLeaf

/-!
## Per-machine product route projections
-/

structure GeneratedProductMachineRoute
    {leftN rightN : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftN))
    (right : TuringMachine MachineCodeSymbol (Fin rightN)) :
    Prop where
  runner :
    GeneratedProductExactFuelRunnerConstruction left right
  search :
    GeneratedProductExactFuelSearchConstruction left right
  nestedShape :
    forall input : Word MachineCodeSymbol,
    forall leftFuel rightFuel : Nat,
      GeneratedProductNestedStageShape
        left right input leftFuel rightFuel
  acceptsNestedStageIff :
    forall selectedState : Type,
    forall selected : TuringMachine MachineCodeSymbol selectedState,
      ProductExactFuelRunnerSpec
        selected left right GeneratedCode.nestedStageCode ->
      forall input : Word MachineCodeSymbol,
      forall leftFuel rightFuel : Nat,
        TuringMachine.HaltsOnInput selected
            (GeneratedCode.nestedStageCode input rightFuel leftFuel) <->
          TuringMachine.HaltsOnInputIn left leftFuel input ∧
            TuringMachine.HaltsOnInputIn right rightFuel input

theorem GeneratedProductFiniteRoute.machineRoute
    (hroute : GeneratedProductFiniteRoute)
    {leftN rightN : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftN))
    (right : TuringMachine MachineCodeSymbol (Fin rightN)) :
    GeneratedProductMachineRoute left right :=
  { runner :=
      hroute.runnerConstruction leftN rightN left right
    search :=
      hroute.searchConstruction leftN rightN left right
    nestedShape :=
      hroute.nestedShape leftN rightN left right
    acceptsNestedStageIff := by
      intro selectedState selected hselected input leftFuel rightFuel
      exact hselected input leftFuel rightFuel }

theorem generatedProductMachineRoute_finiteLeaf
    {leftN rightN : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftN))
    (right : TuringMachine MachineCodeSymbol (Fin rightN)) :
    GeneratedProductMachineRoute left right :=
  GeneratedProductFiniteRoute.machineRoute
    generatedProductFiniteRoute_finiteLeaf left right

theorem GeneratedProductFiniteRoute.runnerConstruction_arbitrary
    (hroute : GeneratedProductFiniteRoute)
    {leftState : Type uLeft} {rightState : Type uRight}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) :
    GeneratedProductExactFuelRunnerConstruction left right :=
  generatedProductExactFuelRunnerConstruction_of_finStateConstruction
    left right hroute.finStateRunner

theorem GeneratedProductFiniteRoute.runnerConstruction_arbitraryDecidable
    (hroute : GeneratedProductFiniteRoute)
    {leftState : Type uLeft} {rightState : Type uRight}
    [DecidableEq leftState] [DecidableEq rightState]
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) :
    GeneratedProductExactFuelRunnerConstruction left right :=
  generatedProductExactFuelRunnerConstruction_of_finStateConstructionDecidable
    left right hroute.finStateRunner

theorem GeneratedProductFiniteRoute.searchConstruction_arbitrary
    (hroute : GeneratedProductFiniteRoute)
    {leftState : Type uLeft} {rightState : Type uRight}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) :
    GeneratedProductExactFuelSearchConstruction left right :=
  generatedProductExactFuelSearchConstruction_of_finStateConstruction
    left right hroute.finStateSearch

theorem GeneratedProductFiniteRoute.searchConstruction_arbitraryDecidable
    (hroute : GeneratedProductFiniteRoute)
    {leftState : Type uLeft} {rightState : Type uRight}
    [DecidableEq leftState] [DecidableEq rightState]
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) :
    GeneratedProductExactFuelSearchConstruction left right :=
  generatedProductExactFuelSearchConstruction_of_finStateConstructionDecidable
    left right hroute.finStateSearch

theorem generatedProductExactFuelRunnerRoute_finiteLeaf
    {leftState : Type uLeft} {rightState : Type uRight}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) :
    GeneratedProductExactFuelRunnerConstruction left right :=
  generatedProductFiniteRoute_finiteLeaf.runnerConstruction_arbitrary
    left right

theorem generatedProductExactFuelRunnerRouteDecidable_finiteLeaf
    {leftState : Type uLeft} {rightState : Type uRight}
    [DecidableEq leftState] [DecidableEq rightState]
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) :
    GeneratedProductExactFuelRunnerConstruction left right :=
  generatedProductFiniteRoute_finiteLeaf.runnerConstruction_arbitraryDecidable
    left right

theorem generatedProductExactFuelSearchRoute_finiteLeaf
    {leftState : Type uLeft} {rightState : Type uRight}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) :
    GeneratedProductExactFuelSearchConstruction left right :=
  generatedProductFiniteRoute_finiteLeaf.searchConstruction_arbitrary
    left right

theorem generatedProductExactFuelSearchRouteDecidable_finiteLeaf
    {leftState : Type uLeft} {rightState : Type uRight}
    [DecidableEq leftState] [DecidableEq rightState]
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) :
    GeneratedProductExactFuelSearchConstruction left right :=
  generatedProductFiniteRoute_finiteLeaf.searchConstruction_arbitraryDecidable
    left right

/-!
## Search route surface
-/

structure GeneratedProductSearchRoute
    {leftState : Type uLeft} {rightState : Type uRight}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState)
    (bothState : Type)
    (both : TuringMachine MachineCodeSymbol bothState) : Prop where
  exactFuelSearch :
    forall input : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput both input <->
        exists leftFuel : Nat,
        exists rightFuel : Nat,
          TuringMachine.HaltsOnInputIn left leftFuel input ∧
            TuringMachine.HaltsOnInputIn right rightFuel input
  leftRightHaltingOfSearch :
    forall input : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput both input ->
        exists leftFuel : Nat,
        exists rightFuel : Nat,
          TuringMachine.HaltsOnInputIn left leftFuel input ∧
            TuringMachine.HaltsOnInputIn right rightFuel input
  searchOfLeftRightFuel :
    forall input : Word MachineCodeSymbol,
    forall leftFuel rightFuel : Nat,
      TuringMachine.HaltsOnInputIn left leftFuel input ->
      TuringMachine.HaltsOnInputIn right rightFuel input ->
        TuringMachine.HaltsOnInput both input

def GeneratedProductSearchRouteConstruction
    {leftState : Type uLeft} {rightState : Type uRight}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) : Prop :=
  exists bothState : Type,
  exists both : TuringMachine MachineCodeSymbol bothState,
    GeneratedProductSearchRoute left right bothState both

theorem generatedProductSearchRoute_of_construction
    {leftState : Type uLeft} {rightState : Type uRight}
    {left : TuringMachine MachineCodeSymbol leftState}
    {right : TuringMachine MachineCodeSymbol rightState}
    (hsearch :
      GeneratedProductExactFuelSearchConstruction left right) :
    GeneratedProductSearchRouteConstruction left right := by
  rcases hsearch with ⟨bothState, both, hboth⟩
  refine ⟨bothState, both, ?_⟩
  exact
    { exactFuelSearch := hboth
      leftRightHaltingOfSearch := by
        intro input hhalt
        exact (hboth input).mp hhalt
      searchOfLeftRightFuel := by
        intro input leftFuel rightFuel hleft hright
        exact (hboth input).mpr
          ⟨leftFuel, rightFuel, hleft, hright⟩ }

theorem GeneratedProductFiniteRoute.searchRoute
    (hroute : GeneratedProductFiniteRoute)
    {leftState : Type uLeft} {rightState : Type uRight}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) :
    GeneratedProductSearchRouteConstruction left right :=
  generatedProductSearchRoute_of_construction
    (hroute.searchConstruction_arbitrary left right)

theorem GeneratedProductFiniteRoute.searchRouteDecidable
    (hroute : GeneratedProductFiniteRoute)
    {leftState : Type uLeft} {rightState : Type uRight}
    [DecidableEq leftState] [DecidableEq rightState]
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) :
    GeneratedProductSearchRouteConstruction left right :=
  generatedProductSearchRoute_of_construction
    (hroute.searchConstruction_arbitraryDecidable left right)

theorem generatedProductSearchRoute_finiteLeaf
    {leftState : Type uLeft} {rightState : Type uRight}
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) :
    GeneratedProductSearchRouteConstruction left right :=
  generatedProductFiniteRoute_finiteLeaf.searchRoute left right

theorem generatedProductSearchRouteDecidable_finiteLeaf
    {leftState : Type uLeft} {rightState : Type uRight}
    [DecidableEq leftState] [DecidableEq rightState]
    (left : TuringMachine MachineCodeSymbol leftState)
    (right : TuringMachine MachineCodeSymbol rightState) :
    GeneratedProductSearchRouteConstruction left right :=
  generatedProductFiniteRoute_finiteLeaf.searchRouteDecidable left right

end FiniteRecognizer

end Computability
end FoC
