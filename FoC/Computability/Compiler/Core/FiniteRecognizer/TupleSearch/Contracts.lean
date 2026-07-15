import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.ExactFuel

set_option doc.verso true

/-!
# Generated tuple-search route contracts

This module packages the generated tuple-search route around the remaining
unbounded and bounded hidden-fuel finite-table leaves in
{module}`FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Program`.
The route records the precise separation between public tuple parameters
{lit}`inner` and {lit}`outer` and the hidden selected-machine exact fuel, then
exposes the derived ordinary enumerator, generated exact-fuel, and generated
halting search surfaces used by later product and controller code.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace TupleSearch

universe uSelected uMachine

/-!
## Hidden-fuel semantic shape
-/

structure GeneratedHiddenFuelPairShape
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (input : Word MachineCodeSymbol)
    (budget : Nat) : Prop where
  unboundedHiddenIffOrdinary :
    (exists inner : Nat,
      exists outer : Nat,
      exists selectedFuel : Nat,
        TuringMachine.HaltsOnInputIn selected selectedFuel
          (GeneratedCode.nestedStageCode input inner outer)) <->
      exists inner : Nat,
      exists outer : Nat,
        TuringMachine.HaltsOnInput selected
          (GeneratedCode.nestedStageCode input inner outer)
  boundedHiddenIffOrdinary :
    (exists inner : Nat,
      exists outer : Nat,
      exists selectedFuel : Nat,
        inner <= budget /\
          outer <= budget /\
          TuringMachine.HaltsOnInputIn selected selectedFuel
            (GeneratedCode.nestedStageCode input inner outer)) <->
      exists inner : Nat,
      exists outer : Nat,
        inner <= budget /\
          outer <= budget /\
          TuringMachine.HaltsOnInput selected
            (GeneratedCode.nestedStageCode input inner outer)
  hiddenFuelToOrdinary :
    forall inner outer selectedFuel : Nat,
      TuringMachine.HaltsOnInputIn selected selectedFuel
        (GeneratedCode.nestedStageCode input inner outer) ->
      TuringMachine.HaltsOnInput selected
        (GeneratedCode.nestedStageCode input inner outer)
  ordinaryToHiddenFuel :
    forall inner outer : Nat,
      TuringMachine.HaltsOnInput selected
        (GeneratedCode.nestedStageCode input inner outer) ->
        exists selectedFuel : Nat,
          TuringMachine.HaltsOnInputIn selected selectedFuel
            (GeneratedCode.nestedStageCode input inner outer)
  boundedHiddenFuelToOrdinary :
    forall inner outer selectedFuel : Nat,
      inner <= budget ->
      outer <= budget ->
      TuringMachine.HaltsOnInputIn selected selectedFuel
        (GeneratedCode.nestedStageCode input inner outer) ->
      inner <= budget /\
        outer <= budget /\
        TuringMachine.HaltsOnInput selected
          (GeneratedCode.nestedStageCode input inner outer)
  boundedOrdinaryToHiddenFuel :
    forall inner outer : Nat,
      inner <= budget ->
      outer <= budget ->
      TuringMachine.HaltsOnInput selected
        (GeneratedCode.nestedStageCode input inner outer) ->
        exists selectedFuel : Nat,
          inner <= budget /\
            outer <= budget /\
            TuringMachine.HaltsOnInputIn selected selectedFuel
              (GeneratedCode.nestedStageCode input inner outer)

theorem generatedHiddenFuelPairShape
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (input : Word MachineCodeSymbol)
    (budget : Nat) :
    GeneratedHiddenFuelPairShape selected input budget :=
  { unboundedHiddenIffOrdinary :=
      generatedNested_exists_hiddenFuel_iff_exists_pair_haltsOnInput
        selected input
    boundedHiddenIffOrdinary :=
      generatedNested_exists_bounded_hiddenFuel_iff_exists_bounded_pair_haltsOnInput
        selected input budget
    hiddenFuelToOrdinary := by
      intro inner outer selectedFuel hselected
      exact
        TuringMachine.halts_on_input_in_to_halts_on_input
          (n := selectedFuel) hselected
    ordinaryToHiddenFuel := by
      intro inner outer hselected
      exact
        TuringMachine.halts_on_input_to_halts_on_input_in
          hselected
    boundedHiddenFuelToOrdinary := by
      intro inner outer selectedFuel hinner houter hselected
      exact
        ⟨hinner, houter,
          TuringMachine.halts_on_input_in_to_halts_on_input
            (n := selectedFuel) hselected⟩
    boundedOrdinaryToHiddenFuel := by
      intro inner outer hinner houter hselected
      rcases
          TuringMachine.halts_on_input_to_halts_on_input_in
            hselected with
        ⟨selectedFuel, hfuel⟩
      exact ⟨selectedFuel, hinner, houter, hfuel⟩ }

/-!
## Hidden-fuel route surfaces
-/

structure GeneratedUnboundedHiddenFuelPairRoute
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (searcherState : Type)
    (searcher : TuringMachine MachineCodeSymbol searcherState) :
    Prop where
  spec :
    GeneratedUnboundedHiddenFuelPairSpec searcher selected
  toHiddenFuel :
    forall input : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput searcher input ->
        exists inner : Nat,
        exists outer : Nat,
        exists selectedFuel : Nat,
          TuringMachine.HaltsOnInputIn selected selectedFuel
            (GeneratedCode.nestedStageCode input inner outer)
  ofHiddenFuel :
    forall input : Word MachineCodeSymbol,
    forall inner outer selectedFuel : Nat,
      TuringMachine.HaltsOnInputIn selected selectedFuel
        (GeneratedCode.nestedStageCode input inner outer) ->
      TuringMachine.HaltsOnInput searcher input
  enumeratorSpec :
    NestedPairEnumeratorSpec
      searcher selected GeneratedCode.nestedStageCode
  toOrdinaryPair :
    forall input : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput searcher input ->
        exists inner : Nat,
        exists outer : Nat,
          TuringMachine.HaltsOnInput selected
            (GeneratedCode.nestedStageCode input inner outer)

structure GeneratedBoundedHiddenFuelPairRoute
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (searcherState : Type)
    (searcher : TuringMachine MachineCodeSymbol searcherState) :
    Prop where
  spec :
    GeneratedBoundedHiddenFuelPairSpec searcher selected
  toHiddenFuel :
    forall input : Word MachineCodeSymbol,
    forall budget : Nat,
      TuringMachine.HaltsOnInput searcher
          (GeneratedCode.stageCode input budget) ->
        exists inner : Nat,
        exists outer : Nat,
        exists selectedFuel : Nat,
          inner <= budget /\
            outer <= budget /\
            TuringMachine.HaltsOnInputIn selected selectedFuel
              (GeneratedCode.nestedStageCode input inner outer)
  ofHiddenFuel :
    forall input : Word MachineCodeSymbol,
    forall budget inner outer selectedFuel : Nat,
      inner <= budget ->
      outer <= budget ->
      TuringMachine.HaltsOnInputIn selected selectedFuel
        (GeneratedCode.nestedStageCode input inner outer) ->
      TuringMachine.HaltsOnInput searcher
        (GeneratedCode.stageCode input budget)
  enumeratorSpec :
    BoundedNestedPairEnumeratorSpec
      searcher selected
      GeneratedCode.stageCode GeneratedCode.nestedStageCode
  toOrdinaryPair :
    forall input : Word MachineCodeSymbol,
    forall budget : Nat,
      TuringMachine.HaltsOnInput searcher
          (GeneratedCode.stageCode input budget) ->
        exists inner : Nat,
        exists outer : Nat,
          inner <= budget /\
            outer <= budget /\
            TuringMachine.HaltsOnInput selected
              (GeneratedCode.nestedStageCode input inner outer)

def GeneratedUnboundedHiddenFuelPairRouteConstruction
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    GeneratedUnboundedHiddenFuelPairRoute selected searcherState searcher

def GeneratedBoundedHiddenFuelPairRouteConstruction
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    GeneratedBoundedHiddenFuelPairRoute selected searcherState searcher

def GeneratedHiddenFuelPairRouteConstruction
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    Prop :=
  GeneratedUnboundedHiddenFuelPairRouteConstruction selected /\
    GeneratedBoundedHiddenFuelPairRouteConstruction selected

theorem generatedUnboundedHiddenFuelPairRoute_of_construction
    {selectedState : Type uSelected}
    {selected : TuringMachine MachineCodeSymbol selectedState}
    (h :
      GeneratedUnboundedHiddenFuelPairConstruction selected) :
    GeneratedUnboundedHiddenFuelPairRouteConstruction selected := by
  rcases h with ⟨searcherState, searcher, hspec⟩
  refine ⟨searcherState, searcher, ?_⟩
  exact
    { spec := hspec
      toHiddenFuel := by
        intro input hhalt
        exact (hspec input).mp hhalt
      ofHiddenFuel := by
        intro input inner outer selectedFuel hselected
        exact (hspec input).mpr
          ⟨inner, outer, selectedFuel, hselected⟩
      enumeratorSpec :=
        generatedNestedPairEnumeratorSpec_of_hiddenFuel hspec
      toOrdinaryPair := by
        intro input hhalt
        rcases (hspec input).mp hhalt with
          ⟨inner, outer, selectedFuel, hselected⟩
        exact
          ⟨inner, outer,
            TuringMachine.halts_on_input_in_to_halts_on_input
              (n := selectedFuel) hselected⟩ }

theorem generatedBoundedHiddenFuelPairRoute_of_construction
    {selectedState : Type uSelected}
    {selected : TuringMachine MachineCodeSymbol selectedState}
    (h :
      GeneratedBoundedHiddenFuelPairConstruction selected) :
    GeneratedBoundedHiddenFuelPairRouteConstruction selected := by
  rcases h with ⟨searcherState, searcher, hspec⟩
  refine ⟨searcherState, searcher, ?_⟩
  exact
    { spec := hspec
      toHiddenFuel := by
        intro input budget hhalt
        exact (hspec input budget).mp hhalt
      ofHiddenFuel := by
        intro input budget inner outer selectedFuel hinner houter hselected
        exact (hspec input budget).mpr
          ⟨inner, outer, selectedFuel, hinner, houter, hselected⟩
      enumeratorSpec :=
        generatedBoundedNestedPairEnumeratorSpec_of_hiddenFuel hspec
      toOrdinaryPair := by
        intro input budget hhalt
        rcases (hspec input budget).mp hhalt with
          ⟨inner, outer, selectedFuel, hinner, houter, hselected⟩
        exact
          ⟨inner, outer, hinner, houter,
            TuringMachine.halts_on_input_in_to_halts_on_input
              (n := selectedFuel) hselected⟩ }

theorem generatedHiddenFuelPairRoute_of_construction
    {selectedState : Type uSelected}
    {selected : TuringMachine MachineCodeSymbol selectedState}
    (h :
      GeneratedHiddenFuelPairConstruction selected) :
    GeneratedHiddenFuelPairRouteConstruction selected :=
  ⟨generatedUnboundedHiddenFuelPairRoute_of_construction h.left,
    generatedBoundedHiddenFuelPairRoute_of_construction h.right⟩

/-!
## Enumerator route surfaces
-/

structure GeneratedNestedPairEnumeratorRoute
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (searcherState : Type)
    (searcher : TuringMachine MachineCodeSymbol searcherState) :
    Prop where
  spec :
    NestedPairEnumeratorSpec
      searcher selected GeneratedCode.nestedStageCode
  toOrdinaryPair :
    forall input : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput searcher input ->
        exists inner : Nat,
        exists outer : Nat,
          TuringMachine.HaltsOnInput selected
            (GeneratedCode.nestedStageCode input inner outer)
  ofOrdinaryPair :
    forall input : Word MachineCodeSymbol,
    forall inner outer : Nat,
      TuringMachine.HaltsOnInput selected
        (GeneratedCode.nestedStageCode input inner outer) ->
      TuringMachine.HaltsOnInput searcher input

structure GeneratedBoundedNestedPairEnumeratorRoute
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState)
    (searcherState : Type)
    (searcher : TuringMachine MachineCodeSymbol searcherState) :
    Prop where
  spec :
    BoundedNestedPairEnumeratorSpec
      searcher selected
      GeneratedCode.stageCode GeneratedCode.nestedStageCode
  toOrdinaryPair :
    forall input : Word MachineCodeSymbol,
    forall budget : Nat,
      TuringMachine.HaltsOnInput searcher
          (GeneratedCode.stageCode input budget) ->
        exists inner : Nat,
        exists outer : Nat,
          inner <= budget /\
            outer <= budget /\
            TuringMachine.HaltsOnInput selected
              (GeneratedCode.nestedStageCode input inner outer)
  ofOrdinaryPair :
    forall input : Word MachineCodeSymbol,
    forall budget inner outer : Nat,
      inner <= budget ->
      outer <= budget ->
      TuringMachine.HaltsOnInput selected
        (GeneratedCode.nestedStageCode input inner outer) ->
      TuringMachine.HaltsOnInput searcher
        (GeneratedCode.stageCode input budget)

def GeneratedNestedPairEnumeratorRouteConstruction
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    GeneratedNestedPairEnumeratorRoute selected searcherState searcher

def GeneratedBoundedNestedPairEnumeratorRouteConstruction
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    GeneratedBoundedNestedPairEnumeratorRoute selected searcherState searcher

theorem generatedNestedPairEnumeratorRoute_of_construction
    {selectedState : Type uSelected}
    {selected : TuringMachine MachineCodeSymbol selectedState}
    (h :
      GeneratedNestedPairEnumeratorConstruction selected) :
    GeneratedNestedPairEnumeratorRouteConstruction selected := by
  rcases h with ⟨searcherState, searcher, hspec⟩
  refine ⟨searcherState, searcher, ?_⟩
  exact
    { spec := hspec
      toOrdinaryPair := by
        intro input hhalt
        exact (hspec input).mp hhalt
      ofOrdinaryPair := by
        intro input inner outer hselected
        exact (hspec input).mpr
          ⟨inner, outer, hselected⟩ }

theorem generatedBoundedNestedPairEnumeratorRoute_of_construction
    {selectedState : Type uSelected}
    {selected : TuringMachine MachineCodeSymbol selectedState}
    (h :
      GeneratedBoundedNestedPairEnumeratorConstruction selected) :
    GeneratedBoundedNestedPairEnumeratorRouteConstruction selected := by
  rcases h with ⟨searcherState, searcher, hspec⟩
  refine ⟨searcherState, searcher, ?_⟩
  exact
    { spec := hspec
      toOrdinaryPair := by
        intro input budget hhalt
        exact (hspec input budget).mp hhalt
      ofOrdinaryPair := by
        intro input budget inner outer hinner houter hselected
        exact (hspec input budget).mpr
          ⟨inner, outer, hinner, houter, hselected⟩ }

/-!
## Fin-state hidden-fuel route
-/

structure GeneratedHiddenFuelFiniteRoute : Prop where
  unboundedFinState :
    GeneratedUnboundedHiddenFuelPairFinStateConstruction
  boundedFinState :
    GeneratedBoundedHiddenFuelPairFinStateConstruction
  hiddenFinState :
    GeneratedHiddenFuelPairFinStateConstruction
  nestedEnumeratorFinState :
    GeneratedNestedPairEnumeratorFinStateConstruction
  boundedEnumeratorFinState :
    GeneratedBoundedNestedPairEnumeratorFinStateConstruction

def GeneratedHiddenFuelFiniteRouteConstruction : Prop :=
  GeneratedHiddenFuelFiniteRoute

theorem generatedHiddenFuelFiniteRoute_of_components
    (hunbounded : GeneratedUnboundedHiddenFuelPairFinStateConstruction)
    (hbounded : GeneratedBoundedHiddenFuelPairFinStateConstruction) :
    GeneratedHiddenFuelFiniteRoute := by
  let hhidden : GeneratedHiddenFuelPairFinStateConstruction :=
    ⟨hunbounded, hbounded⟩
  let hnested : GeneratedNestedPairEnumeratorFinStateConstruction :=
    generatedNestedPairEnumeratorFinStateConstruction_of_hiddenFuelComponents
      hhidden
  let hboundedNested :
      GeneratedBoundedNestedPairEnumeratorFinStateConstruction :=
    generatedBoundedNestedPairEnumeratorFinStateConstruction_of_hiddenFuelComponents
      hhidden
  exact
    { unboundedFinState := hunbounded
      boundedFinState := hbounded
      hiddenFinState := hhidden
      nestedEnumeratorFinState := hnested
      boundedEnumeratorFinState := hboundedNested }

theorem generatedHiddenFuelFiniteRoute_finiteLeaf :
    GeneratedHiddenFuelFiniteRoute :=
  generatedHiddenFuelFiniteRoute_of_components
    generatedUnboundedHiddenFuelPairFinStateFiniteLeaf
    generatedBoundedHiddenFuelPairFinStateFiniteLeaf

theorem generatedHiddenFuelFiniteRouteConstruction_finiteLeaf :
    GeneratedHiddenFuelFiniteRouteConstruction :=
  generatedHiddenFuelFiniteRoute_finiteLeaf

theorem generatedHiddenFuelRoute_finiteLeaf
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    GeneratedHiddenFuelPairRouteConstruction selected :=
  generatedHiddenFuelPairRoute_of_construction
    (generatedHiddenFuelPairConstruction_of_finStateConstruction
      selected generatedHiddenFuelFiniteRoute_finiteLeaf.hiddenFinState)

theorem generatedNestedPairEnumeratorRoute_finiteLeaf
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    GeneratedNestedPairEnumeratorRouteConstruction selected :=
  generatedNestedPairEnumeratorRoute_of_construction
    (generatedNestedPairEnumeratorConstruction_of_finStateConstruction
      selected
      generatedHiddenFuelFiniteRoute_finiteLeaf.nestedEnumeratorFinState)

theorem generatedBoundedNestedPairEnumeratorRoute_finiteLeaf
    {selectedState : Type uSelected}
    (selected : TuringMachine MachineCodeSymbol selectedState) :
    GeneratedBoundedNestedPairEnumeratorRouteConstruction selected :=
  generatedBoundedNestedPairEnumeratorRoute_of_construction
    (generatedBoundedNestedPairEnumeratorConstruction_of_finStateConstruction
      selected
      generatedHiddenFuelFiniteRoute_finiteLeaf.boundedEnumeratorFinState)

/-!
## Exact-fuel tuple-search route
-/

structure GeneratedNestedExactFuelSearchRoute
    {machineState : Type uMachine}
    (M : TuringMachine MachineCodeSymbol machineState)
    (searcherState : Type)
    (searcher : TuringMachine MachineCodeSymbol searcherState) :
    Prop where
  spec :
    GeneratedUnboundedNestedExactFuelSearchSpec searcher M
  toExactFuel :
    forall input : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput searcher input ->
        exists inner : Nat,
        exists outer : Nat,
          TuringMachine.HaltsOnInputIn M outer
            (GeneratedCode.stageCode input inner)
  ofExactFuel :
    forall input : Word MachineCodeSymbol,
    forall inner outer : Nat,
      TuringMachine.HaltsOnInputIn M outer
        (GeneratedCode.stageCode input inner) ->
      TuringMachine.HaltsOnInput searcher input

structure GeneratedBoundedNestedExactFuelSearchRoute
    {machineState : Type uMachine}
    (M : TuringMachine MachineCodeSymbol machineState)
    (searcherState : Type)
    (searcher : TuringMachine MachineCodeSymbol searcherState) :
    Prop where
  spec :
    GeneratedBoundedNestedExactFuelSearchSpec searcher M
  toExactFuel :
    forall input : Word MachineCodeSymbol,
    forall budget : Nat,
      TuringMachine.HaltsOnInput searcher
          (GeneratedCode.stageCode input budget) ->
        exists inner : Nat,
        exists outer : Nat,
          inner <= budget /\
            outer <= budget /\
            TuringMachine.HaltsOnInputIn M outer
              (GeneratedCode.stageCode input inner)
  ofExactFuel :
    forall input : Word MachineCodeSymbol,
    forall budget inner outer : Nat,
      inner <= budget ->
      outer <= budget ->
      TuringMachine.HaltsOnInputIn M outer
        (GeneratedCode.stageCode input inner) ->
      TuringMachine.HaltsOnInput searcher
        (GeneratedCode.stageCode input budget)

structure GeneratedNestedHaltingSearchRoute
    {machineState : Type uMachine}
    (M : TuringMachine MachineCodeSymbol machineState)
    (searcherState : Type)
    (searcher : TuringMachine MachineCodeSymbol searcherState) :
    Prop where
  spec :
    forall input : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput searcher input <->
        exists inner : Nat,
          TuringMachine.HaltsOnInput M
            (GeneratedCode.stageCode input inner)
  toHalting :
    forall input : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput searcher input ->
        exists inner : Nat,
          TuringMachine.HaltsOnInput M
            (GeneratedCode.stageCode input inner)
  ofHalting :
    forall input : Word MachineCodeSymbol,
    forall inner : Nat,
      TuringMachine.HaltsOnInput M
        (GeneratedCode.stageCode input inner) ->
      TuringMachine.HaltsOnInput searcher input

def GeneratedNestedExactFuelSearchRouteConstruction
    {machineState : Type uMachine}
    (M : TuringMachine MachineCodeSymbol machineState) : Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    GeneratedNestedExactFuelSearchRoute M searcherState searcher

def GeneratedBoundedNestedExactFuelSearchRouteConstruction
    {machineState : Type uMachine}
    (M : TuringMachine MachineCodeSymbol machineState) : Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    GeneratedBoundedNestedExactFuelSearchRoute M searcherState searcher

def GeneratedNestedHaltingSearchRouteConstruction
    {machineState : Type uMachine}
    (M : TuringMachine MachineCodeSymbol machineState) : Prop :=
  exists searcherState : Type,
  exists searcher : TuringMachine MachineCodeSymbol searcherState,
    GeneratedNestedHaltingSearchRoute M searcherState searcher

theorem generatedNestedExactFuelSearchRoute_of_construction
    {machineState : Type uMachine}
    {M : TuringMachine MachineCodeSymbol machineState}
    (h :
      GeneratedNestedExactFuelSearchConstruction M) :
    GeneratedNestedExactFuelSearchRouteConstruction M := by
  rcases h with ⟨searcherState, searcher, hspec⟩
  refine ⟨searcherState, searcher, ?_⟩
  exact
    { spec := hspec
      toExactFuel := by
        intro input hhalt
        exact (hspec input).mp hhalt
      ofExactFuel := by
        intro input inner outer hM
        exact (hspec input).mpr ⟨inner, outer, hM⟩ }

theorem generatedBoundedNestedExactFuelSearchRoute_of_construction
    {machineState : Type uMachine}
    {M : TuringMachine MachineCodeSymbol machineState}
    (h :
      GeneratedBoundedNestedExactFuelSearchConstruction M) :
    GeneratedBoundedNestedExactFuelSearchRouteConstruction M := by
  rcases h with ⟨searcherState, searcher, hspec⟩
  refine ⟨searcherState, searcher, ?_⟩
  exact
    { spec := hspec
      toExactFuel := by
        intro input budget hhalt
        exact (hspec input budget).mp hhalt
      ofExactFuel := by
        intro input budget inner outer hinner houter hM
        exact (hspec input budget).mpr
          ⟨inner, outer, hinner, houter, hM⟩ }

theorem generatedNestedHaltingSearchRoute_of_construction
    {machineState : Type uMachine}
    {M : TuringMachine MachineCodeSymbol machineState}
    (h :
      GeneratedNestedHaltingSearchConstruction M) :
    GeneratedNestedHaltingSearchRouteConstruction M := by
  rcases h with ⟨searcherState, searcher, hspec⟩
  refine ⟨searcherState, searcher, ?_⟩
  exact
    { spec := hspec
      toHalting := by
        intro input hhalt
        exact (hspec input).mp hhalt
      ofHalting := by
        intro input inner hM
        exact (hspec input).mpr ⟨inner, hM⟩ }

structure GeneratedTupleExactFuelRoute
    {machineState : Type uMachine}
    (M : TuringMachine MachineCodeSymbol machineState) : Prop where
  stageRunner :
    ExactFuel.RunnerConstruction M GeneratedCode.stageCode
  nestedExactFuel :
    GeneratedNestedExactFuelSearchConstruction M
  boundedNestedExactFuel :
    GeneratedBoundedNestedExactFuelSearchConstruction M
  nestedHalting :
    GeneratedNestedHaltingSearchConstruction M
  nestedExactFuelRoute :
    GeneratedNestedExactFuelSearchRouteConstruction M
  boundedNestedExactFuelRoute :
    GeneratedBoundedNestedExactFuelSearchRouteConstruction M
  nestedHaltingRoute :
    GeneratedNestedHaltingSearchRouteConstruction M

theorem generatedTupleExactFuelRoute_finiteLeaf
    {machineState : Type uMachine}
    (M : TuringMachine MachineCodeSymbol machineState) :
    GeneratedTupleExactFuelRoute M :=
  { stageRunner :=
      generatedStageProgramRunnerConstructionFiniteLeaf M
    nestedExactFuel :=
      generatedNestedExactFuelSearchFiniteLeaf M
    boundedNestedExactFuel :=
      generatedBoundedNestedExactFuelSearchFiniteLeaf M
    nestedHalting :=
      generatedNestedHaltingSearchFiniteLeaf M
    nestedExactFuelRoute :=
      generatedNestedExactFuelSearchRoute_of_construction
        (generatedNestedExactFuelSearchFiniteLeaf M)
    boundedNestedExactFuelRoute :=
      generatedBoundedNestedExactFuelSearchRoute_of_construction
        (generatedBoundedNestedExactFuelSearchFiniteLeaf M)
    nestedHaltingRoute :=
      generatedNestedHaltingSearchRoute_of_construction
        (generatedNestedHaltingSearchFiniteLeaf M) }

theorem generatedTupleExactFuelRouteDecidable_finiteLeaf
    {machineState : Type uMachine} [DecidableEq machineState]
    (M : TuringMachine MachineCodeSymbol machineState) :
    GeneratedTupleExactFuelRoute M :=
  { stageRunner :=
      generatedStageProgramRunnerConstructionFiniteLeafDecidable M
    nestedExactFuel :=
      generatedNestedExactFuelSearchFiniteLeafDecidable M
    boundedNestedExactFuel :=
      generatedBoundedNestedExactFuelSearchFiniteLeafDecidable M
    nestedHalting :=
      generatedNestedHaltingSearchFiniteLeafDecidable M
    nestedExactFuelRoute :=
      generatedNestedExactFuelSearchRoute_of_construction
        (generatedNestedExactFuelSearchFiniteLeafDecidable M)
    boundedNestedExactFuelRoute :=
      generatedBoundedNestedExactFuelSearchRoute_of_construction
        (generatedBoundedNestedExactFuelSearchFiniteLeafDecidable M)
    nestedHaltingRoute :=
      generatedNestedHaltingSearchRoute_of_construction
        (generatedNestedHaltingSearchFiniteLeafDecidable M) }

/-!
## Compatibility aliases
-/

theorem generatedUnboundedHiddenFuelPairFinStateFiniteLeaf_route :
    GeneratedUnboundedHiddenFuelPairFinStateConstruction :=
  generatedHiddenFuelFiniteRoute_finiteLeaf.unboundedFinState

theorem generatedBoundedHiddenFuelPairFinStateFiniteLeaf_route :
    GeneratedBoundedHiddenFuelPairFinStateConstruction :=
  generatedHiddenFuelFiniteRoute_finiteLeaf.boundedFinState

theorem generatedHiddenFuelPairFinStateFiniteLeaves_route :
    GeneratedHiddenFuelPairFinStateConstruction :=
  generatedHiddenFuelFiniteRoute_finiteLeaf.hiddenFinState

theorem generatedNestedPairEnumeratorFinStateFiniteLeaf_route :
    GeneratedNestedPairEnumeratorFinStateConstruction :=
  generatedHiddenFuelFiniteRoute_finiteLeaf.nestedEnumeratorFinState

theorem generatedBoundedNestedPairEnumeratorFinStateFiniteLeaf_route :
    GeneratedBoundedNestedPairEnumeratorFinStateConstruction :=
  generatedHiddenFuelFiniteRoute_finiteLeaf.boundedEnumeratorFinState

end TupleSearch
end FiniteRecognizer

end Computability
end FoC
