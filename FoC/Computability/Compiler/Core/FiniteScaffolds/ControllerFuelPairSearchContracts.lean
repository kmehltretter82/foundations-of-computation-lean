import FoC.Computability.Compiler.Core.FiniteScaffolds.ControllerFuelPairSearch

set_option doc.verso true

/-!
# Controller fuel-pair search route contracts

This module packages the bounded {lit}`(limit, fuel)` enumerator route used by
the controller search driver.  The concrete finite-table enumerator leaf
remains in
{module}`FoC.Computability.Compiler.Core.FiniteScaffolds.ControllerFuelPairSearch`;
the route contracts here expose the reusable path from right-shifted bounded
enumeration, through raw-output classification, to the final fuel-pair search
construction.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

/-!
## Bounded fuel-pair witness shape
-/

structure ControllerStageAttemptBoundedFuelPairWitnessShape
    (runner : MachineDescription)
    (i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner) : Prop where
  outputCodeEq :
    PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorOutputCode
        i =
      encodeBoolWord i.result
  outputTapeNormalized :
    Tape.normalizedOutput
        (PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
          i) =
      encodeCodeWordAsInput
        (PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorOutputCode
          i)
  outputTapeNormalizedBoolWord :
    Tape.normalizedOutput
        (PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
          i) =
      encodeCodeWordAsInput (encodeBoolWord i.result)
  runnerHalts :
    runner.HaltsWithOutput
      (encodeCodeWordAsInput
        (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
          i.input i.limit i.fuel))
      (encodeCodeWordAsInput (encodeBoolWord i.result))
  boundedTuple :
    exists searchLimit : Nat,
    exists limit : Nat,
    exists fuel : Nat,
      limit <= searchLimit ∧ fuel <= searchLimit ∧
        runner.HaltsWithOutput
          (encodeCodeWordAsInput
            (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
              i.input limit fuel))
          (encodeCodeWordAsInput (encodeBoolWord i.result))

theorem controllerStageAttemptBoundedFuelPairWitnessShape
    (runner : MachineDescription)
    (i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner) :
    ControllerStageAttemptBoundedFuelPairWitnessShape runner i :=
  { outputCodeEq := rfl
    outputTapeNormalized :=
      pairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape_normalizedOutput
        i
    outputTapeNormalizedBoolWord := by
      exact
        pairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape_normalizedOutput
          i
    runnerHalts := i.runner_halts
    boundedTuple :=
      ⟨i.searchLimit, i.limit, i.fuel,
        i.limit_le_searchLimit, i.fuel_le_searchLimit,
        i.runner_halts⟩ }

/-!
## Bounded right-shifted enumerator route
-/

structure ControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedRoute
    (runner enumerator : MachineDescription) : Prop where
  rightShiftedSpec :
    PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedSpec
      runner enumerator
  subroutineReady :
    enumerator.SubroutineReady
  forwardTape :
    forall i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner,
      enumerator.HaltsWithTape
        i.input
        (PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
          i)
  closedTape :
    forall w : Word Bool,
    forall T : Tape Bool,
      enumerator.HaltsWithTape w T ->
        exists i :
          PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
            runner,
          w = i.input ∧
            T =
              PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
                i
  boundedRealizes :
    PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRealizes
      runner enumerator
  boundedOutputIff :
    forall w result : Word Bool,
      enumerator.HaltsWithOutput w
          (encodeCodeWordAsInput (encodeBoolWord result)) <->
        exists searchLimit : Nat,
        exists limit : Nat,
        exists fuel : Nat,
          limit <= searchLimit ∧ fuel <= searchLimit ∧
            runner.HaltsWithOutput
              (encodeCodeWordAsInput
                (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
                  w limit fuel))
              (encodeCodeWordAsInput (encodeBoolWord result))
  unboundedRealizes :
    PairedRecognizerDovetailControllerStageAttemptFuelPairEnumeratorRealizes
      runner enumerator
  unboundedOutputIff :
    forall w result : Word Bool,
      enumerator.HaltsWithOutput w
          (encodeCodeWordAsInput (encodeBoolWord result)) <->
        exists limit : Nat,
        exists fuel : Nat,
          runner.HaltsWithOutput
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
                w limit fuel))
            (encodeCodeWordAsInput (encodeBoolWord result))
  boolWordRightShifted :
    PairedRecognizerDovetailControllerBoolWordRightShiftedEnumeratorSpec
      enumerator

def ControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedRouteConstruction :
    Prop :=
  forall runner : MachineDescription,
    runner.SubroutineReady ->
      exists enumerator : MachineDescription,
        ControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedRoute
          runner enumerator

theorem controllerStageAttemptBoundedFuelPairEnumeratorRightShiftedRoute_of_spec
    {runner enumerator : MachineDescription}
    (hspec :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedSpec
        runner enumerator) :
    ControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedRoute
      runner enumerator := by
  let hbounded :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRealizes
        runner enumerator :=
    pairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRealizes_of_rightShiftedSpec
      hspec
  let hunbounded :
      PairedRecognizerDovetailControllerStageAttemptFuelPairEnumeratorRealizes
        runner enumerator :=
    pairedRecognizerDovetailControllerStageAttemptFuelPairEnumeratorRealizes_of_bounded
      hbounded
  exact
    { rightShiftedSpec := hspec
      subroutineReady := hspec.left
      forwardTape := hspec.right.left
      closedTape := hspec.right.right
      boundedRealizes := hbounded
      boundedOutputIff := hbounded.right
      unboundedRealizes := hunbounded
      unboundedOutputIff := hunbounded.right
      boolWordRightShifted :=
        pairedRecognizerDovetailControllerBoolWordRightShiftedEnumeratorSpec_of_boundedFuelPairEnumerator
          hspec }

theorem controllerStageAttemptBoundedFuelPairEnumeratorRightShiftedRouteConstruction_of_spec
    (h :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedSpecConstruction) :
    ControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedRouteConstruction := by
  intro runner hrunner
  rcases h runner hrunner with ⟨enumerator, henumerator⟩
  exact
    ⟨enumerator,
      controllerStageAttemptBoundedFuelPairEnumeratorRightShiftedRoute_of_spec
        henumerator⟩

/-!
## Bool-word right-shifted enumerator route
-/

structure ControllerBoolWordRightShiftedEnumeratorRoute
    (enumerator : MachineDescription) : Prop where
  spec :
    PairedRecognizerDovetailControllerBoolWordRightShiftedEnumeratorSpec
      enumerator
  subroutineReady :
    enumerator.SubroutineReady
  outputForward :
    forall w result : Word Bool,
      enumerator.HaltsWithOutput w
          (encodeCodeWordAsInput (encodeBoolWord result)) ->
        enumerator.HaltsWithTape w
          (PairedRecognizerDovetailControllerBoolWordRightShiftedOutputTape
            result)
  outputClosed :
    forall w : Word Bool,
    forall T : Tape Bool,
      enumerator.HaltsWithTape w T ->
        exists result : Word Bool,
          enumerator.HaltsWithOutput w
              (encodeCodeWordAsInput (encodeBoolWord result)) ∧
            T =
              PairedRecognizerDovetailControllerBoolWordRightShiftedOutputTape
                result

theorem controllerBoolWordRightShiftedEnumeratorRoute_of_spec
    {enumerator : MachineDescription}
    (hspec :
      PairedRecognizerDovetailControllerBoolWordRightShiftedEnumeratorSpec
        enumerator) :
    ControllerBoolWordRightShiftedEnumeratorRoute enumerator :=
  { spec := hspec
    subroutineReady := hspec.left
    outputForward := hspec.right.left
    outputClosed := hspec.right.right }

theorem controllerBoolWordRightShiftedEnumeratorRoute_of_bounded
    {runner enumerator : MachineDescription}
    (hroute :
      ControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedRoute
        runner enumerator) :
    ControllerBoolWordRightShiftedEnumeratorRoute enumerator :=
  controllerBoolWordRightShiftedEnumeratorRoute_of_spec
    hroute.boolWordRightShifted

/-!
## Raw-output emitter and classifier routes
-/

structure ControllerBoolWordRawOutputEmitterRoute
    (emitter : MachineDescription) : Prop where
  realizes :
    PairedRecognizerDovetailControllerBoolWordRawOutputEmitterRealizes
      emitter
  subroutineReady :
    emitter.SubroutineReady
  emitsIff :
    forall result : Word Bool,
    forall b : Bool,
      emitter.HaltsWithOutput
          (encodeCodeWordAsInput (encodeBoolWord result)) [b] <->
        PairedRecognizerDovetailControllerRawOutput result = some [b]
  emitsOfRaw :
    forall result : Word Bool,
    forall b : Bool,
      PairedRecognizerDovetailControllerRawOutput result = some [b] ->
        emitter.HaltsWithOutput
          (encodeCodeWordAsInput (encodeBoolWord result)) [b]
  rawOfEmits :
    forall result : Word Bool,
    forall b : Bool,
      emitter.HaltsWithOutput
          (encodeCodeWordAsInput (encodeBoolWord result)) [b] ->
        PairedRecognizerDovetailControllerRawOutput result = some [b]

def ControllerBoolWordRawOutputEmitterRouteConstruction : Prop :=
  exists emitter : MachineDescription,
    ControllerBoolWordRawOutputEmitterRoute emitter

theorem controllerBoolWordRawOutputEmitterRoute_of_realizes
    {emitter : MachineDescription}
    (h :
      PairedRecognizerDovetailControllerBoolWordRawOutputEmitterRealizes
        emitter) :
    ControllerBoolWordRawOutputEmitterRoute emitter :=
  { realizes := h
    subroutineReady := h.left
    emitsIff := h.right
    emitsOfRaw := by
      intro result b hraw
      exact (h.right result b).mpr hraw
    rawOfEmits := by
      intro result b hemit
      exact (h.right result b).mp hemit }

theorem controllerBoolWordRawOutputEmitterRoute_of_construction
    (h :
      PairedRecognizerDovetailControllerBoolWordRawOutputEmitterConstruction) :
    ControllerBoolWordRawOutputEmitterRouteConstruction := by
  rcases h with ⟨emitter, hemitter⟩
  exact
    ⟨emitter,
      controllerBoolWordRawOutputEmitterRoute_of_realizes hemitter⟩

structure ControllerStageAttemptRawOutputClassifierRoute
    (enumerator emitter classifier : MachineDescription) : Prop where
  outputSpec :
    PairedRecognizerDovetailControllerStageAttemptRawOutputClassifierSequencerOutputSpec
      enumerator emitter classifier
  subroutineReady :
    classifier.SubroutineReady
  forward :
    forall w : Word Bool,
    forall result : Word Bool,
    forall b : Bool,
      enumerator.HaltsWithOutput w
          (encodeCodeWordAsInput (encodeBoolWord result)) ->
      emitter.HaltsWithOutput
          (encodeCodeWordAsInput (encodeBoolWord result)) [b] ->
        classifier.HaltsWithOutput w [b]
  closed :
    forall w : Word Bool,
    forall b : Bool,
      classifier.HaltsWithOutput w [b] ->
        exists result : Word Bool,
          enumerator.HaltsWithOutput w
              (encodeCodeWordAsInput (encodeBoolWord result)) ∧
            emitter.HaltsWithOutput
              (encodeCodeWordAsInput (encodeBoolWord result)) [b]

def ControllerStageAttemptRawOutputClassifierRouteConstruction
    (enumerator emitter : MachineDescription) : Prop :=
  exists classifier : MachineDescription,
    ControllerStageAttemptRawOutputClassifierRoute
      enumerator emitter classifier

theorem controllerStageAttemptRawOutputClassifierRoute_of_spec
    {enumerator emitter classifier : MachineDescription}
    (hspec :
      PairedRecognizerDovetailControllerStageAttemptRawOutputClassifierSequencerOutputSpec
        enumerator emitter classifier) :
    ControllerStageAttemptRawOutputClassifierRoute
      enumerator emitter classifier :=
  { outputSpec := hspec
    subroutineReady := hspec.left
    forward := hspec.right.left
    closed := hspec.right.right }

theorem controllerStageAttemptRawOutputClassifierRoute_of_components
    {enumerator emitter : MachineDescription}
    (henumerator :
      PairedRecognizerDovetailControllerBoolWordRightShiftedEnumeratorSpec
        enumerator)
    (hemitter :
      PairedRecognizerDovetailControllerBoolWordRawOutputEmitterRealizes
        emitter) :
    ControllerStageAttemptRawOutputClassifierRouteConstruction
      enumerator emitter := by
  rcases
      pairedRecognizerDovetailControllerStageAttemptRawOutputClassifierSequencer_rightShiftedEnumeratorConstruction
        enumerator emitter henumerator hemitter with
    ⟨classifier, hclassifier⟩
  exact
    ⟨classifier,
      controllerStageAttemptRawOutputClassifierRoute_of_spec hclassifier⟩

/-!
## Fuel-pair search route
-/

structure ControllerStageAttemptFuelPairSearchRoute
    (runner decider : MachineDescription) : Prop where
  realizes :
    PairedRecognizerDovetailControllerStageAttemptFuelPairSearchRealizes
      runner decider
  wellFormed :
    decider.WellFormed
  searchIff :
    forall w : Word Bool,
    forall b : Bool,
      decider.HaltsWithOutput w [b] <->
        exists limit : Nat,
        exists fuel : Nat,
        exists result : Word Bool,
          runner.HaltsWithOutput
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
                w limit fuel))
            (encodeCodeWordAsInput (encodeBoolWord result)) ∧
          PairedRecognizerDovetailControllerRawOutput result = some [b]
  toRunnerOutput :
    forall w : Word Bool,
    forall b : Bool,
      decider.HaltsWithOutput w [b] ->
        exists limit : Nat,
        exists fuel : Nat,
        exists result : Word Bool,
          runner.HaltsWithOutput
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
                w limit fuel))
            (encodeCodeWordAsInput (encodeBoolWord result)) ∧
          PairedRecognizerDovetailControllerRawOutput result = some [b]
  ofRunnerOutput :
    forall w : Word Bool,
    forall b : Bool,
    forall limit fuel : Nat,
    forall result : Word Bool,
      runner.HaltsWithOutput
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
            w limit fuel))
        (encodeCodeWordAsInput (encodeBoolWord result)) ->
      PairedRecognizerDovetailControllerRawOutput result = some [b] ->
        decider.HaltsWithOutput w [b]

def ControllerStageAttemptFuelPairSearchRouteConstruction : Prop :=
  forall runner : MachineDescription,
    runner.SubroutineReady ->
      exists decider : MachineDescription,
        ControllerStageAttemptFuelPairSearchRoute runner decider

theorem controllerStageAttemptFuelPairSearchRoute_of_realizes
    {runner decider : MachineDescription}
    (h :
      PairedRecognizerDovetailControllerStageAttemptFuelPairSearchRealizes
        runner decider) :
    ControllerStageAttemptFuelPairSearchRoute runner decider :=
  { realizes := h
    wellFormed := h.left
    searchIff := h.right
    toRunnerOutput := by
      intro w b hhalt
      exact (h.right w b).mp hhalt
    ofRunnerOutput := by
      intro w b limit fuel result hrun hraw
      exact (h.right w b).mpr
        ⟨limit, fuel, result, hrun, hraw⟩ }

theorem controllerStageAttemptFuelPairSearchRoute_of_construction
    (h :
      PairedRecognizerDovetailControllerStageAttemptFuelPairSearchConstruction) :
    ControllerStageAttemptFuelPairSearchRouteConstruction := by
  intro runner hrunner
  rcases h runner hrunner with ⟨decider, hdecider⟩
  exact
    ⟨decider,
      controllerStageAttemptFuelPairSearchRoute_of_realizes hdecider⟩

/-!
## Pipeline route bundle
-/

structure ControllerStageAttemptFuelPairSearchPipelineRoute
    (runner : MachineDescription) : Prop where
  boundedEnumerator :
    exists enumerator : MachineDescription,
      ControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedRoute
        runner enumerator
  rawEmitter :
    exists emitter : MachineDescription,
      ControllerBoolWordRawOutputEmitterRoute emitter
  boolWordEnumerator :
    exists enumerator : MachineDescription,
      ControllerBoolWordRightShiftedEnumeratorRoute enumerator
  classifier :
    exists enumerator : MachineDescription,
    exists emitter : MachineDescription,
    exists classifier : MachineDescription,
      ControllerStageAttemptRawOutputClassifierRoute
        enumerator emitter classifier
  fuelPairSearch :
    exists decider : MachineDescription,
      ControllerStageAttemptFuelPairSearchRoute runner decider

def ControllerStageAttemptFuelPairSearchPipelineRouteConstruction :
    Prop :=
  forall runner : MachineDescription,
    runner.SubroutineReady ->
      ControllerStageAttemptFuelPairSearchPipelineRoute runner

theorem controllerStageAttemptFuelPairSearchPipelineRoute_of_bounded_emitter
    (henumerator :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedSpecConstruction)
    (hemitter :
      PairedRecognizerDovetailControllerBoolWordRawOutputEmitterConstruction) :
    ControllerStageAttemptFuelPairSearchPipelineRouteConstruction := by
  intro runner hrunner
  rcases henumerator runner hrunner with ⟨enumerator, henumeratorSpec⟩
  let hboundedRoute :
      ControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedRoute
        runner enumerator :=
    controllerStageAttemptBoundedFuelPairEnumeratorRightShiftedRoute_of_spec
      henumeratorSpec
  rcases hemitter with ⟨emitter, hemitterSpec⟩
  let hemitterRoute :
      ControllerBoolWordRawOutputEmitterRoute emitter :=
    controllerBoolWordRawOutputEmitterRoute_of_realizes hemitterSpec
  let hboolRoute :
      ControllerBoolWordRightShiftedEnumeratorRoute enumerator :=
    controllerBoolWordRightShiftedEnumeratorRoute_of_bounded
      hboundedRoute
  rcases
      controllerStageAttemptRawOutputClassifierRoute_of_components
        hboundedRoute.boolWordRightShifted hemitterSpec with
    ⟨classifier, hclassifierRoute⟩
  have hsearch :
      PairedRecognizerDovetailControllerStageAttemptFuelPairSearchConstruction :=
    pairedRecognizerDovetailControllerStageAttemptFuelPairSearchConstruction_of_boundedRightShiftedEnumerator_emitter
      henumerator ⟨emitter, hemitterSpec⟩
  rcases
      controllerStageAttemptFuelPairSearchRoute_of_construction
        hsearch runner hrunner with
    ⟨decider, hdeciderRoute⟩
  exact
    { boundedEnumerator := ⟨enumerator, hboundedRoute⟩
      rawEmitter := ⟨emitter, hemitterRoute⟩
      boolWordEnumerator := ⟨enumerator, hboolRoute⟩
      classifier := ⟨enumerator, emitter, classifier, hclassifierRoute⟩
      fuelPairSearch := ⟨decider, hdeciderRoute⟩ }

theorem controllerStageAttemptFuelPairSearchPipelineRoute_search
    {runner : MachineDescription}
    (hroute :
      ControllerStageAttemptFuelPairSearchPipelineRoute runner) :
    exists decider : MachineDescription,
      ControllerStageAttemptFuelPairSearchRoute runner decider :=
  hroute.fuelPairSearch

theorem controllerStageAttemptFuelPairSearchRouteConstruction_of_pipeline
    (hpipeline :
      ControllerStageAttemptFuelPairSearchPipelineRouteConstruction) :
    ControllerStageAttemptFuelPairSearchRouteConstruction := by
  intro runner hrunner
  exact (hpipeline runner hrunner).fuelPairSearch

/-!
## Public finite-leaf aliases
-/

theorem pairedRecognizerDovetailControllerStageAttemptFuelPairSearchConstruction_finite_leaf_route :
    PairedRecognizerDovetailControllerStageAttemptFuelPairSearchConstruction :=
  pairedRecognizerDovetailControllerStageAttemptFuelPairSearchConstruction_finite_leaf

theorem controllerStageAttemptFuelPairSearchRouteConstruction_finite_leaf :
    ControllerStageAttemptFuelPairSearchRouteConstruction :=
  controllerStageAttemptFuelPairSearchRoute_of_construction
    pairedRecognizerDovetailControllerStageAttemptFuelPairSearchConstruction_finite_leaf

end Computability
end FoC
