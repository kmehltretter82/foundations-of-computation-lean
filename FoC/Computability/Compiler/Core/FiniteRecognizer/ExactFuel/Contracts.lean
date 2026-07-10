import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.Program

set_option doc.verso true

/-!
# Exact-fuel generated-runner route contracts

This module packages the semantic and ordinary-halting construction surfaces
for the normalized exact-fuel generated runner. The concrete finite-table leaf
remains in
{module}`FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.Program`;
the route contracts here record the reusable path from decoded stage input to
protected layout, ordinary protected-layout recognition, a code machine, and
an arbitrary finite-state exact-fuel runner.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel

/-!
## Stage-code semantic shape
-/

structure StageProgramSemanticShape
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (input : Word MachineCodeSymbol) (fuel : Nat) : Prop where
  stageCodeDecodeNat :
    MachineDescription.decodeNat
        (StageProgram.stageCode input fuel) =
      some (fuel, input)
  stageCodeEqOfDecodeNat :
    forall tokens : Word MachineCodeSymbol,
      MachineDescription.decodeNat tokens = some (fuel, input) ->
        tokens = StageProgram.stageCode input fuel
  runStageCodeIff :
    StageProgram.run M (StageProgram.stageCode input fuel) =
        some ([] : Word MachineCodeSymbol) <->
      TuringMachine.HaltsOnInputIn M fuel input
  runEqSomeIffDecodeNat :
    forall tokens : Word MachineCodeSymbol,
      StageProgram.run M tokens =
          some ([] : Word MachineCodeSymbol) <->
        exists decodedFuel : Nat,
        exists decodedInput : Word MachineCodeSymbol,
          MachineDescription.decodeNat tokens =
              some (decodedFuel, decodedInput) /\
            TuringMachine.HaltsOnInputIn M decodedFuel decodedInput
  initialLayoutConfig :
    (Layout.initial M input fuel).config =
      TuringMachine.initial M input
  initialLayoutFuel :
    (Layout.initial M input fuel).fuel = fuel
  initialLayoutState :
    (Layout.initial M input fuel).state = M.start
  initialLayoutLeft :
    (Layout.initial M input fuel).left = []
  initialLayoutAcceptsIff :
    Layout.accepts M (Layout.initial M input fuel) <->
      TuringMachine.HaltsOnInputIn M fuel input
  initialLayoutEncodedDecodes :
    Layout.decode stateCount
        (Layout.encode (Layout.initial M input fuel)) =
      some (Layout.initial M input fuel, [])
  stageCodeToInitialLayoutCode :
    Layout.stageCodeToInitialLayoutCode M
        (StageProgram.stageCode input fuel) =
      some (Layout.encode (Layout.initial M input fuel))
  materializerPrimitiveStageCode :
    (StageProgram.initialLayoutMaterializerCodePrimitive M).transform
        (StageProgram.stageCode input fuel) =
      some (Layout.encode (Layout.initial M input fuel))
  layoutCodeRunInitialIff :
    layoutCodeRun M
        (Layout.encode (Layout.initial M input fuel)) =
        some ([] : Word MachineCodeSymbol) <->
      TuringMachine.HaltsOnInputIn M fuel input
  layoutCodeRunPrimitiveInitialIff :
    (layoutCodeRunPrimitive M).transform
        (Layout.encode (Layout.initial M input fuel)) =
        some ([] : Word MachineCodeSymbol) <->
      TuringMachine.HaltsOnInputIn M fuel input
  layoutFuelLoopRunInitialIff :
    layoutFuelLoopCode M
        (Layout.encode (Layout.initial M input fuel)) =
        some ([] : Word MachineCodeSymbol) <->
      TuringMachine.HaltsOnInputIn M fuel input
  stageProgramFuelLoopPrimitiveStageCodeIff :
    (StageProgram.stageProgramFuelLoopCodePrimitive M).transform
        (StageProgram.stageCode input fuel) =
        some ([] : Word MachineCodeSymbol) <->
      TuringMachine.HaltsOnInputIn M fuel input
  stageProgramFuelLoopPrimitiveRunIff :
    forall tokens : Word MachineCodeSymbol,
      (StageProgram.stageProgramFuelLoopCodePrimitive M).transform tokens =
          some ([] : Word MachineCodeSymbol) <->
        StageProgram.run M tokens =
          some ([] : Word MachineCodeSymbol)

theorem stageProgramSemanticShape
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    StageProgramSemanticShape M input fuel :=
  { stageCodeDecodeNat :=
      StageProgram.stageCode_decodeNat input fuel
    stageCodeEqOfDecodeNat := by
      intro tokens hdecode
      exact StageProgram.stageCode_eq_of_decodeNat hdecode
    runStageCodeIff :=
      StageProgram.run_stageCode_eq_some_iff M input fuel
    runEqSomeIffDecodeNat :=
      StageProgram.run_eq_some_iff_decodeNat M
    initialLayoutConfig :=
      Layout.config_initial M input fuel
    initialLayoutFuel :=
      Layout.initial_fuel M input fuel
    initialLayoutState :=
      Layout.initial_state M input fuel
    initialLayoutLeft :=
      Layout.initial_left M input fuel
    initialLayoutAcceptsIff :=
      Layout.accepts_initial_iff_haltsOnInputIn M input fuel
    initialLayoutEncodedDecodes :=
      Layout.decode_encode (Layout.initial M input fuel)
    stageCodeToInitialLayoutCode := by
      simpa [StageProgram.stageCode, GeneratedCode.stageCode] using
        Layout.stageCodeToInitialLayoutCode_stageCode M input fuel
    materializerPrimitiveStageCode :=
      StageProgram.initialLayoutMaterializerCodePrimitive_stageCode
        M input fuel
    layoutCodeRunInitialIff :=
      layoutCodeRun_encode_initial_eq_some_iff M input fuel
    layoutCodeRunPrimitiveInitialIff :=
      layoutCodeRunPrimitive_encode_initial_eq_some_iff M input fuel
    layoutFuelLoopRunInitialIff :=
      Iff.trans
        (layoutFuelLoopCode_eq_layoutCodeRun_on_empty_output
          M (Layout.encode (Layout.initial M input fuel)))
        (layoutCodeRun_encode_initial_eq_some_iff M input fuel)
    stageProgramFuelLoopPrimitiveStageCodeIff :=
      Iff.trans
        (StageProgram.stageProgramFuelLoopCodePrimitive_eq_some_empty_iff
          M (StageProgram.stageCode input fuel))
        (StageProgram.run_stageCode_eq_some_iff M input fuel)
    stageProgramFuelLoopPrimitiveRunIff :=
      StageProgram.stageProgramFuelLoopCodePrimitive_eq_some_empty_iff M }

theorem stageProgramSemanticShape_of_decodeNat
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    {tokens input : Word MachineCodeSymbol} {fuel : Nat}
    (hdecode :
      MachineDescription.decodeNat tokens = some (fuel, input)) :
    tokens = StageProgram.stageCode input fuel ∧
      (StageProgram.run M tokens =
          some ([] : Word MachineCodeSymbol) <->
        TuringMachine.HaltsOnInputIn M fuel input) := by
  have hshape := stageProgramSemanticShape M input fuel
  constructor
  · exact hshape.stageCodeEqOfDecodeNat tokens hdecode
  · rw [hshape.stageCodeEqOfDecodeNat tokens hdecode]
    exact hshape.runStageCodeIff

theorem stageProgramFuelLoopPrimitive_stageCode_eq_run
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    (StageProgram.stageProgramFuelLoopCodePrimitive M).transform
        (StageProgram.stageCode input fuel) =
        some ([] : Word MachineCodeSymbol) <->
      TuringMachine.HaltsOnInputIn M fuel input :=
  (stageProgramSemanticShape M input fuel).stageProgramFuelLoopPrimitiveStageCodeIff

theorem stageProgramFuelLoopPrimitive_tokens_eq_run
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tokens : Word MachineCodeSymbol) :
    (StageProgram.stageProgramFuelLoopCodePrimitive M).transform tokens =
        some ([] : Word MachineCodeSymbol) <->
      StageProgram.run M tokens =
        some ([] : Word MachineCodeSymbol) :=
  StageProgram.stageProgramFuelLoopCodePrimitive_eq_some_empty_iff M tokens

theorem layoutFuelLoopCode_initial_eq_run
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    layoutFuelLoopCode M
        (Layout.encode (Layout.initial M input fuel)) =
        some ([] : Word MachineCodeSymbol) <->
      TuringMachine.HaltsOnInputIn M fuel input :=
  (stageProgramSemanticShape M input fuel).layoutFuelLoopRunInitialIff

theorem layoutCodeRun_initial_eq_run
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    layoutCodeRun M
        (Layout.encode (Layout.initial M input fuel)) =
        some ([] : Word MachineCodeSymbol) <->
      TuringMachine.HaltsOnInputIn M fuel input :=
  layoutCodeRun_encode_initial_eq_some_iff M input fuel

/-!
## Initial-layout and layout-loop endpoint routes
-/

structure InitialLayoutDecodedPrimitiveRoute
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (materializerState : Type)
    (materializer : TuringMachine MachineCodeSymbol materializerState) :
    Prop where
  decodedSpec :
    StageProgram.InitialLayoutDecodedExactOutputSpec materializer M
  canonical :
    StageProgram.ExactOutputCanonicalSpec materializer
      (Layout.stageCodeToInitialLayoutCode M)
  haltingTransitionsDisabled :
    TuringMachine.HaltingTransitionsDisabled materializer
  forwardStageCode :
    forall input : Word MachineCodeSymbol,
    forall fuel : Nat,
      TuringMachine.HaltsWithExactOutput materializer
        (StageProgram.stageCode input fuel)
        (StageProgram.initialLayoutDecodedOutput M fuel input)
  closedStageCode :
    forall tokens output : Word MachineCodeSymbol,
      TuringMachine.HaltsWithExactOutput materializer tokens output ->
        exists input : Word MachineCodeSymbol,
        exists fuel : Nat,
          tokens = StageProgram.stageCode input fuel /\
            output = StageProgram.initialLayoutDecodedOutput
              M fuel input

def InitialLayoutDecodedPrimitiveRouteConstruction
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    Prop :=
  exists materializerState : Type,
  exists materializer : TuringMachine MachineCodeSymbol materializerState,
    InitialLayoutDecodedPrimitiveRoute M materializerState materializer

theorem initialLayoutDecodedPrimitiveRoute_of_construction
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (h :
      StageProgram.InitialLayoutDecodedExactOutputPrimitiveConstruction
        M) :
    InitialLayoutDecodedPrimitiveRouteConstruction M := by
  rcases h with
    ⟨materializerState, materializer, hspec, hcanonical, hstop⟩
  exact
    ⟨materializerState, materializer,
      { decodedSpec := hspec
        canonical := hcanonical
        haltingTransitionsDisabled := hstop
        forwardStageCode := hspec.left
        closedStageCode := hspec.right }⟩

theorem initialLayoutDecodedPrimitiveRouteConstruction_of_finState
    (h :
      StageProgram.InitialLayoutDecodedExactOutputPrimitiveFinStateConstruction) :
    forall stateCount : Nat,
    forall M : TuringMachine MachineCodeSymbol (Fin stateCount),
      InitialLayoutDecodedPrimitiveRouteConstruction M := by
  intro stateCount M
  exact initialLayoutDecodedPrimitiveRoute_of_construction (h stateCount M)

/-!
## Finite construction-chain routes
-/

structure ExactFuelFiniteComponentRoute : Prop where
  components :
    StageProgram.FiniteComponentFinStateConstruction
  layoutFuelLoop :
    FinStateLayoutFuelLoopCodeMachineConstruction
  codeMachine :
    StageProgram.FinStateCodeMachineConstruction
  runner :
    FinStateRunnerConstruction StageProgram.stageCode
  initialLayoutRoute :
    forall stateCount : Nat,
    forall M : TuringMachine MachineCodeSymbol (Fin stateCount),
      InitialLayoutDecodedPrimitiveRouteConstruction M

def ExactFuelFiniteComponentRouteConstruction : Prop :=
  ExactFuelFiniteComponentRoute

theorem exactFuelFiniteComponentRoute_of_components
    (hcomponents : StageProgram.FiniteComponentFinStateConstruction) :
    ExactFuelFiniteComponentRoute := by
  let hcode :
      StageProgram.FinStateCodeMachineConstruction :=
    StageProgram.codeMachineFinStateConstruction_of_finiteComponents
      hcomponents
  exact
    { components := hcomponents
      layoutFuelLoop := hcomponents.right
      codeMachine := hcode
      runner :=
        StageProgram.finStateRunnerConstruction_of_codeMachine
          hcode
      initialLayoutRoute :=
        initialLayoutDecodedPrimitiveRouteConstruction_of_finState
          hcomponents.left }

theorem exactFuelFiniteComponentRoute_finiteLeaf :
    ExactFuelFiniteComponentRoute :=
  exactFuelFiniteComponentRoute_of_components
    StageProgram.finiteComponentFiniteLeaves

theorem exactFuelFiniteComponentRouteConstruction_finiteLeaf :
    ExactFuelFiniteComponentRouteConstruction :=
  exactFuelFiniteComponentRoute_finiteLeaf

/-!
## Per-machine route projections
-/

structure ExactFuelMachineRoute
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : Prop where
  initialLayoutDecoded :
    StageProgram.InitialLayoutDecodedExactOutputPrimitiveConstruction M
  layoutFuelLoop :
    LayoutFuelLoopCodeMachineConstruction M
  initialLayoutRoute :
    InitialLayoutDecodedPrimitiveRouteConstruction M
  codeMachine :
    StageProgram.CodeMachineConstruction M
  runner :
    RunnerConstruction M StageProgram.stageCode
  semanticShape :
    forall input : Word MachineCodeSymbol,
    forall fuel : Nat,
      StageProgramSemanticShape M input fuel

theorem ExactFuelFiniteComponentRoute.machineRoute
    (hroute : ExactFuelFiniteComponentRoute)
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    ExactFuelMachineRoute M :=
  { initialLayoutDecoded :=
      hroute.components.left stateCount M
    layoutFuelLoop :=
      hroute.layoutFuelLoop stateCount M
    initialLayoutRoute :=
      hroute.initialLayoutRoute stateCount M
    codeMachine :=
      hroute.codeMachine stateCount M
    runner :=
      StageProgram.runnerConstruction_of_codeMachine
        (hroute.codeMachine stateCount M)
    semanticShape :=
      stageProgramSemanticShape M }

theorem exactFuelMachineRoute_finiteLeaf
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    ExactFuelMachineRoute M :=
  exactFuelFiniteComponentRoute_finiteLeaf.machineRoute M

theorem ExactFuelFiniteComponentRoute.runnerConstruction
    (hroute : ExactFuelFiniteComponentRoute)
    {state : Type}
    (M : TuringMachine MachineCodeSymbol state) :
    RunnerConstruction M StageProgram.stageCode :=
  runnerConstruction_of_finStateConstruction M hroute.runner

theorem ExactFuelFiniteComponentRoute.runnerConstructionDecidable
    (hroute : ExactFuelFiniteComponentRoute)
    {state : Type} [DecidableEq state]
    (M : TuringMachine MachineCodeSymbol state) :
    RunnerConstruction M StageProgram.stageCode :=
  runnerConstruction_of_finStateConstructionDecidable M hroute.runner

theorem exactFuelRunnerConstruction_finiteLeaf
    {state : Type}
    (M : TuringMachine MachineCodeSymbol state) :
    RunnerConstruction M StageProgram.stageCode :=
  exactFuelFiniteComponentRoute_finiteLeaf.runnerConstruction M

theorem exactFuelRunnerConstructionDecidable_finiteLeaf
    {state : Type} [DecidableEq state]
    (M : TuringMachine MachineCodeSymbol state) :
    RunnerConstruction M StageProgram.stageCode :=
  exactFuelFiniteComponentRoute_finiteLeaf.runnerConstructionDecidable M

structure ExactFuelRunnerRoute
    {state : Type}
    (M : TuringMachine MachineCodeSymbol state)
    (runnerState : Type)
    (runner : TuringMachine MachineCodeSymbol runnerState) :
    Prop where
  spec :
    ExactFuelRunnerSpec runner M StageProgram.stageCode
  acceptsStageCodeIff :
    forall input : Word MachineCodeSymbol,
    forall fuel : Nat,
      TuringMachine.HaltsOnInput runner
          (StageProgram.stageCode input fuel) <->
        TuringMachine.HaltsOnInputIn M fuel input

def ExactFuelRunnerRouteConstruction
    {state : Type}
    (M : TuringMachine MachineCodeSymbol state) : Prop :=
  exists runnerState : Type,
  exists runner : TuringMachine MachineCodeSymbol runnerState,
    ExactFuelRunnerRoute M runnerState runner

theorem exactFuelRunnerRoute_of_construction
    {state : Type}
    {M : TuringMachine MachineCodeSymbol state}
    (h : RunnerConstruction M StageProgram.stageCode) :
    ExactFuelRunnerRouteConstruction M := by
  rcases h with ⟨runnerState, runner, hspec⟩
  exact
    ⟨runnerState, runner,
      { spec := hspec
        acceptsStageCodeIff := hspec }⟩

theorem ExactFuelFiniteComponentRoute.runnerRoute
    (hroute : ExactFuelFiniteComponentRoute)
    {state : Type}
    (M : TuringMachine MachineCodeSymbol state) :
    ExactFuelRunnerRouteConstruction M :=
  exactFuelRunnerRoute_of_construction
    (hroute.runnerConstruction M)

theorem ExactFuelFiniteComponentRoute.runnerRouteDecidable
    (hroute : ExactFuelFiniteComponentRoute)
    {state : Type} [DecidableEq state]
    (M : TuringMachine MachineCodeSymbol state) :
    ExactFuelRunnerRouteConstruction M :=
  exactFuelRunnerRoute_of_construction
    (hroute.runnerConstructionDecidable M)

theorem exactFuelRunnerRoute_finiteLeaf
    {state : Type}
    (M : TuringMachine MachineCodeSymbol state) :
    ExactFuelRunnerRouteConstruction M :=
  exactFuelFiniteComponentRoute_finiteLeaf.runnerRoute M

theorem exactFuelRunnerRouteDecidable_finiteLeaf
    {state : Type} [DecidableEq state]
    (M : TuringMachine MachineCodeSymbol state) :
    ExactFuelRunnerRouteConstruction M :=
  exactFuelFiniteComponentRoute_finiteLeaf.runnerRouteDecidable M

/-!
## Code-machine route projections
-/

structure ExactFuelCodeMachineRoute
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (runnerState : Type)
    (runner : TuringMachine MachineCodeSymbol runnerState) :
    Prop where
  codeMachineSpec :
    StageProgram.CodeMachineSpec runner M
  acceptsTokensIffRun :
    forall tokens : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput runner tokens <->
        StageProgram.run M tokens =
          some ([] : Word MachineCodeSymbol)
  acceptsStageCodeIff :
    forall input : Word MachineCodeSymbol,
    forall fuel : Nat,
      TuringMachine.HaltsOnInput runner
          (StageProgram.stageCode input fuel) <->
        TuringMachine.HaltsOnInputIn M fuel input

def ExactFuelCodeMachineRouteConstruction
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    Prop :=
  exists runnerState : Type,
  exists runner : TuringMachine MachineCodeSymbol runnerState,
    ExactFuelCodeMachineRoute M runnerState runner

theorem exactFuelCodeMachineRoute_of_construction
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (h : StageProgram.CodeMachineConstruction M) :
    ExactFuelCodeMachineRouteConstruction M := by
  rcases h with ⟨runnerState, runner, hspec⟩
  exact
    ⟨runnerState, runner,
      { codeMachineSpec := hspec
        acceptsTokensIffRun := hspec
        acceptsStageCodeIff := by
          intro input fuel
          exact Iff.trans
            (hspec (StageProgram.stageCode input fuel))
            (StageProgram.run_stageCode_eq_some_iff M input fuel) }⟩

theorem ExactFuelFiniteComponentRoute.codeMachineRoute
    (hroute : ExactFuelFiniteComponentRoute)
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    ExactFuelCodeMachineRouteConstruction M :=
  exactFuelCodeMachineRoute_of_construction
    (hroute.codeMachine stateCount M)

theorem exactFuelCodeMachineRoute_finiteLeaf
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    ExactFuelCodeMachineRouteConstruction M :=
  exactFuelFiniteComponentRoute_finiteLeaf.codeMachineRoute M

end ExactFuel
end FiniteRecognizer

end Computability
end FoC
