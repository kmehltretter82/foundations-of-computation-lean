import FoC.Computability.Compiler.Core.FiniteScaffolds.ControllerOutputLevelSimulator

set_option doc.verso true

/-!
# Controller output-level simulator route contracts

This module packages the controller-facing exact-fuel runner route through the
generated-input parser, fixed-description bounded simulator, and output
extractor.  The concrete parser and extractor finite-table leaves remain in
{module}`FoC.Computability.Compiler.Core.FiniteScaffolds.ControllerOutputLevelSimulator`;
the route contracts here expose the reusable surfaces and the composition
path used by the controller fuel-search driver.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

/-!
## Generated simulator-input shape
-/

structure ControllerStageAttemptFuelSimulatorInputShape
    (attempt : MachineDescription)
    (w : Word Bool) (limit fuel : Nat) : Prop where
  primitiveEncode :
    (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodePrimitive
        attempt).transform
        (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
          w limit fuel) =
      some
        (SimulatorLayout.encode
          (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout
            attempt w limit fuel))
  outputTapeNormalized :
    Tape.normalizedOutput
        (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorOutputTape
          attempt w limit fuel) =
      encodeCodeWordAsInput
        (SimulatorLayout.encode
          (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout
            attempt w limit fuel))
  transformIff :
    forall code out : Word MachineCodeSymbol,
      (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodePrimitive
          attempt).transform code = some out <->
        exists decodedInput : Word Bool,
        exists decodedLimit decodedFuel : Nat,
          code =
            PairedRecognizerDovetailControllerStageAttemptFuelInputCode
              decodedInput decodedLimit decodedFuel ∧
          out =
            SimulatorLayout.encode
              (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout
                attempt decodedInput decodedLimit decodedFuel)
  outputTapeOfTransform :
    forall code out : Word MachineCodeSymbol,
      (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodePrimitive
          attempt).transform code = some out ->
        exists decodedInput : Word Bool,
        exists decodedLimit decodedFuel : Nat,
          code =
            PairedRecognizerDovetailControllerStageAttemptFuelInputCode
              decodedInput decodedLimit decodedFuel ∧
          out =
            SimulatorLayout.encode
              (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout
                attempt decodedInput decodedLimit decodedFuel)

theorem controllerStageAttemptFuelSimulatorInputShape
    (attempt : MachineDescription)
    (w : Word Bool) (limit fuel : Nat) :
    ControllerStageAttemptFuelSimulatorInputShape attempt w limit fuel :=
  { primitiveEncode :=
      pairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodePrimitive_encode
        attempt w limit fuel
    outputTapeNormalized := by
      exact
        EncRewriters.tape_normalizedOutput_move_right_input
          (encodeCodeWordAsInput
            (SimulatorLayout.encode
              (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout
                attempt w limit fuel)))
    transformIff := by
      intro code out
      exact
        pairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodePrimitive_transform_eq_some_iff
          attempt code out
    outputTapeOfTransform := by
      intro code out htransform
      exact
        (pairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodePrimitive_transform_eq_some_iff
          attempt code out).mp htransform }

/-!
## Fuel simulator parser route
-/

structure ControllerStageAttemptFuelSimulatorRightShiftedRoute
    (attempt parser : MachineDescription) : Prop where
  spec :
    PairedRecognizerDovetailControllerStageAttemptFuelSimulatorRightShiftedSpec
      attempt parser
  subroutineReady :
    parser.SubroutineReady
  forwardTape :
    forall w : Word Bool,
    forall limit fuel : Nat,
      parser.HaltsWithTape
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
            w limit fuel))
        (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorOutputTape
          attempt w limit fuel)
  closedTape :
    forall code : Word MachineCodeSymbol,
    forall T : Tape Bool,
      parser.HaltsWithTape (encodeCodeWordAsInput code) T ->
        exists w : Word Bool,
        exists limit fuel : Nat,
          code =
            PairedRecognizerDovetailControllerStageAttemptFuelInputCode
              w limit fuel ∧
          T =
            PairedRecognizerDovetailControllerStageAttemptFuelSimulatorOutputTape
              attempt w limit fuel
  outputTapeNormalized :
    forall w : Word Bool,
    forall limit fuel : Nat,
      Tape.normalizedOutput
        (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorOutputTape
          attempt w limit fuel) =
        encodeCodeWordAsInput
          (SimulatorLayout.encode
            (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout
              attempt w limit fuel))

def ControllerStageAttemptFuelSimulatorRightShiftedRouteConstruction :
    Prop :=
  forall attempt : MachineDescription,
    exists parser : MachineDescription,
      ControllerStageAttemptFuelSimulatorRightShiftedRoute attempt parser

theorem controllerStageAttemptFuelSimulatorRightShiftedRoute_of_spec
    {attempt parser : MachineDescription}
    (h :
      PairedRecognizerDovetailControllerStageAttemptFuelSimulatorRightShiftedSpec
        attempt parser) :
    ControllerStageAttemptFuelSimulatorRightShiftedRoute attempt parser :=
  { spec := h
    subroutineReady := h.left
    forwardTape := h.right.left
    closedTape := h.right.right
    outputTapeNormalized := by
      intro w limit fuel
      exact
        (controllerStageAttemptFuelSimulatorInputShape
          attempt w limit fuel).outputTapeNormalized }

theorem controllerStageAttemptFuelSimulatorRightShiftedRouteConstruction_of_spec
    (h :
      PairedRecognizerDovetailControllerStageAttemptFuelSimulatorRightShiftedSpecConstruction) :
    ControllerStageAttemptFuelSimulatorRightShiftedRouteConstruction := by
  intro attempt
  rcases h attempt with ⟨parser, hparser⟩
  exact
    ⟨parser,
      controllerStageAttemptFuelSimulatorRightShiftedRoute_of_spec hparser⟩

structure ControllerStageAttemptFuelSimulatorCompiledRoute : Prop where
  rightShiftedSpecConstruction :
    PairedRecognizerDovetailControllerStageAttemptFuelSimulatorRightShiftedSpecConstruction
  rightShiftedRouteConstruction :
    ControllerStageAttemptFuelSimulatorRightShiftedRouteConstruction
  rightShiftedCompiled :
    PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodeRightShiftedConstruction
  closedHandoffCompiled :
    PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodeClosedHandoffConstruction

def ControllerStageAttemptFuelSimulatorCompiledRouteConstruction : Prop :=
  ControllerStageAttemptFuelSimulatorCompiledRoute

theorem controllerStageAttemptFuelSimulatorCompiledRoute_of_spec
    (h :
      PairedRecognizerDovetailControllerStageAttemptFuelSimulatorRightShiftedSpecConstruction) :
    ControllerStageAttemptFuelSimulatorCompiledRoute :=
  { rightShiftedSpecConstruction := h
    rightShiftedRouteConstruction :=
      controllerStageAttemptFuelSimulatorRightShiftedRouteConstruction_of_spec
        h
    rightShiftedCompiled :=
      pairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodeRightShiftedConstruction_of_spec
        h
    closedHandoffCompiled :=
      pairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodeClosedHandoffConstruction_of_rightShifted
        (pairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodeRightShiftedConstruction_of_spec
          h) }

/-!
## Simulator output extractor route
-/

structure ControllerStageAttemptFuelOutputIndexShape
    (attempt : MachineDescription)
    (i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt) : Prop where
  inputCodeEq :
    PairedRecognizerDovetailControllerStageAttemptFuelOutputInputCode i =
      SimulatorLayout.encode i.1.1
  outputCodeEq :
    PairedRecognizerDovetailControllerStageAttemptFuelOutputOutputCode i =
      i.1.2
  outputTapeNormalized :
    Tape.normalizedOutput
        (PairedRecognizerDovetailControllerStageAttemptFuelOutputTape i) =
      encodeCodeWordAsInput
        (PairedRecognizerDovetailControllerStageAttemptFuelOutputOutputCode
          i)
  haltedLayout :
    i.1.1.config.state = attempt.halt
  layoutOutput :
    Tape.normalizedOutput i.1.1.config.tape =
      encodeCodeWordAsInput i.1.2

theorem controllerStageAttemptFuelOutputIndexShape
    (attempt : MachineDescription)
    (i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt) :
    ControllerStageAttemptFuelOutputIndexShape attempt i :=
  { inputCodeEq := rfl
    outputCodeEq := rfl
    outputTapeNormalized :=
      CommonGround.CodeWordEmitters.exactOutputTape_normalizedOutput
        PairedRecognizerDovetailControllerStageAttemptFuelOutputOutputCode i
    haltedLayout := i.2.left
    layoutOutput := i.2.right }

structure ControllerStageAttemptFuelOutputExtractorRoute
    (attempt extractor : MachineDescription) : Prop where
  spec :
    PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineSpec
      attempt extractor
  subroutineReady :
    extractor.SubroutineReady
  forwardTape :
    forall i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt,
      extractor.HaltsWithTape
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageAttemptFuelOutputInputCode
            i))
        (PairedRecognizerDovetailControllerStageAttemptFuelOutputTape i)
  closedTape :
    forall code : Word MachineCodeSymbol,
    forall T : Tape Bool,
      extractor.HaltsWithTape (encodeCodeWordAsInput code) T ->
        exists i :
          PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
            attempt,
          code =
            PairedRecognizerDovetailControllerStageAttemptFuelOutputInputCode
              i ∧
          T =
            PairedRecognizerDovetailControllerStageAttemptFuelOutputTape i
  outputTapeNormalized :
    forall i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt,
      Tape.normalizedOutput
          (PairedRecognizerDovetailControllerStageAttemptFuelOutputTape i) =
        encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageAttemptFuelOutputOutputCode
            i)

def ControllerStageAttemptFuelOutputExtractorRouteConstruction : Prop :=
  forall attempt : MachineDescription,
    exists extractor : MachineDescription,
      ControllerStageAttemptFuelOutputExtractorRoute attempt extractor

theorem controllerStageAttemptFuelOutputExtractorRoute_of_spec
    {attempt extractor : MachineDescription}
    (h :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineSpec
        attempt extractor) :
    ControllerStageAttemptFuelOutputExtractorRoute attempt extractor :=
  { spec := h
    subroutineReady := h.left
    forwardTape := h.right.left
    closedTape := h.right.right
    outputTapeNormalized := by
      intro i
      exact
        (controllerStageAttemptFuelOutputIndexShape
          attempt i).outputTapeNormalized }

theorem controllerStageAttemptFuelOutputExtractorRouteConstruction_of_spec
    (h :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineSpecConstruction) :
    ControllerStageAttemptFuelOutputExtractorRouteConstruction := by
  intro attempt
  rcases h attempt with ⟨extractor, hextractor⟩
  exact
    ⟨extractor,
      controllerStageAttemptFuelOutputExtractorRoute_of_spec hextractor⟩

structure ControllerStageAttemptFuelOutputExtractorCompiledRoute : Prop where
  specConstruction :
    PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineSpecConstruction
  routeConstruction :
    ControllerStageAttemptFuelOutputExtractorRouteConstruction
  outputCompiled :
    PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction

def ControllerStageAttemptFuelOutputExtractorCompiledRouteConstruction :
    Prop :=
  ControllerStageAttemptFuelOutputExtractorCompiledRoute

theorem controllerStageAttemptFuelOutputExtractorCompiledRoute_of_spec
    (h :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineSpecConstruction) :
    ControllerStageAttemptFuelOutputExtractorCompiledRoute :=
  { specConstruction := h
    routeConstruction :=
      controllerStageAttemptFuelOutputExtractorRouteConstruction_of_spec h
    outputCompiled :=
      pairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction_of_spec
        h }

/-!
## Protected exact-fuel runner route
-/

structure ControllerStageAttemptExactFuelRunnerRoute
    (attempt runner : MachineDescription) : Prop where
  realizes :
    PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerRealizes
      attempt runner
  subroutineReady :
    runner.SubroutineReady
  runnerIff :
    forall w : Word Bool,
    forall limit fuel : Nat,
    forall result : Word Bool,
      runner.HaltsWithOutput
          (encodeCodeWordAsInput
            (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
              w limit fuel))
          (encodeCodeWordAsInput (encodeBoolWord result)) <->
        attempt.HaltsWithOutputIn fuel
          (encodeCodeWordAsInput
            (PairedRecognizerDovetailStageInputCode w limit))
          (encodeCodeWordAsInput (encodeBoolWord result))
  forward :
    PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerForwardSpec
      attempt runner
  closed :
    PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerClosedSpec
      attempt runner

def ControllerStageAttemptExactFuelRunnerRouteConstruction : Prop :=
  forall attempt : MachineDescription,
    attempt.SubroutineReady ->
      exists runner : MachineDescription,
        ControllerStageAttemptExactFuelRunnerRoute attempt runner

theorem controllerStageAttemptExactFuelRunnerRoute_of_realizes
    {attempt runner : MachineDescription}
    (h :
      PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerRealizes
        attempt runner) :
    ControllerStageAttemptExactFuelRunnerRoute attempt runner :=
  { realizes := h
    subroutineReady := h.left
    runnerIff := h.right
    forward := by
      intro w limit fuel result hattempt
      exact (h.right w limit fuel result).mpr hattempt
    closed := by
      intro w limit fuel result hrunner
      exact (h.right w limit fuel result).mp hrunner }

theorem controllerStageAttemptExactFuelRunnerRouteConstruction_of_construction
    (h :
      PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerConstruction) :
    ControllerStageAttemptExactFuelRunnerRouteConstruction := by
  intro attempt hattempt
  rcases h attempt hattempt with ⟨runner, hrunner⟩
  exact
    ⟨runner,
      controllerStageAttemptExactFuelRunnerRoute_of_realizes hrunner⟩

structure ProtectedControllerStageAttemptExactFuelRunnerRoute
    (attempt invoker runner : MachineDescription) : Prop where
  protectedInvocation :
    CommonGround.ControllerInvocation.StageAttemptProtectedRealizes
      attempt invoker
  realizes :
    PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerRealizes
      attempt runner
  route :
    ControllerStageAttemptExactFuelRunnerRoute attempt runner
  forward :
    PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerForwardSpec
      attempt runner
  closed :
    PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerClosedSpec
      attempt runner

def ProtectedControllerStageAttemptExactFuelRunnerRouteConstruction :
    Prop :=
  forall attempt invoker : MachineDescription,
    CommonGround.ControllerInvocation.StageAttemptProtectedRealizes
      attempt invoker ->
      exists runner : MachineDescription,
        ProtectedControllerStageAttemptExactFuelRunnerRoute
          attempt invoker runner

theorem protectedControllerStageAttemptExactFuelRunnerRoute_of_realizes
    {attempt invoker runner : MachineDescription}
    (hinvoker :
      CommonGround.ControllerInvocation.StageAttemptProtectedRealizes
        attempt invoker)
    (hrunner :
      PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerRealizes
        attempt runner) :
    ProtectedControllerStageAttemptExactFuelRunnerRoute
      attempt invoker runner :=
  { protectedInvocation := hinvoker
    realizes := hrunner
    route :=
      controllerStageAttemptExactFuelRunnerRoute_of_realizes hrunner
    forward := by
      intro w limit fuel result hattempt
      exact (hrunner.right w limit fuel result).mpr hattempt
    closed := by
      intro w limit fuel result hrunnerOutput
      exact (hrunner.right w limit fuel result).mp hrunnerOutput }

theorem protectedControllerStageAttemptExactFuelRunnerRouteConstruction_of_construction
    (h :
      PairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerConstruction) :
    ProtectedControllerStageAttemptExactFuelRunnerRouteConstruction := by
  intro attempt invoker hinvoker
  rcases h attempt invoker hinvoker with ⟨runner, hrunner⟩
  exact
    ⟨runner,
      protectedControllerStageAttemptExactFuelRunnerRoute_of_realizes
        hinvoker hrunner⟩

/-!
## Parser/simulator/extractor composition route
-/

structure ProtectedControllerStageAttemptExactFuelRunnerComponentRoute :
    Prop where
  parserClosedHandoff :
    PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodeClosedHandoffConstruction
  simulatorEquiv :
    FixedDescriptionBoundedSimulatorEquivConstruction
  extractorOutput :
    PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction
  forwardClosed :
    PairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerForwardClosedConstruction
  protectedConstruction :
    PairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerConstruction
  protectedRouteConstruction :
    ProtectedControllerStageAttemptExactFuelRunnerRouteConstruction

def ProtectedControllerStageAttemptExactFuelRunnerComponentRouteConstruction :
    Prop :=
  ProtectedControllerStageAttemptExactFuelRunnerComponentRoute

theorem protectedControllerStageAttemptExactFuelRunnerComponentRoute_of_components
    (hparser :
      PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodeClosedHandoffConstruction)
    (hsimulator :
      FixedDescriptionBoundedSimulatorEquivConstruction)
    (hextractor :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction) :
    ProtectedControllerStageAttemptExactFuelRunnerComponentRoute :=
  { parserClosedHandoff := hparser
    simulatorEquiv := hsimulator
    extractorOutput := hextractor
    forwardClosed :=
      pairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerForwardClosedConstruction_of_parser_equiv_extractor
        hparser hsimulator hextractor
    protectedConstruction :=
      pairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerConstruction_of_forward_closed
        (pairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerForwardClosedConstruction_of_parser_equiv_extractor
          hparser hsimulator hextractor)
    protectedRouteConstruction :=
      protectedControllerStageAttemptExactFuelRunnerRouteConstruction_of_construction
        (pairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerConstruction_of_forward_closed
          (pairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerForwardClosedConstruction_of_parser_equiv_extractor
            hparser hsimulator hextractor)) }

theorem protectedControllerStageAttemptExactFuelRunnerRouteConstruction_of_components
    (hparser :
      PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodeClosedHandoffConstruction)
    (hsimulator :
      FixedDescriptionBoundedSimulatorEquivConstruction)
    (hextractor :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction) :
    ProtectedControllerStageAttemptExactFuelRunnerRouteConstruction :=
  (protectedControllerStageAttemptExactFuelRunnerComponentRoute_of_components
    hparser hsimulator hextractor).protectedRouteConstruction

/-!
## Public finite-leaf aliases
-/

theorem pairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerConstruction_finite_leaf_route :
    PairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerConstruction :=
  pairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerConstruction_finite_leaf

theorem protectedControllerStageAttemptExactFuelRunnerRouteConstruction_finiteLeaf :
    ProtectedControllerStageAttemptExactFuelRunnerRouteConstruction :=
  protectedControllerStageAttemptExactFuelRunnerRouteConstruction_of_construction
    pairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerConstruction_finite_leaf

end Computability
end FoC
