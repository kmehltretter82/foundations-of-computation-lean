import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.PhaseAdapters
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.Basic
import FoC.Computability.Compiler.Core.FixedDescriptionBoundedSimulator.CodeRightShifted

set_option doc.verso true

/-!
# Bounded runner simulator scaffold adapters
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

namespace EncodedRewriters
namespace BoundedLayoutRunner

def FixedDescriptionBoundedSimulatorStepPhaseConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists simulateStep : Fragment,
      FixedDescriptionBoundedSimulatorPhaseRealizes
        (FixedDescriptionBoundedSimulatorHandoffTape Direction.right)
        FixedDescriptionBoundedSimulatorLayoutTape
        (fun L => SimulatorLayout.run D L.stage L)
        simulateStep

def FixedDescriptionBoundedSimulatorPaddedPhaseSpec_configRunner
    (D sim : MachineDescription) : Prop :=
  PaddedEquivEmitterSpec
    (fun L : SimulatorLayout =>
      Tape.input (FixedDescriptionBoundedSimulatorInput L))
    (FixedDescriptionBoundedSimulatorPaddedOutputTape D)
    (FixedDescriptionBoundedSimulatorCanonicalOutputTape D)
    sim

def FixedDescriptionBoundedSimulatorPaddedPhaseConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists sim : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedPhaseSpec_configRunner D sim

theorem fixedDescriptionBoundedSimulatorPaddedPhaseSpec_of_paddedSpec_configRunner
    {D sim : MachineDescription}
    (hsim : FixedDescriptionBoundedSimulatorPaddedSpec D sim) :
    FixedDescriptionBoundedSimulatorPaddedPhaseSpec_configRunner D sim := by
  constructor
  · exact hsim.left
  constructor
  · intro L
    simpa [FixedDescriptionBoundedSimulatorPaddedPhaseSpec_configRunner,
      HaltsWithTape,
      HaltsWithTapeIn,
      HaltsFromTape,
      HaltsFromTapeIn,
      initial] using hsim.right.left L
  · intro L
    exact
      FixedDescriptionBoundedSimulatorPaddedOutputTape_equiv_canonical D L

theorem fixedDescriptionBoundedSimulatorPaddedSpec_of_paddedPhaseSpec_configRunner
    {D sim : MachineDescription}
    (hsim : FixedDescriptionBoundedSimulatorPaddedPhaseSpec_configRunner D sim) :
    FixedDescriptionBoundedSimulatorPaddedSpec D sim := by
  constructor
  · exact hsim.left
  constructor
  · intro L
    rcases hsim.right.left L with ⟨n, hn⟩
    exact
      ⟨n, by
        simpa [FixedDescriptionBoundedSimulatorPaddedPhaseSpec_configRunner,
          HaltsWithTapeIn,
          HaltsFromTapeIn,
          initial] using hn⟩
  · intro L T hhalt
    have hfrom :
        sim.HaltsFromTape
          (Tape.input (FixedDescriptionBoundedSimulatorInput L)) T := by
      rcases hhalt with ⟨n, hn⟩
      exact
        ⟨n, by
          simpa [HaltsWithTapeIn,
            HaltsFromTapeIn,
            initial] using hn⟩
    exact
      haltsFromTape_functional_of_haltTransitionFree
        hsim.left.right hfrom (hsim.right.left L)

theorem fixedDescriptionBoundedSimulatorPaddedConstruction_of_paddedPhase_configRunner
    (hphase :
      FixedDescriptionBoundedSimulatorPaddedPhaseConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedConstruction := by
  intro D
  rcases hphase D with ⟨sim, hsim⟩
  exact
    ⟨sim,
      fixedDescriptionBoundedSimulatorPaddedSpec_of_paddedPhaseSpec_configRunner
        hsim⟩

theorem fixedDescriptionBoundedSimulatorEquivSpec_of_paddedPhase_configRunner
    {D sim : MachineDescription}
    (hsim : FixedDescriptionBoundedSimulatorPaddedPhaseSpec_configRunner D sim) :
    FixedDescriptionBoundedSimulatorEquivSpec D sim := by
  constructor
  · exact hsim.left
  constructor
  · intro L
    rcases PaddedEquivEmitterSpec.haltsFromTapeEquiv hsim L with
      ⟨Tactual, hactual, hactualEquiv⟩
    refine ⟨Tactual, ?_, hactualEquiv⟩
    rcases hactual with ⟨n, hn⟩
    exact
      ⟨n, by
        simpa [HaltsWithTapeIn,
          HaltsFromTapeIn,
          initial] using hn⟩
  · intro L T hhalt
    have hfrom :
        sim.HaltsFromTape
          (Tape.input (FixedDescriptionBoundedSimulatorInput L)) T := by
      rcases hhalt with ⟨n, hn⟩
      exact
        ⟨n, by
          simpa [HaltsWithTapeIn,
            HaltsFromTapeIn,
            initial] using hn⟩
    exact
      PaddedEquivEmitterSpec.closedFromTapeEquiv hsim L T hfrom

theorem fixedDescriptionBoundedSimulatorEquivConstruction_of_paddedPhase_configRunner
    (hphase :
      FixedDescriptionBoundedSimulatorPaddedPhaseConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorEquivConstruction := by
  intro D
  rcases hphase D with ⟨sim, hsim⟩
  exact
    ⟨sim,
      fixedDescriptionBoundedSimulatorEquivSpec_of_paddedPhase_configRunner
        hsim⟩

theorem fixedDescriptionBoundedSimulatorReturnFromRightPhaseRealizes_configRunner :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      (FixedDescriptionBoundedSimulatorHandoffTape Direction.right)
      FixedDescriptionBoundedSimulatorLayoutTape
      id
      (Fragment.handoff Direction.left) :=
  fixedDescriptionBoundedSimulatorReturnFromRightHandoffPhaseRealizes

theorem fixedDescriptionBoundedSimulatorSkeletonPhaseConstruction_of_stepPhase_configRunner
    (hstep :
      FixedDescriptionBoundedSimulatorStepPhaseConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorSkeletonPhaseConstruction := by
  intro D
  rcases hstep D with ⟨simulateStep, hsimulateStep⟩
  let S : FixedSimulatorTableSkeleton :=
    { decodeLayout := Fragment.halt
      simulateStep := simulateStep
      repeatControl := Fragment.handoff Direction.left
      emitLayout := Fragment.handoff Direction.left
      decodeLayout_wellFormed :=
        Fragment.halt_wellFormed
      simulateStep_wellFormed := hsimulateStep.left
      repeatControl_wellFormed :=
        Fragment.handoff_wellFormed Direction.left
      emitLayout_wellFormed :=
        Fragment.handoff_wellFormed Direction.left }
  refine
    ⟨S, Direction.right,
      FixedDescriptionBoundedSimulatorPhaseTargets.canonical D, ?_⟩
  refine
    { decodeLayout := ?_
      simulateStep := ?_
      repeatControl := ?_
      emitLayout := ?_ }
  · simpa [S, FixedDescriptionBoundedSimulatorPhaseTargets.canonical] using
      fixedDescriptionBoundedSimulatorHaltPhaseRealizes
        FixedDescriptionBoundedSimulatorLayoutTape
  · simpa [S, FixedDescriptionBoundedSimulatorPhaseTargets.canonical] using
      hsimulateStep
  · simpa [S, FixedDescriptionBoundedSimulatorPhaseTargets.canonical] using
      fixedDescriptionBoundedSimulatorReturnFromRightPhaseRealizes_configRunner
  · simpa [S, FixedDescriptionBoundedSimulatorPhaseTargets.canonical] using
      fixedDescriptionBoundedSimulatorReturnFromRightPhaseRealizes_configRunner

def FixedDescriptionBoundedSimulatorPaddedExactShapeSpec_configRunner
    (D sim : MachineDescription) : Prop :=
  sim.SubroutineReady ∧
    forall L : SimulatorLayout,
      sim.HaltsWithTape
        (FixedDescriptionBoundedSimulatorInput L)
        (FixedDescriptionBoundedSimulatorPaddedOutputTape D L)

def FixedDescriptionBoundedSimulatorPaddedExactShapeConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists sim : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedExactShapeSpec_configRunner D sim

def FixedDescriptionBoundedSimulatorPaddedEmitterExactShapeSpec_configRunner
    (D emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall L : SimulatorLayout,
      emitter.HaltsWithTape
        (SimulatorLayout.asBoolInput L)
        (FixedDescriptionBoundedSimulatorPaddedOutputTape D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterExactShapeConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists emitter : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterExactShapeSpec_configRunner
        D emitter

def FixedDescriptionBoundedSimulatorPaddedParserEmitterConstruction_configRunner :
    Prop :=
  CommonGround.SimulatorLayouts.ClosedRecognizerConstruction ∧
    FixedDescriptionBoundedSimulatorPaddedEmitterExactShapeConstruction_configRunner

def FixedDescriptionBoundedSimulatorPaddedParserEmitterRunner
    (parser emitter : MachineDescription) : MachineDescription :=
  seqSubroutine parser emitter Direction.left

theorem fixedDescriptionBoundedSimulatorPaddedExactShapeSpec_of_parser_emitter_configRunner
    {D parser emitter : MachineDescription}
    (hparser :
      CommonGround.SimulatorLayouts.ClosedRecognizerSpec parser)
    (hemitter :
      FixedDescriptionBoundedSimulatorPaddedEmitterExactShapeSpec_configRunner
        D emitter) :
    FixedDescriptionBoundedSimulatorPaddedExactShapeSpec_configRunner D
      (FixedDescriptionBoundedSimulatorPaddedParserEmitterRunner
        parser emitter) := by
  have hrunnerReady :
      (FixedDescriptionBoundedSimulatorPaddedParserEmitterRunner
        parser emitter).SubroutineReady :=
    seqSubroutine_subroutineReady hparser.left hemitter.left
  constructor
  · exact hrunnerReady
  · intro L
    have hparserRun :
        parser.HaltsWithTape
          (FixedDescriptionBoundedSimulatorInput L)
          (CommonGround.SimulatorLayouts.handoffTape L) := by
      simpa [FixedDescriptionBoundedSimulatorInput,
        CommonGround.SimulatorLayouts.bits,
        CommonGround.LayoutTapes.Bits,
        CommonGround.SimulatorLayouts.encode] using
        hparser.right.left L
    have hemitterRun :
        emitter.HaltsWithTape
          (SimulatorLayout.asBoolInput L)
          (FixedDescriptionBoundedSimulatorPaddedOutputTape D L) :=
      hemitter.right L
    rcases runConfig_eq_halt_of_haltsWithTape
      hemitterRun with ⟨n, hn⟩
    exact
      seqSubroutine_haltsWithTape_of_haltsWithTape
        hparser.left hemitter.left hparserRun
        ⟨n, by
          simpa [
            CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape
              L] using hn⟩

theorem fixedDescriptionBoundedSimulatorPaddedExactShapeConstruction_of_parserEmitter_configRunner
    (h :
      FixedDescriptionBoundedSimulatorPaddedParserEmitterConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedExactShapeConstruction_configRunner := by
  intro D
  rcases h.left with ⟨parser, hparser⟩
  rcases h.right D with ⟨emitter, hemits⟩
  exact
    ⟨FixedDescriptionBoundedSimulatorPaddedParserEmitterRunner
        parser emitter,
      fixedDescriptionBoundedSimulatorPaddedExactShapeSpec_of_parser_emitter_configRunner
        hparser hemits⟩

theorem fixedDescriptionBoundedSimulatorPaddedSpec_of_exactShape_configRunner
    {D sim : MachineDescription}
    (hsim :
      FixedDescriptionBoundedSimulatorPaddedExactShapeSpec_configRunner D sim) :
    FixedDescriptionBoundedSimulatorPaddedSpec D sim := by
  constructor
  · exact hsim.left
  constructor
  · intro L
    exact hsim.right L
  · intro L T hhalt
    exact
      haltsWithTape_functional_of_haltTransitionFree
        hsim.left.right hhalt (hsim.right L)

theorem fixedDescriptionBoundedSimulatorPaddedConstruction_of_exactShape_configRunner
    (hexact :
      FixedDescriptionBoundedSimulatorPaddedExactShapeConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedConstruction := by
  intro D
  rcases hexact D with ⟨sim, hsim⟩
  exact
    ⟨sim,
      fixedDescriptionBoundedSimulatorPaddedSpec_of_exactShape_configRunner
        hsim⟩

theorem fixedDescriptionBoundedSimulatorPaddedPhaseSpec_of_exactShape_configRunner
    {D sim : MachineDescription}
    (hsim :
      FixedDescriptionBoundedSimulatorPaddedExactShapeSpec_configRunner D sim) :
    FixedDescriptionBoundedSimulatorPaddedPhaseSpec_configRunner D sim := by
  constructor
  · exact hsim.left
  constructor
  · intro L
    rcases hsim.right L with ⟨n, hn⟩
    exact
      ⟨n, by
        simpa [FixedDescriptionBoundedSimulatorPaddedPhaseSpec_configRunner,
          HaltsWithTapeIn,
          HaltsFromTapeIn,
          initial] using hn⟩
  · intro L
    exact
      FixedDescriptionBoundedSimulatorPaddedOutputTape_equiv_canonical
        D L

theorem fixedDescriptionBoundedSimulatorPaddedPhaseConstruction_of_exactShape_configRunner
    (hexact :
      FixedDescriptionBoundedSimulatorPaddedExactShapeConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedPhaseConstruction_configRunner := by
  intro D
  rcases hexact D with ⟨sim, hsim⟩
  exact
    ⟨sim,
      fixedDescriptionBoundedSimulatorPaddedPhaseSpec_of_exactShape_configRunner
        hsim⟩

def fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner :
    Word Bool :=
  encodeCodeSymbolAsInput MachineCodeSymbol.header

def FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner :
    MachineDescription where
  stateCount := 100
  start := 30
  halt := 99
  transitions :=
    [ keepMove 30 (some false) Direction.right 31
    , keepMove 31 (some false) Direction.right 32
    , keepMove 32 (some false) Direction.right 33
    , keepMove 33 (some false) Direction.right 40
    , keepMove 40 (some false) Direction.left 99
    , keepMove 40 (some true) Direction.left 99
    ]

theorem fixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_wellFormed_configRunner :
    FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l :=
        FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.transitions)
      (stateCount :=
        FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l :=
        FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.transitions)
      (by decide)

theorem fixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_haltTransitionFree_configRunner :
    FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.HaltTransitionFree :=
  transition_notFrom_of_all
    (l :=
      FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.transitions)
    (state :=
      FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.halt)
    (by decide)

theorem fixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_subroutineReady_configRunner :
    FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.SubroutineReady :=
  ⟨fixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_wellFormed_configRunner,
    fixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_haltTransitionFree_configRunner⟩

def fixedDescriptionBoundedSimulatorHeaderPrefixHandoffConfigWithBase_configRunner
    (baseLeft : List (Option Bool)) (suffixBits : Word Bool) :
    Configuration :=
  { state :=
      FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.halt
    tape :=
      Tape.move Direction.left
        (DovetailInitialLayoutInitializer.tapeAtCells
          (List.append
            (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.reverse.map
              some)
            baseLeft)
          (suffixBits.map some)) }

theorem fixedDescriptionBoundedSimulatorHeaderPrefix_run_raw_to_handoff_withBase_configRunner
    (baseLeft : List (Option Bool)) (b : Bool)
    (suffixTail : Word Bool) :
    exists steps : Nat,
      FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.runConfig
          steps
          (DovetailInitialLayoutInitializer.config
            FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.start
            baseLeft
            (List.append
              (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.map
                some)
              (some b :: suffixTail.map some))) =
        fixedDescriptionBoundedSimulatorHeaderPrefixHandoffConfigWithBase_configRunner
          baseLeft (b :: suffixTail) := by
  refine ⟨5, ?_⟩
  cases b <;>
    simp [FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner,
      fixedDescriptionBoundedSimulatorHeaderPrefixHandoffConfigWithBase_configRunner,
      fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
      DovetailInitialLayoutInitializer.config,
      DovetailInitialLayoutInitializer.tapeAtCells, keepMove, runConfig,
      stepConfig,
      lookupTransition, Matches, transition, encodeCodeSymbolAsInput,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

def FixedDescriptionBoundedSimulatorHeaderPrefixScannerSpec_configRunner
    (scanner : MachineDescription) : Prop :=
  scanner.SubroutineReady ∧
    forall (baseLeft : List (Option Bool)) (b : Bool)
      (suffixTail : Word Bool),
      scanner.HaltsFromTape
        (DovetailInitialLayoutInitializer.tapeAtCells baseLeft
          (List.append
            (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.map
              some)
            (some b :: suffixTail.map some)))
        (fixedDescriptionBoundedSimulatorHeaderPrefixHandoffConfigWithBase_configRunner
          baseLeft (b :: suffixTail)).tape

def FixedDescriptionBoundedSimulatorHeaderPrefixScannerConstruction_configRunner :
    Prop :=
  exists scanner : MachineDescription,
    FixedDescriptionBoundedSimulatorHeaderPrefixScannerSpec_configRunner
      scanner

theorem fixedDescriptionBoundedSimulatorHeaderPrefixScannerConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorHeaderPrefixScannerConstruction_configRunner := by
  refine
    ⟨FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner,
      ?_⟩
  constructor
  · exact
      fixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_subroutineReady_configRunner
  · intro baseLeft b suffixTail
    rcases
        fixedDescriptionBoundedSimulatorHeaderPrefix_run_raw_to_handoff_withBase_configRunner
          baseLeft b suffixTail with
      ⟨steps, hsteps⟩
    exact
      ⟨steps, by
        constructor
        · simpa [HaltsFromTapeIn] using
            congrArg Configuration.state hsteps
        · simpa [HaltsFromTapeIn] using
            congrArg Configuration.tape hsteps⟩

/--
Concrete finite-machine leaf for the simulator-layout parser primitive.  The
machine must implement {name}`SimulatorLayout.normalizeCodePrimitive`: reject
malformed code words and, for a complete simulator layout, emit the same
canonical simulator-layout code one cell to the right.  The header-prefix block
above handles the first code symbol; the remaining parser work is to compose it
with the bool-word, stage, configuration, and hit-flag field scanners.
-/
theorem fixedDescriptionBoundedSimulatorPaddedParserPrimitiveConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorCodeRightShiftedParserPrimitiveConstruction := by
  sorry

/--
Concrete finite-machine leaf for parsing complete canonical simulator layouts.
The parser halts on the standard one-cell-left handoff tape used by downstream
emitter phases.
-/
theorem fixedDescriptionBoundedSimulatorPaddedParserConstruction_scaffold_configRunner :
    CommonGround.SimulatorLayouts.ClosedRecognizerConstruction :=
  fixedDescriptionBoundedSimulatorCodeRightShiftedParserConstruction_of_primitive
    fixedDescriptionBoundedSimulatorPaddedParserPrimitiveConstruction_scaffold_configRunner

/--
Concrete finite-machine leaf for the padded fixed-description simulator
emitter.  On an already validated simulator layout tape, it must run the fixed
description for the encoded stage bound, emit the updated simulator-layout code
at the left edge, and leave the old simulator-layout window as trailing blank
padding.
-/
theorem fixedDescriptionBoundedSimulatorPaddedEmitterExactShapeConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterExactShapeConstruction_configRunner := by
  intro D
  sorry

theorem fixedDescriptionBoundedSimulatorPaddedParserEmitterConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorPaddedParserEmitterConstruction_configRunner :=
  ⟨fixedDescriptionBoundedSimulatorPaddedParserConstruction_scaffold_configRunner,
    fixedDescriptionBoundedSimulatorPaddedEmitterExactShapeConstruction_scaffold_configRunner⟩

theorem fixedDescriptionBoundedSimulatorPaddedExactShapeConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorPaddedExactShapeConstruction_configRunner :=
  fixedDescriptionBoundedSimulatorPaddedExactShapeConstruction_of_parserEmitter_configRunner
    fixedDescriptionBoundedSimulatorPaddedParserEmitterConstruction_scaffold_configRunner

/--
Finite-machine leaf for the config-runner fixed-description simulators.

The exact right-handoff skeleton target has a context-length shrink obstruction;
see {lit}`LEAN_COUNTEREXAMPLE_OVERVIEW.md` for the archived design note.  The
live config-runner assembly should use this padded target, whose output is
equivalent to the canonical simulator layout while preserving enough blank
window to avoid a forced shrink.
-/
theorem fixedDescriptionBoundedSimulatorPaddedConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorPaddedConstruction :=
  fixedDescriptionBoundedSimulatorPaddedConstruction_of_exactShape_configRunner
    fixedDescriptionBoundedSimulatorPaddedExactShapeConstruction_scaffold_configRunner

theorem fixedDescriptionBoundedSimulatorPaddedPhaseConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorPaddedPhaseConstruction_configRunner :=
  fixedDescriptionBoundedSimulatorPaddedPhaseConstruction_of_exactShape_configRunner
    fixedDescriptionBoundedSimulatorPaddedExactShapeConstruction_scaffold_configRunner

theorem fixedDescriptionBoundedSimulatorEquivConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorEquivConstruction :=
  fixedDescriptionBoundedSimulatorEquivConstruction_of_paddedPhase_configRunner
    fixedDescriptionBoundedSimulatorPaddedPhaseConstruction_scaffold_configRunner

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
