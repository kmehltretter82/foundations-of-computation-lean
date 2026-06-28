import FoC.Computability.Compiler.Core.CommonGround.SeqComposition
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.PhaseAdapters
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.Basic
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.Composition
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.ConfigurationClosed
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

open CanonicalLayouts.DovetailLayoutScanner
open CanonicalLayouts.DovetailStagePrefix
open CommonGround.SeqComposition

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

def FixedDescriptionBoundedSimulatorPaddedParserEquivSpec_configRunner
    (parser : MachineDescription) : Prop :=
  parser.SubroutineReady ∧
    (forall L : SimulatorLayout,
      parser.HaltsWithTapeEquiv
        (FixedDescriptionBoundedSimulatorInput L)
        (CommonGround.SimulatorLayouts.handoffTape L)) ∧
      forall L : SimulatorLayout,
      forall T : Tape Bool,
        parser.HaltsWithTape (FixedDescriptionBoundedSimulatorInput L) T ->
          Tape.Equiv T (CommonGround.SimulatorLayouts.handoffTape L)

def FixedDescriptionBoundedSimulatorPaddedParserEquivConstruction_configRunner :
    Prop :=
  exists parser : MachineDescription,
    FixedDescriptionBoundedSimulatorPaddedParserEquivSpec_configRunner
      parser

def FixedDescriptionBoundedSimulatorPaddedParserEquivEmitterConstruction_configRunner :
    Prop :=
  FixedDescriptionBoundedSimulatorPaddedParserEquivConstruction_configRunner ∧
    FixedDescriptionBoundedSimulatorPaddedEmitterExactShapeConstruction_configRunner

theorem fixedDescriptionBoundedSimulatorEquivSpec_of_parserEquiv_emitter_configRunner
    {D parser emitter : MachineDescription}
    (hparser :
      FixedDescriptionBoundedSimulatorPaddedParserEquivSpec_configRunner
        parser)
    (hemitter :
      FixedDescriptionBoundedSimulatorPaddedEmitterExactShapeSpec_configRunner
        D emitter) :
    FixedDescriptionBoundedSimulatorEquivSpec D
      (FixedDescriptionBoundedSimulatorPaddedParserEmitterRunner
        parser emitter) := by
  have hrunnerReady :
      (FixedDescriptionBoundedSimulatorPaddedParserEmitterRunner
        parser emitter).SubroutineReady :=
    seqSubroutine_subroutineReady hparser.left hemitter.left
  constructor
  · exact hrunnerReady
  constructor
  · intro L
    rcases hparser.right.left L with
      ⟨Tmid, hparserRun, hTmid⟩
    have hbridge :
        Tape.Equiv
          (Tape.move Direction.left Tmid)
          (Tape.input (SimulatorLayout.asBoolInput L)) := by
      exact
        Tape.Equiv.trans
          (Tape.Equiv.move hTmid Direction.left)
          (by
            rw [CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape]
            exact Tape.Equiv.refl _)
    have hemitterFrom :
        emitter.HaltsFromTape
          (Tape.input (SimulatorLayout.asBoolInput L))
          (FixedDescriptionBoundedSimulatorPaddedOutputTape D L) := by
      rcases hemitter.right L with ⟨n, hn⟩
      exact
        ⟨n, by
          simpa [HaltsWithTapeIn, HaltsFromTapeIn,
            initial] using hn⟩
    rcases
        HaltsFromTapeEquiv_of_input_equiv
          (D := emitter)
          (Tape.Equiv.symm hbridge) hemitterFrom with
      ⟨Tactual, hemitterActual, hTactual⟩
    have hseq :
        (FixedDescriptionBoundedSimulatorPaddedParserEmitterRunner
          parser emitter).HaltsWithTape
          (FixedDescriptionBoundedSimulatorInput L) Tactual :=
      seqSubroutine_haltsWithTape_of_haltsWithTape
        hparser.left hemitter.left hparserRun
        (runConfig_eq_halt_of_haltsFromTape hemitterActual)
    exact
      ⟨Tactual, hseq,
        Tape.Equiv.trans hTactual
          (FixedDescriptionBoundedSimulatorPaddedOutputTape_equiv_canonical
            D L)⟩
  · intro L T hhalt
    rcases
        seqSubroutine_haltsWithTape_inv
          hparser.left hemitter.left hhalt with
      ⟨Tmid, hparserRun, hemitterReach⟩
    have hTmid :
        Tape.Equiv Tmid
          (CommonGround.SimulatorLayouts.handoffTape L) :=
      hparser.right.right L Tmid hparserRun
    have hbridge :
        Tape.Equiv
          (Tape.move Direction.left Tmid)
          (Tape.input (SimulatorLayout.asBoolInput L)) := by
      exact
        Tape.Equiv.trans
          (Tape.Equiv.move hTmid Direction.left)
          (by
            rw [CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape]
            exact Tape.Equiv.refl _)
    rcases hemitterReach with ⟨n, hn⟩
    have hemitterRun :
        emitter.HaltsFromTape (Tape.move Direction.left Tmid) T :=
      ⟨n, by
        constructor
        · simpa [HaltsFromTapeIn] using
            congrArg Configuration.state hn
        · simpa [HaltsFromTapeIn] using
            congrArg Configuration.tape hn⟩
    rcases
        HaltsFromTapeEquiv_of_input_equiv
          (D := emitter) hbridge hemitterRun with
      ⟨Tactual, hemitterActual, hTactual⟩
    have hemitterForward :
        emitter.HaltsFromTape
          (Tape.input (SimulatorLayout.asBoolInput L))
          (FixedDescriptionBoundedSimulatorPaddedOutputTape D L) := by
      rcases hemitter.right L with ⟨nForward, hforward⟩
      exact
        ⟨nForward, by
          simpa [HaltsWithTapeIn, HaltsFromTapeIn,
            initial] using hforward⟩
    have hTactual_eq :
        Tactual = FixedDescriptionBoundedSimulatorPaddedOutputTape D L :=
      haltsFromTape_functional_of_haltTransitionFree
        hemitter.left.right hemitterActual hemitterForward
    rw [hTactual_eq] at hTactual
    exact
      Tape.Equiv.trans (Tape.Equiv.symm hTactual)
        (FixedDescriptionBoundedSimulatorPaddedOutputTape_equiv_canonical
          D L)

theorem fixedDescriptionBoundedSimulatorEquivConstruction_of_parserEquivEmitter_configRunner
    (h :
      FixedDescriptionBoundedSimulatorPaddedParserEquivEmitterConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorEquivConstruction := by
  intro D
  rcases h.left with ⟨parser, hparser⟩
  rcases h.right D with ⟨emitter, hemits⟩
  exact
    ⟨FixedDescriptionBoundedSimulatorPaddedParserEmitterRunner
        parser emitter,
      fixedDescriptionBoundedSimulatorEquivSpec_of_parserEquiv_emitter_configRunner
        hparser hemits⟩

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
    have hemitterFrom :
        emitter.HaltsFromTape
          (Tape.input (SimulatorLayout.asBoolInput L))
          (FixedDescriptionBoundedSimulatorPaddedOutputTape D L) := by
      rcases hemitterRun with ⟨n, hn⟩
      exact ⟨n, by
        simpa [HaltsWithTapeIn, HaltsFromTapeIn] using hn⟩
    exact
      seqSubroutine_haltsWithTape_of_haltsWithTape_eq
        hparser.left hemitter.left hparserRun
        (CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape L)
        hemitterFrom

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

theorem fixedDescriptionBoundedSimulatorHeaderPrefixHandoffConfigWithBase_move_right_configRunner
    (baseLeft : List (Option Bool)) (b : Bool)
    (suffixTail : Word Bool) :
    Tape.move Direction.right
        (fixedDescriptionBoundedSimulatorHeaderPrefixHandoffConfigWithBase_configRunner
          baseLeft (b :: suffixTail)).tape =
      DovetailInitialLayoutInitializer.tapeAtCells
        (List.append
          (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.reverse.map
            some)
          baseLeft)
        ((b :: suffixTail).map some) := by
  cases b <;>
    simp [fixedDescriptionBoundedSimulatorHeaderPrefixHandoffConfigWithBase_configRunner,
      fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
      encodeCodeSymbolAsInput,
      DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]

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
Concrete scanner for the configuration field followed by the final simulator
hit flag.
-/
def FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner :
    MachineDescription :=
  seqSubroutine
    ConfigurationSuffixScannerDescription
    BoolFinalScannerDescription
    Direction.right

theorem fixedDescriptionBoundedSimulatorConfigHitScannerDescription_subroutineReady_configRunner :
    FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner.SubroutineReady :=
  seqSubroutine_subroutineReady
    configurationSuffixScannerDescription_subroutineReady
    boolFinalScannerDescription_subroutineReady

theorem run_fixedDescriptionBoundedSimulatorConfigHit_raw_to_handoff_withBase_configRunner
    (cfg : Configuration) (hit : Bool)
    (baseLeft : List (Option Bool)) :
    exists steps : Nat,
      FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner.runConfig
          steps
          { state :=
              FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner.start
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells baseLeft
                ((configurationFieldBits cfg
                  (boolFieldBits hit [])).map some) } =
        { state :=
            FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner.halt
          tape :=
            (boolFinalHandoffConfigWithBase hit
              (configurationRestoredLeftWithBase cfg baseLeft)).tape } := by
  rcases cellCodeBits_cons_false (some hit) with ⟨hitTail, hhitTail⟩
  rcases run_configurationSuffix_raw_to_handoff_withBase
      cfg baseLeft hitTail with
    ⟨configSteps, hconfig⟩
  let TmidTape : Tape Bool :=
    (cellListCanonicalHandoffConfigWithBase cfg.tape.right
      (List.append ((cellCodeBits cfg.tape.head).reverse.map some)
        (cellListCanonicalRestoredLeftWithBase cfg.tape.left
          (List.append ((stageNatBits cfg.state).reverse.map some)
            baseLeft)))
      (false :: hitTail)).tape
  have hArun :
      ConfigurationSuffixScannerDescription.runConfig configSteps
          { state := ConfigurationSuffixScannerDescription.start
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells baseLeft
                ((configurationFieldBits cfg
                  (boolFieldBits hit [])).map some) } =
        { state := ConfigurationSuffixScannerDescription.halt
          tape := TmidTape } := by
    rw [show
        ((configurationFieldBits cfg
          (boolFieldBits hit [])).map some) =
          (configurationFieldBits cfg (false :: hitTail)).map some by
      simp [boolFieldBits, cellFieldBits, hhitTail]]
    simpa [TmidTape] using hconfig
  have hBReach :
      exists nB : Nat,
        BoolFinalScannerDescription.runConfig nB
            { state := BoolFinalScannerDescription.start
              tape := Tape.move Direction.right TmidTape } =
          { state := BoolFinalScannerDescription.halt
            tape :=
              (boolFinalHandoffConfigWithBase hit
                (configurationRestoredLeftWithBase cfg baseLeft)).tape } := by
    rcases run_boolFinal_raw_to_handoff_withBase
        hit (configurationRestoredLeftWithBase cfg baseLeft) with
      ⟨finalSteps, hfinal⟩
    have hmove :
        Tape.move Direction.right TmidTape =
          DovetailInitialLayoutInitializer.tapeAtCells
            (configurationRestoredLeftWithBase cfg baseLeft)
            ((cellCodeBits (some hit)).map some) := by
      have hraw :
          Tape.move Direction.right TmidTape =
            DovetailInitialLayoutInitializer.tapeAtCells
              (configurationRestoredLeftWithBase cfg baseLeft)
              ((false :: hitTail).map some) := by
        simpa [TmidTape, configurationRestoredLeftWithBase] using
          cellListCanonicalHandoffConfigWithBase_move_right
            cfg.tape.right
            (List.append
              ((cellCodeBits cfg.tape.head).reverse.map some)
              (cellListCanonicalRestoredLeftWithBase cfg.tape.left
                (List.append
                  ((stageNatBits cfg.state).reverse.map some)
                  baseLeft)))
            false hitTail
      rw [hraw]
      have hhitCells :
          (false :: hitTail).map some =
            (cellCodeBits (some hit)).map some := by
        simpa using congrArg (fun bits => bits.map some) hhitTail.symm
      simp [hhitCells]
    exact
      runConfig_reaches_from_move_eq
        (B := BoolFinalScannerDescription)
        (handoffMove := Direction.right)
        hmove
        (by simpa [DovetailInitialLayoutInitializer.config] using hfinal)
  simpa [FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner,
    TmidTape] using
      seqSubroutine_runConfig_exists
        (A := ConfigurationSuffixScannerDescription)
        (B := BoolFinalScannerDescription)
        (handoffMove := Direction.right)
        configurationSuffixScannerDescription_subroutineReady
        boolFinalScannerDescription_subroutineReady
        hArun hBReach

theorem fixedDescriptionBoundedSimulatorConfigHitScannerDescription_runConfig_code_inv_configRunner
    (baseLeft : List (Option Bool)) (code : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner.runConfig
          n
          (DovetailInitialLayoutInitializer.config
            FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner.start
            baseLeft
            ((encodeCodeWordAsInput code).map some)) =
        { state :=
            FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner.halt
          tape := Tout }) :
    exists cfg : Configuration,
    exists hit : Bool,
    exists baseAfter : List (Option Bool),
      code = encodeConfigurationAppend cfg (encodeBoolAppend hit []) ∧
        Tape.move Direction.right Tout =
          DovetailInitialLayoutInitializer.tapeAtCells baseAfter [] := by
  have hseq :
      (seqSubroutine
        ConfigurationSuffixScannerDescription
        BoolFinalScannerDescription
        Direction.right).runConfig n
          (DovetailInitialLayoutInitializer.config
            (seqSubroutine
              ConfigurationSuffixScannerDescription
              BoolFinalScannerDescription
              Direction.right).start
            baseLeft
            ((encodeCodeWordAsInput code).map some)) =
        { state :=
            (seqSubroutine
              ConfigurationSuffixScannerDescription
              BoolFinalScannerDescription
              Direction.right).halt
          tape := Tout } := by
    simpa [FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner]
      using h
  rcases
      seqSubroutine_runConfig_inv
        (A := ConfigurationSuffixScannerDescription)
        (B := BoolFinalScannerDescription)
        (handoffMove := Direction.right)
        configurationSuffixScannerDescription_subroutineReady
        boolFinalScannerDescription_subroutineReady
        hseq with
    ⟨Tcfg, hcfg, hhit⟩
  rcases hcfg with ⟨nCfg, hcfgRun, _hcfgFirst⟩
  rcases
      configurationSuffixScannerDescription_runConfig_code_handoff
        baseLeft code
        (by simpa [DovetailInitialLayoutInitializer.config] using
          hcfgRun) with
    ⟨cfg, suffix, baseAfterCfg, hcode, hcfgMove⟩
  rcases hhit with ⟨nHit, hhitRun⟩
  have hhitCodeRun :
      BoolFinalScannerDescription.runConfig nHit
          (DovetailInitialLayoutInitializer.config
            BoolFinalScannerDescription.start baseAfterCfg
            ((encodeCodeWordAsInput suffix).map some)) =
        { state := BoolFinalScannerDescription.halt
          tape := Tout } := by
    simpa [DovetailInitialLayoutInitializer.config, hcfgMove] using
      hhitRun
  rcases
      boolFinalScannerDescription_runConfig_code_terminal_inv
        baseAfterCfg suffix hhitCodeRun with
    ⟨hit, hsuffix, hmove⟩
  refine ⟨cfg, hit, _, ?_, hmove⟩
  rw [hcode, hsuffix]

theorem fixedDescriptionBoundedSimulatorBoolFinalHandoffConfigWithBase_normalizedOutput_configRunner
    (hit : Bool) (baseLeft : List (Option Bool)) :
    Tape.normalizedOutput
        (boolFinalHandoffConfigWithBase hit baseLeft).tape =
      List.append (baseLeft.reverse.filterMap (fun cell => cell))
        (cellCodeBits (some hit)) := by
  cases hit <;>
    simp [boolFinalHandoffConfigWithBase, cellCodeBits,
      encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.normalizedOutput, Tape.cells,
      List.filterMap_append, List.append_assoc]

theorem fixedDescriptionBoundedSimulatorConfigurationRestoredLeftWithBase_reverse_filterMap_configRunner
    (cfg : Configuration) (baseLeft : List (Option Bool)) :
    (configurationRestoredLeftWithBase cfg baseLeft).reverse.filterMap
        (fun cell => cell) =
      List.append (baseLeft.reverse.filterMap (fun cell => cell))
        (configurationFieldBits cfg []) := by
  rw [← configurationRestoredBitsRev_map_some_withBase cfg baseLeft]
  simp [Function.comp_def, List.reverse_append, List.filterMap_append,
    configurationRestoredBitsRev_reverse]

theorem fixedDescriptionBoundedSimulatorCellListCanonicalRestoredLeftWithBase_reverse_filterMap_configRunner
    (cells baseLeft : List (Option Bool)) :
    (cellListCanonicalRestoredLeftWithBase cells baseLeft).reverse.filterMap
        (fun cell => cell) =
      List.append (baseLeft.reverse.filterMap (fun cell => cell))
        (cellListFieldBits cells []) := by
  rw [← cellListCanonicalRestoredBitsRev_map_some_withBase cells baseLeft]
  simp [Function.comp_def, List.reverse_append, List.filterMap_append,
    cellListCanonicalRestoredBitsRev_reverse]

/--
Concrete scanner for the stage, configuration, and final hit fields of a
simulator layout.
-/
def FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner :
    MachineDescription :=
  seqSubroutine
    NonemptyNatSuffixScannerDescription
    FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner
    Direction.right

theorem fixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_subroutineReady_configRunner :
    FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner.SubroutineReady :=
  seqSubroutine_subroutineReady
    nonemptyNatSuffixScannerDescription_subroutineReady
    fixedDescriptionBoundedSimulatorConfigHitScannerDescription_subroutineReady_configRunner

theorem run_fixedDescriptionBoundedSimulatorStageConfigHit_raw_to_handoff_withBase_configRunner
    (stage : Nat) (cfg : Configuration) (hit : Bool)
    (baseLeft : List (Option Bool)) :
    exists steps : Nat,
      FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner.runConfig
          steps
          { state :=
              FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner.start
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells baseLeft
                ((List.append (stageNatBits stage)
                  (configurationFieldBits cfg
                    (boolFieldBits hit []))).map some) } =
        { state :=
            FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner.halt
          tape :=
            (boolFinalHandoffConfigWithBase hit
              (configurationRestoredLeftWithBase cfg
                (List.append ((stageNatBits stage).reverse.map some)
                  baseLeft))).tape } := by
  rcases configurationFieldBits_cons_false cfg (boolFieldBits hit []) with
    ⟨cfgTail, hcfgTail⟩
  rcases run_nonemptyNatSuffix_raw_to_handoff_withBase
      stage baseLeft false cfgTail with
    ⟨stageSteps, hstage⟩
  let TmidTape : Tape Bool :=
    (nonemptyNatSuffixHandoffConfigWithBase
      stage baseLeft (false :: cfgTail)).tape
  let baseAfterStage : List (Option Bool) :=
    List.append ((stageNatBits stage).reverse.map some) baseLeft
  have hArun :
      NonemptyNatSuffixScannerDescription.runConfig stageSteps
          { state := NonemptyNatSuffixScannerDescription.start
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells baseLeft
                ((List.append (stageNatBits stage)
                  (configurationFieldBits cfg
                    (boolFieldBits hit []))).map some) } =
        { state := NonemptyNatSuffixScannerDescription.halt
          tape := TmidTape } := by
    rw [show
        (List.append (stageNatBits stage)
          (configurationFieldBits cfg
            (boolFieldBits hit []))).map some =
          (List.append (stageNatBits stage)
            (false :: cfgTail)).map some by
      rw [hcfgTail]]
    simpa [TmidTape] using hstage
  have hBReach :
      exists nB : Nat,
        FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner.runConfig
            nB
            { state :=
                FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner.start
              tape := Tape.move Direction.right TmidTape } =
          { state :=
              FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner.halt
            tape :=
              (boolFinalHandoffConfigWithBase hit
                (configurationRestoredLeftWithBase cfg baseAfterStage)).tape } := by
    rcases
        run_fixedDescriptionBoundedSimulatorConfigHit_raw_to_handoff_withBase_configRunner
          cfg hit baseAfterStage with
      ⟨configSteps, hconfig⟩
    have hmove :
        Tape.move Direction.right TmidTape =
          DovetailInitialLayoutInitializer.tapeAtCells baseAfterStage
            ((configurationFieldBits cfg (boolFieldBits hit [])).map some) := by
      have hraw :
          Tape.move Direction.right TmidTape =
            DovetailInitialLayoutInitializer.tapeAtCells baseAfterStage
              ((false :: cfgTail).map some) := by
        simpa [TmidTape, baseAfterStage] using
          nonemptyNatSuffixHandoffConfigWithBase_move_right
            stage baseLeft false cfgTail
      rw [hraw]
      have hcfgCells :
          (false :: cfgTail).map some =
            (configurationFieldBits cfg (boolFieldBits hit [])).map some := by
        simpa using congrArg (fun bits => bits.map some) hcfgTail.symm
      simp [hcfgCells]
    exact
      runConfig_reaches_from_move_eq
        (B := FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner)
        (handoffMove := Direction.right)
        hmove
        hconfig
  simpa [FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner,
    TmidTape, baseAfterStage] using
      seqSubroutine_runConfig_exists
        (A := NonemptyNatSuffixScannerDescription)
        (B := FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner)
        (handoffMove := Direction.right)
        nonemptyNatSuffixScannerDescription_subroutineReady
        fixedDescriptionBoundedSimulatorConfigHitScannerDescription_subroutineReady_configRunner
        hArun hBReach

theorem fixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_runConfig_code_inv_configRunner
    (baseLeft : List (Option Bool)) (code : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner.runConfig
          n
          (DovetailInitialLayoutInitializer.config
            FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner.start
            baseLeft
            ((encodeCodeWordAsInput code).map some)) =
        { state :=
            FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner.halt
          tape := Tout }) :
    exists stage : Nat,
    exists cfg : Configuration,
    exists hit : Bool,
    exists baseAfter : List (Option Bool),
      code =
        encodeNatAppend stage
          (encodeConfigurationAppend cfg (encodeBoolAppend hit [])) ∧
        Tape.move Direction.right Tout =
          DovetailInitialLayoutInitializer.tapeAtCells baseAfter [] := by
  have hseq :
      (seqSubroutine
        NonemptyNatSuffixScannerDescription
        FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner
        Direction.right).runConfig n
          (DovetailInitialLayoutInitializer.config
            (seqSubroutine
              NonemptyNatSuffixScannerDescription
              FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner
              Direction.right).start
            baseLeft
            ((encodeCodeWordAsInput code).map some)) =
        { state :=
            (seqSubroutine
              NonemptyNatSuffixScannerDescription
              FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner
              Direction.right).halt
          tape := Tout } := by
    simpa [FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner]
      using h
  rcases
      seqSubroutine_runConfig_inv
        (A := NonemptyNatSuffixScannerDescription)
        (B := FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner)
        (handoffMove := Direction.right)
        nonemptyNatSuffixScannerDescription_subroutineReady
        fixedDescriptionBoundedSimulatorConfigHitScannerDescription_subroutineReady_configRunner
        hseq with
    ⟨Tstage, hstage, hrest⟩
  rcases hstage with ⟨nStage, hstageRun, _hstageFirst⟩
  rcases
      nonemptyNatSuffixScannerDescription_runConfig_code_inv
        baseLeft code
        (by simpa [DovetailInitialLayoutInitializer.config] using
          hstageRun) with
    ⟨stage, suffixSymbol, suffixRest, hcodeStage⟩
  rcases
      encodeCodeWordAsInput_cons_bits suffixSymbol suffixRest with
    ⟨suffixBit, suffixTail, hsuffixBits⟩
  rcases
      nonemptyNatSuffixScannerDescription_runConfig_encodeNatAppend_handoff
        baseLeft stage (suffixSymbol :: suffixRest) suffixBit suffixTail
        hsuffixBits
        (by
          simpa [DovetailInitialLayoutInitializer.config, hcodeStage] using
            hstageRun) with
    ⟨baseAfterStage, hstageMove⟩
  rcases hrest with ⟨nRest, hrestRun⟩
  have hrestCodeRun :
      FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner.runConfig
          nRest
          (DovetailInitialLayoutInitializer.config
            FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner.start
            baseAfterStage
            ((encodeCodeWordAsInput
              (suffixSymbol :: suffixRest)).map some)) =
        { state :=
            FixedDescriptionBoundedSimulatorConfigHitScannerDescription_configRunner.halt
          tape := Tout } := by
    simpa [DovetailInitialLayoutInitializer.config, hstageMove] using
      hrestRun
  rcases
      fixedDescriptionBoundedSimulatorConfigHitScannerDescription_runConfig_code_inv_configRunner
        baseAfterStage (suffixSymbol :: suffixRest) hrestCodeRun with
    ⟨cfg, hit, baseAfter, hsuffixCode, hmove⟩
  refine ⟨stage, cfg, hit, baseAfter, ?_, hmove⟩
  rw [hcodeStage, hsuffixCode]

/--
Concrete scanner for the simulator-layout payload after the leading header code
symbol.  It validates the bool-word input, stage, configuration, and final hit
flag using the existing canonical suffix scanners.
-/
def FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner :
    MachineDescription :=
  seqSubroutine
    BoolWordSuffixScannerDescription
    FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner
    Direction.right

theorem fixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_subroutineReady_configRunner :
    FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner.SubroutineReady :=
  seqSubroutine_subroutineReady
    boolWordSuffixScannerDescription_subroutineReady
    fixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_subroutineReady_configRunner

def fixedDescriptionBoundedSimulatorLayoutPayloadBits_configRunner
    (L : SimulatorLayout) : Word Bool :=
  boolWordFieldBits L.input
    (List.append (stageNatBits L.stage)
      (configurationFieldBits L.config (boolFieldBits L.hit [])))

theorem fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_header_payloadBits_configRunner
    (L : SimulatorLayout) :
    SimulatorLayout.asBoolInput L =
      List.append fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner
        (fixedDescriptionBoundedSimulatorLayoutPayloadBits_configRunner L) := by
  rw [SimulatorLayout.asBoolInput, SimulatorLayout.encode,
    SimulatorLayout.encodeAppend]
  change
    List.append (encodeCodeSymbolAsInput MachineCodeSymbol.header)
        (encodeCodeWordAsInput
          (encodeBoolWordAppend L.input
            (encodeNatAppend L.stage
              (encodeConfigurationAppend L.config
                (encodeBoolAppend L.hit []))))) =
      List.append fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner
        (fixedDescriptionBoundedSimulatorLayoutPayloadBits_configRunner L)
  rw [boolWordBits_eq_encodeBoolWordAppend]
  rw [natBits_eq_encodeNatAppend]
  rw [configurationFieldBits_eq_encodeConfigurationAppend]
  rw [boolBits_eq_encodeBoolAppend]
  simp [fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
    fixedDescriptionBoundedSimulatorLayoutPayloadBits_configRunner,
    boolWordFieldBits, cellListFieldBits, boolFieldBits,
    cellFieldBits, configurationFieldBits, tapeFieldBits,
    encodeCodeWordAsInput, List.append_nil]

theorem run_fixedDescriptionBoundedSimulatorLayoutPayload_raw_to_handoff_withBase_configRunner
    (L : SimulatorLayout) (baseLeft : List (Option Bool)) :
    exists steps : Nat,
      FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner.runConfig
          steps
          { state :=
              FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner.start
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells baseLeft
                ((boolWordFieldBits L.input
                  (List.append (stageNatBits L.stage)
                    (configurationFieldBits L.config
                      (boolFieldBits L.hit [])))).map some) } =
        { state :=
            FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner.halt
          tape :=
            (boolFinalHandoffConfigWithBase L.hit
              (configurationRestoredLeftWithBase L.config
                (List.append ((stageNatBits L.stage).reverse.map some)
                  (cellListCanonicalRestoredLeftWithBase
                    (L.input.map some) baseLeft)))).tape } := by
  let stageSuffix : Word Bool :=
    configurationFieldBits L.config (boolFieldBits L.hit [])
  rcases stageNatBits_cons_false L.stage with ⟨stageTail, hstageTail⟩
  let inputSuffixTail : Word Bool :=
    List.append stageTail stageSuffix
  rcases run_boolWordSuffix_raw_to_canonical_handoff_withBase
      L.input baseLeft inputSuffixTail with
    ⟨inputSteps, hinput⟩
  let TmidTape : Tape Bool :=
    (boolWordCanonicalHandoffConfigWithBase L.input baseLeft
      (false :: inputSuffixTail)).tape
  let baseAfterInput : List (Option Bool) :=
    cellListCanonicalRestoredLeftWithBase (L.input.map some) baseLeft
  have hArun :
      BoolWordSuffixScannerDescription.runConfig inputSteps
          { state := BoolWordSuffixScannerDescription.start
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells baseLeft
                ((boolWordFieldBits L.input
                  (List.append (stageNatBits L.stage)
                    (configurationFieldBits L.config
                      (boolFieldBits L.hit [])))).map some) } =
        { state := BoolWordSuffixScannerDescription.halt
          tape := TmidTape } := by
    change
      BoolWordSuffixScannerDescription.runConfig inputSteps
          (DovetailInitialLayoutInitializer.config
            BoolWordSuffixScannerDescription.start baseLeft
            ((boolWordFieldBits L.input
              (List.append (stageNatBits L.stage) stageSuffix)).map some)) =
        { state := BoolWordSuffixScannerDescription.halt
          tape := TmidTape }
    rw [show
        ((boolWordFieldBits L.input
          (List.append (stageNatBits L.stage) stageSuffix)).map some) =
          List.append ((stageNatBits L.input.length).map some)
            (List.append ((cellsCodeBits (L.input.map some)).map some)
              (some false :: inputSuffixTail.map some)) by
      rw [hstageTail]
      simp [boolWordFieldBits, cellListFieldBits, inputSuffixTail,
        stageSuffix, List.map_append]]
    simpa [TmidTape, boolWordCanonicalHandoffConfigWithBase] using
      hinput
  have hBReach :
      exists nB : Nat,
        FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner.runConfig
            nB
            { state :=
                FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner.start
              tape := Tape.move Direction.right TmidTape } =
          { state :=
              FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner.halt
            tape :=
              (boolFinalHandoffConfigWithBase L.hit
                (configurationRestoredLeftWithBase L.config
                  (List.append ((stageNatBits L.stage).reverse.map some)
                    baseAfterInput))).tape } := by
    rcases
        run_fixedDescriptionBoundedSimulatorStageConfigHit_raw_to_handoff_withBase_configRunner
          L.stage L.config L.hit baseAfterInput with
      ⟨stageSteps, hstage⟩
    have hmove :
        Tape.move Direction.right TmidTape =
          DovetailInitialLayoutInitializer.tapeAtCells baseAfterInput
            ((List.append (stageNatBits L.stage) stageSuffix).map some) := by
      have hraw :
          Tape.move Direction.right TmidTape =
            DovetailInitialLayoutInitializer.tapeAtCells baseAfterInput
              ((false :: inputSuffixTail).map some) := by
        simpa [TmidTape, baseAfterInput,
          boolWordCanonicalHandoffConfigWithBase] using
          cellListCanonicalHandoffConfigWithBase_move_right
            (L.input.map some) baseLeft false inputSuffixTail
      rw [hraw]
      have hsuffixCells :
          (false :: inputSuffixTail).map some =
            (List.append (stageNatBits L.stage) stageSuffix).map some := by
        rw [hstageTail]
        simp [inputSuffixTail, List.map_append]
      simp [hsuffixCells]
    exact
      runConfig_reaches_from_move_eq
        (B := FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner)
        (handoffMove := Direction.right)
        hmove
        (by simpa [baseAfterInput, stageSuffix] using hstage)
  simpa [FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner,
    TmidTape, baseAfterInput] using
      seqSubroutine_runConfig_exists
        (A := BoolWordSuffixScannerDescription)
        (B := FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner)
        (handoffMove := Direction.right)
        boolWordSuffixScannerDescription_subroutineReady
        fixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_subroutineReady_configRunner
        hArun hBReach

theorem fixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_runConfig_code_inv_configRunner
    (baseLeft : List (Option Bool)) (code : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner.runConfig
          n
          (DovetailInitialLayoutInitializer.config
            FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner.start
            baseLeft
            ((encodeCodeWordAsInput code).map some)) =
        { state :=
            FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner.halt
          tape := Tout }) :
    exists input : Word Bool,
    exists stage : Nat,
    exists cfg : Configuration,
    exists hit : Bool,
    exists baseAfter : List (Option Bool),
      code =
        encodeBoolWordAppend input
          (encodeNatAppend stage
            (encodeConfigurationAppend cfg (encodeBoolAppend hit []))) ∧
        Tape.move Direction.right Tout =
          DovetailInitialLayoutInitializer.tapeAtCells baseAfter [] := by
  have hseq :
      (seqSubroutine
        BoolWordSuffixScannerDescription
        FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner
        Direction.right).runConfig n
          (DovetailInitialLayoutInitializer.config
            (seqSubroutine
              BoolWordSuffixScannerDescription
              FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner
              Direction.right).start
            baseLeft
            ((encodeCodeWordAsInput code).map some)) =
        { state :=
            (seqSubroutine
              BoolWordSuffixScannerDescription
              FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner
              Direction.right).halt
          tape := Tout } := by
    simpa [FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner]
      using h
  rcases
      seqSubroutine_runConfig_inv
        (A := BoolWordSuffixScannerDescription)
        (B := FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner)
        (handoffMove := Direction.right)
        boolWordSuffixScannerDescription_subroutineReady
        fixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_subroutineReady_configRunner
        hseq with
    ⟨Tinput, hinput, hrest⟩
  rcases hinput with ⟨nInput, hinputRun, _hinputFirst⟩
  rcases
      boolWordSuffixScannerDescription_runConfig_code_inv
        baseLeft code
        (by simpa [DovetailInitialLayoutInitializer.config] using
          hinputRun) with
    ⟨input, suffix, hcodeInput⟩
  rcases
      boolWordSuffixScannerDescription_runConfig_encodeBoolWordAppend_handoff
        baseLeft input suffix
        (by
          simpa [DovetailInitialLayoutInitializer.config, hcodeInput] using
            hinputRun) with
    ⟨suffixTail, hsuffixBits, hTinput⟩
  let baseAfterInput : List (Option Bool) :=
    cellListCanonicalRestoredLeftWithBase (input.map some) baseLeft
  have hinputMove :
      Tape.move Direction.right Tinput =
        DovetailInitialLayoutInitializer.tapeAtCells baseAfterInput
          ((encodeCodeWordAsInput suffix).map some) := by
    rw [hTinput]
    have hraw :
        Tape.move Direction.right
            (boolWordCanonicalHandoffConfigWithBase input baseLeft
              (false :: suffixTail)).tape =
          DovetailInitialLayoutInitializer.tapeAtCells baseAfterInput
            ((false :: suffixTail).map some) := by
      simpa [boolWordCanonicalHandoffConfigWithBase, baseAfterInput]
        using
          cellListCanonicalHandoffConfigWithBase_move_right
            (input.map some) baseLeft false suffixTail
    rw [hraw]
    simp [hsuffixBits]
  rcases hrest with ⟨nRest, hrestRun⟩
  have hrestCodeRun :
      FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner.runConfig
          nRest
          (DovetailInitialLayoutInitializer.config
            FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner.start
            baseAfterInput
            ((encodeCodeWordAsInput suffix).map some)) =
        { state :=
            FixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_configRunner.halt
          tape := Tout } := by
    simpa [DovetailInitialLayoutInitializer.config, hinputMove] using
      hrestRun
  rcases
      fixedDescriptionBoundedSimulatorStageConfigHitScannerDescription_runConfig_code_inv_configRunner
        baseAfterInput suffix hrestCodeRun with
    ⟨stage, cfg, hit, baseAfter, hsuffixCode, hmove⟩
  refine ⟨input, stage, cfg, hit, baseAfter, ?_, hmove⟩
  rw [hcodeInput, hsuffixCode]

/--
Concrete scanner for a complete simulator-layout code word.  This chains the
fixed header-prefix block with the simulator payload scanner.
-/
def FixedDescriptionBoundedSimulatorLayoutScannerDescription_configRunner :
    MachineDescription :=
  seqSubroutine
    FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner
    FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner
    Direction.right

theorem fixedDescriptionBoundedSimulatorLayoutScannerDescription_subroutineReady_configRunner :
    FixedDescriptionBoundedSimulatorLayoutScannerDescription_configRunner.SubroutineReady :=
  seqSubroutine_subroutineReady
    fixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_subroutineReady_configRunner
    fixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_subroutineReady_configRunner

def fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_configRunner
    (L : SimulatorLayout) (baseLeft : List (Option Bool)) : Tape Bool :=
  (boolFinalHandoffConfigWithBase L.hit
    (configurationRestoredLeftWithBase L.config
      (List.append ((stageNatBits L.stage).reverse.map some)
        (cellListCanonicalRestoredLeftWithBase (L.input.map some)
          (List.append
            (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.reverse.map
              some)
            baseLeft))))).tape

theorem fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_normalizedOutput_configRunner
    (L : SimulatorLayout) (baseLeft : List (Option Bool)) :
    Tape.normalizedOutput
        (fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_configRunner
          L baseLeft) =
      List.append (baseLeft.reverse.filterMap (fun cell => cell))
        (SimulatorLayout.asBoolInput L) := by
  rw [fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_configRunner]
  rw [fixedDescriptionBoundedSimulatorBoolFinalHandoffConfigWithBase_normalizedOutput_configRunner]
  rw [fixedDescriptionBoundedSimulatorConfigurationRestoredLeftWithBase_reverse_filterMap_configRunner]
  simp [List.reverse_append, List.filterMap_append, List.map_reverse,
    List.append_assoc]
  have hcellList :
      (List.filterMap (fun cell => cell)
          (cellListCanonicalRestoredLeftWithBase (L.input.map some)
            (List.append
              (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.map
                some).reverse
              baseLeft))).reverse =
        List.append
          ((List.append
            (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.map
              some).reverse
            baseLeft).reverse.filterMap (fun cell => cell))
          (cellListFieldBits (L.input.map some) []) := by
    rw [← Tape.filterMap_reverse]
    exact
      fixedDescriptionBoundedSimulatorCellListCanonicalRestoredLeftWithBase_reverse_filterMap_configRunner
        (L.input.map some)
        (List.append
          (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.map
            some).reverse
          baseLeft)
  rw [show
      (List.filterMap (fun cell => cell)
          (cellListCanonicalRestoredLeftWithBase (L.input.map some)
            ((fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.map
              some).reverse ++ baseLeft))).reverse =
        List.append
          (((fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.map
            some).reverse ++ baseLeft).reverse.filterMap
              (fun cell => cell))
          (cellListFieldBits (L.input.map some) []) by
    simpa using hcellList]
  rw [fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_header_payloadBits_configRunner]
  simp [fixedDescriptionBoundedSimulatorLayoutPayloadBits_configRunner,
    boolWordFieldBits, cellListFieldBits, boolFieldBits,
    cellFieldBits, configurationFieldBits, tapeFieldBits,
    Function.comp_def,
    List.reverse_append, List.filterMap_append,
    List.append_assoc]

theorem run_fixedDescriptionBoundedSimulatorLayoutScanner_raw_to_handoff_withBase_configRunner
    (L : SimulatorLayout) (baseLeft : List (Option Bool)) :
    exists steps : Nat,
      FixedDescriptionBoundedSimulatorLayoutScannerDescription_configRunner.runConfig
          steps
          { state :=
              FixedDescriptionBoundedSimulatorLayoutScannerDescription_configRunner.start
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells baseLeft
                ((SimulatorLayout.asBoolInput L).map some) } =
        { state :=
            FixedDescriptionBoundedSimulatorLayoutScannerDescription_configRunner.halt
          tape :=
            fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_configRunner
              L baseLeft } := by
  let payloadBits : Word Bool :=
    fixedDescriptionBoundedSimulatorLayoutPayloadBits_configRunner L
  rcases
      cellListFieldBits_cons_false (L.input.map some)
        (List.append (stageNatBits L.stage)
          (configurationFieldBits L.config (boolFieldBits L.hit []))) with
    ⟨payloadTail, hpayloadTail⟩
  rcases
      fixedDescriptionBoundedSimulatorHeaderPrefix_run_raw_to_handoff_withBase_configRunner
        baseLeft false payloadTail with
    ⟨headerSteps, hheader⟩
  let TmidTape : Tape Bool :=
    (fixedDescriptionBoundedSimulatorHeaderPrefixHandoffConfigWithBase_configRunner
      baseLeft (false :: payloadTail)).tape
  let baseAfterHeader : List (Option Bool) :=
    List.append
      (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.reverse.map
        some)
      baseLeft
  have hpayloadEq :
      payloadBits = false :: payloadTail := by
    simpa [payloadBits,
      fixedDescriptionBoundedSimulatorLayoutPayloadBits_configRunner,
      boolWordFieldBits] using hpayloadTail
  have hArun :
      FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.runConfig
          headerSteps
          { state :=
              FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.start
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells baseLeft
                ((SimulatorLayout.asBoolInput L).map some) } =
        { state :=
            FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.halt
          tape := TmidTape } := by
    rw [fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_header_payloadBits_configRunner]
    rw [show
        fixedDescriptionBoundedSimulatorLayoutPayloadBits_configRunner L =
          false :: payloadTail by
      simpa [payloadBits] using hpayloadEq]
    simp [List.map_append]
    change
      FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.runConfig
          headerSteps
          (DovetailInitialLayoutInitializer.config
            FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.start
            baseLeft
            (List.append
              (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.map
                some)
              ((false :: payloadTail).map some))) =
        { state :=
            FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner.halt
          tape := TmidTape }
    simpa [TmidTape] using hheader
  have hBReach :
      exists nB : Nat,
        FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner.runConfig
            nB
            { state :=
                FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner.start
              tape := Tape.move Direction.right TmidTape } =
          { state :=
              FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner.halt
            tape :=
              fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_configRunner
                L baseLeft } := by
    rcases
        run_fixedDescriptionBoundedSimulatorLayoutPayload_raw_to_handoff_withBase_configRunner
          L baseAfterHeader with
      ⟨payloadSteps, hpayload⟩
    have hmove :
        Tape.move Direction.right TmidTape =
          DovetailInitialLayoutInitializer.tapeAtCells baseAfterHeader
            (payloadBits.map some) := by
      have hraw :
          Tape.move Direction.right TmidTape =
            DovetailInitialLayoutInitializer.tapeAtCells baseAfterHeader
              ((false :: payloadTail).map some) := by
        simpa [TmidTape, baseAfterHeader] using
          fixedDescriptionBoundedSimulatorHeaderPrefixHandoffConfigWithBase_move_right_configRunner
            baseLeft false payloadTail
      rw [hraw]
      simp [hpayloadEq]
    exact
      runConfig_reaches_from_move_eq
        (B := FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner)
        (handoffMove := Direction.right)
        hmove
        (by
          simpa [baseAfterHeader, payloadBits,
            fixedDescriptionBoundedSimulatorLayoutPayloadBits_configRunner,
            fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_configRunner]
            using hpayload)
  simpa [FixedDescriptionBoundedSimulatorLayoutScannerDescription_configRunner,
    TmidTape] using
      seqSubroutine_runConfig_exists
        (A := FixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_configRunner)
        (B := FixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_configRunner)
        (handoffMove := Direction.right)
        fixedDescriptionBoundedSimulatorHeaderPrefixScannerDescription_subroutineReady_configRunner
        fixedDescriptionBoundedSimulatorLayoutPayloadScannerDescription_subroutineReady_configRunner
        hArun hBReach

theorem fixedDescriptionBoundedSimulatorLayoutScannerDescription_haltsWithOutput_configRunner
    (L : SimulatorLayout) :
    FixedDescriptionBoundedSimulatorLayoutScannerDescription_configRunner.HaltsWithOutput
      (SimulatorLayout.asBoolInput L)
      (SimulatorLayout.asBoolInput L) := by
  rcases
      run_fixedDescriptionBoundedSimulatorLayoutScanner_raw_to_handoff_withBase_configRunner
        L [] with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [MachineDescription.HaltsWithOutputIn,
      MachineDescription.initial,
      DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.input] using congrArg Configuration.state hsteps
  · have htape :
        (FixedDescriptionBoundedSimulatorLayoutScannerDescription_configRunner.runConfig
            steps
            (FixedDescriptionBoundedSimulatorLayoutScannerDescription_configRunner.initial
              (SimulatorLayout.asBoolInput L))).tape =
          fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_configRunner
            L [] := by
      simpa [MachineDescription.initial,
        DovetailInitialLayoutInitializer.tapeAtCells,
        Tape.input] using congrArg Configuration.tape hsteps
    rw [htape]
    simpa using
      fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_normalizedOutput_configRunner
        L []

theorem fixedDescriptionBoundedSimulatorLayoutScannerRestoredLeft_eq_asBoolInput_reverse_map_some_configRunner
    (L : SimulatorLayout) :
    List.append ((cellCodeBits (some L.hit)).reverse.map some)
      (configurationRestoredLeftWithBase L.config
        (List.append ((stageNatBits L.stage).reverse.map some)
          (cellListCanonicalRestoredLeftWithBase (L.input.map some)
            (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.reverse.map
              some)))) =
      (SimulatorLayout.asBoolInput L).reverse.map some := by
  have hinput :
      cellListCanonicalRestoredLeftWithBase (L.input.map some)
          (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.reverse.map
            some) =
        List.append
          ((cellListCanonicalRestoredBitsRev (L.input.map some)).map some)
          (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.reverse.map
            some) := by
    exact
      (cellListCanonicalRestoredBitsRev_map_some_withBase
        (L.input.map some)
        (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.reverse.map
          some)).symm
  rw [hinput]
  have hconfig :
      configurationRestoredLeftWithBase L.config
        (List.append ((stageNatBits L.stage).reverse.map some)
          (List.append
            ((cellListCanonicalRestoredBitsRev (L.input.map some)).map some)
            (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.reverse.map
              some))) =
        List.append ((configurationRestoredBitsRev L.config).map some)
          (List.append ((stageNatBits L.stage).reverse.map some)
            (List.append
              ((cellListCanonicalRestoredBitsRev (L.input.map some)).map some)
              (fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner.reverse.map
                some))) := by
    exact
      (configurationRestoredBitsRev_map_some_withBase L.config _).symm
  rw [hconfig]
  have hinputBits :
      (cellListCanonicalRestoredBitsRev (L.input.map some)).map some =
        (cellListFieldBits (L.input.map some) []).reverse.map some := by
    have h :=
      congrArg (fun xs : Word Bool => xs.reverse.map some)
        (cellListCanonicalRestoredBitsRev_reverse (L.input.map some))
    simpa using h
  have hconfigBits :
      (configurationRestoredBitsRev L.config).map some =
        (configurationFieldBits L.config []).reverse.map some := by
    have h :=
      congrArg (fun xs : Word Bool => xs.reverse.map some)
        (configurationRestoredBitsRev_reverse L.config)
    simpa using h
  rw [hinputBits, hconfigBits]
  simp [SimulatorLayout.asBoolInput, SimulatorLayout.encode,
    SimulatorLayout.encodeAppend,
    fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
    boolWordBits_eq_encodeBoolWordAppend,
    natBits_eq_encodeNatAppend,
    configurationFieldBits_eq_encodeConfigurationAppend,
    boolBits_eq_encodeBoolAppend,
    cellListFieldBits, cellFieldBits, configurationFieldBits,
    tapeFieldBits, encodeCodeWordAsInput, List.append_assoc,
    List.map_append, List.reverse_append]

theorem fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_move_right_eq_terminal_configRunner
    (L : SimulatorLayout) :
    Tape.move Direction.right
        (fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_configRunner
          L []) =
      DovetailInitialLayoutInitializer.tapeAtCells
        ((SimulatorLayout.asBoolInput L).reverse.map some) [] := by
  rw [fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_configRunner]
  rw [boolFinalHandoffConfigWithBase_move_right]
  exact
    by
      simpa using
        congrArg
          (fun left =>
            DovetailInitialLayoutInitializer.tapeAtCells left [])
          (fixedDescriptionBoundedSimulatorLayoutScannerRestoredLeft_eq_asBoolInput_reverse_map_some_configRunner
            L)

/--
Return from a scanned right edge to the standard right-shifted input head.

This phase assumes the validating scanner has already halted at the last
nonblank bit and is sequenced with a left handoff.  It scans left to the blank
before the word, then moves right twice, landing one cell right of the first
bit.  The phase preserves every stored cell, including any explicit trailing
blank already introduced by the scanner.
-/
def FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner :
    MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ keepMove 0 (some false) Direction.left 0
    , keepMove 0 (some true) Direction.left 0
    , keepMove 0 none Direction.right 1
    , keepMove 1 (some false) Direction.right 2
    , keepMove 1 (some true) Direction.right 2
    ]

theorem fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_wellFormed_configRunner :
    FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l :=
        FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner.transitions)
      (stateCount :=
        FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l :=
        FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner.transitions)
      (by decide)

theorem fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_haltTransitionFree_configRunner :
    FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner.HaltTransitionFree :=
  transition_notFrom_of_all
    (l :=
      FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner.transitions)
    (state :=
      FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner.halt)
    (by decide)

theorem fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_subroutineReady_configRunner :
    FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner.SubroutineReady :=
  ⟨fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_wellFormed_configRunner,
    fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_haltTransitionFree_configRunner⟩

private abbrev FDBSReturnToRightShiftedInput_configRunner :=
  FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner

theorem fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_run_configRunner
    (leftRev : Word Bool) (current : Bool) (right : List (Option Bool)) :
    FDBSReturnToRightShiftedInput_configRunner.runConfig
        (leftRev.length + 3)
        (DovetailInitialLayoutInitializer.config
          FDBSReturnToRightShiftedInput_configRunner.start
          (leftRev.map some)
          (some current :: right)) =
      { state := FDBSReturnToRightShiftedInput_configRunner.halt
        tape :=
          Tape.move Direction.right
            (DovetailInitialLayoutInitializer.tapeAtCells [none]
              (List.append (leftRev.reverse.map some)
                (some current :: right))) } := by
  induction leftRev generalizing current right with
  | nil =>
      cases current
      · cases right with
        | nil =>
            simp [FDBSReturnToRightShiftedInput_configRunner,
              FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner,
              DovetailInitialLayoutInitializer.config,
              DovetailInitialLayoutInitializer.tapeAtCells,
              runConfig, stepConfig, lookupTransition, Matches,
              keepMove, transition, Tape.read, Tape.write, Tape.move,
              Tape.moveLeft, Tape.moveRight]
        | cons cell rest =>
            cases cell <;>
              simp [FDBSReturnToRightShiftedInput_configRunner,
                FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner,
                DovetailInitialLayoutInitializer.config,
                DovetailInitialLayoutInitializer.tapeAtCells,
                runConfig, stepConfig, lookupTransition, Matches,
                keepMove, transition, Tape.read, Tape.write, Tape.move,
                Tape.moveLeft, Tape.moveRight]
      · cases right with
        | nil =>
            simp [FDBSReturnToRightShiftedInput_configRunner,
              FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner,
              DovetailInitialLayoutInitializer.config,
              DovetailInitialLayoutInitializer.tapeAtCells,
              runConfig, stepConfig, lookupTransition, Matches,
              keepMove, transition, Tape.read, Tape.write, Tape.move,
              Tape.moveLeft, Tape.moveRight]
        | cons cell rest =>
            cases cell <;>
              simp [FDBSReturnToRightShiftedInput_configRunner,
                FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner,
                DovetailInitialLayoutInitializer.config,
                DovetailInitialLayoutInitializer.tapeAtCells,
                runConfig, stepConfig, lookupTransition, Matches,
                keepMove, transition, Tape.read, Tape.write, Tape.move,
                Tape.moveLeft, Tape.moveRight]
  | cons leftBit rest ih =>
      simp only [List.length_cons]
      rw [show Nat.succ rest.length + 3 = (rest.length + 3) + 1 by omega]
      rw [runConfig]
      cases current
      · simpa [FDBSReturnToRightShiftedInput_configRunner,
          FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner,
          DovetailInitialLayoutInitializer.config,
          DovetailInitialLayoutInitializer.tapeAtCells,
          stepConfig, lookupTransition, Matches, keepMove, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          List.append_assoc] using ih leftBit (some false :: right)
      · simpa [FDBSReturnToRightShiftedInput_configRunner,
          FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner,
          DovetailInitialLayoutInitializer.config,
          DovetailInitialLayoutInitializer.tapeAtCells,
          stepConfig, lookupTransition, Matches, keepMove, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          List.append_assoc] using ih leftBit (some true :: right)

theorem fixedDescriptionBoundedSimulator_reverse_two_split_configRunner
    (w : Word Bool) (h : 2 <= w.length) :
    exists last penult : Bool,
    exists middleRev : Word Bool,
      w.reverse = last :: penult :: middleRev ∧
        w = List.append middleRev.reverse [penult, last] := by
  cases hr : w.reverse with
  | nil =>
      have hlen : w.length = 0 := by
        have := congrArg List.length hr
        simpa using this
      omega
  | cons last rest =>
      cases hrest : rest with
      | nil =>
          have hlen : w.length = 1 := by
            have := congrArg List.length hr
            simp [hrest] at this
            simpa using this
          omega
      | cons penult middleRev =>
          refine ⟨last, penult, middleRev, ?_, ?_⟩
          · rfl
          · have hrev : w.reverse = last :: penult :: middleRev := by
              simpa [hrest] using hr
            have := congrArg List.reverse hrev
            simpa using this

theorem fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_eq_terminal_left_configRunner
    (L : SimulatorLayout) :
    fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_configRunner L [] =
      Tape.move Direction.left
        (DovetailInitialLayoutInitializer.tapeAtCells
          ((SimulatorLayout.asBoolInput L).reverse.map some) []) := by
  rw [fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_configRunner]
  rw [boolFinalHandoffConfigWithBase]
  simp
  have hleft :=
    fixedDescriptionBoundedSimulatorLayoutScannerRestoredLeft_eq_asBoolInput_reverse_map_some_configRunner
      L
  simpa [List.map_reverse] using
    congrArg
      (fun left =>
        Tape.move Direction.left
          (DovetailInitialLayoutInitializer.tapeAtCells left []))
      hleft

theorem fixedDescriptionBoundedSimulator_tapeAtCells_left_blank_append_none_equiv_input_configRunner
    (w : Word Bool) :
    Tape.Equiv
      (DovetailInitialLayoutInitializer.tapeAtCells [none]
        (List.append (w.map some) [none]))
      (Tape.input w) := by
  cases w with
  | nil =>
      simp [DovetailInitialLayoutInitializer.tapeAtCells,
        Tape.input, Tape.blank, Tape.Equiv, Tape.dropTrailingNone]
  | cons bit rest =>
      constructor
      · rfl
      constructor
      · rfl
      · simp [DovetailInitialLayoutInitializer.tapeAtCells,
          Tape.input,
          fixedDescriptionBoundedSimulator_dropTrailingNone_append_none]

theorem fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_haltsFromTapeEquiv_terminal_configRunner
    (middleRev : Word Bool) (penult last : Bool) :
    FDBSReturnToRightShiftedInput_configRunner.HaltsFromTapeEquiv
      (Tape.move Direction.left
        (Tape.move Direction.left
          (DovetailInitialLayoutInitializer.tapeAtCells
            ((last :: penult :: middleRev).map some) [])))
      (Tape.move Direction.right
        (Tape.input (List.append middleRev.reverse [penult, last]))) := by
  let Tactual : Tape Bool :=
    Tape.move Direction.right
      (DovetailInitialLayoutInitializer.tapeAtCells [none]
        (List.append (middleRev.reverse.map some)
          [some penult, some last, none]))
  refine ⟨Tactual, ?_, ?_⟩
  · refine ⟨middleRev.length + 3, ?_⟩
    have hrun :=
      fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_run_configRunner
        middleRev penult [some last, none]
    constructor
    · simpa [Tactual, HaltsFromTapeIn,
        DovetailInitialLayoutInitializer.config,
        DovetailInitialLayoutInitializer.tapeAtCells,
        Tape.move, Tape.moveLeft] using
        congrArg Configuration.state hrun
    · simpa [Tactual, HaltsFromTapeIn,
        DovetailInitialLayoutInitializer.config,
        DovetailInitialLayoutInitializer.tapeAtCells,
        Tape.move, Tape.moveLeft] using
        congrArg Configuration.tape hrun
  · have heq :=
      Tape.Equiv.move
        (fixedDescriptionBoundedSimulator_tapeAtCells_left_blank_append_none_equiv_input_configRunner
          (List.append middleRev.reverse [penult, last]))
        Direction.right
    simpa [Tactual, List.map_append, List.append_assoc] using heq

theorem fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_haltsFromTapeEquiv_scannerHandoff_configRunner
    (L : SimulatorLayout) :
    FDBSReturnToRightShiftedInput_configRunner.HaltsFromTapeEquiv
      (Tape.move Direction.left
        (fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_configRunner
          L []))
      (CommonGround.SimulatorLayouts.handoffTape L) := by
  have hlen : 2 <= (SimulatorLayout.asBoolInput L).length := by
    rw [fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_header_payloadBits_configRunner]
    simp [fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
      encodeCodeSymbolAsInput]
  rcases
      fixedDescriptionBoundedSimulator_reverse_two_split_configRunner
        (SimulatorLayout.asBoolInput L) hlen with
    ⟨last, penult, middleRev, hrev, hw⟩
  have hreturn :=
    fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_haltsFromTapeEquiv_terminal_configRunner
      middleRev penult last
  have hout :
      List.append middleRev.reverse [penult, last] =
        encodeCodeWordAsInput (SimulatorLayout.encode L) := by
    simpa [SimulatorLayout.asBoolInput] using hw.symm
  have hscanner :=
    fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_eq_terminal_left_configRunner
      L
  rw [hout] at hreturn
  rw [hscanner]
  rw [hrev]
  simpa [
    CommonGround.SimulatorLayouts.handoffTape,
    CommonGround.SimulatorLayouts.encode,
    CommonGround.SimulatorLayouts.bits,
    SimulatorLayout.asBoolInput,
    CommonGround.LayoutTapes.HandoffTape,
    CommonGround.LayoutTapes.InputTape,
    CommonGround.LayoutTapes.Bits] using hreturn

def FixedDescriptionBoundedSimulatorPaddedParserEquivRunner_configRunner :
    MachineDescription :=
  seqSubroutine
    FixedDescriptionBoundedSimulatorLayoutScannerDescription_configRunner
    FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner
    Direction.left

theorem fixedDescriptionBoundedSimulatorPaddedParserEquivRunner_subroutineReady_configRunner :
    FixedDescriptionBoundedSimulatorPaddedParserEquivRunner_configRunner.SubroutineReady :=
  seqSubroutine_subroutineReady
    fixedDescriptionBoundedSimulatorLayoutScannerDescription_subroutineReady_configRunner
    fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_subroutineReady_configRunner

theorem fixedDescriptionBoundedSimulatorLayoutScannerDescription_haltsWithTape_configRunner
    (L : SimulatorLayout) :
    FixedDescriptionBoundedSimulatorLayoutScannerDescription_configRunner.HaltsWithTape
      (FixedDescriptionBoundedSimulatorInput L)
      (fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_configRunner
        L []) := by
  rcases
      run_fixedDescriptionBoundedSimulatorLayoutScanner_raw_to_handoff_withBase_configRunner
        L [] with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [HaltsWithTapeIn, initial,
      FixedDescriptionBoundedSimulatorInput,
      DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.input] using congrArg Configuration.state hsteps
  · simpa [HaltsWithTapeIn, initial,
      FixedDescriptionBoundedSimulatorInput,
      DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.input] using congrArg Configuration.tape hsteps

theorem fixedDescriptionBoundedSimulatorPaddedParserEquivRunner_haltsWithTapeEquiv_configRunner
    (L : SimulatorLayout) :
    FixedDescriptionBoundedSimulatorPaddedParserEquivRunner_configRunner.HaltsWithTapeEquiv
      (FixedDescriptionBoundedSimulatorInput L)
      (CommonGround.SimulatorLayouts.handoffTape L) := by
  have hscanner :=
    fixedDescriptionBoundedSimulatorLayoutScannerDescription_haltsWithTape_configRunner
      L
  rcases
      fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_haltsFromTapeEquiv_scannerHandoff_configRunner
        L with
    ⟨Tactual, hreturn, hTequiv⟩
  have hseq :
      FixedDescriptionBoundedSimulatorPaddedParserEquivRunner_configRunner.HaltsWithTape
        (FixedDescriptionBoundedSimulatorInput L) Tactual := by
    exact
      seqSubroutine_haltsWithTape_of_haltsWithTape
        fixedDescriptionBoundedSimulatorLayoutScannerDescription_subroutineReady_configRunner
        fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_subroutineReady_configRunner
        hscanner
        (runConfig_eq_halt_of_haltsFromTape hreturn)
  exact ⟨Tactual, hseq, hTequiv⟩

theorem fixedDescriptionBoundedSimulatorPaddedParserEquivRunner_closed_configRunner
    (L : SimulatorLayout) (T : Tape Bool)
    (hhlt :
      FixedDescriptionBoundedSimulatorPaddedParserEquivRunner_configRunner.HaltsWithTape
        (FixedDescriptionBoundedSimulatorInput L) T) :
    Tape.Equiv T (CommonGround.SimulatorLayouts.handoffTape L) := by
  have hscannerKnown :=
    fixedDescriptionBoundedSimulatorLayoutScannerDescription_haltsWithTape_configRunner
      L
  rcases
      seqSubroutine_haltsWithTape_inv
        fixedDescriptionBoundedSimulatorLayoutScannerDescription_subroutineReady_configRunner
        fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_subroutineReady_configRunner
        hhlt with
    ⟨Tmid, hscannerRun, hreturnReach⟩
  have hTmid_eq :
      Tmid =
        fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_configRunner
          L [] :=
    haltsWithTape_functional_of_haltTransitionFree
      fixedDescriptionBoundedSimulatorLayoutScannerDescription_subroutineReady_configRunner.right
      hscannerRun hscannerKnown
  subst Tmid
  rcases hreturnReach with ⟨n, hn⟩
  have hreturnRun :
      FDBSReturnToRightShiftedInput_configRunner.HaltsFromTape
        (Tape.move Direction.left
          (fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_configRunner
            L []))
        T := by
    refine ⟨n, ?_⟩
    constructor
    · simpa [HaltsFromTapeIn] using
        congrArg Configuration.state hn
    · simpa [HaltsFromTapeIn] using
        congrArg Configuration.tape hn
  rcases
      fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_haltsFromTapeEquiv_scannerHandoff_configRunner
        L with
    ⟨Tactual, hreturnActual, hTequiv⟩
  have hT_eq : T = Tactual :=
    haltsFromTape_functional_of_haltTransitionFree
      fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_subroutineReady_configRunner.right
      hreturnRun hreturnActual
  rw [hT_eq]
  exact hTequiv

theorem fixedDescriptionBoundedSimulatorPaddedParserEquivSpec_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorPaddedParserEquivSpec_configRunner
      FixedDescriptionBoundedSimulatorPaddedParserEquivRunner_configRunner := by
  constructor
  · exact
      fixedDescriptionBoundedSimulatorPaddedParserEquivRunner_subroutineReady_configRunner
  constructor
  · intro L
    exact
      fixedDescriptionBoundedSimulatorPaddedParserEquivRunner_haltsWithTapeEquiv_configRunner
        L
  · intro L T hhalt
    exact
      fixedDescriptionBoundedSimulatorPaddedParserEquivRunner_closed_configRunner
        L T hhalt

theorem fixedDescriptionBoundedSimulatorPaddedParserEquivConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorPaddedParserEquivConstruction_configRunner :=
  ⟨FixedDescriptionBoundedSimulatorPaddedParserEquivRunner_configRunner,
    fixedDescriptionBoundedSimulatorPaddedParserEquivSpec_scaffold_configRunner⟩

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
