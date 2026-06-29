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


end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
