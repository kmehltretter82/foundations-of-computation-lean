import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.PhaseAdapters
import FoC.Computability.Compiler.Core.FixedDescriptionBoundedSimulator.CodeRightShifted

set_option doc.verso true

/-!
# Bounded runner simulator scaffold adapters
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

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

/--
Finite-machine leaf for the config-runner fixed-description simulators.

The exact right-handoff skeleton target has a context-length shrink obstruction;
see {lit}`LEAN_COUNTEREXAMPLE_OVERVIEW.md` for the archived design note.  The
live config-runner assembly should use this padded target, whose output is
equivalent to the canonical simulator layout while preserving enough blank
window to avoid a forced shrink.
-/
theorem fixedDescriptionBoundedSimulatorPaddedConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorPaddedConstruction := by
  intro D
  sorry

theorem fixedDescriptionBoundedSimulatorPaddedPhaseConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorPaddedPhaseConstruction_configRunner := by
  intro D
  rcases fixedDescriptionBoundedSimulatorPaddedConstruction_scaffold_configRunner
      D with
    ⟨sim, hsim⟩
  exact
    ⟨sim,
      fixedDescriptionBoundedSimulatorPaddedPhaseSpec_of_paddedSpec_configRunner
        hsim⟩

theorem fixedDescriptionBoundedSimulatorEquivConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorEquivConstruction :=
  fixedDescriptionBoundedSimulatorEquivConstruction_of_paddedPhase_configRunner
    fixedDescriptionBoundedSimulatorPaddedPhaseConstruction_scaffold_configRunner

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
