import FoC.Computability.Compiler.FixedSimulatorSkeletons
import FoC.Computability.Compiler.Core.FixedDescriptionBoundedSimulator.Spec

set_option doc.verso true

/-!
# Canonical soundness for fixed-simulator skeletons

This module keeps the exact tape information carried by
{name}`FoC.Computability.FixedDescriptionBoundedSimulatorFragmentReaches` instead of projecting
immediately to normalized output.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

theorem fixedDescriptionBoundedSimulatorPhaseRealizes_standard_tape
    {phase :
      SimulatorLayout ->
        SimulatorLayout}
    {fragment : Fragment}
    (h :
      FixedDescriptionBoundedSimulatorPhaseRealizes
        FixedDescriptionBoundedSimulatorLayoutTape
        FixedDescriptionBoundedSimulatorLayoutTape
        phase fragment)
    (L : SimulatorLayout) :
    fragment.toDescription.HaltsWithTape
      (FixedDescriptionBoundedSimulatorInput L)
      (FixedDescriptionBoundedSimulatorLayoutTape (phase L)) := by
  rcases h.right L with ⟨n, hn, _hminimal⟩
  refine ⟨n, ?_⟩
  constructor
  · simpa [Fragment.toDescription,
      FixedDescriptionBoundedSimulatorInput,
      FixedDescriptionBoundedSimulatorLayoutTape,
      SimulatorLayout.tape] using congrArg
        (fun c : Configuration => c.state) hn
  · simpa [Fragment.toDescription,
      FixedDescriptionBoundedSimulatorInput,
      FixedDescriptionBoundedSimulatorLayoutTape,
      SimulatorLayout.tape] using congrArg
        (fun c : Configuration => c.tape) hn

theorem fixedDescriptionBoundedSimulatorCanonicalSpec_of_skeletonPhaseRealizes
    {D : MachineDescription}
    {S : FixedSimulatorTableSkeleton}
    {handoffMove : Direction}
    {targets : FixedDescriptionBoundedSimulatorPhaseTargets D}
    (htargets :
      FixedDescriptionBoundedSimulatorSkeletonPhaseRealizes
        D S handoffMove targets) :
    FixedDescriptionBoundedSimulatorCanonicalSpec
      D (S.toDescription handoffMove) := by
  have hDecodeSim :
      FixedDescriptionBoundedSimulatorPhaseRealizes
        FixedDescriptionBoundedSimulatorLayoutTape
        FixedDescriptionBoundedSimulatorLayoutTape
        (fun L => targets.simulateStep (targets.decodeLayout L))
        (Fragment.seq
          S.decodeLayout S.simulateStep handoffMove) :=
    fixedDescriptionBoundedSimulatorPhaseRealizes_seq
      (entryTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (midTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (exitTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (phaseA := targets.decodeLayout)
      (phaseB := targets.simulateStep)
      (A := S.decodeLayout)
      (B := S.simulateStep)
      (handoffMove := handoffMove)
      htargets.decodeLayout htargets.simulateStep
  have hDecodeSimRepeat :
      FixedDescriptionBoundedSimulatorPhaseRealizes
        FixedDescriptionBoundedSimulatorLayoutTape
        FixedDescriptionBoundedSimulatorLayoutTape
        (fun L =>
          targets.repeatControl
            (targets.simulateStep (targets.decodeLayout L)))
        (Fragment.seq
          (Fragment.seq
            S.decodeLayout S.simulateStep handoffMove)
          S.repeatControl handoffMove) :=
    fixedDescriptionBoundedSimulatorPhaseRealizes_seq
      (entryTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (midTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (exitTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (phaseA := fun L =>
        targets.simulateStep (targets.decodeLayout L))
      (phaseB := targets.repeatControl)
      (A := Fragment.seq
        S.decodeLayout S.simulateStep handoffMove)
      (B := S.repeatControl)
      (handoffMove := handoffMove)
      hDecodeSim htargets.repeatControl
  have hAllPhases :
      FixedDescriptionBoundedSimulatorPhaseRealizes
        FixedDescriptionBoundedSimulatorLayoutTape
        FixedDescriptionBoundedSimulatorLayoutTape
        (fun L =>
          targets.emitLayout
            (targets.repeatControl
              (targets.simulateStep (targets.decodeLayout L))))
        (Fragment.seq
          (Fragment.seq
            (Fragment.seq
              S.decodeLayout S.simulateStep handoffMove)
            S.repeatControl handoffMove)
          S.emitLayout handoffMove) :=
    fixedDescriptionBoundedSimulatorPhaseRealizes_seq
      (entryTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (midTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (exitTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (phaseA := fun L =>
        targets.repeatControl
          (targets.simulateStep (targets.decodeLayout L)))
      (phaseB := targets.emitLayout)
      (A := Fragment.seq
        (Fragment.seq
          S.decodeLayout S.simulateStep handoffMove)
        S.repeatControl handoffMove)
      (B := S.emitLayout)
      (handoffMove := handoffMove)
      hDecodeSimRepeat htargets.emitLayout
  have hready :
      (S.toDescription handoffMove).SubroutineReady := by
    exact
      Fragment.toDescription_subroutineReady
        (FixedSimulatorTableSkeleton.toFragment_wellFormed
          S handoffMove)
  constructor
  · exact hready
  constructor
  · intro L
    have hTape :=
      fixedDescriptionBoundedSimulatorPhaseRealizes_standard_tape
        hAllPhases L
    have hpipeline :
        targets.emitLayout
            (targets.repeatControl
              (targets.simulateStep (targets.decodeLayout L))) =
          SimulatorLayout.run D L.stage L :=
      targets.pipeline_correct L
    simpa [FixedSimulatorTableSkeleton.toDescription,
      FixedSimulatorTableSkeleton.toFragment,
      FixedDescriptionBoundedSimulatorCanonicalOutputTape,
      FixedDescriptionBoundedSimulatorInput,
      FixedDescriptionBoundedSimulatorLayoutTape, hpipeline] using hTape
  · intro L T hhalt
    have hforward :
        (S.toDescription handoffMove).HaltsWithTape
          (FixedDescriptionBoundedSimulatorInput L)
          (FixedDescriptionBoundedSimulatorCanonicalOutputTape D L) := by
      exact
        (show
          FixedDescriptionBoundedSimulatorCanonicalForwardSpec
            D (S.toDescription handoffMove) from
          by
            intro L'
            have hTape :=
              fixedDescriptionBoundedSimulatorPhaseRealizes_standard_tape
                hAllPhases L'
            have hpipeline :
                targets.emitLayout
                    (targets.repeatControl
                      (targets.simulateStep (targets.decodeLayout L'))) =
                  SimulatorLayout.run D L'.stage L' :=
              targets.pipeline_correct L'
            simpa [FixedSimulatorTableSkeleton.toDescription,
              FixedSimulatorTableSkeleton.toFragment,
              FixedDescriptionBoundedSimulatorCanonicalOutputTape,
              FixedDescriptionBoundedSimulatorInput,
              FixedDescriptionBoundedSimulatorLayoutTape, hpipeline] using hTape)
          L
    exact
      MachineDescription.haltsWithTape_functional_of_haltTransitionFree
        hready.right hhalt hforward

theorem fixedDescriptionBoundedSimulatorCanonicalConstruction_of_phaseConstruction
    (hcompile :
      FixedDescriptionBoundedSimulatorSkeletonPhaseConstruction) :
    FixedDescriptionBoundedSimulatorCanonicalConstruction :=
  fun D =>
    Exists.elim (hcompile D) fun S hS =>
      Exists.elim hS fun handoffMove hmove =>
        Exists.elim hmove fun _targets htargets =>
          ⟨S.toDescription handoffMove,
      fixedDescriptionBoundedSimulatorCanonicalSpec_of_skeletonPhaseRealizes
        htargets⟩

theorem fixedDescriptionBoundedSimulatorTableCompiler_of_canonicalPhaseConstruction
    (hcompile :
      FixedDescriptionBoundedSimulatorSkeletonPhaseConstruction) :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction :=
  fixedDescriptionBoundedSimulatorTableCompiler_of_canonicalConstruction
    (fixedDescriptionBoundedSimulatorCanonicalConstruction_of_phaseConstruction
      hcompile)

end Computability
end FoC
