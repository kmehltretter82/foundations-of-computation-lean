import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.PhaseAdapters
import FoC.Computability.Compiler.Core.FixedDescriptionBoundedSimulator.CodeRightShifted

set_option doc.verso true

/-!
# Bounded runner simulator scaffold adapters
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace BoundedLayoutRunner

def FixedDescriptionBoundedSimulatorStepPhaseConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists simulateStep : MachineDescription.Fragment,
      FixedDescriptionBoundedSimulatorPhaseRealizes
        (FixedDescriptionBoundedSimulatorHandoffTape Direction.right)
        FixedDescriptionBoundedSimulatorLayoutTape
        (fun L => MachineDescription.SimulatorLayout.run D L.stage L)
        simulateStep

theorem fixedDescriptionBoundedSimulatorReturnFromRightPhaseRealizes_configRunner :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      (FixedDescriptionBoundedSimulatorHandoffTape Direction.right)
      FixedDescriptionBoundedSimulatorLayoutTape
      id
      (MachineDescription.Fragment.handoff Direction.left) :=
  fixedDescriptionBoundedSimulatorReturnFromRightHandoffPhaseRealizes

theorem fixedDescriptionBoundedSimulatorSkeletonPhaseConstruction_of_stepPhase_configRunner
    (hstep :
      FixedDescriptionBoundedSimulatorStepPhaseConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorSkeletonPhaseConstruction := by
  intro D
  rcases hstep D with ⟨simulateStep, hsimulateStep⟩
  let S : MachineDescription.FixedSimulatorTableSkeleton :=
    { decodeLayout := MachineDescription.Fragment.halt
      simulateStep := simulateStep
      repeatControl := MachineDescription.Fragment.handoff Direction.left
      emitLayout := MachineDescription.Fragment.handoff Direction.left
      decodeLayout_wellFormed :=
        MachineDescription.Fragment.halt_wellFormed
      simulateStep_wellFormed := hsimulateStep.left
      repeatControl_wellFormed :=
        MachineDescription.Fragment.handoff_wellFormed Direction.left
      emitLayout_wellFormed :=
        MachineDescription.Fragment.handoff_wellFormed Direction.left }
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

theorem fixedDescriptionBoundedSimulatorStepPhaseConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorStepPhaseConstruction_configRunner :=
  FoC.Computability.fixedDescriptionBoundedSimulatorRightHandoffStepPhaseConstruction_scaffold

theorem fixedDescriptionBoundedSimulatorSkeletonPhaseConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorSkeletonPhaseConstruction :=
  fixedDescriptionBoundedSimulatorSkeletonPhaseConstruction_of_stepPhase_configRunner
    fixedDescriptionBoundedSimulatorStepPhaseConstruction_scaffold_configRunner

theorem fixedDescriptionBoundedSimulatorCanonicalConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorCanonicalConstruction :=
  fixedDescriptionBoundedSimulatorCanonicalConstruction_of_phaseConstruction
    fixedDescriptionBoundedSimulatorSkeletonPhaseConstruction_scaffold_configRunner


end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
