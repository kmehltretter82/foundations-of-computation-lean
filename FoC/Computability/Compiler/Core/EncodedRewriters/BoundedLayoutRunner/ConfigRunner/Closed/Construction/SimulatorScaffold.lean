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
      (MachineDescription.Fragment.handoff Direction.left) := by
  constructor
  · exact MachineDescription.Fragment.handoff_wellFormed Direction.left
  · intro L
    rcases
        MachineDescription.Fragment.handoff_firstReaches Direction.left
          (FixedDescriptionBoundedSimulatorHandoffTape Direction.right L) with
      ⟨n, hn, hminimal⟩
    refine ⟨n, ?_, hminimal⟩
    simpa [FixedDescriptionBoundedSimulatorHandoffTape,
      FixedDescriptionBoundedSimulatorLayoutTape] using hn

theorem fixedDescriptionBoundedSimulatorRightShiftedRunCodePhaseRealizes_configRunner
    {D runner : MachineDescription}
    (hrunner :
      RightShiftedOutputCompiledSubroutineByDescription
        (FixedDescriptionBoundedSimulatorCode D) runner) :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      FixedDescriptionBoundedSimulatorLayoutTape
      (FixedDescriptionBoundedSimulatorHandoffTape Direction.right)
      (fun L => MachineDescription.SimulatorLayout.run D L.stage L)
      runner.asFragment := by
  constructor
  · exact
      MachineDescription.asFragment_wellFormed
        ⟨hrunner.left, hrunner.right.left⟩
  · intro L
    have hhalt :
        runner.HaltsWithTape
          (FixedDescriptionBoundedSimulatorInput L)
          (FixedDescriptionBoundedSimulatorHandoffTape Direction.right
            (MachineDescription.SimulatorLayout.run D L.stage L)) := by
      have htransform :
          (FixedDescriptionBoundedSimulatorCode D).transform
              (MachineDescription.SimulatorLayout.encode L) =
            some
              (MachineDescription.SimulatorLayout.encode
                (MachineDescription.SimulatorLayout.run D L.stage L)) :=
        fixedDescriptionBoundedSimulatorCode_encode D L
      simpa [FixedDescriptionBoundedSimulatorInput,
        FixedDescriptionBoundedSimulatorHandoffTape,
        FixedDescriptionBoundedSimulatorLayoutTape,
        MachineDescription.SimulatorLayout.tape,
        MachineDescription.SimulatorLayout.asBoolInput] using
        rightShiftedOutputCompiled_haltsWithTape_of_transform
          hrunner htransform
    rcases MachineDescription.runConfig_eq_halt_of_haltsWithTape hhalt with
      ⟨n, hn⟩
    rcases
        MachineDescription.firstReaches_halt_of_runConfig_eq
          hrunner.right.left hn with
      ⟨m, _hmle, hm, hminimal⟩
    refine ⟨m, ?_, ?_⟩
    · simpa [MachineDescription.asFragment_toDescription,
        MachineDescription.asFragment] using hm
    · intro k hk
      simpa [MachineDescription.asFragment_toDescription,
        MachineDescription.asFragment] using hminimal k hk

theorem fixedDescriptionBoundedSimulatorStepPhaseConstruction_of_rightShifted_configRunner
    (hcode :
      FoC.Computability.FixedDescriptionBoundedSimulatorCodeRightShiftedConstruction) :
    FixedDescriptionBoundedSimulatorStepPhaseConstruction_configRunner := by
  intro D
  rcases hcode D with ⟨runner, hrunner⟩
  let leftReturn : MachineDescription.Fragment :=
    MachineDescription.Fragment.handoff Direction.left
  let rightPause : MachineDescription.Fragment :=
    MachineDescription.Fragment.halt
  let runCode : MachineDescription.Fragment :=
    runner.asFragment
  let finalPause : MachineDescription.Fragment :=
    MachineDescription.Fragment.halt
  let enterRun : MachineDescription.Fragment :=
    MachineDescription.Fragment.seq leftReturn rightPause Direction.right
  let runAndReturn : MachineDescription.Fragment :=
    MachineDescription.Fragment.seq runCode finalPause Direction.left
  let simulateStep : MachineDescription.Fragment :=
    MachineDescription.Fragment.seq enterRun runAndReturn Direction.left
  refine ⟨simulateStep, ?_⟩
  have hEnterRun :
      FixedDescriptionBoundedSimulatorPhaseRealizes
        (FixedDescriptionBoundedSimulatorHandoffTape Direction.right)
        (FixedDescriptionBoundedSimulatorHandoffTape Direction.right)
        id enterRun := by
    have hLeft :=
      fixedDescriptionBoundedSimulatorReturnFromRightPhaseRealizes_configRunner
    have hPause :
        FixedDescriptionBoundedSimulatorPhaseRealizes
          (FixedDescriptionBoundedSimulatorHandoffTape Direction.right)
          (FixedDescriptionBoundedSimulatorHandoffTape Direction.right)
          id rightPause := by
      simpa [rightPause] using
        fixedDescriptionBoundedSimulatorHaltPhaseRealizes
          (FixedDescriptionBoundedSimulatorHandoffTape Direction.right)
    simpa [enterRun, leftReturn] using
      fixedDescriptionBoundedSimulatorPhaseRealizes_seq
        (entryTape := FixedDescriptionBoundedSimulatorHandoffTape
          Direction.right)
        (midTape := FixedDescriptionBoundedSimulatorLayoutTape)
        (exitTape := FixedDescriptionBoundedSimulatorHandoffTape
          Direction.right)
        (phaseA := id)
        (phaseB := id)
        (A := leftReturn)
        (B := rightPause)
        (handoffMove := Direction.right)
        hLeft hPause
  have hRunAndReturn :
      FixedDescriptionBoundedSimulatorPhaseRealizes
        FixedDescriptionBoundedSimulatorLayoutTape
        FixedDescriptionBoundedSimulatorLayoutTape
        (fun L => MachineDescription.SimulatorLayout.run D L.stage L)
        runAndReturn := by
    have hRun :=
      fixedDescriptionBoundedSimulatorRightShiftedRunCodePhaseRealizes_configRunner
        hrunner
    have hPause :
        FixedDescriptionBoundedSimulatorPhaseRealizes
          FixedDescriptionBoundedSimulatorLayoutTape
          FixedDescriptionBoundedSimulatorLayoutTape
          id finalPause := by
      simpa [finalPause] using
        fixedDescriptionBoundedSimulatorHaltPhaseRealizes
          FixedDescriptionBoundedSimulatorLayoutTape
    simpa [runAndReturn, runCode, finalPause] using
      fixedDescriptionBoundedSimulatorPhaseRealizes_seq
        (entryTape := FixedDescriptionBoundedSimulatorLayoutTape)
        (midTape := FixedDescriptionBoundedSimulatorHandoffTape
          Direction.right)
        (exitTape := FixedDescriptionBoundedSimulatorLayoutTape)
        (phaseA := fun L =>
          MachineDescription.SimulatorLayout.run D L.stage L)
        (phaseB := id)
        (A := runCode)
        (B := finalPause)
        (handoffMove := Direction.left)
        hRun hPause
  simpa [simulateStep, enterRun, runAndReturn] using
    fixedDescriptionBoundedSimulatorPhaseRealizes_seq
      (entryTape := FixedDescriptionBoundedSimulatorHandoffTape
        Direction.right)
      (midTape := FixedDescriptionBoundedSimulatorHandoffTape
        Direction.right)
      (exitTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (phaseA := id)
      (phaseB := fun L =>
        MachineDescription.SimulatorLayout.run D L.stage L)
      (A := enterRun)
      (B := runAndReturn)
      (handoffMove := Direction.left)
      hEnterRun hRunAndReturn

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

theorem fixedDescriptionBoundedSimulatorCodeRightShiftedConstruction_scaffold_configRunner :
    FoC.Computability.FixedDescriptionBoundedSimulatorCodeRightShiftedConstruction :=
  FoC.Computability.fixedDescriptionBoundedSimulatorCodeRightShiftedConstruction_scaffold

theorem fixedDescriptionBoundedSimulatorStepPhaseConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorStepPhaseConstruction_configRunner :=
  fixedDescriptionBoundedSimulatorStepPhaseConstruction_of_rightShifted_configRunner
    fixedDescriptionBoundedSimulatorCodeRightShiftedConstruction_scaffold_configRunner

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
