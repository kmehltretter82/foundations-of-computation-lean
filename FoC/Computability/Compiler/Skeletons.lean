import FoC.Computability.Compiler.Core

set_option doc.verso true

/-!
# Fixed-simulator skeleton compiler bridges
-/

namespace FoC
namespace Computability

open Languages

structure FixedDescriptionBoundedSimulatorPhaseTargets
    (D : MachineDescription) where
  decodeLayout :
    MachineDescription.SimulatorLayout ->
      MachineDescription.SimulatorLayout
  simulateStep :
    MachineDescription.SimulatorLayout ->
      MachineDescription.SimulatorLayout
  repeatControl :
    MachineDescription.SimulatorLayout ->
      MachineDescription.SimulatorLayout
  emitLayout :
    MachineDescription.SimulatorLayout ->
      MachineDescription.SimulatorLayout
  pipeline_correct :
    forall L : MachineDescription.SimulatorLayout,
      emitLayout (repeatControl (simulateStep (decodeLayout L))) =
        MachineDescription.SimulatorLayout.run D L.stage L

namespace FixedDescriptionBoundedSimulatorPhaseTargets

def canonical (D : MachineDescription) :
    FixedDescriptionBoundedSimulatorPhaseTargets D where
  decodeLayout := id
  simulateStep := fun L =>
    MachineDescription.SimulatorLayout.run D L.stage L
  repeatControl := id
  emitLayout := id
  pipeline_correct := by
    intro L
    rfl

theorem canonical_pipeline_correct
    (D : MachineDescription) (L : MachineDescription.SimulatorLayout) :
    (canonical D).emitLayout
        ((canonical D).repeatControl
          ((canonical D).simulateStep ((canonical D).decodeLayout L))) =
      MachineDescription.SimulatorLayout.run D L.stage L :=
  (canonical D).pipeline_correct L

end FixedDescriptionBoundedSimulatorPhaseTargets

def FixedDescriptionBoundedSimulatorLayoutTape
    (L : MachineDescription.SimulatorLayout) : Tape Bool :=
  MachineDescription.SimulatorLayout.tape L

def FixedDescriptionBoundedSimulatorHandoffTape
    (handoffMove : Direction)
    (L : MachineDescription.SimulatorLayout) : Tape Bool :=
  Tape.move handoffMove (FixedDescriptionBoundedSimulatorLayoutTape L)

def FixedDescriptionBoundedSimulatorFragmentReaches
    (entryTape exitTape :
      MachineDescription.SimulatorLayout -> Tape Bool)
    (phase :
      MachineDescription.SimulatorLayout ->
        MachineDescription.SimulatorLayout)
    (fragment : MachineDescription.Fragment)
    (L : MachineDescription.SimulatorLayout) : Prop :=
  exists n : Nat,
    fragment.toDescription.runConfig n
        { state := fragment.entry, tape := entryTape L } =
      { state := fragment.exit, tape := exitTape (phase L) } ∧
      forall k : Nat,
        k < n ->
          (fragment.toDescription.runConfig k
            { state := fragment.entry, tape := entryTape L }).state ≠
            fragment.exit

def FixedDescriptionBoundedSimulatorFragmentRealizes
    (entryTape exitTape :
      MachineDescription.SimulatorLayout -> Tape Bool)
    (phase :
      MachineDescription.SimulatorLayout ->
        MachineDescription.SimulatorLayout)
    (fragment : MachineDescription.Fragment) : Prop :=
  fragment.WellFormed ∧
    forall L : MachineDescription.SimulatorLayout,
      FixedDescriptionBoundedSimulatorFragmentReaches
        entryTape exitTape phase fragment L

abbrev FixedDescriptionBoundedSimulatorPhaseRealizes :=
  FixedDescriptionBoundedSimulatorFragmentRealizes

theorem fixedDescriptionBoundedSimulatorPhaseRealizes_standard_output
    {phase :
      MachineDescription.SimulatorLayout ->
        MachineDescription.SimulatorLayout}
    {fragment : MachineDescription.Fragment}
    (h :
      FixedDescriptionBoundedSimulatorPhaseRealizes
        FixedDescriptionBoundedSimulatorLayoutTape
        FixedDescriptionBoundedSimulatorLayoutTape
        phase fragment) :
    fragment.WellFormed ∧
      forall L : MachineDescription.SimulatorLayout,
        fragment.toDescription.HaltsWithOutput
          (FixedDescriptionBoundedSimulatorInput L)
          (FixedDescriptionBoundedSimulatorInput (phase L)) := by
  constructor
  · exact h.left
  · intro L
    rcases h.right L with ⟨n, hn, _hminimal⟩
    exists n
    have hstate :
        (fragment.toDescription.runConfig n
          (fragment.toDescription.initial
            (FixedDescriptionBoundedSimulatorInput L))).state =
          fragment.exit := by
      simpa [MachineDescription.Fragment.toDescription,
        FixedDescriptionBoundedSimulatorInput,
        FixedDescriptionBoundedSimulatorLayoutTape,
        MachineDescription.SimulatorLayout.tape] using congrArg
          (fun c : MachineDescription.Configuration => c.state) hn
    have htape :
        (fragment.toDescription.runConfig n
          (fragment.toDescription.initial
            (FixedDescriptionBoundedSimulatorInput L))).tape =
          FixedDescriptionBoundedSimulatorLayoutTape (phase L) := by
      simpa [MachineDescription.Fragment.toDescription,
        FixedDescriptionBoundedSimulatorInput,
        FixedDescriptionBoundedSimulatorLayoutTape,
        MachineDescription.SimulatorLayout.tape] using congrArg
          (fun c : MachineDescription.Configuration => c.tape) hn
    constructor
    · simpa [MachineDescription.Fragment.toDescription] using hstate
    · rw [htape]
      exact MachineDescription.SimulatorLayout.tape_normalizedOutput
        (phase L)

theorem fixedDescriptionBoundedSimulatorHandoffPhaseRealizes
    (move : Direction) :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      FixedDescriptionBoundedSimulatorLayoutTape
      (FixedDescriptionBoundedSimulatorHandoffTape move)
      id
      (MachineDescription.Fragment.handoff move) := by
  constructor
  · exact MachineDescription.Fragment.handoff_wellFormed move
  · intro L
    simpa [FixedDescriptionBoundedSimulatorLayoutTape,
      FixedDescriptionBoundedSimulatorHandoffTape] using
      MachineDescription.Fragment.handoff_firstReaches move
        (FixedDescriptionBoundedSimulatorLayoutTape L)

theorem fixedDescriptionBoundedSimulatorHaltPhaseRealizes
    (tape : MachineDescription.SimulatorLayout -> Tape Bool) :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      tape tape id MachineDescription.Fragment.halt := by
  constructor
  · exact MachineDescription.Fragment.halt_wellFormed
  · intro L
    exists 0
    constructor
    · rfl
    · intro k hk
      omega

theorem pairedRecognizerDovetailTotalStageAttemptSubroutineSequencingConstruction_scaffold :
    PairedRecognizerDovetailTotalStageAttemptSubroutineSequencingConstruction := by
  intro accept reject initializer runner emitter
    hinitializer hrunner hemitter
  let initRunner :=
    MachineDescription.seqSubroutine initializer runner
      tapeCodePrimitiveCodeWordHandoffMove
  let attempt :=
    MachineDescription.seqSubroutine initRunner emitter
      tapeCodePrimitiveCodeWordHandoffMove
  refine ⟨attempt, ?_⟩
  have hfirst :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (MachineDescription.TapeCodePrimitive.compose
          (PairedRecognizerDovetailInitialLayoutCode accept reject)
          (PairedRecognizerDovetailLayoutCode accept reject))
        initRunner tapeCodePrimitiveCodeWordHandoffMove :=
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_compose
      hinitializer hrunner
  have hsecond :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (MachineDescription.TapeCodePrimitive.compose
          (MachineDescription.TapeCodePrimitive.compose
            (PairedRecognizerDovetailInitialLayoutCode accept reject)
            (PairedRecognizerDovetailLayoutCode accept reject))
          PairedRecognizerDovetailTotalOutputCode)
        attempt tapeCodePrimitiveCodeWordHandoffMove :=
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_compose
      hfirst hemitter
  have houtput :
      TapeCodePrimitiveOutputCompiledSubroutineByDescription
        (MachineDescription.TapeCodePrimitive.compose
          (MachineDescription.TapeCodePrimitive.compose
            (PairedRecognizerDovetailInitialLayoutCode accept reject)
            (PairedRecognizerDovetailLayoutCode accept reject))
          PairedRecognizerDovetailTotalOutputCode)
        attempt :=
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_outputCompiled
      hsecond
  simpa [PairedRecognizerDovetailTotalStageAttemptSourceCode,
    initRunner, attempt] using houtput

theorem pairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction_scaffold :
    PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction :=
  pairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction_of_finiteSourceComponents
    pairedRecognizerDovetailStageInputInitializerClosedHandoffCompiledSubroutineConstruction_scaffold
    pairedRecognizerDovetailBoundedLayoutRunnerClosedHandoffCompiledSubroutineConstruction_scaffold
    pairedRecognizerDovetailTotalOutputEmitterClosedHandoffCompiledSubroutineConstruction_scaffold
    pairedRecognizerDovetailTotalStageAttemptSubroutineSequencingConstruction_scaffold

def pairedRecognizerDovetailFiniteControllerCompilerCloseout_scaffold :
    PairedRecognizerDovetailFiniteControllerCompilerCloseout where
  totalStageAttemptSubroutine :=
    pairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction_scaffold
  finiteStageLoopController :=
    pairedRecognizerDovetailFiniteStageLoopControllerConstruction_scaffold

theorem pairedRecognizerDovetailTotalStageAttemptHandoffSubroutineRealizerSequencingConstruction_scaffold :
    PairedRecognizerDovetailTotalStageAttemptHandoffSubroutineRealizerSequencingConstruction := by
  intro accept reject initializer runner emitter
    hinitializer hrunner hemitter
  let initRunner :=
    MachineDescription.seqSubroutine initializer runner
      tapeCodePrimitiveCodeWordHandoffMove
  let attempt :=
    MachineDescription.seqSubroutine initRunner emitter
      tapeCodePrimitiveCodeWordHandoffMove
  refine ⟨attempt, ?_⟩
  have hinitRealized :
      TapeCodePrimitiveHandoffSubroutineRealizedByDescription
        (PairedRecognizerDovetailInitialLayoutCode accept reject)
        initializer tapeCodePrimitiveCodeWordHandoffMove :=
    tapeCodePrimitiveHandoffSubroutineRealizedByDescription_of_handoffCompiled
      hinitializer
  have hrunnerRealized :
      TapeCodePrimitiveHandoffSubroutineRealizedByDescription
        (PairedRecognizerDovetailLayoutCode accept reject)
        runner tapeCodePrimitiveCodeWordHandoffMove :=
    tapeCodePrimitiveHandoffSubroutineRealizedByDescription_of_handoffCompiled
      hrunner
  have hemitterRealized :
      TapeCodePrimitiveHandoffSubroutineRealizedByDescription
        PairedRecognizerDovetailTotalOutputCode
        emitter tapeCodePrimitiveCodeWordHandoffMove :=
    tapeCodePrimitiveHandoffSubroutineRealizedByDescription_of_handoffCompiled
      hemitter
  have hfirst :
      TapeCodePrimitiveHandoffSubroutineRealizedByDescription
        (MachineDescription.TapeCodePrimitive.compose
          (PairedRecognizerDovetailInitialLayoutCode accept reject)
          (PairedRecognizerDovetailLayoutCode accept reject))
        initRunner tapeCodePrimitiveCodeWordHandoffMove :=
    tapeCodePrimitiveHandoffSubroutineRealizedByDescription_compose
      hinitRealized hrunnerRealized
  have hsecond :
      TapeCodePrimitiveHandoffSubroutineRealizedByDescription
        (MachineDescription.TapeCodePrimitive.compose
          (MachineDescription.TapeCodePrimitive.compose
            (PairedRecognizerDovetailInitialLayoutCode accept reject)
            (PairedRecognizerDovetailLayoutCode accept reject))
          PairedRecognizerDovetailTotalOutputCode)
        attempt tapeCodePrimitiveCodeWordHandoffMove :=
    tapeCodePrimitiveHandoffSubroutineRealizedByDescription_compose
      hfirst hemitterRealized
  simpa [PairedRecognizerDovetailTotalStageAttemptSourceCode,
    initRunner, attempt] using hsecond

theorem pairedRecognizerDovetailTotalStageAttemptCodeHandoffSubroutineRealizerConstruction_scaffold :
    PairedRecognizerDovetailTotalStageAttemptCodeHandoffSubroutineRealizerConstruction :=
  pairedRecognizerDovetailTotalStageAttemptCodeHandoffSubroutineRealizerConstruction_of_finiteSourceHandoffComponents
    pairedRecognizerDovetailStageInputInitializerHandoffCompiledSubroutineConstruction_scaffold
    pairedRecognizerDovetailBoundedLayoutRunnerHandoffCompiledSubroutineConstruction_scaffold
    pairedRecognizerDovetailTotalOutputEmitterHandoffCompiledSubroutineConstruction_scaffold
    pairedRecognizerDovetailTotalStageAttemptHandoffSubroutineRealizerSequencingConstruction_scaffold

theorem pairedRecognizerDovetailTotalStageAttemptCodeOutputSubroutineRealizerConstruction_scaffold :
    PairedRecognizerDovetailTotalStageAttemptCodeOutputSubroutineRealizerConstruction :=
  pairedRecognizerDovetailTotalStageAttemptCodeOutputSubroutineRealizerConstruction_of_handoff
    pairedRecognizerDovetailTotalStageAttemptCodeHandoffSubroutineRealizerConstruction_scaffold

theorem fixedDescriptionBoundedSimulatorPhaseRealizes_seq
    {entryTape midTape exitTape :
      MachineDescription.SimulatorLayout -> Tape Bool}
    {phaseA phaseB :
      MachineDescription.SimulatorLayout ->
        MachineDescription.SimulatorLayout}
    {A B : MachineDescription.Fragment} {handoffMove : Direction}
    (hA :
      FixedDescriptionBoundedSimulatorPhaseRealizes
        entryTape midTape phaseA A)
    (hB :
      FixedDescriptionBoundedSimulatorPhaseRealizes
        (fun L => Tape.move handoffMove (midTape L))
        exitTape phaseB B) :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      entryTape exitTape (fun L => phaseB (phaseA L))
      (MachineDescription.Fragment.seq A B handoffMove) := by
  constructor
  · exact MachineDescription.Fragment.seq_wellFormed hA.left hB.left
  · intro L
    simpa [FixedDescriptionBoundedSimulatorFragmentReaches] using
      MachineDescription.Fragment.seq_firstReaches
        (A := A) (B := B) (handoffMove := handoffMove)
        hA.left hB.left
        (Tin := entryTape L)
        (Tmid := midTape (phaseA L))
        (Tout := exitTape (phaseB (phaseA L)))
        (hA.right L)
        (hB.right (phaseA L))

structure FixedDescriptionBoundedSimulatorSkeletonPhaseRealizes
    (D : MachineDescription)
    (S : MachineDescription.FixedSimulatorTableSkeleton)
    (handoffMove : Direction)
    (targets : FixedDescriptionBoundedSimulatorPhaseTargets D) :
    Prop where
  decodeLayout :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      FixedDescriptionBoundedSimulatorLayoutTape
      FixedDescriptionBoundedSimulatorLayoutTape
      targets.decodeLayout S.decodeLayout
  simulateStep :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      (FixedDescriptionBoundedSimulatorHandoffTape handoffMove)
      FixedDescriptionBoundedSimulatorLayoutTape
      targets.simulateStep S.simulateStep
  repeatControl :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      (FixedDescriptionBoundedSimulatorHandoffTape handoffMove)
      FixedDescriptionBoundedSimulatorLayoutTape
      targets.repeatControl S.repeatControl
  emitLayout :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      (FixedDescriptionBoundedSimulatorHandoffTape handoffMove)
      FixedDescriptionBoundedSimulatorLayoutTape
      targets.emitLayout S.emitLayout

def FixedDescriptionBoundedSimulatorSkeletonRealizes
    (D : MachineDescription)
    (S : MachineDescription.FixedSimulatorTableSkeleton)
    (handoffMove : Direction) : Prop :=
  forall L : MachineDescription.SimulatorLayout,
    (S.toDescription handoffMove).HaltsWithOutput
      (FixedDescriptionBoundedSimulatorInput L)
      (FixedDescriptionBoundedSimulatorOutput D L)

def FixedDescriptionBoundedSimulatorSkeletonRealizesExact
    (D : MachineDescription)
    (S : MachineDescription.FixedSimulatorTableSkeleton)
    (handoffMove : Direction) : Prop :=
  forall L : MachineDescription.SimulatorLayout,
    (S.toDescription handoffMove).HaltsWithExactOutput
      (FixedDescriptionBoundedSimulatorInput L)
      (FixedDescriptionBoundedSimulatorOutput D L)

theorem fixedDescriptionBoundedSimulatorSkeletonRealizes_of_exact
    {D : MachineDescription}
    {S : MachineDescription.FixedSimulatorTableSkeleton}
    {handoffMove : Direction}
    (h : FixedDescriptionBoundedSimulatorSkeletonRealizesExact
      D S handoffMove) :
    FixedDescriptionBoundedSimulatorSkeletonRealizes D S handoffMove := by
  intro L
  exact MachineDescription.haltsWithOutput_of_haltsWithExactOutput
    (h L)

theorem fixedDescriptionBoundedSimulatorTableRealizes_of_skeletonRealizes
    {D : MachineDescription}
    {S : MachineDescription.FixedSimulatorTableSkeleton}
    {handoffMove : Direction}
    (h : FixedDescriptionBoundedSimulatorSkeletonRealizes
      D S handoffMove) :
    FixedDescriptionBoundedSimulatorTableRealizes
      D (S.toDescription handoffMove) := by
  constructor
  · exact
      MachineDescription.FixedSimulatorTableSkeleton.toDescription_wellFormed
        S handoffMove
  · exact h

theorem fixedDescriptionBoundedSimulatorSkeletonRealizes_output
    {D : MachineDescription}
    {S : MachineDescription.FixedSimulatorTableSkeleton}
    {handoffMove : Direction}
    (h : FixedDescriptionBoundedSimulatorSkeletonRealizes
      D S handoffMove)
    (L : MachineDescription.SimulatorLayout) :
    (S.toDescription handoffMove).HaltsWithOutput
      (FixedDescriptionBoundedSimulatorInput L)
      (FixedDescriptionBoundedSimulatorOutput D L) :=
  h L

def FixedDescriptionBoundedSimulatorSkeletonCompilerConstruction : Prop :=
  forall D : MachineDescription,
    exists S : MachineDescription.FixedSimulatorTableSkeleton,
      exists handoffMove : Direction,
        FixedDescriptionBoundedSimulatorSkeletonRealizes D S handoffMove

theorem fixedDescriptionBoundedSimulatorTableCompiler_of_skeletonCompiler
    (hcompile :
      FixedDescriptionBoundedSimulatorSkeletonCompilerConstruction) :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction := by
  intro D
  rcases hcompile D with ⟨S, handoffMove, hS⟩
  exact ⟨S.toDescription handoffMove,
    fixedDescriptionBoundedSimulatorTableRealizes_of_skeletonRealizes hS⟩

def FixedDescriptionBoundedSimulatorSkeletonPhaseConstruction : Prop :=
  forall D : MachineDescription,
    exists S : MachineDescription.FixedSimulatorTableSkeleton,
      exists handoffMove : Direction,
      exists targets : FixedDescriptionBoundedSimulatorPhaseTargets D,
        FixedDescriptionBoundedSimulatorSkeletonPhaseRealizes
          D S handoffMove targets

def FixedDescriptionBoundedSimulatorSkeletonPhaseSoundness : Prop :=
  forall D : MachineDescription,
    forall S : MachineDescription.FixedSimulatorTableSkeleton,
    forall handoffMove : Direction,
    forall targets : FixedDescriptionBoundedSimulatorPhaseTargets D,
      FixedDescriptionBoundedSimulatorSkeletonPhaseRealizes
        D S handoffMove targets ->
      FixedDescriptionBoundedSimulatorSkeletonRealizes D S handoffMove

theorem fixedDescriptionBoundedSimulatorSkeletonPhaseSoundness :
    FixedDescriptionBoundedSimulatorSkeletonPhaseSoundness := by
  intro D S handoffMove targets htargets
  have hDecodeSim :
      FixedDescriptionBoundedSimulatorPhaseRealizes
        FixedDescriptionBoundedSimulatorLayoutTape
        FixedDescriptionBoundedSimulatorLayoutTape
        (fun L => targets.simulateStep (targets.decodeLayout L))
        (MachineDescription.Fragment.seq
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
        (MachineDescription.Fragment.seq
          (MachineDescription.Fragment.seq
            S.decodeLayout S.simulateStep handoffMove)
          S.repeatControl handoffMove) :=
    fixedDescriptionBoundedSimulatorPhaseRealizes_seq
      (entryTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (midTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (exitTape := FixedDescriptionBoundedSimulatorLayoutTape)
      (phaseA := fun L =>
        targets.simulateStep (targets.decodeLayout L))
      (phaseB := targets.repeatControl)
      (A := MachineDescription.Fragment.seq
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
        (MachineDescription.Fragment.seq
          (MachineDescription.Fragment.seq
            (MachineDescription.Fragment.seq
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
      (A := MachineDescription.Fragment.seq
        (MachineDescription.Fragment.seq
          S.decodeLayout S.simulateStep handoffMove)
        S.repeatControl handoffMove)
      (B := S.emitLayout)
      (handoffMove := handoffMove)
      hDecodeSimRepeat htargets.emitLayout
  intro L
  have hOutput :=
    (fixedDescriptionBoundedSimulatorPhaseRealizes_standard_output
      hAllPhases).right L
  have hpipeline :
      targets.emitLayout
          (targets.repeatControl
            (targets.simulateStep (targets.decodeLayout L))) =
        MachineDescription.SimulatorLayout.run D L.stage L :=
    targets.pipeline_correct L
  simpa [MachineDescription.FixedSimulatorTableSkeleton.toDescription,
    MachineDescription.FixedSimulatorTableSkeleton.toFragment,
    FixedDescriptionBoundedSimulatorOutput, hpipeline] using hOutput

theorem fixedDescriptionBoundedSimulatorSkeletonCompiler_of_phaseCompiler
    (hsound : FixedDescriptionBoundedSimulatorSkeletonPhaseSoundness)
    (hcompile :
      FixedDescriptionBoundedSimulatorSkeletonPhaseConstruction) :
      FixedDescriptionBoundedSimulatorSkeletonCompilerConstruction := by
  intro D
  rcases hcompile D with ⟨S, handoffMove, targets, htargets⟩
  exact ⟨S, handoffMove,
    hsound D S handoffMove targets htargets⟩

theorem fixedDescriptionBoundedSimulatorTableCompiler_of_phaseCompiler
    (hsound : FixedDescriptionBoundedSimulatorSkeletonPhaseSoundness)
    (hcompile :
      FixedDescriptionBoundedSimulatorSkeletonPhaseConstruction) :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction :=
  fixedDescriptionBoundedSimulatorTableCompiler_of_skeletonCompiler
    (fixedDescriptionBoundedSimulatorSkeletonCompiler_of_phaseCompiler
      hsound hcompile)

theorem pairedRecognizerDovetailDescriptionCompiler_of_dovetailDescriptionCompiler
    (hcompile : DovetailDescriptionCompilerPrinciple) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple := by
  intro accept reject
  exact hcompile
    (fun w n => accept.HaltsIn n w)
    (fun w n => reject.HaltsIn n w)

theorem pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    (hcompile :
      PairedRecognizerBoundedDovetailTableCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple := by
  intro accept reject
  cases hcompile accept reject with
  | intro decider hdecider =>
      exists decider
      constructor
      · exact hdecider.left
      · intro w b
        constructor
        · intro hhalt
          cases (hdecider.right w b).mp hhalt with
          | intro limit hlimit =>
              exists limit
              rwa [MachineDescription.boundedDovetailOutput_eq_dovetailProgram_run]
                at hlimit
        · intro hprog
          cases hprog with
          | intro limit hlimit =>
              apply (hdecider.right w b).mpr
              exists limit
              rwa [MachineDescription.boundedDovetailOutput_eq_dovetailProgram_run]

theorem pairedRecognizerBoundedDovetailTableCompiler_of_pairedRecognizerDovetailDescriptionCompiler
    (hcompile : PairedRecognizerDovetailDescriptionCompilerPrinciple) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction := by
  intro accept reject
  rcases hcompile accept reject with ⟨decider, hdecider⟩
  refine ⟨decider, ?_⟩
  constructor
  · exact hdecider.left
  · intro w b
    constructor
    · intro hhalt
      rcases (hdecider.right w b).mp hhalt with ⟨limit, hlimit⟩
      exact
        ⟨limit, by
          simpa [MachineDescription.boundedDovetailOutput_eq_dovetailProgram_run]
            using hlimit⟩
    · intro hlimit
      rcases hlimit with ⟨limit, hlimit⟩
      apply (hdecider.right w b).mpr
      exact
        ⟨limit, by
          simpa [MachineDescription.boundedDovetailOutput_eq_dovetailProgram_run]
            using hlimit⟩

theorem pairedRecognizerBoundedDovetailTableCompiler_iff_pairedRecognizerDovetailDescriptionCompiler :
    PairedRecognizerBoundedDovetailTableCompilerConstruction <->
      PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  ⟨pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler,
    pairedRecognizerBoundedDovetailTableCompiler_of_pairedRecognizerDovetailDescriptionCompiler⟩

theorem pairedRecognizerDovetailDescriptionCompiler_of_layoutCodeOutputRealizer_and_searchDriver
    (hrunner :
      PairedRecognizerDovetailLayoutCodeOutputRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    (pairedRecognizerBoundedDovetailTableCompiler_of_layoutCodeOutputRealizer_and_searchDriver
      hrunner hdriver)

theorem pairedRecognizerDovetailDescriptionCompiler_of_stageAttemptCodeOutputRealizer_and_stageAttemptSearchDriver
    (hattempt :
      PairedRecognizerDovetailStageAttemptCodeOutputRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailStageAttemptSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    (pairedRecognizerBoundedDovetailTableCompiler_of_stageAttemptCodeOutputRealizer_and_stageAttemptSearchDriver
      hattempt hdriver)

theorem pairedRecognizerDovetailDescriptionCompiler_of_tapeCodeOutputCompiler_and_descriptionBoolDeciderCompiler
    (htape : MachineDescriptionTapeCodeOutputCompilerConstruction)
    (hbool : DescriptionProgramBoolDeciderCompilationPrinciple) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_stageAttemptCodeOutputRealizer_and_stageAttemptSearchDriver
    (pairedRecognizerDovetailStageAttemptCodeOutputRealizer_of_tapeCodeOutputCompiler
      htape)
    (pairedRecognizerDovetailStageAttemptSearchDriverCompiler_of_descriptionBoolDeciderCompiler
      hbool)

theorem pairedRecognizerDovetailDescriptionCompiler_of_totalStageAttemptCodeOutputSubroutineRealizer_and_totalStageAttemptSearchDriver
    (hattempt :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputSubroutineRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailTotalStageAttemptSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    (pairedRecognizerBoundedDovetailTableCompiler_of_totalStageAttemptCodeOutputSubroutineRealizer_and_totalStageAttemptSearchDriver
      hattempt hdriver)

theorem pairedRecognizerDovetailDescriptionCompiler_of_totalStageAttemptCodeOutputCompiledSubroutine_and_controllerSearchDriver
    (hattempt :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction)
    (hdriver :
      PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    (pairedRecognizerBoundedDovetailTableCompiler_of_totalStageAttemptCodeOutputCompiledSubroutine_and_controllerSearchDriver
      hattempt hdriver)

theorem pairedRecognizerDovetailDescriptionCompiler_of_controllerCompilerCloseout
    (hclose : PairedRecognizerDovetailControllerCompilerCloseout) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    (pairedRecognizerBoundedDovetailTableCompiler_of_controllerCompilerCloseout
      hclose)

theorem pairedRecognizerDovetailDescriptionCompiler_of_finiteControllerCompilerCloseout
    (hclose : PairedRecognizerDovetailFiniteControllerCompilerCloseout) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    (pairedRecognizerBoundedDovetailTableCompiler_of_finiteControllerCompilerCloseout
      hclose)

theorem finiteSourcePairedRecognizerDovetailCompilerConstruction_scaffold :
    FiniteSourcePairedRecognizerDovetailCompilerConstruction :=
  pairedRecognizerDovetailDescriptionCompiler_of_finiteControllerCompilerCloseout
    pairedRecognizerDovetailFiniteControllerCompilerCloseout_scaffold

theorem pairedRecognizerDovetailDescriptionCompiler_of_totalStageAttemptCodeOutputCompiledSubroutine_and_descriptionBoolDeciderCompiler
    (hattempt :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction)
    (hbool : DescriptionProgramBoolDeciderCompilationPrinciple) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_totalStageAttemptCodeOutputCompiledSubroutine_and_controllerSearchDriver
    hattempt
    (pairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompiler_of_descriptionBoolDeciderCompiler
      hbool)

theorem pairedRecognizerDovetailDescriptionCompiler_of_layoutCodeOutputSubroutineRealizer_and_subroutineSearchDriver
    (hrunner :
      PairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailSubroutineSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    (pairedRecognizerBoundedDovetailTableCompiler_of_layoutCodeOutputSubroutineRealizer_and_subroutineSearchDriver
      hrunner hdriver)

theorem pairedRecognizerDovetailDescriptionCompiler_of_layoutCodeOutputSubroutineRealizer_and_subroutineRunnerSearchDriver
    (hrunner :
      PairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailSubroutineRunnerSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    (pairedRecognizerBoundedDovetailTableCompiler_of_layoutCodeOutputSubroutineRealizer_and_subroutineRunnerSearchDriver
      hrunner hdriver)

theorem dovetailDescriptionCompiler_of_descriptionBoolDeciderCompiler
    (hcompile : DescriptionProgramBoolDeciderCompilationPrinciple) :
    DovetailDescriptionCompilerPrinciple := by
  intro accept reject
  exact hcompile (DovetailProgram accept reject)

theorem pairedRecognizerDovetailDescriptionCompiler_of_descriptionBoolDeciderCompiler
    (hcompile : DescriptionProgramBoolDeciderCompilationPrinciple) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_dovetailDescriptionCompiler
    (dovetailDescriptionCompiler_of_descriptionBoolDeciderCompiler hcompile)

theorem programAcceptorCompilationPrinciple_of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple) :
    ProgramAcceptorCompilationPrinciple Bool := by
  intro L hL
  cases hL with
  | intro P hP =>
      cases hcompile P with
      | intro D hD =>
          exact programAcceptableByDescription_turingAcceptable
            (Exists.intro P (Exists.intro D (And.intro hP hD)))

theorem programBoolDeciderCompilationPrinciple_of_descriptionCompiler
    (hcompile : DescriptionProgramBoolDeciderCompilationPrinciple) :
    ProgramBoolDeciderCompilationPrinciple Bool := by
  intro L hL
  cases hL with
  | intro P hP =>
      cases hcompile P with
      | intro D hD =>
          exact programBoolDecidableByDescription_turingDecidable
            (Exists.intro P (Exists.intro D (And.intro hP hD)))

theorem complementaryTraces_turingDecidable_of_dovetailDescriptionCompiler
    (hcompile : DovetailDescriptionCompilerPrinciple)
    {L : Language Bool}
    {accept reject : Word Bool -> Nat -> Prop}
    (htraces : ComplementaryAcceptanceTraces accept reject L) :
    TuringDecidable L := by
  cases hcompile accept reject with
  | intro D hD =>
      exact programBoolDecidableByDescription_turingDecidable
        (Exists.intro (DovetailProgram accept reject)
          (Exists.intro D (And.intro (dovetailProgram_decides htraces) hD)))

theorem reCoRe_turingDecidable_of_dovetailDescriptionCompiler
    (hcompile : DovetailDescriptionCompilerPrinciple)
    {L : Language Bool}
    (h : RecursivelyEnumerableWithComplement L) :
    TuringDecidable L := by
  cases recursivelyEnumerable_with_complement_has_complementaryTraces h with
  | intro accept haccept =>
      cases haccept with
      | intro reject htraces =>
          exact complementaryTraces_turingDecidable_of_dovetailDescriptionCompiler
            hcompile htraces

theorem reCoReToDecidablePrinciple_of_dovetailDescriptionCompiler
    (hcompile : DovetailDescriptionCompilerPrinciple) :
    ReCoReToDecidablePrinciple Bool := by
  intro L h
  exact reCoRe_turingDecidable_of_dovetailDescriptionCompiler hcompile h

end Computability
end FoC
