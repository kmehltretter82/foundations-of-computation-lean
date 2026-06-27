import FoC.Computability.Compiler.SeqSubroutineSemantics
import FoC.Computability.Compiler.Core.BoundedTrace

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

theorem fixedDescriptionBoundedSimulatorReturnFromRightHandoffPhaseRealizes :
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
    FixedDescriptionBoundedSimulatorTableCompilerConstruction :=
  fun D =>
    Exists.elim (hcompile D) fun S hS =>
      Exists.elim hS fun handoffMove hrealizes =>
        ⟨S.toDescription handoffMove,
          fixedDescriptionBoundedSimulatorTableRealizes_of_skeletonRealizes
            hrealizes⟩

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
      FixedDescriptionBoundedSimulatorSkeletonCompilerConstruction :=
  fun D =>
    Exists.elim (hcompile D) fun S hS =>
      Exists.elim hS fun handoffMove hmove =>
        Exists.elim hmove fun targets htargets =>
          ⟨S, handoffMove, hsound D S handoffMove targets htargets⟩

theorem fixedDescriptionBoundedSimulatorTableCompiler_of_phaseCompiler
    (hsound : FixedDescriptionBoundedSimulatorSkeletonPhaseSoundness)
    (hcompile :
      FixedDescriptionBoundedSimulatorSkeletonPhaseConstruction) :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction :=
  fixedDescriptionBoundedSimulatorTableCompiler_of_skeletonCompiler
    (fixedDescriptionBoundedSimulatorSkeletonCompiler_of_phaseCompiler
      hsound hcompile)

end Computability
end FoC
