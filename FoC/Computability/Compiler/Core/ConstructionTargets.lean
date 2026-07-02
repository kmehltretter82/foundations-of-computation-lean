import FoC.Computability.Compiler.Core.CommonGround.Controller
import FoC.Computability.Compiler.Core.CommonGround.CodeWordEmitters
import FoC.Computability.Compiler.Core.CommonGround.Layouts
import FoC.Computability.Compiler.Core.CommonGround.SearchAlgebra
import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.Basic
import FoC.Computability.Compiler.Core.TapeCodePrimitiveSequencing

set_option doc.verso true

/-!
# Finite compiler construction targets
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

def MachineDescriptionTapeCodeExactCompilerConstruction : Prop :=
  forall P : TapeCodePrimitive,
    exists D : MachineDescription,
      TapeCodePrimitiveCompiledByDescription P D

def MachineDescriptionTapeCodeOutputCompilerConstruction : Prop :=
  forall P : TapeCodePrimitive,
    exists D : MachineDescription,
      TapeCodePrimitiveOutputRealizedByDescription P D

theorem not_machineDescriptionTapeCodeExactCompilerConstruction :
    ¬ MachineDescriptionTapeCodeExactCompilerConstruction := by
  intro hcompile
  rcases hcompile TapeCodePrimitive.erase with
    ⟨D, hD⟩
  exact not_tapeCodePrimitiveCompiledByDescription_erase ⟨D, hD⟩

theorem machineDescriptionTapeCodeOutputCompiler_realizes
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction)
    (P : TapeCodePrimitive) :
    exists D : MachineDescription,
      TapeCodePrimitiveOutputRealizedByDescription P D :=
  hcompile P

def TapeCodePrimitiveCodeComposition
    (A B C : MachineDescription) : Prop :=
  C.WellFormed ∧
    forall code out : Word MachineCodeSymbol,
      C.HaltsWithExactOutput
        (encodeCodeWordAsInput code)
        (encodeCodeWordAsInput out) <->
        exists mid : Word MachineCodeSymbol,
          A.HaltsWithExactOutput
              (encodeCodeWordAsInput code)
              (encodeCodeWordAsInput mid) ∧
            B.HaltsWithExactOutput
              (encodeCodeWordAsInput mid)
              (encodeCodeWordAsInput out)

theorem tapeCodePrimitiveCompiledByDescription_compose
    {P Q : TapeCodePrimitive}
    {A B C : MachineDescription}
    (hcomp : TapeCodePrimitiveCodeComposition A B C)
    (hP : TapeCodePrimitiveCompiledByDescription P A)
    (hQ : TapeCodePrimitiveCompiledByDescription Q B) :
    TapeCodePrimitiveCompiledByDescription
      (TapeCodePrimitive.compose P Q) C := by
  constructor
  · exact hcomp.left
  · intro code out
    constructor
    · intro h
      rcases (hcomp.right code out).mp h with
        ⟨mid, hA, hB⟩
      have hPmid : P.transform code = some mid :=
        (hP.right code mid).mp hA
      have hQout : Q.transform mid = some out :=
        (hQ.right mid out).mp hB
      exact
        TapeCodePrimitive.compose_transform_some
          hPmid hQout
    · intro h
      unfold TapeCodePrimitive.compose at h
      cases hPcode : P.transform code with
      | none =>
          simp [hPcode] at h
      | some mid =>
          have hQout : Q.transform mid = some out := by
            simpa [hPcode] using h
          apply (hcomp.right code out).mpr
          exists mid
          constructor
          · exact (hP.right code mid).mpr hPcode
          · exact (hQ.right mid out).mpr hQout

def FixedDescriptionBoundedSimulatorCodeCompilerConstruction : Prop :=
  forall D : MachineDescription,
    exists simulator : MachineDescription,
      TapeCodePrimitiveCompiledByDescription
        (FixedDescriptionBoundedSimulatorCode D) simulator

def FixedDescriptionBoundedSimulatorCodeOutputRealizerConstruction : Prop :=
  forall D : MachineDescription,
    exists simulator : MachineDescription,
      TapeCodePrimitiveOutputRealizedByDescription
        (FixedDescriptionBoundedSimulatorCode D) simulator

def FixedDescriptionBoundedSimulatorCodeRightShiftedConstruction : Prop :=
  forall D : MachineDescription,
    exists simulator : MachineDescription,
      EncodedRewriters.RightShiftedOutputCompiledSubroutineByDescription
        (FixedDescriptionBoundedSimulatorCode D) simulator

def FixedDescriptionStepCodeCompilerConstruction : Prop :=
  forall D : MachineDescription,
    exists stepper : MachineDescription,
      TapeCodePrimitiveCompiledByDescription
        (FixedDescriptionStepCode D) stepper

def FixedDescriptionStepCodeOutputRealizerConstruction : Prop :=
  forall D : MachineDescription,
    exists stepper : MachineDescription,
      TapeCodePrimitiveOutputRealizedByDescription
        (FixedDescriptionStepCode D) stepper

def FixedDescriptionStepCodeConfigurationRealizes
    (D stepper : MachineDescription) : Prop :=
  stepper.WellFormed ∧
    forall c : Configuration,
      stepper.HaltsWithOutput
        (encodeCodeWordAsInput
          (encodeConfiguration c))
        (encodeCodeWordAsInput
          (encodeConfiguration (D.runConfig 1 c)))

def FixedDescriptionStepCodeConfigurationRealizerConstruction : Prop :=
  forall D : MachineDescription,
    exists stepper : MachineDescription,
      FixedDescriptionStepCodeConfigurationRealizes D stepper

def PairedRecognizerDovetailInitialLayoutCodeOutputRealizerConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists builder : MachineDescription,
      TapeCodePrimitiveOutputRealizedByDescription
        (PairedRecognizerDovetailInitialLayoutCode accept reject)
        builder

def PairedRecognizerDovetailOutputCodeOutputRealizerConstruction : Prop :=
  exists inspector : MachineDescription,
    TapeCodePrimitiveOutputRealizedByDescription
      PairedRecognizerDovetailOutputCode inspector

def PairedRecognizerDovetailStageAttemptCodeOutputRealizerConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists attempt : MachineDescription,
      TapeCodePrimitiveOutputRealizedByDescription
        (PairedRecognizerDovetailStageAttemptCode accept reject)
        attempt

def PairedRecognizerDovetailTotalStageAttemptCodeOutputRealizerConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists attempt : MachineDescription,
      TapeCodePrimitiveOutputRealizedByDescription
        (PairedRecognizerDovetailTotalStageAttemptCode accept reject)
        attempt

def PairedRecognizerDovetailTotalThenRawOutputCodeOutputRealizerConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists attempt : MachineDescription,
      TapeCodePrimitiveOutputRealizedByDescription
        (PairedRecognizerDovetailTotalThenRawOutputCode accept reject)
        attempt

def PairedRecognizerDovetailControllerContinueCodeOutputRealizerConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists branch : MachineDescription,
      TapeCodePrimitiveOutputRealizedByDescription
        (PairedRecognizerDovetailControllerContinueCode accept reject)
        branch

def PairedRecognizerDovetailControllerEmitCodeOutputRealizerConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists branch : MachineDescription,
      TapeCodePrimitiveOutputRealizedByDescription
        (PairedRecognizerDovetailControllerEmitCode accept reject)
        branch

def PairedRecognizerDovetailTotalStageAttemptCodeOutputSubroutineRealizerConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists attempt : MachineDescription,
      TapeCodePrimitiveOutputSubroutineRealizedByDescription
        (PairedRecognizerDovetailTotalStageAttemptCode accept reject)
        attempt

def PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists attempt : MachineDescription,
      TapeCodePrimitiveOutputCompiledSubroutineByDescription
        (PairedRecognizerDovetailTotalStageAttemptCode accept reject)
        attempt

def PairedRecognizerDovetailStageInputInitializerCompiledSubroutineConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists initializer : MachineDescription,
      TapeCodePrimitiveOutputCompiledSubroutineByDescription
        (PairedRecognizerDovetailInitialLayoutCode accept reject)
        initializer

def PairedRecognizerDovetailBoundedLayoutRunnerCompiledSubroutineConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists runner : MachineDescription,
      TapeCodePrimitiveOutputCompiledSubroutineByDescription
        (PairedRecognizerDovetailLayoutCode accept reject)
        runner

def PairedRecognizerDovetailBoundedLayoutRunnerSpecConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists runner : MachineDescription,
      EncodedRewriters.BoundedLayoutRunner.Spec accept reject runner

def PairedRecognizerDovetailTotalOutputEmitterCompiledSubroutineConstruction :
    Prop :=
  exists emitter : MachineDescription,
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      PairedRecognizerDovetailTotalOutputCode
      emitter

def PairedRecognizerDovetailTotalOutputEmitterOutputSubroutineRealizerConstruction :
    Prop :=
  exists emitter : MachineDescription,
    TapeCodePrimitiveOutputSubroutineRealizedByDescription
      PairedRecognizerDovetailTotalOutputCode
      emitter

def PairedRecognizerDovetailStageInputInitializerHandoffCompiledSubroutineConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists initializer : MachineDescription,
      TapeCodePrimitiveHandoffCompiledSubroutineByDescription
        (PairedRecognizerDovetailInitialLayoutCode accept reject)
        initializer tapeCodePrimitiveCodeWordHandoffMove

/--
Obsolete compatibility target for the bounded runner.  The active bounded-runner
route is {name}`PairedRecognizerDovetailBoundedLayoutRunnerCompiledSubroutineConstruction`,
which uses the output-compiled padded/equivalence contract.
-/
def PairedRecognizerDovetailBoundedLayoutRunnerHandoffCompiledSubroutineConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists runner : MachineDescription,
      TapeCodePrimitiveHandoffCompiledSubroutineByDescription
        (PairedRecognizerDovetailLayoutCode accept reject)
        runner tapeCodePrimitiveCodeWordHandoffMove

def PairedRecognizerDovetailTotalOutputEmitterHandoffCompiledSubroutineConstruction :
    Prop :=
  exists emitter : MachineDescription,
    TapeCodePrimitiveHandoffCompiledSubroutineByDescription
      PairedRecognizerDovetailTotalOutputCode
      emitter tapeCodePrimitiveCodeWordHandoffMove

def PairedRecognizerDovetailStageInputInitializerClosedHandoffCompiledSubroutineConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists initializer : MachineDescription,
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (PairedRecognizerDovetailInitialLayoutCode accept reject)
        initializer tapeCodePrimitiveCodeWordHandoffMove

/--
Obsolete compatibility target for the bounded runner.  Exact closed handoff is
too strong for the padded/equivalence runner and has no active construction
scaffold.
-/
def PairedRecognizerDovetailBoundedLayoutRunnerClosedHandoffCompiledSubroutineConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists runner : MachineDescription,
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (PairedRecognizerDovetailLayoutCode accept reject)
        runner tapeCodePrimitiveCodeWordHandoffMove

def PairedRecognizerDovetailTotalOutputEmitterClosedHandoffCompiledSubroutineConstruction :
    Prop :=
  exists emitter : MachineDescription,
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      PairedRecognizerDovetailTotalOutputCode
      emitter tapeCodePrimitiveCodeWordHandoffMove

def PairedRecognizerDovetailTotalStageAttemptSubroutineSequencingConstruction :
    Prop :=
  forall accept reject initializer runner emitter : MachineDescription,
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      (PairedRecognizerDovetailInitialLayoutCode accept reject)
      initializer tapeCodePrimitiveCodeWordHandoffMove ->
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      (PairedRecognizerDovetailLayoutCode accept reject)
      runner tapeCodePrimitiveCodeWordHandoffMove ->
    TapeCodePrimitiveOutputSubroutineRealizedByDescription
      PairedRecognizerDovetailTotalOutputCode
      emitter ->
    exists attempt : MachineDescription,
      TapeCodePrimitiveOutputCompiledSubroutineByDescription
        (PairedRecognizerDovetailTotalStageAttemptSourceCode accept reject)
        attempt

def PairedRecognizerDovetailTotalStageAttemptOutputSubroutineSequencingConstruction :
    Prop :=
  forall accept reject initializer runner emitter : MachineDescription,
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      (PairedRecognizerDovetailInitialLayoutCode accept reject)
      initializer tapeCodePrimitiveCodeWordHandoffMove ->
    EncodedRewriters.BoundedLayoutRunner.Spec accept reject runner ->
    TapeCodePrimitiveOutputSubroutineRealizedByDescription
      PairedRecognizerDovetailTotalOutputCode
      emitter ->
    exists attempt : MachineDescription,
      TapeCodePrimitiveOutputCompiledSubroutineByDescription
        (PairedRecognizerDovetailTotalStageAttemptSourceCode accept reject)
        attempt

def PairedRecognizerDovetailTotalStageAttemptHandoffSubroutineRealizerSequencingConstruction :
    Prop :=
  forall accept reject initializer runner emitter : MachineDescription,
    TapeCodePrimitiveHandoffCompiledSubroutineByDescription
      (PairedRecognizerDovetailInitialLayoutCode accept reject)
      initializer tapeCodePrimitiveCodeWordHandoffMove ->
    TapeCodePrimitiveHandoffCompiledSubroutineByDescription
      (PairedRecognizerDovetailLayoutCode accept reject)
      runner tapeCodePrimitiveCodeWordHandoffMove ->
    TapeCodePrimitiveHandoffCompiledSubroutineByDescription
      PairedRecognizerDovetailTotalOutputCode
      emitter tapeCodePrimitiveCodeWordHandoffMove ->
    exists attempt : MachineDescription,
      TapeCodePrimitiveHandoffSubroutineRealizedByDescription
        (PairedRecognizerDovetailTotalStageAttemptSourceCode accept reject)
        attempt tapeCodePrimitiveCodeWordHandoffMove

def PairedRecognizerDovetailTotalStageAttemptCodeHandoffSubroutineRealizerConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists attempt : MachineDescription,
      TapeCodePrimitiveHandoffSubroutineRealizedByDescription
        (PairedRecognizerDovetailTotalStageAttemptCode accept reject)
        attempt tapeCodePrimitiveCodeWordHandoffMove

def PairedRecognizerDovetailLayoutCodeCompilerConstruction : Prop :=
  forall accept reject : MachineDescription,
    exists runner : MachineDescription,
      TapeCodePrimitiveCompiledByDescription
        (PairedRecognizerDovetailLayoutCode accept reject) runner

def PairedRecognizerDovetailLayoutCodeOutputRealizerConstruction : Prop :=
  forall accept reject : MachineDescription,
    exists runner : MachineDescription,
      TapeCodePrimitiveOutputRealizedByDescription
        (PairedRecognizerDovetailLayoutCode accept reject) runner

def PairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists runner : MachineDescription,
      TapeCodePrimitiveOutputSubroutineRealizedByDescription
        (PairedRecognizerDovetailLayoutCode accept reject) runner

def PairedRecognizerDovetailSearchDriverCompilerConstruction : Prop :=
  forall accept reject runner : MachineDescription,
    TapeCodePrimitiveOutputRealizedByDescription
      (PairedRecognizerDovetailLayoutCode accept reject) runner ->
      exists decider : MachineDescription,
        PairedRecognizerBoundedDovetailTableRealizes accept reject decider

def PairedRecognizerDovetailSubroutineSearchDriverCompilerConstruction :
    Prop :=
  forall accept reject runner : MachineDescription,
    TapeCodePrimitiveOutputSubroutineRealizedByDescription
      (PairedRecognizerDovetailLayoutCode accept reject) runner ->
      exists decider : MachineDescription,
        PairedRecognizerBoundedDovetailTableRealizes accept reject decider

def PairedRecognizerDovetailRunnerSearchDriverRealizes
    (accept reject runner decider : MachineDescription) : Prop :=
  decider.WellFormed ∧
    forall w : Word Bool, forall b : Bool,
      decider.HaltsWithOutput w [b] <->
        exists limit : Nat,
          runner.HaltsWithOutput
            (DovetailLayout.asBoolInput
              (DovetailLayout.initial
                accept reject w limit))
            (DovetailLayout.asBoolInput
              (DovetailLayout.run accept reject limit
                (DovetailLayout.initial
                  accept reject w limit))) ∧
          DovetailLayout.outputFromHits
              (DovetailLayout.run accept reject limit
                (DovetailLayout.initial
                  accept reject w limit)) =
            some [b]

def PairedRecognizerDovetailRunnerSearchDriverCompilerConstruction : Prop :=
  forall accept reject runner : MachineDescription,
    exists decider : MachineDescription,
      PairedRecognizerDovetailRunnerSearchDriverRealizes
        accept reject runner decider

def PairedRecognizerDovetailSubroutineRunnerSearchDriverCompilerConstruction :
    Prop :=
  forall accept reject runner : MachineDescription,
    runner.SubroutineReady ->
      exists decider : MachineDescription,
        PairedRecognizerDovetailRunnerSearchDriverRealizes
          accept reject runner decider

def PairedRecognizerDovetailStageAttemptSearchDriverRealizes
    (accept reject attempt decider : MachineDescription) : Prop :=
  decider.WellFormed ∧
    forall w : Word Bool, forall b : Bool,
      decider.HaltsWithOutput w [b] <->
        exists limit : Nat,
          attempt.HaltsWithOutput
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (encodeCodeWordAsInput
              (encodeBoolWord [b])) ∧
          boundedDovetailOutput
            accept reject w limit = some [b]

def PairedRecognizerDovetailStageAttemptSearchDriverCompilerConstruction :
    Prop :=
  forall accept reject attempt : MachineDescription,
    exists decider : MachineDescription,
      PairedRecognizerDovetailStageAttemptSearchDriverRealizes
        accept reject attempt decider

def PairedRecognizerDovetailTotalStageAttemptSearchDriverRealizes
    (accept reject attempt decider : MachineDescription) : Prop :=
  decider.WellFormed ∧
    forall w : Word Bool, forall b : Bool,
      decider.HaltsWithOutput w [b] <->
        exists limit : Nat,
          attempt.HaltsWithOutput
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (encodeCodeWordAsInput
              (encodeBoolWord [b])) ∧
          boundedDovetailOutput
            accept reject w limit = some [b]

def PairedRecognizerDovetailTotalStageAttemptSearchDriverCompilerConstruction :
    Prop :=
  forall accept reject attempt : MachineDescription,
    attempt.SubroutineReady ->
      exists decider : MachineDescription,
        PairedRecognizerDovetailTotalStageAttemptSearchDriverRealizes
          accept reject attempt decider

def PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
    (attempt decider : MachineDescription) : Prop :=
  decider.WellFormed ∧
    forall w : Word Bool, forall b : Bool,
      decider.HaltsWithOutput w [b] <->
        exists limit : Nat,
        exists result : Word Bool,
          attempt.HaltsWithOutput
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (encodeCodeWordAsInput
              (encodeBoolWord result)) ∧
          PairedRecognizerDovetailControllerRawOutput result = some [b]

def PairedRecognizerDovetailTotalStageAttemptControllerFuelSearchDriverRealizes
    (attempt decider : MachineDescription) : Prop :=
  decider.WellFormed ∧
    forall w : Word Bool, forall b : Bool,
      decider.HaltsWithOutput w [b] <->
        exists limit : Nat,
        exists fuel : Nat,
        exists result : Word Bool,
          attempt.HaltsWithOutputIn fuel
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (encodeCodeWordAsInput
              (encodeBoolWord result)) ∧
          PairedRecognizerDovetailControllerRawOutput result = some [b]

def PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerRealizes
    (attempt runner : MachineDescription) : Prop :=
  runner.SubroutineReady ∧
    forall w : Word Bool,
    forall limit fuel : Nat,
    forall result : Word Bool,
      runner.HaltsWithOutput
          (encodeCodeWordAsInput
            (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
              w limit fuel))
          (encodeCodeWordAsInput
            (encodeBoolWord result)) <->
        attempt.HaltsWithOutputIn fuel
          (encodeCodeWordAsInput
            (PairedRecognizerDovetailStageInputCode w limit))
          (encodeCodeWordAsInput
            (encodeBoolWord result))

def PairedRecognizerDovetailControllerStageAttemptUnconditionalExactFuelRunnerConstruction :
    Prop :=
  forall attempt : MachineDescription,
    exists runner : MachineDescription,
      PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerRealizes
        attempt runner

def PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodeClosedHandoffConstruction :
    Prop :=
  forall attempt : MachineDescription,
    exists parser : MachineDescription,
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodePrimitive
          attempt)
        parser tapeCodePrimitiveCodeWordHandoffMove

def PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodeRightShiftedConstruction :
    Prop :=
  forall attempt : MachineDescription,
    exists parser : MachineDescription,
      EncodedRewriters.RightShiftedOutputCompiledSubroutineByDescription
        (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodePrimitive
          attempt)
        parser

def PairedRecognizerDovetailControllerStageAttemptFuelSimulatorOutputTape
    (attempt : MachineDescription)
    (w : Word Bool) (limit fuel : Nat) : Tape Bool :=
  Tape.move Direction.right
    (Tape.input
      (encodeCodeWordAsInput
        (SimulatorLayout.encode
          (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout
            attempt w limit fuel))))

def PairedRecognizerDovetailControllerStageAttemptFuelSimulatorRightShiftedSpec
    (attempt runner : MachineDescription) : Prop :=
  runner.SubroutineReady ∧
    (forall w : Word Bool,
      forall limit fuel : Nat,
        runner.HaltsWithTape
          (encodeCodeWordAsInput
            (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
              w limit fuel))
          (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorOutputTape
            attempt w limit fuel)) ∧
      forall code : Word MachineCodeSymbol,
      forall T : Tape Bool,
        runner.HaltsWithTape (encodeCodeWordAsInput code) T ->
          exists w : Word Bool,
          exists limit fuel : Nat,
            code =
              PairedRecognizerDovetailControllerStageAttemptFuelInputCode
                w limit fuel ∧
            T =
              PairedRecognizerDovetailControllerStageAttemptFuelSimulatorOutputTape
                attempt w limit fuel

def PairedRecognizerDovetailControllerStageAttemptFuelSimulatorRightShiftedSpecConstruction :
    Prop :=
  forall attempt : MachineDescription,
    exists runner : MachineDescription,
      PairedRecognizerDovetailControllerStageAttemptFuelSimulatorRightShiftedSpec
        attempt runner

theorem pairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodeRightShiftedConstruction_of_spec
    (h :
      PairedRecognizerDovetailControllerStageAttemptFuelSimulatorRightShiftedSpecConstruction) :
    PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodeRightShiftedConstruction := by
  intro attempt
  rcases h attempt with ⟨runner, hrunner⟩
  refine ⟨runner, ?_⟩
  exact
    CommonGround.CodeWordEmitters.rightShiftedOutputCompiled_of_indexed_tape_spec
      (P :=
        PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodePrimitive
          attempt)
      (runner := runner)
      hrunner.left.left
      hrunner.left.right
      (fun i : Sigma (fun _ : Word Bool => Nat × Nat) =>
        PairedRecognizerDovetailControllerStageAttemptFuelInputCode
          i.1 i.2.1 i.2.2)
      (fun i : Sigma (fun _ : Word Bool => Nat × Nat) =>
        SimulatorLayout.encode
          (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout
            attempt i.1 i.2.1 i.2.2))
      (fun i : Sigma (fun _ : Word Bool => Nat × Nat) =>
        PairedRecognizerDovetailControllerStageAttemptFuelSimulatorOutputTape
          attempt i.1 i.2.1 i.2.2)
      (by
        intro i
        rfl)
      (by
        intro i
        exact hrunner.right.left i.1 i.2.1 i.2.2)
      (by
        intro code T hhalt
        rcases hrunner.right.right code T hhalt with
          ⟨w, limit, fuel, hcode, hT⟩
        exact ⟨⟨w, (limit, fuel)⟩, hcode, hT⟩)
      (by
        intro code out
        constructor
        · intro htransform
          rcases
              (pairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodePrimitive_transform_eq_some_iff
                attempt code out).mp htransform with
            ⟨w, limit, fuel, hcode, hout⟩
          exact ⟨⟨w, (limit, fuel)⟩, hcode, hout⟩
        · intro hindexed
          rcases hindexed with ⟨i, hcode, hout⟩
          exact
            (pairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodePrimitive_transform_eq_some_iff
              attempt code out).mpr
              ⟨i.1, i.2.1, i.2.2, hcode, hout⟩)

theorem pairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodeClosedHandoffConstruction_of_rightShifted
    (h :
      PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodeRightShiftedConstruction) :
    PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodeClosedHandoffConstruction := by
  intro attempt
  rcases h attempt with ⟨parser, hparser⟩
  exact
    ⟨parser,
      EncodedRewriters.closedHandoffCompiled_of_rightShiftedOutputCompiled
        hparser
        (by
          intro code out htransform
          exact
            pairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodePrimitive_transform_eq_some_cons
              htransform)⟩

def PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction :
    Prop :=
  forall attempt : MachineDescription,
    exists extractor : MachineDescription,
      TapeCodePrimitiveOutputCompiledSubroutineByDescription
        (PairedRecognizerDovetailControllerStageAttemptFuelOutputCodePrimitive
          attempt)
        extractor

def PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
    (attempt : MachineDescription) : Type :=
  { pair : SimulatorLayout × Word MachineCodeSymbol //
      pair.1.config.state = attempt.halt ∧
        Tape.normalizedOutput pair.1.config.tape =
          encodeCodeWordAsInput pair.2 }

def PairedRecognizerDovetailControllerStageAttemptFuelOutputInputCode
    {attempt : MachineDescription}
    (i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt) :
    Word MachineCodeSymbol :=
  SimulatorLayout.encode i.1.1

def PairedRecognizerDovetailControllerStageAttemptFuelOutputOutputCode
    {attempt : MachineDescription}
    (i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt) :
    Word MachineCodeSymbol :=
  i.1.2

def PairedRecognizerDovetailControllerStageAttemptFuelOutputTape
    {attempt : MachineDescription}
    (i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt) :
    Tape Bool :=
  CommonGround.CodeWordEmitters.ExactOutputTape
    PairedRecognizerDovetailControllerStageAttemptFuelOutputOutputCode i

def PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineSpec
    (attempt extractor : MachineDescription) : Prop :=
  extractor.SubroutineReady ∧
    (forall i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt,
        extractor.HaltsWithTape
          (encodeCodeWordAsInput
            (PairedRecognizerDovetailControllerStageAttemptFuelOutputInputCode
              i))
          (PairedRecognizerDovetailControllerStageAttemptFuelOutputTape i)) ∧
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

def PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineSpecConstruction :
    Prop :=
  forall attempt : MachineDescription,
    exists extractor : MachineDescription,
      PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineSpec
        attempt extractor

theorem pairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction_of_spec
    (h :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineSpecConstruction) :
    PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction := by
  intro attempt
  rcases h attempt with ⟨extractor, hextractor⟩
  refine ⟨extractor, ?_⟩
  exact
    CommonGround.CodeWordEmitters.outputCompiled_of_indexed_tape_spec
      (P :=
        PairedRecognizerDovetailControllerStageAttemptFuelOutputCodePrimitive
          attempt)
      (runner := extractor)
      hextractor.left.left
      hextractor.left.right
      PairedRecognizerDovetailControllerStageAttemptFuelOutputInputCode
      PairedRecognizerDovetailControllerStageAttemptFuelOutputOutputCode
      PairedRecognizerDovetailControllerStageAttemptFuelOutputTape
      (by
        intro i
        exact
          CommonGround.CodeWordEmitters.exactOutputTape_normalizedOutput
            PairedRecognizerDovetailControllerStageAttemptFuelOutputOutputCode i)
      (by
        intro i
        exact hextractor.right.left i)
      (by
        intro code T hhalt
        exact hextractor.right.right code T hhalt)
      (by
        intro code out
        constructor
        · intro htransform
          rcases
              (pairedRecognizerDovetailControllerStageAttemptFuelOutputCodePrimitive_transform_eq_some_iff
                attempt code out).mp htransform with
            ⟨L, hcode, hstate, houtput⟩
          exact
            ⟨⟨(L, out), ⟨hstate, houtput⟩⟩, hcode, rfl⟩
        · intro hindexed
          rcases hindexed with ⟨i, hcode, hout⟩
          rcases i with ⟨pair, hpair⟩
          rcases pair with ⟨L, indexedOut⟩
          dsimp at hcode hout hpair
          exact
            (pairedRecognizerDovetailControllerStageAttemptFuelOutputCodePrimitive_transform_eq_some_iff
              attempt code out).mpr
              ⟨L, hcode, hpair.left, by
                rw [hout]
                exact hpair.right⟩)

def PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerCodeSubroutineConstruction :
    Prop :=
  forall attempt : MachineDescription,
    exists runner : MachineDescription,
      TapeCodePrimitiveOutputCompiledSubroutineByDescription
        (PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerCode
          attempt)
        runner

def PairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerCodeSubroutineConstruction :
    Prop :=
  forall attempt invoker : MachineDescription,
    CommonGround.ControllerInvocation.StageAttemptProtectedRealizes
      attempt invoker ->
      exists runner : MachineDescription,
        TapeCodePrimitiveOutputCompiledSubroutineByDescription
          (PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerCode
            attempt)
          runner

theorem pairedRecognizerDovetailControllerStageAttemptExactFuelRunnerCodeSubroutineConstruction_of_components
    (hparser :
      PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodeClosedHandoffConstruction)
    (hsimulator : FixedDescriptionBoundedSimulatorCodeRightShiftedConstruction)
    (houtput :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction) :
    PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerCodeSubroutineConstruction := by
  intro attempt
  rcases hparser attempt with ⟨parser, hparser⟩
  rcases hsimulator attempt with ⟨simulator, hsimulator⟩
  rcases houtput attempt with ⟨extractor, houtput⟩
  have hsimulatorClosed :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (FixedDescriptionBoundedSimulatorCode attempt)
        simulator tapeCodePrimitiveCodeWordHandoffMove :=
    EncodedRewriters.closedHandoffCompiled_of_rightShiftedOutputCompiled
      hsimulator
      (by
        intro code out htransform
        exact
          CommonGround.SimulatorLayouts.runCodePrimitive_transform_eq_some_cons
            htransform)
  have hprefix :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (TapeCodePrimitive.compose
          (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodePrimitive
            attempt)
          (FixedDescriptionBoundedSimulatorCode attempt))
        (seqSubroutine parser simulator tapeCodePrimitiveCodeWordHandoffMove)
        tapeCodePrimitiveCodeWordHandoffMove :=
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_compose
      hparser hsimulatorClosed
  refine
    ⟨seqSubroutine
      (seqSubroutine parser simulator tapeCodePrimitiveCodeWordHandoffMove)
      extractor tapeCodePrimitiveCodeWordHandoffMove, ?_⟩
  simpa [PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerCode] using
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_compose_outputCompiled
      hprefix houtput

theorem pairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerCodeSubroutineConstruction_of_components
    (hparser :
      PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodeClosedHandoffConstruction)
    (hsimulator : FixedDescriptionBoundedSimulatorCodeRightShiftedConstruction)
    (houtput :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction) :
    PairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerCodeSubroutineConstruction := by
  intro attempt _invoker _hinvoker
  exact
    pairedRecognizerDovetailControllerStageAttemptExactFuelRunnerCodeSubroutineConstruction_of_components
      hparser hsimulator houtput attempt

theorem pairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerCodeSubroutineConstruction_of_unconditional
    (hcode :
      PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerCodeSubroutineConstruction) :
    PairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerCodeSubroutineConstruction := by
  intro attempt _invoker _hinvoker
  exact hcode attempt

theorem pairedRecognizerDovetailControllerStageAttemptUnconditionalExactFuelRunnerConstruction_of_codeSubroutine
    (hcode :
      PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerCodeSubroutineConstruction) :
    PairedRecognizerDovetailControllerStageAttemptUnconditionalExactFuelRunnerConstruction := by
  intro attempt
  rcases hcode attempt with ⟨runner, hrunner⟩
  refine ⟨runner, ?_⟩
  constructor
  · exact
      tapeCodePrimitiveOutputCompiledSubroutineByDescription_subroutineReady
        hrunner
  · intro w limit fuel result
    exact
      Iff.trans
        (tapeCodePrimitiveOutputCompiledSubroutineByDescription_haltsWithOutput_iff
          hrunner
          (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
            w limit fuel)
          (encodeBoolWord result))
        (pairedRecognizerDovetailControllerStageAttemptExactFuelRunnerCode_transform_boolWord_iff
          attempt w result limit fuel)

def PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerConstruction :
    Prop :=
  forall attempt : MachineDescription,
    attempt.SubroutineReady ->
      exists runner : MachineDescription,
        PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerRealizes
          attempt runner

abbrev ControllerStageAttemptExactFuelRunnerConstruction : Prop :=
  PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerConstruction

theorem pairedRecognizerDovetailControllerStageAttemptExactFuelRunnerConstruction_of_unconditional
    (hrunner :
      PairedRecognizerDovetailControllerStageAttemptUnconditionalExactFuelRunnerConstruction) :
    PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerConstruction := by
  intro attempt _hattempt
  exact hrunner attempt

def PairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerConstruction :
    Prop :=
  forall attempt invoker : MachineDescription,
    CommonGround.ControllerInvocation.StageAttemptProtectedRealizes
      attempt invoker ->
      exists runner : MachineDescription,
        PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerRealizes
          attempt runner

theorem pairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerConstruction_of_unconditional
    (hrunner :
      PairedRecognizerDovetailControllerStageAttemptUnconditionalExactFuelRunnerConstruction) :
    PairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerConstruction := by
  intro attempt _invoker _hinvoker
  exact hrunner attempt

theorem pairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerConstruction_of_codeSubroutine
    (hcode :
      PairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerCodeSubroutineConstruction) :
    PairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerConstruction := by
  intro attempt invoker hinvoker
  rcases hcode attempt invoker hinvoker with ⟨runner, hrunner⟩
  refine ⟨runner, ?_⟩
  constructor
  · exact
      tapeCodePrimitiveOutputCompiledSubroutineByDescription_subroutineReady
        hrunner
  · intro w limit fuel result
    exact
      Iff.trans
        (tapeCodePrimitiveOutputCompiledSubroutineByDescription_haltsWithOutput_iff
          hrunner
          (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
            w limit fuel)
          (encodeBoolWord result))
        (pairedRecognizerDovetailControllerStageAttemptExactFuelRunnerCode_transform_boolWord_iff
          attempt w result limit fuel)

def PairedRecognizerDovetailControllerStageAttemptFuelPairSearchRealizes
    (runner decider : MachineDescription) : Prop :=
  decider.WellFormed ∧
    forall w : Word Bool, forall b : Bool,
      decider.HaltsWithOutput w [b] <->
        exists limit : Nat,
        exists fuel : Nat,
        exists result : Word Bool,
          runner.HaltsWithOutput
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
                w limit fuel))
            (encodeCodeWordAsInput
              (encodeBoolWord result)) ∧
          PairedRecognizerDovetailControllerRawOutput result = some [b]

def PairedRecognizerDovetailControllerStageAttemptFuelPairEnumeratorRealizes
    (runner enumerator : MachineDescription) : Prop :=
  enumerator.SubroutineReady ∧
    forall w : Word Bool, forall result : Word Bool,
      enumerator.HaltsWithOutput w
          (encodeCodeWordAsInput (encodeBoolWord result)) <->
        exists limit : Nat,
        exists fuel : Nat,
          runner.HaltsWithOutput
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
                w limit fuel))
            (encodeCodeWordAsInput
              (encodeBoolWord result))

def PairedRecognizerDovetailControllerStageAttemptFuelPairEnumeratorConstruction :
    Prop :=
  forall runner : MachineDescription,
    runner.SubroutineReady ->
      exists enumerator : MachineDescription,
        PairedRecognizerDovetailControllerStageAttemptFuelPairEnumeratorRealizes
          runner enumerator

abbrev ControllerStageAttemptFuelPairEnumeratorConstruction : Prop :=
  PairedRecognizerDovetailControllerStageAttemptFuelPairEnumeratorConstruction

def PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRealizes
    (runner enumerator : MachineDescription) : Prop :=
  enumerator.SubroutineReady ∧
    forall w : Word Bool, forall result : Word Bool,
      enumerator.HaltsWithOutput w
          (encodeCodeWordAsInput (encodeBoolWord result)) <->
        exists searchLimit : Nat,
        exists limit : Nat,
        exists fuel : Nat,
          limit <= searchLimit ∧ fuel <= searchLimit ∧
            runner.HaltsWithOutput
              (encodeCodeWordAsInput
                (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
                  w limit fuel))
              (encodeCodeWordAsInput
                (encodeBoolWord result))

def PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorConstruction :
    Prop :=
  forall runner : MachineDescription,
    runner.SubroutineReady ->
      exists enumerator : MachineDescription,
        PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRealizes
          runner enumerator

theorem pairedRecognizerDovetailControllerStageAttemptFuelPairEnumeratorConstruction_of_bounded
    (hbounded :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorConstruction) :
    PairedRecognizerDovetailControllerStageAttemptFuelPairEnumeratorConstruction := by
  intro runner hrunner
  rcases hbounded runner hrunner with ⟨enumerator, henumerator⟩
  refine ⟨enumerator, ?_⟩
  constructor
  · exact henumerator.left
  · intro w result
    exact Iff.trans (henumerator.right w result) <| by
      simpa using
        (CommonGround.exists_bounded_pair_iff_exists_pair
          (fun limit fuel =>
            runner.HaltsWithOutput
              (encodeCodeWordAsInput
                (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
                  w limit fuel))
              (encodeCodeWordAsInput
                (encodeBoolWord result))))

def PairedRecognizerDovetailControllerStageAttemptRawOutputClassifierRealizes
    (enumerator classifier : MachineDescription) : Prop :=
  classifier.WellFormed ∧
    forall w : Word Bool, forall b : Bool,
      classifier.HaltsWithOutput w [b] <->
        exists result : Word Bool,
          enumerator.HaltsWithOutput w
              (encodeCodeWordAsInput (encodeBoolWord result)) ∧
            PairedRecognizerDovetailControllerRawOutput result = some [b]

def PairedRecognizerDovetailControllerStageAttemptRawOutputClassifierConstruction :
    Prop :=
  forall enumerator : MachineDescription,
    enumerator.SubroutineReady ->
      exists classifier : MachineDescription,
        PairedRecognizerDovetailControllerStageAttemptRawOutputClassifierRealizes
          enumerator classifier

abbrev ControllerStageAttemptRawOutputClassifierConstruction : Prop :=
  PairedRecognizerDovetailControllerStageAttemptRawOutputClassifierConstruction

def PairedRecognizerDovetailControllerStageAttemptFuelPairSearchConstruction :
    Prop :=
  forall runner : MachineDescription,
    runner.SubroutineReady ->
      exists decider : MachineDescription,
        PairedRecognizerDovetailControllerStageAttemptFuelPairSearchRealizes
          runner decider

abbrev ControllerStageAttemptSearchDriverConstruction : Prop :=
  PairedRecognizerDovetailControllerStageAttemptFuelPairSearchConstruction

theorem pairedRecognizerDovetailControllerStageAttemptFuelPairSearchConstruction_of_enumerator_classifier
    (henumerator :
      PairedRecognizerDovetailControllerStageAttemptFuelPairEnumeratorConstruction)
    (hclassifier :
      PairedRecognizerDovetailControllerStageAttemptRawOutputClassifierConstruction) :
    PairedRecognizerDovetailControllerStageAttemptFuelPairSearchConstruction := by
  intro runner hrunner
  rcases henumerator runner hrunner with ⟨enumerator, henumeratorSpec⟩
  rcases hclassifier enumerator henumeratorSpec.left with
    ⟨classifier, hclassifierSpec⟩
  refine ⟨classifier, ?_⟩
  constructor
  · exact hclassifierSpec.left
  · intro w b
    exact Iff.trans (hclassifierSpec.right w b) <| by
      constructor
      · intro h
        rcases h with ⟨result, henum, hraw⟩
        rcases (henumeratorSpec.right w result).mp henum with
          ⟨limit, fuel, hrun⟩
        exact ⟨limit, fuel, result, hrun, hraw⟩
      · intro h
        rcases h with ⟨limit, fuel, result, hrun, hraw⟩
        exact
          ⟨result,
            (henumeratorSpec.right w result).mpr
              ⟨limit, fuel, hrun⟩,
            hraw⟩

def PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompilerConstruction :
    Prop :=
  forall _accept _reject attempt : MachineDescription,
    attempt.SubroutineReady ->
      exists decider : MachineDescription,
        PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
          attempt decider

def PairedRecognizerDovetailProtectedStageAttemptControllerFuelSearchDriverConstruction :
    Prop :=
  forall attempt invoker : MachineDescription,
    CommonGround.ControllerInvocation.StageAttemptProtectedRealizes
      attempt invoker ->
      exists decider : MachineDescription,
        PairedRecognizerDovetailTotalStageAttemptControllerFuelSearchDriverRealizes
          attempt decider

theorem pairedRecognizerDovetailProtectedStageAttemptControllerFuelSearchDriverConstruction_of_exactFuelRunner_and_pairSearch
    (hrunner :
      PairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerConstruction)
    (hsearch :
      PairedRecognizerDovetailControllerStageAttemptFuelPairSearchConstruction) :
    PairedRecognizerDovetailProtectedStageAttemptControllerFuelSearchDriverConstruction := by
  intro attempt invoker hinvoker
  rcases hrunner attempt invoker hinvoker with
    ⟨runner, hrunnerSpec⟩
  rcases hsearch runner hrunnerSpec.left with
    ⟨decider, hdecider⟩
  refine ⟨decider, ?_⟩
  constructor
  · exact hdecider.left
  · intro w b
    exact Iff.trans (hdecider.right w b) <| by
      constructor
      · intro h
        rcases h with ⟨limit, fuel, result, hrun, hraw⟩
        exact
          ⟨limit, fuel, result,
            (hrunnerSpec.right w limit fuel result).mp hrun, hraw⟩
      · intro h
        rcases h with ⟨limit, fuel, result, hattempt, hraw⟩
        exact
          ⟨limit, fuel, result,
            (hrunnerSpec.right w limit fuel result).mpr hattempt, hraw⟩

def PairedRecognizerDovetailProtectedStageAttemptControllerSearchDriverConstruction :
    Prop :=
  forall attempt invoker : MachineDescription,
    CommonGround.ControllerInvocation.StageAttemptProtectedRealizes
      attempt invoker ->
      exists decider : MachineDescription,
        PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
          attempt decider

abbrev ControllerStageAttemptProtectedSearchDriverConstruction : Prop :=
  PairedRecognizerDovetailProtectedStageAttemptControllerSearchDriverConstruction

theorem pairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes_of_fuel
    {attempt decider : MachineDescription}
    (hdriver :
      PairedRecognizerDovetailTotalStageAttemptControllerFuelSearchDriverRealizes
        attempt decider) :
    PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
      attempt decider := by
  constructor
  · exact hdriver.left
  · intro w b
    exact Iff.trans (hdriver.right w b) <| by
      constructor
      · intro h
        rcases h with ⟨limit, fuel, result, hattempt, hraw⟩
        exact ⟨limit, result, ⟨fuel, hattempt⟩, hraw⟩
      · intro h
        rcases h with ⟨limit, result, hattempt, hraw⟩
        rcases
            MachineDescription.haltsWithOutput_iff_exists_haltsWithOutputIn.mp
              hattempt with
          ⟨fuel, hfuel⟩
        exact ⟨limit, fuel, result, hfuel, hraw⟩

theorem pairedRecognizerDovetailProtectedStageAttemptControllerSearchDriverConstruction_of_fuel
    (hcompile :
      PairedRecognizerDovetailProtectedStageAttemptControllerFuelSearchDriverConstruction) :
    PairedRecognizerDovetailProtectedStageAttemptControllerSearchDriverConstruction := by
  intro attempt invoker hinvoker
  rcases hcompile attempt invoker hinvoker with ⟨decider, hdecider⟩
  exact
    ⟨decider,
      pairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes_of_fuel
        hdecider⟩

def PairedRecognizerDovetailFiniteStageLoopControllerConstruction :
    Prop :=
  forall attempt : MachineDescription,
    attempt.SubroutineReady ->
      exists decider : MachineDescription,
        PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
          attempt decider

def PairedRecognizerDovetailControllerInputInitializerRealizes
    (initializer : MachineDescription) : Prop :=
  initializer.SubroutineReady ∧
    forall w : Word Bool,
      initializer.HaltsWithOutput w
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerInitialCode w))

def PairedRecognizerDovetailControllerInputInitializerConstruction :
    Prop :=
  exists initializer : MachineDescription,
    PairedRecognizerDovetailControllerInputInitializerRealizes initializer

def PairedRecognizerDovetailControllerStageInputEncoderConstruction :
    Prop :=
  exists encoder : MachineDescription,
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      PairedRecognizerDovetailControllerStageInputCodePrimitive
      encoder

def PairedRecognizerDovetailControllerStageInputEncoderHandoffConstruction :
    Prop :=
  exists encoder : MachineDescription,
    TapeCodePrimitiveHandoffCompiledSubroutineByDescription
      PairedRecognizerDovetailControllerStageInputCodePrimitive
      encoder tapeCodePrimitiveCodeWordHandoffMove

def PairedRecognizerDovetailControllerStageInputEncoderClosedHandoffConstruction :
    Prop :=
  exists encoder : MachineDescription,
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      PairedRecognizerDovetailControllerStageInputCodePrimitive
      encoder tapeCodePrimitiveCodeWordHandoffMove

theorem pairedRecognizerDovetailControllerStageInputEncoderConstruction_of_handoff
    (h : PairedRecognizerDovetailControllerStageInputEncoderHandoffConstruction) :
    PairedRecognizerDovetailControllerStageInputEncoderConstruction :=
  Exists.elim h fun encoder hencoder =>
    ⟨encoder,
      tapeCodePrimitiveHandoffCompiledSubroutineByDescription_outputCompiled
        hencoder⟩

theorem pairedRecognizerDovetailControllerStageInputEncoderHandoffConstruction_of_closedHandoff
    (h :
      PairedRecognizerDovetailControllerStageInputEncoderClosedHandoffConstruction) :
    PairedRecognizerDovetailControllerStageInputEncoderHandoffConstruction :=
  Exists.elim h fun encoder hencoder =>
    ⟨encoder,
      tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffCompiled
        hencoder⟩

theorem pairedRecognizerDovetailControllerStageInputEncoderConstruction_of_closedHandoff
    (h :
      PairedRecognizerDovetailControllerStageInputEncoderClosedHandoffConstruction) :
    PairedRecognizerDovetailControllerStageInputEncoderConstruction :=
  pairedRecognizerDovetailControllerStageInputEncoderConstruction_of_handoff
    (pairedRecognizerDovetailControllerStageInputEncoderHandoffConstruction_of_closedHandoff
      h)

def PairedRecognizerDovetailStageAttemptInvocationRealizes
    (attempt encoder invoker : MachineDescription) : Prop :=
  invoker.SubroutineReady ∧
    forall C : DovetailControllerLayout,
    forall result : Word Bool,
      invoker.HaltsWithOutput
          (encodeCodeWordAsInput
            (DovetailControllerLayout.encode C))
          (encodeCodeWordAsInput
            (DovetailControllerLayout.encode
              (DovetailControllerLayout.withResult
                C result))) <->
        encoder.HaltsWithOutput
            (encodeCodeWordAsInput
              (DovetailControllerLayout.encode C))
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailControllerStageInputCode C)) ∧
          attempt.HaltsWithOutput
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailControllerStageInputCode C))
            (encodeCodeWordAsInput
              (encodeBoolWord result))

def PairedRecognizerDovetailStageAttemptInvocationConstruction :
    Prop :=
  forall attempt encoder : MachineDescription,
    attempt.SubroutineReady ->
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      PairedRecognizerDovetailControllerStageInputCodePrimitive
      encoder ->
    exists invoker : MachineDescription,
      PairedRecognizerDovetailStageAttemptInvocationRealizes
        attempt encoder invoker

def PairedRecognizerDovetailStageAttemptInvocationHandoffConstruction :
    Prop :=
  forall attempt encoder : MachineDescription,
    attempt.SubroutineReady ->
    TapeCodePrimitiveHandoffCompiledSubroutineByDescription
      PairedRecognizerDovetailControllerStageInputCodePrimitive
      encoder tapeCodePrimitiveCodeWordHandoffMove ->
    exists invoker : MachineDescription,
      PairedRecognizerDovetailStageAttemptInvocationRealizes
        attempt encoder invoker

def PairedRecognizerDovetailStageAttemptInvocationClosedHandoffConstruction :
    Prop :=
  forall attempt encoder : MachineDescription,
    attempt.SubroutineReady ->
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      PairedRecognizerDovetailControllerStageInputCodePrimitive
      encoder tapeCodePrimitiveCodeWordHandoffMove ->
    exists invoker : MachineDescription,
      PairedRecognizerDovetailStageAttemptInvocationRealizes
        attempt encoder invoker

theorem pairedRecognizerDovetailStageAttemptInvocationHandoffConstruction_of_output
    (h : PairedRecognizerDovetailStageAttemptInvocationConstruction) :
    PairedRecognizerDovetailStageAttemptInvocationHandoffConstruction :=
  fun attempt encoder hattempt hencoder =>
    h attempt encoder hattempt
      (tapeCodePrimitiveHandoffCompiledSubroutineByDescription_outputCompiled
        hencoder)

theorem pairedRecognizerDovetailStageAttemptInvocationClosedHandoffConstruction_of_handoff
    (h :
      PairedRecognizerDovetailStageAttemptInvocationHandoffConstruction) :
    PairedRecognizerDovetailStageAttemptInvocationClosedHandoffConstruction :=
  fun attempt encoder hattempt hencoder =>
    h attempt encoder hattempt
      (tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffCompiled
        hencoder)

def PairedRecognizerDovetailControllerResultEmitterRealizes
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall C : DovetailControllerLayout,
    forall b : Bool,
      emitter.HaltsWithOutput
          (encodeCodeWordAsInput
            (DovetailControllerLayout.encode C))
          [b] <->
        PairedRecognizerDovetailControllerRawOutput C.result = some [b]

def PairedRecognizerDovetailControllerResultEmitterConstruction :
    Prop :=
  exists emitter : MachineDescription,
    PairedRecognizerDovetailControllerResultEmitterRealizes emitter

def PairedRecognizerDovetailControllerBoolWordRawOutputEmitterRealizes
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall result : Word Bool,
    forall b : Bool,
      emitter.HaltsWithOutput
          (encodeCodeWordAsInput (encodeBoolWord result))
          [b] <->
        PairedRecognizerDovetailControllerRawOutput result = some [b]

def PairedRecognizerDovetailControllerBoolWordRawOutputEmitterConstruction :
    Prop :=
  exists emitter : MachineDescription,
    PairedRecognizerDovetailControllerBoolWordRawOutputEmitterRealizes
      emitter

def PairedRecognizerDovetailControllerStageAttemptRawOutputClassifierSequencerRealizes
    (enumerator emitter classifier : MachineDescription) : Prop :=
  classifier.WellFormed ∧
    forall w : Word Bool, forall b : Bool,
      classifier.HaltsWithOutput w [b] <->
        exists result : Word Bool,
          enumerator.HaltsWithOutput w
              (encodeCodeWordAsInput (encodeBoolWord result)) ∧
            emitter.HaltsWithOutput
              (encodeCodeWordAsInput (encodeBoolWord result)) [b]

def PairedRecognizerDovetailControllerStageAttemptRawOutputClassifierSequencerConstruction :
    Prop :=
  forall enumerator emitter : MachineDescription,
    enumerator.SubroutineReady ->
    PairedRecognizerDovetailControllerBoolWordRawOutputEmitterRealizes
      emitter ->
      exists classifier : MachineDescription,
        PairedRecognizerDovetailControllerStageAttemptRawOutputClassifierSequencerRealizes
          enumerator emitter classifier

theorem pairedRecognizerDovetailControllerStageAttemptRawOutputClassifierConstruction_of_sequencer_emitter
    (hsequencer :
      PairedRecognizerDovetailControllerStageAttemptRawOutputClassifierSequencerConstruction)
    (hemitter :
      PairedRecognizerDovetailControllerBoolWordRawOutputEmitterConstruction) :
    PairedRecognizerDovetailControllerStageAttemptRawOutputClassifierConstruction := by
  intro enumerator henumerator
  rcases hemitter with ⟨emitter, hemits⟩
  rcases hsequencer enumerator emitter henumerator hemits with
    ⟨classifier, hclassifier⟩
  refine ⟨classifier, ?_⟩
  constructor
  · exact hclassifier.left
  · intro w b
    exact Iff.trans (hclassifier.right w b) <| by
      constructor
      · intro h
        rcases h with ⟨result, henum, hemit⟩
        exact ⟨result, henum, (hemits.right result b).mp hemit⟩
      · intro h
        rcases h with ⟨result, henum, hraw⟩
        exact ⟨result, henum, (hemits.right result b).mpr hraw⟩

def PairedRecognizerDovetailControllerContinueRealizes
    (continuer : MachineDescription) : Prop :=
  continuer.SubroutineReady ∧
    forall C : DovetailControllerLayout,
      continuer.HaltsWithOutput
          (encodeCodeWordAsInput
            (DovetailControllerLayout.encode C))
          (encodeCodeWordAsInput
            (DovetailControllerLayout.encode
              (DovetailControllerLayout.nextStage C))) <->
        PairedRecognizerDovetailControllerRawOutput C.result = none

def PairedRecognizerDovetailControllerContinueConstruction :
    Prop :=
  exists continuer : MachineDescription,
    PairedRecognizerDovetailControllerContinueRealizes continuer

def PairedRecognizerDovetailFiniteStageLoopSequencingConstruction :
    Prop :=
  forall attempt initializer encoder invoker emitter continuer :
      MachineDescription,
    attempt.SubroutineReady ->
    PairedRecognizerDovetailControllerInputInitializerRealizes
      initializer ->
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      PairedRecognizerDovetailControllerStageInputCodePrimitive
      encoder ->
    PairedRecognizerDovetailStageAttemptInvocationRealizes
      attempt encoder invoker ->
    PairedRecognizerDovetailControllerResultEmitterRealizes
      emitter ->
    PairedRecognizerDovetailControllerContinueRealizes
      continuer ->
    exists decider : MachineDescription,
      PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
        attempt decider

def PairedRecognizerDovetailFiniteStageLoopSequencingHandoffConstruction :
    Prop :=
  forall attempt initializer encoder invoker emitter continuer :
      MachineDescription,
    attempt.SubroutineReady ->
    PairedRecognizerDovetailControllerInputInitializerRealizes
      initializer ->
    TapeCodePrimitiveHandoffCompiledSubroutineByDescription
      PairedRecognizerDovetailControllerStageInputCodePrimitive
      encoder tapeCodePrimitiveCodeWordHandoffMove ->
    PairedRecognizerDovetailStageAttemptInvocationRealizes
      attempt encoder invoker ->
    PairedRecognizerDovetailControllerResultEmitterRealizes
      emitter ->
    PairedRecognizerDovetailControllerContinueRealizes
      continuer ->
    exists decider : MachineDescription,
      PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
        attempt decider

theorem pairedRecognizerDovetailFiniteStageLoopSequencingHandoffConstruction_of_output
    (h : PairedRecognizerDovetailFiniteStageLoopSequencingConstruction) :
    PairedRecognizerDovetailFiniteStageLoopSequencingHandoffConstruction := by
  intro attempt initializer encoder invoker emitter continuer
    hattempt hinitializer hencoder hinvoker hemitter hcontinuer
  exact h attempt initializer encoder invoker emitter continuer
    hattempt hinitializer
    (tapeCodePrimitiveHandoffCompiledSubroutineByDescription_outputCompiled
      hencoder)
    hinvoker hemitter hcontinuer

/-!
## Grouped bounded-runner target

The individual construction targets above remain the stable compatibility API.
This grouped surface is the preferred internal boundary when a downstream
closeout needs the padded/equivalence bounded-runner route as a package.
-/

structure BoundedRunnerConstructionSurface where
  fixedSimulatorOutput :
    FixedDescriptionBoundedSimulatorCodeOutputRealizerConstruction
  fixedStepConfiguration :
    FixedDescriptionStepCodeConfigurationRealizerConstruction
  layoutRunnerSubroutine :
    PairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction
  totalStageAttemptSubroutine :
    PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction
  finiteStageLoopController :
    PairedRecognizerDovetailFiniteStageLoopControllerConstruction

end Computability
end FoC
