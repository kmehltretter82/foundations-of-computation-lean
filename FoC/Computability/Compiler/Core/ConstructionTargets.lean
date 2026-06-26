import FoC.Computability.Compiler.Core.EncodedRewriters.RightShifted

set_option doc.verso true

/-!
# Finite compiler construction targets
-/

namespace FoC
namespace Computability

open Languages

def MachineDescriptionTapeCodeExactCompilerConstruction : Prop :=
  forall P : MachineDescription.TapeCodePrimitive,
    exists D : MachineDescription,
      TapeCodePrimitiveCompiledByDescription P D

def MachineDescriptionTapeCodeOutputCompilerConstruction : Prop :=
  forall P : MachineDescription.TapeCodePrimitive,
    exists D : MachineDescription,
      TapeCodePrimitiveOutputRealizedByDescription P D

theorem not_machineDescriptionTapeCodeExactCompilerConstruction :
    ¬ MachineDescriptionTapeCodeExactCompilerConstruction := by
  intro hcompile
  rcases hcompile MachineDescription.TapeCodePrimitive.erase with
    ⟨D, hD⟩
  exact not_tapeCodePrimitiveCompiledByDescription_erase ⟨D, hD⟩

theorem machineDescriptionTapeCodeOutputCompiler_realizes
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction)
    (P : MachineDescription.TapeCodePrimitive) :
    exists D : MachineDescription,
      TapeCodePrimitiveOutputRealizedByDescription P D :=
  hcompile P

def TapeCodePrimitiveCodeComposition
    (A B C : MachineDescription) : Prop :=
  C.WellFormed ∧
    forall code out : Word MachineCodeSymbol,
      C.HaltsWithExactOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) <->
        exists mid : Word MachineCodeSymbol,
          A.HaltsWithExactOutput
              (MachineDescription.encodeCodeWordAsInput code)
              (MachineDescription.encodeCodeWordAsInput mid) ∧
            B.HaltsWithExactOutput
              (MachineDescription.encodeCodeWordAsInput mid)
              (MachineDescription.encodeCodeWordAsInput out)

theorem tapeCodePrimitiveCompiledByDescription_compose
    {P Q : MachineDescription.TapeCodePrimitive}
    {A B C : MachineDescription}
    (hcomp : TapeCodePrimitiveCodeComposition A B C)
    (hP : TapeCodePrimitiveCompiledByDescription P A)
    (hQ : TapeCodePrimitiveCompiledByDescription Q B) :
    TapeCodePrimitiveCompiledByDescription
      (MachineDescription.TapeCodePrimitive.compose P Q) C := by
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
        MachineDescription.TapeCodePrimitive.compose_transform_some
          hPmid hQout
    · intro h
      unfold MachineDescription.TapeCodePrimitive.compose at h
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
    forall c : MachineDescription.Configuration,
      stepper.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeConfiguration c))
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeConfiguration (D.runConfig 1 c)))

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
            (MachineDescription.DovetailLayout.asBoolInput
              (MachineDescription.DovetailLayout.initial
                accept reject w limit))
            (MachineDescription.DovetailLayout.asBoolInput
              (MachineDescription.DovetailLayout.run accept reject limit
                (MachineDescription.DovetailLayout.initial
                  accept reject w limit))) ∧
          MachineDescription.DovetailLayout.outputFromHits
              (MachineDescription.DovetailLayout.run accept reject limit
                (MachineDescription.DovetailLayout.initial
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
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.encodeBoolWord [b])) ∧
          MachineDescription.boundedDovetailOutput
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
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.encodeBoolWord [b])) ∧
          MachineDescription.boundedDovetailOutput
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
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.encodeBoolWord result)) ∧
          PairedRecognizerDovetailControllerRawOutput result = some [b]

def PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompilerConstruction :
    Prop :=
  forall _accept _reject attempt : MachineDescription,
    attempt.SubroutineReady ->
      exists decider : MachineDescription,
        PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
          attempt decider

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
        (MachineDescription.encodeCodeWordAsInput
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
    PairedRecognizerDovetailControllerStageInputEncoderConstruction := by
  rcases h with ⟨encoder, hencoder⟩
  exact
    ⟨encoder,
      tapeCodePrimitiveHandoffCompiledSubroutineByDescription_outputCompiled
        hencoder⟩

theorem pairedRecognizerDovetailControllerStageInputEncoderHandoffConstruction_of_closedHandoff
    (h :
      PairedRecognizerDovetailControllerStageInputEncoderClosedHandoffConstruction) :
    PairedRecognizerDovetailControllerStageInputEncoderHandoffConstruction := by
  rcases h with ⟨encoder, hencoder⟩
  exact
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
    forall C : MachineDescription.DovetailControllerLayout,
    forall result : Word Bool,
      invoker.HaltsWithOutput
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.DovetailControllerLayout.encode C))
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.DovetailControllerLayout.encode
              (MachineDescription.DovetailControllerLayout.withResult
                C result))) <->
        encoder.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.DovetailControllerLayout.encode C))
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailControllerStageInputCode C)) ∧
          attempt.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailControllerStageInputCode C))
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.encodeBoolWord result))

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
    forall C : MachineDescription.DovetailControllerLayout,
    forall b : Bool,
      emitter.HaltsWithOutput
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.DovetailControllerLayout.encode C))
          [b] <->
        PairedRecognizerDovetailControllerRawOutput C.result = some [b]

def PairedRecognizerDovetailControllerResultEmitterConstruction :
    Prop :=
  exists emitter : MachineDescription,
    PairedRecognizerDovetailControllerResultEmitterRealizes emitter

def PairedRecognizerDovetailControllerContinueRealizes
    (continuer : MachineDescription) : Prop :=
  continuer.SubroutineReady ∧
    forall C : MachineDescription.DovetailControllerLayout,
      continuer.HaltsWithOutput
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.DovetailControllerLayout.encode C))
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.DovetailControllerLayout.encode
              (MachineDescription.DovetailControllerLayout.nextStage C))) <->
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

end Computability
end FoC
