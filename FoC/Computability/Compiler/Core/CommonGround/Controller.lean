import FoC.Computability.Compiler.Core.DovetailCode
import FoC.Computability.Compiler.Core.EncodingLemmas
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.Controller

set_option doc.verso true

/-!
# Common controller-layout helpers

This module contains the reusable controller-layout encoding facts and the
shared controller-invocation contract vocabulary.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround

namespace ControllerLayouts

export EncodedRewriters.CanonicalLayouts.Controller
  ( Layout
    decode
    encode
    bits
    inputTape
    handoffTape
    identityPrimitive
    ClosedRecognizerSpec
    ClosedRecognizerConstruction
    IdentityClosedHandoffConstruction
    decode_encode
    decode_eq_some_encode
    encode_cons
    identityPrimitive_transform_eq_some_iff
    identityClosedHandoffConstruction_of_closedRecognizer )

export DovetailControllerLayout
  ( encodeAppend
    encode_injective
    decodeComplete
    decodeComplete_encode
    decodeComplete_eq_some_encode
    initial
    stageInputCode
    stageInputCode_injective_on_input_stage
    withResult
    nextStage
    rawOutput?
    rawOutput_nil
    rawOutput_singleton
    rawOutput_none_iff
    rawOutput_eq_some_singleton_iff
    continueResultCode
    continueResultCodePrimitive
    continueResultCode_encode
    continueResultCodePrimitive_encode
    continueResultCode_encode_of_rawOutput_eq_none
    continueResultCode_encode_of_rawOutput_eq_some
    continueResultCode_encode_eq_some_iff
    continueResultCodePrimitive_encode_eq_some_iff )

export FoC.Computability
  ( pairedRecognizerDovetailControllerStageInputCode_injective_on_input_stage
    pairedRecognizerDovetailControllerRawOutput_none_iff )

def initialSuffix : Word MachineCodeSymbol :=
  encodeNatAppend 0
    (encodeBoolWordAppend [] [])

theorem initialCode_eq_header_boolWordAppend
    (w : Word Bool) :
    PairedRecognizerDovetailControllerInitialCode w =
      MachineCodeSymbol.header ::
        encodeBoolWordAppend w initialSuffix := by
  rfl

theorem stageInputCode_eq_boolWordNat
    (C : DovetailControllerLayout) :
    PairedRecognizerDovetailControllerStageInputCode C =
      encodeBoolWordAppend C.input
        (encodeNatAppend C.stage []) := by
  cases C
  rfl

theorem withResult_input
    (C : DovetailControllerLayout)
    (result : Word Bool) :
    (DovetailControllerLayout.withResult C result).input =
      C.input := by
  cases C
  rfl

theorem withResult_stage
    (C : DovetailControllerLayout)
    (result : Word Bool) :
    (DovetailControllerLayout.withResult C result).stage =
      C.stage := by
  cases C
  rfl

theorem withResult_result
    (C : DovetailControllerLayout)
    (result : Word Bool) :
    (DovetailControllerLayout.withResult C result).result =
      result := by
  cases C
  rfl

theorem stageInputCode_withResult
    (C : DovetailControllerLayout)
    (result : Word Bool) :
    PairedRecognizerDovetailControllerStageInputCode
        (DovetailControllerLayout.withResult C result) =
      PairedRecognizerDovetailControllerStageInputCode C := by
  cases C
  rfl

theorem encode_eq_header_stageInput_append_result
    (C : DovetailControllerLayout) :
    DovetailControllerLayout.encode C =
      MachineCodeSymbol.header ::
        List.append (PairedRecognizerDovetailControllerStageInputCode C)
          (encodeBoolWordAppend C.result []) :=
  dovetailControllerLayout_encode_eq_header_stageInput_append_result C

theorem withResult_encode_eq_header_stage_result
    (C : DovetailControllerLayout)
    (result : Word Bool) :
    DovetailControllerLayout.encode
        (DovetailControllerLayout.withResult C result) =
      MachineCodeSymbol.header ::
        encodeBoolWordAppend C.input
          (encodeNatAppend C.stage
            (encodeBoolWordAppend result [])) := by
  cases C
  rfl

theorem withResult_encode_eq_stageInput_append_result
    (C : DovetailControllerLayout)
    (result : Word Bool) :
    DovetailControllerLayout.encode
        (DovetailControllerLayout.withResult C result) =
      MachineCodeSymbol.header ::
        List.append (PairedRecognizerDovetailControllerStageInputCode C)
          (encodeBoolWordAppend result []) := by
  simpa [stageInputCode_withResult, withResult_result] using
    encode_eq_header_stageInput_append_result
      (DovetailControllerLayout.withResult C result)

theorem resultContinue_transform_eq_some_iff
    (code out : Word MachineCodeSymbol) :
    PairedRecognizerDovetailControllerResultContinueCode.transform code =
        some out <->
      exists C : DovetailControllerLayout,
        code = DovetailControllerLayout.encode C ∧
          PairedRecognizerDovetailControllerRawOutput C.result = none ∧
            out =
              DovetailControllerLayout.encode
                (DovetailControllerLayout.nextStage C) :=
  pairedRecognizerDovetailControllerResultContinueCode_transform_eq_some_iff
    code out

theorem resultContinue_encode_nextStage_iff
    {C : DovetailControllerLayout} :
    PairedRecognizerDovetailControllerResultContinueCode.transform
        (DovetailControllerLayout.encode C) =
        some
          (DovetailControllerLayout.encode
            (DovetailControllerLayout.nextStage C)) <->
      PairedRecognizerDovetailControllerRawOutput C.result = none :=
  pairedRecognizerDovetailControllerResultContinueCode_encode_nextStage_iff

theorem resultContinue_encode_eq_some_iff
    {C : DovetailControllerLayout}
    {outCode : Word MachineCodeSymbol} :
    PairedRecognizerDovetailControllerResultContinueCode.transform
        (DovetailControllerLayout.encode C) =
        some outCode <->
      PairedRecognizerDovetailControllerRawOutput C.result = none ∧
        outCode =
          DovetailControllerLayout.encode
            (DovetailControllerLayout.nextStage C) :=
  pairedRecognizerDovetailControllerResultContinueCode_encode_eq_some_iff

end ControllerLayouts

namespace ControllerInvocation

def StageAttemptWitnessedForwardSpec
    (attempt invoker : MachineDescription) : Prop :=
  forall C : DovetailControllerLayout,
  forall result : Word Bool,
  forall n : Nat,
    attempt.HaltsWithOutputIn n
      (encodeCodeWordAsInput
        (PairedRecognizerDovetailControllerStageInputCode C))
      (encodeCodeWordAsInput
        (encodeBoolWord result)) ->
    invoker.HaltsWithOutput
      (encodeCodeWordAsInput
        (DovetailControllerLayout.encode C))
      (encodeCodeWordAsInput
        (DovetailControllerLayout.encode
          (DovetailControllerLayout.withResult
            C result)))

def StageAttemptFramedForwardSpec
    (attempt invoker : MachineDescription) : Prop :=
  forall C : DovetailControllerLayout,
  forall result : Word Bool,
    (exists n : Nat,
      attempt.HaltsWithOutputIn n
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageInputCode C))
        (encodeCodeWordAsInput
          (encodeBoolWord result))) ->
    invoker.HaltsWithOutput
      (encodeCodeWordAsInput
        (DovetailControllerLayout.encode C))
      (encodeCodeWordAsInput
        (DovetailControllerLayout.encode
          (DovetailControllerLayout.withResult
            C result)))

def StageAttemptFramedClosedSpec
    (attempt invoker : MachineDescription) : Prop :=
  forall C : DovetailControllerLayout,
  forall result : Word Bool,
    invoker.HaltsWithOutput
        (encodeCodeWordAsInput
          (DovetailControllerLayout.encode C))
        (encodeCodeWordAsInput
          (DovetailControllerLayout.encode
            (DovetailControllerLayout.withResult
              C result))) ->
      exists n : Nat,
        attempt.HaltsWithOutputIn n
          (encodeCodeWordAsInput
            (PairedRecognizerDovetailControllerStageInputCode C))
          (encodeCodeWordAsInput
            (encodeBoolWord result))

def StageAttemptWitnessedRealizes
    (attempt invoker : MachineDescription) : Prop :=
  invoker.SubroutineReady ∧
    StageAttemptWitnessedForwardSpec attempt invoker ∧
      StageAttemptFramedClosedSpec attempt invoker

def StageAttemptFramedRealizes
    (attempt invoker : MachineDescription) : Prop :=
  invoker.SubroutineReady ∧
    StageAttemptFramedForwardSpec attempt invoker ∧
      StageAttemptFramedClosedSpec attempt invoker

def StageAttemptWitnessedConstruction : Prop :=
  forall attempt : MachineDescription,
    attempt.SubroutineReady ->
      exists invoker : MachineDescription,
        StageAttemptWitnessedRealizes attempt invoker

def StageAttemptFramedConstruction : Prop :=
  forall attempt : MachineDescription,
    attempt.SubroutineReady ->
      exists invoker : MachineDescription,
        StageAttemptFramedRealizes attempt invoker

abbrev ControllerStageAttemptWitnessedConstruction : Prop :=
  StageAttemptWitnessedConstruction

abbrev ControllerStageAttemptFramedInvocationConstruction : Prop :=
  StageAttemptFramedConstruction

theorem stageAttemptFramedForwardSpec_of_witnessed
    {attempt invoker : MachineDescription}
    (h : StageAttemptWitnessedForwardSpec attempt invoker) :
    StageAttemptFramedForwardSpec attempt invoker := by
  intro C result hrun
  rcases hrun with ⟨n, hn⟩
  exact h C result n hn

theorem stageAttemptWitnessedForwardSpec_of_framed
    {attempt invoker : MachineDescription}
    (h : StageAttemptFramedForwardSpec attempt invoker) :
    StageAttemptWitnessedForwardSpec attempt invoker := by
  intro C result n hn
  exact h C result ⟨n, hn⟩

theorem stageAttemptFramedRealizes_of_witnessed
    {attempt invoker : MachineDescription}
    (h : StageAttemptWitnessedRealizes attempt invoker) :
    StageAttemptFramedRealizes attempt invoker := by
  exact
    ⟨h.left,
      stageAttemptFramedForwardSpec_of_witnessed h.right.left,
      h.right.right⟩

theorem stageAttemptWitnessedRealizes_of_framed
    {attempt invoker : MachineDescription}
    (h : StageAttemptFramedRealizes attempt invoker) :
    StageAttemptWitnessedRealizes attempt invoker := by
  exact
    ⟨h.left,
      stageAttemptWitnessedForwardSpec_of_framed h.right.left,
      h.right.right⟩

theorem stageAttemptFramedConstruction_of_witnessed
    (h : StageAttemptWitnessedConstruction) :
    StageAttemptFramedConstruction := by
  intro attempt hattempt
  rcases h attempt hattempt with ⟨invoker, hinvoker⟩
  exact ⟨invoker, stageAttemptFramedRealizes_of_witnessed hinvoker⟩

theorem stageAttemptWitnessedConstruction_of_framed
    (h : StageAttemptFramedConstruction) :
    StageAttemptWitnessedConstruction := by
  intro attempt hattempt
  rcases h attempt hattempt with ⟨invoker, hinvoker⟩
  exact ⟨invoker, stageAttemptWitnessedRealizes_of_framed hinvoker⟩

end ControllerInvocation

end CommonGround

end Computability
end FoC
