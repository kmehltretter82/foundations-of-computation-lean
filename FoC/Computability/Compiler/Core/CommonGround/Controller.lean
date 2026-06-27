import FoC.Computability.Compiler.Core.DovetailCode
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts

set_option doc.verso true

/-!
# Common controller-layout helpers

This module contains the reusable controller-layout encoding facts and the
shared controller-invocation contract vocabulary.
-/

namespace FoC
namespace Computability

open Languages

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

export MachineDescription.DovetailControllerLayout
  ( encodeAppend
    decodeComplete
    decodeComplete_encode
    decodeComplete_eq_some_encode
    initial
    stageInputCode
    withResult
    nextStage
    rawOutput?
    rawOutput_nil
    rawOutput_singleton
    rawOutput_eq_some_singleton_iff
    continueResultCode
    continueResultCodePrimitive
    continueResultCode_encode
    continueResultCodePrimitive_encode
    continueResultCode_encode_of_rawOutput_eq_none
    continueResultCode_encode_of_rawOutput_eq_some
    continueResultCode_encode_eq_some_iff
    continueResultCodePrimitive_encode_eq_some_iff )

def initialSuffix : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend 0
    (MachineDescription.encodeBoolWordAppend [] [])

theorem initialCode_eq_header_boolWordAppend
    (w : Word Bool) :
    PairedRecognizerDovetailControllerInitialCode w =
      MachineCodeSymbol.header ::
        MachineDescription.encodeBoolWordAppend w initialSuffix := by
  rfl

theorem stageInputCode_eq_boolWordNat
    (C : MachineDescription.DovetailControllerLayout) :
    PairedRecognizerDovetailControllerStageInputCode C =
      MachineDescription.encodeBoolWordAppend C.input
        (MachineDescription.encodeNatAppend C.stage []) := by
  cases C
  rfl

theorem withResult_input
    (C : MachineDescription.DovetailControllerLayout)
    (result : Word Bool) :
    (MachineDescription.DovetailControllerLayout.withResult C result).input =
      C.input := by
  cases C
  rfl

theorem withResult_stage
    (C : MachineDescription.DovetailControllerLayout)
    (result : Word Bool) :
    (MachineDescription.DovetailControllerLayout.withResult C result).stage =
      C.stage := by
  cases C
  rfl

theorem withResult_result
    (C : MachineDescription.DovetailControllerLayout)
    (result : Word Bool) :
    (MachineDescription.DovetailControllerLayout.withResult C result).result =
      result := by
  cases C
  rfl

theorem stageInputCode_withResult
    (C : MachineDescription.DovetailControllerLayout)
    (result : Word Bool) :
    PairedRecognizerDovetailControllerStageInputCode
        (MachineDescription.DovetailControllerLayout.withResult C result) =
      PairedRecognizerDovetailControllerStageInputCode C := by
  cases C
  rfl

theorem encode_eq_header_stageInput_append_result
    (C : MachineDescription.DovetailControllerLayout) :
    MachineDescription.DovetailControllerLayout.encode C =
      MachineCodeSymbol.header ::
        List.append (PairedRecognizerDovetailControllerStageInputCode C)
          (MachineDescription.encodeBoolWordAppend C.result []) :=
  dovetailControllerLayout_encode_eq_header_stageInput_append_result C

theorem withResult_encode_eq_header_stage_result
    (C : MachineDescription.DovetailControllerLayout)
    (result : Word Bool) :
    MachineDescription.DovetailControllerLayout.encode
        (MachineDescription.DovetailControllerLayout.withResult C result) =
      MachineCodeSymbol.header ::
        MachineDescription.encodeBoolWordAppend C.input
          (MachineDescription.encodeNatAppend C.stage
            (MachineDescription.encodeBoolWordAppend result [])) := by
  cases C
  rfl

theorem withResult_encode_eq_stageInput_append_result
    (C : MachineDescription.DovetailControllerLayout)
    (result : Word Bool) :
    MachineDescription.DovetailControllerLayout.encode
        (MachineDescription.DovetailControllerLayout.withResult C result) =
      MachineCodeSymbol.header ::
        List.append (PairedRecognizerDovetailControllerStageInputCode C)
          (MachineDescription.encodeBoolWordAppend result []) := by
  simpa [stageInputCode_withResult, withResult_result] using
    encode_eq_header_stageInput_append_result
      (MachineDescription.DovetailControllerLayout.withResult C result)

theorem resultContinue_transform_eq_some_iff
    (code out : Word MachineCodeSymbol) :
    PairedRecognizerDovetailControllerResultContinueCode.transform code =
        some out <->
      exists C : MachineDescription.DovetailControllerLayout,
        code = MachineDescription.DovetailControllerLayout.encode C ∧
          PairedRecognizerDovetailControllerRawOutput C.result = none ∧
            out =
              MachineDescription.DovetailControllerLayout.encode
                (MachineDescription.DovetailControllerLayout.nextStage C) :=
  pairedRecognizerDovetailControllerResultContinueCode_transform_eq_some_iff
    code out

theorem resultContinue_encode_nextStage_iff
    {C : MachineDescription.DovetailControllerLayout} :
    PairedRecognizerDovetailControllerResultContinueCode.transform
        (MachineDescription.DovetailControllerLayout.encode C) =
        some
          (MachineDescription.DovetailControllerLayout.encode
            (MachineDescription.DovetailControllerLayout.nextStage C)) <->
      PairedRecognizerDovetailControllerRawOutput C.result = none :=
  pairedRecognizerDovetailControllerResultContinueCode_encode_nextStage_iff

theorem resultContinue_encode_eq_some_iff
    {C : MachineDescription.DovetailControllerLayout}
    {outCode : Word MachineCodeSymbol} :
    PairedRecognizerDovetailControllerResultContinueCode.transform
        (MachineDescription.DovetailControllerLayout.encode C) =
        some outCode <->
      PairedRecognizerDovetailControllerRawOutput C.result = none ∧
        outCode =
          MachineDescription.DovetailControllerLayout.encode
            (MachineDescription.DovetailControllerLayout.nextStage C) :=
  pairedRecognizerDovetailControllerResultContinueCode_encode_eq_some_iff

end ControllerLayouts

namespace ControllerInvocation

def StageAttemptWitnessedForwardSpec
    (attempt invoker : MachineDescription) : Prop :=
  forall C : MachineDescription.DovetailControllerLayout,
  forall result : Word Bool,
  forall n : Nat,
    attempt.HaltsWithOutputIn n
      (MachineDescription.encodeCodeWordAsInput
        (PairedRecognizerDovetailControllerStageInputCode C))
      (MachineDescription.encodeCodeWordAsInput
        (MachineDescription.encodeBoolWord result)) ->
    invoker.HaltsWithOutput
      (MachineDescription.encodeCodeWordAsInput
        (MachineDescription.DovetailControllerLayout.encode C))
      (MachineDescription.encodeCodeWordAsInput
        (MachineDescription.DovetailControllerLayout.encode
          (MachineDescription.DovetailControllerLayout.withResult
            C result)))

def StageAttemptFramedClosedSpec
    (attempt invoker : MachineDescription) : Prop :=
  forall C : MachineDescription.DovetailControllerLayout,
  forall result : Word Bool,
    invoker.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.DovetailControllerLayout.encode C))
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.DovetailControllerLayout.encode
            (MachineDescription.DovetailControllerLayout.withResult
              C result))) ->
      exists n : Nat,
        attempt.HaltsWithOutputIn n
          (MachineDescription.encodeCodeWordAsInput
            (PairedRecognizerDovetailControllerStageInputCode C))
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.encodeBoolWord result))

def StageAttemptWitnessedRealizes
    (attempt invoker : MachineDescription) : Prop :=
  invoker.SubroutineReady ∧
    StageAttemptWitnessedForwardSpec attempt invoker ∧
      StageAttemptFramedClosedSpec attempt invoker

def StageAttemptWitnessedConstruction : Prop :=
  forall attempt : MachineDescription,
    attempt.SubroutineReady ->
      exists invoker : MachineDescription,
        StageAttemptWitnessedRealizes attempt invoker

end ControllerInvocation

end CommonGround

end Computability
end FoC
