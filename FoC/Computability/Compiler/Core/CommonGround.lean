import FoC.Computability.Compiler.Core.DovetailCode
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts
import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.Assembly
import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.BoolWordQuoter
import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.ReturnAppend

set_option doc.verso true

/-!
# Common compiler helper surface

This module collects stable names for the helper families that are shared by
the remaining finite-machine leaves: complete canonical field inversions,
exact/right-shifted code-word emitter contracts, closed scanner inversions, and
append/return-to-marker machines.

The declarations are re-exported rather than moved in this first pass.  That
keeps existing proof files untouched while giving later driver proofs a single
import path that does not depend on initializer-internal module names.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround

namespace FieldInversions

export EncodedRewriters.CanonicalLayouts.Fields
  ( decodeNatComplete
    decodeNatComplete_encode
    decodeNatComplete_eq_some_encode
    decodeBoolComplete
    decodeBoolComplete_encode
    decodeBoolComplete_eq_some_encode
    decodeBoolWordComplete
    decodeBoolWordComplete_encode
    decodeBoolWordComplete_eq_some_encode
    decodeCodeWordFieldComplete
    decodeCodeWordFieldComplete_encode
    decodeCodeWordFieldComplete_eq_some_encode
    decodeCellListComplete
    decodeCellListComplete_encode
    decodeCellListComplete_eq_some_encode
    decodeTapeComplete
    decodeTapeComplete_encode
    decodeTapeComplete_eq_some_encode
    decodeConfigurationComplete
    decodeConfigurationComplete_encode
    decodeConfigurationComplete_eq_some_encode )

end FieldInversions

namespace ScannerInversions

export EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner
  ( BoolWordSuffixScannerDescription
    CheckedDovetailLayoutScannerDescription
    transitionRemainderBits
    cellListCanonicalRestoredLeftWithBase
    boolWordCanonicalHandoffConfigWithBase_move_right_all
    boolWordSuffixScannerDescription_runConfig_start_bit_inv
    boolWordSuffixScannerDescription_runConfig_start_nat_prefix_inv
    boolWordSuffixScannerDescription_runConfig_code_inv
    boolWordSuffixScannerDescription_runConfig_encodeBoolWordAppend_handoff
    cellListSuffixScannerDescription_runConfig_code_inv
    cellListSuffixScannerDescription_runConfig_encodeCellListAppend_handoff_false
    cellListSuffixScannerDescription_runConfig_encodeCellListAppend_suffix_false
    natSuffixScannerDescription_runConfig_nonblank_suffix_inv
    configurationSuffixScannerDescription_runConfig_canonical_false_suffix_inv
    finalHitFlagsScannerDescription_runConfig_canonical_inv
    finalHitFlagsScannerDescription_runConfig_inv
    encodeCodeWordAsInput_transition_prefix_inv
    checkedDovetailLayoutScannerDescription_haltsWithTape_inputBoolWord_inv
    checkedDovetailLayoutScannerDescription_haltsWithTape_stageField_inv
    checkedDovetailLayoutScannerDescription_haltsWithTape_finalFlags_inv )

export EncodedRewriters.CanonicalLayouts.DovetailStagePrefix
  ( NatSuffixScannerDescription
    natBits_eq_encodeNatAppend
    markedPrefix_run_state200_stageNat_handoff
    natSuffix_run_state200_stageNat_to_state210 )

end ScannerInversions

namespace CodeWordEmitters

export EncodedRewriters.CanonicalLayouts
  ( ExactOutputTape
    exactOutputTape_normalizedOutput
    ExactEmitterSpec
    ExactEmitterConstruction
    OutputTape
    outputTape_normalizedOutput
    RightShiftedOutputTape
    rightShiftedOutputTape_normalizedOutput
    EmitterSpec
    EmitterConstruction
    RightShiftedEmitterSpec
    RightShiftedEmitterConstruction )

theorem rightShiftedOutputCompiled_of_indexed_tape_spec
    {ι : Type}
    {P : MachineDescription.TapeCodePrimitive}
    {runner : MachineDescription}
    (hwell : runner.WellFormed)
    (hhaltFree : runner.HaltTransitionFree)
    (inputCode outputCode : ι -> Word MachineCodeSymbol)
    (outputTape : ι -> Tape Bool)
    (houtputTape :
      forall i : ι,
        outputTape i =
          Tape.move Direction.right
            (Tape.input
              (MachineDescription.encodeCodeWordAsInput
                (outputCode i))))
    (hforward :
      forall i : ι,
        runner.HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput (inputCode i))
          (outputTape i))
    (hclosed :
      forall code : Word MachineCodeSymbol,
      forall T : Tape Bool,
        runner.HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput code) T ->
        exists i : ι, code = inputCode i ∧ T = outputTape i)
    (htransform :
      forall code out : Word MachineCodeSymbol,
        P.transform code = some out <->
          exists i : ι, code = inputCode i ∧ out = outputCode i) :
    EncodedRewriters.RightShiftedOutputCompiledSubroutineByDescription
      P runner := by
  constructor
  · exact hwell
  constructor
  · exact hhaltFree
  constructor
  · intro code out
    constructor
    · intro hhalt
      rcases hhalt with ⟨n, hn⟩
      let T : Tape Bool :=
        (runner.runConfig n
          (runner.initial
            (MachineDescription.encodeCodeWordAsInput code))).tape
      have hTape :
          runner.HaltsWithTape
              (MachineDescription.encodeCodeWordAsInput code) T := by
        exact ⟨n, ⟨hn.left, rfl⟩⟩
      rcases hclosed code T hTape with ⟨i, hcode, hT⟩
      have hactual :
          Tape.normalizedOutput T =
            MachineDescription.encodeCodeWordAsInput out := by
        simpa [T] using hn.right
      have hexpected :
          Tape.normalizedOutput T =
            MachineDescription.encodeCodeWordAsInput (outputCode i) := by
        rw [hT, houtputTape i]
        exact
          EncodedRewriters.tape_normalizedOutput_move_right_input
            (MachineDescription.encodeCodeWordAsInput (outputCode i))
      have houtBits :
          MachineDescription.encodeCodeWordAsInput out =
            MachineDescription.encodeCodeWordAsInput (outputCode i) :=
        hactual.symm.trans hexpected
      have hout : out = outputCode i :=
        MachineDescription.encodeCodeWordAsInput_injective houtBits
      exact (htransform code out).mpr ⟨i, hcode, hout⟩
    · intro hP
      rcases (htransform code out).mp hP with ⟨i, hcode, hout⟩
      rw [hcode, hout]
      simpa [houtputTape i,
        EncodedRewriters.tape_normalizedOutput_move_right_input] using
        MachineDescription.haltsWithOutput_of_haltsWithTape
          (hforward i)
  · intro code T hhalt
    rcases hclosed code T hhalt with ⟨i, hcode, hT⟩
    refine ⟨outputCode i, ?_, ?_⟩
    · exact (htransform code (outputCode i)).mpr ⟨i, hcode, rfl⟩
    · rw [hT, houtputTape i]

end CodeWordEmitters

namespace DovetailLayouts

export EncodedRewriters.CanonicalLayouts.Dovetail
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
    identityPrimitive_encode
    identityClosedHandoffConstruction_of_closedRecognizer )

abbrev IdentityRightShiftedConstruction : Prop :=
  exists runner : MachineDescription,
    EncodedRewriters.RightShiftedOutputCompiledSubroutineByDescription
      identityPrimitive runner

theorem identityPrimitive_transform_eq_some_cons
    {code out : Word MachineCodeSymbol}
    (h : identityPrimitive.transform code = some out) :
    exists symbol : MachineCodeSymbol,
    exists tail : Word MachineCodeSymbol,
      out = symbol :: tail :=
  EncodedRewriters.CanonicalLayouts.identityPrimitive_transform_eq_some_cons
    decode_encode (fun h => decode_eq_some_encode h) encode_cons h

theorem identityClosedHandoffConstruction_of_rightShifted
    (h : IdentityRightShiftedConstruction) :
    IdentityClosedHandoffConstruction := by
  rcases h with ⟨runner, hrunner⟩
  exact
    ⟨runner,
      EncodedRewriters.closedHandoffCompiled_of_rightShiftedOutputCompiled
        hrunner
        (by
          intro code out htransform
          exact identityPrimitive_transform_eq_some_cons htransform)⟩

end DovetailLayouts

namespace SimulatorLayouts

export EncodedRewriters.CanonicalLayouts.Simulator
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

export MachineDescription.SimulatorLayout
  ( encodeAppend
    decodeComplete
    decodeComplete_encode
    decodeComplete_eq_some_encode
    asBoolInput
    run
    runCode
    runCodePrimitive
    normalizeCodePrimitive )

end SimulatorLayouts

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
  cases C with
  | mk input stage oldResult =>
      have hnat :
          MachineDescription.encodeNatAppend stage
              (MachineDescription.encodeBoolWordAppend result []) =
            List.append (MachineDescription.encodeNatAppend stage [])
              (MachineDescription.encodeBoolWordAppend result []) := by
        simpa using
          encodeNatAppend_append stage ([] : Word MachineCodeSymbol)
            (MachineDescription.encodeBoolWordAppend result [])
      simp [PairedRecognizerDovetailControllerStageInputCode,
        MachineDescription.DovetailControllerLayout.withResult,
        MachineDescription.DovetailControllerLayout.encode,
        MachineDescription.DovetailControllerLayout.encodeAppend,
        MachineDescription.DovetailControllerLayout.stageInputCode,
        MachineDescription.DovetailLayout.stageInputCode,
        MachineDescription.DovetailLayout.stageInputCodeAppend, hnat]
      change
        MachineCodeSymbol.header ::
            MachineDescription.encodeBoolWordAppend input
              (List.append (MachineDescription.encodeNatAppend stage [])
                (MachineDescription.encodeBoolWordAppend result [])) =
          MachineCodeSymbol.header ::
            List.append
              (MachineDescription.encodeBoolWordAppend input
                (MachineDescription.encodeNatAppend stage []))
              (MachineDescription.encodeBoolWordAppend result [])
      rw [encodeBoolWordAppend_append input
        (MachineDescription.encodeNatAppend stage [])
        (MachineDescription.encodeBoolWordAppend result [])]

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

namespace BoolWordQuoters

export DovetailInitialLayoutInitializer
  ( stageInputBits
    inputTapeBits
    AppendInputTapeReturnForwardSpec
    AppendInputTapeReturnSpec
    appendInputTapeReturnSpec_realizer
    checkedNonemptyBoolWordQuoteDirectSourceBits
    checkedNonemptyBoolWordQuoteDirectSourceBits_eq
    checkedNonemptyBoolWordQuoteDirectCopiedTrailerBits
    checkedNonemptyBoolWordQuoteDirectSourceBits_encodeNatAppend
    CheckedRawBoolWordAppendCodeWordReturnDescription
    checkedRawBoolWordAppendCodeWordReturnDescription_subroutineReady
    checkedRawBoolWordAppendCodeWordReturnDescription_run
    checkedRawBoolWordAppendCodeWordReturnDescription_haltsFromTape
    CheckedRawBoolWordAppendHeaderReturnDescription
    checkedRawBoolWordAppendHeaderReturnDescription_subroutineReady
    checkedRawBoolWordAppendHeaderReturnDescription_run
    checkedRawBoolWordAppendHeaderReturnDescription_haltsFromTape )

def RawBoolWordHeaderEmitterSpec
    (suffix : Word MachineCodeSymbol)
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall w : Word Bool,
      emitter.HaltsWithOutput w
        (MachineDescription.encodeCodeWordAsInput
          (MachineCodeSymbol.header ::
            MachineDescription.encodeBoolWordAppend w suffix))

def RawBoolWordHeaderEmitterConstruction
    (suffix : Word MachineCodeSymbol) : Prop :=
  exists emitter : MachineDescription,
    RawBoolWordHeaderEmitterSpec suffix emitter

end BoolWordQuoters

namespace Identity

theorem exactIdentityDescription_subroutineReady :
    MachineDescription.ExactIdentityDescription.SubroutineReady :=
  ⟨MachineDescription.exactIdentityDescription_wellFormed,
    MachineDescription.exactIdentityDescription_haltTransitionFree⟩

theorem exactIdentityDescription_haltsFromTape
    (T : Tape Bool) :
    MachineDescription.ExactIdentityDescription.HaltsFromTape T T := by
  refine ⟨0, ?_⟩
  constructor <;> rfl

theorem exactIdentityDescription_run_from_start
    (T : Tape Bool) :
    exists steps : Nat,
      MachineDescription.ExactIdentityDescription.runConfig steps
          { state := MachineDescription.ExactIdentityDescription.start
            tape := T } =
        { state := MachineDescription.ExactIdentityDescription.halt
          tape := T } := by
  refine ⟨0, ?_⟩
  simp [MachineDescription.ExactIdentityDescription,
    MachineDescription.runConfig]

end Identity

namespace LeftBoundaryReturn

def ReturnToLeftBoundaryDescription : MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove
        0 (some false) Direction.left 0
    , DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove
        0 (some true) Direction.left 0
    , DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove
        0 none Direction.right 1
    ]

theorem returnToLeftBoundaryDescription_wellFormed :
    ReturnToLeftBoundaryDescription.WellFormed := by
  refine ⟨by native_decide, by native_decide, by native_decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := ReturnToLeftBoundaryDescription.transitions)
      (stateCount := ReturnToLeftBoundaryDescription.stateCount)
      (by native_decide)
  · exact transition_deterministic_of_all
      (l := ReturnToLeftBoundaryDescription.transitions)
      (by native_decide)

theorem returnToLeftBoundaryDescription_haltTransitionFree :
    ReturnToLeftBoundaryDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := ReturnToLeftBoundaryDescription.transitions)
    (state := ReturnToLeftBoundaryDescription.halt)
    (by native_decide)

theorem returnToLeftBoundaryDescription_subroutineReady :
    ReturnToLeftBoundaryDescription.SubroutineReady :=
  ⟨returnToLeftBoundaryDescription_wellFormed,
    returnToLeftBoundaryDescription_haltTransitionFree⟩

def returnToLeftBoundaryScanConfig
    (remainingRev : Word Bool) (scanned : List (Option Bool)) :
    MachineDescription.Configuration :=
  match remainingRev with
  | [] =>
      { state := 0
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells []
            (none :: scanned) }
  | bit :: rest =>
      { state := 0
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            (rest.map some) (some bit :: scanned) }

theorem returnToLeftBoundaryDescription_run_scan
    (remainingRev : Word Bool) (scanned : List (Option Bool)) :
    ReturnToLeftBoundaryDescription.runConfig
        (remainingRev.length + 1)
        (returnToLeftBoundaryScanConfig remainingRev scanned) =
      { state := ReturnToLeftBoundaryDescription.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells [none]
            (List.append (remainingRev.reverse.map some) scanned) } := by
  induction remainingRev generalizing scanned with
  | nil =>
      cases scanned <;>
      simp [returnToLeftBoundaryScanConfig,
        ReturnToLeftBoundaryDescription,
        DovetailInitialLayoutInitializer.tapeAtCells,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
        MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition,
        MachineDescription.Matches,
        MachineDescription.transition,
        Tape.read, Tape.write, Tape.move, Tape.moveRight]
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 = 1 + (rest.length + 1) by
        simp
        omega]
      have hstep :
          ReturnToLeftBoundaryDescription.runConfig 1
              (returnToLeftBoundaryScanConfig (bit :: rest) scanned) =
            returnToLeftBoundaryScanConfig rest (some bit :: scanned) := by
        cases bit <;> cases rest <;>
          simp [returnToLeftBoundaryScanConfig,
            ReturnToLeftBoundaryDescription,
            DovetailInitialLayoutInitializer.tapeAtCells,
            DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
            MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition,
            MachineDescription.Matches,
            MachineDescription.transition,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [MachineDescription.runConfig_add]
      rw [hstep]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (some bit :: scanned)

theorem returnToLeftBoundaryDescription_run_from_cells
    (prefixRev : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    ReturnToLeftBoundaryDescription.runConfig
        (prefixRev.length + 2)
        { state := ReturnToLeftBoundaryDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (prefixRev.map some) (some current :: right) } =
      { state := ReturnToLeftBoundaryDescription.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells [none]
            (List.append (prefixRev.reverse.map some)
              (some current :: right)) } := by
  rw [show prefixRev.length + 2 = 1 + (prefixRev.length + 1) by omega]
  rw [MachineDescription.runConfig_add]
  have hstep :
      ReturnToLeftBoundaryDescription.runConfig 1
          { state := ReturnToLeftBoundaryDescription.start
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells
                (prefixRev.map some) (some current :: right) } =
        returnToLeftBoundaryScanConfig prefixRev
          (some current :: right) := by
    cases current <;> cases prefixRev <;>
      simp [returnToLeftBoundaryScanConfig,
        ReturnToLeftBoundaryDescription,
        DovetailInitialLayoutInitializer.tapeAtCells,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
        MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition,
        MachineDescription.Matches,
        MachineDescription.transition,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft]
  rw [hstep]
  simpa [List.append_assoc] using
    returnToLeftBoundaryDescription_run_scan prefixRev
      (some current :: right)

theorem returnToLeftBoundaryDescription_haltsFromTape_from_cells
    (prefixRev : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    ReturnToLeftBoundaryDescription.HaltsFromTape
      (DovetailInitialLayoutInitializer.tapeAtCells
        (prefixRev.map some) (some current :: right))
      (DovetailInitialLayoutInitializer.tapeAtCells [none]
        (List.append (prefixRev.reverse.map some)
          (some current :: right))) := by
  rcases
      returnToLeftBoundaryDescription_run_from_cells
        prefixRev current right with
    hrun
  refine ⟨prefixRev.length + 2, ?_⟩
  constructor
  · simpa [MachineDescription.HaltsFromTapeIn] using
      congrArg MachineDescription.Configuration.state hrun
  · simpa [MachineDescription.HaltsFromTapeIn] using
      congrArg MachineDescription.Configuration.tape hrun

end LeftBoundaryReturn

namespace AppendReturn

export DovetailInitialLayoutInitializer
  ( AppendCodeWordLastDescription
    appendCodeWordLastDescription_subroutineReady
    appendCodeWordLastDescription_run_from_scan
    appendCodeWordLastDescription_run_from_scan_atCells
    appendCodeWordLastTape
    appendCodeWordLastTapeAtCells
    encodeNat_ne_nil
    AppendNatLastDescription
    appendNatLastTape
    appendNatLastDescription_subroutineReady
    appendNatLastDescription_run_from_scan
    appendNatLastDescription_haltsWithTape
    MarkedPrefixThenAppendNatLastDescription
    markedPrefixThenAppendNatLastDescription_subroutineReady
    markedPrefixThenAppendNatLastDescription_run
    ReturnToCurrentMarkerDescription
    returnToCurrentMarkerDescription_subroutineReady
    returnToCurrentMarkerDescription_run
    returnToCurrentMarkerDescription_run_after_append_atCells
    AppendCodeWordReturnToCurrentMarkerDescription
    appendCodeWordReturnToCurrentMarkerDescription_subroutineReady
    appendCodeWordReturnToCurrentMarkerDescription_run_from_scan
    markedPrefixAppendCodeWordReturnDescription_run_checked
    markedPrefixAppendCodeWordReturnDescription_run_stageInput
    MarkedPrefixAppendNatReturnDescription
    markedPrefixAppendNatReturnDescription_subroutineReady
    markedPrefixAppendNatReturnDescription_run
    markedPrefixAppendNatReturnDescription_run_checked
    markedPrefixAppendNatReturnDescription_run_stageInput
    markedPrefixAppendNatReturnDescription_run_stageInput_checked
    AppendCodeSymbolReturnToCurrentMarkerDescription
    appendCodeSymbolReturnToCurrentMarkerDescription_subroutineReady
    appendCodeSymbolReturnToCurrentMarkerDescription_run_from_scan
    TransitionPrefixedThenAppendCodeWordLastDescription
    transitionPrefixedThenAppendCodeWordLastDescription_subroutineReady
    transitionPrefixedThenAppendCodeWordLastDescription_run
    TransitionPrefixedAppendNatReturnDescription
    transitionPrefixedAppendNatReturnDescription_subroutineReady
    transitionPrefixedAppendNatReturnDescription_run )

end AppendReturn

end CommonGround

end Computability
end FoC
