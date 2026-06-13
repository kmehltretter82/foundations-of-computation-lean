import FoC.Computability.MachineBuilder.DovetailLayout

set_option doc.verso true

/-!
# Machine-builder dovetail controller layouts
-/

namespace FoC
namespace Computability

open Languages

namespace MachineDescription

structure DovetailControllerLayout where
  input : Word Bool
  stage : Nat
  result : Word Bool

namespace DovetailControllerLayout

def encodeAppend (C : DovetailControllerLayout)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineCodeSymbol.header ::
    DovetailLayout.stageInputCodeAppend C.input C.stage
      (encodeBoolWordAppend C.result suffix)

def encode (C : DovetailControllerLayout) :
    Word MachineCodeSymbol :=
  encodeAppend C []

def decode (tokens : Word MachineCodeSymbol) :
    Option (DovetailControllerLayout × Word MachineCodeSymbol) :=
  match tokens with
  | MachineCodeSymbol.header :: rest =>
      match DovetailLayout.decodeStageInput rest with
      | none => none
      | some ((input, stage), rest) =>
          match decodeBoolWord rest with
          | none => none
          | some (result, suffix) =>
              some ({ input := input, stage := stage, result := result },
                suffix)
  | _ => none

theorem decode_encodeAppend
    (C : DovetailControllerLayout)
    (suffix : Word MachineCodeSymbol) :
    decode (encodeAppend C suffix) = some (C, suffix) := by
  cases C
  simp [encodeAppend, decode,
    DovetailLayout.decodeStageInput_stageInputCodeAppend,
    decodeBoolWord_encodeBoolWordAppend]

theorem decode_encode (C : DovetailControllerLayout) :
    decode (encode C) = some (C, []) :=
  decode_encodeAppend C []

def decodeComplete (tokens : Word MachineCodeSymbol) :
    Option DovetailControllerLayout :=
  match decode tokens with
  | some (C, []) => some C
  | _ => none

theorem decodeComplete_encode (C : DovetailControllerLayout) :
    decodeComplete (encode C) = some C := by
  simp [decodeComplete, decode_encode]

def initial (w : Word Bool) : DovetailControllerLayout where
  input := w
  stage := 0
  result := []

def stageInputCode (C : DovetailControllerLayout) :
    Word MachineCodeSymbol :=
  DovetailLayout.stageInputCode C.input C.stage

def withResult (C : DovetailControllerLayout)
    (result : Word Bool) : DovetailControllerLayout :=
  { C with result := result }

def nextStage (C : DovetailControllerLayout) :
    DovetailControllerLayout :=
  { C with stage := C.stage + 1, result := [] }

def decodeAttemptResultCode
    (tokens : Word MachineCodeSymbol) : Option (Word Bool) :=
  match decodeBoolWord tokens with
  | some (result, []) => some result
  | _ => none

theorem decodeAttemptResultCode_encodeBoolWord
    (result : Word Bool) :
    decodeAttemptResultCode (encodeBoolWord result) = some result := by
  simp [decodeAttemptResultCode, encodeBoolWord,
    decodeBoolWord_encodeBoolWordAppend]

def rawOutput? : Word Bool -> Option (Word Bool)
  | b :: [] => some [b]
  | _ => none

def rawOutputCode
    (tokens : Word MachineCodeSymbol) : Option (Word MachineCodeSymbol) :=
  match decodeAttemptResultCode tokens with
  | none => none
  | some result =>
      match rawOutput? result with
      | none => none
      | some out => some (encodeBoolWord out)

def rawOutputCodePrimitive : TapeCodePrimitive where
  transform := rawOutputCode

theorem rawOutputCode_eq_some_iff
    {tokens outCode : Word MachineCodeSymbol} :
    rawOutputCode tokens = some outCode <->
      exists result out : Word Bool,
        decodeAttemptResultCode tokens = some result ∧
          rawOutput? result = some out ∧
            outCode = encodeBoolWord out := by
  unfold rawOutputCode
  cases hdecode : decodeAttemptResultCode tokens with
  | none =>
      simp
  | some result =>
      cases hraw : rawOutput? result with
      | none =>
          simp [hraw]
      | some out =>
          simp [hraw]
          constructor
          · intro h
            exact h.symm
          · intro h
            exact h.symm

theorem rawOutput_nil :
    rawOutput? [] = none :=
  rfl

theorem rawOutput_singleton (b : Bool) :
    rawOutput? [b] = some [b] :=
  rfl

theorem rawOutputCode_encodeBoolWord
    (result : Word Bool) :
    rawOutputCode (encodeBoolWord result) =
      Option.map encodeBoolWord (rawOutput? result) := by
  cases h : rawOutput? result <;>
    simp [rawOutputCode, decodeAttemptResultCode_encodeBoolWord, h]

theorem rawOutputCodePrimitive_encodeBoolWord
    (result : Word Bool) :
    rawOutputCodePrimitive.transform (encodeBoolWord result) =
      Option.map encodeBoolWord (rawOutput? result) :=
  rawOutputCode_encodeBoolWord result

theorem rawOutputCode_encodeBoolWord_nil :
    rawOutputCode (encodeBoolWord []) = none := by
  simp [rawOutputCode_encodeBoolWord, rawOutput_nil]

theorem rawOutputCode_encodeBoolWord_singleton (b : Bool) :
    rawOutputCode (encodeBoolWord [b]) =
      some (encodeBoolWord [b]) := by
  rw [rawOutputCode_encodeBoolWord, rawOutput_singleton]
  rfl

theorem rawOutputCode_encodeBoolWord_outputWordFromHits
    (L : DovetailLayout) :
    rawOutputCode (encodeBoolWord (DovetailLayout.outputWordFromHits L)) =
      Option.map encodeBoolWord (DovetailLayout.outputFromHits L) := by
  cases haccept : L.acceptHit <;> cases hreject : L.rejectHit <;>
    simp [DovetailLayout.outputWordFromHits,
      DovetailLayout.outputWordFromOption,
      DovetailLayout.outputFromHits, haccept, hreject,
      rawOutputCode_encodeBoolWord_nil,
      rawOutputCode_encodeBoolWord_singleton]

theorem rawOutput_eq_some_singleton_iff
    (result : Word Bool) (b : Bool) :
    rawOutput? result = some [b] <-> result = [b] := by
  constructor
  · intro h
    cases result with
    | nil =>
        simp [rawOutput?] at h
    | cons head tail =>
        cases tail with
        | nil =>
            exact Option.some.inj h
        | cons next rest =>
            simp [rawOutput?] at h
  · intro h
    rw [h]
    exact rawOutput_singleton b

theorem rawOutputCode_eq_some_encodeBoolWord_singleton_iff
    {tokens : Word MachineCodeSymbol} {b : Bool} :
    rawOutputCode tokens = some (encodeBoolWord [b]) <->
      decodeAttemptResultCode tokens = some [b] := by
  constructor
  · intro h
    rcases rawOutputCode_eq_some_iff.mp h with
      ⟨result, out, hdecode, hraw, hcode⟩
    have hout : [b] = out := encodeBoolWord_injective hcode
    rw [← hout] at hraw
    have hresult : result = [b] :=
      (rawOutput_eq_some_singleton_iff result b).mp hraw
    rwa [hresult] at hdecode
  · intro h
    exact rawOutputCode_eq_some_iff.mpr
      ⟨[b], [b], h, rawOutput_singleton b, rfl⟩

theorem cellBranchTarget_output_nil
    (blankTarget falseTarget trueTarget : Nat) :
    cellBranchTarget (Tape.read (Tape.output ([] : Word Bool)))
      blankTarget falseTarget trueTarget =
        blankTarget :=
  rfl

theorem cellBranchTarget_output_singleton
    (b : Bool) (blankTarget falseTarget trueTarget : Nat) :
    cellBranchTarget (Tape.read (Tape.output [b]))
      blankTarget falseTarget trueTarget =
        if b then trueTarget else falseTarget := by
  cases b <;> rfl

theorem cellBranchTarget_output_of_rawOutput_eq_some
    {result : Word Bool} {b : Bool}
    (blankTarget falseTarget trueTarget : Nat)
    (hraw : rawOutput? result = some [b]) :
    cellBranchTarget (Tape.read (Tape.output result))
      blankTarget falseTarget trueTarget =
        if b then trueTarget else falseTarget := by
  have hresult := (rawOutput_eq_some_singleton_iff result b).mp hraw
  rw [hresult]
  exact cellBranchTarget_output_singleton b
    blankTarget falseTarget trueTarget

theorem cellBranchDescription_runConfig_one_output_nil
    (stateCount source halt blankTarget falseTarget trueTarget : Nat)
    (move : Direction) :
    (cellBranchDescription stateCount source halt
      blankTarget falseTarget trueTarget move).runConfig 1
        { state := source, tape := Tape.output ([] : Word Bool) } =
      { state := blankTarget,
        tape := Tape.move move (Tape.output ([] : Word Bool)) } := by
  rw [cellBranchDescription_runConfig_one_start]
  rfl

theorem cellBranchDescription_runConfig_one_output_of_rawOutput_eq_some
    (stateCount source halt blankTarget falseTarget trueTarget : Nat)
    (move : Direction) {result : Word Bool} {b : Bool}
    (hraw : rawOutput? result = some [b]) :
    (cellBranchDescription stateCount source halt
      blankTarget falseTarget trueTarget move).runConfig 1
        { state := source, tape := Tape.output result } =
      { state := if b then trueTarget else falseTarget,
        tape := Tape.move move (Tape.output result) } := by
  rw [cellBranchDescription_runConfig_one_start]
  rw [cellBranchTarget_output_of_rawOutput_eq_some
    blankTarget falseTarget trueTarget hraw]

def totalAttemptResult
    (accept reject : MachineDescription)
    (C : DovetailControllerLayout) : Word Bool :=
  DovetailLayout.outputWordFromOption
    (boundedDovetailOutput accept reject C.input C.stage)

theorem rawOutput_outputWordFromOption_boundedDovetailOutput
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    rawOutput?
        (DovetailLayout.outputWordFromOption
          (boundedDovetailOutput accept reject w stage)) =
      boundedDovetailOutput accept reject w stage := by
  by_cases haccept : hitsByBool accept w stage = true
  · simp [boundedDovetailOutput, haccept, DovetailLayout.outputWordFromOption,
      rawOutput?]
  · by_cases hreject : hitsByBool reject w stage = true
    · simp [boundedDovetailOutput, haccept, hreject,
        DovetailLayout.outputWordFromOption, rawOutput?]
    · simp [boundedDovetailOutput, haccept, hreject,
        DovetailLayout.outputWordFromOption, rawOutput?]

theorem rawOutput_totalAttemptResult
    (accept reject : MachineDescription)
    (C : DovetailControllerLayout) :
    rawOutput? (totalAttemptResult accept reject C) =
      boundedDovetailOutput accept reject C.input C.stage :=
  rawOutput_outputWordFromOption_boundedDovetailOutput
    accept reject C.input C.stage

def continueCode
    (accept reject : MachineDescription)
    (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match decodeComplete tokens with
  | none => none
  | some C =>
      match rawOutput? (totalAttemptResult accept reject C) with
      | none => some (encode (nextStage C))
      | some _ => none

def continueCodePrimitive
    (accept reject : MachineDescription) : TapeCodePrimitive where
  transform := continueCode accept reject

def emitCode
    (accept reject : MachineDescription)
    (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match decodeComplete tokens with
  | none => none
  | some C =>
      match rawOutput? (totalAttemptResult accept reject C) with
      | none => none
      | some out => some (encodeBoolWord out)

def emitCodePrimitive
    (accept reject : MachineDescription) : TapeCodePrimitive where
  transform := emitCode accept reject

theorem continueCode_encode
    (accept reject : MachineDescription)
    (C : DovetailControllerLayout) :
    continueCode accept reject (encode C) =
      if boundedDovetailOutput accept reject C.input C.stage = none then
        some (encode (nextStage C))
      else
        none := by
  simp [continueCode, decodeComplete_encode]
  cases hraw : rawOutput? (totalAttemptResult accept reject C) with
  | none =>
      have hbounded :
          boundedDovetailOutput accept reject C.input C.stage = none := by
        simpa [rawOutput_totalAttemptResult] using hraw
      simp [hbounded]
  | some out =>
      have hbounded :
          boundedDovetailOutput accept reject C.input C.stage =
            some out := by
        simpa [rawOutput_totalAttemptResult] using hraw
      simp [hbounded]

theorem continueCodePrimitive_encode
    (accept reject : MachineDescription)
    (C : DovetailControllerLayout) :
    (continueCodePrimitive accept reject).transform (encode C) =
      if boundedDovetailOutput accept reject C.input C.stage = none then
        some (encode (nextStage C))
      else
        none :=
  continueCode_encode accept reject C

theorem continueCode_encode_of_boundedDovetailOutput_eq_none
    {accept reject : MachineDescription}
    {C : DovetailControllerLayout}
    (h :
      boundedDovetailOutput accept reject C.input C.stage = none) :
    continueCode accept reject (encode C) =
      some (encode (nextStage C)) := by
  rw [continueCode_encode, if_pos h]

theorem continueCode_encode_of_boundedDovetailOutput_eq_some
    {accept reject : MachineDescription}
    {C : DovetailControllerLayout} {out : Word Bool}
    (h :
      boundedDovetailOutput accept reject C.input C.stage = some out) :
    continueCode accept reject (encode C) = none := by
  rw [continueCode_encode, if_neg]
  intro hnone
  rw [h] at hnone
  cases hnone

theorem emitCode_encode
    (accept reject : MachineDescription)
    (C : DovetailControllerLayout) :
    emitCode accept reject (encode C) =
      Option.map encodeBoolWord
        (boundedDovetailOutput accept reject C.input C.stage) := by
  simp [emitCode, decodeComplete_encode]
  rw [rawOutput_totalAttemptResult]
  cases boundedDovetailOutput accept reject C.input C.stage <;> rfl

theorem emitCodePrimitive_encode
    (accept reject : MachineDescription)
    (C : DovetailControllerLayout) :
    (emitCodePrimitive accept reject).transform (encode C) =
      Option.map encodeBoolWord
        (boundedDovetailOutput accept reject C.input C.stage) :=
  emitCode_encode accept reject C

theorem emitCode_encode_of_boundedDovetailOutput_eq_some
    {accept reject : MachineDescription}
    {C : DovetailControllerLayout} {out : Word Bool}
    (h :
      boundedDovetailOutput accept reject C.input C.stage = some out) :
    emitCode accept reject (encode C) =
      some (encodeBoolWord out) := by
  rw [emitCode_encode, h]
  rfl

theorem emitCode_encode_of_boundedDovetailOutput_eq_none
    {accept reject : MachineDescription}
    {C : DovetailControllerLayout}
    (h :
      boundedDovetailOutput accept reject C.input C.stage = none) :
    emitCode accept reject (encode C) = none := by
  rw [emitCode_encode, h]
  rfl

theorem continueCode_encode_eq_some_iff
    {accept reject : MachineDescription}
    {C : DovetailControllerLayout}
    {out : Word MachineCodeSymbol} :
    continueCode accept reject (encode C) = some out <->
      boundedDovetailOutput accept reject C.input C.stage = none ∧
        out = encode (nextStage C) := by
  by_cases hnone :
      boundedDovetailOutput accept reject C.input C.stage = none
  · rw [continueCode_encode_of_boundedDovetailOutput_eq_none hnone]
    constructor
    · intro hout
      exact ⟨hnone, (Option.some.inj hout).symm⟩
    · intro hout
      rw [hout.right]
  · rw [continueCode_encode, if_neg hnone]
    simp [hnone]

theorem continueCodePrimitive_encode_eq_some_iff
    {accept reject : MachineDescription}
    {C : DovetailControllerLayout}
    {out : Word MachineCodeSymbol} :
    (continueCodePrimitive accept reject).transform (encode C) =
        some out <->
      boundedDovetailOutput accept reject C.input C.stage = none ∧
        out = encode (nextStage C) :=
  continueCode_encode_eq_some_iff

theorem emitCode_encode_eq_some_iff
    {accept reject : MachineDescription}
    {C : DovetailControllerLayout}
    {outCode : Word MachineCodeSymbol} :
    emitCode accept reject (encode C) = some outCode <->
      exists out : Word Bool,
        boundedDovetailOutput accept reject C.input C.stage = some out ∧
          outCode = encodeBoolWord out := by
  constructor
  · intro houtCode
    rw [emitCode_encode] at houtCode
    let result :=
      boundedDovetailOutput accept reject C.input C.stage
    cases hresult : result with
    | none =>
        have hnone :
            boundedDovetailOutput accept reject C.input C.stage = none := by
          simpa [result] using hresult
        simp [hnone] at houtCode
    | some out =>
        have hsome :
            boundedDovetailOutput accept reject C.input C.stage =
              some out := by
          simpa [result] using hresult
        refine ⟨out, hsome, ?_⟩
        rw [hsome] at houtCode
        exact (Option.some.inj houtCode).symm
  · intro houtCode
    rcases houtCode with ⟨out, hbounded, rfl⟩
    exact emitCode_encode_of_boundedDovetailOutput_eq_some hbounded

theorem emitCodePrimitive_encode_eq_some_iff
    {accept reject : MachineDescription}
    {C : DovetailControllerLayout}
    {outCode : Word MachineCodeSymbol} :
    (emitCodePrimitive accept reject).transform (encode C) = some outCode <->
      exists out : Word Bool,
        boundedDovetailOutput accept reject C.input C.stage = some out ∧
          outCode = encodeBoolWord out :=
  emitCode_encode_eq_some_iff

theorem emitCode_encode_eq_encodeBoolWord_iff
    {accept reject : MachineDescription}
    {C : DovetailControllerLayout}
    {out : Word Bool} :
    emitCode accept reject (encode C) = some (encodeBoolWord out) <->
      boundedDovetailOutput accept reject C.input C.stage = some out := by
  constructor
  · intro h
    rcases emitCode_encode_eq_some_iff.mp h with
      ⟨actual, hactual, hcode⟩
    have hsame : out = actual :=
      encodeBoolWord_injective hcode
    rwa [hsame]
  · intro h
    exact emitCode_encode_of_boundedDovetailOutput_eq_some h

theorem emitCodePrimitive_encode_eq_encodeBoolWord_iff
    {accept reject : MachineDescription}
    {C : DovetailControllerLayout}
    {out : Word Bool} :
    (emitCodePrimitive accept reject).transform (encode C) =
        some (encodeBoolWord out) <->
      boundedDovetailOutput accept reject C.input C.stage = some out :=
  emitCode_encode_eq_encodeBoolWord_iff

theorem continueCode_emitCode_encode_exclusive
    {accept reject : MachineDescription}
    {C : DovetailControllerLayout}
    {next out : Word MachineCodeSymbol}
    (hcontinue :
      continueCode accept reject (encode C) = some next)
    (hemit :
      emitCode accept reject (encode C) = some out) :
    False := by
  rcases continueCode_encode_eq_some_iff.mp hcontinue with
    ⟨hnone, _⟩
  rcases emitCode_encode_eq_some_iff.mp hemit with
    ⟨actual, hsome, _⟩
  rw [hnone] at hsome
  cases hsome

theorem continue_emit_branch_encode
    (accept reject : MachineDescription)
    (C : DovetailControllerLayout) :
    (continueCode accept reject (encode C) =
        some (encode (nextStage C)) ∧
      emitCode accept reject (encode C) = none) ∨
      (continueCode accept reject (encode C) = none ∧
        exists out : Word Bool,
          boundedDovetailOutput accept reject C.input C.stage = some out ∧
            emitCode accept reject (encode C) =
              some (encodeBoolWord out)) := by
  let result := boundedDovetailOutput accept reject C.input C.stage
  cases hresult : result with
  | none =>
      left
      have hnone :
          boundedDovetailOutput accept reject C.input C.stage = none := by
        simpa [result] using hresult
      exact
        ⟨continueCode_encode_of_boundedDovetailOutput_eq_none hnone,
          emitCode_encode_of_boundedDovetailOutput_eq_none hnone⟩
  | some out =>
      right
      have hsome :
          boundedDovetailOutput accept reject C.input C.stage =
            some out := by
        simpa [result] using hresult
      exact
        ⟨continueCode_encode_of_boundedDovetailOutput_eq_some hsome,
          ⟨out, hsome,
            emitCode_encode_of_boundedDovetailOutput_eq_some hsome⟩⟩

theorem rawOutputCode_after_totalStageAttemptCode
    (accept reject : MachineDescription)
    (tokens : Word MachineCodeSymbol) :
    (TapeCodePrimitive.compose
      (DovetailLayout.totalStageAttemptCodePrimitive accept reject)
      rawOutputCodePrimitive).transform tokens =
      (DovetailLayout.stageAttemptCodePrimitive accept reject).transform
        tokens := by
  unfold TapeCodePrimitive.compose
  change
    (match
      (DovetailLayout.totalStageAttemptCodePrimitive accept reject).transform
        tokens with
    | none => none
    | some mid => rawOutputCodePrimitive.transform mid) =
      (DovetailLayout.stageAttemptCodePrimitive accept reject).transform
        tokens
  unfold DovetailLayout.totalStageAttemptCodePrimitive
    DovetailLayout.stageAttemptCodePrimitive
  change
    (match DovetailLayout.totalStageAttemptCode accept reject tokens with
    | none => none
    | some mid => rawOutputCodePrimitive.transform mid) =
      DovetailLayout.stageAttemptCode accept reject tokens
  unfold DovetailLayout.totalStageAttemptCode DovetailLayout.stageAttemptCode
  cases hdecode : DovetailLayout.decodeStageInputComplete tokens with
  | none =>
      simp
  | some parsed =>
      cases parsed with
      | mk w stage =>
          cases houtput :
              DovetailLayout.outputFromHits
                (DovetailLayout.run accept reject stage
                  (DovetailLayout.initial accept reject w stage)) <;>
          simp [rawOutputCodePrimitive,
            rawOutputCode_encodeBoolWord_outputWordFromHits, houtput]

theorem rawOutputCode_after_totalStageAttemptCode_stageInputCode
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    (TapeCodePrimitive.compose
      (DovetailLayout.totalStageAttemptCodePrimitive accept reject)
      rawOutputCodePrimitive).transform
        (DovetailLayout.stageInputCode w stage) =
      Option.map encodeBoolWord
        (boundedDovetailOutput accept reject w stage) := by
  rw [rawOutputCode_after_totalStageAttemptCode,
    DovetailLayout.stageAttemptCodePrimitive_stageInputCode]

end DovetailControllerLayout

theorem boundedDovetailOutput_eq_dovetailProgram_run
    (accept reject : MachineDescription)
    (w : Word Bool) (limit : Nat) :
    boundedDovetailOutput accept reject w limit =
      (DovetailProgram
        (fun w n => accept.HaltsIn n w)
        (fun w n => reject.HaltsIn n w)).run w limit := by
  classical
  by_cases haccept : hitsByBool accept w limit = true
  · have hacceptTrace :
      TraceHitsBy (fun w n => accept.HaltsIn n w) w limit :=
        (hitsByBool_eq_true_iff accept w limit).mp haccept
    simp [boundedDovetailOutput, DovetailProgram, haccept, hacceptTrace]
  · have hacceptTrace :
      ¬ TraceHitsBy (fun w n => accept.HaltsIn n w) w limit := by
        intro h
        exact haccept ((hitsByBool_eq_true_iff accept w limit).mpr h)
    by_cases hreject : hitsByBool reject w limit = true
    · have hrejectTrace :
        TraceHitsBy (fun w n => reject.HaltsIn n w) w limit :=
          (hitsByBool_eq_true_iff reject w limit).mp hreject
      simp [boundedDovetailOutput, DovetailProgram, haccept, hacceptTrace,
        hreject, hrejectTrace]
    · have hrejectTrace :
        ¬ TraceHitsBy (fun w n => reject.HaltsIn n w) w limit := by
          intro h
          exact hreject ((hitsByBool_eq_true_iff reject w limit).mpr h)
      simp [boundedDovetailOutput, DovetailProgram, haccept, hacceptTrace,
        hreject, hrejectTrace]

theorem boundedDovetailOutput_true_iff_of_complementaryTraces
    {accept reject : MachineDescription}
    {L : Language Bool}
    (htraces :
      ComplementaryAcceptanceTraces
        (fun w n => accept.HaltsIn n w)
        (fun w n => reject.HaltsIn n w) L)
    (w : Word Bool) :
    (exists limit : Nat,
      boundedDovetailOutput accept reject w limit = some [true]) <->
        w ∈ L := by
  constructor
  · intro h
    rcases h with ⟨limit, hlimit⟩
    have hrun :
        (DovetailProgram
          (fun w n => accept.HaltsIn n w)
          (fun w n => reject.HaltsIn n w)).run w limit =
          some [true] := by
      simpa [boundedDovetailOutput_eq_dovetailProgram_run]
        using hlimit
    exact (dovetailProgram_decides htraces).left w |>.mp
      ⟨limit, hrun⟩
  · intro hw
    rcases ((dovetailProgram_decides htraces).left w).mpr hw with
      ⟨limit, hrun⟩
    exists limit
    simpa [boundedDovetailOutput_eq_dovetailProgram_run]
      using hrun

theorem boundedDovetailOutput_false_iff_of_complementaryTraces
    {accept reject : MachineDescription}
    {L : Language Bool}
    (htraces :
      ComplementaryAcceptanceTraces
        (fun w n => accept.HaltsIn n w)
        (fun w n => reject.HaltsIn n w) L)
    (w : Word Bool) :
    (exists limit : Nat,
      boundedDovetailOutput accept reject w limit = some [false]) <->
        ¬ w ∈ L := by
  constructor
  · intro h
    rcases h with ⟨limit, hlimit⟩
    have hrun :
        (DovetailProgram
          (fun w n => accept.HaltsIn n w)
          (fun w n => reject.HaltsIn n w)).run w limit =
          some [false] := by
      simpa [boundedDovetailOutput_eq_dovetailProgram_run]
        using hlimit
    exact (dovetailProgram_decides htraces).right w |>.mp
      ⟨limit, hrun⟩
  · intro hw
    rcases ((dovetailProgram_decides htraces).right w).mpr hw with
      ⟨limit, hrun⟩
    exists limit
    simpa [boundedDovetailOutput_eq_dovetailProgram_run]
      using hrun

theorem boundedDovetailOutput_eventually_classifies_of_complementaryTraces
    {accept reject : MachineDescription}
    {L : Language Bool}
    (htraces :
      ComplementaryAcceptanceTraces
        (fun w n => accept.HaltsIn n w)
        (fun w n => reject.HaltsIn n w) L)
    (w : Word Bool) :
    exists limit : Nat,
      (boundedDovetailOutput accept reject w limit = some [true] ∧
          w ∈ L) ∨
        (boundedDovetailOutput accept reject w limit = some [false] ∧
          ¬ w ∈ L) := by
  classical
  by_cases hw : w ∈ L
  · rcases
      (boundedDovetailOutput_true_iff_of_complementaryTraces
        htraces w).mpr hw with
      ⟨limit, hlimit⟩
    exact ⟨limit, Or.inl ⟨hlimit, hw⟩⟩
  · rcases
      (boundedDovetailOutput_false_iff_of_complementaryTraces
        htraces w).mpr hw with
      ⟨limit, hlimit⟩
    exact ⟨limit, Or.inr ⟨hlimit, hw⟩⟩


end MachineDescription

end Computability
end FoC
