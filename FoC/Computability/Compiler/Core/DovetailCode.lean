import FoC.Computability.Compiler.Core.BoundedTrace

set_option doc.verso true

/-!
# Paired-recognizer dovetail code primitives
-/

namespace FoC
namespace Computability

open Languages

def PairedRecognizerDovetailLayoutCode
    (accept reject : MachineDescription) :
    MachineDescription.TapeCodePrimitive :=
  MachineDescription.DovetailLayout.runCodePrimitive accept reject

def PairedRecognizerDovetailStageInputCode
    (w : Word Bool) (stage : Nat) : Word MachineCodeSymbol :=
  MachineDescription.DovetailLayout.stageInputCode w stage

def PairedRecognizerDovetailInitialLayoutCode
    (accept reject : MachineDescription) :
    MachineDescription.TapeCodePrimitive :=
  MachineDescription.DovetailLayout.initialCodePrimitive accept reject

def PairedRecognizerDovetailOutputCode :
    MachineDescription.TapeCodePrimitive :=
  MachineDescription.DovetailLayout.outputCodePrimitive

def PairedRecognizerDovetailTotalOutputCode :
    MachineDescription.TapeCodePrimitive where
  transform := fun tokens =>
    match MachineDescription.DovetailLayout.decodeComplete tokens with
    | none => none
    | some L =>
        some
          (MachineDescription.encodeBoolWord
            (MachineDescription.DovetailLayout.outputWordFromHits L))

def PairedRecognizerDovetailStageAttemptCode
    (accept reject : MachineDescription) :
    MachineDescription.TapeCodePrimitive :=
  MachineDescription.DovetailLayout.stageAttemptCodePrimitive accept reject

def PairedRecognizerDovetailTotalStageAttemptCode
    (accept reject : MachineDescription) :
    MachineDescription.TapeCodePrimitive :=
  MachineDescription.DovetailLayout.totalStageAttemptCodePrimitive
    accept reject

def PairedRecognizerDovetailControllerLayoutCode
    (w : Word Bool) (stage : Nat) (result : Word Bool) :
    Word MachineCodeSymbol :=
  MachineDescription.DovetailControllerLayout.encode
    { input := w, stage := stage, result := result }

def PairedRecognizerDovetailControllerInitialCode
    (w : Word Bool) : Word MachineCodeSymbol :=
  MachineDescription.DovetailControllerLayout.encode
    (MachineDescription.DovetailControllerLayout.initial w)

def PairedRecognizerDovetailControllerStageInputCode
    (C : MachineDescription.DovetailControllerLayout) :
    Word MachineCodeSymbol :=
  MachineDescription.DovetailControllerLayout.stageInputCode C

def PairedRecognizerDovetailControllerStageInputCodePrimitive :
    MachineDescription.TapeCodePrimitive where
  transform := fun tokens =>
    match MachineDescription.DovetailControllerLayout.decodeComplete tokens with
    | none => none
    | some C => some (PairedRecognizerDovetailControllerStageInputCode C)

def PairedRecognizerDovetailControllerRawOutput
    (result : Word Bool) : Option (Word Bool) :=
  MachineDescription.DovetailControllerLayout.rawOutput? result

def PairedRecognizerDovetailControllerRawOutputCode :
    MachineDescription.TapeCodePrimitive :=
  MachineDescription.DovetailControllerLayout.rawOutputCodePrimitive

def PairedRecognizerDovetailControllerResultEmitterCode :
    MachineDescription.TapeCodePrimitive :=
  MachineDescription.DovetailControllerLayout.emitResultCodePrimitive

def PairedRecognizerDovetailControllerResultContinueCode :
    MachineDescription.TapeCodePrimitive :=
  MachineDescription.DovetailControllerLayout.continueResultCodePrimitive

def PairedRecognizerDovetailControllerContinueCode
    (accept reject : MachineDescription) :
    MachineDescription.TapeCodePrimitive :=
  MachineDescription.DovetailControllerLayout.continueCodePrimitive
    accept reject

def PairedRecognizerDovetailControllerEmitCode
    (accept reject : MachineDescription) :
    MachineDescription.TapeCodePrimitive :=
  MachineDescription.DovetailControllerLayout.emitCodePrimitive
    accept reject

def PairedRecognizerDovetailTotalThenRawOutputCode
    (accept reject : MachineDescription) :
    MachineDescription.TapeCodePrimitive :=
  MachineDescription.TapeCodePrimitive.compose
    (PairedRecognizerDovetailTotalStageAttemptCode accept reject)
    PairedRecognizerDovetailControllerRawOutputCode

def PairedRecognizerDovetailTotalStageAttemptSourceCode
    (accept reject : MachineDescription) :
    MachineDescription.TapeCodePrimitive :=
  MachineDescription.TapeCodePrimitive.compose
    (MachineDescription.TapeCodePrimitive.compose
      (PairedRecognizerDovetailInitialLayoutCode accept reject)
      (PairedRecognizerDovetailLayoutCode accept reject))
    PairedRecognizerDovetailTotalOutputCode

def PairedRecognizerDovetailControllerRawOutputCodeRealizes
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  forall result : Word Bool,
    P.transform (MachineDescription.encodeBoolWord result) =
      Option.map MachineDescription.encodeBoolWord
        (PairedRecognizerDovetailControllerRawOutput result)

def PairedRecognizerDovetailControllerContinueCodeRealizes
    (accept reject : MachineDescription)
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  forall C : MachineDescription.DovetailControllerLayout,
    P.transform (MachineDescription.DovetailControllerLayout.encode C) =
      if MachineDescription.boundedDovetailOutput
          accept reject C.input C.stage = none then
        some
          (MachineDescription.DovetailControllerLayout.encode
            (MachineDescription.DovetailControllerLayout.nextStage C))
      else
        none

def PairedRecognizerDovetailControllerEmitCodeRealizes
    (accept reject : MachineDescription)
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  forall C : MachineDescription.DovetailControllerLayout,
    P.transform (MachineDescription.DovetailControllerLayout.encode C) =
      Option.map MachineDescription.encodeBoolWord
        (MachineDescription.boundedDovetailOutput
          accept reject C.input C.stage)

def PairedRecognizerDovetailInitialLayoutCodeRealizes
    (accept reject : MachineDescription)
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  forall w : Word Bool, forall stage : Nat,
    P.transform (PairedRecognizerDovetailStageInputCode w stage) =
      some
        (MachineDescription.DovetailLayout.encode
          (MachineDescription.DovetailLayout.initial
            accept reject w stage))

def PairedRecognizerDovetailLayoutCodeRealizes
    (accept reject : MachineDescription)
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  forall L : MachineDescription.DovetailLayout,
    P.transform (MachineDescription.DovetailLayout.encode L) =
      some
        (MachineDescription.DovetailLayout.encode
          (MachineDescription.DovetailLayout.run
            accept reject L.stage L))

def PairedRecognizerDovetailOutputCodeRealizes
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  forall L : MachineDescription.DovetailLayout, forall out : Word Bool,
    MachineDescription.DovetailLayout.outputFromHits L = some out ->
      P.transform (MachineDescription.DovetailLayout.encode L) =
        some (MachineDescription.encodeBoolWord out)

def PairedRecognizerDovetailTotalOutputCodeRealizes
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  forall L : MachineDescription.DovetailLayout,
    P.transform (MachineDescription.DovetailLayout.encode L) =
      some
        (MachineDescription.encodeBoolWord
          (MachineDescription.DovetailLayout.outputWordFromHits L))

def PairedRecognizerDovetailControllerStageInputCodeRealizes
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  forall C : MachineDescription.DovetailControllerLayout,
    P.transform (MachineDescription.DovetailControllerLayout.encode C) =
      some (PairedRecognizerDovetailControllerStageInputCode C)

def PairedRecognizerDovetailStageAttemptCodeRealizes
    (accept reject : MachineDescription)
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  forall w : Word Bool, forall stage : Nat,
    P.transform (PairedRecognizerDovetailStageInputCode w stage) =
      Option.map MachineDescription.encodeBoolWord
        (MachineDescription.boundedDovetailOutput
          accept reject w stage)

def PairedRecognizerDovetailTotalStageAttemptCodeRealizes
    (accept reject : MachineDescription)
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  forall w : Word Bool, forall stage : Nat,
    P.transform (PairedRecognizerDovetailStageInputCode w stage) =
      some
        (MachineDescription.encodeBoolWord
          (MachineDescription.DovetailLayout.outputWordFromOption
            (MachineDescription.boundedDovetailOutput
              accept reject w stage)))

def PairedRecognizerDovetailTotalStageAttemptControllerResultRealizes
    (accept reject : MachineDescription)
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  forall w : Word Bool, forall stage : Nat,
    exists result : Word Bool,
      P.transform (PairedRecognizerDovetailStageInputCode w stage) =
        some (MachineDescription.encodeBoolWord result) ∧
      PairedRecognizerDovetailControllerRawOutput result =
        MachineDescription.boundedDovetailOutput accept reject w stage

theorem pairedRecognizerDovetailInitialLayoutCode_encode
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    (PairedRecognizerDovetailInitialLayoutCode accept reject).transform
        (PairedRecognizerDovetailStageInputCode w stage) =
      some
        (MachineDescription.DovetailLayout.encode
          (MachineDescription.DovetailLayout.initial
            accept reject w stage)) :=
  MachineDescription.DovetailLayout.initialCodePrimitive_stageInputCode
    accept reject w stage

theorem pairedRecognizerDovetailInitialLayoutCode_transform_eq_some_iff
    (accept reject : MachineDescription)
    (code out : Word MachineCodeSymbol) :
    (PairedRecognizerDovetailInitialLayoutCode accept reject).transform
        code = some out <->
      exists w : Word Bool,
      exists stage : Nat,
        code = PairedRecognizerDovetailStageInputCode w stage ∧
          out =
            MachineDescription.DovetailLayout.encode
              (MachineDescription.DovetailLayout.initial
                accept reject w stage) := by
  constructor
  · intro h
    unfold PairedRecognizerDovetailInitialLayoutCode at h
    unfold MachineDescription.DovetailLayout.initialCodePrimitive at h
    unfold MachineDescription.DovetailLayout.initialCode at h
    cases hdecode :
        MachineDescription.DovetailLayout.decodeStageInputComplete code with
    | none =>
        simp [hdecode] at h
    | some parsed =>
        cases parsed with
        | mk w stage =>
            simp [hdecode] at h
            cases h
            exact
              ⟨w, stage,
                MachineDescription.DovetailLayout.decodeStageInputComplete_eq_some_stageInputCode
                  hdecode,
                rfl⟩
  · intro h
    rcases h with ⟨w, stage, rfl, rfl⟩
    exact pairedRecognizerDovetailInitialLayoutCode_encode
      accept reject w stage

theorem pairedRecognizerDovetailInitialLayoutCode_realizes
    (accept reject : MachineDescription) :
    PairedRecognizerDovetailInitialLayoutCodeRealizes
      accept reject
      (PairedRecognizerDovetailInitialLayoutCode accept reject) :=
  pairedRecognizerDovetailInitialLayoutCode_encode accept reject

theorem pairedRecognizerDovetailLayoutCode_encode
    (accept reject : MachineDescription)
    (L : MachineDescription.DovetailLayout) :
    (PairedRecognizerDovetailLayoutCode accept reject).transform
        (MachineDescription.DovetailLayout.encode L) =
      some
        (MachineDescription.DovetailLayout.encode
          (MachineDescription.DovetailLayout.run
            accept reject L.stage L)) :=
  MachineDescription.DovetailLayout.runCodePrimitive_encode
    accept reject L

theorem pairedRecognizerDovetailLayoutCode_transform_eq_some_iff
    (accept reject : MachineDescription)
    (code out : Word MachineCodeSymbol) :
    (PairedRecognizerDovetailLayoutCode accept reject).transform code =
        some out <->
      exists L : MachineDescription.DovetailLayout,
        code = MachineDescription.DovetailLayout.encode L ∧
          out =
            MachineDescription.DovetailLayout.encode
              (MachineDescription.DovetailLayout.run
                accept reject L.stage L) := by
  constructor
  · intro h
    unfold PairedRecognizerDovetailLayoutCode at h
    unfold MachineDescription.DovetailLayout.runCodePrimitive at h
    unfold MachineDescription.DovetailLayout.runCode at h
    cases hdecode :
        MachineDescription.DovetailLayout.decodeComplete code with
    | none =>
        simp [hdecode] at h
    | some L =>
        simp [hdecode] at h
        cases h
        exact
          ⟨L,
            MachineDescription.DovetailLayout.decodeComplete_eq_some_encode
              hdecode,
            rfl⟩
  · intro h
    rcases h with ⟨L, rfl, rfl⟩
    exact pairedRecognizerDovetailLayoutCode_encode accept reject L

theorem pairedRecognizerDovetailLayoutCode_realizes
    (accept reject : MachineDescription) :
    PairedRecognizerDovetailLayoutCodeRealizes
      accept reject
      (PairedRecognizerDovetailLayoutCode accept reject) :=
  pairedRecognizerDovetailLayoutCode_encode accept reject

theorem pairedRecognizerDovetailOutputCode_encode
    {L : MachineDescription.DovetailLayout} {out : Word Bool}
    (h :
      MachineDescription.DovetailLayout.outputFromHits L = some out) :
    PairedRecognizerDovetailOutputCode.transform
        (MachineDescription.DovetailLayout.encode L) =
      some (MachineDescription.encodeBoolWord out) :=
  MachineDescription.DovetailLayout.outputCode_encode_of_outputFromHits_eq_some
    h

theorem pairedRecognizerDovetailOutputCode_realizes :
    PairedRecognizerDovetailOutputCodeRealizes
      PairedRecognizerDovetailOutputCode :=
  fun _L _out => pairedRecognizerDovetailOutputCode_encode

theorem pairedRecognizerDovetailTotalOutputCode_encode
    (L : MachineDescription.DovetailLayout) :
    PairedRecognizerDovetailTotalOutputCode.transform
        (MachineDescription.DovetailLayout.encode L) =
      some
        (MachineDescription.encodeBoolWord
          (MachineDescription.DovetailLayout.outputWordFromHits L)) := by
  simp [PairedRecognizerDovetailTotalOutputCode,
    MachineDescription.DovetailLayout.decodeComplete_encode]

theorem pairedRecognizerDovetailTotalOutputCode_transform_eq_some_iff
    (code out : Word MachineCodeSymbol) :
    PairedRecognizerDovetailTotalOutputCode.transform code = some out <->
      exists L : MachineDescription.DovetailLayout,
        code = MachineDescription.DovetailLayout.encode L ∧
          out =
            MachineDescription.encodeBoolWord
              (MachineDescription.DovetailLayout.outputWordFromHits L) := by
  constructor
  · intro h
    unfold PairedRecognizerDovetailTotalOutputCode at h
    cases hdecode :
        MachineDescription.DovetailLayout.decodeComplete code with
    | none =>
        simp [hdecode] at h
    | some L =>
        simp [hdecode] at h
        cases h
        exact
          ⟨L,
            MachineDescription.DovetailLayout.decodeComplete_eq_some_encode
              hdecode,
            rfl⟩
  · intro h
    rcases h with ⟨L, rfl, rfl⟩
    exact pairedRecognizerDovetailTotalOutputCode_encode L

theorem pairedRecognizerDovetailTotalOutputCode_realizes :
    PairedRecognizerDovetailTotalOutputCodeRealizes
      PairedRecognizerDovetailTotalOutputCode :=
  pairedRecognizerDovetailTotalOutputCode_encode

theorem pairedRecognizerDovetailControllerStageInputCode_encode
    (C : MachineDescription.DovetailControllerLayout) :
    PairedRecognizerDovetailControllerStageInputCodePrimitive.transform
        (MachineDescription.DovetailControllerLayout.encode C) =
      some (PairedRecognizerDovetailControllerStageInputCode C) := by
  simp [PairedRecognizerDovetailControllerStageInputCodePrimitive,
    MachineDescription.DovetailControllerLayout.decodeComplete_encode]

theorem pairedRecognizerDovetailControllerStageInputCode_transform_eq_some_iff
    (code out : Word MachineCodeSymbol) :
    PairedRecognizerDovetailControllerStageInputCodePrimitive.transform code =
        some out <->
      exists C : MachineDescription.DovetailControllerLayout,
        code = MachineDescription.DovetailControllerLayout.encode C ∧
          out = PairedRecognizerDovetailControllerStageInputCode C := by
  constructor
  · intro h
    unfold PairedRecognizerDovetailControllerStageInputCodePrimitive at h
    cases hdecode :
        MachineDescription.DovetailControllerLayout.decodeComplete code with
    | none =>
        simp [hdecode] at h
    | some C =>
        simp [hdecode] at h
        cases h
        exact
          ⟨C,
            MachineDescription.DovetailControllerLayout.decodeComplete_eq_some_encode
              hdecode,
            rfl⟩
  · intro h
    rcases h with ⟨C, rfl, rfl⟩
    exact pairedRecognizerDovetailControllerStageInputCode_encode C

theorem pairedRecognizerDovetailControllerStageInputCode_realizes :
    PairedRecognizerDovetailControllerStageInputCodeRealizes
      PairedRecognizerDovetailControllerStageInputCodePrimitive :=
  pairedRecognizerDovetailControllerStageInputCode_encode

theorem pairedRecognizerDovetailStageAttemptCode_encode
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    (PairedRecognizerDovetailStageAttemptCode accept reject).transform
        (PairedRecognizerDovetailStageInputCode w stage) =
      Option.map MachineDescription.encodeBoolWord
        (MachineDescription.boundedDovetailOutput
          accept reject w stage) :=
  MachineDescription.DovetailLayout.stageAttemptCodePrimitive_stageInputCode
    accept reject w stage

theorem pairedRecognizerDovetailStageAttemptCode_transform_eq_some_iff
    (accept reject : MachineDescription)
    (code out : Word MachineCodeSymbol) :
    (PairedRecognizerDovetailStageAttemptCode accept reject).transform code =
        some out <->
      exists w : Word Bool,
      exists stage : Nat,
      exists result : Word Bool,
        code = PairedRecognizerDovetailStageInputCode w stage ∧
          MachineDescription.boundedDovetailOutput accept reject w stage =
            some result ∧
          out = MachineDescription.encodeBoolWord result := by
  constructor
  · intro h
    unfold PairedRecognizerDovetailStageAttemptCode at h
    unfold MachineDescription.DovetailLayout.stageAttemptCodePrimitive at h
    unfold MachineDescription.DovetailLayout.stageAttemptCode at h
    cases hdecode :
        MachineDescription.DovetailLayout.decodeStageInputComplete code with
    | none =>
        simp [hdecode] at h
    | some parsed =>
        cases parsed with
        | mk w stage =>
            simp [hdecode] at h
            rw [MachineDescription.DovetailLayout.outputFromHits_run_initial_eq_boundedDovetailOutput]
              at h
            cases hbounded :
                MachineDescription.boundedDovetailOutput
                  accept reject w stage with
            | none =>
                simp [hbounded] at h
            | some result =>
                simp [hbounded] at h
                cases h
                exact
                  ⟨w, stage, result,
                    MachineDescription.DovetailLayout.decodeStageInputComplete_eq_some_stageInputCode
                      hdecode,
                    hbounded,
                    rfl⟩
  · intro h
    rcases h with ⟨w, stage, result, rfl, hbounded, rfl⟩
    rw [pairedRecognizerDovetailStageAttemptCode_encode, hbounded]
    rfl

theorem pairedRecognizerDovetailStageAttemptCode_realizes
    (accept reject : MachineDescription) :
    PairedRecognizerDovetailStageAttemptCodeRealizes
      accept reject
      (PairedRecognizerDovetailStageAttemptCode accept reject) :=
  pairedRecognizerDovetailStageAttemptCode_encode accept reject

theorem pairedRecognizerDovetailTotalStageAttemptCode_encode
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    (PairedRecognizerDovetailTotalStageAttemptCode accept reject).transform
        (PairedRecognizerDovetailStageInputCode w stage) =
      some
        (MachineDescription.encodeBoolWord
          (MachineDescription.DovetailLayout.outputWordFromOption
            (MachineDescription.boundedDovetailOutput
              accept reject w stage))) :=
  MachineDescription.DovetailLayout.totalStageAttemptCodePrimitive_stageInputCode
    accept reject w stage

theorem pairedRecognizerDovetailTotalStageAttemptCode_transform_eq_some_iff
    (accept reject : MachineDescription)
    (code out : Word MachineCodeSymbol) :
    (PairedRecognizerDovetailTotalStageAttemptCode accept reject).transform
        code = some out <->
      exists w : Word Bool,
      exists stage : Nat,
        code = PairedRecognizerDovetailStageInputCode w stage ∧
          out =
            MachineDescription.encodeBoolWord
              (MachineDescription.DovetailLayout.outputWordFromOption
                (MachineDescription.boundedDovetailOutput
                  accept reject w stage)) := by
  constructor
  · intro h
    unfold PairedRecognizerDovetailTotalStageAttemptCode at h
    unfold MachineDescription.DovetailLayout.totalStageAttemptCodePrimitive at h
    unfold MachineDescription.DovetailLayout.totalStageAttemptCode at h
    cases hdecode :
        MachineDescription.DovetailLayout.decodeStageInputComplete code with
    | none =>
        simp [hdecode] at h
    | some parsed =>
        cases parsed with
        | mk w stage =>
            simp [hdecode] at h
            cases h
            exact
              ⟨w, stage,
                MachineDescription.DovetailLayout.decodeStageInputComplete_eq_some_stageInputCode
                  hdecode,
                by
                  simp [MachineDescription.DovetailLayout.outputWordFromHits,
                    MachineDescription.DovetailLayout.outputFromHits_run_initial_eq_boundedDovetailOutput]⟩
  · intro h
    rcases h with ⟨w, stage, rfl, rfl⟩
    exact pairedRecognizerDovetailTotalStageAttemptCode_encode
      accept reject w stage

theorem pairedRecognizerDovetailTotalStageAttemptCode_realizes
    (accept reject : MachineDescription) :
    PairedRecognizerDovetailTotalStageAttemptCodeRealizes
      accept reject
      (PairedRecognizerDovetailTotalStageAttemptCode accept reject) :=
  pairedRecognizerDovetailTotalStageAttemptCode_encode accept reject

theorem pairedRecognizerDovetailTotalStageAttemptSourceCode_transform_eq
    (accept reject : MachineDescription)
    (tokens : Word MachineCodeSymbol) :
    (PairedRecognizerDovetailTotalStageAttemptSourceCode
        accept reject).transform tokens =
      (PairedRecognizerDovetailTotalStageAttemptCode
        accept reject).transform tokens := by
  unfold PairedRecognizerDovetailTotalStageAttemptSourceCode
  unfold PairedRecognizerDovetailInitialLayoutCode
  unfold PairedRecognizerDovetailLayoutCode
  unfold PairedRecognizerDovetailTotalOutputCode
  unfold PairedRecognizerDovetailTotalStageAttemptCode
  unfold MachineDescription.TapeCodePrimitive.compose
  unfold MachineDescription.DovetailLayout.initialCodePrimitive
  unfold MachineDescription.DovetailLayout.runCodePrimitive
  unfold MachineDescription.DovetailLayout.totalStageAttemptCodePrimitive
  unfold MachineDescription.DovetailLayout.initialCode
  unfold MachineDescription.DovetailLayout.runCode
  unfold MachineDescription.DovetailLayout.totalStageAttemptCode
  cases h : MachineDescription.DovetailLayout.decodeStageInputComplete
      tokens with
  | none =>
      simp [h]
  | some parsed =>
      rcases parsed with ⟨w, stage⟩
      simp [h, MachineDescription.DovetailLayout.decodeComplete_encode,
        MachineDescription.DovetailLayout.initial]

theorem pairedRecognizerDovetailTotalStageAttemptCodeRealizes_controllerResult
    {accept reject : MachineDescription}
    {P : MachineDescription.TapeCodePrimitive}
    (hP :
      PairedRecognizerDovetailTotalStageAttemptCodeRealizes
        accept reject P) :
    PairedRecognizerDovetailTotalStageAttemptControllerResultRealizes
      accept reject P := by
  intro w stage
  refine
    ⟨MachineDescription.DovetailLayout.outputWordFromOption
        (MachineDescription.boundedDovetailOutput
          accept reject w stage), ?_, ?_⟩
  · exact hP w stage
  · exact
      MachineDescription.DovetailControllerLayout.rawOutput_outputWordFromOption_boundedDovetailOutput
        accept reject w stage

theorem pairedRecognizerDovetailTotalStageAttemptCode_controllerResultRealizes
    (accept reject : MachineDescription) :
    PairedRecognizerDovetailTotalStageAttemptControllerResultRealizes
      accept reject
      (PairedRecognizerDovetailTotalStageAttemptCode accept reject) :=
  pairedRecognizerDovetailTotalStageAttemptCodeRealizes_controllerResult
    (pairedRecognizerDovetailTotalStageAttemptCode_realizes accept reject)

theorem pairedRecognizerDovetailControllerRawOutputCode_realizes :
    PairedRecognizerDovetailControllerRawOutputCodeRealizes
      PairedRecognizerDovetailControllerRawOutputCode := by
  intro result
  exact
    MachineDescription.DovetailControllerLayout.rawOutputCodePrimitive_encodeBoolWord
      result

theorem pairedRecognizerDovetailControllerRawOutputCode_eq_some_encodeBoolWord_singleton_iff
    {tokens : Word MachineCodeSymbol} {b : Bool} :
      PairedRecognizerDovetailControllerRawOutputCode.transform tokens =
        some (MachineDescription.encodeBoolWord [b]) <->
      MachineDescription.DovetailControllerLayout.decodeAttemptResultCode
        tokens = some [b] :=
  MachineDescription.DovetailControllerLayout.rawOutputCode_eq_some_encodeBoolWord_singleton_iff

theorem pairedRecognizerDovetailControllerRawOutputCode_transform_eq_some_iff
    (code outCode : Word MachineCodeSymbol) :
    PairedRecognizerDovetailControllerRawOutputCode.transform code =
        some outCode <->
      exists result out : Word Bool,
        code = MachineDescription.encodeBoolWord result ∧
          PairedRecognizerDovetailControllerRawOutput result = some out ∧
          outCode = MachineDescription.encodeBoolWord out := by
  constructor
  · intro h
    rcases
        MachineDescription.DovetailControllerLayout.rawOutputCode_eq_some_iff.mp
          h with
      ⟨result, out, hdecode, hraw, hout⟩
    exact
      ⟨result, out,
        MachineDescription.DovetailControllerLayout.decodeAttemptResultCode_eq_some_encodeBoolWord
          hdecode,
        hraw,
        hout⟩
  · intro h
    rcases h with ⟨result, out, rfl, hraw, rfl⟩
    exact
      MachineDescription.DovetailControllerLayout.rawOutputCode_eq_some_iff.mpr
        ⟨result, out,
          MachineDescription.DovetailControllerLayout.decodeAttemptResultCode_encodeBoolWord
            result,
          hraw,
          rfl⟩

theorem pairedRecognizerDovetailControllerRawOutputCode_eq_some_self
    {code out : Word MachineCodeSymbol}
    (h :
      PairedRecognizerDovetailControllerRawOutputCode.transform code =
        some out) :
    out = code := by
  rcases MachineDescription.DovetailControllerLayout.rawOutputCode_eq_some_iff.mp
      h with
    ⟨result, raw, hdecode, hraw, hout⟩
  cases result with
  | nil =>
      simp [MachineDescription.DovetailControllerLayout.rawOutput?] at hraw
  | cons b tail =>
      cases tail with
      | nil =>
          simp [MachineDescription.DovetailControllerLayout.rawOutput?] at hraw
          cases hraw
          have hcode : code = MachineDescription.encodeBoolWord [b] := by
            apply
              MachineDescription.DovetailControllerLayout.decodeAttemptResultCode_eq_some_encodeBoolWord
            exact hdecode
          rw [hout, hcode]
      | cons c rest =>
          simp [MachineDescription.DovetailControllerLayout.rawOutput?] at hraw

theorem pairedRecognizerDovetailControllerContinueCode_realizes
    (accept reject : MachineDescription) :
    PairedRecognizerDovetailControllerContinueCodeRealizes
      accept reject
      (PairedRecognizerDovetailControllerContinueCode accept reject) := by
  intro C
  exact
    MachineDescription.DovetailControllerLayout.continueCodePrimitive_encode
      accept reject C

theorem pairedRecognizerDovetailControllerEmitCode_realizes
    (accept reject : MachineDescription) :
    PairedRecognizerDovetailControllerEmitCodeRealizes
      accept reject
      (PairedRecognizerDovetailControllerEmitCode accept reject) := by
  intro C
  exact
    MachineDescription.DovetailControllerLayout.emitCodePrimitive_encode
      accept reject C

theorem pairedRecognizerDovetailControllerContinueCode_encode_eq_some_iff
    {accept reject : MachineDescription}
    {C : MachineDescription.DovetailControllerLayout}
    {out : Word MachineCodeSymbol} :
    (PairedRecognizerDovetailControllerContinueCode accept reject).transform
        (MachineDescription.DovetailControllerLayout.encode C) =
        some out <->
      MachineDescription.boundedDovetailOutput
          accept reject C.input C.stage = none ∧
        out =
          MachineDescription.DovetailControllerLayout.encode
            (MachineDescription.DovetailControllerLayout.nextStage C) :=
  MachineDescription.DovetailControllerLayout.continueCodePrimitive_encode_eq_some_iff

theorem pairedRecognizerDovetailControllerEmitCode_encode_eq_some_iff
    {accept reject : MachineDescription}
    {C : MachineDescription.DovetailControllerLayout}
    {outCode : Word MachineCodeSymbol} :
    (PairedRecognizerDovetailControllerEmitCode accept reject).transform
        (MachineDescription.DovetailControllerLayout.encode C) =
        some outCode <->
      exists out : Word Bool,
        MachineDescription.boundedDovetailOutput
          accept reject C.input C.stage = some out ∧
          outCode = MachineDescription.encodeBoolWord out :=
  MachineDescription.DovetailControllerLayout.emitCodePrimitive_encode_eq_some_iff

theorem pairedRecognizerDovetailControllerEmitCode_encode_eq_encodeBoolWord_iff
    {accept reject : MachineDescription}
    {C : MachineDescription.DovetailControllerLayout}
    {out : Word Bool} :
    (PairedRecognizerDovetailControllerEmitCode accept reject).transform
        (MachineDescription.DovetailControllerLayout.encode C) =
        some (MachineDescription.encodeBoolWord out) <->
      MachineDescription.boundedDovetailOutput
        accept reject C.input C.stage = some out :=
  MachineDescription.DovetailControllerLayout.emitCodePrimitive_encode_eq_encodeBoolWord_iff

theorem pairedRecognizerDovetailControllerContinueEmitCode_exclusive
    {accept reject : MachineDescription}
    {C : MachineDescription.DovetailControllerLayout}
    {next out : Word MachineCodeSymbol}
    (hcontinue :
      (PairedRecognizerDovetailControllerContinueCode accept reject).transform
        (MachineDescription.DovetailControllerLayout.encode C) =
          some next)
    (hemit :
      (PairedRecognizerDovetailControllerEmitCode accept reject).transform
        (MachineDescription.DovetailControllerLayout.encode C) =
          some out) :
    False :=
  MachineDescription.DovetailControllerLayout.continueCode_emitCode_encode_exclusive
    hcontinue hemit

theorem pairedRecognizerDovetailControllerContinueEmitCode_branch
    (accept reject : MachineDescription)
    (C : MachineDescription.DovetailControllerLayout) :
    ((PairedRecognizerDovetailControllerContinueCode accept reject).transform
        (MachineDescription.DovetailControllerLayout.encode C) =
        some
          (MachineDescription.DovetailControllerLayout.encode
            (MachineDescription.DovetailControllerLayout.nextStage C)) ∧
      (PairedRecognizerDovetailControllerEmitCode accept reject).transform
        (MachineDescription.DovetailControllerLayout.encode C) = none) ∨
      ((PairedRecognizerDovetailControllerContinueCode
          accept reject).transform
        (MachineDescription.DovetailControllerLayout.encode C) = none ∧
        exists out : Word Bool,
          MachineDescription.boundedDovetailOutput
            accept reject C.input C.stage = some out ∧
            (PairedRecognizerDovetailControllerEmitCode
              accept reject).transform
              (MachineDescription.DovetailControllerLayout.encode C) =
                some (MachineDescription.encodeBoolWord out)) :=
  MachineDescription.DovetailControllerLayout.continue_emit_branch_encode
    accept reject C

theorem pairedRecognizerDovetailControllerResultEmitterCode_encode_eq_some_iff
    {C : MachineDescription.DovetailControllerLayout}
    {outCode : Word MachineCodeSymbol} :
    PairedRecognizerDovetailControllerResultEmitterCode.transform
        (MachineDescription.DovetailControllerLayout.encode C) =
        some outCode <->
      exists out : Word Bool,
        PairedRecognizerDovetailControllerRawOutput C.result = some out ∧
          outCode = MachineDescription.encodeBoolWord out :=
  MachineDescription.DovetailControllerLayout.emitResultCodePrimitive_encode_eq_some_iff

theorem pairedRecognizerDovetailControllerResultEmitterCode_encode_eq_encodeBoolWord_iff
    {C : MachineDescription.DovetailControllerLayout}
    {out : Word Bool} :
    PairedRecognizerDovetailControllerResultEmitterCode.transform
        (MachineDescription.DovetailControllerLayout.encode C) =
        some (MachineDescription.encodeBoolWord out) <->
      PairedRecognizerDovetailControllerRawOutput C.result = some out :=
  MachineDescription.DovetailControllerLayout.emitResultCodePrimitive_encode_eq_encodeBoolWord_iff

theorem pairedRecognizerDovetailControllerResultContinueCode_encode_eq_some_iff
    {C : MachineDescription.DovetailControllerLayout}
    {outCode : Word MachineCodeSymbol} :
    PairedRecognizerDovetailControllerResultContinueCode.transform
        (MachineDescription.DovetailControllerLayout.encode C) =
        some outCode <->
      PairedRecognizerDovetailControllerRawOutput C.result = none ∧
        outCode =
          MachineDescription.DovetailControllerLayout.encode
            (MachineDescription.DovetailControllerLayout.nextStage C) :=
  MachineDescription.DovetailControllerLayout.continueResultCodePrimitive_encode_eq_some_iff

theorem pairedRecognizerDovetailControllerResultContinueCode_encode_nextStage_iff
    {C : MachineDescription.DovetailControllerLayout} :
    PairedRecognizerDovetailControllerResultContinueCode.transform
        (MachineDescription.DovetailControllerLayout.encode C) =
        some
          (MachineDescription.DovetailControllerLayout.encode
            (MachineDescription.DovetailControllerLayout.nextStage C)) <->
      PairedRecognizerDovetailControllerRawOutput C.result = none := by
  constructor
  · intro h
    exact
      (pairedRecognizerDovetailControllerResultContinueCode_encode_eq_some_iff.mp
        h).left
  · intro h
    exact
      pairedRecognizerDovetailControllerResultContinueCode_encode_eq_some_iff.mpr
        ⟨h, rfl⟩

theorem pairedRecognizerDovetailControllerResultContinueCode_transform_eq_some_iff
    (code out : Word MachineCodeSymbol) :
    PairedRecognizerDovetailControllerResultContinueCode.transform code =
        some out <->
      exists C : MachineDescription.DovetailControllerLayout,
        code = MachineDescription.DovetailControllerLayout.encode C ∧
          PairedRecognizerDovetailControllerRawOutput C.result = none ∧
            out =
              MachineDescription.DovetailControllerLayout.encode
                (MachineDescription.DovetailControllerLayout.nextStage C) := by
  constructor
  · intro h
    unfold PairedRecognizerDovetailControllerResultContinueCode at h
    unfold MachineDescription.DovetailControllerLayout.continueResultCodePrimitive at h
    unfold MachineDescription.DovetailControllerLayout.continueResultCode at h
    cases hdecode :
        MachineDescription.DovetailControllerLayout.decodeComplete code with
    | none =>
        simp [hdecode] at h
    | some C =>
        cases hraw :
            MachineDescription.DovetailControllerLayout.rawOutput? C.result with
        | none =>
            simp [hdecode, hraw] at h
            cases h
            exact
              ⟨C,
                MachineDescription.DovetailControllerLayout.decodeComplete_eq_some_encode
                  hdecode,
                by
                  simpa [PairedRecognizerDovetailControllerRawOutput] using hraw,
                rfl⟩
        | some out =>
            simp [hdecode, hraw] at h
  · intro h
    rcases h with ⟨C, rfl, hraw, rfl⟩
    exact
      pairedRecognizerDovetailControllerResultContinueCode_encode_eq_some_iff.mpr
        ⟨hraw, rfl⟩

theorem pairedRecognizerDovetailTotalThenRawOutputCode_encode
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    (PairedRecognizerDovetailTotalThenRawOutputCode
      accept reject).transform
        (PairedRecognizerDovetailStageInputCode w stage) =
      Option.map MachineDescription.encodeBoolWord
        (MachineDescription.boundedDovetailOutput
          accept reject w stage) :=
  MachineDescription.DovetailControllerLayout.rawOutputCode_after_totalStageAttemptCode_stageInputCode
    accept reject w stage

theorem pairedRecognizerDovetailTotalThenRawOutputCode_eq_stageAttemptCode
    (accept reject : MachineDescription)
    (tokens : Word MachineCodeSymbol) :
    (PairedRecognizerDovetailTotalThenRawOutputCode
      accept reject).transform tokens =
      (PairedRecognizerDovetailStageAttemptCode
        accept reject).transform tokens :=
  MachineDescription.DovetailControllerLayout.rawOutputCode_after_totalStageAttemptCode
    accept reject tokens

theorem pairedRecognizerDovetailTotalThenRawOutputCode_realizes
    (accept reject : MachineDescription) :
    PairedRecognizerDovetailStageAttemptCodeRealizes
      accept reject
      (PairedRecognizerDovetailTotalThenRawOutputCode accept reject) :=
  pairedRecognizerDovetailTotalThenRawOutputCode_encode accept reject

theorem pairedRecognizerDovetailLayout_initial_output
    (accept reject : MachineDescription)
    (w : Word Bool) (limit : Nat) :
    MachineDescription.DovetailLayout.outputFromHits
        (MachineDescription.DovetailLayout.run accept reject limit
          (MachineDescription.DovetailLayout.initial
            accept reject w limit)) =
      MachineDescription.boundedDovetailOutput accept reject w limit :=
  MachineDescription.DovetailLayout.outputFromHits_run_initial_eq_boundedDovetailOutput
    accept reject w limit

end Computability
end FoC
