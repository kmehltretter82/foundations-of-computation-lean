import FoC.Computability.Compiler.Core.BoundedTrace

set_option doc.verso true

/-!
# Paired-recognizer dovetail code primitives
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

def PairedRecognizerDovetailLayoutCode
    (accept reject : MachineDescription) :
    TapeCodePrimitive :=
  DovetailLayout.runCodePrimitive accept reject

def PairedRecognizerDovetailStageInputCode
    (w : Word Bool) (stage : Nat) : Word MachineCodeSymbol :=
  DovetailLayout.stageInputCode w stage

def PairedRecognizerDovetailControllerStageAttemptFuelInputCode
    (w : Word Bool) (limit fuel : Nat) :
    Word MachineCodeSymbol :=
  DovetailLayout.stageInputCodeAppend w limit
    (encodeNatAppend fuel [])

def PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout
    (attempt : MachineDescription)
    (w : Word Bool) (limit fuel : Nat) : SimulatorLayout :=
  SimulatorLayout.initial attempt
    (encodeCodeWordAsInput
      (PairedRecognizerDovetailStageInputCode w limit))
    fuel

def PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCode
    (attempt : MachineDescription)
    (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match DovetailLayout.decodeStageInput tokens with
  | none => none
  | some ((w, limit), suffix) =>
      match decodeNat suffix with
      | none => none
      | some (fuel, []) =>
          some
            (SimulatorLayout.encode
              (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout
                attempt w limit fuel))
      | some (_, _ :: _) => none

def PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodePrimitive
    (attempt : MachineDescription) : TapeCodePrimitive where
  transform :=
    PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCode attempt

def PairedRecognizerDovetailControllerStageAttemptFuelOutputCode
    (attempt : MachineDescription)
    (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match SimulatorLayout.decodeComplete tokens with
  | none => none
  | some L =>
      if L.config.state = attempt.halt then
        decodeCodeWordAsInput (Tape.normalizedOutput L.config.tape)
      else
        none

def PairedRecognizerDovetailControllerStageAttemptFuelOutputCodePrimitive
    (attempt : MachineDescription) : TapeCodePrimitive where
  transform :=
    PairedRecognizerDovetailControllerStageAttemptFuelOutputCode attempt

def PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerCode
    (attempt : MachineDescription) : TapeCodePrimitive :=
  TapeCodePrimitive.compose
    (TapeCodePrimitive.compose
      (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodePrimitive
        attempt)
      (FixedDescriptionBoundedSimulatorCode attempt))
    (PairedRecognizerDovetailControllerStageAttemptFuelOutputCodePrimitive
      attempt)

theorem pairedRecognizerDovetailControllerStageAttemptFuelInputCode_decodeStageInput
    (w : Word Bool) (limit fuel : Nat) :
    DovetailLayout.decodeStageInput
        (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
          w limit fuel) =
      some ((w, limit), encodeNatAppend fuel []) := by
  exact DovetailLayout.decodeStageInput_stageInputCodeAppend
    w limit (encodeNatAppend fuel [])

theorem pairedRecognizerDovetailControllerStageAttemptFuelSimulatorCode_encode
    (attempt : MachineDescription)
    (w : Word Bool) (limit fuel : Nat) :
    PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCode attempt
        (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
          w limit fuel) =
      some
        (SimulatorLayout.encode
          (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout
            attempt w limit fuel)) := by
  simp [PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCode,
    pairedRecognizerDovetailControllerStageAttemptFuelInputCode_decodeStageInput,
    decodeNat_encodeNatAppend]

theorem pairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodePrimitive_encode
    (attempt : MachineDescription)
    (w : Word Bool) (limit fuel : Nat) :
    (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodePrimitive
        attempt).transform
        (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
          w limit fuel) =
      some
        (SimulatorLayout.encode
          (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout
            attempt w limit fuel)) :=
  pairedRecognizerDovetailControllerStageAttemptFuelSimulatorCode_encode
    attempt w limit fuel

theorem pairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout_haltsWithOutputIn_iff
    (attempt : MachineDescription)
    (w : Word Bool) (limit fuel : Nat) (out : Word Bool) :
    let L :=
      PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout
        attempt w limit fuel
    ((SimulatorLayout.run attempt L.stage L).config.state = attempt.halt ∧
        Tape.normalizedOutput
          (SimulatorLayout.run attempt L.stage L).config.tape = out) <->
      attempt.HaltsWithOutputIn fuel
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailStageInputCode w limit))
        out := by
  simp [PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout,
    MachineDescription.HaltsWithOutputIn, SimulatorLayout.initial,
    SimulatorLayout.run]

theorem pairedRecognizerDovetailControllerStageAttemptFuelOutputCode_run_iff
    (attempt : MachineDescription)
    (w : Word Bool) (limit fuel : Nat) (out : Word MachineCodeSymbol) :
    let L :=
      PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout
        attempt w limit fuel
    PairedRecognizerDovetailControllerStageAttemptFuelOutputCode attempt
        (SimulatorLayout.encode (SimulatorLayout.run attempt L.stage L)) =
        some out <->
      attempt.HaltsWithOutputIn fuel
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailStageInputCode w limit))
        (encodeCodeWordAsInput out) := by
  simp [PairedRecognizerDovetailControllerStageAttemptFuelOutputCode,
    PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout,
    MachineDescription.HaltsWithOutputIn, SimulatorLayout.initial,
    SimulatorLayout.run, SimulatorLayout.decodeComplete_encode,
    decodeCodeWordAsInput_eq_some_iff]

theorem pairedRecognizerDovetailControllerStageAttemptFuelOutputCodePrimitive_run_iff
    (attempt : MachineDescription)
    (w : Word Bool) (limit fuel : Nat) (out : Word MachineCodeSymbol) :
    let L :=
      PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout
        attempt w limit fuel
    (PairedRecognizerDovetailControllerStageAttemptFuelOutputCodePrimitive
        attempt).transform
        (SimulatorLayout.encode (SimulatorLayout.run attempt L.stage L)) =
        some out <->
      attempt.HaltsWithOutputIn fuel
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailStageInputCode w limit))
        (encodeCodeWordAsInput out) :=
  pairedRecognizerDovetailControllerStageAttemptFuelOutputCode_run_iff
    attempt w limit fuel out

theorem pairedRecognizerDovetailControllerStageAttemptFuelOutputCode_run_boolWord_iff
    (attempt : MachineDescription)
    (w result : Word Bool) (limit fuel : Nat) :
    let L :=
      PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout
        attempt w limit fuel
    PairedRecognizerDovetailControllerStageAttemptFuelOutputCode attempt
        (SimulatorLayout.encode (SimulatorLayout.run attempt L.stage L)) =
        some (encodeBoolWord result) <->
      attempt.HaltsWithOutputIn fuel
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailStageInputCode w limit))
        (encodeCodeWordAsInput (encodeBoolWord result)) :=
  pairedRecognizerDovetailControllerStageAttemptFuelOutputCode_run_iff
    attempt w limit fuel (encodeBoolWord result)

theorem pairedRecognizerDovetailControllerStageAttemptFuelOutputCodePrimitive_run_boolWord_iff
    (attempt : MachineDescription)
    (w result : Word Bool) (limit fuel : Nat) :
    let L :=
      PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout
        attempt w limit fuel
    (PairedRecognizerDovetailControllerStageAttemptFuelOutputCodePrimitive
        attempt).transform
        (SimulatorLayout.encode (SimulatorLayout.run attempt L.stage L)) =
        some (encodeBoolWord result) <->
      attempt.HaltsWithOutputIn fuel
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailStageInputCode w limit))
        (encodeCodeWordAsInput (encodeBoolWord result)) :=
  pairedRecognizerDovetailControllerStageAttemptFuelOutputCode_run_boolWord_iff
    attempt w result limit fuel

theorem pairedRecognizerDovetailControllerStageAttemptExactFuelRunnerCode_transform_boolWord_iff
    (attempt : MachineDescription)
    (w result : Word Bool) (limit fuel : Nat) :
    (PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerCode
        attempt).transform
        (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
          w limit fuel) =
        some (encodeBoolWord result) <->
      attempt.HaltsWithOutputIn fuel
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailStageInputCode w limit))
        (encodeCodeWordAsInput (encodeBoolWord result)) := by
  let L :=
    PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout
      attempt w limit fuel
  simpa [PairedRecognizerDovetailControllerStageAttemptExactFuelRunnerCode,
    TapeCodePrimitive.compose, L,
    pairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodePrimitive_encode,
    fixedDescriptionBoundedSimulatorCode_encode] using
    pairedRecognizerDovetailControllerStageAttemptFuelOutputCodePrimitive_run_boolWord_iff
      attempt w result limit fuel

theorem pairedRecognizerDovetailControllerStageAttemptFuelInputCode_injective
    {w1 w2 : Word Bool} {limit1 limit2 fuel1 fuel2 : Nat}
    (h :
      PairedRecognizerDovetailControllerStageAttemptFuelInputCode
          w1 limit1 fuel1 =
        PairedRecognizerDovetailControllerStageAttemptFuelInputCode
          w2 limit2 fuel2) :
    w1 = w2 ∧ limit1 = limit2 ∧ fuel1 = fuel2 := by
  have hdecode := congrArg DovetailLayout.decodeStageInput h
  rw [pairedRecognizerDovetailControllerStageAttemptFuelInputCode_decodeStageInput,
    pairedRecognizerDovetailControllerStageAttemptFuelInputCode_decodeStageInput] at hdecode
  have hdecoded :=
    Option.some.inj hdecode
  have hpair := Prod.ext_iff.mp hdecoded
  have hwlimit := Prod.ext_iff.mp hpair.left
  have hsuffix := hpair.right
  have hfuelDecode := congrArg decodeNat hsuffix
  simp [decodeNat_encodeNatAppend] at hfuelDecode
  exact ⟨hwlimit.left, hwlimit.right, hfuelDecode⟩

def PairedRecognizerDovetailInitialLayoutCode
    (accept reject : MachineDescription) :
    TapeCodePrimitive :=
  DovetailLayout.initialCodePrimitive accept reject

def PairedRecognizerDovetailOutputCode :
    TapeCodePrimitive :=
  DovetailLayout.outputCodePrimitive

def PairedRecognizerDovetailTotalOutputCode :
    TapeCodePrimitive where
  transform := fun tokens =>
    match DovetailLayout.decodeComplete tokens with
    | none => none
    | some L =>
        some
          (encodeBoolWord
            (DovetailLayout.outputWordFromHits L))

def PairedRecognizerDovetailStageAttemptCode
    (accept reject : MachineDescription) :
    TapeCodePrimitive :=
  DovetailLayout.stageAttemptCodePrimitive accept reject

def PairedRecognizerDovetailTotalStageAttemptCode
    (accept reject : MachineDescription) :
    TapeCodePrimitive :=
  DovetailLayout.totalStageAttemptCodePrimitive
    accept reject

def PairedRecognizerDovetailControllerLayoutCode
    (w : Word Bool) (stage : Nat) (result : Word Bool) :
    Word MachineCodeSymbol :=
  DovetailControllerLayout.encode
    { input := w, stage := stage, result := result }

def PairedRecognizerDovetailControllerInitialCode
    (w : Word Bool) : Word MachineCodeSymbol :=
  DovetailControllerLayout.encode
    (DovetailControllerLayout.initial w)

def PairedRecognizerDovetailControllerStageInputCode
    (C : DovetailControllerLayout) :
    Word MachineCodeSymbol :=
  DovetailControllerLayout.stageInputCode C

theorem pairedRecognizerDovetailControllerStageInputCode_injective_on_input_stage
    {C1 C2 : DovetailControllerLayout}
    (h :
      PairedRecognizerDovetailControllerStageInputCode C1 =
        PairedRecognizerDovetailControllerStageInputCode C2) :
    C1.input = C2.input ∧ C1.stage = C2.stage :=
  DovetailControllerLayout.stageInputCode_injective_on_input_stage h

def PairedRecognizerDovetailControllerStageInputCodePrimitive :
    TapeCodePrimitive where
  transform := fun tokens =>
    match DovetailControllerLayout.decodeComplete tokens with
    | none => none
    | some C => some (PairedRecognizerDovetailControllerStageInputCode C)

def PairedRecognizerDovetailControllerRawOutput
    (result : Word Bool) : Option (Word Bool) :=
  DovetailControllerLayout.rawOutput? result

theorem pairedRecognizerDovetailControllerRawOutput_none_iff
    (result : Word Bool) :
    PairedRecognizerDovetailControllerRawOutput result = none <->
      result = [] ∨
        exists b b' tail, result = b :: b' :: tail :=
  DovetailControllerLayout.rawOutput_none_iff result

def PairedRecognizerDovetailControllerRawOutputCode :
    TapeCodePrimitive :=
  DovetailControllerLayout.rawOutputCodePrimitive

def PairedRecognizerDovetailControllerResultEmitterCode :
    TapeCodePrimitive :=
  DovetailControllerLayout.emitResultCodePrimitive

def PairedRecognizerDovetailControllerResultContinueCode :
    TapeCodePrimitive :=
  DovetailControllerLayout.continueResultCodePrimitive

def PairedRecognizerDovetailControllerContinueCode
    (accept reject : MachineDescription) :
    TapeCodePrimitive :=
  DovetailControllerLayout.continueCodePrimitive
    accept reject

def PairedRecognizerDovetailControllerEmitCode
    (accept reject : MachineDescription) :
    TapeCodePrimitive :=
  DovetailControllerLayout.emitCodePrimitive
    accept reject

def PairedRecognizerDovetailTotalThenRawOutputCode
    (accept reject : MachineDescription) :
    TapeCodePrimitive :=
  TapeCodePrimitive.compose
    (PairedRecognizerDovetailTotalStageAttemptCode accept reject)
    PairedRecognizerDovetailControllerRawOutputCode

def PairedRecognizerDovetailTotalStageAttemptSourceCode
    (accept reject : MachineDescription) :
    TapeCodePrimitive :=
  TapeCodePrimitive.compose
    (TapeCodePrimitive.compose
      (PairedRecognizerDovetailInitialLayoutCode accept reject)
      (PairedRecognizerDovetailLayoutCode accept reject))
    PairedRecognizerDovetailTotalOutputCode

def PairedRecognizerDovetailControllerRawOutputCodeRealizes
    (P : TapeCodePrimitive) : Prop :=
  forall result : Word Bool,
    P.transform (encodeBoolWord result) =
      Option.map encodeBoolWord
        (PairedRecognizerDovetailControllerRawOutput result)

def PairedRecognizerDovetailControllerContinueCodeRealizes
    (accept reject : MachineDescription)
    (P : TapeCodePrimitive) : Prop :=
  forall C : DovetailControllerLayout,
    P.transform (DovetailControllerLayout.encode C) =
      if boundedDovetailOutput
          accept reject C.input C.stage = none then
        some
          (DovetailControllerLayout.encode
            (DovetailControllerLayout.nextStage C))
      else
        none

def PairedRecognizerDovetailControllerEmitCodeRealizes
    (accept reject : MachineDescription)
    (P : TapeCodePrimitive) : Prop :=
  forall C : DovetailControllerLayout,
    P.transform (DovetailControllerLayout.encode C) =
      Option.map encodeBoolWord
        (boundedDovetailOutput
          accept reject C.input C.stage)

def PairedRecognizerDovetailInitialLayoutCodeRealizes
    (accept reject : MachineDescription)
    (P : TapeCodePrimitive) : Prop :=
  forall w : Word Bool, forall stage : Nat,
    P.transform (PairedRecognizerDovetailStageInputCode w stage) =
      some
        (DovetailLayout.encode
          (DovetailLayout.initial
            accept reject w stage))

def PairedRecognizerDovetailLayoutCodeRealizes
    (accept reject : MachineDescription)
    (P : TapeCodePrimitive) : Prop :=
  forall L : DovetailLayout,
    P.transform (DovetailLayout.encode L) =
      some
        (DovetailLayout.encode
          (DovetailLayout.run
            accept reject L.stage L))

def PairedRecognizerDovetailOutputCodeRealizes
    (P : TapeCodePrimitive) : Prop :=
  forall L : DovetailLayout, forall out : Word Bool,
    DovetailLayout.outputFromHits L = some out ->
      P.transform (DovetailLayout.encode L) =
        some (encodeBoolWord out)

def PairedRecognizerDovetailTotalOutputCodeRealizes
    (P : TapeCodePrimitive) : Prop :=
  forall L : DovetailLayout,
    P.transform (DovetailLayout.encode L) =
      some
        (encodeBoolWord
          (DovetailLayout.outputWordFromHits L))

def PairedRecognizerDovetailControllerStageInputCodeRealizes
    (P : TapeCodePrimitive) : Prop :=
  forall C : DovetailControllerLayout,
    P.transform (DovetailControllerLayout.encode C) =
      some (PairedRecognizerDovetailControllerStageInputCode C)

def PairedRecognizerDovetailStageAttemptCodeRealizes
    (accept reject : MachineDescription)
    (P : TapeCodePrimitive) : Prop :=
  forall w : Word Bool, forall stage : Nat,
    P.transform (PairedRecognizerDovetailStageInputCode w stage) =
      Option.map encodeBoolWord
        (boundedDovetailOutput
          accept reject w stage)

def PairedRecognizerDovetailTotalStageAttemptCodeRealizes
    (accept reject : MachineDescription)
    (P : TapeCodePrimitive) : Prop :=
  forall w : Word Bool, forall stage : Nat,
    P.transform (PairedRecognizerDovetailStageInputCode w stage) =
      some
        (encodeBoolWord
          (DovetailLayout.outputWordFromOption
            (boundedDovetailOutput
              accept reject w stage)))

def PairedRecognizerDovetailTotalStageAttemptControllerResultRealizes
    (accept reject : MachineDescription)
    (P : TapeCodePrimitive) : Prop :=
  forall w : Word Bool, forall stage : Nat,
    exists result : Word Bool,
      P.transform (PairedRecognizerDovetailStageInputCode w stage) =
        some (encodeBoolWord result) ∧
      PairedRecognizerDovetailControllerRawOutput result =
        boundedDovetailOutput accept reject w stage

theorem pairedRecognizerDovetailInitialLayoutCode_encode
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    (PairedRecognizerDovetailInitialLayoutCode accept reject).transform
        (PairedRecognizerDovetailStageInputCode w stage) =
      some
        (DovetailLayout.encode
          (DovetailLayout.initial
            accept reject w stage)) :=
  DovetailLayout.initialCodePrimitive_stageInputCode
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
            DovetailLayout.encode
              (DovetailLayout.initial
                accept reject w stage) := by
  constructor
  · intro h
    unfold PairedRecognizerDovetailInitialLayoutCode at h
    unfold DovetailLayout.initialCodePrimitive at h
    unfold DovetailLayout.initialCode at h
    cases hdecode :
        DovetailLayout.decodeStageInputComplete code with
    | none =>
        simp [hdecode] at h
    | some parsed =>
        cases parsed with
        | mk w stage =>
            simp [hdecode] at h
            cases h
            exact
              ⟨w, stage,
                DovetailLayout.decodeStageInputComplete_eq_some_stageInputCode
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
    (L : DovetailLayout) :
    (PairedRecognizerDovetailLayoutCode accept reject).transform
        (DovetailLayout.encode L) =
      some
        (DovetailLayout.encode
          (DovetailLayout.run
            accept reject L.stage L)) :=
  DovetailLayout.runCodePrimitive_encode
    accept reject L

theorem pairedRecognizerDovetailLayoutCode_transform_eq_some_iff
    (accept reject : MachineDescription)
    (code out : Word MachineCodeSymbol) :
    (PairedRecognizerDovetailLayoutCode accept reject).transform code =
        some out <->
      exists L : DovetailLayout,
        code = DovetailLayout.encode L ∧
          out =
            DovetailLayout.encode
              (DovetailLayout.run
                accept reject L.stage L) := by
  constructor
  · intro h
    unfold PairedRecognizerDovetailLayoutCode at h
    unfold DovetailLayout.runCodePrimitive at h
    unfold DovetailLayout.runCode at h
    cases hdecode :
        DovetailLayout.decodeComplete code with
    | none =>
        simp [hdecode] at h
    | some L =>
        simp [hdecode] at h
        cases h
        exact
          ⟨L,
            DovetailLayout.decodeComplete_eq_some_encode
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
    {L : DovetailLayout} {out : Word Bool}
    (h :
      DovetailLayout.outputFromHits L = some out) :
    PairedRecognizerDovetailOutputCode.transform
        (DovetailLayout.encode L) =
      some (encodeBoolWord out) :=
  DovetailLayout.outputCode_encode_of_outputFromHits_eq_some
    h

theorem pairedRecognizerDovetailOutputCode_realizes :
    PairedRecognizerDovetailOutputCodeRealizes
      PairedRecognizerDovetailOutputCode :=
  fun _L _out => pairedRecognizerDovetailOutputCode_encode

theorem pairedRecognizerDovetailTotalOutputCode_encode
    (L : DovetailLayout) :
    PairedRecognizerDovetailTotalOutputCode.transform
        (DovetailLayout.encode L) =
      some
        (encodeBoolWord
          (DovetailLayout.outputWordFromHits L)) := by
  simp [PairedRecognizerDovetailTotalOutputCode,
    DovetailLayout.decodeComplete_encode]

theorem pairedRecognizerDovetailTotalOutputCode_transform_eq_some_iff
    (code out : Word MachineCodeSymbol) :
    PairedRecognizerDovetailTotalOutputCode.transform code = some out <->
      exists L : DovetailLayout,
        code = DovetailLayout.encode L ∧
          out =
            encodeBoolWord
              (DovetailLayout.outputWordFromHits L) := by
  constructor
  · intro h
    unfold PairedRecognizerDovetailTotalOutputCode at h
    cases hdecode :
        DovetailLayout.decodeComplete code with
    | none =>
        simp [hdecode] at h
    | some L =>
        simp [hdecode] at h
        cases h
        exact
          ⟨L,
            DovetailLayout.decodeComplete_eq_some_encode
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
    (C : DovetailControllerLayout) :
    PairedRecognizerDovetailControllerStageInputCodePrimitive.transform
        (DovetailControllerLayout.encode C) =
      some (PairedRecognizerDovetailControllerStageInputCode C) := by
  simp [PairedRecognizerDovetailControllerStageInputCodePrimitive,
    DovetailControllerLayout.decodeComplete_encode]

theorem pairedRecognizerDovetailControllerStageInputCode_transform_eq_some_iff
    (code out : Word MachineCodeSymbol) :
    PairedRecognizerDovetailControllerStageInputCodePrimitive.transform code =
        some out <->
      exists C : DovetailControllerLayout,
        code = DovetailControllerLayout.encode C ∧
          out = PairedRecognizerDovetailControllerStageInputCode C := by
  constructor
  · intro h
    unfold PairedRecognizerDovetailControllerStageInputCodePrimitive at h
    cases hdecode :
        DovetailControllerLayout.decodeComplete code with
    | none =>
        simp [hdecode] at h
    | some C =>
        simp [hdecode] at h
        cases h
        exact
          ⟨C,
            DovetailControllerLayout.decodeComplete_eq_some_encode
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
      Option.map encodeBoolWord
        (boundedDovetailOutput
          accept reject w stage) :=
  DovetailLayout.stageAttemptCodePrimitive_stageInputCode
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
          boundedDovetailOutput accept reject w stage =
            some result ∧
          out = encodeBoolWord result := by
  constructor
  · intro h
    unfold PairedRecognizerDovetailStageAttemptCode at h
    unfold DovetailLayout.stageAttemptCodePrimitive at h
    unfold DovetailLayout.stageAttemptCode at h
    cases hdecode :
        DovetailLayout.decodeStageInputComplete code with
    | none =>
        simp [hdecode] at h
    | some parsed =>
        cases parsed with
        | mk w stage =>
            simp [hdecode] at h
            rw [DovetailLayout.outputFromHits_run_initial_eq_boundedDovetailOutput]
              at h
            cases hbounded :
                boundedDovetailOutput
                  accept reject w stage with
            | none =>
                simp [hbounded] at h
            | some result =>
                simp [hbounded] at h
                cases h
                exact
                  ⟨w, stage, result,
                    DovetailLayout.decodeStageInputComplete_eq_some_stageInputCode
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
        (encodeBoolWord
          (DovetailLayout.outputWordFromOption
            (boundedDovetailOutput
              accept reject w stage))) :=
  DovetailLayout.totalStageAttemptCodePrimitive_stageInputCode
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
            encodeBoolWord
              (DovetailLayout.outputWordFromOption
                (boundedDovetailOutput
                  accept reject w stage)) := by
  constructor
  · intro h
    unfold PairedRecognizerDovetailTotalStageAttemptCode at h
    unfold DovetailLayout.totalStageAttemptCodePrimitive at h
    unfold DovetailLayout.totalStageAttemptCode at h
    cases hdecode :
        DovetailLayout.decodeStageInputComplete code with
    | none =>
        simp [hdecode] at h
    | some parsed =>
        cases parsed with
        | mk w stage =>
            simp [hdecode] at h
            cases h
            exact
              ⟨w, stage,
                DovetailLayout.decodeStageInputComplete_eq_some_stageInputCode
                  hdecode,
                by
                  simp [DovetailLayout.outputWordFromHits,
                    DovetailLayout.outputFromHits_run_initial_eq_boundedDovetailOutput]⟩
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
  unfold TapeCodePrimitive.compose
  unfold DovetailLayout.initialCodePrimitive
  unfold DovetailLayout.runCodePrimitive
  unfold DovetailLayout.totalStageAttemptCodePrimitive
  unfold DovetailLayout.initialCode
  unfold DovetailLayout.runCode
  unfold DovetailLayout.totalStageAttemptCode
  cases h : DovetailLayout.decodeStageInputComplete
      tokens with
  | none =>
      simp [h]
  | some parsed =>
      rcases parsed with ⟨w, stage⟩
      simp [h, DovetailLayout.decodeComplete_encode,
        DovetailLayout.initial]

theorem pairedRecognizerDovetailTotalStageAttemptCodeRealizes_controllerResult
    {accept reject : MachineDescription}
    {P : TapeCodePrimitive}
    (hP :
      PairedRecognizerDovetailTotalStageAttemptCodeRealizes
        accept reject P) :
    PairedRecognizerDovetailTotalStageAttemptControllerResultRealizes
      accept reject P := by
  intro w stage
  refine
    ⟨DovetailLayout.outputWordFromOption
        (boundedDovetailOutput
          accept reject w stage), ?_, ?_⟩
  · exact hP w stage
  · exact
      DovetailControllerLayout.rawOutput_outputWordFromOption_boundedDovetailOutput
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
    DovetailControllerLayout.rawOutputCodePrimitive_encodeBoolWord
      result

theorem pairedRecognizerDovetailControllerRawOutputCode_eq_some_encodeBoolWord_singleton_iff
    {tokens : Word MachineCodeSymbol} {b : Bool} :
      PairedRecognizerDovetailControllerRawOutputCode.transform tokens =
        some (encodeBoolWord [b]) <->
      DovetailControllerLayout.decodeAttemptResultCode
        tokens = some [b] :=
  DovetailControllerLayout.rawOutputCode_eq_some_encodeBoolWord_singleton_iff

theorem pairedRecognizerDovetailControllerRawOutputCode_transform_eq_some_iff
    (code outCode : Word MachineCodeSymbol) :
    PairedRecognizerDovetailControllerRawOutputCode.transform code =
        some outCode <->
      exists result out : Word Bool,
        code = encodeBoolWord result ∧
          PairedRecognizerDovetailControllerRawOutput result = some out ∧
          outCode = encodeBoolWord out := by
  constructor
  · intro h
    rcases
        DovetailControllerLayout.rawOutputCode_eq_some_iff.mp
          h with
      ⟨result, out, hdecode, hraw, hout⟩
    exact
      ⟨result, out,
        DovetailControllerLayout.decodeAttemptResultCode_eq_some_encodeBoolWord
          hdecode,
        hraw,
        hout⟩
  · intro h
    rcases h with ⟨result, out, rfl, hraw, rfl⟩
    exact
      DovetailControllerLayout.rawOutputCode_eq_some_iff.mpr
        ⟨result, out,
          DovetailControllerLayout.decodeAttemptResultCode_encodeBoolWord
            result,
          hraw,
          rfl⟩

theorem pairedRecognizerDovetailControllerRawOutputCode_eq_some_self
    {code out : Word MachineCodeSymbol}
    (h :
      PairedRecognizerDovetailControllerRawOutputCode.transform code =
        some out) :
    out = code := by
  rcases DovetailControllerLayout.rawOutputCode_eq_some_iff.mp
      h with
    ⟨result, raw, hdecode, hraw, hout⟩
  cases result with
  | nil =>
      simp [DovetailControllerLayout.rawOutput?] at hraw
  | cons b tail =>
      cases tail with
      | nil =>
          simp [DovetailControllerLayout.rawOutput?] at hraw
          cases hraw
          have hcode : code = encodeBoolWord [b] := by
            apply
              DovetailControllerLayout.decodeAttemptResultCode_eq_some_encodeBoolWord
            exact hdecode
          rw [hout, hcode]
      | cons c rest =>
          simp [DovetailControllerLayout.rawOutput?] at hraw

theorem pairedRecognizerDovetailControllerContinueCode_realizes
    (accept reject : MachineDescription) :
    PairedRecognizerDovetailControllerContinueCodeRealizes
      accept reject
      (PairedRecognizerDovetailControllerContinueCode accept reject) := by
  intro C
  exact
    DovetailControllerLayout.continueCodePrimitive_encode
      accept reject C

theorem pairedRecognizerDovetailControllerEmitCode_realizes
    (accept reject : MachineDescription) :
    PairedRecognizerDovetailControllerEmitCodeRealizes
      accept reject
      (PairedRecognizerDovetailControllerEmitCode accept reject) := by
  intro C
  exact
    DovetailControllerLayout.emitCodePrimitive_encode
      accept reject C

theorem pairedRecognizerDovetailControllerContinueCode_encode_eq_some_iff
    {accept reject : MachineDescription}
    {C : DovetailControllerLayout}
    {out : Word MachineCodeSymbol} :
    (PairedRecognizerDovetailControllerContinueCode accept reject).transform
        (DovetailControllerLayout.encode C) =
        some out <->
      boundedDovetailOutput
          accept reject C.input C.stage = none ∧
        out =
          DovetailControllerLayout.encode
            (DovetailControllerLayout.nextStage C) :=
  DovetailControllerLayout.continueCodePrimitive_encode_eq_some_iff

theorem pairedRecognizerDovetailControllerEmitCode_encode_eq_some_iff
    {accept reject : MachineDescription}
    {C : DovetailControllerLayout}
    {outCode : Word MachineCodeSymbol} :
    (PairedRecognizerDovetailControllerEmitCode accept reject).transform
        (DovetailControllerLayout.encode C) =
        some outCode <->
      exists out : Word Bool,
        boundedDovetailOutput
          accept reject C.input C.stage = some out ∧
          outCode = encodeBoolWord out :=
  DovetailControllerLayout.emitCodePrimitive_encode_eq_some_iff

theorem pairedRecognizerDovetailControllerEmitCode_encode_eq_encodeBoolWord_iff
    {accept reject : MachineDescription}
    {C : DovetailControllerLayout}
    {out : Word Bool} :
    (PairedRecognizerDovetailControllerEmitCode accept reject).transform
        (DovetailControllerLayout.encode C) =
        some (encodeBoolWord out) <->
      boundedDovetailOutput
        accept reject C.input C.stage = some out :=
  DovetailControllerLayout.emitCodePrimitive_encode_eq_encodeBoolWord_iff

theorem pairedRecognizerDovetailControllerContinueEmitCode_exclusive
    {accept reject : MachineDescription}
    {C : DovetailControllerLayout}
    {next out : Word MachineCodeSymbol}
    (hcontinue :
      (PairedRecognizerDovetailControllerContinueCode accept reject).transform
        (DovetailControllerLayout.encode C) =
          some next)
    (hemit :
      (PairedRecognizerDovetailControllerEmitCode accept reject).transform
        (DovetailControllerLayout.encode C) =
          some out) :
    False :=
  DovetailControllerLayout.continueCode_emitCode_encode_exclusive
    hcontinue hemit

theorem pairedRecognizerDovetailControllerContinueEmitCode_branch
    (accept reject : MachineDescription)
    (C : DovetailControllerLayout) :
    ((PairedRecognizerDovetailControllerContinueCode accept reject).transform
        (DovetailControllerLayout.encode C) =
        some
          (DovetailControllerLayout.encode
            (DovetailControllerLayout.nextStage C)) ∧
      (PairedRecognizerDovetailControllerEmitCode accept reject).transform
        (DovetailControllerLayout.encode C) = none) ∨
      ((PairedRecognizerDovetailControllerContinueCode
          accept reject).transform
        (DovetailControllerLayout.encode C) = none ∧
        exists out : Word Bool,
          boundedDovetailOutput
            accept reject C.input C.stage = some out ∧
            (PairedRecognizerDovetailControllerEmitCode
              accept reject).transform
              (DovetailControllerLayout.encode C) =
                some (encodeBoolWord out)) :=
  DovetailControllerLayout.continue_emit_branch_encode
    accept reject C

theorem pairedRecognizerDovetailControllerResultEmitterCode_encode_eq_some_iff
    {C : DovetailControllerLayout}
    {outCode : Word MachineCodeSymbol} :
    PairedRecognizerDovetailControllerResultEmitterCode.transform
        (DovetailControllerLayout.encode C) =
        some outCode <->
      exists out : Word Bool,
        PairedRecognizerDovetailControllerRawOutput C.result = some out ∧
          outCode = encodeBoolWord out :=
  DovetailControllerLayout.emitResultCodePrimitive_encode_eq_some_iff

theorem pairedRecognizerDovetailControllerResultEmitterCode_encode_eq_encodeBoolWord_iff
    {C : DovetailControllerLayout}
    {out : Word Bool} :
    PairedRecognizerDovetailControllerResultEmitterCode.transform
        (DovetailControllerLayout.encode C) =
        some (encodeBoolWord out) <->
      PairedRecognizerDovetailControllerRawOutput C.result = some out :=
  DovetailControllerLayout.emitResultCodePrimitive_encode_eq_encodeBoolWord_iff

theorem pairedRecognizerDovetailControllerResultContinueCode_encode_eq_some_iff
    {C : DovetailControllerLayout}
    {outCode : Word MachineCodeSymbol} :
    PairedRecognizerDovetailControllerResultContinueCode.transform
        (DovetailControllerLayout.encode C) =
        some outCode <->
      PairedRecognizerDovetailControllerRawOutput C.result = none ∧
        outCode =
          DovetailControllerLayout.encode
            (DovetailControllerLayout.nextStage C) :=
  DovetailControllerLayout.continueResultCodePrimitive_encode_eq_some_iff

theorem pairedRecognizerDovetailControllerResultContinueCode_encode_nextStage_iff
    {C : DovetailControllerLayout} :
    PairedRecognizerDovetailControllerResultContinueCode.transform
        (DovetailControllerLayout.encode C) =
        some
          (DovetailControllerLayout.encode
            (DovetailControllerLayout.nextStage C)) <->
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
      exists C : DovetailControllerLayout,
        code = DovetailControllerLayout.encode C ∧
          PairedRecognizerDovetailControllerRawOutput C.result = none ∧
            out =
              DovetailControllerLayout.encode
                (DovetailControllerLayout.nextStage C) := by
  constructor
  · intro h
    unfold PairedRecognizerDovetailControllerResultContinueCode at h
    unfold DovetailControllerLayout.continueResultCodePrimitive at h
    unfold DovetailControllerLayout.continueResultCode at h
    cases hdecode :
        DovetailControllerLayout.decodeComplete code with
    | none =>
        simp [hdecode] at h
    | some C =>
        cases hraw :
            DovetailControllerLayout.rawOutput? C.result with
        | none =>
            simp [hdecode, hraw] at h
            cases h
            exact
              ⟨C,
                DovetailControllerLayout.decodeComplete_eq_some_encode
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
      Option.map encodeBoolWord
        (boundedDovetailOutput
          accept reject w stage) :=
  DovetailControllerLayout.rawOutputCode_after_totalStageAttemptCode_stageInputCode
    accept reject w stage

theorem pairedRecognizerDovetailTotalThenRawOutputCode_eq_stageAttemptCode
    (accept reject : MachineDescription)
    (tokens : Word MachineCodeSymbol) :
    (PairedRecognizerDovetailTotalThenRawOutputCode
      accept reject).transform tokens =
      (PairedRecognizerDovetailStageAttemptCode
        accept reject).transform tokens :=
  DovetailControllerLayout.rawOutputCode_after_totalStageAttemptCode
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
    DovetailLayout.outputFromHits
        (DovetailLayout.run accept reject limit
          (DovetailLayout.initial
            accept reject w limit)) =
      boundedDovetailOutput accept reject w limit :=
  DovetailLayout.outputFromHits_run_initial_eq_boundedDovetailOutput
    accept reject w limit

end Computability
end FoC
