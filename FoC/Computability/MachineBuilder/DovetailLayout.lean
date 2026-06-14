import FoC.Computability.MachineBuilder.SimulatorLayout

set_option doc.verso true

/-!
# Machine-builder dovetail layouts
-/

namespace FoC
namespace Computability

open Languages

namespace MachineDescription

structure DovetailLayout where
  input : Word Bool
  stage : Nat
  acceptConfig : Configuration
  rejectConfig : Configuration
  acceptHit : Bool
  rejectHit : Bool

namespace DovetailLayout

def encodeAppend (L : DovetailLayout)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineCodeSymbol.transition ::
    encodeBoolWordAppend L.input
      (encodeNatAppend L.stage
        (encodeConfigurationAppend L.acceptConfig
          (encodeConfigurationAppend L.rejectConfig
            (encodeBoolAppend L.acceptHit
              (encodeBoolAppend L.rejectHit suffix)))))

def encode (L : DovetailLayout) : Word MachineCodeSymbol :=
  encodeAppend L []

def decode (tokens : Word MachineCodeSymbol) :
    Option (DovetailLayout × Word MachineCodeSymbol) :=
  match tokens with
  | MachineCodeSymbol.transition :: rest =>
      match decodeBoolWord rest with
      | none => none
      | some (input, rest) =>
          match decodeNat rest with
          | none => none
          | some (stage, rest) =>
              match decodeConfiguration rest with
              | none => none
              | some (acceptConfig, rest) =>
                  match decodeConfiguration rest with
                  | none => none
                  | some (rejectConfig, rest) =>
                      match decodeBool rest with
                      | none => none
                      | some (acceptHit, rest) =>
                          match decodeBool rest with
                          | none => none
                          | some (rejectHit, suffix) =>
                              some ({ input := input
                                      stage := stage
                                      acceptConfig := acceptConfig
                                      rejectConfig := rejectConfig
                                      acceptHit := acceptHit
                                      rejectHit := rejectHit }, suffix)
  | _ => none

theorem decode_encodeAppend
    (L : DovetailLayout) (suffix : Word MachineCodeSymbol) :
    decode (encodeAppend L suffix) = some (L, suffix) := by
  cases L
  simp [encodeAppend, decode, decodeBoolWord_encodeBoolWordAppend,
    decodeNat_encodeNatAppend, decodeConfiguration_encodeConfigurationAppend,
    decodeBool_encodeBoolAppend]

theorem decode_encode (L : DovetailLayout) :
    decode (encode L) = some (L, []) :=
  decode_encodeAppend L []

theorem decode_eq_some_encodeAppend
    {tokens : Word MachineCodeSymbol} {L : DovetailLayout}
    {suffix : Word MachineCodeSymbol}
    (h : decode tokens = some (L, suffix)) :
    tokens = encodeAppend L suffix := by
  unfold decode at h
  cases tokens with
  | nil =>
      simp at h
  | cons marker rest =>
      cases marker with
      | transition =>
          simp at h
          cases hinput : decodeBoolWord rest with
          | none =>
              simp [hinput] at h
          | some parsedInput =>
              cases parsedInput with
              | mk input restAfterInput =>
                  simp [hinput] at h
                  cases hstage : decodeNat restAfterInput with
                  | none =>
                      simp [hstage] at h
                  | some parsedStage =>
                      cases parsedStage with
                      | mk stage restAfterStage =>
                          simp [hstage] at h
                          cases hacceptConfig :
                              decodeConfiguration restAfterStage with
                          | none =>
                              simp [hacceptConfig] at h
                          | some parsedAcceptConfig =>
                              cases parsedAcceptConfig with
                              | mk acceptConfig restAfterAcceptConfig =>
                                  simp [hacceptConfig] at h
                                  cases hrejectConfig :
                                      decodeConfiguration
                                        restAfterAcceptConfig with
                                  | none =>
                                      simp [hrejectConfig] at h
                                  | some parsedRejectConfig =>
                                      cases parsedRejectConfig with
                                      | mk rejectConfig restAfterRejectConfig =>
                                          simp [hrejectConfig] at h
                                          cases hacceptHit :
                                              decodeBool
                                                restAfterRejectConfig with
                                          | none =>
                                              simp [hacceptHit] at h
                                          | some parsedAcceptHit =>
                                              cases parsedAcceptHit with
                                              | mk acceptHit
                                                  restAfterAcceptHit =>
                                                  simp [hacceptHit] at h
                                                  cases hrejectHit :
                                                      decodeBool
                                                        restAfterAcceptHit with
                                                  | none =>
                                                      simp [hrejectHit] at h
                                                  | some parsedRejectHit =>
                                                      cases parsedRejectHit with
                                                      | mk rejectHit
                                                          parsedSuffix =>
                                                          simp [hrejectHit]
                                                            at h
                                                          cases h
                                                          subst L
                                                          subst suffix
                                                          have hinputTokens :
                                                              rest =
                                                                encodeBoolWordAppend
                                                                  input
                                                                  restAfterInput :=
                                                            decodeBoolWord_eq_some_encodeBoolWordAppend
                                                              hinput
                                                          have hstageTokens :
                                                              restAfterInput =
                                                                encodeNatAppend
                                                                  stage
                                                                  restAfterStage :=
                                                            decodeNat_eq_some_encodeNatAppend
                                                              hstage
                                                          have hacceptConfigTokens :
                                                              restAfterStage =
                                                                encodeConfigurationAppend
                                                                  acceptConfig
                                                                  restAfterAcceptConfig :=
                                                            decodeConfiguration_eq_some_encodeConfigurationAppend
                                                              hacceptConfig
                                                          have hrejectConfigTokens :
                                                              restAfterAcceptConfig =
                                                                encodeConfigurationAppend
                                                                  rejectConfig
                                                                  restAfterRejectConfig :=
                                                            decodeConfiguration_eq_some_encodeConfigurationAppend
                                                              hrejectConfig
                                                          have hacceptHitTokens :
                                                              restAfterRejectConfig =
                                                                encodeBoolAppend
                                                                  acceptHit
                                                                  restAfterAcceptHit :=
                                                            decodeBool_eq_some_encodeBoolAppend
                                                              hacceptHit
                                                          have hrejectHitTokens :
                                                              restAfterAcceptHit =
                                                                encodeBoolAppend
                                                                  rejectHit
                                                                  parsedSuffix :=
                                                            decodeBool_eq_some_encodeBoolAppend
                                                              hrejectHit
                                                          simp [encodeAppend,
                                                            hinputTokens,
                                                            hstageTokens,
                                                            hacceptConfigTokens,
                                                            hrejectConfigTokens,
                                                            hacceptHitTokens,
                                                            hrejectHitTokens]
      | header => simp at h
      | tick => simp at h
      | done => simp at h
      | blank => simp at h
      | zero => simp at h
      | one => simp at h
      | moveLeft => simp at h
      | moveRight => simp at h

def decodeComplete (tokens : Word MachineCodeSymbol) :
    Option DovetailLayout :=
  match decode tokens with
  | some (L, []) => some L
  | _ => none

theorem decodeComplete_encode (L : DovetailLayout) :
    decodeComplete (encode L) = some L := by
  simp [decodeComplete, decode_encode]

theorem decodeComplete_eq_some_encode
    {tokens : Word MachineCodeSymbol} {L : DovetailLayout}
    (h : decodeComplete tokens = some L) :
    tokens = encode L := by
  unfold decodeComplete at h
  cases hdecode : decode tokens with
  | none =>
      simp [hdecode] at h
  | some parsed =>
      cases parsed with
      | mk decoded suffix =>
          cases suffix with
          | nil =>
              simp [hdecode] at h
              cases h
              simpa [encode] using decode_eq_some_encodeAppend hdecode
          | cons _ _ =>
              simp [hdecode] at h

def asBoolInput (L : DovetailLayout) : Word Bool :=
  encodeCodeWordAsInput (encode L)

def tape (L : DovetailLayout) : Tape Bool :=
  Tape.input (asBoolInput L)

theorem tape_normalizedOutput (L : DovetailLayout) :
    Tape.normalizedOutput (tape L) = asBoolInput L := by
  simpa [tape, asBoolInput] using
    (Tape.normalizedOutput_output (encodeCodeWordAsInput (encode L)))

def initial (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) : DovetailLayout where
  input := w
  stage := stage
  acceptConfig := accept.initial w
  rejectConfig := reject.initial w
  acceptHit := false
  rejectHit := false

def advance (accept reject : MachineDescription)
    (L : DovetailLayout) (steps : Nat) : DovetailLayout :=
  let acceptConfig := accept.runConfig steps L.acceptConfig
  let rejectConfig := reject.runConfig steps L.rejectConfig
  { L with
    acceptConfig := acceptConfig
    rejectConfig := rejectConfig
    acceptHit := L.acceptHit || (acceptConfig.state == accept.halt)
    rejectHit := L.rejectHit || (rejectConfig.state == reject.halt) }

theorem advance_acceptConfig
    (accept reject : MachineDescription)
    (L : DovetailLayout) (steps : Nat) :
    (advance accept reject L steps).acceptConfig =
      accept.runConfig steps L.acceptConfig := by
  simp [advance]

theorem advance_rejectConfig
    (accept reject : MachineDescription)
    (L : DovetailLayout) (steps : Nat) :
    (advance accept reject L steps).rejectConfig =
      reject.runConfig steps L.rejectConfig := by
  simp [advance]

def run (accept reject : MachineDescription)
    (steps : Nat) (L : DovetailLayout) : DovetailLayout :=
  let acceptConfig := accept.runConfig steps L.acceptConfig
  let rejectConfig := reject.runConfig steps L.rejectConfig
  { L with
    acceptConfig := acceptConfig
    rejectConfig := rejectConfig
    acceptHit :=
      L.acceptHit ||
        SimulatorLayout.hitsFromConfigByBool
          accept L.acceptConfig steps
    rejectHit :=
      L.rejectHit ||
        SimulatorLayout.hitsFromConfigByBool
          reject L.rejectConfig steps }

theorem run_acceptConfig
    (accept reject : MachineDescription)
    (L : DovetailLayout) (steps : Nat) :
    (run accept reject steps L).acceptConfig =
      accept.runConfig steps L.acceptConfig := by
  simp [run]

theorem run_rejectConfig
    (accept reject : MachineDescription)
    (L : DovetailLayout) (steps : Nat) :
    (run accept reject steps L).rejectConfig =
      reject.runConfig steps L.rejectConfig := by
  simp [run]

def outputFromHits (L : DovetailLayout) : Option (Word Bool) :=
  if L.acceptHit = true then
    some [true]
  else if L.rejectHit = true then
    some [false]
  else
    none

def outputWordFromOption :
    Option (Word Bool) -> Word Bool
  | none => []
  | some out => out

def outputWordFromHits (L : DovetailLayout) : Word Bool :=
  outputWordFromOption (outputFromHits L)

def stageInputCodeAppend (w : Word Bool) (stage : Nat)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  encodeBoolWordAppend w (encodeNatAppend stage suffix)

def stageInputCode (w : Word Bool) (stage : Nat) :
    Word MachineCodeSymbol :=
  stageInputCodeAppend w stage []

def decodeStageInput (tokens : Word MachineCodeSymbol) :
    Option ((Word Bool × Nat) × Word MachineCodeSymbol) :=
  match decodeBoolWord tokens with
  | none => none
  | some (w, rest) =>
      match decodeNat rest with
      | none => none
      | some (stage, suffix) => some ((w, stage), suffix)

theorem decodeStageInput_stageInputCodeAppend
    (w : Word Bool) (stage : Nat)
    (suffix : Word MachineCodeSymbol) :
    decodeStageInput (stageInputCodeAppend w stage suffix) =
      some ((w, stage), suffix) := by
  simp [decodeStageInput, stageInputCodeAppend,
    decodeBoolWord_encodeBoolWordAppend, decodeNat_encodeNatAppend]

theorem decodeStageInput_stageInputCode
    (w : Word Bool) (stage : Nat) :
    decodeStageInput (stageInputCode w stage) =
      some ((w, stage), []) :=
  decodeStageInput_stageInputCodeAppend w stage []

theorem decodeStageInput_eq_some_stageInputCodeAppend
    {tokens : Word MachineCodeSymbol} {w : Word Bool} {stage : Nat}
    {suffix : Word MachineCodeSymbol}
    (h : decodeStageInput tokens = some ((w, stage), suffix)) :
    tokens = stageInputCodeAppend w stage suffix := by
  unfold decodeStageInput at h
  cases hinput : decodeBoolWord tokens with
  | none =>
      simp [hinput] at h
  | some parsedInput =>
      cases parsedInput with
      | mk decodedInput restAfterInput =>
          simp [hinput] at h
          cases hstage : decodeNat restAfterInput with
          | none =>
              simp [hstage] at h
          | some parsedStage =>
              cases parsedStage with
              | mk decodedStage parsedSuffix =>
                  simp [hstage] at h
                  rcases h with ⟨hpair, hsuffix⟩
                  have hinputTokens :
                      tokens =
                        encodeBoolWordAppend decodedInput restAfterInput :=
                    decodeBoolWord_eq_some_encodeBoolWordAppend hinput
                  have hstageTokens :
                      restAfterInput =
                        encodeNatAppend decodedStage parsedSuffix :=
                    decodeNat_eq_some_encodeNatAppend hstage
                  simp [stageInputCodeAppend, hinputTokens, hstageTokens,
                    hpair.1, hpair.2, hsuffix]

def decodeStageInputComplete (tokens : Word MachineCodeSymbol) :
    Option (Word Bool × Nat) :=
  match decodeStageInput tokens with
  | some (parsed, []) => some parsed
  | _ => none

theorem decodeStageInputComplete_stageInputCode
    (w : Word Bool) (stage : Nat) :
    decodeStageInputComplete (stageInputCode w stage) =
      some (w, stage) := by
  simp [decodeStageInputComplete, decodeStageInput_stageInputCode]

theorem decodeStageInputComplete_eq_some_stageInputCode
    {tokens : Word MachineCodeSymbol} {w : Word Bool} {stage : Nat}
    (h : decodeStageInputComplete tokens = some (w, stage)) :
    tokens = stageInputCode w stage := by
  unfold decodeStageInputComplete at h
  cases hdecode : decodeStageInput tokens with
  | none =>
      simp [hdecode] at h
  | some parsed =>
      cases parsed with
      | mk pair suffix =>
          cases suffix with
          | nil =>
              simp [hdecode] at h
              cases h
              simpa [stageInputCode] using
                decodeStageInput_eq_some_stageInputCodeAppend hdecode
          | cons _ _ =>
              simp [hdecode] at h

def initialCode (accept reject : MachineDescription)
    (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match decodeStageInputComplete tokens with
  | none => none
  | some (w, stage) => some (encode (initial accept reject w stage))

theorem initialCode_stageInputCode
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    initialCode accept reject (stageInputCode w stage) =
      some (encode (initial accept reject w stage)) := by
  simp [initialCode, decodeStageInputComplete_stageInputCode]

def initialCodePrimitive
    (accept reject : MachineDescription) : TapeCodePrimitive where
  transform := initialCode accept reject

theorem initialCodePrimitive_stageInputCode
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    (initialCodePrimitive accept reject).transform
        (stageInputCode w stage) =
      some (encode (initial accept reject w stage)) :=
  initialCode_stageInputCode accept reject w stage

def outputCode (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match decodeComplete tokens with
  | none => none
  | some L =>
      match outputFromHits L with
      | none => none
      | some out => some (encodeBoolWord out)

theorem outputCode_encode_of_outputFromHits_eq_some
    {L : DovetailLayout} {out : Word Bool}
    (h : outputFromHits L = some out) :
    outputCode (encode L) = some (encodeBoolWord out) := by
  simp [outputCode, decodeComplete_encode, h]

theorem outputCode_encode_of_outputFromHits_eq_none
    {L : DovetailLayout}
    (h : outputFromHits L = none) :
    outputCode (encode L) = none := by
  simp [outputCode, decodeComplete_encode, h]

def outputCodePrimitive : TapeCodePrimitive where
  transform := outputCode

def stageAttemptCode (accept reject : MachineDescription)
    (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match decodeStageInputComplete tokens with
  | none => none
  | some (w, stage) =>
      match outputFromHits
          (run accept reject stage
            (initial accept reject w stage)) with
      | none => none
      | some out => some (encodeBoolWord out)

def stageAttemptCodePrimitive
    (accept reject : MachineDescription) : TapeCodePrimitive where
  transform := stageAttemptCode accept reject

def totalStageAttemptCode (accept reject : MachineDescription)
    (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match decodeStageInputComplete tokens with
  | none => none
  | some (w, stage) =>
      some
        (encodeBoolWord
          (outputWordFromHits
            (run accept reject stage
              (initial accept reject w stage))))

def totalStageAttemptCodePrimitive
    (accept reject : MachineDescription) : TapeCodePrimitive where
  transform := totalStageAttemptCode accept reject

def runCode (accept reject : MachineDescription)
    (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match decodeComplete tokens with
  | none => none
  | some L => some (encode (run accept reject L.stage L))

theorem runCode_encode
    (accept reject : MachineDescription) (L : DovetailLayout) :
    runCode accept reject (encode L) =
      some (encode (run accept reject L.stage L)) := by
  simp [runCode, decodeComplete_encode]

def runCodePrimitive
    (accept reject : MachineDescription) : TapeCodePrimitive where
  transform := runCode accept reject

theorem runCodePrimitive_encode
    (accept reject : MachineDescription) (L : DovetailLayout) :
    (runCodePrimitive accept reject).transform (encode L) =
      some (encode (run accept reject L.stage L)) :=
  runCode_encode accept reject L

end DovetailLayout

/-!
## Executable bounded simulation

The following Boolean search is the executable core of the textbook dovetailing
argument.  It searches the concrete interpreter up to a stage bound and is
proved equivalent to the trace-level search used by {name}`DovetailProgram`.
-/

def haltsInBool (D : MachineDescription) (n : Nat)
    (w : Word Bool) : Bool :=
  (D.runConfig n (D.initial w)).state == D.halt

theorem haltsInBool_eq_true_iff
    (D : MachineDescription) (n : Nat) (w : Word Bool) :
    haltsInBool D n w = true <-> D.HaltsIn n w := by
  simp [haltsInBool, HaltsIn]

def hitsByBool (D : MachineDescription) (w : Word Bool) :
    Nat -> Bool
  | 0 => haltsInBool D 0 w
  | limit + 1 =>
      hitsByBool D w limit || haltsInBool D (limit + 1) w

theorem hitsByBool_eq_true_iff
    (D : MachineDescription) (w : Word Bool) (limit : Nat) :
    hitsByBool D w limit = true <->
      exists n : Nat, n ≤ limit ∧ D.HaltsIn n w := by
  induction limit with
  | zero =>
      constructor
      · intro h
        exact ⟨0, Nat.le_refl 0,
          (haltsInBool_eq_true_iff D 0 w).mp h⟩
      · intro h
        rcases h with ⟨n, hnle, hhalt⟩
        have hn : n = 0 := by omega
        cases hn
        exact (haltsInBool_eq_true_iff D 0 w).mpr hhalt
  | succ limit ih =>
      constructor
      · intro h
        have hcases :
            hitsByBool D w limit = true ∨
              haltsInBool D (limit + 1) w = true := by
          simpa [hitsByBool] using h
        cases hcases with
        | inl hprev =>
            rcases ih.mp hprev with ⟨n, hnle, hhalt⟩
            exact ⟨n, Nat.le_trans hnle (Nat.le_succ limit), hhalt⟩
        | inr hnow =>
            exact ⟨limit + 1, Nat.le_refl (limit + 1),
              (haltsInBool_eq_true_iff D (limit + 1) w).mp hnow⟩
      · intro h
        rcases h with ⟨n, hnle, hhalt⟩
        by_cases hn : n ≤ limit
        · have hprev : hitsByBool D w limit = true :=
            ih.mpr ⟨n, hn, hhalt⟩
          simp [hitsByBool, hprev]
        · have hnEq : n = limit + 1 := by omega
          cases hnEq
          have hnow : haltsInBool D (limit + 1) w = true :=
            (haltsInBool_eq_true_iff D (limit + 1) w).mpr hhalt
          simp [hitsByBool, hnow]

def boundedDovetailOutput
    (accept reject : MachineDescription)
    (w : Word Bool) (limit : Nat) : Option (Word Bool) :=
  if hitsByBool accept w limit = true then
    some [true]
  else if hitsByBool reject w limit = true then
    some [false]
  else
    none

namespace DovetailLayout

theorem simulator_hitsFromInitial_eq_hitsByBool
    (D : MachineDescription) (w : Word Bool) (limit : Nat) :
    SimulatorLayout.hitsFromConfigByBool D (D.initial w) limit =
      hitsByBool D w limit := by
  induction limit with
  | zero =>
      simp [SimulatorLayout.hitsFromConfigByBool, hitsByBool,
        SimulatorLayout.haltedFromConfigInBool, haltsInBool]
  | succ limit ih =>
      simp [SimulatorLayout.hitsFromConfigByBool, hitsByBool,
        SimulatorLayout.haltedFromConfigInBool, haltsInBool, ih]

theorem run_initial_acceptHit
    (accept reject : MachineDescription)
    (w : Word Bool) (limit : Nat) :
    (run accept reject limit
      (initial accept reject w limit)).acceptHit =
      hitsByBool accept w limit := by
  simp [run, initial, simulator_hitsFromInitial_eq_hitsByBool]

theorem run_initial_rejectHit
    (accept reject : MachineDescription)
    (w : Word Bool) (limit : Nat) :
    (run accept reject limit
      (initial accept reject w limit)).rejectHit =
      hitsByBool reject w limit := by
  simp [run, initial, simulator_hitsFromInitial_eq_hitsByBool]

theorem outputFromHits_run_initial_eq_boundedDovetailOutput
    (accept reject : MachineDescription)
    (w : Word Bool) (limit : Nat) :
    outputFromHits
        (run accept reject limit
          (initial accept reject w limit)) =
      boundedDovetailOutput accept reject w limit := by
  simp [outputFromHits, boundedDovetailOutput,
    run_initial_acceptHit, run_initial_rejectHit]

theorem stageAttemptCode_stageInputCode
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    stageAttemptCode accept reject (stageInputCode w stage) =
      Option.map encodeBoolWord
        (boundedDovetailOutput accept reject w stage) := by
  rw [← outputFromHits_run_initial_eq_boundedDovetailOutput]
  cases h :
      outputFromHits
        (run accept reject stage (initial accept reject w stage)) <;>
    simp [stageAttemptCode, decodeStageInputComplete_stageInputCode, h]

theorem stageAttemptCode_stageInputCode_of_boundedDovetailOutput_eq_some
    {accept reject : MachineDescription}
    {w : Word Bool} {stage : Nat} {out : Word Bool}
    (h :
      boundedDovetailOutput accept reject w stage = some out) :
    stageAttemptCode accept reject (stageInputCode w stage) =
      some (encodeBoolWord out) := by
  rw [stageAttemptCode_stageInputCode, h]
  rfl

theorem stageAttemptCode_stageInputCode_of_boundedDovetailOutput_eq_none
    {accept reject : MachineDescription}
    {w : Word Bool} {stage : Nat}
    (h :
      boundedDovetailOutput accept reject w stage = none) :
    stageAttemptCode accept reject (stageInputCode w stage) = none := by
  rw [stageAttemptCode_stageInputCode, h]
  rfl

theorem stageAttemptCodePrimitive_stageInputCode
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    (stageAttemptCodePrimitive accept reject).transform
        (stageInputCode w stage) =
      Option.map encodeBoolWord
        (boundedDovetailOutput accept reject w stage) :=
  stageAttemptCode_stageInputCode accept reject w stage

theorem totalStageAttemptCode_stageInputCode
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    totalStageAttemptCode accept reject (stageInputCode w stage) =
      some
        (encodeBoolWord
          (outputWordFromOption
            (boundedDovetailOutput accept reject w stage))) := by
  rw [← outputFromHits_run_initial_eq_boundedDovetailOutput]
  cases h :
      outputFromHits
        (run accept reject stage (initial accept reject w stage)) <;>
    simp [totalStageAttemptCode, outputWordFromHits,
      outputWordFromOption, decodeStageInputComplete_stageInputCode, h]

theorem totalStageAttemptCode_stageInputCode_of_boundedDovetailOutput_eq_some
    {accept reject : MachineDescription}
    {w : Word Bool} {stage : Nat} {out : Word Bool}
    (h :
      boundedDovetailOutput accept reject w stage = some out) :
    totalStageAttemptCode accept reject (stageInputCode w stage) =
      some (encodeBoolWord out) := by
  rw [totalStageAttemptCode_stageInputCode, h]
  rfl

theorem totalStageAttemptCode_stageInputCode_of_boundedDovetailOutput_eq_none
    {accept reject : MachineDescription}
    {w : Word Bool} {stage : Nat}
    (h :
      boundedDovetailOutput accept reject w stage = none) :
    totalStageAttemptCode accept reject (stageInputCode w stage) =
      some (encodeBoolWord []) := by
  rw [totalStageAttemptCode_stageInputCode, h]
  rfl

theorem totalStageAttemptCodePrimitive_stageInputCode
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    (totalStageAttemptCodePrimitive accept reject).transform
        (stageInputCode w stage) =
      some
        (encodeBoolWord
          (outputWordFromOption
            (boundedDovetailOutput accept reject w stage))) :=
  totalStageAttemptCode_stageInputCode accept reject w stage

end DovetailLayout

end MachineDescription

end Computability
end FoC
