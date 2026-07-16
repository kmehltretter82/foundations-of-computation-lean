import FoC.Computability.Compiler.Core.FiniteRecognizer.DecodedDescriptionInterpreter
import FoC.Computability.Compiler.UniversalAndRanges.Basic

set_option doc.verso true

/-!
# Normalized decoded bounded simulator runner

This module specifies the uniform finite-machine construction for the
normalized decoded bounded simulator. The public wrapper in
the decoded bounded simulator module
adapts this construction to the local spec definitions.
-/

namespace FoC
namespace Computability

open Languages

namespace MachineDescription

theorem haltsIn_zero_iff
    (D : MachineDescription) (w : Word Bool) :
    D.HaltsIn 0 w <-> D.start = D.halt := by
  simp [HaltsIn, initial, runConfig]

theorem runConfig_succ_of_stepConfig_none
    {D : MachineDescription} {c : Configuration} {n : Nat}
    (hstep : D.stepConfig c = none) :
    D.runConfig (n + 1) c = c := by
  simp [runConfig, hstep]

theorem runConfig_succ_of_stepConfig_some
    {D : MachineDescription} {c next : Configuration} {n : Nat}
    (hstep : D.stepConfig c = some next) :
    D.runConfig (n + 1) c = D.runConfig n next := by
  simp [runConfig, hstep]

theorem stepConfig_of_lookupTransition_none
    {D : MachineDescription} {c : Configuration}
    (hlookup :
      D.lookupTransition c.state (Tape.read c.tape) = none) :
    D.stepConfig c = none := by
  simp [stepConfig, hlookup]

theorem stepConfig_of_lookupTransition_some
    {D : MachineDescription} {c : Configuration}
    {t : TransitionDescription}
    (hlookup :
      D.lookupTransition c.state (Tape.read c.tape) = some t) :
    D.stepConfig c =
      some
        { state := t.target
          tape := Tape.move t.move (Tape.write t.write c.tape) } := by
  simp [stepConfig, hlookup]

def scanTransitionTable
    (source : Nat) (read : Option Bool)
    (transitions : List TransitionDescription) :
    Option TransitionDescription :=
  transitions.find? (Matches source read)

theorem lookupTransition_eq_scanTransitionTable
    (D : MachineDescription) (source : Nat) (read : Option Bool) :
    D.lookupTransition source read =
      scanTransitionTable source read D.transitions :=
  rfl

theorem scanTransitionTable_nil
    (source : Nat) (read : Option Bool) :
    scanTransitionTable source read [] = none :=
  rfl

theorem scanTransitionTable_cons_match
    {source : Nat} {read : Option Bool}
    {transition : TransitionDescription}
    {rest : List TransitionDescription}
    (hmatch : Matches source read transition = true) :
    scanTransitionTable source read (transition :: rest) =
      some transition := by
  simp [scanTransitionTable, hmatch]

theorem scanTransitionTable_cons_skip
    {source : Nat} {read : Option Bool}
    {transition : TransitionDescription}
    {rest : List TransitionDescription}
    (hmatch : Matches source read transition = false) :
    scanTransitionTable source read (transition :: rest) =
      scanTransitionTable source read rest := by
  simp [scanTransitionTable, hmatch]

theorem matches_eq_true_iff
    (source : Nat) (read : Option Bool)
    (transition : TransitionDescription) :
    Matches source read transition = true <->
      transition.source = source ∧ transition.read = read := by
  simp [Matches]

theorem stepConfig_eq_none_iff_lookupTransition_eq_none
    {D : MachineDescription} {c : Configuration} :
    D.stepConfig c = none <->
      D.lookupTransition c.state (Tape.read c.tape) = none := by
  unfold stepConfig
  cases D.lookupTransition c.state (Tape.read c.tape) <;> simp

theorem stepConfig_eq_some_iff_lookupTransition_eq_some
    {D : MachineDescription} {c next : Configuration} :
    D.stepConfig c = some next <->
      exists t : TransitionDescription,
        D.lookupTransition c.state (Tape.read c.tape) = some t ∧
          next =
            { state := t.target
              tape := Tape.move t.move (Tape.write t.write c.tape) } := by
  constructor
  · intro hstep
    unfold stepConfig at hstep
    cases hlookup :
        D.lookupTransition c.state (Tape.read c.tape) with
    | none =>
        simp [hlookup] at hstep
    | some t =>
        simp [hlookup] at hstep
        subst next
        exact ⟨t, rfl, rfl⟩
  · intro h
    rcases h with ⟨t, hlookup, rfl⟩
    exact stepConfig_of_lookupTransition_some hlookup

theorem haltsIn_succ_iff_stepConfig_initial_none
    {D : MachineDescription} {w : Word Bool} {n : Nat}
    (hstep : D.stepConfig (D.initial w) = none) :
    D.HaltsIn (n + 1) w <-> D.start = D.halt := by
  change
    (D.runConfig (n + 1) (D.initial w)).state = D.halt <->
      D.start = D.halt
  rw [runConfig_succ_of_stepConfig_none hstep]
  simp [initial]

theorem haltsIn_succ_iff_stepConfig_initial_some
    {D : MachineDescription} {w : Word Bool} {n : Nat}
    {next : Configuration}
    (hstep : D.stepConfig (D.initial w) = some next) :
    D.HaltsIn (n + 1) w <->
      (D.runConfig n next).state = D.halt := by
  simp [HaltsIn, runConfig_succ_of_stepConfig_some hstep]

theorem runConfig_succ_of_lookupTransition_none
    {D : MachineDescription} {c : Configuration} {n : Nat}
    (hlookup :
      D.lookupTransition c.state (Tape.read c.tape) = none) :
    D.runConfig (n + 1) c = c :=
  runConfig_succ_of_stepConfig_none
    (stepConfig_of_lookupTransition_none hlookup)

theorem runConfig_succ_of_lookupTransition_some
    {D : MachineDescription} {c : Configuration}
    {t : TransitionDescription} {n : Nat}
    (hlookup :
      D.lookupTransition c.state (Tape.read c.tape) = some t) :
    D.runConfig (n + 1) c =
      D.runConfig n
        { state := t.target
          tape := Tape.move t.move (Tape.write t.write c.tape) } :=
  runConfig_succ_of_stepConfig_some
    (stepConfig_of_lookupTransition_some hlookup)

theorem stepConfig_eq_scanTransitionTable
    {D : MachineDescription} {c : Configuration} :
    D.stepConfig c =
      match
        scanTransitionTable c.state (Tape.read c.tape)
          D.transitions with
      | none => none
      | some t =>
          some
            { state := t.target
              tape := Tape.move t.move (Tape.write t.write c.tape) } := by
  rfl

theorem runConfig_succ_eq_scanTransitionTable
    {D : MachineDescription} {c : Configuration} {n : Nat} :
    D.runConfig (n + 1) c =
      match
        scanTransitionTable c.state (Tape.read c.tape)
          D.transitions with
      | none => c
      | some t =>
          D.runConfig n
            { state := t.target
              tape := Tape.move t.move (Tape.write t.write c.tape) } := by
  simp [scanTransitionTable, lookupTransition, runConfig, stepConfig]
  cases hlookup :
      List.find? (Matches c.state (Tape.read c.tape))
        D.transitions <;> simp

end MachineDescription

/-- Canonical source word for a normalized decoded bounded-simulator call. -/
def decodedBoundedSimulatorNormalizedInput
    (stage : Nat) (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  CodePrefixRecognizerStageCode
    (List.append (MachineDescription.encodeDescription D) input) stage

/-- The normalized source word decodes to its requested stage and payload. -/
theorem decodedBoundedSimulatorNormalizedInput_decodeNat
    (stage : Nat) (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    MachineDescription.decodeNat
        (decodedBoundedSimulatorNormalizedInput stage D input) =
      some (stage,
        List.append (MachineDescription.encodeDescription D) input) := by
  simpa [decodedBoundedSimulatorNormalizedInput] using!
    codePrefixRecognizerStageCode_decodeNat
      (List.append (MachineDescription.encodeDescription D) input) stage

/--
The code primitive accepts a normalized source word exactly when the decoded
machine halts within the requested stage bound.
-/
theorem decodedBoundedSimulatorNormalizedInput_transform_eq_some_nil_iff
    (stage : Nat) (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    CodePrefixDecodedBoundedSimulatorCode.transform
        (decodedBoundedSimulatorNormalizedInput stage D input) =
        some ([] : Word MachineCodeSymbol) <->
      D.HaltsIn stage
        (MachineDescription.encodeCodeWordAsInput input) := by
  simpa [decodedBoundedSimulatorNormalizedInput] using
    codePrefixDecodedBoundedSimulatorCode_stageCode_eq_some_iff
      (MachineDescription.decodeDescriptionPrefix_encodeDescription_append
        D input)

/--
The code primitive has the same accepted language as the normalized decoded
source predicate used by the uniform runner construction.
-/
theorem decodedBoundedSimulatorNormalizedCode_transform_eq_some_nil_iff
    (tokens : Word MachineCodeSymbol) :
    CodePrefixDecodedBoundedSimulatorCode.transform tokens =
        some ([] : Word MachineCodeSymbol) <->
      exists stage : Nat,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens =
            some (stage,
              List.append (MachineDescription.encodeDescription D) input) ∧
          D.HaltsIn stage
            (MachineDescription.encodeCodeWordAsInput input) := by
  constructor
  · intro h
    rcases
        (codePrefixDecodedBoundedSimulatorCode_transform_eq_some_iff
          tokens ([] : Word MachineCodeSymbol)).mp h with
      ⟨_, stage, encoded, D, input, htokens, hdecode, hhalts⟩
    have hstage :
        MachineDescription.decodeNat tokens =
          some (stage, encoded) := by
      simpa [htokens] using
        codePrefixRecognizerStageCode_decodeNat encoded stage
    have hencoded :
        encoded =
          List.append (MachineDescription.encodeDescription D) input :=
      MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescription_append
        hdecode
    exact
      ⟨stage, D, input, by simpa [hencoded] using! hstage, hhalts⟩
  · intro h
    rcases h with ⟨stage, D, input, hstage, hhalts⟩
    exact
      (codePrefixDecodedBoundedSimulatorCode_transform_eq_some_iff
        tokens ([] : Word MachineCodeSymbol)).mpr
        ⟨rfl, stage,
          List.append (MachineDescription.encodeDescription D) input,
          D, input,
          codePrefixRecognizerStageCode_eq_of_decodeNat hstage,
          MachineDescription.decodeDescriptionPrefix_encodeDescription_append
            D input,
          hhalts⟩

/--
On a generated stage-coded input, the code primitive is exactly the bounded
stage evaluator for {name}`CodePrefixRecognizerProgram`.
-/
theorem decodedBoundedSimulatorCode_stageCode_transform_eq_program_run
    (encoded : Word MachineCodeSymbol) (stage : Nat) :
    CodePrefixDecodedBoundedSimulatorCode.transform
        (CodePrefixRecognizerStageCode encoded stage) =
        some ([] : Word MachineCodeSymbol) <->
      CodePrefixRecognizerProgram.run encoded stage = some [] := by
  unfold CodePrefixRecognizerProgram
  cases hdecode :
      MachineDescription.decodeDescriptionPrefix encoded with
  | none =>
      simp [CodePrefixDecodedBoundedSimulatorCode,
        CodePrefixRecognizerStageCode,
        MachineDescription.decodeNat_encodeNatAppend, hdecode]
  | some decoded =>
      rcases decoded with ⟨D, input⟩
      by_cases hhalts :
          D.HaltsIn stage
            (MachineDescription.encodeCodeWordAsInput input)
      · simp [CodePrefixDecodedBoundedSimulatorCode,
          CodePrefixRecognizerStageCode,
          MachineDescription.decodeNat_encodeNatAppend, hdecode, hhalts]
        constructor <;> intro _ <;> rfl
      · simp [CodePrefixDecodedBoundedSimulatorCode,
          CodePrefixRecognizerStageCode,
          MachineDescription.decodeNat_encodeNatAppend, hdecode, hhalts]

/--
The same evaluator equivalence, phrased for an arbitrary source word whose
outer stage code has already been decoded.
-/
theorem decodedBoundedSimulatorCode_transform_eq_program_run_of_decodeNat
    {tokens encoded : Word MachineCodeSymbol} {stage : Nat}
    (hstage :
      MachineDescription.decodeNat tokens = some (stage, encoded)) :
    CodePrefixDecodedBoundedSimulatorCode.transform tokens =
        some ([] : Word MachineCodeSymbol) <->
      CodePrefixRecognizerProgram.run encoded stage = some [] := by
  have htokens :
      tokens = CodePrefixRecognizerStageCode encoded stage :=
    codePrefixRecognizerStageCode_eq_of_decodeNat hstage
  subst tokens
  exact
    decodedBoundedSimulatorCode_stageCode_transform_eq_program_run
      encoded stage

/--
The code primitive accepts exactly those inputs whose outer stage code exposes
a bounded successful run of {name}`CodePrefixRecognizerProgram`.
-/
theorem decodedBoundedSimulatorCode_transform_eq_stageProgramRun_iff
    (tokens : Word MachineCodeSymbol) :
    CodePrefixDecodedBoundedSimulatorCode.transform tokens =
        some ([] : Word MachineCodeSymbol) <->
      exists stage : Nat,
      exists encoded : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens = some (stage, encoded) ∧
          CodePrefixRecognizerProgram.run encoded stage = some [] := by
  constructor
  · intro h
    rcases
        (codePrefixDecodedBoundedSimulatorCode_transform_eq_some_iff
          tokens ([] : Word MachineCodeSymbol)).mp h with
      ⟨_, stage, encoded, _D, _input, htokens, _hdecode, _hhalts⟩
    have hstage :
        MachineDescription.decodeNat tokens = some (stage, encoded) := by
      simpa [htokens] using
        codePrefixRecognizerStageCode_decodeNat encoded stage
    have hprogram :
        CodePrefixRecognizerProgram.run encoded stage = some [] :=
      (decodedBoundedSimulatorCode_transform_eq_program_run_of_decodeNat
        hstage).mp h
    exact ⟨stage, encoded, hstage, hprogram⟩
  · intro h
    rcases h with ⟨stage, encoded, hstage, hprogram⟩
    exact
      (decodedBoundedSimulatorCode_transform_eq_program_run_of_decodeNat
        hstage).mpr hprogram

/--
One stage of {name}`CodePrefixRecognizerProgram` succeeds exactly when the
payload decodes and the decoded description halts within that stage bound.
-/
theorem codePrefixRecognizerProgram_run_eq_some_nil_iff
    (encoded : Word MachineCodeSymbol) (stage : Nat) :
    CodePrefixRecognizerProgram.run encoded stage = some [] <->
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeDescriptionPrefix encoded =
            some (D, input) ∧
          D.HaltsIn stage
            (MachineDescription.encodeCodeWordAsInput input) := by
  unfold CodePrefixRecognizerProgram
  constructor
  · intro h
    cases hdecode :
        MachineDescription.decodeDescriptionPrefix encoded with
    | none =>
        simp [hdecode] at h
    | some decoded =>
        rcases decoded with ⟨D, input⟩
        by_cases hhalts :
            D.HaltsIn stage
              (MachineDescription.encodeCodeWordAsInput input)
        · exact ⟨D, input, rfl, hhalts⟩
        · simp [hdecode, hhalts] at h
  · intro h
    rcases h with ⟨D, input, hdecode, hhalts⟩
    simp [hdecode, hhalts]
    rfl

/--
Boolean form of the staged evaluator. The normalized runner computes the
executable bounded-trace predicate
{name}`MachineDescription.haltsInBool` after the source has been normalized.
-/
theorem codePrefixRecognizerProgram_run_eq_some_nil_iff_haltsInBool
    (encoded : Word MachineCodeSymbol) (stage : Nat) :
    CodePrefixRecognizerProgram.run encoded stage = some [] <->
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeDescriptionPrefix encoded =
            some (D, input) ∧
          MachineDescription.haltsInBool D stage
            (MachineDescription.encodeCodeWordAsInput input) = true := by
  rw [codePrefixRecognizerProgram_run_eq_some_nil_iff]
  constructor
  · intro h
    rcases h with ⟨D, input, hdecode, hhalts⟩
    exact
      ⟨D, input, hdecode,
        (MachineDescription.haltsInBool_eq_true_iff D stage
          (MachineDescription.encodeCodeWordAsInput input)).mpr hhalts⟩
  · intro h
    rcases h with ⟨D, input, hdecode, hhalts⟩
    exact
      ⟨D, input, hdecode,
        (MachineDescription.haltsInBool_eq_true_iff D stage
          (MachineDescription.encodeCodeWordAsInput input)).mp hhalts⟩

/--
Normalized Boolean runner specification for the decoded bounded simulator: it
parses the outer stage and a canonical encoded description payload, then
evaluates the executable bounded-trace Boolean.
-/
def DecodedBoundedSimulatorBooleanRunnerSpec
    (runner : TuringMachine MachineCodeSymbol state) : Prop :=
  forall tokens : Word MachineCodeSymbol,
    TuringMachine.HaltsOnInput runner tokens <->
      exists stage : Nat,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens =
            some (stage,
              List.append (MachineDescription.encodeDescription D) input) ∧
          MachineDescription.haltsInBool D stage
            (MachineDescription.encodeCodeWordAsInput input) = true

/--
Finite-machine construction target for the normalized boolean runner.
-/
def DecodedBoundedSimulatorBooleanRunnerConstruction : Prop :=
  exists state : Type,
  exists runner : TuringMachine MachineCodeSymbol state,
    DecodedBoundedSimulatorBooleanRunnerSpec runner

/--
Run-config form of the normalized bounded simulator runner.  This is the
transition-level target underneath {name}`MachineDescription.haltsInBool`.
-/
def DecodedBoundedSimulatorRunConfigRunnerSpec
    (runner : TuringMachine MachineCodeSymbol state) : Prop :=
  forall tokens : Word MachineCodeSymbol,
    TuringMachine.HaltsOnInput runner tokens <->
      exists stage : Nat,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens =
            some (stage,
              List.append (MachineDescription.encodeDescription D) input) ∧
          (D.runConfig stage
            (D.initial
              (MachineDescription.encodeCodeWordAsInput input))).state =
            D.halt

/--
Finite-machine construction target for the normalized run-config runner.
-/
def DecodedBoundedSimulatorRunConfigRunnerConstruction : Prop :=
  exists state : Type,
  exists runner : TuringMachine MachineCodeSymbol state,
    DecodedBoundedSimulatorRunConfigRunnerSpec runner

/--
The semantic configuration reached by the uniform decoded transition loop from
an arbitrary current configuration. This invariant describes repeated scans of
the decoded transition table, application of the selected write/move action,
and decrement of the parsed stage counter.
-/
def decodedBoundedSimulatorTransitionLoopFromConfig
    (stage : Nat) (D : MachineDescription)
    (config : MachineDescription.Configuration) :
    MachineDescription.Configuration :=
  D.runConfig stage config

theorem decodedBoundedSimulatorTransitionLoopFromConfig_zero
    (D : MachineDescription)
    (config : MachineDescription.Configuration) :
    decodedBoundedSimulatorTransitionLoopFromConfig 0 D config =
      config :=
  rfl

theorem decodedBoundedSimulatorTransitionLoopFromConfig_succ_eq_scan
    (stage : Nat) (D : MachineDescription)
    (config : MachineDescription.Configuration) :
    decodedBoundedSimulatorTransitionLoopFromConfig (stage + 1) D config =
      match
        MachineDescription.scanTransitionTable
          config.state (Tape.read config.tape) D.transitions with
      | none => config
      | some transition =>
          decodedBoundedSimulatorTransitionLoopFromConfig stage D
            { state := transition.target
              tape :=
                Tape.move transition.move
                  (Tape.write transition.write config.tape) } := by
  simpa [decodedBoundedSimulatorTransitionLoopFromConfig] using!
    (MachineDescription.runConfig_succ_eq_scanTransitionTable
      (D := D) (c := config) (n := stage))

/--
The semantic configuration reached by the uniform decoded transition loop from
the canonical initial configuration for a decoded source word.
-/
def decodedBoundedSimulatorTransitionLoopConfig
    (stage : Nat) (D : MachineDescription)
    (input : Word MachineCodeSymbol) : MachineDescription.Configuration :=
  decodedBoundedSimulatorTransitionLoopFromConfig stage D
    (D.initial (MachineDescription.encodeCodeWordAsInput input))

theorem decodedBoundedSimulatorTransitionLoopConfig_zero
    (D : MachineDescription) (input : Word MachineCodeSymbol) :
    decodedBoundedSimulatorTransitionLoopConfig 0 D input =
      D.initial (MachineDescription.encodeCodeWordAsInput input) :=
  rfl

theorem decodedBoundedSimulatorTransitionLoopConfig_succ
    (stage : Nat) (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    decodedBoundedSimulatorTransitionLoopConfig (stage + 1) D input =
      match
        D.stepConfig
          (D.initial (MachineDescription.encodeCodeWordAsInput input)) with
      | none =>
          D.initial (MachineDescription.encodeCodeWordAsInput input)
      | some next => D.runConfig stage next := by
  simp [decodedBoundedSimulatorTransitionLoopConfig,
    decodedBoundedSimulatorTransitionLoopFromConfig,
    MachineDescription.runConfig]
  rfl

theorem decodedBoundedSimulatorTransitionLoopConfig_succ_eq_scan
    (stage : Nat) (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    decodedBoundedSimulatorTransitionLoopConfig (stage + 1) D input =
      match
        MachineDescription.scanTransitionTable
          (D.initial
            (MachineDescription.encodeCodeWordAsInput input)).state
          (Tape.read
            (D.initial
              (MachineDescription.encodeCodeWordAsInput input)).tape)
          D.transitions with
      | none =>
          D.initial (MachineDescription.encodeCodeWordAsInput input)
      | some transition =>
          decodedBoundedSimulatorTransitionLoopFromConfig stage D
            { state := transition.target
              tape :=
                Tape.move transition.move
                  (Tape.write transition.write
                    (D.initial
                      (MachineDescription.encodeCodeWordAsInput input)).tape) } := by
  simpa [decodedBoundedSimulatorTransitionLoopConfig] using
    decodedBoundedSimulatorTransitionLoopFromConfig_succ_eq_scan
      stage D
      (D.initial (MachineDescription.encodeCodeWordAsInput input))

/--
Canonical code payload for the transition-loop work tape: decoded description,
remaining stage, current configuration, then a preserved suffix.
-/
def decodedBoundedSimulatorTransitionLoopWorkCodeAppend
    (D : MachineDescription) (stage : Nat)
    (config : MachineDescription.Configuration)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeDescriptionAppend D
    (MachineDescription.encodeNatAppend stage
      (MachineDescription.encodeConfigurationAppend config suffix))

/-- Canonical complete transition-loop work payload. -/
def decodedBoundedSimulatorTransitionLoopWorkCode
    (D : MachineDescription) (stage : Nat)
    (config : MachineDescription.Configuration) :
    Word MachineCodeSymbol :=
  decodedBoundedSimulatorTransitionLoopWorkCodeAppend D stage config []

/--
Decoder for the canonical transition-loop work payload.
-/
def decodedBoundedSimulatorTransitionLoopWorkDecode
    (tokens : Word MachineCodeSymbol) :
    Option
      (MachineDescription × Nat ×
        MachineDescription.Configuration × Word MachineCodeSymbol) :=
  match MachineDescription.decodeDescriptionPrefix tokens with
  | none => none
  | some (D, rest) =>
      match MachineDescription.decodeNat rest with
      | none => none
      | some (stage, rest) =>
          match MachineDescription.decodeConfiguration rest with
          | none => none
          | some (config, suffix) => some (D, stage, config, suffix)

theorem decodedBoundedSimulatorTransitionLoopWorkDecode_encodeAppend
    (D : MachineDescription) (stage : Nat)
    (config : MachineDescription.Configuration)
    (suffix : Word MachineCodeSymbol) :
    decodedBoundedSimulatorTransitionLoopWorkDecode
        (decodedBoundedSimulatorTransitionLoopWorkCodeAppend
          D stage config suffix) =
      some (D, stage, config, suffix) := by
  simp [decodedBoundedSimulatorTransitionLoopWorkDecode,
    decodedBoundedSimulatorTransitionLoopWorkCodeAppend,
    MachineDescription.decodeDescriptionPrefix_encodeDescriptionAppend,
    MachineDescription.decodeNat_encodeNatAppend,
    MachineDescription.decodeConfiguration_encodeConfigurationAppend]

theorem decodedBoundedSimulatorTransitionLoopWorkDecode_encode
    (D : MachineDescription) (stage : Nat)
    (config : MachineDescription.Configuration) :
    decodedBoundedSimulatorTransitionLoopWorkDecode
        (decodedBoundedSimulatorTransitionLoopWorkCode
          D stage config) =
      some (D, stage, config, []) := by
  exact
    decodedBoundedSimulatorTransitionLoopWorkDecode_encodeAppend
      D stage config []

theorem decodedBoundedSimulatorTransitionLoopWorkDecode_eq_some_encodeAppend
    {tokens : Word MachineCodeSymbol}
    {D : MachineDescription} {stage : Nat}
    {config : MachineDescription.Configuration}
    {suffix : Word MachineCodeSymbol}
    (hdecode :
      decodedBoundedSimulatorTransitionLoopWorkDecode tokens =
        some (D, stage, config, suffix)) :
    tokens =
      decodedBoundedSimulatorTransitionLoopWorkCodeAppend
        D stage config suffix := by
  unfold decodedBoundedSimulatorTransitionLoopWorkDecode at hdecode
  cases hdescription :
      MachineDescription.decodeDescriptionPrefix tokens with
  | none =>
      simp [hdescription] at hdecode
  | some parsedDescription =>
      rcases parsedDescription with ⟨D', restAfterDescription⟩
      simp [hdescription] at hdecode
      cases hstage :
          MachineDescription.decodeNat restAfterDescription with
      | none =>
          simp [hstage] at hdecode
      | some parsedStage =>
          rcases parsedStage with ⟨stage', restAfterStage⟩
          simp [hstage] at hdecode
          cases hconfig :
              MachineDescription.decodeConfiguration restAfterStage with
          | none =>
              simp [hconfig] at hdecode
          | some parsedConfig =>
              rcases parsedConfig with ⟨config', parsedSuffix⟩
              simp [hconfig] at hdecode
              rcases hdecode with
                ⟨hD, hstageEq, hconfigEq, hsuffixEq⟩
              cases hD
              cases hstageEq
              cases hconfigEq
              cases hsuffixEq
              have htokens :
                  tokens =
                    MachineDescription.encodeDescriptionAppend
                      D restAfterDescription :=
                MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescriptionAppend
                  hdescription
              have hrestAfterDescription :
                  restAfterDescription =
                    MachineDescription.encodeNatAppend
                      stage restAfterStage :=
                MachineDescription.decodeNat_eq_some_encodeNatAppend
                  hstage
              have hrestAfterStage :
                  restAfterStage =
                    MachineDescription.encodeConfigurationAppend
                      config suffix :=
                MachineDescription.decodeConfiguration_eq_some_encodeConfigurationAppend
                  hconfig
              simp [decodedBoundedSimulatorTransitionLoopWorkCodeAppend,
                htokens, hrestAfterDescription, hrestAfterStage]

/--
One semantic work-loop iteration.  It either stops immediately when there is no
remaining stage or no outgoing transition, or advances to the scanned
transition's next configuration with one less remaining stage.
-/
def decodedBoundedSimulatorTransitionLoopStepTarget
    (stage : Nat) (D : MachineDescription)
    (config : MachineDescription.Configuration) :
    Nat × MachineDescription.Configuration :=
  match stage with
  | 0 => (0, config)
  | remaining + 1 =>
      match
        MachineDescription.scanTransitionTable
          config.state (Tape.read config.tape) D.transitions with
      | none => (0, config)
      | some transition =>
          (remaining,
            { state := transition.target
              tape :=
                Tape.move transition.move
                  (Tape.write transition.write config.tape) })

theorem decodedBoundedSimulatorTransitionLoopStepTarget_preserves_final
    (stage : Nat) (D : MachineDescription)
    (config : MachineDescription.Configuration) :
    decodedBoundedSimulatorTransitionLoopFromConfig stage D config =
      decodedBoundedSimulatorTransitionLoopFromConfig
        (decodedBoundedSimulatorTransitionLoopStepTarget
          stage D config).fst
        D
        (decodedBoundedSimulatorTransitionLoopStepTarget
          stage D config).snd := by
  cases stage with
  | zero =>
      simp [decodedBoundedSimulatorTransitionLoopStepTarget,
        decodedBoundedSimulatorTransitionLoopFromConfig]
  | succ remaining =>
      rw [decodedBoundedSimulatorTransitionLoopFromConfig_succ_eq_scan]
      cases hscan :
          MachineDescription.scanTransitionTable
            config.state (Tape.read config.tape) D.transitions
      · simp [decodedBoundedSimulatorTransitionLoopStepTarget, hscan,
          decodedBoundedSimulatorTransitionLoopFromConfig,
          MachineDescription.runConfig]
      · simp [decodedBoundedSimulatorTransitionLoopStepTarget, hscan]

/--
Encoded output payload for one semantic work-loop iteration.
-/
def decodedBoundedSimulatorTransitionLoopWorkStepCodeAppend
    (D : MachineDescription) (stage : Nat)
    (config : MachineDescription.Configuration)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  let target :=
    decodedBoundedSimulatorTransitionLoopStepTarget stage D config
  decodedBoundedSimulatorTransitionLoopWorkCodeAppend
    D target.fst target.snd suffix

theorem decodedBoundedSimulatorTransitionLoopWorkStepDecode_encodeAppend
    (D : MachineDescription) (stage : Nat)
    (config : MachineDescription.Configuration)
    (suffix : Word MachineCodeSymbol) :
    decodedBoundedSimulatorTransitionLoopWorkDecode
        (decodedBoundedSimulatorTransitionLoopWorkStepCodeAppend
          D stage config suffix) =
      some
        (D,
          (decodedBoundedSimulatorTransitionLoopStepTarget
            stage D config).fst,
          (decodedBoundedSimulatorTransitionLoopStepTarget
            stage D config).snd,
          suffix) := by
  simp [decodedBoundedSimulatorTransitionLoopWorkStepCodeAppend,
    decodedBoundedSimulatorTransitionLoopWorkDecode_encodeAppend]

/--
Partial code transform for one semantic work-loop iteration.
-/
def decodedBoundedSimulatorTransitionLoopWorkStepCode
    (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match decodedBoundedSimulatorTransitionLoopWorkDecode tokens with
  | none => none
  | some (D, stage, config, suffix) =>
      some
        (decodedBoundedSimulatorTransitionLoopWorkStepCodeAppend
          D stage config suffix)

theorem decodedBoundedSimulatorTransitionLoopWorkStepCode_encodeAppend
    (D : MachineDescription) (stage : Nat)
    (config : MachineDescription.Configuration)
    (suffix : Word MachineCodeSymbol) :
    decodedBoundedSimulatorTransitionLoopWorkStepCode
        (decodedBoundedSimulatorTransitionLoopWorkCodeAppend
          D stage config suffix) =
      some
        (decodedBoundedSimulatorTransitionLoopWorkStepCodeAppend
          D stage config suffix) := by
  simp [decodedBoundedSimulatorTransitionLoopWorkStepCode,
    decodedBoundedSimulatorTransitionLoopWorkDecode_encodeAppend]

theorem decodedBoundedSimulatorTransitionLoopWorkStepCode_eq_some_iff
    (tokens out : Word MachineCodeSymbol) :
    decodedBoundedSimulatorTransitionLoopWorkStepCode tokens = some out <->
      exists D : MachineDescription,
      exists stage : Nat,
      exists config : MachineDescription.Configuration,
      exists suffix : Word MachineCodeSymbol,
        decodedBoundedSimulatorTransitionLoopWorkDecode tokens =
            some (D, stage, config, suffix) ∧
          out =
            decodedBoundedSimulatorTransitionLoopWorkStepCodeAppend
              D stage config suffix := by
  unfold decodedBoundedSimulatorTransitionLoopWorkStepCode
  cases hdecode :
      decodedBoundedSimulatorTransitionLoopWorkDecode tokens with
  | none =>
      constructor
      · intro h
        cases h
      · intro h
        rcases h with
          ⟨D, stage, config, suffix, hdecode', _hout⟩
        cases hdecode'
  | some parsed =>
      rcases parsed with ⟨D, stage, config, suffix⟩
      constructor
      · intro h
        cases h
        exact ⟨D, stage, config, suffix, rfl, rfl⟩
      · intro h
        rcases h with
          ⟨D', stage', config', suffix', hdecode', hout⟩
        cases hdecode'
        cases hout
        rfl

theorem decodedBoundedSimulatorTransitionLoopWorkStepCode_output_decode_of_decode
    {tokens out : Word MachineCodeSymbol}
    {D : MachineDescription} {stage : Nat}
    {config : MachineDescription.Configuration}
    {suffix : Word MachineCodeSymbol}
    (hdecode :
      decodedBoundedSimulatorTransitionLoopWorkDecode tokens =
        some (D, stage, config, suffix))
    (hstep :
      decodedBoundedSimulatorTransitionLoopWorkStepCode tokens = some out) :
    decodedBoundedSimulatorTransitionLoopWorkDecode out =
      some
        (D,
          (decodedBoundedSimulatorTransitionLoopStepTarget
            stage D config).fst,
          (decodedBoundedSimulatorTransitionLoopStepTarget
            stage D config).snd,
          suffix) := by
  unfold decodedBoundedSimulatorTransitionLoopWorkStepCode at hstep
  simp [hdecode] at hstep
  subst out
  exact
    decodedBoundedSimulatorTransitionLoopWorkStepDecode_encodeAppend
      D stage config suffix

theorem decodedBoundedSimulatorTransitionLoopWorkStepCode_preserves_final_of_decode
    {tokens out : Word MachineCodeSymbol}
    {D : MachineDescription} {stage : Nat}
    {config : MachineDescription.Configuration}
    {suffix : Word MachineCodeSymbol}
    (hdecode :
      decodedBoundedSimulatorTransitionLoopWorkDecode tokens =
        some (D, stage, config, suffix))
    (hstep :
      decodedBoundedSimulatorTransitionLoopWorkStepCode tokens = some out) :
    exists nextStage : Nat,
    exists nextConfig : MachineDescription.Configuration,
      decodedBoundedSimulatorTransitionLoopWorkDecode out =
        some (D, nextStage, nextConfig, suffix) ∧
        decodedBoundedSimulatorTransitionLoopFromConfig stage D config =
          decodedBoundedSimulatorTransitionLoopFromConfig
            nextStage D nextConfig := by
  refine
    ⟨(decodedBoundedSimulatorTransitionLoopStepTarget
        stage D config).fst,
      (decodedBoundedSimulatorTransitionLoopStepTarget
        stage D config).snd,
      ?_, ?_⟩
  · exact
      decodedBoundedSimulatorTransitionLoopWorkStepCode_output_decode_of_decode
        hdecode hstep
  · exact
      decodedBoundedSimulatorTransitionLoopStepTarget_preserves_final
        stage D config

/--
Repeated semantic work-loop iterations.
-/
def decodedBoundedSimulatorTransitionLoopIterateStepTarget :
    Nat -> MachineDescription -> Nat ->
      MachineDescription.Configuration ->
      Nat × MachineDescription.Configuration
  | 0, _D, stage, config => (stage, config)
  | fuel + 1, D, stage, config =>
      let target :=
        decodedBoundedSimulatorTransitionLoopStepTarget stage D config
      decodedBoundedSimulatorTransitionLoopIterateStepTarget
        fuel D target.fst target.snd

def decodedBoundedSimulatorTransitionLoopIterateWorkStepCode :
    Nat -> Word MachineCodeSymbol -> Option (Word MachineCodeSymbol)
  | 0, tokens => some tokens
  | fuel + 1, tokens =>
      match decodedBoundedSimulatorTransitionLoopWorkStepCode tokens with
      | none => none
      | some next =>
          decodedBoundedSimulatorTransitionLoopIterateWorkStepCode
            fuel next

theorem decodedBoundedSimulatorTransitionLoopIterateWorkStepCode_encodeAppend
    (fuel : Nat) (D : MachineDescription) (stage : Nat)
    (config : MachineDescription.Configuration)
    (suffix : Word MachineCodeSymbol) :
    decodedBoundedSimulatorTransitionLoopIterateWorkStepCode fuel
        (decodedBoundedSimulatorTransitionLoopWorkCodeAppend
          D stage config suffix) =
      some
        (decodedBoundedSimulatorTransitionLoopWorkCodeAppend
          D
          (decodedBoundedSimulatorTransitionLoopIterateStepTarget
            fuel D stage config).fst
          (decodedBoundedSimulatorTransitionLoopIterateStepTarget
            fuel D stage config).snd
          suffix) := by
  induction fuel generalizing stage config with
  | zero =>
      rfl
  | succ fuel ih =>
      simp [decodedBoundedSimulatorTransitionLoopIterateWorkStepCode,
        decodedBoundedSimulatorTransitionLoopIterateStepTarget,
        decodedBoundedSimulatorTransitionLoopWorkStepCode_encodeAppend,
        decodedBoundedSimulatorTransitionLoopWorkStepCodeAppend, ih]

theorem decodedBoundedSimulatorTransitionLoopIterateWorkStepCode_encode
    (fuel : Nat) (D : MachineDescription) (stage : Nat)
    (config : MachineDescription.Configuration) :
    decodedBoundedSimulatorTransitionLoopIterateWorkStepCode fuel
        (decodedBoundedSimulatorTransitionLoopWorkCode D stage config) =
      some
        (decodedBoundedSimulatorTransitionLoopWorkCode
          D
          (decodedBoundedSimulatorTransitionLoopIterateStepTarget
            fuel D stage config).fst
          (decodedBoundedSimulatorTransitionLoopIterateStepTarget
            fuel D stage config).snd) := by
  simpa [decodedBoundedSimulatorTransitionLoopWorkCode] using
    decodedBoundedSimulatorTransitionLoopIterateWorkStepCode_encodeAppend
      fuel D stage config []

theorem decodedBoundedSimulatorTransitionLoopIterateWorkStepCode_output_decode_of_decode
    {tokens out : Word MachineCodeSymbol}
    {D : MachineDescription} {stage : Nat}
    {config : MachineDescription.Configuration}
    {suffix : Word MachineCodeSymbol}
    (fuel : Nat)
    (hdecode :
      decodedBoundedSimulatorTransitionLoopWorkDecode tokens =
        some (D, stage, config, suffix))
    (hiter :
      decodedBoundedSimulatorTransitionLoopIterateWorkStepCode fuel tokens =
        some out) :
    decodedBoundedSimulatorTransitionLoopWorkDecode out =
      some
        (D,
          (decodedBoundedSimulatorTransitionLoopIterateStepTarget
            fuel D stage config).fst,
          (decodedBoundedSimulatorTransitionLoopIterateStepTarget
            fuel D stage config).snd,
          suffix) := by
  induction fuel generalizing tokens out D stage config suffix with
  | zero =>
      simp [decodedBoundedSimulatorTransitionLoopIterateWorkStepCode] at hiter
      subst out
      simpa [decodedBoundedSimulatorTransitionLoopIterateStepTarget] using
        hdecode
  | succ fuel ih =>
      simp [decodedBoundedSimulatorTransitionLoopIterateWorkStepCode] at hiter
      cases hstep :
          decodedBoundedSimulatorTransitionLoopWorkStepCode tokens with
      | none =>
          simp [hstep] at hiter
      | some mid =>
          simp [hstep] at hiter
          have hmidDecode :
              decodedBoundedSimulatorTransitionLoopWorkDecode mid =
                some
                  (D,
                    (decodedBoundedSimulatorTransitionLoopStepTarget
                      stage D config).fst,
                    (decodedBoundedSimulatorTransitionLoopStepTarget
                      stage D config).snd,
                    suffix) :=
            decodedBoundedSimulatorTransitionLoopWorkStepCode_output_decode_of_decode
              hdecode hstep
          have hfinal := ih hmidDecode hiter
          simpa [decodedBoundedSimulatorTransitionLoopIterateStepTarget] using
            hfinal

theorem decodedBoundedSimulatorTransitionLoopIterateWorkStepCode_preserves_final_of_decode
    {tokens out : Word MachineCodeSymbol}
    {D : MachineDescription} {stage : Nat}
    {config : MachineDescription.Configuration}
    {suffix : Word MachineCodeSymbol}
    (fuel : Nat)
    (hdecode :
      decodedBoundedSimulatorTransitionLoopWorkDecode tokens =
        some (D, stage, config, suffix))
    (hiter :
      decodedBoundedSimulatorTransitionLoopIterateWorkStepCode fuel tokens =
        some out) :
    exists nextStage : Nat,
    exists nextConfig : MachineDescription.Configuration,
      decodedBoundedSimulatorTransitionLoopWorkDecode out =
        some (D, nextStage, nextConfig, suffix) ∧
        decodedBoundedSimulatorTransitionLoopFromConfig stage D config =
          decodedBoundedSimulatorTransitionLoopFromConfig
            nextStage D nextConfig := by
  induction fuel generalizing tokens out D stage config suffix with
  | zero =>
      simp [decodedBoundedSimulatorTransitionLoopIterateWorkStepCode] at hiter
      subst out
      exact ⟨stage, config, hdecode, rfl⟩
  | succ fuel ih =>
      simp [decodedBoundedSimulatorTransitionLoopIterateWorkStepCode] at hiter
      cases hstep :
          decodedBoundedSimulatorTransitionLoopWorkStepCode tokens with
      | none =>
          simp [hstep] at hiter
      | some mid =>
          simp [hstep] at hiter
          rcases
              decodedBoundedSimulatorTransitionLoopWorkStepCode_preserves_final_of_decode
                hdecode hstep with
            ⟨nextStage, nextConfig, hmidDecode, hpresStep⟩
          rcases ih hmidDecode hiter with
            ⟨finalStage, finalConfig, hfinalDecode, hpresTail⟩
          exact
            ⟨finalStage, finalConfig, hfinalDecode,
              hpresStep.trans hpresTail⟩

theorem decodedBoundedSimulatorTransitionLoopIterateStepTarget_preserves_final
    (fuel stage : Nat) (D : MachineDescription)
    (config : MachineDescription.Configuration) :
    decodedBoundedSimulatorTransitionLoopFromConfig stage D config =
      decodedBoundedSimulatorTransitionLoopFromConfig
        (decodedBoundedSimulatorTransitionLoopIterateStepTarget
          fuel D stage config).fst
        D
        (decodedBoundedSimulatorTransitionLoopIterateStepTarget
          fuel D stage config).snd := by
  induction fuel generalizing stage config with
  | zero =>
      rfl
  | succ fuel ih =>
      simp [decodedBoundedSimulatorTransitionLoopIterateStepTarget]
      rw [decodedBoundedSimulatorTransitionLoopStepTarget_preserves_final]
      exact ih
        (decodedBoundedSimulatorTransitionLoopStepTarget
          stage D config).fst
        (decodedBoundedSimulatorTransitionLoopStepTarget
          stage D config).snd

theorem decodedBoundedSimulatorTransitionLoopIterateStepTarget_zero_fst
    (fuel : Nat) (D : MachineDescription)
    (config : MachineDescription.Configuration) :
    (decodedBoundedSimulatorTransitionLoopIterateStepTarget
      fuel D 0 config).fst = 0 := by
  induction fuel generalizing config with
  | zero =>
      rfl
  | succ fuel ih =>
      simp [decodedBoundedSimulatorTransitionLoopIterateStepTarget,
        decodedBoundedSimulatorTransitionLoopStepTarget, ih]

theorem decodedBoundedSimulatorTransitionLoopIterateStepTarget_self_fst
    (stage : Nat) (D : MachineDescription)
    (config : MachineDescription.Configuration) :
    (decodedBoundedSimulatorTransitionLoopIterateStepTarget
      stage D stage config).fst = 0 := by
  induction stage generalizing config with
  | zero =>
      rfl
  | succ remaining ih =>
      simp [decodedBoundedSimulatorTransitionLoopIterateStepTarget]
      cases hscan :
          MachineDescription.scanTransitionTable
            config.state (Tape.read config.tape) D.transitions
      · simp [decodedBoundedSimulatorTransitionLoopStepTarget, hscan,
          decodedBoundedSimulatorTransitionLoopIterateStepTarget_zero_fst]
      · simp [decodedBoundedSimulatorTransitionLoopStepTarget, hscan, ih]

theorem decodedBoundedSimulatorTransitionLoopIterateWorkStepCode_self_output_decode_of_decode
    {tokens out : Word MachineCodeSymbol}
    {D : MachineDescription} {stage : Nat}
    {config : MachineDescription.Configuration}
    {suffix : Word MachineCodeSymbol}
    (hdecode :
      decodedBoundedSimulatorTransitionLoopWorkDecode tokens =
        some (D, stage, config, suffix))
    (hiter :
      decodedBoundedSimulatorTransitionLoopIterateWorkStepCode stage tokens =
        some out) :
    exists finalConfig : MachineDescription.Configuration,
      decodedBoundedSimulatorTransitionLoopWorkDecode out =
        some (D, 0, finalConfig, suffix) ∧
        decodedBoundedSimulatorTransitionLoopFromConfig stage D config =
          decodedBoundedSimulatorTransitionLoopFromConfig
            0 D finalConfig := by
  let target :=
    decodedBoundedSimulatorTransitionLoopIterateStepTarget
      stage D stage config
  have hdecodeOut :
      decodedBoundedSimulatorTransitionLoopWorkDecode out =
        some (D, target.fst, target.snd, suffix) := by
    simpa [target] using
      decodedBoundedSimulatorTransitionLoopIterateWorkStepCode_output_decode_of_decode
        stage hdecode hiter
  have hzero : target.fst = 0 := by
    simpa [target] using
      decodedBoundedSimulatorTransitionLoopIterateStepTarget_self_fst
        stage D config
  have hpres :
      decodedBoundedSimulatorTransitionLoopFromConfig stage D config =
        decodedBoundedSimulatorTransitionLoopFromConfig
          target.fst D target.snd := by
    simpa [target] using
      decodedBoundedSimulatorTransitionLoopIterateStepTarget_preserves_final
        stage stage D config
  refine ⟨target.snd, ?_, ?_⟩
  · simpa [hzero] using hdecodeOut
  · simpa [hzero] using hpres

/--
Initial transition-loop work payload for a normalized decoded-simulator source.
-/
def decodedBoundedSimulatorInitialWorkCode
    (stage : Nat) (D : MachineDescription)
    (input : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  decodedBoundedSimulatorTransitionLoopWorkCode
    D stage
    (D.initial (MachineDescription.encodeCodeWordAsInput input))

theorem decodedBoundedSimulatorInitialWorkCode_decode
    (stage : Nat) (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    decodedBoundedSimulatorTransitionLoopWorkDecode
        (decodedBoundedSimulatorInitialWorkCode stage D input) =
      some
        (D, stage,
          D.initial (MachineDescription.encodeCodeWordAsInput input),
          []) := by
  simp [decodedBoundedSimulatorInitialWorkCode,
    decodedBoundedSimulatorTransitionLoopWorkCode,
    decodedBoundedSimulatorTransitionLoopWorkDecode_encodeAppend]
  rfl

/--
Semantic initial handoff from a normalized source word into loop work code.
-/
def decodedBoundedSimulatorInitialWorkCodeTransform
    (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match MachineDescription.decodeNat tokens with
  | none => none
  | some (stage, encoded) =>
      match MachineDescription.decodeDescriptionPrefix encoded with
      | none => none
      | some (D, input) =>
          some (decodedBoundedSimulatorInitialWorkCode stage D input)

theorem decodedBoundedSimulatorInitialWorkCodeTransform_normalizedInput
    (stage : Nat) (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    decodedBoundedSimulatorInitialWorkCodeTransform
        (decodedBoundedSimulatorNormalizedInput stage D input) =
      some (decodedBoundedSimulatorInitialWorkCode stage D input) := by
  unfold decodedBoundedSimulatorInitialWorkCodeTransform
  rw [decodedBoundedSimulatorNormalizedInput_decodeNat]
  simp only
  cases hdecode :
      MachineDescription.decodeDescriptionPrefix
        (List.append (MachineDescription.encodeDescription D) input) with
  | none =>
      have hcanonical :
          MachineDescription.decodeDescriptionPrefix
              (List.append (MachineDescription.encodeDescription D) input) =
            some (D, input) :=
        MachineDescription.decodeDescriptionPrefix_encodeDescription_append
          D input
      rw [hdecode] at hcanonical
      cases hcanonical
  | some decoded =>
      rcases decoded with ⟨decodedD, decodedInput⟩
      have hcanonical :
          MachineDescription.decodeDescriptionPrefix
              (List.append (MachineDescription.encodeDescription D) input) =
            some (D, input) :=
        MachineDescription.decodeDescriptionPrefix_encodeDescription_append
          D input
      rw [hdecode] at hcanonical
      cases hcanonical
      rfl

theorem decodedBoundedSimulatorInitialWorkCodeTransform_eq_some_iff
    (tokens work : Word MachineCodeSymbol) :
    decodedBoundedSimulatorInitialWorkCodeTransform tokens = some work <->
      exists stage : Nat,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens =
            some (stage,
              List.append (MachineDescription.encodeDescription D) input) ∧
          work = decodedBoundedSimulatorInitialWorkCode stage D input := by
  unfold decodedBoundedSimulatorInitialWorkCodeTransform
  constructor
  · intro h
    cases hstage : MachineDescription.decodeNat tokens with
    | none =>
        simp [hstage] at h
    | some parsed =>
        rcases parsed with ⟨stage, encoded⟩
        simp [hstage] at h
        cases hdecode : MachineDescription.decodeDescriptionPrefix encoded with
        | none =>
            simp [hdecode] at h
        | some decoded =>
            rcases decoded with ⟨D, input⟩
            simp [hdecode] at h
            have hencoded :
                encoded =
                  List.append (MachineDescription.encodeDescription D) input :=
              MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescription_append
                hdecode
            refine ⟨stage, D, input, ?_, ?_⟩
            · exact congrArg (fun tail => some (stage, tail)) hencoded
            · exact h.symm
  · intro h
    rcases h with ⟨stage, D, input, hstage, hwork⟩
    simp [hstage, hwork]
    have hcanonical :
        MachineDescription.decodeDescriptionPrefix
            (List.append (MachineDescription.encodeDescription D) input) =
          some (D, input) :=
      MachineDescription.decodeDescriptionPrefix_encodeDescription_append
        D input
    cases hdecode :
        MachineDescription.decodeDescriptionPrefix
          (List.append (MachineDescription.encodeDescription D) input) with
    | none =>
        rw [hdecode] at hcanonical
        cases hcanonical
    | some decoded =>
        rcases decoded with ⟨decodedD, decodedInput⟩
        rw [hdecode] at hcanonical
        cases hcanonical
        rfl

theorem decodedBoundedSimulatorTransitionLoopConfig_eq_initialWork
    (stage : Nat) (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    decodedBoundedSimulatorTransitionLoopConfig stage D input =
      decodedBoundedSimulatorTransitionLoopFromConfig stage D
        (D.initial (MachineDescription.encodeCodeWordAsInput input)) :=
  rfl

/--
Final accept transform for completed transition-loop work code.
-/
def decodedBoundedSimulatorTransitionLoopFinalAcceptCode
    (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match decodedBoundedSimulatorTransitionLoopWorkDecode tokens with
  | none => none
  | some (D, stage, config, suffix) =>
      match stage, suffix with
      | 0, [] =>
          if config.state = D.halt then some ([] : Word MachineCodeSymbol)
          else none
      | _, _ => none

theorem decodedBoundedSimulatorTransitionLoopFinalAcceptCode_encode_zero_iff
    (D : MachineDescription)
    (config : MachineDescription.Configuration) :
    decodedBoundedSimulatorTransitionLoopFinalAcceptCode
        (decodedBoundedSimulatorTransitionLoopWorkCode D 0 config) =
        some ([] : Word MachineCodeSymbol) <->
      config.state = D.halt := by
  unfold decodedBoundedSimulatorTransitionLoopFinalAcceptCode
  rw [decodedBoundedSimulatorTransitionLoopWorkDecode_encode]
  change (if config.state = D.halt then some ([] : Word MachineCodeSymbol)
      else none) = some ([] : Word MachineCodeSymbol) <->
    config.state = D.halt
  by_cases hhalt : config.state = D.halt
  · rw [if_pos hhalt]
    constructor
    · intro _
      exact hhalt
    · intro _
      rfl
  · rw [if_neg hhalt]
    constructor
    · intro h
      cases h
    · intro h
      exact False.elim (hhalt h)

theorem decodedBoundedSimulatorTransitionLoopFinalAcceptCode_of_decode_zero_iff
    {tokens : Word MachineCodeSymbol}
    {D : MachineDescription}
    {config : MachineDescription.Configuration}
    (hdecode :
      decodedBoundedSimulatorTransitionLoopWorkDecode tokens =
        some (D, 0, config, [])) :
    decodedBoundedSimulatorTransitionLoopFinalAcceptCode tokens =
        some ([] : Word MachineCodeSymbol) <->
      config.state = D.halt := by
  unfold decodedBoundedSimulatorTransitionLoopFinalAcceptCode
  rw [hdecode]
  change (if config.state = D.halt then some ([] : Word MachineCodeSymbol)
      else none) = some ([] : Word MachineCodeSymbol) <->
    config.state = D.halt
  by_cases hhalt : config.state = D.halt
  · simp [hhalt]
  · simp [hhalt]

theorem decodedBoundedSimulatorTransitionLoopFromConfig_zero_state_iff
    (D : MachineDescription)
    (config : MachineDescription.Configuration) :
    (decodedBoundedSimulatorTransitionLoopFromConfig 0 D config).state =
        D.halt <->
      config.state = D.halt := by
  rfl

theorem decodedBoundedSimulatorTransitionLoopFinalAcceptCode_encode_zero_iff_loop
    (D : MachineDescription)
    (config : MachineDescription.Configuration) :
    decodedBoundedSimulatorTransitionLoopFinalAcceptCode
        (decodedBoundedSimulatorTransitionLoopWorkCode D 0 config) =
        some ([] : Word MachineCodeSymbol) <->
      (decodedBoundedSimulatorTransitionLoopFromConfig 0 D config).state =
        D.halt := by
  simpa [decodedBoundedSimulatorTransitionLoopFromConfig] using!
    decodedBoundedSimulatorTransitionLoopFinalAcceptCode_encode_zero_iff
      D config

theorem decodedBoundedSimulatorTransitionLoopFinalAcceptCode_iterate_self_iff
    (stage : Nat) (D : MachineDescription)
    (config : MachineDescription.Configuration) :
    decodedBoundedSimulatorTransitionLoopFinalAcceptCode
        (decodedBoundedSimulatorTransitionLoopWorkCode D
          (decodedBoundedSimulatorTransitionLoopIterateStepTarget
            stage D stage config).fst
          (decodedBoundedSimulatorTransitionLoopIterateStepTarget
            stage D stage config).snd) =
        some ([] : Word MachineCodeSymbol) <->
      (decodedBoundedSimulatorTransitionLoopFromConfig
        stage D config).state = D.halt := by
  let target :=
    decodedBoundedSimulatorTransitionLoopIterateStepTarget
      stage D stage config
  change
    decodedBoundedSimulatorTransitionLoopFinalAcceptCode
        (decodedBoundedSimulatorTransitionLoopWorkCode
          D target.fst target.snd) =
        some ([] : Word MachineCodeSymbol) <->
      (decodedBoundedSimulatorTransitionLoopFromConfig
        stage D config).state = D.halt
  have hzero : target.fst = 0 := by
    simpa [target] using
      decodedBoundedSimulatorTransitionLoopIterateStepTarget_self_fst
        stage D config
  have hpres :
      decodedBoundedSimulatorTransitionLoopFromConfig stage D config =
        decodedBoundedSimulatorTransitionLoopFromConfig
          target.fst D target.snd := by
    simpa [target] using
      decodedBoundedSimulatorTransitionLoopIterateStepTarget_preserves_final
        stage stage D config
  rw [hpres, hzero]
  exact
    decodedBoundedSimulatorTransitionLoopFinalAcceptCode_encode_zero_iff_loop
      D target.snd

theorem decodedBoundedSimulatorTransitionLoopFinalAcceptCode_iterate_self_output_iff_of_decode
    {tokens out : Word MachineCodeSymbol}
    {D : MachineDescription} {stage : Nat}
    {config : MachineDescription.Configuration}
    (hdecode :
      decodedBoundedSimulatorTransitionLoopWorkDecode tokens =
        some (D, stage, config, []))
    (hiter :
      decodedBoundedSimulatorTransitionLoopIterateWorkStepCode stage tokens =
        some out) :
    decodedBoundedSimulatorTransitionLoopFinalAcceptCode out =
        some ([] : Word MachineCodeSymbol) <->
      (decodedBoundedSimulatorTransitionLoopFromConfig
        stage D config).state = D.halt := by
  rcases
      decodedBoundedSimulatorTransitionLoopIterateWorkStepCode_self_output_decode_of_decode
        hdecode hiter with
    ⟨finalConfig, hfinalDecode, hpres⟩
  rw [hpres]
  simpa [decodedBoundedSimulatorTransitionLoopFromConfig,
    MachineDescription.runConfig] using!
    decodedBoundedSimulatorTransitionLoopFinalAcceptCode_of_decode_zero_iff
      hfinalDecode

/--
Complete work payload after semantically iterating the transition loop.
-/
def decodedBoundedSimulatorTransitionLoopIteratedWorkCode
    (D : MachineDescription) (stage : Nat)
    (config : MachineDescription.Configuration) :
    Word MachineCodeSymbol :=
  let target :=
    decodedBoundedSimulatorTransitionLoopIterateStepTarget
      stage D stage config
  decodedBoundedSimulatorTransitionLoopWorkCode
    D target.fst target.snd

theorem decodedBoundedSimulatorTransitionLoopIterateWorkStepCode_initial
    (stage : Nat) (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    decodedBoundedSimulatorTransitionLoopIterateWorkStepCode stage
        (decodedBoundedSimulatorInitialWorkCode stage D input) =
      some
        (decodedBoundedSimulatorTransitionLoopIteratedWorkCode
          D stage
          (D.initial
            (MachineDescription.encodeCodeWordAsInput input))) := by
  simpa [decodedBoundedSimulatorInitialWorkCode,
    decodedBoundedSimulatorTransitionLoopIteratedWorkCode] using
    decodedBoundedSimulatorTransitionLoopIterateWorkStepCode_encode
      stage D stage
      (D.initial (MachineDescription.encodeCodeWordAsInput input))

/--
Semantic code transform for the whole normalized transition-loop pipeline.
-/
def decodedBoundedSimulatorTransitionLoopPipelineCode
    (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match decodedBoundedSimulatorInitialWorkCodeTransform tokens with
  | none => none
  | some work =>
      match decodedBoundedSimulatorTransitionLoopWorkDecode work with
      | some (D, stage, config, []) =>
          decodedBoundedSimulatorTransitionLoopFinalAcceptCode
            (decodedBoundedSimulatorTransitionLoopIteratedWorkCode
              D stage config)
      | _ => none

def decodedBoundedSimulatorTransitionLoopPipelineIterateCode
    (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match decodedBoundedSimulatorInitialWorkCodeTransform tokens with
  | none => none
  | some work =>
      match decodedBoundedSimulatorTransitionLoopWorkDecode work with
      | some (_D, stage, _config, []) =>
          match
            decodedBoundedSimulatorTransitionLoopIterateWorkStepCode
              stage work with
          | none => none
          | some finalWork =>
              decodedBoundedSimulatorTransitionLoopFinalAcceptCode
                finalWork
      | _ => none

theorem decodedBoundedSimulatorTransitionLoopPipelineIterateCode_eq_some_nil_iff_parts
    (tokens : Word MachineCodeSymbol) :
    decodedBoundedSimulatorTransitionLoopPipelineIterateCode tokens =
        some ([] : Word MachineCodeSymbol) <->
      exists work : Word MachineCodeSymbol,
      exists D : MachineDescription,
      exists stage : Nat,
      exists config : MachineDescription.Configuration,
      exists finalWork : Word MachineCodeSymbol,
        decodedBoundedSimulatorInitialWorkCodeTransform tokens =
            some work ∧
          decodedBoundedSimulatorTransitionLoopWorkDecode work =
            some (D, stage, config, []) ∧
          decodedBoundedSimulatorTransitionLoopIterateWorkStepCode
              stage work = some finalWork ∧
          decodedBoundedSimulatorTransitionLoopFinalAcceptCode finalWork =
            some ([] : Word MachineCodeSymbol) := by
  unfold decodedBoundedSimulatorTransitionLoopPipelineIterateCode
  constructor
  · intro h
    cases hinit :
        decodedBoundedSimulatorInitialWorkCodeTransform tokens with
    | none =>
        simp [hinit] at h
    | some work =>
        simp [hinit] at h
        cases hdecode :
            decodedBoundedSimulatorTransitionLoopWorkDecode work with
        | none =>
            simp [hdecode] at h
        | some parsed =>
            rcases parsed with ⟨D, stage, config, suffix⟩
            cases suffix with
            | nil =>
                simp [hdecode] at h
                cases hiter :
                    decodedBoundedSimulatorTransitionLoopIterateWorkStepCode
                      stage work with
                | none =>
                    simp [hiter] at h
                | some finalWork =>
                    simp [hiter] at h
                    exact
                      ⟨work, D, stage, config, finalWork,
                        rfl, hdecode, hiter, h⟩
            | cons _ _ =>
                simp [hdecode] at h
  · intro h
    rcases h with
      ⟨work, D, stage, config, finalWork,
        hinit, hdecode, hiter, hfinal⟩
    simp [hinit, hdecode, hiter, hfinal]

theorem decodedBoundedSimulatorTransitionLoopPipelineIterateCode_eq_some_nil_iff_initial_parts
    (tokens : Word MachineCodeSymbol) :
    decodedBoundedSimulatorTransitionLoopPipelineIterateCode tokens =
        some ([] : Word MachineCodeSymbol) <->
      exists stage : Nat,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
      exists finalWork : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens =
            some (stage,
              List.append (MachineDescription.encodeDescription D) input) ∧
          decodedBoundedSimulatorTransitionLoopIterateWorkStepCode stage
              (decodedBoundedSimulatorInitialWorkCode stage D input) =
            some finalWork ∧
          decodedBoundedSimulatorTransitionLoopFinalAcceptCode finalWork =
            some ([] : Word MachineCodeSymbol) := by
  constructor
  · intro h
    rcases
        (decodedBoundedSimulatorTransitionLoopPipelineIterateCode_eq_some_nil_iff_parts
          tokens).mp h with
      ⟨work, parsedD, parsedStage, config, finalWork,
        hinit, hworkDecode, hiter, hfinal⟩
    rcases
        (decodedBoundedSimulatorInitialWorkCodeTransform_eq_some_iff
          tokens work).mp hinit with
      ⟨stage, D, input, hstage, hwork⟩
    rw [hwork, decodedBoundedSimulatorInitialWorkCode_decode] at hworkDecode
    cases hworkDecode
    exact
      ⟨parsedStage, parsedD, input, finalWork, hstage,
        by simpa [hwork] using hiter, hfinal⟩
  · intro h
    rcases h with
      ⟨stage, D, input, finalWork, hstage, hiter, hfinal⟩
    apply
      (decodedBoundedSimulatorTransitionLoopPipelineIterateCode_eq_some_nil_iff_parts
        tokens).mpr
    refine
      ⟨decodedBoundedSimulatorInitialWorkCode stage D input,
        D, stage,
        D.initial (MachineDescription.encodeCodeWordAsInput input),
        finalWork, ?_, ?_, hiter, hfinal⟩
    · exact
        (decodedBoundedSimulatorInitialWorkCodeTransform_eq_some_iff
          tokens
          (decodedBoundedSimulatorInitialWorkCode stage D input)).mpr
          ⟨stage, D, input, hstage, rfl⟩
    · exact decodedBoundedSimulatorInitialWorkCode_decode stage D input

theorem decodedBoundedSimulatorTransitionLoopPipelineIterateCode_eq_some_nil_iff_initial_halt
    (tokens : Word MachineCodeSymbol) :
    decodedBoundedSimulatorTransitionLoopPipelineIterateCode tokens =
        some ([] : Word MachineCodeSymbol) <->
      exists stage : Nat,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens =
            some (stage,
              List.append (MachineDescription.encodeDescription D) input) ∧
          (decodedBoundedSimulatorTransitionLoopFromConfig stage D
            (D.initial
              (MachineDescription.encodeCodeWordAsInput input))).state =
            D.halt := by
  constructor
  · intro h
    rcases
        (decodedBoundedSimulatorTransitionLoopPipelineIterateCode_eq_some_nil_iff_initial_parts
          tokens).mp h with
      ⟨stage, D, input, finalWork, hstage, hiter, hfinal⟩
    have hdecode :=
      decodedBoundedSimulatorInitialWorkCode_decode stage D input
    have hhalt :
        (decodedBoundedSimulatorTransitionLoopFromConfig stage D
          (D.initial
            (MachineDescription.encodeCodeWordAsInput input))).state =
          D.halt :=
      (decodedBoundedSimulatorTransitionLoopFinalAcceptCode_iterate_self_output_iff_of_decode
        hdecode hiter).mp hfinal
    exact ⟨stage, D, input, hstage, hhalt⟩
  · intro h
    rcases h with ⟨stage, D, input, hstage, hhalt⟩
    apply
      (decodedBoundedSimulatorTransitionLoopPipelineIterateCode_eq_some_nil_iff_initial_parts
        tokens).mpr
    refine
      ⟨stage, D, input,
        decodedBoundedSimulatorTransitionLoopIteratedWorkCode D stage
          (D.initial
            (MachineDescription.encodeCodeWordAsInput input)),
        hstage, ?_, ?_⟩
    · exact
        decodedBoundedSimulatorTransitionLoopIterateWorkStepCode_initial
          stage D input
    · exact
        (decodedBoundedSimulatorTransitionLoopFinalAcceptCode_iterate_self_iff
          stage D
          (D.initial
            (MachineDescription.encodeCodeWordAsInput input))).mpr
          hhalt

theorem decodedBoundedSimulatorTransitionLoopPipelineIterateCode_eq_pipelineCode
    (tokens : Word MachineCodeSymbol) :
    decodedBoundedSimulatorTransitionLoopPipelineIterateCode tokens =
      decodedBoundedSimulatorTransitionLoopPipelineCode tokens := by
  unfold decodedBoundedSimulatorTransitionLoopPipelineIterateCode
  unfold decodedBoundedSimulatorTransitionLoopPipelineCode
  cases hinit :
      decodedBoundedSimulatorInitialWorkCodeTransform tokens with
  | none =>
      rfl
  | some work =>
      cases hdecode :
          decodedBoundedSimulatorTransitionLoopWorkDecode work with
      | none =>
          simp [hdecode]
      | some parsed =>
          rcases parsed with ⟨D, stage, config, suffix⟩
          cases suffix with
          | nil =>
              have hwork :
                  work =
                    decodedBoundedSimulatorTransitionLoopWorkCode
                      D stage config := by
                simpa [decodedBoundedSimulatorTransitionLoopWorkCode] using
                  decodedBoundedSimulatorTransitionLoopWorkDecode_eq_some_encodeAppend
                    hdecode
              subst work
              simp [
                decodedBoundedSimulatorTransitionLoopWorkDecode_encode,
                decodedBoundedSimulatorTransitionLoopIterateWorkStepCode_encode,
                decodedBoundedSimulatorTransitionLoopIteratedWorkCode]
          | cons _ _ =>
              simp [hdecode]

theorem decodedBoundedSimulatorTransitionLoopPipelineCode_normalizedInput_iff
    (stage : Nat) (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    decodedBoundedSimulatorTransitionLoopPipelineCode
        (decodedBoundedSimulatorNormalizedInput stage D input) =
        some ([] : Word MachineCodeSymbol) <->
      (decodedBoundedSimulatorTransitionLoopConfig stage D input).state =
        D.halt := by
  simp [decodedBoundedSimulatorTransitionLoopPipelineCode,
    decodedBoundedSimulatorInitialWorkCodeTransform_normalizedInput,
    decodedBoundedSimulatorInitialWorkCode_decode,
    decodedBoundedSimulatorTransitionLoopIteratedWorkCode,
    decodedBoundedSimulatorTransitionLoopConfig,
    decodedBoundedSimulatorTransitionLoopFinalAcceptCode_iterate_self_iff]

theorem decodedBoundedSimulatorTransitionLoopPipelineCode_eq_some_nil_iff
    (tokens : Word MachineCodeSymbol) :
    decodedBoundedSimulatorTransitionLoopPipelineCode tokens =
        some ([] : Word MachineCodeSymbol) <->
      exists stage : Nat,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens =
            some (stage,
              List.append (MachineDescription.encodeDescription D) input) ∧
          (decodedBoundedSimulatorTransitionLoopConfig
            stage D input).state = D.halt := by
  constructor
  · intro hpipeline
    unfold decodedBoundedSimulatorTransitionLoopPipelineCode at hpipeline
    unfold decodedBoundedSimulatorInitialWorkCodeTransform at hpipeline
    cases hstage : MachineDescription.decodeNat tokens with
    | none =>
        simp [hstage] at hpipeline
    | some parsedStage =>
        rcases parsedStage with ⟨stage, encoded⟩
        simp [hstage] at hpipeline
        cases hdescription :
            MachineDescription.decodeDescriptionPrefix encoded with
        | none =>
            simp [hdescription] at hpipeline
        | some parsedDescription =>
            rcases parsedDescription with ⟨D, input⟩
            simp [hdescription,
              decodedBoundedSimulatorInitialWorkCode_decode,
              decodedBoundedSimulatorTransitionLoopIteratedWorkCode]
              at hpipeline
            have hencoded :
                encoded =
                  List.append (MachineDescription.encodeDescription D)
                    input :=
              MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescription_append
                hdescription
            have hdecode :
                some (stage, encoded) =
                  some (stage,
                    List.append (MachineDescription.encodeDescription D)
                      input) := by
              rw [hencoded]
              rfl
            have hhalt :
                (decodedBoundedSimulatorTransitionLoopConfig
                  stage D input).state = D.halt := by
              exact
                (decodedBoundedSimulatorTransitionLoopFinalAcceptCode_iterate_self_iff
                  stage D
                  (D.initial
                    (MachineDescription.encodeCodeWordAsInput input))).mp
                  hpipeline
            exact ⟨stage, D, input, hdecode, hhalt⟩
  · intro h
    rcases h with ⟨stage, D, input, hdecode, hhalt⟩
    have htokens :
        tokens = decodedBoundedSimulatorNormalizedInput stage D input := by
      exact
        MachineDescription.decodeNat_eq_some_encodeNatAppend hdecode
    rw [htokens]
    exact
      (decodedBoundedSimulatorTransitionLoopPipelineCode_normalizedInput_iff
        stage D input).mpr hhalt

theorem decodedBoundedSimulatorTransitionLoopPipelineCode_eq_some_output_nil
    {tokens out : Word MachineCodeSymbol}
    (h :
      decodedBoundedSimulatorTransitionLoopPipelineCode tokens = some out) :
    out = [] := by
  unfold decodedBoundedSimulatorTransitionLoopPipelineCode at h
  cases hinit :
      decodedBoundedSimulatorInitialWorkCodeTransform tokens with
  | none =>
      simp [hinit] at h
  | some work =>
      simp [hinit] at h
      cases hdecode :
          decodedBoundedSimulatorTransitionLoopWorkDecode work with
      | none =>
          simp [hdecode] at h
      | some parsed =>
          rcases parsed with ⟨D, stage, config, suffix⟩
          cases suffix with
          | nil =>
              unfold decodedBoundedSimulatorTransitionLoopFinalAcceptCode at h
              cases hwork :
                  decodedBoundedSimulatorTransitionLoopWorkDecode
                    (decodedBoundedSimulatorTransitionLoopIteratedWorkCode
                      D stage config) with
              | none =>
                  simp [hdecode, hwork] at h
              | some finalParsed =>
                  rcases finalParsed with
                    ⟨D', finalStage, finalConfig, finalSuffix⟩
                  cases finalStage with
                  | zero =>
                      cases finalSuffix with
                      | nil =>
                          by_cases hhalt : finalConfig.state = D'.halt
                          · simp [hdecode, hwork, hhalt] at h
                            exact h.symm
                          · simp [hdecode, hwork, hhalt] at h
                      | cons head tail =>
                          simp [hdecode, hwork] at h
                  | succ finalStage =>
                      simp [hdecode, hwork] at h
          | cons head tail =>
              simp [hdecode] at h

theorem decodedBoundedSimulatorTransitionLoopPipelineIterateCode_normalizedInput_iff
    (stage : Nat) (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    decodedBoundedSimulatorTransitionLoopPipelineIterateCode
        (decodedBoundedSimulatorNormalizedInput stage D input) =
        some ([] : Word MachineCodeSymbol) <->
      (decodedBoundedSimulatorTransitionLoopConfig stage D input).state =
        D.halt := by
  rw [decodedBoundedSimulatorTransitionLoopPipelineIterateCode_eq_pipelineCode]
  exact
    decodedBoundedSimulatorTransitionLoopPipelineCode_normalizedInput_iff
      stage D input

theorem decodedBoundedSimulatorTransitionLoopPipelineIterateCode_eq_some_nil_iff
    (tokens : Word MachineCodeSymbol) :
    decodedBoundedSimulatorTransitionLoopPipelineIterateCode tokens =
        some ([] : Word MachineCodeSymbol) <->
      exists stage : Nat,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens =
            some (stage,
              List.append (MachineDescription.encodeDescription D) input) ∧
          (decodedBoundedSimulatorTransitionLoopConfig
            stage D input).state = D.halt := by
  rw [decodedBoundedSimulatorTransitionLoopPipelineIterateCode_eq_pipelineCode]
  exact
    decodedBoundedSimulatorTransitionLoopPipelineCode_eq_some_nil_iff
      tokens

theorem decodedBoundedSimulatorTransitionLoopPipelineIterateCode_eq_some_output_nil
    {tokens out : Word MachineCodeSymbol}
    (h :
      decodedBoundedSimulatorTransitionLoopPipelineIterateCode tokens =
        some out) :
    out = [] := by
  apply decodedBoundedSimulatorTransitionLoopPipelineCode_eq_some_output_nil
  simpa [decodedBoundedSimulatorTransitionLoopPipelineIterateCode_eq_pipelineCode]
    using h

theorem decodedBoundedSimulatorTransitionLoopPipelineCode_eq_some_iff_code
    (tokens out : Word MachineCodeSymbol) :
    decodedBoundedSimulatorTransitionLoopPipelineCode tokens = some out <->
      CodePrefixDecodedBoundedSimulatorCode.transform tokens = some out := by
  constructor
  · intro hpipeline
    have hout :
        out = [] :=
      decodedBoundedSimulatorTransitionLoopPipelineCode_eq_some_output_nil
        hpipeline
    have hpipelineNil :
        decodedBoundedSimulatorTransitionLoopPipelineCode tokens =
          some ([] : Word MachineCodeSymbol) := by
      simpa [hout] using! hpipeline
    rcases
        (decodedBoundedSimulatorTransitionLoopPipelineCode_eq_some_nil_iff
          tokens).mp hpipelineNil with
      ⟨stage, D, input, hdecode, hhalt⟩
    have hhalts :
        D.HaltsIn stage
          (MachineDescription.encodeCodeWordAsInput input) := by
      simpa [MachineDescription.HaltsIn,
        decodedBoundedSimulatorTransitionLoopConfig,
        decodedBoundedSimulatorTransitionLoopFromConfig] using hhalt
    have hcodeNil :
        CodePrefixDecodedBoundedSimulatorCode.transform tokens =
          some ([] : Word MachineCodeSymbol) :=
      (decodedBoundedSimulatorNormalizedCode_transform_eq_some_nil_iff
        tokens).mpr
        ⟨stage, D, input, hdecode, hhalts⟩
    simpa [hout] using! hcodeNil
  · intro hcode
    rcases
        (codePrefixDecodedBoundedSimulatorCode_transform_eq_some_iff
          tokens out).mp hcode with
      ⟨hout, stage, encoded, D, input, htokens, hdescription, hhalts⟩
    have hdecode :
        MachineDescription.decodeNat tokens =
          some (stage,
            List.append (MachineDescription.encodeDescription D) input) := by
      have hstage :
          MachineDescription.decodeNat tokens =
            some (stage, encoded) := by
        simpa [htokens] using
          codePrefixRecognizerStageCode_decodeNat encoded stage
      have hencoded :
          encoded =
            List.append (MachineDescription.encodeDescription D) input :=
        MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescription_append
          hdescription
      simpa [hencoded] using! hstage
    have hhalt :
        (decodedBoundedSimulatorTransitionLoopConfig stage D input).state =
          D.halt := by
      simpa [MachineDescription.HaltsIn,
        decodedBoundedSimulatorTransitionLoopConfig,
        decodedBoundedSimulatorTransitionLoopFromConfig] using hhalts
    have hpipelineNil :
        decodedBoundedSimulatorTransitionLoopPipelineCode tokens =
          some ([] : Word MachineCodeSymbol) :=
      (decodedBoundedSimulatorTransitionLoopPipelineCode_eq_some_nil_iff
        tokens).mpr
        ⟨stage, D, input, hdecode, hhalt⟩
    simpa [hout] using! hpipelineNil

theorem decodedBoundedSimulatorTransitionLoopPipelineIterateCode_eq_some_iff_code
    (tokens out : Word MachineCodeSymbol) :
    decodedBoundedSimulatorTransitionLoopPipelineIterateCode tokens =
        some out <->
      CodePrefixDecodedBoundedSimulatorCode.transform tokens = some out := by
  rw [decodedBoundedSimulatorTransitionLoopPipelineIterateCode_eq_pipelineCode]
  exact
    decodedBoundedSimulatorTransitionLoopPipelineCode_eq_some_iff_code
      tokens out

theorem decodedBoundedSimulatorTransitionLoopPipelineIterateCode_eq_stageProgramRun_iff
    (tokens : Word MachineCodeSymbol) :
    decodedBoundedSimulatorTransitionLoopPipelineIterateCode tokens =
        some ([] : Word MachineCodeSymbol) <->
      exists stage : Nat,
      exists encoded : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens = some (stage, encoded) ∧
          CodePrefixRecognizerProgram.run encoded stage = some [] :=
  Iff.trans
    (decodedBoundedSimulatorTransitionLoopPipelineIterateCode_eq_some_iff_code
      tokens ([] : Word MachineCodeSymbol))
    (decodedBoundedSimulatorCode_transform_eq_stageProgramRun_iff tokens)

end Computability
end FoC
