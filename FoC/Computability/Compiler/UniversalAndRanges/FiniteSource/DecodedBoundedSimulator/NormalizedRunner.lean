import FoC.Computability.Compiler.UniversalAndRanges.Basic

set_option doc.verso true

/-!
# Normalized decoded bounded simulator runner

This module isolates the uniform finite-machine obligation for the normalized
decoded bounded simulator.  The public wrapper in
the decoded bounded simulator module
adapts this construction to the local spec definitions.
-/

namespace FoC
namespace Computability

open Languages

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
  simpa [decodedBoundedSimulatorNormalizedInput] using
    codePrefixRecognizerStageCode_decodeNat
      (List.append (MachineDescription.encodeDescription D) input) stage

/-- The normalized payload has exactly the requested decoded description. -/
theorem decodedBoundedSimulatorNormalizedInput_decodeDescriptionPrefix
    (D : MachineDescription) (input : Word MachineCodeSymbol) :
    MachineDescription.decodeDescriptionPrefix
        (List.append (MachineDescription.encodeDescription D) input) =
      some (D, input) := by
  simpa using
    MachineDescription.decodeDescriptionPrefix_encodeDescription_append
      D input

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
      (decodedBoundedSimulatorNormalizedInput_decodeDescriptionPrefix
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
      ⟨stage, D, input, by simpa [hencoded] using hstage, hhalts⟩
  · intro h
    rcases h with ⟨stage, D, input, hstage, hhalts⟩
    exact
      (codePrefixDecodedBoundedSimulatorCode_transform_eq_some_iff
        tokens ([] : Word MachineCodeSymbol)).mpr
        ⟨rfl, stage,
          List.append (MachineDescription.encodeDescription D) input,
          D, input,
          codePrefixRecognizerStageCode_eq_of_decodeNat hstage,
          decodedBoundedSimulatorNormalizedInput_decodeDescriptionPrefix
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
Boolean form of the staged evaluator.  The remaining finite runner only needs
to compute the executable bounded-trace predicate
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
Normalized boolean runner spec for the decoded bounded simulator.  This is the
next construction boundary: parse the outer stage, parse a canonical encoded
description payload, then evaluate the executable bounded-trace boolean.
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
The stage-program acceptance predicate is equivalent to the normalized boolean
bounded-trace predicate.
-/
theorem decodedBoundedSimulatorStageProgramRun_iff_haltsInBool
    (tokens : Word MachineCodeSymbol) :
    (exists stage : Nat,
      exists encoded : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens = some (stage, encoded) ∧
          CodePrefixRecognizerProgram.run encoded stage = some []) <->
      exists stage : Nat,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens =
            some (stage,
              List.append (MachineDescription.encodeDescription D) input) ∧
          MachineDescription.haltsInBool D stage
            (MachineDescription.encodeCodeWordAsInput input) = true := by
  constructor
  · intro h
    rcases h with ⟨stage, encoded, hstage, hprogram⟩
    rcases
        (codePrefixRecognizerProgram_run_eq_some_nil_iff_haltsInBool
          encoded stage).mp hprogram with
      ⟨D, input, hdecode, hhalts⟩
    have hencoded :
        encoded =
          List.append (MachineDescription.encodeDescription D) input :=
      MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescription_append
        hdecode
    exact ⟨stage, D, input, by simpa [hencoded] using hstage, hhalts⟩
  · intro h
    rcases h with ⟨stage, D, input, hstage, hhalts⟩
    exact
      ⟨stage,
        List.append (MachineDescription.encodeDescription D) input,
        hstage,
        (codePrefixRecognizerProgram_run_eq_some_nil_iff_haltsInBool
          (List.append (MachineDescription.encodeDescription D) input)
          stage).mpr
          ⟨D, input,
            MachineDescription.decodeDescriptionPrefix_encodeDescription_append
              D input,
            hhalts⟩⟩

/--
The normalized boolean bounded-trace predicate is exactly the run-config halt
state predicate.
-/
theorem decodedBoundedSimulatorHaltsInBool_iff_runConfig
    (tokens : Word MachineCodeSymbol) :
    (exists stage : Nat,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens =
            some (stage,
              List.append (MachineDescription.encodeDescription D) input) ∧
          MachineDescription.haltsInBool D stage
            (MachineDescription.encodeCodeWordAsInput input) = true) <->
      exists stage : Nat,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens =
            some (stage,
              List.append (MachineDescription.encodeDescription D) input) ∧
          (D.runConfig stage
            (D.initial
              (MachineDescription.encodeCodeWordAsInput input))).state =
            D.halt := by
  constructor
  · intro h
    rcases h with ⟨stage, D, input, hstage, hhalts⟩
    have hhaltsIn :
        D.HaltsIn stage
          (MachineDescription.encodeCodeWordAsInput input) :=
      (MachineDescription.haltsInBool_eq_true_iff D stage
        (MachineDescription.encodeCodeWordAsInput input)).mp hhalts
    exact ⟨stage, D, input, hstage, by
      simpa [MachineDescription.HaltsIn] using hhaltsIn⟩
  · intro h
    rcases h with ⟨stage, D, input, hstage, hrun⟩
    have hhaltsIn :
        D.HaltsIn stage
          (MachineDescription.encodeCodeWordAsInput input) := by
      simpa [MachineDescription.HaltsIn] using hrun
    exact
      ⟨stage, D, input, hstage,
        (MachineDescription.haltsInBool_eq_true_iff D stage
          (MachineDescription.encodeCodeWordAsInput input)).mpr hhaltsIn⟩

/--
Any independently supplied machine for the code primitive is already a
normalized decoded bounded-simulator runner.
-/
theorem decodedBoundedSimulatorNormalizedRunnerConstruction_of_codeMachine
    (hcode : CodePrefixDecodedBoundedSimulatorCodeMachineConstruction) :
    exists state : Type,
    exists runner : TuringMachine MachineCodeSymbol state,
      forall tokens : Word MachineCodeSymbol,
        TuringMachine.HaltsOnInput runner tokens <->
          exists stage : Nat,
          exists D : MachineDescription,
          exists input : Word MachineCodeSymbol,
            MachineDescription.decodeNat tokens =
                some (stage,
                  List.append (MachineDescription.encodeDescription D)
                    input) ∧
              D.HaltsIn stage
                (MachineDescription.encodeCodeWordAsInput input) := by
  rcases hcode with ⟨state, runner, hrunner⟩
  exact
    ⟨state, runner, fun tokens =>
      Iff.trans (hrunner tokens)
        (decodedBoundedSimulatorNormalizedCode_transform_eq_some_nil_iff
          tokens)⟩

/--
Run-config finite-machine leaf for the normalized decoded simulator.
-/
theorem decodedBoundedSimulatorRunConfigRunnerConstruction :
    DecodedBoundedSimulatorRunConfigRunnerConstruction := by
  sorry

/--
The run-config runner is enough to realize the Boolean bounded-trace runner.
-/
theorem decodedBoundedSimulatorBooleanRunnerConstruction_of_runConfigRunner
    (hrunner : DecodedBoundedSimulatorRunConfigRunnerConstruction) :
    DecodedBoundedSimulatorBooleanRunnerConstruction := by
  rcases hrunner with ⟨state, runner, hrunner⟩
  exact
    ⟨state, runner, fun tokens =>
      Iff.trans (hrunner tokens)
        (Iff.symm
          (decodedBoundedSimulatorHaltsInBool_iff_runConfig tokens))⟩

/--
Boolean bounded-trace finite-machine leaf for the normalized decoded simulator.
-/
theorem decodedBoundedSimulatorBooleanRunnerConstruction :
    DecodedBoundedSimulatorBooleanRunnerConstruction := by
  exact
    decodedBoundedSimulatorBooleanRunnerConstruction_of_runConfigRunner
      decodedBoundedSimulatorRunConfigRunnerConstruction

/--
The normalized boolean runner is enough to realize the staged-program runner.
-/
theorem decodedBoundedSimulatorStageProgramRunnerConstruction_of_booleanRunner
    (hrunner : DecodedBoundedSimulatorBooleanRunnerConstruction) :
    exists state : Type,
    exists runner : TuringMachine MachineCodeSymbol state,
      forall tokens : Word MachineCodeSymbol,
        TuringMachine.HaltsOnInput runner tokens <->
          exists stage : Nat,
          exists encoded : Word MachineCodeSymbol,
            MachineDescription.decodeNat tokens = some (stage, encoded) ∧
              CodePrefixRecognizerProgram.run encoded stage = some [] := by
  rcases hrunner with ⟨state, runner, hrunner⟩
  exact
    ⟨state, runner, fun tokens =>
      Iff.trans (hrunner tokens)
        (Iff.symm
          (decodedBoundedSimulatorStageProgramRun_iff_haltsInBool
            tokens))⟩

/--
Stage-coded evaluator construction for the fixed staged program
{name}`CodePrefixRecognizerProgram`.

This is a sharper form of the remaining uniform-runner obligation: parse the
outer unary stage field and evaluate the fixed staged program at that exact
stage.
-/
theorem decodedBoundedSimulatorStageProgramRunnerConstruction :
    exists state : Type,
    exists runner : TuringMachine MachineCodeSymbol state,
      forall tokens : Word MachineCodeSymbol,
        TuringMachine.HaltsOnInput runner tokens <->
          exists stage : Nat,
          exists encoded : Word MachineCodeSymbol,
            MachineDescription.decodeNat tokens = some (stage, encoded) ∧
              CodePrefixRecognizerProgram.run encoded stage = some [] := by
  exact
    decodedBoundedSimulatorStageProgramRunnerConstruction_of_booleanRunner
      decodedBoundedSimulatorBooleanRunnerConstruction

/--
The stage-program runner is enough to realize the decoded bounded simulator
code primitive.
-/
theorem decodedBoundedSimulatorUniformCodeMachineConstruction_of_stageProgramRunner
    (hrunner :
      exists state : Type,
      exists runner : TuringMachine MachineCodeSymbol state,
        forall tokens : Word MachineCodeSymbol,
          TuringMachine.HaltsOnInput runner tokens <->
            exists stage : Nat,
            exists encoded : Word MachineCodeSymbol,
              MachineDescription.decodeNat tokens = some (stage, encoded) ∧
                CodePrefixRecognizerProgram.run encoded stage = some []) :
    CodePrefixDecodedBoundedSimulatorCodeMachineConstruction := by
  rcases hrunner with ⟨state, runner, hrunner⟩
  exact
    ⟨state, runner, fun tokens =>
      Iff.trans (hrunner tokens)
        (Iff.symm
          (decodedBoundedSimulatorCode_transform_eq_stageProgramRun_iff
            tokens))⟩

/--
Conversely, a machine realizing the code primitive is a stage-program runner.
Together with
{name}`decodedBoundedSimulatorUniformCodeMachineConstruction_of_stageProgramRunner`,
this pins down the exact remaining construction boundary.
-/
theorem decodedBoundedSimulatorStageProgramRunnerConstruction_of_codeMachine
    (hcode : CodePrefixDecodedBoundedSimulatorCodeMachineConstruction) :
    exists state : Type,
    exists runner : TuringMachine MachineCodeSymbol state,
      forall tokens : Word MachineCodeSymbol,
        TuringMachine.HaltsOnInput runner tokens <->
          exists stage : Nat,
          exists encoded : Word MachineCodeSymbol,
            MachineDescription.decodeNat tokens = some (stage, encoded) ∧
              CodePrefixRecognizerProgram.run encoded stage = some [] := by
  rcases hcode with ⟨state, runner, hrunner⟩
  exact
    ⟨state, runner, fun tokens =>
      Iff.trans (hrunner tokens)
        (decodedBoundedSimulatorCode_transform_eq_stageProgramRun_iff
          tokens)⟩

/--
Uniform code-machine leaf for the decoded bounded simulator primitive.

This is the remaining transition-table obligation: one fixed machine must
realize the transform of
{name}`CodePrefixDecodedBoundedSimulatorCode`, interpreting the decoded
description as tape data rather than selecting a generated
description-specific simulator.
-/
theorem decodedBoundedSimulatorUniformCodeMachineConstruction :
    CodePrefixDecodedBoundedSimulatorCodeMachineConstruction := by
  exact
    decodedBoundedSimulatorUniformCodeMachineConstruction_of_stageProgramRunner
      decodedBoundedSimulatorStageProgramRunnerConstruction

/--
Uniform normalized decoded-bounded-simulator runner construction.

The witness machine must parse the outer unary stage code, recover one
canonical encoded description prefix, and interpret the decoded description as
tape data for exactly the parsed bound.
-/
theorem decodedBoundedSimulatorNormalizedRunnerConstruction :
    exists state : Type,
    exists runner : TuringMachine MachineCodeSymbol state,
      forall tokens : Word MachineCodeSymbol,
        TuringMachine.HaltsOnInput runner tokens <->
          exists stage : Nat,
          exists D : MachineDescription,
          exists input : Word MachineCodeSymbol,
            MachineDescription.decodeNat tokens =
                some (stage,
                  List.append (MachineDescription.encodeDescription D)
                    input) ∧
              D.HaltsIn stage
                (MachineDescription.encodeCodeWordAsInput input) := by
  exact
    decodedBoundedSimulatorNormalizedRunnerConstruction_of_codeMachine
      decodedBoundedSimulatorUniformCodeMachineConstruction

end Computability
end FoC
