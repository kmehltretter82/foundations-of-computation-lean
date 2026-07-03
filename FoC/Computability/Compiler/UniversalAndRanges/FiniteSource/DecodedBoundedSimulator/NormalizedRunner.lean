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
  sorry

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
