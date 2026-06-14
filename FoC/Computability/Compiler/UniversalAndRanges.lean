import FoC.Computability.Compiler.Skeletons
import FoC.Computability.MachineBuilder.PrefixParser

set_option doc.verso true

/-!
# Universal runners and compiled ranges
-/

namespace FoC
namespace Computability

open Languages

/-!
## Encoded input languages and universal runners

Section 5.3 encodes machine descriptions and their inputs over the common
{name}`MachineCodeSymbol` alphabet, while concrete descriptions still execute
on Boolean tapes. The next predicates isolate the exact compiler and runner
obligations needed for a concrete universal machine.
-/

def MachineDescriptionAcceptsEncodedInputLanguage
    (D : MachineDescription)
    (L : Language MachineCodeSymbol) : Prop :=
  D.WellFormed ∧ Language.Equal (MachineDescription.EncodedInputLanguage D) L

def EncodedInputProgramCompiledByDescription
    (P : StagedProgram MachineCodeSymbol Unit)
    (D : MachineDescription) : Prop :=
  D.WellFormed ∧
    forall w : Word MachineCodeSymbol,
      D.HaltsOnInput (MachineDescription.encodeCodeWordAsInput w) <->
        ProgramHaltsWithOutput P w []

def EncodedInputProgramAcceptorCompilationPrinciple : Prop :=
  forall P : StagedProgram MachineCodeSymbol Unit,
    exists D : MachineDescription,
      EncodedInputProgramCompiledByDescription P D

def EncodedInputDescriptionCompilerPrinciple : Prop :=
  forall L : Language MachineCodeSymbol,
    RecursivelyEnumerable L ->
      exists D : MachineDescription,
        MachineDescriptionAcceptsEncodedInputLanguage D L

/-!
The encoded-input compiler handoff reduces code-symbol recognizers to ordinary
Boolean-input recognizers.  The Boolean program first parses its input using
{name}`MachineDescription.decodeCodeWordAsInput`; on canonical encoded inputs
this parser is inverse to {name}`MachineDescription.encodeCodeWordAsInput`.
-/

noncomputable def EncodedInputBoolProgram
    (P : StagedProgram MachineCodeSymbol Unit) :
    StagedProgram Bool Unit :=
  by
    exact
      { run := fun bits stage =>
          match MachineDescription.decodeCodeWordAsInput bits with
          | none => none
          | some w => P.run w stage }

theorem encodedInputBoolProgram_halts_iff_decode
    (P : StagedProgram MachineCodeSymbol Unit)
    (bits : Word Bool) :
    ProgramHaltsWithOutput (EncodedInputBoolProgram P) bits [] <->
      exists w : Word MachineCodeSymbol,
        MachineDescription.decodeCodeWordAsInput bits = some w ∧
          ProgramHaltsWithOutput P w [] := by
  constructor
  · intro h
    rcases h with ⟨stage, hstage⟩
    unfold EncodedInputBoolProgram at hstage
    cases hdecode : MachineDescription.decodeCodeWordAsInput bits with
    | none =>
        simp [hdecode] at hstage
    | some w =>
        exact ⟨w, rfl, ⟨stage, by simpa [hdecode] using hstage⟩⟩
  · intro h
    rcases h with ⟨w, hdecode, stage, hstage⟩
    exact ⟨stage, by
      unfold EncodedInputBoolProgram
      simp [hdecode, hstage]⟩

theorem encodedInputBoolProgram_halts_encodeCodeWordAsInput_iff
    (P : StagedProgram MachineCodeSymbol Unit)
    (w : Word MachineCodeSymbol) :
    ProgramHaltsWithOutput (EncodedInputBoolProgram P)
      (MachineDescription.encodeCodeWordAsInput w) [] <->
        ProgramHaltsWithOutput P w [] := by
  constructor
  · intro h
    rcases (encodedInputBoolProgram_halts_iff_decode P
        (MachineDescription.encodeCodeWordAsInput w)).mp h with
      ⟨decoded, hdecode, hhalts⟩
    have hcanonical :
        decoded = w := by
      have hdecode' := MachineDescription.decodeCodeWordAsInput_encodeCodeWordAsInput w
      rw [hdecode'] at hdecode
      exact Option.some.inj hdecode.symm
    simpa [hcanonical] using hhalts
  · intro h
    exact
      (encodedInputBoolProgram_halts_iff_decode P
        (MachineDescription.encodeCodeWordAsInput w)).mpr
        ⟨w,
          MachineDescription.decodeCodeWordAsInput_encodeCodeWordAsInput w,
          h⟩

def CodeUniversalPrefixMachineSpec
    (universal : TuringMachine MachineCodeSymbol state) : Prop :=
  forall encoded : Word MachineCodeSymbol,
    TuringMachine.HaltsOnInput universal encoded <->
      MachineDescription.CodePrefixAccepts encoded

def CodeUniversalPrefixMachineRowLanguage
    (universal : TuringMachine MachineCodeSymbol state)
    (machine : Word MachineCodeSymbol) : Language MachineCodeSymbol :=
  fun input => TuringMachine.HaltsOnInput universal
    (Languages.Word.Concat machine input)

def CodeUniversalPrefixRowsCoverAcceptableLanguages
    (universal : TuringMachine MachineCodeSymbol state) : Prop :=
  forall L : Language MachineCodeSymbol, RecursivelyEnumerable L ->
    exists machine : Word MachineCodeSymbol,
      Language.Equal
        (CodeUniversalPrefixMachineRowLanguage universal machine) L

def CodeUniversalPrefixRunnerConstruction : Prop :=
  exists state : Type,
    exists universal : TuringMachine MachineCodeSymbol state,
      CodeUniversalPrefixMachineSpec universal

def CodeUniversalPrefixRowsCoverConstruction : Prop :=
  exists state : Type,
    exists universal : TuringMachine MachineCodeSymbol state,
      CodeUniversalPrefixMachineSpec universal ∧
        CodeUniversalPrefixRowsCoverAcceptableLanguages universal

/-!
The prefix accepted language is semidecidable by a direct staged search:
decode one description from the front of the input, then run the decoded
description for the current stage bound on the encoded suffix.
-/

noncomputable def CodePrefixRecognizerProgram :
    StagedProgram MachineCodeSymbol Unit :=
  by
    classical
    exact
      { run := fun encoded stage =>
          match MachineDescription.decodeDescriptionPrefix encoded with
          | none => none
          | some (D, input) =>
              if D.HaltsIn stage
                  (MachineDescription.encodeCodeWordAsInput input) then
                some []
              else
                none }

theorem codePrefixRecognizerProgram_acceptsLanguage :
    ProgramAcceptsLanguage CodePrefixRecognizerProgram
      MachineDescription.CodePrefixAcceptedLanguage := by
  classical
  intro encoded
  constructor
  · intro h
    rcases h with ⟨stage, hstage⟩
    unfold CodePrefixRecognizerProgram at hstage
    cases hdecode :
        MachineDescription.decodeDescriptionPrefix encoded with
    | none =>
        simp [hdecode] at hstage
    | some decoded =>
        rcases decoded with ⟨D, input⟩
        by_cases hhalts :
            D.HaltsIn stage
              (MachineDescription.encodeCodeWordAsInput input)
        · exact
            ⟨D, input, hdecode, ⟨stage, hhalts⟩⟩
        · simp [hdecode, hhalts] at hstage
  · intro h
    rcases h with ⟨D, input, hdecode, hhalts⟩
    rcases hhalts with ⟨stage, hstage⟩
    exact ⟨stage, by
      unfold CodePrefixRecognizerProgram
      simp [hdecode, hstage]⟩

theorem codePrefixAcceptedLanguage_programAcceptable :
    ProgramAcceptable MachineDescription.CodePrefixAcceptedLanguage :=
  ⟨CodePrefixRecognizerProgram,
    codePrefixRecognizerProgram_acceptsLanguage⟩

/-!
The finite prefix recognizer starts with a parser over
{name}`MachineCodeSymbol` tapes.  At this layer the parser is represented as
checked {name}`MachineDescription.TapeCodePrimitive` data: a partial normalizer
that succeeds exactly on one-description prefixes, and a total branch primitive
that emits a success/failure bit.
-/

def CodePrefixParserNormalizerCode :
    MachineDescription.TapeCodePrimitive :=
  MachineDescription.PrefixParser.normalizeCodePrimitive

def CodePrefixParserBranchCode :
    MachineDescription.TapeCodePrimitive :=
  MachineDescription.PrefixParser.branchCodePrimitive

def CodePrefixParserCodeConstruction : Prop :=
  Nonempty MachineDescription.PrefixParser.CodeConstruction

theorem codePrefixParserCodeConstruction :
    CodePrefixParserCodeConstruction :=
  ⟨MachineDescription.PrefixParser.codeConstruction⟩

theorem codePrefixParser_normalize_success_iff
    (tokens : Word MachineCodeSymbol) :
    MachineDescription.PrefixParser.normalizeCode tokens = some tokens <->
      exists D : MachineDescription,
        exists input : Word MachineCodeSymbol,
          MachineDescription.decodeDescriptionPrefix tokens =
            some (D, input) :=
  MachineDescription.PrefixParser.normalizeCode_eq_some_self_iff tokens

theorem codePrefixParserNormalizerCode_transform_eq_some_iff
    (tokens out : Word MachineCodeSymbol) :
    CodePrefixParserNormalizerCode.transform tokens = some out <->
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeDescriptionPrefix tokens =
            some (D, input) ∧
          out = List.append (MachineDescription.encodeDescription D) input := by
  simpa [CodePrefixParserNormalizerCode] using
    MachineDescription.PrefixParser.normalizeCode_eq_some_iff tokens out

theorem codePrefixParserNormalizerCode_transform_eq_none_iff
    (tokens : Word MachineCodeSymbol) :
    CodePrefixParserNormalizerCode.transform tokens = none <->
      MachineDescription.decodeDescriptionPrefix tokens = none := by
  simpa [CodePrefixParserNormalizerCode] using
    MachineDescription.PrefixParser.normalizeCode_eq_none_iff tokens

theorem codePrefixParser_branch_success
    {tokens : Word MachineCodeSymbol} {D : MachineDescription}
    {input : Word MachineCodeSymbol}
    (h : MachineDescription.decodeDescriptionPrefix tokens =
      some (D, input)) :
    MachineDescription.PrefixParser.branchCode tokens =
      some (MachineDescription.encodeBoolWordAppend [true] tokens) :=
  MachineDescription.PrefixParser.branchCode_of_decodeDescriptionPrefix h

theorem codePrefixParser_branch_failure
    {tokens : Word MachineCodeSymbol}
    (h : MachineDescription.decodeDescriptionPrefix tokens = none) :
    MachineDescription.PrefixParser.branchCode tokens =
      some (MachineDescription.encodeBoolWord [false]) :=
  MachineDescription.PrefixParser.branchCode_of_decodeDescriptionPrefix_none h

theorem codePrefixParser_branch_total
    (tokens : Word MachineCodeSymbol) :
    exists out : Word MachineCodeSymbol,
      MachineDescription.PrefixParser.branchCode tokens = some out :=
  MachineDescription.PrefixParser.branchCode_total tokens

theorem codePrefixParserBranchCode_transform_eq_some_iff
    (tokens out : Word MachineCodeSymbol) :
    CodePrefixParserBranchCode.transform tokens = some out <->
      (MachineDescription.decodeDescriptionPrefix tokens = none ∧
        out = MachineDescription.encodeBoolWord [false]) ∨
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeDescriptionPrefix tokens =
            some (D, input) ∧
          out =
            MachineDescription.encodeBoolWordAppend [true]
              (List.append (MachineDescription.encodeDescription D) input) := by
  simpa [CodePrefixParserBranchCode] using
    MachineDescription.PrefixParser.branchCode_eq_some_iff tokens out

theorem codePrefixParserBranchCode_total
    (tokens : Word MachineCodeSymbol) :
    exists out : Word MachineCodeSymbol,
      CodePrefixParserBranchCode.transform tokens = some out := by
  simpa [CodePrefixParserBranchCode] using
    MachineDescription.PrefixParser.branchCode_total tokens

/-!
The finite universal-prefix runner can be built by recognizing exactly the
single prefix language above on the concrete code alphabet.  This target avoids
an arbitrary staged-program compiler: a machine satisfying the fixed-alphabet
recognizer specification is already a universal prefix runner.
-/

def CodePrefixRecognizerMachineSpec
    (universal : TuringMachine MachineCodeSymbol state) : Prop :=
  forall encoded : Word MachineCodeSymbol,
    TuringMachine.HaltsOnInput universal encoded <->
      ProgramHaltsWithOutput CodePrefixRecognizerProgram encoded []

def CodePrefixRecognizerMachineConstruction : Prop :=
  exists state : Type,
    exists universal : TuringMachine MachineCodeSymbol state,
      CodePrefixRecognizerMachineSpec universal

def CodePrefixParserNormalizerMachineSpec
    (normalizer : TuringMachine MachineCodeSymbol state) : Prop :=
  forall tokens out : Word MachineCodeSymbol,
    TuringMachine.HaltsWithOutput normalizer tokens out <->
      MachineDescription.PrefixParser.normalizeCode tokens = some out

def CodePrefixParserNormalizerMachineConstruction : Prop :=
  exists state : Type,
    exists normalizer : TuringMachine MachineCodeSymbol state,
      CodePrefixParserNormalizerMachineSpec normalizer

def CodePrefixParserNormalizerCodeMachineSpec
    (normalizer : TuringMachine MachineCodeSymbol state) : Prop :=
  forall tokens out : Word MachineCodeSymbol,
    TuringMachine.HaltsWithOutput normalizer tokens out <->
      CodePrefixParserNormalizerCode.transform tokens = some out

def CodePrefixParserNormalizerCodeMachineConstruction : Prop :=
  exists state : Type,
    exists normalizer : TuringMachine MachineCodeSymbol state,
      CodePrefixParserNormalizerCodeMachineSpec normalizer

theorem codePrefixParserNormalizerMachineSpec_of_codeMachineSpec
    {normalizer : TuringMachine MachineCodeSymbol state}
    (hnormalizer :
      CodePrefixParserNormalizerCodeMachineSpec normalizer) :
    CodePrefixParserNormalizerMachineSpec normalizer := by
  intro tokens out
  simpa [CodePrefixParserNormalizerCode] using hnormalizer tokens out

theorem codePrefixParserNormalizerMachineConstruction_of_codeMachine
    (hcode : CodePrefixParserNormalizerCodeMachineConstruction) :
    CodePrefixParserNormalizerMachineConstruction := by
  rcases hcode with ⟨state, normalizer, hnormalizer⟩
  exact
    ⟨state, normalizer,
      codePrefixParserNormalizerMachineSpec_of_codeMachineSpec
        hnormalizer⟩

def CodePrefixParserBranchMachineSpec
    (branch : TuringMachine MachineCodeSymbol state) : Prop :=
  forall tokens out : Word MachineCodeSymbol,
    TuringMachine.HaltsWithOutput branch tokens out <->
      MachineDescription.PrefixParser.branchCode tokens = some out

def CodePrefixParserBranchMachineConstruction : Prop :=
  exists state : Type,
    exists branch : TuringMachine MachineCodeSymbol state,
      CodePrefixParserBranchMachineSpec branch

def CodePrefixParserBranchCodeMachineSpec
    (branch : TuringMachine MachineCodeSymbol state) : Prop :=
  forall tokens out : Word MachineCodeSymbol,
    TuringMachine.HaltsWithOutput branch tokens out <->
      CodePrefixParserBranchCode.transform tokens = some out

def CodePrefixParserBranchCodeMachineConstruction : Prop :=
  exists state : Type,
    exists branch : TuringMachine MachineCodeSymbol state,
      CodePrefixParserBranchCodeMachineSpec branch

theorem codePrefixParserBranchMachineSpec_of_codeMachineSpec
    {branch : TuringMachine MachineCodeSymbol state}
    (hbranch : CodePrefixParserBranchCodeMachineSpec branch) :
    CodePrefixParserBranchMachineSpec branch := by
  intro tokens out
  simpa [CodePrefixParserBranchCode] using hbranch tokens out

theorem codePrefixParserBranchMachineConstruction_of_codeMachine
    (hcode : CodePrefixParserBranchCodeMachineConstruction) :
    CodePrefixParserBranchMachineConstruction := by
  rcases hcode with ⟨state, branch, hbranch⟩
  exact
    ⟨state, branch,
      codePrefixParserBranchMachineSpec_of_codeMachineSpec hbranch⟩

def CodePrefixRecognizerStageCode
    (encoded : Word MachineCodeSymbol) (stage : Nat) :
    Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend stage encoded

noncomputable def CodePrefixDecodedBoundedSimulatorCode :
    MachineDescription.TapeCodePrimitive :=
  by
    classical
    exact
      { transform := fun tokens =>
          match MachineDescription.decodeNat tokens with
          | none => none
          | some (stage, encoded) =>
              match MachineDescription.decodeDescriptionPrefix encoded with
              | none => none
              | some (D, input) =>
                  if D.HaltsIn stage
                      (MachineDescription.encodeCodeWordAsInput input) then
                    some []
                  else
                    none }

theorem codePrefixRecognizerStageCode_decodeNat
    (encoded : Word MachineCodeSymbol) (stage : Nat) :
    MachineDescription.decodeNat
        (CodePrefixRecognizerStageCode encoded stage) =
      some (stage, encoded) :=
  MachineDescription.decodeNat_encodeNatAppend stage encoded

theorem codePrefixRecognizerStageCode_eq_of_decodeNat
    {tokens encoded : Word MachineCodeSymbol} {stage : Nat}
    (h : MachineDescription.decodeNat tokens = some (stage, encoded)) :
    tokens = CodePrefixRecognizerStageCode encoded stage :=
  MachineDescription.decodeNat_eq_some_encodeNatAppend h

theorem codePrefixDecodedBoundedSimulatorCode_stageCode_of_halts
    {encoded input : Word MachineCodeSymbol}
    {D : MachineDescription} {stage : Nat}
    (hdecode :
      MachineDescription.decodeDescriptionPrefix encoded =
        some (D, input))
    (hhalts :
      D.HaltsIn stage
        (MachineDescription.encodeCodeWordAsInput input)) :
    CodePrefixDecodedBoundedSimulatorCode.transform
        (CodePrefixRecognizerStageCode encoded stage) =
      some ([] : Word MachineCodeSymbol) := by
  classical
  simp [CodePrefixDecodedBoundedSimulatorCode,
    CodePrefixRecognizerStageCode,
    MachineDescription.decodeNat_encodeNatAppend, hdecode, hhalts]
  rfl

theorem codePrefixDecodedBoundedSimulatorCode_stageCode_of_not_halts
    {encoded input : Word MachineCodeSymbol}
    {D : MachineDescription} {stage : Nat}
    (hdecode :
      MachineDescription.decodeDescriptionPrefix encoded =
        some (D, input))
    (hhalts :
      ¬ D.HaltsIn stage
        (MachineDescription.encodeCodeWordAsInput input)) :
    CodePrefixDecodedBoundedSimulatorCode.transform
        (CodePrefixRecognizerStageCode encoded stage) =
      none := by
  classical
  simp [CodePrefixDecodedBoundedSimulatorCode,
    CodePrefixRecognizerStageCode,
    MachineDescription.decodeNat_encodeNatAppend, hdecode, hhalts]

theorem codePrefixDecodedBoundedSimulatorCode_stageCode_eq_some_iff
    {encoded input : Word MachineCodeSymbol}
    {D : MachineDescription} {stage : Nat}
    (hdecode :
      MachineDescription.decodeDescriptionPrefix encoded =
        some (D, input)) :
    CodePrefixDecodedBoundedSimulatorCode.transform
        (CodePrefixRecognizerStageCode encoded stage) =
      some ([] : Word MachineCodeSymbol) <->
        D.HaltsIn stage
          (MachineDescription.encodeCodeWordAsInput input) := by
  classical
  constructor
  · intro h
    by_cases hhalts :
        D.HaltsIn stage
          (MachineDescription.encodeCodeWordAsInput input)
    · exact hhalts
    · rw [codePrefixDecodedBoundedSimulatorCode_stageCode_of_not_halts
        hdecode hhalts] at h
      cases h
  · intro hhalts
    exact
      codePrefixDecodedBoundedSimulatorCode_stageCode_of_halts
        hdecode hhalts

theorem codePrefixDecodedBoundedSimulatorCode_transform_eq_some_iff
    (tokens out : Word MachineCodeSymbol) :
    CodePrefixDecodedBoundedSimulatorCode.transform tokens = some out <->
      out = [] ∧
        exists stage : Nat,
        exists encoded : Word MachineCodeSymbol,
        exists D : MachineDescription,
        exists input : Word MachineCodeSymbol,
          tokens = CodePrefixRecognizerStageCode encoded stage ∧
            MachineDescription.decodeDescriptionPrefix encoded =
              some (D, input) ∧
            D.HaltsIn stage
              (MachineDescription.encodeCodeWordAsInput input) := by
  classical
  constructor
  · intro h
    unfold CodePrefixDecodedBoundedSimulatorCode at h
    cases hstage : MachineDescription.decodeNat tokens with
    | none =>
        simp [hstage] at h
    | some parsedStage =>
        cases parsedStage with
        | mk stage encoded =>
            simp [hstage] at h
            cases hdecode :
                MachineDescription.decodeDescriptionPrefix encoded with
            | none =>
                simp [hdecode] at h
            | some decoded =>
                cases decoded with
                | mk D input =>
                    simp [hdecode] at h
                    by_cases hhalts :
                        D.HaltsIn stage
                          (MachineDescription.encodeCodeWordAsInput input)
                    · simp [hhalts] at h
                      cases h
                      exact
                        ⟨rfl, stage, encoded, D, input,
                          codePrefixRecognizerStageCode_eq_of_decodeNat
                            hstage,
                          hdecode,
                          hhalts⟩
                    · simp [hhalts] at h
  · intro h
    rcases h with
      ⟨rfl, stage, encoded, D, input, rfl, hdecode, hhalts⟩
    exact
      codePrefixDecodedBoundedSimulatorCode_stageCode_of_halts
        hdecode hhalts

def CodePrefixDecodedBoundedSimulatorSpec
    (simulator : TuringMachine MachineCodeSymbol state) : Prop :=
  forall encoded : Word MachineCodeSymbol,
  forall D : MachineDescription,
  forall input : Word MachineCodeSymbol,
  forall stage : Nat,
    MachineDescription.decodeDescriptionPrefix encoded = some (D, input) ->
      (TuringMachine.HaltsOnInput simulator
            (CodePrefixRecognizerStageCode encoded stage) <->
          D.HaltsIn stage
            (MachineDescription.encodeCodeWordAsInput input))

def CodePrefixDecodedBoundedSimulatorConstruction : Prop :=
  exists state : Type,
    exists simulator : TuringMachine MachineCodeSymbol state,
      CodePrefixDecodedBoundedSimulatorSpec simulator

def CodePrefixDecodedBoundedSimulatorCodeMachineSpec
    (simulator : TuringMachine MachineCodeSymbol state) : Prop :=
  forall tokens : Word MachineCodeSymbol,
    TuringMachine.HaltsOnInput simulator tokens <->
      CodePrefixDecodedBoundedSimulatorCode.transform tokens =
        some ([] : Word MachineCodeSymbol)

def CodePrefixDecodedBoundedSimulatorCodeMachineConstruction : Prop :=
  exists state : Type,
    exists simulator : TuringMachine MachineCodeSymbol state,
      CodePrefixDecodedBoundedSimulatorCodeMachineSpec simulator

theorem codePrefixDecodedBoundedSimulatorSpec_of_codeMachineSpec
    {simulator : TuringMachine MachineCodeSymbol state}
    (hsim :
      CodePrefixDecodedBoundedSimulatorCodeMachineSpec simulator) :
    CodePrefixDecodedBoundedSimulatorSpec simulator := by
  intro encoded D input stage hdecode
  exact Iff.trans
    (hsim (CodePrefixRecognizerStageCode encoded stage))
    (codePrefixDecodedBoundedSimulatorCode_stageCode_eq_some_iff hdecode)

theorem codePrefixDecodedBoundedSimulatorConstruction_of_codeMachine
    (hcode : CodePrefixDecodedBoundedSimulatorCodeMachineConstruction) :
    CodePrefixDecodedBoundedSimulatorConstruction := by
  rcases hcode with ⟨state, simulator, hsim⟩
  exact
    ⟨state, simulator,
      codePrefixDecodedBoundedSimulatorSpec_of_codeMachineSpec hsim⟩

def CodePrefixDecodedStageSearchAccepts
    (encoded : Word MachineCodeSymbol) : Prop :=
  exists D : MachineDescription,
  exists input : Word MachineCodeSymbol,
  exists stage : Nat,
    MachineDescription.decodeDescriptionPrefix encoded = some (D, input) ∧
      D.HaltsIn stage
        (MachineDescription.encodeCodeWordAsInput input)

theorem codePrefixDecodedStageSearchAccepts_iff_boundedSimulatorCode
    (encoded : Word MachineCodeSymbol) :
    CodePrefixDecodedStageSearchAccepts encoded <->
      exists stage : Nat,
        CodePrefixDecodedBoundedSimulatorCode.transform
          (CodePrefixRecognizerStageCode encoded stage) =
          some ([] : Word MachineCodeSymbol) := by
  classical
  constructor
  · intro h
    rcases h with ⟨D, input, stage, hdecode, hhalts⟩
    exact
      ⟨stage,
        codePrefixDecodedBoundedSimulatorCode_stageCode_of_halts
          hdecode hhalts⟩
  · intro h
    rcases h with ⟨stage, hstage⟩
    unfold CodePrefixDecodedBoundedSimulatorCode at hstage
    simp [CodePrefixRecognizerStageCode,
      MachineDescription.decodeNat_encodeNatAppend] at hstage
    cases hdecode :
        MachineDescription.decodeDescriptionPrefix encoded with
    | none =>
        simp [hdecode] at hstage
    | some decoded =>
        cases decoded with
        | mk D input =>
            simp [hdecode] at hstage
            by_cases hhalts :
                D.HaltsIn stage
                  (MachineDescription.encodeCodeWordAsInput input)
            · exact ⟨D, input, stage, hdecode, hhalts⟩
            · simp [hhalts] at hstage

theorem codePrefixDecodedStageSearchAccepts_iff_codeMachineHalts
    {simulator : TuringMachine MachineCodeSymbol state}
    (hsim :
      CodePrefixDecodedBoundedSimulatorCodeMachineSpec simulator)
    (encoded : Word MachineCodeSymbol) :
    CodePrefixDecodedStageSearchAccepts encoded <->
      exists stage : Nat,
        TuringMachine.HaltsOnInput simulator
          (CodePrefixRecognizerStageCode encoded stage) := by
  rw [codePrefixDecodedStageSearchAccepts_iff_boundedSimulatorCode]
  constructor
  · intro h
    rcases h with ⟨stage, hstage⟩
    exact ⟨stage, (hsim _).mpr hstage⟩
  · intro h
    rcases h with ⟨stage, hstage⟩
    exact ⟨stage, (hsim _).mp hstage⟩

theorem codePrefixDecodedStageSearchAccepts_iff_programHalts
    (encoded : Word MachineCodeSymbol) :
    CodePrefixDecodedStageSearchAccepts encoded <->
      ProgramHaltsWithOutput CodePrefixRecognizerProgram encoded [] := by
  constructor
  · intro h
    rcases h with ⟨D, input, stage, hdecode, hhalts⟩
    exact
      (codePrefixRecognizerProgram_acceptsLanguage encoded).mpr
        ⟨D, input, hdecode, ⟨stage, hhalts⟩⟩
  · intro h
    rcases (codePrefixRecognizerProgram_acceptsLanguage encoded).mp h with
      ⟨D, input, hdecode, stage, hhalts⟩
    exact ⟨D, input, stage, hdecode, hhalts⟩

def CodePrefixStageSearchControllerSpec
    (simulator : TuringMachine MachineCodeSymbol simulatorState)
    (searcher : TuringMachine MachineCodeSymbol searcherState) :
    Prop :=
  forall encoded : Word MachineCodeSymbol,
    TuringMachine.HaltsOnInput searcher encoded <->
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
      exists stage : Nat,
        MachineDescription.decodeDescriptionPrefix encoded =
            some (D, input) ∧
          TuringMachine.HaltsOnInput simulator
            (CodePrefixRecognizerStageCode encoded stage)

def CodePrefixStageSearchControllerConstruction : Prop :=
  forall {normalizerState branchState simulatorState : Type}
    (normalizer : TuringMachine MachineCodeSymbol normalizerState)
    (branch : TuringMachine MachineCodeSymbol branchState)
    (simulator : TuringMachine MachineCodeSymbol simulatorState),
    CodePrefixParserNormalizerMachineSpec normalizer ->
    CodePrefixParserBranchMachineSpec branch ->
    CodePrefixDecodedBoundedSimulatorSpec simulator ->
      exists searcherState : Type,
      exists searcher : TuringMachine MachineCodeSymbol searcherState,
        CodePrefixStageSearchControllerSpec simulator searcher

theorem codePrefixRecognizerMachineSpec_of_stageSearchController
    {simulator : TuringMachine MachineCodeSymbol simulatorState}
    {searcher : TuringMachine MachineCodeSymbol searcherState}
    (hsimulator : CodePrefixDecodedBoundedSimulatorSpec simulator)
    (hsearch :
      CodePrefixStageSearchControllerSpec simulator searcher) :
    CodePrefixRecognizerMachineSpec searcher := by
  intro encoded
  constructor
  · intro h
    rcases (hsearch encoded).mp h with
      ⟨D, input, stage, hdecode, hsimHalts⟩
    have hiff :=
      (hsimulator encoded D input stage) hdecode
    exact
      (codePrefixDecodedStageSearchAccepts_iff_programHalts
        encoded).mp
        ⟨D, input, stage, hdecode, hiff.mp hsimHalts⟩
  · intro h
    rcases
        (codePrefixDecodedStageSearchAccepts_iff_programHalts
          encoded).mpr h with
      ⟨D, input, stage, hdecode, hhalts⟩
    have hiff :=
      (hsimulator encoded D input stage) hdecode
    exact
      (hsearch encoded).mpr
        ⟨D, input, stage, hdecode, hiff.mpr hhalts⟩

theorem codePrefixRecognizerMachineConstruction_of_finiteSourceComponents
    (hnormalizer : CodePrefixParserNormalizerMachineConstruction)
    (hbranch : CodePrefixParserBranchMachineConstruction)
    (hsimulator : CodePrefixDecodedBoundedSimulatorConstruction)
    (hsearch : CodePrefixStageSearchControllerConstruction) :
    CodePrefixRecognizerMachineConstruction := by
  rcases hnormalizer with
    ⟨normalizerState, normalizer, hnormalizer⟩
  rcases hbranch with ⟨branchState, branch, hbranch⟩
  rcases hsimulator with
    ⟨simulatorState, simulator, hsimulator⟩
  rcases hsearch normalizer branch simulator
      hnormalizer hbranch hsimulator with
    ⟨searcherState, searcher, hsearcher⟩
  exact
    ⟨searcherState, searcher,
      codePrefixRecognizerMachineSpec_of_stageSearchController
        hsimulator hsearcher⟩

theorem codeUniversalPrefixMachineSpec_of_codePrefixRecognizerMachineSpec
    {universal : TuringMachine MachineCodeSymbol state}
    (hspec : CodePrefixRecognizerMachineSpec universal) :
    CodeUniversalPrefixMachineSpec universal := by
  intro encoded
  exact Iff.trans (hspec encoded)
    (codePrefixRecognizerProgram_acceptsLanguage encoded)

theorem codePrefixRecognizerMachineSpec_of_codeUniversalPrefixMachineSpec
    {universal : TuringMachine MachineCodeSymbol state}
    (hspec : CodeUniversalPrefixMachineSpec universal) :
    CodePrefixRecognizerMachineSpec universal := by
  intro encoded
  exact Iff.trans (hspec encoded)
    (Iff.symm (codePrefixRecognizerProgram_acceptsLanguage encoded))

theorem codeUniversalPrefixRunnerConstruction_of_codePrefixRecognizerMachine
    (hrunner : CodePrefixRecognizerMachineConstruction) :
    CodeUniversalPrefixRunnerConstruction := by
  rcases hrunner with ⟨state, universal, hspec⟩
  exact
    ⟨state, universal,
      codeUniversalPrefixMachineSpec_of_codePrefixRecognizerMachineSpec
        hspec⟩

theorem codePrefixRecognizerMachine_of_codeUniversalPrefixRunnerConstruction
    (hrunner : CodeUniversalPrefixRunnerConstruction) :
    CodePrefixRecognizerMachineConstruction := by
  rcases hrunner with ⟨state, universal, hspec⟩
  exact
    ⟨state, universal,
      codePrefixRecognizerMachineSpec_of_codeUniversalPrefixMachineSpec
        hspec⟩

theorem codePrefixRecognizerMachineConstruction_iff_universalPrefixRunner :
    CodePrefixRecognizerMachineConstruction <->
      CodeUniversalPrefixRunnerConstruction := by
  constructor
  · exact codeUniversalPrefixRunnerConstruction_of_codePrefixRecognizerMachine
  · exact codePrefixRecognizerMachine_of_codeUniversalPrefixRunnerConstruction

theorem codePrefixAcceptedLanguage_compiledByDescription_of_programCompiler
    (hcompile : EncodedInputProgramAcceptorCompilationPrinciple) :
    exists D : MachineDescription,
      MachineDescriptionAcceptsEncodedInputLanguage D
        MachineDescription.CodePrefixAcceptedLanguage := by
  rcases hcompile CodePrefixRecognizerProgram with ⟨D, hD⟩
  refine ⟨D, ?_⟩
  constructor
  · exact hD.left
  · intro w
    exact Iff.trans (hD.right w)
      (codePrefixRecognizerProgram_acceptsLanguage w)

structure CodeUniversalPrefixSection53Closeout where
  encodedInputProgramCompiler : EncodedInputProgramAcceptorCompilationPrinciple
  universalRunner : CodeUniversalPrefixRunnerConstruction

structure CodeUniversalPrefixFiniteSourceCloseout where
  encodedInputDescriptionCompiler : EncodedInputDescriptionCompilerPrinciple
  prefixRecognizerMachine : CodePrefixRecognizerMachineConstruction

structure CodeUniversalPrefixRunnerFiniteSourceCloseout where
  prefixRecognizerMachine : CodePrefixRecognizerMachineConstruction

theorem codeUniversalPrefixMachine_halts_on_encoded_description_iff
    {universal : TuringMachine MachineCodeSymbol state}
    (hspec : CodeUniversalPrefixMachineSpec universal)
    (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    TuringMachine.HaltsOnInput universal
      (Languages.Word.Concat (MachineDescription.encodeDescription D) input) <->
        D.HaltsOnInput (MachineDescription.encodeCodeWordAsInput input) := by
  exact Iff.trans
    (hspec (Languages.Word.Concat (MachineDescription.encodeDescription D) input))
    (MachineDescription.codePrefixAccepts_encodeDescription_append_iff D input)

theorem codeUniversalPrefixMachine_rowLanguage_equal_encodedInputLanguage
    {universal : TuringMachine MachineCodeSymbol state}
    (hspec : CodeUniversalPrefixMachineSpec universal)
    (D : MachineDescription) :
    Language.Equal
      (CodeUniversalPrefixMachineRowLanguage universal
        (MachineDescription.encodeDescription D))
      (MachineDescription.EncodedInputLanguage D) :=
  codeUniversalPrefixMachine_halts_on_encoded_description_iff hspec D

theorem codeUniversalPrefixRowsCoverAcceptableLanguages_of_encodedInputDescriptionCompiler
    {universal : TuringMachine MachineCodeSymbol state}
    (hspec : CodeUniversalPrefixMachineSpec universal)
    (hcompile : EncodedInputDescriptionCompilerPrinciple) :
    CodeUniversalPrefixRowsCoverAcceptableLanguages universal := by
  intro L hL
  cases hcompile L hL with
  | intro D hD =>
      exists MachineDescription.encodeDescription D
      exact Language.equal_trans
        (codeUniversalPrefixMachine_rowLanguage_equal_encodedInputLanguage
          hspec D)
        hD.right

theorem codeUniversalPrefixRowsCoverConstruction_of_constructions
    (hcompile : EncodedInputDescriptionCompilerPrinciple)
    (hrunner : CodeUniversalPrefixRunnerConstruction) :
    CodeUniversalPrefixRowsCoverConstruction := by
  unfold CodeUniversalPrefixRunnerConstruction at hrunner
  rcases hrunner with ⟨state, universal, hspec⟩
  exact
    ⟨state, universal,
      hspec,
      codeUniversalPrefixRowsCoverAcceptableLanguages_of_encodedInputDescriptionCompiler
        hspec hcompile⟩

theorem codeUniversalPrefixRowsCoverConstruction_of_finiteSourceCloseout
    (hclose : CodeUniversalPrefixFiniteSourceCloseout) :
    CodeUniversalPrefixRowsCoverConstruction :=
  codeUniversalPrefixRowsCoverConstruction_of_constructions
    hclose.encodedInputDescriptionCompiler
    (codeUniversalPrefixRunnerConstruction_of_codePrefixRecognizerMachine
      hclose.prefixRecognizerMachine)

theorem codeUniversalPrefixRunnerConstruction_of_runnerFiniteSourceCloseout
    (hclose : CodeUniversalPrefixRunnerFiniteSourceCloseout) :
    CodeUniversalPrefixRunnerConstruction :=
  codeUniversalPrefixRunnerConstruction_of_codePrefixRecognizerMachine
    hclose.prefixRecognizerMachine

/-!
**Section 5.3 finite-source scaffold.**  The universal-machine construction
target is the prefix version.  The finite-source scaffold below is the active
deferred fixed-alphabet prefix recognizer machine target.  Row coverage over all
recursively enumerable code-symbol languages still requires an explicit
encoded-input description compiler, as in
{name}`codeUniversalPrefixRowsCoverConstruction_of_finiteSourceCloseout`.
-/

def CodePrefixDescriptionHeaderFieldsParserConstruction : Prop :=
  exists state : Type,
  exists parser : TuringMachine MachineCodeSymbol state,
    forall tokens : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput parser tokens <->
        exists stateCount start halt transitionCount : Nat,
        exists rest : Word MachineCodeSymbol,
          tokens =
            MachineCodeSymbol.header ::
              MachineDescription.encodeNatAppend stateCount
                (MachineDescription.encodeNatAppend start
                  (MachineDescription.encodeNatAppend halt
                    (MachineDescription.encodeNatAppend transitionCount
                      rest)))

def CodePrefixDescriptionTransitionListParserConstruction : Prop :=
  exists state : Type,
  exists parser : TuringMachine MachineCodeSymbol state,
    forall count : Nat,
    forall tokens : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput parser
          (MachineDescription.encodeNatAppend count tokens) <->
        exists transitions : List TransitionDescription,
        exists suffix : Word MachineCodeSymbol,
          MachineDescription.decodeTransitions count tokens =
            some (transitions, suffix)

def CodePrefixParserNormalizerIdentityMachineSpec
    (normalizer : TuringMachine MachineCodeSymbol state) : Prop :=
  forall tokens out : Word MachineCodeSymbol,
    TuringMachine.HaltsWithOutput normalizer tokens out <->
      out = tokens ∧
        exists D : MachineDescription,
        exists input : Word MachineCodeSymbol,
          MachineDescription.decodeDescriptionPrefix tokens =
            some (D, input)

def CodePrefixParserNormalizerIdentityMachineConstruction : Prop :=
  exists state : Type,
  exists normalizer : TuringMachine MachineCodeSymbol state,
    CodePrefixParserNormalizerIdentityMachineSpec normalizer

theorem codePrefixParserNormalizerCodeMachineConstruction_of_identityMachine
    (hidentity : CodePrefixParserNormalizerIdentityMachineConstruction) :
    CodePrefixParserNormalizerCodeMachineConstruction := by
  rcases hidentity with ⟨state, normalizer, hnormalizer⟩
  refine ⟨state, normalizer, ?_⟩
  intro tokens out
  rw [hnormalizer tokens out]
  constructor
  · intro h
    rcases h with ⟨hout, D, input, hdecode⟩
    exact
      (codePrefixParserNormalizerCode_transform_eq_some_iff
        tokens out).mpr
        ⟨D, input, hdecode,
          by
            rw [hout]
            exact
              MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescription_append
                hdecode⟩
  · intro h
    rcases
        (codePrefixParserNormalizerCode_transform_eq_some_iff
          tokens out).mp h with
      ⟨D, input, hdecode, hout⟩
    have htokens :
        tokens = List.append (MachineDescription.encodeDescription D) input :=
      MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescription_append
        hdecode
    exact ⟨by rw [htokens, hout], D, input, hdecode⟩

def CodePrefixParserBranchFailureEmitterConstruction : Prop :=
  exists state : Type,
  exists emitter : TuringMachine MachineCodeSymbol state,
    forall tokens out : Word MachineCodeSymbol,
      TuringMachine.HaltsWithOutput emitter tokens out <->
        MachineDescription.decodeDescriptionPrefix tokens = none ∧
          out = MachineDescription.encodeBoolWord [false]

def CodePrefixParserBranchSuccessEmitterConstruction : Prop :=
  exists state : Type,
  exists emitter : TuringMachine MachineCodeSymbol state,
    forall tokens out : Word MachineCodeSymbol,
      TuringMachine.HaltsWithOutput emitter tokens out <->
        exists D : MachineDescription,
        exists input : Word MachineCodeSymbol,
          MachineDescription.decodeDescriptionPrefix tokens =
              some (D, input) ∧
            out =
              MachineDescription.encodeBoolWordAppend [true] tokens

def CodePrefixParserBranchTaggedMachineSpec
    (branch : TuringMachine MachineCodeSymbol state) : Prop :=
  forall tokens out : Word MachineCodeSymbol,
    TuringMachine.HaltsWithOutput branch tokens out <->
      (MachineDescription.decodeDescriptionPrefix tokens = none ∧
        out = MachineDescription.encodeBoolWord [false]) ∨
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeDescriptionPrefix tokens =
            some (D, input) ∧
          out =
            MachineDescription.encodeBoolWordAppend [true] tokens

def CodePrefixParserBranchTaggedMachineConstruction : Prop :=
  exists state : Type,
  exists branch : TuringMachine MachineCodeSymbol state,
    CodePrefixParserBranchTaggedMachineSpec branch

theorem codePrefixParserBranchCodeMachineConstruction_of_taggedMachine
    (htagged : CodePrefixParserBranchTaggedMachineConstruction) :
    CodePrefixParserBranchCodeMachineConstruction := by
  rcases htagged with ⟨state, branch, hbranch⟩
  refine ⟨state, branch, ?_⟩
  intro tokens out
  rw [hbranch tokens out]
  constructor
  · intro h
    rcases h with hfailure | hsuccess
    · exact
        (codePrefixParserBranchCode_transform_eq_some_iff
          tokens out).mpr (Or.inl hfailure)
    · rcases hsuccess with ⟨D, input, hdecode, hout⟩
      have htokens :
          tokens = List.append (MachineDescription.encodeDescription D)
            input :=
        MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescription_append
          hdecode
      exact
        (codePrefixParserBranchCode_transform_eq_some_iff
          tokens out).mpr
          (Or.inr
            ⟨D, input, hdecode, by simpa [htokens] using hout⟩)
  · intro h
    rcases
        (codePrefixParserBranchCode_transform_eq_some_iff
          tokens out).mp h with
      hfailure | hsuccess
    · exact Or.inl hfailure
    · rcases hsuccess with ⟨D, input, hdecode, hout⟩
      have htokens :
          tokens = List.append (MachineDescription.encodeDescription D)
            input :=
        MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescription_append
          hdecode
      exact Or.inr
        ⟨D, input, hdecode, by simpa [htokens] using hout⟩

def CodePrefixStageCodeDecoderConstruction : Prop :=
  exists state : Type,
  exists decoder : TuringMachine MachineCodeSymbol state,
    forall tokens : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput decoder tokens <->
        exists stage : Nat,
        exists encoded : Word MachineCodeSymbol,
          tokens = CodePrefixRecognizerStageCode encoded stage

def CodePrefixStageDescriptionPrefixDecoderConstruction : Prop :=
  exists state : Type,
  exists decoder : TuringMachine MachineCodeSymbol state,
    forall encoded : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput decoder encoded <->
        exists D : MachineDescription,
        exists input : Word MachineCodeSymbol,
          MachineDescription.decodeDescriptionPrefix encoded =
            some (D, input)

def CodePrefixDecodedBoundedSimulatorSemanticMachineSpec
    (simulator : TuringMachine MachineCodeSymbol state) : Prop :=
  forall tokens : Word MachineCodeSymbol,
    TuringMachine.HaltsOnInput simulator tokens <->
      exists stage : Nat,
      exists encoded : Word MachineCodeSymbol,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        tokens = CodePrefixRecognizerStageCode encoded stage ∧
          MachineDescription.decodeDescriptionPrefix encoded =
            some (D, input) ∧
          D.HaltsIn stage
            (MachineDescription.encodeCodeWordAsInput input)

def CodePrefixDecodedBoundedSimulatorSemanticMachineConstruction : Prop :=
  exists state : Type,
  exists simulator : TuringMachine MachineCodeSymbol state,
    CodePrefixDecodedBoundedSimulatorSemanticMachineSpec simulator

theorem codePrefixDecodedBoundedSimulatorCodeMachineConstruction_of_semanticMachine
    (hsemantic :
      CodePrefixDecodedBoundedSimulatorSemanticMachineConstruction) :
    CodePrefixDecodedBoundedSimulatorCodeMachineConstruction := by
  rcases hsemantic with ⟨state, simulator, hsimulator⟩
  refine ⟨state, simulator, ?_⟩
  intro tokens
  rw [hsimulator tokens]
  constructor
  · intro h
    exact
      (codePrefixDecodedBoundedSimulatorCode_transform_eq_some_iff
        tokens ([] : Word MachineCodeSymbol)).mpr
        ⟨rfl, h⟩
  · intro h
    exact
      ((codePrefixDecodedBoundedSimulatorCode_transform_eq_some_iff
        tokens ([] : Word MachineCodeSymbol)).mp h).right

def CodePrefixStageSearchControllerCoreConstruction : Prop :=
  forall {simulatorState : Type}
    (simulator : TuringMachine MachineCodeSymbol simulatorState),
    CodePrefixDecodedBoundedSimulatorSpec simulator ->
      exists searcherState : Type,
      exists searcher : TuringMachine MachineCodeSymbol searcherState,
        CodePrefixStageSearchControllerSpec simulator searcher

theorem codePrefixDescriptionHeaderFieldsParserConstruction_scaffold :
    CodePrefixDescriptionHeaderFieldsParserConstruction := by
  sorry

theorem codePrefixDescriptionTransitionListParserConstruction_scaffold :
    CodePrefixDescriptionTransitionListParserConstruction := by
  sorry

theorem codePrefixParserNormalizerIdentityMachineConstruction_of_parserComponents
    (hheader : CodePrefixDescriptionHeaderFieldsParserConstruction)
    (htransitions : CodePrefixDescriptionTransitionListParserConstruction) :
    CodePrefixParserNormalizerIdentityMachineConstruction := by
  sorry

theorem codePrefixParserNormalizerCodeMachineConstruction_scaffold :
    CodePrefixParserNormalizerCodeMachineConstruction :=
  codePrefixParserNormalizerCodeMachineConstruction_of_identityMachine
    (codePrefixParserNormalizerIdentityMachineConstruction_of_parserComponents
      codePrefixDescriptionHeaderFieldsParserConstruction_scaffold
      codePrefixDescriptionTransitionListParserConstruction_scaffold)

theorem codePrefixParserNormalizerMachineConstruction_scaffold :
    CodePrefixParserNormalizerMachineConstruction :=
  codePrefixParserNormalizerMachineConstruction_of_codeMachine
    codePrefixParserNormalizerCodeMachineConstruction_scaffold

theorem codePrefixParserBranchFailureEmitterConstruction_scaffold :
    CodePrefixParserBranchFailureEmitterConstruction := by
  sorry

theorem codePrefixParserBranchSuccessEmitterConstruction_scaffold :
    CodePrefixParserBranchSuccessEmitterConstruction := by
  sorry

theorem codePrefixParserBranchTaggedMachineConstruction_of_emitters
    (hfailure : CodePrefixParserBranchFailureEmitterConstruction)
    (hsuccess : CodePrefixParserBranchSuccessEmitterConstruction) :
    CodePrefixParserBranchTaggedMachineConstruction := by
  sorry

theorem codePrefixParserBranchCodeMachineConstruction_scaffold :
    CodePrefixParserBranchCodeMachineConstruction :=
  codePrefixParserBranchCodeMachineConstruction_of_taggedMachine
    (codePrefixParserBranchTaggedMachineConstruction_of_emitters
      codePrefixParserBranchFailureEmitterConstruction_scaffold
      codePrefixParserBranchSuccessEmitterConstruction_scaffold)

theorem codePrefixParserBranchMachineConstruction_scaffold :
    CodePrefixParserBranchMachineConstruction :=
  codePrefixParserBranchMachineConstruction_of_codeMachine
    codePrefixParserBranchCodeMachineConstruction_scaffold

theorem codePrefixStageCodeDecoderConstruction_scaffold :
    CodePrefixStageCodeDecoderConstruction := by
  sorry

theorem codePrefixStageDescriptionPrefixDecoderConstruction_scaffold :
    CodePrefixStageDescriptionPrefixDecoderConstruction := by
  sorry

theorem codePrefixDecodedBoundedSimulatorSemanticMachineConstruction_of_decoders
    (hstage : CodePrefixStageCodeDecoderConstruction)
    (hdescription : CodePrefixStageDescriptionPrefixDecoderConstruction) :
    CodePrefixDecodedBoundedSimulatorSemanticMachineConstruction := by
  sorry

theorem codePrefixDecodedBoundedSimulatorCodeMachineConstruction_scaffold :
    CodePrefixDecodedBoundedSimulatorCodeMachineConstruction :=
  codePrefixDecodedBoundedSimulatorCodeMachineConstruction_of_semanticMachine
    (codePrefixDecodedBoundedSimulatorSemanticMachineConstruction_of_decoders
      codePrefixStageCodeDecoderConstruction_scaffold
      codePrefixStageDescriptionPrefixDecoderConstruction_scaffold)

theorem codePrefixDecodedBoundedSimulatorConstruction_scaffold :
    CodePrefixDecodedBoundedSimulatorConstruction :=
  codePrefixDecodedBoundedSimulatorConstruction_of_codeMachine
    codePrefixDecodedBoundedSimulatorCodeMachineConstruction_scaffold

theorem codePrefixStageSearchControllerCoreConstruction_scaffold :
    CodePrefixStageSearchControllerCoreConstruction := by
  sorry

theorem codePrefixStageSearchControllerConstruction_scaffold :
    CodePrefixStageSearchControllerConstruction := by
  intro normalizerState branchState simulatorState
    normalizer branch simulator hnormalizer hbranch hsimulator
  exact codePrefixStageSearchControllerCoreConstruction_scaffold
    simulator hsimulator

theorem codePrefixRecognizerMachineConstruction_scaffold :
    CodePrefixRecognizerMachineConstruction :=
  codePrefixRecognizerMachineConstruction_of_finiteSourceComponents
    codePrefixParserNormalizerMachineConstruction_scaffold
    codePrefixParserBranchMachineConstruction_scaffold
    codePrefixDecodedBoundedSimulatorConstruction_scaffold
    codePrefixStageSearchControllerConstruction_scaffold

def codeUniversalPrefixRunnerFiniteSourceCloseout_scaffold :
    CodeUniversalPrefixRunnerFiniteSourceCloseout where
  prefixRecognizerMachine :=
    codePrefixRecognizerMachineConstruction_scaffold

theorem codeUniversalPrefixRunnerConstruction_scaffold :
    CodeUniversalPrefixRunnerConstruction :=
  codeUniversalPrefixRunnerConstruction_of_runnerFiniteSourceCloseout
    codeUniversalPrefixRunnerFiniteSourceCloseout_scaffold

theorem encodedInputProgramCompiledByDescription_acceptsLanguage
    {P : StagedProgram MachineCodeSymbol Unit}
    {D : MachineDescription}
    {L : Language MachineCodeSymbol}
    (hP : ProgramAcceptsLanguage P L)
    (hcompile : EncodedInputProgramCompiledByDescription P D) :
    MachineDescriptionAcceptsEncodedInputLanguage D L := by
  constructor
  · exact hcompile.left
  · intro w
    exact Iff.trans (hcompile.right w) (hP w)

theorem encodedInputProgramAcceptorCompilationPrinciple_of_descriptionProgramCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple) :
    EncodedInputProgramAcceptorCompilationPrinciple := by
  intro P
  rcases hcompile (EncodedInputBoolProgram P) with ⟨D, hD⟩
  refine ⟨D, ?_⟩
  constructor
  · exact hD.left
  · intro w
    exact Iff.trans
      (hD.right (MachineDescription.encodeCodeWordAsInput w))
      (encodedInputBoolProgram_halts_encodeCodeWordAsInput_iff P w)

theorem encodedInputDescriptionCompilerPrinciple_of_programCompiler
    (hcompile : EncodedInputProgramAcceptorCompilationPrinciple) :
    EncodedInputDescriptionCompilerPrinciple := by
  intro L hL
  cases recursivelyEnumerable_has_acceptanceTrace hL with
  | intro trace htrace =>
      cases hcompile (TraceRecognizerProgram trace) with
      | intro D hD =>
          exists D
          exact encodedInputProgramCompiledByDescription_acceptsLanguage
            (traceRecognizerProgram_acceptsLanguage htrace) hD

theorem encodedInputDescriptionCompilerPrinciple_of_descriptionProgramCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple) :
    EncodedInputDescriptionCompilerPrinciple :=
  encodedInputDescriptionCompilerPrinciple_of_programCompiler
    (encodedInputProgramAcceptorCompilationPrinciple_of_descriptionProgramCompiler
      hcompile)

theorem codeUniversalPrefixRowsCoverConstruction_of_section53Closeout
    (hclose : CodeUniversalPrefixSection53Closeout) :
    CodeUniversalPrefixRowsCoverConstruction :=
  codeUniversalPrefixRowsCoverConstruction_of_constructions
    (encodedInputDescriptionCompilerPrinciple_of_programCompiler
      hclose.encodedInputProgramCompiler)
    hclose.universalRunner

/-!
**Compiled partial-function ranges.**
-/

def PartialFunctionCompiledByDescription
    (f : Word input -> Option (Word Bool))
    (encodeInput : input -> Bool)
    (D : MachineDescription) : Prop :=
  D.WellFormed ∧
    forall w : Word input,
      match f w with
      | some out => D.HaltsWithOutput (EncodeWord encodeInput w) out
      | none => ¬ D.HaltsOnInput (EncodeWord encodeInput w)

theorem partialFunctionCompiledByDescription_turingComputablePartial
    {f : Word input -> Option (Word Bool)}
    {encodeInput : input -> Bool}
    {D : MachineDescription}
    (h : PartialFunctionCompiledByDescription f encodeInput D) :
    TuringComputablePartial f := by
  exists Bool
  exists Fin (D.stateCount + 1)
  exists D.toTuringMachine
  exists encodeInput
  exists fun b : Bool => b
  intro w
  cases hf : f w with
  | none =>
      have hnone := h.right w
      rw [hf] at hnone
      intro hhalt
      exact hnone ((MachineDescription.toTuringMachine_haltsOnInput_iff
        h.left (EncodeWord encodeInput w)).mp hhalt)
  | some out =>
      have hsome := h.right w
      rw [hf] at hsome
      simp at hsome
      simpa [encodeWord_id] using
        (MachineDescription.toTuringMachine_haltsWithOutput_iff
          h.left (EncodeWord encodeInput w) out).mpr hsome

def PartialUnaryTuringComputableRange (L : Language Bool) : Prop :=
  exists f : Word Unit -> Option (Word Bool),
    TuringComputablePartial f ∧ Language.Equal (PartialRangeLanguage f) L

def CompiledPartialUnaryRange (L : Language Bool) : Prop :=
  exists f : Word Unit -> Option (Word Bool), exists D : MachineDescription,
    PartialFunctionCompiledByDescription f (fun _ : Unit => true) D ∧
      Language.Equal (PartialRangeLanguage f) L

def CompiledPartialUnaryFunctionProgramRange (L : Language Bool) : Prop :=
  exists f : Word Unit -> Option (Word Bool), exists D : MachineDescription,
    PartialFunctionCompiledByDescription f (fun _ : Unit => true) D ∧
      Language.Equal (ProgramRangeLanguage (PartialFunctionProgram f)) L

def PartialUnaryRangeDescriptionCompilerPrinciple : Prop :=
  forall f : Word Unit -> Option (Word Bool),
    exists D : MachineDescription,
      PartialFunctionCompiledByDescription f (fun _ : Unit => true) D

def SemanticPartialUnaryRangeCompilerAssumption : Prop :=
  PartialUnaryRangeDescriptionCompilerPrinciple

/-!
The partial-unary compiler principle is intentionally strong: its source is an
arbitrary semantic Lean partial function, not a finite program syntax.  The
following consequences make that strength explicit.  Concrete closeouts should
therefore keep this principle as a named construction boundary unless a finite
source syntax is supplied.
-/

theorem partialUnaryRangeDescriptionCompilerPrinciple_turingComputablePartial
    (hcompile : PartialUnaryRangeDescriptionCompilerPrinciple)
    (f : Word Unit -> Option (Word Bool)) :
    TuringComputablePartial f := by
  rcases hcompile f with ⟨D, hD⟩
  exact partialFunctionCompiledByDescription_turingComputablePartial hD

theorem partialUnaryRangeDescriptionCompilerPrinciple_compiledRange
    (hcompile : PartialUnaryRangeDescriptionCompilerPrinciple)
    (f : Word Unit -> Option (Word Bool)) :
    CompiledPartialUnaryRange (PartialRangeLanguage f) := by
  rcases hcompile f with ⟨D, hD⟩
  exact ⟨f, D, hD, Language.equal_refl (PartialRangeLanguage f)⟩

theorem partialUnaryRangeDescriptionCompilerPrinciple_compiledProgramRange
    (hcompile : PartialUnaryRangeDescriptionCompilerPrinciple)
    (f : Word Unit -> Option (Word Bool)) :
    CompiledPartialUnaryFunctionProgramRange
      (ProgramRangeLanguage (PartialFunctionProgram f)) := by
  rcases hcompile f with ⟨D, hD⟩
  exact ⟨f, D, hD,
    Language.equal_refl
      (ProgramRangeLanguage (PartialFunctionProgram f))⟩

theorem compiledPartialUnaryRange_partialRangeOfUnaryFunction
    {L : Language Bool}
    (h : CompiledPartialUnaryRange L) :
    PartialRangeOfUnaryFunction L := by
  cases h with
  | intro f hf =>
      cases hf with
      | intro _ hD =>
          exists f
          exact hD.right

theorem compiledPartialUnaryRange_turingComputableRange
    {L : Language Bool}
    (h : CompiledPartialUnaryRange L) :
    PartialUnaryTuringComputableRange L := by
  cases h with
  | intro f hf =>
      cases hf with
      | intro D hD =>
          exists f
          constructor
          · exact partialFunctionCompiledByDescription_turingComputablePartial
              hD.left
          · exact hD.right

theorem compiledPartialUnaryFunctionProgramRange_compiledRange
    {L : Language Bool}
    (h : CompiledPartialUnaryFunctionProgramRange L) :
    CompiledPartialUnaryRange L := by
  cases h with
  | intro f hf =>
      cases hf with
      | intro D hD =>
          exists f
          exists D
          constructor
          · exact hD.left
          · exact Language.equal_trans
              (Language.equal_symm (partialFunctionProgram_range f))
              hD.right

theorem compiledPartialUnaryFunctionProgramRange_turingComputableRange
    {L : Language Bool}
    (h : CompiledPartialUnaryFunctionProgramRange L) :
    PartialUnaryTuringComputableRange L :=
  compiledPartialUnaryRange_turingComputableRange
    (compiledPartialUnaryFunctionProgramRange_compiledRange h)

theorem compiledPartialUnaryFunctionProgramRange_partialRange
    {L : Language Bool}
    (h : CompiledPartialUnaryFunctionProgramRange L) :
    PartialRangeOfUnaryFunction L :=
  compiledPartialUnaryRange_partialRangeOfUnaryFunction
    (compiledPartialUnaryFunctionProgramRange_compiledRange h)

theorem compiledPartialUnaryRange_of_partialRangeOfUnaryFunction
    (hcompile : PartialUnaryRangeDescriptionCompilerPrinciple)
    {L : Language Bool}
    (h : PartialRangeOfUnaryFunction L) :
    CompiledPartialUnaryRange L := by
  cases h with
  | intro f hf =>
      cases hcompile f with
      | intro D hD =>
          exact Exists.intro f (Exists.intro D (And.intro hD hf))

theorem compiledPartialUnaryRange_of_partiallyListable
    (hcompile : PartialUnaryRangeDescriptionCompilerPrinciple)
    {L : Language Bool}
    (h : PartiallyListable L) :
    CompiledPartialUnaryRange L :=
  compiledPartialUnaryRange_of_partialRangeOfUnaryFunction
    hcompile (partiallyListable_partialRangeOfUnaryFunction h)

theorem compiledPartialUnaryFunctionProgramRange_of_partialRangeOfUnaryFunction
    (hcompile : PartialUnaryRangeDescriptionCompilerPrinciple)
    {L : Language Bool}
    (h : PartialRangeOfUnaryFunction L) :
    CompiledPartialUnaryFunctionProgramRange L := by
  cases h with
  | intro f hf =>
      cases hcompile f with
      | intro D hD =>
          exact Exists.intro f
            (Exists.intro D
              (And.intro hD
                (Language.equal_trans (partialFunctionProgram_range f) hf)))

theorem compiledPartialUnaryFunctionProgramRange_of_partiallyListable
    (hcompile : PartialUnaryRangeDescriptionCompilerPrinciple)
    {L : Language Bool}
    (h : PartiallyListable L) :
    CompiledPartialUnaryFunctionProgramRange L :=
  compiledPartialUnaryFunctionProgramRange_of_partialRangeOfUnaryFunction
    hcompile (partiallyListable_partialRangeOfUnaryFunction h)

theorem compiledPartialUnaryRange_of_unaryProgramRange
    (hcompile : PartialUnaryRangeDescriptionCompilerPrinciple)
    (P : StagedProgram Unit Bool) :
    CompiledPartialUnaryRange (ProgramRangeLanguage P) :=
  compiledPartialUnaryRange_of_partialRangeOfUnaryFunction
    hcompile (programRange_partialRangeOfUnaryFunction P)

theorem compiledPartialUnaryFunctionProgramRange_of_unaryProgramRange
    (hcompile : PartialUnaryRangeDescriptionCompilerPrinciple)
    (P : StagedProgram Unit Bool) :
    CompiledPartialUnaryFunctionProgramRange (ProgramRangeLanguage P) :=
  compiledPartialUnaryFunctionProgramRange_of_partialRangeOfUnaryFunction
    hcompile (programRange_partialRangeOfUnaryFunction P)


end Computability
end FoC
