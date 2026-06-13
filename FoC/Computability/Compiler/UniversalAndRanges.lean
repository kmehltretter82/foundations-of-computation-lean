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

def CodeUniversalMachineSpec
    (universal : TuringMachine MachineCodeSymbol state) : Prop :=
  forall machine input : Word MachineCodeSymbol,
    TuringMachine.HaltsOnInput universal
      (Languages.Word.Concat machine input) <->
        MachineDescription.CodeAccepts machine input

def ImmediateHaltingDescription : MachineDescription where
  stateCount := 1
  start := 0
  halt := 0
  transitions := []

theorem immediateHaltingDescription_haltsOnInput
    (input : Word Bool) :
    ImmediateHaltingDescription.HaltsOnInput input := by
  exact ⟨0, rfl⟩

theorem codeAccepts_empty_false
    (input : Word MachineCodeSymbol) :
    ¬ MachineDescription.CodeAccepts [] input := by
  intro h
  rcases h with ⟨D, hdecode, _⟩
  simp [MachineDescription.decodeDescription] at hdecode

theorem codeUniversalMachineSpec_rawConcat_inconsistent
    (universal : TuringMachine MachineCodeSymbol state) :
    ¬ CodeUniversalMachineSpec universal := by
  intro hspec
  let D := ImmediateHaltingDescription
  have haccept :
      MachineDescription.CodeAccepts
        (MachineDescription.encodeDescription D) [] :=
    MachineDescription.codeAccepts_of_encodeDescription
      (immediateHaltingDescription_haltsOnInput [])
  have hhalts :
      TuringMachine.HaltsOnInput universal
        (Languages.Word.Concat (MachineDescription.encodeDescription D) []) :=
    (hspec (MachineDescription.encodeDescription D) []).mpr haccept
  have hhaltsEmpty :
      TuringMachine.HaltsOnInput universal
        (Languages.Word.Concat [] (MachineDescription.encodeDescription D)) := by
    simpa [Languages.Word.Concat] using hhalts
  have hfalse :
      MachineDescription.CodeAccepts []
        (MachineDescription.encodeDescription D) :=
    (hspec [] (MachineDescription.encodeDescription D)).mp hhaltsEmpty
  exact codeAccepts_empty_false (MachineDescription.encodeDescription D) hfalse

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

def CodeUniversalMachineRowLanguage
    (universal : TuringMachine MachineCodeSymbol state)
    (machine : Word MachineCodeSymbol) : Language MachineCodeSymbol :=
  fun input => TuringMachine.HaltsOnInput universal
    (Languages.Word.Concat machine input)

def CodeUniversalRowsCoverAcceptableLanguages
    (universal : TuringMachine MachineCodeSymbol state) : Prop :=
  forall L : Language MachineCodeSymbol, RecursivelyEnumerable L ->
    exists machine : Word MachineCodeSymbol,
      Language.Equal (CodeUniversalMachineRowLanguage universal machine) L

def CodeUniversalRunnerConstruction : Prop :=
  exists state : Type,
    exists universal : TuringMachine MachineCodeSymbol state,
      CodeUniversalMachineSpec universal

theorem not_codeUniversalRunnerConstruction :
    ¬ CodeUniversalRunnerConstruction := by
  intro h
  unfold CodeUniversalRunnerConstruction at h
  rcases h with ⟨state, universal, hspec⟩
  exact codeUniversalMachineSpec_rawConcat_inconsistent universal hspec

def CodeUniversalRowsCoverConstruction : Prop :=
  exists state : Type,
    exists universal : TuringMachine MachineCodeSymbol state,
      CodeUniversalMachineSpec universal ∧
        CodeUniversalRowsCoverAcceptableLanguages universal

structure CodeUniversalSection53Closeout where
  encodedInputProgramCompiler : EncodedInputProgramAcceptorCompilationPrinciple
  universalRunner : CodeUniversalRunnerConstruction

theorem not_codeUniversalSection53Closeout :
    ¬ CodeUniversalSection53Closeout := by
  intro hclose
  exact not_codeUniversalRunnerConstruction hclose.universalRunner

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

theorem codeUniversalMachineRowLanguage_equal_codeAcceptedLanguage
    {universal : TuringMachine MachineCodeSymbol state}
    (hspec : CodeUniversalMachineSpec universal)
    (machine : Word MachineCodeSymbol) :
    Language.Equal
      (CodeUniversalMachineRowLanguage universal machine)
      (MachineDescription.CodeAcceptedLanguage machine) :=
  hspec machine

theorem codeUniversalMachineRowLanguage_equal_encodedInputLanguage
    {universal : TuringMachine MachineCodeSymbol state}
    (hspec : CodeUniversalMachineSpec universal)
    (D : MachineDescription) :
    Language.Equal
      (CodeUniversalMachineRowLanguage universal
        (MachineDescription.encodeDescription D))
      (MachineDescription.EncodedInputLanguage D) := by
  intro input
  exact Iff.trans
    (codeUniversalMachineRowLanguage_equal_codeAcceptedLanguage
      hspec (MachineDescription.encodeDescription D) input)
    (MachineDescription.codeAccepts_encodeDescription_iff D input)

theorem codeUniversalRowsCoverAcceptableLanguages_of_encodedInputDescriptionCompiler
    {universal : TuringMachine MachineCodeSymbol state}
    (hspec : CodeUniversalMachineSpec universal)
    (hcompile : EncodedInputDescriptionCompilerPrinciple) :
    CodeUniversalRowsCoverAcceptableLanguages universal := by
  intro L hL
  cases hcompile L hL with
  | intro D hD =>
      exists MachineDescription.encodeDescription D
      exact Language.equal_trans
        (codeUniversalMachineRowLanguage_equal_encodedInputLanguage hspec D)
        hD.right

theorem codeUniversalRowsCoverConstruction_of_constructions
    (hcompile : EncodedInputDescriptionCompilerPrinciple)
    (hrunner : CodeUniversalRunnerConstruction) :
    CodeUniversalRowsCoverConstruction := by
  cases hrunner with
  | intro state hstate =>
      cases hstate with
      | intro universal hspec =>
          exact
            Exists.intro state
              (Exists.intro universal
                (And.intro hspec
                  (codeUniversalRowsCoverAcceptableLanguages_of_encodedInputDescriptionCompiler
                    hspec hcompile)))

theorem encodedInputDescriptionCompilerPrinciple_of_section53Closeout
    (hclose : CodeUniversalSection53Closeout) :
    EncodedInputDescriptionCompilerPrinciple :=
  encodedInputDescriptionCompilerPrinciple_of_programCompiler
    hclose.encodedInputProgramCompiler

theorem codeUniversalPrefixRowsCoverConstruction_of_section53Closeout
    (hclose : CodeUniversalPrefixSection53Closeout) :
    CodeUniversalPrefixRowsCoverConstruction :=
  codeUniversalPrefixRowsCoverConstruction_of_constructions
    (encodedInputDescriptionCompilerPrinciple_of_programCompiler
      hclose.encodedInputProgramCompiler)
    hclose.universalRunner

theorem codeUniversalRowsCoverConstruction_of_section53Closeout
    (hclose : CodeUniversalSection53Closeout) :
    CodeUniversalRowsCoverConstruction :=
  codeUniversalRowsCoverConstruction_of_constructions
    (encodedInputDescriptionCompilerPrinciple_of_section53Closeout hclose)
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
