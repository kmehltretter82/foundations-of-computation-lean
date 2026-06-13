import FoC.Computability.Coding
import FoC.Computability.Compiler
import FoC.Computability.DiagonalPairMachine
import FoC.Computability.Encoding

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter05
namespace Section03

/-!
# Chapter 5, Section 5.3: The Limits of Computation

This section formalizes the diagonal and halting-problem statements that mark
the limits of computation. The definitions are book-facing wrappers over
{module}`FoC.Computability.Undecidable`,
{module}`FoC.Computability.Coding`, and
{module}`FoC.Computability.Encoding`, with languages represented as predicates
on encoded words.

The page supplies a concrete pair-code alphabet for halting-problem reductions.
It also exposes the first concrete machine-description syntax and interpreter.
Universal-machine execution is still relative to a later proof that this
interpreter can itself be implemented by a concrete machine.

The structure mirrors the standard textbook argument but keeps the implementation
boundary visible. Abstract decoder and diagonalization theorems are proved in
full generality. Concrete code words, machine descriptions, pair encodings, and
interpreter semantics are present. The final step, a single finite universal
machine implementing the decoder relation, remains an explicit construction
target rather than an implicit assumption.
-/

open Languages
open Computability

/-!
## Undecidability Vocabulary

The first definitions name non-computable functions, non-acceptable languages,
undecidable languages, reductions, diagonal languages, universal decoders, and
halting-problem variants.

The wrappers distinguish two kinds of impossibility. An undecidable language
has no total decider. A non-acceptable language has no recognizer at all. The
diagonal languages are the standard tools for proving such statements.

The concrete definitions in this group are intentionally low-level: they expose
machine code symbols, description encoders and decoders, well-formed transition
tables, interpreter configurations, and description-backed self-halting and
pair-halting languages. This gives later construction work a precise target.
-/

def NonComputableStringFunction (f : Word input -> Word output) : Prop :=
  NonComputableFunction f

def NonTuringAcceptableLanguage (L : Language alpha) : Prop :=
  NonAcceptableLanguage L

def UndecidableTuringLanguage (L : Language alpha) : Prop :=
  UndecidableLanguage L

def RecursiveTuringLanguage (L : Language alpha) : Prop :=
  Recursive L

def RecursivelyEnumerableTuringLanguage (L : Language alpha) : Prop :=
  RecursivelyEnumerable L

def DecidableToAcceptableConstruction (alpha : Type u) : Prop :=
  DecidableToAcceptablePrinciple alpha

def TuringDecidableReduction
    (L : Language input) (K : Language output) : Prop :=
  DecidableReduction L K

def TuringAcceptableReduction
    (L : Language input) (K : Language output) : Prop :=
  AcceptableReduction L K

def TuringDiagonalLanguage (acceptsSelf : Word code -> Prop) : Language code :=
  DiagonalLanguage acceptsSelf

def TuringDecoderRecognizes
    (decodeAccepts : Word code -> Word code -> Prop)
    (machine : Word code) (L : Language code) : Prop :=
  DecoderRecognizes decodeAccepts machine L

def TuringSelfDiagonalLanguage
    (decodeAccepts : Word code -> Word code -> Prop) : Language code :=
  SelfDiagonalLanguage decodeAccepts

def TuringDecoderUniversalForAcceptableLanguages
    (decodeAccepts : Word code -> Word code -> Prop) : Prop :=
  DecoderUniversalForAcceptableLanguages decodeAccepts

def TuringDecoderUniversalForAllLanguages
    (decodeAccepts : Word code -> Word code -> Prop) : Prop :=
  DecoderUniversalForAllLanguages decodeAccepts

def TuringHaltingProblem (haltsOnCodeInput : Word code -> Word code -> Prop) :
    Language code :=
  HaltingProblem haltsOnCodeInput

def TuringPairHaltingProblem
    (encodePair : Word code -> Word code -> Word pairSymbol)
    (haltsOnCodeInput : Word code -> Word code -> Prop) :
    Language pairSymbol :=
  PairHaltingProblem encodePair haltsOnCodeInput

def TuringSelfHaltingLanguage
    (haltsOnCodeInput : Word code -> Word code -> Prop) : Language code :=
  SelfHaltingLanguage haltsOnCodeInput

def TuringSelfHaltingPairLanguage
    (encodePair : Word code -> Word code -> Word pairSymbol)
    (haltsOnCodeInput : Word code -> Word code -> Prop) :
    Language pairSymbol :=
  SelfHaltingPairLanguage encodePair haltsOnCodeInput

def DiagonalPairDecidablePreimageConstruction
    (encodePair : Word code -> Word code -> Word pairSymbol) : Prop :=
  DiagonalPairDecidablePreimagePrinciple encodePair

def TuringWordPreimageLanguage
    (map : Word input -> Word output)
    (L : Language output) : Language input :=
  WordPreimageLanguage map L

def TuringDecidablePreimageConstruction
    (map : Word input -> Word output) : Prop :=
  DecidablePreimagePrinciple map

def ComputableMapDecidablePreimageConstruction
    (input : Type u) (output : Type v) : Prop :=
  ComputableMapDecidablePreimagePrinciple input output

def FaithfulComputableMapDecidablePreimageConstruction
    (input : Type u) (output : Type v) : Prop :=
  FaithfulComputableMapDecidablePreimagePrinciple input output

def TuringComputableWordMap (map : Word input -> Word output) : Prop :=
  TuringComputable map

def FaithfulTuringComputableWordMap
    (map : Word input -> Word output) : Prop :=
  FaithfulTuringComputable map

def TuringPairEncodingInjective
    (encodePair : Word code -> Word code -> Word pairSymbol) : Prop :=
  PairEncodingInjective encodePair

def TuringDiagonalPairMap
    (encodePair : Word code -> Word code -> Word pairSymbol) :
    Word code -> Word pairSymbol :=
  DiagonalPairMap encodePair

/-!
The concrete alphabet below is the file's current machine-code model. It
provides pair encodings, finite code symbols, machine descriptions, decoders,
interpreter configurations, and the encoded self-halting languages used by the
later reduction theorems.
-/

def ConcretePairCodeSymbol (code : Type u) : Type u :=
  PairCodeSymbol code

def ConcretePairEncoding (left right : Word code) :
    Word (ConcretePairCodeSymbol code) :=
  PairCodeSymbol.encodePair left right

def ConcreteDiagonalPairMap (w : Word code) :
    Word (ConcretePairCodeSymbol code) :=
  PairCodeSymbol.diagonalMap w

def ConcreteMachineCodeSymbol : Type :=
  MachineCodeSymbol

def ConcreteDiagonalPairMapComputable : Prop :=
  TuringComputableWordMap
    (ConcreteDiagonalPairMap :
      Word ConcreteMachineCodeSymbol ->
        Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))

theorem concrete_diagonal_pair_map_empty :
    ConcreteDiagonalPairMap ([] : Word ConcreteMachineCodeSymbol) =
      [PairCodeSymbol.separator] :=
  rfl

def ConcreteMachineCodeSymbolFinite :
    Foundation.FiniteType ConcreteMachineCodeSymbol :=
  MachineCodeSymbol.finite

/-!
The concrete diagonal-pair machine proof lives in
{module}`FoC.Computability.DiagonalPairMachine`. The primary theorem exposed
here is the faithful witness: the machine preserves distinct machine-code input
symbols and distinct pair-code output symbols through injective encodings. The
older compatibility theorem is kept as a corollary for statements that still
use {name}`TuringComputable`.
-/

def FaithfulConcreteDiagonalPairMapComputable : Prop :=
  FaithfulTuringComputable
    (ConcreteDiagonalPairMap :
      Word ConcreteMachineCodeSymbol ->
        Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))

theorem concrete_diagonal_pair_map_computable_noninjective :
    ConcreteDiagonalPairMapComputable := by
  simpa [ConcreteDiagonalPairMapComputable, TuringComputableWordMap,
    ConcreteDiagonalPairMap, ConcretePairCodeSymbol, ConcreteMachineCodeSymbol,
    Computability.ConcreteDiagonalPairMapComputable,
    Computability.ConcreteDiagonalPairMap,
    Computability.ConcretePairCodeSymbol,
    Computability.ConcreteMachineCodeSymbol]
    using Computability.concrete_diagonal_pair_map_computable_noninjective

theorem faithful_concrete_diagonal_pair_map_computable :
    FaithfulConcreteDiagonalPairMapComputable := by
  simpa [FaithfulConcreteDiagonalPairMapComputable,
    FaithfulTuringComputableWordMap, ConcreteDiagonalPairMap,
    ConcretePairCodeSymbol, ConcreteMachineCodeSymbol,
    Computability.FaithfulConcreteDiagonalPairMapComputable,
    Computability.ConcreteDiagonalPairMap,
    Computability.ConcretePairCodeSymbol,
    Computability.ConcreteMachineCodeSymbol]
    using Computability.faithful_concrete_diagonal_pair_map_computable

theorem concrete_diagonal_pair_map_computable :
    ConcreteDiagonalPairMapComputable :=
  faithfulTuringComputable_to_turingComputable
    faithful_concrete_diagonal_pair_map_computable

def ConcreteMachineTransition : Type :=
  TransitionDescription

def ConcreteMachineDescription : Type :=
  MachineDescription

def ConcreteMachineWellFormed (D : ConcreteMachineDescription) : Prop :=
  MachineDescription.WellFormed D

def ConcreteMachineEncode (D : ConcreteMachineDescription) :
    Word ConcreteMachineCodeSymbol :=
  MachineDescription.encodeDescription D

def ConcreteMachineDecode (w : Word ConcreteMachineCodeSymbol) :
    Option ConcreteMachineDescription :=
  MachineDescription.decodeDescription w

def ConcreteMachineDecodePrefix
    (w : Word ConcreteMachineCodeSymbol) :
    Option (ConcreteMachineDescription × Word ConcreteMachineCodeSymbol) :=
  MachineDescription.decodeDescriptionPrefix w

def ConcreteMachineConfiguration : Type :=
  MachineDescription.Configuration

def ConcreteMachineInitial (D : ConcreteMachineDescription)
    (w : Word Bool) : ConcreteMachineConfiguration :=
  D.initial w

def ConcreteMachineStep (D : ConcreteMachineDescription)
    (c : ConcreteMachineConfiguration) :
    Option ConcreteMachineConfiguration :=
  D.stepConfig c

def ConcreteMachineRunConfig (D : ConcreteMachineDescription)
    (n : Nat) (c : ConcreteMachineConfiguration) :
    ConcreteMachineConfiguration :=
  D.runConfig n c

def ConcreteMachineHaltsOnInput (D : ConcreteMachineDescription)
    (w : Word Bool) : Prop :=
  D.HaltsOnInput w

def ConcreteMachineEncodeCodeInput
    (input : Word ConcreteMachineCodeSymbol) : Word Bool :=
  MachineDescription.encodeCodeWordAsInput input

def ConcreteMachineCodeAccepts
    (machine input : Word ConcreteMachineCodeSymbol) : Prop :=
  MachineDescription.CodeAccepts machine input

def ConcreteMachineCodePrefixAccepts
    (encoded : Word ConcreteMachineCodeSymbol) : Prop :=
  MachineDescription.CodePrefixAccepts encoded

def ConcreteMachineCodeAcceptedLanguage
    (machine : Word ConcreteMachineCodeSymbol) :
    Language ConcreteMachineCodeSymbol :=
  MachineDescription.CodeAcceptedLanguage machine

def ConcreteMachineCodePrefixAcceptedLanguage :
    Language ConcreteMachineCodeSymbol :=
  MachineDescription.CodePrefixAcceptedLanguage

/-!
The prefix decoder relation is semidecidable by a direct staged search: parse
one description prefix, then run the decoded description for the current stage
bound on the encoded suffix. This is the executable semantic target for the
remaining finite universal-runner construction.
-/

noncomputable def ConcreteCodePrefixRecognizerProgram :
    StagedProgram ConcreteMachineCodeSymbol Unit :=
  Computability.CodePrefixRecognizerProgram

theorem concrete_code_prefix_recognizer_program_accepts_language :
    ProgramAcceptsLanguage ConcreteCodePrefixRecognizerProgram
      ConcreteMachineCodePrefixAcceptedLanguage := by
  simpa [ConcreteCodePrefixRecognizerProgram,
    ConcreteMachineCodePrefixAcceptedLanguage]
    using Computability.codePrefixRecognizerProgram_acceptsLanguage

theorem concrete_code_prefix_accepted_language_program_acceptable :
    ProgramAcceptable ConcreteMachineCodePrefixAcceptedLanguage :=
  ⟨ConcreteCodePrefixRecognizerProgram,
    concrete_code_prefix_recognizer_program_accepts_language⟩

def ConcreteCodePrefixParserCodeConstruction : Prop :=
  CodePrefixParserCodeConstruction

theorem concrete_code_prefix_parser_code_construction :
    ConcreteCodePrefixParserCodeConstruction :=
  Computability.codePrefixParserCodeConstruction

theorem concrete_code_prefix_parser_normalize_success_iff
    (tokens : Word ConcreteMachineCodeSymbol) :
    MachineDescription.PrefixParser.normalizeCode tokens = some tokens <->
      exists D : ConcreteMachineDescription,
        exists input : Word ConcreteMachineCodeSymbol,
          ConcreteMachineDecodePrefix tokens = some (D, input) := by
  simpa [ConcreteMachineDecodePrefix, ConcreteMachineDescription,
    ConcreteMachineCodeSymbol]
    using Computability.codePrefixParser_normalize_success_iff tokens

theorem concrete_code_prefix_parser_branch_success
    {tokens : Word ConcreteMachineCodeSymbol}
    {D : ConcreteMachineDescription}
    {input : Word ConcreteMachineCodeSymbol}
    (h : ConcreteMachineDecodePrefix tokens = some (D, input)) :
    MachineDescription.PrefixParser.branchCode tokens =
      some (MachineDescription.encodeBoolWordAppend [true] tokens) :=
  Computability.codePrefixParser_branch_success
    (by
      simpa [ConcreteMachineDecodePrefix] using h)

theorem concrete_code_prefix_parser_branch_failure
    {tokens : Word ConcreteMachineCodeSymbol}
    (h : ConcreteMachineDecodePrefix tokens = none) :
    MachineDescription.PrefixParser.branchCode tokens =
      some (MachineDescription.encodeBoolWord [false]) :=
  Computability.codePrefixParser_branch_failure
    (by
      simpa [ConcreteMachineDecodePrefix] using h)

theorem concrete_code_prefix_parser_branch_total
    (tokens : Word ConcreteMachineCodeSymbol) :
    exists out : Word ConcreteMachineCodeSymbol,
      MachineDescription.PrefixParser.branchCode tokens = some out :=
  Computability.codePrefixParser_branch_total tokens

def ConcreteMachineEncodedInputLanguage
    (D : ConcreteMachineDescription) :
    Language ConcreteMachineCodeSymbol :=
  MachineDescription.EncodedInputLanguage D

def ConcreteMachineSelfHaltingLanguage :
    Language ConcreteMachineCodeSymbol :=
  TuringSelfHaltingLanguage ConcreteMachineCodeAccepts

def ConcreteMachinePairHaltingProblem :
    Language (ConcretePairCodeSymbol ConcreteMachineCodeSymbol) :=
  TuringPairHaltingProblem
    (ConcretePairEncoding :
      Word ConcreteMachineCodeSymbol ->
        Word ConcreteMachineCodeSymbol ->
          Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))
    ConcreteMachineCodeAccepts

def ConcreteMachineDiagonalPairPreimageLanguage :
    Language ConcreteMachineCodeSymbol :=
  TuringWordPreimageLanguage
    (ConcreteDiagonalPairMap :
      Word ConcreteMachineCodeSymbol ->
        Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))
    ConcreteMachinePairHaltingProblem

def ConcreteMachineDecoderUniversalForAcceptableLanguages : Prop :=
  TuringDecoderUniversalForAcceptableLanguages ConcreteMachineCodeAccepts

def ConcreteMachineDescriptionAcceptsEncodedInputLanguage
    (D : ConcreteMachineDescription)
    (L : Language ConcreteMachineCodeSymbol) : Prop :=
  Computability.MachineDescriptionAcceptsEncodedInputLanguage D L

def ConcreteEncodedInputProgramAcceptorCompilationConstruction : Prop :=
  EncodedInputProgramAcceptorCompilationPrinciple

def ConcreteEncodedInputDescriptionCompilerConstruction : Prop :=
  EncodedInputDescriptionCompilerPrinciple

def ConcreteBooleanDescriptionAcceptorCompilationConstruction : Prop :=
  DescriptionProgramAcceptorCompilationPrinciple

theorem concrete_encoded_input_program_compiler_of_boolean_description_compiler
    (hcompile : ConcreteBooleanDescriptionAcceptorCompilationConstruction) :
    ConcreteEncodedInputProgramAcceptorCompilationConstruction :=
  Computability.encodedInputProgramAcceptorCompilationPrinciple_of_descriptionProgramCompiler
    hcompile

theorem concrete_encoded_input_description_compiler_of_boolean_description_compiler
    (hcompile : ConcreteBooleanDescriptionAcceptorCompilationConstruction) :
    ConcreteEncodedInputDescriptionCompilerConstruction :=
  Computability.encodedInputDescriptionCompilerPrinciple_of_descriptionProgramCompiler
    hcompile

theorem concrete_code_prefix_accepted_language_compiled_by_description_of_program_compiler
    (hcompile : ConcreteEncodedInputProgramAcceptorCompilationConstruction) :
    exists D : ConcreteMachineDescription,
      ConcreteMachineDescriptionAcceptsEncodedInputLanguage D
        ConcreteMachineCodePrefixAcceptedLanguage := by
  simpa [ConcreteMachineDescriptionAcceptsEncodedInputLanguage,
    ConcreteMachineCodePrefixAcceptedLanguage,
    ConcreteEncodedInputProgramAcceptorCompilationConstruction]
    using
      Computability.codePrefixAcceptedLanguage_compiledByDescription_of_programCompiler
        hcompile

def ConcreteMachineToTuringMachine (D : ConcreteMachineDescription) :
    TuringMachine Bool (Fin (D.stateCount + 1)) :=
  D.toTuringMachine

def UniversalTuringMachineSpec
    (universal : TuringMachine symbol state)
    (decodeAccepts : Word symbol -> Word symbol -> Prop) : Prop :=
  UniversalMachineSpec universal decodeAccepts

def UniversalMachineRowLanguage
    (universal : TuringMachine symbol state)
    (machine : Word symbol) : Language symbol :=
  fun input => TuringMachine.HaltsOnInput universal
    (Languages.Word.Concat machine input)

def UniversalMachineRowsCoverAcceptableLanguages
    (universal : TuringMachine symbol state) : Prop :=
  forall L : Language symbol, TuringAcceptable L ->
    exists machine : Word symbol,
      Language.Equal (UniversalMachineRowLanguage universal machine) L

def ConcreteUniversalPrefixMachineSpec
    (universal : TuringMachine ConcreteMachineCodeSymbol state) : Prop :=
  CodeUniversalPrefixMachineSpec universal

def ConcreteCodePrefixRecognizerMachineSpec
    (universal : TuringMachine ConcreteMachineCodeSymbol state) : Prop :=
  CodePrefixRecognizerMachineSpec universal

def ConcreteUniversalPrefixRunnerConstruction : Prop :=
  CodeUniversalPrefixRunnerConstruction

def ConcreteCodePrefixRecognizerMachineConstruction : Prop :=
  CodePrefixRecognizerMachineConstruction

def ConcreteUniversalPrefixRowsCoverConstruction : Prop :=
  CodeUniversalPrefixRowsCoverConstruction

abbrev ConcreteSection53UniversalPrefixCloseout :=
  CodeUniversalPrefixSection53Closeout

abbrev ConcreteSection53UniversalPrefixFiniteSourceCloseout :=
  CodeUniversalPrefixFiniteSourceCloseout

abbrev ConcreteSection53UniversalPrefixRunnerFiniteSourceCloseout :=
  CodeUniversalPrefixRunnerFiniteSourceCloseout

theorem concrete_section53_universal_prefix_finite_source_closeout_of_boolean_description_compiler
    (hcompiler : ConcreteBooleanDescriptionAcceptorCompilationConstruction)
    (hrunner : ConcreteCodePrefixRecognizerMachineConstruction) :
    ConcreteSection53UniversalPrefixFiniteSourceCloseout where
  encodedInputDescriptionCompiler :=
    concrete_encoded_input_description_compiler_of_boolean_description_compiler
      hcompiler
  prefixRecognizerMachine := hrunner

theorem concrete_section53_universal_prefix_closeout_of_constructions
    (hcompiler : ConcreteEncodedInputProgramAcceptorCompilationConstruction)
    (hrunner : ConcreteUniversalPrefixRunnerConstruction) :
    ConcreteSection53UniversalPrefixCloseout where
  encodedInputProgramCompiler := hcompiler
  universalRunner := hrunner

theorem concrete_universal_prefix_runner_of_code_prefix_recognizer_machine
    (hrunner : ConcreteCodePrefixRecognizerMachineConstruction) :
    ConcreteUniversalPrefixRunnerConstruction :=
  Computability.codeUniversalPrefixRunnerConstruction_of_codePrefixRecognizerMachine
    hrunner

theorem concrete_code_prefix_recognizer_machine_of_universal_prefix_runner
    (hrunner : ConcreteUniversalPrefixRunnerConstruction) :
    ConcreteCodePrefixRecognizerMachineConstruction :=
  Computability.codePrefixRecognizerMachine_of_codeUniversalPrefixRunnerConstruction
    hrunner

theorem concrete_code_prefix_recognizer_machine_iff_universal_prefix_runner :
    ConcreteCodePrefixRecognizerMachineConstruction <->
      ConcreteUniversalPrefixRunnerConstruction :=
  Computability.codePrefixRecognizerMachineConstruction_iff_universalPrefixRunner

def ConcreteUniversalPrefixMachineRowsCoverAcceptableLanguages
    (universal : TuringMachine ConcreteMachineCodeSymbol state) : Prop :=
  CodeUniversalPrefixRowsCoverAcceptableLanguages universal

/-!
**Reductions and Closure.**

Undecidability and non-acceptability are transported by equality and by the
appropriate reduction notions. Complement theorems record that decidability
and undecidability are symmetric under language complement.

A reduction packages the idea "if the target problem were solvable, then the
source problem would be solvable." Therefore an impossible source problem
transfers impossibility to the target.

The section uses two reduction strengths. Decidable reductions are enough for
undecidability transfer. Acceptable reductions are used when the conclusion is
non-acceptability. The pair-halting results later specialize these general
transfer principles to concrete diagonal pair encodings.
-/

theorem undecidable_of_not_decidable {L : Language alpha}
    (h : ¬ TuringDecidable L) : UndecidableTuringLanguage L :=
  Computability.undecidable_of_not_decidable h

theorem undecidable_language_of_equal {L K : Language alpha}
    (h : UndecidableTuringLanguage L) (hEq : Language.Equal L K) :
    UndecidableTuringLanguage K :=
  Computability.undecidable_of_equal h hEq

theorem undecidable_language_complement {L : Language alpha}
    (h : UndecidableTuringLanguage L) :
    UndecidableTuringLanguage (Language.Compl L) :=
  Computability.undecidable_complement h

theorem undecidable_language_of_undecidable_complement {L : Language alpha}
    (h : UndecidableTuringLanguage (Language.Compl L)) :
    UndecidableTuringLanguage L :=
  Computability.undecidable_of_complement h

theorem undecidable_language_complement_iff {L : Language alpha} :
    UndecidableTuringLanguage (Language.Compl L) <-> UndecidableTuringLanguage L :=
  Computability.undecidable_complement_iff

theorem decidable_reduction_refl (L : Language alpha) :
    TuringDecidableReduction L L :=
  Computability.decidableReduction_refl L

theorem decidable_reduction_trans
    {L : Language alpha} {K : Language beta} {H : Language gamma}
    (hLK : TuringDecidableReduction L K)
    (hKH : TuringDecidableReduction K H) :
    TuringDecidableReduction L H :=
  Computability.decidableReduction_trans hLK hKH

theorem undecidable_of_decidable_reduction
    {L : Language alpha} {K : Language beta}
    (hred : TuringDecidableReduction L K)
    (hL : UndecidableTuringLanguage L) :
    UndecidableTuringLanguage K :=
  Computability.undecidable_of_decidableReduction hred hL

theorem decidable_reduction_complement
    {L : Language alpha} {K : Language beta}
    (h : TuringDecidableReduction L K) :
    TuringDecidableReduction (Language.Compl L) (Language.Compl K) :=
  Computability.decidableReduction_complement h

theorem not_acceptable_of_contradiction {L : Language alpha}
    (h : TuringAcceptable L -> False) : NonTuringAcceptableLanguage L :=
  Computability.not_acceptable_of_diagonal_contradiction h

theorem non_acceptable_language_of_equal {L K : Language alpha}
    (h : NonTuringAcceptableLanguage L) (hEq : Language.Equal L K) :
    NonTuringAcceptableLanguage K :=
  Computability.not_acceptable_of_equal h hEq

theorem acceptable_reduction_refl (L : Language alpha) :
    TuringAcceptableReduction L L :=
  Computability.acceptableReduction_refl L

theorem acceptable_reduction_trans
    {L : Language alpha} {K : Language beta} {H : Language gamma}
    (hLK : TuringAcceptableReduction L K)
    (hKH : TuringAcceptableReduction K H) :
    TuringAcceptableReduction L H :=
  Computability.acceptableReduction_trans hLK hKH

theorem non_acceptable_of_acceptable_reduction
    {L : Language alpha} {K : Language beta}
    (hred : TuringAcceptableReduction L K)
    (hL : NonTuringAcceptableLanguage L) :
    NonTuringAcceptableLanguage K :=
  Computability.not_acceptable_of_acceptableReduction hred hL

theorem non_computable_function_of_pointwise_equal
    {f g : Word input -> Word output}
    (h : NonComputableStringFunction f) (hfg : forall w, f w = g w) :
    NonComputableStringFunction g :=
  Computability.nonComputableFunction_of_pointwise_equal h hfg

theorem decoder_recognizes_of_equal
    {decodeAccepts : Word code -> Word code -> Prop}
    {machine : Word code} {L K : Language code}
    (h : TuringDecoderRecognizes decodeAccepts machine L)
    (hEq : Language.Equal L K) :
    TuringDecoderRecognizes decodeAccepts machine K :=
  Computability.decoderRecognizes_of_equal h hEq

/-!
**Diagonalization.**

The diagonal language differs from every listed row. If a decoder were
universal for all languages, the self-diagonal language would be one of its
rows, contradicting the diagonal theorem.

The construction flips the answer on the diagonal: at code {lit}`w`, it disagrees
with what the {lit}`w`-th decoded machine says about {lit}`w`. No row can therefore be
the diagonal language.

This block is intentionally abstract. It does not depend on a particular
machine encoding, so it cleanly separates the mathematical contradiction from
the engineering task of implementing a universal decoder.
-/

theorem diagonal_language_not_self_recognized (acceptsSelf : Word code -> Prop) :
    ¬ forall w : Word code,
      acceptsSelf w <-> w ∈ TuringDiagonalLanguage acceptsSelf :=
  Computability.diagonal_not_self_recognized acceptsSelf

theorem decoder_cannot_recognize_self_diagonal
    (decodeAccepts : Word code -> Word code -> Prop) :
    ¬ exists machine : Word code,
      TuringDecoderRecognizes decodeAccepts machine
        (TuringSelfDiagonalLanguage decodeAccepts) :=
  Computability.decoder_cannot_recognize_self_diagonal decodeAccepts

theorem decoder_row_not_self_diagonal
    (decodeAccepts : Word code -> Word code -> Prop)
    (machine : Word code) :
    ¬ TuringDecoderRecognizes decodeAccepts machine
      (TuringSelfDiagonalLanguage decodeAccepts) :=
  Computability.decoder_row_not_self_diagonal decodeAccepts machine

theorem self_diagonal_missing_from_decoder_rows
    (decodeAccepts : Word code -> Word code -> Prop) :
    exists L : Language code,
      ¬ exists machine : Word code,
        TuringDecoderRecognizes decodeAccepts machine L :=
  Computability.self_diagonal_missing_from_decoder_rows decodeAccepts

theorem decoder_not_universal_for_all_languages
    (decodeAccepts : Word code -> Word code -> Prop) :
    ¬ TuringDecoderUniversalForAllLanguages decodeAccepts :=
  Computability.decoder_not_universal_for_all_languages decodeAccepts

theorem self_diagonal_not_acceptable_if_decoder_universal
    {decodeAccepts : Word code -> Word code -> Prop}
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts) :
    NonTuringAcceptableLanguage
      (TuringSelfDiagonalLanguage decodeAccepts) :=
  Computability.self_diagonal_not_acceptable_if_decoder_universal huniv

theorem exists_nonacceptable_language_if_decoder_universal
    {decodeAccepts : Word code -> Word code -> Prop}
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts) :
    exists L : Language code, NonTuringAcceptableLanguage L :=
  Computability.exists_nonacceptable_language_if_decoder_universal huniv

/-!
**Self-Halting and the Halting Problem.**

The self-diagonal language is the complement of self-halting. Under a universal
decoder, this yields the standard undecidability and non-RE complement results,
then relates self-halting to pair-encoded halting problems.

Self-halting asks whether a machine halts on its own code. The ordinary
two-input halting problem is at least as hard because self-halting is the
preimage obtained by feeding the same code into both slots.

The concrete pair-code alphabet makes that preimage statement exact for encoded
machine descriptions. The remaining computability/preimage construction
theorems name the compiler and universal-runner facts required to turn the
abstract reduction into the final concrete halting-problem theorem.
-/

theorem self_diagonal_equal_complement_self_halting
    (haltsOnCodeInput : Word code -> Word code -> Prop) :
    Language.Equal (TuringSelfDiagonalLanguage haltsOnCodeInput)
      (Language.Compl (TuringSelfHaltingLanguage haltsOnCodeInput)) :=
  Computability.selfDiagonal_equal_compl_selfHalting haltsOnCodeInput

theorem complement_self_halting_not_acceptable_if_decoder_universal
    {decodeAccepts : Word code -> Word code -> Prop}
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts) :
    NonTuringAcceptableLanguage
      (Language.Compl (TuringSelfHaltingLanguage decodeAccepts)) :=
  Computability.compl_selfHalting_not_acceptable_if_decoder_universal huniv

theorem complement_self_halting_not_recursively_enumerable_if_decoder_universal
    {decodeAccepts : Word code -> Word code -> Prop}
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts) :
    ¬ RecursivelyEnumerableTuringLanguage
      (Language.Compl (TuringSelfHaltingLanguage decodeAccepts)) :=
  Computability.compl_selfHalting_not_recursivelyEnumerable_if_decoder_universal
    huniv

theorem self_halting_not_recursive_if_decoder_universal
    {decodeAccepts : Word code -> Word code -> Prop}
    (haccept : DecidableToAcceptableConstruction code)
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts) :
    ¬ RecursiveTuringLanguage (TuringSelfHaltingLanguage decodeAccepts) :=
  Computability.selfHalting_not_recursive_if_decoder_universal
    haccept huniv

theorem self_halting_undecidable_if_decoder_universal
    {decodeAccepts : Word code -> Word code -> Prop}
    (haccept : DecidableToAcceptableConstruction code)
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts) :
    UndecidableTuringLanguage (TuringSelfHaltingLanguage decodeAccepts) :=
  Computability.selfHalting_undecidable_if_decoder_universal
    haccept huniv

theorem self_halting_re_not_recursive_and_complement_not_re_if_decoder_universal
    {decodeAccepts : Word code -> Word code -> Prop}
    (haccept : DecidableToAcceptableConstruction code)
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts)
    (hself : RecursivelyEnumerableTuringLanguage
      (TuringSelfHaltingLanguage decodeAccepts)) :
    RecursivelyEnumerableTuringLanguage
        (TuringSelfHaltingLanguage decodeAccepts) ∧
      ¬ RecursiveTuringLanguage (TuringSelfHaltingLanguage decodeAccepts) ∧
        ¬ RecursivelyEnumerableTuringLanguage
          (Language.Compl (TuringSelfHaltingLanguage decodeAccepts)) :=
  Computability.selfHalting_re_not_recursive_and_compl_not_re_if_decoder_universal
    haccept huniv hself

/-!
These membership lemmas unfold the halting-problem encodings. They make the
two-input problem explicit either as concatenation or as a supplied pair encoder,
then identify self-halting as the diagonal preimage of pair halting.
-/

theorem halting_problem_mem
    (haltsOnCodeInput : Word code -> Word code -> Prop)
    (encodedPair : Word code) :
    encodedPair ∈ TuringHaltingProblem haltsOnCodeInput <->
      exists machine input : Word code,
        encodedPair = Languages.Word.Concat machine input ∧
          haltsOnCodeInput machine input :=
  Computability.haltingProblem_mem haltsOnCodeInput encodedPair

theorem pair_halting_problem_mem
    (encodePair : Word code -> Word code -> Word pairSymbol)
    (haltsOnCodeInput : Word code -> Word code -> Prop)
    (encodedPair : Word pairSymbol) :
    encodedPair ∈
        TuringPairHaltingProblem encodePair haltsOnCodeInput <->
      exists machine input : Word code,
        encodedPair = encodePair machine input ∧
          haltsOnCodeInput machine input :=
  Computability.pairHaltingProblem_mem
    encodePair haltsOnCodeInput encodedPair

theorem halting_problem_equal_concat_pair_halting_problem
    (haltsOnCodeInput : Word code -> Word code -> Prop) :
    Language.Equal (TuringHaltingProblem haltsOnCodeInput)
      (TuringPairHaltingProblem
        (fun machine input : Word code => Languages.Word.Concat machine input)
        haltsOnCodeInput) :=
  Computability.haltingProblem_equal_pairHaltingProblem_concat
    haltsOnCodeInput

theorem halting_problem_contains_encoded_halting_pair
    (haltsOnCodeInput : Word code -> Word code -> Prop)
    {machine input : Word code}
    (hhalts : haltsOnCodeInput machine input) :
    Languages.Word.Concat machine input ∈
      TuringHaltingProblem haltsOnCodeInput :=
  Computability.haltingProblem_contains_encoded_halting_pair
    haltsOnCodeInput hhalts

theorem pair_halting_problem_contains_encoded_halting_pair
    (encodePair : Word code -> Word code -> Word pairSymbol)
    (haltsOnCodeInput : Word code -> Word code -> Prop)
    {machine input : Word code}
    (hhalts : haltsOnCodeInput machine input) :
    encodePair machine input ∈
      TuringPairHaltingProblem encodePair haltsOnCodeInput :=
  Computability.pairHaltingProblem_contains_encoded_halting_pair
    encodePair haltsOnCodeInput hhalts

theorem halting_problem_pair_elim
    {haltsOnCodeInput : Word code -> Word code -> Prop}
    {encodedPair : Word code}
    (h : encodedPair ∈ TuringHaltingProblem haltsOnCodeInput) :
    exists machine input : Word code,
      encodedPair = Languages.Word.Concat machine input ∧
        haltsOnCodeInput machine input :=
  Computability.haltingProblem_pair_elim h

theorem pair_halting_problem_pair_elim
    {encodePair : Word code -> Word code -> Word pairSymbol}
    {haltsOnCodeInput : Word code -> Word code -> Prop}
    {encodedPair : Word pairSymbol}
    (h : encodedPair ∈
      TuringPairHaltingProblem encodePair haltsOnCodeInput) :
    exists machine input : Word code,
      encodedPair = encodePair machine input ∧
        haltsOnCodeInput machine input :=
  Computability.pairHaltingProblem_pair_elim h

theorem self_halting_pair_language_mem
    (encodePair : Word code -> Word code -> Word pairSymbol)
    (haltsOnCodeInput : Word code -> Word code -> Prop)
    (encodedPair : Word pairSymbol) :
    encodedPair ∈
        TuringSelfHaltingPairLanguage encodePair haltsOnCodeInput <->
      exists machine : Word code,
        encodedPair = encodePair machine machine ∧
          haltsOnCodeInput machine machine :=
  Computability.selfHaltingPairLanguage_mem
    encodePair haltsOnCodeInput encodedPair

theorem self_halting_pair_language_subset_pair_halting_problem
    (encodePair : Word code -> Word code -> Word pairSymbol)
    (haltsOnCodeInput : Word code -> Word code -> Prop) :
    Language.Subset
      (TuringSelfHaltingPairLanguage encodePair haltsOnCodeInput)
      (TuringPairHaltingProblem encodePair haltsOnCodeInput) :=
  Computability.selfHaltingPairLanguage_subset_pairHaltingProblem
    encodePair haltsOnCodeInput

theorem word_preimage_language_mem
    (map : Word input -> Word output)
    (L : Language output)
    (w : Word input) :
    w ∈ TuringWordPreimageLanguage map L <-> map w ∈ L :=
  Computability.wordPreimageLanguage_mem map L w

theorem diagonal_pair_preimage_pair_halting_equal_self_halting
    {encodePair : Word code -> Word code -> Word pairSymbol}
    {haltsOnCodeInput : Word code -> Word code -> Prop}
    (hinj : TuringPairEncodingInjective encodePair) :
    Language.Equal
      (TuringWordPreimageLanguage
        (TuringDiagonalPairMap encodePair)
        (TuringPairHaltingProblem encodePair haltsOnCodeInput))
      (TuringSelfHaltingLanguage haltsOnCodeInput) :=
  Computability.diagonalPairMap_preimage_pairHalting_equal_selfHalting
    (encodePair := encodePair)
    (haltsOnCodeInput := haltsOnCodeInput)
    hinj

/-!
The next facts specialize the abstract decoder story to concrete machine
descriptions. Encoding then decoding a description is exact, and a universal
machine specification is phrased as an iff between universal-machine halting and
the description-level acceptance relation.
-/

theorem concrete_machine_decode_encode
    (D : ConcreteMachineDescription) :
    ConcreteMachineDecode (ConcreteMachineEncode D) = some D :=
  MachineDescription.decodeDescription_encodeDescription D

theorem concrete_machine_decode_prefix_encode_append
    (D : ConcreteMachineDescription)
    (input : Word ConcreteMachineCodeSymbol) :
    ConcreteMachineDecodePrefix
      (Languages.Word.Concat (ConcreteMachineEncode D) input) =
        some (D, input) :=
  MachineDescription.decodeDescriptionPrefix_encodeDescription_append D input

theorem concrete_machine_decode_prefix_eq_some_encode_append
    {encoded : Word ConcreteMachineCodeSymbol}
    {D : ConcreteMachineDescription}
    {input : Word ConcreteMachineCodeSymbol}
    (h : ConcreteMachineDecodePrefix encoded = some (D, input)) :
    encoded = Languages.Word.Concat (ConcreteMachineEncode D) input := by
  simpa [ConcreteMachineDecodePrefix, ConcreteMachineEncode,
    Languages.Word.Concat]
    using
      MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescription_append
        h

theorem concrete_machine_code_accepts_encode_description_iff
    (D : ConcreteMachineDescription)
    (input : Word ConcreteMachineCodeSymbol) :
    ConcreteMachineCodeAccepts (ConcreteMachineEncode D) input <->
      ConcreteMachineHaltsOnInput D
        (ConcreteMachineEncodeCodeInput input) :=
  MachineDescription.codeAccepts_encodeDescription_iff D input

theorem concrete_machine_code_prefix_accepts_encode_description_iff
    (D : ConcreteMachineDescription)
    (input : Word ConcreteMachineCodeSymbol) :
    ConcreteMachineCodePrefixAccepts
      (Languages.Word.Concat (ConcreteMachineEncode D) input) <->
        ConcreteMachineHaltsOnInput D
          (ConcreteMachineEncodeCodeInput input) :=
  MachineDescription.codePrefixAccepts_encodeDescription_append_iff D input

theorem concrete_machine_encoded_description_accepts
    {D : ConcreteMachineDescription}
    {input : Word ConcreteMachineCodeSymbol}
    (h : ConcreteMachineHaltsOnInput D
      (ConcreteMachineEncodeCodeInput input)) :
    ConcreteMachineCodeAccepts (ConcreteMachineEncode D) input :=
  (concrete_machine_code_accepts_encode_description_iff D input).mpr h

theorem concrete_machine_encoded_description_accepts_elim
    {D : ConcreteMachineDescription}
    {input : Word ConcreteMachineCodeSymbol}
    (h : ConcreteMachineCodeAccepts (ConcreteMachineEncode D) input) :
    ConcreteMachineHaltsOnInput D
      (ConcreteMachineEncodeCodeInput input) :=
  (concrete_machine_code_accepts_encode_description_iff D input).mp h

theorem concrete_machine_encoded_description_recognizes_input_language
    (D : ConcreteMachineDescription) :
    TuringDecoderRecognizes ConcreteMachineCodeAccepts
      (ConcreteMachineEncode D)
      (ConcreteMachineEncodedInputLanguage D) := by
  intro input
  exact concrete_machine_code_accepts_encode_description_iff D input

theorem concrete_encoded_input_description_compiler_of_program_compiler
    (hcompile : ConcreteEncodedInputProgramAcceptorCompilationConstruction) :
    ConcreteEncodedInputDescriptionCompilerConstruction :=
  Computability.encodedInputDescriptionCompilerPrinciple_of_programCompiler
    hcompile

theorem concrete_encoded_input_description_compiler_decoder_universal
    (hcompile : ConcreteEncodedInputDescriptionCompilerConstruction) :
    ConcreteMachineDecoderUniversalForAcceptableLanguages := by
  intro L hL
  cases hcompile L hL with
  | intro D hD =>
      exists ConcreteMachineEncode D
      intro input
      exact Iff.trans
        (concrete_machine_encoded_description_recognizes_input_language
          D input)
        (hD.right input)

theorem concrete_machine_compiled_transition_of_lookup
    {D : ConcreteMachineDescription}
    {source : Nat} {read : Option Bool}
    {t : ConcreteMachineTransition}
    (hsource : source < D.stateCount + 1)
    (hlookup : D.lookupTransition source read = some t) :
    (ConcreteMachineToTuringMachine D).transition
      (D.stateOfNat source) read =
        some (t.write, t.move, D.stateOfNat t.target) :=
  MachineDescription.toTuringMachine_transition_of_lookup
    hsource hlookup

theorem concrete_machine_turing_step_of_interpreter_step
    {D : ConcreteMachineDescription}
    {c d : ConcreteMachineConfiguration}
    (hsource : c.state < D.stateCount + 1)
    (hstep : ConcreteMachineStep D c = some d) :
    TuringMachine.Step (ConcreteMachineToTuringMachine D)
      (D.toTMConfig c) (D.toTMConfig d) :=
  MachineDescription.toTuringMachine_step_of_stepConfig
    hsource hstep

/-!
Concrete pair codes discharge the injectivity part of diagonal preimages. The
remaining preimage principles say when a decider for pair halting would induce a
decider for self-halting by composing with the diagonal map.
-/

def concrete_pair_code_symbol_finite
    (h : Foundation.FiniteType code) :
    Foundation.FiniteType (ConcretePairCodeSymbol code) :=
  PairCodeSymbol.finite h

theorem concrete_pair_encoding_injective :
    TuringPairEncodingInjective
      (ConcretePairEncoding :
        Word code -> Word code -> Word (ConcretePairCodeSymbol code)) :=
  PairCodeSymbol.encodePair_injective

theorem concrete_diagonal_pair_preimage_pair_halting_equal_self_halting
    {haltsOnCodeInput : Word code -> Word code -> Prop} :
    Language.Equal
      (TuringWordPreimageLanguage
        (ConcreteDiagonalPairMap :
          Word code -> Word (ConcretePairCodeSymbol code))
        (TuringPairHaltingProblem
          (ConcretePairEncoding :
            Word code -> Word code -> Word (ConcretePairCodeSymbol code))
          haltsOnCodeInput))
      (TuringSelfHaltingLanguage haltsOnCodeInput) :=
  PairCodeSymbol.diagonalMap_preimage_pairHalting_equal_selfHalting

theorem concrete_machine_diagonal_pair_preimage_pair_halting_equal_self_halting :
    Language.Equal
      ConcreteMachineDiagonalPairPreimageLanguage
      ConcreteMachineSelfHaltingLanguage :=
  concrete_diagonal_pair_preimage_pair_halting_equal_self_halting
    (haltsOnCodeInput := ConcreteMachineCodeAccepts)

theorem diagonal_pair_map_mem_pair_halting_iff_self_halting
    {encodePair : Word code -> Word code -> Word pairSymbol}
    (hinj : TuringPairEncodingInjective encodePair)
    {haltsOnCodeInput : Word code -> Word code -> Prop}
    (machine : Word code) :
    (TuringDiagonalPairMap encodePair machine) ∈
        TuringPairHaltingProblem encodePair haltsOnCodeInput <->
      machine ∈ TuringSelfHaltingLanguage haltsOnCodeInput := by
  change machine ∈
      TuringWordPreimageLanguage
        (TuringDiagonalPairMap encodePair)
        (TuringPairHaltingProblem encodePair haltsOnCodeInput) <->
    machine ∈ TuringSelfHaltingLanguage haltsOnCodeInput
  exact diagonal_pair_preimage_pair_halting_equal_self_halting
    (encodePair := encodePair)
    (haltsOnCodeInput := haltsOnCodeInput)
    hinj
    machine

theorem concrete_diagonal_pair_map_mem_pair_halting_iff_self_halting
    (machine : Word ConcreteMachineCodeSymbol) :
    (ConcreteDiagonalPairMap machine) ∈ ConcreteMachinePairHaltingProblem <->
      machine ∈ ConcreteMachineSelfHaltingLanguage := by
  change machine ∈ ConcreteMachineDiagonalPairPreimageLanguage <->
    machine ∈ ConcreteMachineSelfHaltingLanguage
  exact
    concrete_machine_diagonal_pair_preimage_pair_halting_equal_self_halting
      machine

theorem diagonal_pair_preimage_recursive_iff_self_halting_recursive
    {encodePair : Word code -> Word code -> Word pairSymbol}
    (hinj : TuringPairEncodingInjective encodePair)
    {haltsOnCodeInput : Word code -> Word code -> Prop} :
    RecursiveTuringLanguage
        (TuringWordPreimageLanguage
          (TuringDiagonalPairMap encodePair)
          (TuringPairHaltingProblem encodePair haltsOnCodeInput)) <->
      RecursiveTuringLanguage
        (TuringSelfHaltingLanguage haltsOnCodeInput) := by
  constructor
  · intro h
    exact Computability.turing_decidable_of_equal h
      (diagonal_pair_preimage_pair_halting_equal_self_halting
        (encodePair := encodePair)
        (haltsOnCodeInput := haltsOnCodeInput)
        hinj)
  · intro h
    exact Computability.turing_decidable_of_equal h
      (Language.equal_symm
        (diagonal_pair_preimage_pair_halting_equal_self_halting
          (encodePair := encodePair)
          (haltsOnCodeInput := haltsOnCodeInput)
          hinj))

theorem concrete_machine_diagonal_pair_preimage_recursive_iff_self_halting_recursive :
    RecursiveTuringLanguage ConcreteMachineDiagonalPairPreimageLanguage <->
      RecursiveTuringLanguage ConcreteMachineSelfHaltingLanguage := by
  constructor
  · intro h
    exact Computability.turing_decidable_of_equal h
      concrete_machine_diagonal_pair_preimage_pair_halting_equal_self_halting
  · intro h
    exact Computability.turing_decidable_of_equal h
      (Language.equal_symm
        concrete_machine_diagonal_pair_preimage_pair_halting_equal_self_halting)

theorem diagonal_pair_decidable_preimage_construction_of_preimage
    {encodePair : Word code -> Word code -> Word pairSymbol}
    (hinj : TuringPairEncodingInjective encodePair)
    (hpreimage :
      TuringDecidablePreimageConstruction (TuringDiagonalPairMap encodePair)) :
    DiagonalPairDecidablePreimageConstruction encodePair :=
  Computability.diagonalPairDecidablePreimagePrinciple_of_preimage
    hinj hpreimage

theorem concrete_diagonal_pair_decidable_preimage_construction_of_preimage
    (hpreimage :
      TuringDecidablePreimageConstruction
        (ConcreteDiagonalPairMap :
          Word code -> Word (ConcretePairCodeSymbol code))) :
    DiagonalPairDecidablePreimageConstruction
      (ConcretePairEncoding :
        Word code -> Word code -> Word (ConcretePairCodeSymbol code)) :=
  PairCodeSymbol.diagonalPairDecidablePreimagePrinciple_of_concrete_preimage
    hpreimage

theorem decidable_preimage_construction_of_computable_map_construction
    (hpreimage : ComputableMapDecidablePreimageConstruction input output)
    {map : Word input -> Word output}
    (hcomputable : TuringComputableWordMap map) :
    TuringDecidablePreimageConstruction map :=
  Computability.decidablePreimagePrinciple_of_computableMapPrinciple
    hpreimage hcomputable

theorem decidable_preimage_construction_of_faithful_computable_map_construction
    (hpreimage :
      FaithfulComputableMapDecidablePreimageConstruction input output)
    {map : Word input -> Word output}
    (hcomputable : FaithfulTuringComputableWordMap map) :
    TuringDecidablePreimageConstruction map :=
  Computability.decidablePreimagePrinciple_of_faithfulComputableMapPrinciple
    hpreimage hcomputable

theorem faithful_computable_map_decidable_preimage_construction_of_computable_map_construction
    (hpreimage : ComputableMapDecidablePreimageConstruction input output) :
    FaithfulComputableMapDecidablePreimageConstruction input output :=
  Computability.faithfulComputableMapDecidablePreimagePrinciple_of_computableMapPrinciple
    hpreimage

theorem diagonal_pair_decidable_preimage_construction_of_computable_map
    {encodePair : Word code -> Word code -> Word pairSymbol}
    (hinj : TuringPairEncodingInjective encodePair)
    (hpreimage : ComputableMapDecidablePreimageConstruction code pairSymbol)
    (hcomputable : TuringComputableWordMap (TuringDiagonalPairMap encodePair)) :
    DiagonalPairDecidablePreimageConstruction encodePair :=
  Computability.diagonalPairDecidablePreimagePrinciple_of_computableMapPrinciple
    hinj hpreimage hcomputable

theorem diagonal_pair_decidable_preimage_construction_of_faithful_computable_map
    {encodePair : Word code -> Word code -> Word pairSymbol}
    (hinj : TuringPairEncodingInjective encodePair)
    (hpreimage :
      FaithfulComputableMapDecidablePreimageConstruction code pairSymbol)
    (hcomputable :
      FaithfulTuringComputableWordMap (TuringDiagonalPairMap encodePair)) :
    DiagonalPairDecidablePreimageConstruction encodePair :=
  Computability.diagonalPairDecidablePreimagePrinciple_of_faithfulComputableMapPrinciple
    hinj hpreimage hcomputable

theorem diagonal_pair_decidable_reduction_self_halting_to_pair_halting
    {encodePair : Word code -> Word code -> Word pairSymbol}
    {haltsOnCodeInput : Word code -> Word code -> Prop}
    (hdiag : DiagonalPairDecidablePreimageConstruction encodePair) :
    TuringDecidableReduction
      (TuringSelfHaltingLanguage haltsOnCodeInput)
      (TuringPairHaltingProblem encodePair haltsOnCodeInput) :=
  hdiag haltsOnCodeInput

theorem diagonal_pair_decidable_reduction_self_halting_to_pair_halting_of_preimage
    {encodePair : Word code -> Word code -> Word pairSymbol}
    (hinj : TuringPairEncodingInjective encodePair)
    (hpreimage :
      TuringDecidablePreimageConstruction (TuringDiagonalPairMap encodePair))
    {haltsOnCodeInput : Word code -> Word code -> Prop} :
    TuringDecidableReduction
      (TuringSelfHaltingLanguage haltsOnCodeInput)
      (TuringPairHaltingProblem encodePair haltsOnCodeInput) :=
  diagonal_pair_decidable_reduction_self_halting_to_pair_halting
    (diagonal_pair_decidable_preimage_construction_of_preimage
      hinj hpreimage)

theorem diagonal_pair_decidable_reduction_self_halting_to_pair_halting_of_computable_map
    {encodePair : Word code -> Word code -> Word pairSymbol}
    (hinj : TuringPairEncodingInjective encodePair)
    (hpreimage : ComputableMapDecidablePreimageConstruction code pairSymbol)
    (hcomputable : TuringComputableWordMap (TuringDiagonalPairMap encodePair))
    {haltsOnCodeInput : Word code -> Word code -> Prop} :
    TuringDecidableReduction
      (TuringSelfHaltingLanguage haltsOnCodeInput)
      (TuringPairHaltingProblem encodePair haltsOnCodeInput) :=
  diagonal_pair_decidable_reduction_self_halting_to_pair_halting
    (diagonal_pair_decidable_preimage_construction_of_computable_map
      hinj hpreimage hcomputable)

theorem diagonal_pair_decidable_reduction_self_halting_to_pair_halting_of_faithful_computable_map
    {encodePair : Word code -> Word code -> Word pairSymbol}
    (hinj : TuringPairEncodingInjective encodePair)
    (hpreimage :
      FaithfulComputableMapDecidablePreimageConstruction code pairSymbol)
    (hcomputable :
      FaithfulTuringComputableWordMap (TuringDiagonalPairMap encodePair))
    {haltsOnCodeInput : Word code -> Word code -> Prop} :
    TuringDecidableReduction
      (TuringSelfHaltingLanguage haltsOnCodeInput)
      (TuringPairHaltingProblem encodePair haltsOnCodeInput) :=
  diagonal_pair_decidable_reduction_self_halting_to_pair_halting
    (diagonal_pair_decidable_preimage_construction_of_faithful_computable_map
      hinj hpreimage hcomputable)

theorem concrete_diagonal_pair_decidable_preimage_construction_of_computable_map
    (hpreimage :
      ComputableMapDecidablePreimageConstruction
        ConcreteMachineCodeSymbol
        (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))
    (hcomputable : ConcreteDiagonalPairMapComputable) :
    DiagonalPairDecidablePreimageConstruction
      (ConcretePairEncoding :
        Word ConcreteMachineCodeSymbol ->
          Word ConcreteMachineCodeSymbol ->
            Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol)) := by
  simpa [DiagonalPairDecidablePreimageConstruction,
    ConcretePairEncoding, ConcretePairCodeSymbol, ConcreteDiagonalPairMap,
    ConcreteDiagonalPairMapComputable,
    ComputableMapDecidablePreimageConstruction, TuringComputableWordMap]
    using
      PairCodeSymbol.diagonalPairDecidablePreimagePrinciple_of_concrete_computable_map
        (code := ConcreteMachineCodeSymbol) hpreimage hcomputable

theorem concrete_diagonal_pair_decidable_preimage_construction_of_faithful_computable_map
    (hpreimage :
      FaithfulComputableMapDecidablePreimageConstruction
        ConcreteMachineCodeSymbol
        (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))
    (hcomputable : FaithfulConcreteDiagonalPairMapComputable) :
    DiagonalPairDecidablePreimageConstruction
      (ConcretePairEncoding :
        Word ConcreteMachineCodeSymbol ->
          Word ConcreteMachineCodeSymbol ->
            Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol)) := by
  simpa [DiagonalPairDecidablePreimageConstruction,
    ConcretePairEncoding, ConcretePairCodeSymbol, ConcreteDiagonalPairMap,
    FaithfulConcreteDiagonalPairMapComputable,
    FaithfulComputableMapDecidablePreimageConstruction,
    FaithfulTuringComputableWordMap]
    using
      PairCodeSymbol.diagonalPairDecidablePreimagePrinciple_of_concrete_faithful_computable_map
        (code := ConcreteMachineCodeSymbol) hpreimage hcomputable

theorem concrete_diagonal_pair_decidable_preimage_construction_of_faithful_preimage
    (hpreimage :
      FaithfulComputableMapDecidablePreimageConstruction
        ConcreteMachineCodeSymbol
        (ConcretePairCodeSymbol ConcreteMachineCodeSymbol)) :
    DiagonalPairDecidablePreimageConstruction
      (ConcretePairEncoding :
        Word ConcreteMachineCodeSymbol ->
          Word ConcreteMachineCodeSymbol ->
            Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol)) :=
  concrete_diagonal_pair_decidable_preimage_construction_of_faithful_computable_map
    hpreimage faithful_concrete_diagonal_pair_map_computable

theorem concrete_machine_self_halting_reduces_to_pair_halting_of_preimage
    (hpreimage :
      TuringDecidablePreimageConstruction
        (ConcreteDiagonalPairMap :
          Word ConcreteMachineCodeSymbol ->
            Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))) :
    TuringDecidableReduction
      ConcreteMachineSelfHaltingLanguage
      ConcreteMachinePairHaltingProblem := by
  simpa [ConcreteMachineSelfHaltingLanguage, ConcreteMachinePairHaltingProblem]
    using
      diagonal_pair_decidable_reduction_self_halting_to_pair_halting
        (encodePair :=
          (ConcretePairEncoding :
            Word ConcreteMachineCodeSymbol ->
              Word ConcreteMachineCodeSymbol ->
                Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol)))
        (haltsOnCodeInput := ConcreteMachineCodeAccepts)
        (concrete_diagonal_pair_decidable_preimage_construction_of_preimage
          (code := ConcreteMachineCodeSymbol) hpreimage)

theorem concrete_machine_self_halting_reduces_to_pair_halting_of_computable_map
    (hpreimage :
      ComputableMapDecidablePreimageConstruction
        ConcreteMachineCodeSymbol
        (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))
    (hcomputable : ConcreteDiagonalPairMapComputable) :
    TuringDecidableReduction
      ConcreteMachineSelfHaltingLanguage
      ConcreteMachinePairHaltingProblem := by
  simpa [ConcreteMachineSelfHaltingLanguage, ConcreteMachinePairHaltingProblem]
    using
      diagonal_pair_decidable_reduction_self_halting_to_pair_halting
        (encodePair :=
          (ConcretePairEncoding :
            Word ConcreteMachineCodeSymbol ->
              Word ConcreteMachineCodeSymbol ->
                Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol)))
        (haltsOnCodeInput := ConcreteMachineCodeAccepts)
        (concrete_diagonal_pair_decidable_preimage_construction_of_computable_map
          hpreimage hcomputable)

theorem concrete_machine_self_halting_reduces_to_pair_halting_of_faithful_computable_map
    (hpreimage :
      FaithfulComputableMapDecidablePreimageConstruction
        ConcreteMachineCodeSymbol
        (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))
    (hcomputable : FaithfulConcreteDiagonalPairMapComputable) :
    TuringDecidableReduction
      ConcreteMachineSelfHaltingLanguage
      ConcreteMachinePairHaltingProblem := by
  simpa [ConcreteMachineSelfHaltingLanguage, ConcreteMachinePairHaltingProblem]
    using
      diagonal_pair_decidable_reduction_self_halting_to_pair_halting
        (encodePair :=
          (ConcretePairEncoding :
            Word ConcreteMachineCodeSymbol ->
              Word ConcreteMachineCodeSymbol ->
                Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol)))
        (haltsOnCodeInput := ConcreteMachineCodeAccepts)
        (concrete_diagonal_pair_decidable_preimage_construction_of_faithful_computable_map
          hpreimage hcomputable)

theorem concrete_machine_self_halting_reduces_to_pair_halting_of_faithful_preimage
    (hpreimage :
      FaithfulComputableMapDecidablePreimageConstruction
        ConcreteMachineCodeSymbol
        (ConcretePairCodeSymbol ConcreteMachineCodeSymbol)) :
    TuringDecidableReduction
      ConcreteMachineSelfHaltingLanguage
      ConcreteMachinePairHaltingProblem :=
  concrete_machine_self_halting_reduces_to_pair_halting_of_faithful_computable_map
    hpreimage faithful_concrete_diagonal_pair_map_computable

theorem halting_problem_of_pointwise_iff
    {halts1 halts2 : Word code -> Word code -> Prop}
    (hiff : forall machine input : Word code,
      halts1 machine input <-> halts2 machine input) :
    Language.Equal (TuringHaltingProblem halts1)
      (TuringHaltingProblem halts2) :=
  Computability.haltingProblem_of_pointwise_iff hiff

theorem pair_halting_problem_of_pointwise_iff
    (encodePair : Word code -> Word code -> Word pairSymbol)
    {halts1 halts2 : Word code -> Word code -> Prop}
    (hiff : forall machine input : Word code,
      halts1 machine input <-> halts2 machine input) :
    Language.Equal (TuringPairHaltingProblem encodePair halts1)
      (TuringPairHaltingProblem encodePair halts2) :=
  Computability.pairHaltingProblem_of_pointwise_iff encodePair hiff

/-!
The pair-halting transfer theorems now apply the diagonal preimage argument.
An undecidable self-halting language forces the corresponding pair-halting
language to be undecidable; universal decoders supply the self-halting
undecidability needed for the standard theorem.
-/

theorem pair_halting_undecidable_if_self_halting_undecidable
    {encodePair : Word code -> Word code -> Word pairSymbol}
    {haltsOnCodeInput : Word code -> Word code -> Prop}
    (hdiag :
      DiagonalPairDecidablePreimageConstruction encodePair)
    (hself :
      UndecidableTuringLanguage
        (TuringSelfHaltingLanguage haltsOnCodeInput)) :
    UndecidableTuringLanguage
      (TuringPairHaltingProblem encodePair haltsOnCodeInput) :=
  Computability.pairHalting_undecidable_if_selfHalting_undecidable
    hdiag hself

theorem pair_halting_undecidable_if_self_halting_undecidable_of_preimage
    {encodePair : Word code -> Word code -> Word pairSymbol}
    {haltsOnCodeInput : Word code -> Word code -> Prop}
    (hinj : TuringPairEncodingInjective encodePair)
    (hpreimage :
      TuringDecidablePreimageConstruction (TuringDiagonalPairMap encodePair))
    (hself :
      UndecidableTuringLanguage
        (TuringSelfHaltingLanguage haltsOnCodeInput)) :
    UndecidableTuringLanguage
      (TuringPairHaltingProblem encodePair haltsOnCodeInput) :=
  Computability.pairHalting_undecidable_if_selfHalting_undecidable_of_preimage
    hinj hpreimage hself

theorem pair_halting_undecidable_if_decoder_universal
    {encodePair : Word code -> Word code -> Word pairSymbol}
    {decodeAccepts : Word code -> Word code -> Prop}
    (haccept : DecidableToAcceptableConstruction code)
    (hdiag :
      DiagonalPairDecidablePreimageConstruction encodePair)
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts) :
    UndecidableTuringLanguage
      (TuringPairHaltingProblem encodePair decodeAccepts) :=
  Computability.pairHalting_undecidable_if_decoder_universal
    haccept hdiag huniv

theorem pair_halting_undecidable_if_decoder_universal_of_preimage
    {encodePair : Word code -> Word code -> Word pairSymbol}
    {decodeAccepts : Word code -> Word code -> Prop}
    (haccept : DecidableToAcceptableConstruction code)
    (hinj : TuringPairEncodingInjective encodePair)
    (hpreimage :
      TuringDecidablePreimageConstruction (TuringDiagonalPairMap encodePair))
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts) :
    UndecidableTuringLanguage
      (TuringPairHaltingProblem encodePair decodeAccepts) :=
  Computability.pairHalting_undecidable_if_decoder_universal_of_preimage
    haccept hinj hpreimage huniv

theorem pair_halting_undecidable_if_decoder_universal_of_computable_map
    {encodePair : Word code -> Word code -> Word pairSymbol}
    {decodeAccepts : Word code -> Word code -> Prop}
    (haccept : DecidableToAcceptableConstruction code)
    (hinj : TuringPairEncodingInjective encodePair)
    (hpreimage : ComputableMapDecidablePreimageConstruction code pairSymbol)
    (hcomputable : TuringComputableWordMap (TuringDiagonalPairMap encodePair))
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts) :
    UndecidableTuringLanguage
      (TuringPairHaltingProblem encodePair decodeAccepts) :=
  Computability.pairHalting_undecidable_if_decoder_universal
    haccept
    (diagonal_pair_decidable_preimage_construction_of_computable_map
      hinj hpreimage hcomputable)
    huniv

theorem pair_halting_undecidable_if_decoder_universal_of_faithful_computable_map
    {encodePair : Word code -> Word code -> Word pairSymbol}
    {decodeAccepts : Word code -> Word code -> Prop}
    (haccept : DecidableToAcceptableConstruction code)
    (hinj : TuringPairEncodingInjective encodePair)
    (hpreimage :
      FaithfulComputableMapDecidablePreimageConstruction code pairSymbol)
    (hcomputable :
      FaithfulTuringComputableWordMap (TuringDiagonalPairMap encodePair))
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts) :
    UndecidableTuringLanguage
      (TuringPairHaltingProblem encodePair decodeAccepts) :=
  Computability.pairHalting_undecidable_if_decoder_universal
    haccept
    (diagonal_pair_decidable_preimage_construction_of_faithful_computable_map
      hinj hpreimage hcomputable)
    huniv

theorem concrete_pair_halting_undecidable_if_decoder_universal_of_preimage
    {decodeAccepts : Word code -> Word code -> Prop}
    (haccept : DecidableToAcceptableConstruction code)
    (hpreimage :
      TuringDecidablePreimageConstruction
        (ConcreteDiagonalPairMap :
          Word code -> Word (ConcretePairCodeSymbol code)))
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts) :
    UndecidableTuringLanguage
      (TuringPairHaltingProblem
        (ConcretePairEncoding :
          Word code -> Word code -> Word (ConcretePairCodeSymbol code))
        decodeAccepts) :=
  PairCodeSymbol.concretePairHalting_undecidable_if_decoder_universal_of_preimage
    haccept hpreimage huniv

theorem concrete_pair_halting_undecidable_if_decoder_universal_of_computable_map
    {decodeAccepts : Word code -> Word code -> Prop}
    (haccept : DecidableToAcceptableConstruction code)
    (hpreimage :
      ComputableMapDecidablePreimageConstruction code (ConcretePairCodeSymbol code))
    (hcomputable :
      TuringComputableWordMap
        (ConcreteDiagonalPairMap :
          Word code -> Word (ConcretePairCodeSymbol code)))
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts) :
    UndecidableTuringLanguage
      (TuringPairHaltingProblem
        (ConcretePairEncoding :
          Word code -> Word code -> Word (ConcretePairCodeSymbol code))
        decodeAccepts) :=
  PairCodeSymbol.concretePairHalting_undecidable_if_decoder_universal_of_computable_map
    haccept hpreimage hcomputable huniv

theorem concrete_pair_halting_undecidable_if_decoder_universal_of_faithful_computable_map
    {decodeAccepts : Word code -> Word code -> Prop}
    (haccept : DecidableToAcceptableConstruction code)
    (hpreimage :
      FaithfulComputableMapDecidablePreimageConstruction code
        (ConcretePairCodeSymbol code))
    (hcomputable :
      FaithfulTuringComputableWordMap
        (ConcreteDiagonalPairMap :
          Word code -> Word (ConcretePairCodeSymbol code)))
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts) :
    UndecidableTuringLanguage
      (TuringPairHaltingProblem
        (ConcretePairEncoding :
          Word code -> Word code -> Word (ConcretePairCodeSymbol code))
        decodeAccepts) :=
  PairCodeSymbol.concretePairHalting_undecidable_if_decoder_universal_of_faithful_computable_map
    haccept hpreimage hcomputable huniv

/-!
The concrete machine statements instantiate the abstract results with the
machine-code alphabet and description decoder. They remain conditional on the
acceptability principle, universal decoder, and diagonal-map preimage or
computability hypotheses named in their signatures.
-/

theorem concrete_machine_self_halting_undecidable_if_decoder_universal
    (haccept :
      DecidableToAcceptableConstruction ConcreteMachineCodeSymbol)
    (huniv : ConcreteMachineDecoderUniversalForAcceptableLanguages) :
    UndecidableTuringLanguage ConcreteMachineSelfHaltingLanguage :=
  self_halting_undecidable_if_decoder_universal
    haccept huniv

theorem concrete_machine_complement_self_halting_not_recursively_enumerable_if_decoder_universal
    (huniv : ConcreteMachineDecoderUniversalForAcceptableLanguages) :
    ¬ RecursivelyEnumerableTuringLanguage
      (Language.Compl ConcreteMachineSelfHaltingLanguage) :=
  complement_self_halting_not_recursively_enumerable_if_decoder_universal
    huniv

theorem concrete_machine_pair_halting_undecidable_if_self_halting_undecidable_of_preimage
    (hpreimage :
      TuringDecidablePreimageConstruction
        (ConcreteDiagonalPairMap :
          Word ConcreteMachineCodeSymbol ->
            Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol)))
    (hself :
      UndecidableTuringLanguage ConcreteMachineSelfHaltingLanguage) :
    UndecidableTuringLanguage ConcreteMachinePairHaltingProblem := by
  simpa [ConcreteMachinePairHaltingProblem]
    using
      pair_halting_undecidable_if_self_halting_undecidable_of_preimage
        (encodePair :=
          (ConcretePairEncoding :
            Word ConcreteMachineCodeSymbol ->
              Word ConcreteMachineCodeSymbol ->
                Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol)))
        (haltsOnCodeInput := ConcreteMachineCodeAccepts)
        concrete_pair_encoding_injective
        hpreimage
        hself

theorem concrete_machine_pair_halting_undecidable_if_self_halting_undecidable_of_computable_map
    (hpreimage :
      ComputableMapDecidablePreimageConstruction
        ConcreteMachineCodeSymbol
        (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))
    (hcomputable : ConcreteDiagonalPairMapComputable)
    (hself :
      UndecidableTuringLanguage ConcreteMachineSelfHaltingLanguage) :
    UndecidableTuringLanguage ConcreteMachinePairHaltingProblem :=
  undecidable_of_decidable_reduction
    (concrete_machine_self_halting_reduces_to_pair_halting_of_computable_map
      hpreimage hcomputable)
    hself

theorem concrete_machine_pair_halting_undecidable_if_self_halting_undecidable_of_faithful_computable_map
    (hpreimage :
      FaithfulComputableMapDecidablePreimageConstruction
        ConcreteMachineCodeSymbol
        (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))
    (hcomputable : FaithfulConcreteDiagonalPairMapComputable)
    (hself :
      UndecidableTuringLanguage ConcreteMachineSelfHaltingLanguage) :
    UndecidableTuringLanguage ConcreteMachinePairHaltingProblem :=
  undecidable_of_decidable_reduction
    (concrete_machine_self_halting_reduces_to_pair_halting_of_faithful_computable_map
      hpreimage hcomputable)
    hself

theorem concrete_machine_pair_halting_undecidable_if_self_halting_undecidable_of_faithful_preimage
    (hpreimage :
      FaithfulComputableMapDecidablePreimageConstruction
        ConcreteMachineCodeSymbol
        (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))
    (hself :
      UndecidableTuringLanguage ConcreteMachineSelfHaltingLanguage) :
    UndecidableTuringLanguage ConcreteMachinePairHaltingProblem :=
  concrete_machine_pair_halting_undecidable_if_self_halting_undecidable_of_faithful_computable_map
    hpreimage faithful_concrete_diagonal_pair_map_computable hself

theorem concrete_machine_pair_halting_undecidable_if_decoder_universal_of_preimage
    (haccept :
      DecidableToAcceptableConstruction ConcreteMachineCodeSymbol)
    (hpreimage :
      TuringDecidablePreimageConstruction
        (ConcreteDiagonalPairMap :
          Word ConcreteMachineCodeSymbol ->
            Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol)))
    (huniv : ConcreteMachineDecoderUniversalForAcceptableLanguages) :
    UndecidableTuringLanguage ConcreteMachinePairHaltingProblem := by
  simpa [ConcreteMachinePairHaltingProblem]
    using
      concrete_pair_halting_undecidable_if_decoder_universal_of_preimage
        (code := ConcreteMachineCodeSymbol)
        (decodeAccepts := ConcreteMachineCodeAccepts)
        haccept hpreimage huniv

theorem concrete_machine_pair_halting_undecidable_if_decoder_universal_of_computable_map
    (haccept :
      DecidableToAcceptableConstruction ConcreteMachineCodeSymbol)
    (hpreimage :
      ComputableMapDecidablePreimageConstruction
        ConcreteMachineCodeSymbol
        (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))
    (hcomputable : ConcreteDiagonalPairMapComputable)
    (huniv : ConcreteMachineDecoderUniversalForAcceptableLanguages) :
    UndecidableTuringLanguage ConcreteMachinePairHaltingProblem := by
  simpa [ConcreteMachinePairHaltingProblem]
    using
      concrete_pair_halting_undecidable_if_decoder_universal_of_computable_map
        (code := ConcreteMachineCodeSymbol)
        (decodeAccepts := ConcreteMachineCodeAccepts)
        haccept hpreimage hcomputable huniv

theorem concrete_machine_pair_halting_undecidable_if_decoder_universal_of_faithful_computable_map
    (haccept :
      DecidableToAcceptableConstruction ConcreteMachineCodeSymbol)
    (hpreimage :
      FaithfulComputableMapDecidablePreimageConstruction
        ConcreteMachineCodeSymbol
        (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))
    (hcomputable : FaithfulConcreteDiagonalPairMapComputable)
    (huniv : ConcreteMachineDecoderUniversalForAcceptableLanguages) :
    UndecidableTuringLanguage ConcreteMachinePairHaltingProblem := by
  simpa [ConcreteMachinePairHaltingProblem]
    using
      concrete_pair_halting_undecidable_if_decoder_universal_of_faithful_computable_map
        (code := ConcreteMachineCodeSymbol)
        (decodeAccepts := ConcreteMachineCodeAccepts)
        haccept hpreimage hcomputable huniv

theorem concrete_machine_pair_halting_undecidable_if_decoder_universal_of_faithful_preimage
    (haccept :
      DecidableToAcceptableConstruction ConcreteMachineCodeSymbol)
    (hpreimage :
      FaithfulComputableMapDecidablePreimageConstruction
        ConcreteMachineCodeSymbol
        (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))
    (huniv : ConcreteMachineDecoderUniversalForAcceptableLanguages) :
    UndecidableTuringLanguage ConcreteMachinePairHaltingProblem :=
  concrete_machine_pair_halting_undecidable_if_decoder_universal_of_faithful_computable_map
    haccept hpreimage faithful_concrete_diagonal_pair_map_computable huniv

theorem concrete_machine_pair_halting_undecidable_if_encoded_input_compiler_of_faithful_preimage
    (haccept :
      DecidableToAcceptableConstruction ConcreteMachineCodeSymbol)
    (hpreimage :
      FaithfulComputableMapDecidablePreimageConstruction
        ConcreteMachineCodeSymbol
        (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))
    (hcompile : ConcreteEncodedInputDescriptionCompilerConstruction) :
    UndecidableTuringLanguage ConcreteMachinePairHaltingProblem :=
  concrete_machine_pair_halting_undecidable_if_decoder_universal_of_faithful_preimage
    haccept hpreimage
    (concrete_encoded_input_description_compiler_decoder_universal hcompile)

/-!
The abstract row-coverage lemmas below are parameterized by an arbitrary
decoder relation.  The concrete construction that follows instantiates the
universal-machine target with the prefix specification, where the runner
decodes one self-delimiting machine description from the front of the tape and
uses the remaining symbols as the simulated input.
-/

theorem universal_machine_spec_pair_halts
    {universal : TuringMachine symbol state}
    {decodeAccepts : Word symbol -> Word symbol -> Prop}
    (hspec : UniversalTuringMachineSpec universal decodeAccepts)
    {machine input : Word symbol}
    (hdecode : decodeAccepts machine input) :
    TuringMachine.HaltsOnInput universal
      (Languages.Word.Concat machine input) :=
  Computability.universalMachineSpec_pair_halts hspec hdecode

theorem universal_machine_spec_pair_decode
    {universal : TuringMachine symbol state}
    {decodeAccepts : Word symbol -> Word symbol -> Prop}
    (hspec : UniversalTuringMachineSpec universal decodeAccepts)
    {machine input : Word symbol}
    (hhalts : TuringMachine.HaltsOnInput universal
      (Languages.Word.Concat machine input)) :
    decodeAccepts machine input :=
  Computability.universalMachineSpec_pair_decode hspec hhalts

theorem universal_machine_spec_decoder_recognizes_row_language
    {universal : TuringMachine symbol state}
    {decodeAccepts : Word symbol -> Word symbol -> Prop}
    (hspec : UniversalTuringMachineSpec universal decodeAccepts)
    (machine : Word symbol) :
    TuringDecoderRecognizes decodeAccepts machine
      (UniversalMachineRowLanguage universal machine) := by
  intro input
  exact (hspec machine input).symm

theorem universal_machine_rows_cover_of_decoder_universal
    {universal : TuringMachine symbol state}
    {decodeAccepts : Word symbol -> Word symbol -> Prop}
    (hspec : UniversalTuringMachineSpec universal decodeAccepts)
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts) :
    UniversalMachineRowsCoverAcceptableLanguages universal := by
  intro L hL
  cases huniv L hL with
  | intro machine hmachine =>
      exists machine
      intro input
      exact Iff.trans (hspec machine input) (hmachine input)

theorem decoder_universal_of_universal_machine_rows_cover
    {universal : TuringMachine symbol state}
    {decodeAccepts : Word symbol -> Word symbol -> Prop}
    (hspec : UniversalTuringMachineSpec universal decodeAccepts)
    (hrows : UniversalMachineRowsCoverAcceptableLanguages universal) :
    TuringDecoderUniversalForAcceptableLanguages decodeAccepts := by
  intro L hL
  cases hrows L hL with
  | intro machine hmachine =>
      exists machine
      intro input
      exact Iff.trans (hspec machine input).symm (hmachine input)

theorem universal_machine_rows_cover_iff_decoder_universal
    {universal : TuringMachine symbol state}
    {decodeAccepts : Word symbol -> Word symbol -> Prop}
    (hspec : UniversalTuringMachineSpec universal decodeAccepts) :
    UniversalMachineRowsCoverAcceptableLanguages universal <->
      TuringDecoderUniversalForAcceptableLanguages decodeAccepts := by
  constructor
  · exact decoder_universal_of_universal_machine_rows_cover hspec
  · exact universal_machine_rows_cover_of_decoder_universal hspec

theorem concrete_universal_prefix_machine_halts_on_encoded_description_iff
    {universal : TuringMachine ConcreteMachineCodeSymbol state}
    (hspec : ConcreteUniversalPrefixMachineSpec universal)
    (D : ConcreteMachineDescription)
    (input : Word ConcreteMachineCodeSymbol) :
    TuringMachine.HaltsOnInput universal
      (Languages.Word.Concat (ConcreteMachineEncode D) input) <->
        ConcreteMachineHaltsOnInput D
          (ConcreteMachineEncodeCodeInput input) :=
  Computability.codeUniversalPrefixMachine_halts_on_encoded_description_iff
    hspec D input

theorem concrete_universal_prefix_machine_row_language_equal_encoded_input_language
    {universal : TuringMachine ConcreteMachineCodeSymbol state}
    (hspec : ConcreteUniversalPrefixMachineSpec universal)
    (D : ConcreteMachineDescription) :
    Language.Equal
      (UniversalMachineRowLanguage universal (ConcreteMachineEncode D))
      (ConcreteMachineEncodedInputLanguage D) :=
  Computability.codeUniversalPrefixMachine_rowLanguage_equal_encodedInputLanguage
    hspec D

theorem concrete_universal_prefix_machine_rows_cover_of_encoded_input_description_compiler
    {universal : TuringMachine ConcreteMachineCodeSymbol state}
    (hspec : ConcreteUniversalPrefixMachineSpec universal)
    (hcompile : ConcreteEncodedInputDescriptionCompilerConstruction) :
    ConcreteUniversalPrefixMachineRowsCoverAcceptableLanguages universal :=
  Computability.codeUniversalPrefixRowsCoverAcceptableLanguages_of_encodedInputDescriptionCompiler
    hspec hcompile

theorem exists_concrete_universal_prefix_machine_rows_cover_of_constructions
    (hcompile : ConcreteEncodedInputDescriptionCompilerConstruction)
    (hrunner : ConcreteUniversalPrefixRunnerConstruction) :
    exists state : Type,
      exists universal : TuringMachine ConcreteMachineCodeSymbol state,
        ConcreteUniversalPrefixMachineSpec universal ∧
          ConcreteUniversalPrefixMachineRowsCoverAcceptableLanguages universal :=
  Computability.codeUniversalPrefixRowsCoverConstruction_of_constructions
    hcompile hrunner

theorem exists_concrete_universal_prefix_machine_rows_cover_of_section53_closeout
    (hclose : ConcreteSection53UniversalPrefixCloseout) :
    exists state : Type,
      exists universal : TuringMachine ConcreteMachineCodeSymbol state,
        ConcreteUniversalPrefixMachineSpec universal ∧
          ConcreteUniversalPrefixMachineRowsCoverAcceptableLanguages universal :=
  Computability.codeUniversalPrefixRowsCoverConstruction_of_section53Closeout
    hclose

theorem exists_concrete_universal_prefix_machine_rows_cover_of_finite_source_closeout
    (hclose : ConcreteSection53UniversalPrefixFiniteSourceCloseout) :
    exists state : Type,
      exists universal : TuringMachine ConcreteMachineCodeSymbol state,
        ConcreteUniversalPrefixMachineSpec universal ∧
          ConcreteUniversalPrefixMachineRowsCoverAcceptableLanguages universal :=
  Computability.codeUniversalPrefixRowsCoverConstruction_of_finiteSourceCloseout
    hclose

/-!
**Section 5.3 scaffold.**  The universal-machine target is the prefix runner
route.  These wrappers expose the reusable finite-source runner scaffold at the
book-facing layer.  Row coverage remains available through the closeout theorem
above when an explicit encoded-input description compiler is supplied.
-/

theorem concrete_code_prefix_recognizer_machine_scaffold :
    ConcreteCodePrefixRecognizerMachineConstruction :=
  Computability.codePrefixRecognizerMachineConstruction_scaffold

def concrete_section53_universal_prefix_runner_finite_source_closeout_scaffold :
    ConcreteSection53UniversalPrefixRunnerFiniteSourceCloseout :=
  Computability.codeUniversalPrefixRunnerFiniteSourceCloseout_scaffold

theorem concrete_universal_prefix_runner_scaffold :
    ConcreteUniversalPrefixRunnerConstruction :=
  Computability.codeUniversalPrefixRunnerConstruction_scaffold

theorem exists_concrete_universal_prefix_machine_scaffold :
    exists state : Type,
      exists universal : TuringMachine ConcreteMachineCodeSymbol state,
        ConcreteUniversalPrefixMachineSpec universal :=
  concrete_universal_prefix_runner_scaffold

theorem exists_concrete_universal_prefix_machine_rows_cover_of_boolean_description_compiler
    (hcompiler : ConcreteBooleanDescriptionAcceptorCompilationConstruction)
    (hrunner : ConcreteCodePrefixRecognizerMachineConstruction) :
    exists state : Type,
      exists universal : TuringMachine ConcreteMachineCodeSymbol state,
        ConcreteUniversalPrefixMachineSpec universal ∧
          ConcreteUniversalPrefixMachineRowsCoverAcceptableLanguages universal :=
  exists_concrete_universal_prefix_machine_rows_cover_of_finite_source_closeout
    (concrete_section53_universal_prefix_finite_source_closeout_of_boolean_description_compiler
      hcompiler hrunner)

theorem exists_concrete_universal_prefix_machine_rows_cover_of_program_compiler_and_runner
    (hcompiler : ConcreteEncodedInputProgramAcceptorCompilationConstruction)
    (hrunner : ConcreteUniversalPrefixRunnerConstruction) :
    exists state : Type,
      exists universal : TuringMachine ConcreteMachineCodeSymbol state,
        ConcreteUniversalPrefixMachineSpec universal ∧
          ConcreteUniversalPrefixMachineRowsCoverAcceptableLanguages universal :=
  exists_concrete_universal_prefix_machine_rows_cover_of_section53_closeout
    (concrete_section53_universal_prefix_closeout_of_constructions
      hcompiler hrunner)

/-!
The section's universal-machine and diagonalization theorems require a concrete
encoding of machines as strings.  This module records the formal statement
vocabulary without adding an unproved universal-machine assumption.

Once a concrete universal machine and encoding are supplied, these statements
can be instantiated to recover the usual textbook halting-problem theorems.

This is the current status boundary for Section 5.3. The encoding, interpreter,
compiled-machine simulation, decoder-row wrappers, and pair-code reductions are
formalized. Machine output is now read through normalized tape contents, so
singleton outputs from empty input and Boolean deciders are no longer blocked by
finite tape-window artifacts. The concrete diagonal pair map now has a faithful
finite-machine witness, and the concrete theorem wrappers reuse that witness
without asking callers to pass it again.

The viable universal-machine target is the prefix version. The semantic staged
recognizer {name}`ConcreteCodePrefixRecognizerProgram` accepts exactly
{name}`ConcreteMachineCodePrefixAcceptedLanguage`. The encoded-input compiler
handoff now factors through
{name}`ConcreteBooleanDescriptionAcceptorCompilationConstruction`: Boolean
inputs are decoded by {name}`MachineDescription.decodeCodeWordAsInput`, and
canonical inputs produced by {name}`MachineDescription.encodeCodeWordAsInput`
recover the original code-symbol recognizer. Thus row-coverage closeouts can
reuse an explicit Boolean description compiler instead of carrying a separate
encoded-input program compiler. The remaining fixed-alphabet runner work is
now isolated as
{name}`ConcreteCodePrefixRecognizerMachineConstruction`; this target is
equivalent to {name}`ConcreteUniversalPrefixRunnerConstruction`, because the
prefix recognizer's language is exactly the decoder relation needed by the
universal machine. The prefix parser layer is now formalized as
{name}`ConcreteCodePrefixParserCodeConstruction`: a normalizing code primitive
succeeds exactly on one-description prefixes, and a total branch primitive
emits the success or failure code used by the later recognizer controller. The
no-argument scaffold supplies only this runner target. For row coverage, the
explicit
{name}`ConcreteSection53UniversalPrefixFiniteSourceCloseout` pairs that runner
target with an encoded-input description compiler and routes directly to
{name}`exists_concrete_universal_prefix_machine_rows_cover_of_finite_source_closeout`.
This is the same finite-source layer used by Section 5.2: canonical
{name}`MachineCodeSymbol` parsers, normalized-output emitters,
subroutine-ready sequencing, and cell or parse branch controllers. Together
with the explicit compiler assumption, the closeout fields imply row coverage
by the finite-source closeout theorem, while the older program-compiler route
remains as a compatibility wrapper.
-/

end Section03
end Chapter05
end Book
end FoC
