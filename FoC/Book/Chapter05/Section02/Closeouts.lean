import FoC.Book.Chapter05.Section02.ConstructionStatus
import FoC.Book.Chapter05.Section02.Dovetailing
import FoC.Book.Chapter05.Section02.Grammars
import FoC.Book.Chapter05.Section02.Ranges
import FoC.Book.Chapter05.Section02.Vocabulary
import FoC.Computability.Transform

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter05
namespace Section02

/-!
# Section 5.2: Closeout Theorems
-/

open Languages
open Computability
open Grammars

universe u v

/-!
## Grammar-Pair Characterizations

The last equivalence is stated in terms of a grammar for the language and a
grammar for its complement. Once grammar generation and recursive enumerability
are known equivalent, this is exactly the RE/co-RE characterization of recursive
languages.
-/

private theorem recursive_language_iff_generated_pair
    (generated : Language terminal -> Prop)
    {L : Language terminal}
    (hre : TuringDecidableIffReCoRePrinciple terminal)
    (hgrammarL : generated L <-> TuringAcceptable L)
    (hgrammarCompl :
      generated (Language.Compl L) <->
        TuringAcceptable (Language.Compl L)) :
    TuringDecidable L <->
      generated L ∧ generated (Language.Compl L) := by
  constructor
  · intro hrecursive
    have hrecore := (hre L).mp hrecursive
    constructor
    · exact hgrammarL.mpr hrecore.left
    · exact hgrammarCompl.mpr hrecore.right
  · intro hgrammar
    apply (hre L).mpr
    constructor
    · exact hgrammarL.mp hgrammar.left
    · exact hgrammarCompl.mp hgrammar.right

theorem recursive_language_iff_general_grammar_pair
    {L : Language terminal}
    (hre : TuringDecidableIffReCoRePrinciple terminal)
    (hgrammarL : Computability.GeneralGrammarAcceptabilityEquivalence L)
    (hgrammarCompl :
      Computability.GeneralGrammarAcceptabilityEquivalence
        (Language.Compl L)) :
    TuringDecidable L <-> GeneralGrammarPairGenerated L := by
  change TuringDecidable L <->
    GeneralGrammar.Generated L ∧
      GeneralGrammar.Generated (Language.Compl L)
  exact recursive_language_iff_generated_pair
    GeneralGrammar.Generated hre hgrammarL hgrammarCompl

theorem recursive_language_iff_general_grammar_pair_of_constructions
    (haccept : DecidableToAcceptablePrinciple terminal)
    (hdovetail : ReCoReToDecidablePrinciple terminal)
    (hgrammar : forall K : Language terminal,
      Computability.GeneralGrammarAcceptabilityEquivalence K)
    (L : Language terminal) :
    TuringDecidable L <-> GeneralGrammarPairGenerated L :=
  recursive_language_iff_general_grammar_pair
    (recursive_iff_re_co_re_construction_of_principles haccept hdovetail)
    (hgrammar L)
    (hgrammar (Language.Compl L))

theorem recursive_language_iff_general_grammar_pair_of_grammar_constructions
    (haccept : DecidableToAcceptablePrinciple terminal)
    (hdovetail : ReCoReToDecidablePrinciple terminal)
    (hto : GeneralGrammarToRecursivelyEnumerablePrinciple terminal)
    (hfrom : RecursivelyEnumerableToGeneralGrammarPrinciple terminal)
    (L : Language terminal) :
    TuringDecidable L <-> GeneralGrammarPairGenerated L :=
  recursive_language_iff_general_grammar_pair_of_constructions
    haccept hdovetail
    (general_grammar_re_equivalence_construction_of_constructions
      hto hfrom)
    L

theorem recursive_language_iff_general_grammar_pair_of_staged_program_compiler
    (haccept : DecidableToAcceptablePrinciple terminal)
    (hdovetail : ReCoReToDecidablePrinciple terminal)
    (hcompile : ProgramAcceptorCompilationPrinciple terminal)
    (L : Language terminal) :
    TuringDecidable L <-> GeneralGrammarPairGenerated L :=
  recursive_language_iff_general_grammar_pair_of_grammar_constructions
    haccept hdovetail
    (general_grammar_to_recursively_enumerable_construction_of_staged_program_compiler
      hcompile)
    recursively_enumerable_to_general_grammar_construction_semantic L

theorem boolean_recursive_language_iff_general_grammar_pair_of_concrete_grammar_compiler
    (haccept : DecidableToAcceptablePrinciple Bool)
    (hdovetail : ReCoReToDecidablePrinciple Bool)
    (hcompile : Computability.SemanticBooleanGeneralGrammarRecognizerCompilerAssumption)
    (L : Language Bool) :
    TuringDecidable L <-> GeneralGrammarPairGenerated L :=
  recursive_language_iff_general_grammar_pair_of_grammar_constructions
    haccept hdovetail
    (boolean_general_grammar_to_recursively_enumerable_construction_of_concrete_grammar_compiler
      hcompile)
    recursively_enumerable_to_general_grammar_construction_semantic L

theorem recursive_language_iff_finite_general_grammar_pair
    {L : Language terminal}
    (hre : TuringDecidableIffReCoRePrinciple terminal)
    (hgrammarL :
      FiniteGeneralGrammarGenerated L <-> TuringAcceptable L)
    (hgrammarCompl :
      FiniteGeneralGrammarGenerated (Language.Compl L) <->
        TuringAcceptable (Language.Compl L)) :
    TuringDecidable L <-> FiniteGeneralGrammarPairGenerated L := by
  change TuringDecidable L <->
    FiniteGeneralGrammarGenerated L ∧
      FiniteGeneralGrammarGenerated (Language.Compl L)
  exact recursive_language_iff_generated_pair
    FiniteGeneralGrammarGenerated hre hgrammarL hgrammarCompl

theorem recursive_language_iff_finite_general_grammar_pair_of_constructions
    (haccept : DecidableToAcceptablePrinciple terminal)
    (hdovetail : ReCoReToDecidablePrinciple terminal)
    (hgrammar : forall K : Language terminal,
      FiniteGeneralGrammarGenerated K <-> TuringAcceptable K)
    (L : Language terminal) :
    TuringDecidable L <-> FiniteGeneralGrammarPairGenerated L :=
  recursive_language_iff_finite_general_grammar_pair
    (recursive_iff_re_co_re_construction_of_principles haccept hdovetail)
    (hgrammar L)
    (hgrammar (Language.Compl L))

theorem recursive_language_iff_finite_general_grammar_pair_of_grammar_constructions
    (haccept : DecidableToAcceptablePrinciple terminal)
    (hdovetail : ReCoReToDecidablePrinciple terminal)
    (hto : FiniteGeneralGrammarToRecursivelyEnumerableConstruction terminal)
    (hfrom :
      RecursivelyEnumerableToFinitePresentationGeneralGrammarPrinciple
        terminal)
    (L : Language terminal) :
    TuringDecidable L <-> FiniteGeneralGrammarPairGenerated L :=
  recursive_language_iff_finite_general_grammar_pair_of_constructions
    haccept hdovetail
    (finite_general_grammar_re_equivalence_construction_of_constructions
      hto hfrom)
    L

/-!
## Consequences of Section Closeouts

The semantic closeout fields instantiate the dovetailing, range, and grammar
principles used by the chapter-level equivalence theorems.
-/

theorem dovetailing_decidable_construction_of_section52_closeout
    (hclose : BooleanSection52CompilerCloseout) :
    ReCoReToDecidablePrinciple Bool :=
  dovetailing_decidable_construction_of_concrete_dovetail_description_compiler
    hclose.dovetailDescription

theorem bounded_trace_search_construction_of_section52_closeout
    (hclose : BooleanSection52CompilerCloseout) :
    Computability.BoundedTraceSearchConstruction :=
  hclose.boundedTraceSearch

theorem recursive_language_iff_re_and_co_re_of_section52_closeout
    (hclose : BooleanSection52CompilerCloseout)
    (L : Language Bool) :
    TuringDecidable L <-> RecursivelyEnumerableWithComplement L :=
  recursive_language_iff_re_and_co_re_of_constructions
    hclose.decidableToAcceptable
    (dovetailing_decidable_construction_of_section52_closeout hclose)
    L

theorem recursive_language_iff_re_and_co_re_of_semantic_surface
    (h : SemanticLanguagePrincipleSurface terminal)
    (L : Language terminal) :
    TuringDecidable L <-> RecursivelyEnumerableWithComplement L :=
  recursive_language_iff_re_and_co_re_of_constructions
    h.decidableToAcceptable h.dovetailingDecidable L

theorem partially_listable_language_iff_concrete_compiled_partial_unary_range_of_section52_closeout
    (hclose : BooleanSection52CompilerCloseout)
    (L : Language Bool) :
    PartiallyListable L <-> CompiledPartialUnaryRange L :=
  partially_listable_language_iff_concrete_compiled_partial_unary_range_of_concrete_compiler
    hclose.partialUnaryRangeDescription L

theorem partially_listable_language_iff_concrete_compiled_partial_unary_program_range_of_section52_closeout
    (hclose : BooleanSection52CompilerCloseout)
    (L : Language Bool) :
    PartiallyListable L <->
      CompiledPartialUnaryFunctionProgramRange L :=
  partially_listable_language_iff_concrete_compiled_partial_unary_program_range_of_concrete_compiler
    hclose.partialUnaryRangeDescription L

theorem boolean_general_grammar_to_recursively_enumerable_construction_of_section52_closeout
    (hclose : BooleanSection52CompilerCloseout) :
    GeneralGrammarToRecursivelyEnumerablePrinciple Bool :=
  boolean_general_grammar_to_recursively_enumerable_construction_of_concrete_grammar_compiler
    hclose.grammarRecognizerDescription

theorem boolean_general_grammar_re_equivalence_construction_of_section52_closeout
    (hclose : BooleanSection52CompilerCloseout) :
    GeneralGrammarREEquivalencePrinciple Bool :=
  general_grammar_re_equivalence_construction_of_to_construction
    (boolean_general_grammar_to_recursively_enumerable_construction_of_section52_closeout
      hclose)

theorem finite_general_grammar_to_recursively_enumerable_construction_of_section52_closeout
    (hclose : BooleanSection52CompilerCloseout) :
    FiniteGeneralGrammarToRecursivelyEnumerableConstruction Bool :=
  boolean_finite_general_grammar_to_recursively_enumerable_construction_of_concrete_grammar_compiler
    hclose.grammarRecognizerDescription

theorem boolean_recursive_language_iff_general_grammar_pair_of_section52_closeout
    (hclose : BooleanSection52CompilerCloseout)
    (L : Language Bool) :
    TuringDecidable L <-> GeneralGrammarPairGenerated L :=
  recursive_language_iff_general_grammar_pair_of_grammar_constructions
    hclose.decidableToAcceptable
    (dovetailing_decidable_construction_of_section52_closeout hclose)
    (boolean_general_grammar_to_recursively_enumerable_construction_of_section52_closeout
      hclose)
    recursively_enumerable_to_general_grammar_construction_semantic
    L

/-!
## Finite-Data Grammar Consequences

Finite-presentation compiler fields and description-backed recognizers supply
the effective grammar direction without widening the closeout assumptions.
-/

theorem finite_general_grammar_to_recursively_enumerable_construction_of_finite_section52_closeout
    (hclose : BooleanFiniteGrammarSection52Closeout) :
    FiniteGeneralGrammarToRecursivelyEnumerableConstruction Bool :=
  BooleanFiniteGeneralGrammar.to_re_construction_of_concreteFiniteGrammarCompiler
    (concrete_finite_grammar_recognizer_compiler_of_finite_presentation_compiler
      hclose.finiteGrammarRecognizerDescription)

theorem program_acceptable_by_description_to_finite_general_grammar_construction_of_finite_data_closeout
    (hclose : BooleanFiniteDataSection52CompilerCloseout) :
    ProgramAcceptableByDescriptionToFiniteGeneralGrammarConstruction :=
  Computability.booleanFiniteDataSection52CompilerCloseout_programAcceptableByDescriptionToFiniteGrammar
    hclose

theorem program_acceptable_by_description_to_finite_general_grammar_presentation_construction_of_finite_data_closeout
    (hclose : BooleanFiniteDataSection52CompilerCloseout) :
    ProgramAcceptableByDescriptionToFiniteGeneralGrammarPresentationConstruction :=
  Computability.booleanFiniteDataSection52CompilerCloseout_programAcceptableByDescriptionToFinitePresentationGrammar
    hclose

theorem program_acceptable_by_description_finite_general_grammar_of_finite_data_closeout
    (hclose : BooleanFiniteDataSection52CompilerCloseout)
    {L : Language Bool}
    (hL : ProgramAcceptableByDescription L) :
    FiniteGeneralGrammarGenerated L :=
  (program_acceptable_by_description_to_finite_general_grammar_presentation_construction_of_finite_data_closeout
    hclose) L hL

theorem concrete_finite_complementary_recognizers_of_finite_general_grammar_pair
    (hfinite :
      FiniteBoolGeneralGrammarPresentation.CompilerConstruction)
    {L : Language Bool}
    (hpair : FiniteGeneralGrammarPairGenerated L) :
    ConcreteFiniteComplementaryRecognizers L := by
  rcases hpair.left with ⟨acceptNonterminal, acceptG,
    acceptFinite, acceptEq⟩
  rcases hpair.right with ⟨rejectNonterminal, rejectG,
    rejectFinite, rejectEq⟩
  let hgrammar : FiniteBooleanGeneralGrammarRecognizerCompilerPrinciple :=
    concrete_finite_grammar_recognizer_compiler_of_finite_presentation_compiler
      hfinite
  rcases hgrammar
      (nonterminal := acceptNonterminal) acceptG
        (GeneralGrammar.hasFiniteProductions_of_hasFinitePresentation
          acceptFinite) with
    ⟨acceptD, acceptCompiled⟩
  rcases hgrammar
      (nonterminal := rejectNonterminal) rejectG
        (GeneralGrammar.hasFiniteProductions_of_hasFinitePresentation
          rejectFinite) with
    ⟨rejectD, rejectCompiled⟩
  let acceptProgram : FiniteAcceptorProgram :=
    { description := acceptD }
  let rejectProgram : FiniteAcceptorProgram :=
    { description := rejectD }
  have acceptGenerated :
      MachineDescriptionAcceptsLanguage acceptD
        (GeneralGrammar.GeneratedLanguage acceptG) :=
    Computability.programCompiledByDescription_acceptsLanguage
      (Computability.generalGrammarRecognizerProgram_acceptsLanguage acceptG)
      acceptCompiled
  have rejectGenerated :
      MachineDescriptionAcceptsLanguage rejectD
        (GeneralGrammar.GeneratedLanguage rejectG) :=
    Computability.programCompiledByDescription_acceptsLanguage
      (Computability.generalGrammarRecognizerProgram_acceptsLanguage rejectG)
      rejectCompiled
  have acceptLanguage :
      MachineDescriptionAcceptsLanguage acceptD L := by
    constructor
    · exact acceptGenerated.left
    · intro w
      exact Iff.trans (acceptGenerated.right w) (acceptEq w)
  have rejectLanguage :
      MachineDescriptionAcceptsLanguage rejectD (Language.Compl L) := by
    constructor
    · exact rejectGenerated.left
    · intro w
      exact Iff.trans (rejectGenerated.right w) (rejectEq w)
  have htraces :
      ComplementaryAcceptanceTraces
        (FiniteAcceptorProgram.trace acceptProgram)
        (FiniteAcceptorProgram.trace rejectProgram) L := by
    constructor
    · simpa [acceptProgram, FiniteAcceptorProgram.trace,
        Computability.FiniteAcceptorProgram.trace] using!
        concrete_machine_description_acceptance_trace acceptLanguage
    · simpa [rejectProgram, FiniteAcceptorProgram.trace,
        Computability.FiniteAcceptorProgram.trace] using!
        concrete_machine_description_acceptance_trace rejectLanguage
  exact ⟨acceptProgram, rejectProgram, acceptLanguage.left,
    rejectLanguage.left, htraces⟩

/-- A finite stopped decider unconditionally yields finite-presentation
grammars for its accepted and rejected languages. -/
theorem concrete_finite_decidable_language_has_finite_general_grammar_pair
    {L : Language Bool}
    (h : ConcreteFiniteDecidableLanguage L) :
    FiniteGeneralGrammarPairGenerated L := by
  rcases concrete_finite_decidable_has_complementary_recognizers h with
    ⟨accept, reject, haccept, hreject, htraces⟩
  constructor
  · apply
      (finite_bool_grammar_generated_iff_finite_general_grammar_generated L).mp
    exact concrete_finite_recognizable_language_finite_bool_grammar_generated
      ⟨accept, haccept, htraces.left⟩
  · apply
      (finite_bool_grammar_generated_iff_finite_general_grammar_generated
        (Language.Compl L)).mp
    exact concrete_finite_recognizable_language_finite_bool_grammar_generated
      ⟨reject, hreject, htraces.right⟩

/-- Finite-presentation grammar pairs yield finite stopped deciders once the
two honest finite compiler interfaces are supplied. -/
theorem concrete_finite_general_grammar_pair_is_decidable_of_constructions
    (hdovetail :
      StoppedPairedRecognizerDovetailDescriptionCompilerPrinciple)
    (hgrammar :
      FiniteBoolGeneralGrammarPresentation.CompilerConstruction)
    {L : Language Bool}
    (hpair : FiniteGeneralGrammarPairGenerated L) :
    ConcreteFiniteDecidableLanguage L :=
  concrete_finite_complementary_recognizers_decidable_of_stopped_compiler
    hdovetail
    (concrete_finite_complementary_recognizers_of_finite_general_grammar_pair
      hgrammar hpair)

/-- The effective finite-machine form of the finite grammar-pair
characterization. The forward direction is unconditional; the reverse
direction states exactly the two compiler constructions still required. -/
theorem concrete_finite_decidable_iff_finite_general_grammar_pair_of_constructions
    (hdovetail :
      StoppedPairedRecognizerDovetailDescriptionCompilerPrinciple)
    (hgrammar :
      FiniteBoolGeneralGrammarPresentation.CompilerConstruction)
    (L : Language Bool) :
    ConcreteFiniteDecidableLanguage L <->
      FiniteGeneralGrammarPairGenerated L :=
  ⟨concrete_finite_decidable_language_has_finite_general_grammar_pair,
    concrete_finite_general_grammar_pair_is_decidable_of_constructions
      hdovetail hgrammar⟩

theorem finite_general_grammar_pair_recursive_of_finite_data_constructions
    (hpaired : PairedRecognizerDovetailDescriptionCompilerPrinciple)
    (hfinite :
      FiniteBoolGeneralGrammarPresentation.CompilerConstruction)
    {L : Language Bool}
    (hpair : FiniteGeneralGrammarPairGenerated L) :
    TuringDecidable L := by
  rcases
      concrete_finite_complementary_recognizers_of_finite_general_grammar_pair
        hfinite hpair with
    ⟨accept, reject, _haccept, _hreject, htraces⟩
  exact
    concrete_finite_dovetail_program_turing_decidable_of_paired_recognizer_compiler
      hpaired (accept := accept) (reject := reject) htraces

theorem finite_general_grammar_pair_recursive_of_finite_data_closeout
    (hclose : BooleanFiniteDataSection52CompilerCloseout)
    {L : Language Bool}
    (hpair : FiniteGeneralGrammarPairGenerated L) :
    TuringDecidable L :=
  finite_general_grammar_pair_recursive_of_finite_data_constructions
    hclose.pairedDovetailDescription
    hclose.finiteGrammarRecognizerDescription
    hpair

/-!
## Finite-Data Composition

These theorems make the finite-data dependency graph explicit. Closeout records
carry the semantic acceptor bridge needed by recursive-language theorems, while
the finite consequences consume the paired-dovetail and grammar-presentation
interfaces directly. The stopped-decider conversion is stated separately, and
the checked-certificate grammar compiler serves as an adapter to the
first-order presentation compiler.
-/

theorem stopped_decidable_to_acceptable_construction_bool :
  forall L : Language Bool,
      StoppedTuringDecidable L -> TuringAcceptable L := by
  intro _L h
  exact TuringMachine.stoppedTuringDecidable_to_turingAcceptable h

theorem program_acceptable_by_description_to_finite_general_grammar :
    ProgramAcceptableByDescriptionToFiniteGeneralGrammarConstruction :=
  Computability.programAcceptableByDescriptionToFiniteGeneralGrammarConstruction_of_descriptionRecognizer
    (Computability.machineDescriptionAcceptsToFiniteGeneralGrammarConstruction_of_machineConstruction
      Computability.machineDescriptionToFiniteGeneralGrammarConstruction)

theorem program_acceptable_by_description_to_finite_general_grammar_presentation :
    ProgramAcceptableByDescriptionToFiniteGeneralGrammarPresentationConstruction :=
  Computability.programAcceptableByDescriptionToFiniteGeneralGrammarPresentationConstruction_of_descriptionRecognizer
    (Computability.machineDescriptionAcceptsToFiniteGeneralGrammarPresentationConstruction_of_machineConstruction
      Computability.machineDescriptionToFiniteGeneralGrammarPresentationConstruction)

theorem program_acceptable_by_description_finite_general_grammar
    {L : Language Bool}
    (hL : ProgramAcceptableByDescription L) :
    FiniteGeneralGrammarGenerated L :=
  program_acceptable_by_description_to_finite_general_grammar_presentation
    L hL

theorem finite_general_grammar_pair_recursive_of_checked_presentation_compiler
    (hpaired : PairedRecognizerDovetailDescriptionCompilerPrinciple)
    (hcompile :
      FiniteBoolGeneralGrammarPresentation.CheckedIndexedCertificateRecognizerCompilerConstruction)
    {L : Language Bool}
    (hpair : FiniteGeneralGrammarPairGenerated L) :
    TuringDecidable L :=
  finite_general_grammar_pair_recursive_of_finite_data_constructions
    hpaired
    (FiniteBoolGeneralGrammarPresentation.compilerConstruction_of_boundedRecognizerCompiler
      (FiniteBoolGeneralGrammarPresentation.boundedRecognizerCompilerConstruction_of_checkedIndexedCertificateRecognizerCompiler
        hcompile))
    hpair

theorem boolean_finite_general_grammar_re_equivalence_construction_of_finite_section52_closeout
    (hclose : BooleanFiniteGrammarSection52Closeout) :
    FinitePresentationGeneralGrammarREEquivalencePrinciple Bool :=
  finite_general_grammar_re_equivalence_construction_of_constructions
    (finite_general_grammar_to_recursively_enumerable_construction_of_finite_section52_closeout
      hclose)
    hclose.recursivelyEnumerableToFinitePresentationGrammar

theorem boolean_recursive_language_iff_finite_general_grammar_pair_of_finite_section52_closeout
    (hclose : BooleanFiniteGrammarSection52Closeout)
    (L : Language Bool) :
    TuringDecidable L <-> FiniteGeneralGrammarPairGenerated L :=
  recursive_language_iff_finite_general_grammar_pair_of_grammar_constructions
    hclose.decidableToAcceptable
    (dovetailing_decidable_construction_of_concrete_dovetail_description_compiler
      hclose.dovetailDescription)
    (finite_general_grammar_to_recursively_enumerable_construction_of_finite_section52_closeout
      hclose)
    hclose.recursivelyEnumerableToFinitePresentationGrammar
    L

theorem boolean_finite_general_grammar_re_equivalence_construction_of_semantic_section52_closeout
    (hclose : BooleanSection52CompilerCloseout)
    (hpresentation :
      FiniteBoolGeneralGrammarPresentation.CompilerConstruction)
    (hfinite :
      RecursivelyEnumerableToFiniteGeneralGrammarPrinciple Bool) :
    FinitePresentationGeneralGrammarREEquivalencePrinciple Bool :=
  boolean_finite_general_grammar_re_equivalence_construction_of_finite_section52_closeout
    (concrete_finite_section52_closeout_of_semantic_closeout
      hclose hpresentation hfinite)

theorem boolean_recursive_language_iff_finite_general_grammar_pair_of_semantic_section52_closeout
    (hclose : BooleanSection52CompilerCloseout)
    (hpresentation :
      FiniteBoolGeneralGrammarPresentation.CompilerConstruction)
    (hfinite :
      RecursivelyEnumerableToFiniteGeneralGrammarPrinciple Bool)
    (L : Language Bool) :
    TuringDecidable L <-> FiniteGeneralGrammarPairGenerated L :=
  boolean_recursive_language_iff_finite_general_grammar_pair_of_finite_section52_closeout
    (concrete_finite_section52_closeout_of_semantic_closeout
      hclose hpresentation hfinite)
    L

/-!
## Semantic and Finite Grammar Boundaries

The theorem equating general grammars with recursively enumerable languages has
two representation-level forms. For semantic unrestricted grammars, the
reverse direction is proved by {name}`SemanticLanguageGrammar`: arbitrary
production predicates can generate any language with one nonterminal. The
finite-presentation form is factored through
{name}`BooleanFiniteGrammarSection52Closeout`. Under that interface,
{name}`boolean_recursive_language_iff_finite_general_grammar_pair_of_finite_section52_closeout`
proves the finite grammar pair characterization. The narrower
{name}`BooleanFiniteDataSection52CompilerCloseout` records concrete
finite-data ingredients: the paired-recognizer dovetail compiler, the finite
first-order grammar-presentation recognizer compiler, and the description-backed
recognizer-to-finite grammar construction. The ordinary finite-grammar compiler
is a derived bridge: a finite grammar is converted to an explicit
{name}`Fin`-indexed production-list presentation, and the compiled presentation
recognizer is transferred to the abstract recognizer by accepted-language
extensionality. The presentation compiler itself is factored through a bounded
derivation-search recognizer compiler. That bounded recognizer is mirrored
by explicit finite production-list certificate recognizers. The indexed
certificate form names each rewrite rule by a finite index into the production
list, and its recursive checked-data form is proved sound and complete for the
indexed proof certificate. The checked-data trace and bounded search are proved
equivalent to the derivation search. Consequently, the checked
certificate-recognizer interface implies the indexed, bounded, and first-order
presentation compiler interfaces.

The declarations above expose that infrastructure as
{name}`BooleanSection52CompilerCloseout` for the semantic grammar page
and {name}`BooleanFiniteGrammarSection52Closeout` for the finite grammar
page, while {name}`BooleanFiniteDataSection52CompilerCloseout` records
the finite-data route. These closeouts carry
{name}`Computability.BoundedTraceSearchConstruction` as the primary finite-trace handoff. The
semantic closeout uses the semantic reverse grammar construction. The
finite-data closeout uses the paired-recognizer dovetail compiler and the
first-order finite grammar-presentation compiler, together with the
description-backed construction
{name}`DescriptionRecognizerToFiniteGeneralGrammarConstruction`.
The checked-presentation wrapper takes the paired-recognizer dovetail compiler
and checked-certificate presentation compiler explicitly so that its dependency
currency is visible in the theorem type.
-/


end Section02
end Chapter05
end Book
end FoC
