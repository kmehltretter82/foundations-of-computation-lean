import FoC.Book.Chapter05.Section02.Grammars
import FoC.Computability.Transform

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter05
namespace Section02

/-!
# Section 5.2 closeout theorems
-/

open Languages
open Computability
open Grammars

universe u v

/-!
The last equivalence is stated in terms of a grammar for the language and a
grammar for its complement. Once grammar generation and recursive enumerability
are known equivalent, this is exactly the RE/co-RE characterization of recursive
languages.
-/

theorem recursive_language_iff_general_grammar_pair
    {L : Language terminal}
    (hre : RecursiveIffReCoREConstruction terminal)
    (hgrammarL : GeneralGrammarAcceptabilityEquivalence L)
    (hgrammarCompl :
      GeneralGrammarAcceptabilityEquivalence (Language.Compl L)) :
    RecursiveLanguage L <-> GeneralGrammarPairGenerated L := by
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

theorem recursive_language_iff_general_grammar_pair_of_constructions
    (haccept : DecidableToAcceptableConstruction terminal)
    (hdovetail : DovetailingDecidableConstruction terminal)
    (hgrammar : forall K : Language terminal,
      GeneralGrammarAcceptabilityEquivalence K)
    (L : Language terminal) :
    RecursiveLanguage L <-> GeneralGrammarPairGenerated L :=
  recursive_language_iff_general_grammar_pair
    (recursive_iff_re_co_re_construction_of_principles haccept hdovetail)
    (hgrammar L)
    (hgrammar (Language.Compl L))

theorem recursive_language_iff_general_grammar_pair_of_grammar_constructions
    (haccept : DecidableToAcceptableConstruction terminal)
    (hdovetail : DovetailingDecidableConstruction terminal)
    (hto : GeneralGrammarToRecursivelyEnumerableConstruction terminal)
    (hfrom : RecursivelyEnumerableToGeneralGrammarConstruction terminal)
    (L : Language terminal) :
    RecursiveLanguage L <-> GeneralGrammarPairGenerated L :=
  recursive_language_iff_general_grammar_pair_of_constructions
    haccept hdovetail
    (general_grammar_re_equivalence_construction_of_constructions
      hto hfrom)
    L

theorem recursive_language_iff_general_grammar_pair_of_staged_program_compiler
    (haccept : DecidableToAcceptableConstruction terminal)
    (hdovetail : DovetailingDecidableConstruction terminal)
    (hcompile : StagedAcceptorCompilationConstruction terminal)
    (L : Language terminal) :
    RecursiveLanguage L <-> GeneralGrammarPairGenerated L :=
  recursive_language_iff_general_grammar_pair_of_grammar_constructions
    haccept hdovetail
    (general_grammar_to_recursively_enumerable_construction_of_staged_program_compiler
      hcompile)
    recursively_enumerable_to_general_grammar_construction_semantic L

theorem boolean_recursive_language_iff_general_grammar_pair_of_concrete_grammar_compiler
    (haccept : DecidableToAcceptableConstruction Bool)
    (hdovetail : DovetailingDecidableConstruction Bool)
    (hcompile : ConcreteBooleanGeneralGrammarRecognizerCompilerConstruction)
    (L : Language Bool) :
    RecursiveLanguage L <-> GeneralGrammarPairGenerated L :=
  recursive_language_iff_general_grammar_pair_of_grammar_constructions
    haccept hdovetail
    (boolean_general_grammar_to_recursively_enumerable_construction_of_concrete_grammar_compiler
      hcompile)
    recursively_enumerable_to_general_grammar_construction_semantic L

theorem recursive_language_iff_finite_general_grammar_pair
    {L : Language terminal}
    (hre : RecursiveIffReCoREConstruction terminal)
    (hgrammarL :
      FiniteGeneralGrammarGenerated L <-> RecursivelyEnumerableLanguage L)
    (hgrammarCompl :
      FiniteGeneralGrammarGenerated (Language.Compl L) <->
        RecursivelyEnumerableLanguage (Language.Compl L)) :
    RecursiveLanguage L <-> FiniteGeneralGrammarPairGenerated L := by
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

theorem recursive_language_iff_finite_general_grammar_pair_of_constructions
    (haccept : DecidableToAcceptableConstruction terminal)
    (hdovetail : DovetailingDecidableConstruction terminal)
    (hgrammar : forall K : Language terminal,
      FiniteGeneralGrammarGenerated K <-> RecursivelyEnumerableLanguage K)
    (L : Language terminal) :
    RecursiveLanguage L <-> FiniteGeneralGrammarPairGenerated L :=
  recursive_language_iff_finite_general_grammar_pair
    (recursive_iff_re_co_re_construction_of_principles haccept hdovetail)
    (hgrammar L)
    (hgrammar (Language.Compl L))

theorem recursive_language_iff_finite_general_grammar_pair_of_grammar_constructions
    (haccept : DecidableToAcceptableConstruction terminal)
    (hdovetail : DovetailingDecidableConstruction terminal)
    (hto : FiniteGeneralGrammarToRecursivelyEnumerableConstruction terminal)
    (hfrom : RecursivelyEnumerableToFiniteGeneralGrammarConstruction terminal)
    (L : Language terminal) :
    RecursiveLanguage L <-> FiniteGeneralGrammarPairGenerated L :=
  recursive_language_iff_finite_general_grammar_pair_of_constructions
    haccept hdovetail
    (finite_general_grammar_re_equivalence_construction_of_constructions
      hto hfrom)
    L

theorem dovetailing_decidable_construction_of_section52_closeout
    (hclose : ConcreteBooleanSection52CompilerCloseout) :
    DovetailingDecidableConstruction Bool :=
  dovetailing_decidable_construction_of_concrete_dovetail_description_compiler
    hclose.dovetailDescription

theorem bounded_trace_search_construction_of_section52_closeout
    (hclose : ConcreteBooleanSection52CompilerCloseout) :
    BoundedTraceSearchConstruction :=
  hclose.boundedTraceSearch

theorem recursive_language_iff_re_and_co_re_of_section52_closeout
    (hclose : ConcreteBooleanSection52CompilerCloseout)
    (L : Language Bool) :
    RecursiveLanguage L <-> RecursivelyEnumerableLanguageWithComplement L :=
  recursive_language_iff_re_and_co_re_of_constructions
    hclose.decidableToAcceptable
    (dovetailing_decidable_construction_of_section52_closeout hclose)
    L

theorem partially_listable_language_iff_concrete_compiled_partial_unary_range_of_section52_closeout
    (hclose : ConcreteBooleanSection52CompilerCloseout)
    (L : Language Bool) :
    LanguagePartiallyListable L <-> ConcreteCompiledPartialUnaryRange L :=
  partially_listable_language_iff_concrete_compiled_partial_unary_range_of_concrete_compiler
    hclose.partialUnaryRangeDescription L

theorem partially_listable_language_iff_concrete_compiled_partial_unary_program_range_of_section52_closeout
    (hclose : ConcreteBooleanSection52CompilerCloseout)
    (L : Language Bool) :
    LanguagePartiallyListable L <->
      ConcreteCompiledPartialUnaryFunctionProgramRange L :=
  partially_listable_language_iff_concrete_compiled_partial_unary_program_range_of_concrete_compiler
    hclose.partialUnaryRangeDescription L

theorem boolean_general_grammar_to_recursively_enumerable_construction_of_section52_closeout
    (hclose : ConcreteBooleanSection52CompilerCloseout) :
    GeneralGrammarToRecursivelyEnumerableConstruction Bool :=
  boolean_general_grammar_to_recursively_enumerable_construction_of_concrete_grammar_compiler
    hclose.grammarRecognizerDescription

theorem boolean_general_grammar_re_equivalence_construction_of_section52_closeout
    (hclose : ConcreteBooleanSection52CompilerCloseout) :
    GeneralGrammarREEquivalenceConstruction Bool :=
  general_grammar_re_equivalence_construction_of_to_construction
    (boolean_general_grammar_to_recursively_enumerable_construction_of_section52_closeout
      hclose)

theorem finite_general_grammar_to_recursively_enumerable_construction_of_section52_closeout
    (hclose : ConcreteBooleanSection52CompilerCloseout) :
    FiniteGeneralGrammarToRecursivelyEnumerableConstruction Bool :=
  boolean_finite_general_grammar_to_recursively_enumerable_construction_of_concrete_grammar_compiler
    hclose.grammarRecognizerDescription

theorem boolean_recursive_language_iff_general_grammar_pair_of_section52_closeout
    (hclose : ConcreteBooleanSection52CompilerCloseout)
    (L : Language Bool) :
    RecursiveLanguage L <-> GeneralGrammarPairGenerated L :=
  recursive_language_iff_general_grammar_pair_of_grammar_constructions
    hclose.decidableToAcceptable
    (dovetailing_decidable_construction_of_section52_closeout hclose)
    (boolean_general_grammar_to_recursively_enumerable_construction_of_section52_closeout
      hclose)
    recursively_enumerable_to_general_grammar_construction_semantic
    L

theorem finite_general_grammar_to_recursively_enumerable_construction_of_finite_section52_closeout
    (hclose : ConcreteBooleanFiniteGrammarSection52Closeout) :
    FiniteGeneralGrammarToRecursivelyEnumerableConstruction Bool :=
  boolean_finite_general_grammar_to_recursively_enumerable_construction_of_concrete_finite_grammar_compiler
    (concrete_finite_grammar_recognizer_compiler_of_finite_presentation_compiler
      hclose.finiteGrammarRecognizerDescription)

theorem program_acceptable_by_description_to_finite_general_grammar_construction_of_finite_data_closeout
    (hclose : ConcreteBooleanFiniteDataSection52CompilerCloseout) :
    ConcreteProgramAcceptableByDescriptionToFiniteGeneralGrammarConstruction :=
  Computability.booleanFiniteDataSection52CompilerCloseout_programAcceptableByDescriptionToFiniteGrammar
    hclose

theorem program_acceptable_by_description_finite_general_grammar_of_finite_data_closeout
    (hclose : ConcreteBooleanFiniteDataSection52CompilerCloseout)
    {L : Language Bool}
    (hL : ConcreteProgramAcceptableByDescription L) :
    FiniteGeneralGrammarGenerated L :=
  (program_acceptable_by_description_to_finite_general_grammar_construction_of_finite_data_closeout
    hclose) L hL

theorem finite_general_grammar_pair_recursive_of_finite_data_constructions
    (hpaired : ConcretePairedRecognizerDovetailCompilerConstruction)
    (hfinite :
      ConcreteFiniteBoolGeneralGrammarPresentationRecognizerCompilerConstruction)
    {L : Language Bool}
    (hpair : FiniteGeneralGrammarPairGenerated L) :
    RecursiveLanguage L := by
  rcases hpair.left with ⟨acceptNonterminal, acceptG,
    acceptFinite, acceptEq⟩
  rcases hpair.right with ⟨rejectNonterminal, rejectG,
    rejectFinite, rejectEq⟩
  let hlist : ConcreteFiniteProductionListGrammarRecognizerCompilerConstruction :=
    concrete_finite_production_list_grammar_recognizer_compiler_of_finite_presentation_compiler
      hfinite
  let hgrammar : ConcreteFiniteBooleanGeneralGrammarRecognizerCompilerConstruction :=
    concrete_finite_grammar_recognizer_compiler_of_production_list_compiler
      hlist
  rcases hgrammar
      (nonterminal := acceptNonterminal) acceptG acceptFinite with
    ⟨acceptD, acceptCompiled⟩
  rcases hgrammar
      (nonterminal := rejectNonterminal) rejectG rejectFinite with
    ⟨rejectD, rejectCompiled⟩
  let acceptProgram : ConcreteFiniteAcceptorProgram :=
    { description := acceptD }
  let rejectProgram : ConcreteFiniteAcceptorProgram :=
    { description := rejectD }
  have acceptGenerated :
      ConcreteMachineDescriptionAccepts acceptD
        (GeneralGrammarGeneratedLanguage acceptG) :=
    Computability.programCompiledByDescription_acceptsLanguage
      (Computability.generalGrammarRecognizerProgram_acceptsLanguage acceptG)
      acceptCompiled
  have rejectGenerated :
      ConcreteMachineDescriptionAccepts rejectD
        (GeneralGrammarGeneratedLanguage rejectG) :=
    Computability.programCompiledByDescription_acceptsLanguage
      (Computability.generalGrammarRecognizerProgram_acceptsLanguage rejectG)
      rejectCompiled
  have acceptLanguage :
      ConcreteMachineDescriptionAccepts acceptD L := by
    constructor
    · exact acceptGenerated.left
    · intro w
      exact Iff.trans (acceptGenerated.right w) (acceptEq w)
  have rejectLanguage :
      ConcreteMachineDescriptionAccepts rejectD (Language.Compl L) := by
    constructor
    · exact rejectGenerated.left
    · intro w
      exact Iff.trans (rejectGenerated.right w) (rejectEq w)
  have htraces :
      LanguageComplementaryAcceptanceTraces
        (ConcreteFiniteAcceptorTrace acceptProgram)
        (ConcreteFiniteAcceptorTrace rejectProgram) L := by
    constructor
    · simpa [acceptProgram, ConcreteFiniteAcceptorTrace,
        Computability.FiniteAcceptorProgram.trace] using
        concrete_machine_description_acceptance_trace acceptLanguage
    · simpa [rejectProgram, ConcreteFiniteAcceptorTrace,
        Computability.FiniteAcceptorProgram.trace] using
        concrete_machine_description_acceptance_trace rejectLanguage
  exact
    concrete_finite_dovetail_program_turing_decidable_of_paired_recognizer_compiler
      hpaired
      (accept := acceptProgram) (reject := rejectProgram) htraces

theorem finite_general_grammar_pair_recursive_of_finite_data_closeout
    (hclose : ConcreteBooleanFiniteDataSection52CompilerCloseout)
    {L : Language Bool}
    (hpair : FiniteGeneralGrammarPairGenerated L) :
    RecursiveLanguage L :=
  finite_general_grammar_pair_recursive_of_finite_data_constructions
    hclose.pairedDovetailDescription
    hclose.finiteGrammarRecognizerDescription
    hpair

/-!
**Section 5.2 finite-data scaffold.**  This is the explicit dependency graph
for the remaining finite/effective route.  It deliberately does not manufacture
the broad {name}`DecidableToAcceptableConstruction` field of the semantic
closeout.  The safe stopped-decider variant is recorded separately, while the
finite consequences below use only the paired-dovetail and finite
grammar-recognizer scaffolds plus the machine-history construction.
-/

theorem stopped_decidable_to_acceptable_construction_bool :
  forall L : Language Bool,
      StoppedTuringDecidableLanguage L -> RecursivelyEnumerableLanguage L := by
  intro _L h
  exact TuringMachine.stoppedTuringDecidable_to_turingAcceptable h

theorem program_acceptable_by_description_to_finite_general_grammar_scaffold :
    ConcreteProgramAcceptableByDescriptionToFiniteGeneralGrammarConstruction :=
  Computability.programAcceptableByDescriptionToFiniteGeneralGrammarConstruction_of_descriptionRecognizer
    (Computability.machineDescriptionAcceptsToFiniteGeneralGrammarConstruction_of_machineConstruction
      concrete_machine_description_to_finite_general_grammar_construction)

theorem program_acceptable_by_description_finite_general_grammar_scaffold
    {L : Language Bool}
    (hL : ConcreteProgramAcceptableByDescription L) :
    FiniteGeneralGrammarGenerated L :=
  program_acceptable_by_description_to_finite_general_grammar_scaffold L hL

theorem finite_general_grammar_pair_recursive_scaffold
    {L : Language Bool}
    (hpair : FiniteGeneralGrammarPairGenerated L) :
    RecursiveLanguage L :=
  finite_general_grammar_pair_recursive_of_finite_data_constructions
    paired_recognizer_dovetail_compiler_scaffold
    concrete_finite_bool_general_grammar_presentation_compiler_scaffold
    hpair

theorem boolean_finite_general_grammar_re_equivalence_construction_of_finite_section52_closeout
    (hclose : ConcreteBooleanFiniteGrammarSection52Closeout) :
    FiniteGeneralGrammarREEquivalenceConstruction Bool :=
  finite_general_grammar_re_equivalence_construction_of_constructions
    (finite_general_grammar_to_recursively_enumerable_construction_of_finite_section52_closeout
      hclose)
    hclose.recursivelyEnumerableToFiniteGrammar

theorem boolean_recursive_language_iff_finite_general_grammar_pair_of_finite_section52_closeout
    (hclose : ConcreteBooleanFiniteGrammarSection52Closeout)
    (L : Language Bool) :
    RecursiveLanguage L <-> FiniteGeneralGrammarPairGenerated L :=
  recursive_language_iff_finite_general_grammar_pair_of_grammar_constructions
    hclose.decidableToAcceptable
    (dovetailing_decidable_construction_of_concrete_dovetail_description_compiler
      hclose.dovetailDescription)
    (finite_general_grammar_to_recursively_enumerable_construction_of_finite_section52_closeout
      hclose)
    hclose.recursivelyEnumerableToFiniteGrammar
    L

theorem boolean_finite_general_grammar_re_equivalence_construction_of_semantic_section52_closeout
    (hclose : ConcreteBooleanSection52CompilerCloseout)
    (hpresentation :
      ConcreteFiniteBoolGeneralGrammarPresentationRecognizerCompilerConstruction)
    (hfinite :
      RecursivelyEnumerableToFiniteGeneralGrammarConstruction Bool) :
    FiniteGeneralGrammarREEquivalenceConstruction Bool :=
  boolean_finite_general_grammar_re_equivalence_construction_of_finite_section52_closeout
    (concrete_finite_section52_closeout_of_semantic_closeout
      hclose hpresentation hfinite)

theorem boolean_recursive_language_iff_finite_general_grammar_pair_of_semantic_section52_closeout
    (hclose : ConcreteBooleanSection52CompilerCloseout)
    (hpresentation :
      ConcreteFiniteBoolGeneralGrammarPresentationRecognizerCompilerConstruction)
    (hfinite :
      RecursivelyEnumerableToFiniteGeneralGrammarConstruction Bool)
    (L : Language Bool) :
    RecursiveLanguage L <-> FiniteGeneralGrammarPairGenerated L :=
  boolean_recursive_language_iff_finite_general_grammar_pair_of_finite_section52_closeout
    (concrete_finite_section52_closeout_of_semantic_closeout
      hclose hpresentation hfinite)
    L

/-!
The theorem equating general grammars with recursively enumerable languages is
now split into two statements. For semantic unrestricted grammars, the reverse
direction is proved by {name}`SemanticLanguageGrammar`: arbitrary production
predicates can generate any language with one nonterminal. The finite/effective
content is factored through {name}`ConcreteBooleanFiniteGrammarSection52Closeout`.
Under that closeout,
{name}`boolean_recursive_language_iff_finite_general_grammar_pair_of_finite_section52_closeout`
proves the finite grammar pair characterization. The narrower
{name}`ConcreteBooleanFiniteDataSection52CompilerCloseout` records concrete
finite-data ingredients: the paired-recognizer dovetail compiler, the finite
first-order grammar-presentation recognizer compiler, and the description-backed
recognizer-to-finite grammar construction. The ordinary finite-grammar compiler
is now a derived bridge: a finite grammar is converted to an explicit
{lit}`Fin n` production-list presentation, and the compiled presentation
recognizer is transferred to the abstract recognizer by accepted-language
extensionality. The presentation compiler itself is factored through a bounded
derivation-search recognizer compiler. That bounded recognizer is now mirrored
by explicit finite production-list certificate recognizers. The indexed
certificate form names each rewrite rule by a finite index into the production
list, and its recursive checked-data form is proved sound and complete for the
indexed proof certificate. The checked-data trace and bounded search are proved
equivalent to the derivation search, so the remaining finite grammar table
construction is a first-order certificate-checking compiler problem: verify a
bounded list of indexed sentential-form rewrites and emit acceptance exactly
when such a certificate exists. The corresponding checked certificate-recognizer
compiler target now implies the indexed, bounded, and first-order presentation
compiler targets.

The declarations above now pin that infrastructure down as
{name}`ConcreteBooleanSection52CompilerCloseout` for the semantic grammar page
and {name}`ConcreteBooleanFiniteGrammarSection52Closeout` for the finite grammar
page, while {name}`ConcreteBooleanFiniteDataSection52CompilerCloseout` records
the narrowed finite/effective route. These closeouts carry
{name}`BoundedTraceSearchConstruction` as the primary finite-trace handoff. The
semantic closeout uses the semantic reverse grammar construction. The
finite-data closeout replaces the older broad dovetail compiler by a paired
recognizer dovetail compiler; the bounded-dovetail table target is proved
equivalent to that paired-recognizer target. It also uses the first-order finite
grammar-presentation compiler as its finite grammar-recognizer input, and uses the
description-backed construction
{name}`ConcreteDescriptionRecognizerToFiniteGeneralGrammarConstruction`.
The first-order presentation, checked-certificate, and runner-search
boundaries identify the remaining transition-table construction work without
changing these book-facing equivalence statements.
-/


end Section02
end Chapter05
end Book
end FoC
