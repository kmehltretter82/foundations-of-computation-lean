import FoC.Book.Chapter05.Section02.ConstructionStatus
import FoC.Book.Chapter05.Section02.Dovetailing
import FoC.Computability.Compiler.Core.Language
import FoC.Computability.FiniteProgram
import FoC.Computability.Grammar.Closeouts

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter05
namespace Section02

/-!
# Section 5.2: Grammar Recognizers
-/

open Languages
open Computability
open Grammars

universe u v

/-!
## Grammar Recognizers and Finite Presentations

The definitions relate unrestricted grammar generation to recursive
enumerability and state the recursive-language characterization using grammars
for a language and its complement.

Finite derivations provide finite-stage evidence. The reusable grammar bridge
turns derivation length into an acceptance trace, bounded derivation search,
and staged recognizer program. Conversely, a recognizer trace becomes a
trace-simulation grammar in which each finite accepting configuration trace is
a semantic derivation. Finite trace tables yield explicit start-to-word
production lists, while
{name}`MachineDescriptionHistoryGrammar.grammar` supplies a finite semi-Thue
presentation for any machine description by reversing its transition table and
cleaning initial configurations back to input words.

Semantic unrestricted grammars use the one-nonterminal construction in
{module}`FoC.Computability.Grammar.SemanticAndTraceTables`. Concrete
finite-description results use
{name}`DescriptionRecognizerToFiniteGeneralGrammarConstruction`: finite
grammars compile to recognizer descriptions, paired recognizers are dovetailed,
and description-backed recognizers are converted to finite grammars. The finite
presentation compiler is factored through bounded derivation search and its
certificate, indexed-certificate, and checked-indexed-certificate recognizers.

Proof-relevant {name}`GeneralGrammar.Presentation` is the canonical finite
grammar interface. Finite-production names remain as compatibility surfaces for
existing callers.
-/

theorem finite_production_list_derivation_certificate_trace_iff_trace
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {w : Word terminal} {n : Nat} :
    FiniteProductionListDerivationCertificateTrace G rules w n <->
      FiniteProductionListDerivationTrace G rules w n :=
  Computability.finiteProductionListDerivationCertificateTrace_iff_trace

theorem finite_production_list_indexed_derivation_certificate_trace_iff_trace
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {w : Word terminal} {n : Nat} :
    FiniteProductionListIndexedDerivationCertificateTrace
        G rules w n <->
      FiniteProductionListDerivationTrace G rules w n :=
  Computability.finiteProductionListIndexedDerivationCertificateTrace_iff_trace

theorem finite_production_list_checked_indexed_derivation_certificate_trace_iff_trace
    [DecidableEq terminal] [DecidableEq nonterminal]
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {w : Word terminal} {n : Nat} :
    FiniteProductionListCheckedIndexedDerivationCertificateTrace
        G rules w n <->
      FiniteProductionListDerivationTrace G rules w n :=
  Computability.finiteProductionListCheckedIndexedDerivationCertificateTrace_iff_trace

theorem finite_production_list_indexed_derivation_certificate_of_checked_data
    [DecidableEq terminal] [DecidableEq nonterminal]
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {n : Nat} {x y : SententialForm terminal nonterminal}
    {cert :
      FiniteProductionListIndexedDerivationCertificateData
        rules n x y}
    (h : cert.check = true) :
    FiniteProductionListIndexedDerivationCertificate rules n x y :=
  Computability.FiniteProductionListIndexedDerivationCertificateData.to_indexedCertificate_of_check_eq_true
    h

theorem finite_production_list_indexed_derivation_certificate_has_checked_data
    [DecidableEq terminal] [DecidableEq nonterminal]
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {n : Nat} {x y : SententialForm terminal nonterminal}
    (cert : FiniteProductionListIndexedDerivationCertificate rules n x y) :
    exists data :
      FiniteProductionListIndexedDerivationCertificateData
        rules n x y,
      data.check = true :=
  Computability.FiniteProductionListIndexedDerivationCertificateData.exists_check_eq_true_of_indexedCertificate
    cert

/-!
## Section 5.2 Grammar Closeouts

The underlying records are layered: the semantic closeout contains semantic
compiler principles, the finite-grammar closeout mixes semantic bridges with a
finite-presentation grammar compiler, and the finite-data closeout narrows the
dovetail and grammar-recognizer fields to finite-source or finite-presentation
targets while still carrying the acceptor bridge needed by the theorem surface.
-/

theorem concrete_finite_grammar_recognizer_compiler_of_finite_presentation_compiler
    (hcompile :
      FiniteBoolGeneralGrammarPresentation.CompilerConstruction) :
    FiniteBooleanGeneralGrammarRecognizerCompilerPrinciple :=
  Computability.finiteBooleanGeneralGrammarRecognizerCompilerPrinciple_of_productionListCompiler
    (Computability.finiteProductionListGrammarRecognizerCompilerConstruction_of_finitePresentationCompiler
      hcompile)

theorem concrete_finite_section52_closeout_of_semantic_closeout
    (hclose : BooleanSection52CompilerCloseout)
    (hpresentation :
      FiniteBoolGeneralGrammarPresentation.CompilerConstruction)
    (hfinite :
      RecursivelyEnumerableToFiniteGeneralGrammarPrinciple Bool) :
    BooleanFiniteGrammarSection52Closeout where
  boundedTraceSearch := hclose.boundedTraceSearch
  decidableToAcceptable := hclose.decidableToAcceptable
  dovetailDescription := hclose.dovetailDescription
  finiteGrammarRecognizerDescription := hpresentation
  recursivelyEnumerableToFiniteGrammar := hfinite

theorem concrete_finite_section52_closeout_of_semantic_closeout_and_description_compiler
    (hclose : BooleanSection52CompilerCloseout)
    (hcompile : SemanticDescriptionAcceptorCompilationAssumption) :
    BooleanFiniteGrammarSection52Closeout :=
  concrete_finite_section52_closeout_of_semantic_closeout hclose
    (FiniteBoolGeneralGrammarPresentation.compilerConstruction_of_descriptionCompiler
      hcompile)
    (Computability.recursivelyEnumerableToFiniteGeneralGrammarPrinciple_bool_of_descriptionCompiler
      hcompile)

theorem concrete_finite_data_section52_closeout_of_semantic_closeout
    (hclose : BooleanSection52CompilerCloseout)
    (hpresentation :
      FiniteBoolGeneralGrammarPresentation.CompilerConstruction) :
    BooleanFiniteDataSection52CompilerCloseout where
  boundedTraceSearch := hclose.boundedTraceSearch
  decidableToAcceptable := hclose.decidableToAcceptable
  pairedDovetailDescription :=
    paired_recognizer_dovetail_compiler_of_concrete_dovetail_description_compiler
      hclose.dovetailDescription
  finiteGrammarRecognizerDescription := hpresentation
  descriptionRecognizerToFiniteGrammar :=
    Computability.machineDescriptionAcceptsToFiniteGeneralGrammarConstruction_of_machineConstruction
      Computability.machineDescriptionToFiniteGeneralGrammarConstruction

theorem concrete_finite_data_section52_closeout_of_semantic_closeout_and_description_compilers
    (hclose : BooleanSection52CompilerCloseout)
    (haccept : SemanticDescriptionAcceptorCompilationAssumption)
    (hbool : SemanticDescriptionBoolDeciderCompilationAssumption) :
    BooleanFiniteDataSection52CompilerCloseout where
  boundedTraceSearch := hclose.boundedTraceSearch
  decidableToAcceptable := hclose.decidableToAcceptable
  pairedDovetailDescription :=
    paired_recognizer_dovetail_compiler_of_concrete_bool_description_compiler
      hbool
  finiteGrammarRecognizerDescription :=
    FiniteBoolGeneralGrammarPresentation.compilerConstruction_of_descriptionCompiler
      haccept
  descriptionRecognizerToFiniteGrammar :=
    Computability.machineDescriptionAcceptsToFiniteGeneralGrammarConstruction_of_machineConstruction
      Computability.machineDescriptionToFiniteGeneralGrammarConstruction

abbrev FiniteGeneralGrammarGenerated (L : Language terminal) : Prop :=
  GeneralGrammar.FinitePresentationGenerated L

/-- Canonical first-order finite Boolean grammar currency. A witness contains
the nonterminal bound, start symbol, and finite production list as data. -/
def FiniteBoolGrammarGenerated (L : Language Bool) : Prop :=
  exists P : FiniteBoolGeneralGrammarPresentation,
    Language.Equal (GeneralGrammar.GeneratedLanguage P.toGrammar) L

theorem finite_bool_grammar_generated_iff_finite_general_grammar_generated
    (L : Language Bool) :
    FiniteBoolGrammarGenerated L <-> FiniteGeneralGrammarGenerated L := by
  constructor
  · intro h
    rcases h with ⟨P, hP⟩
    exact ⟨Fin P.nonterminalCount, P.toGrammar,
      P.toGrammar_hasFinitePresentation, hP⟩
  · intro h
    rcases h with ⟨nonterminal, G, hfinite, hG⟩
    rcases hfinite with ⟨presentation⟩
    classical
    refine ⟨FiniteBoolGeneralGrammarPresentation.ofPresentation presentation, ?_⟩
    exact FoC.Foundation.FSet.equal_trans
      (FiniteBoolGeneralGrammarPresentation.generatedLanguage_equal_ofPresentation
        presentation)
      hG

def FiniteGeneralGrammarToRecursivelyEnumerableConstruction
    (terminal : Type u) : Prop :=
  forall L : Language terminal,
    FiniteGeneralGrammarGenerated L -> TuringAcceptable L

def GeneralGrammarPairGenerated (L : Language terminal) : Prop :=
  GeneralGrammar.Generated L ∧ GeneralGrammar.Generated (Language.Compl L)

def FiniteGeneralGrammarPairGenerated (L : Language terminal) : Prop :=
  FiniteGeneralGrammarGenerated L ∧
    FiniteGeneralGrammarGenerated (Language.Compl L)

def ConcreteFiniteGeneralGrammarRecognizerPresentsLanguage
    {nonterminal : Type}
    (G : GeneralGrammar Bool nonterminal)
    (L : Language Bool) : Prop :=
  GeneralGrammar.HasFinitePresentation G ∧
    Language.Equal (GeneralGrammar.GeneratedLanguage G) L ∧
      exists D : MachineDescription,
        ProgramCompiledByDescription
          (GeneralGrammarRecognizerProgram G) D

def ConcreteFiniteGeneralGrammarRecognizerLanguage
    (L : Language Bool) : Prop :=
  exists nonterminal : Type,
    exists G : GeneralGrammar Bool nonterminal,
      ConcreteFiniteGeneralGrammarRecognizerPresentsLanguage G L

/-!
## Finite Grammar Recognizer Presentations

A finite unrestricted grammar
together with a supplied description for its derivation-search recognizer is
already enough to obtain recursive enumerability of the generated language.
The harder compiler theorem is the uniform construction of that description
from the finite production list.
-/

/-!
## Derivation Traces and Staged Recognizers

For unrestricted grammars, a finite derivation is a finite acceptance trace.
The first theorems in this block build that trace-level recognizer before any
machine compiler is assumed.
-/

theorem general_grammar_derivation_trace_accepts_generated_language
    (G : GeneralGrammar terminal nonterminal) :
    AcceptanceTrace
      (GeneralGrammarDerivationTrace G)
      (GeneralGrammar.GeneratedLanguage G) :=
  Computability.generalGrammar_derivationTrace_acceptance G

theorem finite_production_list_trace_iff_general_derivation_trace
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs)
    {w : Word terminal} {n : Nat} :
    FiniteProductionListDerivationTrace G rules w n <->
      GeneralGrammarDerivationTrace G w n :=
  Computability.finiteProductionListDerivationTrace_iff_derivationTrace
    hrules

theorem finite_presentation_trace_iff_general_derivation_trace
    {G : GeneralGrammar terminal nonterminal}
    (presentation : GeneralGrammar.Presentation G)
    {w : Word terminal} {n : Nat} :
    FinitePresentationDerivationTrace presentation w n <->
      GeneralGrammarDerivationTrace G w n :=
  Computability.finitePresentationDerivationTrace_iff_derivationTrace
    presentation

theorem finite_production_list_trace_accepts_generated_language
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs) :
    AcceptanceTrace
      (FiniteProductionListDerivationTrace G rules)
      (GeneralGrammar.GeneratedLanguage G) :=
  Computability.finiteProductionListDerivationTrace_acceptance hrules

theorem finite_presentation_trace_accepts_generated_language
    {G : GeneralGrammar terminal nonterminal}
    (presentation : GeneralGrammar.Presentation G) :
    AcceptanceTrace
      (FinitePresentationDerivationTrace presentation)
      (GeneralGrammar.GeneratedLanguage G) :=
  Computability.finitePresentationDerivationTrace_acceptance presentation

theorem general_grammar_bounded_derivation_search_sound
    {G : GeneralGrammar terminal nonterminal}
    {w : Word terminal} {limit : Nat}
    (hit : GeneralGrammarBoundedDerivationSearch G w limit) :
    w ∈ GeneralGrammar.GeneratedLanguage G :=
  Computability.generalGrammarBoundedDerivationSearch_sound hit

theorem general_grammar_bounded_derivation_search_complete
    {G : GeneralGrammar terminal nonterminal}
    {w : Word terminal}
    (hw : w ∈ GeneralGrammar.GeneratedLanguage G) :
    exists limit : Nat,
      GeneralGrammarBoundedDerivationSearch G w limit :=
  Computability.generalGrammarBoundedDerivationSearch_complete hw

theorem finite_production_list_bounded_derivation_search_sound
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs)
    {w : Word terminal} {limit : Nat}
    (hit :
      FiniteProductionListBoundedDerivationSearch
        G rules w limit) :
    w ∈ GeneralGrammar.GeneratedLanguage G :=
  Computability.finiteProductionListBoundedDerivationSearch_sound
    hrules hit

theorem finite_production_list_bounded_derivation_search_complete
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs)
    {w : Word terminal}
    (hw : w ∈ GeneralGrammar.GeneratedLanguage G) :
    exists limit : Nat,
      FiniteProductionListBoundedDerivationSearch
        G rules w limit :=
  Computability.finiteProductionListBoundedDerivationSearch_complete
    hrules hw

theorem general_grammar_staged_recognizer_accepts_generated_language
    (G : GeneralGrammar terminal nonterminal) :
    ProgramAcceptsLanguage
      (GeneralGrammarRecognizerProgram G)
      (GeneralGrammar.GeneratedLanguage G) :=
  Computability.generalGrammarRecognizerProgram_acceptsLanguage G

theorem finite_production_list_staged_recognizer_accepts_generated_language
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs) :
    ProgramAcceptsLanguage
      (FiniteProductionListRecognizerProgram G rules)
      (GeneralGrammar.GeneratedLanguage G) :=
  Computability.finiteProductionListRecognizerProgram_acceptsLanguage
    hrules

theorem finite_presentation_staged_recognizer_accepts_generated_language
    {G : GeneralGrammar terminal nonterminal}
    (presentation : GeneralGrammar.Presentation G) :
    ProgramAcceptsLanguage
      (FinitePresentationRecognizerProgram presentation)
      (GeneralGrammar.GeneratedLanguage G) :=
  Computability.finitePresentationRecognizerProgram_acceptsLanguage
    presentation

theorem general_grammar_bounded_staged_recognizer_accepts_generated_language
    (G : GeneralGrammar terminal nonterminal) :
    ProgramAcceptsLanguage
      (GeneralGrammarBoundedRecognizerProgram G)
      (GeneralGrammar.GeneratedLanguage G) :=
  Computability.generalGrammarBoundedRecognizerProgram_acceptsLanguage G

theorem finite_production_list_bounded_staged_recognizer_accepts_generated_language
    [DecidableEq terminal] [DecidableEq nonterminal]
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs) :
    ProgramAcceptsLanguage
      (FiniteProductionListBoundedRecognizerProgram G rules)
      (GeneralGrammar.GeneratedLanguage G) :=
  Computability.finiteProductionListBoundedRecognizerProgram_acceptsLanguage
    hrules

theorem finite_presentation_bounded_staged_recognizer_accepts_generated_language
    [DecidableEq terminal] [DecidableEq nonterminal]
    {G : GeneralGrammar terminal nonterminal}
    (presentation : GeneralGrammar.Presentation G) :
    ProgramAcceptsLanguage
      (FinitePresentationBoundedRecognizerProgram presentation)
      (GeneralGrammar.GeneratedLanguage G) :=
  Computability.finitePresentationBoundedRecognizerProgram_acceptsLanguage
    presentation

theorem finite_production_list_certificate_staged_recognizer_accepts_generated_language
    [DecidableEq terminal] [DecidableEq nonterminal]
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs) :
    ProgramAcceptsLanguage
      (FiniteProductionListCertificateRecognizerProgram G rules)
      (GeneralGrammar.GeneratedLanguage G) :=
  Computability.finiteProductionListCertificateRecognizerProgram_acceptsLanguage
    hrules

theorem finite_production_list_indexed_certificate_staged_recognizer_accepts_generated_language
    [DecidableEq terminal] [DecidableEq nonterminal]
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs) :
    ProgramAcceptsLanguage
      (FiniteProductionListIndexedCertificateRecognizerProgram
        G rules)
      (GeneralGrammar.GeneratedLanguage G) :=
  Computability.finiteProductionListIndexedCertificateRecognizerProgram_acceptsLanguage
    hrules

theorem finite_production_list_checked_indexed_certificate_staged_recognizer_accepts_generated_language
    [DecidableEq terminal] [DecidableEq nonterminal]
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs) :
    ProgramAcceptsLanguage
      (FiniteProductionListCheckedIndexedCertificateRecognizerProgram
        G rules)
      (GeneralGrammar.GeneratedLanguage G) :=
  Computability.finiteProductionListCheckedIndexedCertificateRecognizerProgram_acceptsLanguage
    hrules

theorem finite_production_list_certificate_staged_recognizer_same_language_as_bounded
    [DecidableEq terminal] [DecidableEq nonterminal]
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs) :
    forall w : Word terminal,
      ProgramHaltsWithOutput
          (FiniteProductionListCertificateRecognizerProgram
            G rules) w [] <->
        ProgramHaltsWithOutput
          (FiniteProductionListBoundedRecognizerProgram
            G rules) w [] :=
  Computability.finiteProductionListCertificateRecognizerProgram_same_language
    hrules

theorem finite_production_list_indexed_certificate_staged_recognizer_same_language_as_bounded
    [DecidableEq terminal] [DecidableEq nonterminal]
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs) :
    forall w : Word terminal,
      ProgramHaltsWithOutput
          (FiniteProductionListIndexedCertificateRecognizerProgram
            G rules) w [] <->
        ProgramHaltsWithOutput
          (FiniteProductionListBoundedRecognizerProgram
            G rules) w [] :=
  Computability.finiteProductionListIndexedCertificateRecognizerProgram_same_language
    hrules

theorem finite_production_list_checked_indexed_certificate_staged_recognizer_same_language_as_bounded
    [DecidableEq terminal] [DecidableEq nonterminal]
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs) :
    forall w : Word terminal,
      ProgramHaltsWithOutput
          (FiniteProductionListCheckedIndexedCertificateRecognizerProgram
            G rules) w [] <->
        ProgramHaltsWithOutput
          (FiniteProductionListBoundedRecognizerProgram
            G rules) w [] :=
  Computability.finiteProductionListCheckedIndexedCertificateRecognizerProgram_same_language
    hrules

theorem acceptance_trace_simulation_grammar_derivesIn_one_of_trace
    {trace : Word terminal -> Nat -> Prop}
    {w : Word terminal} {n : Nat}
    (h : trace w n) :
    GeneralGrammar.DerivesIn
      (TraceSimulationGrammar trace) 1
      [Symbol.nonterminal ()]
      (SententialForm.terminalWord w) :=
  Computability.traceSimulationGrammar_derivesIn_one_of_trace h

theorem acceptance_trace_simulation_grammar_generated
    {trace : Word terminal -> Nat -> Prop}
    {L : Language terminal}
    (htrace : AcceptanceTrace trace L) :
    Language.Equal
      (GeneralGrammar.GeneratedLanguage
        (TraceSimulationGrammar trace)) L :=
  Computability.traceSimulationGrammar_generated_of_acceptanceTrace htrace

theorem acceptance_trace_generated_by_simulation_grammar
    {trace : Word terminal -> Nat -> Prop}
    {L : Language terminal}
    (htrace : AcceptanceTrace trace L) :
    GeneralGrammar.Generated L :=
  Computability.acceptanceTrace_generated_by_traceSimulationGrammar htrace

theorem machine_configuration_trace_simulation_grammar_derivesIn_one_of_haltsIn
    {D : MachineDescription} {w : Word Bool} {n : Nat}
    (h : D.HaltsIn n w) :
    GeneralGrammar.DerivesIn
      (MachineHaltingTraceSimulationGrammar D) 1
      [Symbol.nonterminal ()]
      (SententialForm.terminalWord w) :=
  Computability.machineHaltingTraceSimulationGrammar_derivesIn_one_of_haltsIn h

theorem machine_configuration_trace_simulation_grammar_generated
    (D : MachineDescription) :
    Language.Equal
      (GeneralGrammar.GeneratedLanguage
        (MachineHaltingTraceSimulationGrammar D))
      (fun w => D.HaltsOnInput w) :=
  Computability.machineHaltingTraceSimulationGrammar_generated D

theorem concrete_machine_description_accepts_generated_by_configuration_trace_grammar
    {D : MachineDescription} {L : Language Bool}
    (h : MachineDescriptionAcceptsLanguage D L) :
    Language.Equal
      (GeneralGrammar.GeneratedLanguage
        (MachineHaltingTraceSimulationGrammar D)) L :=
  Computability.machineDescription_accepts_generated_by_traceSimulationGrammar h

theorem concrete_machine_history_grammar_has_finite_productions
    (D : MachineDescription) :
    GeneralGrammar.HasFiniteProductions
      (MachineDescriptionHistoryGrammar.grammar D) :=
  Computability.MachineDescriptionHistoryGrammar.hasFiniteProductions D

theorem concrete_machine_history_grammar_has_finite_presentation
    (D : MachineDescription) :
    GeneralGrammar.HasFinitePresentation
      (MachineDescriptionHistoryGrammar.grammar D) :=
  Computability.MachineDescriptionHistoryGrammar.hasFinitePresentation D

theorem concrete_machine_history_grammar_complete
    {D : MachineDescription} {w : Word Bool}
    (h : D.HaltsOnInput w) :
    w ∈ GeneralGrammar.GeneratedLanguage
      (MachineDescriptionHistoryGrammar.grammar D) :=
  Computability.MachineDescriptionHistoryGrammar.complete h

theorem concrete_machine_history_grammar_sound
    {D : MachineDescription} (hD : D.WellFormed) {w : Word Bool}
    (h : w ∈ GeneralGrammar.GeneratedLanguage
      (MachineDescriptionHistoryGrammar.grammar D)) :
    D.HaltsOnInput w :=
  Computability.MachineDescriptionHistoryGrammar.sound hD h

theorem concrete_machine_history_grammar_generated
    {D : MachineDescription} (hD : D.WellFormed) :
    Language.Equal
      (GeneralGrammar.GeneratedLanguage
        (MachineDescriptionHistoryGrammar.grammar D))
      (fun w : Word Bool => D.HaltsOnInput w) :=
  Computability.MachineDescriptionHistoryGrammar.generated_language hD

/-- A supplied well-formed finite recognizer description yields canonical
first-order finite Boolean grammar data via its machine-history grammar. -/
theorem finite_bool_grammar_generated_of_machine_description_accepts
    {D : MachineDescription} {L : Language Bool}
    (h : MachineDescriptionAcceptsLanguage D L) :
    FiniteBoolGrammarGenerated L := by
  classical
  refine ⟨FiniteBoolGeneralGrammarPresentation.ofPresentation
    (MachineDescriptionHistoryGrammar.presentation D), ?_⟩
  exact FoC.Foundation.FSet.equal_trans
    (FiniteBoolGeneralGrammarPresentation.generatedLanguage_equal_ofPresentation
      (MachineDescriptionHistoryGrammar.presentation D))
    (FoC.Foundation.FSet.equal_trans
      (MachineDescriptionHistoryGrammar.generated_language h.left)
      h.right)

/-- Every language recognized by a supplied finite description has a
canonical first-order finite Boolean history grammar. -/
theorem concrete_finite_recognizable_language_finite_bool_grammar_generated
    {L : Language Bool}
    (h : ConcreteFiniteRecognizableLanguage L) :
    FiniteBoolGrammarGenerated L := by
  rcases h with ⟨P, hP⟩
  exact finite_bool_grammar_generated_of_machine_description_accepts
    (D := P.description) hP

/-- Compiling the canonical recognizer of first-order finite Boolean grammar
data supplies the converse finite recognizability direction. -/
theorem concrete_finite_recognizable_language_of_finite_bool_grammar_generated
    (hcompile :
      FiniteBoolGeneralGrammarPresentation.CompilerConstruction)
    {L : Language Bool}
    (h : FiniteBoolGrammarGenerated L) :
    ConcreteFiniteRecognizableLanguage L := by
  rcases h with ⟨P, hP⟩
  rcases hcompile P with ⟨D, hD⟩
  refine ⟨{ description := D }, ?_⟩
  exact programCompiledByDescription_acceptsLanguage
    (fun w => Iff.trans (P.recognizerProgram_acceptsLanguage w) (hP w))
    hD

/-- The effective finite grammar characterization, conditional only on the
first-order finite-presentation recognizer compiler. -/
theorem concrete_finite_recognizable_language_iff_finite_bool_grammar_generated
    (hcompile :
      FiniteBoolGeneralGrammarPresentation.CompilerConstruction)
    (L : Language Bool) :
    ConcreteFiniteRecognizableLanguage L <-> FiniteBoolGrammarGenerated L := by
  constructor
  case mpr =>
    exact concrete_finite_recognizable_language_of_finite_bool_grammar_generated
      hcompile
  case mp =>
    exact concrete_finite_recognizable_language_finite_bool_grammar_generated

/-- Boolean-terminal corollary in the proof-relevant finite-presentation
currency used by the general grammar API. -/
theorem concrete_finite_recognizable_language_iff_finite_general_grammar_generated
    (hcompile :
      FiniteBoolGeneralGrammarPresentation.CompilerConstruction)
    (L : Language Bool) :
    ConcreteFiniteRecognizableLanguage L <->
      FiniteGeneralGrammarGenerated L := by
  exact Iff.trans
    (concrete_finite_recognizable_language_iff_finite_bool_grammar_generated
      hcompile L)
    (finite_bool_grammar_generated_iff_finite_general_grammar_generated L)

/-!
## Finite Acceptance Trace Tables

A finite table of accepting traces gives a genuine
finite-production grammar: the production list contains one rule from the start
nonterminal to each table word. This is the finite-data bridge used to state the
description-backed recognizer-to-finite-grammar interface precisely.
-/

theorem concrete_finite_acceptance_trace_table_has_finite_productions
    (T : FiniteAcceptanceTraceTable terminal) :
    GeneralGrammar.HasFiniteProductions
      (T.grammar) :=
  Computability.FiniteAcceptanceTraceTable.hasFiniteProductions T

theorem concrete_finite_acceptance_trace_table_has_finite_presentation
    (T : FiniteAcceptanceTraceTable terminal) :
    GeneralGrammar.HasFinitePresentation
      (T.grammar) :=
  Computability.FiniteAcceptanceTraceTable.hasFinitePresentation T

theorem concrete_finite_acceptance_trace_table_generated_language
    (T : FiniteAcceptanceTraceTable terminal) :
    Language.Equal
      (GeneralGrammar.GeneratedLanguage
        (T.grammar))
      (T.language) :=
  Computability.FiniteAcceptanceTraceTable.generated_language T

theorem concrete_finite_acceptance_trace_table_finite_presentation_generated
    (T : FiniteAcceptanceTraceTable terminal) :
    FiniteGeneralGrammarGenerated
      (T.language) :=
  Computability.FiniteAcceptanceTraceTable.finitePresentationGenerated_language T

theorem concrete_finite_acceptance_trace_table_finite_production_generated
    (T : FiniteAcceptanceTraceTable terminal) :
    GeneralGrammar.FiniteProductionGenerated
      (T.language) :=
  Computability.FiniteAcceptanceTraceTable.finiteProductionGenerated_language T

theorem concrete_finite_trace_table_recognizable_finite_presentation_generated
    {L : Language terminal}
    (h : FiniteTraceTableRecognizable L) :
    FiniteGeneralGrammarGenerated L :=
  Computability.finiteTraceTableRecognizable_finitePresentationGenerated h

theorem concrete_finite_trace_table_recognizable_finite_production_generated
    {L : Language terminal}
    (h : FiniteTraceTableRecognizable L) :
    GeneralGrammar.FiniteProductionGenerated L :=
  Computability.finiteTraceTableRecognizable_finiteProductionGenerated h

theorem concrete_finite_trace_table_to_finite_general_grammar_construction
    (terminal : Type u) :
    FiniteTraceTableToFiniteGeneralGrammarConstruction terminal :=
  Computability.finiteTraceTableToFiniteGeneralGrammarConstruction terminal

theorem concrete_machine_finite_acceptance_trace_table_generated
    {D : MachineDescription}
    {T : MachineFiniteAcceptanceTraceTable D}
    (hT : MachineFiniteAcceptanceTraceTable.Presents D T) :
    Language.Equal
      (GeneralGrammar.GeneratedLanguage
        (T.grammar))
      (fun w : Word Bool => D.HaltsOnInput w) :=
  Computability.machineFiniteAcceptanceTraceTable_generated hT

theorem concrete_machine_finite_acceptance_trace_table_finite_presentation_generated
    {D : MachineDescription}
    {T : MachineFiniteAcceptanceTraceTable D}
    (hT : MachineFiniteAcceptanceTraceTable.Presents D T) :
    FiniteGeneralGrammarGenerated
      (fun w : Word Bool => D.HaltsOnInput w) :=
  Computability.machineFiniteAcceptanceTraceTable_finitePresentationGenerated hT

theorem concrete_machine_finite_acceptance_trace_table_finite_production_generated
    {D : MachineDescription}
    {T : MachineFiniteAcceptanceTraceTable D}
    (hT : MachineFiniteAcceptanceTraceTable.Presents D T) :
    GeneralGrammar.FiniteProductionGenerated
      (fun w : Word Bool => D.HaltsOnInput w) :=
  Computability.machineFiniteAcceptanceTraceTable_finiteProductionGenerated hT

theorem concrete_machine_description_accepts_to_finite_general_grammar :
    MachineDescriptionAcceptsToFiniteGeneralGrammarConstruction :=
  Computability.machineDescriptionAcceptsToFiniteGeneralGrammarConstruction_of_machineConstruction
    Computability.machineDescriptionToFiniteGeneralGrammarConstruction

/-!
## From Grammars to Recognizable Languages

Finite presentations produce staged recognizers directly. Supplying the
appropriate description compiler then upgrades those program-level results to
recursive enumerability.
-/

theorem finite_general_grammar_has_finite_list_staged_recognizer
    {G : GeneralGrammar terminal nonterminal}
    (hfinite : GeneralGrammar.HasFiniteProductions G) :
    exists rules : List (GeneralGrammar.Production terminal nonterminal),
      ProgramAcceptsLanguage
        (FiniteProductionListRecognizerProgram G rules)
        (GeneralGrammar.GeneratedLanguage G) :=
  Computability.finiteProductionListRecognizerProgram_acceptsLanguage_of_hasFiniteProductions
    hfinite

theorem finite_general_grammar_has_finite_presentation_staged_recognizer
    {G : GeneralGrammar terminal nonterminal}
    (hfinite : GeneralGrammar.HasFinitePresentation G) :
    exists presentation : GeneralGrammar.Presentation G,
      ProgramAcceptsLanguage
        (FinitePresentationRecognizerProgram presentation)
        (GeneralGrammar.GeneratedLanguage G) :=
  Computability.finitePresentationRecognizerProgram_acceptsLanguage_of_hasFinitePresentation
    hfinite

theorem general_grammar_generated_language_is_program_acceptable
    (G : GeneralGrammar terminal nonterminal) :
    ProgramAcceptable (GeneralGrammar.GeneratedLanguage G) :=
  Computability.generalGrammar_generatedLanguage_programAcceptable G

theorem boolean_general_grammar_generated_language_is_recursively_enumerable_of_concrete_description
    (G : GeneralGrammar Bool nonterminal)
    {D : MachineDescription}
    (hcompile : ProgramCompiledByDescription
      (GeneralGrammarRecognizerProgram G) D) :
    TuringAcceptable (GeneralGrammar.GeneratedLanguage G) :=
  concrete_program_acceptable_by_description_turing_acceptable
    (by
      exists GeneralGrammarRecognizerProgram G
      exists D
      exact And.intro
        (general_grammar_staged_recognizer_accepts_generated_language G)
        hcompile)

theorem boolean_general_grammar_generated_is_recursively_enumerable_of_concrete_description
    {L : Language Bool}
    (G : GeneralGrammar Bool nonterminal)
    {D : MachineDescription}
    (hcompile : ProgramCompiledByDescription
      (GeneralGrammarRecognizerProgram G) D)
    (hEq : Language.Equal (GeneralGrammar.GeneratedLanguage G) L) :
    TuringAcceptable L :=
  recursively_enumerable_language_of_equal
    (boolean_general_grammar_generated_language_is_recursively_enumerable_of_concrete_description
      G hcompile)
    hEq

theorem concrete_finite_general_grammar_recognizer_presentation_recursively_enumerable
    {nonterminal : Type}
    (G : GeneralGrammar Bool nonterminal)
    {L : Language Bool}
    (h : ConcreteFiniteGeneralGrammarRecognizerPresentsLanguage G L) :
    TuringAcceptable L := by
  cases h.right.right with
  | intro D hD =>
      exact
        boolean_general_grammar_generated_is_recursively_enumerable_of_concrete_description
          G hD h.right.left

theorem concrete_finite_general_grammar_recognizer_language_recursively_enumerable
    {L : Language Bool}
    (h : ConcreteFiniteGeneralGrammarRecognizerLanguage L) :
    TuringAcceptable L := by
  cases h with
  | intro nonterminal hnonterminal =>
      cases hnonterminal with
      | intro G hG =>
          exact
            concrete_finite_general_grammar_recognizer_presentation_recursively_enumerable
              G hG

theorem concrete_finite_general_grammar_recognizer_presentation_generated
    {nonterminal : Type}
    (G : GeneralGrammar Bool nonterminal)
    {L : Language Bool}
    (h : ConcreteFiniteGeneralGrammarRecognizerPresentsLanguage G L) :
    FiniteGeneralGrammarGenerated L := by
  exists nonterminal
  exists G
  exact And.intro h.left h.right.left

theorem concrete_finite_general_grammar_recognizer_language_generated
    {L : Language Bool}
    (h : ConcreteFiniteGeneralGrammarRecognizerLanguage L) :
    FiniteGeneralGrammarGenerated L := by
  cases h with
  | intro nonterminal hnonterminal =>
      cases hnonterminal with
      | intro G hG =>
          exact
            concrete_finite_general_grammar_recognizer_presentation_generated
              G hG

theorem boolean_general_grammar_generated_language_is_recursively_enumerable_of_concrete_grammar_compiler
    {nonterminal : Type}
    (hcompile : Computability.SemanticBooleanGeneralGrammarRecognizerCompilerAssumption)
    (G : GeneralGrammar Bool nonterminal) :
    TuringAcceptable (GeneralGrammar.GeneratedLanguage G) := by
  cases hcompile (nonterminal := nonterminal) G with
  | intro D hD =>
      exact
        boolean_general_grammar_generated_language_is_recursively_enumerable_of_concrete_description
          G hD

theorem boolean_general_grammar_generated_is_recursively_enumerable_of_concrete_grammar_compiler
    {nonterminal : Type}
    (hcompile : Computability.SemanticBooleanGeneralGrammarRecognizerCompilerAssumption)
    {L : Language Bool}
    (G : GeneralGrammar Bool nonterminal)
    (hEq : Language.Equal (GeneralGrammar.GeneratedLanguage G) L) :
    TuringAcceptable L :=
  recursively_enumerable_language_of_equal
    (boolean_general_grammar_generated_language_is_recursively_enumerable_of_concrete_grammar_compiler
      hcompile G)
    hEq

theorem boolean_general_grammar_to_recursively_enumerable_construction_of_concrete_grammar_compiler
    (hcompile : Computability.SemanticBooleanGeneralGrammarRecognizerCompilerAssumption) :
    GeneralGrammarToRecursivelyEnumerablePrinciple Bool := by
  intro L hgenerated
  cases hgenerated with
  | intro nonterminal hnonterminal =>
      cases hnonterminal with
      | intro G hEq =>
          exact
            boolean_general_grammar_generated_is_recursively_enumerable_of_concrete_grammar_compiler
              hcompile (nonterminal := nonterminal) G hEq

theorem boolean_finite_general_grammar_generated_is_recursively_enumerable_of_concrete_grammar_compiler
    (hcompile : Computability.SemanticBooleanGeneralGrammarRecognizerCompilerAssumption)
    {L : Language Bool}
    (h : FiniteGeneralGrammarGenerated L) :
    TuringAcceptable L := by
  cases h with
  | intro nonterminal hnonterminal =>
      cases hnonterminal with
      | intro G hG =>
          exact
            boolean_general_grammar_generated_is_recursively_enumerable_of_concrete_grammar_compiler
              hcompile (nonterminal := nonterminal) G hG.right

namespace BooleanFiniteGeneralGrammar

theorem generated_re_of_concreteFiniteGrammarCompiler
    (hcompile : FiniteBooleanGeneralGrammarRecognizerCompilerPrinciple)
    {L : Language Bool}
    (h : FiniteGeneralGrammarGenerated L) :
    TuringAcceptable L := by
  cases h with
  | intro nonterminal hnonterminal =>
      cases hnonterminal with
      | intro G hG =>
          cases hcompile (nonterminal := nonterminal) G
              (GeneralGrammar.hasFiniteProductions_of_hasFinitePresentation
                hG.left) with
          | intro D hD =>
              exact
                boolean_general_grammar_generated_is_recursively_enumerable_of_concrete_description
                  G hD hG.right

end BooleanFiniteGeneralGrammar

theorem concrete_finite_general_grammar_recognizer_presentation_of_finite_compiler
    (hcompile : FiniteBooleanGeneralGrammarRecognizerCompilerPrinciple)
    {nonterminal : Type}
    (G : GeneralGrammar Bool nonterminal)
    (hfinite : GeneralGrammar.HasFinitePresentation G) :
    ConcreteFiniteGeneralGrammarRecognizerPresentsLanguage
      G (GeneralGrammar.GeneratedLanguage G) := by
  cases hcompile G
      (GeneralGrammar.hasFiniteProductions_of_hasFinitePresentation hfinite) with
  | intro D hD =>
      constructor
      · exact hfinite
      · constructor
        · intro w
          rfl
        · exists D

theorem concrete_finite_general_grammar_recognizer_language_of_finite_compiler
    (hcompile : FiniteBooleanGeneralGrammarRecognizerCompilerPrinciple)
    {nonterminal : Type}
    (G : GeneralGrammar Bool nonterminal)
    (hfinite : GeneralGrammar.HasFinitePresentation G) :
    ConcreteFiniteGeneralGrammarRecognizerLanguage
      (GeneralGrammar.GeneratedLanguage G) := by
  exists nonterminal
  exists G
  exact
    concrete_finite_general_grammar_recognizer_presentation_of_finite_compiler
      hcompile G hfinite

theorem boolean_finite_general_grammar_to_recursively_enumerable_construction_of_concrete_grammar_compiler
    (hcompile : Computability.SemanticBooleanGeneralGrammarRecognizerCompilerAssumption) :
    FiniteGeneralGrammarToRecursivelyEnumerableConstruction Bool := by
  intro L hgenerated
  exact
    boolean_finite_general_grammar_generated_is_recursively_enumerable_of_concrete_grammar_compiler
      hcompile hgenerated

namespace BooleanFiniteGeneralGrammar

theorem to_re_construction_of_concreteFiniteGrammarCompiler
    (hcompile : FiniteBooleanGeneralGrammarRecognizerCompilerPrinciple) :
    FiniteGeneralGrammarToRecursivelyEnumerableConstruction Bool := by
  intro L hgenerated
  exact
    generated_re_of_concreteFiniteGrammarCompiler
      hcompile hgenerated

end BooleanFiniteGeneralGrammar

theorem finite_general_grammar_generated_language_is_program_acceptable
    {L : Language terminal}
    (h : FiniteGeneralGrammarGenerated L) :
    ProgramAcceptable L :=
  Computability.finitePresentationGenerated_programAcceptable h

theorem general_grammar_generated_language_is_recursively_enumerable_of_staged_program_compiler
    (hcompile : ProgramAcceptorCompilationPrinciple terminal)
    (G : GeneralGrammar terminal nonterminal) :
    TuringAcceptable (GeneralGrammar.GeneratedLanguage G) :=
  Computability.generalGrammar_generatedLanguage_turingAcceptable_of_programCompiler
    hcompile G

theorem general_grammar_generated_is_recursively_enumerable_of_staged_program_compiler
    (hcompile : ProgramAcceptorCompilationPrinciple terminal)
    {L : Language terminal}
    (h : GeneralGrammar.Generated L) :
    TuringAcceptable L :=
  Computability.generalGrammar_generated_turingAcceptable_of_programCompiler
    hcompile h

theorem general_grammar_to_recursively_enumerable_construction_of_staged_program_compiler
    (hcompile : ProgramAcceptorCompilationPrinciple terminal) :
    GeneralGrammarToRecursivelyEnumerablePrinciple terminal := by
  intro L hgenerated
  exact
    general_grammar_generated_is_recursively_enumerable_of_staged_program_compiler
      hcompile hgenerated

theorem finite_general_grammar_generated_language_is_recursively_enumerable_of_staged_program_compiler
    (hcompile : ProgramAcceptorCompilationPrinciple terminal)
    {L : Language terminal}
    (h : FiniteGeneralGrammarGenerated L) :
    TuringAcceptable L :=
  Computability.finitePresentationGenerated_turingAcceptable_of_programCompiler
    hcompile h

theorem finite_general_grammar_to_recursively_enumerable_construction_of_staged_program_compiler
    (hcompile : ProgramAcceptorCompilationPrinciple terminal) :
    FiniteGeneralGrammarToRecursivelyEnumerableConstruction terminal := by
  intro L hgenerated
  exact
    finite_general_grammar_generated_language_is_recursively_enumerable_of_staged_program_compiler
      hcompile hgenerated

/-!
## Semantic Reverse Construction and Equivalences

The semantic reverse construction turns every recursively enumerable language
into an unrestricted grammar. Combining it with the forward constructions
yields the final grammar/RE equivalence surfaces.
-/

theorem recursively_enumerable_to_general_grammar_construction_semantic :
    RecursivelyEnumerableToGeneralGrammarPrinciple terminal :=
  Computability.recursivelyEnumerableToGeneralGrammarPrinciple_semantic
    terminal

theorem general_grammar_acceptability_equivalence_of_constructions
    (hto : GeneralGrammarToRecursivelyEnumerablePrinciple terminal)
    (hfrom : RecursivelyEnumerableToGeneralGrammarPrinciple terminal)
    (L : Language terminal) :
    GeneralGrammarAcceptabilityEquivalence L := by
  constructor
  · exact hto L
  · exact hfrom L

theorem general_grammar_re_equivalence_construction_of_constructions
    (hto : GeneralGrammarToRecursivelyEnumerablePrinciple terminal)
    (hfrom : RecursivelyEnumerableToGeneralGrammarPrinciple terminal) :
    GeneralGrammarREEquivalencePrinciple terminal := by
  intro L
  exact general_grammar_acceptability_equivalence_of_constructions
    hto hfrom L

theorem general_grammar_re_equivalence_construction_of_to_construction
    (hto : GeneralGrammarToRecursivelyEnumerablePrinciple terminal) :
    GeneralGrammarREEquivalencePrinciple terminal :=
  general_grammar_re_equivalence_construction_of_constructions
    hto recursively_enumerable_to_general_grammar_construction_semantic

theorem finite_general_grammar_acceptability_equivalence_of_constructions
    (hto : FiniteGeneralGrammarToRecursivelyEnumerableConstruction terminal)
    (hfrom :
      RecursivelyEnumerableToFinitePresentationGeneralGrammarPrinciple
        terminal)
    (L : Language terminal) :
    FiniteGeneralGrammarGenerated L <-> TuringAcceptable L := by
  constructor
  · exact hto L
  · exact hfrom L

theorem finite_general_grammar_re_equivalence_construction_of_constructions
    (hto : FiniteGeneralGrammarToRecursivelyEnumerableConstruction terminal)
    (hfrom :
      RecursivelyEnumerableToFinitePresentationGeneralGrammarPrinciple
        terminal) :
    FinitePresentationGeneralGrammarREEquivalencePrinciple terminal := by
  intro L
  exact finite_general_grammar_acceptability_equivalence_of_constructions
    hto hfrom L


end Section02
end Chapter05
end Book
end FoC
