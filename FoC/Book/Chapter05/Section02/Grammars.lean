import FoC.Book.Chapter05.Section02.Ranges

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter05
namespace Section02

/-!
# Section 5.2 grammar recognizers
-/

open Languages
open Computability
open Grammars

universe u v

/-!
**General Grammars and RE Languages.**

The final definitions relate unrestricted grammar generation to recursive
enumerability, then state the recursive-language equivalence for a language
and its complement under those construction principles.

Finite derivations are also finite-stage evidence: the reusable grammar bridge
turns derivation length into an acceptance trace, a bounded derivation search,
and a staged recognizer program. In the reverse direction, a recognizer trace
is represented as a trace-simulation grammar: each finite accepting
configuration trace becomes a one-step semantic derivation. For concrete finite
evidence, finite trace tables now produce an explicit finite list of
start-to-word productions, and {name}`ConcreteFiniteTraceTableRecognizable`
is proved to imply finite-production generation. For arbitrary machine
descriptions, {name}`ConcreteMachineHistoryGrammar` supplies the finite
semi-Thue presentation: it generates halting configurations, runs the finite
transition table backward, and cleans initial configurations to input words.
The finite-data closeout keeps the concrete recognizer route
description-backed: finite grammars are compiled to recognizer descriptions,
paired recognizers are dovetailed directly, and description-backed recognizers
use a dedicated finite-grammar construction interface.

For finite-production general grammars, the page already contains the
program-acceptability bridge and the supplied-description consequences. For
semantic unrestricted grammars, the reverse direction is now closed by the
one-nonterminal trace-simulation construction in
{module}`FoC.Computability.Grammar`. The effective textbook target used here is
the well-formed description-backed construction named
{name}`ConcreteDescriptionRecognizerToFiniteGeneralGrammarConstruction`. The
concrete finite-description compiler for finite grammar recognizers is a
separate named field of the finite-data closeout, and also follows from the
general description acceptor compiler by compiling the staged grammar
recognizer. The same description compiler now also supplies the certificate,
indexed-certificate, and checked-indexed-certificate recognizer targets used
to factor the finite presentation compiler. The paired-recognizer dovetail
field is supplied either by a
dedicated dovetail compiler or by the Boolean description decider compiler.
-/

def GeneralGrammarGeneratedLanguage (G : GeneralGrammar terminal nonterminal) :
    Language terminal :=
  GeneralGrammar.GeneratedLanguage G

def GeneralGrammarDerivationTraceLanguage
    (G : GeneralGrammar terminal nonterminal)
    (w : Word terminal) (n : Nat) : Prop :=
  GeneralGrammarDerivationTrace G w n

def GeneralGrammarFiniteProductionListTraceLanguage
    (G : GeneralGrammar terminal nonterminal)
    (rules : List (GeneralGrammar.Production terminal nonterminal))
    (w : Word terminal) (n : Nat) : Prop :=
  FiniteProductionListDerivationTrace G rules w n

def GeneralGrammarBoundedDerivationSearchLanguage
    (G : GeneralGrammar terminal nonterminal)
    (w : Word terminal) (limit : Nat) : Prop :=
  GeneralGrammarBoundedDerivationSearch G w limit

def GeneralGrammarFiniteProductionListBoundedSearchLanguage
    (G : GeneralGrammar terminal nonterminal)
    (rules : List (GeneralGrammar.Production terminal nonterminal))
    (w : Word terminal) (limit : Nat) : Prop :=
  FiniteProductionListBoundedDerivationSearch G rules w limit

noncomputable def GeneralGrammarStagedRecognizer
    (G : GeneralGrammar terminal nonterminal) :
    StagedProgram terminal Unit :=
  GeneralGrammarRecognizerProgram G

noncomputable def GeneralGrammarFiniteProductionListStagedRecognizer
    (G : GeneralGrammar terminal nonterminal)
    (rules : List (GeneralGrammar.Production terminal nonterminal)) :
    StagedProgram terminal Unit :=
  FiniteProductionListRecognizerProgram G rules

noncomputable def GeneralGrammarBoundedStagedRecognizer
    (G : GeneralGrammar terminal nonterminal) :
    StagedProgram terminal Unit :=
  GeneralGrammarBoundedRecognizerProgram G

noncomputable def GeneralGrammarFiniteProductionListBoundedStagedRecognizer
    (G : GeneralGrammar terminal nonterminal)
    (rules : List (GeneralGrammar.Production terminal nonterminal)) :
    StagedProgram terminal Unit :=
  FiniteProductionListBoundedRecognizerProgram G rules

def ConcreteFiniteProductionListDerivationCertificateTrace
    (G : GeneralGrammar terminal nonterminal)
    (rules : List (GeneralGrammar.Production terminal nonterminal))
    (w : Word terminal) (n : Nat) : Prop :=
  FiniteProductionListDerivationCertificateTrace G rules w n

def ConcreteFiniteProductionListIndexedDerivationCertificateTrace
    (G : GeneralGrammar terminal nonterminal)
    (rules : List (GeneralGrammar.Production terminal nonterminal))
    (w : Word terminal) (n : Nat) : Prop :=
  FiniteProductionListIndexedDerivationCertificateTrace G rules w n

def ConcreteFiniteProductionListCheckedIndexedDerivationCertificateTrace
    [DecidableEq terminal] [DecidableEq nonterminal]
    (G : GeneralGrammar terminal nonterminal)
    (rules : List (GeneralGrammar.Production terminal nonterminal))
    (w : Word terminal) (n : Nat) : Prop :=
  FiniteProductionListCheckedIndexedDerivationCertificateTrace G rules w n

abbrev ConcreteFiniteProductionListIndexedDerivationCertificateData
    (rules : List (GeneralGrammar.Production terminal nonterminal))
    (n : Nat)
    (x y : SententialForm terminal nonterminal) :=
  FiniteProductionListIndexedDerivationCertificateData rules n x y

noncomputable def GeneralGrammarFiniteProductionListCertificateStagedRecognizer
    (G : GeneralGrammar terminal nonterminal)
    (rules : List (GeneralGrammar.Production terminal nonterminal)) :
    StagedProgram terminal Unit :=
  FiniteProductionListCertificateRecognizerProgram G rules

noncomputable def GeneralGrammarFiniteProductionListIndexedCertificateStagedRecognizer
    (G : GeneralGrammar terminal nonterminal)
    (rules : List (GeneralGrammar.Production terminal nonterminal)) :
    StagedProgram terminal Unit :=
  FiniteProductionListIndexedCertificateRecognizerProgram G rules

noncomputable def GeneralGrammarFiniteProductionListCheckedIndexedCertificateStagedRecognizer
    [DecidableEq terminal] [DecidableEq nonterminal]
    (G : GeneralGrammar terminal nonterminal)
    (rules : List (GeneralGrammar.Production terminal nonterminal)) :
    StagedProgram terminal Unit :=
  FiniteProductionListCheckedIndexedCertificateRecognizerProgram G rules

theorem finite_production_list_derivation_certificate_trace_iff_trace
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {w : Word terminal} {n : Nat} :
    ConcreteFiniteProductionListDerivationCertificateTrace G rules w n <->
      FiniteProductionListDerivationTrace G rules w n :=
  Computability.finiteProductionListDerivationCertificateTrace_iff_trace

theorem finite_production_list_indexed_derivation_certificate_trace_iff_trace
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {w : Word terminal} {n : Nat} :
    ConcreteFiniteProductionListIndexedDerivationCertificateTrace
        G rules w n <->
      FiniteProductionListDerivationTrace G rules w n :=
  Computability.finiteProductionListIndexedDerivationCertificateTrace_iff_trace

theorem finite_production_list_checked_indexed_derivation_certificate_trace_iff_trace
    [DecidableEq terminal] [DecidableEq nonterminal]
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {w : Word terminal} {n : Nat} :
    ConcreteFiniteProductionListCheckedIndexedDerivationCertificateTrace
        G rules w n <->
      FiniteProductionListDerivationTrace G rules w n :=
  Computability.finiteProductionListCheckedIndexedDerivationCertificateTrace_iff_trace

theorem finite_production_list_indexed_derivation_certificate_of_checked_data
    [DecidableEq terminal] [DecidableEq nonterminal]
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {n : Nat} {x y : SententialForm terminal nonterminal}
    {cert :
      ConcreteFiniteProductionListIndexedDerivationCertificateData
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
      ConcreteFiniteProductionListIndexedDerivationCertificateData
        rules n x y,
      data.check = true :=
  Computability.FiniteProductionListIndexedDerivationCertificateData.exists_check_eq_true_of_indexedCertificate
    cert

abbrev ConcreteFiniteBoolGeneralGrammarPresentation :=
  FiniteBoolGeneralGrammarPresentation

def ConcreteFiniteBoolGeneralGrammarPresentationGrammar
    (P : ConcreteFiniteBoolGeneralGrammarPresentation) :
    GeneralGrammar Bool (Fin P.nonterminalCount) :=
  P.toGrammar

def ConcreteFiniteBoolGeneralGrammarPresentationGeneratedLanguage
    (P : ConcreteFiniteBoolGeneralGrammarPresentation) :
    Language Bool :=
  GeneralGrammarGeneratedLanguage P.toGrammar

noncomputable def ConcreteFiniteBoolGeneralGrammarPresentationStagedRecognizer
    (P : ConcreteFiniteBoolGeneralGrammarPresentation) :
    StagedProgram Bool Unit :=
  P.recognizerProgram

def AcceptanceTraceSimulationGrammar
    (trace : Word terminal -> Nat -> Prop) :
    GeneralGrammar terminal Unit :=
  TraceSimulationGrammar trace

def MachineConfigurationTraceSimulationGrammar
    (D : MachineDescription) : GeneralGrammar Bool Unit :=
  MachineHaltingTraceSimulationGrammar D

abbrev ConcreteFiniteAcceptanceTraceTable (terminal : Type u) :=
  FiniteAcceptanceTraceTable terminal

def ConcreteFiniteAcceptanceTraceTableLanguage
    (T : ConcreteFiniteAcceptanceTraceTable terminal) :
    Language terminal :=
  T.language

def ConcreteFiniteTraceTableToFiniteGeneralGrammarConstruction
    (terminal : Type u) : Prop :=
  FiniteTraceTableToFiniteGeneralGrammarConstruction terminal

def ConcreteFiniteAcceptanceTraceTableGrammar
    (T : ConcreteFiniteAcceptanceTraceTable terminal) :
    GeneralGrammar terminal Unit :=
  T.grammar

def ConcreteMachineFiniteAcceptanceTraceTable
    (D : MachineDescription) : Type :=
  MachineFiniteAcceptanceTraceTable D

def ConcreteMachineFiniteAcceptanceTraceTablePresents
    (D : MachineDescription)
    (T : ConcreteMachineFiniteAcceptanceTraceTable D) : Prop :=
  MachineFiniteAcceptanceTraceTable.Presents D T

def ConcreteMachineDescriptionToFiniteGeneralGrammarConstruction : Prop :=
  MachineDescriptionToFiniteGeneralGrammarConstruction

def ConcreteMachineDescriptionAcceptsToFiniteGeneralGrammarConstruction : Prop :=
  MachineDescriptionAcceptsToFiniteGeneralGrammarConstruction

theorem concrete_machine_description_to_finite_general_grammar_construction :
    ConcreteMachineDescriptionToFiniteGeneralGrammarConstruction :=
  Computability.machineDescriptionToFiniteGeneralGrammarConstruction

def SemanticBooleanGeneralGrammarRecognizerCompilerAssumption : Prop :=
  Computability.SemanticBooleanGeneralGrammarRecognizerCompilerAssumption

def ConcreteBooleanGeneralGrammarRecognizerCompilerConstruction : Prop :=
  SemanticBooleanGeneralGrammarRecognizerCompilerAssumption

def ConcreteFiniteSourceFiniteGeneralGrammarRecognizerCompilerConstruction :
    Prop :=
  FiniteSourceFiniteGeneralGrammarRecognizerCompilerConstruction

def ConcreteFiniteProductionListGrammarRecognizerCompilerConstruction : Prop :=
  FiniteProductionListGrammarRecognizerCompilerConstruction

def ConcreteFiniteBoolGeneralGrammarPresentationRecognizerCompilerConstruction :
    Prop :=
  FiniteBoolGeneralGrammarPresentationRecognizerCompilerConstruction

def ConcreteFiniteBoolGeneralGrammarPresentationBoundedRecognizerCompilerConstruction :
    Prop :=
  FiniteBoolGeneralGrammarPresentationBoundedRecognizerCompilerConstruction

def ConcreteFiniteBoolGeneralGrammarPresentationCertificateRecognizerCompilerConstruction :
    Prop :=
  FiniteBoolGeneralGrammarPresentationCertificateRecognizerCompilerConstruction

def ConcreteFiniteBoolGeneralGrammarPresentationIndexedCertificateRecognizerCompilerConstruction :
    Prop :=
  FiniteBoolGeneralGrammarPresentationIndexedCertificateRecognizerCompilerConstruction

def ConcreteFiniteBoolGeneralGrammarPresentationCheckedIndexedCertificateRecognizerCompilerConstruction :
    Prop :=
  FiniteBoolGeneralGrammarPresentationCheckedIndexedCertificateRecognizerCompilerConstruction

def ConcreteFiniteBooleanGeneralGrammarRecognizerCompilerConstruction : Prop :=
  ConcreteFiniteSourceFiniteGeneralGrammarRecognizerCompilerConstruction

def GeneralGrammarAcceptabilityEquivalence (L : Language terminal) : Prop :=
  Computability.GeneralGrammarAcceptabilityEquivalence L

def GeneralGrammarToRecursivelyEnumerableConstruction
    (terminal : Type u) : Prop :=
  GeneralGrammarToRecursivelyEnumerablePrinciple terminal

def RecursivelyEnumerableToGeneralGrammarConstruction
    (terminal : Type u) : Prop :=
  RecursivelyEnumerableToGeneralGrammarPrinciple terminal

def RecursivelyEnumerableToFiniteGeneralGrammarConstruction
    (terminal : Type u) : Prop :=
  RecursivelyEnumerableToFiniteGeneralGrammarPrinciple terminal

abbrev ConcreteBooleanSection52CompilerCloseout :=
  BooleanSection52CompilerCloseout

abbrev ConcreteBooleanFiniteGrammarSection52Closeout :=
  BooleanFiniteGrammarSection52Closeout

abbrev ConcreteBooleanFiniteDataSection52CompilerCloseout :=
  BooleanFiniteDataSection52CompilerCloseout

theorem concrete_finite_grammar_recognizer_compiler_of_general_compiler
    (hcompile : ConcreteBooleanGeneralGrammarRecognizerCompilerConstruction) :
    ConcreteFiniteBooleanGeneralGrammarRecognizerCompilerConstruction :=
  Computability.finiteBooleanGeneralGrammarRecognizerCompilerPrinciple_of_generalCompiler
    hcompile

theorem concrete_finite_production_list_grammar_recognizer_compiler_of_description_compiler
    (hcompile : ConcreteDescriptionAcceptorCompilationConstruction) :
    ConcreteFiniteProductionListGrammarRecognizerCompilerConstruction :=
  Computability.finiteProductionListGrammarRecognizerCompilerConstruction_of_descriptionCompiler
    hcompile

theorem concrete_finite_grammar_recognizer_compiler_of_production_list_compiler
    (hcompile :
      ConcreteFiniteProductionListGrammarRecognizerCompilerConstruction) :
    ConcreteFiniteBooleanGeneralGrammarRecognizerCompilerConstruction :=
  Computability.finiteBooleanGeneralGrammarRecognizerCompilerPrinciple_of_productionListCompiler
    hcompile

theorem concrete_finite_production_list_grammar_recognizer_compiler_of_finite_presentation_compiler
    (hcompile :
      ConcreteFiniteBoolGeneralGrammarPresentationRecognizerCompilerConstruction) :
    ConcreteFiniteProductionListGrammarRecognizerCompilerConstruction :=
  Computability.finiteProductionListGrammarRecognizerCompilerConstruction_of_finitePresentationCompiler
    hcompile

theorem concrete_finite_grammar_recognizer_compiler_of_finite_presentation_compiler
    (hcompile :
      ConcreteFiniteBoolGeneralGrammarPresentationRecognizerCompilerConstruction) :
    ConcreteFiniteBooleanGeneralGrammarRecognizerCompilerConstruction :=
  concrete_finite_grammar_recognizer_compiler_of_production_list_compiler
    (concrete_finite_production_list_grammar_recognizer_compiler_of_finite_presentation_compiler
      hcompile)

namespace ConcreteFiniteBoolGeneralGrammarPresentation

namespace RecognizerCompiler

theorem of_boundedRecognizerCompiler
    (hcompile :
      ConcreteFiniteBoolGeneralGrammarPresentationBoundedRecognizerCompilerConstruction) :
    ConcreteFiniteBoolGeneralGrammarPresentationRecognizerCompilerConstruction :=
  Computability.FiniteBoolGeneralGrammarPresentation.RecognizerCompilerConstruction.of_boundedRecognizerCompiler
    hcompile

end RecognizerCompiler

namespace BoundedRecognizerCompiler

theorem of_certificateRecognizerCompiler
    (hcompile :
      ConcreteFiniteBoolGeneralGrammarPresentationCertificateRecognizerCompilerConstruction) :
    ConcreteFiniteBoolGeneralGrammarPresentationBoundedRecognizerCompilerConstruction :=
  Computability.FiniteBoolGeneralGrammarPresentation.BoundedRecognizerCompilerConstruction.of_certificateRecognizerCompiler
    hcompile

theorem of_indexedCertificateRecognizerCompiler
    (hcompile :
      ConcreteFiniteBoolGeneralGrammarPresentationIndexedCertificateRecognizerCompilerConstruction) :
    ConcreteFiniteBoolGeneralGrammarPresentationBoundedRecognizerCompilerConstruction :=
  Computability.FiniteBoolGeneralGrammarPresentation.BoundedRecognizerCompilerConstruction.of_indexedCertificateRecognizerCompiler
    hcompile

theorem of_checkedIndexedCertificateRecognizerCompiler
    (hcompile :
      ConcreteFiniteBoolGeneralGrammarPresentationCheckedIndexedCertificateRecognizerCompilerConstruction) :
    ConcreteFiniteBoolGeneralGrammarPresentationBoundedRecognizerCompilerConstruction :=
  Computability.FiniteBoolGeneralGrammarPresentation.BoundedRecognizerCompilerConstruction.of_checkedIndexedCertificateRecognizerCompiler
    hcompile

end BoundedRecognizerCompiler

namespace IndexedCertificateRecognizerCompiler

theorem of_checkedIndexedCertificateRecognizerCompiler
    (hcompile :
      ConcreteFiniteBoolGeneralGrammarPresentationCheckedIndexedCertificateRecognizerCompilerConstruction) :
    ConcreteFiniteBoolGeneralGrammarPresentationIndexedCertificateRecognizerCompilerConstruction :=
  Computability.FiniteBoolGeneralGrammarPresentation.IndexedCertificateRecognizerCompilerConstruction.of_checkedIndexedCertificateRecognizerCompiler
    hcompile

end IndexedCertificateRecognizerCompiler

namespace RecognizerCompiler

theorem of_certificateRecognizerCompiler
    (hcompile :
      ConcreteFiniteBoolGeneralGrammarPresentationCertificateRecognizerCompilerConstruction) :
    ConcreteFiniteBoolGeneralGrammarPresentationRecognizerCompilerConstruction :=
  of_boundedRecognizerCompiler
    (BoundedRecognizerCompiler.of_certificateRecognizerCompiler
      hcompile)

theorem of_indexedCertificateRecognizerCompiler
    (hcompile :
      ConcreteFiniteBoolGeneralGrammarPresentationIndexedCertificateRecognizerCompilerConstruction) :
    ConcreteFiniteBoolGeneralGrammarPresentationRecognizerCompilerConstruction :=
  of_boundedRecognizerCompiler
    (BoundedRecognizerCompiler.of_indexedCertificateRecognizerCompiler
      hcompile)

theorem of_checkedIndexedCertificateRecognizerCompiler
    (hcompile :
      ConcreteFiniteBoolGeneralGrammarPresentationCheckedIndexedCertificateRecognizerCompilerConstruction) :
    ConcreteFiniteBoolGeneralGrammarPresentationRecognizerCompilerConstruction :=
  of_boundedRecognizerCompiler
    (BoundedRecognizerCompiler.of_checkedIndexedCertificateRecognizerCompiler
      hcompile)

end RecognizerCompiler

end ConcreteFiniteBoolGeneralGrammarPresentation

theorem concrete_finite_bool_general_grammar_presentation_has_finite_productions
    (P : ConcreteFiniteBoolGeneralGrammarPresentation) :
    GeneralGrammar.HasFiniteProductions P.toGrammar :=
  Computability.FiniteBoolGeneralGrammarPresentation.toGrammar_hasFiniteProductions
    P

theorem concrete_finite_bool_general_grammar_presentation_staged_recognizer_accepts
    (P : ConcreteFiniteBoolGeneralGrammarPresentation) :
    ProgramAcceptsLanguage
      (ConcreteFiniteBoolGeneralGrammarPresentationStagedRecognizer P)
      (ConcreteFiniteBoolGeneralGrammarPresentationGeneratedLanguage P) :=
  Computability.FiniteBoolGeneralGrammarPresentation.recognizerProgram_acceptsLanguage
    P

namespace ConcreteFiniteBoolGeneralGrammarPresentation

namespace RecognizerCompiler

theorem of_descriptionCompiler
    (hcompile : ConcreteDescriptionAcceptorCompilationConstruction) :
    ConcreteFiniteBoolGeneralGrammarPresentationRecognizerCompilerConstruction :=
  Computability.FiniteBoolGeneralGrammarPresentation.RecognizerCompilerConstruction.of_descriptionCompiler
    hcompile

end RecognizerCompiler

namespace CertificateRecognizerCompiler

theorem of_descriptionCompiler
    (hcompile : ConcreteDescriptionAcceptorCompilationConstruction) :
    ConcreteFiniteBoolGeneralGrammarPresentationCertificateRecognizerCompilerConstruction :=
  Computability.FiniteBoolGeneralGrammarPresentation.CertificateRecognizerCompilerConstruction.of_descriptionCompiler
    hcompile

end CertificateRecognizerCompiler

namespace IndexedCertificateRecognizerCompiler

theorem of_descriptionCompiler
    (hcompile : ConcreteDescriptionAcceptorCompilationConstruction) :
    ConcreteFiniteBoolGeneralGrammarPresentationIndexedCertificateRecognizerCompilerConstruction :=
  Computability.FiniteBoolGeneralGrammarPresentation.IndexedCertificateRecognizerCompilerConstruction.of_descriptionCompiler
    hcompile

end IndexedCertificateRecognizerCompiler

namespace CheckedIndexedCertificateRecognizerCompiler

theorem of_descriptionCompiler
    (hcompile : ConcreteDescriptionAcceptorCompilationConstruction) :
    ConcreteFiniteBoolGeneralGrammarPresentationCheckedIndexedCertificateRecognizerCompilerConstruction :=
  Computability.FiniteBoolGeneralGrammarPresentation.CheckedIndexedCertificateRecognizerCompilerConstruction.of_descriptionCompiler
    hcompile

theorem scaffold
    (hcompile :
      ConcreteFiniteBoolGeneralGrammarPresentationCheckedIndexedCertificateRecognizerCompilerConstruction) :
    ConcreteFiniteBoolGeneralGrammarPresentationCheckedIndexedCertificateRecognizerCompilerConstruction :=
  Computability.FiniteBoolGeneralGrammarPresentation.CheckedIndexedCertificateRecognizerCompilerConstruction.scaffold
    hcompile

end CheckedIndexedCertificateRecognizerCompiler

namespace BoundedRecognizerCompiler

theorem of_descriptionCompiler
    (hcompile : ConcreteDescriptionAcceptorCompilationConstruction) :
    ConcreteFiniteBoolGeneralGrammarPresentationBoundedRecognizerCompilerConstruction :=
  of_checkedIndexedCertificateRecognizerCompiler
    (CheckedIndexedCertificateRecognizerCompiler.of_descriptionCompiler
      hcompile)

end BoundedRecognizerCompiler

end ConcreteFiniteBoolGeneralGrammarPresentation

theorem concrete_general_grammar_recognizer_compiler_of_description_compiler
    (hcompile : ConcreteDescriptionAcceptorCompilationConstruction) :
    ConcreteBooleanGeneralGrammarRecognizerCompilerConstruction :=
  Computability.booleanGeneralGrammarRecognizerCompilerPrinciple_of_descriptionCompiler
    hcompile

theorem concrete_finite_grammar_recognizer_compiler_of_description_compiler
    (hcompile : ConcreteDescriptionAcceptorCompilationConstruction) :
    ConcreteFiniteBooleanGeneralGrammarRecognizerCompilerConstruction :=
  Computability.finiteBooleanGeneralGrammarRecognizerCompilerPrinciple_of_descriptionCompiler
    hcompile

theorem concrete_finite_bool_general_grammar_presentation_compiler_scaffold
    (hcompile :
      ConcreteFiniteBoolGeneralGrammarPresentationCheckedIndexedCertificateRecognizerCompilerConstruction) :
    ConcreteFiniteBoolGeneralGrammarPresentationRecognizerCompilerConstruction :=
  Computability.FiniteBoolGeneralGrammarPresentation.RecognizerCompilerConstruction.scaffold
    hcompile

theorem concrete_finite_section52_closeout_of_semantic_closeout
    (hclose : ConcreteBooleanSection52CompilerCloseout)
    (hpresentation :
      ConcreteFiniteBoolGeneralGrammarPresentationRecognizerCompilerConstruction)
    (hfinite :
      RecursivelyEnumerableToFiniteGeneralGrammarConstruction Bool) :
    ConcreteBooleanFiniteGrammarSection52Closeout where
  boundedTraceSearch := hclose.boundedTraceSearch
  decidableToAcceptable := hclose.decidableToAcceptable
  dovetailDescription := hclose.dovetailDescription
  finiteGrammarRecognizerDescription := hpresentation
  recursivelyEnumerableToFiniteGrammar := hfinite

theorem recursively_enumerable_to_finite_general_grammar_construction_of_description_compiler
    (hcompile : ConcreteDescriptionAcceptorCompilationConstruction) :
    RecursivelyEnumerableToFiniteGeneralGrammarConstruction Bool :=
  Computability.recursivelyEnumerableToFiniteGeneralGrammarPrinciple_bool_of_descriptionCompiler
    hcompile

theorem concrete_finite_section52_closeout_of_semantic_closeout_and_description_compiler
    (hclose : ConcreteBooleanSection52CompilerCloseout)
    (hcompile : ConcreteDescriptionAcceptorCompilationConstruction) :
    ConcreteBooleanFiniteGrammarSection52Closeout :=
  concrete_finite_section52_closeout_of_semantic_closeout hclose
    (ConcreteFiniteBoolGeneralGrammarPresentation.RecognizerCompiler.of_descriptionCompiler
      hcompile)
    (recursively_enumerable_to_finite_general_grammar_construction_of_description_compiler
      hcompile)

theorem concrete_finite_data_section52_closeout_of_semantic_closeout
    (hclose : ConcreteBooleanSection52CompilerCloseout)
    (hpresentation :
      ConcreteFiniteBoolGeneralGrammarPresentationRecognizerCompilerConstruction) :
    ConcreteBooleanFiniteDataSection52CompilerCloseout where
  boundedTraceSearch := hclose.boundedTraceSearch
  decidableToAcceptable := hclose.decidableToAcceptable
  pairedDovetailDescription :=
    paired_recognizer_dovetail_compiler_of_concrete_dovetail_description_compiler
      hclose.dovetailDescription
  finiteGrammarRecognizerDescription := hpresentation
  descriptionRecognizerToFiniteGrammar :=
    Computability.machineDescriptionAcceptsToFiniteGeneralGrammarConstruction_of_machineConstruction
      concrete_machine_description_to_finite_general_grammar_construction

theorem concrete_finite_data_section52_closeout_of_semantic_closeout_and_description_compilers
    (hclose : ConcreteBooleanSection52CompilerCloseout)
    (haccept : ConcreteDescriptionAcceptorCompilationConstruction)
    (hbool : ConcreteDescriptionBoolDeciderCompilationConstruction) :
    ConcreteBooleanFiniteDataSection52CompilerCloseout where
  boundedTraceSearch := hclose.boundedTraceSearch
  decidableToAcceptable := hclose.decidableToAcceptable
  pairedDovetailDescription :=
    paired_recognizer_dovetail_compiler_of_concrete_bool_description_compiler
      hbool
  finiteGrammarRecognizerDescription :=
    ConcreteFiniteBoolGeneralGrammarPresentation.RecognizerCompiler.of_descriptionCompiler
      haccept
  descriptionRecognizerToFiniteGrammar :=
    Computability.machineDescriptionAcceptsToFiniteGeneralGrammarConstruction_of_machineConstruction
      concrete_machine_description_to_finite_general_grammar_construction

def GeneralGrammarREEquivalenceConstruction
    (terminal : Type u) : Prop :=
  GeneralGrammarREEquivalencePrinciple terminal

def FiniteGeneralGrammarREEquivalenceConstruction
    (terminal : Type u) : Prop :=
  FiniteGeneralGrammarREEquivalencePrinciple terminal

def FiniteGeneralGrammarGenerated (L : Language terminal) : Prop :=
  GeneralGrammar.FiniteProductionGenerated L

def FiniteGeneralGrammarToRecursivelyEnumerableConstruction
    (terminal : Type u) : Prop :=
  forall L : Language terminal,
    FiniteGeneralGrammarGenerated L -> RecursivelyEnumerableLanguage L

def GeneralGrammarPairGenerated (L : Language terminal) : Prop :=
  GeneralGrammar.Generated L ∧ GeneralGrammar.Generated (Language.Compl L)

def FiniteGeneralGrammarPairGenerated (L : Language terminal) : Prop :=
  FiniteGeneralGrammarGenerated L ∧
    FiniteGeneralGrammarGenerated (Language.Compl L)

def ConcreteFiniteGeneralGrammarRecognizerPresentsLanguage
    {nonterminal : Type}
    (G : GeneralGrammar Bool nonterminal)
    (L : Language Bool) : Prop :=
  GeneralGrammar.HasFiniteProductions G ∧
    Language.Equal (GeneralGrammarGeneratedLanguage G) L ∧
      exists D : MachineDescription,
        ConcreteProgramCompiledByDescription
          (GeneralGrammarStagedRecognizer G) D

def ConcreteFiniteGeneralGrammarRecognizerLanguage
    (L : Language Bool) : Prop :=
  exists nonterminal : Type,
    exists G : GeneralGrammar Bool nonterminal,
      ConcreteFiniteGeneralGrammarRecognizerPresentsLanguage G L

/-!
**Finite grammar recognizer presentations.**  A finite unrestricted grammar
together with a supplied description for its derivation-search recognizer is
already enough to obtain recursive enumerability of the generated language.
The harder compiler theorem is the uniform construction of that description
from the finite production list.
-/

/-!
For unrestricted grammars, a finite derivation is a finite acceptance trace.
The first theorems in this block build that trace-level recognizer before any
machine compiler is assumed.
-/

theorem general_grammar_derivation_trace_accepts_generated_language
    (G : GeneralGrammar terminal nonterminal) :
    LanguageAcceptanceTrace
      (GeneralGrammarDerivationTraceLanguage G)
      (GeneralGrammarGeneratedLanguage G) :=
  Computability.generalGrammar_derivationTrace_acceptance G

theorem finite_production_list_trace_iff_general_derivation_trace
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs)
    {w : Word terminal} {n : Nat} :
    GeneralGrammarFiniteProductionListTraceLanguage G rules w n <->
      GeneralGrammarDerivationTraceLanguage G w n :=
  Computability.finiteProductionListDerivationTrace_iff_derivationTrace
    hrules

theorem finite_production_list_trace_accepts_generated_language
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs) :
    LanguageAcceptanceTrace
      (GeneralGrammarFiniteProductionListTraceLanguage G rules)
      (GeneralGrammarGeneratedLanguage G) :=
  Computability.finiteProductionListDerivationTrace_acceptance hrules

theorem general_grammar_bounded_derivation_search_sound
    {G : GeneralGrammar terminal nonterminal}
    {w : Word terminal} {limit : Nat}
    (hit : GeneralGrammarBoundedDerivationSearchLanguage G w limit) :
    w ∈ GeneralGrammarGeneratedLanguage G :=
  Computability.generalGrammarBoundedDerivationSearch_sound hit

theorem general_grammar_bounded_derivation_search_complete
    {G : GeneralGrammar terminal nonterminal}
    {w : Word terminal}
    (hw : w ∈ GeneralGrammarGeneratedLanguage G) :
    exists limit : Nat,
      GeneralGrammarBoundedDerivationSearchLanguage G w limit :=
  Computability.generalGrammarBoundedDerivationSearch_complete hw

theorem finite_production_list_bounded_derivation_search_sound
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs)
    {w : Word terminal} {limit : Nat}
    (hit :
      GeneralGrammarFiniteProductionListBoundedSearchLanguage
        G rules w limit) :
    w ∈ GeneralGrammarGeneratedLanguage G :=
  Computability.finiteProductionListBoundedDerivationSearch_sound
    hrules hit

theorem finite_production_list_bounded_derivation_search_complete
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs)
    {w : Word terminal}
    (hw : w ∈ GeneralGrammarGeneratedLanguage G) :
    exists limit : Nat,
      GeneralGrammarFiniteProductionListBoundedSearchLanguage
        G rules w limit :=
  Computability.finiteProductionListBoundedDerivationSearch_complete
    hrules hw

theorem general_grammar_staged_recognizer_accepts_generated_language
    (G : GeneralGrammar terminal nonterminal) :
    ProgramAcceptsLanguage
      (GeneralGrammarStagedRecognizer G)
      (GeneralGrammarGeneratedLanguage G) :=
  Computability.generalGrammarRecognizerProgram_acceptsLanguage G

theorem finite_production_list_staged_recognizer_accepts_generated_language
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs) :
    ProgramAcceptsLanguage
      (GeneralGrammarFiniteProductionListStagedRecognizer G rules)
      (GeneralGrammarGeneratedLanguage G) :=
  Computability.finiteProductionListRecognizerProgram_acceptsLanguage
    hrules

theorem general_grammar_bounded_staged_recognizer_accepts_generated_language
    (G : GeneralGrammar terminal nonterminal) :
    ProgramAcceptsLanguage
      (GeneralGrammarBoundedStagedRecognizer G)
      (GeneralGrammarGeneratedLanguage G) :=
  Computability.generalGrammarBoundedRecognizerProgram_acceptsLanguage G

theorem finite_production_list_bounded_staged_recognizer_accepts_generated_language
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs) :
    ProgramAcceptsLanguage
      (GeneralGrammarFiniteProductionListBoundedStagedRecognizer G rules)
      (GeneralGrammarGeneratedLanguage G) :=
  Computability.finiteProductionListBoundedRecognizerProgram_acceptsLanguage
    hrules

theorem finite_production_list_certificate_staged_recognizer_accepts_generated_language
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs) :
    ProgramAcceptsLanguage
      (GeneralGrammarFiniteProductionListCertificateStagedRecognizer G rules)
      (GeneralGrammarGeneratedLanguage G) :=
  Computability.finiteProductionListCertificateRecognizerProgram_acceptsLanguage
    hrules

theorem finite_production_list_indexed_certificate_staged_recognizer_accepts_generated_language
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs) :
    ProgramAcceptsLanguage
      (GeneralGrammarFiniteProductionListIndexedCertificateStagedRecognizer
        G rules)
      (GeneralGrammarGeneratedLanguage G) :=
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
      (GeneralGrammarFiniteProductionListCheckedIndexedCertificateStagedRecognizer
        G rules)
      (GeneralGrammarGeneratedLanguage G) :=
  Computability.finiteProductionListCheckedIndexedCertificateRecognizerProgram_acceptsLanguage
    hrules

theorem finite_production_list_certificate_staged_recognizer_same_language_as_bounded
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs) :
    forall w : Word terminal,
      ProgramHaltsWithOutput
          (GeneralGrammarFiniteProductionListCertificateStagedRecognizer
            G rules) w [] <->
        ProgramHaltsWithOutput
          (GeneralGrammarFiniteProductionListBoundedStagedRecognizer
            G rules) w [] :=
  Computability.finiteProductionListCertificateRecognizerProgram_same_language
    hrules

theorem finite_production_list_indexed_certificate_staged_recognizer_same_language_as_bounded
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs) :
    forall w : Word terminal,
      ProgramHaltsWithOutput
          (GeneralGrammarFiniteProductionListIndexedCertificateStagedRecognizer
            G rules) w [] <->
        ProgramHaltsWithOutput
          (GeneralGrammarFiniteProductionListBoundedStagedRecognizer
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
          (GeneralGrammarFiniteProductionListCheckedIndexedCertificateStagedRecognizer
            G rules) w [] <->
        ProgramHaltsWithOutput
          (GeneralGrammarFiniteProductionListBoundedStagedRecognizer
            G rules) w [] :=
  Computability.finiteProductionListCheckedIndexedCertificateRecognizerProgram_same_language
    hrules

theorem acceptance_trace_simulation_grammar_derivesIn_one_of_trace
    {trace : Word terminal -> Nat -> Prop}
    {w : Word terminal} {n : Nat}
    (h : trace w n) :
    GeneralGrammar.DerivesIn
      (AcceptanceTraceSimulationGrammar trace) 1
      [Symbol.nonterminal ()]
      (SententialForm.terminalWord w) :=
  Computability.traceSimulationGrammar_derivesIn_one_of_trace h

theorem acceptance_trace_simulation_grammar_generated
    {trace : Word terminal -> Nat -> Prop}
    {L : Language terminal}
    (htrace : LanguageAcceptanceTrace trace L) :
    Language.Equal
      (GeneralGrammarGeneratedLanguage
        (AcceptanceTraceSimulationGrammar trace)) L :=
  Computability.traceSimulationGrammar_generated_of_acceptanceTrace htrace

theorem acceptance_trace_generated_by_simulation_grammar
    {trace : Word terminal -> Nat -> Prop}
    {L : Language terminal}
    (htrace : LanguageAcceptanceTrace trace L) :
    GeneralGrammar.Generated L :=
  Computability.acceptanceTrace_generated_by_traceSimulationGrammar htrace

theorem machine_configuration_trace_simulation_grammar_derivesIn_one_of_haltsIn
    {D : MachineDescription} {w : Word Bool} {n : Nat}
    (h : D.HaltsIn n w) :
    GeneralGrammar.DerivesIn
      (MachineConfigurationTraceSimulationGrammar D) 1
      [Symbol.nonterminal ()]
      (SententialForm.terminalWord w) :=
  Computability.machineHaltingTraceSimulationGrammar_derivesIn_one_of_haltsIn h

theorem machine_configuration_trace_simulation_grammar_generated
    (D : MachineDescription) :
    Language.Equal
      (GeneralGrammarGeneratedLanguage
        (MachineConfigurationTraceSimulationGrammar D))
      (fun w => D.HaltsOnInput w) :=
  Computability.machineHaltingTraceSimulationGrammar_generated D

theorem concrete_machine_description_accepts_generated_by_configuration_trace_grammar
    {D : MachineDescription} {L : Language Bool}
    (h : ConcreteMachineDescriptionAccepts D L) :
    Language.Equal
      (GeneralGrammarGeneratedLanguage
        (MachineConfigurationTraceSimulationGrammar D)) L :=
  Computability.machineDescription_accepts_generated_by_traceSimulationGrammar h

theorem concrete_machine_history_grammar_has_finite_productions
    (D : MachineDescription) :
    GeneralGrammar.HasFiniteProductions
      (ConcreteMachineHistoryGrammar D) :=
  Computability.MachineDescriptionHistoryGrammar.hasFiniteProductions D

theorem concrete_machine_history_grammar_complete
    {D : MachineDescription} {w : Word Bool}
    (h : D.HaltsOnInput w) :
    w ∈ GeneralGrammarGeneratedLanguage
      (ConcreteMachineHistoryGrammar D) :=
  Computability.MachineDescriptionHistoryGrammar.complete h

theorem concrete_machine_history_grammar_sound
    {D : MachineDescription} (hD : D.WellFormed) {w : Word Bool}
    (h : w ∈ GeneralGrammarGeneratedLanguage
      (ConcreteMachineHistoryGrammar D)) :
    D.HaltsOnInput w :=
  Computability.MachineDescriptionHistoryGrammar.sound hD h

theorem concrete_machine_history_grammar_generated
    {D : MachineDescription} (hD : D.WellFormed) :
    Language.Equal
      (GeneralGrammarGeneratedLanguage
        (ConcreteMachineHistoryGrammar D))
      (fun w : Word Bool => D.HaltsOnInput w) :=
  Computability.MachineDescriptionHistoryGrammar.generated_language hD

/-!
**Finite trace tables.**  A finite table of accepting traces gives a genuine
finite-production grammar: the production list contains one rule from the start
nonterminal to each table word. This is the finite-data bridge used to state the
description-backed recognizer-to-finite-grammar interface precisely.
-/

def ConcreteFiniteAcceptanceTraceTableProductions
    (T : ConcreteFiniteAcceptanceTraceTable terminal) :
    List (GeneralGrammar.Production terminal Unit) :=
  T.productions

theorem concrete_finite_acceptance_trace_table_has_finite_productions
    (T : ConcreteFiniteAcceptanceTraceTable terminal) :
    GeneralGrammar.HasFiniteProductions
      (ConcreteFiniteAcceptanceTraceTableGrammar T) :=
  Computability.FiniteAcceptanceTraceTable.hasFiniteProductions T

theorem concrete_finite_acceptance_trace_table_generated_language
    (T : ConcreteFiniteAcceptanceTraceTable terminal) :
    Language.Equal
      (GeneralGrammarGeneratedLanguage
        (ConcreteFiniteAcceptanceTraceTableGrammar T))
      (ConcreteFiniteAcceptanceTraceTableLanguage T) :=
  Computability.FiniteAcceptanceTraceTable.generated_language T

theorem concrete_finite_acceptance_trace_table_finite_production_generated
    (T : ConcreteFiniteAcceptanceTraceTable terminal) :
    FiniteGeneralGrammarGenerated
      (ConcreteFiniteAcceptanceTraceTableLanguage T) :=
  Computability.FiniteAcceptanceTraceTable.finiteProductionGenerated_language T

theorem concrete_finite_trace_table_recognizable_finite_production_generated
    {L : Language terminal}
    (h : ConcreteFiniteTraceTableRecognizable L) :
    FiniteGeneralGrammarGenerated L :=
  Computability.finiteTraceTableRecognizable_finiteProductionGenerated h

theorem concrete_finite_trace_table_to_finite_general_grammar_construction
    (terminal : Type u) :
    ConcreteFiniteTraceTableToFiniteGeneralGrammarConstruction terminal :=
  Computability.finiteTraceTableToFiniteGeneralGrammarConstruction terminal

theorem concrete_machine_finite_acceptance_trace_table_generated
    {D : MachineDescription}
    {T : ConcreteMachineFiniteAcceptanceTraceTable D}
    (hT : ConcreteMachineFiniteAcceptanceTraceTablePresents D T) :
    Language.Equal
      (GeneralGrammarGeneratedLanguage
        (ConcreteFiniteAcceptanceTraceTableGrammar T))
      (fun w : Word Bool => D.HaltsOnInput w) :=
  Computability.machineFiniteAcceptanceTraceTable_generated hT

theorem concrete_machine_finite_acceptance_trace_table_finite_production_generated
    {D : MachineDescription}
    {T : ConcreteMachineFiniteAcceptanceTraceTable D}
    (hT : ConcreteMachineFiniteAcceptanceTraceTablePresents D T) :
    FiniteGeneralGrammarGenerated
      (fun w : Word Bool => D.HaltsOnInput w) :=
  Computability.machineFiniteAcceptanceTraceTable_finiteProductionGenerated hT

theorem concrete_machine_description_accepts_to_finite_general_grammar :
    ConcreteMachineDescriptionAcceptsToFiniteGeneralGrammarConstruction :=
  Computability.machineDescriptionAcceptsToFiniteGeneralGrammarConstruction_of_machineConstruction
    concrete_machine_description_to_finite_general_grammar_construction

theorem finite_general_grammar_has_finite_list_staged_recognizer
    {G : GeneralGrammar terminal nonterminal}
    (hfinite : GeneralGrammar.HasFiniteProductions G) :
    exists rules : List (GeneralGrammar.Production terminal nonterminal),
      ProgramAcceptsLanguage
        (GeneralGrammarFiniteProductionListStagedRecognizer G rules)
        (GeneralGrammarGeneratedLanguage G) :=
  Computability.finiteProductionListRecognizerProgram_acceptsLanguage_of_hasFiniteProductions
    hfinite

theorem general_grammar_generated_language_is_program_acceptable
    (G : GeneralGrammar terminal nonterminal) :
    ProgramAcceptableLanguage (GeneralGrammarGeneratedLanguage G) :=
  Computability.generalGrammar_generatedLanguage_programAcceptable G

theorem boolean_general_grammar_generated_language_is_recursively_enumerable_of_concrete_description
    (G : GeneralGrammar Bool nonterminal)
    {D : MachineDescription}
    (hcompile : ConcreteProgramCompiledByDescription
      (GeneralGrammarStagedRecognizer G) D) :
    RecursivelyEnumerableLanguage (GeneralGrammarGeneratedLanguage G) :=
  concrete_program_acceptable_by_description_turing_acceptable
    (by
      exists GeneralGrammarStagedRecognizer G
      exists D
      exact And.intro
        (general_grammar_staged_recognizer_accepts_generated_language G)
        hcompile)

theorem boolean_general_grammar_generated_is_recursively_enumerable_of_concrete_description
    {L : Language Bool}
    (G : GeneralGrammar Bool nonterminal)
    {D : MachineDescription}
    (hcompile : ConcreteProgramCompiledByDescription
      (GeneralGrammarStagedRecognizer G) D)
    (hEq : Language.Equal (GeneralGrammarGeneratedLanguage G) L) :
    RecursivelyEnumerableLanguage L :=
  recursively_enumerable_language_of_equal
    (boolean_general_grammar_generated_language_is_recursively_enumerable_of_concrete_description
      G hcompile)
    hEq

theorem concrete_finite_general_grammar_recognizer_presentation_recursively_enumerable
    {nonterminal : Type}
    (G : GeneralGrammar Bool nonterminal)
    {L : Language Bool}
    (h : ConcreteFiniteGeneralGrammarRecognizerPresentsLanguage G L) :
    RecursivelyEnumerableLanguage L := by
  cases h.right.right with
  | intro D hD =>
      exact
        boolean_general_grammar_generated_is_recursively_enumerable_of_concrete_description
          G hD h.right.left

theorem concrete_finite_general_grammar_recognizer_language_recursively_enumerable
    {L : Language Bool}
    (h : ConcreteFiniteGeneralGrammarRecognizerLanguage L) :
    RecursivelyEnumerableLanguage L := by
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
    (hcompile : ConcreteBooleanGeneralGrammarRecognizerCompilerConstruction)
    (G : GeneralGrammar Bool nonterminal) :
    RecursivelyEnumerableLanguage (GeneralGrammarGeneratedLanguage G) := by
  cases hcompile (nonterminal := nonterminal) G with
  | intro D hD =>
      exact
        boolean_general_grammar_generated_language_is_recursively_enumerable_of_concrete_description
          G hD

theorem boolean_general_grammar_generated_is_recursively_enumerable_of_concrete_grammar_compiler
    {nonterminal : Type}
    (hcompile : ConcreteBooleanGeneralGrammarRecognizerCompilerConstruction)
    {L : Language Bool}
    (G : GeneralGrammar Bool nonterminal)
    (hEq : Language.Equal (GeneralGrammarGeneratedLanguage G) L) :
    RecursivelyEnumerableLanguage L :=
  recursively_enumerable_language_of_equal
    (boolean_general_grammar_generated_language_is_recursively_enumerable_of_concrete_grammar_compiler
      hcompile G)
    hEq

theorem boolean_general_grammar_to_recursively_enumerable_construction_of_concrete_grammar_compiler
    (hcompile : ConcreteBooleanGeneralGrammarRecognizerCompilerConstruction) :
    GeneralGrammarToRecursivelyEnumerableConstruction Bool := by
  intro L hgenerated
  cases hgenerated with
  | intro nonterminal hnonterminal =>
      cases hnonterminal with
      | intro G hEq =>
          exact
            boolean_general_grammar_generated_is_recursively_enumerable_of_concrete_grammar_compiler
              hcompile (nonterminal := nonterminal) G hEq

theorem boolean_finite_general_grammar_generated_is_recursively_enumerable_of_concrete_grammar_compiler
    (hcompile : ConcreteBooleanGeneralGrammarRecognizerCompilerConstruction)
    {L : Language Bool}
    (h : FiniteGeneralGrammarGenerated L) :
    RecursivelyEnumerableLanguage L := by
  cases h with
  | intro nonterminal hnonterminal =>
      cases hnonterminal with
      | intro G hG =>
          exact
            boolean_general_grammar_generated_is_recursively_enumerable_of_concrete_grammar_compiler
              hcompile (nonterminal := nonterminal) G hG.right

namespace BooleanFiniteGeneralGrammar

theorem generated_re_of_concreteFiniteGrammarCompiler
    (hcompile : ConcreteFiniteBooleanGeneralGrammarRecognizerCompilerConstruction)
    {L : Language Bool}
    (h : FiniteGeneralGrammarGenerated L) :
    RecursivelyEnumerableLanguage L := by
  cases h with
  | intro nonterminal hnonterminal =>
      cases hnonterminal with
      | intro G hG =>
          cases hcompile (nonterminal := nonterminal) G hG.left with
          | intro D hD =>
              exact
                boolean_general_grammar_generated_is_recursively_enumerable_of_concrete_description
                  G hD hG.right

end BooleanFiniteGeneralGrammar

theorem concrete_finite_general_grammar_recognizer_presentation_of_finite_compiler
    (hcompile : ConcreteFiniteBooleanGeneralGrammarRecognizerCompilerConstruction)
    {nonterminal : Type}
    (G : GeneralGrammar Bool nonterminal)
    (hfinite : GeneralGrammar.HasFiniteProductions G) :
    ConcreteFiniteGeneralGrammarRecognizerPresentsLanguage
      G (GeneralGrammarGeneratedLanguage G) := by
  cases hcompile G hfinite with
  | intro D hD =>
      constructor
      · exact hfinite
      · constructor
        · intro w
          rfl
        · exists D

theorem concrete_finite_general_grammar_recognizer_language_of_finite_compiler
    (hcompile : ConcreteFiniteBooleanGeneralGrammarRecognizerCompilerConstruction)
    {nonterminal : Type}
    (G : GeneralGrammar Bool nonterminal)
    (hfinite : GeneralGrammar.HasFiniteProductions G) :
    ConcreteFiniteGeneralGrammarRecognizerLanguage
      (GeneralGrammarGeneratedLanguage G) := by
  exists nonterminal
  exists G
  exact
    concrete_finite_general_grammar_recognizer_presentation_of_finite_compiler
      hcompile G hfinite

theorem boolean_finite_general_grammar_to_recursively_enumerable_construction_of_concrete_grammar_compiler
    (hcompile : ConcreteBooleanGeneralGrammarRecognizerCompilerConstruction) :
    FiniteGeneralGrammarToRecursivelyEnumerableConstruction Bool := by
  intro L hgenerated
  exact
    boolean_finite_general_grammar_generated_is_recursively_enumerable_of_concrete_grammar_compiler
      hcompile hgenerated

namespace BooleanFiniteGeneralGrammar

theorem to_re_construction_of_concreteFiniteGrammarCompiler
    (hcompile : ConcreteFiniteBooleanGeneralGrammarRecognizerCompilerConstruction) :
    FiniteGeneralGrammarToRecursivelyEnumerableConstruction Bool := by
  intro L hgenerated
  exact
    generated_re_of_concreteFiniteGrammarCompiler
      hcompile hgenerated

end BooleanFiniteGeneralGrammar

theorem finite_general_grammar_generated_language_is_program_acceptable
    {L : Language terminal}
    (h : FiniteGeneralGrammarGenerated L) :
    ProgramAcceptableLanguage L :=
  Computability.finiteProductionGenerated_programAcceptable h

theorem general_grammar_generated_language_is_recursively_enumerable_of_staged_program_compiler
    (hcompile : StagedAcceptorCompilationConstruction terminal)
    (G : GeneralGrammar terminal nonterminal) :
    RecursivelyEnumerableLanguage (GeneralGrammarGeneratedLanguage G) :=
  Computability.generalGrammar_generatedLanguage_recursivelyEnumerable_of_programCompiler
    hcompile G

theorem general_grammar_generated_is_recursively_enumerable_of_staged_program_compiler
    (hcompile : StagedAcceptorCompilationConstruction terminal)
    {L : Language terminal}
    (h : GeneralGrammar.Generated L) :
    RecursivelyEnumerableLanguage L :=
  Computability.generalGrammar_generated_recursivelyEnumerable_of_programCompiler
    hcompile h

theorem general_grammar_to_recursively_enumerable_construction_of_staged_program_compiler
    (hcompile : StagedAcceptorCompilationConstruction terminal) :
    GeneralGrammarToRecursivelyEnumerableConstruction terminal := by
  intro L hgenerated
  exact
    general_grammar_generated_is_recursively_enumerable_of_staged_program_compiler
      hcompile hgenerated

theorem finite_general_grammar_generated_language_is_recursively_enumerable_of_staged_program_compiler
    (hcompile : StagedAcceptorCompilationConstruction terminal)
    {L : Language terminal}
    (h : FiniteGeneralGrammarGenerated L) :
    RecursivelyEnumerableLanguage L :=
  Computability.finiteProductionGenerated_recursivelyEnumerable_of_programCompiler
    hcompile h

theorem finite_general_grammar_to_recursively_enumerable_construction_of_staged_program_compiler
    (hcompile : StagedAcceptorCompilationConstruction terminal) :
    FiniteGeneralGrammarToRecursivelyEnumerableConstruction terminal := by
  intro L hgenerated
  exact
    finite_general_grammar_generated_language_is_recursively_enumerable_of_staged_program_compiler
      hcompile hgenerated

theorem recursively_enumerable_to_general_grammar_construction_semantic :
    RecursivelyEnumerableToGeneralGrammarConstruction terminal :=
  Computability.recursivelyEnumerableToGeneralGrammarPrinciple_semantic
    terminal

theorem general_grammar_acceptability_equivalence_of_constructions
    (hto : GeneralGrammarToRecursivelyEnumerableConstruction terminal)
    (hfrom : RecursivelyEnumerableToGeneralGrammarConstruction terminal)
    (L : Language terminal) :
    GeneralGrammarAcceptabilityEquivalence L := by
  constructor
  · exact hto L
  · exact hfrom L

theorem general_grammar_re_equivalence_construction_of_constructions
    (hto : GeneralGrammarToRecursivelyEnumerableConstruction terminal)
    (hfrom : RecursivelyEnumerableToGeneralGrammarConstruction terminal) :
    GeneralGrammarREEquivalenceConstruction terminal := by
  intro L
  exact general_grammar_acceptability_equivalence_of_constructions
    hto hfrom L

theorem general_grammar_re_equivalence_construction_of_to_construction
    (hto : GeneralGrammarToRecursivelyEnumerableConstruction terminal) :
    GeneralGrammarREEquivalenceConstruction terminal :=
  general_grammar_re_equivalence_construction_of_constructions
    hto recursively_enumerable_to_general_grammar_construction_semantic

theorem finite_general_grammar_acceptability_equivalence_of_constructions
    (hto : FiniteGeneralGrammarToRecursivelyEnumerableConstruction terminal)
    (hfrom : RecursivelyEnumerableToFiniteGeneralGrammarConstruction terminal)
    (L : Language terminal) :
    FiniteGeneralGrammarGenerated L <-> RecursivelyEnumerableLanguage L := by
  constructor
  · exact hto L
  · exact hfrom L

theorem finite_general_grammar_re_equivalence_construction_of_constructions
    (hto : FiniteGeneralGrammarToRecursivelyEnumerableConstruction terminal)
    (hfrom : RecursivelyEnumerableToFiniteGeneralGrammarConstruction terminal) :
    FiniteGeneralGrammarREEquivalenceConstruction terminal := by
  intro L
  exact finite_general_grammar_acceptability_equivalence_of_constructions
    hto hfrom L


end Section02
end Chapter05
end Book
end FoC
