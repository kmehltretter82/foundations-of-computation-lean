import FoC.Computability.Compiler
import FoC.Computability.FiniteProgram
import FoC.Computability.Grammar

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter05
namespace Section02

/-!
# Chapter 5, Section 5.2: Computability

This section connects recursive, recursively enumerable, acceptable, and
listable languages. It also records the statement shape for the theorem that
finite general grammars generate exactly the recursively enumerable languages.
The reusable modules are {module}`FoC.Computability.Enumerable`,
{module}`FoC.Computability.Program`, {module}`FoC.Computability.Compiler`,
{module}`FoC.Computability.FiniteProgram`,
{module}`FoC.Computability.Grammar`, and
{module}`FoC.Grammars.GeneralGrammar`.

The guiding distinction is total decision versus semi-decision. Recursive
languages have deciders. Recursively enumerable languages have recognizers or
listings: members eventually appear, but nonmembers may never be ruled out.
-/

open Languages
open Computability
open Grammars

universe u v

/-!
## Recursive and Recursively Enumerable Languages

The definitions name the main language classes and the construction principles
used by the book's proofs: decidable-to-acceptable conversion and dovetailing
paired recognizers for a language and its complement.

The construction principles are kept as explicit hypotheses where the reusable
library avoids assuming a concrete universal machine. This lets the page state
the textbook theorem shapes without smuggling in unproved implementation
details.
-/

def RecursivelyEnumerableLanguage (L : Language alpha) : Prop :=
  RecursivelyEnumerable L

def CoRecursivelyEnumerableLanguage (L : Language alpha) : Prop :=
  CoRecursivelyEnumerable L

def RecursivelyEnumerableLanguageWithComplement (L : Language alpha) : Prop :=
  RecursivelyEnumerableWithComplement L

def RecursiveLanguage (L : Language alpha) : Prop :=
  Recursive L

def StoppedTuringDecidableLanguage (L : Language alpha) : Prop :=
  StoppedTuringDecidable L

def DecidableToAcceptableConstruction (alpha : Type u) : Prop :=
  DecidableToAcceptablePrinciple alpha

def DovetailingDecidableConstruction (alpha : Type u) : Prop :=
  ReCoReToDecidablePrinciple alpha

def RecursiveIffReCoREConstruction (alpha : Type u) : Prop :=
  RecursiveIffReCoRePrinciple alpha

def StagedAcceptorCompilationConstruction (alpha : Type u) : Prop :=
  ProgramAcceptorCompilationPrinciple alpha

def StagedBoolDeciderCompilationConstruction (alpha : Type u) : Prop :=
  ProgramBoolDeciderCompilationPrinciple alpha

def ConcreteDescriptionAcceptorCompilationConstruction : Prop :=
  DescriptionProgramAcceptorCompilationPrinciple

def ConcreteDescriptionBoolDeciderCompilationConstruction : Prop :=
  DescriptionProgramBoolDeciderCompilationPrinciple

def ConcreteDovetailDescriptionCompilerConstruction : Prop :=
  DovetailDescriptionCompilerPrinciple

def ConcretePartialUnaryRangeDescriptionCompilerConstruction : Prop :=
  PartialUnaryRangeDescriptionCompilerPrinciple

def PartialFunctionDomainLanguage
    (f : Word input -> Option (Word output)) : Language input :=
  PartialFunctionDomain f

def LanguageAcceptanceTrace
    (trace : Word alpha -> Nat -> Prop)
    (L : Language alpha) : Prop :=
  AcceptanceTrace trace L

def LanguageComplementaryAcceptanceTraces
    (accept reject : Word alpha -> Nat -> Prop)
    (L : Language alpha) : Prop :=
  ComplementaryAcceptanceTraces accept reject L

def LanguageTraceHitsBy
    (trace : Word alpha -> Nat -> Prop)
    (w : Word alpha) (limit : Nat) : Prop :=
  TraceHitsBy trace w limit

def LanguageDovetailSearchHit
    (accept reject : Word alpha -> Nat -> Prop)
    (w : Word alpha) (limit : Nat) : Prop :=
  ComplementaryTraceSearchHit accept reject w limit

noncomputable def TraceDovetailProgram
    (accept reject : Word alpha -> Nat -> Prop) :
    StagedProgram alpha Bool :=
  Computability.DovetailProgram accept reject

def ProgramBoolDecidesLanguage
    (P : StagedProgram alpha Bool) (L : Language alpha) : Prop :=
  ProgramBoolDecides P L

def ProgramBoolDecidableLanguage (L : Language alpha) : Prop :=
  ProgramBoolDecidable L

def ProgramAcceptableLanguage (L : Language alpha) : Prop :=
  ProgramAcceptable L

def ConcreteMachineDescriptionAccepts
    (D : MachineDescription) (L : Language Bool) : Prop :=
  MachineDescriptionAcceptsLanguage D L

def ConcreteMachineDescriptionDecides
    (D : MachineDescription) (L : Language Bool) : Prop :=
  MachineDescriptionDecidesLanguage D L

def ConcreteProgramCompiledByDescription
    (P : StagedProgram Bool Unit) (D : MachineDescription) : Prop :=
  ProgramCompiledByDescription P D

def ConcreteBoolProgramCompiledByDescription
    (P : StagedProgram Bool Bool) (D : MachineDescription) : Prop :=
  BoolProgramCompiledByDescription P D

def ConcreteProgramAcceptableByDescription
    (L : Language Bool) : Prop :=
  ProgramAcceptableByDescription L

def ConcreteProgramBoolDecidableByDescription
    (L : Language Bool) : Prop :=
  ProgramBoolDecidableByDescription L

def ConcreteFiniteAcceptorProgram : Type :=
  FiniteAcceptorProgram

def ConcreteFiniteBoolProgram : Type :=
  FiniteBoolProgram

def ConcreteFiniteDovetailProgram : Type :=
  FiniteDovetailProgram

def ConcreteFinitePartialUnaryRangeProgram : Type :=
  FinitePartialUnaryRangeProgram

def ConcreteFiniteAcceptorTrace
    (P : ConcreteFiniteAcceptorProgram)
    (w : Word Bool) (n : Nat) : Prop :=
  P.trace w n

def ConcreteFiniteAcceptorDescription
    (P : ConcreteFiniteAcceptorProgram) : MachineDescription :=
  P.compile

def ConcreteFiniteBoolDescription
    (P : ConcreteFiniteBoolProgram) : MachineDescription :=
  P.compile

def ConcreteFiniteDovetailDescription
    (P : ConcreteFiniteDovetailProgram) : MachineDescription :=
  P.decider.compile

def ConcreteFiniteAcceptorStagedProgram
    (P : ConcreteFiniteAcceptorProgram) :
    StagedProgram Bool Unit :=
  P.toStagedProgram

def ConcreteFiniteBoolStagedProgram
    (P : ConcreteFiniteBoolProgram) :
    StagedProgram Bool Bool :=
  P.toStagedProgram

noncomputable def ConcreteFiniteDovetailStagedProgram
    (P : ConcreteFiniteDovetailProgram) :
    StagedProgram Bool Bool :=
  P.toStagedProgram

def ConcreteFiniteDovetailCompiled
    (P : ConcreteFiniteDovetailProgram) : Prop :=
  P.Compiled

def ConcreteFinitePartialUnaryRangeStagedProgram
    (P : ConcreteFinitePartialUnaryRangeProgram) :
    StagedProgram Unit Bool :=
  P.toStagedProgram

def ConcreteFinitePartialUnaryOutputRange
    (P : ConcreteFinitePartialUnaryRangeProgram) :
    Language Bool :=
  P.outputRange

def ConcreteFinitePartialUnaryDescriptionOutputRange
    (P : ConcreteFinitePartialUnaryRangeProgram) :
    Language Bool :=
  P.descriptionOutputRange

def LanguageProgramAcceptanceTrace
    (P : StagedProgram alpha Unit)
    (w : Word alpha) (n : Nat) : Prop :=
  ProgramAcceptanceTrace P w n

noncomputable def AcceptanceTraceStagedRecognizer
    (trace : Word alpha -> Nat -> Prop) :
    StagedProgram alpha Unit :=
  TraceRecognizerProgram trace

/-!
## Complements and Extensionality

Recursive languages are closed under complement, stopped deciders can be
swapped to decide complements, and both recursive and recursively enumerable
properties are invariant under language equality.

The contrast with recursively enumerable languages is important: complement
closure is immediate for deciders, but not for recognizers unless a recognizer
for the complement is also available.
-/

theorem recursive_language_complement {L : Language alpha}
    (h : RecursiveLanguage L) : RecursiveLanguage (Language.Compl L) :=
  Computability.recursive_complement h

theorem recursive_language_of_recursive_complement {L : Language alpha}
    (h : RecursiveLanguage (Language.Compl L)) : RecursiveLanguage L :=
  Computability.recursive_of_complement h

theorem recursive_language_complement_iff {L : Language alpha} :
    RecursiveLanguage (Language.Compl L) <-> RecursiveLanguage L :=
  Computability.recursive_complement_iff

theorem stopped_turing_decidable_language_is_recursive
    {L : Language alpha}
    (h : StoppedTuringDecidableLanguage L) :
    RecursiveLanguage L :=
  Computability.stoppedTuringDecidable_to_turingDecidable h

theorem stopped_turing_decidable_language_complement
    {L : Language alpha}
    (h : StoppedTuringDecidableLanguage L) :
    StoppedTuringDecidableLanguage (Language.Compl L) :=
  Computability.stoppedTuringDecidable_complement h

theorem recursive_language_of_equal {L K : Language alpha}
    (h : RecursiveLanguage L) (hEq : Language.Equal L K) :
    RecursiveLanguage K :=
  Computability.recursive_of_equal h hEq

theorem recursively_enumerable_language_of_equal {L K : Language alpha}
    (h : RecursivelyEnumerableLanguage L) (hEq : Language.Equal L K) :
    RecursivelyEnumerableLanguage K :=
  Computability.recursivelyEnumerable_of_equal h hEq

/-!
## Traces and Dovetailing

Acceptance traces represent finite-stage evidence for RE languages. With
complementary traces, bounded dovetailing eventually classifies each input and
gives the formal core of the RE/co-RE-to-recursive theorem.

A trace is a time-indexed witness that some recognizer has accepted by a
bounded stage. Dovetailing searches both the language trace and complement
trace in increasing bounds until one side hits.
-/

theorem partial_computable_function_domain_is_recursively_enumerable
    {f : Word input -> Option (Word output)}
    (h : TuringComputablePartial f) :
    RecursivelyEnumerableLanguage (PartialFunctionDomainLanguage f) :=
  Computability.turingComputablePartial_domain_recursivelyEnumerable h

theorem recursively_enumerable_language_has_acceptance_trace
    {L : Language alpha}
    (h : RecursivelyEnumerableLanguage L) :
    exists trace : Word alpha -> Nat -> Prop,
      LanguageAcceptanceTrace trace L :=
  Computability.recursivelyEnumerable_has_acceptanceTrace h

theorem program_accepts_language_has_acceptance_trace
    {P : StagedProgram alpha Unit} {L : Language alpha}
    (h : ProgramAcceptsLanguage P L) :
    LanguageAcceptanceTrace (LanguageProgramAcceptanceTrace P) L :=
  Computability.programAcceptsLanguage_acceptanceTrace h

theorem program_acceptable_language_has_acceptance_trace
    {L : Language alpha}
    (h : ProgramAcceptableLanguage L) :
    exists trace : Word alpha -> Nat -> Prop,
      LanguageAcceptanceTrace trace L :=
  Computability.programAcceptable_has_acceptanceTrace h

theorem acceptance_trace_staged_recognizer_accepts_language
    {trace : Word alpha -> Nat -> Prop} {L : Language alpha}
    (h : LanguageAcceptanceTrace trace L) :
    ProgramAcceptsLanguage
      (AcceptanceTraceStagedRecognizer trace) L :=
  Computability.traceRecognizerProgram_acceptsLanguage h

theorem acceptance_trace_has_program_acceptable_language
    {trace : Word alpha -> Nat -> Prop} {L : Language alpha}
    (h : LanguageAcceptanceTrace trace L) :
    ProgramAcceptableLanguage L :=
  Computability.acceptanceTrace_programAcceptable h

theorem program_acceptable_language_iff_has_acceptance_trace
    (L : Language alpha) :
    ProgramAcceptableLanguage L <->
      exists trace : Word alpha -> Nat -> Prop,
        LanguageAcceptanceTrace trace L :=
  Computability.programAcceptable_iff_has_acceptanceTrace L

theorem recursively_enumerable_language_is_program_acceptable
    {L : Language alpha}
    (h : RecursivelyEnumerableLanguage L) :
    ProgramAcceptableLanguage L := by
  cases recursively_enumerable_language_has_acceptance_trace h with
  | intro trace htrace =>
      exact acceptance_trace_has_program_acceptable_language htrace

theorem re_and_co_re_have_complementary_acceptance_traces
    {L : Language alpha}
    (h : RecursivelyEnumerableLanguageWithComplement L) :
    exists accept reject : Word alpha -> Nat -> Prop,
      LanguageComplementaryAcceptanceTraces accept reject L :=
  Computability.recursivelyEnumerable_with_complement_has_complementaryTraces h

theorem complementary_trace_accept_sound
    {accept reject : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (h : LanguageComplementaryAcceptanceTraces accept reject L)
    {w : Word alpha} {n : Nat}
    (hn : accept w n) :
    w ∈ L :=
  Computability.complementaryAcceptanceTraces_accept_sound h hn

theorem complementary_trace_reject_sound
    {accept reject : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (h : LanguageComplementaryAcceptanceTraces accept reject L)
    {w : Word alpha} {n : Nat}
    (hn : reject w n) :
    ¬ w ∈ L :=
  Computability.complementaryAcceptanceTraces_reject_sound h hn

theorem complementary_traces_eventually_hit
    {accept reject : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (h : LanguageComplementaryAcceptanceTraces accept reject L)
    (w : Word alpha) :
    exists n : Nat, accept w n ∨ reject w n :=
  Computability.complementaryAcceptanceTraces_eventually_hits_classical h w

theorem language_trace_hit_mono
    {trace : Word alpha -> Nat -> Prop}
    {w : Word alpha} {m n : Nat}
    (hmn : m ≤ n)
    (h : LanguageTraceHitsBy trace w m) :
    LanguageTraceHitsBy trace w n :=
  Computability.traceHitsBy_mono hmn h

theorem complementary_trace_accepts_by_sound
    {accept reject : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (h : LanguageComplementaryAcceptanceTraces accept reject L)
    {w : Word alpha} {limit : Nat}
    (hit : LanguageTraceHitsBy accept w limit) :
    w ∈ L :=
  Computability.complementaryTraceAcceptsBy_sound h hit

theorem complementary_trace_rejects_by_sound
    {accept reject : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (h : LanguageComplementaryAcceptanceTraces accept reject L)
    {w : Word alpha} {limit : Nat}
    (hit : LanguageTraceHitsBy reject w limit) :
    ¬ w ∈ L :=
  Computability.complementaryTraceRejectsBy_sound h hit

theorem complementary_trace_search_no_conflict
    {accept reject : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (h : LanguageComplementaryAcceptanceTraces accept reject L)
    {w : Word alpha} {acceptLimit rejectLimit : Nat}
    (ha : LanguageTraceHitsBy accept w acceptLimit)
    (hr : LanguageTraceHitsBy reject w rejectLimit) :
    False :=
  Computability.complementaryTraceSearch_no_conflict h ha hr

theorem complementary_trace_search_eventually_hits_by
    {accept reject : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (h : LanguageComplementaryAcceptanceTraces accept reject L)
    (w : Word alpha) :
    exists limit : Nat, LanguageDovetailSearchHit accept reject w limit :=
  Computability.complementaryTraceSearch_eventually_hits_by h w

theorem complementary_trace_search_eventually_classifies
    {accept reject : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (h : LanguageComplementaryAcceptanceTraces accept reject L)
    (w : Word alpha) :
    exists limit : Nat,
      (LanguageTraceHitsBy accept w limit ∧ w ∈ L) ∨
        (LanguageTraceHitsBy reject w limit ∧ ¬ w ∈ L) :=
  Computability.complementaryTraceSearch_eventually_classifies h w

theorem re_and_co_re_bounded_search_eventually_classifies
    {L : Language alpha}
    (h : RecursivelyEnumerableLanguageWithComplement L)
    (w : Word alpha) :
    exists accept reject : Word alpha -> Nat -> Prop,
      LanguageComplementaryAcceptanceTraces accept reject L ∧
        exists limit : Nat,
          (LanguageTraceHitsBy accept w limit ∧ w ∈ L) ∨
            (LanguageTraceHitsBy reject w limit ∧ ¬ w ∈ L) := by
  cases re_and_co_re_have_complementary_acceptance_traces h with
  | intro accept haccept =>
      cases haccept with
      | intro reject hreject =>
          exists accept
          exists reject
          constructor
          · exact hreject
          · exact complementary_trace_search_eventually_classifies hreject w

theorem complementary_traces_dovetailing_program_decides
    {accept reject : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (h : LanguageComplementaryAcceptanceTraces accept reject L) :
    ProgramBoolDecidesLanguage
      (TraceDovetailProgram accept reject) L :=
  Computability.dovetailProgram_decides h

theorem re_and_co_re_have_dovetailing_program
    {L : Language alpha}
    (h : RecursivelyEnumerableLanguageWithComplement L) :
    exists accept reject : Word alpha -> Nat -> Prop,
      LanguageComplementaryAcceptanceTraces accept reject L ∧
        ProgramBoolDecidesLanguage
          (TraceDovetailProgram accept reject) L :=
  Computability.reCoRe_has_dovetailProgram h

theorem re_and_co_re_have_program_bool_decider
    {L : Language alpha}
    (h : RecursivelyEnumerableLanguageWithComplement L) :
    ProgramBoolDecidableLanguage L :=
  Computability.reCoRe_programBoolDecidable h

theorem dovetailing_decidable_construction_of_staged_program_compiler
    (hcompile : StagedBoolDeciderCompilationConstruction alpha) :
    DovetailingDecidableConstruction alpha :=
  Computability.reCoReToDecidablePrinciple_of_programBoolCompiler hcompile

theorem staged_acceptor_compilation_construction_of_concrete_descriptions
    (hcompile : ConcreteDescriptionAcceptorCompilationConstruction) :
    StagedAcceptorCompilationConstruction Bool :=
  Computability.programAcceptorCompilationPrinciple_of_descriptionCompiler
    hcompile

theorem staged_bool_decider_compilation_construction_of_concrete_descriptions
    (hcompile : ConcreteDescriptionBoolDeciderCompilationConstruction) :
    StagedBoolDeciderCompilationConstruction Bool :=
  Computability.programBoolDeciderCompilationPrinciple_of_descriptionCompiler
    hcompile

theorem dovetailing_decidable_construction_of_concrete_description_compiler
    (hcompile : ConcreteDescriptionBoolDeciderCompilationConstruction) :
    DovetailingDecidableConstruction Bool :=
  dovetailing_decidable_construction_of_staged_program_compiler
    (staged_bool_decider_compilation_construction_of_concrete_descriptions
      hcompile)

theorem dovetailing_decidable_construction_of_concrete_dovetail_description_compiler
    (hcompile : ConcreteDovetailDescriptionCompilerConstruction) :
    DovetailingDecidableConstruction Bool :=
  Computability.reCoReToDecidablePrinciple_of_dovetailDescriptionCompiler
    hcompile

theorem complementary_traces_recursive_language_of_concrete_dovetail_description_compiler
    (hcompile : ConcreteDovetailDescriptionCompilerConstruction)
    {L : Language Bool}
    {accept reject : Word Bool -> Nat -> Prop}
    (htraces : LanguageComplementaryAcceptanceTraces accept reject L) :
    RecursiveLanguage L :=
  Computability.complementaryTraces_turingDecidable_of_dovetailDescriptionCompiler
    hcompile htraces

theorem re_and_co_re_recursive_language_of_concrete_dovetail_description_compiler
    (hcompile : ConcreteDovetailDescriptionCompilerConstruction)
    {L : Language Bool}
    (h : RecursivelyEnumerableLanguageWithComplement L) :
    RecursiveLanguage L :=
  Computability.reCoRe_turingDecidable_of_dovetailDescriptionCompiler
    hcompile h

theorem recursive_language_iff_re_and_co_re_of_concrete_dovetail_description_compiler
    (haccept : DecidableToAcceptableConstruction Bool)
    (hcompile : ConcreteDovetailDescriptionCompilerConstruction)
    (L : Language Bool) :
    RecursiveLanguage L <-> RecursivelyEnumerableLanguageWithComplement L :=
  Computability.recursive_iff_reCoRe_of_principles
    haccept
    (Computability.reCoReToDecidablePrinciple_of_dovetailDescriptionCompiler
      hcompile)
    L

theorem concrete_machine_description_accepts_turing_acceptable
    {D : MachineDescription} {L : Language Bool}
    (h : ConcreteMachineDescriptionAccepts D L) :
    RecursivelyEnumerableLanguage L :=
  Computability.machineDescriptionAcceptsLanguage_turingAcceptable h

theorem concrete_machine_description_decides_turing_decidable
    {D : MachineDescription} {L : Language Bool}
    (h : ConcreteMachineDescriptionDecides D L) :
    RecursiveLanguage L :=
  Computability.machineDescriptionDecidesLanguage_turingDecidable h

theorem concrete_program_acceptable_by_description_turing_acceptable
    {L : Language Bool}
    (h : ConcreteProgramAcceptableByDescription L) :
    RecursivelyEnumerableLanguage L :=
  Computability.programAcceptableByDescription_turingAcceptable h

theorem concrete_program_bool_decidable_by_description_turing_decidable
    {L : Language Bool}
    (h : ConcreteProgramBoolDecidableByDescription L) :
    RecursiveLanguage L :=
  Computability.programBoolDecidableByDescription_turingDecidable h

theorem concrete_finite_acceptor_compiled_by_description
    (P : ConcreteFiniteAcceptorProgram)
    (hD : P.description.WellFormed) :
    ConcreteProgramCompiledByDescription
      (ConcreteFiniteAcceptorStagedProgram P)
      (ConcreteFiniteAcceptorDescription P) :=
  Computability.FiniteAcceptorProgram.compiledByDescription P hD

theorem concrete_finite_acceptor_program_acceptable_by_description
    (P : ConcreteFiniteAcceptorProgram)
    (hD : P.description.WellFormed)
    {L : Language Bool}
    (haccepts :
      ProgramAcceptsLanguage
        (ConcreteFiniteAcceptorStagedProgram P) L) :
    ConcreteProgramAcceptableByDescription L := by
  exists ConcreteFiniteAcceptorStagedProgram P
  exists ConcreteFiniteAcceptorDescription P
  exact And.intro haccepts
    (concrete_finite_acceptor_compiled_by_description P hD)

theorem concrete_finite_acceptor_recursively_enumerable
    (P : ConcreteFiniteAcceptorProgram)
    (hD : P.description.WellFormed)
    {L : Language Bool}
    (haccepts :
      ProgramAcceptsLanguage
        (ConcreteFiniteAcceptorStagedProgram P) L) :
    RecursivelyEnumerableLanguage L :=
  concrete_program_acceptable_by_description_turing_acceptable
    (concrete_finite_acceptor_program_acceptable_by_description
      P hD haccepts)

theorem concrete_finite_trace_recognizer_compiled_by_description
    (P : ConcreteFiniteAcceptorProgram)
    (hD : P.description.WellFormed) :
    ConcreteProgramCompiledByDescription
      (AcceptanceTraceStagedRecognizer
        (ConcreteFiniteAcceptorTrace P))
      (ConcreteFiniteAcceptorDescription P) := by
  simpa [AcceptanceTraceStagedRecognizer,
    ConcreteFiniteAcceptorTrace, ConcreteFiniteAcceptorDescription]
    using
      Computability.FiniteAcceptorProgram.traceRecognizer_compiledByDescription
        P hD

theorem concrete_finite_trace_recognizer_acceptable_by_description
    (P : ConcreteFiniteAcceptorProgram)
    (hD : P.description.WellFormed)
    {L : Language Bool}
    (htrace : LanguageAcceptanceTrace
      (ConcreteFiniteAcceptorTrace P) L) :
    ConcreteProgramAcceptableByDescription L :=
  Computability.FiniteAcceptorProgram.traceRecognizer_programAcceptableByDescription
    P hD htrace

theorem concrete_finite_trace_recognizer_recursively_enumerable
    (P : ConcreteFiniteAcceptorProgram)
    (hD : P.description.WellFormed)
    {L : Language Bool}
    (htrace : LanguageAcceptanceTrace
      (ConcreteFiniteAcceptorTrace P) L) :
    RecursivelyEnumerableLanguage L :=
  Computability.FiniteAcceptorProgram.traceRecognizer_turingAcceptable
    P hD htrace

theorem concrete_finite_bool_program_compiled_by_description
    (P : ConcreteFiniteBoolProgram)
    (hD : P.description.WellFormed) :
    ConcreteBoolProgramCompiledByDescription
      (ConcreteFiniteBoolStagedProgram P)
      (ConcreteFiniteBoolDescription P) :=
  Computability.FiniteBoolProgram.compiledByDescription P hD

theorem concrete_finite_bool_program_bool_decidable_by_description
    (P : ConcreteFiniteBoolProgram)
    (hD : P.description.WellFormed)
    {L : Language Bool}
    (hdecides :
      ProgramBoolDecidesLanguage
        (ConcreteFiniteBoolStagedProgram P) L) :
    ConcreteProgramBoolDecidableByDescription L :=
  Computability.FiniteBoolProgram.programBoolDecidableByDescription
    P hD hdecides

theorem concrete_finite_bool_program_turing_decidable
    (P : ConcreteFiniteBoolProgram)
    (hD : P.description.WellFormed)
    {L : Language Bool}
    (hdecides :
      ProgramBoolDecidesLanguage
        (ConcreteFiniteBoolStagedProgram P) L) :
    RecursiveLanguage L :=
  Computability.FiniteBoolProgram.turingDecidable P hD hdecides

theorem concrete_finite_dovetail_program_bool_decidable_by_description
    (P : ConcreteFiniteDovetailProgram)
    {L : Language Bool}
    (htraces : LanguageComplementaryAcceptanceTraces
      (ConcreteFiniteAcceptorTrace P.accept)
      (ConcreteFiniteAcceptorTrace P.reject) L)
    (hcompiled : ConcreteFiniteDovetailCompiled P) :
    ConcreteProgramBoolDecidableByDescription L := by
  simpa [ConcreteFiniteDovetailCompiled, ConcreteFiniteAcceptorTrace]
    using
      Computability.FiniteDovetailProgram.programBoolDecidableByDescription
        P htraces hcompiled

theorem concrete_finite_dovetail_program_turing_decidable
    (P : ConcreteFiniteDovetailProgram)
    {L : Language Bool}
    (htraces : LanguageComplementaryAcceptanceTraces
      (ConcreteFiniteAcceptorTrace P.accept)
      (ConcreteFiniteAcceptorTrace P.reject) L)
    (hcompiled : ConcreteFiniteDovetailCompiled P) :
    RecursiveLanguage L := by
  simpa [ConcreteFiniteDovetailCompiled, ConcreteFiniteAcceptorTrace]
    using Computability.FiniteDovetailProgram.turingDecidable
      P htraces hcompiled

theorem stopped_decider_has_complementary_output_traces
    {M : TuringMachine symbol state}
    {encodeInput : alpha -> symbol} {zero one : symbol}
    {L : Language alpha}
    (hstop : TuringMachine.HaltingTransitionsDisabled M)
    (hzeroOne : zero ≠ one)
    (h : DecidesLanguage M encodeInput zero one L) :
    LanguageComplementaryAcceptanceTraces
      (fun w n =>
        TuringMachine.HaltsWithOutputIn
          M n (EncodeWord encodeInput w) [one])
      (fun w n =>
        TuringMachine.HaltsWithOutputIn
          M n (EncodeWord encodeInput w) [zero])
      L :=
  Computability.stopped_decider_has_complementary_output_traces
    hstop hzeroOne h

theorem stopped_decider_acceptance_trace
    {M : TuringMachine symbol state}
    {encodeInput : alpha -> symbol} {zero one : symbol}
    {L : Language alpha}
    (hstop : TuringMachine.HaltingTransitionsDisabled M)
    (hzeroOne : zero ≠ one)
    (h : DecidesLanguage M encodeInput zero one L) :
    LanguageAcceptanceTrace
      (fun w n =>
        TuringMachine.HaltsWithOutputIn
          M n (EncodeWord encodeInput w) [one])
      L :=
  Computability.stopped_decider_acceptanceTrace hstop hzeroOne h

theorem stopped_decider_complement_acceptance_trace
    {M : TuringMachine symbol state}
    {encodeInput : alpha -> symbol} {zero one : symbol}
    {L : Language alpha}
    (hstop : TuringMachine.HaltingTransitionsDisabled M)
    (hzeroOne : zero ≠ one)
    (h : DecidesLanguage M encodeInput zero one L) :
    LanguageAcceptanceTrace
      (fun w n =>
        TuringMachine.HaltsWithOutputIn
          M n (EncodeWord encodeInput w) [zero])
      (Language.Compl L) :=
  Computability.stopped_decider_complement_acceptanceTrace
    hstop hzeroOne h

theorem stopped_decider_bounded_search_eventually_classifies
    {M : TuringMachine symbol state}
    {encodeInput : alpha -> symbol} {zero one : symbol}
    {L : Language alpha}
    (hstop : TuringMachine.HaltingTransitionsDisabled M)
    (hzeroOne : zero ≠ one)
    (h : DecidesLanguage M encodeInput zero one L)
    (w : Word alpha) :
    exists limit : Nat,
      (LanguageTraceHitsBy
        (fun x n =>
          TuringMachine.HaltsWithOutputIn
            M n (EncodeWord encodeInput x) [one])
        w limit ∧ w ∈ L) ∨
        (LanguageTraceHitsBy
          (fun x n =>
            TuringMachine.HaltsWithOutputIn
              M n (EncodeWord encodeInput x) [zero])
          w limit ∧ ¬ w ∈ L) :=
  complementary_trace_search_eventually_classifies
    (stopped_decider_has_complementary_output_traces hstop hzeroOne h) w

theorem stopped_turing_decidable_language_has_complementary_output_traces
    {L : Language alpha}
    (h : StoppedTuringDecidableLanguage L) :
    exists accept reject : Word alpha -> Nat -> Prop,
      LanguageComplementaryAcceptanceTraces accept reject L :=
  Computability.stoppedTuringDecidable_has_complementary_output_traces h

theorem stopped_turing_decidable_language_has_acceptance_trace
    {L : Language alpha}
    (h : StoppedTuringDecidableLanguage L) :
    exists trace : Word alpha -> Nat -> Prop,
      LanguageAcceptanceTrace trace L :=
  Computability.stoppedTuringDecidable_has_acceptanceTrace h

theorem stopped_turing_decidable_language_complement_has_acceptance_trace
    {L : Language alpha}
    (h : StoppedTuringDecidableLanguage L) :
    exists trace : Word alpha -> Nat -> Prop,
      LanguageAcceptanceTrace trace (Language.Compl L) :=
  Computability.stoppedTuringDecidable_complement_has_acceptanceTrace h

theorem stopped_turing_decidable_language_bounded_search_eventually_classifies
    {L : Language alpha}
    (h : StoppedTuringDecidableLanguage L)
    (w : Word alpha) :
    exists accept reject : Word alpha -> Nat -> Prop,
      LanguageComplementaryAcceptanceTraces accept reject L ∧
        exists limit : Nat,
          (LanguageTraceHitsBy accept w limit ∧ w ∈ L) ∨
            (LanguageTraceHitsBy reject w limit ∧ ¬ w ∈ L) :=
  Computability.stoppedTuringDecidable_bounded_search_eventually_classifies h w

theorem recursive_language_re_and_co_re_of_decidable_to_acceptable
    (haccept : DecidableToAcceptableConstruction alpha)
    {L : Language alpha}
    (h : RecursiveLanguage L) :
    RecursivelyEnumerableLanguageWithComplement L :=
  Computability.recursive_reCoRe_of_decidableToAcceptable haccept h

theorem recursive_language_iff_re_and_co_re_of_constructions
    (haccept : DecidableToAcceptableConstruction alpha)
    (hdovetail : DovetailingDecidableConstruction alpha)
    (L : Language alpha) :
    RecursiveLanguage L <-> RecursivelyEnumerableLanguageWithComplement L :=
  Computability.recursive_iff_reCoRe_of_principles haccept hdovetail L

theorem recursive_iff_re_co_re_construction_of_principles
    (haccept : DecidableToAcceptableConstruction alpha)
    (hdovetail : DovetailingDecidableConstruction alpha) :
    RecursiveIffReCoREConstruction alpha :=
  Computability.recursiveIffReCoRePrinciple_of_principles
    haccept hdovetail

/-!
## Listings and Ranges

Listable languages are represented by streams of words. The range theorems
connect listability with unary string functions, matching the book's
enumerator viewpoint.

The list may repeat words and does not have to decide absence. What matters is
eventual appearance: every member of the language occurs somewhere in the
stream.
-/

def LanguageListedBy (stream : Nat -> Word alpha) (L : Language alpha) : Prop :=
  ListedBy stream L

def LanguagePartiallyListedBy
    (stream : Nat -> Option (Word alpha)) (L : Language alpha) : Prop :=
  PartiallyListedBy stream L

theorem listed_language_of_equal {stream : Nat -> Word alpha}
    {L K : Language alpha}
    (h : LanguageListedBy stream L) (hEq : Language.Equal L K) :
    LanguageListedBy stream K :=
  listedBy_of_equal h hEq

theorem partially_listed_language_of_equal
    {stream : Nat -> Option (Word alpha)} {L K : Language alpha}
    (h : LanguagePartiallyListedBy stream L) (hEq : Language.Equal L K) :
    LanguagePartiallyListedBy stream K :=
  partiallyListedBy_of_equal h hEq

theorem listed_word_in_language {stream : Nat -> Word alpha} {L : Language alpha}
    (h : LanguageListedBy stream L) (n : Nat) :
    stream n ∈ L :=
  listed_word_mem h n

theorem partially_listed_word_in_language
    {stream : Nat -> Option (Word alpha)} {L : Language alpha}
    (h : LanguagePartiallyListedBy stream L)
    {n : Nat} {w : Word alpha}
    (hn : stream n = some w) :
    w ∈ L :=
  partially_listed_word_mem h hn

def LanguageListable (L : Language alpha) : Prop :=
  Listable L

def LanguagePartiallyListable (L : Language alpha) : Prop :=
  PartiallyListable L

def UnaryInputString (n : Nat) : Word Unit :=
  UnaryInputWord n

theorem listable_language_of_equal {L K : Language alpha}
    (h : LanguageListable L) (hEq : Language.Equal L K) :
    LanguageListable K :=
  listable_of_equal h hEq

theorem partially_listable_language_of_equal {L K : Language alpha}
    (h : LanguagePartiallyListable L) (hEq : Language.Equal L K) :
    LanguagePartiallyListable K :=
  partiallyListable_of_equal h hEq

theorem empty_language_is_partially_listable :
    LanguagePartiallyListable (Language.Empty : Language alpha) :=
  Computability.empty_partiallyListable

def FunctionRangeLanguage (f : Word input -> Word output) : Language output :=
  RangeLanguage f

def PartialFunctionRangeLanguage
    (f : Word input -> Option (Word output)) : Language output :=
  PartialRangeLanguage f

def RangeOfUnaryStringFunction (L : Language output) : Prop :=
  RangeOfUnaryFunction L

def PartialRangeOfUnaryStringFunction (L : Language output) : Prop :=
  PartialRangeOfUnaryFunction L

def ListingAsUnaryStringFunction (stream : Nat -> Word output) :
    Word Unit -> Word output :=
  ListingAsUnaryFunction stream

def PartialListingAsUnaryStringFunction
    (stream : Nat -> Option (Word output)) :
    Word Unit -> Option (Word output) :=
  PartialListingAsUnaryFunction stream

theorem unary_input_string_length (n : Nat) :
    Word.Length (UnaryInputString n) = n :=
  Computability.unaryInputWord_length n

theorem unary_function_range_is_listed
    (f : Word Unit -> Word output) :
    LanguageListedBy
      (fun n => f (UnaryInputString n))
      (FunctionRangeLanguage f) :=
  Computability.unaryFunctionRange_listedBy f

theorem unary_function_range_is_listable
    (f : Word Unit -> Word output) :
    LanguageListable (FunctionRangeLanguage f) :=
  Computability.unaryFunctionRange_listable f

theorem partial_unary_function_range_is_partially_listed
    (f : Word Unit -> Option (Word output)) :
    LanguagePartiallyListedBy
      (fun n => f (UnaryInputString n))
      (PartialFunctionRangeLanguage f) :=
  Computability.partialUnaryFunctionRange_partiallyListedBy f

theorem partial_unary_function_range_is_partially_listable
    (f : Word Unit -> Option (Word output)) :
    LanguagePartiallyListable (PartialFunctionRangeLanguage f) :=
  Computability.partialUnaryFunctionRange_partiallyListable f

theorem listed_language_range_of_unary_function
    {stream : Nat -> Word output} {L : Language output}
    (h : LanguageListedBy stream L) :
    Language.Equal
      (FunctionRangeLanguage (ListingAsUnaryStringFunction stream)) L :=
  Computability.listedBy_rangeLanguage_listingAsUnaryFunction h

theorem partially_listed_language_range_of_partial_unary_function
    {stream : Nat -> Option (Word output)} {L : Language output}
    (h : LanguagePartiallyListedBy stream L) :
    Language.Equal
      (PartialFunctionRangeLanguage
        (PartialListingAsUnaryStringFunction stream)) L :=
  Computability.partiallyListedBy_partialRangeLanguage_partialListingAsUnaryFunction
    h

theorem listable_language_has_unary_range_function
    {L : Language output}
    (h : LanguageListable L) :
    exists f : Word Unit -> Word output,
      Language.Equal (FunctionRangeLanguage f) L :=
  Computability.listable_has_unary_range_function h

theorem partially_listable_language_has_partial_unary_range_function
    {L : Language output}
    (h : LanguagePartiallyListable L) :
    exists f : Word Unit -> Option (Word output),
      Language.Equal (PartialFunctionRangeLanguage f) L :=
  Computability.partiallyListable_has_partial_unary_range_function h

theorem listable_language_range_of_unary_string_function
    {L : Language output}
    (h : LanguageListable L) :
    RangeOfUnaryStringFunction L :=
  Computability.listable_rangeOfUnaryFunction h

theorem partially_listable_language_range_of_partial_unary_string_function
    {L : Language output}
    (h : LanguagePartiallyListable L) :
    PartialRangeOfUnaryStringFunction L :=
  Computability.partiallyListable_partialRangeOfUnaryFunction h

theorem unary_string_function_range_is_listable
    {L : Language output}
    (h : RangeOfUnaryStringFunction L) :
    LanguageListable L :=
  Computability.rangeOfUnaryFunction_listable h

theorem partial_unary_string_function_range_is_partially_listable
    {L : Language output}
    (h : PartialRangeOfUnaryStringFunction L) :
    LanguagePartiallyListable L :=
  Computability.partialRangeOfUnaryFunction_partiallyListable h

theorem listable_language_iff_range_of_unary_string_function
    (L : Language output) :
    LanguageListable L <-> RangeOfUnaryStringFunction L :=
  Computability.listable_iff_rangeOfUnaryFunction L

theorem partially_listable_language_iff_partial_range_of_unary_string_function
    (L : Language output) :
    LanguagePartiallyListable L <-> PartialRangeOfUnaryStringFunction L :=
  Computability.partiallyListable_iff_partialRangeOfUnaryFunction L

def LanguageListingProgram (output : Type u) : Type u :=
  ListingProgram output

def LanguageListingProgramLists
    (stream : LanguageListingProgram output) (L : Language output) : Prop :=
  ListingProgramLists stream L

def LanguagePartialUnaryRangeProgram (output : Type u) : Type u :=
  PartialUnaryRangeProgram output

def LanguagePartialUnaryRangeProgramGenerates
    (f : LanguagePartialUnaryRangeProgram output)
    (L : Language output) : Prop :=
  PartialUnaryRangeProgramGenerates f L

def LanguagePartialFunctionProgram
    (f : Word input -> Option (Word output)) :
    StagedProgram input output :=
  PartialFunctionProgram f

def ConcretePartialFunctionCompiledByDescription
    (f : Word input -> Option (Word Bool))
    (encodeInput : input -> Bool)
    (D : MachineDescription) : Prop :=
  PartialFunctionCompiledByDescription f encodeInput D

def LanguageProgramRange (P : StagedProgram input output) :
    Language output :=
  ProgramRangeLanguage P

def LanguagePartialUnaryFunctionProgramRange
    (L : Language output) : Prop :=
  PartialUnaryFunctionProgramRange L

def ConcretePartialUnaryTuringComputableRange
    (L : Language Bool) : Prop :=
  PartialUnaryTuringComputableRange L

def ConcreteCompiledPartialUnaryRange
    (L : Language Bool) : Prop :=
  CompiledPartialUnaryRange L

def ConcreteCompiledPartialUnaryFunctionProgramRange
    (L : Language Bool) : Prop :=
  CompiledPartialUnaryFunctionProgramRange L

theorem listing_program_iff_partially_listable_language
    (L : Language output) :
    (exists stream : LanguageListingProgram output,
      LanguageListingProgramLists stream L) <->
        LanguagePartiallyListable L :=
  Computability.listingProgram_iff_partiallyListable L

theorem partial_unary_range_program_iff_partial_range_of_unary_function
    (L : Language output) :
    (exists f : LanguagePartialUnaryRangeProgram output,
      LanguagePartialUnaryRangeProgramGenerates f L) <->
        PartialRangeOfUnaryStringFunction L :=
  Computability.partialUnaryRangeProgram_iff_partialRangeOfUnaryFunction L

theorem partial_function_program_range_language
    (f : Word input -> Option (Word output)) :
    Language.Equal
      (LanguageProgramRange (LanguagePartialFunctionProgram f))
      (PartialFunctionRangeLanguage f) :=
  Computability.partialFunctionProgram_range f

theorem partial_unary_function_program_range_iff_partial_range
    (L : Language output) :
    LanguagePartialUnaryFunctionProgramRange L <->
      PartialRangeOfUnaryStringFunction L :=
  Computability.partialUnaryFunctionProgramRange_iff_partialRangeOfUnaryFunction
    L

theorem partially_listable_language_iff_partial_unary_function_program_range
    (L : Language output) :
    LanguagePartiallyListable L <->
      LanguagePartialUnaryFunctionProgramRange L :=
  Computability.partiallyListable_iff_partialUnaryFunctionProgramRange L

theorem concrete_partial_function_compiled_turing_computable_partial
    {f : Word input -> Option (Word Bool)}
    {encodeInput : input -> Bool}
    {D : MachineDescription}
    (h : ConcretePartialFunctionCompiledByDescription f encodeInput D) :
    TuringComputablePartial f :=
  Computability.partialFunctionCompiledByDescription_turingComputablePartial h

theorem concrete_compiled_partial_unary_range_is_partial_range
    {L : Language Bool}
    (h : ConcreteCompiledPartialUnaryRange L) :
    PartialRangeOfUnaryStringFunction L :=
  Computability.compiledPartialUnaryRange_partialRangeOfUnaryFunction h

theorem concrete_compiled_partial_unary_range_has_turing_computable_range
    {L : Language Bool}
    (h : ConcreteCompiledPartialUnaryRange L) :
    ConcretePartialUnaryTuringComputableRange L :=
  Computability.compiledPartialUnaryRange_turingComputableRange h

theorem concrete_compiled_partial_unary_function_program_range_is_partial_range
    {L : Language Bool}
    (h : ConcreteCompiledPartialUnaryFunctionProgramRange L) :
    PartialRangeOfUnaryStringFunction L :=
  Computability.compiledPartialUnaryFunctionProgramRange_partialRange h

theorem concrete_compiled_partial_unary_function_program_range_has_turing_computable_range
    {L : Language Bool}
    (h : ConcreteCompiledPartialUnaryFunctionProgramRange L) :
    ConcretePartialUnaryTuringComputableRange L :=
  Computability.compiledPartialUnaryFunctionProgramRange_turingComputableRange h

theorem partial_unary_string_function_range_has_concrete_compiled_range_of_concrete_compiler
    (hcompile : ConcretePartialUnaryRangeDescriptionCompilerConstruction)
    {L : Language Bool}
    (h : PartialRangeOfUnaryStringFunction L) :
    ConcreteCompiledPartialUnaryRange L :=
  Computability.compiledPartialUnaryRange_of_partialRangeOfUnaryFunction
    hcompile h

theorem partially_listable_language_has_concrete_compiled_partial_unary_range_of_concrete_compiler
    (hcompile : ConcretePartialUnaryRangeDescriptionCompilerConstruction)
    {L : Language Bool}
    (h : LanguagePartiallyListable L) :
    ConcreteCompiledPartialUnaryRange L :=
  Computability.compiledPartialUnaryRange_of_partiallyListable hcompile h

theorem partial_unary_string_function_range_has_concrete_compiled_program_range_of_concrete_compiler
    (hcompile : ConcretePartialUnaryRangeDescriptionCompilerConstruction)
    {L : Language Bool}
    (h : PartialRangeOfUnaryStringFunction L) :
    ConcreteCompiledPartialUnaryFunctionProgramRange L :=
  Computability.compiledPartialUnaryFunctionProgramRange_of_partialRangeOfUnaryFunction
    hcompile h

theorem partially_listable_language_has_concrete_compiled_partial_unary_program_range_of_concrete_compiler
    (hcompile : ConcretePartialUnaryRangeDescriptionCompilerConstruction)
    {L : Language Bool}
    (h : LanguagePartiallyListable L) :
    ConcreteCompiledPartialUnaryFunctionProgramRange L :=
  Computability.compiledPartialUnaryFunctionProgramRange_of_partiallyListable
    hcompile h

theorem concrete_finite_partial_unary_output_range_is_program_range
    (P : ConcreteFinitePartialUnaryRangeProgram) :
    Language.Equal
      (ConcreteFinitePartialUnaryOutputRange P)
      (LanguageProgramRange
        (ConcreteFinitePartialUnaryRangeStagedProgram P)) := by
  intro out
  rfl

theorem concrete_finite_partial_unary_range_equal_description_outputs
    (P : ConcreteFinitePartialUnaryRangeProgram) :
    Language.Equal
      (ConcreteFinitePartialUnaryOutputRange P)
      (ConcreteFinitePartialUnaryDescriptionOutputRange P) := by
  simpa [ConcreteFinitePartialUnaryOutputRange,
    ConcreteFinitePartialUnaryDescriptionOutputRange]
    using
      Computability.FinitePartialUnaryRangeProgram.outputRange_equal_descriptionOutputRange
        P

theorem function_value_in_range (f : Word input -> Word output) (x : Word input) :
    f x ∈ FunctionRangeLanguage f :=
  range_mem x

theorem function_range_equal_of_pointwise
    {f g : Word input -> Word output}
    (hfg : forall x, f x = g x) :
    Language.Equal (FunctionRangeLanguage f) (FunctionRangeLanguage g) :=
  rangeLanguage_equal_of_pointwise hfg

theorem partial_function_range_equal_of_pointwise
    {f g : Word input -> Option (Word output)}
    (hfg : forall x, f x = g x) :
    Language.Equal
      (PartialFunctionRangeLanguage f) (PartialFunctionRangeLanguage g) :=
  partialRangeLanguage_equal_of_pointwise hfg

theorem computable_range_language_of_equal {L K : Language output}
    (h : RangeOfComputableFunction L) (hEq : Language.Equal L K) :
    RangeOfComputableFunction K :=
  rangeOfComputableFunction_of_equal h hEq

theorem unary_range_language_of_equal {L K : Language output}
    (h : RangeOfUnaryStringFunction L) (hEq : Language.Equal L K) :
    RangeOfUnaryStringFunction K :=
  rangeOfUnaryFunction_of_equal h hEq

theorem partial_unary_range_language_of_equal {L K : Language output}
    (h : PartialRangeOfUnaryStringFunction L) (hEq : Language.Equal L K) :
    PartialRangeOfUnaryStringFunction K :=
  partialRangeOfUnaryFunction_of_equal h hEq

def AcceptableListingEquivalenceStatement (L : Language alpha) : Prop :=
  AcceptableListingEquivalence L

def AcceptableRangeEquivalenceStatement (L : Language alpha) : Prop :=
  AcceptableRangeEquivalence L

/-!
## General Grammars and RE Languages

The final definitions relate unrestricted grammar generation to recursive
enumerability, then state the recursive-language equivalence for a language
and its complement under those construction principles.

Finite derivations are also finite-stage evidence: the reusable grammar bridge
turns derivation length into an acceptance trace and a staged recognizer
program.  The full Turing-machine equivalence remains a theorem shape until
the formalization has the universal/interpreter infrastructure needed to
compile that staged recognizer.
-/

def GeneralGrammarGeneratedLanguage (G : GeneralGrammar terminal nonterminal) :
    Language terminal :=
  GeneralGrammar.GeneratedLanguage G

def GeneralGrammarDerivationTraceLanguage
    (G : GeneralGrammar terminal nonterminal)
    (w : Word terminal) (n : Nat) : Prop :=
  GeneralGrammarDerivationTrace G w n

noncomputable def GeneralGrammarStagedRecognizer
    (G : GeneralGrammar terminal nonterminal) :
    StagedProgram terminal Unit :=
  GeneralGrammarRecognizerProgram G

def ConcreteBooleanGeneralGrammarRecognizerCompilerConstruction : Prop :=
  forall {nonterminal : Type}, forall G : GeneralGrammar Bool nonterminal,
    exists D : MachineDescription,
      ConcreteProgramCompiledByDescription (GeneralGrammarStagedRecognizer G) D

def GeneralGrammarAcceptabilityEquivalence (L : Language terminal) : Prop :=
  GeneralGrammar.Generated L <-> RecursivelyEnumerable L

def FiniteGeneralGrammarGenerated (L : Language terminal) : Prop :=
  GeneralGrammar.FiniteProductionGenerated L

def GeneralGrammarPairGenerated (L : Language terminal) : Prop :=
  GeneralGrammar.Generated L ∧ GeneralGrammar.Generated (Language.Compl L)

theorem general_grammar_derivation_trace_accepts_generated_language
    (G : GeneralGrammar terminal nonterminal) :
    LanguageAcceptanceTrace
      (GeneralGrammarDerivationTraceLanguage G)
      (GeneralGrammarGeneratedLanguage G) :=
  Computability.generalGrammar_derivationTrace_acceptance G

theorem general_grammar_staged_recognizer_accepts_generated_language
    (G : GeneralGrammar terminal nonterminal) :
    ProgramAcceptsLanguage
      (GeneralGrammarStagedRecognizer G)
      (GeneralGrammarGeneratedLanguage G) :=
  Computability.generalGrammarRecognizerProgram_acceptsLanguage G

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

theorem finite_general_grammar_generated_language_is_recursively_enumerable_of_staged_program_compiler
    (hcompile : StagedAcceptorCompilationConstruction terminal)
    {L : Language terminal}
    (h : FiniteGeneralGrammarGenerated L) :
    RecursivelyEnumerableLanguage L :=
  Computability.finiteProductionGenerated_recursivelyEnumerable_of_programCompiler
    hcompile h

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

/-!
The theorem equating general grammars with recursively enumerable languages is
recorded as an explicit statement shape. The construction proof is deferred
until the formalization has enough machine-encoding and simulation
infrastructure.
-/

end Section02
end Chapter05
end Book
end FoC
