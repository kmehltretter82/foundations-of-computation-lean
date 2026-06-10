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

The formal page separates three levels of argument.

* At the semantic level, traces, listings, ranges, partial functions, and staged
  programs are related directly.
* At the bounded-trace level, finite machine runs, encoded configurations,
  finite derivation searches, and recognizer-to-grammar trace simulations are
  checked without requiring a generic transition-table compiler.
* At the compiler-principle level, staged programs and bounded trace checkers
  are connected to Turing machines by named construction hypotheses.
* At the finite-description level, concrete supplied descriptions and finite
  program records expose the construction interfaces used for executable
  machine descriptions.

The finite compiler boundaries are now first-order where possible. Boolean
finite grammar presentations use explicit {lit}`Fin n` nonterminals and a
production list, while paired-recognizer dovetailing is split into a bounded
layout runner and an unbounded stage-search driver.

This makes the theorem statements honest about implementation work. When a
textbook proof says to dovetail two recognizers or check a finite derivation,
this page proves the bounded trace core and names the finite compiler
interfaces instead of treating them as implicit.
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

The many definitions at the start of the file are mostly vocabulary adapters:
they give book-facing names to reusable predicates, staged-program compiler
principles, finite program descriptions, and concrete machine-description
relations. The theorem groups later in the page explain how those names fit
together.  The compiler vocabulary is split explicitly: names containing
{lit}`Semantic` are assumptions over arbitrary Lean-level programs, traces, or
partial functions; names containing {lit}`FiniteSource` are the finite-data
construction targets that can become concrete transition-table compilers.
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

def SemanticDescriptionAcceptorCompilationAssumption : Prop :=
  SemanticDescriptionAcceptorCompilerAssumption

def SemanticDescriptionBoolDeciderCompilationAssumption : Prop :=
  SemanticDescriptionBoolDeciderCompilerAssumption

def SemanticDovetailDescriptionCompilerAssumption : Prop :=
  Computability.SemanticDovetailDescriptionCompilerAssumption

def ConcreteDescriptionAcceptorCompilationConstruction : Prop :=
  SemanticDescriptionAcceptorCompilationAssumption

def ConcreteDescriptionBoolDeciderCompilationConstruction : Prop :=
  SemanticDescriptionBoolDeciderCompilationAssumption

def ConcreteDovetailDescriptionCompilerConstruction : Prop :=
  SemanticDovetailDescriptionCompilerAssumption

def ConcreteFiniteSourcePairedRecognizerDovetailCompilerConstruction : Prop :=
  FiniteSourcePairedRecognizerDovetailCompilerConstruction

def ConcretePairedRecognizerDovetailCompilerConstruction : Prop :=
  ConcreteFiniteSourcePairedRecognizerDovetailCompilerConstruction

def ConcreteTapeCodeExactCompilerConstruction : Prop :=
  MachineDescriptionTapeCodeExactCompilerConstruction

def ConcreteTapeCodeOutputCompilerConstruction : Prop :=
  MachineDescriptionTapeCodeOutputCompilerConstruction

def ConcretePairedRecognizerBoundedDovetailTableCompilerConstruction : Prop :=
  FiniteSourcePairedRecognizerBoundedDovetailTableCompilerConstruction

def ConcretePairedRecognizerDovetailSearchDriverCompilerConstruction : Prop :=
  PairedRecognizerDovetailSearchDriverCompilerConstruction

def ConcreteFixedDescriptionBoundedSimulatorCodeCompilerConstruction : Prop :=
  FixedDescriptionBoundedSimulatorCodeCompilerConstruction

def ConcreteFixedDescriptionBoundedSimulatorCodeOutputRealizerConstruction :
    Prop :=
  FixedDescriptionBoundedSimulatorCodeOutputRealizerConstruction

def ConcreteFixedDescriptionStepCodeCompilerConstruction : Prop :=
  FixedDescriptionStepCodeCompilerConstruction

def ConcreteFixedDescriptionStepCodeOutputRealizerConstruction : Prop :=
  FixedDescriptionStepCodeOutputRealizerConstruction

def ConcreteFixedDescriptionStepCodeConfigurationRealizerConstruction :
    Prop :=
  FixedDescriptionStepCodeConfigurationRealizerConstruction

def ConcreteMachineBoundedTraceSearchConstruction : Prop :=
  MachineBoundedTraceSearchConstruction

def ConcreteEncodedConfigurationTraceSearchConstruction : Prop :=
  EncodedConfigurationTraceSearchConstruction

def BoundedTraceSearchConstruction : Prop :=
  Computability.BoundedTraceSearchConstruction

def ConcretePairedRecognizerDovetailLayoutCodeCompilerConstruction : Prop :=
  PairedRecognizerDovetailLayoutCodeCompilerConstruction

def ConcretePairedRecognizerDovetailLayoutCodeOutputRealizerConstruction :
    Prop :=
  PairedRecognizerDovetailLayoutCodeOutputRealizerConstruction

def ConcreteFiniteDovetailCompilerConstruction : Prop :=
  FiniteDovetailProgram.CompilerConstruction

def SemanticPartialUnaryRangeCompilerAssumption : Prop :=
  Computability.SemanticPartialUnaryRangeCompilerAssumption

def ConcretePartialUnaryRangeDescriptionCompilerConstruction : Prop :=
  SemanticPartialUnaryRangeCompilerAssumption

def ConcreteFinitePartialUnaryRangeProgramCompilerConstruction : Prop :=
  FinitePartialUnaryRangeProgram.CompilerConstruction

def ConcreteFinitePartialUnaryRangeProgramCloseoutConstruction : Prop :=
  FinitePartialUnaryRangeProgram.RangeCloseoutConstruction

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

/-!
The next group changes representation level. The preceding staged-program
predicates are semantic; the description predicates say that a supplied finite
machine description realizes the same staged computation. Later theorems use
these bridges to state exactly which compiler facts are supplied by closeout
records.
-/

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

theorem concrete_machine_description_acceptance_trace
    {D : MachineDescription} {L : Language Bool}
    (h : ConcreteMachineDescriptionAccepts D L) :
    LanguageAcceptanceTrace (fun w n => D.HaltsIn n w) L := by
  intro w
  exact h.right w

/-!
Finite program wrappers give concrete handles for the examples and compiler
interfaces used below. They expose traces, compiled descriptions, staged
programs, and output-range conditions while keeping the reusable implementation
in the computability library.
-/

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

noncomputable def ConcreteFiniteBoolStagedProgram
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

def ConcreteFinitePartialUnaryOutputComplete
    (P : ConcreteFinitePartialUnaryRangeProgram) : Prop :=
  P.OutputComplete

def ConcreteFinitePartialUnaryOutputFunctional
    (P : ConcreteFinitePartialUnaryRangeProgram) : Prop :=
  P.OutputFunctional

noncomputable def ConcreteFinitePartialUnaryOutputFunction
    (P : ConcreteFinitePartialUnaryRangeProgram) :
    Word Unit -> Option (Word Bool) :=
  P.outputFunction

noncomputable def ConcreteFinitePartialUnaryOutputListing
    (P : ConcreteFinitePartialUnaryRangeProgram) :
    Nat -> Option (Word Bool) :=
  P.outputListing

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

def ConcreteFiniteAcceptorRecognizesLanguage
    (P : ConcreteFiniteAcceptorProgram) (L : Language Bool) : Prop :=
  P.description.WellFormed ∧
    LanguageAcceptanceTrace (ConcreteFiniteAcceptorTrace P) L

def ConcreteFiniteRecognizableLanguage (L : Language Bool) : Prop :=
  exists P : ConcreteFiniteAcceptorProgram,
    ConcreteFiniteAcceptorRecognizesLanguage P L

def ConcreteFiniteComplementaryRecognizers
    (L : Language Bool) : Prop :=
  exists accept reject : ConcreteFiniteAcceptorProgram,
    accept.description.WellFormed ∧ reject.description.WellFormed ∧
      LanguageComplementaryAcceptanceTraces
        (ConcreteFiniteAcceptorTrace accept)
        (ConcreteFiniteAcceptorTrace reject) L

def ConcreteFinitePartialUnaryRangePresentsLanguage
    (P : ConcreteFinitePartialUnaryRangeProgram)
    (L : Language Bool) : Prop :=
  P.description.WellFormed ∧
    ConcreteFinitePartialUnaryOutputComplete P ∧
      ConcreteFinitePartialUnaryOutputFunctional P ∧
        Language.Equal
          (ConcreteFinitePartialUnaryDescriptionOutputRange P) L

def ConcreteFinitePartialUnaryRangeLanguage
    (L : Language Bool) : Prop :=
  exists P : ConcreteFinitePartialUnaryRangeProgram,
    ConcreteFinitePartialUnaryRangePresentsLanguage P L

/-!
**Finite source presentations.**  These predicates name the concrete case where
the source object is already a finite supplied description.  A finite acceptor
recognizes a language by its halting trace, paired finite acceptors provide the
finite-source version of RE/co-RE dovetailing, and a finite partial-unary range
program presents a language when its normalized output range is extensionally
that language.  The later compiler assumptions are therefore only about
synthesizing these finite descriptions uniformly, not about the consequences of
having them.
-/

def LanguageProgramAcceptanceTrace
    (P : StagedProgram alpha Unit)
    (w : Word alpha) (n : Nat) : Prop :=
  ProgramAcceptanceTrace P w n

noncomputable def AcceptanceTraceStagedRecognizer
    (trace : Word alpha -> Nat -> Prop) :
    StagedProgram alpha Unit :=
  TraceRecognizerProgram trace

/-!
**Complements and Extensionality.**

Recursive languages are closed under complement, stopped deciders can be
swapped to decide complements, and both recursive and recursively enumerable
properties are invariant under language equality.

The contrast with recursively enumerable languages is important: complement
closure is immediate for deciders, but not for recognizers unless a recognizer
for the complement is also available.

These lemmas are small but structurally important. They make later equivalence
theorems insensitive to the particular predicate expression used for a language,
and they keep complement arguments reusable rather than tied to one concrete
machine.
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
**Traces and Dovetailing.**

Acceptance traces represent finite-stage evidence for RE languages. With
complementary traces, bounded dovetailing eventually classifies each input and
gives the formal core of the RE/co-RE-to-recursive theorem.

A trace is a time-indexed witness that some recognizer has accepted by a
bounded stage. Dovetailing searches both the language trace and complement
trace in increasing bounds until one side hits.

This is the didactic center of the page. The trace-level dovetailer is a
concrete staged program: it is not merely a postulated language theorem. The
compiler closeouts specify the description-level interfaces that turn that
staged program into a concrete Turing-machine description in each intended
setting.
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

/-!
Complementary traces are the finite evidence supplied by recognizers for a
language and for its complement. Soundness says a hit on one side decides the
input's status; eventuality says at least one side eventually hits for every
input.
-/

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

theorem re_and_co_re_have_paired_bounded_search_decider
    {L : Language alpha}
    (h : RecursivelyEnumerableLanguageWithComplement L) :
    exists accept reject : Word alpha -> Nat -> Prop,
      LanguageComplementaryAcceptanceTraces accept reject L ∧
        ProgramBoolDecidesLanguage
          (TraceDovetailProgram accept reject) L :=
  re_and_co_re_have_dovetailing_program h

theorem re_and_co_re_have_program_bool_decider
    {L : Language alpha}
    (h : RecursivelyEnumerableLanguageWithComplement L) :
    ProgramBoolDecidableLanguage L :=
  Computability.reCoRe_programBoolDecidable h

theorem re_and_co_re_have_program_bool_decider_by_paired_bounded_search
    {L : Language alpha}
    (h : RecursivelyEnumerableLanguageWithComplement L) :
    ProgramBoolDecidableLanguage L :=
  re_and_co_re_have_program_bool_decider h

/-!
This is the compiler handoff. The trace-level dovetailer already decides the
language as a staged program.  The named bounded-trace construction below is
the main Section 5.2 proof boundary for concrete finite traces: machine
halting, bounded hits, dovetail output, and canonical encoded configuration
runs are checked by executable predicates.  The following compiler theorems
explain how optional lower-level description compilers turn that bounded trace
route into ordinary recursive-language statements.

The paired-recognizer compiler construction is the concrete transition-level
version of the dovetailing handoff: its inputs are two finite
{name}`MachineDescription`s, and its output is a finite Boolean description for
the staged dovetailer over their halting traces.  The finite dovetail program
record is proved equivalent to this exact construction target.  The bounded
table-realizer target gives the corresponding transition-table interface: it
asks for a finite transition table that realizes the executable bounded dovetail
output from {module}`FoC.Computability.MachineBuilder`.
-/

theorem bounded_trace_search_construction :
    BoundedTraceSearchConstruction :=
  Computability.boundedTraceSearchConstruction

theorem concrete_machine_halts_in_bool_correct
    (D : MachineDescription) (n : Nat) (w : Word Bool) :
    MachineDescription.haltsInBool D n w = true <-> D.HaltsIn n w :=
  MachineDescription.haltsInBool_eq_true_iff D n w

theorem concrete_machine_hits_by_bool_correct
    (D : MachineDescription) (w : Word Bool) (limit : Nat) :
    MachineDescription.hitsByBool D w limit = true <->
      exists n : Nat, n ≤ limit ∧ D.HaltsIn n w :=
  MachineDescription.hitsByBool_eq_true_iff D w limit

theorem concrete_bounded_dovetail_output_correct
    (accept reject : MachineDescription)
    (w : Word Bool) (limit : Nat) :
    MachineDescription.boundedDovetailOutput accept reject w limit =
      (TraceDovetailProgram
        (fun w n => accept.HaltsIn n w)
        (fun w n => reject.HaltsIn n w)).run w limit :=
  MachineDescription.boundedDovetailOutput_eq_dovetailProgram_run
    accept reject w limit

theorem concrete_machine_bounded_dovetail_true_iff_of_complementary_traces
    {accept reject : MachineDescription}
    {L : Language Bool}
    (htraces :
      LanguageComplementaryAcceptanceTraces
        (fun w n => accept.HaltsIn n w)
        (fun w n => reject.HaltsIn n w) L)
    (w : Word Bool) :
    (exists limit : Nat,
      MachineDescription.boundedDovetailOutput
        accept reject w limit = some [true]) <->
        w ∈ L :=
  MachineDescription.boundedDovetailOutput_true_iff_of_complementaryTraces
    htraces w

theorem concrete_machine_bounded_dovetail_false_iff_of_complementary_traces
    {accept reject : MachineDescription}
    {L : Language Bool}
    (htraces :
      LanguageComplementaryAcceptanceTraces
        (fun w n => accept.HaltsIn n w)
        (fun w n => reject.HaltsIn n w) L)
    (w : Word Bool) :
    (exists limit : Nat,
      MachineDescription.boundedDovetailOutput
        accept reject w limit = some [false]) <->
        ¬ w ∈ L :=
  MachineDescription.boundedDovetailOutput_false_iff_of_complementaryTraces
    htraces w

theorem concrete_machine_bounded_dovetail_eventually_classifies
    {accept reject : MachineDescription}
    {L : Language Bool}
    (htraces :
      LanguageComplementaryAcceptanceTraces
        (fun w n => accept.HaltsIn n w)
        (fun w n => reject.HaltsIn n w) L)
    (w : Word Bool) :
    exists limit : Nat,
      (MachineDescription.boundedDovetailOutput
          accept reject w limit = some [true] ∧ w ∈ L) ∨
        (MachineDescription.boundedDovetailOutput
          accept reject w limit = some [false] ∧ ¬ w ∈ L) :=
  MachineDescription.boundedDovetailOutput_eventually_classifies_of_complementaryTraces
    htraces w

theorem concrete_checks_encoded_run_canonical
    (D : MachineDescription)
    (c : MachineDescription.Configuration)
    (steps : Nat) :
    MachineDescription.checksEncodedRun D
      (MachineDescription.encodeConfiguration c)
      steps
      (MachineDescription.encodeConfiguration
        (D.runConfig steps c)) = true :=
  MachineDescription.checksEncodedRun_encodeConfiguration D steps c

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

theorem concrete_dovetail_description_compiler_of_concrete_bool_description_compiler
    (hcompile : ConcreteDescriptionBoolDeciderCompilationConstruction) :
    ConcreteDovetailDescriptionCompilerConstruction :=
  Computability.dovetailDescriptionCompiler_of_descriptionBoolDeciderCompiler
    hcompile

theorem paired_recognizer_dovetail_compiler_of_concrete_bool_description_compiler
    (hcompile : ConcreteDescriptionBoolDeciderCompilationConstruction) :
    ConcretePairedRecognizerDovetailCompilerConstruction :=
  Computability.pairedRecognizerDovetailDescriptionCompiler_of_descriptionBoolDeciderCompiler
    hcompile

theorem paired_recognizer_dovetail_compiler_of_bounded_dovetail_table_compiler
    (hcompile :
      ConcretePairedRecognizerBoundedDovetailTableCompilerConstruction) :
    ConcretePairedRecognizerDovetailCompilerConstruction :=
  Computability.pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    hcompile

theorem bounded_dovetail_table_compiler_of_paired_recognizer_dovetail_compiler
    (hcompile : ConcretePairedRecognizerDovetailCompilerConstruction) :
    ConcretePairedRecognizerBoundedDovetailTableCompilerConstruction :=
  Computability.pairedRecognizerBoundedDovetailTableCompiler_of_pairedRecognizerDovetailDescriptionCompiler
    hcompile

theorem bounded_dovetail_table_compiler_iff_paired_recognizer_dovetail_compiler :
    ConcretePairedRecognizerBoundedDovetailTableCompilerConstruction <->
      ConcretePairedRecognizerDovetailCompilerConstruction :=
  Computability.pairedRecognizerBoundedDovetailTableCompiler_iff_pairedRecognizerDovetailDescriptionCompiler

theorem bounded_dovetail_table_compiler_of_layout_code_output_realizer_and_search_driver
    (hrunner :
      ConcretePairedRecognizerDovetailLayoutCodeOutputRealizerConstruction)
    (hdriver :
      ConcretePairedRecognizerDovetailSearchDriverCompilerConstruction) :
    ConcretePairedRecognizerBoundedDovetailTableCompilerConstruction :=
  Computability.pairedRecognizerBoundedDovetailTableCompiler_of_layoutCodeOutputRealizer_and_searchDriver
    hrunner hdriver

theorem paired_recognizer_dovetail_compiler_of_layout_code_output_realizer_and_search_driver
    (hrunner :
      ConcretePairedRecognizerDovetailLayoutCodeOutputRealizerConstruction)
    (hdriver :
      ConcretePairedRecognizerDovetailSearchDriverCompilerConstruction) :
    ConcretePairedRecognizerDovetailCompilerConstruction :=
  Computability.pairedRecognizerDovetailDescriptionCompiler_of_layoutCodeOutputRealizer_and_searchDriver
    hrunner hdriver

theorem dovetailing_decidable_construction_of_concrete_dovetail_description_compiler
    (hcompile : ConcreteDovetailDescriptionCompilerConstruction) :
    DovetailingDecidableConstruction Bool :=
  Computability.reCoReToDecidablePrinciple_of_dovetailDescriptionCompiler
    hcompile

theorem paired_recognizer_dovetail_compiler_of_concrete_dovetail_description_compiler
    (hcompile : ConcreteDovetailDescriptionCompilerConstruction) :
    ConcretePairedRecognizerDovetailCompilerConstruction :=
  Computability.pairedRecognizerDovetailDescriptionCompiler_of_dovetailDescriptionCompiler
    hcompile

theorem finite_dovetail_compiler_construction_of_paired_recognizer_dovetail_compiler
    (hcompile : ConcretePairedRecognizerDovetailCompilerConstruction) :
    ConcreteFiniteDovetailCompilerConstruction :=
  Computability.FiniteDovetailProgram.compilerConstruction_of_pairedRecognizerDescriptionCompiler
    hcompile

theorem paired_recognizer_dovetail_compiler_of_finite_dovetail_compiler
    (hcompile : ConcreteFiniteDovetailCompilerConstruction) :
    ConcretePairedRecognizerDovetailCompilerConstruction :=
  Computability.FiniteDovetailProgram.pairedRecognizerDescriptionCompiler_of_compilerConstruction
    hcompile

theorem finite_dovetail_compiler_construction_iff_paired_recognizer_dovetail_compiler :
    ConcreteFiniteDovetailCompilerConstruction <->
      ConcretePairedRecognizerDovetailCompilerConstruction :=
  Computability.FiniteDovetailProgram.compilerConstruction_iff_pairedRecognizerDescriptionCompiler

theorem finite_dovetail_compiler_construction_of_concrete_dovetail_description_compiler
    (hcompile : ConcreteDovetailDescriptionCompilerConstruction) :
    ConcreteFiniteDovetailCompilerConstruction :=
  Computability.FiniteDovetailProgram.compilerConstruction_of_dovetailDescriptionCompiler
    hcompile

theorem finite_dovetail_compiler_construction_of_concrete_bool_description_compiler
    (hcompile : ConcreteDescriptionBoolDeciderCompilationConstruction) :
    ConcreteFiniteDovetailCompilerConstruction :=
  Computability.FiniteDovetailProgram.compilerConstruction_of_descriptionBoolDeciderCompiler
    hcompile

theorem finite_dovetail_compiler_construction_of_bounded_dovetail_table_compiler
    (hcompile :
      ConcretePairedRecognizerBoundedDovetailTableCompilerConstruction) :
    ConcreteFiniteDovetailCompilerConstruction :=
  Computability.FiniteDovetailProgram.compilerConstruction_of_boundedDovetailTableCompiler
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

/-!
The concrete-description consequences are bookkeeping rather than new
diagonalization. They say that once a program or Boolean program is compiled by
a well-formed description, the usual Turing-acceptable or Turing-decidable
classification follows.
-/

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

theorem concrete_finite_acceptor_recognizes_language_recursively_enumerable
    (P : ConcreteFiniteAcceptorProgram)
    {L : Language Bool}
    (h : ConcreteFiniteAcceptorRecognizesLanguage P L) :
    RecursivelyEnumerableLanguage L :=
  concrete_finite_trace_recognizer_recursively_enumerable
    P h.left h.right

theorem concrete_finite_recognizable_language_recursively_enumerable
    {L : Language Bool}
    (h : ConcreteFiniteRecognizableLanguage L) :
    RecursivelyEnumerableLanguage L := by
  cases h with
  | intro P hP =>
      exact
        concrete_finite_acceptor_recognizes_language_recursively_enumerable
          P hP

theorem concrete_finite_complementary_recognizers_have_re_and_co_re
    {L : Language Bool}
    (h : ConcreteFiniteComplementaryRecognizers L) :
    RecursivelyEnumerableLanguageWithComplement L := by
  cases h with
  | intro accept haccept =>
      cases haccept with
      | intro reject hreject =>
          constructor
          · exact
              concrete_finite_trace_recognizer_recursively_enumerable
                accept hreject.left hreject.right.right.left
          · exact
              concrete_finite_trace_recognizer_recursively_enumerable
                reject hreject.right.left hreject.right.right.right

/-!
The next cluster is the deciding analogue of the acceptor cluster above. Boolean
programs compile to descriptions that decide a language, while dovetail programs
combine two finite acceptor traces into one Boolean decision procedure.
-/

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

theorem concrete_finite_dovetail_program_turing_decidable_of_compiler_construction
    (hcompile : ConcreteFiniteDovetailCompilerConstruction)
    {accept reject : ConcreteFiniteAcceptorProgram}
    {L : Language Bool}
    (htraces : LanguageComplementaryAcceptanceTraces
      (ConcreteFiniteAcceptorTrace accept)
      (ConcreteFiniteAcceptorTrace reject) L) :
    RecursiveLanguage L := by
  simpa [ConcreteFiniteDovetailCompilerConstruction,
    ConcreteFiniteAcceptorTrace]
    using
      Computability.FiniteDovetailProgram.turingDecidable_of_compilerConstruction
        hcompile htraces

theorem concrete_finite_dovetail_program_turing_decidable_of_paired_recognizer_compiler
    (hcompile : ConcretePairedRecognizerDovetailCompilerConstruction)
    {accept reject : ConcreteFiniteAcceptorProgram}
    {L : Language Bool}
    (htraces : LanguageComplementaryAcceptanceTraces
      (ConcreteFiniteAcceptorTrace accept)
      (ConcreteFiniteAcceptorTrace reject) L) :
    RecursiveLanguage L :=
  concrete_finite_dovetail_program_turing_decidable_of_compiler_construction
    (finite_dovetail_compiler_construction_of_paired_recognizer_dovetail_compiler
      hcompile)
    htraces

theorem concrete_finite_dovetail_program_exists_of_compiler_construction
    (hcompile : ConcreteFiniteDovetailCompilerConstruction)
    (accept reject : ConcreteFiniteAcceptorProgram) :
    exists P : ConcreteFiniteDovetailProgram,
      P.accept = accept ∧ P.reject = reject ∧
        ConcreteFiniteDovetailCompiled P := by
  cases hcompile accept reject with
  | intro decider hcompiled =>
      exact Exists.intro
        ({ accept := accept, reject := reject, decider := decider } :
          ConcreteFiniteDovetailProgram)
        (And.intro rfl (And.intro rfl hcompiled))

theorem concrete_finite_dovetail_program_bool_decidable_by_description_of_compiler_construction
    (hcompile : ConcreteFiniteDovetailCompilerConstruction)
    {accept reject : ConcreteFiniteAcceptorProgram}
    {L : Language Bool}
    (htraces : LanguageComplementaryAcceptanceTraces
      (ConcreteFiniteAcceptorTrace accept)
      (ConcreteFiniteAcceptorTrace reject) L) :
    ConcreteProgramBoolDecidableByDescription L := by
  cases hcompile accept reject with
  | intro decider hcompiled =>
      simpa [ConcreteFiniteAcceptorTrace]
        using
          concrete_finite_dovetail_program_bool_decidable_by_description
            ({ accept := accept, reject := reject, decider := decider } :
              ConcreteFiniteDovetailProgram)
            htraces hcompiled

theorem finite_complementary_traces_recursive_language_of_finite_dovetail_compiler
    (hcompile : ConcreteFiniteDovetailCompilerConstruction)
    {L : Language Bool}
    (h : exists accept reject : ConcreteFiniteAcceptorProgram,
      LanguageComplementaryAcceptanceTraces
        (ConcreteFiniteAcceptorTrace accept)
        (ConcreteFiniteAcceptorTrace reject) L) :
    RecursiveLanguage L := by
  cases h with
  | intro accept haccept =>
      cases haccept with
      | intro reject htraces =>
          exact
            concrete_finite_dovetail_program_turing_decidable_of_compiler_construction
              hcompile htraces

theorem concrete_finite_complementary_recognizers_recursive_language_of_finite_dovetail_compiler
    (hcompile : ConcreteFiniteDovetailCompilerConstruction)
    {L : Language Bool}
    (h : ConcreteFiniteComplementaryRecognizers L) :
    RecursiveLanguage L := by
  cases h with
  | intro accept haccept =>
      cases haccept with
      | intro reject hreject =>
          exact
            concrete_finite_dovetail_program_turing_decidable_of_compiler_construction
              hcompile hreject.right.right

theorem concrete_finite_complementary_recognizers_have_compiled_dovetail_program
    (hcompile : ConcreteFiniteDovetailCompilerConstruction)
    {L : Language Bool}
    (h : ConcreteFiniteComplementaryRecognizers L) :
    exists P : ConcreteFiniteDovetailProgram,
      ProgramBoolDecidesLanguage
        (ConcreteFiniteDovetailStagedProgram P) L ∧
        ConcreteFiniteDovetailCompiled P := by
  cases h with
  | intro accept haccept =>
      cases haccept with
      | intro reject hreject =>
          cases
            concrete_finite_dovetail_program_exists_of_compiler_construction
              hcompile accept reject with
          | intro P hP =>
              exists P
              constructor
              · cases hP.left
                cases hP.right.left
                exact
                  complementary_traces_dovetailing_program_decides
                    hreject.right.right
              · exact hP.right.right

/-!
Stopped deciders supply a concrete source of complementary traces: one trace
looks for a halted accepting output, while the other looks for a halted
rejecting output. This connects the Section 5.1 machine-level decider facts to
the dovetailing proof in this section.
-/

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
**Code-output boundary.**  Exact tape output is intentionally separated from
normalized code output here.  The identity primitive satisfies both contracts,
while erasure is impossible for the exact tape-window contract but is realized
by a concrete finite normalized-output machine.

For the fixed one-step primitive, the new bridge says that it is enough to
build a finite stepper on canonical encoded configurations.  Parser
canonicalization lemmas then promote that theorem to the full
{name}`TapeCodePrimitiveOutputRealizedByDescription` interface, covering any
code word whose configuration decoder succeeds completely.

The two formulations are now proved equivalent.  This concentrates the
construction interface into one finite transducer problem: build the concrete
Boolean transition table that parses a canonical configuration, performs one
fixed description-table lookup, and emits the re-encoded successor
configuration.

The concrete transducer pieces are retained as a small compiler core. A finite table
appends one fixed encoded code symbol to the normalized Boolean output, while
the code-primitive layer provides fixed unary comparisons and one-step tape
write/move actions with canonical encode/decode theorems. Exact compilation
of every code primitive is proved impossible because erasure cannot produce an
exact empty tape window from nonempty input. The viable boundary is therefore a
normalized-output tape-code compiler: if that one generic compiler principle is
supplied, the fixed stepper, bounded simulator, and dovetail-layout
machine-description obligations all follow.
-/

theorem concrete_fixed_description_bounded_simulator_table_compiler_of_code_compiler
    (hcompile :
      ConcreteFixedDescriptionBoundedSimulatorCodeCompilerConstruction) :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction :=
  Computability.fixedDescriptionBoundedSimulatorTableCompiler_of_codeCompiler
    hcompile

theorem concrete_fixed_description_bounded_simulator_table_compiler_of_code_output_realizer
    (hcompile :
      ConcreteFixedDescriptionBoundedSimulatorCodeOutputRealizerConstruction) :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction :=
  Computability.fixedDescriptionBoundedSimulatorTableCompiler_of_codeOutputRealizer
    hcompile

def concrete_machine_description_primitive_compiler_core :
    MachineDescriptionPrimitiveCompilerCore :=
  Computability.machineDescriptionPrimitiveCompilerCore

theorem concrete_tape_code_exact_compiler_construction_impossible :
    ¬ ConcreteTapeCodeExactCompilerConstruction :=
  Computability.not_machineDescriptionTapeCodeExactCompilerConstruction

def concrete_machine_description_compiler_closeout_of_tape_code_output_compiler
    (hcompile : ConcreteTapeCodeOutputCompilerConstruction) :
    MachineDescriptionCompilerCloseout :=
  Computability.machineDescriptionCompilerCloseout_of_tapeCodeOutputCompiler
    hcompile

theorem concrete_fixed_description_step_code_configuration_realizer_construction_of_tape_code_output_compiler
    (hcompile : ConcreteTapeCodeOutputCompilerConstruction) :
    ConcreteFixedDescriptionStepCodeConfigurationRealizerConstruction :=
  Computability.fixedDescriptionStepCodeConfigurationRealizerConstruction_of_tapeCodeOutputCompiler
    hcompile

theorem concrete_fixed_description_bounded_simulator_table_compiler_of_tape_code_output_compiler
    (hcompile : ConcreteTapeCodeOutputCompilerConstruction) :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction :=
  Computability.fixedDescriptionBoundedSimulatorTableCompiler_of_tapeCodeOutputCompiler
    hcompile

theorem concrete_paired_recognizer_dovetail_layout_code_output_realizer_of_tape_code_output_compiler
    (hcompile : ConcreteTapeCodeOutputCompilerConstruction) :
    ConcretePairedRecognizerDovetailLayoutCodeOutputRealizerConstruction :=
  Computability.pairedRecognizerDovetailLayoutCodeOutputRealizer_of_tapeCodeOutputCompiler
    hcompile

theorem concrete_fixed_description_step_code_output_realizer_of_configuration_realizer
    {D stepper : MachineDescription}
    (hstepper :
      FixedDescriptionStepCodeConfigurationRealizes D stepper) :
    TapeCodePrimitiveOutputRealizedByDescription
      (FixedDescriptionStepCode D) stepper :=
  Computability.fixedDescriptionStepCodeOutputRealizer_of_configurationRealizer
    hstepper

theorem concrete_fixed_description_step_code_output_realizer_construction_of_configuration_realizer_construction
    (hcompile :
      ConcreteFixedDescriptionStepCodeConfigurationRealizerConstruction) :
    ConcreteFixedDescriptionStepCodeOutputRealizerConstruction :=
  Computability.fixedDescriptionStepCodeOutputRealizerConstruction_of_configurationRealizerConstruction
    hcompile

theorem concrete_fixed_description_step_code_configuration_realizer_construction_of_output_realizer_construction
    (hcompile :
      ConcreteFixedDescriptionStepCodeOutputRealizerConstruction) :
    ConcreteFixedDescriptionStepCodeConfigurationRealizerConstruction :=
  Computability.fixedDescriptionStepCodeConfigurationRealizerConstruction_of_outputRealizerConstruction
    hcompile

theorem concrete_fixed_description_step_code_configuration_realizer_construction_iff_output_realizer_construction :
    ConcreteFixedDescriptionStepCodeConfigurationRealizerConstruction <->
      ConcreteFixedDescriptionStepCodeOutputRealizerConstruction :=
  Computability.fixedDescriptionStepCodeConfigurationRealizerConstruction_iff_outputRealizerConstruction

theorem concrete_fixed_description_step_code_configuration_realizes_transitionless
    {D : MachineDescription}
    (hD : D.transitions = []) :
    FixedDescriptionStepCodeConfigurationRealizes
      D MachineDescription.ExactIdentityDescription :=
  Computability.fixedDescriptionStepCodeConfigurationRealizes_transitionless
    hD

theorem concrete_fixed_description_step_code_configuration_realizes_exact_identity :
    FixedDescriptionStepCodeConfigurationRealizes
      MachineDescription.ExactIdentityDescription
      MachineDescription.ExactIdentityDescription :=
  Computability.fixedDescriptionStepCodeConfigurationRealizes_exactIdentityDescription

theorem concrete_tape_code_identity_compiled_by_description :
    TapeCodePrimitiveCompiledByDescription
      MachineDescription.TapeCodePrimitive.identity
      MachineDescription.ExactIdentityDescription :=
  Computability.tapeCodePrimitiveCompiledByDescription_identity

theorem concrete_tape_code_identity_output_realized_by_description :
    TapeCodePrimitiveOutputRealizedByDescription
      MachineDescription.TapeCodePrimitive.identity
      MachineDescription.ExactIdentityDescription :=
  Computability.tapeCodePrimitiveOutputRealizedByDescription_identity

theorem concrete_tape_code_erase_output_realized_by_description :
    TapeCodePrimitiveOutputRealizedByDescription
      MachineDescription.TapeCodePrimitive.erase
      MachineDescription.EraseRightDescription :=
  Computability.tapeCodePrimitiveOutputRealizedByDescription_erase

theorem concrete_tape_code_erase_not_exact_compiled_by_description :
    ¬ exists D : MachineDescription,
      TapeCodePrimitiveCompiledByDescription
        MachineDescription.TapeCodePrimitive.erase D :=
  Computability.not_tapeCodePrimitiveCompiledByDescription_erase

theorem concrete_tape_code_append_singleton_output_realized_by_description
    (symbol : MachineCodeSymbol) :
    TapeCodePrimitiveOutputRealizedByDescription
      (MachineDescription.TapeCodePrimitive.append [symbol])
      (MachineDescription.AppendCodeSymbolRightDescription symbol) :=
  Computability.tapeCodePrimitiveOutputRealizedByDescription_append_singleton
    symbol

theorem concrete_tape_code_compare_nat_eq_on_encoded_nat
    (target n : Nat) (suffix : Word MachineCodeSymbol) :
    (MachineDescription.TapeCodePrimitive.compareNatEq target).transform
        (MachineDescription.encodeNatAppend n suffix) =
      some (MachineDescription.encodeBoolAppend (n == target) suffix) :=
  MachineDescription.TapeCodePrimitive.compareNatEq_transform_encodeNatAppend
    target n suffix

theorem concrete_tape_code_compare_nat_lt_on_encoded_nat
    (bound n : Nat) (suffix : Word MachineCodeSymbol) :
    (MachineDescription.TapeCodePrimitive.compareNatLt bound).transform
        (MachineDescription.encodeNatAppend n suffix) =
      some
        (MachineDescription.encodeBoolAppend (decide (n < bound)) suffix) :=
  MachineDescription.TapeCodePrimitive.compareNatLt_transform_encodeNatAppend
    bound n suffix

theorem concrete_tape_code_write_move_on_encoded_tape
    (cell : Option Bool) (dir : Direction) (T : Tape Bool) :
    (MachineDescription.TapeCodePrimitive.writeMove cell dir).transform
        (MachineDescription.encodeTape T) =
      some
        (MachineDescription.encodeTape
          (Tape.move dir (Tape.write cell T))) :=
  MachineDescription.TapeCodePrimitive.writeMove_transform_encodeTape
    cell dir T

theorem concrete_tape_code_transition_action_on_lookup
    {D : MachineDescription} {c : MachineDescription.Configuration}
    {t : TransitionDescription}
    (hlookup :
      D.lookupTransition c.state (Tape.read c.tape) = some t) :
    (MachineDescription.TapeCodePrimitive.transitionTapeAction t).transform
        (MachineDescription.encodeTape c.tape) =
      some
        (MachineDescription.encodeTape (D.runConfig 1 c).tape) :=
  MachineDescription.TapeCodePrimitive.transitionTapeAction_transform_encodeTape_of_lookupTransition
    hlookup

theorem concrete_fixed_description_step_code_realizes
    (D : MachineDescription) :
    FixedDescriptionStepCodeRealizes D (FixedDescriptionStepCode D) :=
  Computability.fixedDescriptionStepCode_realizes D

theorem concrete_paired_recognizer_dovetail_layout_code_realizes
    (accept reject : MachineDescription) :
    PairedRecognizerDovetailLayoutCodeRealizes
      accept reject
      (PairedRecognizerDovetailLayoutCode accept reject) :=
  Computability.pairedRecognizerDovetailLayoutCode_realizes accept reject

theorem concrete_paired_recognizer_dovetail_layout_initial_output
    (accept reject : MachineDescription)
    (w : Word Bool) (limit : Nat) :
    MachineDescription.DovetailLayout.outputFromHits
        (MachineDescription.DovetailLayout.run accept reject limit
          (MachineDescription.DovetailLayout.initial
            accept reject w limit)) =
      MachineDescription.boundedDovetailOutput accept reject w limit :=
  Computability.pairedRecognizerDovetailLayout_initial_output
    accept reject w limit

/-!
**Listings and Ranges.**

Listable languages are represented by streams of words. The range theorems
connect listability with unary string functions, matching the book's
enumerator viewpoint.

The list may repeat words and does not have to decide absence. What matters is
eventual appearance: every member of the language occurs somewhere in the
stream.

The formalization includes total listings, partial listings that can represent
the empty language, unary-input range functions, and partial-function programs.
These versions are extensionally equivalent at the semantic layer. The concrete
compiled-range theorems then identify the finite output-completeness and
functionality conditions needed to recover the same range from a supplied
machine description.
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

def LanguageWordStreamCovers
    (stream : Nat -> Option (Word alpha)) : Prop :=
  WordStreamCovers stream

noncomputable def CodeCandidateStream
    (code : alpha -> Nat) : Nat -> Option alpha :=
  CodeCandidates code

noncomputable def BoundedAcceptanceTraceListing
    (candidates : Nat -> Option (Word alpha))
    (trace : Word alpha -> Nat -> Prop) :
    Nat -> Option (Word alpha) :=
  BoundedTraceListing candidates trace

theorem code_candidate_stream_covers
    {code : alpha -> Nat}
    (hcode : FoC.Foundation.Fn.Injective code) :
    forall x : alpha, exists n : Nat,
      CodeCandidateStream code n = some x :=
  codeCandidates_covers hcode

theorem bounded_acceptance_trace_listing_partially_lists
    {candidates : Nat -> Option (Word alpha)}
    {trace : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (hcovers : LanguageWordStreamCovers candidates)
    (htrace : LanguageAcceptanceTrace trace L) :
    LanguagePartiallyListedBy
      (BoundedAcceptanceTraceListing candidates trace) L :=
  acceptanceTrace_boundedTraceListing_partiallyListedBy hcovers htrace

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

theorem acceptance_trace_partially_listable_by_bounded_search
    {candidates : Nat -> Option (Word alpha)}
    {trace : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (hcovers : LanguageWordStreamCovers candidates)
    (htrace : LanguageAcceptanceTrace trace L) :
    LanguagePartiallyListable L :=
  acceptanceTrace_partiallyListable_of_word_stream hcovers htrace

theorem acceptance_trace_partially_listable_by_code_bounded_search
    {code : Word alpha -> Nat}
    (hcode : FoC.Foundation.Fn.Injective code)
    {trace : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (htrace : LanguageAcceptanceTrace trace L) :
    LanguagePartiallyListable L :=
  acceptanceTrace_partiallyListable_of_word_code hcode htrace

theorem recursively_enumerable_language_partially_listable_by_code_bounded_search
    {code : Word alpha -> Nat}
    (hcode : FoC.Foundation.Fn.Injective code)
    {L : Language alpha}
    (h : RecursivelyEnumerableLanguage L) :
    LanguagePartiallyListable L := by
  rcases recursively_enumerable_language_has_acceptance_trace h with
    ⟨trace, htrace⟩
  exact acceptance_trace_partially_listable_by_code_bounded_search
    hcode htrace

theorem listed_language_has_acceptance_trace
    {stream : Nat -> Word alpha} {L : Language alpha}
    (h : LanguageListedBy stream L) :
    LanguageAcceptanceTrace (fun w n => stream n = w) L :=
  listedBy_acceptanceTrace h

theorem partially_listed_language_has_acceptance_trace
    {stream : Nat -> Option (Word alpha)} {L : Language alpha}
    (h : LanguagePartiallyListedBy stream L) :
    LanguageAcceptanceTrace (fun w n => stream n = some w) L :=
  partiallyListedBy_acceptanceTrace h

theorem partially_listable_language_has_acceptance_trace_by_bounded_search
    {L : Language alpha}
    (h : LanguagePartiallyListable L) :
    exists trace : Word alpha -> Nat -> Prop,
      LanguageAcceptanceTrace trace L := by
  rcases h with ⟨stream, hstream⟩
  exact ⟨fun w n => stream n = some w,
    partially_listed_language_has_acceptance_trace hstream⟩

theorem partially_listable_language_program_acceptable_by_bounded_search
    {L : Language alpha}
    (h : LanguagePartiallyListable L) :
    ProgramAcceptableLanguage L := by
  rcases partially_listable_language_has_acceptance_trace_by_bounded_search
      h with
    ⟨trace, htrace⟩
  exact acceptance_trace_has_program_acceptable_language htrace

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

/-!
Unary inputs turn an index into a word. This small coding step is what makes a
list stream look like the range of a string function, and it also explains why
partial listings become partial unary functions rather than total ones.
-/

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

/-!
The range direction goes back from a stream to a function. Unary inputs encode
the stream index, so a total stream becomes a total unary function and a partial
stream becomes a partial unary function. The following equivalences package that
translation as language-class facts.
-/

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

theorem acceptance_trace_partial_range_by_bounded_search
    {candidates : Nat -> Option (Word output)}
    {trace : Word output -> Nat -> Prop}
    {L : Language output}
    (hcovers : LanguageWordStreamCovers candidates)
    (htrace : LanguageAcceptanceTrace trace L) :
    PartialRangeOfUnaryStringFunction L :=
  acceptanceTrace_partialRangeOfUnaryFunction_of_word_stream hcovers htrace

theorem acceptance_trace_partial_range_by_code_bounded_search
    {code : Word output -> Nat}
    (hcode : FoC.Foundation.Fn.Injective code)
    {trace : Word output -> Nat -> Prop}
    {L : Language output}
    (htrace : LanguageAcceptanceTrace trace L) :
    PartialRangeOfUnaryStringFunction L :=
  acceptanceTrace_partialRangeOfUnaryFunction_of_word_code hcode htrace

theorem recursively_enumerable_language_partial_range_by_code_bounded_search
    {code : Word output -> Nat}
    (hcode : FoC.Foundation.Fn.Injective code)
    {L : Language output}
    (h : RecursivelyEnumerableLanguage L) :
    PartialRangeOfUnaryStringFunction L := by
  rcases recursively_enumerable_language_has_acceptance_trace h with
    ⟨trace, htrace⟩
  exact acceptance_trace_partial_range_by_code_bounded_search hcode htrace

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

theorem partial_unary_string_function_range_has_acceptance_trace
    {L : Language output}
    (h : PartialRangeOfUnaryStringFunction L) :
    exists trace : Word output -> Nat -> Prop,
      LanguageAcceptanceTrace trace L :=
  partialRangeOfUnaryFunction_acceptanceTrace h

theorem partial_unary_string_function_range_program_acceptable_by_bounded_search
    {L : Language output}
    (h : PartialRangeOfUnaryStringFunction L) :
    ProgramAcceptableLanguage L := by
  rcases partial_unary_string_function_range_has_acceptance_trace h with
    ⟨trace, htrace⟩
  exact acceptance_trace_has_program_acceptable_language htrace

theorem listable_language_iff_range_of_unary_string_function
    (L : Language output) :
    LanguageListable L <-> RangeOfUnaryStringFunction L :=
  Computability.listable_iff_rangeOfUnaryFunction L

theorem partially_listable_language_iff_partial_range_of_unary_string_function
    (L : Language output) :
    LanguagePartiallyListable L <-> PartialRangeOfUnaryStringFunction L :=
  Computability.partiallyListable_iff_partialRangeOfUnaryFunction L

/-!
Programs are the operational version of the same listing/range story. A listing
program may skip outputs by being partial; a partial unary range program
generates exactly the language elements that appear as defined outputs.
-/

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

theorem partially_listable_language_has_listing_program
    {L : Language output}
    (h : LanguagePartiallyListable L) :
    exists stream : LanguageListingProgram output,
      LanguageListingProgramLists stream L :=
  (listing_program_iff_partially_listable_language L).mpr h

theorem listing_program_language_is_partially_listable
    {stream : LanguageListingProgram output} {L : Language output}
    (h : LanguageListingProgramLists stream L) :
    LanguagePartiallyListable L :=
  (listing_program_iff_partially_listable_language L).mp
    (Exists.intro stream h)

theorem partially_listable_language_has_partial_unary_range_program
    {L : Language output}
    (h : LanguagePartiallyListable L) :
    exists f : LanguagePartialUnaryRangeProgram output,
      LanguagePartialUnaryRangeProgramGenerates f L :=
  (partial_unary_range_program_iff_partial_range_of_unary_function L).mpr
    (partially_listable_language_range_of_partial_unary_string_function h)

theorem partial_unary_range_program_language_is_partially_listable
    {f : LanguagePartialUnaryRangeProgram output} {L : Language output}
    (h : LanguagePartialUnaryRangeProgramGenerates f L) :
    LanguagePartiallyListable L :=
  (partially_listable_language_iff_partial_range_of_unary_string_function L).mpr
    ((partial_unary_range_program_iff_partial_range_of_unary_function L).mp
      (Exists.intro f h))

theorem partially_listable_language_has_partial_unary_function_program_range
    {L : Language output}
    (h : LanguagePartiallyListable L) :
    LanguagePartialUnaryFunctionProgramRange L :=
  (partially_listable_language_iff_partial_unary_function_program_range L).mp h

theorem partial_unary_function_program_range_language_is_partially_listable
    {L : Language output}
    (h : LanguagePartialUnaryFunctionProgramRange L) :
    LanguagePartiallyListable L :=
  (partially_listable_language_iff_partial_unary_function_program_range L).mpr h

theorem staged_unary_program_range_is_partial_unary_range
    (P : StagedProgram Unit output) :
    PartialRangeOfUnaryStringFunction (LanguageProgramRange P) :=
  Computability.programRange_partialRangeOfUnaryFunction P

/-!
The compiled-range theorems state what a concrete description must provide to
serve as an enumerator. The semantic range is already a partial unary range; the
compiler hypothesis upgrades it to a machine-description-backed range over the
Boolean alphabet. Because the source of
{name}`ConcretePartialUnaryRangeDescriptionCompilerConstruction` is an arbitrary
Lean partial function, not a finite source syntax, the construction remains a
named boundary. The wrappers below record the consequences of supplying it.
-/

theorem concrete_partial_function_compiled_turing_computable_partial
    {f : Word input -> Option (Word Bool)}
    {encodeInput : input -> Bool}
    {D : MachineDescription}
    (h : ConcretePartialFunctionCompiledByDescription f encodeInput D) :
    TuringComputablePartial f :=
  Computability.partialFunctionCompiledByDescription_turingComputablePartial h

theorem concrete_partial_unary_range_description_compiler_computes_partial_function
    (hcompile : ConcretePartialUnaryRangeDescriptionCompilerConstruction)
    (f : Word Unit -> Option (Word Bool)) :
    TuringComputablePartial f :=
  Computability.partialUnaryRangeDescriptionCompilerPrinciple_turingComputablePartial
    hcompile f

theorem concrete_partial_unary_range_description_compiler_compiles_range
    (hcompile : ConcretePartialUnaryRangeDescriptionCompilerConstruction)
    (f : Word Unit -> Option (Word Bool)) :
    ConcreteCompiledPartialUnaryRange (PartialFunctionRangeLanguage f) :=
  Computability.partialUnaryRangeDescriptionCompilerPrinciple_compiledRange
    hcompile f

theorem concrete_partial_unary_range_description_compiler_compiles_program_range
    (hcompile : ConcretePartialUnaryRangeDescriptionCompilerConstruction)
    (f : Word Unit -> Option (Word Bool)) :
    ConcreteCompiledPartialUnaryFunctionProgramRange
      (LanguageProgramRange (LanguagePartialFunctionProgram f)) :=
  Computability.partialUnaryRangeDescriptionCompilerPrinciple_compiledProgramRange
    hcompile f

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

theorem concrete_partial_unary_turing_computable_range_is_partially_listable
    {L : Language Bool}
    (h : ConcretePartialUnaryTuringComputableRange L) :
    LanguagePartiallyListable L := by
  cases h with
  | intro f hf =>
      exact partial_unary_string_function_range_is_partially_listable
        (Exists.intro f hf.right)

theorem concrete_compiled_partial_unary_range_is_partially_listable
    {L : Language Bool}
    (h : ConcreteCompiledPartialUnaryRange L) :
    LanguagePartiallyListable L :=
  concrete_partial_unary_turing_computable_range_is_partially_listable
    (concrete_compiled_partial_unary_range_has_turing_computable_range h)

theorem concrete_compiled_partial_unary_function_program_range_is_partially_listable
    {L : Language Bool}
    (h : ConcreteCompiledPartialUnaryFunctionProgramRange L) :
    LanguagePartiallyListable L :=
  concrete_partial_unary_turing_computable_range_is_partially_listable
    (concrete_compiled_partial_unary_function_program_range_has_turing_computable_range
      h)

theorem concrete_compiled_partial_unary_range_of_equal
    {L K : Language Bool}
    (h : ConcreteCompiledPartialUnaryRange L)
    (hEq : Language.Equal L K) :
    ConcreteCompiledPartialUnaryRange K := by
  cases h with
  | intro f hf =>
      cases hf with
      | intro D hD =>
          exists f
          exists D
          exact And.intro hD.left
            (Language.equal_trans hD.right hEq)

theorem concrete_compiled_partial_unary_function_program_range_of_equal
    {L K : Language Bool}
    (h : ConcreteCompiledPartialUnaryFunctionProgramRange L)
    (hEq : Language.Equal L K) :
    ConcreteCompiledPartialUnaryFunctionProgramRange K := by
  cases h with
  | intro f hf =>
      cases hf with
      | intro D hD =>
          exists f
          exists D
          exact And.intro hD.left
            (Language.equal_trans hD.right hEq)

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

theorem staged_unary_program_range_has_concrete_compiled_range_of_concrete_compiler
    (hcompile : ConcretePartialUnaryRangeDescriptionCompilerConstruction)
    (P : StagedProgram Unit Bool) :
    ConcreteCompiledPartialUnaryRange (LanguageProgramRange P) :=
  Computability.compiledPartialUnaryRange_of_unaryProgramRange hcompile P

theorem staged_unary_program_range_has_concrete_compiled_program_range_of_concrete_compiler
    (hcompile : ConcretePartialUnaryRangeDescriptionCompilerConstruction)
    (P : StagedProgram Unit Bool) :
    ConcreteCompiledPartialUnaryFunctionProgramRange (LanguageProgramRange P) :=
  Computability.compiledPartialUnaryFunctionProgramRange_of_unaryProgramRange
    hcompile P

theorem partially_listable_language_has_concrete_compiled_partial_unary_program_range_of_concrete_compiler
    (hcompile : ConcretePartialUnaryRangeDescriptionCompilerConstruction)
    {L : Language Bool}
    (h : LanguagePartiallyListable L) :
    ConcreteCompiledPartialUnaryFunctionProgramRange L :=
  Computability.compiledPartialUnaryFunctionProgramRange_of_partiallyListable
    hcompile h

theorem partially_listable_language_iff_concrete_compiled_partial_unary_range_of_concrete_compiler
    (hcompile : ConcretePartialUnaryRangeDescriptionCompilerConstruction)
    (L : Language Bool) :
    LanguagePartiallyListable L <-> ConcreteCompiledPartialUnaryRange L := by
  constructor
  · intro h
    exact
      partially_listable_language_has_concrete_compiled_partial_unary_range_of_concrete_compiler
        hcompile h
  · exact concrete_compiled_partial_unary_range_is_partially_listable

theorem partially_listable_language_iff_concrete_compiled_partial_unary_program_range_of_concrete_compiler
    (hcompile : ConcretePartialUnaryRangeDescriptionCompilerConstruction)
    (L : Language Bool) :
    LanguagePartiallyListable L <->
      ConcreteCompiledPartialUnaryFunctionProgramRange L := by
  constructor
  · intro h
    exact
      partially_listable_language_has_concrete_compiled_partial_unary_program_range_of_concrete_compiler
        hcompile h
  · exact concrete_compiled_partial_unary_function_program_range_is_partially_listable

/-!
Finite partial-unary programs make the range story executable. Output
completeness supplies a compiled partial function, while functionality ensures
that the output relation really determines one partial function and therefore
one range language.
-/

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

theorem concrete_finite_partial_unary_output_function_compiled_by_description
    (P : ConcreteFinitePartialUnaryRangeProgram)
    (hD : P.description.WellFormed)
    (hcomplete : ConcreteFinitePartialUnaryOutputComplete P) :
    ConcretePartialFunctionCompiledByDescription
      (ConcreteFinitePartialUnaryOutputFunction P)
      (fun _ : Unit => true)
      P.description := by
  simpa [ConcreteFinitePartialUnaryOutputFunction,
    ConcreteFinitePartialUnaryOutputComplete]
    using
      Computability.FinitePartialUnaryRangeProgram.outputFunction_compiledByDescription
        P hD hcomplete

theorem concrete_finite_partial_unary_output_function_range_equal_description_outputs
    (P : ConcreteFinitePartialUnaryRangeProgram)
    (hfunctional : ConcreteFinitePartialUnaryOutputFunctional P) :
    Language.Equal
      (PartialFunctionRangeLanguage
        (ConcreteFinitePartialUnaryOutputFunction P))
      (ConcreteFinitePartialUnaryDescriptionOutputRange P) := by
  simpa [PartialFunctionRangeLanguage,
    ConcreteFinitePartialUnaryOutputFunction,
    ConcreteFinitePartialUnaryDescriptionOutputRange,
    ConcreteFinitePartialUnaryOutputFunctional]
    using
      Computability.FinitePartialUnaryRangeProgram.partialRange_outputFunction_equal_descriptionOutputRange
        P hfunctional

theorem concrete_finite_partial_unary_output_listing_partially_lists_description_outputs
    (P : ConcreteFinitePartialUnaryRangeProgram)
    (hfunctional : ConcreteFinitePartialUnaryOutputFunctional P) :
    LanguagePartiallyListedBy
      (ConcreteFinitePartialUnaryOutputListing P)
      (ConcreteFinitePartialUnaryDescriptionOutputRange P) := by
  simpa [ConcreteFinitePartialUnaryOutputListing,
    ConcreteFinitePartialUnaryDescriptionOutputRange,
    ConcreteFinitePartialUnaryOutputFunctional]
    using
      Computability.FinitePartialUnaryRangeProgram.outputListing_partiallyListedBy_descriptionOutputRange
        P hfunctional

theorem concrete_finite_partial_unary_description_output_range_compiled
    (P : ConcreteFinitePartialUnaryRangeProgram)
    (hD : P.description.WellFormed)
    (hcomplete : ConcreteFinitePartialUnaryOutputComplete P)
    (hfunctional : ConcreteFinitePartialUnaryOutputFunctional P) :
    ConcreteCompiledPartialUnaryRange
      (ConcreteFinitePartialUnaryDescriptionOutputRange P) := by
  simpa [ConcreteCompiledPartialUnaryRange,
    ConcreteFinitePartialUnaryDescriptionOutputRange,
    ConcreteFinitePartialUnaryOutputComplete,
    ConcreteFinitePartialUnaryOutputFunctional]
    using
      Computability.FinitePartialUnaryRangeProgram.compiledPartialUnaryRange_descriptionOutputRange
        P hD hcomplete hfunctional

theorem concrete_finite_partial_unary_description_output_range_turing_computable
    (P : ConcreteFinitePartialUnaryRangeProgram)
    (hD : P.description.WellFormed)
    (hcomplete : ConcreteFinitePartialUnaryOutputComplete P)
    (hfunctional : ConcreteFinitePartialUnaryOutputFunctional P) :
    ConcretePartialUnaryTuringComputableRange
      (ConcreteFinitePartialUnaryDescriptionOutputRange P) :=
  concrete_compiled_partial_unary_range_has_turing_computable_range
    (concrete_finite_partial_unary_description_output_range_compiled
      P hD hcomplete hfunctional)

theorem concrete_finite_partial_unary_description_output_range_partially_listable
    (P : ConcreteFinitePartialUnaryRangeProgram)
    (hD : P.description.WellFormed)
    (hcomplete : ConcreteFinitePartialUnaryOutputComplete P)
    (hfunctional : ConcreteFinitePartialUnaryOutputFunctional P) :
    LanguagePartiallyListable
      (ConcreteFinitePartialUnaryDescriptionOutputRange P) :=
  concrete_compiled_partial_unary_range_is_partially_listable
    (concrete_finite_partial_unary_description_output_range_compiled
      P hD hcomplete hfunctional)

theorem concrete_finite_partial_unary_description_output_range_has_program_range
    (P : ConcreteFinitePartialUnaryRangeProgram)
    (hD : P.description.WellFormed)
    (hcomplete : ConcreteFinitePartialUnaryOutputComplete P)
    (hfunctional : ConcreteFinitePartialUnaryOutputFunctional P) :
    LanguagePartialUnaryFunctionProgramRange
      (ConcreteFinitePartialUnaryDescriptionOutputRange P) :=
  partially_listable_language_has_partial_unary_function_program_range
    (concrete_finite_partial_unary_description_output_range_partially_listable
      P hD hcomplete hfunctional)

theorem concrete_finite_partial_unary_description_output_range_closeout
    (P : ConcreteFinitePartialUnaryRangeProgram)
    (hD : P.description.WellFormed)
    (hcomplete : ConcreteFinitePartialUnaryOutputComplete P)
    (hfunctional : ConcreteFinitePartialUnaryOutputFunctional P) :
    ConcreteCompiledPartialUnaryRange
        (ConcreteFinitePartialUnaryDescriptionOutputRange P) ∧
      ConcretePartialUnaryTuringComputableRange
        (ConcreteFinitePartialUnaryDescriptionOutputRange P) ∧
      LanguagePartiallyListable
        (ConcreteFinitePartialUnaryDescriptionOutputRange P) ∧
      LanguagePartialUnaryFunctionProgramRange
        (ConcreteFinitePartialUnaryDescriptionOutputRange P) := by
  constructor
  · exact
      concrete_finite_partial_unary_description_output_range_compiled
        P hD hcomplete hfunctional
  · constructor
    · exact
        concrete_finite_partial_unary_description_output_range_turing_computable
          P hD hcomplete hfunctional
    · constructor
      · exact
          concrete_finite_partial_unary_description_output_range_partially_listable
            P hD hcomplete hfunctional
      · exact
          concrete_finite_partial_unary_description_output_range_has_program_range
            P hD hcomplete hfunctional

theorem concrete_finite_partial_unary_description_output_range_compiled_program_range
    (P : ConcreteFinitePartialUnaryRangeProgram)
    (hD : P.description.WellFormed)
    (hcomplete : ConcreteFinitePartialUnaryOutputComplete P)
    (hfunctional : ConcreteFinitePartialUnaryOutputFunctional P) :
    ConcreteCompiledPartialUnaryFunctionProgramRange
      (ConcreteFinitePartialUnaryDescriptionOutputRange P) := by
  simpa [ConcreteCompiledPartialUnaryFunctionProgramRange,
    ConcreteFinitePartialUnaryDescriptionOutputRange,
    ConcreteFinitePartialUnaryOutputComplete,
    ConcreteFinitePartialUnaryOutputFunctional]
    using
      Computability.FinitePartialUnaryRangeProgram.compiledPartialUnaryFunctionProgramRange_descriptionOutputRange
        P hD hcomplete hfunctional

theorem concrete_finite_partial_unary_range_presentation_compiled_range
    (P : ConcreteFinitePartialUnaryRangeProgram)
    {L : Language Bool}
    (h : ConcreteFinitePartialUnaryRangePresentsLanguage P L) :
    ConcreteCompiledPartialUnaryRange L :=
  concrete_compiled_partial_unary_range_of_equal
    (concrete_finite_partial_unary_description_output_range_compiled
      P h.left h.right.left h.right.right.left)
    h.right.right.right

theorem concrete_finite_partial_unary_range_presentation_compiled_program_range
    (P : ConcreteFinitePartialUnaryRangeProgram)
    {L : Language Bool}
    (h : ConcreteFinitePartialUnaryRangePresentsLanguage P L) :
    ConcreteCompiledPartialUnaryFunctionProgramRange L :=
  concrete_compiled_partial_unary_function_program_range_of_equal
    (concrete_finite_partial_unary_description_output_range_compiled_program_range
      P h.left h.right.left h.right.right.left)
    h.right.right.right

theorem concrete_finite_partial_unary_range_language_compiled_range
    {L : Language Bool}
    (h : ConcreteFinitePartialUnaryRangeLanguage L) :
    ConcreteCompiledPartialUnaryRange L := by
  cases h with
  | intro P hP =>
      exact
        concrete_finite_partial_unary_range_presentation_compiled_range
          P hP

theorem concrete_finite_partial_unary_range_language_compiled_program_range
    {L : Language Bool}
    (h : ConcreteFinitePartialUnaryRangeLanguage L) :
    ConcreteCompiledPartialUnaryFunctionProgramRange L := by
  cases h with
  | intro P hP =>
      exact
        concrete_finite_partial_unary_range_presentation_compiled_program_range
          P hP

theorem concrete_finite_partial_unary_range_language_partially_listable
    {L : Language Bool}
    (h : ConcreteFinitePartialUnaryRangeLanguage L) :
    LanguagePartiallyListable L :=
  concrete_compiled_partial_unary_range_is_partially_listable
    (concrete_finite_partial_unary_range_language_compiled_range h)

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

def ConcreteFiniteTraceTableRecognizable
    (L : Language terminal) : Prop :=
  FiniteTraceTableRecognizable L

def ConcreteDescriptionRecognizerToFiniteGeneralGrammarConstruction : Prop :=
  DescriptionRecognizerToFiniteGeneralGrammarConstruction

def ConcreteBooleanRecognizerToFiniteGeneralGrammarConstruction : Prop :=
  BooleanRecognizerToFiniteGeneralGrammarConstruction

def ConcreteProgramAcceptableByDescriptionToFiniteGeneralGrammarConstruction :
    Prop :=
  ProgramAcceptableByDescriptionToFiniteGeneralGrammarConstruction

abbrev ConcreteMachineHistoryNonterminal
    (D : MachineDescription) :=
  MachineHistoryNonterminal D

def ConcreteMachineHistoryGrammar
    (D : MachineDescription) :
    GeneralGrammar Bool (ConcreteMachineHistoryNonterminal D) :=
  MachineDescriptionHistoryGrammar.grammar D

def ConcreteMachineHistoryGrammarProductions
    (D : MachineDescription) :
    List (GeneralGrammar.Production Bool
      (ConcreteMachineHistoryNonterminal D)) :=
  MachineDescriptionHistoryGrammar.productions D

def ConcreteMachineHistoryConfigurationForm
    (D : MachineDescription)
    (c : MachineDescription.Configuration) :
    SententialForm Bool (ConcreteMachineHistoryNonterminal D) :=
  MachineDescriptionHistoryGrammar.configForm D c

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
recognizer.  The paired-recognizer dovetail field is supplied either by a
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

theorem concrete_finite_bool_general_grammar_presentation_compiler_of_description_compiler
    (hcompile : ConcreteDescriptionAcceptorCompilationConstruction) :
    ConcreteFiniteBoolGeneralGrammarPresentationRecognizerCompilerConstruction :=
  Computability.finiteBoolGeneralGrammarPresentationRecognizerCompilerConstruction_of_descriptionCompiler
    hcompile

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
  partialUnaryRangeDescription := hclose.partialUnaryRangeDescription
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
    (concrete_finite_bool_general_grammar_presentation_compiler_of_description_compiler
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
    concrete_finite_bool_general_grammar_presentation_compiler_of_description_compiler
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

theorem boolean_finite_general_grammar_generated_is_recursively_enumerable_of_concrete_finite_grammar_compiler
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

theorem boolean_finite_general_grammar_to_recursively_enumerable_construction_of_concrete_finite_grammar_compiler
    (hcompile : ConcreteFiniteBooleanGeneralGrammarRecognizerCompilerConstruction) :
    FiniteGeneralGrammarToRecursivelyEnumerableConstruction Bool := by
  intro L hgenerated
  exact
    boolean_finite_general_grammar_generated_is_recursively_enumerable_of_concrete_finite_grammar_compiler
      hcompile hgenerated

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

theorem finite_general_grammar_pair_recursive_of_finite_data_closeout
    (hclose : ConcreteBooleanFiniteDataSection52CompilerCloseout)
    {L : Language Bool}
    (hpair : FiniteGeneralGrammarPairGenerated L) :
    RecursiveLanguage L := by
  rcases hpair.left with ⟨acceptNonterminal, acceptG,
    acceptFinite, acceptEq⟩
  rcases hpair.right with ⟨rejectNonterminal, rejectG,
    rejectFinite, rejectEq⟩
  let hlist : ConcreteFiniteProductionListGrammarRecognizerCompilerConstruction :=
    concrete_finite_production_list_grammar_recognizer_compiler_of_finite_presentation_compiler
      hclose.finiteGrammarRecognizerDescription
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
      hclose.pairedDovetailDescription
      (accept := acceptProgram) (reject := rejectProgram) htraces

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
extensionality.

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
The first-order presentation and search-driver boundaries identify the
remaining transition-table construction work without changing these book-facing
equivalence statements.
-/

end Section02
end Chapter05
end Book
end FoC
