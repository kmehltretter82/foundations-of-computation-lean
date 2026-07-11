import FoC.Book.Chapter05.Section02.ConstructionStatus
import FoC.Computability.Compiler.Skeletons

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter05
namespace Section02

/-!
# Section 5.2 dovetailing
-/

open Languages
open Computability

universe u v

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

def AcceptanceTraceStagedRecognizer
    (trace : Word alpha -> Nat -> Prop)
    [∀ w n, Decidable (trace w n)] :
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
    (h : TuringDecidable L) : TuringDecidable (Language.Compl L) :=
  Computability.turing_decidable_complement h

theorem recursive_language_of_recursive_complement {L : Language alpha}
    (h : TuringDecidable (Language.Compl L)) : TuringDecidable L :=
  Computability.turing_decidable_of_complement h

theorem recursive_language_complement_iff {L : Language alpha} :
    TuringDecidable (Language.Compl L) <-> TuringDecidable L :=
  Computability.turing_decidable_complement_iff

theorem stopped_turing_decidable_language_is_recursive
    {L : Language alpha}
    (h : StoppedTuringDecidable L) :
    TuringDecidable L :=
  Computability.stoppedTuringDecidable_to_turingDecidable h

theorem stopped_turing_decidable_language_complement
    {L : Language alpha}
    (h : StoppedTuringDecidable L) :
    StoppedTuringDecidable (Language.Compl L) :=
  Computability.stoppedTuringDecidable_complement h

theorem recursive_language_of_equal {L K : Language alpha}
    (h : TuringDecidable L) (hEq : Language.Equal L K) :
    TuringDecidable K :=
  Computability.turing_decidable_of_equal h hEq

theorem recursively_enumerable_language_of_equal {L K : Language alpha}
    (h : TuringAcceptable L) (hEq : Language.Equal L K) :
    TuringAcceptable K :=
  Computability.turing_acceptable_of_equal h hEq

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
    TuringAcceptable (PartialFunctionDomain f) :=
  Computability.turingComputablePartial_domain_acceptable h

theorem recursively_enumerable_language_has_acceptance_trace
    {L : Language alpha}
    (h : TuringAcceptable L) :
    exists trace : Word alpha -> Nat -> Prop,
      AcceptanceTrace trace L :=
  Computability.turing_acceptable_has_acceptanceTrace h

theorem program_accepts_language_has_acceptance_trace
    {P : StagedProgram alpha Unit} {L : Language alpha}
    (h : ProgramAcceptsLanguage P L) :
    AcceptanceTrace (LanguageProgramAcceptanceTrace P) L :=
  Computability.programAcceptsLanguage_acceptanceTrace h

theorem program_acceptable_language_has_acceptance_trace
    {L : Language alpha}
    (h : ProgramAcceptable L) :
    exists trace : Word alpha -> Nat -> Prop,
      AcceptanceTrace trace L :=
  Computability.programAcceptable_has_acceptanceTrace h

theorem acceptance_trace_staged_recognizer_accepts_language
    {trace : Word alpha -> Nat -> Prop} {L : Language alpha}
    [∀ w n, Decidable (trace w n)]
    (h : AcceptanceTrace trace L) :
    ProgramAcceptsLanguage
      (AcceptanceTraceStagedRecognizer trace) L := by
  exact Computability.traceRecognizerProgram_acceptsLanguage h

theorem acceptance_trace_has_program_acceptable_language
    {trace : Word alpha -> Nat -> Prop} {L : Language alpha}
    [∀ w n, Decidable (trace w n)]
    (h : AcceptanceTrace trace L) :
    ProgramAcceptable L := by
  exact Computability.acceptanceTrace_programAcceptable h

theorem program_acceptable_language_iff_has_acceptance_trace
    (L : Language alpha) :
    ProgramAcceptable L <->
      exists trace : Word alpha -> Nat -> Prop,
        (exists _ : (forall w n, Decidable (trace w n)),
          AcceptanceTrace trace L) :=
  Computability.programAcceptable_iff_has_acceptanceTrace L

theorem recursively_enumerable_language_is_program_acceptable
    {L : Language alpha}
    (h : TuringAcceptable L) :
  ProgramAcceptable L :=
  Computability.hasDecidableAcceptanceTrace_programAcceptable
    (Computability.turing_acceptable_has_decidableAcceptanceTrace h)

/-!
Complementary traces are the finite evidence supplied by recognizers for a
language and for its complement. Soundness says a hit on one side decides the
input's status; eventuality says at least one side eventually hits for every
input.
-/

theorem re_and_co_re_have_complementary_acceptance_traces
    {L : Language alpha}
    (h : RecursivelyEnumerableWithComplement L) :
    exists accept reject : Word alpha -> Nat -> Prop,
      ComplementaryAcceptanceTraces accept reject L :=
  Computability.recursivelyEnumerable_with_complement_has_complementaryTraces h

theorem complementary_trace_accept_sound
    {accept reject : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (h : ComplementaryAcceptanceTraces accept reject L)
    {w : Word alpha} {n : Nat}
    (hn : accept w n) :
    w ∈ L :=
  Computability.complementaryAcceptanceTraces_accept_sound h hn

theorem complementary_trace_reject_sound
    {accept reject : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (h : ComplementaryAcceptanceTraces accept reject L)
    {w : Word alpha} {n : Nat}
    (hn : reject w n) :
    ¬ w ∈ L :=
  Computability.complementaryAcceptanceTraces_reject_sound h hn

theorem complementary_traces_eventually_hit
    {accept reject : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (h : ComplementaryAcceptanceTraces accept reject L)
    (w : Word alpha) :
    exists n : Nat, accept w n ∨ reject w n :=
  Computability.complementaryAcceptanceTraces_eventually_hits_classical h w

theorem language_trace_hit_mono
    {trace : Word alpha -> Nat -> Prop}
    {w : Word alpha} {m n : Nat}
    (hmn : m ≤ n)
    (h : TraceHitsBy trace w m) :
    TraceHitsBy trace w n :=
  Computability.traceHitsBy_mono hmn h

theorem complementary_trace_accepts_by_sound
    {accept reject : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (h : ComplementaryAcceptanceTraces accept reject L)
    {w : Word alpha} {limit : Nat}
    (hit : TraceHitsBy accept w limit) :
    w ∈ L :=
  Computability.complementaryTraceAcceptsBy_sound h hit

theorem complementary_trace_rejects_by_sound
    {accept reject : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (h : ComplementaryAcceptanceTraces accept reject L)
    {w : Word alpha} {limit : Nat}
    (hit : TraceHitsBy reject w limit) :
    ¬ w ∈ L :=
  Computability.complementaryTraceRejectsBy_sound h hit

theorem complementary_trace_search_no_conflict
    {accept reject : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (h : ComplementaryAcceptanceTraces accept reject L)
    {w : Word alpha} {acceptLimit rejectLimit : Nat}
    (ha : TraceHitsBy accept w acceptLimit)
    (hr : TraceHitsBy reject w rejectLimit) :
    False :=
  Computability.complementaryTraceSearch_no_conflict h ha hr

theorem complementary_trace_search_eventually_hits_by
    {accept reject : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (h : ComplementaryAcceptanceTraces accept reject L)
    (w : Word alpha) :
    exists limit : Nat, ComplementaryTraceSearchHit accept reject w limit :=
  Computability.complementaryTraceSearch_eventually_hits_by h w

theorem complementary_trace_search_eventually_classifies
    {accept reject : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (h : ComplementaryAcceptanceTraces accept reject L)
    (w : Word alpha) :
    exists limit : Nat,
      (TraceHitsBy accept w limit ∧ w ∈ L) ∨
        (TraceHitsBy reject w limit ∧ ¬ w ∈ L) :=
  Computability.complementaryTraceSearch_eventually_classifies h w

theorem re_and_co_re_bounded_search_eventually_classifies
    {L : Language alpha}
    (h : RecursivelyEnumerableWithComplement L)
    (w : Word alpha) :
    exists accept reject : Word alpha -> Nat -> Prop,
      ComplementaryAcceptanceTraces accept reject L ∧
        exists limit : Nat,
          (TraceHitsBy accept w limit ∧ w ∈ L) ∨
            (TraceHitsBy reject w limit ∧ ¬ w ∈ L) := by
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
    [∀ w n, Decidable (accept w n)]
    [∀ w n, Decidable (reject w n)]
    {L : Language alpha}
    (h : ComplementaryAcceptanceTraces accept reject L) :
    ProgramBoolDecides
      (Computability.DovetailProgram accept reject) L := by
  exact Computability.dovetailProgram_decides h

theorem re_and_co_re_have_dovetailing_program
    {L : Language alpha}
    (h : RecursivelyEnumerableWithComplement L) :
    exists accept reject : Word alpha -> Nat -> Prop,
      (exists _ : (forall w n, Decidable (accept w n)),
        exists _ : (forall w n, Decidable (reject w n)),
          ComplementaryAcceptanceTraces accept reject L ∧
            ProgramBoolDecides
              (Computability.DovetailProgram accept reject) L) :=
  by
    rcases
      Computability.recursivelyEnumerable_with_complement_has_decidableComplementaryTraces
        h with
      ⟨accept, reject, acceptDecidable, rejectDecidable, htraces⟩
    letI := acceptDecidable
    letI := rejectDecidable
    exact ⟨accept, reject, acceptDecidable, rejectDecidable, htraces,
      complementary_traces_dovetailing_program_decides htraces⟩

theorem re_and_co_re_have_paired_bounded_search_decider
    {L : Language alpha}
    (h : RecursivelyEnumerableWithComplement L) :
    exists accept reject : Word alpha -> Nat -> Prop,
      (exists _ : (forall w n, Decidable (accept w n)),
        exists _ : (forall w n, Decidable (reject w n)),
          ComplementaryAcceptanceTraces accept reject L ∧
            ProgramBoolDecides
              (Computability.DovetailProgram accept reject) L) :=
  re_and_co_re_have_dovetailing_program h

theorem re_and_co_re_have_program_bool_decider
    {L : Language alpha}
    (h : RecursivelyEnumerableWithComplement L) :
    ProgramBoolDecidable L :=
  Computability.reCoRe_programBoolDecidable h

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
    Computability.BoundedTraceSearchConstruction :=
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
      (Computability.DovetailProgram
        (fun w n => accept.HaltsIn n w)
        (fun w n => reject.HaltsIn n w)).run w limit :=
  by
    simpa [Computability.DovetailProgram]
      using MachineDescription.boundedDovetailOutput_eq_dovetailProgram_run
        accept reject w limit

theorem concrete_machine_bounded_dovetail_true_iff_of_complementary_traces
    {accept reject : MachineDescription}
    {L : Language Bool}
    (htraces :
      ComplementaryAcceptanceTraces
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
      ComplementaryAcceptanceTraces
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
      ComplementaryAcceptanceTraces
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
    (hcompile : ProgramBoolDeciderCompilationPrinciple alpha) :
    ReCoReToDecidablePrinciple alpha :=
  Computability.reCoReToDecidablePrinciple_of_programBoolCompiler hcompile

theorem staged_acceptor_compilation_construction_of_concrete_descriptions
    (hcompile : SemanticDescriptionAcceptorCompilationAssumption) :
    ProgramAcceptorCompilationPrinciple Bool :=
  Computability.programAcceptorCompilationPrinciple_of_descriptionCompiler
    hcompile

theorem staged_bool_decider_compilation_construction_of_concrete_descriptions
    (hcompile : SemanticDescriptionBoolDeciderCompilationAssumption) :
    ProgramBoolDeciderCompilationPrinciple Bool :=
  Computability.programBoolDeciderCompilationPrinciple_of_descriptionCompiler
    hcompile

theorem dovetailing_decidable_construction_of_concrete_description_compiler
    (hcompile : SemanticDescriptionBoolDeciderCompilationAssumption) :
    ReCoReToDecidablePrinciple Bool :=
  dovetailing_decidable_construction_of_staged_program_compiler
    (staged_bool_decider_compilation_construction_of_concrete_descriptions
      hcompile)

theorem concrete_dovetail_description_compiler_of_concrete_bool_description_compiler
    (hcompile : SemanticDescriptionBoolDeciderCompilationAssumption) :
    DovetailDescriptionCompilerPrinciple :=
  Computability.dovetailDescriptionCompiler_of_descriptionBoolDeciderCompiler
    hcompile

theorem paired_recognizer_dovetail_compiler_of_concrete_bool_description_compiler
    (hcompile : SemanticDescriptionBoolDeciderCompilationAssumption) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  Computability.pairedRecognizerDovetailDescriptionCompiler_of_descriptionBoolDeciderCompiler
    hcompile

theorem paired_recognizer_dovetail_compiler_of_bounded_dovetail_table_compiler
    (hcompile :
      PairedRecognizerBoundedDovetailTableCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  Computability.pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    hcompile

theorem bounded_dovetail_table_compiler_of_paired_recognizer_dovetail_compiler
    (hcompile : PairedRecognizerDovetailDescriptionCompilerPrinciple) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction :=
  Computability.pairedRecognizerBoundedDovetailTableCompiler_of_pairedRecognizerDovetailDescriptionCompiler
    hcompile

theorem bounded_dovetail_table_compiler_iff_paired_recognizer_dovetail_compiler :
    PairedRecognizerBoundedDovetailTableCompilerConstruction <->
      PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  Computability.pairedRecognizerBoundedDovetailTableCompiler_iff_pairedRecognizerDovetailDescriptionCompiler

namespace BoundedDovetailTableCompiler

theorem of_layoutOutput_and_searchDriver
    (hrunner :
      PairedRecognizerDovetailLayoutCodeOutputRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailSearchDriverCompilerConstruction) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction :=
  Computability.pairedRecognizerBoundedDovetailTableCompiler_of_layoutCodeOutputRealizer_and_searchDriver
    hrunner hdriver

theorem of_stageAttemptOutput_and_searchDriver
    (hattempt :
      PairedRecognizerDovetailStageAttemptCodeOutputRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailStageAttemptSearchDriverCompilerConstruction) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction :=
  Computability.PairedRecognizerBoundedDovetailTableCompiler.of_stageAttemptOutput_and_search
    hattempt hdriver

theorem of_totalThenRawOutput_and_searchDriver
    (hattempt :
      PairedRecognizerDovetailTotalThenRawOutputCodeOutputRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailStageAttemptSearchDriverCompilerConstruction) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction :=
  Computability.PairedRecognizerBoundedDovetailTableCompiler.of_totalThenRawOutput_and_search
    hattempt hdriver

theorem of_totalStageAttemptOutput_and_searchDriver
    (hattempt :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailStageAttemptSearchDriverCompilerConstruction) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction :=
  Computability.PairedRecognizerBoundedDovetailTableCompiler.of_totalStageAttemptOutput_and_search
    hattempt hdriver

end BoundedDovetailTableCompiler

namespace PairedRecognizerDovetail

namespace StageAttemptSearchDriver

theorem of_descriptionBoolDeciderCompiler
    (hcompile : SemanticDescriptionBoolDeciderCompilationAssumption) :
    PairedRecognizerDovetailStageAttemptSearchDriverCompilerConstruction :=
  Computability.Search.stageCompilerOfDecider
    hcompile

end StageAttemptSearchDriver

namespace TotalStageAttemptSearchDriver

theorem of_descriptionBoolDeciderCompiler
    (hcompile : SemanticDescriptionBoolDeciderCompilationAssumption) :
    PairedRecognizerDovetailTotalStageAttemptSearchDriverCompilerConstruction :=
  Computability.Search.totalStageCompilerOfDecider
    hcompile

end TotalStageAttemptSearchDriver

namespace TotalStageAttemptControllerSearchDriver

theorem of_finiteStageLoopController
    (hloop :
      PairedRecognizerDovetailFiniteStageLoopControllerConstruction) :
    PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompilerConstruction :=
  Computability.pairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompiler_of_finiteStageLoopController
    hloop

end TotalStageAttemptControllerSearchDriver

end PairedRecognizerDovetail

namespace BoundedDovetailTableCompiler

theorem of_tapeCodeCompiler_and_descriptionBoolDeciderCompiler
    (htape : MachineDescriptionTapeCodeOutputCompilerConstruction)
    (hbool : SemanticDescriptionBoolDeciderCompilationAssumption) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction :=
  of_stageAttemptOutput_and_searchDriver
    (Computability.pairedRecognizerDovetailStageAttemptCodeOutputRealizer_of_tapeCodeOutputCompiler
      htape)
    (PairedRecognizerDovetail.StageAttemptSearchDriver.of_descriptionBoolDeciderCompiler
      hbool)

theorem of_totalStageAttemptSubroutine_and_totalSearchDriver
    (hattempt :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputSubroutineRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailTotalStageAttemptSearchDriverCompilerConstruction) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction :=
  Computability.Search.boundedCompilerOfSubroutineAndTotalSearch
    hattempt hdriver

theorem of_compiledSubroutine_and_controllerSearchDriver
    (hattempt :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction)
    (hdriver :
      PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompilerConstruction) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction :=
  Computability.Search.boundedCompilerOfCompiledSubroutineAndController
    hattempt hdriver

theorem of_controllerCloseout
    (hclose : PairedRecognizerDovetailControllerCompilerCloseout) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction :=
  Computability.pairedRecognizerBoundedDovetailTableCompiler_of_controllerCompilerCloseout
    hclose

theorem of_finiteControllerCloseout
    (hclose :
      PairedRecognizerDovetailFiniteControllerCompilerCloseout) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction :=
  Computability.pairedRecognizerBoundedDovetailTableCompiler_of_finiteControllerCompilerCloseout
    hclose

end BoundedDovetailTableCompiler

namespace PairedRecognizerDovetail

namespace LayoutCodeOutputRealizer

theorem of_subroutineRealizer
    (hrunner :
      PairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction) :
    PairedRecognizerDovetailLayoutCodeOutputRealizerConstruction :=
  Computability.pairedRecognizerDovetailLayoutCodeOutputRealizer_of_subroutineRealizer
    hrunner

end LayoutCodeOutputRealizer

end PairedRecognizerDovetail

namespace BoundedDovetailTableCompiler

theorem of_layoutSubroutine_and_subroutineSearchDriver
    (hrunner :
      PairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailSubroutineSearchDriverCompilerConstruction) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction :=
  Computability.PairedRecognizerBoundedDovetailTableCompiler.of_layoutSubroutine_and_subroutineSearch
    hrunner hdriver

end BoundedDovetailTableCompiler

namespace PairedRecognizerDovetailCompiler

theorem of_layoutOutput_and_searchDriver
    (hrunner :
      PairedRecognizerDovetailLayoutCodeOutputRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  Computability.DescriptionCompiler.ofLayoutAndSearch
    hrunner hdriver

theorem of_stageAttemptOutput_and_searchDriver
    (hattempt :
      PairedRecognizerDovetailStageAttemptCodeOutputRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailStageAttemptSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  Computability.DescriptionCompiler.ofStageAttemptAndSearch
    hattempt hdriver

theorem of_tapeCodeCompiler_and_descriptionBoolDeciderCompiler
    (htape : MachineDescriptionTapeCodeOutputCompilerConstruction)
    (hbool : SemanticDescriptionBoolDeciderCompilationAssumption) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  Computability.DescriptionCompiler.ofTapeCodeAndDecider
    htape hbool

theorem of_totalStageAttemptSubroutine_and_totalSearchDriver
    (hattempt :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputSubroutineRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailTotalStageAttemptSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  Computability.DescriptionCompiler.ofTotalStageSubroutineAndSearch
    hattempt hdriver

theorem of_compiledSubroutine_and_controllerSearchDriver
    (hattempt :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction)
    (hdriver :
      PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  paired_recognizer_dovetail_compiler_of_bounded_dovetail_table_compiler
    (BoundedDovetailTableCompiler.of_compiledSubroutine_and_controllerSearchDriver
      hattempt hdriver)

theorem of_controllerCloseout
    (hclose : PairedRecognizerDovetailControllerCompilerCloseout) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  Computability.pairedRecognizerDovetailDescriptionCompiler_of_controllerCompilerCloseout
    hclose

theorem of_finiteControllerCloseout
    (hclose :
      PairedRecognizerDovetailFiniteControllerCompilerCloseout) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  Computability.pairedRecognizerDovetailDescriptionCompiler_of_finiteControllerCompilerCloseout
    hclose

theorem of_layoutSubroutine_and_subroutineSearchDriver
    (hrunner :
      PairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailSubroutineSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  paired_recognizer_dovetail_compiler_of_bounded_dovetail_table_compiler
    (BoundedDovetailTableCompiler.of_layoutSubroutine_and_subroutineSearchDriver
      hrunner hdriver)

end PairedRecognizerDovetailCompiler

namespace PairedRecognizerDovetail

namespace SearchDriver

theorem of_runnerSearchDriver
    (hdriver :
      PairedRecognizerDovetailRunnerSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailSearchDriverCompilerConstruction :=
  Computability.pairedRecognizerDovetailSearchDriverCompiler_of_runnerSearchDriverCompiler
    hdriver

end SearchDriver

namespace SubroutineSearchDriver

theorem of_subroutineRunnerSearchDriver
    (hdriver :
      PairedRecognizerDovetailSubroutineRunnerSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailSubroutineSearchDriverCompilerConstruction :=
  Computability.pairedRecognizerDovetailSubroutineSearchDriverCompiler_of_subroutineRunnerSearchDriverCompiler
    hdriver

end SubroutineSearchDriver

end PairedRecognizerDovetail

namespace BoundedDovetailTableCompiler

theorem of_layoutOutput_and_runnerSearchDriver
    (hrunner :
      PairedRecognizerDovetailLayoutCodeOutputRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailRunnerSearchDriverCompilerConstruction) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction :=
  of_layoutOutput_and_searchDriver
    hrunner
    (PairedRecognizerDovetail.SearchDriver.of_runnerSearchDriver
      hdriver)

theorem of_layoutSubroutine_and_runnerSearchDriver
    (hrunner :
      PairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailSubroutineRunnerSearchDriverCompilerConstruction) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction :=
  of_layoutSubroutine_and_subroutineSearchDriver
    hrunner
    (PairedRecognizerDovetail.SubroutineSearchDriver.of_subroutineRunnerSearchDriver
      hdriver)

end BoundedDovetailTableCompiler

namespace PairedRecognizerDovetailCompiler

theorem of_layoutOutput_and_runnerSearchDriver
    (hrunner :
      PairedRecognizerDovetailLayoutCodeOutputRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailRunnerSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  of_layoutOutput_and_searchDriver
    hrunner
    (PairedRecognizerDovetail.SearchDriver.of_runnerSearchDriver
      hdriver)

theorem of_layoutSubroutine_and_runnerSearchDriver
    (hrunner :
      PairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailSubroutineRunnerSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  of_layoutSubroutine_and_subroutineSearchDriver
    hrunner
    (PairedRecognizerDovetail.SubroutineSearchDriver.of_subroutineRunnerSearchDriver
      hdriver)

end PairedRecognizerDovetailCompiler

theorem dovetailing_decidable_construction_of_concrete_dovetail_description_compiler
    (hcompile : DovetailDescriptionCompilerPrinciple) :
    ReCoReToDecidablePrinciple Bool :=
  Computability.reCoReToDecidablePrinciple_of_dovetailDescriptionCompiler
    hcompile

theorem paired_recognizer_dovetail_compiler_of_concrete_dovetail_description_compiler
    (hcompile : DovetailDescriptionCompilerPrinciple) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  Computability.pairedRecognizerDovetailDescriptionCompiler_of_dovetailDescriptionCompiler
    hcompile

theorem finite_dovetail_compiler_construction_of_paired_recognizer_dovetail_compiler
    (hcompile : PairedRecognizerDovetailDescriptionCompilerPrinciple) :
    FiniteDovetailProgram.CompilerConstruction :=
  Computability.FiniteDovetailProgram.compilerConstruction_of_pairedRecognizerDescriptionCompiler
    hcompile

theorem paired_recognizer_dovetail_compiler_of_finite_dovetail_compiler
    (hcompile : FiniteDovetailProgram.CompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  Computability.FiniteDovetailProgram.pairedRecognizerDescriptionCompiler_of_compilerConstruction
    hcompile

theorem finite_dovetail_compiler_construction_iff_paired_recognizer_dovetail_compiler :
    FiniteDovetailProgram.CompilerConstruction <->
      PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  Computability.FiniteDovetailProgram.compilerConstruction_iff_pairedRecognizerDescriptionCompiler

theorem finite_dovetail_compiler_construction_of_concrete_dovetail_description_compiler
    (hcompile : DovetailDescriptionCompilerPrinciple) :
    FiniteDovetailProgram.CompilerConstruction :=
  Computability.FiniteDovetailProgram.compilerConstruction_of_dovetailDescriptionCompiler
    hcompile

theorem finite_dovetail_compiler_construction_of_concrete_bool_description_compiler
    (hcompile : SemanticDescriptionBoolDeciderCompilationAssumption) :
    FiniteDovetailProgram.CompilerConstruction :=
  Computability.FiniteDovetailProgram.compilerConstruction_of_descriptionBoolDeciderCompiler
    hcompile

theorem finite_dovetail_compiler_construction_of_bounded_dovetail_table_compiler
    (hcompile :
      PairedRecognizerBoundedDovetailTableCompilerConstruction) :
    FiniteDovetailProgram.CompilerConstruction :=
  Computability.FiniteDovetailProgram.compilerConstruction_of_boundedDovetailTableCompiler
    hcompile

theorem complementary_traces_recursive_language_of_concrete_dovetail_description_compiler
    (hcompile : DovetailDescriptionCompilerPrinciple)
    {L : Language Bool}
    {accept reject : Word Bool -> Nat -> Prop}
    [∀ w n, Decidable (accept w n)]
    [∀ w n, Decidable (reject w n)]
    (htraces : ComplementaryAcceptanceTraces accept reject L) :
    TuringDecidable L :=
  Computability.complementaryTraces_turingDecidable_of_dovetailDescriptionCompiler
    hcompile htraces

theorem re_and_co_re_recursive_language_of_concrete_dovetail_description_compiler
    (hcompile : DovetailDescriptionCompilerPrinciple)
    {L : Language Bool}
    (h : RecursivelyEnumerableWithComplement L) :
    TuringDecidable L :=
  Computability.reCoRe_turingDecidable_of_dovetailDescriptionCompiler
    hcompile h

theorem recursive_language_iff_re_and_co_re_of_concrete_dovetail_description_compiler
    (haccept : DecidableToAcceptablePrinciple Bool)
    (hcompile : DovetailDescriptionCompilerPrinciple)
    (L : Language Bool) :
    TuringDecidable L <-> RecursivelyEnumerableWithComplement L :=
  Computability.turingDecidable_iff_reCoRe_of_principles
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
    (h : MachineDescriptionAcceptsLanguage D L) :
    TuringAcceptable L :=
  Computability.machineDescriptionAcceptsLanguage_turingAcceptable h

theorem concrete_machine_description_decides_turing_decidable
    {D : MachineDescription} {L : Language Bool}
    (h : MachineDescriptionDecidesLanguage D L) :
    TuringDecidable L :=
  Computability.machineDescriptionDecidesLanguage_turingDecidable h

theorem concrete_program_acceptable_by_description_turing_acceptable
    {L : Language Bool}
    (h : ProgramAcceptableByDescription L) :
    TuringAcceptable L :=
  Computability.programAcceptableByDescription_turingAcceptable h

theorem concrete_program_bool_decidable_by_description_turing_decidable
    {L : Language Bool}
    (h : ProgramBoolDecidableByDescription L) :
    TuringDecidable L :=
  Computability.programBoolDecidableByDescription_turingDecidable h

theorem concrete_finite_acceptor_compiled_by_description
    (P : FiniteAcceptorProgram)
    (hD : P.description.WellFormed) :
    ProgramCompiledByDescription
      (FiniteAcceptorProgram.toStagedProgram P)
      (FiniteAcceptorProgram.compile P) :=
  Computability.FiniteAcceptorProgram.compiledByDescription P hD

theorem concrete_finite_acceptor_program_acceptable_by_description
    (P : FiniteAcceptorProgram)
    (hD : P.description.WellFormed)
    {L : Language Bool}
    (haccepts :
      ProgramAcceptsLanguage
        (FiniteAcceptorProgram.toStagedProgram P) L) :
    ProgramAcceptableByDescription L := by
  exists FiniteAcceptorProgram.toStagedProgram P
  exists FiniteAcceptorProgram.compile P
  exact And.intro haccepts
    (concrete_finite_acceptor_compiled_by_description P hD)

theorem concrete_finite_acceptor_recursively_enumerable
    (P : FiniteAcceptorProgram)
    (hD : P.description.WellFormed)
    {L : Language Bool}
    (haccepts :
      ProgramAcceptsLanguage
        (FiniteAcceptorProgram.toStagedProgram P) L) :
    TuringAcceptable L :=
  concrete_program_acceptable_by_description_turing_acceptable
    (concrete_finite_acceptor_program_acceptable_by_description
      P hD haccepts)

theorem concrete_finite_trace_recognizer_compiled_by_description
    (P : FiniteAcceptorProgram)
    (hD : P.description.WellFormed) :
    ProgramCompiledByDescription
      (AcceptanceTraceStagedRecognizer
        (FiniteAcceptorProgram.trace P))
      (FiniteAcceptorProgram.compile P) := by
  constructor
  · exact hD
  · intro w
    constructor
    · intro hhalt
      rcases hhalt with ⟨n, hn⟩
      exists n
      have htrace : FiniteAcceptorProgram.trace P w n := by
        simpa [FiniteAcceptorProgram.trace, FiniteAcceptorProgram.compile]
          using! hn
      simp [AcceptanceTraceStagedRecognizer, TraceRecognizerProgram, htrace]
    · intro hprog
      rcases hprog with ⟨n, hn⟩
      by_cases htrace : FiniteAcceptorProgram.trace P w n
      · exact ⟨n, by
          simpa [FiniteAcceptorProgram.trace, FiniteAcceptorProgram.compile]
            using! htrace⟩
      · simp [AcceptanceTraceStagedRecognizer, TraceRecognizerProgram,
          htrace] at hn

theorem concrete_finite_trace_recognizer_acceptable_by_description
    (P : FiniteAcceptorProgram)
    (hD : P.description.WellFormed)
    {L : Language Bool}
    (htrace : AcceptanceTrace
      (FiniteAcceptorProgram.trace P) L) :
    ProgramAcceptableByDescription L :=
  Computability.FiniteAcceptorProgram.traceRecognizer_programAcceptableByDescription
    P hD htrace

theorem concrete_finite_trace_recognizer_recursively_enumerable
    (P : FiniteAcceptorProgram)
    (hD : P.description.WellFormed)
    {L : Language Bool}
    (htrace : AcceptanceTrace
      (FiniteAcceptorProgram.trace P) L) :
    TuringAcceptable L :=
      Computability.FiniteAcceptorProgram.traceRecognizer_turingAcceptable
    P hD htrace

theorem concrete_finite_acceptor_recognizes_language_recursively_enumerable
    (P : FiniteAcceptorProgram)
    {L : Language Bool}
    (h : ConcreteFiniteAcceptorRecognizesLanguage P L) :
    TuringAcceptable L :=
  concrete_finite_trace_recognizer_recursively_enumerable
    P h.left h.right

theorem concrete_finite_recognizable_language_recursively_enumerable
    {L : Language Bool}
    (h : ConcreteFiniteRecognizableLanguage L) :
    TuringAcceptable L := by
  cases h with
  | intro P hP =>
      exact
        concrete_finite_acceptor_recognizes_language_recursively_enumerable
          P hP

theorem concrete_finite_complementary_recognizers_have_re_and_co_re
    {L : Language Bool}
    (h : ConcreteFiniteComplementaryRecognizers L) :
    RecursivelyEnumerableWithComplement L := by
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
    (P : FiniteBoolProgram)
    (hD : P.description.WellFormed) :
    BoolProgramCompiledByDescription
      (FiniteBoolProgram.toStagedProgram P)
      (FiniteBoolProgram.compile P) :=
  Computability.FiniteBoolProgram.compiledByDescription P hD

theorem concrete_finite_bool_program_bool_decidable_by_description
    (P : FiniteBoolProgram)
    (hD : P.description.WellFormed)
    {L : Language Bool}
    (hdecides :
      ProgramBoolDecides
        (FiniteBoolProgram.toStagedProgram P) L) :
    ProgramBoolDecidableByDescription L :=
  Computability.FiniteBoolProgram.programBoolDecidableByDescription
    P hD hdecides

theorem concrete_finite_bool_program_turing_decidable
    (P : FiniteBoolProgram)
    (hD : P.description.WellFormed)
    {L : Language Bool}
    (hdecides :
      ProgramBoolDecides
        (FiniteBoolProgram.toStagedProgram P) L) :
    TuringDecidable L :=
  Computability.FiniteBoolProgram.turingDecidable P hD hdecides

theorem concrete_finite_dovetail_program_bool_decidable_by_description
    (P : FiniteDovetailProgram)
    {L : Language Bool}
    (htraces : ComplementaryAcceptanceTraces
      (FiniteAcceptorProgram.trace P.accept)
      (FiniteAcceptorProgram.trace P.reject) L)
    (hcompiled : FiniteDovetailProgram.Compiled P) :
    ProgramBoolDecidableByDescription L := by
  simpa [FiniteDovetailProgram.Compiled, FiniteAcceptorProgram.trace]
    using!
      Computability.FiniteDovetailProgram.programBoolDecidableByDescription
        P htraces hcompiled

theorem concrete_finite_dovetail_program_turing_decidable
    (P : FiniteDovetailProgram)
    {L : Language Bool}
    (htraces : ComplementaryAcceptanceTraces
      (FiniteAcceptorProgram.trace P.accept)
      (FiniteAcceptorProgram.trace P.reject) L)
    (hcompiled : FiniteDovetailProgram.Compiled P) :
    TuringDecidable L := by
  simpa [FiniteDovetailProgram.Compiled, FiniteAcceptorProgram.trace]
    using! Computability.FiniteDovetailProgram.turingDecidable
      P htraces hcompiled

theorem concrete_finite_dovetail_program_turing_decidable_of_compiler_construction
    (hcompile : FiniteDovetailProgram.CompilerConstruction)
    {accept reject : FiniteAcceptorProgram}
    {L : Language Bool}
    (htraces : ComplementaryAcceptanceTraces
      (FiniteAcceptorProgram.trace accept)
      (FiniteAcceptorProgram.trace reject) L) :
    TuringDecidable L := by
  simpa [FiniteDovetailProgram.CompilerConstruction,
    FiniteAcceptorProgram.trace]
    using!
      Computability.FiniteDovetailProgram.turingDecidable_of_compilerConstruction
        hcompile htraces

theorem concrete_finite_dovetail_program_turing_decidable_of_paired_recognizer_compiler
    (hcompile : PairedRecognizerDovetailDescriptionCompilerPrinciple)
    {accept reject : FiniteAcceptorProgram}
    {L : Language Bool}
    (htraces : ComplementaryAcceptanceTraces
      (FiniteAcceptorProgram.trace accept)
      (FiniteAcceptorProgram.trace reject) L) :
    TuringDecidable L :=
  concrete_finite_dovetail_program_turing_decidable_of_compiler_construction
    (finite_dovetail_compiler_construction_of_paired_recognizer_dovetail_compiler
      hcompile)
    htraces

theorem concrete_finite_dovetail_program_exists_of_compiler_construction
    (hcompile : FiniteDovetailProgram.CompilerConstruction)
    (accept reject : FiniteAcceptorProgram) :
    exists P : FiniteDovetailProgram,
      P.accept = accept ∧ P.reject = reject ∧
        FiniteDovetailProgram.Compiled P := by
  cases hcompile accept reject with
  | intro decider hcompiled =>
      exact Exists.intro
        ({ accept := accept, reject := reject, decider := decider } :
          FiniteDovetailProgram)
        (And.intro rfl (And.intro rfl hcompiled))

theorem concrete_finite_dovetail_program_bool_decidable_by_description_of_compiler_construction
    (hcompile : FiniteDovetailProgram.CompilerConstruction)
    {accept reject : FiniteAcceptorProgram}
    {L : Language Bool}
    (htraces : ComplementaryAcceptanceTraces
      (FiniteAcceptorProgram.trace accept)
      (FiniteAcceptorProgram.trace reject) L) :
    ProgramBoolDecidableByDescription L := by
  cases hcompile accept reject with
  | intro decider hcompiled =>
      simpa [FiniteAcceptorProgram.trace]
        using
          concrete_finite_dovetail_program_bool_decidable_by_description
            ({ accept := accept, reject := reject, decider := decider } :
              FiniteDovetailProgram)
            htraces hcompiled

theorem finite_complementary_traces_recursive_language_of_finite_dovetail_compiler
    (hcompile : FiniteDovetailProgram.CompilerConstruction)
    {L : Language Bool}
    (h : exists accept reject : FiniteAcceptorProgram,
      ComplementaryAcceptanceTraces
        (FiniteAcceptorProgram.trace accept)
        (FiniteAcceptorProgram.trace reject) L) :
    TuringDecidable L := by
  cases h with
  | intro accept haccept =>
      cases haccept with
      | intro reject htraces =>
          exact
            concrete_finite_dovetail_program_turing_decidable_of_compiler_construction
              hcompile htraces

theorem concrete_finite_complementary_recognizers_recursive_language_of_finite_dovetail_compiler
    (hcompile : FiniteDovetailProgram.CompilerConstruction)
    {L : Language Bool}
    (h : ConcreteFiniteComplementaryRecognizers L) :
    TuringDecidable L := by
  cases h with
  | intro accept haccept =>
      cases haccept with
      | intro reject hreject =>
          exact
            concrete_finite_dovetail_program_turing_decidable_of_compiler_construction
              hcompile hreject.right.right

theorem concrete_finite_complementary_recognizers_have_compiled_dovetail_program
    (hcompile : FiniteDovetailProgram.CompilerConstruction)
    {L : Language Bool}
    (h : ConcreteFiniteComplementaryRecognizers L) :
    exists P : FiniteDovetailProgram,
      ProgramBoolDecides
        (FiniteDovetailProgram.toStagedProgram P) L ∧
        FiniteDovetailProgram.Compiled P := by
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
                exact Computability.dovetailProgram_decides
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
    ComplementaryAcceptanceTraces
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
    AcceptanceTrace
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
    AcceptanceTrace
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
      (TraceHitsBy
        (fun x n =>
          TuringMachine.HaltsWithOutputIn
            M n (EncodeWord encodeInput x) [one])
        w limit ∧ w ∈ L) ∨
        (TraceHitsBy
          (fun x n =>
            TuringMachine.HaltsWithOutputIn
              M n (EncodeWord encodeInput x) [zero])
          w limit ∧ ¬ w ∈ L) :=
  complementary_trace_search_eventually_classifies
    (stopped_decider_has_complementary_output_traces hstop hzeroOne h) w

theorem stopped_turing_decidable_language_has_complementary_output_traces
    {L : Language alpha}
    (h : StoppedTuringDecidable L) :
    exists accept reject : Word alpha -> Nat -> Prop,
      ComplementaryAcceptanceTraces accept reject L :=
  Computability.stoppedTuringDecidable_has_complementary_output_traces h

theorem stopped_turing_decidable_language_has_acceptance_trace
    {L : Language alpha}
    (h : StoppedTuringDecidable L) :
    exists trace : Word alpha -> Nat -> Prop,
      AcceptanceTrace trace L :=
  Computability.stoppedTuringDecidable_has_acceptanceTrace h

theorem stopped_turing_decidable_language_complement_has_acceptance_trace
    {L : Language alpha}
    (h : StoppedTuringDecidable L) :
    exists trace : Word alpha -> Nat -> Prop,
      AcceptanceTrace trace (Language.Compl L) :=
  Computability.stoppedTuringDecidable_complement_has_acceptanceTrace h

theorem stopped_turing_decidable_language_bounded_search_eventually_classifies
    {L : Language alpha}
    (h : StoppedTuringDecidable L)
    (w : Word alpha) :
    exists accept reject : Word alpha -> Nat -> Prop,
      ComplementaryAcceptanceTraces accept reject L ∧
        exists limit : Nat,
          (TraceHitsBy accept w limit ∧ w ∈ L) ∨
            (TraceHitsBy reject w limit ∧ ¬ w ∈ L) :=
  Computability.stoppedTuringDecidable_bounded_search_eventually_classifies h w

theorem recursive_language_re_and_co_re_of_decidable_to_acceptable
    (haccept : DecidableToAcceptablePrinciple alpha)
    {L : Language alpha}
    (h : TuringDecidable L) :
    RecursivelyEnumerableWithComplement L :=
  Computability.turingDecidable_reCoRe_of_decidableToAcceptable haccept h

theorem recursive_language_iff_re_and_co_re_of_constructions
    (haccept : DecidableToAcceptablePrinciple alpha)
    (hdovetail : ReCoReToDecidablePrinciple alpha)
    (L : Language alpha) :
    TuringDecidable L <-> RecursivelyEnumerableWithComplement L :=
  Computability.turingDecidable_iff_reCoRe_of_principles haccept hdovetail L

theorem recursive_iff_re_co_re_construction_of_principles
    (haccept : DecidableToAcceptablePrinciple alpha)
    (hdovetail : ReCoReToDecidablePrinciple alpha) :
    TuringDecidableIffReCoRePrinciple alpha :=
  Computability.turingDecidableIffReCoRePrinciple_of_principles
    haccept hdovetail


end Section02
end Chapter05
end Book
end FoC
