import FoC.Book.Chapter05.Section02.Vocabulary

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
open Grammars

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

theorem bounded_dovetail_table_compiler_of_stage_attempt_code_output_realizer_and_stage_attempt_search_driver
    (hattempt :
      ConcretePairedRecognizerDovetailStageAttemptCodeOutputRealizerConstruction)
    (hdriver :
      ConcretePairedRecognizerDovetailStageAttemptSearchDriverCompilerConstruction) :
    ConcretePairedRecognizerBoundedDovetailTableCompilerConstruction :=
  Computability.pairedRecognizerBoundedDovetailTableCompiler_of_stageAttemptCodeOutputRealizer_and_stageAttemptSearchDriver
    hattempt hdriver

theorem bounded_dovetail_table_compiler_of_total_then_raw_output_code_output_realizer_and_stage_attempt_search_driver
    (hattempt :
      ConcretePairedRecognizerDovetailTotalThenRawOutputCodeOutputRealizerConstruction)
    (hdriver :
      ConcretePairedRecognizerDovetailStageAttemptSearchDriverCompilerConstruction) :
    ConcretePairedRecognizerBoundedDovetailTableCompilerConstruction :=
  Computability.pairedRecognizerBoundedDovetailTableCompiler_of_totalThenRawOutputCodeOutputRealizer_and_stageAttemptSearchDriver
    hattempt hdriver

theorem paired_recognizer_dovetail_stage_attempt_search_driver_of_description_bool_decider_compiler
    (hcompile : ConcreteDescriptionBoolDeciderCompilationConstruction) :
    ConcretePairedRecognizerDovetailStageAttemptSearchDriverCompilerConstruction :=
  Computability.pairedRecognizerDovetailStageAttemptSearchDriverCompiler_of_descriptionBoolDeciderCompiler
    hcompile

theorem paired_recognizer_dovetail_total_stage_attempt_search_driver_of_description_bool_decider_compiler
    (hcompile : ConcreteDescriptionBoolDeciderCompilationConstruction) :
    ConcretePairedRecognizerDovetailTotalStageAttemptSearchDriverCompilerConstruction :=
  Computability.pairedRecognizerDovetailTotalStageAttemptSearchDriverCompiler_of_descriptionBoolDeciderCompiler
    hcompile

theorem paired_recognizer_dovetail_total_stage_attempt_controller_search_driver_of_description_bool_decider_compiler
    (hcompile : ConcreteDescriptionBoolDeciderCompilationConstruction) :
    ConcretePairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompilerConstruction :=
  Computability.pairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompiler_of_descriptionBoolDeciderCompiler
    hcompile

theorem bounded_dovetail_table_compiler_of_tape_code_output_compiler_and_description_bool_decider_compiler
    (htape : ConcreteTapeCodeOutputCompilerConstruction)
    (hbool : ConcreteDescriptionBoolDeciderCompilationConstruction) :
    ConcretePairedRecognizerBoundedDovetailTableCompilerConstruction :=
  bounded_dovetail_table_compiler_of_stage_attempt_code_output_realizer_and_stage_attempt_search_driver
    (Computability.pairedRecognizerDovetailStageAttemptCodeOutputRealizer_of_tapeCodeOutputCompiler
      htape)
    (paired_recognizer_dovetail_stage_attempt_search_driver_of_description_bool_decider_compiler
      hbool)

theorem bounded_dovetail_table_compiler_of_total_stage_attempt_code_output_subroutine_realizer_and_total_stage_attempt_search_driver
    (hattempt :
      ConcretePairedRecognizerDovetailTotalStageAttemptCodeOutputSubroutineRealizerConstruction)
    (hdriver :
      ConcretePairedRecognizerDovetailTotalStageAttemptSearchDriverCompilerConstruction) :
    ConcretePairedRecognizerBoundedDovetailTableCompilerConstruction :=
  Computability.pairedRecognizerBoundedDovetailTableCompiler_of_totalStageAttemptCodeOutputSubroutineRealizer_and_totalStageAttemptSearchDriver
    hattempt hdriver

theorem bounded_dovetail_table_compiler_of_total_stage_attempt_code_output_compiled_subroutine_and_controller_search_driver
    (hattempt :
      ConcretePairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction)
    (hdriver :
      ConcretePairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompilerConstruction) :
    ConcretePairedRecognizerBoundedDovetailTableCompilerConstruction :=
  Computability.pairedRecognizerBoundedDovetailTableCompiler_of_totalStageAttemptCodeOutputCompiledSubroutine_and_controllerSearchDriver
    hattempt hdriver

theorem bounded_dovetail_table_compiler_of_controller_closeout
    (hclose : ConcretePairedRecognizerDovetailControllerCompilerCloseout) :
    ConcretePairedRecognizerBoundedDovetailTableCompilerConstruction :=
  Computability.pairedRecognizerBoundedDovetailTableCompiler_of_controllerCompilerCloseout
    hclose

theorem bounded_dovetail_table_compiler_of_total_stage_attempt_code_output_compiled_subroutine_and_description_bool_decider_compiler
    (hattempt :
      ConcretePairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction)
    (hbool : ConcreteDescriptionBoolDeciderCompilationConstruction) :
    ConcretePairedRecognizerBoundedDovetailTableCompilerConstruction :=
  Computability.pairedRecognizerBoundedDovetailTableCompiler_of_totalStageAttemptCodeOutputCompiledSubroutine_and_descriptionBoolDeciderCompiler
    hattempt hbool

theorem paired_recognizer_dovetail_layout_code_output_realizer_of_subroutine_realizer
    (hrunner :
      ConcretePairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction) :
    ConcretePairedRecognizerDovetailLayoutCodeOutputRealizerConstruction :=
  Computability.pairedRecognizerDovetailLayoutCodeOutputRealizer_of_subroutineRealizer
    hrunner

theorem bounded_dovetail_table_compiler_of_layout_code_output_subroutine_realizer_and_subroutine_search_driver
    (hrunner :
      ConcretePairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction)
    (hdriver :
      ConcretePairedRecognizerDovetailSubroutineSearchDriverCompilerConstruction) :
    ConcretePairedRecognizerBoundedDovetailTableCompilerConstruction :=
  Computability.pairedRecognizerBoundedDovetailTableCompiler_of_layoutCodeOutputSubroutineRealizer_and_subroutineSearchDriver
    hrunner hdriver

theorem paired_recognizer_dovetail_compiler_of_layout_code_output_realizer_and_search_driver
    (hrunner :
      ConcretePairedRecognizerDovetailLayoutCodeOutputRealizerConstruction)
    (hdriver :
      ConcretePairedRecognizerDovetailSearchDriverCompilerConstruction) :
    ConcretePairedRecognizerDovetailCompilerConstruction :=
  Computability.pairedRecognizerDovetailDescriptionCompiler_of_layoutCodeOutputRealizer_and_searchDriver
    hrunner hdriver

theorem paired_recognizer_dovetail_compiler_of_stage_attempt_code_output_realizer_and_stage_attempt_search_driver
    (hattempt :
      ConcretePairedRecognizerDovetailStageAttemptCodeOutputRealizerConstruction)
    (hdriver :
      ConcretePairedRecognizerDovetailStageAttemptSearchDriverCompilerConstruction) :
    ConcretePairedRecognizerDovetailCompilerConstruction :=
  Computability.pairedRecognizerDovetailDescriptionCompiler_of_stageAttemptCodeOutputRealizer_and_stageAttemptSearchDriver
    hattempt hdriver

theorem paired_recognizer_dovetail_compiler_of_tape_code_output_compiler_and_description_bool_decider_compiler
    (htape : ConcreteTapeCodeOutputCompilerConstruction)
    (hbool : ConcreteDescriptionBoolDeciderCompilationConstruction) :
    ConcretePairedRecognizerDovetailCompilerConstruction :=
  Computability.pairedRecognizerDovetailDescriptionCompiler_of_tapeCodeOutputCompiler_and_descriptionBoolDeciderCompiler
    htape hbool

theorem paired_recognizer_dovetail_compiler_of_total_stage_attempt_code_output_subroutine_realizer_and_total_stage_attempt_search_driver
    (hattempt :
      ConcretePairedRecognizerDovetailTotalStageAttemptCodeOutputSubroutineRealizerConstruction)
    (hdriver :
      ConcretePairedRecognizerDovetailTotalStageAttemptSearchDriverCompilerConstruction) :
    ConcretePairedRecognizerDovetailCompilerConstruction :=
  Computability.pairedRecognizerDovetailDescriptionCompiler_of_totalStageAttemptCodeOutputSubroutineRealizer_and_totalStageAttemptSearchDriver
    hattempt hdriver

theorem paired_recognizer_dovetail_compiler_of_total_stage_attempt_code_output_compiled_subroutine_and_controller_search_driver
    (hattempt :
      ConcretePairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction)
    (hdriver :
      ConcretePairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompilerConstruction) :
    ConcretePairedRecognizerDovetailCompilerConstruction :=
  paired_recognizer_dovetail_compiler_of_bounded_dovetail_table_compiler
    (bounded_dovetail_table_compiler_of_total_stage_attempt_code_output_compiled_subroutine_and_controller_search_driver
      hattempt hdriver)

theorem paired_recognizer_dovetail_compiler_of_controller_closeout
    (hclose : ConcretePairedRecognizerDovetailControllerCompilerCloseout) :
    ConcretePairedRecognizerDovetailCompilerConstruction :=
  Computability.pairedRecognizerDovetailDescriptionCompiler_of_controllerCompilerCloseout
    hclose

theorem paired_recognizer_dovetail_compiler_of_total_stage_attempt_code_output_compiled_subroutine_and_description_bool_decider_compiler
    (hattempt :
      ConcretePairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction)
    (hbool : ConcreteDescriptionBoolDeciderCompilationConstruction) :
    ConcretePairedRecognizerDovetailCompilerConstruction :=
  Computability.pairedRecognizerDovetailDescriptionCompiler_of_totalStageAttemptCodeOutputCompiledSubroutine_and_descriptionBoolDeciderCompiler
    hattempt hbool

theorem paired_recognizer_dovetail_compiler_of_layout_code_output_subroutine_realizer_and_subroutine_search_driver
    (hrunner :
      ConcretePairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction)
    (hdriver :
      ConcretePairedRecognizerDovetailSubroutineSearchDriverCompilerConstruction) :
    ConcretePairedRecognizerDovetailCompilerConstruction :=
  paired_recognizer_dovetail_compiler_of_bounded_dovetail_table_compiler
    (bounded_dovetail_table_compiler_of_layout_code_output_subroutine_realizer_and_subroutine_search_driver
      hrunner hdriver)

theorem paired_recognizer_dovetail_search_driver_of_runner_search_driver
    (hdriver :
      ConcretePairedRecognizerDovetailRunnerSearchDriverCompilerConstruction) :
    ConcretePairedRecognizerDovetailSearchDriverCompilerConstruction :=
  Computability.pairedRecognizerDovetailSearchDriverCompiler_of_runnerSearchDriverCompiler
    hdriver

theorem paired_recognizer_dovetail_subroutine_search_driver_of_subroutine_runner_search_driver
    (hdriver :
      ConcretePairedRecognizerDovetailSubroutineRunnerSearchDriverCompilerConstruction) :
    ConcretePairedRecognizerDovetailSubroutineSearchDriverCompilerConstruction :=
  Computability.pairedRecognizerDovetailSubroutineSearchDriverCompiler_of_subroutineRunnerSearchDriverCompiler
    hdriver

theorem bounded_dovetail_table_compiler_of_layout_code_output_realizer_and_runner_search_driver
    (hrunner :
      ConcretePairedRecognizerDovetailLayoutCodeOutputRealizerConstruction)
    (hdriver :
      ConcretePairedRecognizerDovetailRunnerSearchDriverCompilerConstruction) :
    ConcretePairedRecognizerBoundedDovetailTableCompilerConstruction :=
  bounded_dovetail_table_compiler_of_layout_code_output_realizer_and_search_driver
    hrunner
    (paired_recognizer_dovetail_search_driver_of_runner_search_driver
      hdriver)

theorem bounded_dovetail_table_compiler_of_layout_code_output_subroutine_realizer_and_subroutine_runner_search_driver
    (hrunner :
      ConcretePairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction)
    (hdriver :
      ConcretePairedRecognizerDovetailSubroutineRunnerSearchDriverCompilerConstruction) :
    ConcretePairedRecognizerBoundedDovetailTableCompilerConstruction :=
  bounded_dovetail_table_compiler_of_layout_code_output_subroutine_realizer_and_subroutine_search_driver
    hrunner
    (paired_recognizer_dovetail_subroutine_search_driver_of_subroutine_runner_search_driver
      hdriver)

theorem paired_recognizer_dovetail_compiler_of_layout_code_output_realizer_and_runner_search_driver
    (hrunner :
      ConcretePairedRecognizerDovetailLayoutCodeOutputRealizerConstruction)
    (hdriver :
      ConcretePairedRecognizerDovetailRunnerSearchDriverCompilerConstruction) :
    ConcretePairedRecognizerDovetailCompilerConstruction :=
  paired_recognizer_dovetail_compiler_of_layout_code_output_realizer_and_search_driver
    hrunner
    (paired_recognizer_dovetail_search_driver_of_runner_search_driver
      hdriver)

theorem paired_recognizer_dovetail_compiler_of_layout_code_output_subroutine_realizer_and_subroutine_runner_search_driver
    (hrunner :
      ConcretePairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction)
    (hdriver :
      ConcretePairedRecognizerDovetailSubroutineRunnerSearchDriverCompilerConstruction) :
    ConcretePairedRecognizerDovetailCompilerConstruction :=
  paired_recognizer_dovetail_compiler_of_layout_code_output_subroutine_realizer_and_subroutine_search_driver
    hrunner
    (paired_recognizer_dovetail_subroutine_search_driver_of_subroutine_runner_search_driver
      hdriver)

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


end Section02
end Chapter05
end Book
end FoC
