import FoC.Book.Chapter05.Section02.ConstructionStatus
import FoC.Book.Chapter05.Section02.Dovetailing
import FoC.Computability.Compiler.UniversalAndRanges.Ranges
import FoC.Computability.FiniteProgram

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter05
namespace Section02

/-!
# Section 5.2: Listings and Ranges
-/

open Languages
open Computability

universe u v

/-!
## Listings and Bounded Enumeration

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

theorem listed_language_of_equal {stream : Nat -> Word alpha}
    {L K : Language alpha}
    (h : ListedBy stream L) (hEq : Language.Equal L K) :
    ListedBy stream K :=
  listedBy_of_equal h hEq

theorem partially_listed_language_of_equal
    {stream : Nat -> Option (Word alpha)} {L K : Language alpha}
    (h : PartiallyListedBy stream L) (hEq : Language.Equal L K) :
    PartiallyListedBy stream K :=
  partiallyListedBy_of_equal h hEq

theorem listed_word_in_language {stream : Nat -> Word alpha} {L : Language alpha}
    (h : ListedBy stream L) (n : Nat) :
    stream n ∈ L :=
  listed_word_mem h n

theorem partially_listed_word_in_language
    {stream : Nat -> Option (Word alpha)} {L : Language alpha}
    (h : PartiallyListedBy stream L)
    {n : Nat} {w : Word alpha}
    (hn : stream n = some w) :
    w ∈ L :=
  partially_listed_word_mem h hn

theorem code_candidate_stream_covers
    {code : alpha -> Nat}
    (hcode : FoC.Foundation.Fn.Injective code) :
    forall x : alpha, exists n : Nat,
      CodeCandidates code n = some x :=
  codeCandidates_covers hcode

theorem bounded_acceptance_trace_listing_partially_lists
    {candidates : Nat -> Option (Word alpha)}
    {trace : Word alpha -> Nat -> Prop}
    [∀ w n, Decidable (trace w n)]
    {L : Language alpha}
    (hcovers : WordStreamCovers candidates)
    (htrace : AcceptanceTrace trace L) :
    PartiallyListedBy
      (BoundedTraceListing candidates trace) L :=
  acceptanceTrace_boundedTraceListing_partiallyListedBy hcovers htrace

theorem listable_language_of_equal {L K : Language alpha}
    (h : Listable L) (hEq : Language.Equal L K) :
    Listable K :=
  listable_of_equal h hEq

theorem partially_listable_language_of_equal {L K : Language alpha}
    (h : PartiallyListable L) (hEq : Language.Equal L K) :
    PartiallyListable K :=
  partiallyListable_of_equal h hEq

theorem empty_language_is_partially_listable :
    PartiallyListable (Language.Empty : Language alpha) :=
  Computability.empty_partiallyListable

theorem acceptance_trace_partially_listable_by_bounded_search
    {candidates : Nat -> Option (Word alpha)}
    {trace : Word alpha -> Nat -> Prop}
    [∀ w n, Decidable (trace w n)]
    {L : Language alpha}
    (hcovers : WordStreamCovers candidates)
    (htrace : AcceptanceTrace trace L) :
    PartiallyListable L :=
  acceptanceTrace_partiallyListable_of_word_stream hcovers htrace

theorem acceptance_trace_partially_listable_by_code_bounded_search
    {code : Word alpha -> Nat}
    (hcode : FoC.Foundation.Fn.Injective code)
    {trace : Word alpha -> Nat -> Prop}
    [∀ w n, Decidable (trace w n)]
    {L : Language alpha}
    (htrace : AcceptanceTrace trace L) :
    PartiallyListable L :=
  acceptanceTrace_partiallyListable_of_word_code hcode htrace

theorem recursively_enumerable_language_partially_listable_by_code_bounded_search
    {code : Word alpha -> Nat}
    (hcode : FoC.Foundation.Fn.Injective code)
    {L : Language alpha}
    (h : TuringAcceptable L) :
    PartiallyListable L := by
  classical
  rcases recursively_enumerable_language_has_acceptance_trace h with
    ⟨trace, htrace⟩
  exact acceptance_trace_partially_listable_by_code_bounded_search
    hcode htrace

theorem listed_language_has_acceptance_trace
    {stream : Nat -> Word alpha} {L : Language alpha}
    (h : ListedBy stream L) :
    AcceptanceTrace (fun w n => stream n = w) L :=
  listedBy_acceptanceTrace h

theorem partially_listed_language_has_acceptance_trace
    {stream : Nat -> Option (Word alpha)} {L : Language alpha}
    (h : PartiallyListedBy stream L) :
    AcceptanceTrace (fun w n => stream n = some w) L :=
  partiallyListedBy_acceptanceTrace h

theorem partially_listable_language_has_acceptance_trace_by_bounded_search
    {L : Language alpha}
    (h : PartiallyListable L) :
    exists trace : Word alpha -> Nat -> Prop,
      AcceptanceTrace trace L := by
  rcases h with ⟨stream, hstream⟩
  exact ⟨fun w n => stream n = some w,
    partially_listed_language_has_acceptance_trace hstream⟩

theorem partially_listable_language_program_acceptable_by_bounded_search
    [DecidableEq alpha]
    {L : Language alpha}
    (h : PartiallyListable L) :
    ProgramAcceptable L := by
  rcases h with ⟨stream, hstream⟩
  let trace : Word alpha -> Nat -> Prop := fun w n => stream n = some w
  have htrace : AcceptanceTrace trace L :=
    partially_listed_language_has_acceptance_trace hstream
  exact acceptance_trace_has_program_acceptable_language htrace

theorem unary_input_string_length (n : Nat) :
    Word.Length (UnaryInputWord n) = n :=
  Computability.unaryInputWord_length n

/-!
## Unary Range Functions

Unary inputs turn an index into a word. This small coding step is what makes a
list stream look like the range of a string function, and it also explains why
partial listings become partial unary functions rather than total ones.
-/

theorem unary_function_range_is_listed
    (f : Word Unit -> Word output) :
    ListedBy
      (fun n => f (UnaryInputWord n))
      (RangeLanguage f) :=
  Computability.unaryFunctionRange_listedBy f

theorem unary_function_range_is_listable
    (f : Word Unit -> Word output) :
    Listable (RangeLanguage f) :=
  Computability.unaryFunctionRange_listable f

theorem partial_unary_function_range_is_partially_listed
    (f : Word Unit -> Option (Word output)) :
    PartiallyListedBy
      (fun n => f (UnaryInputWord n))
      (PartialRangeLanguage f) :=
  Computability.partialUnaryFunctionRange_partiallyListedBy f

theorem partial_unary_function_range_is_partially_listable
    (f : Word Unit -> Option (Word output)) :
    PartiallyListable (PartialRangeLanguage f) :=
  Computability.partialUnaryFunctionRange_partiallyListable f

theorem listed_language_range_of_unary_function
    {stream : Nat -> Word output} {L : Language output}
    (h : ListedBy stream L) :
    Language.Equal
      (RangeLanguage (ListingAsUnaryFunction stream)) L :=
  Computability.listedBy_rangeLanguage_listingAsUnaryFunction h

theorem partially_listed_language_range_of_partial_unary_function
    {stream : Nat -> Option (Word output)} {L : Language output}
    (h : PartiallyListedBy stream L) :
    Language.Equal
      (PartialRangeLanguage
        (PartialListingAsUnaryFunction stream)) L :=
  Computability.partiallyListedBy_partialRangeLanguage_partialListingAsUnaryFunction
    h

theorem listable_language_has_unary_range_function
    {L : Language output}
    (h : Listable L) :
    exists f : Word Unit -> Word output,
      Language.Equal (RangeLanguage f) L :=
  Computability.listable_has_unary_range_function h

theorem partially_listable_language_has_partial_unary_range_function
    {L : Language output}
    (h : PartiallyListable L) :
    exists f : Word Unit -> Option (Word output),
      Language.Equal (PartialRangeLanguage f) L :=
  Computability.partiallyListable_has_partial_unary_range_function h

/-!
## String-Function Range Equivalences

The range direction goes back from a stream to a function. Unary inputs encode
the stream index, so a total stream becomes a total unary function and a partial
stream becomes a partial unary function. The following equivalences package that
translation as language-class facts.
-/

theorem listable_language_range_of_unary_string_function
    {L : Language output}
    (h : Listable L) :
    RangeOfUnaryFunction L :=
  Computability.listable_rangeOfUnaryFunction h

theorem partially_listable_language_range_of_partial_unary_string_function
    {L : Language output}
    (h : PartiallyListable L) :
    PartialRangeOfUnaryFunction L :=
  Computability.partiallyListable_partialRangeOfUnaryFunction h

theorem acceptance_trace_partial_range_by_bounded_search
    {candidates : Nat -> Option (Word output)}
    {trace : Word output -> Nat -> Prop}
    [∀ w n, Decidable (trace w n)]
    {L : Language output}
    (hcovers : WordStreamCovers candidates)
    (htrace : AcceptanceTrace trace L) :
    PartialRangeOfUnaryFunction L :=
  acceptanceTrace_partialRangeOfUnaryFunction_of_word_stream hcovers htrace

theorem acceptance_trace_partial_range_by_code_bounded_search
    {code : Word output -> Nat}
    (hcode : FoC.Foundation.Fn.Injective code)
    {trace : Word output -> Nat -> Prop}
    [∀ w n, Decidable (trace w n)]
    {L : Language output}
    (htrace : AcceptanceTrace trace L) :
    PartialRangeOfUnaryFunction L :=
  acceptanceTrace_partialRangeOfUnaryFunction_of_word_code hcode htrace

theorem recursively_enumerable_language_partial_range_by_code_bounded_search
    {code : Word output -> Nat}
    (hcode : FoC.Foundation.Fn.Injective code)
    {L : Language output}
    (h : TuringAcceptable L) :
    PartialRangeOfUnaryFunction L := by
  classical
  rcases recursively_enumerable_language_has_acceptance_trace h with
    ⟨trace, htrace⟩
  exact acceptance_trace_partial_range_by_code_bounded_search hcode htrace

theorem unary_string_function_range_is_listable
    {L : Language output}
    (h : RangeOfUnaryFunction L) :
    Listable L :=
  Computability.rangeOfUnaryFunction_listable h

theorem partial_unary_string_function_range_is_partially_listable
    {L : Language output}
    (h : PartialRangeOfUnaryFunction L) :
    PartiallyListable L :=
  Computability.partialRangeOfUnaryFunction_partiallyListable h

theorem partial_unary_string_function_range_has_acceptance_trace
    {L : Language output}
    (h : PartialRangeOfUnaryFunction L) :
    exists trace : Word output -> Nat -> Prop,
      AcceptanceTrace trace L :=
  partialRangeOfUnaryFunction_acceptanceTrace h

theorem partial_unary_string_function_range_program_acceptable_by_bounded_search
    [DecidableEq output]
    {L : Language output}
    (h : PartialRangeOfUnaryFunction L) :
    ProgramAcceptable L := by
  rcases Computability.partialRangeOfUnaryFunction_partiallyListable h with
    ⟨stream, hstream⟩
  let trace : Word output -> Nat -> Prop := fun w n => stream n = some w
  have htrace : AcceptanceTrace trace L :=
    partiallyListedBy_acceptanceTrace hstream
  exact acceptance_trace_has_program_acceptable_language htrace

theorem listable_language_iff_range_of_unary_string_function
    (L : Language output) :
    Listable L <-> RangeOfUnaryFunction L :=
  Computability.listable_iff_rangeOfUnaryFunction L

theorem partially_listable_language_iff_partial_range_of_unary_string_function
    (L : Language output) :
    PartiallyListable L <-> PartialRangeOfUnaryFunction L :=
  Computability.partiallyListable_iff_partialRangeOfUnaryFunction L

/-!
## Compiled Partial-Function Range Contracts

An option-valued function embeds into the staged-program semantics at stage
zero.  The following aliases retain the book page's compiled-range notation;
listability and partial unary ranges themselves use the canonical predicates
from {module}`FoC.Computability.Enumerable` directly.
-/

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

def ConcretePartialUnaryTuringComputableRange
    (L : Language Bool) : Prop :=
  PartialUnaryTuringComputableRange L

def ConcreteCompiledPartialUnaryRange
    (L : Language Bool) : Prop :=
  CompiledPartialUnaryRange L

def ConcreteCompiledPartialUnaryFunctionProgramRange
    (L : Language Bool) : Prop :=
  CompiledPartialUnaryFunctionProgramRange L

theorem partial_function_program_range_language
    (f : Word input -> Option (Word output)) :
    Language.Equal
      (LanguageProgramRange (LanguagePartialFunctionProgram f))
      (PartialRangeLanguage f) :=
  Computability.partialFunctionProgram_range f

theorem staged_unary_program_range_is_partial_unary_range
    (P : StagedProgram Unit output) :
    PartialRangeOfUnaryFunction (LanguageProgramRange P) :=
  Computability.programRange_partialRangeOfUnaryFunction P

/-!
## Description-Backed Range Compilers

The compiled-range theorems state what a concrete description must provide to
serve as an enumerator. The semantic range is already a partial unary range; the
compiler hypothesis upgrades it to a machine-description-backed range over the
Boolean alphabet. Because the source of
{name}`SemanticPartialUnaryRangeCompilerAssumption` is an arbitrary Lean partial
function, not a finite source syntax, the construction remains a named
semantic boundary. The wrappers below record the consequences of supplying it.
-/

theorem concrete_partial_function_compiled_turing_computable_partial
    {f : Word input -> Option (Word Bool)}
    {encodeInput : input -> Bool}
    {D : MachineDescription}
    (h : ConcretePartialFunctionCompiledByDescription f encodeInput D) :
    TuringComputablePartial f :=
  Computability.partialFunctionCompiledByDescription_turingComputablePartial h

theorem concrete_partial_unary_range_description_compiler_computes_partial_function
    (hcompile : SemanticPartialUnaryRangeCompilerAssumption)
    (f : Word Unit -> Option (Word Bool)) :
    TuringComputablePartial f :=
  Computability.partialUnaryRangeDescriptionCompilerPrinciple_turingComputablePartial
    hcompile f

theorem concrete_partial_unary_range_description_compiler_compiles_range
    (hcompile : SemanticPartialUnaryRangeCompilerAssumption)
    (f : Word Unit -> Option (Word Bool)) :
    ConcreteCompiledPartialUnaryRange (PartialRangeLanguage f) :=
  Computability.partialUnaryRangeDescriptionCompilerPrinciple_compiledRange
    hcompile f

theorem concrete_partial_unary_range_description_compiler_compiles_program_range
    (hcompile : SemanticPartialUnaryRangeCompilerAssumption)
    (f : Word Unit -> Option (Word Bool)) :
    ConcreteCompiledPartialUnaryFunctionProgramRange
      (LanguageProgramRange (LanguagePartialFunctionProgram f)) :=
  Computability.partialUnaryRangeDescriptionCompilerPrinciple_compiledProgramRange
    hcompile f

theorem concrete_compiled_partial_unary_range_is_partial_range
    {L : Language Bool}
    (h : ConcreteCompiledPartialUnaryRange L) :
    PartialRangeOfUnaryFunction L :=
  Computability.compiledPartialUnaryRange_partialRangeOfUnaryFunction h

theorem concrete_compiled_partial_unary_range_has_turing_computable_range
    {L : Language Bool}
    (h : ConcreteCompiledPartialUnaryRange L) :
    ConcretePartialUnaryTuringComputableRange L :=
  Computability.compiledPartialUnaryRange_turingComputableRange h

theorem concrete_compiled_partial_unary_function_program_range_is_partial_range
    {L : Language Bool}
    (h : ConcreteCompiledPartialUnaryFunctionProgramRange L) :
    PartialRangeOfUnaryFunction L :=
  Computability.compiledPartialUnaryFunctionProgramRange_partialRange h

theorem concrete_compiled_partial_unary_function_program_range_has_turing_computable_range
    {L : Language Bool}
    (h : ConcreteCompiledPartialUnaryFunctionProgramRange L) :
    ConcretePartialUnaryTuringComputableRange L :=
  Computability.compiledPartialUnaryFunctionProgramRange_turingComputableRange h

theorem concrete_partial_unary_turing_computable_range_is_partially_listable
    {L : Language Bool}
    (h : ConcretePartialUnaryTuringComputableRange L) :
    PartiallyListable L := by
  cases h with
  | intro f hf =>
      exact partial_unary_string_function_range_is_partially_listable
        (Exists.intro f hf.right)

theorem concrete_compiled_partial_unary_range_is_partially_listable
    {L : Language Bool}
    (h : ConcreteCompiledPartialUnaryRange L) :
    PartiallyListable L :=
  concrete_partial_unary_turing_computable_range_is_partially_listable
    (concrete_compiled_partial_unary_range_has_turing_computable_range h)

theorem concrete_compiled_partial_unary_function_program_range_is_partially_listable
    {L : Language Bool}
    (h : ConcreteCompiledPartialUnaryFunctionProgramRange L) :
    PartiallyListable L :=
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
            (FoC.Foundation.FSet.equal_trans hD.right hEq)

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
            (FoC.Foundation.FSet.equal_trans hD.right hEq)

theorem partial_unary_string_function_range_has_concrete_compiled_range_of_concrete_compiler
    (hcompile : SemanticPartialUnaryRangeCompilerAssumption)
    {L : Language Bool}
    (h : PartialRangeOfUnaryFunction L) :
    ConcreteCompiledPartialUnaryRange L :=
  Computability.compiledPartialUnaryRange_of_partialRangeOfUnaryFunction
    hcompile h

theorem partially_listable_language_has_concrete_compiled_partial_unary_range_of_concrete_compiler
    (hcompile : SemanticPartialUnaryRangeCompilerAssumption)
    {L : Language Bool}
    (h : PartiallyListable L) :
    ConcreteCompiledPartialUnaryRange L :=
  Computability.compiledPartialUnaryRange_of_partiallyListable hcompile h

theorem partial_unary_string_function_range_has_concrete_compiled_program_range_of_concrete_compiler
    (hcompile : SemanticPartialUnaryRangeCompilerAssumption)
    {L : Language Bool}
    (h : PartialRangeOfUnaryFunction L) :
    ConcreteCompiledPartialUnaryFunctionProgramRange L :=
  Computability.compiledPartialUnaryFunctionProgramRange_of_partialRangeOfUnaryFunction
    hcompile h

theorem staged_unary_program_range_has_concrete_compiled_range_of_concrete_compiler
    (hcompile : SemanticPartialUnaryRangeCompilerAssumption)
    (P : StagedProgram Unit Bool) :
    ConcreteCompiledPartialUnaryRange (LanguageProgramRange P) :=
  Computability.compiledPartialUnaryRange_of_unaryProgramRange hcompile P

theorem staged_unary_program_range_has_concrete_compiled_program_range_of_concrete_compiler
    (hcompile : SemanticPartialUnaryRangeCompilerAssumption)
    (P : StagedProgram Unit Bool) :
    ConcreteCompiledPartialUnaryFunctionProgramRange (LanguageProgramRange P) :=
  Computability.compiledPartialUnaryFunctionProgramRange_of_unaryProgramRange
    hcompile P

theorem partially_listable_language_has_concrete_compiled_partial_unary_program_range_of_concrete_compiler
    (hcompile : SemanticPartialUnaryRangeCompilerAssumption)
    {L : Language Bool}
    (h : PartiallyListable L) :
    ConcreteCompiledPartialUnaryFunctionProgramRange L :=
  Computability.compiledPartialUnaryFunctionProgramRange_of_partiallyListable
    hcompile h

theorem partially_listable_language_iff_concrete_compiled_partial_unary_range_of_concrete_compiler
    (hcompile : SemanticPartialUnaryRangeCompilerAssumption)
    (L : Language Bool) :
    PartiallyListable L <-> ConcreteCompiledPartialUnaryRange L := by
  constructor
  · intro h
    exact
      partially_listable_language_has_concrete_compiled_partial_unary_range_of_concrete_compiler
        hcompile h
  · exact concrete_compiled_partial_unary_range_is_partially_listable

theorem partially_listable_language_iff_concrete_compiled_partial_unary_program_range_of_concrete_compiler
    (hcompile : SemanticPartialUnaryRangeCompilerAssumption)
    (L : Language Bool) :
    PartiallyListable L <->
      ConcreteCompiledPartialUnaryFunctionProgramRange L := by
  constructor
  · intro h
    exact
      partially_listable_language_has_concrete_compiled_partial_unary_program_range_of_concrete_compiler
        hcompile h
  · exact concrete_compiled_partial_unary_function_program_range_is_partially_listable

/-!
## Finite Partial-Unary Programs

Finite partial-unary programs make the range story executable. Output
completeness supplies a compiled partial function, while functionality ensures
that the output relation really determines one partial function and therefore
one range language.
-/

theorem concrete_finite_partial_unary_output_range_is_program_range
    (P : FinitePartialUnaryRangeProgram) :
    Language.Equal
      (FinitePartialUnaryRangeProgram.outputRange P)
      (LanguageProgramRange
        (FinitePartialUnaryRangeProgram.toStagedProgram P)) := by
  intro out
  rfl

theorem concrete_finite_partial_unary_range_equal_description_outputs
    (P : FinitePartialUnaryRangeProgram) :
    Language.Equal
      (FinitePartialUnaryRangeProgram.outputRange P)
      (FinitePartialUnaryRangeProgram.descriptionOutputRange P) := by
  simpa [FinitePartialUnaryRangeProgram.outputRange,
    FinitePartialUnaryRangeProgram.descriptionOutputRange]
    using!
      Computability.FinitePartialUnaryRangeProgram.outputRange_equal_descriptionOutputRange
        P

theorem concrete_finite_partial_unary_output_function_compiled_by_description
    (P : FinitePartialUnaryRangeProgram)
    (hD : P.description.WellFormed)
    (hcomplete : FinitePartialUnaryRangeProgram.OutputComplete P) :
    ConcretePartialFunctionCompiledByDescription
      (FinitePartialUnaryRangeProgram.outputFunction P)
      (fun _ : Unit => true)
      P.description := by
  simpa [FinitePartialUnaryRangeProgram.outputFunction,
    FinitePartialUnaryRangeProgram.OutputComplete]
    using!
      Computability.FinitePartialUnaryRangeProgram.outputFunction_compiledByDescription
        P hD hcomplete

theorem concrete_finite_partial_unary_output_function_range_equal_description_outputs
    (P : FinitePartialUnaryRangeProgram)
    (hfunctional : FinitePartialUnaryRangeProgram.OutputFunctional P) :
    Language.Equal
      (PartialRangeLanguage
        (FinitePartialUnaryRangeProgram.outputFunction P))
      (FinitePartialUnaryRangeProgram.descriptionOutputRange P) := by
  simpa [PartialRangeLanguage,
    FinitePartialUnaryRangeProgram.outputFunction,
    FinitePartialUnaryRangeProgram.descriptionOutputRange,
    FinitePartialUnaryRangeProgram.OutputFunctional]
    using
      Computability.FinitePartialUnaryRangeProgram.partialRange_outputFunction_equal_descriptionOutputRange
        P hfunctional

theorem concrete_finite_partial_unary_output_listing_partially_lists_description_outputs
    (P : FinitePartialUnaryRangeProgram)
    (hfunctional : FinitePartialUnaryRangeProgram.OutputFunctional P) :
    PartiallyListedBy
      (FinitePartialUnaryRangeProgram.outputListing P)
      (FinitePartialUnaryRangeProgram.descriptionOutputRange P) := by
  simpa [FinitePartialUnaryRangeProgram.outputListing,
    FinitePartialUnaryRangeProgram.descriptionOutputRange,
    FinitePartialUnaryRangeProgram.OutputFunctional]
    using!
      Computability.FinitePartialUnaryRangeProgram.outputListing_partiallyListedBy_descriptionOutputRange
        P hfunctional

theorem concrete_finite_partial_unary_description_output_range_compiled
    (P : FinitePartialUnaryRangeProgram)
    (hD : P.description.WellFormed)
    (hcomplete : FinitePartialUnaryRangeProgram.OutputComplete P)
    (hfunctional : FinitePartialUnaryRangeProgram.OutputFunctional P) :
    ConcreteCompiledPartialUnaryRange
      (FinitePartialUnaryRangeProgram.descriptionOutputRange P) := by
  simpa [ConcreteCompiledPartialUnaryRange,
    FinitePartialUnaryRangeProgram.descriptionOutputRange,
    FinitePartialUnaryRangeProgram.OutputComplete,
    FinitePartialUnaryRangeProgram.OutputFunctional]
    using
      Computability.FinitePartialUnaryRangeProgram.compiledPartialUnaryRange_descriptionOutputRange
        P hD hcomplete hfunctional

theorem concrete_finite_partial_unary_description_output_range_turing_computable
    (P : FinitePartialUnaryRangeProgram)
    (hD : P.description.WellFormed)
    (hcomplete : FinitePartialUnaryRangeProgram.OutputComplete P)
    (hfunctional : FinitePartialUnaryRangeProgram.OutputFunctional P) :
    ConcretePartialUnaryTuringComputableRange
      (FinitePartialUnaryRangeProgram.descriptionOutputRange P) :=
  concrete_compiled_partial_unary_range_has_turing_computable_range
    (concrete_finite_partial_unary_description_output_range_compiled
      P hD hcomplete hfunctional)

theorem concrete_finite_partial_unary_description_output_range_partially_listable
    (P : FinitePartialUnaryRangeProgram)
    (hD : P.description.WellFormed)
    (hcomplete : FinitePartialUnaryRangeProgram.OutputComplete P)
    (hfunctional : FinitePartialUnaryRangeProgram.OutputFunctional P) :
    PartiallyListable
      (FinitePartialUnaryRangeProgram.descriptionOutputRange P) :=
  concrete_compiled_partial_unary_range_is_partially_listable
    (concrete_finite_partial_unary_description_output_range_compiled
      P hD hcomplete hfunctional)

theorem concrete_finite_partial_unary_description_output_range_compiled_program_range
    (P : FinitePartialUnaryRangeProgram)
    (hD : P.description.WellFormed)
    (hcomplete : FinitePartialUnaryRangeProgram.OutputComplete P)
    (hfunctional : FinitePartialUnaryRangeProgram.OutputFunctional P) :
    ConcreteCompiledPartialUnaryFunctionProgramRange
      (FinitePartialUnaryRangeProgram.descriptionOutputRange P) := by
  simpa [ConcreteCompiledPartialUnaryFunctionProgramRange,
    FinitePartialUnaryRangeProgram.descriptionOutputRange,
    FinitePartialUnaryRangeProgram.OutputComplete,
    FinitePartialUnaryRangeProgram.OutputFunctional]
    using
      Computability.FinitePartialUnaryRangeProgram.compiledPartialUnaryFunctionProgramRange_descriptionOutputRange
        P hD hcomplete hfunctional

theorem concrete_finite_partial_unary_range_presentation_compiled_range
    (P : FinitePartialUnaryRangeProgram)
    {L : Language Bool}
    (h : ConcreteFinitePartialUnaryRangePresentsLanguage P L) :
    ConcreteCompiledPartialUnaryRange L :=
  concrete_compiled_partial_unary_range_of_equal
    (concrete_finite_partial_unary_description_output_range_compiled
      P h.left h.right.left h.right.right.left)
    h.right.right.right

theorem concrete_finite_partial_unary_range_presentation_compiled_program_range
    (P : FinitePartialUnaryRangeProgram)
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
    PartiallyListable L :=
  concrete_compiled_partial_unary_range_is_partially_listable
    (concrete_finite_partial_unary_range_language_compiled_range h)

/-!
## Range Extensionality

The closing lemmas transport range languages across pointwise function
equalities and language equivalence.
-/

theorem function_value_in_range (f : Word input -> Word output) (x : Word input) :
    f x ∈ RangeLanguage f :=
  range_mem x

theorem function_range_equal_of_pointwise
    {f g : Word input -> Word output}
    (hfg : forall x, f x = g x) :
    Language.Equal (RangeLanguage f) (RangeLanguage g) :=
  rangeLanguage_equal_of_pointwise hfg

theorem partial_function_range_equal_of_pointwise
    {f g : Word input -> Option (Word output)}
    (hfg : forall x, f x = g x) :
    Language.Equal
      (PartialRangeLanguage f) (PartialRangeLanguage g) :=
  partialRangeLanguage_equal_of_pointwise hfg

theorem computable_range_language_of_equal {L K : Language output}
    (h : RangeOfComputableFunction L) (hEq : Language.Equal L K) :
    RangeOfComputableFunction K :=
  rangeOfComputableFunction_of_equal h hEq

theorem unary_range_language_of_equal {L K : Language output}
    (h : RangeOfUnaryFunction L) (hEq : Language.Equal L K) :
    RangeOfUnaryFunction K :=
  rangeOfUnaryFunction_of_equal h hEq

theorem partial_unary_range_language_of_equal {L K : Language output}
    (h : PartialRangeOfUnaryFunction L) (hEq : Language.Equal L K) :
    PartialRangeOfUnaryFunction K :=
  partialRangeOfUnaryFunction_of_equal h hEq

end Section02
end Chapter05
end Book
end FoC
