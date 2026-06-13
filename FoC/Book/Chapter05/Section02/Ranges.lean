import FoC.Book.Chapter05.Section02.MachineCompiler

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter05
namespace Section02

/-!
# Section 5.2 listings and ranges
-/

open Languages
open Computability
open Grammars

universe u v

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


end Section02
end Chapter05
end Book
end FoC
