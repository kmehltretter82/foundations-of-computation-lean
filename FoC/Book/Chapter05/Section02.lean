import FoC.Computability.Enumerable
import FoC.Grammars.GeneralGrammar

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
The reusable modules are {module}`FoC.Computability.Enumerable` and
{module}`FoC.Grammars.GeneralGrammar`.

The guiding distinction is total decision versus semi-decision. Recursive
languages have deciders. Recursively enumerable languages have recognizers or
listings: members eventually appear, but nonmembers may never be ruled out.
-/

open Languages
open Computability
open Grammars

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

theorem listed_language_of_equal {stream : Nat -> Word alpha}
    {L K : Language alpha}
    (h : LanguageListedBy stream L) (hEq : Language.Equal L K) :
    LanguageListedBy stream K :=
  listedBy_of_equal h hEq

theorem listed_word_in_language {stream : Nat -> Word alpha} {L : Language alpha}
    (h : LanguageListedBy stream L) (n : Nat) :
    stream n ∈ L :=
  listed_word_mem h n

def LanguageListable (L : Language alpha) : Prop :=
  Listable L

def UnaryInputString (n : Nat) : Word Unit :=
  UnaryInputWord n

theorem listable_language_of_equal {L K : Language alpha}
    (h : LanguageListable L) (hEq : Language.Equal L K) :
    LanguageListable K :=
  listable_of_equal h hEq

def FunctionRangeLanguage (f : Word input -> Word output) : Language output :=
  RangeLanguage f

def RangeOfUnaryStringFunction (L : Language output) : Prop :=
  RangeOfUnaryFunction L

def ListingAsUnaryStringFunction (stream : Nat -> Word output) :
    Word Unit -> Word output :=
  ListingAsUnaryFunction stream

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

theorem listed_language_range_of_unary_function
    {stream : Nat -> Word output} {L : Language output}
    (h : LanguageListedBy stream L) :
    Language.Equal
      (FunctionRangeLanguage (ListingAsUnaryStringFunction stream)) L :=
  Computability.listedBy_rangeLanguage_listingAsUnaryFunction h

theorem listable_language_has_unary_range_function
    {L : Language output}
    (h : LanguageListable L) :
    exists f : Word Unit -> Word output,
      Language.Equal (FunctionRangeLanguage f) L :=
  Computability.listable_has_unary_range_function h

theorem listable_language_range_of_unary_string_function
    {L : Language output}
    (h : LanguageListable L) :
    RangeOfUnaryStringFunction L :=
  Computability.listable_rangeOfUnaryFunction h

theorem unary_string_function_range_is_listable
    {L : Language output}
    (h : RangeOfUnaryStringFunction L) :
    LanguageListable L :=
  Computability.rangeOfUnaryFunction_listable h

theorem listable_language_iff_range_of_unary_string_function
    (L : Language output) :
    LanguageListable L <-> RangeOfUnaryStringFunction L :=
  Computability.listable_iff_rangeOfUnaryFunction L

theorem function_value_in_range (f : Word input -> Word output) (x : Word input) :
    f x ∈ FunctionRangeLanguage f :=
  range_mem x

theorem function_range_equal_of_pointwise
    {f g : Word input -> Word output}
    (hfg : forall x, f x = g x) :
    Language.Equal (FunctionRangeLanguage f) (FunctionRangeLanguage g) :=
  rangeLanguage_equal_of_pointwise hfg

theorem computable_range_language_of_equal {L K : Language output}
    (h : RangeOfComputableFunction L) (hEq : Language.Equal L K) :
    RangeOfComputableFunction K :=
  rangeOfComputableFunction_of_equal h hEq

theorem unary_range_language_of_equal {L K : Language output}
    (h : RangeOfUnaryStringFunction L) (hEq : Language.Equal L K) :
    RangeOfUnaryStringFunction K :=
  rangeOfUnaryFunction_of_equal h hEq

def AcceptableListingEquivalenceStatement (L : Language alpha) : Prop :=
  AcceptableListingEquivalence L

def AcceptableRangeEquivalenceStatement (L : Language alpha) : Prop :=
  AcceptableRangeEquivalence L

/-!
## General Grammars and RE Languages

The final definitions relate unrestricted grammar generation to recursive
enumerability, then state the recursive-language equivalence for a language
and its complement under those construction principles.

The formalization records the theorem shape rather than constructing a
universal interpreter here: if general grammars and recognizers are known to
match, then recursive languages are exactly those whose language and complement
are both generated by finite general grammars.
-/

def GeneralGrammarGeneratedLanguage (G : GeneralGrammar terminal nonterminal) :
    Language terminal :=
  GeneralGrammar.GeneratedLanguage G

def GeneralGrammarAcceptabilityEquivalence (L : Language terminal) : Prop :=
  GeneralGrammar.Generated L <-> RecursivelyEnumerable L

def GeneralGrammarPairGenerated (L : Language terminal) : Prop :=
  GeneralGrammar.Generated L ∧ GeneralGrammar.Generated (Language.Compl L)

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
