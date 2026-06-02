import FoC.Computability.Enumerable
import FoC.Grammars.GeneralGrammar

namespace FoC
namespace Book
namespace Chapter05
namespace Section02

/-!
Book: Chapter 5, Section 5.2, Computability.
-/

open Languages
open Computability
open Grammars

-- Book: Chapter 5, Section 5.2, recursively enumerable languages.
def RecursivelyEnumerableLanguage (L : Language alpha) : Prop :=
  RecursivelyEnumerable L

-- Book: Chapter 5, Section 5.2, co-recursively enumerable languages.
def CoRecursivelyEnumerableLanguage (L : Language alpha) : Prop :=
  CoRecursivelyEnumerable L

-- Book: Chapter 5, Section 5.2, languages whose language and complement are
-- recursively enumerable.
def RecursivelyEnumerableLanguageWithComplement (L : Language alpha) : Prop :=
  RecursivelyEnumerableWithComplement L

-- Book: Chapter 5, Section 5.2, recursive languages.
def RecursiveLanguage (L : Language alpha) : Prop :=
  Recursive L

-- Book: Chapter 5, Section 5.2, finite-stage acceptance traces for RE
-- languages.
def LanguageAcceptanceTrace
    (trace : Word alpha -> Nat -> Prop)
    (L : Language alpha) : Prop :=
  AcceptanceTrace trace L

-- Book: Chapter 5, Section 5.2, paired acceptance traces for a language and
-- its complement.
def LanguageComplementaryAcceptanceTraces
    (accept reject : Word alpha -> Nat -> Prop)
    (L : Language alpha) : Prop :=
  ComplementaryAcceptanceTraces accept reject L

-- Book: Chapter 5, Section 5.2, a trace has hit by a bounded search stage.
def LanguageTraceHitsBy
    (trace : Word alpha -> Nat -> Prop)
    (w : Word alpha) (limit : Nat) : Prop :=
  TraceHitsBy trace w limit

-- Book: Chapter 5, Section 5.2, bounded dovetailing has found an accepting
-- or rejecting trace hit.
def LanguageDovetailSearchHit
    (accept reject : Word alpha -> Nat -> Prop)
    (w : Word alpha) (limit : Nat) : Prop :=
  ComplementaryTraceSearchHit accept reject w limit

-- Book: Chapter 5, Section 5.2, recursive languages are closed under complement.
theorem recursive_language_complement {L : Language alpha}
    (h : RecursiveLanguage L) : RecursiveLanguage (Language.Compl L) :=
  Computability.recursive_complement h

-- Book: Chapter 5, Section 5.2, if the complement is recursive, then so is
-- the original language.
theorem recursive_language_of_recursive_complement {L : Language alpha}
    (h : RecursiveLanguage (Language.Compl L)) : RecursiveLanguage L :=
  Computability.recursive_of_complement h

-- Book: Chapter 5, Section 5.2, recursiveness is equivalent for a language
-- and its complement.
theorem recursive_language_complement_iff {L : Language alpha} :
    RecursiveLanguage (Language.Compl L) <-> RecursiveLanguage L :=
  Computability.recursive_complement_iff

-- Book: Chapter 5, Section 5.2, recursive languages are extensional.
theorem recursive_language_of_equal {L K : Language alpha}
    (h : RecursiveLanguage L) (hEq : Language.Equal L K) :
    RecursiveLanguage K :=
  Computability.recursive_of_equal h hEq

-- Book: Chapter 5, Section 5.2, recursively enumerable languages are
-- extensional.
theorem recursively_enumerable_language_of_equal {L K : Language alpha}
    (h : RecursivelyEnumerableLanguage L) (hEq : Language.Equal L K) :
    RecursivelyEnumerableLanguage K :=
  Computability.recursivelyEnumerable_of_equal h hEq

-- Book: Chapter 5, Section 5.2, every recursively enumerable language has a
-- finite-stage acceptance trace.
theorem recursively_enumerable_language_has_acceptance_trace
    {L : Language alpha}
    (h : RecursivelyEnumerableLanguage L) :
    exists trace : Word alpha -> Nat -> Prop,
      LanguageAcceptanceTrace trace L :=
  Computability.recursivelyEnumerable_has_acceptanceTrace h

-- Book: Chapter 5, Section 5.2, RE plus co-RE supplies complementary finite
-- acceptance traces.
theorem re_and_co_re_have_complementary_acceptance_traces
    {L : Language alpha}
    (h : RecursivelyEnumerableLanguageWithComplement L) :
    exists accept reject : Word alpha -> Nat -> Prop,
      LanguageComplementaryAcceptanceTraces accept reject L :=
  Computability.recursivelyEnumerable_with_complement_has_complementaryTraces h

-- Book: Chapter 5, Section 5.2, an accepting trace hit is sound.
theorem complementary_trace_accept_sound
    {accept reject : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (h : LanguageComplementaryAcceptanceTraces accept reject L)
    {w : Word alpha} {n : Nat}
    (hn : accept w n) :
    w ∈ L :=
  Computability.complementaryAcceptanceTraces_accept_sound h hn

-- Book: Chapter 5, Section 5.2, a rejecting trace hit is sound.
theorem complementary_trace_reject_sound
    {accept reject : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (h : LanguageComplementaryAcceptanceTraces accept reject L)
    {w : Word alpha} {n : Nat}
    (hn : reject w n) :
    ¬ w ∈ L :=
  Computability.complementaryAcceptanceTraces_reject_sound h hn

-- Book: Chapter 5, Section 5.2, paired traces eventually give either an
-- accepting or rejecting finite hit on each input.
theorem complementary_traces_eventually_hit
    {accept reject : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (h : LanguageComplementaryAcceptanceTraces accept reject L)
    (w : Word alpha) :
    exists n : Nat, accept w n ∨ reject w n :=
  Computability.complementaryAcceptanceTraces_eventually_hits_classical h w

-- Book: Chapter 5, Section 5.2, bounded trace hits are monotone in the search
-- bound.
theorem language_trace_hit_mono
    {trace : Word alpha -> Nat -> Prop}
    {w : Word alpha} {m n : Nat}
    (hmn : m ≤ n)
    (h : LanguageTraceHitsBy trace w m) :
    LanguageTraceHitsBy trace w n :=
  Computability.traceHitsBy_mono hmn h

-- Book: Chapter 5, Section 5.2, an accepting bounded trace hit is sound.
theorem complementary_trace_accepts_by_sound
    {accept reject : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (h : LanguageComplementaryAcceptanceTraces accept reject L)
    {w : Word alpha} {limit : Nat}
    (hit : LanguageTraceHitsBy accept w limit) :
    w ∈ L :=
  Computability.complementaryTraceAcceptsBy_sound h hit

-- Book: Chapter 5, Section 5.2, a rejecting bounded trace hit is sound.
theorem complementary_trace_rejects_by_sound
    {accept reject : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (h : LanguageComplementaryAcceptanceTraces accept reject L)
    {w : Word alpha} {limit : Nat}
    (hit : LanguageTraceHitsBy reject w limit) :
    ¬ w ∈ L :=
  Computability.complementaryTraceRejectsBy_sound h hit

-- Book: Chapter 5, Section 5.2, accepting and rejecting bounded hits cannot
-- both occur for complementary traces.
theorem complementary_trace_search_no_conflict
    {accept reject : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (h : LanguageComplementaryAcceptanceTraces accept reject L)
    {w : Word alpha} {acceptLimit rejectLimit : Nat}
    (ha : LanguageTraceHitsBy accept w acceptLimit)
    (hr : LanguageTraceHitsBy reject w rejectLimit) :
    False :=
  Computability.complementaryTraceSearch_no_conflict h ha hr

-- Book: Chapter 5, Section 5.2, complementary traces eventually have a
-- bounded search stage with a hit.
theorem complementary_trace_search_eventually_hits_by
    {accept reject : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (h : LanguageComplementaryAcceptanceTraces accept reject L)
    (w : Word alpha) :
    exists limit : Nat, LanguageDovetailSearchHit accept reject w limit :=
  Computability.complementaryTraceSearch_eventually_hits_by h w

-- Book: Chapter 5, Section 5.2, complementary traces eventually classify
-- each input by a bounded search stage.
theorem complementary_trace_search_eventually_classifies
    {accept reject : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (h : LanguageComplementaryAcceptanceTraces accept reject L)
    (w : Word alpha) :
    exists limit : Nat,
      (LanguageTraceHitsBy accept w limit ∧ w ∈ L) ∨
        (LanguageTraceHitsBy reject w limit ∧ ¬ w ∈ L) :=
  Computability.complementaryTraceSearch_eventually_classifies h w

-- Book: Chapter 5, Section 5.2, RE plus co-RE gives the bounded-search core
-- used by the standard dovetailing proof.
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

-- Book: Chapter 5, Section 5.2, a stopped 0/1 decider gives complementary
-- finite output traces.
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

-- Book: Chapter 5, Section 5.2, a stopped 0/1 decider has a bounded output
-- search classification stage for every input.
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

-- Book: Chapter 5, Section 5.2, languages listed by a stream of words.
def LanguageListedBy (stream : Nat -> Word alpha) (L : Language alpha) : Prop :=
  ListedBy stream L

-- Book: Chapter 5, Section 5.2, listed languages are extensional.
theorem listed_language_of_equal {stream : Nat -> Word alpha}
    {L K : Language alpha}
    (h : LanguageListedBy stream L) (hEq : Language.Equal L K) :
    LanguageListedBy stream K :=
  listedBy_of_equal h hEq

-- Book: Chapter 5, Section 5.2, every listed word belongs to the listed language.
theorem listed_word_in_language {stream : Nat -> Word alpha} {L : Language alpha}
    (h : LanguageListedBy stream L) (n : Nat) :
    stream n ∈ L :=
  listed_word_mem h n

-- Book: Chapter 5, Section 5.2, language-listability vocabulary.
def LanguageListable (L : Language alpha) : Prop :=
  Listable L

-- Book: Chapter 5, Section 5.2, listability is extensional.
theorem listable_language_of_equal {L K : Language alpha}
    (h : LanguageListable L) (hEq : Language.Equal L K) :
    LanguageListable K :=
  listable_of_equal h hEq

-- Book: Chapter 5, Section 5.2, languages as ranges of functions.
def FunctionRangeLanguage (f : Word input -> Word output) : Language output :=
  RangeLanguage f

-- Book: Chapter 5, Section 5.2, a function value is in its range language.
theorem function_value_in_range (f : Word input -> Word output) (x : Word input) :
    f x ∈ FunctionRangeLanguage f :=
  range_mem x

-- Book: Chapter 5, Section 5.2, pointwise equal functions have the same range.
theorem function_range_equal_of_pointwise
    {f g : Word input -> Word output}
    (hfg : forall x, f x = g x) :
    Language.Equal (FunctionRangeLanguage f) (FunctionRangeLanguage g) :=
  rangeLanguage_equal_of_pointwise hfg

-- Book: Chapter 5, Section 5.2, computable-function range descriptions are
-- extensional.
theorem computable_range_language_of_equal {L K : Language output}
    (h : RangeOfComputableFunction L) (hEq : Language.Equal L K) :
    RangeOfComputableFunction K :=
  rangeOfComputableFunction_of_equal h hEq

-- Book: Chapter 5, Section 5.2, equivalence vocabulary for RE languages.
def AcceptableListingEquivalenceStatement (L : Language alpha) : Prop :=
  AcceptableListingEquivalence L

-- Book: Chapter 5, Section 5.2, equivalence vocabulary for computable ranges.
def AcceptableRangeEquivalenceStatement (L : Language alpha) : Prop :=
  AcceptableRangeEquivalence L

-- Book: Chapter 5, Section 5.2, general grammar generated languages.
def GeneralGrammarGeneratedLanguage (G : GeneralGrammar terminal nonterminal) :
    Language terminal :=
  GeneralGrammar.GeneratedLanguage G

-- Book: Chapter 5, Section 5.2, grammar/RE-language equivalence statement.
def GeneralGrammarAcceptabilityEquivalence (L : Language terminal) : Prop :=
  GeneralGrammar.Generated L <-> RecursivelyEnumerable L

/-!
The theorem equating general grammars with recursively enumerable languages is
recorded as an explicit statement shape.  The construction proof is deferred
until the formalization has enough machine-encoding and simulation
infrastructure.
-/

end Section02
end Chapter05
end Book
end FoC
