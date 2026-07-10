import FoC.Languages.Language
import FoC.Languages.WordCountable

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter03
namespace Section01

/-!
# Chapter 3, Section 3.1: Languages

This section starts the formal language part of the book. Words are finite
lists over an alphabet, and a language is represented extensionally as a
predicate on words. The reusable vocabulary is developed in
{module}`FoC.Languages.Words`, {module}`FoC.Languages.Language`, and
{module}`FoC.Foundation.Finite`.

Unlike the textbook definition, the core Lean vocabulary does not require every
alphabet type to be finite or nonempty. The binary and a/b alphabets below are
finite examples; later automata and regular-expression theorems add explicit
finite alphabet data when a construction needs to enumerate symbols.

The concrete alphabet types below give the book's binary and a/b examples
small finite types, so later automata and grammar examples can state
membership facts with actual words. The accompanying witnesses
{lit}`BitAlphabet` and {lit}`ABAlphabet` record the book's convention that these
alphabets are finite. The automata-to-expression API and later chapter bridges
accept these witnesses directly when alphabet enumeration is required.

The key modeling choice is extensional: a language is not a list of words, but
a predicate saying which words belong. This is why theorems about language
operations look like set-theoretic membership laws.
-/

open Foundation
open Languages

/-- The binary alphabet used by the book's automata examples. -/
inductive Bit where
  | zero
  | one
deriving DecidableEq

/-- The two-symbol alphabet used by the book's regular-language examples. -/
inductive AB where
  | a
  | b
deriving DecidableEq

/-- A finite witness for the binary alphabet. -/
def BitAlphabet : FiniteType Bit where
  elems := [Bit.zero, Bit.one]
  complete := by
    intro x
    cases x <;> simp

/-- A finite witness for the two-symbol alphabet. -/
def ABAlphabet : FiniteType AB where
  elems := [AB.a, AB.b]
  complete := by
    intro x
    cases x <;> simp

/-!
## Words

The first statements record the algebra of finite strings: length, the empty
word, reverse, and concatenation. The formal versions are wrappers around the
general word lemmas used throughout the rest of the project.
-/

theorem word_length_definition (w : Word alpha) :
    Word.Length w = w.length :=
  rfl

theorem word_concatenation_associative (x y z : Word alpha) :
    Word.Concat (Word.Concat x y) z = Word.Concat x (Word.Concat y z) :=
  Word.concat_assoc x y z

theorem empty_string_length : Word.Length (Word.Empty : Word alpha) = 0 :=
  Word.length_empty

theorem empty_string_reverse : Word.Reverse (Word.Empty : Word alpha) = Word.Empty :=
  Word.reverse_empty

theorem empty_string_concat_left (w : Word alpha) :
    Word.Concat Word.Empty w = w :=
  Word.concat_empty_left w

theorem empty_string_concat_right (w : Word alpha) :
    Word.Concat w Word.Empty = w :=
  Word.concat_empty_right w

/-!
## Languages

Language operations are set operations on word predicates. The membership
lemmas below unfold the definitions of union, intersection, complement,
difference, concatenation, singleton languages, and Kleene star in the book's
order.

Concatenation and Kleene star are the first genuinely language-specific
operations. Concatenation asks for a split of the word into a left part and a
right part; star asks for a finite list of pieces whose concatenation is the
word. The book instead introduces the star of a language as the union
{lit}`S^0 ∪ S^1 ∪ S^2 ∪ ...` of concatenation powers; the power membership
lemmas and {lit}`kleene_star_membership` below record that the two
presentations agree.
-/

theorem language_membership_definition (L : Language alpha) (w : Word alpha) :
    w ∈ L <-> L w :=
  Iff.rfl

theorem language_union_membership (L M : Language alpha) (w : Word alpha) :
    w ∈ Language.Union L M <-> w ∈ L ∨ w ∈ M :=
  Language.mem_union w L M

theorem language_intersection_membership (L M : Language alpha) (w : Word alpha) :
    w ∈ Language.Inter L M <-> w ∈ L ∧ w ∈ M :=
  Language.mem_inter w L M

theorem language_complement_membership (L : Language alpha) (w : Word alpha) :
    w ∈ Language.Compl L <-> ¬ w ∈ L :=
  Language.mem_compl w L

theorem language_difference_membership (L M : Language alpha) (w : Word alpha) :
    w ∈ Language.Diff L M <-> w ∈ L ∧ ¬ w ∈ M :=
  Language.mem_diff w L M

theorem language_concatenation_membership (L M : Language alpha) (w : Word alpha) :
    w ∈ Language.Concat L M <->
      exists x y, x ∈ L ∧ y ∈ M ∧ w = Word.Concat x y :=
  Language.mem_concat w L M

theorem singleton_language_membership (x w : Word alpha) :
    w ∈ Language.Singleton x <-> w = x :=
  Language.mem_singleton w x

theorem language_power_zero_membership (L : Language alpha) (w : Word alpha) :
    w ∈ Language.Power L 0 <-> w = Word.Empty :=
  Language.mem_power_zero w L

theorem language_power_succ_membership (L : Language alpha) (n : Nat) (w : Word alpha) :
    w ∈ Language.Power L (n + 1) <->
      exists x y, x ∈ L ∧ y ∈ Language.Power L n ∧ w = Word.Concat x y :=
  Language.mem_power_succ w L n

theorem kleene_star_membership (L : Language alpha) (w : Word alpha) :
    w ∈ Language.Star L <-> exists n, w ∈ Language.Power L n :=
  Language.mem_star_iff_power w L

theorem language_union_idempotent (L : Language alpha) :
    Language.Equal (Language.Union L L) L :=
  FoC.Foundation.FSet.union_idempotent L

theorem language_intersection_idempotent (L : Language alpha) :
    Language.Equal (Language.Inter L L) L :=
  FoC.Foundation.FSet.inter_idempotent L

theorem language_union_absorption (L M : Language alpha) :
    Language.Equal (Language.Union L (Language.Inter L M)) L :=
  FoC.Foundation.FSet.union_absorption L M

theorem language_intersection_absorption (L M : Language alpha) :
    Language.Equal (Language.Inter L (Language.Union L M)) L :=
  FoC.Foundation.FSet.inter_absorption L M

theorem language_difference_as_intersection_with_complement
    (L M : Language alpha) :
    Language.Equal (Language.Diff L M) (Language.Inter L (Language.Compl M)) :=
  Language.diff_as_inter_compl L M

theorem language_concat_with_empty_language_left (L : Language alpha) :
    Language.Equal (Language.Concat Language.Empty L) Language.Empty :=
  Language.concat_empty_language_left L

theorem language_concat_with_empty_language_right (L : Language alpha) :
    Language.Equal (Language.Concat L Language.Empty) Language.Empty :=
  Language.concat_empty_language_right L

theorem language_concat_with_epsilon_left (L : Language alpha) :
    Language.Equal (Language.Concat (Language.Singleton Word.Empty) L) L :=
  Language.concat_epsilon_left L

theorem language_concat_with_epsilon_right (L : Language alpha) :
    Language.Equal (Language.Concat L (Language.Singleton Word.Empty)) L :=
  Language.concat_epsilon_right L

theorem language_reverse_twice (L : Language alpha) :
    Language.Equal (Language.Reverse (Language.Reverse L)) L :=
  Language.reverse_reverse L

theorem kleene_star_contains_empty (L : Language alpha) :
    Word.Empty ∈ Language.Star L :=
  Language.star_empty_word L

theorem singleton_language_finite (w : Word alpha) :
    Language.Finite (Language.Singleton w) :=
  FoC.Foundation.FSet.singleton_finite w

/-!
## Countability and Diagonalization

Words over a finite nonempty alphabet are countably infinite. Cantor's
diagonal argument then proves the book's theorem that the collection of all
languages over that alphabet is uncountable. The word-indexed formulation is
also retained as the direct powerset obstruction.

Even when the alphabet is small, the set of all languages over that alphabet
is too large to be listed by words. The proof is the same diagonal idea as for
powersets: a proposed list misses the language that flips membership at each
listed word.
-/

/-- Words over a finite nonempty alphabet are countably infinite. -/
theorem words_over_finite_nonempty_alphabet_countably_infinite
    (alphabet : FiniteType alpha) (a : alpha) :
    FSet.CountablyInfinite (FSet.Univ : FSet (Word alpha)) :=
  Word.univ_countablyInfinite alphabet a

/-- The set of all languages over a finite nonempty alphabet is uncountable. -/
theorem languages_over_finite_nonempty_alphabet_uncountable
    (alphabet : FiniteType alpha) (a : alpha) :
    FSet.Uncountable (FSet.Univ : FSet (Language alpha)) := by
  change FSet.Uncountable (FSet.Univ : FSet (FSet (Word alpha)))
  exact FSet.univ_fset_uncountable_of_countablyInfinite
    (Word.univ_countablyInfinite alphabet a)

theorem no_word_indexed_listing_of_all_languages
    (f : Word alpha -> Language alpha) :
    ¬ (forall L : Language alpha, exists w : Word alpha, Language.Equal (f w) L) :=
  FSet.cantor_no_surjective_powerset f

end Section01
end Chapter03
end Book
end FoC
