import FoC.Foundation.Sets
import FoC.Foundation.Finite
import FoC.Languages.Regular

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

The concrete alphabets below give the book's binary and a/b examples small
finite types, so later automata and grammar examples can state
membership facts with actual words.

The key modeling choice is extensional: a language is not a list of words, but
a predicate saying which words belong. This is why theorems about language
operations look like set-theoretic membership laws.
-/

open Foundation
open Languages

inductive Bit where
  | zero
  | one
deriving DecidableEq

inductive AB where
  | a
  | b
deriving DecidableEq

def BitAlphabet : FiniteType Bit where
  elems := [Bit.zero, Bit.one]
  complete := by
    intro x
    cases x <;> simp

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

Language operations are set operations on word predicates. The definitions of
union, intersection, complement, concatenation, singleton languages, and
Kleene star are unfolded here in the book's order.

Concatenation and Kleene star are the first genuinely language-specific
operations. Concatenation asks for a split of the word into a left part and a
right part; star asks for a finite list of pieces whose concatenation is the
word.
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

theorem language_concatenation_membership (L M : Language alpha) (w : Word alpha) :
    w ∈ Language.Concat L M <->
      exists x y, x ∈ L ∧ y ∈ M ∧ w = Word.Concat x y :=
  Language.mem_concat w L M

theorem kleene_star_contains_empty (L : Language alpha) :
    Word.Empty ∈ Language.Star L :=
  Language.star_empty_word L

theorem singleton_language_finite (w : Word alpha) :
    Language.Finite (Language.Singleton w) :=
  Language.singleton_finite w

/-!
## Diagonalization

The final theorem is the Cantor-style statement from the section: there is no
word-indexed listing of all languages over an alphabet. This is the language
version of the powerset diagonal argument from {module}`FoC.Foundation.Sets`.

Even when the alphabet is small, the set of all languages over that alphabet
is too large to be listed by words. The proof is the same diagonal idea as for
powersets: a proposed list misses the language that flips membership at each
listed word.
-/

theorem no_word_indexed_listing_of_all_languages
    (f : Word alpha -> Language alpha) :
    ¬ (forall L : Language alpha, exists w : Word alpha, Language.Equal (f w) L) :=
  FSet.cantor_no_surjective_powerset f

end Section01
end Chapter03
end Book
end FoC
