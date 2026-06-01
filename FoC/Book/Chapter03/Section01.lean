import FoC.Foundation.Sets
import FoC.Foundation.Finite
import FoC.Languages.Regular

namespace FoC
namespace Book
namespace Chapter03
namespace Section01

/-!
Book: Chapter 3, Section 3.1, Languages.
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

-- Book: Chapter 3, Section 3.1, strings are finite words over an alphabet.
theorem word_length_definition (w : Word alpha) :
    Word.Length w = w.length :=
  rfl

-- Book: Chapter 3, Section 3.1, concatenation is associative.
theorem word_concatenation_associative (x y z : Word alpha) :
    Word.Concat (Word.Concat x y) z = Word.Concat x (Word.Concat y z) :=
  Word.concat_assoc x y z

-- Book: Chapter 3, Section 3.1, the empty string has length zero.
theorem empty_string_length : Word.Length (Word.Empty : Word alpha) = 0 :=
  Word.length_empty

-- Book: Chapter 3, Section 3.1, the empty string reverses to itself.
theorem empty_string_reverse : Word.Reverse (Word.Empty : Word alpha) = Word.Empty :=
  Word.reverse_empty

-- Book: Chapter 3, Section 3.1, empty string is a left identity for concatenation.
theorem empty_string_concat_left (w : Word alpha) :
    Word.Concat Word.Empty w = w :=
  Word.concat_empty_left w

-- Book: Chapter 3, Section 3.1, empty string is a right identity for concatenation.
theorem empty_string_concat_right (w : Word alpha) :
    Word.Concat w Word.Empty = w :=
  Word.concat_empty_right w

-- Book: Chapter 3, Section 3.1, Definition 3.1.
theorem language_membership_definition (L : Language alpha) (w : Word alpha) :
    w ∈ L <-> L w :=
  Iff.rfl

-- Book: Chapter 3, Section 3.1, language union.
theorem language_union_membership (L M : Language alpha) (w : Word alpha) :
    w ∈ Language.Union L M <-> w ∈ L ∨ w ∈ M :=
  Language.mem_union w L M

-- Book: Chapter 3, Section 3.1, language intersection.
theorem language_intersection_membership (L M : Language alpha) (w : Word alpha) :
    w ∈ Language.Inter L M <-> w ∈ L ∧ w ∈ M :=
  Language.mem_inter w L M

-- Book: Chapter 3, Section 3.1, language complement.
theorem language_complement_membership (L : Language alpha) (w : Word alpha) :
    w ∈ Language.Compl L <-> ¬ w ∈ L :=
  Language.mem_compl w L

-- Book: Chapter 3, Section 3.1, language concatenation.
theorem language_concatenation_membership (L M : Language alpha) (w : Word alpha) :
    w ∈ Language.Concat L M <->
      exists x y, x ∈ L ∧ y ∈ M ∧ w = Word.Concat x y :=
  Language.mem_concat w L M

-- Book: Chapter 3, Section 3.1, Kleene closure contains the empty string.
theorem kleene_star_contains_empty (L : Language alpha) :
    Word.Empty ∈ Language.Star L :=
  Language.star_empty_word L

-- Book: Chapter 3, Section 3.1, singleton language is finite.
theorem singleton_language_finite (w : Word alpha) :
    Language.Finite (Language.Singleton w) :=
  Language.singleton_finite w

-- Book: Chapter 3, Section 3.1, Cantor-style diagonal form of Theorem 3.1.
theorem no_word_indexed_listing_of_all_languages
    (f : Word alpha -> Language alpha) :
    ¬ (forall L : Language alpha, exists w : Word alpha, Language.Equal (f w) L) :=
  FSet.cantor_no_surjective_powerset f

end Section01
end Chapter03
end Book
end FoC
