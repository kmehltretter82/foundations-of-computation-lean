import FoC.Foundation.Countable
import FoC.Foundation.Functions
import FoC.Foundation.Cardinality
import FoC.Foundation.Rationals

namespace FoC
namespace Book
namespace Chapter02
namespace Section06

/-!
Book: Chapter 2, Section 2.6, Counting Past Infinity.
-/

open Foundation

-- Book: Chapter 2, Section 2.6, finite sets by explicit enumeration.
theorem empty_set_is_finite : FSet.Finite (FSet.Empty : FSet alpha) :=
  FSet.empty_finite

-- Book: Chapter 2, Section 2.6, singleton sets are finite.
theorem singleton_set_is_finite (x : alpha) : FSet.Finite (FSet.Singleton x) :=
  FSet.singleton_finite x

-- Book: Chapter 2, Section 2.6, natural numbers are countable.
theorem natural_numbers_countable : FSet.Countable (FSet.Univ : FSet Nat) :=
  FSet.nat_univ_countable

-- Book: Chapter 2, Section 2.6, even natural numbers are countable.
theorem even_natural_numbers_countable : FSet.Countable FSet.EvenNaturals :=
  FSet.even_naturals_countable

-- Book: Chapter 2, Section 2.6, natural numbers are encodable by natural numbers.
theorem natural_numbers_encodable : Countability.EncodableByNat Nat :=
  Countability.nat_encodable

-- Book: Chapter 2, Section 2.6, integers are countable by an explicit code.
theorem integers_encodable : Countability.EncodableByNat Int :=
  Countability.int_encodable

-- Book: Chapter 2, Section 2.6, every pair of natural numbers appears on a diagonal.
theorem nat_pair_on_diagonal (a b : Nat) :
    (a, b) ∈ Countability.DiagonalList (a + b) :=
  Countability.pair_mem_diagonalList a b

-- Book: Chapter 2, Section 2.6, each diagonal for Nat x Nat is finite.
theorem nat_pair_diagonal_length (s : Nat) :
    (Countability.DiagonalList s).length = s + 1 :=
  Countability.length_diagonalList s

def RationalRepresentativeStage (s : Nat) : FSet Rational :=
  fun q => Countability.IntCode q.num + Countability.IntCode q.den = s

def RationalRepresentativeCode (q : Rational) : Nat × Nat :=
  (Countability.IntCode q.num, Countability.IntCode q.den)

-- Book: Chapter 2, Section 2.6, rational representatives have injective pair codes.
theorem rational_representative_code_injective :
    Fn.Injective RationalRepresentativeCode := by
  intro q r h
  cases q with
  | mk qnum qden qhden =>
      cases r with
      | mk rnum rden rhden =>
          simp [RationalRepresentativeCode] at h
          have hnum : qnum = rnum := Countability.intCode_injective h.left
          have hden : qden = rden := Countability.intCode_injective h.right
          cases hnum
          cases hden
          rfl

-- Book: Chapter 2, Section 2.6, rational representatives appear in finite-code stages.
theorem rational_representative_in_stage (q : Rational) :
    q ∈ RationalRepresentativeStage (Countability.IntCode q.num + Countability.IntCode q.den) :=
  rfl

-- Book: Chapter 2, Section 2.6, rational representative codes appear on diagonals.
theorem rational_representative_code_on_diagonal (q : Rational) :
    RationalRepresentativeCode q ∈
      Countability.DiagonalList ((RationalRepresentativeCode q).1 + (RationalRepresentativeCode q).2) :=
  Countability.pair_mem_diagonalList (RationalRepresentativeCode q).1 (RationalRepresentativeCode q).2

-- Book: Chapter 2, Section 2.6, empty finite set has cardinality zero.
theorem empty_has_cardinality_zero :
    FSet.HasCardinality (FSet.Empty : FSet alpha) 0 :=
  FSet.empty_has_cardinality_zero

-- Book: Chapter 2, Section 2.6, singleton finite set has cardinality one.
theorem singleton_has_cardinality_one (x : alpha) :
    FSet.HasCardinality (FSet.Singleton x) 1 :=
  FSet.singleton_has_cardinality_one x

-- Book: Chapter 2, Section 2.6, cardinality is well-defined for equal sets.
theorem cardinality_respects_set_equality {A B : FSet alpha} {n : Nat}
    (hAB : FSet.Equal A B) (hA : FSet.HasCardinality A n) :
    FSet.HasCardinality B n :=
  FSet.hasCardinality_of_equal hAB hA

-- Book: Chapter 2, Section 2.6, product cardinality.
theorem list_product_cardinality (xs : List alpha) (ys : List beta) :
    (ListCard.Pairs xs ys).length = xs.length * ys.length :=
  ListCard.length_pairs xs ys

-- Book: Chapter 2, Section 2.6, disjoint-union cardinality.
theorem list_disjoint_union_cardinality (xs ys : List alpha) :
    (xs ++ ys).length = xs.length + ys.length :=
  ListCard.length_append xs ys

-- Book: Chapter 2, Section 2.6, inclusion-exclusion cardinality by disjoint parts.
theorem union_cardinality_by_parts (leftOnly both rightOnly : Nat) :
    leftOnly + both + rightOnly =
      (leftOnly + both) + (both + rightOnly) - both :=
  ListCard.union_cardinality_by_parts leftOnly both rightOnly

-- Book: Chapter 2, Section 2.6, powerset cardinality.
theorem list_powerset_cardinality (xs : List alpha) :
    (ListCard.Sublists xs).length = 2 ^ xs.length :=
  ListCard.length_sublists xs

-- Book: Chapter 2, Section 2.6, finite function-space cardinality.
theorem list_function_space_cardinality (choices : List alpha) (domainSize : Nat) :
    (ListCard.Tuples choices domainSize).length = choices.length ^ domainSize :=
  ListCard.length_tuples choices domainSize

-- Book: Chapter 2, Section 2.6, Theorem: no set has the cardinality of its powerset.
theorem cantor_no_one_to_one_correspondence_with_powerset
    (f : alpha -> FSet alpha) :
    ¬ (forall A : FSet alpha, exists x : alpha, FSet.Equal (f x) A) :=
  FSet.cantor_no_surjective_powerset f

-- Book: Chapter 2, Section 2.6, no bijective function reaches the powerset.
theorem cantor_no_bijection_with_powerset (f : alpha -> FSet alpha) :
    ¬ Fn.Bijective f := by
  intro hf
  apply FSet.cantor_no_surjective_powerset f
  intro A
  cases hf.right A with
  | intro x hx =>
      exists x
      rw [hx]
      exact FSet.equal_refl A

end Section06
end Chapter02
end Book
end FoC
