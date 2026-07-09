import FoC.Foundation.Countable
import FoC.Foundation.Functions
import FoC.Foundation.Cardinality
import FoC.Foundation.Rationals
import FoC.Foundation.DigitStreams
import FoC.Foundation.Reals
import FoC.Foundation.RealUncountability

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter02
namespace Section06

/-!
# Chapter 2, Section 2.6: Counting Past Infinity

This section formalizes the chapter's finite, countable, countably infinite,
and uncountable vocabulary. The reusable infrastructure comes from
{module}`FoC.Foundation.Countable`, {module}`FoC.Foundation.Cardinality`,
{module}`FoC.Foundation.DigitStreams`, and {module}`FoC.Foundation.Reals`.

The formalization separates three ideas that the textbook presents together:
explicit finite cardinality, encodings by natural numbers, and diagonal
arguments proving that some collections cannot be enumerated.

The first two ideas prove countability by building data: finite lists,
encodings, or staged enumerations. The diagonal arguments prove
uncountability by contradiction: given any proposed listing, construct an
object that differs from the listed object at its own index.
-/

open Foundation

/-!
## Finite, Infinite, and Countable Sets

The opening statements give basic examples: the empty set and singletons are
finite, while the natural numbers and even natural numbers are infinite yet
countable, hence countably infinite.  Every finite set is countable, matching
the book's definition of countable as "finite or countably infinite".
Exercise 11 is represented by closure of countability under union and by the
corresponding countably-infinite union statement, which the countably
infinite examples below can instantiate.

These declarations distinguish finite from countable. Finite sets have a
specific finite presentation, while countable sets only need an enumeration or
encoding by natural numbers.
-/

theorem empty_set_is_finite : FSet.Finite (FSet.Empty : FSet alpha) :=
  FSet.empty_finite

theorem singleton_set_is_finite (x : alpha) : FSet.Finite (FSet.Singleton x) :=
  FSet.singleton_finite x

theorem natural_numbers_countable : FSet.Countable (FSet.Univ : FSet Nat) :=
  FSet.nat_univ_countable

theorem even_natural_numbers_countable : FSet.Countable FSet.EvenNaturals :=
  FSet.even_naturals_countable

theorem natural_numbers_infinite : ¬ FSet.Finite (FSet.Univ : FSet Nat) :=
  FSet.nat_univ_not_finite

theorem even_natural_numbers_infinite : ¬ FSet.Finite FSet.EvenNaturals :=
  FSet.even_naturals_not_finite

theorem natural_numbers_countably_infinite :
    FSet.CountablyInfinite (FSet.Univ : FSet Nat) :=
  FSet.nat_univ_countably_infinite

theorem even_natural_numbers_countably_infinite :
    FSet.CountablyInfinite FSet.EvenNaturals :=
  FSet.even_naturals_countably_infinite

theorem finite_set_countable {A : FSet alpha}
    (hA : FSet.Finite A) : FSet.Countable A :=
  FSet.countable_of_finite hA

theorem union_of_countable_sets_countable {A B : FSet alpha}
    (hA : FSet.Countable A) (hB : FSet.Countable B) :
    FSet.Countable (FSet.Union A B) :=
  FSet.countable_union hA hB

theorem subset_of_countable_set_countable {A B : FSet alpha}
    (hAB : FSet.Subset A B) (hB : FSet.Countable B) :
    FSet.Countable A :=
  FSet.countable_subset_classical hAB hB

theorem union_of_countably_infinite_sets_countably_infinite {A B : FSet alpha}
    (hA : FSet.CountablyInfinite A) (hB : FSet.CountablyInfinite B) :
    FSet.CountablyInfinite (FSet.Union A B) :=
  FSet.countably_infinite_union hA hB

/-!
## Natural-Number Encodings

The next group records explicit encodings. Naturals are encoded directly,
integers use the project's integer code, and pairs of naturals are organized by
diagonals. This is the formal counterpart of the chapter's listing arguments.
-/

theorem natural_numbers_encodable : Countability.EncodableByNat Nat :=
  Countability.nat_encodable

theorem integers_encodable : Countability.EncodableByNat Int :=
  Countability.int_encodable

def natural_numbers_codec : Countability.NatCodec Nat :=
  Countability.NatCodec.nat

def integers_codec : Countability.NatCodec Int :=
  Countability.NatCodec.int

theorem codec_types_are_countable {alpha : Type u}
    (codec : Countability.NatCodec alpha) :
    FSet.Countable (FSet.Univ : FSet alpha) :=
  Countability.countable_univ_of_natCodec codec

theorem nat_pair_on_diagonal (a b : Nat) :
    (a, b) ∈ Countability.DiagonalList (a + b) :=
  Countability.pair_mem_diagonalList a b

theorem nat_pair_diagonal_length (s : Nat) :
    (Countability.DiagonalList s).length = s + 1 :=
  Countability.length_diagonalList s

/-!
### Pairs of Natural Numbers

Exercise 10 asks for the countability of the set of pairs of natural numbers.
The pair code is an injective encoding of pairs by natural numbers, and
searching for codes enumerates every pair.
-/

theorem natural_number_pairs_encodable :
    Countability.EncodableByNat (Nat × Nat) :=
  Countability.natPair_encodable

theorem natural_number_pairs_countable :
    FSet.Countable (FSet.Univ : FSet (Nat × Nat)) :=
  Countability.natPair_univ_countable

/-!
## Rational Representatives

Rational representatives are assigned finite stages by combining the natural
codes of numerator and denominator. The Lean statements make the diagonal
listing explicit: each representative has a code, the code is injective, and
the pair code appears on the expected diagonal.
-/

def RationalRepresentativeStage (s : Nat) : FSet Rational :=
  fun q => Countability.IntCode q.num + Countability.IntCode q.den = s

def RationalRepresentativeCode (q : Rational) : Nat × Nat :=
  (Countability.IntCode q.num, Countability.IntCode q.den)

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

theorem rational_representative_in_stage (q : Rational) :
    q ∈ RationalRepresentativeStage (Countability.IntCode q.num + Countability.IntCode q.den) :=
  rfl

theorem rational_representative_code_on_diagonal (q : Rational) :
    RationalRepresentativeCode q ∈
      Countability.DiagonalList ((RationalRepresentativeCode q).1 + (RationalRepresentativeCode q).2) :=
  Countability.pair_mem_diagonalList (RationalRepresentativeCode q).1 (RationalRepresentativeCode q).2

/-!
## Finite Cardinality Formulas

The cardinality statements cover the elementary finite cases, the sanity
properties that make cardinality well-defined, the book's counting segments,
and the cardinality laws of Theorem 2.8.

Exercise 5 is the well-definedness of cardinality: a set cannot have two
different cardinalities.  Cardinality also connects to finiteness in both
directions: a set with a cardinality is finite, and a finite set has some
cardinality.
-/

theorem empty_has_cardinality_zero :
    FSet.HasCardinality (FSet.Empty : FSet alpha) 0 :=
  FSet.empty_has_cardinality_zero

theorem singleton_has_cardinality_one (x : alpha) :
    FSet.HasCardinality (FSet.Singleton x) 1 :=
  FSet.singleton_has_cardinality_one x

theorem cardinality_respects_set_equality {A B : FSet alpha} {n : Nat}
    (hAB : FSet.Equal A B) (hA : FSet.HasCardinality A n) :
    FSet.HasCardinality B n :=
  FSet.hasCardinality_of_equal hAB hA

theorem cardinality_well_defined {A : FSet alpha} {m n : Nat}
    (hm : FSet.HasCardinality A m) (hn : FSet.HasCardinality A n) :
    m = n :=
  FSet.hasCardinality_unique_classical hm hn

theorem finite_of_has_cardinality {A : FSet alpha} {n : Nat}
    (h : FSet.HasCardinality A n) : FSet.Finite A :=
  FSet.finite_of_hasCardinality h

theorem finite_set_has_cardinality {A : FSet alpha}
    (h : FSet.Finite A) : exists n, FSet.HasCardinality A n :=
  FSet.exists_hasCardinality_of_finite_classical h

theorem subset_of_finite_set_finite {A B : FSet alpha}
    (hAB : FSet.Subset A B) (hB : FSet.Finite B) :
    FSet.Finite A :=
  FSet.finite_subset_classical hAB hB

/-!
### Counting Segments

Theorem 2.6 concerns the counting segments {lit}`N_n = {0, 1, ..., n-1}`:
each has cardinality {lit}`n`, and segments of different sizes admit no
one-to-one correspondence.
-/

theorem counting_segment_has_cardinality (n : Nat) :
    FSet.HasCardinality (FSet.Segment n) n :=
  FSet.segment_hasCardinality n

theorem no_correspondence_between_distinct_segments {m n : Nat}
    (hmn : m ≠ n) (f : Nat -> Nat) :
    ¬ ((forall x, x ∈ FSet.Segment m -> f x ∈ FSet.Segment n) ∧
        (forall x y, x ∈ FSet.Segment m -> y ∈ FSet.Segment m ->
          f x = f y -> x = y) ∧
        (forall y, y ∈ FSet.Segment n ->
          exists x, x ∈ FSet.Segment m ∧ f x = y)) :=
  FSet.no_segment_correspondence_of_ne hmn f

/-!
### Set-Level Cardinality Laws

Theorem 2.8 is stated for the sets themselves: the cross product of finite
sets multiplies cardinalities, and the union of finite sets satisfies
inclusion-exclusion.  The disjoint case and the subtraction-free additive
form are recorded separately.
-/

theorem product_of_finite_sets_cardinality {A : FSet alpha} {B : FSet beta}
    {m n : Nat}
    (hA : FSet.HasCardinality A m) (hB : FSet.HasCardinality B n) :
    FSet.HasCardinality (FSet.Product A B) (m * n) :=
  FSet.product_hasCardinality hA hB

theorem union_of_finite_sets_cardinality {A B : FSet alpha} {m n k : Nat}
    (hA : FSet.HasCardinality A m) (hB : FSet.HasCardinality B n)
    (hI : FSet.HasCardinality (FSet.Inter A B) k) :
    FSet.HasCardinality (FSet.Union A B) (m + n - k) :=
  FSet.union_hasCardinality_inclusion_exclusion_classical hA hB hI

theorem union_plus_intersection_cardinality {A B : FSet alpha}
    {m n u k : Nat}
    (hA : FSet.HasCardinality A m) (hB : FSet.HasCardinality B n)
    (hU : FSet.HasCardinality (FSet.Union A B) u)
    (hI : FSet.HasCardinality (FSet.Inter A B) k) :
    u + k = m + n :=
  FSet.union_add_inter_cardinality_classical hA hB hU hI

theorem disjoint_union_of_finite_sets_cardinality {A B : FSet alpha}
    {m n : Nat}
    (hA : FSet.HasCardinality A m) (hB : FSet.HasCardinality B n)
    (hAB : FSet.Disjoint A B) :
    FSet.HasCardinality (FSet.Union A B) (m + n) :=
  FSet.union_hasCardinality_of_disjoint_classical hA hB hAB

/-!
### List Models

The remaining formulas of Theorem 2.8 are stated on the list models.  The
completeness and duplicate-freedom lemmas make the lengths honest counts: the
sublist model enumerates each sublist of a duplicate-free enumeration exactly
once, and the tuple model enumerates each length-{lit}`n` tuple of choices
exactly once.
-/

theorem list_product_cardinality (xs : List alpha) (ys : List beta) :
    (ListCard.Pairs xs ys).length = xs.length * ys.length :=
  ListCard.length_pairs xs ys

theorem list_disjoint_union_cardinality (xs ys : List alpha) :
    (xs ++ ys).length = xs.length + ys.length :=
  ListCard.length_append xs ys

theorem union_cardinality_by_parts (leftOnly both rightOnly : Nat) :
    leftOnly + both + rightOnly =
      (leftOnly + both) + (both + rightOnly) - both :=
  ListCard.union_cardinality_by_parts leftOnly both rightOnly

theorem list_powerset_cardinality (xs : List alpha) :
    (ListCard.Sublists xs).length = 2 ^ xs.length :=
  ListCard.length_sublists xs

theorem list_powerset_complete {xs l : List alpha} :
    l ∈ ListCard.Sublists xs <-> l.Sublist xs :=
  ListCard.mem_sublists

theorem list_powerset_duplicate_free {xs : List alpha} (h : xs.Nodup) :
    (ListCard.Sublists xs).Nodup :=
  ListCard.sublists_nodup h

theorem list_function_space_cardinality (choices : List alpha) (domainSize : Nat) :
    (ListCard.Tuples choices domainSize).length = choices.length ^ domainSize :=
  ListCard.length_tuples choices domainSize

theorem list_function_space_complete {choices : List alpha} {n : Nat}
    {l : List alpha} :
    l ∈ ListCard.Tuples choices n <->
      l.length = n ∧ forall x, x ∈ l -> x ∈ choices :=
  ListCard.mem_tuples

theorem list_function_space_duplicate_free {choices : List alpha}
    (h : choices.Nodup) (n : Nat) :
    (ListCard.Tuples choices n).Nodup :=
  ListCard.tuples_nodup h n

/-!
## Cantor's Theorem

Cantor's argument appears as a no-surjection theorem from a type into its
powerset. The bijection version follows because a bijection would in particular
be surjective.

The diagonal set contains exactly those elements that are not in their own
image under the proposed map. That set cannot be equal to any listed image,
which rules out a surjection.
-/

theorem cantor_no_one_to_one_correspondence_with_powerset
    (f : alpha -> FSet alpha) :
    ¬ (forall A : FSet alpha, exists x : alpha, FSet.Equal (f x) A) :=
  FSet.cantor_no_surjective_powerset f

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

/-!
## Reals, Rationals, and Uncountability

The final group connects diagonal digit streams to real-number uncountability.
Rationals and embedded rational reals are countable, while the full real line
and the irrational reals are uncountable.

This is the formal version of the book's contrast: rationals can be listed by
diagonalizing numerator-denominator codes, but digit streams and real numbers
cannot be exhausted by a single sequence.
-/

theorem binary_digit_streams_uncountable :
    FSet.Uncountable (FSet.Univ : FSet DigitStream) :=
  DigitStream.uncountable_univ

theorem quotient_rationals_countable :
    FSet.Countable (FSet.Univ : FSet QRat) :=
  QRat.countable_univ

theorem embedded_rational_reals_countable :
    FSet.Countable Real.rationalSet :=
  Real.rationalSet_countable

theorem real_uncountable_from_digit_stream_embedding
    (embed : DigitStream -> Real) (hembed : Fn.Injective embed) :
    FSet.Uncountable (FSet.Univ : FSet Real) :=
  Real.uncountable_univ_of_digitStream_injective embed hembed

theorem real_numbers_uncountable :
    FSet.Uncountable (FSet.Univ : FSet Real) :=
  Real.uncountable_univ

theorem irrational_real_numbers_uncountable :
    FSet.Uncountable Real.irrationalSet :=
  Real.irrationalSet_uncountable

theorem uncountable_complement_of_countable_subset {X K : FSet alpha}
    (hX : FSet.Uncountable X) (hK : FSet.Countable K)
    (hKX : FSet.Subset K X) :
    FSet.Uncountable (FSet.Diff X K) :=
  FSet.uncountable_diff_countable_subset hX hK hKX

end Section06
end Chapter02
end Book
end FoC
