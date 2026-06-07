import FoC.Foundation.Arithmetic
import FoC.Foundation.Integers
import FoC.Foundation.Rationals
import FoC.Foundation.Reals
import FoC.Book.Chapter01.Section01
import FoC.Book.Chapter01.Section02

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter01
namespace Section06

/-!
# Chapter 1, Section 1.6: Proof

This section collects formal versions of proof examples and exercises about
propositional equivalence, parity, divisibility, rational numbers, and real
numbers.

Some real-number statements use the project's Dedekind-cut real infrastructure.
The irrational-product example now uses the concrete Dedekind-cut square-root
construction.

The page is intentionally a sampler. The first block is still propositional
logic, but the later blocks demonstrate how ordinary mathematical proof
obligations appear in Lean: parity is an existential predicate, divisibility is
an existential integer multiple, rationality is a representation theorem, and
real-number closure is delegated to the reusable real-number layer.
-/

open Foundation

/-!
## Logic Exercises

The first two statements are truth-table equivalences: disjunction can be
expressed as implication from a negated antecedent, and implication out of a
disjunction splits into two implications.
-/

theorem exercise_2_or_as_implication (p q : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.or p q)
      (PropForm.imp (PropForm.not p) q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

theorem exercise_3_or_implication (p q r : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.imp (PropForm.or p q) r)
      (PropForm.and (PropForm.imp p r) (PropForm.imp q r)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    cases hr : PropForm.eval valuation r <;>
    simp [PropForm.eval, hp, hq, hr]

/-!
## Parity and Divisibility

The next group formalizes examples about even numbers, odd squares, and
divisibility of integer squares. The counterexample theorems record false
converses by giving concrete numbers.
-/

theorem product_of_even_numbers_even (m n : Nat)
    (hm : NatPred.Even m) : NatPred.Even (m * n) := by
  cases hm with
  | intro k hk =>
      exists k * n
      rw [hk, Nat.mul_assoc]

theorem product_even_if_right_even (m n : Nat)
    (hn : NatPred.Even n) : NatPred.Even (m * n) := by
  cases hn with
  | intro k hk =>
      exists m * k
      rw [hk]
      calc
        m * (2 * k) = (m * 2) * k := by rw [Nat.mul_assoc]
        _ = (2 * m) * k := by rw [Nat.mul_comm m 2]
        _ = 2 * (m * k) := by rw [Nat.mul_assoc]

theorem integer_even_square_even {n : Int}
    (h : IntPred.Even n) : IntPred.Even (n * n) :=
  IntPred.even_square h

theorem integer_odd_square_odd {n : Int}
    (h : IntPred.Odd n) : IntPred.Odd (n * n) :=
  IntPred.odd_square h

theorem integer_divides_square_if_divides {a n : Int}
    (h : IntPred.Divides a n) : IntPred.Divides a (n * n) :=
  IntPred.divides_square_of_divides h

theorem integer_divisibility_transitive {r s t : Int}
    (hrs : IntPred.Divides r s) (hst : IntPred.Divides s t) :
    IntPred.Divides r t :=
  IntPred.divides_trans hrs hst

theorem integer_square_divisible_by_three_if_number_divisible_by_three {n : Int}
    (h : IntPred.Divides 3 n) : IntPred.Divides 3 (n * n) :=
  IntPred.divides_square_of_divides h

theorem sum_of_two_even_integers_even {m n : Int}
    (hm : IntPred.Even m) (hn : IntPred.Even n) : IntPred.Even (m + n) :=
  IntPred.even_add hm hn

theorem integer_product_of_two_even_numbers_even {m n : Int}
    (hm : IntPred.Even m) (_hn : IntPred.Even n) : IntPred.Even (m * n) :=
  IntPred.even_mul_left hm

theorem product_even_does_not_force_both_factors_even :
    IntPred.Even (2 * 3) ∧ ¬ IntPred.Even 3 := by
  constructor
  · exact IntPred.even_mul_left (IntPred.even_of_double 1)
  · exact IntPred.not_even_of_odd IntPred.three_odd

theorem integer_square_divisible_by_four_if_number_divisible_by_four {n : Int}
    (h : IntPred.Divides 4 n) : IntPred.Divides 4 (n * n) :=
  IntPred.divides_square_of_divides h

theorem square_divisible_by_four_does_not_force_number_divisible_by_four :
    IntPred.Divides 4 (2 * 2) ∧ ¬ IntPred.Divides 4 2 := by
  constructor
  · exists 1
  · exact IntPred.not_four_divides_two

def fourDigitValue (d1 d2 d3 d4 : Int) : Int :=
  1000 * d1 + 100 * d2 + 10 * d3 + d4

def digitSum (d1 d2 d3 d4 : Int) : Int :=
  d1 + d2 + d3 + d4

/-!
The book's direct proof that a four-digit number is divisible by 3 exactly when
the sum of its digits is divisible by 3.
-/
theorem four_digit_divisible_by_three_iff_digit_sum_divisible_by_three
    (d1 d2 d3 d4 : Int) :
    IntPred.Divides 3 (fourDigitValue d1 d2 d3 d4) <->
      IntPred.Divides 3 (digitSum d1 d2 d3 d4) := by
  constructor
  · intro h
    cases h with
    | intro k hk =>
        exists k - (333 * d1 + 33 * d2 + 3 * d3)
        unfold fourDigitValue at hk
        unfold digitSum
        omega
  · intro h
    cases h with
    | intro k hk =>
        exists 333 * d1 + 33 * d2 + 3 * d3 + k
        unfold digitSum at hk
        unfold fourDigitValue
        omega

/-!
# Rational and Real Arithmetic

The rational-number statements show closure under addition and multiplication.
The real-number statements give density, rational-real closure wrappers, and
the direct Dedekind-cut example showing that products of irrational quantities
can be rational.

The rational results are concrete algebra on numerator-denominator
representations. The real results are phrased at the predicate level: a real is
rational if it is represented by an embedded quotient rational, and irrational
if no such representation exists.
-/

theorem rational_representation_definition {a b : Int}
    (hb : b ≠ 0) : Rational.IsRepresentation a b :=
  Rational.representation_of_den_ne_zero hb

theorem six_is_rational_representation :
    Rational.IsRepresentation 6 1 :=
  Rational.representation_of_den_ne_zero (by decide)

theorem three_halves_is_rational_representation :
    Rational.IsRepresentation 3 2 :=
  Rational.representation_of_den_ne_zero (by decide)

theorem sum_of_rational_representations {a b c d : Int}
    (hb : b ≠ 0) (hd : d ≠ 0) :
    Rational.IsRepresentation (a * d + c * b) (b * d) :=
  Rational.add_representation hb hd

theorem sum_of_rational_numbers_is_rational (x y : Rational) :
    (Rational.add x y).den ≠ 0 :=
  Rational.add_den_ne_zero x y

theorem product_of_rational_representations {a b c d : Int}
    (hb : b ≠ 0) (hd : d ≠ 0) :
    Rational.IsRepresentation (a * c) (b * d) :=
  Rational.mul_representation hb hd

theorem product_of_rational_numbers_is_rational (x y : Rational) :
    (Rational.mul x y).den ≠ 0 :=
  Rational.mul_den_ne_zero x y

theorem real_number_between {x y : Real} (h : x < y) :
    exists z : Real, x < z ∧ z < y :=
  Real.exists_between h

theorem product_of_concrete_irrational_reals_can_be_rational :
    Real.Irrational Real.sqrtTwoCut ∧
      Real.Irrational Real.sqrtTwoCut ∧
      Real.Rational (Real.sqrtTwoCut * Real.sqrtTwoCut) := by
  exact And.intro Real.sqrtTwoCut_irrational
    (And.intro Real.sqrtTwoCut_irrational Real.sqrtTwoCut_square_rational)

theorem embedded_rational_real_addition (a b : QRat) :
    Real.qreal a + Real.qreal b = Real.qreal (a + b) :=
  Real.qreal_add a b

theorem embedded_rational_real_subtraction (a b : QRat) :
    Real.qreal a - Real.qreal b = Real.qreal (a - b) :=
  Real.qreal_sub a b

theorem embedded_rational_real_multiplication (a b : QRat) :
    Real.qreal a * Real.qreal b = Real.qreal (a * b) :=
  Real.qreal_mul a b

theorem sum_of_rational_reals_is_rational {x y : Real}
    (hx : Real.Rational x) (hy : Real.Rational y) :
    Real.Rational (x + y) :=
  Real.rational_add hx hy

theorem difference_of_rational_reals_is_rational {x y : Real}
    (hx : Real.Rational x) (hy : Real.Rational y) :
    Real.Rational (x - y) :=
  Real.rational_sub hx hy

theorem product_of_rational_reals_is_rational {x y : Real}
    (hx : Real.Rational x) (hy : Real.Rational y) :
    Real.Rational (x * y) :=
  Real.rational_mul hx hy

theorem positive_rational_scale_of_rational_real_is_rational
    {x : Real} {c : QRat} (hc : 0 < c) (hx : Real.Rational x) :
    Real.Rational (Real.scalePos c hc x) :=
  Real.rational_scalePos hc hx

end Section06
end Chapter01
end Book
end FoC
