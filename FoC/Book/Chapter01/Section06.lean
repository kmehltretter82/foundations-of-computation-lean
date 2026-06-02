import FoC.Foundation.Arithmetic
import FoC.Foundation.Integers
import FoC.Foundation.Rationals
import FoC.Foundation.Reals
import FoC.Foundation.QuadraticSurd
import FoC.Book.Chapter01.Section01
import FoC.Book.Chapter01.Section02

namespace FoC
namespace Book
namespace Chapter01
namespace Section06

/-!
Book: Chapter 1, Section 1.6, Proof.
-/

open Foundation

-- Book: Chapter 1, Section 1.6, Exercise 2
theorem exercise_2_or_as_implication (p q : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.or p q)
      (PropForm.imp (PropForm.not p) q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

-- Book: Chapter 1, Section 1.6, Exercise 3
theorem exercise_3_or_implication (p q r : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.imp (PropForm.or p q) r)
      (PropForm.and (PropForm.imp p r) (PropForm.imp q r)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    cases hr : PropForm.eval valuation r <;>
    simp [PropForm.eval, hp, hq, hr]

-- Book: Chapter 1, Section 1.6
theorem product_of_even_numbers_even (m n : Nat)
    (hm : NatPred.Even m) : NatPred.Even (m * n) := by
  cases hm with
  | intro k hk =>
      exists k * n
      rw [hk, Nat.mul_assoc]

-- Book: Chapter 1, Section 1.6
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

-- Book: Chapter 1, Section 1.6, proof example.
theorem integer_even_square_even {n : Int}
    (h : IntPred.Even n) : IntPred.Even (n * n) :=
  IntPred.even_square h

-- Book: Chapter 1, Section 1.6, Exercise 6.
theorem integer_odd_square_odd {n : Int}
    (h : IntPred.Odd n) : IntPred.Odd (n * n) :=
  IntPred.odd_square h

-- Book: Chapter 1, Section 1.6, divisibility exercise.
theorem integer_divides_square_if_divides {a n : Int}
    (h : IntPred.Divides a n) : IntPred.Divides a (n * n) :=
  IntPred.divides_square_of_divides h

-- Book: Chapter 1, Section 1.6, Exercise 7, true direction.
theorem integer_square_divisible_by_three_if_number_divisible_by_three {n : Int}
    (h : IntPred.Divides 3 n) : IntPred.Divides 3 (n * n) :=
  IntPred.divides_square_of_divides h

-- Book: Chapter 1, Section 1.6, Exercise 8(a).
theorem integer_product_of_two_even_numbers_even {m n : Int}
    (hm : IntPred.Even m) (_hn : IntPred.Even n) : IntPred.Even (m * n) :=
  IntPred.even_mul_left hm

-- Book: Chapter 1, Section 1.6, Exercise 8(b), counterexample to the printed claim.
theorem product_even_does_not_force_both_factors_even :
    IntPred.Even (2 * 3) ∧ ¬ IntPred.Even 3 := by
  constructor
  · exact IntPred.even_mul_left (IntPred.even_of_double 1)
  · exact IntPred.not_even_of_odd IntPred.three_odd

-- Book: Chapter 1, Section 1.6, Exercise 8(e).
theorem integer_square_divisible_by_four_if_number_divisible_by_four {n : Int}
    (h : IntPred.Divides 4 n) : IntPred.Divides 4 (n * n) :=
  IntPred.divides_square_of_divides h

-- Book: Chapter 1, Section 1.6, Exercise 8(f), counterexample to the printed claim.
theorem square_divisible_by_four_does_not_force_number_divisible_by_four :
    IntPred.Divides 4 (2 * 2) ∧ ¬ IntPred.Divides 4 2 := by
  constructor
  · exists 1
  · exact IntPred.not_four_divides_two

-- Book: Chapter 1, Section 1.6, rational-number definition.
theorem rational_representation_definition {a b : Int}
    (hb : b ≠ 0) : Rational.IsRepresentation a b :=
  Rational.representation_of_den_ne_zero hb

-- Book: Chapter 1, Section 1.6, proof example: sum of rationals.
theorem sum_of_rational_representations {a b c d : Int}
    (hb : b ≠ 0) (hd : d ≠ 0) :
    Rational.IsRepresentation (a * d + c * b) (b * d) :=
  Rational.add_representation hb hd

-- Book: Chapter 1, Section 1.6, same proof as an explicit rational object.
theorem sum_of_rational_numbers_is_rational (x y : Rational) :
    (Rational.add x y).den ≠ 0 :=
  Rational.add_den_ne_zero x y

-- Book: Chapter 1, Section 1.6, Exercise 8(c): product of rationals.
theorem product_of_rational_representations {a b c d : Int}
    (hb : b ≠ 0) (hd : d ≠ 0) :
    Rational.IsRepresentation (a * c) (b * d) :=
  Rational.mul_representation hb hd

-- Book: Chapter 1, Section 1.6, Exercise 8(c), object-level form.
theorem product_of_rational_numbers_is_rational (x y : Rational) :
    (Rational.mul x y).den ≠ 0 :=
  Rational.mul_den_ne_zero x y

-- Book: Chapter 1, Section 1.6, real-number density.
theorem real_number_between {x y : Real} (h : x < y) :
    exists z : Real, x < z ∧ z < y :=
  Real.exists_between h

-- Book: Chapter 1, Section 1.6, irrational-product counterexample surrogate.
theorem product_of_irrational_surrogates_can_be_rational :
    Quad2.IrrationalLike Quad2.sqrtTwo ∧
      Quad2.IrrationalLike Quad2.sqrtTwo ∧
      Quad2.RationalLike (Quad2.mul Quad2.sqrtTwo Quad2.sqrtTwo) := by
  exact And.intro Quad2.sqrtTwo_irrationalLike
    (And.intro Quad2.sqrtTwo_irrationalLike Quad2.sqrtTwo_mul_self_rationalLike)

-- Book: Chapter 1, Section 1.6, embedded rational real addition.
theorem embedded_rational_real_addition (a b : QRat) :
    Real.qreal a + Real.qreal b = Real.qreal (a + b) :=
  Real.qreal_add a b

-- Book: Chapter 1, Section 1.6, embedded rational real subtraction.
theorem embedded_rational_real_subtraction (a b : QRat) :
    Real.qreal a - Real.qreal b = Real.qreal (a - b) :=
  Real.qreal_sub a b

-- Book: Chapter 1, Section 1.6, embedded rational real multiplication.
theorem embedded_rational_real_multiplication (a b : QRat) :
    Real.qreal a * Real.qreal b = Real.qreal (a * b) :=
  Real.qreal_mul a b

-- Book: Chapter 1, Section 1.6, rational real sums remain rational.
theorem sum_of_rational_reals_is_rational {x y : Real}
    (hx : Real.Rational x) (hy : Real.Rational y) :
    Real.Rational (x + y) :=
  Real.rational_add hx hy

-- Book: Chapter 1, Section 1.6, rational real differences remain rational.
theorem difference_of_rational_reals_is_rational {x y : Real}
    (hx : Real.Rational x) (hy : Real.Rational y) :
    Real.Rational (x - y) :=
  Real.rational_sub hx hy

-- Book: Chapter 1, Section 1.6, rational real products remain rational.
theorem product_of_rational_reals_is_rational {x y : Real}
    (hx : Real.Rational x) (hy : Real.Rational y) :
    Real.Rational (x * y) :=
  Real.rational_mul hx hy

-- Book: Chapter 1, Section 1.6, positive embedded-rational scaling.
theorem positive_rational_scale_of_rational_real_is_rational
    {x : Real} {c : QRat} (hc : 0 < c) (hx : Real.Rational x) :
    Real.Rational (Real.scalePos c hc x) :=
  Real.rational_scalePos hc hx

end Section06
end Chapter01
end Book
end FoC
