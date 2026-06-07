import FoC.Foundation
import FoC.Foundation.Summation
import FoC.Foundation.Primes
import FoC.Foundation.Reals

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter01
namespace Section08

/-!
# Chapter 1, Section 1.8: Mathematical Induction

This section records the induction principles and recursive numerical examples
used in the book's introduction to mathematical induction. The first three
theorems isolate ordinary induction from zero, induction beginning at an
arbitrary lower bound, and strong induction.

The later statements are the formal kernels behind the textbook examples:
factorial and Fibonacci recursion, closed forms for finite sums, geometric
series identities over the quotient rationals and embedded reals, the sum of
odd numbers, and the existence of a product-of-primes factorization.

Induction in Lean is a recursion principle for proofs. To prove a proposition
about every natural number, the declarations below either supply a base case
and successor step, shift the base case to a lower bound, or use strong
induction where all smaller cases are available at once.
-/

/-- Ordinary induction from zero: a base case and successor step prove every
instance of a predicate on natural numbers. -/
theorem mathematical_induction (P : Nat -> Prop)
    (base : P 0)
    (step : forall k, P k -> P (k + 1)) :
    forall n, P n := by
  intro n
  induction n with
  | zero => exact base
  | succ n ih =>
      exact step n ih

theorem induction_from (P : Nat -> Prop) (m : Nat)
    (base : P m)
    (step : forall k, m <= k -> P k -> P (k + 1)) :
    forall n, m <= n -> P n := by
  intro n hmn
  let Q : Nat -> Prop := fun d => P (m + d)
  have hQ : forall d, Q d := by
    apply mathematical_induction
    · exact base
    · intro d ih
      exact step (m + d) (Nat.le_add_right m d) ih
  have hsplit : exists d, n = m + d := Nat.exists_eq_add_of_le hmn
  cases hsplit with
  | intro d hd =>
      rw [hd]
      exact hQ d

theorem strong_induction_book (P : Nat -> Prop)
    (step : forall n, (forall k, k < n -> P k) -> P n) :
    forall n, P n := by
  intro n
  exact Nat.strongRecOn (motive := P) n step

/-!
# First Induction Example

The book's first worked induction example proves that {lit}`2^(2n) - 1` is
divisible by {lit}`3`.  The formal statement uses the elementary divisibility
predicate from {module}`FoC.Foundation.Arithmetic`.
-/

theorem two_to_even_power_minus_one_divisible_by_three (n : Nat) :
    Foundation.NatPred.Divides 3 (2 ^ (2 * n) - 1) := by
  induction n with
  | zero =>
      exists 0
  | succ n ih =>
      cases ih with
      | intro k hk =>
          exists 4 * k + 1
          have hpow : 2 ^ (2 * (n + 1)) = 4 * 2 ^ (2 * n) := by
            rw [show 2 * (n + 1) = 2 * n + 2 by omega]
            rw [show 2 ^ (2 * n + 2) = 2 ^ (2 * n) * 4 by
              rw [show 2 * n + 2 = 2 * n + 1 + 1 by omega]
              rw [Nat.pow_succ, Nat.pow_succ]
              omega]
            omega
          have hpos : 0 < 2 ^ (2 * n) := Nat.pow_pos (by decide : 0 < 2)
          calc
            2 ^ (2 * (n + 1)) - 1 = 4 * 2 ^ (2 * n) - 1 := by
              rw [hpow]
            _ = 4 * (2 ^ (2 * n) - 1) + 3 := by
              omega
            _ = 4 * (3 * k) + 3 := by
              rw [hk]
            _ = 3 * (4 * k + 1) := by
              omega

/-!
# Recursive Numerical Definitions

The next definitions mirror the textbook's recursive definitions. In Lean, the
equations for factorial and Fibonacci are definitional, so the successor
theorems are proved by reflexivity.
-/

def factorial : Nat -> Nat
  | 0 => 1
  | n + 1 => factorial n * (n + 1)

theorem factorial_succ (n : Nat) : factorial (n + 1) = factorial n * (n + 1) :=
  rfl

theorem factorial_zero : factorial 0 = 1 :=
  rfl

theorem factorial_one : factorial 1 = 1 :=
  rfl

theorem factorial_five : factorial 5 = 120 :=
  rfl

def fib : Nat -> Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

theorem fib_succ_succ (n : Nat) : fib (n + 2) = fib (n + 1) + fib n :=
  rfl

open Foundation

/-!
# Finite Sums and Geometric Series

These statements reuse the finite-summation library from {module}`FoC.Foundation`.
They put the familiar closed forms from the book into the chapter-facing order.

The early formulas are natural-number identities. The geometric-series results
then move through quotient rationals and embedded reals so the chapter can
state the familiar division form while still relying on checked algebraic
infrastructure.
-/

theorem simple_sum_formula (n : Nat) :
    NatSum.SumUpTo (fun i => i) n = n * (n + 1) / 2 :=
  NatSum.sum_identity_closed_form n

theorem sum_first_even_numbers (n : Nat) :
    NatSum.SumUpTo (fun i => 2 * i) n = n * (n + 1) :=
  NatSum.even_sum_closed_form n

theorem sum_first_hundred_integers :
    NatSum.SumUpTo (fun i => i) 100 = 5050 := by
  simpa using simple_sum_formula 100

theorem sum_first_ten_even_numbers :
    NatSum.SumUpTo (fun i => 2 * i) 10 = 110 := by
  simpa using sum_first_even_numbers 10

theorem weighted_power_sum_formula (n : Nat) :
    NatSum.SumUpTo NatSum.WeightedPowerTerm (n + 1) = n * 2 ^ (n + 1) + 1 :=
  NatSum.weighted_power_sum_closed_form_succ n

theorem weighted_power_sum_formula_positive (n : Nat) (hn : 0 < n) :
    NatSum.SumUpTo NatSum.WeightedPowerTerm n = (n - 1) * 2 ^ n + 1 := by
  cases n with
  | zero =>
      cases hn
  | succ n =>
      simpa using NatSum.weighted_power_sum_closed_form_succ n

theorem weighted_power_sum_five :
    NatSum.SumUpTo NatSum.WeightedPowerTerm 5 = 129 := by
  simpa using weighted_power_sum_formula_positive 5 (by decide)

theorem geometric_sum_powers_of_two (n : Nat) :
    NatSum.SumZeroTo (fun i => 2 ^ i) n = 2 ^ (n + 1) - 1 :=
  NatSum.geometric_two_sum n

theorem geometric_sum_powers_of_two_to_ten :
    NatSum.SumZeroTo (fun i => 2 ^ i) 10 = 2047 := by
  simpa using geometric_sum_powers_of_two 10

theorem geometric_successor_base_sum (b n : Nat) :
    b * NatSum.SumZeroTo (fun i => (b + 1) ^ i) n = (b + 1) ^ (n + 1) - 1 :=
  NatSum.geometric_successor_base_sum b n

def qratPower (r : QRat) : Nat -> QRat
  | 0 => 1
  | n + 1 => qratPower r n * r

theorem qratPower_eq_powNat (r : QRat) (n : Nat) :
    qratPower r n = QRat.powNat r n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [qratPower, QRat.powNat_succ, ih]

def qratGeometricSum (r : QRat) : Nat -> QRat
  | 0 => 1
  | n + 1 => qratGeometricSum r n + qratPower r (n + 1)

noncomputable def realGeometricSum (x : Real) : Nat -> Real
  | 0 => 1
  | n + 1 => realGeometricSum x n + Real.powNat x (n + 1)

theorem real_powNat_eq_algebraic_pow (x : Real) (n : Nat) :
    Real.powNat x n = NatSum.GeometricSeries.Pow x n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        Real.powNat x (n + 1) = Real.powNat x n * x := rfl
        _ = NatSum.GeometricSeries.Pow x n * x := by rw [ih]
        _ = NatSum.GeometricSeries.Pow x (n + 1) := rfl

theorem real_geometric_sum_eq_algebraic_sum (x : Real) (n : Nat) :
    realGeometricSum x n = NatSum.GeometricSeries.Sum x n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        realGeometricSum x (n + 1) =
            realGeometricSum x n + Real.powNat x (n + 1) := rfl
        _ = NatSum.GeometricSeries.Sum x n +
              NatSum.GeometricSeries.Pow x (n + 1) := by
            rw [ih, real_powNat_eq_algebraic_pow]
        _ = NatSum.GeometricSeries.Sum x (n + 1) := rfl

def DedekindRealGeometricSeriesAlgebra : Prop :=
  NatSum.GeometricSeries.Algebra Real

theorem dedekind_real_geometric_series_algebra :
    DedekindRealGeometricSeriesAlgebra := by
  exact {
    add_assoc := Real.add_assoc
    zero_add := Real.zero_add
    neg_add_cancel := Real.neg_add_cancel
    sub_eq_add_neg := Real.sub_eq_add_neg
    one_mul := Real.one_mul
    mul_one := Real.mul_one
    left_distrib := by
      intro a b c
      calc
        a * (b + c) = (b + c) * a := Real.mul_comm a (b + c)
        _ = b * a + c * a := Real.right_distrib b c a
        _ = a * b + a * c := by rw [Real.mul_comm b a, Real.mul_comm c a]
    right_distrib := Real.right_distrib
    mul_neg := Real.mul_neg
  }

theorem arbitrary_real_geometric_series_mul_one_sub_of_algebra
    (laws : DedekindRealGeometricSeriesAlgebra)
    (x : Real) (n : Nat) :
    realGeometricSum x n * (1 - x) =
      1 - Real.powNat x (n + 1) := by
  have h := NatSum.GeometricSeries.mul_one_sub laws x n
  rw [real_geometric_sum_eq_algebraic_sum,
    real_powNat_eq_algebraic_pow]
  exact h

theorem arbitrary_real_geometric_series_mul_one_sub
    (x : Real) (n : Nat) :
    realGeometricSum x n * (1 - x) =
      1 - Real.powNat x (n + 1) := by
  exact arbitrary_real_geometric_series_mul_one_sub_of_algebra
    dedekind_real_geometric_series_algebra x n

theorem arbitrary_real_geometric_series_division_formula
    (x : Real) (n : Nat) (hden : 1 - x ≠ 0) :
    realGeometricSum x n =
      Real.divByNonzero
        (1 - Real.powNat x (n + 1)) (1 - x) hden := by
  have hmul := arbitrary_real_geometric_series_mul_one_sub x n
  calc
    realGeometricSum x n =
        Real.divByNonzero
          (realGeometricSum x n * (1 - x)) (1 - x) hden := by
      exact (Real.divByNonzero_mul_cancel
        (realGeometricSum x n) (1 - x) hden).symm
    _ = Real.divByNonzero
          (1 - Real.powNat x (n + 1)) (1 - x) hden := by
      rw [hmul]

/-!
The theorem above is the arbitrary-real induction core for the book's
geometric-series formula, stated against the exact algebra laws needed by the
calculation. The custom Dedekind-real layer supplies the additive laws,
multiplicative identities, multiplication commutativity, right distributivity,
and multiplication by negatives used by
{name}`DedekindRealGeometricSeriesAlgebra`.

The division form uses {name}`Real.divByNonzero`, a noncomputable selector for a
preimage under multiplication by a nonzero denominator. Its cancellation theorem
is now unconditional because {name}`Real.right_distrib` and the no-zero-divisor
theorem are available for the custom Dedekind-cut multiplication. The
quotient-rational and embedded-rational specializations below remain separate
because their denominator is a quotient rational and can use {name}`Real.divByQ`.
-/

theorem real_geometric_sum_qreal (r : QRat) (n : Nat) :
    realGeometricSum (Real.qreal r) n =
      Real.qreal (qratGeometricSum r n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        realGeometricSum (Real.qreal r) (n + 1) =
            realGeometricSum (Real.qreal r) n +
              Real.powNat (Real.qreal r) (n + 1) := rfl
        _ = Real.qreal (qratGeometricSum r n) +
              Real.qreal (QRat.powNat r (n + 1)) := by
            rw [ih, Real.qreal_powNat]
        _ = Real.qreal (qratGeometricSum r n + QRat.powNat r (n + 1)) := by
            rw [Real.qreal_add]
        _ = Real.qreal (qratGeometricSum r n + qratPower r (n + 1)) := by
            rw [← qratPower_eq_powNat]
        _ = Real.qreal (qratGeometricSum r (n + 1)) := rfl

theorem quotient_rational_geometric_series_mul_one_sub (r : QRat) (n : Nat) :
    qratGeometricSum r n * (1 - r) = 1 - qratPower r (n + 1) := by
  induction n with
  | zero =>
      apply QRat.eq_of_toRat_eq
      simp [qratGeometricSum, qratPower, QRat.toRat_mul, QRat.toRat_sub,
        QRat.toRat_one]
  | succ n ih =>
      apply QRat.eq_of_toRat_eq
      have ihRat := congrArg QRat.toRat ih
      simp [qratGeometricSum, qratPower, QRat.toRat_mul, QRat.toRat_add,
        QRat.toRat_sub, QRat.toRat_one] at ihRat ⊢
      grind [Rat.add_mul, Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg,
        Rat.pow_succ]

/-- Division form of the quotient-rational geometric-series formula. -/
theorem quotient_rational_geometric_series_formula
    (r : QRat) (n : Nat) (hr : 1 - r ≠ 0) :
    qratGeometricSum r n = (1 - qratPower r (n + 1)) / (1 - r) := by
  calc
    qratGeometricSum r n =
        qratGeometricSum r n * (1 - r) / (1 - r) := by
      exact (QRat.mul_div_cancel (qratGeometricSum r n) hr).symm
    _ = (1 - qratPower r (n + 1)) / (1 - r) := by
      rw [quotient_rational_geometric_series_mul_one_sub]

/-- Embedded-real specialization of the multiplication form of the
geometric-series identity. -/
theorem real_geometric_series_mul_one_sub (r : QRat) (n : Nat) :
    realGeometricSum (Real.qreal r) n * (1 - Real.qreal r) =
      1 - Real.powNat (Real.qreal r) (n + 1) := by
  have hden : (1 : Real) - Real.qreal r = Real.qreal (1 - r) :=
    Real.qreal_sub 1 r
  have hpow :
      Real.powNat (Real.qreal r) (n + 1) =
        Real.qreal (qratPower r (n + 1)) := by
    rw [Real.qreal_powNat, ← qratPower_eq_powNat]
  have hnum :
      (1 : Real) - Real.powNat (Real.qreal r) (n + 1) =
        Real.qreal (1 - qratPower r (n + 1)) := by
    rw [hpow]
    change Real.qreal 1 - Real.qreal (qratPower r (n + 1)) =
      Real.qreal (1 - qratPower r (n + 1))
    rw [Real.qreal_sub]
  calc
    realGeometricSum (Real.qreal r) n * (1 - Real.qreal r)
        = Real.qreal (qratGeometricSum r n) * ((1 : Real) - Real.qreal r) := by
            rw [real_geometric_sum_qreal]
    _ = Real.qreal (qratGeometricSum r n) * Real.qreal (1 - r) := by
            rw [hden]
    _ = Real.qreal (qratGeometricSum r n * (1 - r)) := by
            rw [Real.qreal_mul]
    _ = Real.qreal (1 - qratPower r (n + 1)) := by
            rw [quotient_rational_geometric_series_mul_one_sub]
    _ = 1 - Real.powNat (Real.qreal r) (n + 1) := hnum.symm

/-- Embedded-real specialization of the division form of the geometric-series
identity. -/
theorem real_geometric_series_formula
    (r : QRat) (n : Nat) (hr : 1 - r ≠ 0) :
    realGeometricSum (Real.qreal r) n =
      Real.divByQ (1 - Real.powNat (Real.qreal r) (n + 1)) (1 - r) hr := by
  have hpow :
      Real.powNat (Real.qreal r) (n + 1) =
        Real.qreal (qratPower r (n + 1)) := by
    rw [Real.qreal_powNat, ← qratPower_eq_powNat]
  have hnum :
      (1 : Real) - Real.powNat (Real.qreal r) (n + 1) =
        Real.qreal (1 - qratPower r (n + 1)) := by
    rw [hpow]
    change Real.qreal 1 - Real.qreal (qratPower r (n + 1)) =
      Real.qreal (1 - qratPower r (n + 1))
    rw [Real.qreal_sub]
  calc
    realGeometricSum (Real.qreal r) n = Real.qreal (qratGeometricSum r n) := by
        rw [real_geometric_sum_qreal]
    _ = Real.qreal ((1 - qratPower r (n + 1)) / (1 - r)) := by
        rw [quotient_rational_geometric_series_formula r n hr]
    _ = Real.divByQ (Real.qreal (1 - qratPower r (n + 1))) (1 - r) hr := by
        rw [Real.qreal_divByQ]
    _ = Real.divByQ (1 - Real.powNat (Real.qreal r) (n + 1)) (1 - r) hr := by
        rw [hnum]

/-!
The final two theorem statements are examples where induction or strong
induction supplies a number-theoretic result rather than merely a closed form.

{lit}`odd_sum_square` is the standard induction identity for sums of odd numbers.
{lit}`product_of_primes_exists` uses strong induction: after extracting a factor,
the proof appeals to the result for smaller numbers.
-/

theorem odd_sum_square (n : Nat) :
    NatSum.SumUpTo (fun i => 2 * i - 1) n = n * n :=
  NatSum.odd_sum_square n

theorem sum_first_ten_odd_numbers :
    NatSum.SumUpTo (fun i => 2 * i - 1) 10 = 100 := by
  simpa using odd_sum_square 10

theorem product_of_primes_exists (n : Nat) (hn : 1 < n) :
    NatPrime.ProductOfPrimes n :=
  NatPrime.product_of_primes_exists n hn

end Section08
end Chapter01
end Book
end FoC
