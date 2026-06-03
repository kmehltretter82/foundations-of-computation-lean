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
-/

theorem simple_sum_formula (n : Nat) :
    NatSum.SumUpTo (fun i => i) n = n * (n + 1) / 2 :=
  NatSum.sum_identity_closed_form n

theorem weighted_power_sum_formula (n : Nat) :
    NatSum.SumUpTo NatSum.WeightedPowerTerm (n + 1) = n * 2 ^ (n + 1) + 1 :=
  NatSum.weighted_power_sum_closed_form_succ n

theorem geometric_sum_powers_of_two (n : Nat) :
    NatSum.SumZeroTo (fun i => 2 ^ i) n = 2 ^ (n + 1) - 1 :=
  NatSum.geometric_two_sum n

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
-/

theorem odd_sum_square (n : Nat) :
    NatSum.SumUpTo (fun i => 2 * i - 1) n = n * n :=
  NatSum.odd_sum_square n

theorem product_of_primes_exists (n : Nat) (hn : 1 < n) :
    NatPrime.ProductOfPrimes n :=
  NatPrime.product_of_primes_exists n hn

end Section08
end Chapter01
end Book
end FoC
