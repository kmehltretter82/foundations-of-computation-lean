import FoC.Foundation.Summation
import FoC.Foundation.Primes
import FoC.Foundation.Reals

namespace FoC
namespace Book
namespace Chapter01
namespace Section08

/-!
Book: Chapter 1, Section 1.8, Mathematical Induction.
-/

-- Book: Chapter 1, Section 1.8, Theorem 1.6
theorem mathematical_induction (P : Nat -> Prop)
    (base : P 0)
    (step : forall k, P k -> P (k + 1)) :
    forall n, P n := by
  intro n
  induction n with
  | zero => exact base
  | succ n ih =>
      exact step n ih

-- Book: Chapter 1, Section 1.8, extended induction from a starting point
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

-- Book: Chapter 1, Section 1.8, second form of induction
theorem strong_induction_book (P : Nat -> Prop)
    (step : forall n, (forall k, k < n -> P k) -> P n) :
    forall n, P n := by
  intro n
  exact Nat.strongRecOn (motive := P) n step

def factorial : Nat -> Nat
  | 0 => 1
  | n + 1 => factorial n * (n + 1)

-- Book: Chapter 1, Section 1.8, recursive factorial equation
theorem factorial_succ (n : Nat) : factorial (n + 1) = factorial n * (n + 1) :=
  rfl

def fib : Nat -> Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

-- Book: Chapter 1, Section 1.8, Fibonacci recurrence infrastructure
theorem fib_succ_succ (n : Nat) : fib (n + 2) = fib (n + 1) + fib n :=
  rfl

open Foundation

-- Book: Chapter 1, Section 1.8, Theorem 1.12
theorem simple_sum_formula (n : Nat) :
    NatSum.SumUpTo (fun i => i) n = n * (n + 1) / 2 :=
  NatSum.sum_identity_closed_form n

-- Book: Chapter 1, Section 1.8, Theorem 1.13
theorem weighted_power_sum_formula (n : Nat) :
    NatSum.SumUpTo NatSum.WeightedPowerTerm (n + 1) = n * 2 ^ (n + 1) + 1 :=
  NatSum.weighted_power_sum_closed_form_succ n

-- Book: Chapter 1, Section 1.8, Exercise 4
theorem geometric_sum_powers_of_two (n : Nat) :
    NatSum.SumZeroTo (fun i => 2 ^ i) n = 2 ^ (n + 1) - 1 :=
  NatSum.geometric_two_sum n

-- Book: Chapter 1, Section 1.8, Exercise 2, division-free natural-number core.
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

-- Book: Chapter 1, Section 1.8, geometric-series identity before division.
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

-- Book: Chapter 1, Section 1.8, geometric-series formula with division by `1 - r`.
theorem quotient_rational_geometric_series_formula
    (r : QRat) (n : Nat) (hr : 1 - r ≠ 0) :
    qratGeometricSum r n = (1 - qratPower r (n + 1)) / (1 - r) := by
  calc
    qratGeometricSum r n =
        qratGeometricSum r n * (1 - r) / (1 - r) := by
      exact (QRat.mul_div_cancel (qratGeometricSum r n) hr).symm
    _ = (1 - qratPower r (n + 1)) / (1 - r) := by
      rw [quotient_rational_geometric_series_mul_one_sub]

-- Book: Chapter 1, Section 1.8, real-valued geometric-series identity.
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

-- Book: Chapter 1, Section 1.8, real-valued geometric-series division form.
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

-- Book: Chapter 1, Section 1.8, Exercise 6
theorem odd_sum_square (n : Nat) :
    NatSum.SumUpTo (fun i => 2 * i - 1) n = n * n :=
  NatSum.odd_sum_square n

-- Book: Chapter 1, Section 1.8, product-of-primes induction example.
theorem product_of_primes_exists (n : Nat) (hn : 1 < n) :
    NatPrime.ProductOfPrimes n :=
  NatPrime.product_of_primes_exists n hn

end Section08
end Chapter01
end Book
end FoC
