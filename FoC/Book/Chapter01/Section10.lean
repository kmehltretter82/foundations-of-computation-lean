import FoC.Book.Chapter01.Section08
import FoC.Foundation.Reals

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter01
namespace Section10

/-!
# Chapter 1, Section 1.10: Recursive Definitions

This section revisits recursive definitions through the Fibonacci sequence. The
formal file exposes the recursive equations, proves an elementary exponential
upper bound, and then develops the scaled lower bound used to compare Fibonacci
growth with powers of three halves.
-/

open Foundation

/-- The Fibonacci function used here is the one defined in Section 1.8. -/
def fib : Nat -> Nat :=
  Section08.fib

/-- The first base equation for Fibonacci numbers. -/
theorem fib_zero : fib 0 = 0 :=
  rfl

/-- The second base equation for Fibonacci numbers. -/
theorem fib_one : fib 1 = 1 :=
  rfl

/-- The recursive Fibonacci equation. -/
theorem fib_recurrence (n : Nat) : fib (n + 2) = fib (n + 1) + fib n :=
  rfl

/-!
The first bound states that Fibonacci numbers grow more slowly than powers of
two. The proof follows the recursive definition and compares the two recursive
upper estimates.
-/

theorem fib_lt_two_pow : forall n, fib n < 2 ^ n
  | 0 => by simp [fib, Section08.fib]
  | 1 => by simp [fib, Section08.fib]
  | n + 2 => by
      have h1 := fib_lt_two_pow (n + 1)
      have h2 := fib_lt_two_pow n
      simp [fib, Section08.fib]
      have hpow_pos : 0 < 2 ^ n := Nat.pow_pos (by decide : 0 < 2)
      have hsum : Section08.fib (n + 1) + Section08.fib n < 2 ^ (n + 1) + 2 ^ n :=
        Nat.add_lt_add h1 h2
      have hbound : 2 ^ (n + 1) + 2 ^ n < 2 ^ (n + 2) := by
        rw [Nat.pow_succ, Nat.pow_succ]
        omega
      exact Nat.lt_trans hsum hbound

/-!
# Lower Bound by Three Halves

The lower-bound proof avoids rational exponents by multiplying both sides by a
power of two. The private helper below is the scaled statement that makes the
induction arithmetic purely natural-number arithmetic.
-/

def scaledFibLower (n : Nat) : Nat :=
  fib (n + 6) * 2 ^ (n + 5)

private theorem scaledFibLower_recurrence (n : Nat) :
    scaledFibLower (n + 2) = 2 * scaledFibLower (n + 1) + 4 * scaledFibLower n := by
  unfold scaledFibLower fib
  change Section08.fib ((n + 6) + 2) * 2 ^ ((n + 5) + 2) =
    2 * (Section08.fib ((n + 6) + 1) * 2 ^ ((n + 5) + 1)) +
      4 * (Section08.fib (n + 6) * 2 ^ (n + 5))
  rw [Section08.fib_succ_succ]
  rw [show 2 ^ ((n + 5) + 2) = 2 ^ (n + 5) * 4 by
    rw [show (n + 5) + 2 = (n + 5) + 1 + 1 by omega]
    rw [Nat.pow_succ, Nat.pow_succ]
    omega]
  rw [show 2 ^ ((n + 5) + 1) = 2 ^ (n + 5) * 2 by rw [Nat.pow_succ]]
  simp [Nat.left_distrib, Nat.mul_assoc, Nat.mul_comm]
  omega

private theorem pow_three_step_bound (n : Nat) :
    3 ^ (n + 7) < 2 * 3 ^ (n + 6) + 4 * 3 ^ (n + 5) := by
  rw [show n + 7 = (n + 5) + 2 by omega]
  rw [show n + 6 = (n + 5) + 1 by omega]
  rw [show 3 ^ ((n + 5) + 2) = 3 ^ (n + 5) * 9 by
    rw [show (n + 5) + 2 = (n + 5) + 1 + 1 by omega]
    rw [Nat.pow_succ, Nat.pow_succ]
    omega]
  rw [show 3 ^ ((n + 5) + 1) = 3 ^ (n + 5) * 3 by rw [Nat.pow_succ]]
  have hpos : 0 < 3 ^ (n + 5) := Nat.pow_pos (by decide : 0 < 3)
  simp [Nat.mul_comm]
  omega

private theorem fib_lower_bound_scaled_shifted : forall n, 3 ^ (n + 5) < scaledFibLower n
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by
      have h0 := fib_lower_bound_scaled_shifted n
      have h1 := fib_lower_bound_scaled_shifted (n + 1)
      have h0mul : 4 * 3 ^ (n + 5) < 4 * scaledFibLower n :=
        Nat.mul_lt_mul_of_pos_left h0 (by decide : 0 < 4)
      have h1mul : 2 * 3 ^ (n + 6) < 2 * scaledFibLower (n + 1) :=
        Nat.mul_lt_mul_of_pos_left h1 (by decide : 0 < 2)
      have hsum : 2 * 3 ^ (n + 6) + 4 * 3 ^ (n + 5) <
          2 * scaledFibLower (n + 1) + 4 * scaledFibLower n :=
        Nat.add_lt_add h1mul h0mul
      have hpow := pow_three_step_bound n
      have htarget := Nat.lt_trans hpow hsum
      rw [scaledFibLower_recurrence]
      exact htarget

theorem fib_lower_bound_three_halves_scaled (n : Nat) (hn : 6 <= n) :
    3 ^ (n - 1) < fib n * 2 ^ (n - 1) := by
  cases Nat.exists_eq_add_of_le hn with
  | intro d hd =>
      rw [hd]
      have h := fib_lower_bound_scaled_shifted d
      simpa [scaledFibLower, fib, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using h

/-!
The remaining statements translate the scaled natural-number inequality into
the quotient-rational and embedded-real versions used by the surrounding real
number formalization.
-/

theorem fib_lower_bound_three_halves_qrat (n : Nat) (hn : 6 <= n) :
    QRat.ofNat (3 ^ (n - 1)) / QRat.ofNat (2 ^ (n - 1)) < QRat.ofNat (fib n) := by
  have hscaled := fib_lower_bound_three_halves_scaled n hn
  have hdenpos : (0 : QRat) < QRat.ofNat (2 ^ (n - 1)) := by
    apply QRat.lt_of_toRat_lt
    rw [QRat.toRat_zero, QRat.toRat_ofNat]
    exact Rat.natCast_pos.mpr (Nat.pow_pos (by decide : 0 < 2))
  rw [QRat.div_lt_iff hdenpos]
  apply QRat.lt_of_toRat_lt
  rw [QRat.toRat_ofNat, QRat.toRat_mul, QRat.toRat_ofNat, QRat.toRat_ofNat]
  rw [← Rat.natCast_mul]
  exact Rat.natCast_lt_natCast.mpr hscaled

theorem fib_lower_bound_three_halves_real (n : Nat) (hn : 6 <= n) :
    Real.qreal (QRat.ofNat (3 ^ (n - 1)) / QRat.ofNat (2 ^ (n - 1))) <
      Real.qreal (QRat.ofNat (fib n)) :=
  Real.qreal_order_preserving (fib_lower_bound_three_halves_qrat n hn)

noncomputable def realThreeHalvesPower (n : Nat) : Real :=
  Real.divByQ
    (Real.powNat (Real.qreal (QRat.ofNat 3)) n)
    (QRat.ofNat (2 ^ n))
    (QRat.ofNat_ne_zero (Nat.pow_pos (by decide : 0 < 2)))

theorem realThreeHalvesPower_eq_qreal (n : Nat) :
    realThreeHalvesPower n =
      Real.qreal (QRat.ofNat (3 ^ n) / QRat.ofNat (2 ^ n)) := by
  unfold realThreeHalvesPower
  calc
    Real.divByQ
        (Real.powNat (Real.qreal (QRat.ofNat 3)) n)
        (QRat.ofNat (2 ^ n))
        (QRat.ofNat_ne_zero (Nat.pow_pos (by decide : 0 < 2)))
        = Real.divByQ
            (Real.qreal (QRat.powNat (QRat.ofNat 3) n))
            (QRat.ofNat (2 ^ n))
            (QRat.ofNat_ne_zero (Nat.pow_pos (by decide : 0 < 2))) := by
            rw [Real.qreal_powNat]
    _ = Real.divByQ
          (Real.qreal (QRat.ofNat (3 ^ n)))
          (QRat.ofNat (2 ^ n))
          (QRat.ofNat_ne_zero (Nat.pow_pos (by decide : 0 < 2))) := by
          rw [QRat.powNat_ofNat]
    _ = Real.qreal (QRat.ofNat (3 ^ n) / QRat.ofNat (2 ^ n)) := by
          rw [Real.qreal_divByQ]

theorem fib_lower_bound_three_halves_real_power (n : Nat) (hn : 6 <= n) :
    realThreeHalvesPower (n - 1) < Real.qreal (QRat.ofNat (fib n)) := by
  rw [realThreeHalvesPower_eq_qreal]
  exact fib_lower_bound_three_halves_real n hn

end Section10
end Chapter01
end Book
end FoC
