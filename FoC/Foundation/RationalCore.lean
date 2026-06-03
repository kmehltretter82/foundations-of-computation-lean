import Init.Data.Nat.Coprime
import Init.Data.Nat.Dvd

set_option doc.verso true

/-!
# Reduced rational cores

## Reduced rational representatives

The earlier {module -checked}`FoC.Foundation.Rationals` module models raw
integer-over-integer representatives.
This module adds the reduced positive-denominator representative shape needed
for the book's square-root irrationality arguments.  It intentionally stops
short of quotienting representatives; a future full {lit}`Real` development can
embed this exact reduced core into a quotient rational field first.

## Book coordinates

Used by:
- Chapter 1, Section 1.7: irrationality of square roots of 2 and 3
- Chapter 2, Section 2.6: exact quotient-rational countability, later
- Future {lit}`Real` bridge: rational embedding and irrationality transport
-/

namespace FoC
namespace Foundation

/-!
# Reduced square-root witnesses

Reduced positive rational representatives provide the exact data needed for the
classic contradiction proofs about square roots.
-/

structure PositiveRatRep where
  num : Int
  den : Nat
  den_pos : 0 < den

namespace PositiveRatRep

def Reduced (q : PositiveRatRep) : Prop :=
  Nat.Coprime q.num.natAbs q.den

def SquareRootOfNat (q : PositiveRatRep) (c : Nat) : Prop :=
  q.num * q.num = (c : Int) * (q.den : Int) * (q.den : Int)

theorem squareRootOfNat_natAbs {q : PositiveRatRep} {c : Nat}
    (h : SquareRootOfNat q c) :
    q.num.natAbs * q.num.natAbs = c * q.den * q.den := by
  have habs := congrArg Int.natAbs h
  simp [Int.natAbs_mul] at habs
  exact habs

end PositiveRatRep

namespace NatDivisibility

/-!
# Divisibility of squares

Exercise 6 in Section 1.6 needs the elementary fact that if {lit}`2` divides a
square, then {lit}`2` divides the original natural number.
-/
theorem two_dvd_of_two_dvd_square {n : Nat} (h : 2 ∣ n * n) : 2 ∣ n := by
  rw [Nat.dvd_iff_mod_eq_zero] at h ⊢
  rw [Nat.mul_mod] at h
  have hlt : n % 2 < 2 := Nat.mod_lt n (by decide : 0 < 2)
  have hcases : n % 2 = 0 ∨ n % 2 = 1 := by
    omega
  cases hcases with
  | inl h0 => exact h0
  | inr h1 =>
      rw [h1] at h
      contradiction

/-!
The analogous divisibility lemma for {lit}`3` is used by the square-root-of-three
irrationality argument.
-/
theorem three_dvd_of_three_dvd_square {n : Nat} (h : 3 ∣ n * n) : 3 ∣ n := by
  rw [Nat.dvd_iff_mod_eq_zero] at h ⊢
  rw [Nat.mul_mod] at h
  have hlt : n % 3 < 3 := Nat.mod_lt n (by decide : 0 < 3)
  have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
    omega
  cases hcases with
  | inl h0 => exact h0
  | inr hrest =>
      cases hrest with
      | inl h1 =>
          rw [h1] at h
          contradiction
      | inr h2 =>
          rw [h2] at h
          contradiction

theorem no_coprime_square_root_two {m n : Nat}
    (hcop : Nat.Coprime m n) (h : m * m = 2 * (n * n)) : False := by
  have hm2div : 2 ∣ m * m := by
    rw [h]
    exact Nat.dvd_mul_right 2 (n * n)
  have hmdiv : 2 ∣ m := two_dvd_of_two_dvd_square hm2div
  cases hmdiv with
  | intro k hm =>
      have hm2 : m * m = 2 * (2 * (k * k)) := by
        rw [hm]
        ac_rfl
      have hcancel : 2 * (n * n) = 2 * (2 * (k * k)) := by
        rw [← h, hm2]
      have hn2eq : n * n = 2 * (k * k) :=
        Nat.mul_left_cancel (by decide : 0 < 2) hcancel
      have hn2div : 2 ∣ n * n := by
        rw [hn2eq]
        exact Nat.dvd_mul_right 2 (k * k)
      have hndiv : 2 ∣ n := two_dvd_of_two_dvd_square hn2div
      exact Nat.not_coprime_of_dvd_of_dvd
        (by decide : 1 < 2) (Exists.intro k hm) hndiv hcop

theorem no_coprime_square_root_three {m n : Nat}
    (hcop : Nat.Coprime m n) (h : m * m = 3 * (n * n)) : False := by
  have hm2div : 3 ∣ m * m := by
    rw [h]
    exact Nat.dvd_mul_right 3 (n * n)
  have hmdiv : 3 ∣ m := three_dvd_of_three_dvd_square hm2div
  cases hmdiv with
  | intro k hm =>
      have hm2 : m * m = 3 * (3 * (k * k)) := by
        rw [hm]
        ac_rfl
      have hcancel : 3 * (n * n) = 3 * (3 * (k * k)) := by
        rw [← h, hm2]
      have hn2eq : n * n = 3 * (k * k) :=
        Nat.mul_left_cancel (by decide : 0 < 3) hcancel
      have hn2div : 3 ∣ n * n := by
        rw [hn2eq]
        exact Nat.dvd_mul_right 3 (k * k)
      have hndiv : 3 ∣ n := three_dvd_of_three_dvd_square hn2div
      exact Nat.not_coprime_of_dvd_of_dvd
        (by decide : 1 < 3) (Exists.intro k hm) hndiv hcop

end NatDivisibility

namespace PositiveRatRep

/-!
# Irrationality cores

The square-root-of-two statement is phrased for reduced positive rational
representatives.  A reduced rational cannot square to {lit}`2`.
-/
theorem no_reduced_square_root_two (q : PositiveRatRep)
    (hred : q.Reduced) : ¬ q.SquareRootOfNat 2 := by
  intro h
  have habs := PositiveRatRep.squareRootOfNat_natAbs h
  rw [Nat.mul_assoc] at habs
  exact NatDivisibility.no_coprime_square_root_two hred habs

/-!
The same reduced-rational argument rules out a rational square root of {lit}`3`.
-/
theorem no_reduced_square_root_three (q : PositiveRatRep)
    (hred : q.Reduced) : ¬ q.SquareRootOfNat 3 := by
  intro h
  have habs := PositiveRatRep.squareRootOfNat_natAbs h
  rw [Nat.mul_assoc] at habs
  exact NatDivisibility.no_coprime_square_root_three hred habs

end PositiveRatRep

end Foundation
end FoC
