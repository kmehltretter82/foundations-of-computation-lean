namespace FoC
namespace Foundation

/-!
Standalone finite-summation infrastructure.

Used by:
- Chapter 1, Section 1.8: Mathematical Induction
- Chapter 1, Section 1.10: Recursive Definitions
- Chapter 2, Section 2.6: finite cardinality arithmetic, later
-/

namespace NatSum

def SumUpTo (f : Nat -> Nat) : Nat -> Nat
  | 0 => 0
  | n + 1 => SumUpTo f n + f (n + 1)

def SumZeroTo (f : Nat -> Nat) : Nat -> Nat
  | 0 => f 0
  | n + 1 => SumZeroTo f n + f (n + 1)

def WeightedPowerTerm (i : Nat) : Nat :=
  i * 2 ^ (i - 1)

theorem SumUpTo.zero (f : Nat -> Nat) :
    SumUpTo f 0 = 0 :=
  rfl

theorem SumUpTo.succ (f : Nat -> Nat) (n : Nat) :
    SumUpTo f (n + 1) = SumUpTo f n + f (n + 1) :=
  rfl

theorem SumZeroTo.zero (f : Nat -> Nat) :
    SumZeroTo f 0 = f 0 :=
  rfl

theorem SumZeroTo.succ (f : Nat -> Nat) (n : Nat) :
    SumZeroTo f (n + 1) = SumZeroTo f n + f (n + 1) :=
  rfl

theorem two_mul_sum_identity (n : Nat) :
    2 * SumUpTo (fun i => i) n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        2 * SumUpTo (fun i => i) (n + 1)
            = 2 * (SumUpTo (fun i => i) n + (n + 1)) := by
                rw [SumUpTo.succ]
        _ = 2 * SumUpTo (fun i => i) n + 2 * (n + 1) := by
                rw [Nat.mul_add]
        _ = n * (n + 1) + 2 * (n + 1) := by
                rw [ih]
        _ = (n + 1) * (n + 1 + 1) := by
                simp [Nat.left_distrib, Nat.right_distrib,
                  Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                omega

-- Book: Chapter 1, Section 1.8, Theorem 1.12.
theorem sum_identity_closed_form (n : Nat) :
    SumUpTo (fun i => i) n = n * (n + 1) / 2 := by
  have h := two_mul_sum_identity n
  omega

theorem weighted_power_algebra (n p : Nat) :
    n * p + 1 + (n + 2) * p = (n + 1) * (p * 2) + 1 := by
  calc
    n * p + 1 + (n + 2) * p = (n * p + (n + 2) * p) + 1 := by
      omega
    _ = (n + (n + 2)) * p + 1 := by
      rw [← Nat.add_mul]
    _ = ((n + 1) * 2) * p + 1 := by
      have h : n + (n + 2) = (n + 1) * 2 := by
        omega
      rw [h]
    _ = (n + 1) * (p * 2) + 1 := by
      rw [Nat.mul_assoc, Nat.mul_comm 2 p, ← Nat.mul_assoc]

-- Book: Chapter 1, Section 1.8, Theorem 1.13.
theorem weighted_power_sum_closed_form_succ (n : Nat) :
    SumUpTo WeightedPowerTerm (n + 1) = n * 2 ^ (n + 1) + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        SumUpTo WeightedPowerTerm (n + 1 + 1)
            = SumUpTo WeightedPowerTerm (n + 1) + WeightedPowerTerm (n + 1 + 1) := by
                rw [SumUpTo.succ]
        _ = n * 2 ^ (n + 1) + 1 + WeightedPowerTerm (n + 1 + 1) := by
                rw [ih]
        _ = n * 2 ^ (n + 1) + 1 + ((n + 2) * 2 ^ (n + 1)) := by
                rfl
        _ = (n + 1) * 2 ^ (n + 1 + 1) + 1 := by
                rw [show 2 ^ (n + 1 + 1) = 2 ^ (n + 1) * 2 by
                  rw [Nat.pow_succ]]
                exact weighted_power_algebra n (2 ^ (n + 1))

-- Book: Chapter 1, Section 1.8, Exercise 4.
theorem geometric_two_sum (n : Nat) :
    SumZeroTo (fun i => 2 ^ i) n = 2 ^ (n + 1) - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        SumZeroTo (fun i => 2 ^ i) (n + 1)
            = SumZeroTo (fun i => 2 ^ i) n + 2 ^ (n + 1) := by
                rw [SumZeroTo.succ]
        _ = (2 ^ (n + 1) - 1) + 2 ^ (n + 1) := by
                rw [ih]
        _ = 2 ^ (n + 1 + 1) - 1 := by
                rw [show 2 ^ (n + 1 + 1) = 2 ^ (n + 1) * 2 by
                  rw [Nat.pow_succ]]
                have hpos : 0 < 2 ^ (n + 1) := Nat.pow_pos (by decide : 0 < 2)
                omega

-- Book: Chapter 1, Section 1.8, Exercise 6.
theorem odd_sum_square (n : Nat) :
    SumUpTo (fun i => 2 * i - 1) n = n * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        SumUpTo (fun i => 2 * i - 1) (n + 1)
            = SumUpTo (fun i => 2 * i - 1) n + (2 * (n + 1) - 1) := by
                rw [SumUpTo.succ]
        _ = n * n + (2 * (n + 1) - 1) := by
                rw [ih]
        _ = (n + 1) * (n + 1) := by
                simp [Nat.left_distrib, Nat.right_distrib,
                  Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                omega

end NatSum

end Foundation
end FoC
