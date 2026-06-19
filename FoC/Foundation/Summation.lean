set_option doc.verso true

/-!
# Finite sums and induction examples

## Recursive finite sums

Chapter 1 introduces induction through closed forms for finite sums and related
recursive identities.  This module records the recursive sum operators and the
algebraic lemmas used to state those examples in Lean.

## Book coordinates

Used by:
- Chapter 1, Section 1.8: Mathematical Induction
- Chapter 1, Section 1.10: Recursive Definitions
- Chapter 2, Section 2.6: finite cardinality arithmetic, later
-/

namespace FoC
namespace Foundation

namespace NatSum

/-!
# Recursive sums

The two summation operators cover sums from {lit}`1` to {lit}`n` and from
{lit}`0` to {lit}`n`.
-/

def SumUpTo (f : Nat -> Nat) : Nat -> Nat
  | 0 => 0
  | n + 1 => SumUpTo f n + f (n + 1)

def SumZeroTo (f : Nat -> Nat) : Nat -> Nat
  | 0 => f 0
  | n + 1 => SumZeroTo f n + f (n + 1)

def WeightedPowerTerm (i : Nat) : Nat :=
  i * 2 ^ (i - 1)

/-!
# Unfolding laws

These equations expose the successor cases used in induction proofs.
-/

theorem SumUpTo.succ (f : Nat -> Nat) (n : Nat) :
    SumUpTo f (n + 1) = SumUpTo f n + f (n + 1) :=
  rfl

theorem SumZeroTo.succ (f : Nat -> Nat) (n : Nat) :
    SumZeroTo f (n + 1) = SumZeroTo f n + f (n + 1) :=
  rfl

namespace GeometricSeries

/-!
## Algebraic geometric-series core

The textbook's arbitrary-base geometric-series proof is an induction that uses
only a small package of ring-style laws. This self-contained project does not
import Mathlib's algebra hierarchy, so the laws are recorded explicitly here.

The theorem below is representation-independent: any future real-number layer
that proves these laws can instantiate the book formula immediately.
-/

structure Algebra (α : Type u) [Zero α] [One α] [Add α] [Neg α] [Sub α]
    [Mul α] where
  add_assoc : forall a b c : α, (a + b) + c = a + (b + c)
  zero_add : forall a : α, 0 + a = a
  neg_add_cancel : forall a : α, -a + a = 0
  sub_eq_add_neg : forall a b : α, a - b = a + -b
  one_mul : forall a : α, 1 * a = a
  mul_one : forall a : α, a * 1 = a
  left_distrib : forall a b c : α, a * (b + c) = a * b + a * c
  right_distrib : forall a b c : α, (a + b) * c = a * c + b * c
  mul_neg : forall a b : α, a * -b = -(a * b)

def Pow {α : Type u} [One α] [Mul α] (x : α) : Nat -> α
  | 0 => 1
  | n + 1 => Pow x n * x

def Sum {α : Type u} [One α] [Add α] [Mul α] (x : α) : Nat -> α
  | 0 => 1
  | n + 1 => Sum x n + Pow x (n + 1)

theorem add_neg_middle
    {α : Type u} [Zero α] [One α] [Add α] [Neg α] [Sub α] [Mul α]
    (laws : Algebra α) (a b c : α) :
    (a + -b) + (b + c) = a + c := by
  calc
    (a + -b) + (b + c) = a + (-b + (b + c)) :=
      laws.add_assoc a (-b) (b + c)
    _ = a + ((-b + b) + c) := by
      rw [← laws.add_assoc (-b) b c]
    _ = a + (0 + c) := by
      rw [laws.neg_add_cancel]
    _ = a + c := by
      rw [laws.zero_add]

theorem mul_one_sub
    {α : Type u} [Zero α] [One α] [Add α] [Neg α] [Sub α] [Mul α]
    (laws : Algebra α) (x : α) (n : Nat) :
    Sum x n * (1 - x) = 1 - Pow x (n + 1) := by
  induction n with
  | zero =>
      calc
        Sum x 0 * (1 - x) = 1 * (1 - x) := rfl
        _ = 1 - x := laws.one_mul (1 - x)
        _ = 1 - Pow x (0 + 1) := by
          change 1 - x = 1 - (1 * x)
          rw [laws.one_mul]
  | succ n ih =>
      let p := Pow x (n + 1)
      have hpow : Pow x (n + 1 + 1) = p * x := rfl
      calc
        Sum x (n + 1) * (1 - x) =
            (Sum x n + p) * (1 - x) := rfl
        _ = Sum x n * (1 - x) + p * (1 - x) := by
          rw [laws.right_distrib]
        _ = (1 - p) + p * (1 - x) := by
          rw [ih]
        _ = (1 + -p) + p * (1 + -x) := by
          rw [laws.sub_eq_add_neg, laws.sub_eq_add_neg]
        _ = (1 + -p) + (p * 1 + p * -x) := by
          rw [laws.left_distrib]
        _ = (1 + -p) + (p + -(p * x)) := by
          rw [laws.mul_one, laws.mul_neg]
        _ = 1 + -(p * x) := by
          exact add_neg_middle laws 1 p (-(p * x))
        _ = 1 - p * x := by
          rw [laws.sub_eq_add_neg]
        _ = 1 - Pow x (n + 1 + 1) := by
          rw [hpow]

end GeometricSeries

/-!
# Closed forms

The main statements prove the finite-sum identities used in the induction
examples and exercises.
-/

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

/-!
Theorem 1.12 gives the closed form for the sum of the first {lit}`n` positive
integers.
-/
theorem sum_identity_closed_form (n : Nat) :
    SumUpTo (fun i => i) n = n * (n + 1) / 2 := by
  have h := two_mul_sum_identity n
  omega

theorem even_sum_closed_form (n : Nat) :
    SumUpTo (fun i => 2 * i) n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        SumUpTo (fun i => 2 * i) (n + 1)
            = SumUpTo (fun i => 2 * i) n + 2 * (n + 1) := by
                rw [SumUpTo.succ]
        _ = n * (n + 1) + 2 * (n + 1) := by
                rw [ih]
        _ = (n + 1) * (n + 1 + 1) := by
                simp [Nat.left_distrib, Nat.right_distrib,
                  Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
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

/-!
Theorem 1.13 is the weighted power-sum identity used as a second induction
example.
-/
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

/-!
Exercise 4 is the finite geometric sum for powers of two.
-/
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

/-!
Exercise 2 is recorded in a division-free natural-number form, avoiding a field
development while preserving the inductive identity.
-/
theorem geometric_successor_base_sum (b n : Nat) :
    b * SumZeroTo (fun i => (b + 1) ^ i) n = (b + 1) ^ (n + 1) - 1 := by
  induction n with
  | zero =>
      simp [SumZeroTo]
  | succ n ih =>
      calc
        b * SumZeroTo (fun i => (b + 1) ^ i) (n + 1)
            = b * (SumZeroTo (fun i => (b + 1) ^ i) n + (b + 1) ^ (n + 1)) := by
                rw [SumZeroTo.succ]
        _ = b * SumZeroTo (fun i => (b + 1) ^ i) n + b * (b + 1) ^ (n + 1) := by
                rw [Nat.mul_add]
        _ = ((b + 1) ^ (n + 1) - 1) + b * (b + 1) ^ (n + 1) := by
                rw [ih]
        _ = (b + 1) ^ (n + 1 + 1) - 1 := by
                rw [show (b + 1) ^ (n + 1 + 1) = (b + 1) ^ (n + 1) * (b + 1) by
                  rw [Nat.pow_succ]]
                have hpos : 0 < (b + 1) ^ (n + 1) := Nat.pow_pos (Nat.succ_pos b)
                simp [Nat.add_mul, Nat.mul_comm]
                omega

/-!
Exercise 6 states the classic identity that the sum of the first {lit}`n` odd
numbers is {lit}`n ^ 2`.
-/
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
