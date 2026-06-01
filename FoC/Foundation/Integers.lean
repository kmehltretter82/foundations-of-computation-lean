namespace FoC
namespace Foundation

/-!
Standalone integer predicates for Chapter 1 proof examples.

Used by:
- Chapter 1, Section 1.6: Proof
- Chapter 1, Section 1.7: Proof by Contradiction
- Chapter 2, Section 2.6: countability of integers, later
-/

namespace IntPred

def Divides (a b : Int) : Prop :=
  exists k : Int, b = a * k

def Even (n : Int) : Prop :=
  exists k : Int, n = 2 * k

def Odd (n : Int) : Prop :=
  exists k : Int, n = 2 * k + 1

theorem divides_refl (n : Int) : Divides n n := by
  exists 1
  omega

theorem divides_trans {a b c : Int}
    (hab : Divides a b) (hbc : Divides b c) : Divides a c := by
  cases hab with
  | intro k hk =>
      cases hbc with
      | intro l hl =>
          exists k * l
          rw [hl, hk]
          ac_rfl

theorem divides_zero (a : Int) : Divides a 0 := by
  exists 0
  omega

theorem divides_mul_right {a b : Int} (h : Divides a b) (c : Int) :
    Divides a (b * c) := by
  cases h with
  | intro k hk =>
      exists k * c
      rw [hk]
      ac_rfl

theorem divides_mul_left {a b : Int} (h : Divides a b) (c : Int) :
    Divides a (c * b) := by
  cases h with
  | intro k hk =>
      exists c * k
      rw [hk]
      ac_rfl

theorem divides_add {a b c : Int}
    (hab : Divides a b) (hac : Divides a c) : Divides a (b + c) := by
  cases hab with
  | intro k hk =>
      cases hac with
      | intro l hl =>
          exists k + l
          rw [hk, hl, Int.mul_add]

theorem divides_sub {a b c : Int}
    (hab : Divides a b) (hac : Divides a c) : Divides a (b - c) := by
  cases hab with
  | intro k hk =>
      cases hac with
      | intro l hl =>
          exists k - l
          rw [hk, hl]
          rw [show a * (k - l) = a * k - a * l by rw [Int.mul_sub]]

theorem divides_square_of_divides {a n : Int} (h : Divides a n) :
    Divides a (n * n) :=
  divides_mul_right h n

theorem even_of_double (k : Int) : Even (2 * k) := by
  exists k

theorem odd_of_double_add_one (k : Int) : Odd (2 * k + 1) := by
  exists k

theorem three_odd : Odd 3 := by
  exists 1

theorem not_even_of_odd {n : Int} (hodd : Odd n) : ¬ Even n := by
  intro heven
  cases hodd with
  | intro k hk =>
      cases heven with
      | intro l hl =>
          omega

theorem not_odd_of_even {n : Int} (heven : Even n) : ¬ Odd n := by
  intro hodd
  exact not_even_of_odd hodd heven

theorem even_add {m n : Int} (hm : Even m) (hn : Even n) : Even (m + n) := by
  cases hm with
  | intro k hk =>
      cases hn with
      | intro l hl =>
          exists k + l
          rw [hk, hl, Int.mul_add]

theorem even_mul_left {m n : Int} (hm : Even m) : Even (m * n) := by
  cases hm with
  | intro k hk =>
      exists k * n
      rw [hk]
      ac_rfl

theorem even_mul_right {m n : Int} (hn : Even n) : Even (m * n) := by
  cases hn with
  | intro k hk =>
      exists m * k
      rw [hk]
      ac_rfl

theorem odd_add_odd_even {m n : Int} (hm : Odd m) (hn : Odd n) : Even (m + n) := by
  cases hm with
  | intro k hk =>
      cases hn with
      | intro l hl =>
          exists k + l + 1
          rw [hk, hl]
          omega

-- Book: Chapter 1, Section 1.6, integer parity proof example.
theorem even_square {n : Int} (h : Even n) : Even (n * n) := by
  cases h with
  | intro k hk =>
      exists 2 * k * k
      rw [hk]
      ac_rfl

-- Book: Chapter 1, Section 1.6, Exercise 8(a).
theorem odd_square {n : Int} (h : Odd n) : Odd (n * n) := by
  cases h with
  | intro k hk =>
      exists 2 * k * k + 2 * k
      rw [hk]
      simp [Int.mul_add, Int.mul_comm, Int.mul_left_comm,
        Int.add_assoc, Int.add_comm, Int.add_left_comm]
      omega

theorem odd_square_not_even {n : Int} (h : Odd n) : ¬ Even (n * n) :=
  not_even_of_odd (odd_square h)

theorem not_four_divides_two : ¬ Divides 4 2 := by
  intro h
  cases h with
  | intro k hk =>
      omega

end IntPred

end Foundation
end FoC
