import FoC.Book.Chapter01.Section08

namespace FoC
namespace Book
namespace Chapter01
namespace Section10

/-!
Book: Chapter 1, Section 1.10, Recursive Definitions.
-/

def fib : Nat -> Nat :=
  Section08.fib

-- Book: Chapter 1, Section 1.10
theorem fib_zero : fib 0 = 0 :=
  rfl

-- Book: Chapter 1, Section 1.10
theorem fib_one : fib 1 = 1 :=
  rfl

-- Book: Chapter 1, Section 1.10
theorem fib_recurrence (n : Nat) : fib (n + 2) = fib (n + 1) + fib n :=
  rfl

-- Book: Chapter 1, Section 1.10, Exercise 1
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

end Section10
end Chapter01
end Book
end FoC
