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

end Section08
end Chapter01
end Book
end FoC
