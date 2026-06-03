set_option doc.verso true

/-!
# Natural-number divisibility and parity

## Divisibility and parity

This module supplies the elementary natural-number predicates used by the proof
examples in Chapter 1.  Divisibility is represented directly by an existential
factor, and evenness and oddness are phrased in terms of that representation.

The statements here are deliberately small: they are the reusable arithmetic
facts needed by the book-facing files, not a replacement for a full arithmetic
library.
-/

namespace FoC
namespace Foundation

namespace NatPred

/-!
# Natural-number predicates

Divisibility is represented by an explicit factor.  The even and odd predicates
are then phrased in the same elementary language used by the textbook examples.
-/

def Divides (a b : Nat) : Prop :=
  exists k, b = a * k

def Even (n : Nat) : Prop :=
  Divides 2 n

def Odd (n : Nat) : Prop :=
  exists k, n = 2 * k + 1

/-!
# Divisibility laws

The first reusable facts are reflexivity and transitivity of divisibility.
-/

theorem divides_refl (n : Nat) : Divides n n := by
  exists 1
  exact (Nat.mul_one n).symm

theorem divides_trans {a b c : Nat} (hab : Divides a b) (hbc : Divides b c) :
    Divides a c := by
  cases hab with
  | intro k hk =>
      cases hbc with
      | intro l hl =>
          exists k * l
          rw [hl, hk, Nat.mul_assoc]

/-!
# Parity witnesses

The concrete parity constructors provide standard witnesses for zero, one,
doubles, and double-plus-one numbers.
-/

theorem even_zero : Even 0 := by
  exact Exists.intro 0 rfl

theorem odd_one : Odd 1 := by
  exact Exists.intro 0 rfl

theorem even_double (n : Nat) : Even (2 * n) := by
  exact Exists.intro n rfl

theorem odd_double_add_one (n : Nat) : Odd (2 * n + 1) := by
  exact Exists.intro n rfl

end NatPred

end Foundation
end FoC
