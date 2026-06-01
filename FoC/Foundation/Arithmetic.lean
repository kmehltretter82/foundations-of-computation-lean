namespace FoC
namespace Foundation

/-!
Small arithmetic predicates used by proof examples in Chapter 1.
-/

namespace NatPred

def Divides (a b : Nat) : Prop :=
  exists k, b = a * k

def Even (n : Nat) : Prop :=
  Divides 2 n

def Odd (n : Nat) : Prop :=
  exists k, n = 2 * k + 1

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
