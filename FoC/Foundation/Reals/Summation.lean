import FoC.Foundation.Summation
import FoC.Foundation.Reals.Basic

set_option doc.verso true

/-!
# Dedekind-real geometric series

This module is the semantic bridge between the representation-independent
geometric-series development in {module}`FoC.Foundation.Summation` and the
Dedekind-cut real implementation. It records the power representation bridge
and packages exactly the real algebra laws needed by the generic induction.
-/

namespace FoC
namespace Foundation
namespace RealGeometricSeries

noncomputable abbrev Sum (x : Real) : Nat -> Real :=
  NatSum.GeometricSeries.Sum x

theorem powNat_eq_algebraic_pow (x : Real) (n : Nat) :
    Real.powNat x n = NatSum.GeometricSeries.Pow x n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        Real.powNat x (n + 1) = Real.powNat x n * x := rfl
        _ = NatSum.GeometricSeries.Pow x n * x := by rw [ih]
        _ = NatSum.GeometricSeries.Pow x (n + 1) := rfl

abbrev Algebra : Prop :=
  NatSum.GeometricSeries.Algebra Real

theorem algebra : Algebra := by
  exact {
    add_assoc := Real.add_assoc
    zero_add := Real.zero_add
    neg_add_cancel := Real.neg_add_cancel
    sub_eq_add_neg := Real.sub_eq_add_neg
    one_mul := Real.one_mul
    mul_one := Real.mul_one
    left_distrib := Real.left_distrib
    right_distrib := Real.right_distrib
    mul_neg := Real.mul_neg
  }

theorem mul_one_sub_of_algebra (laws : Algebra) (x : Real) (n : Nat) :
    Sum x n * (1 - x) = 1 - Real.powNat x (n + 1) := by
  have h := NatSum.GeometricSeries.mul_one_sub laws x n
  rw [powNat_eq_algebraic_pow]
  exact h

theorem mul_one_sub (x : Real) (n : Nat) :
    Sum x n * (1 - x) = 1 - Real.powNat x (n + 1) :=
  mul_one_sub_of_algebra algebra x n

end RealGeometricSeries
end Foundation
end FoC
