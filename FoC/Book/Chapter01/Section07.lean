import FoC.Foundation.Integers
import FoC.Foundation.Functions
import FoC.Foundation.Cardinality
import FoC.Foundation.Primes
import FoC.Foundation.RationalCore
import FoC.Foundation.QuadraticSurd
import FoC.Foundation.Reals

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter01
namespace Section07

/-!
# Chapter 1, Section 1.7: Proof by Contradiction

Concrete square-root cuts now exist as Dedekind-cut candidates, but their
square-equality proofs are still deferred.  The reduced-rational and
quotient-rational square-root contradiction cores, direct real square-equality
irrationality bridges, prime-factor existence, Dedekind-cut real order layer,
and real multiplication are formalized in the foundation.

The section begins with proof-by-contradiction vocabulary, then formalizes the
number-theoretic examples: odd-square contradiction, prime-divisor existence,
Euclid's finite-list theorem for primes, finite pigeonhole vocabulary, and
square-root irrationality cores.

The common pattern is to assume the opposite of the target statement and
derive an impossible combination of facts. In the finite-prime theorem, the
contradiction comes from constructing a prime divisor outside a proposed list.
In the square-root examples, the contradiction comes from divisibility facts
for a reduced rational representative.
-/

open Foundation

/-! Proof by contradiction: if assuming not-p gives false, then p follows. -/
theorem proof_by_contradiction_schema (p : Prop) : (¬ p -> False) -> p := by
  intro h
  exact Classical.byContradiction h

theorem contradiction_elim {p q : Prop} (hp : p) (hnp : ¬ p) : q := by
  exact False.elim (hnp hp)

theorem odd_integer_square_not_even {n : Int}
    (h : IntPred.Odd n) : ¬ IntPred.Even (n * n) :=
  IntPred.odd_square_not_even h

theorem prime_divisor_exists (n : Nat) (hn : 1 < n) :
    exists p, NatPrime.Prime p ∧ NatPred.Divides p n :=
  NatPrime.prime_divisor_exists n hn

theorem euclid_prime_not_in_finite_prime_list (ps : List Nat)
    (hps : NatPrime.AllPrime ps) :
    exists p, NatPrime.Prime p ∧ p ∉ ps :=
  NatPrime.exists_prime_not_in_list ps hps

theorem pigeonhole_collision_schema {alpha : Type u} {beta : Type v}
    {f : alpha -> beta} (h : ¬ Fn.Injective f) :
    exists x y, x ≠ y ∧ f x = f y :=
  Fn.collision_of_not_injective h

theorem finite_cardinality_pigeonhole_collision
    {alpha : Type u} {beta : Type v} [DecidableEq beta]
    {A : FSet alpha} {B : FSet beta} {m n : Nat}
    (hA : FSet.HasCardinality A m) (hB : FSet.HasCardinality B n)
    (hlt : n < m) (f : alpha -> beta)
    (hmap : forall x, x ∈ A -> f x ∈ B) :
    exists x y, x ∈ A ∧ y ∈ A ∧ x ≠ y ∧ f x = f y :=
  FSet.pigeonhole_collision_of_cardinality_lt hA hB hlt f hmap

theorem finite_cardinality_pigeonhole_not_injective
    {alpha : Type u} {beta : Type v} [DecidableEq beta]
    {A : FSet alpha} {B : FSet beta} {m n : Nat}
    (hA : FSet.HasCardinality A m) (hB : FSet.HasCardinality B n)
    (hlt : n < m) (f : alpha -> beta)
    (hmap : forall x, x ∈ A -> f x ∈ B) :
    ¬ Fn.Injective f :=
  FSet.not_injective_of_cardinality_lt_maps_to hA hB hlt f hmap

/-!
# Square-Root Irrationality Cores

The reduced-rational and quotient-rational theorems are the formal core of the
sqrt(2) and sqrt(3) irrationality arguments. The later real bridges say that
any real whose square has the relevant value is irrational.

The formalization separates the textbook proof into layers. First, no reduced
rational representative can square to 2 or 3. Second, the quotient-rational
version removes dependence on a chosen representative. Third, real-number
bridge theorems turn ordinary square equations into irrationality statements.
-/

theorem no_reduced_rational_square_root_two (q : PositiveRatRep)
    (hred : q.Reduced) : ¬ q.SquareRootOfNat 2 :=
  PositiveRatRep.no_reduced_square_root_two q hred

theorem no_reduced_rational_square_root_three (q : PositiveRatRep)
    (hred : q.Reduced) : ¬ q.SquareRootOfNat 3 :=
  PositiveRatRep.no_reduced_square_root_three q hred

theorem no_quotient_rational_square_root_two (q : QRat) :
    q * q ≠ QRat.ofNat 2 :=
  QRat.no_square_root_two q

theorem no_quotient_rational_square_root_three (q : QRat) :
    q * q ≠ QRat.ofNat 3 :=
  QRat.no_square_root_three q

theorem sqrt_two_surrogate_irrational :
    Quad2.IrrationalLike Quad2.sqrtTwo :=
  Quad2.sqrtTwo_irrationalLike

theorem product_of_irrational_surrogates_can_be_rational :
    Quad2.RationalLike (Quad2.mul Quad2.sqrtTwo Quad2.sqrtTwo) :=
  Quad2.sqrtTwo_mul_self_rationalLike

theorem sqrt_two_surrogate_square_eq_two :
    Quad2.mul Quad2.sqrtTwo Quad2.sqrtTwo = Quad2.ofInt 2 :=
  Quad2.sqrtTwo_mul_self_eq_two

theorem negation_of_irrational_real_is_irrational {x : Real}
    (hx : Real.Irrational x) : Real.Irrational (-x) :=
  Real.irrational_neg hx

theorem rational_real_plus_irrational_is_irrational
    {x : Real} {q : QRat} (hx : Real.Irrational x) :
    Real.Irrational (Real.qreal q + x) :=
  Real.irrational_qreal_add hx

theorem irrational_plus_rational_real_is_irrational
    {x : Real} {q : QRat} (hx : Real.Irrational x) :
    Real.Irrational (x + Real.qreal q) :=
  Real.irrational_add_qreal hx

theorem nonzero_rational_real_times_irrational_is_irrational
    {x : Real} {q : QRat} (hq : q ≠ 0) (hx : Real.Irrational x) :
    Real.Irrational (Real.scale q x) :=
  Real.irrational_scale_nonzero hq hx

theorem sqrt_two_cut_nonnegative :
    (0 : Real) ≤ Real.sqrtTwoCut :=
  Real.sqrtTwoCut_nonneg

theorem sqrt_three_cut_nonnegative :
    (0 : Real) ≤ Real.sqrtThreeCut :=
  Real.sqrtThreeCut_nonneg

theorem real_with_square_two_characterization_is_irrational {x : Real}
    (hsquare : Real.qrealSquareCharacterization x 2) :
    Real.Irrational x :=
  Real.irrational_of_qreal_square_eq_two hsquare

theorem real_with_square_three_characterization_is_irrational {x : Real}
    (hsquare : Real.qrealSquareCharacterization x 3) :
    Real.Irrational x :=
  Real.irrational_of_qreal_square_eq_three hsquare

theorem real_with_square_two_is_irrational {x : Real}
    (hsquare : x * x = (2 : Real)) :
    Real.Irrational x :=
  Real.irrational_of_square_eq_two hsquare

theorem real_with_square_three_is_irrational {x : Real}
    (hsquare : x * x = (3 : Real)) :
    Real.Irrational x :=
  Real.irrational_of_square_eq_three hsquare

theorem rational_real_cannot_square_to_two {x : Real}
    (hx : Real.Rational x) : x * x ≠ (2 : Real) :=
  Real.rational_not_square_eq_two hx

theorem rational_real_cannot_square_to_three {x : Real}
    (hx : Real.Rational x) : x * x ≠ (3 : Real) :=
  Real.rational_not_square_eq_three hx

end Section07
end Chapter01
end Book
end FoC
