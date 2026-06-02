import FoC.Foundation.Integers
import FoC.Foundation.Functions
import FoC.Foundation.Primes
import FoC.Foundation.RationalCore
import FoC.Foundation.QuadraticSurd
import FoC.Foundation.Reals

namespace FoC
namespace Book
namespace Chapter01
namespace Section07

/-!
Book: Chapter 1, Section 1.7, Proof by Contradiction.

Concrete square-root cuts now exist as Dedekind-cut candidates, but their
square-equality proofs are still deferred.  The reduced-rational and
quotient-rational square-root contradiction cores, real square-characterization
irrationality bridges, prime-factor existence, Dedekind-cut real order layer,
and real multiplication are formalized in the foundation.
-/

open Foundation

-- Book: Chapter 1, Section 1.7, proof by contradiction schema
theorem proof_by_contradiction_schema (p : Prop) : (¬ p -> False) -> p := by
  intro h
  exact Classical.byContradiction h

-- Book: Chapter 1, Section 1.7
theorem contradiction_elim {p q : Prop} (hp : p) (hnp : ¬ p) : q := by
  exact False.elim (hnp hp)

-- Book: Chapter 1, Section 1.7, integer contradiction infrastructure.
theorem odd_integer_square_not_even {n : Int}
    (h : IntPred.Odd n) : ¬ IntPred.Even (n * n) :=
  IntPred.odd_square_not_even h

-- Book: Chapter 1, Section 1.7, prime divisor theorem.
theorem prime_divisor_exists (n : Nat) (hn : 1 < n) :
    exists p, NatPrime.Prime p ∧ NatPred.Divides p n :=
  NatPrime.prime_divisor_exists n hn

-- Book: Chapter 1, Section 1.7, Euclid infinitude-of-primes core.
theorem euclid_prime_not_in_finite_prime_list (ps : List Nat)
    (hps : NatPrime.AllPrime ps) :
    exists p, NatPrime.Prime p ∧ p ∉ ps :=
  NatPrime.exists_prime_not_in_list ps hps

-- Book: Chapter 1, Section 1.7, pigeonhole-principle collision core.
theorem pigeonhole_collision_schema {alpha : Type u} {beta : Type v}
    {f : alpha -> beta} (h : ¬ Fn.Injective f) :
    exists x y, x ≠ y ∧ f x = f y :=
  Fn.collision_of_not_injective h

-- Book: Chapter 1, Section 1.7, formal core for the `sqrt(2)` exercise.
theorem no_reduced_rational_square_root_two (q : PositiveRatRep)
    (hred : q.Reduced) : ¬ q.SquareRootOfNat 2 :=
  PositiveRatRep.no_reduced_square_root_two q hred

-- Book: Chapter 1, Section 1.7, Theorem: `sqrt(3)` is irrational.
theorem no_reduced_rational_square_root_three (q : PositiveRatRep)
    (hred : q.Reduced) : ¬ q.SquareRootOfNat 3 :=
  PositiveRatRep.no_reduced_square_root_three q hred

-- Book: Chapter 1, Section 1.7, quotient-rational form of `sqrt(2)` irrationality.
theorem no_quotient_rational_square_root_two (q : QRat) :
    q * q ≠ QRat.ofNat 2 :=
  QRat.no_square_root_two q

-- Book: Chapter 1, Section 1.7, quotient-rational form of `sqrt(3)` irrationality.
theorem no_quotient_rational_square_root_three (q : QRat) :
    q * q ≠ QRat.ofNat 3 :=
  QRat.no_square_root_three q

-- Book: Chapter 1, Sections 1.6-1.7, `sqrt(2)` surrogate before square equalities.
theorem sqrt_two_surrogate_irrational :
    Quad2.IrrationalLike Quad2.sqrtTwo :=
  Quad2.sqrtTwo_irrationalLike

-- Book: Chapter 1, Section 1.6, Exercise 8(d) counterexample core.
theorem product_of_irrational_surrogates_can_be_rational :
    Quad2.RationalLike (Quad2.mul Quad2.sqrtTwo Quad2.sqrtTwo) :=
  Quad2.sqrtTwo_mul_self_rationalLike

theorem sqrt_two_surrogate_square_eq_two :
    Quad2.mul Quad2.sqrtTwo Quad2.sqrtTwo = Quad2.ofInt 2 :=
  Quad2.sqrtTwo_mul_self_eq_two

-- Book: Chapter 1, Section 1.7, negating an irrational real stays irrational.
theorem negation_of_irrational_real_is_irrational {x : Real}
    (hx : Real.Irrational x) : Real.Irrational (-x) :=
  Real.irrational_neg hx

-- Book: Chapter 1, Section 1.7, rational plus irrational is irrational.
theorem rational_real_plus_irrational_is_irrational
    {x : Real} {q : QRat} (hx : Real.Irrational x) :
    Real.Irrational (Real.qreal q + x) :=
  Real.irrational_qreal_add hx

-- Book: Chapter 1, Section 1.7, irrational plus rational is irrational.
theorem irrational_plus_rational_real_is_irrational
    {x : Real} {q : QRat} (hx : Real.Irrational x) :
    Real.Irrational (x + Real.qreal q) :=
  Real.irrational_add_qreal hx

-- Book: Chapter 1, Section 1.7, nonzero rational scaling preserves irrationality.
theorem nonzero_rational_real_times_irrational_is_irrational
    {x : Real} {q : QRat} (hq : q ≠ 0) (hx : Real.Irrational x) :
    Real.Irrational (Real.scale q x) :=
  Real.irrational_scale_nonzero hq hx

-- Book: Chapter 1, Section 1.7, concrete Dedekind-cut candidate for `sqrt(2)`.
theorem sqrt_two_cut_nonnegative :
    (0 : Real) ≤ Real.sqrtTwoCut :=
  Real.sqrtTwoCut_nonneg

-- Book: Chapter 1, Section 1.7, concrete Dedekind-cut candidate for `sqrt(3)`.
theorem sqrt_three_cut_nonnegative :
    (0 : Real) ≤ Real.sqrtThreeCut :=
  Real.sqrtThreeCut_nonneg

-- Book: Chapter 1, Section 1.7, real bridge for a future `sqrt(2)` cut.
theorem real_with_square_two_characterization_is_irrational {x : Real}
    (hsquare : Real.qrealSquareCharacterization x 2) :
    Real.Irrational x :=
  Real.irrational_of_qreal_square_eq_two hsquare

-- Book: Chapter 1, Section 1.7, real bridge for a future `sqrt(3)` cut.
theorem real_with_square_three_characterization_is_irrational {x : Real}
    (hsquare : Real.qrealSquareCharacterization x 3) :
    Real.Irrational x :=
  Real.irrational_of_qreal_square_eq_three hsquare

end Section07
end Chapter01
end Book
end FoC
