import FoC.Foundation.Integers
import FoC.Foundation.Primes
import FoC.Foundation.RationalCore
import FoC.Foundation.QuadraticSurd

namespace FoC
namespace Book
namespace Chapter01
namespace Section07

/-!
Book: Chapter 1, Section 1.7, Proof by Contradiction.

Full real-number wrappers remain classified in coverage because the standalone
project intentionally does not yet build real numbers.  The reduced-rational
square-root contradiction cores and prime-factor existence are formalized in
the foundation.
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

-- Book: Chapter 1, Section 1.7, formal core for the `sqrt(2)` exercise.
theorem no_reduced_rational_square_root_two (q : PositiveRatRep)
    (hred : q.Reduced) : ¬ q.SquareRootOfNat 2 :=
  PositiveRatRep.no_reduced_square_root_two q hred

-- Book: Chapter 1, Section 1.7, Theorem: `sqrt(3)` is irrational.
theorem no_reduced_rational_square_root_three (q : PositiveRatRep)
    (hred : q.Reduced) : ¬ q.SquareRootOfNat 3 :=
  PositiveRatRep.no_reduced_square_root_three q hred

-- Book: Chapter 1, Sections 1.6-1.7, `sqrt(2)` surrogate before full reals.
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

end Section07
end Chapter01
end Book
end FoC
