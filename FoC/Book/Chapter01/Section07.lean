import FoC.Foundation.Integers
import FoC.Foundation.Primes

namespace FoC
namespace Book
namespace Chapter01
namespace Section07

/-!
Book: Chapter 1, Section 1.7, Proof by Contradiction.

The real-number irrationality examples remain classified in coverage because
the standalone project intentionally does not yet build real numbers. Rational
representatives and prime-factor existence are formalized in the foundation.
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

end Section07
end Chapter01
end Book
end FoC
