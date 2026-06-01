import FoC.Foundation.Integers

namespace FoC
namespace Book
namespace Chapter01
namespace Section07

/-!
Book: Chapter 1, Section 1.7, Proof by Contradiction.

The real-number irrationality and Euclid-prime examples are classified in
coverage as currently informal for the standalone project, because the project
has not yet built rationals, real numbers, or prime-factor theory.
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

end Section07
end Chapter01
end Book
end FoC
