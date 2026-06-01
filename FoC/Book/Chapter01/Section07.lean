namespace FoC
namespace Book
namespace Chapter01
namespace Section07

/-!
Book: Chapter 1, Section 1.7, Proof by Contradiction.

The real-number irrationality and Euclid-prime examples are classified in
coverage as currently informal for the standalone project, because the project
has not yet built integers, rationals, real numbers, or prime-factor theory.
-/

-- Book: Chapter 1, Section 1.7, proof by contradiction schema
theorem proof_by_contradiction_schema (p : Prop) : (¬ p -> False) -> p := by
  intro h
  exact Classical.byContradiction h

-- Book: Chapter 1, Section 1.7
theorem contradiction_elim {p q : Prop} (hp : p) (hnp : ¬ p) : q := by
  exact False.elim (hnp hp)

end Section07
end Chapter01
end Book
end FoC

