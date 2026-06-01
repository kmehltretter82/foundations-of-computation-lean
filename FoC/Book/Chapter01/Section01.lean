import FoC.Foundation.Logic

namespace FoC
namespace Book
namespace Chapter01
namespace Section01

/-!
Book: Chapter 1, Section 1.1, Propositional Logic.

The reusable syntax and semantics live in `FoC.Foundation.Logic`. This file
contains book-indexed statements for the first pass through the section.
-/

open Foundation

-- Book: Chapter 1, Section 1.1, Definition 1.1
theorem definition_1_1_and_eval (valuation : Var -> Bool) (p q : PropForm Var) :
    PropForm.eval valuation (PropForm.and p q) =
      (PropForm.eval valuation p && PropForm.eval valuation q) :=
  rfl

-- Book: Chapter 1, Section 1.1, Definition 1.1
theorem definition_1_1_or_eval (valuation : Var -> Bool) (p q : PropForm Var) :
    PropForm.eval valuation (PropForm.or p q) =
      (PropForm.eval valuation p || PropForm.eval valuation q) :=
  rfl

-- Book: Chapter 1, Section 1.1, Definition 1.1
theorem definition_1_1_not_eval (valuation : Var -> Bool) (p : PropForm Var) :
    PropForm.eval valuation (PropForm.not p) = !(PropForm.eval valuation p) :=
  rfl

-- Book: Chapter 1, Section 1.1, Definition 1.2
theorem definition_1_2_imp_eval (valuation : Var -> Bool) (p q : PropForm Var) :
    PropForm.eval valuation (PropForm.imp p q) =
      (!(PropForm.eval valuation p) || PropForm.eval valuation q) :=
  rfl

-- Book: Chapter 1, Section 1.1, Definition 1.2
theorem definition_1_2_iff_eval (valuation : Var -> Bool) (p q : PropForm Var) :
    PropForm.eval valuation (PropForm.iff p q) =
      (PropForm.eval valuation p == PropForm.eval valuation q) :=
  rfl

-- Book: Chapter 1, Section 1.1, Definition 1.2
theorem definition_1_2_xor_eval (valuation : Var -> Bool) (p q : PropForm Var) :
    PropForm.eval valuation (PropForm.xor p q) =
      ((PropForm.eval valuation p && !(PropForm.eval valuation q)) ||
        (!(PropForm.eval valuation p) && PropForm.eval valuation q)) :=
  rfl

-- Book: Chapter 1, Section 1.1, Definition 1.3
theorem definition_1_3_not_tautology_iff_contradiction (p : PropForm Var) :
    PropForm.Tautology (PropForm.not p) <-> PropForm.Contradiction p :=
  PropForm.tautology_not_iff_contradiction p

-- Book: Chapter 1, Section 1.1, Definition 1.4
theorem definition_1_4_logical_equivalence_via_iff (p q : PropForm Var) :
    PropForm.LogicallyEquivalent p q <-> PropForm.Tautology (PropForm.iff p q) :=
  PropForm.logicallyEquivalent_iff_iff_tautology p q

-- Book: Chapter 1, Section 1.1, Figure 1.1
theorem figure_1_1_and_associative (p q r : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.and (PropForm.and p q) r)
      (PropForm.and p (PropForm.and q r)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    cases hr : PropForm.eval valuation r <;>
    simp [PropForm.eval, hp, hq, hr]

-- Book: Chapter 1, Section 1.1
theorem implication_equiv_not_or (p q : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.imp p q)
      (PropForm.or (PropForm.not p) q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

-- Book: Chapter 1, Section 1.1
theorem implication_equiv_contrapositive (p q : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.imp p q)
      (PropForm.imp (PropForm.not q) (PropForm.not p)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

-- Book: Chapter 1, Section 1.1
theorem biconditional_equiv_two_implications (p q : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.iff p q)
      (PropForm.and (PropForm.imp p q) (PropForm.imp q p)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

-- Book: Chapter 1, Section 1.1
theorem xor_equiv_or_and_not_and (p q : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.xor p q)
      (PropForm.and (PropForm.or p q) (PropForm.not (PropForm.and p q))) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

-- Book: Chapter 1, Section 1.1, example before Definition 1.4
theorem example_tautology_disjunctive_syllogism (p q : PropForm Var) :
    PropForm.Tautology
      (PropForm.imp (PropForm.and (PropForm.or p q) (PropForm.not q)) p) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

-- Book: Chapter 1, Section 1.1, Exercise 4(a)
theorem exercise_4a_modus_ponens (p q : PropForm Var) :
    PropForm.Tautology
      (PropForm.imp (PropForm.and p (PropForm.imp p q)) q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

-- Book: Chapter 1, Section 1.1, Exercise 4(b)
theorem exercise_4b_hypothetical_syllogism (p q r : PropForm Var) :
    PropForm.Tautology
      (PropForm.imp (PropForm.and (PropForm.imp p q) (PropForm.imp q r)) (PropForm.imp p r)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    cases hr : PropForm.eval valuation r <;>
    simp [PropForm.eval, hp, hq, hr]

-- Book: Chapter 1, Section 1.1, Exercise 4(c)
theorem exercise_4c_contradiction (p : PropForm Var) :
    PropForm.Contradiction (PropForm.and p (PropForm.not p)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    simp [PropForm.eval, hp]

-- Book: Chapter 1, Section 1.1, Exercise 4(e)
theorem exercise_4e_excluded_middle (p : PropForm Var) :
    PropForm.Tautology (PropForm.or p (PropForm.not p)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    simp [PropForm.eval, hp]

-- Book: Chapter 1, Section 1.1, Exercise 4(f)
theorem exercise_4f_and_implies_or (p q : PropForm Var) :
    PropForm.Tautology (PropForm.imp (PropForm.and p q) (PropForm.or p q)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

-- Book: Chapter 1, Section 1.1, Exercise 5(a)
theorem exercise_5a_iff_as_two_implications (p q : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.and (PropForm.imp p q) (PropForm.imp q p))
      (PropForm.iff p q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

-- Book: Chapter 1, Section 1.1, Exercise 5(b)
theorem exercise_5b_iff_of_negations (p q : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.iff (PropForm.not p) (PropForm.not q))
      (PropForm.iff p q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

-- Book: Chapter 1, Section 1.1, Exercise 5(c)
theorem exercise_5c_iff_from_forward_and_reverse_negative (p q : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.and (PropForm.imp p q) (PropForm.imp (PropForm.not p) (PropForm.not q)))
      (PropForm.iff p q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

-- Book: Chapter 1, Section 1.1, Exercise 5(d)
theorem exercise_5d_iff_as_not_xor (p q : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.not (PropForm.xor p q))
      (PropForm.iff p q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

end Section01
end Chapter01
end Book
end FoC
