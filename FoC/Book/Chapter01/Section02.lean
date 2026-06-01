import FoC.Foundation.Logic

namespace FoC
namespace Book
namespace Chapter01
namespace Section02

/-!
Book: Chapter 1, Section 1.2, Boolean Algebra.
-/

open Foundation

-- Book: Chapter 1, Section 1.2, Figure 1.2
theorem double_negation (p : PropForm Var) :
    PropForm.LogicallyEquivalent (PropForm.not (PropForm.not p)) p := by
  intro valuation
  cases hp : PropForm.eval valuation p <;> simp [PropForm.eval, hp]

-- Book: Chapter 1, Section 1.2, Figure 1.2
theorem excluded_middle (p : PropForm Var) :
    PropForm.LogicallyEquivalent (PropForm.or p (PropForm.not p)) PropForm.truth := by
  intro valuation
  cases hp : PropForm.eval valuation p <;> simp [PropForm.eval, hp]

-- Book: Chapter 1, Section 1.2, Figure 1.2
theorem contradiction_law (p : PropForm Var) :
    PropForm.LogicallyEquivalent (PropForm.and p (PropForm.not p)) PropForm.falsity := by
  intro valuation
  cases hp : PropForm.eval valuation p <;> simp [PropForm.eval, hp]

-- Book: Chapter 1, Section 1.2, Figure 1.2
theorem true_and_identity (p : PropForm Var) :
    PropForm.LogicallyEquivalent (PropForm.and PropForm.truth p) p := by
  intro valuation
  cases hp : PropForm.eval valuation p <;> simp [PropForm.eval, hp]

-- Book: Chapter 1, Section 1.2, Figure 1.2
theorem false_or_identity (p : PropForm Var) :
    PropForm.LogicallyEquivalent (PropForm.or PropForm.falsity p) p := by
  intro valuation
  cases hp : PropForm.eval valuation p <;> simp [PropForm.eval, hp]

-- Book: Chapter 1, Section 1.2, Figure 1.2
theorem and_idempotent (p : PropForm Var) :
    PropForm.LogicallyEquivalent (PropForm.and p p) p := by
  intro valuation
  cases hp : PropForm.eval valuation p <;> simp [PropForm.eval, hp]

-- Book: Chapter 1, Section 1.2, Figure 1.2
theorem or_idempotent (p : PropForm Var) :
    PropForm.LogicallyEquivalent (PropForm.or p p) p := by
  intro valuation
  cases hp : PropForm.eval valuation p <;> simp [PropForm.eval, hp]

-- Book: Chapter 1, Section 1.2, Figure 1.2
theorem and_commutative (p q : PropForm Var) :
    PropForm.LogicallyEquivalent (PropForm.and p q) (PropForm.and q p) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

-- Book: Chapter 1, Section 1.2, Figure 1.2
theorem or_commutative (p q : PropForm Var) :
    PropForm.LogicallyEquivalent (PropForm.or p q) (PropForm.or q p) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

-- Book: Chapter 1, Section 1.2, Figure 1.2
theorem and_associative (p q r : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.and (PropForm.and p q) r)
      (PropForm.and p (PropForm.and q r)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    cases hr : PropForm.eval valuation r <;>
    simp [PropForm.eval, hp, hq, hr]

-- Book: Chapter 1, Section 1.2, Figure 1.2
theorem or_associative (p q r : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.or (PropForm.or p q) r)
      (PropForm.or p (PropForm.or q r)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    cases hr : PropForm.eval valuation r <;>
    simp [PropForm.eval, hp, hq, hr]

-- Book: Chapter 1, Section 1.2, Figure 1.2
theorem and_distributive_over_or (p q r : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.and p (PropForm.or q r))
      (PropForm.or (PropForm.and p q) (PropForm.and p r)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    cases hr : PropForm.eval valuation r <;>
    simp [PropForm.eval, hp, hq, hr]

-- Book: Chapter 1, Section 1.2, Figure 1.2
theorem or_distributive_over_and (p q r : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.or p (PropForm.and q r))
      (PropForm.and (PropForm.or p q) (PropForm.or p r)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    cases hr : PropForm.eval valuation r <;>
    simp [PropForm.eval, hp, hq, hr]

-- Book: Chapter 1, Section 1.2, Figure 1.2
theorem demorgan_and (p q : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.not (PropForm.and p q))
      (PropForm.or (PropForm.not p) (PropForm.not q)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

-- Book: Chapter 1, Section 1.2, Figure 1.2
theorem demorgan_or (p q : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.not (PropForm.or p q))
      (PropForm.and (PropForm.not p) (PropForm.not q)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

-- Book: Chapter 1, Section 1.2, Theorem 1.1, First Substitution Law
theorem first_substitution_law {p : PropForm Var} (h : PropForm.Tautology p)
    (sigma : Var -> PropForm Var') : PropForm.Tautology (PropForm.subst sigma p) :=
  PropForm.first_substitution_law h sigma

-- Book: Chapter 1, Section 1.2, Theorem 1.2, Second Substitution Law
theorem second_substitution_law (c : PropForm.Context Var) {p q : PropForm Var}
    (h : PropForm.LogicallyEquivalent p q) :
    PropForm.LogicallyEquivalent
      (PropForm.Context.plug c p)
      (PropForm.Context.plug c q) :=
  PropForm.Context.congr c h

-- Book: Chapter 1, Section 1.2
theorem equivalence_chain {p q r : PropForm Var}
    (hpq : PropForm.LogicallyEquivalent p q)
    (hqr : PropForm.LogicallyEquivalent q r) :
    PropForm.LogicallyEquivalent p r :=
  PropForm.logicallyEquivalent_trans hpq hqr

-- Book: Chapter 1, Section 1.2, negation of implication
theorem not_implication (p q : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.not (PropForm.imp p q))
      (PropForm.and p (PropForm.not q)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

end Section02
end Chapter01
end Book
end FoC

