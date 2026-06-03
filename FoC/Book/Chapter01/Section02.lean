import FoC.Foundation.Logic

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter01
namespace Section02

/-!
# Chapter 1, Section 1.2: Boolean Algebra

This section formalizes the Boolean-algebra laws from Figure 1.2 and the two
substitution laws from the text. Logical equivalence is semantic: two formulas
are equivalent when they have the same truth value under every valuation.

Most laws are proved by truth-table splitting. Lean considers the possible
Boolean values of the formula variables and then simplifies.
-/

open Foundation

/-!
## Figure 1.2 Laws

The first group records double negation, excluded middle, contradiction,
identity laws, idempotence, commutativity, associativity, distributivity, and
De Morgan's laws.
-/

theorem double_negation (p : PropForm Var) :
    PropForm.LogicallyEquivalent (PropForm.not (PropForm.not p)) p := by
  intro valuation
  cases hp : PropForm.eval valuation p <;> simp [PropForm.eval, hp]

theorem excluded_middle (p : PropForm Var) :
    PropForm.LogicallyEquivalent (PropForm.or p (PropForm.not p)) PropForm.truth := by
  intro valuation
  cases hp : PropForm.eval valuation p <;> simp [PropForm.eval, hp]

theorem contradiction_law (p : PropForm Var) :
    PropForm.LogicallyEquivalent (PropForm.and p (PropForm.not p)) PropForm.falsity := by
  intro valuation
  cases hp : PropForm.eval valuation p <;> simp [PropForm.eval, hp]

theorem true_and_identity (p : PropForm Var) :
    PropForm.LogicallyEquivalent (PropForm.and PropForm.truth p) p := by
  intro valuation
  cases hp : PropForm.eval valuation p <;> simp [PropForm.eval, hp]

theorem false_or_identity (p : PropForm Var) :
    PropForm.LogicallyEquivalent (PropForm.or PropForm.falsity p) p := by
  intro valuation
  cases hp : PropForm.eval valuation p <;> simp [PropForm.eval, hp]

theorem and_idempotent (p : PropForm Var) :
    PropForm.LogicallyEquivalent (PropForm.and p p) p := by
  intro valuation
  cases hp : PropForm.eval valuation p <;> simp [PropForm.eval, hp]

theorem or_idempotent (p : PropForm Var) :
    PropForm.LogicallyEquivalent (PropForm.or p p) p := by
  intro valuation
  cases hp : PropForm.eval valuation p <;> simp [PropForm.eval, hp]

theorem and_commutative (p q : PropForm Var) :
    PropForm.LogicallyEquivalent (PropForm.and p q) (PropForm.and q p) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

theorem or_commutative (p q : PropForm Var) :
    PropForm.LogicallyEquivalent (PropForm.or p q) (PropForm.or q p) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

theorem and_associative (p q r : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.and (PropForm.and p q) r)
      (PropForm.and p (PropForm.and q r)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    cases hr : PropForm.eval valuation r <;>
    simp [PropForm.eval, hp, hq, hr]

theorem or_associative (p q r : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.or (PropForm.or p q) r)
      (PropForm.or p (PropForm.or q r)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    cases hr : PropForm.eval valuation r <;>
    simp [PropForm.eval, hp, hq, hr]

theorem and_distributive_over_or (p q r : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.and p (PropForm.or q r))
      (PropForm.or (PropForm.and p q) (PropForm.and p r)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    cases hr : PropForm.eval valuation r <;>
    simp [PropForm.eval, hp, hq, hr]

theorem or_distributive_over_and (p q r : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.or p (PropForm.and q r))
      (PropForm.and (PropForm.or p q) (PropForm.or p r)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    cases hr : PropForm.eval valuation r <;>
    simp [PropForm.eval, hp, hq, hr]

theorem demorgan_and (p q : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.not (PropForm.and p q))
      (PropForm.or (PropForm.not p) (PropForm.not q)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

theorem demorgan_or (p q : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.not (PropForm.or p q))
      (PropForm.and (PropForm.not p) (PropForm.not q)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

/-!
## Substitution and Rewrite Chains

The first substitution law says that replacing variables in a tautology by
arbitrary formulas preserves tautology. The second says that equivalent
formulas can be exchanged inside any one-hole context. The final statements
package common uses of equivalence chaining and negated implication.
-/

theorem first_substitution_law {p : PropForm Var} (h : PropForm.Tautology p)
    (sigma : Var -> PropForm Var') : PropForm.Tautology (PropForm.subst sigma p) :=
  PropForm.first_substitution_law h sigma

theorem second_substitution_law (c : PropForm.Context Var) {p q : PropForm Var}
    (h : PropForm.LogicallyEquivalent p q) :
    PropForm.LogicallyEquivalent
      (PropForm.Context.plug c p)
      (PropForm.Context.plug c q) :=
  PropForm.Context.congr c h

theorem equivalence_chain {p q r : PropForm Var}
    (hpq : PropForm.LogicallyEquivalent p q)
    (hqr : PropForm.LogicallyEquivalent q r) :
    PropForm.LogicallyEquivalent p r :=
  PropForm.logicallyEquivalent_trans hpq hqr

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
