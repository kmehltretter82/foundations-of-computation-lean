import FoC.Foundation.Logic

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter01
namespace Section05

/-!
# Chapter 1, Section 1.5: Deduction

This section interprets deduction rules semantically. A rule is represented as
logical implication: every valuation that makes the premises true also makes
the conclusion true.

The valid rules are checked by truth-table splitting. The invalid rules are
represented by explicit countervaluations.
-/

open Foundation

/-! Book-facing synonym for semantic logical implication. -/
def LogicallyImplies (p q : PropForm Var) : Prop :=
  PropForm.LogicallyImplies p q

/-! Modus ponens: from p implies q and p, infer q. -/
theorem modus_ponens (p q : PropForm Var) :
    PropForm.LogicallyImplies
      (PropForm.and (PropForm.imp p q) p)
      q := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

theorem modus_tollens (p q : PropForm Var) :
    PropForm.LogicallyImplies
      (PropForm.and (PropForm.imp p q) (PropForm.not q))
      (PropForm.not p) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

theorem law_of_syllogism (p q r : PropForm Var) :
    PropForm.LogicallyImplies
      (PropForm.and (PropForm.imp p q) (PropForm.imp q r))
      (PropForm.imp p r) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    cases hr : PropForm.eval valuation r <;>
    simp [PropForm.eval, hp, hq, hr]

theorem disjunctive_syllogism (p q : PropForm Var) :
    PropForm.LogicallyImplies
      (PropForm.and (PropForm.or p q) (PropForm.not p))
      q := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

theorem conjunction_intro (p q : PropForm Var) :
    PropForm.LogicallyImplies
      (PropForm.and p q)
      (PropForm.and p q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

theorem conjunction_elim_left (p q : PropForm Var) :
    PropForm.LogicallyImplies (PropForm.and p q) p := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

theorem disjunction_intro_left (p q : PropForm Var) :
    PropForm.LogicallyImplies p (PropForm.or p q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

inductive FormalProofStep (Statement : Type u) where
  | premise : Statement -> FormalProofStep Statement
  | derived : Statement -> List Statement -> FormalProofStep Statement

/-!
Affirming the consequent is invalid. The valuation in the proof makes "p
implies q" and q true while p is false.
-/
theorem invalid_affirming_consequent :
    exists valuation : Bool -> Bool,
      PropForm.eval valuation (PropForm.imp (PropForm.var false) (PropForm.var true)) = true ∧
      PropForm.eval valuation (PropForm.var true) = true ∧
      PropForm.eval valuation (PropForm.var false) = false := by
  exact Exists.intro (fun b => b) (And.intro rfl (And.intro rfl rfl))

/-!
Denying the antecedent is invalid. The valuation in the proof makes "p implies
q" and "not p" true while "not q" is false.
-/
theorem invalid_denying_antecedent :
    exists valuation : Bool -> Bool,
      PropForm.eval valuation (PropForm.imp (PropForm.var false) (PropForm.var true)) = true ∧
      PropForm.eval valuation (PropForm.not (PropForm.var false)) = true ∧
      PropForm.eval valuation (PropForm.not (PropForm.var true)) = false := by
  exact Exists.intro (fun b => b) (And.intro rfl (And.intro rfl rfl))

end Section05
end Chapter01
end Book
end FoC
