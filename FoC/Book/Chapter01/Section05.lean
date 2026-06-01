import FoC.Foundation.Logic

namespace FoC
namespace Book
namespace Chapter01
namespace Section05

/-!
Book: Chapter 1, Section 1.5, Deduction.
-/

open Foundation

-- Book: Chapter 1, Section 1.5, Definition 1.9
def LogicallyImplies (p q : PropForm Var) : Prop :=
  PropForm.LogicallyImplies p q

-- Book: Chapter 1, Section 1.5, modus ponens
theorem modus_ponens (p q : PropForm Var) :
    PropForm.LogicallyImplies
      (PropForm.and (PropForm.imp p q) p)
      q := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

-- Book: Chapter 1, Section 1.5, modus tollens
theorem modus_tollens (p q : PropForm Var) :
    PropForm.LogicallyImplies
      (PropForm.and (PropForm.imp p q) (PropForm.not q))
      (PropForm.not p) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

-- Book: Chapter 1, Section 1.5, Law of Syllogism
theorem law_of_syllogism (p q r : PropForm Var) :
    PropForm.LogicallyImplies
      (PropForm.and (PropForm.imp p q) (PropForm.imp q r))
      (PropForm.imp p r) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    cases hr : PropForm.eval valuation r <;>
    simp [PropForm.eval, hp, hq, hr]

-- Book: Chapter 1, Section 1.5, disjunctive syllogism
theorem disjunctive_syllogism (p q : PropForm Var) :
    PropForm.LogicallyImplies
      (PropForm.and (PropForm.or p q) (PropForm.not p))
      q := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

-- Book: Chapter 1, Section 1.5, conjunction introduction
theorem conjunction_intro (p q : PropForm Var) :
    PropForm.LogicallyImplies
      (PropForm.and p q)
      (PropForm.and p q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

-- Book: Chapter 1, Section 1.5, conjunction elimination
theorem conjunction_elim_left (p q : PropForm Var) :
    PropForm.LogicallyImplies (PropForm.and p q) p := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

-- Book: Chapter 1, Section 1.5, disjunction introduction
theorem disjunction_intro_left (p q : PropForm Var) :
    PropForm.LogicallyImplies p (PropForm.or p q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

-- Book: Chapter 1, Section 1.5, Definition 1.10
inductive FormalProofStep (Statement : Type u) where
  | premise : Statement -> FormalProofStep Statement
  | derived : Statement -> List Statement -> FormalProofStep Statement

-- Book: Chapter 1, Section 1.5, invalid converse form
theorem invalid_affirming_consequent :
    exists valuation : Bool -> Bool,
      PropForm.eval valuation (PropForm.imp (PropForm.var false) (PropForm.var true)) = true ∧
      PropForm.eval valuation (PropForm.var true) = true ∧
      PropForm.eval valuation (PropForm.var false) = false := by
  exact Exists.intro (fun b => b) (And.intro rfl (And.intro rfl rfl))

-- Book: Chapter 1, Section 1.5, invalid inverse form
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

