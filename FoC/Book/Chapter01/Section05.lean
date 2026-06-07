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

The valid-rule declarations package a premise and conclusion into a single
formula implication. For example, modus ponens is formalized as: whenever
{lit}`p -> q` and {lit}`p` are true under a valuation, {lit}`q` is true under that valuation.
The invalid-rule declarations have the opposite shape: they exhibit a
valuation that makes the premises true while the proposed conclusion is false.
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

theorem conjunction_elim_right (p q : PropForm Var) :
    PropForm.LogicallyImplies (PropForm.and p q) q := by
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

theorem disjunction_intro_right (p q : PropForm Var) :
    PropForm.LogicallyImplies q (PropForm.or p q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

theorem logical_implication_trans {p q r : PropForm Var}
    (hpq : PropForm.LogicallyImplies p q)
    (hqr : PropForm.LogicallyImplies q r) :
    PropForm.LogicallyImplies p r := by
  intro valuation
  have hpqv := hpq valuation
  have hqrv := hqr valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    cases hr : PropForm.eval valuation r <;>
    simp [PropForm.eval, hp, hq, hr] at hpqv hqrv ⊢

theorem logical_equivalence_iff_mutual_implication (p q : PropForm Var) :
    PropForm.LogicallyEquivalent p q <->
      PropForm.LogicallyImplies p q ∧ PropForm.LogicallyImplies q p := by
  constructor
  · intro h
    constructor
    · intro valuation
      have hv := h valuation
      cases hp : PropForm.eval valuation p <;>
        cases hq : PropForm.eval valuation q <;>
        simp [PropForm.eval, hp, hq] at hv ⊢
    · intro valuation
      have hv := h valuation
      cases hp : PropForm.eval valuation p <;>
        cases hq : PropForm.eval valuation q <;>
        simp [PropForm.eval, hp, hq] at hv ⊢
  · intro h valuation
    have hpq := h.left valuation
    have hqp := h.right valuation
    cases hp : PropForm.eval valuation p <;>
      cases hq : PropForm.eval valuation q <;>
      simp [PropForm.eval, hp, hq] at hpq hqp ⊢

def fivePremiseArgumentPremises
    (p q r s t : PropForm Var) : PropForm Var :=
  PropForm.and (PropForm.imp (PropForm.and p r) s)
    (PropForm.and (PropForm.imp q p)
      (PropForm.and (PropForm.imp t r)
        (PropForm.and q t)))

theorem five_premise_argument_valid (p q r s t : PropForm Var) :
    PropForm.LogicallyImplies (fivePremiseArgumentPremises p q r s t) s := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    cases hr : PropForm.eval valuation r <;>
    cases hs : PropForm.eval valuation s <;>
    cases ht : PropForm.eval valuation t <;>
    simp [fivePremiseArgumentPremises, PropForm.eval, hp, hq, hr, hs, ht]

def partyArgumentPremises
    (j m b t f s : PropForm Var) : PropForm Var :=
  PropForm.and (PropForm.imp (PropForm.and m (PropForm.not b)) j)
    (PropForm.and (PropForm.imp (PropForm.or f s) m)
      (PropForm.and (PropForm.imp b t)
        (PropForm.and (PropForm.imp f (PropForm.not t)) f)))

theorem party_argument_valid (j m b t f s : PropForm Var) :
    PropForm.LogicallyImplies (partyArgumentPremises j m b t f s) j := by
  intro valuation
  cases hj : PropForm.eval valuation j <;>
    cases hm : PropForm.eval valuation m <;>
    cases hb : PropForm.eval valuation b <;>
    cases ht : PropForm.eval valuation t <;>
    cases hf : PropForm.eval valuation f <;>
    cases hs : PropForm.eval valuation s <;>
    simp [partyArgumentPremises, PropForm.eval, hj, hm, hb, ht, hf, hs]

theorem universal_instantiation (P : alpha -> Prop) (a : alpha)
    (h : forall x, P x) : P a :=
  h a

theorem predicate_modus_ponens (P Q : alpha -> Prop) (a : alpha)
    (hforall : forall x, P x -> Q x) (ha : P a) : Q a :=
  hforall a ha

theorem predicate_modus_tollens (P Q : alpha -> Prop) (a : alpha)
    (hforall : forall x, P x -> Q x) (hnqa : ¬ Q a) : ¬ P a := by
  intro hpa
  exact hnqa (hforall a hpa)

inductive FormalProofStep (Statement : Type u) where
  | premise : Statement -> FormalProofStep Statement
  | derived : Statement -> List Statement -> FormalProofStep Statement

/-!
{lit}`FormalProofStep` is lightweight vocabulary for the book's discussion of proof
lines: a step is either a premise or something derived from earlier statements.
The semantic soundness of particular rules is handled by the implication
theorems above.
-/

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

inductive DeductionCounterVar where
  | p
  | q
  | r

namespace DeductionCounterVar

def valuation : DeductionCounterVar -> Bool
  | p => false
  | q => false
  | r => true

def P : PropForm DeductionCounterVar :=
  PropForm.var p

def Q : PropForm DeductionCounterVar :=
  PropForm.var q

def R : PropForm DeductionCounterVar :=
  PropForm.var r

end DeductionCounterVar

open DeductionCounterVar

theorem invalid_three_premise_argument_from_text :
    exists valuation : DeductionCounterVar -> Bool,
      PropForm.eval valuation
          (PropForm.and (PropForm.imp P Q)
            (PropForm.and (PropForm.imp Q (PropForm.and P R)) R)) = true ∧
        PropForm.eval valuation P = false := by
  exact Exists.intro valuation (And.intro rfl rfl)

end Section05
end Chapter01
end Book
end FoC
