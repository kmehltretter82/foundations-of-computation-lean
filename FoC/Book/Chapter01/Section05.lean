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
represented by explicit countervaluations, and each countervaluation feeds a
theorem saying that the proposed rule is not a logical implication. The
section's formal-proof discussion is represented by a checked proof-line
format together with a soundness theorem.

Most valid-rule declarations package the premises and conclusion into a single
formula implication. For example, modus ponens is formalized as: whenever
{lit}`p -> q` and {lit}`p` are true under a valuation, {lit}`q` is true under that valuation.
Conjunction introduction is instead stated with two separate premise
hypotheses at the valuation level. The invalid-rule declarations have the
opposite shape: they exhibit a valuation that makes the premises true while
the proposed conclusion is false.
-/

open Foundation

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

/-!
Conjunction introduction takes its two premises separately: a valuation that
makes {lit}`p` true and makes {lit}`q` true also makes the conjunction of
{lit}`p` and {lit}`q` true. Packaging the two premises into a single
conjunction formula would make the rule a triviality, so this rule is stated
at the valuation level.
-/
theorem conjunction_intro (p q : PropForm Var) (valuation : Var -> Bool)
    (hp : PropForm.eval valuation p = true)
    (hq : PropForm.eval valuation q = true) :
    PropForm.eval valuation (PropForm.and p q) = true := by
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

/-!
**Semantically valid proof sequences.**

The book defines a formal proof as a sequence of propositions in which every
line is either a premise of the argument or follows by logical deduction from
lines that precede it, and the last line is the conclusion.
The declaration below records one proof line: a step is either a premise or a
statement derived from a list of cited earlier statements.
-/

inductive FormalProofStep (Statement : Type u) where
  | premise : Statement -> FormalProofStep Statement
  | derived : Statement -> List Statement -> FormalProofStep Statement

def FormalProofStep.statement : FormalProofStep Statement -> Statement
  | premise s => s
  | derived s _ => s

def proofPremises : List (FormalProofStep Statement) -> List Statement
  | [] => []
  | FormalProofStep.premise s :: rest => s :: proofPremises rest
  | FormalProofStep.derived _ _ :: rest => proofPremises rest

/-!
This predicate walks the proof list while accumulating the statements
established so far. Each derived line may cite only earlier statements, and
the caller supplies semantic validity for the derivation. It is deliberately
named as a semantic certificate rather than an executable rule checker.
-/
def SemanticallyValidProofFrom (earlier : List (PropForm Var)) :
    List (FormalProofStep (PropForm Var)) -> Prop
  | [] => True
  | FormalProofStep.premise s :: rest => SemanticallyValidProofFrom (s :: earlier) rest
  | FormalProofStep.derived s cited :: rest =>
      (forall c, c ∈ cited -> c ∈ earlier) ∧
        (forall valuation : Var -> Bool,
          (forall c, c ∈ cited -> PropForm.eval valuation c = true) ->
          PropForm.eval valuation s = true) ∧
        SemanticallyValidProofFrom (s :: earlier) rest

def SemanticallyValidProof (steps : List (FormalProofStep (PropForm Var))) : Prop :=
  SemanticallyValidProofFrom [] steps

/-!
Soundness in accumulator form: if a proof list is semantically valid relative
to already-established statements, then any valuation that makes those
statements and all premise lines true makes every line true.
-/
theorem semanticallyValidProofFrom_all_true {valuation : Var -> Bool} :
    forall {steps : List (FormalProofStep (PropForm Var))}
      {earlier : List (PropForm Var)},
      SemanticallyValidProofFrom earlier steps ->
      (forall p, p ∈ earlier -> PropForm.eval valuation p = true) ->
      (forall p, p ∈ proofPremises steps -> PropForm.eval valuation p = true) ->
      forall step, step ∈ steps ->
        PropForm.eval valuation step.statement = true := by
  intro steps
  induction steps with
  | nil =>
      intro earlier _ _ _ step hstep
      cases hstep
  | cons step rest ih =>
      intro earlier hchecked hearlier hpremises current hcurrent
      cases step with
      | premise s =>
          have hs : PropForm.eval valuation s = true := by
            apply hpremises
            simp [proofPremises]
          have hearlier' : forall p, p ∈ s :: earlier ->
              PropForm.eval valuation p = true := by
            intro p hp
            cases hp with
            | head => exact hs
            | tail _ hmem => exact hearlier p hmem
          have hpremises' : forall p, p ∈ proofPremises rest ->
              PropForm.eval valuation p = true := by
            intro p hp
            apply hpremises
            simp [proofPremises, hp]
          cases hcurrent with
          | head => exact hs
          | tail _ hmem =>
              exact ih hchecked hearlier' hpremises' current hmem
      | derived s cited =>
          have hs : PropForm.eval valuation s = true := by
            apply hchecked.right.left
            intro c hc
            exact hearlier c (hchecked.left c hc)
          have hearlier' : forall p, p ∈ s :: earlier ->
              PropForm.eval valuation p = true := by
            intro p hp
            cases hp with
            | head => exact hs
            | tail _ hmem => exact hearlier p hmem
          cases hcurrent with
          | head => exact hs
          | tail _ hmem =>
              exact ih hchecked.right.right hearlier'
                (by simpa [proofPremises] using hpremises) current hmem

/-!
The existence of a semantically valid proof sequence shows that the argument is valid:
every valuation that makes the premise lines true makes every line true, and
in particular the last line, which is the conclusion of the argument.
-/
theorem semantically_valid_proof_lines_true
    {steps : List (FormalProofStep (PropForm Var))}
    (hvalid : SemanticallyValidProof steps) (valuation : Var -> Bool)
    (hpremises : forall p, p ∈ proofPremises steps ->
      PropForm.eval valuation p = true) :
    forall step, step ∈ steps ->
      PropForm.eval valuation step.statement = true := by
  have hempty : forall p, p ∈ ([] : List (PropForm Var)) ->
      PropForm.eval valuation p = true := by
    intro p hp
    cases hp
  exact semanticallyValidProofFrom_all_true hvalid hempty hpremises

/-!
The section's first displayed formal proof derives {lit}`s` from the five
premises of the five-premise argument in nine numbered lines. The list below
is that proof, line by line, and the theorem certifies its semantic validity:
two modus ponens
steps, a conjunction introduction, and a final modus ponens.
-/
def fivePremiseFormalProof (p q r s t : PropForm Var) :
    List (FormalProofStep (PropForm Var)) :=
  [FormalProofStep.premise (PropForm.imp q p),
    FormalProofStep.premise q,
    FormalProofStep.derived p [PropForm.imp q p, q],
    FormalProofStep.premise (PropForm.imp t r),
    FormalProofStep.premise t,
    FormalProofStep.derived r [PropForm.imp t r, t],
    FormalProofStep.derived (PropForm.and p r) [p, r],
    FormalProofStep.premise (PropForm.imp (PropForm.and p r) s),
    FormalProofStep.derived s
      [PropForm.and p r, PropForm.imp (PropForm.and p r) s]]

theorem fivePremiseFormalProof_semantically_valid (p q r s t : PropForm Var) :
    SemanticallyValidProof (fivePremiseFormalProof p q r s t) := by
  simp [SemanticallyValidProof, fivePremiseFormalProof, SemanticallyValidProofFrom]
  apply And.intro
  · intro valuation h1 h2
    simp [PropForm.eval, h2] at h1
    exact h1
  apply And.intro
  · intro valuation h1 h2
    simp [PropForm.eval, h2] at h1
    exact h1
  apply And.intro
  · intro valuation hp hr
    simp [PropForm.eval, hp, hr]
  · intro valuation h1 h2
    simp [PropForm.eval] at h1
    simp [PropForm.eval, h1.left, h1.right] at h2
    exact h2

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
The countervaluation gives the punchline: the premises of affirming the
consequent do not logically imply its conclusion.
-/
theorem affirming_consequent_not_logically_implies :
    ¬ PropForm.LogicallyImplies
        (PropForm.and (PropForm.imp (PropForm.var false) (PropForm.var true))
          (PropForm.var true))
        (PropForm.var false) := by
  intro h
  have hv := h (fun b => b)
  simp [PropForm.eval] at hv

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

/-!
The same countervaluation shows that the premises of denying the antecedent do
not logically imply its conclusion.
-/
theorem denying_antecedent_not_logically_implies :
    ¬ PropForm.LogicallyImplies
        (PropForm.and (PropForm.imp (PropForm.var false) (PropForm.var true))
          (PropForm.not (PropForm.var false)))
        (PropForm.not (PropForm.var true)) := by
  intro h
  have hv := h (fun b => b)
  simp [PropForm.eval] at hv

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

/-!
The punchline for the text's three-premise argument: its premises do not
logically imply the proposed conclusion {lit}`p`.
-/
theorem three_premise_argument_from_text_not_logically_implies :
    ¬ PropForm.LogicallyImplies
        (PropForm.and (PropForm.imp P Q)
          (PropForm.and (PropForm.imp Q (PropForm.and P R)) R))
        P := by
  intro h
  have hv := h DeductionCounterVar.valuation
  simp [PropForm.eval, P, Q, R, DeductionCounterVar.valuation] at hv

end Section05
end Chapter01
end Book
end FoC
