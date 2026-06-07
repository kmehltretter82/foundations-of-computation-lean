import FoC.Foundation.Logic

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter01
namespace Section01

/-!
# Chapter 1, Section 1.1: Propositional Logic

This section formalizes the book's first truth-table treatment of
propositional logic. The reusable syntax and semantics live in the
Foundation.Logic module; this file records the book-facing statements in the
order in which the section introduces them.

The formalization models each proposition letter as a value of an arbitrary
variable type, formulas as syntax trees, and a truth assignment as a Boolean
function on variables. Semantic notions such as tautology,
contradiction, logical equivalence, and implication are predicates over all
truth assignments.

The later statements in the file also formalize selected exercises: standard
tautologies, countervaluations for formulas that are not tautologies or not
contradictions, associativity behavior for implication and biconditional, and
the construction of the usual connectives from the NOR operator.

Read the declarations in this page as a formal truth-table. A theorem whose
conclusion is {lit}`PropForm.Tautology p` says that every valuation makes {lit}`p` true.
A theorem whose conclusion is an existential statement gives a concrete
valuation witnessing failure of a proposed universal property. Near the end,
the NOR definitions show a different kind of result: one connective is
expressive enough to rebuild the usual propositional connectives.
-/

open Foundation

/--
Three concrete proposition letters used for exercise countervaluations.

Most theorems in this file are polymorphic in the variable type. A few
exercises need an explicit valuation that makes a displayed formula true or
false, so this small type provides named variables p, q, and r.
-/
inductive ExerciseVar where
  | p
  | q
  | r
deriving Repr

namespace ExerciseVar

/--
Build a truth assignment for the exercise variables from three Boolean values.
-/
def valuation (pValue qValue rValue : Bool) : ExerciseVar -> Bool
  | p => pValue
  | q => qValue
  | r => rValue

/-- The formula variable p used in concrete exercise statements. -/
def P : PropForm ExerciseVar :=
  PropForm.var p

/-- The formula variable q used in concrete exercise statements. -/
def Q : PropForm ExerciseVar :=
  PropForm.var q

/-- The formula variable r used in concrete exercise statements. -/
def R : PropForm ExerciseVar :=
  PropForm.var r

end ExerciseVar

/--
The NOR connective, true exactly when both inputs are false.

Exercise 11 uses NOR to show that a single connective can express negation,
conjunction, disjunction, implication, biconditional, and exclusive-or.
-/
def nor (p q : PropForm Var) : PropForm Var :=
  PropForm.not (PropForm.or p q)

namespace NorOnly

/-- Negation expressed using only NOR. -/
def neg (p : PropForm Var) : PropForm Var :=
  nor p p

/-- Disjunction expressed using only NOR. -/
def disj (p q : PropForm Var) : PropForm Var :=
  nor (nor p q) (nor p q)

/-- Conjunction expressed using only NOR. -/
def conj (p q : PropForm Var) : PropForm Var :=
  nor (neg p) (neg q)

/-- Implication expressed using only NOR. -/
def impl (p q : PropForm Var) : PropForm Var :=
  disj (neg p) q

/-- Biconditional expressed using only NOR. -/
def iff (p q : PropForm Var) : PropForm Var :=
  conj (impl p q) (impl q p)

/-- Exclusive-or expressed using only NOR. -/
def xor (p q : PropForm Var) : PropForm Var :=
  conj (disj p q) (neg (conj p q))

end NorOnly

/-!
## Truth Tables as Computation

The first group of checked statements says that Lean's evaluator implements the
truth tables from Definitions 1.1 and 1.2. In the formalization, this is not a
separate table object: evaluating conjunction, disjunction, negation, implication,
biconditional, or exclusive-or formula computes the corresponding Boolean
operation.

These facts are intentionally proved by reflexivity. That means the formal evaluator
was defined so that the book's truth-table clauses are true by unfolding the
definition.
-/

/--
Lean's evaluator for conjunction matches the truth table in Definition 1.1.
-/
theorem definition_1_1_and_eval (valuation : Var -> Bool) (p q : PropForm Var) :
    PropForm.eval valuation (PropForm.and p q) =
      (PropForm.eval valuation p && PropForm.eval valuation q) :=
  rfl

/--
Lean's evaluator for disjunction matches the truth table in Definition 1.1.
-/
theorem definition_1_1_or_eval (valuation : Var -> Bool) (p q : PropForm Var) :
    PropForm.eval valuation (PropForm.or p q) =
      (PropForm.eval valuation p || PropForm.eval valuation q) :=
  rfl

/--
Lean's evaluator for negation matches the truth table in Definition 1.1.
-/
theorem definition_1_1_not_eval (valuation : Var -> Bool) (p : PropForm Var) :
    PropForm.eval valuation (PropForm.not p) = !(PropForm.eval valuation p) :=
  rfl

/--
Material implication is represented by the Boolean formula "not p or q".
-/
theorem definition_1_2_imp_eval (valuation : Var -> Bool) (p q : PropForm Var) :
    PropForm.eval valuation (PropForm.imp p q) =
      (!(PropForm.eval valuation p) || PropForm.eval valuation q) :=
  rfl

/--
Biconditional evaluation is Boolean equality of the two evaluated formulas.
-/
theorem definition_1_2_iff_eval (valuation : Var -> Bool) (p q : PropForm Var) :
    PropForm.eval valuation (PropForm.iff p q) =
      (PropForm.eval valuation p == PropForm.eval valuation q) :=
  rfl

/--
Exclusive-or is true exactly when one side is true and the other is false.
-/
theorem definition_1_2_xor_eval (valuation : Var -> Bool) (p q : PropForm Var) :
    PropForm.eval valuation (PropForm.xor p q) =
      ((PropForm.eval valuation p && !(PropForm.eval valuation q)) ||
        (!(PropForm.eval valuation p) && PropForm.eval valuation q)) :=
  rfl

/-!
## Semantic Vocabulary

The book introduces tautologies, contradictions, and logical equivalence as
truth-table notions. Lean represents these as predicates over all valuations.
For example, a formula is a tautology when every valuation evaluates it to true.

The key bridge in this part is that two formulas are logically equivalent just
when their biconditional is a tautology. That turns a relation between formulas
into a single formula-level statement.
-/

/--
A negated formula is a tautology exactly when the original formula is a
contradiction.
-/
theorem definition_1_3_not_tautology_iff_contradiction (p : PropForm Var) :
    PropForm.Tautology (PropForm.not p) <-> PropForm.Contradiction p :=
  PropForm.tautology_not_iff_contradiction p

/--
Logical equivalence can be checked by proving the biconditional formula is a
tautology.
-/
theorem definition_1_4_logical_equivalence_via_iff (p q : PropForm Var) :
    PropForm.LogicallyEquivalent p q <-> PropForm.Tautology (PropForm.iff p q) :=
  PropForm.logicallyEquivalent_iff_iff_tautology p q

/-!
## Basic Equivalences

The next cluster checks the standard equivalences used throughout the section:
associativity of conjunction, implication as "not p or q", contraposition, the
biconditional as two implications, and exclusive-or as "one side but not both".

The proofs are finite truth-table arguments. In Lean they appear as case splits
over the Boolean values of the relevant formulas, followed by simplification.
-/

/--
The associativity of conjunction from Figure 1.1.
-/
theorem figure_1_1_and_associative (p q r : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.and (PropForm.and p q) r)
      (PropForm.and p (PropForm.and q r)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    cases hr : PropForm.eval valuation r <;>
    simp [PropForm.eval, hp, hq, hr]

/--
The usual equivalence between implication and disjunction with a negated
antecedent.
-/
theorem implication_equiv_not_or (p q : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.imp p q)
      (PropForm.or (PropForm.not p) q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

/--
An implication is equivalent to its contrapositive.
-/
theorem implication_equiv_contrapositive (p q : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.imp p q)
      (PropForm.imp (PropForm.not q) (PropForm.not p)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

/--
The biconditional is equivalent to the conjunction of the two directions of
implication.
-/
theorem biconditional_equiv_two_implications (p q : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.iff p q)
      (PropForm.and (PropForm.imp p q) (PropForm.imp q p)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

/--
Exclusive-or is equivalent to "at least one side, but not both sides".
-/
theorem xor_equiv_or_and_not_and (p q : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.xor p q)
      (PropForm.and (PropForm.or p q) (PropForm.not (PropForm.and p q))) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

/-!
## Selected Exercise Statements

The exercise statements include familiar tautologies, counterexamples, and
equivalence checks. Each one is represented as a semantic statement about all
valuations, or as a concrete valuation showing that a proposed universal claim
fails.

The explanations below are attached directly to the theorem they explain.
These are all truth-table arguments: Lean considers the finite set of possible
Boolean values for the variables and simplifies the resulting Boolean
expression.
-/

/-!
## More Exercise Equivalences

Exercise 5 asks for logical equivalences involving biconditional and
exclusive-or. Exercises 6 and 7 compare parenthesizations and sentence forms.
The explanation for each formal statement appears immediately above it.
-/

/--
The disjunctive syllogism example from the text is a tautology.
-/
theorem example_tautology_disjunctive_syllogism (p q : PropForm Var) :
    PropForm.Tautology
      (PropForm.imp (PropForm.and (PropForm.or p q) (PropForm.not q)) p) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

/--
Exercise 4(a), modus ponens: if p is true and "p implies q" is true, then q is
true. The Lean theorem states that this whole implication is a tautology.
-/
theorem exercise_4a_modus_ponens (p q : PropForm Var) :
    PropForm.Tautology
      (PropForm.imp (PropForm.and p (PropForm.imp p q)) q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

/--
Exercise 4(b), hypothetical syllogism: if "p implies q" and "q implies r" are
both true, then "p implies r" is true.
-/
theorem exercise_4b_hypothetical_syllogism (p q r : PropForm Var) :
    PropForm.Tautology
      (PropForm.imp (PropForm.and (PropForm.imp p q) (PropForm.imp q r)) (PropForm.imp p r)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    cases hr : PropForm.eval valuation r <;>
    simp [PropForm.eval, hp, hq, hr]

/--
Exercise 4(c): "p and not p" is a contradiction, since no valuation can make
both parts true.
-/
theorem exercise_4c_contradiction (p : PropForm Var) :
    PropForm.Contradiction (PropForm.and p (PropForm.not p)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    simp [PropForm.eval, hp]

/--
Exercise 4(d), first half: the displayed implication is not a tautology. The
valuation p = true and q = false makes the antecedent true and the consequent
false.
-/
theorem exercise_4d_not_tautology :
    ¬ PropForm.Tautology
      (PropForm.imp
        (PropForm.or ExerciseVar.P ExerciseVar.Q)
        (PropForm.and ExerciseVar.P ExerciseVar.Q)) := by
  intro h
  have hv := h (ExerciseVar.valuation true false false)
  simp [ExerciseVar.P, ExerciseVar.Q, ExerciseVar.valuation, PropForm.eval] at hv

/--
Exercise 4(d), second half: the same formula is not a contradiction. The
valuation p = true and q = true makes the formula true.
-/
theorem exercise_4d_not_contradiction :
    ¬ PropForm.Contradiction
      (PropForm.imp
        (PropForm.or ExerciseVar.P ExerciseVar.Q)
        (PropForm.and ExerciseVar.P ExerciseVar.Q)) := by
  intro h
  have hv := h (ExerciseVar.valuation true true false)
  simp [ExerciseVar.P, ExerciseVar.Q, ExerciseVar.valuation, PropForm.eval] at hv

/--
Exercise 4(e), excluded middle: "p or not p" is a tautology.
-/
theorem exercise_4e_excluded_middle (p : PropForm Var) :
    PropForm.Tautology (PropForm.or p (PropForm.not p)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    simp [PropForm.eval, hp]

/--
Exercise 4(f): "p and q" implies "p or q" is a tautology.
-/
theorem exercise_4f_and_implies_or (p q : PropForm Var) :
    PropForm.Tautology (PropForm.imp (PropForm.and p q) (PropForm.or p q)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

/--
Exercise 5(a): a biconditional is equivalent to the conjunction of the two
implications, one in each direction.
-/
theorem exercise_5a_iff_as_two_implications (p q : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.and (PropForm.imp p q) (PropForm.imp q p))
      (PropForm.iff p q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

/--
Exercise 5(b): negating both sides of a biconditional does not change its truth
value.
-/
theorem exercise_5b_iff_of_negations (p q : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.iff (PropForm.not p) (PropForm.not q))
      (PropForm.iff p q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

/--
Exercise 5(c): combining "p implies q" with "not p implies not q" is another
way to express that p and q have the same truth value.
-/
theorem exercise_5c_iff_from_forward_and_reverse_negative (p q : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.and (PropForm.imp p q) (PropForm.imp (PropForm.not p) (PropForm.not q)))
      (PropForm.iff p q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

/--
Exercise 5(d): the negation of exclusive-or is equivalent to biconditional:
saying "not exactly one of p and q" is the same as saying "p iff q".
-/
theorem exercise_5d_iff_as_not_xor (p q : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.not (PropForm.xor p q))
      (PropForm.iff p q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

/--
Exercise 6, first half: implication is not associative. The two
parenthesizations have different truth values when p, q, and r are all false.
-/
theorem exercise_6_imp_not_associative :
    ¬ PropForm.LogicallyEquivalent
      (PropForm.imp (PropForm.imp ExerciseVar.P ExerciseVar.Q) ExerciseVar.R)
      (PropForm.imp ExerciseVar.P (PropForm.imp ExerciseVar.Q ExerciseVar.R)) := by
  intro h
  have hv := h (ExerciseVar.valuation false false false)
  simp [ExerciseVar.P, ExerciseVar.Q, ExerciseVar.R, ExerciseVar.valuation, PropForm.eval] at hv

/--
Exercise 6, second half: biconditional is associative. Lean checks this by a
complete truth-table split over p, q, and r.
-/
theorem exercise_6_iff_associative (p q r : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.iff (PropForm.iff p q) r)
      (PropForm.iff p (PropForm.iff q r)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    cases hr : PropForm.eval valuation r <;>
    simp [PropForm.eval, hp, hq, hr]

/--
Exercise 7 formalizes one of the English-sentence equivalences from the
section: "p or q" has the same truth conditions as "if not p, then q".
-/
theorem exercise_7_sentences_equivalent (p q : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.or p q)
      (PropForm.imp (PropForm.not p) q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

/-!
## NOR Completeness

The final group formalizes the section's NOR exercise. First, the NOR formula
is defined as the negation of a disjunction. Then a small namespace gives
definitions of the usual connectives using only NOR.

The checked theorems say that each NOR-only definition is logically equivalent
to the corresponding ordinary connective. This is the formal version of saying
that NOR is functionally complete for these propositional connectives.
-/

theorem exercise_11_nor_truth_table (valuation : Var -> Bool) (p q : PropForm Var) :
    PropForm.eval valuation (nor p q) =
      !(PropForm.eval valuation p || PropForm.eval valuation q) :=
  rfl

theorem exercise_11_not_from_nor (p : PropForm Var) :
    PropForm.LogicallyEquivalent (NorOnly.neg p) (PropForm.not p) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    simp [NorOnly.neg, nor, PropForm.eval, hp]

theorem exercise_11_and_from_nor (p q : PropForm Var) :
    PropForm.LogicallyEquivalent (NorOnly.conj p q) (PropForm.and p q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [NorOnly.conj, NorOnly.neg, nor, PropForm.eval, hp, hq]

theorem exercise_11_or_from_nor (p q : PropForm Var) :
    PropForm.LogicallyEquivalent (NorOnly.disj p q) (PropForm.or p q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [NorOnly.disj, nor, PropForm.eval, hp, hq]

theorem exercise_11_imp_from_nor (p q : PropForm Var) :
    PropForm.LogicallyEquivalent (NorOnly.impl p q) (PropForm.imp p q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [NorOnly.impl, NorOnly.disj, NorOnly.neg, nor, PropForm.eval, hp, hq]

theorem exercise_11_iff_from_nor (p q : PropForm Var) :
    PropForm.LogicallyEquivalent (NorOnly.iff p q) (PropForm.iff p q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [NorOnly.iff, NorOnly.conj, NorOnly.impl, NorOnly.disj, NorOnly.neg,
      nor, PropForm.eval, hp, hq]

theorem exercise_11_xor_from_nor (p q : PropForm Var) :
    PropForm.LogicallyEquivalent (NorOnly.xor p q) (PropForm.xor p q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [NorOnly.xor, NorOnly.conj, NorOnly.disj, NorOnly.neg,
      nor, PropForm.eval, hp, hq]

end Section01
end Chapter01
end Book
end FoC
