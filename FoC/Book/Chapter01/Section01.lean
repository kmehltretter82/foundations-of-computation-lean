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

inductive ExerciseVar where
  | p
  | q
  | r
deriving Repr

namespace ExerciseVar

def valuation (pValue qValue rValue : Bool) : ExerciseVar -> Bool
  | p => pValue
  | q => qValue
  | r => rValue

def P : PropForm ExerciseVar :=
  PropForm.var p

def Q : PropForm ExerciseVar :=
  PropForm.var q

def R : PropForm ExerciseVar :=
  PropForm.var r

end ExerciseVar

def nor (p q : PropForm Var) : PropForm Var :=
  PropForm.not (PropForm.or p q)

namespace NorOnly

def neg (p : PropForm Var) : PropForm Var :=
  nor p p

def disj (p q : PropForm Var) : PropForm Var :=
  nor (nor p q) (nor p q)

def conj (p q : PropForm Var) : PropForm Var :=
  nor (neg p) (neg q)

def impl (p q : PropForm Var) : PropForm Var :=
  disj (neg p) q

def iff (p q : PropForm Var) : PropForm Var :=
  conj (impl p q) (impl q p)

def xor (p q : PropForm Var) : PropForm Var :=
  conj (disj p q) (neg (conj p q))

end NorOnly

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

-- Book: Chapter 1, Section 1.1, Exercise 4(d)
theorem exercise_4d_not_tautology :
    ¬ PropForm.Tautology
      (PropForm.imp
        (PropForm.or ExerciseVar.P ExerciseVar.Q)
        (PropForm.and ExerciseVar.P ExerciseVar.Q)) := by
  intro h
  have hv := h (ExerciseVar.valuation true false false)
  simp [ExerciseVar.P, ExerciseVar.Q, ExerciseVar.valuation, PropForm.eval] at hv

-- Book: Chapter 1, Section 1.1, Exercise 4(d)
theorem exercise_4d_not_contradiction :
    ¬ PropForm.Contradiction
      (PropForm.imp
        (PropForm.or ExerciseVar.P ExerciseVar.Q)
        (PropForm.and ExerciseVar.P ExerciseVar.Q)) := by
  intro h
  have hv := h (ExerciseVar.valuation true true false)
  simp [ExerciseVar.P, ExerciseVar.Q, ExerciseVar.valuation, PropForm.eval] at hv

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

-- Book: Chapter 1, Section 1.1, Exercise 6
theorem exercise_6_imp_not_associative :
    ¬ PropForm.LogicallyEquivalent
      (PropForm.imp (PropForm.imp ExerciseVar.P ExerciseVar.Q) ExerciseVar.R)
      (PropForm.imp ExerciseVar.P (PropForm.imp ExerciseVar.Q ExerciseVar.R)) := by
  intro h
  have hv := h (ExerciseVar.valuation false false false)
  simp [ExerciseVar.P, ExerciseVar.Q, ExerciseVar.R, ExerciseVar.valuation, PropForm.eval] at hv

-- Book: Chapter 1, Section 1.1, Exercise 6
theorem exercise_6_iff_associative (p q r : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.iff (PropForm.iff p q) r)
      (PropForm.iff p (PropForm.iff q r)) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    cases hr : PropForm.eval valuation r <;>
    simp [PropForm.eval, hp, hq, hr]

-- Book: Chapter 1, Section 1.1, Exercise 7
theorem exercise_7_sentences_equivalent (p q : PropForm Var) :
    PropForm.LogicallyEquivalent
      (PropForm.or p q)
      (PropForm.imp (PropForm.not p) q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [PropForm.eval, hp, hq]

-- Book: Chapter 1, Section 1.1, Exercise 11
theorem exercise_11_nor_truth_table (valuation : Var -> Bool) (p q : PropForm Var) :
    PropForm.eval valuation (nor p q) =
      !(PropForm.eval valuation p || PropForm.eval valuation q) :=
  rfl

-- Book: Chapter 1, Section 1.1, Exercise 11
theorem exercise_11_not_from_nor (p : PropForm Var) :
    PropForm.LogicallyEquivalent (NorOnly.neg p) (PropForm.not p) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    simp [NorOnly.neg, nor, PropForm.eval, hp]

-- Book: Chapter 1, Section 1.1, Exercise 11
theorem exercise_11_and_from_nor (p q : PropForm Var) :
    PropForm.LogicallyEquivalent (NorOnly.conj p q) (PropForm.and p q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [NorOnly.conj, NorOnly.neg, nor, PropForm.eval, hp, hq]

-- Book: Chapter 1, Section 1.1, Exercise 11
theorem exercise_11_or_from_nor (p q : PropForm Var) :
    PropForm.LogicallyEquivalent (NorOnly.disj p q) (PropForm.or p q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [NorOnly.disj, nor, PropForm.eval, hp, hq]

-- Book: Chapter 1, Section 1.1, Exercise 11
theorem exercise_11_imp_from_nor (p q : PropForm Var) :
    PropForm.LogicallyEquivalent (NorOnly.impl p q) (PropForm.imp p q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [NorOnly.impl, NorOnly.disj, NorOnly.neg, nor, PropForm.eval, hp, hq]

-- Book: Chapter 1, Section 1.1, Exercise 11
theorem exercise_11_iff_from_nor (p q : PropForm Var) :
    PropForm.LogicallyEquivalent (NorOnly.iff p q) (PropForm.iff p q) := by
  intro valuation
  cases hp : PropForm.eval valuation p <;>
    cases hq : PropForm.eval valuation q <;>
    simp [NorOnly.iff, NorOnly.conj, NorOnly.impl, NorOnly.disj, NorOnly.neg,
      nor, PropForm.eval, hp, hq]

-- Book: Chapter 1, Section 1.1, Exercise 11
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
