set_option doc.verso true

/-!
# Propositional logic

## Formulas and valuations

Chapter 1 begins with truth tables for propositional logic.  This module gives
that material a reusable Lean representation: formulas are syntax trees,
valuations assign Boolean values to variables, and semantic notions are
quantified over all valuations.

The same syntax also supports substitution and formula contexts, which are used
by later chapter-facing statements to express standard equivalence and
replacement principles.
-/

namespace FoC
namespace Foundation

/-!
# Formula syntax

Propositional formulas are syntax trees with variables, truth constants, the
usual Boolean connectives, implication, biconditional, and exclusive-or.
-/

inductive PropForm (Var : Type u) where
  | var : Var -> PropForm Var
  | truth : PropForm Var
  | falsity : PropForm Var
  | not : PropForm Var -> PropForm Var
  | and : PropForm Var -> PropForm Var -> PropForm Var
  | or : PropForm Var -> PropForm Var -> PropForm Var
  | imp : PropForm Var -> PropForm Var -> PropForm Var
  | iff : PropForm Var -> PropForm Var -> PropForm Var
  | xor : PropForm Var -> PropForm Var -> PropForm Var
deriving Repr

namespace PropForm

/-!
# Truth-table semantics

Evaluation takes a Boolean valuation for variables and recursively computes the
truth value of a formula.  Tautology, contradiction, equivalence, and implication
are semantic predicates over all valuations.
-/

def eval (valuation : Var -> Bool) : PropForm Var -> Bool
  | var v => valuation v
  | truth => true
  | falsity => false
  | not p => !(eval valuation p)
  | and p q => eval valuation p && eval valuation q
  | or p q => eval valuation p || eval valuation q
  | imp p q => !(eval valuation p) || eval valuation q
  | iff p q => eval valuation p == eval valuation q
  | xor p q =>
      (eval valuation p && !(eval valuation q)) ||
        (!(eval valuation p) && eval valuation q)

def LogicallyEquivalent (p q : PropForm Var) : Prop :=
  forall valuation : Var -> Bool, eval valuation p = eval valuation q

def Tautology (p : PropForm Var) : Prop :=
  forall valuation : Var -> Bool, eval valuation p = true

def Contradiction (p : PropForm Var) : Prop :=
  forall valuation : Var -> Bool, eval valuation p = false

def LogicallyImplies (p q : PropForm Var) : Prop :=
  Tautology (imp p q)

/-!
# Substitution

Substitution replaces each variable by a formula.  The evaluation theorem states
that substitution is semantically the same as changing the valuation.
-/

def subst (sigma : Var -> PropForm Var') : PropForm Var -> PropForm Var'
  | var v => sigma v
  | truth => truth
  | falsity => falsity
  | not p => not (subst sigma p)
  | and p q => and (subst sigma p) (subst sigma q)
  | or p q => or (subst sigma p) (subst sigma q)
  | imp p q => imp (subst sigma p) (subst sigma q)
  | iff p q => iff (subst sigma p) (subst sigma q)
  | xor p q => xor (subst sigma p) (subst sigma q)

theorem eval_subst (sigma : Var -> PropForm Var') (valuation : Var' -> Bool)
    (p : PropForm Var) :
    eval valuation (subst sigma p) = eval (fun v => eval valuation (sigma v)) p := by
  induction p with
  | var v => rfl
  | truth => rfl
  | falsity => rfl
  | not p ih => simp [subst, eval, ih]
  | and p q ihp ihq => simp [subst, eval, ihp, ihq]
  | or p q ihp ihq => simp [subst, eval, ihp, ihq]
  | imp p q ihp ihq => simp [subst, eval, ihp, ihq]
  | iff p q ihp ihq => simp [subst, eval, ihp, ihq]
  | xor p q ihp ihq => simp [subst, eval, ihp, ihq]

/-!
# Formula contexts

A context is a formula with one hole.  Plugging equivalent formulas into the
same context preserves logical equivalence.
-/

inductive Context (Var : Type u) where
  | hole : Context Var
  | not : Context Var -> Context Var
  | andLeft : Context Var -> PropForm Var -> Context Var
  | andRight : PropForm Var -> Context Var -> Context Var
  | orLeft : Context Var -> PropForm Var -> Context Var
  | orRight : PropForm Var -> Context Var -> Context Var
  | impLeft : Context Var -> PropForm Var -> Context Var
  | impRight : PropForm Var -> Context Var -> Context Var
  | iffLeft : Context Var -> PropForm Var -> Context Var
  | iffRight : PropForm Var -> Context Var -> Context Var
  | xorLeft : Context Var -> PropForm Var -> Context Var
  | xorRight : PropForm Var -> Context Var -> Context Var

namespace Context

def plug : Context Var -> PropForm Var -> PropForm Var
  | hole, p => p
  | not c, p => PropForm.not (plug c p)
  | andLeft c q, p => PropForm.and (plug c p) q
  | andRight q c, p => PropForm.and q (plug c p)
  | orLeft c q, p => PropForm.or (plug c p) q
  | orRight q c, p => PropForm.or q (plug c p)
  | impLeft c q, p => PropForm.imp (plug c p) q
  | impRight q c, p => PropForm.imp q (plug c p)
  | iffLeft c q, p => PropForm.iff (plug c p) q
  | iffRight q c, p => PropForm.iff q (plug c p)
  | xorLeft c q, p => PropForm.xor (plug c p) q
  | xorRight q c, p => PropForm.xor q (plug c p)

theorem congr (c : Context Var) {p q : PropForm Var}
    (h : LogicallyEquivalent p q) :
    LogicallyEquivalent (plug c p) (plug c q) := by
  intro valuation
  induction c with
  | hole => exact h valuation
  | not c ih => simp [plug, eval, ih]
  | andLeft c r ih =>
      rw [plug, plug, eval, eval, ih]
  | andRight r c ih =>
      rw [plug, plug, eval, eval, ih]
  | orLeft c r ih =>
      rw [plug, plug, eval, eval, ih]
  | orRight r c ih =>
      rw [plug, plug, eval, eval, ih]
  | impLeft c r ih =>
      rw [plug, plug, eval, eval, ih]
  | impRight r c ih =>
      rw [plug, plug, eval, eval, ih]
  | iffLeft c r ih =>
      rw [plug, plug, eval, eval, ih]
  | iffRight r c ih =>
      rw [plug, plug, eval, eval, ih]
  | xorLeft c r ih =>
      rw [plug, plug, eval, eval, ih]
  | xorRight r c ih =>
      rw [plug, plug, eval, eval, ih]

end Context

/-!
# Semantic laws

The final lemmas give reusable laws connecting tautologies, contradictions,
logical equivalence, biconditionals, and substitution.
-/

theorem tautology_not_iff_contradiction (p : PropForm Var) :
    Tautology (not p) <-> Contradiction p := by
  constructor
  · intro h valuation
    have hv := h valuation
    cases hp : eval valuation p <;> simp [eval, hp] at hv ⊢
  · intro h valuation
    have hv := h valuation
    cases hp : eval valuation p <;> simp [eval, hp] at hv ⊢

theorem logicallyEquivalent_iff_iff_tautology (p q : PropForm Var) :
    LogicallyEquivalent p q <-> Tautology (iff p q) := by
  constructor
  · intro h valuation
    have hv := h valuation
    cases hp : eval valuation p <;>
      cases hq : eval valuation q <;>
      simp [eval, hp, hq] at hv ⊢
  · intro h valuation
    have hv := h valuation
    cases hp : eval valuation p <;>
      cases hq : eval valuation q <;>
      simp [eval, hp, hq] at hv ⊢

theorem logicallyEquivalent_trans {p q r : PropForm Var}
    (hpq : LogicallyEquivalent p q) (hqr : LogicallyEquivalent q r) :
    LogicallyEquivalent p r := by
  intro valuation
  exact Eq.trans (hpq valuation) (hqr valuation)

theorem first_substitution_law {p : PropForm Var} (h : Tautology p)
    (sigma : Var -> PropForm Var') : Tautology (subst sigma p) := by
  intro valuation
  rw [eval_subst sigma valuation p]
  exact h (fun v => eval valuation (sigma v))

end PropForm

end Foundation
end FoC
