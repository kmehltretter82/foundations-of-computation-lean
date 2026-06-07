set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter01
namespace Section04

/-!
# Chapter 1, Section 1.4: Predicates and Quantifiers

This section moves from propositional formulas to predicates over a domain.
Lean's ordinary function and proposition types already represent the book's
one-place predicates, universal statements, and existential statements.

The theorem group formalizes the Figure 1.5 quantifier laws: negating a
universal statement, negating an existential statement, and commuting two
quantifiers of the same kind.

Lean distinguishes Boolean computation from propositions. Here the predicates
return {lit}`Prop`, so a universal statement is literally a dependent function
{lit}`forall x, P x`, and an existential statement is a pair containing a witness
and a proof that the witness has the property. The theorems below are the
formal versions of the book's quantifier transformations.
-/

/-! A one-place predicate on a domain is a proposition-valued function. -/
def OnePlacePredicate (domain : Type u) : Type u :=
  domain -> Prop

def Universal (P : alpha -> Prop) : Prop :=
  forall x, P x

def Existential (P : alpha -> Prop) : Prop :=
  exists x, P x

/-! Negating a universal statement is equivalent to giving a counterexample. -/
theorem not_forall_equiv_exists_not (P : alpha -> Prop) :
    (¬ forall x, P x) <-> exists x, ¬ P x := by
  classical
  constructor
  · intro h
    exact Classical.byContradiction (fun hnone =>
      h (fun x =>
        Classical.byContradiction (fun hx =>
          hnone (Exists.intro x hx))))
  · intro h hforall
    cases h with
    | intro x hx =>
        exact hx (hforall x)

theorem not_exists_equiv_forall_not (P : alpha -> Prop) :
    (¬ exists x, P x) <-> forall x, ¬ P x := by
  constructor
  · intro h x hx
    exact h (Exists.intro x hx)
  · intro h hexists
    cases hexists with
    | intro x hx =>
        exact h x hx

theorem forall_comm (Q : alpha -> beta -> Prop) :
    (forall x, forall y, Q x y) <-> forall y, forall x, Q x y := by
  constructor
  · intro h y x
    exact h x y
  · intro h x y
    exact h y x

theorem exists_comm (Q : alpha -> beta -> Prop) :
    (exists x, exists y, Q x y) <-> exists y, exists x, Q x y := by
  constructor
  · intro h
    cases h with
    | intro x hy =>
        cases hy with
        | intro y hq =>
            exact Exists.intro y (Exists.intro x hq)
  · intro h
    cases h with
    | intro y hx =>
        cases hx with
        | intro x hq =>
            exact Exists.intro x (Exists.intro y hq)

end Section04
end Chapter01
end Book
end FoC
