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

def TwoPlacePredicate (domain1 : Type u) (domain2 : Type v) : Type (max u v) :=
  domain1 -> domain2 -> Prop

def Universal (P : alpha -> Prop) : Prop :=
  forall x, P x

def Existential (P : alpha -> Prop) : Prop :=
  exists x, P x

def AtLeastTwo (P : alpha -> Prop) : Prop :=
  exists x y, P x ∧ P y ∧ x ≠ y

def AtLeastThree (P : alpha -> Prop) : Prop :=
  exists x y z, P x ∧ P y ∧ P z ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z

def ExactlyOne (P : alpha -> Prop) : Prop :=
  (exists x, P x) ∧ forall y z, P y -> P z -> y = z

/-!
# Finite Domains and Translation Examples

For a finite domain, quantifiers reduce to the propositional connectives from
the previous sections. These examples formalize the exercise that compares
predicate De Morgan laws with ordinary Boolean algebra on two- and three-element
domains.
-/

inductive TwoEntity where
  | first
  | second

namespace TwoEntity

theorem forall_iff_conjunction (P : TwoEntity -> Prop) :
    (forall x, P x) <-> P first ∧ P second := by
  constructor
  · intro h
    exact And.intro (h first) (h second)
  · intro h x
    cases x
    · exact h.left
    · exact h.right

theorem exists_iff_disjunction (P : TwoEntity -> Prop) :
    (exists x, P x) <-> P first ∨ P second := by
  constructor
  · intro h
    cases h with
    | intro x hx =>
        cases x
        · exact Or.inl hx
        · exact Or.inr hx
  · intro h
    cases h with
    | inl hfirst => exact Exists.intro first hfirst
    | inr hsecond => exact Exists.intro second hsecond

end TwoEntity

inductive ThreeEntity where
  | first
  | second
  | third

namespace ThreeEntity

theorem forall_iff_conjunction (P : ThreeEntity -> Prop) :
    (forall x, P x) <-> P first ∧ P second ∧ P third := by
  constructor
  · intro h
    exact And.intro (h first) (And.intro (h second) (h third))
  · intro h x
    cases x
    · exact h.left
    · exact h.right.left
    · exact h.right.right

theorem exists_iff_disjunction (P : ThreeEntity -> Prop) :
    (exists x, P x) <-> P first ∨ P second ∨ P third := by
  constructor
  · intro h
    cases h with
    | intro x hx =>
        cases x
        · exact Or.inl hx
        · exact Or.inr (Or.inl hx)
        · exact Or.inr (Or.inr hx)
  · intro h
    cases h with
    | inl hfirst => exact Exists.intro first hfirst
    | inr hrest =>
        cases hrest with
        | inl hsecond => exact Exists.intro second hsecond
        | inr hthird => exact Exists.intro third hthird

end ThreeEntity

namespace FlowerExample

inductive Flower where
  | rose
  | violet
  | tulip

def IsRose : Flower -> Prop
  | Flower.rose => True
  | Flower.violet => False
  | Flower.tulip => False

def IsRed : Flower -> Prop
  | Flower.rose => True
  | Flower.violet => False
  | Flower.tulip => True

def IsPretty : Flower -> Prop
  | Flower.rose => True
  | Flower.violet => True
  | Flower.tulip => True

theorem roses_are_red_as_implication :
    forall x, IsRose x -> IsRed x := by
  intro x hx
  cases x <;> simp [IsRose, IsRed] at hx ⊢

theorem red_roses_are_pretty :
    forall x, IsRose x ∧ IsRed x -> IsPretty x := by
  intro x hx
  cases x <;> simp [IsRose, IsRed, IsPretty] at hx ⊢

end FlowerExample

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

theorem mixed_quantifier_order_can_change_meaning :
    (¬ (exists x : Bool, forall y : Bool, x = y)) ∧
      (forall y : Bool, exists x : Bool, x = y) := by
  constructor
  · intro h
    cases h with
    | intro x hx =>
        cases x
        · have hbad := hx true
          cases hbad
        · have hbad := hx false
          cases hbad
  · intro y
    exact Exists.intro y rfl

theorem not_forall_or_equiv_exists_not_and_not (R Q : alpha -> Prop) :
    (¬ forall x, R x ∨ Q x) <-> exists x, ¬ R x ∧ ¬ Q x := by
  classical
  constructor
  · intro h
    cases (not_forall_equiv_exists_not (fun x => R x ∨ Q x)).mp h with
    | intro x hx =>
        exact Exists.intro x
          (And.intro
            (fun hr => hx (Or.inl hr))
            (fun hq => hx (Or.inr hq)))
  · intro h hall
    cases h with
    | intro x hx =>
        cases hall x with
        | inl hr => exact hx.left hr
        | inr hq => exact hx.right hq

theorem not_exists_and_forall_imp_equiv
    (P Q : alpha -> Prop) :
    (¬ exists x, P x ∧ (forall y, Q y -> Q x)) <->
      forall x, ¬ P x ∨ exists y, Q y ∧ ¬ Q x := by
  classical
  constructor
  · intro h x
    by_cases hx : P x
    · right
      have hnot : ¬ forall y, Q y -> Q x := by
        intro hall
        exact h (Exists.intro x (And.intro hx hall))
      have hnotQx : ¬ Q x := by
        intro hQx
        exact hnot (fun _ _ => hQx)
      have hexistsQ : exists y, Q y := by
        apply Classical.byContradiction
        intro hnone
        apply hnot
        intro y hy
        exact False.elim (hnone (Exists.intro y hy))
      cases hexistsQ with
      | intro y hy =>
          exact Exists.intro y (And.intro hy hnotQx)
    · left
      exact hx
  · intro h hexists
    cases hexists with
    | intro x hx =>
        cases h x with
        | inl hnP => exact hnP hx.left
        | inr hbad =>
            cases hbad with
            | intro y hy =>
                exact hy.right (hx.right y hy.left)

end Section04
end Chapter01
end Book
end FoC
