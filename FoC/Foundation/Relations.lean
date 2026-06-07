import FoC.Foundation.Sets

set_option doc.verso true

/-!
# Relations

## Relation properties

This module formalizes the relation vocabulary from Chapter 2: reflexive,
symmetric, antisymmetric, transitive, equivalence, partial order, total order,
equivalence classes, and partitions.  Relations are represented directly as
binary predicates.

## Book coordinates

Used by:
- Chapter 2, Section 2.7: Relations
- Later transition-system chapters that need reachability-style relations
-/

namespace FoC
namespace Foundation

/-!
# Relation predicates

A relation is a binary predicate.  The first definitions package the usual
properties and order/equivalence combinations.
-/

def Rel (alpha : Type u) : Type u :=
  alpha -> alpha -> Prop

namespace Rel

def Reflexive (R : Rel alpha) : Prop :=
  forall x, R x x

def Symmetric (R : Rel alpha) : Prop :=
  forall {x y}, R x y -> R y x

def Antisymmetric (R : Rel alpha) : Prop :=
  forall {x y}, R x y -> R y x -> x = y

def Transitive (R : Rel alpha) : Prop :=
  forall {x y z}, R x y -> R y z -> R x z

def Equivalence (R : Rel alpha) : Prop :=
  Reflexive R ∧ Symmetric R ∧ Transitive R

def PartialOrder (R : Rel alpha) : Prop :=
  Reflexive R ∧ Antisymmetric R ∧ Transitive R

def TotalOrder (R : Rel alpha) : Prop :=
  PartialOrder R ∧ forall x y, R x y ∨ R y x

def Class (R : Rel alpha) (x : alpha) : FSet alpha :=
  fun y => R x y

def Classes (R : Rel alpha) : FSet (FSet alpha) :=
  fun C => exists x, FSet.Equal C (Class R x)

structure Partition (alpha : Type u) where
  block : FSet (FSet alpha)
  covers : forall x, exists B, B ∈ block ∧ x ∈ B
  nonempty : forall B, B ∈ block -> exists x, x ∈ B
  overlap_equal :
    forall A B, A ∈ block -> B ∈ block ->
      (exists x, x ∈ A ∧ x ∈ B) -> FSet.Equal A B

/-!
# Equivalence classes and partitions

Equivalence relations determine classes, and those classes form a partition of
the underlying type.
-/

theorem equivalence_reflexive {R : Rel alpha} (h : Equivalence R) : Reflexive R :=
  h.left

theorem equivalence_symmetric {R : Rel alpha} (h : Equivalence R) : Symmetric R :=
  h.right.left

theorem equivalence_transitive {R : Rel alpha} (h : Equivalence R) : Transitive R :=
  h.right.right

theorem equality_equivalence : Equivalence (fun x y : alpha => x = y) := by
  constructor
  · intro x
    rfl
  · constructor
    · intro x y h
      exact h.symm
    · intro x y z hxy hyz
      exact Eq.trans hxy hyz

theorem class_self {R : Rel alpha} (h : Equivalence R) (x : alpha) :
    x ∈ Class R x :=
  h.left x

theorem class_equal_of_related {R : Rel alpha} (h : Equivalence R)
    {a b : alpha} (hab : R a b) : FSet.Equal (Class R a) (Class R b) := by
  intro x
  constructor
  · intro hax
    exact h.right.right (h.right.left hab) hax
  · intro hbx
    exact h.right.right hab hbx

theorem class_equal_iff_related {R : Rel alpha} (h : Equivalence R)
    {a b : alpha} : FSet.Equal (Class R a) (Class R b) <-> R a b := by
  constructor
  · intro hClass
    exact (hClass b).mpr (class_self h b)
  · exact class_equal_of_related h

theorem overlapping_classes_equal {R : Rel alpha} (h : Equivalence R)
    {a b : alpha} (hoverlap : exists x, x ∈ Class R a ∧ x ∈ Class R b) :
    FSet.Equal (Class R a) (Class R b) := by
  cases hoverlap with
  | intro x hx =>
      have hab : R a b := h.right.right hx.left (h.right.left hx.right)
      exact class_equal_of_related h hab

theorem classes_equal_or_disjoint {R : Rel alpha} (h : Equivalence R)
    (a b : alpha) :
    FSet.Equal (Class R a) (Class R b) ∨ FSet.Disjoint (Class R a) (Class R b) := by
  classical
  by_cases hoverlap : exists x, x ∈ Class R a ∧ x ∈ Class R b
  · exact Or.inl (overlapping_classes_equal h hoverlap)
  · exact Or.inr (by
      intro x hx
      exact hoverlap (Exists.intro x hx))

def classes_partition {R : Rel alpha} (h : Equivalence R) : Partition alpha where
  block := Classes R
  covers := by
    intro x
    exact Exists.intro (Class R x)
      (And.intro (Exists.intro x (FSet.equal_refl (Class R x))) (class_self h x))
  nonempty := by
    intro B hB
    cases hB with
    | intro a hEq =>
        exact Exists.intro a ((hEq a).mpr (class_self h a))
  overlap_equal := by
    intro A B hA hB hOverlap
    cases hA with
    | intro a hAeq =>
        cases hB with
        | intro b hBeq =>
            cases hOverlap with
            | intro x hx =>
                have hax : R a x := (hAeq x).mp hx.left
                have hbx : R b x := (hBeq x).mp hx.right
                have hab : R a b := h.right.right hax (h.right.left hbx)
                have hClass : FSet.Equal (Class R a) (Class R b) :=
                  class_equal_of_related h hab
                exact FSet.equal_trans hAeq (FSet.equal_trans hClass (FSet.equal_symm hBeq))

theorem same_fiber_equivalence (f : alpha -> beta) :
    Equivalence (fun x y : alpha => f x = f y) := by
  constructor
  · intro x
    rfl
  · constructor
    · intro x y hxy
      exact hxy.symm
    · intro x y z hxy hyz
      exact Eq.trans hxy hyz

/-!
# Transitive closure

The transitive closure is the reachability-style relation reused by later
transition-system material.
-/

theorem symmetric_antisymmetric_implies_eq {R : Rel alpha}
    (hs : Symmetric R) (ha : Antisymmetric R) :
    forall {x y}, R x y -> x = y := by
  intro x y hxy
  exact ha hxy (hs hxy)

inductive TransitiveClosure (R : Rel alpha) : Rel alpha where
  | single {x y : alpha} : R x y -> TransitiveClosure R x y
  | step {x y z : alpha} : R x y -> TransitiveClosure R y z -> TransitiveClosure R x z

theorem transitiveClosure_transitive {R : Rel alpha} :
    Transitive (TransitiveClosure R) := by
  intro x y z hxy hyz
  induction hxy generalizing z with
  | single h =>
      exact TransitiveClosure.step h hyz
  | step h hrest ih =>
      exact TransitiveClosure.step h (ih hyz)

theorem transitiveClosure_symmetric_of_symmetric {R : Rel alpha}
    (hs : Symmetric R) : Symmetric (TransitiveClosure R) := by
  intro x y hxy
  induction hxy with
  | single h =>
      exact TransitiveClosure.single (hs h)
  | step h hrest ih =>
      exact transitiveClosure_transitive ih (TransitiveClosure.single (hs h))

theorem transitiveClosure_equivalence_of_reflexive_symmetric {R : Rel alpha}
    (hr : Reflexive R) (hs : Symmetric R) : Equivalence (TransitiveClosure R) := by
  constructor
  · intro x
    exact TransitiveClosure.single (hr x)
  · constructor
    · exact transitiveClosure_symmetric_of_symmetric hs
    · exact transitiveClosure_transitive

end Rel

end Foundation
end FoC
