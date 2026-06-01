import FoC.Foundation.Sets

namespace FoC
namespace Foundation

/-!
Standalone relation vocabulary for Chapter 2.
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

def Class (R : Rel alpha) (x : alpha) : FSet alpha :=
  fun y => R x y

structure Partition (alpha : Type u) where
  block : FSet (FSet alpha)
  covers : forall x, exists B, B ∈ block ∧ x ∈ B
  nonempty : forall B, B ∈ block -> exists x, x ∈ B
  overlap_equal :
    forall A B, A ∈ block -> B ∈ block ->
      (exists x, x ∈ A ∧ x ∈ B) -> FSet.Equal A B

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

end Rel

end Foundation
end FoC

