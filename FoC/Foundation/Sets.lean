namespace FoC
namespace Foundation

/-!
Standalone set infrastructure.

The book treats sets extensionally. We represent a set of `alpha` as a
predicate `alpha -> Prop`, and use `FSet.Equal` for book-style equality.
-/

def FSet (alpha : Type u) : Type u :=
  alpha -> Prop

namespace FSet

instance : Membership alpha (FSet alpha) where
  mem A x := A x

def Empty : FSet alpha :=
  fun _ => False

def Univ : FSet alpha :=
  fun _ => True

def Singleton (a : alpha) : FSet alpha :=
  fun x => x = a

def Pair (a b : alpha) : FSet alpha :=
  fun x => x = a ∨ x = b

def Subset (A B : FSet alpha) : Prop :=
  forall x, x ∈ A -> x ∈ B

def Equal (A B : FSet alpha) : Prop :=
  forall x, x ∈ A <-> x ∈ B

def ProperSubset (A B : FSet alpha) : Prop :=
  Subset A B ∧ ¬ Subset B A

def Union (A B : FSet alpha) : FSet alpha :=
  fun x => x ∈ A ∨ x ∈ B

def Inter (A B : FSet alpha) : FSet alpha :=
  fun x => x ∈ A ∧ x ∈ B

def Compl (A : FSet alpha) : FSet alpha :=
  fun x => ¬ x ∈ A

def Diff (A B : FSet alpha) : FSet alpha :=
  fun x => x ∈ A ∧ ¬ x ∈ B

def Powerset (A : FSet alpha) : FSet (FSet alpha) :=
  fun B => Subset B A

theorem subset_refl (A : FSet alpha) : Subset A A := by
  intro x hx
  exact hx

theorem subset_trans {A B C : FSet alpha}
    (hAB : Subset A B) (hBC : Subset B C) : Subset A C := by
  intro x hx
  exact hBC x (hAB x hx)

theorem equal_refl (A : FSet alpha) : Equal A A := by
  intro x
  constructor <;> intro hx <;> exact hx

theorem equal_symm {A B : FSet alpha} (h : Equal A B) : Equal B A := by
  intro x
  constructor
  · intro hx
    exact (h x).mpr hx
  · intro hx
    exact (h x).mp hx

theorem equal_trans {A B C : FSet alpha}
    (hAB : Equal A B) (hBC : Equal B C) : Equal A C := by
  intro x
  constructor
  · intro hx
    exact (hBC x).mp ((hAB x).mp hx)
  · intro hx
    exact (hAB x).mpr ((hBC x).mpr hx)

theorem equal_of_subsets {A B : FSet alpha}
    (hAB : Subset A B) (hBA : Subset B A) : Equal A B := by
  intro x
  constructor
  · intro hx
    exact hAB x hx
  · intro hx
    exact hBA x hx

theorem union_left_subset (A B : FSet alpha) : Subset A (Union A B) := by
  intro x hx
  exact Or.inl hx

theorem union_right_subset (A B : FSet alpha) : Subset B (Union A B) := by
  intro x hx
  exact Or.inr hx

theorem inter_subset_left (A B : FSet alpha) : Subset (Inter A B) A := by
  intro x hx
  exact hx.left

theorem inter_subset_right (A B : FSet alpha) : Subset (Inter A B) B := by
  intro x hx
  exact hx.right

theorem empty_subset (A : FSet alpha) : Subset Empty A := by
  intro x hx
  cases hx

end FSet

end Foundation
end FoC
