import FoC.Foundation.Lists
import FoC.Foundation.Sets

namespace FoC
namespace Foundation

/-!
Finite sets and finite types, represented by explicit list enumerations.
-/

structure FiniteType (alpha : Type u) where
  elems : List alpha
  complete : forall x : alpha, x ∈ elems

namespace FSet

def Finite (A : FSet alpha) : Prop :=
  exists xs : List alpha, ListEnumerates xs A

def FiniteWithNoDuplicates (A : FSet alpha) : Prop :=
  exists xs : List alpha, ListUniquelyEnumerates xs A

theorem empty_finite : Finite (Empty : FSet alpha) := by
  exists []
  intro x
  constructor
  · intro hx
    cases hx
  · intro hx
    cases hx

theorem singleton_finite (a : alpha) : Finite (Singleton a) := by
  exists [a]
  intro x
  constructor
  · intro hx
    rw [hx]
    exact List.Mem.head []
  · intro hx
    cases hx with
    | head =>
        rfl
    | tail _ htail =>
        cases htail

-- Book: Chapter 2, Section 2.6, Exercise 12(c).
theorem finite_subset {A B : FSet alpha}
    (hAB : Subset A B) (hB : Finite B) : Finite A := by
  classical
  cases hB with
  | intro xs hxs =>
      exists xs.filter (fun x => decide (x ∈ A))
      intro x
      constructor
      · intro hxA
        have hxB := hAB x hxA
        have hxList := (hxs x).mp hxB
        simp [hxList]
        exact hxA
      · intro hxFilter
        have hx : x ∈ xs ∧ x ∈ A := by
          simpa using hxFilter
        exact hx.right

end FSet

end Foundation
end FoC
