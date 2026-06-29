import FoC.Foundation.Lists
import FoC.Foundation.Sets

set_option doc.verso true

/-!
# Finite sets

## Finite witnesses

The Foundation library represents finite sets by explicit list enumerations.
This matches the book's concrete use of finite collections while giving Lean a
witness that can be inspected and reused in later cardinality arguments.

The duplicate-free variant records the stronger fact needed when a list is used
as a cardinality witness.
-/

namespace FoC
namespace Foundation

/-!
# Finite types

A finite type is represented by a list that contains every value of the type.
This is the finite-state witness reused by automata and grammar modules.
-/

structure FiniteType (alpha : Type u) where
  elems : List alpha
  complete : forall x : alpha, x ∈ elems

namespace FiniteType

/-!
Finite-state constructions sometimes need to replace an arbitrary finite state
type by a concrete index type.  The index/value helpers below use the
enumerating list carried by {name}`FiniteType`; they are intentionally
noncomputable because the project only needs them for finite construction
packaging, not for extracted computation.
-/

def fin (n : Nat) : FiniteType (Fin n) where
  elems := List.finRange n
  complete := List.mem_finRange

noncomputable def indexOf
    (finite : FiniteType alpha) (x : alpha) : Fin finite.elems.length :=
  let h : ∃ i, ∃ hlt : i < finite.elems.length,
      finite.elems[i] = x :=
    (List.mem_iff_getElem).mp (finite.complete x)
  ⟨Classical.choose h, Classical.choose (Classical.choose_spec h)⟩

def valueOf
    (finite : FiniteType alpha) (index : Fin finite.elems.length) : alpha :=
  finite.elems[index]

theorem valueOf_indexOf
    (finite : FiniteType alpha) (x : alpha) :
    valueOf finite (indexOf finite x) = x := by
  unfold valueOf indexOf
  let h : ∃ i, ∃ hlt : i < finite.elems.length,
      finite.elems[i] = x :=
    (List.mem_iff_getElem).mp (finite.complete x)
  exact Classical.choose_spec (Classical.choose_spec h)

end FiniteType

namespace FSet

/-!
# Finite predicate sets

For sets represented as predicates, finiteness means that some list enumerates
exactly the members of the predicate.  The duplicate-free variant is the one
used for cardinality witnesses.
-/

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

/-!
# Finite subsets

Exercise 12(c) is the finite-subset principle: every subset of a finite set is
finite.  The proof filters the finite list for the larger set.
-/
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
