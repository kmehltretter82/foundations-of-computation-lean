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
enumerating list carried by {name}`FiniteType`.  The general index helper is
intentionally noncomputable because it does not assume decidable equality; the
decidable-equality variant records the executable search used by finite
machine constructions.
-/

def fin (n : Nat) : FiniteType (Fin n) where
  elems := List.finRange n
  complete := List.mem_finRange

def unit : FiniteType Unit where
  elems := [()]
  complete := by
    intro x
    cases x
    simp

def bool : FiniteType Bool where
  elems := [false, true]
  complete := by
    intro x
    cases x <;> simp

def option (finite : FiniteType alpha) : FiniteType (Option alpha) where
  elems := none :: finite.elems.map some
  complete := by
    intro x
    cases x with
    | none =>
        simp
    | some x =>
        simp
        exact finite.complete x

def sum (left : FiniteType alpha) (right : FiniteType beta) :
    FiniteType (Sum alpha beta) where
  elems := left.elems.map Sum.inl ++ right.elems.map Sum.inr
  complete := by
    intro x
    cases x with
    | inl x =>
        simp
        exact left.complete x
    | inr x =>
        simp
        exact right.complete x

def pairElems : List alpha -> List beta -> List (alpha × beta)
  | [], _ => []
  | x :: xs, ys => (ys.map fun y => (x, y)) ++ pairElems xs ys

theorem pair_mem {xs : List alpha} {ys : List beta}
    {x : alpha} {y : beta} (hx : x ∈ xs) (hy : y ∈ ys) :
    (x, y) ∈ pairElems xs ys := by
  induction xs with
  | nil =>
      cases hx
  | cons z zs ih =>
      cases hx with
      | head =>
          simp [pairElems, hy]
      | tail _ htail =>
          exact List.mem_append.mpr (Or.inr (ih htail))

def prod (left : FiniteType alpha) (right : FiniteType beta) :
    FiniteType (alpha × beta) where
  elems := pairElems left.elems right.elems
  complete := by
    intro x
    exact pair_mem (left.complete x.1) (right.complete x.2)

def product (left : FiniteType alpha) (right : FiniteType beta) :
    FiniteType (alpha × beta) :=
  prod left right

def sigma {beta : alpha -> Type v}
    (base : FiniteType alpha)
    (fiber : forall a : alpha, FiniteType (beta a)) :
    FiniteType (Sigma beta) where
  elems :=
    base.elems.flatMap
      (fun a => (fiber a).elems.map (fun b => Sigma.mk a b))
  complete := by
    intro x
    rcases x with ⟨a, b⟩
    exact
      List.mem_flatMap.mpr
        ⟨a, base.complete a,
          List.mem_map.mpr ⟨b, (fiber a).complete b, rfl⟩⟩

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

def indexOfMemDecidable [DecidableEq alpha] :
    (xs : List alpha) -> (x : alpha) -> x ∈ xs -> Fin xs.length
  | [], _x, h => False.elim (by simp at h)
  | y :: ys, x, h =>
      if hxy : x = y then
        ⟨0, by simp⟩
      else
        let tailIndex := indexOfMemDecidable ys x (by
          simpa [hxy] using h)
        ⟨tailIndex.val + 1, by
          have hlt := tailIndex.isLt
          exact Nat.succ_lt_succ hlt⟩

theorem get_indexOfMemDecidable [DecidableEq alpha] :
    (xs : List alpha) -> (x : alpha) -> (h : x ∈ xs) ->
      xs[indexOfMemDecidable xs x h] = x
  | [], _x, h => False.elim (by simp at h)
  | y :: ys, x, h => by
      by_cases hxy : x = y
      · simp [indexOfMemDecidable, hxy]
      · simp [indexOfMemDecidable, hxy]
        exact get_indexOfMemDecidable ys x (by simpa [hxy] using h)

def indexOfDecidable [DecidableEq alpha]
    (finite : FiniteType alpha) (x : alpha) : Fin finite.elems.length :=
  indexOfMemDecidable finite.elems x (finite.complete x)

theorem valueOf_indexOfDecidable [DecidableEq alpha]
    (finite : FiniteType alpha) (x : alpha) :
    valueOf finite (indexOfDecidable finite x) = x :=
  get_indexOfMemDecidable finite.elems x (finite.complete x)

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
