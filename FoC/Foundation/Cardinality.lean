import FoC.Foundation.Finite
import FoC.Foundation.Functions

set_option doc.verso true

/-!
# Finite cardinality

## Finite-cardinality models

The book's finite-cardinality laws are represented by explicit list models:
products are nested lists of pairs, powersets are lists of sublists, and
function spaces are lists of finite tuples. Duplicate-free enumeration remains
the bridge from these list models back to finite sets.

The finite pigeonhole principle uses the same bridge: map the duplicate-free
enumeration of the larger set into the smaller one, then compare list lengths.

## Book coordinates

Used by:
- Chapter 2, Section 2.6: finite cardinality arithmetic
- Later finite-state models with explicit state/alphabet lists
-/

namespace FoC
namespace Foundation

namespace FSet

/-!
# Cardinality witnesses

Cardinality is defined by a duplicate-free finite enumeration whose length is
the displayed cardinal.  The first lemmas transport that witness across
extensional equality and give the empty and singleton cases.
-/

def HasCardinality (A : FSet alpha) (n : Nat) : Prop :=
  exists xs : List alpha, ListUniquelyEnumerates xs A ∧ xs.length = n

theorem hasCardinality_finite {A : FSet alpha} {n : Nat}
    (h : HasCardinality A n) : FiniteWithNoDuplicates A := by
  cases h with
  | intro xs hxs =>
      exact Exists.intro xs hxs.left

theorem hasCardinality_of_equal {A B : FSet alpha} {n : Nat}
    (hAB : Equal A B) (hA : HasCardinality A n) : HasCardinality B n := by
  cases hA with
  | intro xs hxs =>
      exists xs
      constructor
      · constructor
        · exact hxs.left.left
        · intro x
          constructor
          · intro hxB
            exact (hxs.left.right x).mp ((hAB x).mpr hxB)
          · intro hx
            exact (hAB x).mp ((hxs.left.right x).mpr hx)
      · exact hxs.right

theorem empty_has_cardinality_zero : HasCardinality (Empty : FSet alpha) 0 := by
  exists []
  constructor
  · constructor
    · simp [ListDuplicateFree]
    · intro x
      constructor
      · intro hx
        cases hx
      · intro hx
        cases hx
  · rfl

theorem singleton_has_cardinality_one (a : alpha) :
    HasCardinality (Singleton a) 1 := by
  exists [a]
  constructor
  · constructor
    · simp [ListDuplicateFree]
    · intro x
      constructor
      · intro hx
        rw [hx]
        exact List.Mem.head []
      · intro hx
        cases hx with
        | head => rfl
        | tail _ htail => cases htail
  · rfl

/-!
# Finite pigeonhole principle

If a function maps every member of a finite set {lit}`A` into a finite set
{lit}`B` and is injective on {lit}`A`, then {lit}`A` cannot have larger
cardinality than {lit}`B`.  The contrapositive gives the book-facing
pigeonhole theorem: a map from more listed objects into fewer listed boxes must
identify two distinct inputs.
-/

theorem cardinality_le_of_injective_maps_to {A : FSet alpha} {B : FSet beta}
    {m n : Nat} [DecidableEq beta]
    (hA : HasCardinality A m) (hB : HasCardinality B n)
    (f : alpha -> beta)
    (hinj : forall {x y}, x ∈ A -> y ∈ A -> f x = f y -> x = y)
    (hmap : forall x, x ∈ A -> f x ∈ B) : m <= n := by
  cases hA with
  | intro xs hxs =>
      cases hB with
      | intro ys hys =>
          have hndImage : (xs.map f).Nodup :=
            list_nodup_map_of_injective_on_list hxs.left.left (by
              intro a b ha hb hfab
              exact hinj
                ((hxs.left.right a).mpr ha)
                ((hxs.left.right b).mpr hb)
                hfab)
          have hsub : forall y, y ∈ xs.map f -> y ∈ ys := by
            intro y hy
            cases (List.mem_map).mp hy with
            | intro x hx =>
                have hxA : x ∈ A := (hxs.left.right x).mpr hx.left
                have hfyB : f x ∈ B := hmap x hxA
                exact (hys.left.right y).mp (by
                  rw [← hx.right]
                  exact hfyB)
          have hle := list_nodup_length_le_of_subset hndImage hsub
          simpa [List.length_map, hxs.right, hys.right] using hle

theorem not_injective_of_cardinality_lt_maps_to {A : FSet alpha} {B : FSet beta}
    {m n : Nat} [DecidableEq beta]
    (hA : HasCardinality A m) (hB : HasCardinality B n)
    (hlt : n < m) (f : alpha -> beta)
    (hmap : forall x, x ∈ A -> f x ∈ B) :
    ¬ Fn.Injective f := by
  intro hf
  have hle : m <= n :=
    cardinality_le_of_injective_maps_to hA hB f
      (by
        intro x y _hx _hy hxy
        exact hf hxy)
      hmap
  omega

theorem pigeonhole_collision_of_cardinality_lt {A : FSet alpha} {B : FSet beta}
    {m n : Nat} [DecidableEq beta]
    (hA : HasCardinality A m) (hB : HasCardinality B n)
    (hlt : n < m) (f : alpha -> beta)
    (hmap : forall x, x ∈ A -> f x ∈ B) :
    exists x y, x ∈ A ∧ y ∈ A ∧ x ≠ y ∧ f x = f y := by
  classical
  apply Classical.byContradiction
  intro hno
  have hinjOn : forall {x y}, x ∈ A -> y ∈ A -> f x = f y -> x = y := by
    intro x y hx hy hxy
    by_cases hEq : x = y
    · exact hEq
    · exfalso
      apply hno
      exact Exists.intro x
        (Exists.intro y
          (And.intro hx
            (And.intro hy
              (And.intro hEq hxy))))
  have hle : m <= n :=
    cardinality_le_of_injective_maps_to hA hB f hinjOn hmap
  omega

end FSet

namespace ListCard

/-!
# Products and disjoint parts

The finite-cardinality theorems are proved first as list-length identities.
Product cardinality uses nested lists of pairs, and union arithmetic is reduced
to disjoint parts.
-/

def Pairs {alpha : Type u} {beta : Type v} : List alpha -> List beta -> List (alpha × beta)
  | [], _ => []
  | x :: xs, ys => (ys.map fun y => (x, y)) ++ Pairs xs ys

/-!
Product cardinality is first proved at the list level: a nested list of pairs
has length equal to the product of the input lengths.
-/
theorem length_pairs {alpha : Type u} {beta : Type v} (xs : List alpha) (ys : List beta) :
    (Pairs xs ys).length = xs.length * ys.length := by
  induction xs with
  | nil => simp [Pairs]
  | cons x xs ih =>
      simp [Pairs, ih, Nat.add_mul, Nat.add_comm]

/-!
Disjoint union cardinality is represented by appending the two finite lists.
-/
theorem length_append (xs ys : List alpha) :
    (xs ++ ys).length = xs.length + ys.length := by
  exact List.length_append

/-!
The finite inclusion-exclusion identity is reduced to the three disjoint parts:
elements only on the left, elements in both sets, and elements only on the
right.
-/
theorem union_cardinality_by_parts (leftOnly both rightOnly : Nat) :
    leftOnly + both + rightOnly =
      (leftOnly + both) + (both + rightOnly) - both := by
  omega

/-!
Mapping a finite list along a function preserves its length.  This is the list
level statement behind finite cardinality transport.
-/
theorem length_map (f : alpha -> beta) (xs : List alpha) :
    (xs.map f).length = xs.length := by
  exact List.length_map f

/-!
# Powersets

The powerset model enumerates sublists.  Each input element is either omitted or
included, yielding the expected power-of-two length.
-/

def Sublists {alpha : Type u} : List alpha -> List (List alpha)
  | [] => [[]]
  | x :: xs => Sublists xs ++ (Sublists xs).map (fun ys => x :: ys)

/-!
The powerset model enumerates all sublists.  Its length is {lit}`2 ^ n`, matching the
book's finite powerset cardinality law.
-/
theorem length_sublists {alpha : Type u} (xs : List alpha) :
    (Sublists xs).length = 2 ^ xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [Sublists, ih, Nat.pow_succ]
      omega

/-!
# Function spaces

Finite function spaces are modeled as fixed-length tuples of choices.  The tuple
length theorem is the list-level core of the book's finite function-space
cardinality law.
-/

def ExtendTuples {alpha : Type u} (choices : List alpha) : List (List alpha) -> List (List alpha)
  | [] => []
  | tail :: tails => (choices.map fun x => x :: tail) ++ ExtendTuples choices tails

def Tuples {alpha : Type u} (choices : List alpha) : Nat -> List (List alpha)
  | 0 => [[]]
  | n + 1 => ExtendTuples choices (Tuples choices n)

theorem length_extendTuples {alpha : Type u} (choices : List alpha) (tails : List (List alpha)) :
    (ExtendTuples choices tails).length = tails.length * choices.length := by
  induction tails with
  | nil => simp [ExtendTuples]
  | cons tail tails ih =>
      simp [ExtendTuples, ih, Nat.add_mul, Nat.add_comm]

/-!
Finite function spaces are represented as tuples of choices.  If there are
{lit}`k` choices and {lit}`n` input positions, the tuple list has length
{lit}`k ^ n`.
-/
theorem length_tuples {alpha : Type u} (choices : List alpha) (n : Nat) :
    (Tuples choices n).length = choices.length ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Tuples, length_extendTuples, ih, Nat.pow_succ]

end ListCard

end Foundation
end FoC
