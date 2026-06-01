import FoC.Foundation.Finite

namespace FoC
namespace Foundation

/-!
Standalone finite-cardinality infrastructure.

The book's finite-cardinality laws are represented by explicit list models:
products are nested lists of pairs, powersets are lists of sublists, and
function spaces are lists of finite tuples. Duplicate-free enumeration remains
the bridge from these list models back to finite sets.

Used by:
- Chapter 2, Section 2.6: finite cardinality arithmetic
- Later finite-state models with explicit state/alphabet lists
-/

namespace FSet

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

end FSet

namespace ListCard

def Pairs {alpha : Type u} {beta : Type v} : List alpha -> List beta -> List (alpha × beta)
  | [], _ => []
  | x :: xs, ys => (ys.map fun y => (x, y)) ++ Pairs xs ys

-- Book: Chapter 2, Section 2.6, product cardinality.
theorem length_pairs {alpha : Type u} {beta : Type v} (xs : List alpha) (ys : List beta) :
    (Pairs xs ys).length = xs.length * ys.length := by
  induction xs with
  | nil => simp [Pairs]
  | cons x xs ih =>
      simp [Pairs, ih, Nat.add_mul, Nat.add_comm]

-- Book: Chapter 2, Section 2.6, disjoint union cardinality model.
theorem length_append (xs ys : List alpha) :
    (xs ++ ys).length = xs.length + ys.length := by
  exact List.length_append

-- Book: Chapter 2, Section 2.6, inclusion-exclusion by disjoint parts.
theorem union_cardinality_by_parts (leftOnly both rightOnly : Nat) :
    leftOnly + both + rightOnly =
      (leftOnly + both) + (both + rightOnly) - both := by
  omega

-- Book: Chapter 2, Section 2.6, cardinality is preserved by list transport.
theorem length_map (f : alpha -> beta) (xs : List alpha) :
    (xs.map f).length = xs.length := by
  exact List.length_map f

def Sublists {alpha : Type u} : List alpha -> List (List alpha)
  | [] => [[]]
  | x :: xs => Sublists xs ++ (Sublists xs).map (fun ys => x :: ys)

-- Book: Chapter 2, Section 2.6, powerset cardinality.
theorem length_sublists {alpha : Type u} (xs : List alpha) :
    (Sublists xs).length = 2 ^ xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [Sublists, ih, Nat.pow_succ]
      omega

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

-- Book: Chapter 2, Section 2.6, finite function-space cardinality.
theorem length_tuples {alpha : Type u} (choices : List alpha) (n : Nat) :
    (Tuples choices n).length = choices.length ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Tuples, length_extendTuples, ih, Nat.pow_succ]

end ListCard

end Foundation
end FoC
