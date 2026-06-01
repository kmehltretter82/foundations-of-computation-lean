namespace FoC
namespace Foundation

/-!
Small list lemmas and definitions used by the standalone development.

This file starts intentionally small. It should grow only as the book
formalization needs concrete list facts.
-/

def ListContains (xs : List alpha) (x : alpha) : Prop :=
  x ∈ xs

def ListEnumerates (xs : List alpha) (p : alpha -> Prop) : Prop :=
  forall x, p x <-> x ∈ xs

def ListDuplicateFree (xs : List alpha) : Prop :=
  xs.Nodup

def ListUniquelyEnumerates (xs : List alpha) (p : alpha -> Prop) : Prop :=
  ListDuplicateFree xs ∧ ListEnumerates xs p

theorem ListEnumerates.left {xs : List alpha} {p : alpha -> Prop}
    (h : ListEnumerates xs p) {x : alpha} : p x -> x ∈ xs :=
  (h x).mp

theorem ListEnumerates.right {xs : List alpha} {p : alpha -> Prop}
    (h : ListEnumerates xs p) {x : alpha} : x ∈ xs -> p x :=
  (h x).mpr

theorem list_getElem?_of_map_eq_some {α : Type u} {β : Type v}
    {xs : List α} {f : α -> β} {i : Nat} {b : β}
    (h : (xs.map f)[i]? = some b) :
    exists a, xs[i]? = some a ∧ f a = b := by
  rw [List.getElem?_map] at h
  cases hxi : xs[i]? with
  | none =>
      simp [hxi] at h
  | some a =>
      simp [hxi] at h
      exists a

theorem list_nodup_length_le_of_subset {α : Type u} [DecidableEq α]
    {ys xs : List α}
    (hnd : ys.Nodup) (hsub : forall a, a ∈ ys -> a ∈ xs) :
    ys.length <= xs.length := by
  induction ys generalizing xs with
  | nil =>
      simp
  | cons y ys ih =>
      simp at hnd
      have hyxs : y ∈ xs := hsub y (List.Mem.head ys)
      have hsubErase : forall a, a ∈ ys -> a ∈ xs.erase y := by
        intro a ha
        have haxs : a ∈ xs := hsub a (List.Mem.tail y ha)
        have hay : a ≠ y := by
          intro heq
          rw [heq] at ha
          exact hnd.left ha
        exact (List.mem_erase_of_ne hay).mpr haxs
      have hle := ih hnd.right hsubErase
      have hlen := List.length_erase_of_mem hyxs
      have hxpos : 0 < xs.length := List.length_pos_iff_exists_mem.mpr ⟨y, hyxs⟩
      simp
      omega

theorem list_not_nodup_exists_duplicate_split {α : Type u} [DecidableEq α]
    {xs : List α} (h : ¬ xs.Nodup) :
    exists pre a mid post, xs = pre ++ [a] ++ mid ++ [a] ++ post := by
  induction xs with
  | nil =>
      simp at h
  | cons x xs ih =>
      by_cases hx : x ∈ xs
      · cases (List.mem_iff_append.mp hx) with
        | intro mid hmid =>
            cases hmid with
            | intro post hpost =>
                exists []
                exists x
                exists mid
                exists post
                rw [hpost]
                simp [List.append_assoc]
      · have hnotTail : ¬ xs.Nodup := by
          intro hnd
          exact h (by simp [hx, hnd])
        cases ih hnotTail with
        | intro pre hpre =>
            cases hpre with
            | intro a ha =>
                cases ha with
                | intro mid hmid =>
                    cases hmid with
                    | intro post hpost =>
                        exists x :: pre
                        exists a
                        exists mid
                        exists post
                        rw [hpost]
                        rfl

theorem list_duplicate_indices_of_split {α : Type u}
    {xs pre mid post : List α} {a : α}
    (h : xs = pre ++ [a] ++ mid ++ [a] ++ post) :
    exists i j, i < j ∧ j < xs.length ∧ xs[i]? = some a ∧ xs[j]? = some a := by
  subst xs
  exists pre.length
  exists pre.length + 1 + mid.length
  constructor
  · omega
  constructor
  · simp [List.length_append]
    omega
  constructor
  · simp
  · have hj : pre.length + 1 + mid.length = (pre ++ [a] ++ mid).length := by
      simp [List.length_append]
      omega
    rw [hj]
    have hlist :
        pre ++ [a] ++ mid ++ [a] ++ post =
          (pre ++ [a] ++ mid) ++ ([a] ++ post) := by
      simp [List.append_assoc]
    rw [hlist]
    rw [List.getElem?_append_right (l₁ := pre ++ [a] ++ mid) (l₂ := [a] ++ post)]
    · simp
    · omega

theorem list_duplicate_indices_of_length_gt {α : Type u} [DecidableEq α]
    {xs elems : List α}
    (hlen : elems.length < xs.length)
    (hall : forall a, a ∈ xs -> a ∈ elems) :
    exists i j a, i < j ∧ j < xs.length ∧ xs[i]? = some a ∧ xs[j]? = some a := by
  have hnot : ¬ xs.Nodup := by
    intro hnd
    have hle := list_nodup_length_le_of_subset hnd hall
    omega
  cases list_not_nodup_exists_duplicate_split hnot with
  | intro pre hpre =>
      cases hpre with
      | intro a ha =>
          cases ha with
          | intro mid hmid =>
              cases hmid with
              | intro post hpost =>
                  cases list_duplicate_indices_of_split hpost with
                  | intro i hi =>
                      cases hi with
                      | intro j hj =>
                          exists i
                          exists j
                          exists a

end Foundation
end FoC
