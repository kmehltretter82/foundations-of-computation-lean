set_option doc.verso true

/-!
# List lemmas

Small dependency-light list lemmas used by concrete machine proofs.
-/

namespace FoC
namespace Computability

theorem list_replicate_append_cons_eq_cons_append
    (a : α) (n : Nat) (rest : List α) :
    List.replicate n a ++ a :: rest =
      a :: (List.replicate n a ++ rest) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        a :: (List.replicate n a ++ a :: rest) =
          a :: (a :: (List.replicate n a ++ rest))
      rw [ih]

theorem list_replicate_append_self
    (a : α) (n : Nat) (rest : List α) :
    List.replicate n a ++ a :: rest =
      List.replicate (n + 1) a ++ rest := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        a :: (List.replicate n a ++ a :: rest) =
          a :: (List.replicate (n + 1) a ++ rest)
      rw [ih]

theorem list_replicate_add_append
    (a : α) (n m : Nat) (rest : List α) :
    List.replicate (n + m) a ++ rest =
      List.replicate n a ++
        (List.replicate m a ++ rest) := by
  induction m generalizing rest with
  | zero =>
      simp [Nat.add_zero]
  | succ m ih =>
      rw [← Nat.add_assoc]
      rw [← list_replicate_append_self a (n + m) rest]
      rw [ih (a :: rest)]
      rw [list_replicate_append_self a m rest]

theorem list_exists_append_singleton_of_ne_nil
    (xs : List α) (h : xs ≠ []) :
    exists init : List α, exists last : α,
      xs = List.append init [last] := by
  induction xs with
  | nil =>
      contradiction
  | cons head tail ih =>
      cases tail with
      | nil =>
          exact ⟨[], head, rfl⟩
      | cons next rest =>
          rcases ih (by simp) with ⟨init, last, htail⟩
          exact ⟨head :: init, last, by simp [htail]⟩

theorem list_exists_singleton_of_length_eq_one
    (xs : List α) (h : xs.length = 1) :
    exists x : α, xs = [x] := by
  cases xs with
  | nil =>
      simp at h
  | cons head tail =>
      cases tail with
      | nil =>
          exact ⟨head, rfl⟩
      | cons next rest =>
          simp at h

theorem list_exists_pair_of_length_eq_two
    (xs : List α) (h : xs.length = 2) :
    exists x : α, exists y : α, xs = [x, y] := by
  cases xs with
  | nil =>
      simp at h
  | cons first rest =>
      cases rest with
      | nil =>
          simp at h
      | cons second tail =>
          cases tail with
          | nil =>
              exact ⟨first, second, rfl⟩
          | cons third more =>
              simp at h

theorem list_exists_triple_of_length_eq_three
    (xs : List α) (h : xs.length = 3) :
    exists x : α, exists y : α, exists z : α,
      xs = [x, y, z] := by
  cases xs with
  | nil =>
      simp at h
  | cons first rest =>
      cases rest with
      | nil =>
          simp at h
      | cons second tail =>
          cases tail with
          | nil =>
              simp at h
          | cons third more =>
              cases more with
              | nil =>
                  exact ⟨first, second, third, rfl⟩
              | cons fourth restTail =>
                  simp at h

theorem list_exists_append_two_of_two_le_length
    (xs : List α) (h : 2 <= xs.length) :
    exists init : List α, exists beforeLast : α, exists last : α,
      xs = List.append init [beforeLast, last] := by
  induction xs with
  | nil =>
      simp at h
  | cons head tail ih =>
      cases tail with
      | nil =>
          simp at h
      | cons next rest =>
          cases rest with
          | nil =>
              exact ⟨[], head, next, rfl⟩
          | cons third restTail =>
              have htail : 2 <= (next :: third :: restTail).length := by
                simp
              rcases ih htail with ⟨init, beforeLast, last, htailSplit⟩
              exact ⟨head :: init, beforeLast, last, by simp [htailSplit]⟩

theorem list_exists_append_three_of_three_le_length
    (xs : List α) (h : 3 <= xs.length) :
    exists init : List α, exists thirdLast : α,
      exists beforeLast : α, exists last : α,
        xs = List.append init [thirdLast, beforeLast, last] := by
  induction xs with
  | nil =>
      simp at h
  | cons head tail ih =>
      cases tail with
      | nil =>
          simp at h
      | cons second rest =>
          cases rest with
          | nil =>
              simp at h
          | cons third more =>
              cases more with
              | nil =>
                  exact ⟨[], head, second, third, rfl⟩
              | cons fourth restTail =>
                  have htail :
                      3 <= (second :: third :: fourth :: restTail).length := by
                    simp
                  rcases ih htail with
                    ⟨init, thirdLast, beforeLast, last, htailSplit⟩
                  exact
                    ⟨head :: init, thirdLast, beforeLast, last,
                      by simp [htailSplit]⟩

theorem nat_exists_eq_add_of_le {m n : Nat} (h : m <= n) :
    exists k : Nat, n = k + m :=
  ⟨n - m, (Nat.sub_add_cancel h).symm⟩

end Computability
end FoC
