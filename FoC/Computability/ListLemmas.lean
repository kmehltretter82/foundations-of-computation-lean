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

end Computability
end FoC
