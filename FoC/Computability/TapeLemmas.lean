import FoC.Computability.Tape

set_option doc.verso true

/-!
# Tape lemmas

Small dependency-light tape lemmas used by concrete machine proofs.

## Trailing-Blank Normalization

Appending one or many blank cells does not change the normalized finite tape
window obtained by dropping its trailing blanks.
-/

namespace FoC
namespace Computability

theorem dropTrailingNone_append_none
    {symbol : Type u} (xs : List (Option symbol)) :
    Tape.dropTrailingNone (xs ++ [none]) =
      Tape.dropTrailingNone xs := by
  induction xs with
  | nil =>
      rfl
  | cons cell rest ih =>
      rw [List.cons_append, Tape.dropTrailingNone_cons,
        Tape.dropTrailingNone_cons, ih]

theorem dropTrailingNone_replicate_none
    {symbol : Type u} (padding : Nat) :
    Tape.dropTrailingNone
        (List.replicate padding (none : Option symbol)) = [] := by
  induction padding with
  | zero =>
      rfl
  | succ padding ih =>
      simp [List.replicate_succ, Tape.dropTrailingNone, ih]

theorem dropTrailingNone_append_replicate_none
    {symbol : Type u} (xs : List (Option symbol)) (padding : Nat) :
    Tape.dropTrailingNone
        (xs ++ List.replicate padding (none : Option symbol)) =
      Tape.dropTrailingNone xs := by
  induction padding generalizing xs with
  | zero =>
      simp
  | succ padding ih =>
      calc
        Tape.dropTrailingNone
            (xs ++ List.replicate (padding + 1) (none : Option symbol)) =
          Tape.dropTrailingNone
            ((xs ++ [none]) ++
              List.replicate padding (none : Option symbol)) := by
            simp [List.replicate_succ, List.append_assoc]
        _ = Tape.dropTrailingNone (xs ++ [none]) :=
          ih (xs ++ [none])
        _ = Tape.dropTrailingNone xs :=
          dropTrailingNone_append_none xs

end Computability
end FoC
