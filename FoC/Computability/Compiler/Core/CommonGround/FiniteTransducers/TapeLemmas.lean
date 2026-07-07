import FoC.Computability.TapeLemmas
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Basic

set_option doc.verso true

/-!
# Finite-transducer tape lemmas

Shared {name (full := FoC.Computability.CommonGround.FiniteTransducers.tapeAtCells)}`tapeAtCells`
movement lemmas used by concrete finite-machine proofs.
-/

namespace FoC
namespace Computability
namespace CommonGround
namespace FiniteTransducers

theorem tapeAtCells_replicate_none_left_equiv_empty
    (padding : Nat) (right : List (Option Bool)) :
    Tape.Equiv
      (tapeAtCells
        (List.replicate padding (none : Option Bool)) right)
      (tapeAtCells [] right) := by
  cases right <;>
    simp [Tape.Equiv, Tape.dropTrailingNone, tapeAtCells,
      FoC.Computability.dropTrailingNone_replicate_none]

theorem tapeAtCells_moveRight_cons
    (leftRev : List (Option Bool)) (cell : Option Bool)
    (rest : List (Option Bool)) :
    Tape.moveRight (tapeAtCells leftRev (cell :: rest)) =
      tapeAtCells (cell :: leftRev) rest := by
  cases rest <;> rfl

theorem tapeAtCells_move_right_cons
    (leftRev : List (Option Bool)) (cell : Option Bool)
    (rest : List (Option Bool)) :
    Tape.move Direction.right (tapeAtCells leftRev (cell :: rest)) =
      tapeAtCells (cell :: leftRev) rest := by
  exact tapeAtCells_moveRight_cons leftRev cell rest

theorem tapeAtCells_move_right_move_left_append_cons
    (pref tail right : List (Option Bool)) (cell : Option Bool) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tapeAtCells (List.append pref (cell :: tail)) right)) =
      tapeAtCells (List.append pref (cell :: tail)) right := by
  cases pref <;> cases right <;>
    simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem tapeAtCells_move_right_move_left_append_singleton
    (pref : List (Option Bool)) (cell : Option Bool)
    (right : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tapeAtCells (List.append pref [cell]) right)) =
      tapeAtCells (List.append pref [cell]) right := by
  exact tapeAtCells_move_right_move_left_append_cons pref [] right cell

theorem tapeAtCells_move_right_move_left_cons
    (cell : Option Bool) (left : List (Option Bool))
    (head : Option Bool) (right : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tapeAtCells (cell :: left) (head :: right))) =
      tapeAtCells (cell :: left) (head :: right) := by
  exact
    tapeAtCells_move_right_move_left_append_cons []
      left (head :: right) cell

theorem tapeAtCells_move_left_move_right_cons_cons
    (left : List (Option Bool)) (head next : Option Bool)
    (right : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (tapeAtCells left (head :: next :: right))) =
      tapeAtCells left (head :: next :: right) := by
  simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem tapeAtCells_move_left_cells_append_cons_right_cons
    (pref tail right : List (Option Bool)) (cell head : Option Bool) :
    Tape.cells
        (Tape.move Direction.left
          (tapeAtCells (List.append pref (cell :: tail))
            (head :: right))) =
      List.append tail.reverse
        (cell :: List.append pref.reverse (head :: right)) := by
  cases pref <;>
    simp [tapeAtCells, Tape.cells, Tape.move, Tape.moveLeft,
      List.reverse_append, List.append_assoc]

end FiniteTransducers
end CommonGround
end Computability
end FoC
