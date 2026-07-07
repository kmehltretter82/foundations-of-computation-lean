import FoC.Computability.Compiler.Core.CommonGround.Identity
import FoC.Computability.Compiler.Core.CommonGround.SeqComposition
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.TapeLemmas

set_option doc.verso true

/-!
# Fixed blank moves

This module provides small reusable fixed-distance movers.  The machines are
defined by recursively sequencing exact identity with the mandatory
{lit}`seqSubroutine` handoff move; the exact-run lemmas below specialize them
to blank runs.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

private theorem replicate_append_cons_eq_replicate_succ_append
    (n : Nat) (cell : Option Bool) (tail : List (Option Bool)) :
    List.append (List.replicate n cell) (cell :: tail) =
      List.append (List.replicate (Nat.succ n) cell) tail := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simpa [List.replicate_succ, List.append_assoc] using
        congrArg (fun cells => cell :: cells) ih

def leftMoveAcrossBlanksDescription : Nat -> MachineDescription
  | 0 => ExactIdentityDescription
  | n + 1 =>
      seqSubroutine ExactIdentityDescription
        (leftMoveAcrossBlanksDescription n) Direction.left

def rightMoveAcrossBlanksDescription : Nat -> MachineDescription
  | 0 => ExactIdentityDescription
  | n + 1 =>
      seqSubroutine ExactIdentityDescription
        (rightMoveAcrossBlanksDescription n) Direction.right

theorem leftMoveAcrossBlanksDescription_subroutineReady
    (n : Nat) :
    (leftMoveAcrossBlanksDescription n).SubroutineReady := by
  induction n with
  | zero =>
      exact CommonGround.Identity.exactIdentityDescription_subroutineReady
  | succ n ih =>
      rw [leftMoveAcrossBlanksDescription]
      exact
        seqSubroutine_subroutineReady
          CommonGround.Identity.exactIdentityDescription_subroutineReady ih

theorem rightMoveAcrossBlanksDescription_subroutineReady
    (n : Nat) :
    (rightMoveAcrossBlanksDescription n).SubroutineReady := by
  induction n with
  | zero =>
      exact CommonGround.Identity.exactIdentityDescription_subroutineReady
  | succ n ih =>
      rw [rightMoveAcrossBlanksDescription]
      exact
        seqSubroutine_subroutineReady
          CommonGround.Identity.exactIdentityDescription_subroutineReady ih

theorem leftMoveAcrossBlanksDescription_haltsFromTape
    (n : Nat) (left : List (Option Bool)) (head : Option Bool)
    (right : List (Option Bool)) :
    (leftMoveAcrossBlanksDescription n).HaltsFromTape
      (tapeAtCells
        (List.append (List.replicate n (none : Option Bool)) left)
        (head :: right))
      (tapeAtCells left
        (List.append (List.replicate n (none : Option Bool))
          (head :: right))) := by
  induction n generalizing head right with
  | zero =>
      simpa [leftMoveAcrossBlanksDescription] using
        CommonGround.Identity.exactIdentityDescription_haltsFromTape
          (tapeAtCells left (head :: right))
  | succ n ih =>
      rw [leftMoveAcrossBlanksDescription]
      exact
        CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
          CommonGround.Identity.exactIdentityDescription_subroutineReady
          (leftMoveAcrossBlanksDescription_subroutineReady n)
          (CommonGround.Identity.exactIdentityDescription_haltsFromTape
            (tapeAtCells
              (List.append
                (List.replicate (Nat.succ n) (none : Option Bool)) left)
              (head :: right)))
          (by
            show
              Tape.move Direction.left
                  (tapeAtCells
                    (List.append
                      (List.replicate (Nat.succ n)
                        (none : Option Bool)) left)
                    (head :: right)) =
                tapeAtCells
                  (List.append
                    (List.replicate n (none : Option Bool)) left)
                  (none :: head :: right)
            simp [List.replicate_succ, tapeAtCells, Tape.move,
              Tape.moveLeft])
          (by
            have htail :
                List.append (List.replicate n (none : Option Bool))
                    (none :: head :: right) =
                  List.append
                    (List.replicate (n + 1) (none : Option Bool))
                    (head :: right) := by
              simpa [Nat.succ_eq_add_one] using
                replicate_append_cons_eq_replicate_succ_append
                  n (none : Option Bool) (head :: right)
            rw [← htail]
            exact ih none (head :: right))

theorem rightMoveAcrossBlanksDescription_haltsFromTape
    (n : Nat) (left : List (Option Bool)) (head : Option Bool)
    (right : List (Option Bool)) :
    (rightMoveAcrossBlanksDescription n).HaltsFromTape
      (tapeAtCells left
        (List.append (List.replicate n (none : Option Bool))
          (head :: right)))
      (tapeAtCells
        (List.append (List.replicate n (none : Option Bool)) left)
        (head :: right)) := by
  induction n generalizing left with
  | zero =>
      simpa [rightMoveAcrossBlanksDescription] using
        CommonGround.Identity.exactIdentityDescription_haltsFromTape
          (tapeAtCells left (head :: right))
  | succ n ih =>
      rw [rightMoveAcrossBlanksDescription]
      exact
        CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
          CommonGround.Identity.exactIdentityDescription_subroutineReady
          (rightMoveAcrossBlanksDescription_subroutineReady n)
          (CommonGround.Identity.exactIdentityDescription_haltsFromTape
            (tapeAtCells left
              (List.append
                (List.replicate (Nat.succ n) (none : Option Bool))
                (head :: right))))
          (by
            show
              Tape.move Direction.right
                  (tapeAtCells left
                    (List.append
                      (List.replicate (Nat.succ n)
                        (none : Option Bool)) (head :: right))) =
                tapeAtCells (none :: left)
                  (List.append
                    (List.replicate n (none : Option Bool))
                    (head :: right))
            simpa [List.replicate_succ] using
              tapeAtCells_move_right_cons left (none : Option Bool)
                (List.append
                  (List.replicate n (none : Option Bool))
                  (head :: right)))
          (by
            have hleft :
                List.append (List.replicate n (none : Option Bool))
                    (none :: left) =
                  List.append
                    (List.replicate (n + 1) (none : Option Bool))
                    left := by
              simpa [Nat.succ_eq_add_one] using
                replicate_append_cons_eq_replicate_succ_append
                  n (none : Option Bool) left
            rw [← hleft]
            exact ih (none :: left))

end FiniteTransducers
end CommonGround

end Computability
end FoC
