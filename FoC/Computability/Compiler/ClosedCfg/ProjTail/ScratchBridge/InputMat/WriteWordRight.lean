import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.AcceptInserterShapes

/-!
# Exact rightward word overwrite

The semantic word writer used by the accept-tail insertion proof.  When the
replacement word is strictly longer than the old visible word, writing and
moving right ends on the first blank with the replacement word reversed in the
left context.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup
namespace InputMat

def writeWordRight : Word Bool → Tape Bool → Tape Bool
  | [], T => T
  | bit :: rest, T =>
      writeWordRight rest
        (Tape.move Direction.right (Tape.write (some bit) T))

theorem writeWordRight_tapeAtCells_of_length_lt
    (new old : Word Bool) (left : List (Option Bool))
    (h : old.length < new.length) :
    writeWordRight new
        (tapeAtCells left (List.append (old.map some) [none])) =
      tapeAtCells
        (List.append (new.reverse.map some) left) [none] := by
  induction new generalizing old left with
  | nil =>
      simp at h
  | cons bit rest ih =>
      cases old with
      | nil =>
          cases rest with
          | nil =>
              rfl
          | cons next restTail =>
              have hmove :
                  Tape.move Direction.right
                      (Tape.write (some bit)
                        (tapeAtCells left
                          (List.append (([] : Word Bool).map some) [none]))) =
                    tapeAtCells (some bit :: left)
                      (List.append (([] : Word Bool).map some) [none]) := by
                rfl
              have hrest : ([] : Word Bool).length <
                  (next :: restTail).length := by
                simp
              rw [writeWordRight, hmove,
                ih [] (some bit :: left) hrest]
              simp [List.reverse_cons, List.map_append, List.append_assoc]
              done
      | cons oldBit oldRest =>
          have hrest : oldRest.length < rest.length := by
            simpa using h
          have hmove :
              Tape.move Direction.right
                  (Tape.write (some bit)
                    (tapeAtCells left
                      (List.append ((oldBit :: oldRest).map some) [none]))) =
                tapeAtCells (some bit :: left)
                  (List.append (oldRest.map some) [none]) := by
            cases oldRest <;> rfl
          rw [writeWordRight, hmove,
            ih oldRest (some bit :: left) hrest]
          simp [List.reverse_cons, List.map_append, List.append_assoc]
          done


end InputMat
end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
