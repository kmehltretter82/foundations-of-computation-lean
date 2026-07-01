import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.SourceRestFinishCore.Views
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.OneGapCompactor

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

open DovetailInitialLayoutInitializer
open DovetailInitialLayoutInitializer.StageInputMarkedScanner

def scanQuoteRestToLocalGapSourceDescription : MachineDescription :=
  CommonGround.FiniteTransducers.canonicalSeqDescription
    scanRightToBlankLeftDescription
    CommonGround.FiniteTransducers.rightMoveOnceDescription

theorem scanQuoteRestToLocalGapSourceDescription_subroutineReady :
    scanQuoteRestToLocalGapSourceDescription.SubroutineReady :=
  CommonGround.FiniteTransducers.canonicalSeqDescription_subroutineReady
    scanRightToBlankLeftDescription_subroutineReady
    CommonGround.FiniteTransducers.rightMoveOnceDescription_subroutineReady

theorem
    scanRightToBlankLeftHaltTapeWithRight_move_right_eq_localGapSource
    (baseLeft : List (Option Bool)) (current : Bool)
    (leftRest : Word Bool) (rightPadding : List (Option Bool)) :
    Tape.move Direction.right
        (scanRightToBlankLeftHaltTapeWithRight
          (none :: baseLeft) ((current :: leftRest).reverse)
          rightPadding) =
      CommonGround.FiniteTransducers.rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
        baseLeft current leftRest 0 rightPadding := by
  simp [scanRightToBlankLeftHaltTapeWithRight,
    CommonGround.FiniteTransducers.rightBlankLocalGapCompactorSourceTapeWithBaseAndRight,
    tapeAtCells, CommonGround.FiniteTransducers.tapeAtCells,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem
    scanRightToBlankLeftHaltTapeWithRight_move_left_move_right_reverse_cons
    (leftRev : List (Option Bool)) (current : Bool)
    (leftRest : Word Bool) (right : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (scanRightToBlankLeftHaltTapeWithRight
            leftRev ((current :: leftRest).reverse) right)) =
      scanRightToBlankLeftHaltTapeWithRight
        leftRev ((current :: leftRest).reverse) right := by
  unfold scanRightToBlankLeftHaltTapeWithRight
  cases hrev : leftRest.reverse with
  | nil =>
      simp [hrev, tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons _ _ =>
      simp [hrev, tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight,
        List.map_append, List.append_assoc]

theorem scanQuoteRestToLocalGapSourceDescription_haltsFromTape
    (baseLeft : List (Option Bool)) (current : Bool)
    (leftRest : Word Bool) (rightPadding : List (Option Bool)) :
    scanQuoteRestToLocalGapSourceDescription.HaltsFromTape
      (tapeAtCells (none :: baseLeft)
        (List.append (((current :: leftRest).reverse).map some)
          (none :: rightPadding)))
      (CommonGround.FiniteTransducers.rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
        baseLeft current leftRest 0 rightPadding) := by
  exact
    CommonGround.FiniteTransducers.canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      scanRightToBlankLeftDescription_subroutineReady
      CommonGround.FiniteTransducers.rightMoveOnceDescription_subroutineReady
      (scanRightToBlankLeftDescription_haltsFromTape_withRight
        (none :: baseLeft) ((current :: leftRest).reverse) rightPadding)
      (scanRightToBlankLeftHaltTapeWithRight_move_left_move_right_reverse_cons
        (none :: baseLeft) current leftRest rightPadding)
      (by
        rw [← scanRightToBlankLeftHaltTapeWithRight_move_right_eq_localGapSource]
        exact
          CommonGround.FiniteTransducers.rightMoveOnceDescription_haltsFromTape
            (scanRightToBlankLeftHaltTapeWithRight
              (none :: baseLeft) ((current :: leftRest).reverse)
              rightPadding))

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
