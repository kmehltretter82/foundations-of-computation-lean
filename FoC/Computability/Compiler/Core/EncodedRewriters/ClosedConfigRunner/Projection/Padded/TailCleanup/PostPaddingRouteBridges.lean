import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.PostPaddingFramework
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.PostPaddingFieldEraser
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.PostPaddingPrefixScanner

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncodedRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

open CanonicalLayouts.DovetailLayoutScanner

def rightMoveAcrossFiveBlanksDescription : MachineDescription :=
  SeqViaCanonical rightMoveAcrossFourBlanksDescription
    rightMoveOnceDescription

theorem rightMoveAcrossFiveBlanksDescription_subroutineReady :
    rightMoveAcrossFiveBlanksDescription.SubroutineReady :=
  SeqViaCanonical_subroutineReady
    rightMoveAcrossFourBlanksDescription_subroutineReady
    rightMoveOnceDescription_subroutineReady

theorem rightMoveAcrossFourBlanksTarget_move_left_move_right
    (leftCells : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (tapeAtCells
            (List.append (List.replicate 4 (none : Option Bool))
              leftCells.reverse)
            [none, none])) =
      tapeAtCells
        (List.append (List.replicate 4 (none : Option Bool))
          leftCells.reverse)
        [none, none] := by
    simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem rightMoveAcrossFourBlanksTarget_move_left_move_right_withRight
    (leftCells rightPadding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (tapeAtCells
            (List.append (List.replicate 4 (none : Option Bool))
              leftCells.reverse)
            (none :: none :: rightPadding))) =
      tapeAtCells
        (List.append (List.replicate 4 (none : Option Bool))
          leftCells.reverse)
        (none :: none :: rightPadding) := by
  simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem rightMoveOnceDescription_haltsFrom_fourBlankTarget
    (leftCells : List (Option Bool)) :
    rightMoveOnceDescription.HaltsFromTape
      (tapeAtCells
        (List.append (List.replicate 4 (none : Option Bool))
          leftCells.reverse)
        [none, none])
      (rightEndCompactionSourceTape
        (List.append leftCells
          (List.replicate 5 (none : Option Bool)))) := by
  have hmove :=
    rightMoveOnceDescription_haltsFromTape
      (tapeAtCells
        (List.append (List.replicate 4 (none : Option Bool))
          leftCells.reverse)
        [none, none])
  simpa [rightEndCompactionSourceTape, tapeAtCells, Tape.move,
    Tape.moveRight, List.reverse_append, List.replicate_succ,
    List.append_assoc] using hmove

theorem rightMoveOnceDescription_haltsFrom_fourBlankTargetWithRight
    (leftCells rightPadding : List (Option Bool)) :
    rightMoveOnceDescription.HaltsFromTape
      (tapeAtCells
        (List.append (List.replicate 4 (none : Option Bool))
          leftCells.reverse)
        (none :: none :: rightPadding))
      (rightEndCompactionSourceTapeWithRightPadding
        (List.append leftCells
          (List.replicate 5 (none : Option Bool)))
        rightPadding) := by
  have hmove :=
    rightMoveOnceDescription_haltsFromTape
      (tapeAtCells
        (List.append (List.replicate 4 (none : Option Bool))
          leftCells.reverse)
        (none :: none :: rightPadding))
  simpa [rightEndCompactionSourceTapeWithRightPadding, tapeAtCells,
    Tape.move, Tape.moveRight, List.reverse_append, List.replicate_succ,
    List.append_assoc] using hmove

theorem rightMoveAcrossFiveBlanksDescription_haltsFrom_rightPadding
    (leftCells : List (Option Bool)) :
    rightMoveAcrossFiveBlanksDescription.HaltsFromTape
      (rightEndCompactionSourceTapeWithRightPadding
        leftCells (List.replicate 5 (none : Option Bool)))
      (rightEndCompactionSourceTape
        (List.append leftCells
          (List.replicate 5 (none : Option Bool)))) := by
  exact
    SeqViaCanonical_haltsFromTape_of_haltsFromTape
      rightMoveAcrossFourBlanksDescription_subroutineReady
      rightMoveOnceDescription_subroutineReady
      (by
        simpa [rightEndCompactionSourceTapeWithRightPadding,
          List.replicate_succ] using
          rightMoveAcrossFourBlanksDescription_haltsFromTape
            leftCells.reverse [none, none])
      (rightMoveAcrossFourBlanksTarget_move_left_move_right leftCells)
      (rightMoveOnceDescription_haltsFrom_fourBlankTarget leftCells)

theorem rightMoveAcrossFiveBlanksDescription_haltsFrom_rightPaddingWithTail
    (leftCells rightPadding : List (Option Bool)) :
    rightMoveAcrossFiveBlanksDescription.HaltsFromTape
      (rightEndCompactionSourceTapeWithRightPadding
        leftCells
        (List.append (List.replicate 5 (none : Option Bool))
          rightPadding))
      (rightEndCompactionSourceTapeWithRightPadding
        (List.append leftCells
          (List.replicate 5 (none : Option Bool)))
        rightPadding) := by
  exact
    SeqViaCanonical_haltsFromTape_of_haltsFromTape
      rightMoveAcrossFourBlanksDescription_subroutineReady
      rightMoveOnceDescription_subroutineReady
      (by
        simpa [rightEndCompactionSourceTapeWithRightPadding,
          List.replicate_succ, List.append_assoc] using
          rightMoveAcrossFourBlanksDescription_haltsFromTape
            leftCells.reverse (none :: none :: rightPadding))
      (rightMoveAcrossFourBlanksTarget_move_left_move_right_withRight
        leftCells rightPadding)
      (rightMoveOnceDescription_haltsFrom_fourBlankTargetWithRight
        leftCells rightPadding)

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
