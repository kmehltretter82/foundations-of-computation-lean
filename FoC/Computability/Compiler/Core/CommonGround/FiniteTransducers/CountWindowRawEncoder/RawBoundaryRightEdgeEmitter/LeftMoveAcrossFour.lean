import FoC.Computability.Compiler.Core.TransitionTableChecks
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.TapeLemmas

set_option doc.verso true

/-!
# Raw-boundary fixed four-cell left move

This module provides a small positioning primitive for the RAW right-edge
emitter.  It moves left across exactly four nonblank cells and preserves all
cell contents.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace CountWindowRawSourceEncoder
namespace RawBoundaryRightEdgeEmitter

def leftMoveAcrossFourNonblankCellsDescription : MachineDescription where
  stateCount := 5
  start := 0
  halt := 4
  transitions :=
    [ transition 0 (some false) (some false) Direction.left 1
    , transition 0 (some true) (some true) Direction.left 1
    , transition 1 (some false) (some false) Direction.left 2
    , transition 1 (some true) (some true) Direction.left 2
    , transition 2 (some false) (some false) Direction.left 3
    , transition 2 (some true) (some true) Direction.left 3
    , transition 3 (some false) (some false) Direction.left 4
    , transition 3 (some true) (some true) Direction.left 4 ]

theorem leftMoveAcrossFourNonblankCellsDescription_wellFormed :
    leftMoveAcrossFourNonblankCellsDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := leftMoveAcrossFourNonblankCellsDescription.transitions)
      (stateCount :=
        leftMoveAcrossFourNonblankCellsDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := leftMoveAcrossFourNonblankCellsDescription.transitions)
      (by decide)

theorem leftMoveAcrossFourNonblankCellsDescription_haltTransitionFree :
    leftMoveAcrossFourNonblankCellsDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := leftMoveAcrossFourNonblankCellsDescription.transitions)
    (state := leftMoveAcrossFourNonblankCellsDescription.halt)
    (by decide)

theorem leftMoveAcrossFourNonblankCellsDescription_subroutineReady :
    leftMoveAcrossFourNonblankCellsDescription.SubroutineReady :=
  ⟨leftMoveAcrossFourNonblankCellsDescription_wellFormed,
    leftMoveAcrossFourNonblankCellsDescription_haltTransitionFree⟩

theorem leftMoveAcrossFourNonblankCellsDescription_run
    (b0 b1 b2 b3 headBit : Bool)
    (baseLeft right : List (Option Bool)) :
    leftMoveAcrossFourNonblankCellsDescription.runConfig 4
        { state := leftMoveAcrossFourNonblankCellsDescription.start
          tape :=
            tapeAtCells
              (some b3 :: some b2 :: some b1 :: some b0 :: baseLeft)
              (some headBit :: right) } =
      { state := leftMoveAcrossFourNonblankCellsDescription.halt
        tape :=
          tapeAtCells baseLeft
            (some b0 ::
              some b1 ::
                some b2 ::
                  some b3 ::
                    some headBit :: right) } := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    cases headBit <;> cases baseLeft <;> cases right <;>
      simp [leftMoveAcrossFourNonblankCellsDescription, runConfig,
        stepConfig, lookupTransition, Matches, transition, Tape.read,
        Tape.write, Tape.move, Tape.moveLeft, tapeAtCells]

theorem leftMoveAcrossFourNonblankCellsDescription_haltsFromTape
    (b0 b1 b2 b3 headBit : Bool)
    (baseLeft right : List (Option Bool)) :
    leftMoveAcrossFourNonblankCellsDescription.HaltsFromTape
      (tapeAtCells
        (some b3 :: some b2 :: some b1 :: some b0 :: baseLeft)
        (some headBit :: right))
      (tapeAtCells baseLeft
        (some b0 ::
          some b1 ::
            some b2 ::
              some b3 ::
                some headBit :: right)) := by
  refine ⟨4, ?_⟩
  constructor <;>
    rw [leftMoveAcrossFourNonblankCellsDescription_run]

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
