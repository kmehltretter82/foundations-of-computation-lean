import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Basic

set_option doc.verso true

/-!
# Fixed-width preserving skippers

This module contains small fixed-shape scanners used as adapters between
encoded fields.  They preserve the cells they cross and halt on the first cell
after the fixed-width window.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

def rightMoveAcrossFourBitsDescription : MachineDescription where
  stateCount := 5
  start := 0
  halt := 4
  transitions :=
    [ transition 0 (some false) (some false) Direction.right 1
    , transition 0 (some true) (some true) Direction.right 1
    , transition 1 (some false) (some false) Direction.right 2
    , transition 1 (some true) (some true) Direction.right 2
    , transition 2 (some false) (some false) Direction.right 3
    , transition 2 (some true) (some true) Direction.right 3
    , transition 3 (some false) (some false) Direction.right 4
    , transition 3 (some true) (some true) Direction.right 4 ]

theorem rightMoveAcrossFourBitsDescription_wellFormed :
    rightMoveAcrossFourBitsDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := rightMoveAcrossFourBitsDescription.transitions)
      (stateCount := rightMoveAcrossFourBitsDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := rightMoveAcrossFourBitsDescription.transitions)
      (by decide)

theorem rightMoveAcrossFourBitsDescription_haltTransitionFree :
    rightMoveAcrossFourBitsDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := rightMoveAcrossFourBitsDescription.transitions)
    (state := rightMoveAcrossFourBitsDescription.halt)
    (by decide)

theorem rightMoveAcrossFourBitsDescription_subroutineReady :
    rightMoveAcrossFourBitsDescription.SubroutineReady :=
  ⟨rightMoveAcrossFourBitsDescription_wellFormed,
    rightMoveAcrossFourBitsDescription_haltTransitionFree⟩

theorem rightMoveAcrossFourBitsDescription_run
    (b0 b1 b2 b3 : Bool)
    (left right : List (Option Bool)) :
    rightMoveAcrossFourBitsDescription.runConfig 4
        { state := rightMoveAcrossFourBitsDescription.start
          tape :=
            tapeAtCells left
              (some b0 :: some b1 :: some b2 :: some b3 :: right) } =
      { state := rightMoveAcrossFourBitsDescription.halt
        tape :=
          tapeAtCells
            (some b3 :: some b2 :: some b1 :: some b0 :: left)
            right } := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    cases right <;>
    simp [rightMoveAcrossFourBitsDescription, tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem rightMoveAcrossFourBitsDescription_haltsFromTape
    (b0 b1 b2 b3 : Bool)
    (left right : List (Option Bool)) :
    rightMoveAcrossFourBitsDescription.HaltsFromTape
      (tapeAtCells left
        (some b0 :: some b1 :: some b2 :: some b3 :: right))
      (tapeAtCells
        (some b3 :: some b2 :: some b1 :: some b0 :: left)
        right) := by
  refine ⟨4, ?_⟩
  constructor <;>
    rw [rightMoveAcrossFourBitsDescription_run]

theorem rightMoveAcrossFourBitsDescription_haltsFromTape_bits
    (b0 b1 b2 b3 : Bool)
    (left right : List (Option Bool)) :
    rightMoveAcrossFourBitsDescription.HaltsFromTape
      (tapeAtCells left
        (List.append ([b0, b1, b2, b3].map some) right))
      (tapeAtCells
        (List.append ([b0, b1, b2, b3].reverse.map some) left)
        right) := by
  simpa using
    rightMoveAcrossFourBitsDescription_haltsFromTape
      b0 b1 b2 b3 left right

end FiniteTransducers
end CommonGround

end Computability
end FoC
