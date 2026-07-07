import FoC.Computability.ListLemmas
import FoC.Computability.Compiler.Core.TransitionTableChecks
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.TapeLemmas
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawEncoder.RawBoundaryRightEdgeEmitter.PullNearestRawBit
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Quoter.CellPass

set_option doc.verso true

/-!
# Raw-boundary pulled-bit cell emitter

This module turns the one-bit marker produced by the nearest-bit puller into
the corresponding four-bit encoded cell chunk.  It overwrites the marker and
the next three blank scratch cells immediately to the left of the live tail
head, then returns to that live tail head.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf

namespace CommonGround
namespace FiniteTransducers
namespace CountWindowRawSourceEncoder
namespace RawBoundaryRightEdgeEmitter

def emitPulledRawBitCellChunkDescription : MachineDescription where
  stateCount := 10
  start := 0
  halt := 9
  transitions :=
    [ transition 0 (some false) (some false) Direction.left 1
    , transition 0 (some true) (some true) Direction.left 1
    , transition 1 (some false) (some true) Direction.left 2
    , transition 1 (some true) (some false) Direction.left 5
    , transition 2 none (some false) Direction.left 3
    , transition 3 none (some true) Direction.left 4
    , transition 4 none (some false) Direction.right 6
    , transition 5 none (some true) Direction.left 3
    , transition 6 (some false) (some false) Direction.right 7
    , transition 6 (some true) (some true) Direction.right 7
    , transition 7 (some false) (some false) Direction.right 8
    , transition 7 (some true) (some true) Direction.right 8
    , transition 8 (some false) (some false) Direction.right 9
    , transition 8 (some true) (some true) Direction.right 9 ]

theorem emitPulledRawBitCellChunkDescription_wellFormed :
    emitPulledRawBitCellChunkDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := emitPulledRawBitCellChunkDescription.transitions)
      (stateCount := emitPulledRawBitCellChunkDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := emitPulledRawBitCellChunkDescription.transitions)
      (by decide)

theorem emitPulledRawBitCellChunkDescription_haltTransitionFree :
    emitPulledRawBitCellChunkDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := emitPulledRawBitCellChunkDescription.transitions)
    (state := emitPulledRawBitCellChunkDescription.halt)
    (by decide)

theorem emitPulledRawBitCellChunkDescription_subroutineReady :
    emitPulledRawBitCellChunkDescription.SubroutineReady :=
  ⟨emitPulledRawBitCellChunkDescription_wellFormed,
    emitPulledRawBitCellChunkDescription_haltTransitionFree⟩

def pulledRawBitCellChunkBits (bit : Bool) : Word Bool :=
  if bit then preservingCellPassOneBits else preservingCellPassZeroBits

theorem pulledRawBitCellChunkBits_eq_preservingCellPassCellBits_singleton
    (bit : Bool) :
    pulledRawBitCellChunkBits bit =
      preservingCellPassCellBits [bit] := by
  cases bit <;>
    simp [pulledRawBitCellChunkBits, preservingCellPassCellBits,
      preservingCellPassZeroBits, preservingCellPassOneBits]

theorem pulledRawBitCellChunkBits_length
    (bit : Bool) :
    (pulledRawBitCellChunkBits bit).length = 4 := by
  cases bit <;>
    simp [pulledRawBitCellChunkBits, preservingCellPassZeroBits,
      preservingCellPassOneBits]

def emitPulledRawBitCellChunkSourceTape
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (rawBit tailFirst : Bool) (tail : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells
    (some rawBit ::
      List.append
        (List.replicate (scratchTail + 3) (none : Option Bool))
        baseLeft)
    (some tailFirst :: tail)

def emitPulledRawBitCellChunkTargetTape
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (rawBit tailFirst : Bool) (tail : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells
    (List.append
      ((pulledRawBitCellChunkBits rawBit).reverse.map some)
      (List.append
        (List.replicate scratchTail (none : Option Bool))
        baseLeft))
    (some tailFirst :: tail)

theorem emitPulledRawBitCellChunkSourceTape_cells
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (rawBit tailFirst : Bool) (tail : List (Option Bool)) :
    Tape.cells
        (emitPulledRawBitCellChunkSourceTape
          scratchTail baseLeft rawBit tailFirst tail) =
      List.append baseLeft.reverse
        (List.append
          (List.replicate (scratchTail + 3) (none : Option Bool))
          (some rawBit :: some tailFirst :: tail)) := by
  simp [emitPulledRawBitCellChunkSourceTape, Tape.cells, tapeAtCells,
    List.reverse_append, List.append_assoc]

theorem emitPulledRawBitCellChunkTargetTape_cells
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (rawBit tailFirst : Bool) (tail : List (Option Bool)) :
    Tape.cells
        (emitPulledRawBitCellChunkTargetTape
          scratchTail baseLeft rawBit tailFirst tail) =
      List.append baseLeft.reverse
        (List.append
          (List.replicate scratchTail (none : Option Bool))
          (List.append ((pulledRawBitCellChunkBits rawBit).map some)
            (some tailFirst :: tail))) := by
  simp [emitPulledRawBitCellChunkTargetTape, Tape.cells, tapeAtCells,
    List.reverse_append, List.map_reverse, List.append_assoc]

theorem emitPulledRawBitCellChunkSourceTape_left_length
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (rawBit tailFirst : Bool) (tail : List (Option Bool)) :
    (emitPulledRawBitCellChunkSourceTape
      scratchTail baseLeft rawBit tailFirst tail).left.length =
      scratchTail + baseLeft.length + 4 := by
  simp [emitPulledRawBitCellChunkSourceTape, tapeAtCells,
    List.length_append]
  lia

theorem emitPulledRawBitCellChunkTargetTape_left_length
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (rawBit tailFirst : Bool) (tail : List (Option Bool)) :
    (emitPulledRawBitCellChunkTargetTape
      scratchTail baseLeft rawBit tailFirst tail).left.length =
      scratchTail + baseLeft.length + 4 := by
  simp [emitPulledRawBitCellChunkTargetTape, tapeAtCells,
    List.length_append, pulledRawBitCellChunkBits_length]
  lia

private theorem replicate_add_three_append
    (scratchTail : Nat) (baseLeft : List (Option Bool)) :
    List.append
        (List.replicate (scratchTail + 3) (none : Option Bool))
        baseLeft =
      none :: none :: none ::
        List.append
          (List.replicate scratchTail (none : Option Bool))
          baseLeft := by
  rw [show scratchTail + 3 = 3 + scratchTail by lia]
  simpa [List.replicate_succ] using
    FoC.Computability.list_replicate_add_append
      (none : Option Bool) 3 scratchTail baseLeft

theorem emitPulledRawBitCellChunkDescription_run_false
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (tailFirst : Bool) (tail : List (Option Bool)) :
    emitPulledRawBitCellChunkDescription.runConfig 8
        { state := emitPulledRawBitCellChunkDescription.start
          tape :=
            emitPulledRawBitCellChunkSourceTape
              scratchTail baseLeft false tailFirst tail } =
      { state := emitPulledRawBitCellChunkDescription.halt
        tape :=
          emitPulledRawBitCellChunkTargetTape
            scratchTail baseLeft false tailFirst tail } := by
  rw [emitPulledRawBitCellChunkSourceTape]
  rw [replicate_add_three_append]
  cases tailFirst <;> cases tail <;>
    simp [emitPulledRawBitCellChunkDescription,
      emitPulledRawBitCellChunkTargetTape, pulledRawBitCellChunkBits,
      preservingCellPassZeroBits, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem emitPulledRawBitCellChunkDescription_run_true
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (tailFirst : Bool) (tail : List (Option Bool)) :
    emitPulledRawBitCellChunkDescription.runConfig 8
        { state := emitPulledRawBitCellChunkDescription.start
          tape :=
            emitPulledRawBitCellChunkSourceTape
              scratchTail baseLeft true tailFirst tail } =
      { state := emitPulledRawBitCellChunkDescription.halt
        tape :=
          emitPulledRawBitCellChunkTargetTape
            scratchTail baseLeft true tailFirst tail } := by
  rw [emitPulledRawBitCellChunkSourceTape]
  rw [replicate_add_three_append]
  cases tailFirst <;> cases tail <;>
    simp [emitPulledRawBitCellChunkDescription,
      emitPulledRawBitCellChunkTargetTape, pulledRawBitCellChunkBits,
      preservingCellPassOneBits, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem emitPulledRawBitCellChunkDescription_haltsFromTape
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (rawBit tailFirst : Bool) (tail : List (Option Bool)) :
    emitPulledRawBitCellChunkDescription.HaltsFromTape
      (emitPulledRawBitCellChunkSourceTape
        scratchTail baseLeft rawBit tailFirst tail)
      (emitPulledRawBitCellChunkTargetTape
        scratchTail baseLeft rawBit tailFirst tail) := by
  cases rawBit
  · refine ⟨8, ?_⟩
    constructor <;>
      rw [emitPulledRawBitCellChunkDescription_run_false]
  · refine ⟨8, ?_⟩
    constructor <;>
      rw [emitPulledRawBitCellChunkDescription_run_true]

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
