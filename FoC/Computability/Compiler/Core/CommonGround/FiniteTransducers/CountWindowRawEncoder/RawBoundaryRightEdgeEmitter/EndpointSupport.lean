import FoC.Computability.ListLemmas
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.TapeLemmas
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawEncoder.RawBoundaryRightEdgeEmitter.EmitPulledRawBit
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawEncoder.RawBoundaryRightEdgeEmitter.LeftMoveAcrossFour
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawEncoder.RawBoundaryRightEdgeEmitter.PrependCellChunks
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawEncoder.RawBoundaryRightEdgeEmitter.PrependEncodedLayout
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawEncoder.RawBoundaryRightEdgeEmitter.PrependFixedFourBits
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawEncoder.RawBoundaryRightEdgeEmitter.PrependLengthChunks
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawEncoder.RawBoundaryRightEdgeEmitter.PullNearestRawBit
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawEncoder.RawBoundaryRightEdgeEmitter.TailHandoff
import FoC.Computability.Compiler.Core.CommonGround.Identity
import FoC.Computability.Compiler.Core.CommonGround.SameHeadComposition
import FoC.Computability.Compiler.Core.CommonGround.SeqComposition
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.OneGapCompactor
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.RightEdgeRewind
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Quoter.Assembly.Prefix
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Quoter.CellPass

set_option doc.verso true

/-!
# Raw-boundary right-edge endpoint support

This module contains the one-tape endpoint shapes and small composed routes
used by the public raw-boundary right-edge emitter wrapper.
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

def sourceTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells
    (List.append ((List.append skipped count).reverse.map some) [none])
    (none ::
      none ::
      none ::
      List.append
        (List.replicate count.length (none : Option Bool))
        tail)

def encodedLayoutBits (layout : Word Bool) : Word Bool :=
  encodeCodeWordAsInput
    (MachineCodeSymbol.header :: encodeBoolWordAppend layout [])

def rightEdgeTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    ((encodedLayoutBits (List.append skipped count)).reverse.map some)
    (some tailFirst :: tail)

def preRewindTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  Tape.move Direction.left
    (rightEdgeTape skipped count tailFirst tail)

theorem sourceTape_cells
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape.cells (sourceTape skipped count tail) =
      none ::
        List.append ((List.append skipped count).map some)
          (none ::
            none ::
            none ::
            List.append
              (List.replicate count.length (none : Option Bool))
              tail) := by
  simp [sourceTape, Tape.cells, tapeAtCells, List.reverse_append,
    List.map_reverse, List.append_assoc]

-- Defaulted source view for the finite leaf: raw layout bits are followed by
-- the erased count-window gap and then the live tail.
theorem sourceTape_defaultedCells
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    List.map optionBitDefaultFalse
        (Tape.cells (sourceTape skipped count tail)) =
      false ::
        List.append (List.append skipped count)
          (false ::
            false ::
              false ::
                List.append (List.replicate count.length false)
                  (tail.map optionBitDefaultFalse)) := by
  rw [sourceTape_cells]
  simp [List.map_append, List.append_assoc,
    FoC.Computability.EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.optionBitDefaultFalse,
    FoC.Computability.EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.optionBitDefaultFalse_map_some]

def sourceStartTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells [none]
    (List.append ((List.append skipped count).map some)
      (none ::
        none ::
          none ::
            List.append
              (List.replicate count.length (none : Option Bool))
              tail))

theorem sourceStartTape_cells
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape.cells (sourceStartTape skipped count tail) =
      none ::
        List.append ((List.append skipped count).map some)
          (none ::
            none ::
              none ::
                List.append
                  (List.replicate count.length (none : Option Bool))
                  tail) := by
  cases skipped with
  | nil =>
      cases count with
      | nil =>
          simp [sourceStartTape, Tape.cells, tapeAtCells]
      | cons bit rest =>
          cases bit <;>
            simp [sourceStartTape, Tape.cells, tapeAtCells]
  | cons bit rest =>
      cases bit <;>
        simp [sourceStartTape, Tape.cells, tapeAtCells,
          List.append_assoc]

theorem sourceStartTape_defaultedCells
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    List.map optionBitDefaultFalse
        (Tape.cells (sourceStartTape skipped count tail)) =
      false ::
        List.append (List.append skipped count)
          (false ::
            false ::
              false ::
                List.append (List.replicate count.length false)
                  (tail.map optionBitDefaultFalse)) := by
  rw [sourceStartTape_cells]
  simp [List.map_append, List.append_assoc,
    FoC.Computability.EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.optionBitDefaultFalse,
    FoC.Computability.EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.optionBitDefaultFalse_map_some]

theorem rightEdgeRewindDescription_haltsFrom_sourceTape_sourceStart
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    rightEdgeRewindDescription.HaltsFromTape
      (sourceTape skipped count tail)
      (sourceStartTape skipped count tail) := by
  simpa [sourceTape, sourceStartTape, rightEdgeRewindSourceTapeWithBase,
    rightEdgeRewindTargetTapeWithBase, List.append_assoc] using
    rightEdgeRewindDescription_haltsFromTapeWithBase
      ([] : List (Option Bool))
      (List.append skipped count)
      (none ::
        none ::
          List.append
            (List.replicate count.length (none : Option Bool))
            tail)

def tailLeftHandoffTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate (count.length + 2) (none : Option Bool))
      (List.append ((List.append skipped count).reverse.map some) [none]))
    (none :: some tailFirst :: tail)

def tailHeadHandoffTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  Tape.move Direction.right
    (tailLeftHandoffTape skipped count tailFirst tail)

def tailHeadImmediateScratchCellCount (count : Word Bool) : Nat :=
  count.length + 3

def tailHeadRawBaseLeft
    (skipped count : Word Bool) : List (Option Bool) :=
  List.append ((List.append skipped count).reverse.map some) [none]

def tailHeadScratchShortfall
    (skipped count : Word Bool) : Nat :=
  8 * skipped.length + 7 * count.length + 5

theorem rightBlankRunTailFirstLeftHandoffDescription_haltsFrom_sourceTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    rightBlankRunTailFirstLeftHandoffDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (tailLeftHandoffTape skipped count tailFirst tail) := by
  simpa [sourceTape, tailLeftHandoffTape, List.replicate_succ,
    Nat.add_assoc, List.append_assoc] using
    rightBlankRunTailFirstLeftHandoffDescription_haltsFromTape
      (count.length + 2)
      (List.append ((List.append skipped count).reverse.map some) [none])
      tail
      tailFirst

theorem tailHeadImmediateScratchCellCount_lt_encodedLayoutScratchCellCount
    (skipped count : Word Bool) :
    tailHeadImmediateScratchCellCount count <
      encodedLayoutScratchCellCount (List.append skipped count) := by
  simp [tailHeadImmediateScratchCellCount,
    encodedLayoutScratchCellCount_eq, List.length_append]
  lia

theorem tailHeadImmediateScratchCellCount_add_shortfall_eq_encodedLayoutScratchCellCount
    (skipped count : Word Bool) :
    tailHeadImmediateScratchCellCount count +
        tailHeadScratchShortfall skipped count =
      encodedLayoutScratchCellCount (List.append skipped count) := by
  simp [tailHeadImmediateScratchCellCount, tailHeadScratchShortfall,
    encodedLayoutScratchCellCount_eq, List.length_append]
  lia

theorem tailHeadScratchShortfall_pos
    (skipped count : Word Bool) :
    0 < tailHeadScratchShortfall skipped count := by
  simp [tailHeadScratchShortfall]

theorem tailLeftHandoffTape_moveRight
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.right
        (tailLeftHandoffTape skipped count tailFirst tail) =
      tailHeadHandoffTape skipped count tailFirst tail := by
  rfl

theorem tailHeadHandoffTape_eq_tapeAtCells
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    tailHeadHandoffTape skipped count tailFirst tail =
      tapeAtCells
        (none ::
          List.append
            (List.replicate (count.length + 2) (none : Option Bool))
            (List.append ((List.append skipped count).reverse.map some)
              [none]))
        (some tailFirst :: tail) := by
  simpa [tailHeadHandoffTape, tailLeftHandoffTape] using
    rightBlankRunTailFirstLeftHandoffDescription_handoff_right
      (count.length + 2)
      (List.append ((List.append skipped count).reverse.map some) [none])
      tail
      tailFirst

theorem tailHeadHandoffTape_eq_tapeAtCells_scratchBase
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    tailHeadHandoffTape skipped count tailFirst tail =
      tapeAtCells
        (List.append
          (List.replicate (tailHeadImmediateScratchCellCount count)
            (none : Option Bool))
          (tailHeadRawBaseLeft skipped count))
        (some tailFirst :: tail) := by
  rw [tailHeadHandoffTape_eq_tapeAtCells]
  simp [tailHeadImmediateScratchCellCount, tailHeadRawBaseLeft,
    List.replicate_succ, List.append_assoc]

theorem tailHeadHandoffTape_moveLeftRight
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tailHeadHandoffTape skipped count tailFirst tail)) =
      tailHeadHandoffTape skipped count tailFirst tail := by
  rw [tailHeadHandoffTape_eq_tapeAtCells]
  exact
    tapeAtCells_move_right_move_left_cons
      none
      (List.append
        (List.replicate (count.length + 2) (none : Option Bool))
        (List.append ((List.append skipped count).reverse.map some)
          [none]))
      (some tailFirst)
      tail

def tailHeadPulledNearestRawBitTape
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  pullNearestRawBitToTailMarkerTargetTape
    (count.length + 2)
    (List.append (pref.reverse.map some) [none])
    rawBit tailFirst tail

def tailHeadEmittedNearestRawBitCellTape
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  emitPulledRawBitCellChunkTargetTape
    count.length
    (List.append (pref.reverse.map some) [none])
    rawBit tailFirst tail

def tailHeadEmittedNearestRawBitCellLeftEdgeTape
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate count.length (none : Option Bool))
      (List.append (pref.reverse.map some) [none]))
    (List.append
      ((pulledRawBitCellChunkBits rawBit).map some)
      (some tailFirst :: tail))

def tailHeadPulledNextRawBitBeforeEmittedCellTape
    (pref count : Word Bool)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (some nextRawBit ::
      List.append
        (List.replicate count.length (none : Option Bool))
        (List.append (pref.reverse.map some) [none]))
    (List.append
      ((pulledRawBitCellChunkBits emittedRawBit).map some)
      (some tailFirst :: tail))

def tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
    (pref : Word Bool) (scratchTail : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate scratchTail (none : Option Bool))
      (List.append (pref.reverse.map some) [none]))
    (List.append
      ((pulledRawBitCellChunkBits nextRawBit).map some)
      (List.append
        ((pulledRawBitCellChunkBits emittedRawBit).map some)
        (some tailFirst :: tail)))

def tailHeadEmittedThirdRawBitCellBeforeTwoEmittedCellsLeftEdgeTape
    (pref : Word Bool) (scratchTail : Nat)
    (thirdRawBit secondRawBit firstRawBit tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate scratchTail (none : Option Bool))
      (List.append (pref.reverse.map some) [none]))
    (List.append
      ((pulledRawBitCellChunkBits thirdRawBit).map some)
      (List.append
        ((pulledRawBitCellChunkBits secondRawBit).map some)
        (List.append
          ((pulledRawBitCellChunkBits firstRawBit).map some)
          (some tailFirst :: tail))))

def tailHeadEmittedCellSuffixTape
    (pref count cellSuffix : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append
      ((preservingCellPassCellBits cellSuffix).reverse.map some)
      (List.append
        (List.replicate count.length (none : Option Bool))
        (List.append (pref.reverse.map some) [none])))
    (some tailFirst :: tail)

theorem tailHeadEmittedCellSuffixTape_cells
    (pref count cellSuffix : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.cells
        (tailHeadEmittedCellSuffixTape
          pref count cellSuffix tailFirst tail) =
      none ::
        List.append (pref.map some)
          (List.append
            (List.replicate count.length (none : Option Bool))
            (List.append
              ((preservingCellPassCellBits cellSuffix).map some)
              (some tailFirst :: tail))) := by
  simp [tailHeadEmittedCellSuffixTape, Tape.cells, tapeAtCells,
    List.reverse_append, List.map_reverse, List.append_assoc]

theorem tailHeadEmittedCellSuffixTape_defaultedCells
    (pref count cellSuffix : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (tailHeadEmittedCellSuffixTape
            pref count cellSuffix tailFirst tail)) =
      false ::
        List.append pref
          (List.append
            (List.replicate count.length false)
            (List.append
              (preservingCellPassCellBits cellSuffix)
              (tailFirst :: tail.map optionBitDefaultFalse))) := by
  rw [tailHeadEmittedCellSuffixTape_cells]
  simp [List.map_append,
    FoC.Computability.EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.optionBitDefaultFalse,
    FoC.Computability.EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.optionBitDefaultFalse_map_some]

theorem tailHeadEmittedCellSuffixTape_left_length
    (pref count cellSuffix : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (tailHeadEmittedCellSuffixTape
      pref count cellSuffix tailFirst tail).left.length =
      4 * cellSuffix.length + count.length + pref.length + 1 := by
  simp [tailHeadEmittedCellSuffixTape, tapeAtCells,
    List.length_append, preservingCellPassCellBits_length]
  lia

def tailHeadEmittedFullCellSuffixTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  tailHeadEmittedCellSuffixTape
    ([] : Word Bool) count (List.append skipped count) tailFirst tail

def tailHeadPostCellSuffixShortfall
    (skipped count : Word Bool) : Nat :=
  4 * skipped.length + 3 * count.length + 7

theorem tailHeadPostCellSuffixShortfall_pos
    (skipped count : Word Bool) :
    0 < tailHeadPostCellSuffixShortfall skipped count := by
  simp [tailHeadPostCellSuffixShortfall]

theorem tailHeadEmittedFullCellSuffixTape_cells
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.cells
        (tailHeadEmittedFullCellSuffixTape
          skipped count tailFirst tail) =
      none ::
        List.append
          (List.replicate count.length (none : Option Bool))
          (List.append
            ((preservingCellPassCellBits
              (List.append skipped count)).map some)
            (some tailFirst :: tail)) := by
  rw [tailHeadEmittedFullCellSuffixTape,
    tailHeadEmittedCellSuffixTape_cells]
  simp

theorem tailHeadEmittedFullCellSuffixTape_defaultedCells
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (tailHeadEmittedFullCellSuffixTape
            skipped count tailFirst tail)) =
      false ::
        List.append
          (List.replicate count.length false)
          (List.append
            (preservingCellPassCellBits (List.append skipped count))
            (tailFirst :: tail.map optionBitDefaultFalse)) := by
  rw [tailHeadEmittedFullCellSuffixTape,
    tailHeadEmittedCellSuffixTape_defaultedCells]
  simp

theorem tailHeadEmittedFullCellSuffixTape_left_length
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (tailHeadEmittedFullCellSuffixTape
      skipped count tailFirst tail).left.length =
      4 * (List.append skipped count).length + count.length + 1 := by
  rw [tailHeadEmittedFullCellSuffixTape]
  simpa using
    tailHeadEmittedCellSuffixTape_left_length
      ([] : Word Bool) count (List.append skipped count)
      tailFirst tail

theorem tailHeadEmittedFullCellSuffixTape_left_length_eq
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (tailHeadEmittedFullCellSuffixTape
      skipped count tailFirst tail).left.length =
      4 * skipped.length + 5 * count.length + 1 := by
  rw [tailHeadEmittedFullCellSuffixTape_left_length]
  simp [List.length_append]
  lia

theorem tailHeadEmittedFullCellSuffixTape_left_length_add_shortfall
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (tailHeadEmittedFullCellSuffixTape
      skipped count tailFirst tail).left.length +
        tailHeadPostCellSuffixShortfall skipped count =
      encodedLayoutScratchCellCount (List.append skipped count) := by
  rw [tailHeadEmittedFullCellSuffixTape_left_length_eq]
  simp [tailHeadPostCellSuffixShortfall,
    encodedLayoutScratchCellCount_eq, List.length_append]
  lia

theorem tailHeadEmittedNearestRawBitCellTape_eq_cellSuffix_singleton
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    tailHeadEmittedNearestRawBitCellTape pref count rawBit tailFirst tail =
      tailHeadEmittedCellSuffixTape pref count [rawBit] tailFirst tail := by
  simp [tailHeadEmittedNearestRawBitCellTape,
    tailHeadEmittedCellSuffixTape, emitPulledRawBitCellChunkTargetTape,
    pulledRawBitCellChunkBits_eq_preservingCellPassCellBits_singleton]

theorem tailHeadEmittedNearestRawBitCellTape_cells
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.cells
        (tailHeadEmittedNearestRawBitCellTape
          pref count rawBit tailFirst tail) =
      none ::
        List.append (pref.map some)
          (List.append
            (List.replicate count.length (none : Option Bool))
            (List.append
              ((pulledRawBitCellChunkBits rawBit).map some)
              (some tailFirst :: tail))) := by
  simp [tailHeadEmittedNearestRawBitCellTape,
    emitPulledRawBitCellChunkTargetTape, Tape.cells, tapeAtCells,
    List.reverse_append, List.map_reverse, List.append_assoc]

theorem tailHeadEmittedNearestRawBitCellTape_defaultedCells
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (tailHeadEmittedNearestRawBitCellTape
            pref count rawBit tailFirst tail)) =
      false ::
        List.append pref
          (List.append
            (List.replicate count.length false)
            (List.append
              (pulledRawBitCellChunkBits rawBit)
              (tailFirst :: tail.map optionBitDefaultFalse))) := by
  rw [tailHeadEmittedNearestRawBitCellTape_cells]
  simp [List.map_append,
    FoC.Computability.EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.optionBitDefaultFalse,
    FoC.Computability.EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.optionBitDefaultFalse_map_some]

theorem tailHeadEmittedNearestRawBitCellTape_cells_canonical
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.cells
        (tailHeadEmittedNearestRawBitCellTape
          pref count rawBit tailFirst tail) =
      none ::
        List.append (pref.map some)
          (List.append
            (List.replicate count.length (none : Option Bool))
            (List.append
              ((preservingCellPassCellBits [rawBit]).map some)
              (some tailFirst :: tail))) := by
  rw [tailHeadEmittedNearestRawBitCellTape_cells,
    pulledRawBitCellChunkBits_eq_preservingCellPassCellBits_singleton]

theorem tailHeadEmittedNearestRawBitCellTape_defaultedCells_canonical
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (tailHeadEmittedNearestRawBitCellTape
            pref count rawBit tailFirst tail)) =
      false ::
        List.append pref
          (List.append
            (List.replicate count.length false)
            (List.append
              (preservingCellPassCellBits [rawBit])
              (tailFirst :: tail.map optionBitDefaultFalse))) := by
  rw [tailHeadEmittedNearestRawBitCellTape_defaultedCells,
    pulledRawBitCellChunkBits_eq_preservingCellPassCellBits_singleton]

theorem tailHeadEmittedNearestRawBitCellTape_left_length
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    (tailHeadEmittedNearestRawBitCellTape
      pref count rawBit tailFirst tail).left.length =
      4 + count.length + pref.length + 1 := by
  simp [tailHeadEmittedNearestRawBitCellTape,
    emitPulledRawBitCellChunkTargetTape, pulledRawBitCellChunkBits,
    preservingCellPassZeroBits, preservingCellPassOneBits, tapeAtCells,
    List.length_append]
  cases rawBit <;> simp <;> lia

theorem tailHeadEmittedNearestRawBitCellLeftEdgeTape_cells
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.cells
        (tailHeadEmittedNearestRawBitCellLeftEdgeTape
          pref count rawBit tailFirst tail) =
      none ::
        List.append (pref.map some)
          (List.append
            (List.replicate count.length (none : Option Bool))
            (List.append
              ((pulledRawBitCellChunkBits rawBit).map some)
              (some tailFirst :: tail))) := by
  cases rawBit <;>
    simp [tailHeadEmittedNearestRawBitCellLeftEdgeTape,
      Tape.cells, tapeAtCells, pulledRawBitCellChunkBits,
      preservingCellPassZeroBits, preservingCellPassOneBits,
      List.map_reverse, List.append_assoc]

theorem tailHeadEmittedNearestRawBitCellLeftEdgeTape_defaultedCells
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (tailHeadEmittedNearestRawBitCellLeftEdgeTape
            pref count rawBit tailFirst tail)) =
      false ::
        List.append pref
          (List.append
            (List.replicate count.length false)
            (List.append
              (pulledRawBitCellChunkBits rawBit)
              (tailFirst :: tail.map optionBitDefaultFalse))) := by
  rw [tailHeadEmittedNearestRawBitCellLeftEdgeTape_cells]
  simp [List.map_append,
    FoC.Computability.EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.optionBitDefaultFalse,
    FoC.Computability.EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.optionBitDefaultFalse_map_some]

theorem tailHeadEmittedNearestRawBitCellLeftEdgeTape_left_length
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    (tailHeadEmittedNearestRawBitCellLeftEdgeTape
      pref count rawBit tailFirst tail).left.length =
      count.length + pref.length + 1 := by
  cases rawBit <;>
    simp [tailHeadEmittedNearestRawBitCellLeftEdgeTape, tapeAtCells,
      pulledRawBitCellChunkBits, preservingCellPassZeroBits,
      preservingCellPassOneBits, List.length_append] <;> lia

theorem tailHeadPulledNextRawBitBeforeEmittedCellTape_cells
    (pref count : Word Bool)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.cells
        (tailHeadPulledNextRawBitBeforeEmittedCellTape
          pref count nextRawBit emittedRawBit tailFirst tail) =
      none ::
        List.append (pref.map some)
          (List.append
            (List.replicate count.length (none : Option Bool))
            (some nextRawBit ::
              List.append
                ((pulledRawBitCellChunkBits emittedRawBit).map some)
                (some tailFirst :: tail))) := by
  cases emittedRawBit <;>
    simp [tailHeadPulledNextRawBitBeforeEmittedCellTape,
      Tape.cells, tapeAtCells, pulledRawBitCellChunkBits,
      preservingCellPassZeroBits, preservingCellPassOneBits,
      List.map_reverse, List.append_assoc]

theorem tailHeadPulledNextRawBitBeforeEmittedCellTape_defaultedCells
    (pref count : Word Bool)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (tailHeadPulledNextRawBitBeforeEmittedCellTape
            pref count nextRawBit emittedRawBit tailFirst tail)) =
      false ::
        List.append pref
          (List.append
            (List.replicate count.length false)
            (nextRawBit ::
              List.append
                (pulledRawBitCellChunkBits emittedRawBit)
                (tailFirst :: tail.map optionBitDefaultFalse))) := by
  rw [tailHeadPulledNextRawBitBeforeEmittedCellTape_cells]
  simp [List.map_append,
    FoC.Computability.EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.optionBitDefaultFalse,
    FoC.Computability.EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.optionBitDefaultFalse_map_some]

theorem tailHeadPulledNextRawBitBeforeEmittedCellTape_left_length
    (pref count : Word Bool)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    (tailHeadPulledNextRawBitBeforeEmittedCellTape
      pref count nextRawBit emittedRawBit tailFirst tail).left.length =
      count.length + pref.length + 2 := by
  cases emittedRawBit <;>
    simp [tailHeadPulledNextRawBitBeforeEmittedCellTape, tapeAtCells,
      pulledRawBitCellChunkBits, preservingCellPassZeroBits,
      preservingCellPassOneBits, List.length_append] <;> lia

theorem tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_cells
    (pref : Word Bool) (scratchTail : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.cells
        (tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
          pref scratchTail nextRawBit emittedRawBit tailFirst tail) =
      none ::
        List.append (pref.map some)
          (List.append
            (List.replicate scratchTail (none : Option Bool))
            (List.append
              ((pulledRawBitCellChunkBits nextRawBit).map some)
              (List.append
                ((pulledRawBitCellChunkBits emittedRawBit).map some)
                (some tailFirst :: tail)))) := by
  cases nextRawBit <;> cases emittedRawBit <;>
    simp [tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape,
      Tape.cells, tapeAtCells, pulledRawBitCellChunkBits,
      preservingCellPassZeroBits, preservingCellPassOneBits,
      List.map_reverse, List.append_assoc]

theorem tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_defaultedCells
    (pref : Word Bool) (scratchTail : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
            pref scratchTail nextRawBit emittedRawBit tailFirst tail)) =
      false ::
        List.append pref
          (List.append
            (List.replicate scratchTail false)
            (List.append
              (pulledRawBitCellChunkBits nextRawBit)
              (List.append
                (pulledRawBitCellChunkBits emittedRawBit)
                (tailFirst :: tail.map optionBitDefaultFalse)))) := by
  rw [tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_cells]
  simp [List.map_append,
    FoC.Computability.EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.optionBitDefaultFalse,
    FoC.Computability.EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.optionBitDefaultFalse_map_some]

theorem tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_left_length
    (pref : Word Bool) (scratchTail : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    (tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
      pref scratchTail nextRawBit emittedRawBit tailFirst tail).left.length =
      scratchTail + pref.length + 1 := by
  cases nextRawBit <;> cases emittedRawBit <;>
    simp [tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape,
      tapeAtCells, pulledRawBitCellChunkBits,
      preservingCellPassZeroBits, preservingCellPassOneBits,
      List.length_append]
  all_goals lia

theorem tailHeadEmittedThirdRawBitCellBeforeTwoEmittedCellsLeftEdgeTape_cells
    (pref : Word Bool) (scratchTail : Nat)
    (thirdRawBit secondRawBit firstRawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.cells
        (tailHeadEmittedThirdRawBitCellBeforeTwoEmittedCellsLeftEdgeTape
          pref scratchTail thirdRawBit secondRawBit firstRawBit
          tailFirst tail) =
      none ::
        List.append (pref.map some)
          (List.append
            (List.replicate scratchTail (none : Option Bool))
            (List.append
              ((pulledRawBitCellChunkBits thirdRawBit).map some)
              (List.append
                ((pulledRawBitCellChunkBits secondRawBit).map some)
                (List.append
                  ((pulledRawBitCellChunkBits firstRawBit).map some)
                  (some tailFirst :: tail))))) := by
  cases thirdRawBit <;> cases secondRawBit <;> cases firstRawBit <;>
    simp [tailHeadEmittedThirdRawBitCellBeforeTwoEmittedCellsLeftEdgeTape,
      Tape.cells, tapeAtCells, pulledRawBitCellChunkBits,
      preservingCellPassZeroBits, preservingCellPassOneBits,
      List.map_reverse, List.append_assoc]

theorem tailHeadEmittedThirdRawBitCellBeforeTwoEmittedCellsLeftEdgeTape_defaultedCells
    (pref : Word Bool) (scratchTail : Nat)
    (thirdRawBit secondRawBit firstRawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (tailHeadEmittedThirdRawBitCellBeforeTwoEmittedCellsLeftEdgeTape
            pref scratchTail thirdRawBit secondRawBit firstRawBit
            tailFirst tail)) =
      false ::
        List.append pref
          (List.append
            (List.replicate scratchTail false)
            (List.append
              (pulledRawBitCellChunkBits thirdRawBit)
              (List.append
                (pulledRawBitCellChunkBits secondRawBit)
                (List.append
                  (pulledRawBitCellChunkBits firstRawBit)
                  (tailFirst :: tail.map optionBitDefaultFalse))))) := by
  rw [tailHeadEmittedThirdRawBitCellBeforeTwoEmittedCellsLeftEdgeTape_cells]
  simp [List.map_append,
    FoC.Computability.EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.optionBitDefaultFalse,
    FoC.Computability.EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.optionBitDefaultFalse_map_some]

theorem tailHeadEmittedThirdRawBitCellBeforeTwoEmittedCellsLeftEdgeTape_left_length
    (pref : Word Bool) (scratchTail : Nat)
    (thirdRawBit secondRawBit firstRawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    (tailHeadEmittedThirdRawBitCellBeforeTwoEmittedCellsLeftEdgeTape
      pref scratchTail thirdRawBit secondRawBit firstRawBit
      tailFirst tail).left.length =
      scratchTail + pref.length + 1 := by
  cases thirdRawBit <;> cases secondRawBit <;> cases firstRawBit <;>
    simp [tailHeadEmittedThirdRawBitCellBeforeTwoEmittedCellsLeftEdgeTape,
      tapeAtCells, pulledRawBitCellChunkBits,
      preservingCellPassZeroBits, preservingCellPassOneBits,
      List.length_append]
  all_goals lia

theorem tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_moveLeftRight
    (pref : Word Bool) (scratchTail : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
            pref scratchTail nextRawBit emittedRawBit tailFirst tail)) =
      tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
        pref scratchTail nextRawBit emittedRawBit tailFirst tail := by
  rw [tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape]
  simpa [List.append_assoc] using
    tapeAtCells_move_right_move_left_append_singleton
      (List.append (List.replicate scratchTail (none : Option Bool))
        (pref.reverse.map some))
      none
      (List.append ((pulledRawBitCellChunkBits nextRawBit).map some)
        (List.append ((pulledRawBitCellChunkBits emittedRawBit).map some)
          (some tailFirst :: tail)))

theorem leftMoveAcrossFourNonblankCellsDescription_haltsFrom_tailHeadEmittedNearestRawBitCell
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    leftMoveAcrossFourNonblankCellsDescription.HaltsFromTape
      (tailHeadEmittedNearestRawBitCellTape
        pref count rawBit tailFirst tail)
      (tailHeadEmittedNearestRawBitCellLeftEdgeTape
        pref count rawBit tailFirst tail) := by
  cases rawBit <;> cases tailFirst
  · simpa [tailHeadEmittedNearestRawBitCellTape,
      tailHeadEmittedNearestRawBitCellLeftEdgeTape,
      emitPulledRawBitCellChunkTargetTape, pulledRawBitCellChunkBits,
      preservingCellPassZeroBits, List.append_assoc] using
      leftMoveAcrossFourNonblankCellsDescription_haltsFromTape
        false true false true false
        (List.append
          (List.replicate count.length (none : Option Bool))
          (List.append (pref.reverse.map some) [none]))
        tail
  · simpa [tailHeadEmittedNearestRawBitCellTape,
      tailHeadEmittedNearestRawBitCellLeftEdgeTape,
      emitPulledRawBitCellChunkTargetTape, pulledRawBitCellChunkBits,
      preservingCellPassZeroBits, List.append_assoc] using
      leftMoveAcrossFourNonblankCellsDescription_haltsFromTape
        false true false true true
        (List.append
          (List.replicate count.length (none : Option Bool))
          (List.append (pref.reverse.map some) [none]))
        tail
  · simpa [tailHeadEmittedNearestRawBitCellTape,
      tailHeadEmittedNearestRawBitCellLeftEdgeTape,
      emitPulledRawBitCellChunkTargetTape, pulledRawBitCellChunkBits,
      preservingCellPassOneBits, List.append_assoc] using
      leftMoveAcrossFourNonblankCellsDescription_haltsFromTape
        false true true false false
        (List.append
          (List.replicate count.length (none : Option Bool))
          (List.append (pref.reverse.map some) [none]))
        tail
  · simpa [tailHeadEmittedNearestRawBitCellTape,
      tailHeadEmittedNearestRawBitCellLeftEdgeTape,
      emitPulledRawBitCellChunkTargetTape, pulledRawBitCellChunkBits,
      preservingCellPassOneBits, List.append_assoc] using
      leftMoveAcrossFourNonblankCellsDescription_haltsFromTape
        false true true false true
      (List.append
        (List.replicate count.length (none : Option Bool))
          (List.append (pref.reverse.map some) [none]))
        tail

theorem pullNearestRawBitToTailMarkerDescription_haltsFrom_tailHeadEmittedNearestRawBitCellLeftEdge
    (pref count : Word Bool)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    pullNearestRawBitToTailMarkerDescription.HaltsFromTape
      (tailHeadEmittedNearestRawBitCellLeftEdgeTape
        (List.append pref [nextRawBit])
        count emittedRawBit tailFirst tail)
      (tailHeadPulledNextRawBitBeforeEmittedCellTape
        pref count nextRawBit emittedRawBit tailFirst tail) := by
  cases emittedRawBit
  · simpa [tailHeadEmittedNearestRawBitCellLeftEdgeTape,
      tailHeadPulledNextRawBitBeforeEmittedCellTape,
      pullNearestRawBitToHeadMarkerSourceTape,
      pullNearestRawBitToHeadMarkerTargetTape,
      pulledRawBitCellChunkBits, preservingCellPassZeroBits,
      List.reverse_append, List.map_reverse, List.append_assoc] using
      pullNearestRawBitToTailMarkerDescription_haltsFromHeadGap
        count.length
        (List.append (pref.reverse.map some) [none])
        nextRawBit false
        (some true :: some false :: some true :: some tailFirst :: tail)
  · simpa [tailHeadEmittedNearestRawBitCellLeftEdgeTape,
      tailHeadPulledNextRawBitBeforeEmittedCellTape,
      pullNearestRawBitToHeadMarkerSourceTape,
      pullNearestRawBitToHeadMarkerTargetTape,
      pulledRawBitCellChunkBits, preservingCellPassOneBits,
      List.reverse_append, List.map_reverse, List.append_assoc] using
      pullNearestRawBitToTailMarkerDescription_haltsFromHeadGap
        count.length
        (List.append (pref.reverse.map some) [none])
        nextRawBit false
        (some true :: some true :: some false :: some tailFirst :: tail)

theorem tailHeadEmittedNearestRawBitCellTape_moveLeftRight
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tailHeadEmittedNearestRawBitCellTape
            pref count rawBit tailFirst tail)) =
      tailHeadEmittedNearestRawBitCellTape
        pref count rawBit tailFirst tail := by
  cases rawBit
  · rw [tailHeadEmittedNearestRawBitCellTape,
      emitPulledRawBitCellChunkTargetTape]
    simp [pulledRawBitCellChunkBits, preservingCellPassZeroBits]
    exact
      tapeAtCells_move_right_move_left_cons
        (some true)
        (some false ::
          some true ::
            some false ::
              List.append
                (List.replicate count.length (none : Option Bool))
                (List.append ((pref.map some).reverse) [none]))
        (some tailFirst)
        tail
  · rw [tailHeadEmittedNearestRawBitCellTape,
      emitPulledRawBitCellChunkTargetTape]
    simp [pulledRawBitCellChunkBits, preservingCellPassOneBits]
    exact
      tapeAtCells_move_right_move_left_cons
        (some false)
        (some true ::
          some true ::
            some false ::
              List.append
                (List.replicate count.length (none : Option Bool))
                (List.append ((pref.map some).reverse) [none]))
        (some tailFirst)
        tail

theorem tailHeadEmittedNearestRawBitCellLeftEdgeTape_moveLeftRight
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tailHeadEmittedNearestRawBitCellLeftEdgeTape
            pref count rawBit tailFirst tail)) =
      tailHeadEmittedNearestRawBitCellLeftEdgeTape
        pref count rawBit tailFirst tail := by
  rw [tailHeadEmittedNearestRawBitCellLeftEdgeTape]
  simpa [List.append_assoc] using
    tapeAtCells_move_right_move_left_append_singleton
      (List.append (List.replicate count.length (none : Option Bool))
        (pref.reverse.map some))
      none
      (List.append ((pulledRawBitCellChunkBits rawBit).map some)
        (some tailFirst :: tail))

theorem tailHeadRawBaseLeft_eq_splitLast
    (skipped count pref : Word Bool) (rawBit : Bool)
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) :
    tailHeadRawBaseLeft skipped count =
      some rawBit :: List.append (pref.reverse.map some) [none] := by
  rw [tailHeadRawBaseLeft, hlayout]
  simp [List.reverse_append]

theorem pullNearestRawBitToTailMarkerDescription_haltsFrom_tailHeadHandoffTape
    (skipped count pref : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) :
    pullNearestRawBitToTailMarkerDescription.HaltsFromTape
      (tailHeadHandoffTape skipped count tailFirst tail)
      (tailHeadPulledNearestRawBitTape
        pref count rawBit tailFirst tail) := by
  rw [tailHeadHandoffTape_eq_tapeAtCells_scratchBase]
  rw [tailHeadRawBaseLeft_eq_splitLast skipped count pref rawBit hlayout]
  simpa [tailHeadPulledNearestRawBitTape,
    tailHeadImmediateScratchCellCount, Nat.add_assoc] using
    pullNearestRawBitToTailMarkerDescription_haltsFromTape
      (count.length + 2)
      (List.append (pref.reverse.map some) [none])
      rawBit tailFirst tail

theorem pullNearestRawBitToTailMarkerDescription_haltsFrom_tailHeadHandoffTape_of_nonempty
    (skipped count : Word Bool)
    (h : List.append skipped count ≠ [])
    (tailFirst : Bool) (tail : List (Option Bool)) :
    exists pref : Word Bool, exists rawBit : Bool,
      List.append skipped count = List.append pref [rawBit] ∧
        pullNearestRawBitToTailMarkerDescription.HaltsFromTape
          (tailHeadHandoffTape skipped count tailFirst tail)
          (tailHeadPulledNearestRawBitTape
            pref count rawBit tailFirst tail) := by
  rcases
      FoC.Computability.list_exists_append_singleton_of_ne_nil
        (List.append skipped count) h with
    ⟨pref, rawBit, hlayout⟩
  exact
    ⟨pref, rawBit, hlayout,
      pullNearestRawBitToTailMarkerDescription_haltsFrom_tailHeadHandoffTape
        skipped count pref rawBit tailFirst tail hlayout⟩

theorem tailHeadPulledNearestRawBitTape_eq_emitSource
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    tailHeadPulledNearestRawBitTape pref count rawBit tailFirst tail =
      emitPulledRawBitCellChunkSourceTape
        count.length
        (List.append (pref.reverse.map some) [none])
        rawBit tailFirst tail := by
  simp [tailHeadPulledNearestRawBitTape,
    pullNearestRawBitToTailMarkerTargetTape,
    emitPulledRawBitCellChunkSourceTape, Nat.add_assoc]

theorem tailHeadPulledNearestRawBitTape_moveLeftRight
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tailHeadPulledNearestRawBitTape
            pref count rawBit tailFirst tail)) =
      tailHeadPulledNearestRawBitTape
        pref count rawBit tailFirst tail := by
  rw [tailHeadPulledNearestRawBitTape,
    pullNearestRawBitToTailMarkerTargetTape]
  exact
    tapeAtCells_move_right_move_left_cons
      (some rawBit)
      (List.append
        (List.replicate (count.length + 2 + 1)
          (none : Option Bool))
        (List.append (pref.reverse.map some) [none]))
      (some tailFirst)
      tail

theorem emitPulledRawBitCellChunkDescription_haltsFrom_tailHeadPulled
    (pref count : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    emitPulledRawBitCellChunkDescription.HaltsFromTape
      (tailHeadPulledNearestRawBitTape
        pref count rawBit tailFirst tail)
      (tailHeadEmittedNearestRawBitCellTape
        pref count rawBit tailFirst tail) := by
  rw [tailHeadPulledNearestRawBitTape_eq_emitSource]
  simpa [tailHeadEmittedNearestRawBitCellTape] using
    emitPulledRawBitCellChunkDescription_haltsFromTape
      count.length
      (List.append (pref.reverse.map some) [none])
      rawBit tailFirst tail

def pullAndEmitNearestRawBitCellDescription : MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    pullNearestRawBitToTailMarkerDescription
    emitPulledRawBitCellChunkDescription

theorem pullAndEmitNearestRawBitCellDescription_subroutineReady :
    pullAndEmitNearestRawBitCellDescription.SubroutineReady :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    pullNearestRawBitToTailMarkerDescription_subroutineReady
    emitPulledRawBitCellChunkDescription_subroutineReady

theorem pullNearestRawBitToHeadMarkerTargetTape_eq_emitSource
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool) (right : List (Option Bool)) :
    pullNearestRawBitToHeadMarkerTargetTape
        (scratchTail + 3) baseLeft rawBit headBit right =
      emitPulledRawBitCellChunkSourceTape
        scratchTail baseLeft rawBit headBit right := by
  simp [pullNearestRawBitToHeadMarkerTargetTape,
    emitPulledRawBitCellChunkSourceTape]

theorem pullNearestRawBitToHeadMarkerTargetTape_moveLeftRight
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool) (right : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (pullNearestRawBitToHeadMarkerTargetTape
            (scratchTail + 3) baseLeft rawBit headBit right)) =
      pullNearestRawBitToHeadMarkerTargetTape
        (scratchTail + 3) baseLeft rawBit headBit right := by
  rw [pullNearestRawBitToHeadMarkerTargetTape]
  exact
    tapeAtCells_move_right_move_left_cons
      (some rawBit)
      (List.append
        (List.replicate (scratchTail + 3) (none : Option Bool))
        baseLeft)
      (some headBit)
      right

theorem emitPulledRawBitCellChunkDescription_haltsFrom_headGapPulled
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool) (right : List (Option Bool)) :
    emitPulledRawBitCellChunkDescription.HaltsFromTape
      (pullNearestRawBitToHeadMarkerTargetTape
        (scratchTail + 3) baseLeft rawBit headBit right)
      (emitPulledRawBitCellChunkTargetTape
        scratchTail baseLeft rawBit headBit right) := by
  rw [pullNearestRawBitToHeadMarkerTargetTape_eq_emitSource]
  exact
    emitPulledRawBitCellChunkDescription_haltsFromTape
      scratchTail baseLeft rawBit headBit right

theorem pullAndEmitNearestRawBitCellDescription_haltsFrom_headGap
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool) (right : List (Option Bool)) :
    pullAndEmitNearestRawBitCellDescription.HaltsFromTape
      (pullNearestRawBitToHeadMarkerSourceTape
        (scratchTail + 3) baseLeft rawBit headBit right)
      (emitPulledRawBitCellChunkTargetTape
        scratchTail baseLeft rawBit headBit right) :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
    pullNearestRawBitToTailMarkerDescription_subroutineReady
    emitPulledRawBitCellChunkDescription_subroutineReady
    (pullNearestRawBitToTailMarkerDescription_haltsFromHeadGap
      (scratchTail + 3) baseLeft rawBit headBit right)
    (pullNearestRawBitToHeadMarkerTargetTape_moveLeftRight
      scratchTail baseLeft rawBit headBit right)
    (emitPulledRawBitCellChunkDescription_haltsFrom_headGapPulled
      scratchTail baseLeft rawBit headBit right)

def emitPulledRawBitCellChunkLeftEdgeTargetTape
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool) (right : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate scratchTail (none : Option Bool))
      baseLeft)
    (List.append
      ((pulledRawBitCellChunkBits rawBit).map some)
      (some headBit :: right))

theorem emitPulledRawBitCellChunkLeftEdgeTargetTape_cells
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool) (right : List (Option Bool)) :
    Tape.cells
        (emitPulledRawBitCellChunkLeftEdgeTargetTape
          scratchTail baseLeft rawBit headBit right) =
      List.append baseLeft.reverse
        (List.append
          (List.replicate scratchTail (none : Option Bool))
          (List.append ((pulledRawBitCellChunkBits rawBit).map some)
            (some headBit :: right))) := by
  cases rawBit <;>
    simp [emitPulledRawBitCellChunkLeftEdgeTargetTape,
      Tape.cells, tapeAtCells, pulledRawBitCellChunkBits,
      preservingCellPassZeroBits, preservingCellPassOneBits,
      List.append_assoc]

theorem emitPulledRawBitCellChunkLeftEdgeTargetTape_left_length
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool) (right : List (Option Bool)) :
    (emitPulledRawBitCellChunkLeftEdgeTargetTape
      scratchTail baseLeft rawBit headBit right).left.length =
      scratchTail + baseLeft.length := by
  cases rawBit <;>
    simp [emitPulledRawBitCellChunkLeftEdgeTargetTape, tapeAtCells,
      pulledRawBitCellChunkBits, preservingCellPassZeroBits,
      preservingCellPassOneBits, List.length_append]

theorem emitPulledRawBitCellChunkTargetTape_moveLeftRight
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool) (right : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (emitPulledRawBitCellChunkTargetTape
            scratchTail baseLeft rawBit headBit right)) =
      emitPulledRawBitCellChunkTargetTape
        scratchTail baseLeft rawBit headBit right := by
  cases rawBit
  · rw [emitPulledRawBitCellChunkTargetTape]
    simp [pulledRawBitCellChunkBits, preservingCellPassZeroBits]
    exact
      tapeAtCells_move_right_move_left_cons
        (some true)
        (some false ::
          some true ::
            some false ::
              List.append
                (List.replicate scratchTail (none : Option Bool))
                baseLeft)
        (some headBit)
        right
  · rw [emitPulledRawBitCellChunkTargetTape]
    simp [pulledRawBitCellChunkBits, preservingCellPassOneBits]
    exact
      tapeAtCells_move_right_move_left_cons
        (some false)
        (some true ::
          some true ::
            some false ::
              List.append
                (List.replicate scratchTail (none : Option Bool))
                baseLeft)
        (some headBit)
        right

theorem leftMoveAcrossFourNonblankCellsDescription_haltsFrom_emitPulledRawBitCellChunkTarget
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool) (right : List (Option Bool)) :
    leftMoveAcrossFourNonblankCellsDescription.HaltsFromTape
      (emitPulledRawBitCellChunkTargetTape
        scratchTail baseLeft rawBit headBit right)
      (emitPulledRawBitCellChunkLeftEdgeTargetTape
        scratchTail baseLeft rawBit headBit right) := by
  cases rawBit <;> cases headBit
  · simpa [emitPulledRawBitCellChunkTargetTape,
      emitPulledRawBitCellChunkLeftEdgeTargetTape,
      pulledRawBitCellChunkBits, preservingCellPassZeroBits,
      List.append_assoc] using
      leftMoveAcrossFourNonblankCellsDescription_haltsFromTape
        false true false true false
        (List.append
          (List.replicate scratchTail (none : Option Bool))
          baseLeft)
        right
  · simpa [emitPulledRawBitCellChunkTargetTape,
      emitPulledRawBitCellChunkLeftEdgeTargetTape,
      pulledRawBitCellChunkBits, preservingCellPassZeroBits,
      List.append_assoc] using
      leftMoveAcrossFourNonblankCellsDescription_haltsFromTape
        false true false true true
        (List.append
          (List.replicate scratchTail (none : Option Bool))
          baseLeft)
        right
  · simpa [emitPulledRawBitCellChunkTargetTape,
      emitPulledRawBitCellChunkLeftEdgeTargetTape,
      pulledRawBitCellChunkBits, preservingCellPassOneBits,
      List.append_assoc] using
      leftMoveAcrossFourNonblankCellsDescription_haltsFromTape
        false true true false false
        (List.append
          (List.replicate scratchTail (none : Option Bool))
          baseLeft)
        right
  · simpa [emitPulledRawBitCellChunkTargetTape,
      emitPulledRawBitCellChunkLeftEdgeTargetTape,
      pulledRawBitCellChunkBits, preservingCellPassOneBits,
      List.append_assoc] using
      leftMoveAcrossFourNonblankCellsDescription_haltsFromTape
        false true true false true
        (List.append
          (List.replicate scratchTail (none : Option Bool))
          baseLeft)
        right

def emitPulledRawBitCellChunkThenMoveLeftEdgeDescription :
    MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    emitPulledRawBitCellChunkDescription
    leftMoveAcrossFourNonblankCellsDescription

theorem emitPulledRawBitCellChunkThenMoveLeftEdgeDescription_subroutineReady :
    emitPulledRawBitCellChunkThenMoveLeftEdgeDescription.SubroutineReady :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    emitPulledRawBitCellChunkDescription_subroutineReady
    leftMoveAcrossFourNonblankCellsDescription_subroutineReady

theorem emitPulledRawBitCellChunkThenMoveLeftEdgeDescription_haltsFrom_headGapPulled
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool) (right : List (Option Bool)) :
    emitPulledRawBitCellChunkThenMoveLeftEdgeDescription.HaltsFromTape
      (pullNearestRawBitToHeadMarkerTargetTape
        (scratchTail + 3) baseLeft rawBit headBit right)
      (emitPulledRawBitCellChunkLeftEdgeTargetTape
        scratchTail baseLeft rawBit headBit right) :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
    emitPulledRawBitCellChunkDescription_subroutineReady
    leftMoveAcrossFourNonblankCellsDescription_subroutineReady
    (emitPulledRawBitCellChunkDescription_haltsFrom_headGapPulled
      scratchTail baseLeft rawBit headBit right)
    (emitPulledRawBitCellChunkTargetTape_moveLeftRight
      scratchTail baseLeft rawBit headBit right)
    (leftMoveAcrossFourNonblankCellsDescription_haltsFrom_emitPulledRawBitCellChunkTarget
      scratchTail baseLeft rawBit headBit right)

def pullEmitAndMoveRawBitCellLeftEdgeDescription : MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    pullAndEmitNearestRawBitCellDescription
    leftMoveAcrossFourNonblankCellsDescription

theorem pullEmitAndMoveRawBitCellLeftEdgeDescription_subroutineReady :
    pullEmitAndMoveRawBitCellLeftEdgeDescription.SubroutineReady :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    pullAndEmitNearestRawBitCellDescription_subroutineReady
    leftMoveAcrossFourNonblankCellsDescription_subroutineReady

theorem pullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_headGap
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool) (right : List (Option Bool)) :
    pullEmitAndMoveRawBitCellLeftEdgeDescription.HaltsFromTape
      (pullNearestRawBitToHeadMarkerSourceTape
        (scratchTail + 3) baseLeft rawBit headBit right)
      (emitPulledRawBitCellChunkLeftEdgeTargetTape
        scratchTail baseLeft rawBit headBit right) :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
    pullAndEmitNearestRawBitCellDescription_subroutineReady
    leftMoveAcrossFourNonblankCellsDescription_subroutineReady
    (pullAndEmitNearestRawBitCellDescription_haltsFrom_headGap
      scratchTail baseLeft rawBit headBit right)
    (emitPulledRawBitCellChunkTargetTape_moveLeftRight
      scratchTail baseLeft rawBit headBit right)
    (leftMoveAcrossFourNonblankCellsDescription_haltsFrom_emitPulledRawBitCellChunkTarget
      scratchTail baseLeft rawBit headBit right)

theorem pullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_tailHeadEmittedNearestRawBitCellLeftEdge_of_count_length
    (pref count : Word Bool) (scratchTail : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hcount : count.length = scratchTail + 3) :
    pullEmitAndMoveRawBitCellLeftEdgeDescription.HaltsFromTape
      (tailHeadEmittedNearestRawBitCellLeftEdgeTape
        (List.append pref [nextRawBit])
        count emittedRawBit tailFirst tail)
      (tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
        pref scratchTail nextRawBit emittedRawBit tailFirst tail) := by
  cases emittedRawBit
  · simpa [tailHeadEmittedNearestRawBitCellLeftEdgeTape,
      tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape,
      pullNearestRawBitToHeadMarkerSourceTape,
      emitPulledRawBitCellChunkLeftEdgeTargetTape,
      pulledRawBitCellChunkBits, preservingCellPassZeroBits,
      hcount, List.reverse_append, List.map_reverse,
      List.append_assoc] using
      pullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_headGap
        scratchTail
        (List.append (pref.reverse.map some) [none])
        nextRawBit false
        (some true :: some false :: some true :: some tailFirst :: tail)
  · simpa [tailHeadEmittedNearestRawBitCellLeftEdgeTape,
      tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape,
      pullNearestRawBitToHeadMarkerSourceTape,
      emitPulledRawBitCellChunkLeftEdgeTargetTape,
      pulledRawBitCellChunkBits, preservingCellPassOneBits,
      hcount, List.reverse_append, List.map_reverse,
      List.append_assoc] using
      pullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_headGap
        scratchTail
        (List.append (pref.reverse.map some) [none])
        nextRawBit false
        (some true :: some true :: some false :: some tailFirst :: tail)

theorem pullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_tailHeadEmittedNearestRawBitCellLeftEdge_of_three_le_count_length
    (pref count : Word Bool)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hcount : 3 <= count.length) :
    exists scratchTail : Nat,
      count.length = scratchTail + 3 ∧
        pullEmitAndMoveRawBitCellLeftEdgeDescription.HaltsFromTape
          (tailHeadEmittedNearestRawBitCellLeftEdgeTape
            (List.append pref [nextRawBit])
            count emittedRawBit tailFirst tail)
          (tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
            pref scratchTail nextRawBit emittedRawBit tailFirst tail) := by
  rcases nat_exists_eq_add_of_le hcount with ⟨scratchTail, hscratch⟩
  exact
    ⟨scratchTail, hscratch,
      pullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_tailHeadEmittedNearestRawBitCellLeftEdge_of_count_length
        pref count scratchTail nextRawBit emittedRawBit tailFirst tail
        hscratch⟩

theorem pullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_tailHeadEmittedTwoRawBitCellsLeftEdge_of_scratch_length
    (pref : Word Bool) (scratch scratchTail : Nat)
    (thirdRawBit secondRawBit firstRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hscratch : scratch = scratchTail + 3) :
    pullEmitAndMoveRawBitCellLeftEdgeDescription.HaltsFromTape
      (tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
        (List.append pref [thirdRawBit]) scratch secondRawBit firstRawBit
        tailFirst tail)
      (tailHeadEmittedThirdRawBitCellBeforeTwoEmittedCellsLeftEdgeTape
        pref scratchTail thirdRawBit secondRawBit firstRawBit
        tailFirst tail) := by
  cases firstRawBit
  · simpa [tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape,
      tailHeadEmittedNearestRawBitCellLeftEdgeTape,
      tailHeadEmittedThirdRawBitCellBeforeTwoEmittedCellsLeftEdgeTape,
      pulledRawBitCellChunkBits, preservingCellPassZeroBits,
      hscratch, List.reverse_append, List.map_reverse,
      List.append_assoc] using
      pullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_tailHeadEmittedNearestRawBitCellLeftEdge_of_count_length
        pref (List.replicate scratch false) scratchTail
        thirdRawBit secondRawBit false
        (some true :: some false :: some true :: some tailFirst :: tail)
        (by simpa using hscratch)
  · simpa [tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape,
      tailHeadEmittedNearestRawBitCellLeftEdgeTape,
      tailHeadEmittedThirdRawBitCellBeforeTwoEmittedCellsLeftEdgeTape,
      pulledRawBitCellChunkBits, preservingCellPassOneBits,
      hscratch, List.reverse_append, List.map_reverse,
      List.append_assoc] using
      pullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_tailHeadEmittedNearestRawBitCellLeftEdge_of_count_length
        pref (List.replicate scratch false) scratchTail
        thirdRawBit secondRawBit false
        (some true :: some true :: some false :: some tailFirst :: tail)
        (by simpa using hscratch)

theorem pullAndEmitNearestRawBitCellDescription_haltsFrom_tailHeadHandoffTape
    (skipped count pref : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) :
    pullAndEmitNearestRawBitCellDescription.HaltsFromTape
      (tailHeadHandoffTape skipped count tailFirst tail)
      (tailHeadEmittedNearestRawBitCellTape
        pref count rawBit tailFirst tail) :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
    pullNearestRawBitToTailMarkerDescription_subroutineReady
    emitPulledRawBitCellChunkDescription_subroutineReady
    (pullNearestRawBitToTailMarkerDescription_haltsFrom_tailHeadHandoffTape
      skipped count pref rawBit tailFirst tail hlayout)
    (tailHeadPulledNearestRawBitTape_moveLeftRight
      pref count rawBit tailFirst tail)
    (emitPulledRawBitCellChunkDescription_haltsFrom_tailHeadPulled
      pref count rawBit tailFirst tail)

def sourceFirstRawBitCellEmissionDescription : MachineDescription :=
  seqSubroutine rightBlankRunTailFirstLeftHandoffDescription
    pullAndEmitNearestRawBitCellDescription Direction.right

theorem sourceFirstRawBitCellEmissionDescription_subroutineReady :
    sourceFirstRawBitCellEmissionDescription.SubroutineReady := by
  rw [sourceFirstRawBitCellEmissionDescription]
  exact
    seqSubroutine_subroutineReady
      rightBlankRunTailFirstLeftHandoffDescription_subroutineReady
      pullAndEmitNearestRawBitCellDescription_subroutineReady

theorem sourceFirstRawBitCellEmissionDescription_haltsFrom_sourceTape
    (skipped count pref : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) :
    sourceFirstRawBitCellEmissionDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (tailHeadEmittedNearestRawBitCellTape
        pref count rawBit tailFirst tail) := by
  rw [sourceFirstRawBitCellEmissionDescription]
  exact
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      rightBlankRunTailFirstLeftHandoffDescription_subroutineReady
      pullAndEmitNearestRawBitCellDescription_subroutineReady
      (rightBlankRunTailFirstLeftHandoffDescription_haltsFrom_sourceTape
        skipped count tailFirst tail)
      (tailLeftHandoffTape_moveRight skipped count tailFirst tail)
      (pullAndEmitNearestRawBitCellDescription_haltsFrom_tailHeadHandoffTape
        skipped count pref rawBit tailFirst tail hlayout)

def sourceFirstRawBitCellLeftEdgeEmissionDescription : MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    sourceFirstRawBitCellEmissionDescription
    leftMoveAcrossFourNonblankCellsDescription

theorem sourceFirstRawBitCellLeftEdgeEmissionDescription_subroutineReady :
    sourceFirstRawBitCellLeftEdgeEmissionDescription.SubroutineReady :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    sourceFirstRawBitCellEmissionDescription_subroutineReady
    leftMoveAcrossFourNonblankCellsDescription_subroutineReady

theorem sourceFirstRawBitCellLeftEdgeEmissionDescription_haltsFrom_sourceTape
    (skipped count pref : Word Bool) (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) :
    sourceFirstRawBitCellLeftEdgeEmissionDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (tailHeadEmittedNearestRawBitCellLeftEdgeTape
        pref count rawBit tailFirst tail) :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
    sourceFirstRawBitCellEmissionDescription_subroutineReady
    leftMoveAcrossFourNonblankCellsDescription_subroutineReady
    (sourceFirstRawBitCellEmissionDescription_haltsFrom_sourceTape
      skipped count pref rawBit tailFirst tail hlayout)
    (tailHeadEmittedNearestRawBitCellTape_moveLeftRight
      pref count rawBit tailFirst tail)
    (leftMoveAcrossFourNonblankCellsDescription_haltsFrom_tailHeadEmittedNearestRawBitCell
      pref count rawBit tailFirst tail)

def sourceFirstTwoRawBitCellsLeftEdgeEmissionDescription :
    MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    sourceFirstRawBitCellLeftEdgeEmissionDescription
    pullEmitAndMoveRawBitCellLeftEdgeDescription

theorem sourceFirstTwoRawBitCellsLeftEdgeEmissionDescription_subroutineReady :
    sourceFirstTwoRawBitCellsLeftEdgeEmissionDescription.SubroutineReady :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    sourceFirstRawBitCellLeftEdgeEmissionDescription_subroutineReady
    pullEmitAndMoveRawBitCellLeftEdgeDescription_subroutineReady

theorem sourceFirstTwoRawBitCellsLeftEdgeEmissionDescription_haltsFrom_sourceTape_of_count_length
    (skipped count pref : Word Bool) (scratchTail : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count =
        List.append (List.append pref [nextRawBit]) [emittedRawBit])
    (hcount : count.length = scratchTail + 3) :
    sourceFirstTwoRawBitCellsLeftEdgeEmissionDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
        pref scratchTail nextRawBit emittedRawBit tailFirst tail) :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
    sourceFirstRawBitCellLeftEdgeEmissionDescription_subroutineReady
    pullEmitAndMoveRawBitCellLeftEdgeDescription_subroutineReady
    (sourceFirstRawBitCellLeftEdgeEmissionDescription_haltsFrom_sourceTape
      skipped count (List.append pref [nextRawBit]) emittedRawBit
      tailFirst tail hlayout)
    (tailHeadEmittedNearestRawBitCellLeftEdgeTape_moveLeftRight
      (List.append pref [nextRawBit]) count emittedRawBit tailFirst tail)
    (pullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_tailHeadEmittedNearestRawBitCellLeftEdge_of_count_length
      pref count scratchTail nextRawBit emittedRawBit tailFirst tail
      hcount)

def sourceFirstThreeRawBitCellsLeftEdgeEmissionDescription :
    MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    sourceFirstTwoRawBitCellsLeftEdgeEmissionDescription
    pullEmitAndMoveRawBitCellLeftEdgeDescription

theorem sourceFirstThreeRawBitCellsLeftEdgeEmissionDescription_subroutineReady :
    sourceFirstThreeRawBitCellsLeftEdgeEmissionDescription.SubroutineReady :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    sourceFirstTwoRawBitCellsLeftEdgeEmissionDescription_subroutineReady
    pullEmitAndMoveRawBitCellLeftEdgeDescription_subroutineReady

theorem sourceFirstThreeRawBitCellsLeftEdgeEmissionDescription_haltsFrom_sourceTape_of_count_lengths
    (skipped count pref : Word Bool) (scratchOne scratchTail : Nat)
    (thirdRawBit secondRawBit firstRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count =
        List.append
          (List.append (List.append pref [thirdRawBit]) [secondRawBit])
          [firstRawBit])
    (hcount : count.length = scratchOne + 3)
    (hscratch : scratchOne = scratchTail + 3) :
    sourceFirstThreeRawBitCellsLeftEdgeEmissionDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (tailHeadEmittedThirdRawBitCellBeforeTwoEmittedCellsLeftEdgeTape
        pref scratchTail thirdRawBit secondRawBit firstRawBit
        tailFirst tail) :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
    sourceFirstTwoRawBitCellsLeftEdgeEmissionDescription_subroutineReady
    pullEmitAndMoveRawBitCellLeftEdgeDescription_subroutineReady
    (sourceFirstTwoRawBitCellsLeftEdgeEmissionDescription_haltsFrom_sourceTape_of_count_length
      skipped count (List.append pref [thirdRawBit]) scratchOne
      secondRawBit firstRawBit tailFirst tail hlayout hcount)
    (tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_moveLeftRight
      (List.append pref [thirdRawBit]) scratchOne secondRawBit
      firstRawBit tailFirst tail)
    (pullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_tailHeadEmittedTwoRawBitCellsLeftEdge_of_scratch_length
      pref scratchOne scratchTail thirdRawBit secondRawBit firstRawBit
      tailFirst tail hscratch)

theorem sourceFirstTwoRawBitCellsLeftEdgeEmissionDescription_haltsFrom_sourceTape_of_three_le_count_length
    (skipped count pref : Word Bool)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count =
        List.append (List.append pref [nextRawBit]) [emittedRawBit])
    (hcount : 3 <= count.length) :
    exists scratchTail : Nat,
      count.length = scratchTail + 3 ∧
        sourceFirstTwoRawBitCellsLeftEdgeEmissionDescription.HaltsFromTape
          (sourceTape skipped count (some tailFirst :: tail))
          (tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
            pref scratchTail nextRawBit emittedRawBit tailFirst tail) := by
  rcases nat_exists_eq_add_of_le hcount with ⟨scratchTail, hscratch⟩
  exact
    ⟨scratchTail, hscratch,
      sourceFirstTwoRawBitCellsLeftEdgeEmissionDescription_haltsFrom_sourceTape_of_count_length
        skipped count pref scratchTail nextRawBit emittedRawBit tailFirst tail
        hlayout hscratch⟩

theorem sourceFirstTwoRawBitCellsLeftEdgeEmissionDescription_haltsFrom_sourceTape_of_two_le_layout_length_three_le_count_length
    (skipped count : Word Bool)
    (hlayoutLength : 2 <= (List.append skipped count).length)
    (hcount : 3 <= count.length)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    exists pref : Word Bool, exists nextRawBit : Bool,
      exists emittedRawBit : Bool, exists scratchTail : Nat,
        List.append skipped count =
            List.append (List.append pref [nextRawBit]) [emittedRawBit] ∧
          count.length = scratchTail + 3 ∧
            sourceFirstTwoRawBitCellsLeftEdgeEmissionDescription.HaltsFromTape
              (sourceTape skipped count (some tailFirst :: tail))
              (tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
                pref scratchTail nextRawBit emittedRawBit tailFirst tail) := by
  rcases
      FoC.Computability.list_exists_append_two_of_two_le_length
        (List.append skipped count) hlayoutLength with
    ⟨pref, nextRawBit, emittedRawBit, hlayout⟩
  have hlayout' :
      List.append skipped count =
        List.append (List.append pref [nextRawBit]) [emittedRawBit] := by
    simpa [List.append_assoc] using hlayout
  rcases nat_exists_eq_add_of_le hcount with ⟨scratchTail, hscratch⟩
  exact
    ⟨pref, nextRawBit, emittedRawBit, scratchTail,
      hlayout', hscratch,
      sourceFirstTwoRawBitCellsLeftEdgeEmissionDescription_haltsFrom_sourceTape_of_count_length
        skipped count pref scratchTail nextRawBit emittedRawBit tailFirst tail
        hlayout' hscratch⟩

theorem sourceFirstRawBitCellEmissionDescription_haltsFrom_sourceTape_of_nonempty
    (skipped count : Word Bool)
    (h : List.append skipped count ≠ [])
    (tailFirst : Bool) (tail : List (Option Bool)) :
    exists pref : Word Bool, exists rawBit : Bool,
      List.append skipped count = List.append pref [rawBit] ∧
        sourceFirstRawBitCellEmissionDescription.HaltsFromTape
          (sourceTape skipped count (some tailFirst :: tail))
          (tailHeadEmittedNearestRawBitCellTape
            pref count rawBit tailFirst tail) := by
  rcases
      FoC.Computability.list_exists_append_singleton_of_ne_nil
        (List.append skipped count) h with
    ⟨pref, rawBit, hlayout⟩
  exact
    ⟨pref, rawBit, hlayout,
      sourceFirstRawBitCellEmissionDescription_haltsFrom_sourceTape
        skipped count pref rawBit tailFirst tail hlayout⟩

theorem sourceFirstRawBitCellLeftEdgeEmissionDescription_haltsFrom_sourceTape_of_nonempty
    (skipped count : Word Bool)
    (h : List.append skipped count ≠ [])
    (tailFirst : Bool) (tail : List (Option Bool)) :
    exists pref : Word Bool, exists rawBit : Bool,
      List.append skipped count = List.append pref [rawBit] ∧
        sourceFirstRawBitCellLeftEdgeEmissionDescription.HaltsFromTape
          (sourceTape skipped count (some tailFirst :: tail))
          (tailHeadEmittedNearestRawBitCellLeftEdgeTape
            pref count rawBit tailFirst tail) := by
  rcases
      FoC.Computability.list_exists_append_singleton_of_ne_nil
        (List.append skipped count) h with
    ⟨pref, rawBit, hlayout⟩
  exact
    ⟨pref, rawBit, hlayout,
      sourceFirstRawBitCellLeftEdgeEmissionDescription_haltsFrom_sourceTape
        skipped count pref rawBit tailFirst tail hlayout⟩

def entryTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape Bool :=
  Tape.move Direction.left (sourceTape skipped count tail)

def entryDescription : MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ transition 0 none none Direction.left 1 ]

theorem entryDescription_wellFormed :
    entryDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := entryDescription.transitions)
      (stateCount := entryDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := entryDescription.transitions)
      (by decide)

theorem entryDescription_haltTransitionFree :
    entryDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := entryDescription.transitions)
    (state := entryDescription.halt)
    (by decide)

theorem entryDescription_subroutineReady :
    entryDescription.SubroutineReady :=
  ⟨entryDescription_wellFormed,
    entryDescription_haltTransitionFree⟩

theorem entryDescription_run_sourceTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    entryDescription.runConfig 1
        { state := entryDescription.start
          tape := sourceTape skipped count tail } =
      { state := entryDescription.halt
        tape := entryTape skipped count tail } := by
  simp [entryDescription, entryTape, sourceTape, tapeAtCells, runConfig,
    stepConfig, lookupTransition, Matches, transition, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft]

theorem entryDescription_haltsFrom_sourceTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    entryDescription.HaltsFromTape
      (sourceTape skipped count tail)
      (entryTape skipped count tail) := by
  refine ⟨1, ?_⟩
  constructor <;>
    rw [entryDescription_run_sourceTape]

theorem entryTape_moveRight
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape.move Direction.right (entryTape skipped count tail) =
      sourceTape skipped count tail := by
  rw [entryTape, sourceTape]
  exact
    tapeAtCells_move_right_move_left_append_singleton
      ((List.append skipped count).reverse.map some)
      (none : Option Bool)
      (none ::
        none ::
        none ::
        List.append
          (List.replicate count.length (none : Option Bool))
          tail)

theorem rightEdgeTape_cells
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.cells (rightEdgeTape skipped count tailFirst tail) =
      List.append
        ((encodedLayoutBits (List.append skipped count)).map some)
        (some tailFirst :: tail) := by
  rw [rightEdgeTape, encodedLayoutBits]
  change
    Tape.cells
        (tapeAtCells
          ((encodeCodeWordAsInput
            (MachineCodeSymbol.header ::
              encodeBoolWordAppend (List.append skipped count) [])).reverse.map
            some)
          (some tailFirst :: tail)) =
      List.append
        ((encodeCodeWordAsInput
          (MachineCodeSymbol.header ::
            encodeBoolWordAppend (List.append skipped count) [])).map some)
        (some tailFirst :: tail)
  rw [show
      (encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          encodeBoolWordAppend (List.append skipped count) [])).reverse.map
          some =
        List.append
          ((encodeCodeWordAsInput
            (encodeBoolWordAppend (List.append skipped count) [])).reverse.map
            some)
          [some false, some false, some false, some false] by
    simp [encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      List.map_append, List.append_assoc]]
  simp [Tape.cells, tapeAtCells, encodeCodeWordAsInput,
    encodeCodeSymbolAsInput]

-- Defaulted target view just before the final rewind: the encoded layout is
-- immediately followed by the nonblank live-tail head.
theorem rightEdgeTape_defaultedCells
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    List.map optionBitDefaultFalse
        (Tape.cells (rightEdgeTape skipped count tailFirst tail)) =
      List.append
        (encodedLayoutBits (List.append skipped count))
        (tailFirst :: tail.map optionBitDefaultFalse) := by
  rw [rightEdgeTape_cells]
  simp [List.map_append,
    FoC.Computability.EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.optionBitDefaultFalse,
    FoC.Computability.EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.optionBitDefaultFalse_map_some]

def rightEdgeOutputWord
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) : Word Bool :=
  List.append (encodedLayoutBits (List.append skipped count))
    (tailFirst :: tail.filterMap (fun cell => cell))

theorem rightEdgeTape_normalizedOutput
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.normalizedOutput (rightEdgeTape skipped count tailFirst tail) =
      rightEdgeOutputWord skipped count tailFirst tail := by
  rw [Tape.normalizedOutput, rightEdgeTape_cells]
  simp [rightEdgeOutputWord, List.filterMap_append, Function.comp_def]

private theorem encodedLayoutBits_eq_headerQuoteBits
    (layout : Word Bool) :
    encodedLayoutBits layout =
      List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.header)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            layout.length)
          (EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.preservingCellPassCellBits
            layout)) := by
  exact
    (EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.preservingCellPassHeaderQuoteBits_eq_encodeBoolWordAppend
      layout).symm

theorem encodedLayoutBits_eq_header_length_cells
    (layout : Word Bool) :
    encodedLayoutBits layout =
      List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.header)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            layout.length)
          (EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.preservingCellPassCellBits
            layout)) :=
  encodedLayoutBits_eq_headerQuoteBits layout

theorem encodedLayoutChunkBits_eq_encodedLayoutBits
    (layout : Word Bool) :
    encodedLayoutChunkBits layout = encodedLayoutBits layout := by
  rw [encodedLayoutChunkBits, encodedLayoutBits_eq_header_length_cells]

theorem encodedLayoutBits_length
    (layout : Word Bool) :
    (encodedLayoutBits layout).length =
      encodedLayoutScratchCellCount layout := by
  rw [← encodedLayoutChunkBits_eq_encodedLayoutBits]
  simp [encodedLayoutChunkBits, encodedLayoutScratchCellCount_eq,
    encodeCodeSymbolAsInput,
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_length,
    preservingCellPassCellBits_length]
  lia

def rightToLeftEncodedLayoutBits (layout : Word Bool) : Word Bool :=
  List.append
    (EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.preservingCellPassCellBits
      layout).reverse
    (List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        layout.length).reverse
      (encodeCodeSymbolAsInput MachineCodeSymbol.header).reverse)

private theorem rightToLeftEncodedLayoutBits_eq_reverse
    (layout : Word Bool) :
    rightToLeftEncodedLayoutBits layout =
      (encodedLayoutBits layout).reverse := by
  rw [encodedLayoutBits_eq_header_length_cells]
  simp [rightToLeftEncodedLayoutBits, List.reverse_append,
    List.append_assoc]

theorem rightToLeftEncodedLayoutBits_length
    (layout : Word Bool) :
    (rightToLeftEncodedLayoutBits layout).length =
      encodedLayoutScratchCellCount layout := by
  rw [rightToLeftEncodedLayoutBits_eq_reverse]
  simp [encodedLayoutBits_length]

theorem rightEdgeTape_eq_rightToLeftEncodedLayoutBits
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    rightEdgeTape skipped count tailFirst tail =
      tapeAtCells
        ((rightToLeftEncodedLayoutBits
          (List.append skipped count)).map some)
        (some tailFirst :: tail) := by
  rw [rightEdgeTape, rightToLeftEncodedLayoutBits_eq_reverse]

theorem preRewindTape_eq_rightToLeftEncodedLayoutBits
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    preRewindTape skipped count tailFirst tail =
      Tape.move Direction.left
        (tapeAtCells
          ((rightToLeftEncodedLayoutBits
            (List.append skipped count)).map some)
          (some tailFirst :: tail)) := by
  rw [preRewindTape, rightEdgeTape_eq_rightToLeftEncodedLayoutBits]

theorem rightEdgeTape_left_length
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (rightEdgeTape skipped count tailFirst tail).left.length =
      encodedLayoutScratchCellCount (List.append skipped count) := by
  rw [rightEdgeTape_eq_rightToLeftEncodedLayoutBits]
  simp [tapeAtCells, rightToLeftEncodedLayoutBits_length]

theorem rightEdgeTape_left_length_eq_encodedLayoutBits_length
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (rightEdgeTape skipped count tailFirst tail).left.length =
      (encodedLayoutBits (List.append skipped count)).length := by
  rw [rightEdgeTape_left_length, encodedLayoutBits_length]

theorem prependHeaderChunkLeftOfHeadDescription_haltsFrom_layoutSuffix
    (layout : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    prependHeaderChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells
        ((List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            layout.length)
          (preservingCellPassCellBits layout)).reverse.map some)
        (some tailFirst :: tail))
      (tapeAtCells ((encodedLayoutBits layout).reverse.map some)
        (some tailFirst :: tail)) := by
  simpa [encodedLayoutBits_eq_header_length_cells,
    List.append_assoc] using
    prependHeaderChunkLeftOfHeadDescription_haltsFrom_prepend
      (List.append
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          layout.length)
        (preservingCellPassCellBits layout))
      tailFirst tail

theorem prependHeaderChunkLeftOfHeadDescription_haltsFrom_layoutSuffix_rightEdgeTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    prependHeaderChunkLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells
        ((List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            (List.append skipped count).length)
          (preservingCellPassCellBits
            (List.append skipped count))).reverse.map some)
        (some tailFirst :: tail))
      (rightEdgeTape skipped count tailFirst tail) := by
  simpa [rightEdgeTape] using
    prependHeaderChunkLeftOfHeadDescription_haltsFrom_layoutSuffix
      (List.append skipped count) tailFirst tail

theorem prependCellChunksLeftOfHeadDescription_haltsFrom_sourceLayoutCells
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (prependCellChunksLeftOfHeadDescription
      (List.append skipped count)).HaltsFromTape
      (tapeAtCells [] (some tailFirst :: tail))
      (tapeAtCells
        ((preservingCellPassCellBits
          (List.append skipped count)).reverse.map some)
        (some tailFirst :: tail)) :=
  prependCellChunksLeftOfHeadDescription_haltsFrom_emptySuffix
    (List.append skipped count) tailFirst tail

theorem prependLengthChunksLeftOfHeadDescription_haltsFrom_sourceLayoutLength
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (prependLengthChunksLeftOfHeadDescription
      (List.append skipped count).length).HaltsFromTape
      (tapeAtCells
        ((preservingCellPassCellBits
          (List.append skipped count)).reverse.map some)
        (some tailFirst :: tail))
      (tapeAtCells
        ((List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            (List.append skipped count).length)
          (preservingCellPassCellBits
            (List.append skipped count))).reverse.map some)
        (some tailFirst :: tail)) :=
  prependLengthChunksLeftOfHeadDescription_haltsFrom_cellSuffix
    (List.append skipped count) tailFirst tail

theorem prependEncodedLayoutLeftOfHeadDescription_haltsFrom_sourceLayout
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (prependEncodedLayoutLeftOfHeadDescription
      (List.append skipped count)).HaltsFromTape
      (tapeAtCells [] (some tailFirst :: tail))
      (rightEdgeTape skipped count tailFirst tail) := by
  simpa [rightEdgeTape, encodedLayoutChunkBits,
    encodedLayoutBits_eq_header_length_cells, List.append_assoc] using
    prependEncodedLayoutLeftOfHeadDescription_haltsFrom
      (List.append skipped count) tailFirst tail

theorem prependEncodedLayoutLeftOfHeadDescription_haltsFrom_sourceLayoutScratch
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (prependEncodedLayoutLeftOfHeadDescription
      (List.append skipped count)).HaltsFromTape
      (tapeAtCells
        (List.replicate
          (encodedLayoutScratchCellCount (List.append skipped count))
          (none : Option Bool))
        (some tailFirst :: tail))
      (rightEdgeTape skipped count tailFirst tail) := by
  simpa [rightEdgeTape, encodedLayoutChunkBits,
    encodedLayoutBits_eq_header_length_cells, List.append_assoc] using
    prependEncodedLayoutLeftOfHeadDescription_haltsFrom_withScratch
      (List.append skipped count) ([] : List (Option Bool))
      tailFirst tail

def scratchReadyTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.replicate
      (encodedLayoutScratchCellCount (List.append skipped count))
      (none : Option Bool))
    (some tailFirst :: tail)

theorem scratchReadyTape_cells
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.cells (scratchReadyTape skipped count tailFirst tail) =
      List.append
        (List.replicate
          (encodedLayoutScratchCellCount (List.append skipped count))
          (none : Option Bool))
        (some tailFirst :: tail) := by
  simp [scratchReadyTape, Tape.cells, tapeAtCells]

theorem scratchReadyTape_defaultedCells
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    List.map optionBitDefaultFalse
        (Tape.cells (scratchReadyTape skipped count tailFirst tail)) =
      List.append
        (List.replicate
          (encodedLayoutScratchCellCount (List.append skipped count))
          false)
        (tailFirst :: tail.map optionBitDefaultFalse) := by
  rw [scratchReadyTape_cells]
  simp [List.map_append,
    FoC.Computability.EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.optionBitDefaultFalse]

theorem scratchReadyTape_left_length
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (scratchReadyTape skipped count tailFirst tail).left.length =
      encodedLayoutScratchCellCount (List.append skipped count) := by
  simp [scratchReadyTape, tapeAtCells]

theorem scratchReadyTape_left_length_eq_encodedLayoutBits_length
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (scratchReadyTape skipped count tailFirst tail).left.length =
      (encodedLayoutBits (List.append skipped count)).length := by
  rw [scratchReadyTape_left_length, encodedLayoutBits_length]

theorem prependEncodedLayoutLeftOfHeadDescription_haltsFrom_scratchReadyTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (prependEncodedLayoutLeftOfHeadDescription
      (List.append skipped count)).HaltsFromTape
      (scratchReadyTape skipped count tailFirst tail)
      (rightEdgeTape skipped count tailFirst tail) := by
  simpa [scratchReadyTape] using
    prependEncodedLayoutLeftOfHeadDescription_haltsFrom_sourceLayoutScratch
      skipped count tailFirst tail

def prependEmptyLayoutLeftOfHeadDescription : MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    prependLengthDoneChunkLeftOfHeadDescription
    prependHeaderChunkLeftOfHeadDescription

theorem prependEmptyLayoutLeftOfHeadDescription_subroutineReady :
    prependEmptyLayoutLeftOfHeadDescription.SubroutineReady :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    prependLengthDoneChunkLeftOfHeadDescription_subroutineReady
    prependHeaderChunkLeftOfHeadDescription_subroutineReady

theorem prependEmptyLayoutLeftOfHeadDescription_haltsFrom
    (tailFirst : Bool) (tail : List (Option Bool)) :
    prependEmptyLayoutLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells [] (some tailFirst :: tail))
      (rightEdgeTape [] [] tailFirst tail) := by
  have hbridge :
      Tape.move Direction.right
          (Tape.move Direction.left
            (tapeAtCells
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                0).reverse.map some)
              (some tailFirst :: tail))) =
        tapeAtCells
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            0).reverse.map some)
          (some tailFirst :: tail) := by
    simpa [stageNatBits_reverse_zero, encodeCodeSymbolAsInput] using
      prependFixedFourBitsLeftOfHeadDescription_target_moveLeftRight
        false false true true ([] : Word Bool) tailFirst tail
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
      prependLengthDoneChunkLeftOfHeadDescription_subroutineReady
      prependHeaderChunkLeftOfHeadDescription_subroutineReady
      (prependLengthDoneChunkLeftOfHeadDescription_haltsFrom_stageNatBitsZero
        tailFirst tail)
      hbridge
      (by
        simpa [preservingCellPassCellBits] using
          prependHeaderChunkLeftOfHeadDescription_haltsFrom_layoutSuffix_rightEdgeTape
            [] [] tailFirst tail)

theorem prependEmptyLayoutLeftOfHeadDescription_haltsFrom_withScratch
    (tailFirst : Bool) (tail : List (Option Bool)) :
    prependEmptyLayoutLeftOfHeadDescription.HaltsFromTape
      (tapeAtCells (List.replicate 4 (none : Option Bool))
        (some tailFirst :: tail))
      (rightEdgeTape [] [] tailFirst tail) := by
  have hbridge :
      Tape.move Direction.right
          (Tape.move Direction.left
            (tapeAtCells
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                0).reverse.map some)
              (some tailFirst :: tail))) =
        tapeAtCells
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            0).reverse.map some)
          (some tailFirst :: tail) := by
    simpa [stageNatBits_reverse_zero, encodeCodeSymbolAsInput] using
      prependFixedFourBitsLeftOfHeadDescription_target_moveLeftRight
        false false true true ([] : Word Bool) tailFirst tail
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
      prependLengthDoneChunkLeftOfHeadDescription_subroutineReady
      prependHeaderChunkLeftOfHeadDescription_subroutineReady
      (by
        simpa [stageNatBits_reverse_zero, encodeCodeSymbolAsInput] using
          prependLengthDoneChunkLeftOfHeadDescription_haltsFrom_prepend_withScratch
            ([] : Word Bool) ([] : List (Option Bool)) tailFirst tail)
      hbridge
      (by
        simpa [preservingCellPassCellBits] using
          prependHeaderChunkLeftOfHeadDescription_haltsFrom_layoutSuffix_rightEdgeTape
            [] [] tailFirst tail)

theorem prependEmptyLayoutLeftOfHeadDescription_haltsFrom_tailHeadHandoffTape
    (tailFirst : Bool) (tail : List (Option Bool)) :
    prependEmptyLayoutLeftOfHeadDescription.HaltsFromTape
      (tailHeadHandoffTape [] [] tailFirst tail)
      (rightEdgeTape [] [] tailFirst tail) := by
  rw [tailHeadHandoffTape_eq_tapeAtCells_scratchBase]
  simpa [tailHeadImmediateScratchCellCount, tailHeadRawBaseLeft,
    List.replicate_succ, List.append_assoc] using
    prependEmptyLayoutLeftOfHeadDescription_haltsFrom_withScratch
      tailFirst tail

def emptyLayoutTailHandoffRightEdgeDescription : MachineDescription :=
  seqSubroutine rightBlankRunTailFirstLeftHandoffDescription
    prependEmptyLayoutLeftOfHeadDescription Direction.right

theorem emptyLayoutTailHandoffRightEdgeDescription_subroutineReady :
    emptyLayoutTailHandoffRightEdgeDescription.SubroutineReady := by
  rw [emptyLayoutTailHandoffRightEdgeDescription]
  exact
    seqSubroutine_subroutineReady
      rightBlankRunTailFirstLeftHandoffDescription_subroutineReady
      prependEmptyLayoutLeftOfHeadDescription_subroutineReady

theorem emptyLayoutTailHandoffRightEdgeDescription_haltsFrom_sourceTape
    (tailFirst : Bool) (tail : List (Option Bool)) :
    emptyLayoutTailHandoffRightEdgeDescription.HaltsFromTape
      (sourceTape [] [] (some tailFirst :: tail))
      (rightEdgeTape [] [] tailFirst tail) := by
  rw [emptyLayoutTailHandoffRightEdgeDescription]
  exact
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      rightBlankRunTailFirstLeftHandoffDescription_subroutineReady
      prependEmptyLayoutLeftOfHeadDescription_subroutineReady
      (rightBlankRunTailFirstLeftHandoffDescription_haltsFrom_sourceTape
        [] [] tailFirst tail)
      (tailLeftHandoffTape_moveRight [] [] tailFirst tail)
      (prependEmptyLayoutLeftOfHeadDescription_haltsFrom_tailHeadHandoffTape
        tailFirst tail)

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
