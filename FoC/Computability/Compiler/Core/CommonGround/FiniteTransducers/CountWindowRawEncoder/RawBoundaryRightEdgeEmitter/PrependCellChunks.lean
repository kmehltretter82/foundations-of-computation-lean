import FoC.Computability.ListLemmas
import FoC.Computability.Compiler.Core.CommonGround.SameHeadComposition
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawEncoder.RawBoundaryRightEdgeEmitter.PrependFixedFourBits

set_option doc.verso true

/-!
# Raw-boundary right-edge cell-chunk prepender

This module composes the fixed four-bit cell chunk primitive into a finite
description family that prepends the encoded cell chunks for a concrete Boolean
layout.  The family is proof support for the RAW right-edge emitter: it gives
exact tape endpoints for the entire cell-suffix phase.
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

def prependCellChunksLeftOfHeadDescription :
    Word Bool -> MachineDescription
  | [] => ExactIdentityDescription
  | bit :: [] => prependCellChunkLeftOfHeadDescription bit
  | bit :: next :: rest =>
      CommonGround.SameHeadComposition.leftRightSeqDescription
        (prependCellChunksLeftOfHeadDescription (next :: rest))
        (prependCellChunkLeftOfHeadDescription bit)

theorem prependCellChunksLeftOfHeadDescription_subroutineReady
    (layout : Word Bool) :
    (prependCellChunksLeftOfHeadDescription layout).SubroutineReady := by
  induction layout with
  | nil =>
      simpa [prependCellChunksLeftOfHeadDescription] using
        CommonGround.Identity.exactIdentityDescription_subroutineReady
  | cons bit rest ih =>
      cases rest with
      | nil =>
          simpa [prependCellChunksLeftOfHeadDescription] using
            prependCellChunkLeftOfHeadDescription_subroutineReady bit
      | cons next more =>
          simpa [prependCellChunksLeftOfHeadDescription] using
            CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
              ih
              (prependCellChunkLeftOfHeadDescription_subroutineReady bit)

theorem prependCellChunksLeftOfHeadDescription_target_moveLeftRight
    (bit : Bool) (rest suffix : Word Bool)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tapeAtCells
            ((List.append (preservingCellPassCellBits (bit :: rest))
              suffix).reverse.map some)
            (some tailFirst :: tail))) =
      tapeAtCells
        ((List.append (preservingCellPassCellBits (bit :: rest))
          suffix).reverse.map some)
        (some tailFirst :: tail) :=
  prependCellChunkLeftOfHeadDescription_cellAppendSuffix_target_moveLeftRight
    bit rest suffix tailFirst tail

theorem prependCellChunksLeftOfHeadDescription_haltsFrom
    (layout suffix : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (prependCellChunksLeftOfHeadDescription layout).HaltsFromTape
      (tapeAtCells (suffix.reverse.map some)
        (some tailFirst :: tail))
      (tapeAtCells
        ((List.append (preservingCellPassCellBits layout)
          suffix).reverse.map some)
        (some tailFirst :: tail)) := by
  induction layout generalizing suffix tailFirst tail with
  | nil =>
      simpa [prependCellChunksLeftOfHeadDescription,
        preservingCellPassCellBits] using
        CommonGround.Identity.exactIdentityDescription_haltsFromTape
          (tapeAtCells (suffix.reverse.map some)
            (some tailFirst :: tail))
  | cons bit rest ih =>
      cases rest with
      | nil =>
          simpa [prependCellChunksLeftOfHeadDescription,
            preservingCellPassCellBits] using
            prependCellChunkLeftOfHeadDescription_haltsFrom_cellAppendSuffix
              bit [] suffix tailFirst tail
      | cons next more =>
          exact
            CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
              (prependCellChunksLeftOfHeadDescription_subroutineReady
                (next :: more))
              (prependCellChunkLeftOfHeadDescription_subroutineReady bit)
              (ih suffix tailFirst tail)
              (prependCellChunksLeftOfHeadDescription_target_moveLeftRight
                next more suffix tailFirst tail)
              (by
                simpa [preservingCellPassCellBits,
                  preservingCellPassZeroBits, preservingCellPassOneBits,
                  List.append_assoc] using
                  prependCellChunkLeftOfHeadDescription_haltsFrom_cellAppendSuffix
                    bit (next :: more) suffix tailFirst tail)

theorem prependCellChunksLeftOfHeadDescription_haltsFrom_emptySuffix
    (layout : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (prependCellChunksLeftOfHeadDescription layout).HaltsFromTape
      (tapeAtCells [] (some tailFirst :: tail))
      (tapeAtCells
        ((preservingCellPassCellBits layout).reverse.map some)
        (some tailFirst :: tail)) := by
  simpa using
    prependCellChunksLeftOfHeadDescription_haltsFrom
      layout ([] : Word Bool) tailFirst tail

theorem prependCellChunksLeftOfHeadDescription_target_moveLeftRight_withScratch
    (layout suffix : Word Bool) (baseLeft : List (Option Bool))
    (tailFirst : Bool) (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tapeAtCells
            (List.append
              ((List.append (preservingCellPassCellBits layout)
                suffix).reverse.map some)
              (List.append
                (List.replicate 4 (none : Option Bool))
                baseLeft))
            (some tailFirst :: tail))) =
      tapeAtCells
        (List.append
          ((List.append (preservingCellPassCellBits layout)
            suffix).reverse.map some)
          (List.append
            (List.replicate 4 (none : Option Bool))
            baseLeft))
        (some tailFirst :: tail) := by
  simpa [List.replicate, List.append_assoc] using
    tapeAtCells_move_right_move_left_append_cons
      ((List.append (preservingCellPassCellBits layout)
        suffix).reverse.map some)
      (List.append (List.replicate 3 (none : Option Bool))
        baseLeft)
      (some tailFirst :: tail)
      (none : Option Bool)

theorem prependCellChunksLeftOfHeadDescription_haltsFrom_withScratch
    (layout suffix : Word Bool) (baseLeft : List (Option Bool))
    (tailFirst : Bool) (tail : List (Option Bool)) :
    (prependCellChunksLeftOfHeadDescription layout).HaltsFromTape
      (tapeAtCells
        (List.append (suffix.reverse.map some)
          (List.append
            (List.replicate (4 * layout.length)
              (none : Option Bool))
            baseLeft))
        (some tailFirst :: tail))
      (tapeAtCells
        (List.append
          ((List.append (preservingCellPassCellBits layout)
            suffix).reverse.map some)
          baseLeft)
        (some tailFirst :: tail)) := by
  induction layout generalizing suffix baseLeft tailFirst tail with
  | nil =>
      simpa [prependCellChunksLeftOfHeadDescription,
        preservingCellPassCellBits] using
        CommonGround.Identity.exactIdentityDescription_haltsFromTape
          (tapeAtCells (List.append (suffix.reverse.map some) baseLeft)
            (some tailFirst :: tail))
  | cons bit rest ih =>
      cases rest with
      | nil =>
          simpa [prependCellChunksLeftOfHeadDescription,
            preservingCellPassCellBits] using
            prependCellChunkLeftOfHeadDescription_haltsFrom_cellAppendSuffix_withScratch
              bit [] suffix baseLeft tailFirst tail
      | cons next more =>
          exact
            CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
              (prependCellChunksLeftOfHeadDescription_subroutineReady
                (next :: more))
              (prependCellChunkLeftOfHeadDescription_subroutineReady bit)
              (by
                have hA :=
                  ih suffix
                    (List.append
                      (List.replicate 4 (none : Option Bool))
                      baseLeft)
                    tailFirst tail
                have hsource :
                    tapeAtCells
                        (List.append (suffix.reverse.map some)
                          (List.append
                            (List.replicate (4 * (next :: more).length)
                              (none : Option Bool))
                            (List.append
                              (List.replicate 4 (none : Option Bool))
                              baseLeft)))
                        (some tailFirst :: tail) =
                      tapeAtCells
                        (List.append (suffix.reverse.map some)
                          (List.append
                            (List.replicate (4 * (bit :: next :: more).length)
                              (none : Option Bool))
                            baseLeft))
                        (some tailFirst :: tail) := by
                  rw [show
                      4 * (bit :: next :: more).length =
                        4 * (next :: more).length + 4 by
                    simp
                    lia]
                  simp [list_replicate_add_append]
                rw [hsource] at hA
                simpa [prependCellChunksLeftOfHeadDescription,
                  List.append_assoc] using hA)
              (prependCellChunksLeftOfHeadDescription_target_moveLeftRight_withScratch
                (next :: more) suffix baseLeft tailFirst tail)
              (by
                simpa [preservingCellPassCellBits,
                  preservingCellPassZeroBits, preservingCellPassOneBits,
                  List.append_assoc] using
                  prependCellChunkLeftOfHeadDescription_haltsFrom_cellAppendSuffix_withScratch
                    bit (next :: more) suffix baseLeft tailFirst tail)

theorem prependCellChunksLeftOfHeadDescription_haltsFrom_emptySuffix_withScratch
    (layout : Word Bool) (baseLeft : List (Option Bool))
    (tailFirst : Bool) (tail : List (Option Bool)) :
    (prependCellChunksLeftOfHeadDescription layout).HaltsFromTape
      (tapeAtCells
        (List.append
          (List.replicate (4 * layout.length)
            (none : Option Bool))
          baseLeft)
        (some tailFirst :: tail))
      (tapeAtCells
        (List.append
          ((preservingCellPassCellBits layout).reverse.map some)
          baseLeft)
        (some tailFirst :: tail)) := by
  simpa using
    prependCellChunksLeftOfHeadDescription_haltsFrom_withScratch
      layout ([] : Word Bool) baseLeft tailFirst tail

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
