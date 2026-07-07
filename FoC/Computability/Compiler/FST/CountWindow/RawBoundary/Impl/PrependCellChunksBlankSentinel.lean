import FoC.Computability.Compiler.Core.CommonGround.SameHeadComposition
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.PrependFixedFourBitsBlankSentinel

set_option doc.verso true

/-!
# Raw-boundary cell-chunk prepender with a blank sentinel

This module composes the blank-sentinel fixed chunk primitive across a concrete
Boolean layout.  The right boundary remains blank after every emitted chunk, so
later raw-boundary routes can continue to use that blank as a delimiter and
restore the live tail head only once at the end.
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

def prependCellChunksLeftOfBlankSentinelDescription :
    Word Bool -> MachineDescription
  | [] => ExactIdentityDescription
  | bit :: [] => prependCellChunkLeftOfBlankSentinelDescription bit
  | bit :: next :: rest =>
      CommonGround.SameHeadComposition.leftRightSeqDescription
        (prependCellChunksLeftOfBlankSentinelDescription (next :: rest))
        (prependCellChunkLeftOfBlankSentinelDescription bit)

theorem prependCellChunksLeftOfBlankSentinelDescription_subroutineReady
    (layout : Word Bool) :
    (prependCellChunksLeftOfBlankSentinelDescription
      layout).SubroutineReady := by
  induction layout with
  | nil =>
      simpa [prependCellChunksLeftOfBlankSentinelDescription] using
        CommonGround.Identity.exactIdentityDescription_subroutineReady
  | cons bit rest ih =>
      cases rest with
      | nil =>
          simpa [prependCellChunksLeftOfBlankSentinelDescription] using
            prependCellChunkLeftOfBlankSentinelDescription_subroutineReady bit
      | cons next more =>
          simpa [prependCellChunksLeftOfBlankSentinelDescription] using
            CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
              ih
              (prependCellChunkLeftOfBlankSentinelDescription_subroutineReady
                bit)

theorem prependCellChunksLeftOfBlankSentinelDescription_target_moveLeftRight
    (bit : Bool) (rest suffix : Word Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tapeAtCells
            ((List.append (preservingCellPassCellBits (bit :: rest))
              suffix).reverse.map some)
            (none :: tail))) =
      tapeAtCells
        ((List.append (preservingCellPassCellBits (bit :: rest))
          suffix).reverse.map some)
        (none :: tail) := by
  cases bit
  · simpa [preservingCellPassCellBits, preservingCellPassZeroBits,
      List.append_assoc] using
      prependCellChunkLeftOfBlankSentinelDescription_target_moveLeftRight
        false (List.append (preservingCellPassCellBits rest) suffix) tail
  · simpa [preservingCellPassCellBits, preservingCellPassOneBits,
      List.append_assoc] using
      prependCellChunkLeftOfBlankSentinelDescription_target_moveLeftRight
        true (List.append (preservingCellPassCellBits rest) suffix) tail

theorem prependCellChunksLeftOfBlankSentinelDescription_haltsFrom
    (layout suffix : Word Bool) (tail : List (Option Bool)) :
    (prependCellChunksLeftOfBlankSentinelDescription layout).HaltsFromTape
      (tapeAtCells (suffix.reverse.map some) (none :: tail))
      (tapeAtCells
        ((List.append (preservingCellPassCellBits layout)
          suffix).reverse.map some)
        (none :: tail)) := by
  induction layout generalizing suffix tail with
  | nil =>
      simpa [prependCellChunksLeftOfBlankSentinelDescription,
        preservingCellPassCellBits] using
        CommonGround.Identity.exactIdentityDescription_haltsFromTape
          (tapeAtCells (suffix.reverse.map some) (none :: tail))
  | cons bit rest ih =>
      cases rest with
      | nil =>
          simpa [prependCellChunksLeftOfBlankSentinelDescription,
            preservingCellPassCellBits] using
            prependCellChunkLeftOfBlankSentinelDescription_haltsFrom_prepend
              bit suffix tail
      | cons next more =>
          exact
            CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
              (prependCellChunksLeftOfBlankSentinelDescription_subroutineReady
                (next :: more))
              (prependCellChunkLeftOfBlankSentinelDescription_subroutineReady
                bit)
              (ih suffix tail)
              (prependCellChunksLeftOfBlankSentinelDescription_target_moveLeftRight
                next more suffix tail)
              (by
                simpa [preservingCellPassCellBits,
                  preservingCellPassCellBits_reverse_cons_chunk,
                  preservingCellPassZeroBits, preservingCellPassOneBits,
                  List.map_append, List.map_reverse, List.append_assoc] using
                  prependCellChunkLeftOfBlankSentinelDescription_haltsFrom_prepend
                    bit
                    (List.append
                      (preservingCellPassCellBits (next :: more))
                      suffix)
                    tail)

theorem prependCellChunksLeftOfBlankSentinelDescription_haltsFrom_emptySuffix
    (layout : Word Bool) (tail : List (Option Bool)) :
    (prependCellChunksLeftOfBlankSentinelDescription layout).HaltsFromTape
      (tapeAtCells [] (none :: tail))
      (tapeAtCells
        ((preservingCellPassCellBits layout).reverse.map some)
        (none :: tail)) := by
  simpa using
    prependCellChunksLeftOfBlankSentinelDescription_haltsFrom
      layout ([] : Word Bool) tail

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
