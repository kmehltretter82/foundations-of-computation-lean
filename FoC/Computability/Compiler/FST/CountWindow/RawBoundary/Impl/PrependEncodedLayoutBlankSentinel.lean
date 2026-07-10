import FoC.Computability.Compiler.Core.CommonGround.SameHeadComposition
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.PrependCellChunksBlankSentinel
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.PrependEncodedLayout
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.PrependLengthChunksBlankSentinel
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.RestoreBlankSentinel

set_option doc.verso true

/-!
# Raw-boundary encoded-layout prepender with a blank sentinel

This module composes the delimiter-preserving cell-suffix and length-field
families with the fixed header chunk.  For a concrete layout word it gives a
finite machine that prepends exactly the encoded layout bits while leaving the
right boundary blank.
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

def prependLengthAndCellsLeftOfBlankSentinelDescription :
    Word Bool -> MachineDescription
  | [] => prependLengthChunksLeftOfBlankSentinelDescription 0
  | bit :: rest =>
      CommonGround.SameHeadComposition.leftRightSeqDescription
        (prependCellChunksLeftOfBlankSentinelDescription (bit :: rest))
        (prependLengthChunksLeftOfBlankSentinelDescription
          (bit :: rest).length)

theorem prependLengthAndCellsLeftOfBlankSentinelDescription_subroutineReady
    (layout : Word Bool) :
    (prependLengthAndCellsLeftOfBlankSentinelDescription
      layout).SubroutineReady := by
  cases layout with
  | nil =>
      simpa [prependLengthAndCellsLeftOfBlankSentinelDescription] using
        prependLengthChunksLeftOfBlankSentinelDescription_subroutineReady 0
  | cons bit rest =>
      simpa [prependLengthAndCellsLeftOfBlankSentinelDescription] using
        CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
          (prependCellChunksLeftOfBlankSentinelDescription_subroutineReady
            (bit :: rest))
          (prependLengthChunksLeftOfBlankSentinelDescription_subroutineReady
            (bit :: rest).length)

theorem prependLengthAndCellsLeftOfBlankSentinelDescription_haltsFrom
    (layout : Word Bool) (tail : List (Option Bool)) :
    (prependLengthAndCellsLeftOfBlankSentinelDescription
      layout).HaltsFromTape
      (tapeAtCells [] (none :: tail))
      (tapeAtCells
        ((List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            layout.length)
          (preservingCellPassCellBits layout)).reverse.map some)
        (none :: tail)) := by
  cases layout with
  | nil =>
      simpa [prependLengthAndCellsLeftOfBlankSentinelDescription,
        preservingCellPassCellBits] using
        prependLengthChunksLeftOfBlankSentinelDescription_haltsFrom_cellSuffix
          ([] : Word Bool) tail
  | cons bit rest =>
      exact
        CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
          (prependCellChunksLeftOfBlankSentinelDescription_subroutineReady
            (bit :: rest))
          (prependLengthChunksLeftOfBlankSentinelDescription_subroutineReady
            (bit :: rest).length)
          (prependCellChunksLeftOfBlankSentinelDescription_haltsFrom_emptySuffix
            (bit :: rest) tail)
          (by
            simpa using
              prependCellChunksLeftOfBlankSentinelDescription_target_moveLeftRight
                bit rest ([] : Word Bool) tail)
          (prependLengthChunksLeftOfBlankSentinelDescription_haltsFrom_cellSuffix
            (bit :: rest) tail)

def prependEncodedLayoutLeftOfBlankSentinelDescription
    (layout : Word Bool) : MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    (prependLengthAndCellsLeftOfBlankSentinelDescription layout)
    prependHeaderChunkLeftOfBlankSentinelDescription

theorem prependEncodedLayoutLeftOfBlankSentinelDescription_subroutineReady
    (layout : Word Bool) :
    (prependEncodedLayoutLeftOfBlankSentinelDescription
      layout).SubroutineReady :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    (prependLengthAndCellsLeftOfBlankSentinelDescription_subroutineReady
      layout)
    prependHeaderChunkLeftOfBlankSentinelDescription_subroutineReady

theorem prependEncodedLayoutLeftOfBlankSentinelDescription_haltsFrom
    (layout : Word Bool) (tail : List (Option Bool)) :
    (prependEncodedLayoutLeftOfBlankSentinelDescription layout).HaltsFromTape
      (tapeAtCells [] (none :: tail))
      (tapeAtCells
        ((encodedLayoutChunkBits layout).reverse.map some)
        (none :: tail)) := by
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
      (prependLengthAndCellsLeftOfBlankSentinelDescription_subroutineReady
        layout)
      prependHeaderChunkLeftOfBlankSentinelDescription_subroutineReady
      (prependLengthAndCellsLeftOfBlankSentinelDescription_haltsFrom
        layout tail)
      (prependLengthChunksLeftOfBlankSentinelDescription_target_moveLeftRight
        layout.length (preservingCellPassCellBits layout) tail)
      (by
        simpa [encodedLayoutChunkBits, List.append_assoc] using!
          prependHeaderChunkLeftOfBlankSentinelDescription_haltsFrom_prepend
            (List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                layout.length)
              (preservingCellPassCellBits layout))
            tail)

theorem prependEncodedLayoutLeftOfBlankSentinelDescription_target_moveLeftRight
    (layout : Word Bool) (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tapeAtCells
            ((encodedLayoutChunkBits layout).reverse.map some)
            (none :: tail))) =
      tapeAtCells
        ((encodedLayoutChunkBits layout).reverse.map some)
        (none :: tail) := by
  simpa [encodedLayoutChunkBits, List.append_assoc] using!
    prependFixedFourBitsLeftOfBlankSentinelDescription_target_moveLeftRight
      false false false false
      (List.append
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          layout.length)
        (preservingCellPassCellBits layout))
      tail

def prependEncodedLayoutLeftOfBlankSentinelThenRestoreDescription
    (layout : Word Bool) (tailFirst : Bool) : MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    (prependEncodedLayoutLeftOfBlankSentinelDescription layout)
    (restoreBlankSentinelTailHeadDescription tailFirst)

theorem
    prependEncodedLayoutLeftOfBlankSentinelThenRestoreDescription_subroutineReady
    (layout : Word Bool) (tailFirst : Bool) :
    (prependEncodedLayoutLeftOfBlankSentinelThenRestoreDescription
      layout tailFirst).SubroutineReady :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    (prependEncodedLayoutLeftOfBlankSentinelDescription_subroutineReady
      layout)
    (restoreBlankSentinelTailHeadDescription_subroutineReady tailFirst)

theorem prependEncodedLayoutChunkBits_reverse_map_some_ne_nil
    (layout : Word Bool) :
    (encodedLayoutChunkBits layout).reverse.map some ≠ [] := by
  simp [encodedLayoutChunkBits, encodeCodeSymbolAsInput]

theorem prependEncodedLayoutLeftOfBlankSentinelThenRestoreDescription_haltsFrom
    (layout : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (prependEncodedLayoutLeftOfBlankSentinelThenRestoreDescription
      layout tailFirst).HaltsFromTape
      (tapeAtCells [] (none :: tail))
      (tapeAtCells
        ((encodedLayoutChunkBits layout).reverse.map some)
        (some tailFirst :: tail)) := by
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
      (prependEncodedLayoutLeftOfBlankSentinelDescription_subroutineReady
        layout)
      (restoreBlankSentinelTailHeadDescription_subroutineReady tailFirst)
      (prependEncodedLayoutLeftOfBlankSentinelDescription_haltsFrom
        layout tail)
      (prependEncodedLayoutLeftOfBlankSentinelDescription_target_moveLeftRight
        layout tail)
      (restoreBlankSentinelTailHeadDescription_haltsFrom_of_nonempty
        tailFirst
        ((encodedLayoutChunkBits layout).reverse.map some)
        tail
        (prependEncodedLayoutChunkBits_reverse_map_some_ne_nil layout))

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
