import FoC.Computability.Compiler.Core.CommonGround.SameHeadComposition
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawEncoder.RawBoundaryRightEdgeEmitter.PrependFixedFourBitsBlankSentinel

set_option doc.verso true

/-!
# Raw-boundary length-field prepender with a blank sentinel

This module composes the blank-sentinel fixed chunk primitive into a finite
description family for a concrete natural length.  The emitted
{lit}`stageNatBits` field is prepended to an existing suffix while preserving the
blank right-boundary delimiter.
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

def prependLengthChunksLeftOfBlankSentinelDescription :
    Nat -> MachineDescription
  | 0 => prependLengthDoneChunkLeftOfBlankSentinelDescription
  | n + 1 =>
      CommonGround.SameHeadComposition.leftRightSeqDescription
        (prependLengthChunksLeftOfBlankSentinelDescription n)
        prependLengthTickChunkLeftOfBlankSentinelDescription

theorem prependLengthChunksLeftOfBlankSentinelDescription_subroutineReady
    (n : Nat) :
    (prependLengthChunksLeftOfBlankSentinelDescription n).SubroutineReady := by
  induction n with
  | zero =>
      simpa [prependLengthChunksLeftOfBlankSentinelDescription] using
        prependLengthDoneChunkLeftOfBlankSentinelDescription_subroutineReady
  | succ n ih =>
      simpa [prependLengthChunksLeftOfBlankSentinelDescription] using
        CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
          ih
          prependLengthTickChunkLeftOfBlankSentinelDescription_subroutineReady

theorem prependLengthChunksLeftOfBlankSentinelDescription_target_moveLeftRight
    (n : Nat) (suffix : Word Bool) (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tapeAtCells
            ((List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                n)
              suffix).reverse.map some)
            (none :: tail))) =
      tapeAtCells
        ((List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            n)
          suffix).reverse.map some)
        (none :: tail) := by
  cases n with
  | zero =>
      simpa [
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_zero,
        encodeCodeSymbolAsInput] using
        prependFixedFourBitsLeftOfBlankSentinelDescription_target_moveLeftRight
          false false true true suffix tail
  | succ n =>
      simpa [
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ,
        encodeCodeSymbolAsInput, List.append_assoc] using
        prependFixedFourBitsLeftOfBlankSentinelDescription_target_moveLeftRight
          false false true false
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              n)
            suffix)
          tail

theorem prependLengthChunksLeftOfBlankSentinelDescription_haltsFrom
    (n : Nat) (suffix : Word Bool) (tail : List (Option Bool)) :
    (prependLengthChunksLeftOfBlankSentinelDescription n).HaltsFromTape
      (tapeAtCells (suffix.reverse.map some) (none :: tail))
      (tapeAtCells
        ((List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            n)
          suffix).reverse.map some)
        (none :: tail)) := by
  induction n generalizing suffix tail with
  | zero =>
      simpa [prependLengthChunksLeftOfBlankSentinelDescription,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_zero,
        encodeCodeSymbolAsInput] using
        prependLengthDoneChunkLeftOfBlankSentinelDescription_haltsFrom_prepend
          suffix tail
  | succ n ih =>
      exact
        CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
          (prependLengthChunksLeftOfBlankSentinelDescription_subroutineReady n)
          prependLengthTickChunkLeftOfBlankSentinelDescription_subroutineReady
          (ih suffix tail)
          (prependLengthChunksLeftOfBlankSentinelDescription_target_moveLeftRight
            n suffix tail)
          (by
            simpa [
              DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ,
              encodeCodeSymbolAsInput, List.append_assoc] using
              prependLengthTickChunkLeftOfBlankSentinelDescription_haltsFrom_prepend
                (List.append
                  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                    n)
                  suffix)
                tail)

theorem prependLengthChunksLeftOfBlankSentinelDescription_haltsFrom_cellSuffix
    (layout : Word Bool) (tail : List (Option Bool)) :
    (prependLengthChunksLeftOfBlankSentinelDescription
      layout.length).HaltsFromTape
      (tapeAtCells ((preservingCellPassCellBits layout).reverse.map some)
        (none :: tail))
      (tapeAtCells
        ((List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            layout.length)
          (preservingCellPassCellBits layout)).reverse.map some)
        (none :: tail)) :=
  prependLengthChunksLeftOfBlankSentinelDescription_haltsFrom
    layout.length (preservingCellPassCellBits layout) tail

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
