import FoC.Computability.ListLemmas
import FoC.Computability.Compiler.Core.CommonGround.SameHeadComposition
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawEncoder.RawBoundaryRightEdgeEmitter.PrependFixedFourBits

set_option doc.verso true

/-!
# Raw-boundary right-edge length-field prepender

This module composes the fixed length-field chunks into a finite description
family for a concrete natural length.  The generated machine prepends
{name (full := FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits)}`stageNatBits`
to an already-emitted suffix, preserving the live tail head exactly.
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

def prependLengthChunksLeftOfHeadDescription :
    Nat -> MachineDescription
  | 0 => prependLengthDoneChunkLeftOfHeadDescription
  | n + 1 =>
      CommonGround.SameHeadComposition.leftRightSeqDescription
        (prependLengthChunksLeftOfHeadDescription n)
        prependLengthTickChunkLeftOfHeadDescription

theorem prependLengthChunksLeftOfHeadDescription_subroutineReady
    (n : Nat) :
    (prependLengthChunksLeftOfHeadDescription n).SubroutineReady := by
  induction n with
  | zero =>
      simpa [prependLengthChunksLeftOfHeadDescription] using
        prependLengthDoneChunkLeftOfHeadDescription_subroutineReady
  | succ n ih =>
      simpa [prependLengthChunksLeftOfHeadDescription] using
        CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
          ih
          prependLengthTickChunkLeftOfHeadDescription_subroutineReady

theorem prependLengthChunksLeftOfHeadDescription_target_moveLeftRight
    (n : Nat) (suffix : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tapeAtCells
            ((List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                n)
              suffix).reverse.map some)
            (some tailFirst :: tail))) =
      tapeAtCells
        ((List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            n)
          suffix).reverse.map some)
        (some tailFirst :: tail) := by
  cases n with
  | zero =>
      simpa [
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_zero,
        encodeCodeSymbolAsInput] using
        prependLengthDoneChunkLeftOfHeadDescription_target_moveLeftRight
          suffix tailFirst tail
  | succ n =>
      simpa [
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ,
        encodeCodeSymbolAsInput, List.append_assoc] using
        prependLengthTickChunkLeftOfHeadDescription_target_moveLeftRight
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              n)
            suffix)
          tailFirst tail

theorem prependLengthChunksLeftOfHeadDescription_haltsFrom
    (n : Nat) (suffix : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (prependLengthChunksLeftOfHeadDescription n).HaltsFromTape
      (tapeAtCells (suffix.reverse.map some)
        (some tailFirst :: tail))
      (tapeAtCells
        ((List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            n)
          suffix).reverse.map some)
        (some tailFirst :: tail)) := by
  induction n generalizing suffix tailFirst tail with
  | zero =>
      simpa [prependLengthChunksLeftOfHeadDescription] using
        prependLengthDoneChunkLeftOfHeadDescription_haltsFrom_stageNatBitsZeroSuffix
          suffix tailFirst tail
  | succ n ih =>
      exact
        CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
          (prependLengthChunksLeftOfHeadDescription_subroutineReady n)
          prependLengthTickChunkLeftOfHeadDescription_subroutineReady
          (ih suffix tailFirst tail)
          (prependLengthChunksLeftOfHeadDescription_target_moveLeftRight
            n suffix tailFirst tail)
          (prependLengthTickChunkLeftOfHeadDescription_haltsFrom_stageNatBitsSuffix
            n suffix tailFirst tail)

theorem prependLengthChunksLeftOfHeadDescription_haltsFrom_cellSuffix
    (layout : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (prependLengthChunksLeftOfHeadDescription layout.length).HaltsFromTape
      (tapeAtCells ((preservingCellPassCellBits layout).reverse.map some)
        (some tailFirst :: tail))
      (tapeAtCells
        ((List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            layout.length)
          (preservingCellPassCellBits layout)).reverse.map some)
        (some tailFirst :: tail)) :=
  prependLengthChunksLeftOfHeadDescription_haltsFrom
    layout.length (preservingCellPassCellBits layout) tailFirst tail

theorem prependLengthChunksLeftOfHeadDescription_target_moveLeftRight_withScratch
    (n : Nat) (suffix : Word Bool) (baseLeft : List (Option Bool))
    (tailFirst : Bool) (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tapeAtCells
            (List.append
              ((List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  n)
                suffix).reverse.map some)
              (List.append
                (List.replicate 4 (none : Option Bool))
                baseLeft))
            (some tailFirst :: tail))) =
      tapeAtCells
        (List.append
          ((List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              n)
            suffix).reverse.map some)
          (List.append
            (List.replicate 4 (none : Option Bool))
            baseLeft))
        (some tailFirst :: tail) := by
  simpa [List.replicate, List.append_assoc] using
    tapeAtCells_move_right_move_left_append_cons
      ((List.append
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          n)
        suffix).reverse.map some)
      (List.append (List.replicate 3 (none : Option Bool))
        baseLeft)
      (some tailFirst :: tail)
      (none : Option Bool)

theorem prependLengthChunksLeftOfHeadDescription_haltsFrom_withScratch
    (n : Nat) (suffix : Word Bool)
    (baseLeft : List (Option Bool)) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (prependLengthChunksLeftOfHeadDescription n).HaltsFromTape
      (tapeAtCells
        (List.append (suffix.reverse.map some)
          (List.append
            (List.replicate (4 * (n + 1))
              (none : Option Bool))
            baseLeft))
        (some tailFirst :: tail))
      (tapeAtCells
        (List.append
          ((List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              n)
            suffix).reverse.map some)
          baseLeft)
        (some tailFirst :: tail)) := by
  induction n generalizing suffix baseLeft tailFirst tail with
  | zero =>
      simpa [prependLengthChunksLeftOfHeadDescription,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_zero,
        encodeCodeSymbolAsInput] using
        prependLengthDoneChunkLeftOfHeadDescription_haltsFrom_prepend_withScratch
          suffix baseLeft tailFirst tail
  | succ n ih =>
      exact
        CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
          (prependLengthChunksLeftOfHeadDescription_subroutineReady n)
          prependLengthTickChunkLeftOfHeadDescription_subroutineReady
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
                        (List.replicate (4 * (n + 1))
                          (none : Option Bool))
                        (List.append
                          (List.replicate 4 (none : Option Bool))
                          baseLeft)))
                    (some tailFirst :: tail) =
                  tapeAtCells
                    (List.append (suffix.reverse.map some)
                      (List.append
                        (List.replicate (4 * (n + 1 + 1))
                          (none : Option Bool))
                        baseLeft))
                    (some tailFirst :: tail) := by
              rw [show 4 * (n + 1 + 1) = 4 * (n + 1) + 4 by
                lia]
              simp [list_replicate_add_append]
            rw [hsource] at hA
            simpa [prependLengthChunksLeftOfHeadDescription,
              List.append_assoc] using hA)
          (prependLengthChunksLeftOfHeadDescription_target_moveLeftRight_withScratch
            n suffix baseLeft tailFirst tail)
          (by
            simpa [
              DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ,
              encodeCodeSymbolAsInput, List.append_assoc] using
              prependLengthTickChunkLeftOfHeadDescription_haltsFrom_prepend_withScratch
                (List.append
                  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                    n)
                  suffix)
                baseLeft tailFirst tail)

theorem prependLengthChunksLeftOfHeadDescription_haltsFrom_cellSuffix_withScratch
    (layout : Word Bool) (baseLeft : List (Option Bool))
    (tailFirst : Bool) (tail : List (Option Bool)) :
    (prependLengthChunksLeftOfHeadDescription layout.length).HaltsFromTape
      (tapeAtCells
        (List.append
          ((preservingCellPassCellBits layout).reverse.map some)
          (List.append
            (List.replicate (4 * (layout.length + 1))
              (none : Option Bool))
            baseLeft))
        (some tailFirst :: tail))
      (tapeAtCells
        (List.append
          ((List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              layout.length)
            (preservingCellPassCellBits layout)).reverse.map some)
          baseLeft)
        (some tailFirst :: tail)) :=
  prependLengthChunksLeftOfHeadDescription_haltsFrom_withScratch
    layout.length (preservingCellPassCellBits layout)
    baseLeft tailFirst tail

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
