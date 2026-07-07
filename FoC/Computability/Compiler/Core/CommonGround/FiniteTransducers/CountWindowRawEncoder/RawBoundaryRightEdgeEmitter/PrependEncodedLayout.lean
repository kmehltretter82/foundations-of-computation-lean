import FoC.Computability.ListLemmas
import FoC.Computability.Compiler.Core.CommonGround.SameHeadComposition
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawEncoder.RawBoundaryRightEdgeEmitter.PrependCellChunks
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawEncoder.RawBoundaryRightEdgeEmitter.PrependLengthChunks

set_option doc.verso true

/-!
# Raw-boundary right-edge encoded-layout prepender

This module composes the generated cell-suffix and length-field prepender
families with the fixed header chunk.  For a concrete layout word it gives a
finite machine that prepends exactly the encoded layout bits immediately to the
left of a live tail head.
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

def encodedLayoutChunkBits (layout : Word Bool) : Word Bool :=
  List.append
    (encodeCodeSymbolAsInput MachineCodeSymbol.header)
    (List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        layout.length)
      (preservingCellPassCellBits layout))

def lengthAndCellsScratchCellCount (layout : Word Bool) : Nat :=
  4 * layout.length + 4 * (layout.length + 1)

def encodedLayoutScratchCellCount (layout : Word Bool) : Nat :=
  lengthAndCellsScratchCellCount layout + 4

theorem lengthAndCellsScratchCellCount_eq
    (layout : Word Bool) :
    lengthAndCellsScratchCellCount layout = 8 * layout.length + 4 := by
  simp [lengthAndCellsScratchCellCount]
  lia

theorem encodedLayoutScratchCellCount_eq
    (layout : Word Bool) :
    encodedLayoutScratchCellCount layout = 8 * layout.length + 8 := by
  simp [encodedLayoutScratchCellCount,
    lengthAndCellsScratchCellCount_eq]

theorem encodedLayoutScratchCellCount_pos
    (layout : Word Bool) :
    0 < encodedLayoutScratchCellCount layout := by
  rw [encodedLayoutScratchCellCount_eq]
  lia

def prependLengthAndCellsLeftOfHeadDescription :
    Word Bool -> MachineDescription
  | [] => prependLengthChunksLeftOfHeadDescription 0
  | bit :: rest =>
      CommonGround.SameHeadComposition.leftRightSeqDescription
        (prependCellChunksLeftOfHeadDescription (bit :: rest))
        (prependLengthChunksLeftOfHeadDescription (bit :: rest).length)

theorem prependLengthAndCellsLeftOfHeadDescription_subroutineReady
    (layout : Word Bool) :
    (prependLengthAndCellsLeftOfHeadDescription layout).SubroutineReady := by
  cases layout with
  | nil =>
      simpa [prependLengthAndCellsLeftOfHeadDescription] using
        prependLengthChunksLeftOfHeadDescription_subroutineReady 0
  | cons bit rest =>
      simpa [prependLengthAndCellsLeftOfHeadDescription] using
        CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
          (prependCellChunksLeftOfHeadDescription_subroutineReady
            (bit :: rest))
          (prependLengthChunksLeftOfHeadDescription_subroutineReady
            (bit :: rest).length)

theorem prependLengthAndCellsLeftOfHeadDescription_haltsFrom
    (layout : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (prependLengthAndCellsLeftOfHeadDescription layout).HaltsFromTape
      (tapeAtCells [] (some tailFirst :: tail))
      (tapeAtCells
        ((List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            layout.length)
          (preservingCellPassCellBits layout)).reverse.map some)
        (some tailFirst :: tail)) := by
  cases layout with
  | nil =>
      simpa [prependLengthAndCellsLeftOfHeadDescription,
        preservingCellPassCellBits] using
        prependLengthChunksLeftOfHeadDescription_haltsFrom_cellSuffix
          ([] : Word Bool) tailFirst tail
  | cons bit rest =>
      exact
        CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
          (prependCellChunksLeftOfHeadDescription_subroutineReady
            (bit :: rest))
          (prependLengthChunksLeftOfHeadDescription_subroutineReady
            (bit :: rest).length)
          (prependCellChunksLeftOfHeadDescription_haltsFrom_emptySuffix
            (bit :: rest) tailFirst tail)
          (by
            simpa using
              prependCellChunksLeftOfHeadDescription_target_moveLeftRight
                bit rest ([] : Word Bool) tailFirst tail)
          (prependLengthChunksLeftOfHeadDescription_haltsFrom_cellSuffix
            (bit :: rest) tailFirst tail)

theorem tapeAtCells_moveRight_moveLeft_withScratchSucc
    (emittedRev baseLeft right : List (Option Bool)) (scratch : Nat) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tapeAtCells
            (List.append emittedRev
              (List.append
                (List.replicate (scratch + 1) (none : Option Bool))
                baseLeft))
            right)) =
      tapeAtCells
        (List.append emittedRev
          (List.append
            (List.replicate (scratch + 1) (none : Option Bool))
            baseLeft))
        right := by
  simpa [List.replicate_succ, Nat.add_comm, List.append_assoc] using
    tapeAtCells_move_right_move_left_append_cons
      emittedRev
      (List.append (List.replicate scratch (none : Option Bool))
        baseLeft)
      right
      (none : Option Bool)

theorem prependLengthAndCellsLeftOfHeadDescription_haltsFrom_withScratch
    (layout : Word Bool) (baseLeft : List (Option Bool))
    (tailFirst : Bool) (tail : List (Option Bool)) :
    (prependLengthAndCellsLeftOfHeadDescription layout).HaltsFromTape
      (tapeAtCells
        (List.append
          (List.replicate (lengthAndCellsScratchCellCount layout)
            (none : Option Bool))
          baseLeft)
        (some tailFirst :: tail))
      (tapeAtCells
        (List.append
          ((List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              layout.length)
            (preservingCellPassCellBits layout)).reverse.map some)
          baseLeft)
        (some tailFirst :: tail)) := by
  cases layout with
  | nil =>
      simpa [prependLengthAndCellsLeftOfHeadDescription,
        lengthAndCellsScratchCellCount, preservingCellPassCellBits] using
        prependLengthChunksLeftOfHeadDescription_haltsFrom_cellSuffix_withScratch
          ([] : Word Bool) baseLeft tailFirst tail
  | cons bit rest =>
      exact
        CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
          (prependCellChunksLeftOfHeadDescription_subroutineReady
            (bit :: rest))
          (prependLengthChunksLeftOfHeadDescription_subroutineReady
            (bit :: rest).length)
          (by
            have hA :=
              prependCellChunksLeftOfHeadDescription_haltsFrom_emptySuffix_withScratch
                (bit :: rest)
                (List.append
                  (List.replicate (4 * ((bit :: rest).length + 1))
                    (none : Option Bool))
                  baseLeft)
                tailFirst tail
            have hsource :
                tapeAtCells
                    (List.append
                      (List.replicate (4 * (bit :: rest).length)
                        (none : Option Bool))
                      (List.append
                        (List.replicate (4 * ((bit :: rest).length + 1))
                          (none : Option Bool))
                        baseLeft))
                    (some tailFirst :: tail) =
                  tapeAtCells
                    (List.append
                      (List.replicate
                        (lengthAndCellsScratchCellCount (bit :: rest))
                        (none : Option Bool))
                      baseLeft)
                    (some tailFirst :: tail) := by
              simp [lengthAndCellsScratchCellCount,
                list_replicate_add_append]
            rw [hsource] at hA
            simpa [prependLengthAndCellsLeftOfHeadDescription,
              List.append_assoc] using hA)
          (by
            rw [show
                4 * ((bit :: rest).length + 1) =
                  4 * (bit :: rest).length + 3 + 1 by
              lia]
            simpa using
              tapeAtCells_moveRight_moveLeft_withScratchSucc
                ((preservingCellPassCellBits (bit :: rest)).reverse.map some)
                baseLeft
                (some tailFirst :: tail)
                (4 * (bit :: rest).length + 3))
          (prependLengthChunksLeftOfHeadDescription_haltsFrom_cellSuffix_withScratch
            (bit :: rest) baseLeft tailFirst tail)

def prependEncodedLayoutLeftOfHeadDescription
    (layout : Word Bool) : MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    (prependLengthAndCellsLeftOfHeadDescription layout)
    prependHeaderChunkLeftOfHeadDescription

theorem prependEncodedLayoutLeftOfHeadDescription_subroutineReady
    (layout : Word Bool) :
    (prependEncodedLayoutLeftOfHeadDescription layout).SubroutineReady :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    (prependLengthAndCellsLeftOfHeadDescription_subroutineReady layout)
    prependHeaderChunkLeftOfHeadDescription_subroutineReady

theorem prependEncodedLayoutLeftOfHeadDescription_haltsFrom
    (layout : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (prependEncodedLayoutLeftOfHeadDescription layout).HaltsFromTape
      (tapeAtCells [] (some tailFirst :: tail))
      (tapeAtCells
        ((encodedLayoutChunkBits layout).reverse.map some)
        (some tailFirst :: tail)) := by
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
      (prependLengthAndCellsLeftOfHeadDescription_subroutineReady layout)
      prependHeaderChunkLeftOfHeadDescription_subroutineReady
      (prependLengthAndCellsLeftOfHeadDescription_haltsFrom
        layout tailFirst tail)
      (prependLengthChunksLeftOfHeadDescription_target_moveLeftRight
        layout.length (preservingCellPassCellBits layout)
        tailFirst tail)
      (by
        simpa [encodedLayoutChunkBits, List.append_assoc] using
          prependHeaderChunkLeftOfHeadDescription_haltsFrom_prepend
            (List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                layout.length)
              (preservingCellPassCellBits layout))
            tailFirst tail)

theorem prependEncodedLayoutLeftOfHeadDescription_haltsFrom_withScratch
    (layout : Word Bool) (baseLeft : List (Option Bool))
    (tailFirst : Bool) (tail : List (Option Bool)) :
    (prependEncodedLayoutLeftOfHeadDescription layout).HaltsFromTape
      (tapeAtCells
        (List.append
          (List.replicate (encodedLayoutScratchCellCount layout)
            (none : Option Bool))
          baseLeft)
        (some tailFirst :: tail))
      (tapeAtCells
        (List.append
          ((encodedLayoutChunkBits layout).reverse.map some)
          baseLeft)
        (some tailFirst :: tail)) := by
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
      (prependLengthAndCellsLeftOfHeadDescription_subroutineReady layout)
      prependHeaderChunkLeftOfHeadDescription_subroutineReady
      (by
        have hA :=
          prependLengthAndCellsLeftOfHeadDescription_haltsFrom_withScratch
            layout
            (List.append (List.replicate 4 (none : Option Bool))
              baseLeft)
            tailFirst tail
        have hsource :
            tapeAtCells
                (List.append
                  (List.replicate (lengthAndCellsScratchCellCount layout)
                    (none : Option Bool))
                  (List.append (List.replicate 4 (none : Option Bool))
                    baseLeft))
                (some tailFirst :: tail) =
              tapeAtCells
                (List.append
                  (List.replicate (encodedLayoutScratchCellCount layout)
                    (none : Option Bool))
                  baseLeft)
                (some tailFirst :: tail) := by
          simp [encodedLayoutScratchCellCount,
            list_replicate_add_append]
        rw [hsource] at hA
        simpa [List.append_assoc] using hA)
      (prependLengthChunksLeftOfHeadDescription_target_moveLeftRight_withScratch
        layout.length (preservingCellPassCellBits layout)
        baseLeft tailFirst tail)
      (by
        simpa [encodedLayoutChunkBits, List.append_assoc] using
          prependHeaderChunkLeftOfHeadDescription_haltsFrom_prepend_withScratch
            (List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                layout.length)
              (preservingCellPassCellBits layout))
            baseLeft tailFirst tail)

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
