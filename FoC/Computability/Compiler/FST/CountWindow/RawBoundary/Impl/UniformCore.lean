import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.SourceBoundaryEntry
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.GuardedHeaderPrepend
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.TailHandoffSeams
import FoC.Computability.Compiler.Core.CommonGround.SameHeadComposition
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.TapeLemmas

set_option doc.verso true

/-!
# Raw-boundary uniform right-edge emitter core

This module assembles the two-pass uniform raw-boundary right-edge emitter
from the five proved stage machines: the source-boundary entry glue, the
chunk-expansion loop, the length-cursor loop, the guarded header prepender,
and the packaged tail-handoff/block-migration transit.  The composed core
halts, up to trailing blank residue, on the encoded-layout left edge for
every raw layout — no emptiness split.

The empty and nonempty raw layouts are merged by stating every interior
same-head seam on a left context that carries an explicit trailing anchor
blank: the padded tape is equivalent to each stage's exact halt tape, it is
exactly the anchored entry the guarded header prepender accepts, and its
left context is never empty, so the left-then-right seam jiggle is the
identity in both cases.
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

/--
Uniform two-pass emitter core: entry glue, then (as same-head phases) the
chunk-expansion loop, the length-cursor loop, the guarded header prepender,
and the blank-run transit into the block-migration loop.
-/
def rawBoundaryUniformEmitterCoreDescription : MachineDescription :=
  seqSubroutine rawBoundarySourceBoundaryEntryDescription
    (SameHeadComposition.leftRightSeqDescription
      rawBoundaryChunkExpandLoopDescription
      (SameHeadComposition.leftRightSeqDescription
        rawBoundaryLengthCursorLoopDescription
        (SameHeadComposition.leftRightSeqDescription
          rawBoundaryGuardedHeaderPrependDescription
          (seqSubroutine rightBlankRunTailFirstLeftHandoffDescription
            rawBoundaryBlockMigrationLoopDescription
            Direction.right))))
    Direction.left

theorem rawBoundaryUniformEmitterCoreDescription_subroutineReady :
    rawBoundaryUniformEmitterCoreDescription.SubroutineReady := by
  rw [rawBoundaryUniformEmitterCoreDescription]
  exact
    seqSubroutine_subroutineReady
      rawBoundarySourceBoundaryEntryDescription_subroutineReady
      (SameHeadComposition.leftRightSeqDescription_subroutineReady
        rawBoundaryChunkExpandLoopDescription_subroutineReady
        (SameHeadComposition.leftRightSeqDescription_subroutineReady
          rawBoundaryLengthCursorLoopDescription_subroutineReady
          (SameHeadComposition.leftRightSeqDescription_subroutineReady
            rawBoundaryGuardedHeaderPrependDescription_subroutineReady
            tailHandoffMigrationSeq_subroutineReady)))

/-!
## Padded separator seam tapes

Appending one anchor blank to the left context does not change the tape up
to trailing blank residue, and it keeps the left context nonempty so the
same-head seam jiggle is exactly the identity.
-/

theorem tapeAtCells_pad_left_none_equiv
    (cells right : List (Option Bool)) :
    Tape.Equiv (tapeAtCells cells right)
      (tapeAtCells (List.append cells [none]) right) := by
  cases right with
  | nil =>
      exact ⟨(dropTrailingNone_append_none cells).symm, rfl, rfl⟩
  | cons cell rest =>
      exact ⟨(dropTrailingNone_append_none cells).symm, rfl, rfl⟩

theorem rawBoundaryLengthCursorSeparatorTape_equiv_padded
    (emitted : Word Bool) (blankTail : Nat)
    (right : List (Option Bool)) :
    Tape.Equiv
      (rawBoundaryLengthCursorSeparatorTape emitted blankTail right)
      (tapeAtCells
        (List.append (emitted.reverse.map some) [none])
        (none ::
          List.append
            (List.replicate (blankTail + 1) (none : Option Bool))
            right)) := by
  rw [rawBoundaryLengthCursorSeparatorTape]
  exact
    tapeAtCells_pad_left_none_equiv (emitted.reverse.map some)
      (none ::
        List.append
          (List.replicate (blankTail + 1) (none : Option Bool))
          right)

/--
Definitional bridge between the chunk-expansion exit tape (fully consumed
raw layout, emitted block from the empty seed) and the length-cursor entry
separator tape.
-/
theorem rawBoundaryChunkExpandExitTape_eq_lengthCursorSeparatorTape
    (layout : Word Bool) (blankTail : Nat)
    (right : List (Option Bool)) :
    rawBoundaryChunkExpandSeparatorTape
        (List.append (preservingCellPassCellBits layout) []) []
        blankTail right =
      rawBoundaryLengthCursorSeparatorTape
        (preservingCellPassCellBits layout) blankTail right := by
  simp [rawBoundaryChunkExpandSeparatorTape,
    rawBoundaryLengthCursorSeparatorTape]

/-!
## Uniform end-to-end theorem
-/

/--
Uniform start-to-halt statement for the two-pass emitter core, stated on the
raw left-edge target cells (the {lit}`encodedLeftEdgeTape` shape unfolded to
its {lit}`tapeAtCells` form): from the raw-boundary source tape the core
halts, up to trailing blank residue, with the encoded layout immediately
left of the live tail and the head on the layout's first bit.  Uniform in
{lit}`skipped` and {lit}`count`; no emptiness split.
-/
theorem rawBoundaryUniformEmitterCoreDescription_haltsFrom_sourceTape_encodedLeftEdgeCells
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    rawBoundaryUniformEmitterCoreDescription.HaltsFromTapeEquiv
      (sourceTape skipped count (some tailFirst :: tail))
      (tapeAtCells [none]
        (List.append
          ((encodedLayoutBits (List.append skipped count)).map some)
          (some tailFirst :: tail))) := by
  -- Chunk-expansion stage, restated on the padded separator tape.
  have hChunk :
      rawBoundaryChunkExpandLoopDescription.HaltsFromTapeEquiv
        (rawBoundaryChunkExpandSeparatorTape []
          (List.append skipped count) (count.length + 2)
          (some tailFirst :: tail))
        (tapeAtCells
          (List.append
            ((preservingCellPassCellBits
              (List.append skipped count)).reverse.map some)
            [none])
          (none ::
            List.append
              (List.replicate
                (count.length + 2 + (List.append skipped count).length + 1)
                (none : Option Bool))
              (some tailFirst :: tail))) := by
    refine
      haltsFromTapeEquiv_across_output_equiv
        (rawBoundaryChunkExpandLoopDescription_haltsFrom_separator_obligation
          (List.append skipped count) [] (count.length + 2)
          (some tailFirst :: tail)).toEquiv ?_
    rw [rawBoundaryChunkExpandExitTape_eq_lengthCursorSeparatorTape]
    exact
      rawBoundaryLengthCursorSeparatorTape_equiv_padded
        (preservingCellPassCellBits (List.append skipped count))
        (count.length + 2 + (List.append skipped count).length)
        (some tailFirst :: tail)
  -- Length-cursor stage, padded on both ends.
  have hCursor :
      rawBoundaryLengthCursorLoopDescription.HaltsFromTapeEquiv
        (tapeAtCells
          (List.append
            ((preservingCellPassCellBits
              (List.append skipped count)).reverse.map some)
            [none])
          (none ::
            List.append
              (List.replicate
                (count.length + 2 + (List.append skipped count).length + 1)
                (none : Option Bool))
              (some tailFirst :: tail)))
        (tapeAtCells
          (List.append
            ((rawBoundaryLengthCursorOutputBits
              (List.append skipped count)).reverse.map some)
            [none])
          (none ::
            List.append
              (List.replicate
                (count.length + 2 + (List.append skipped count).length + 1)
                (none : Option Bool))
              (some tailFirst :: tail))) := by
    refine
      haltsFromTapeEquiv_across_output_equiv
        (haltsFromTapeEquiv_across_input_equiv
          (rawBoundaryLengthCursorSeparatorTape_equiv_padded
            (preservingCellPassCellBits (List.append skipped count))
            (count.length + 2 + (List.append skipped count).length)
            (some tailFirst :: tail))
          (rawBoundaryLengthCursorLoopDescription_haltsFrom_separator_obligation
            (List.append skipped count)
            (count.length + 2 + (List.append skipped count).length)
            (some tailFirst :: tail))) ?_
    rw [rawBoundaryLengthCursorTargetTape]
    exact
      rawBoundaryLengthCursorSeparatorTape_equiv_padded
        (rawBoundaryLengthCursorOutputBits (List.append skipped count))
        (count.length + 2 + (List.append skipped count).length)
        (some tailFirst :: tail)
  -- Guarded header writer stage: the padded tape is exactly the anchored
  -- entry, and the halt tape is exact.
  have hWriter :
      rawBoundaryGuardedHeaderPrependDescription.HaltsFromTape
        (tapeAtCells
          (List.append
            ((rawBoundaryLengthCursorOutputBits
              (List.append skipped count)).reverse.map some)
            [none])
          (none ::
            List.append
              (List.replicate
                (count.length + 2 + (List.append skipped count).length + 1)
                (none : Option Bool))
              (some tailFirst :: tail)))
        (tapeAtCells
          (List.append
            ((encodedLayoutBits (List.append skipped count)).reverse.map
              some)
            [some true, none])
          (none ::
            List.append
              (List.replicate
                (count.length + 2 + (List.append skipped count).length + 1)
                (none : Option Bool))
              (some tailFirst :: tail))) := by
    simpa using
      rawBoundaryGuardedHeaderPrependDescription_haltsFrom_separator_anchored
        true (List.append skipped count)
        (count.length + 2 + (List.append skipped count).length)
        (some tailFirst :: tail)
  rw [rawBoundaryUniformEmitterCoreDescription]
  exact
    SeqComposition.seqSubroutine_haltsFromTapeEquiv_of_haltsFromTape_eq
      rawBoundarySourceBoundaryEntryDescription_subroutineReady
      (SameHeadComposition.leftRightSeqDescription_subroutineReady
        rawBoundaryChunkExpandLoopDescription_subroutineReady
        (SameHeadComposition.leftRightSeqDescription_subroutineReady
          rawBoundaryLengthCursorLoopDescription_subroutineReady
          (SameHeadComposition.leftRightSeqDescription_subroutineReady
            rawBoundaryGuardedHeaderPrependDescription_subroutineReady
            tailHandoffMigrationSeq_subroutineReady)))
      (rawBoundarySourceBoundaryEntryDescription_haltsFrom_sourceTape
        skipped count (some tailFirst :: tail))
      (rawBoundarySourceBoundaryEntryExitTape_move_left
        skipped count tailFirst tail)
      (SameHeadComposition.leftRightSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv
        rawBoundaryChunkExpandLoopDescription_subroutineReady
        (SameHeadComposition.leftRightSeqDescription_subroutineReady
          rawBoundaryLengthCursorLoopDescription_subroutineReady
          (SameHeadComposition.leftRightSeqDescription_subroutineReady
            rawBoundaryGuardedHeaderPrependDescription_subroutineReady
            tailHandoffMigrationSeq_subroutineReady))
        hChunk
        (tapeAtCells_move_right_move_left_append_singleton
          ((preservingCellPassCellBits
            (List.append skipped count)).reverse.map some)
          none
          (none ::
            List.append
              (List.replicate
                (count.length + 2 + (List.append skipped count).length + 1)
                (none : Option Bool))
              (some tailFirst :: tail)))
        (SameHeadComposition.leftRightSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv
          rawBoundaryLengthCursorLoopDescription_subroutineReady
          (SameHeadComposition.leftRightSeqDescription_subroutineReady
            rawBoundaryGuardedHeaderPrependDescription_subroutineReady
            tailHandoffMigrationSeq_subroutineReady)
          hCursor
          (tapeAtCells_move_right_move_left_append_singleton
            ((rawBoundaryLengthCursorOutputBits
              (List.append skipped count)).reverse.map some)
            none
            (none ::
              List.append
                (List.replicate
                  (count.length + 2 +
                    (List.append skipped count).length + 1)
                  (none : Option Bool))
                (some tailFirst :: tail)))
          (SameHeadComposition.leftRightSeqDescription_haltsFromTapeEquiv_of_haltsFromTape
            rawBoundaryGuardedHeaderPrependDescription_subroutineReady
            tailHandoffMigrationSeq_subroutineReady
            hWriter
            (guardedWriterExitTape_move_right_move_left
              (List.append skipped count)
              (count.length + 2 + (List.append skipped count).length)
              (some tailFirst :: tail))
            (tailHandoffMigrationSeq_haltsFromEquiv_guardedWriterExit_leftEdge
              (List.append skipped count)
              (count.length + 2 + (List.append skipped count).length)
              tailFirst tail))))

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
