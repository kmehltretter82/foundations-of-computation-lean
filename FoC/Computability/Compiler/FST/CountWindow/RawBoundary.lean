import FoC.Computability.ListLemmas
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.TapeLemmas
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.BlankSentinelFinalizer
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.BlockMigrationLoop
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.EmitPulledRawBit
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.CellSuffixLoop
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.ChunkExpandLoop
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.LengthCursorLoop
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.CountedBoundary
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.EndpointSupport
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.EraseRawFootprintBlankSentinel
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.EraseTailHeadBlankSentinel
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.LeftMoveAcrossFour
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.PrependCellChunks
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.PrependCellChunksBlankSentinel
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.PrependEncodedLayout
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.PrependEncodedLayoutBlankSentinel
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.PrependFixedFourBits
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.PrependFixedFourBitsBlankSentinel
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.PrependLengthChunks
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.PrependLengthChunksBlankSentinel
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.PullNearestRawBit
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.MarkerAwarePull
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.MarkedCellSuffixLoop
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.FixedBranchLoop
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.RestoreBlankSentinel
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.TailHandoff
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.UniformCore
import FoC.Computability.Compiler.Core.CommonGround.Identity
import FoC.Computability.Compiler.Core.CommonGround.SameHeadComposition
import FoC.Computability.Compiler.Core.CommonGround.SeqComposition
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.OneGapCompactor
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.RightEdgeRewind
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTableChecks
import FoC.Computability.Compiler.Structured.Lowering.ConcreteRefresh
import FoC.Computability.Compiler.Structured.Lowering.ThreeTapeHelpers
import FoC.Computability.Compiler.Structured.Lowering.ThreeTapeTactic
import FoC.Computability.Compiler.ClosedCfg.QuoteAssembly.Prefix
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Quoter.CellPass

set_option doc.verso true

/-!
# Count-window raw-boundary right-edge emitter

This module isolates the finite-machine leaf for the count-window raw-source
encoder.  The input head is on the raw boundary blank after the layout bits;
the right side contains the repaired count-window gap and a live nonblank tail
head.  The desired output is the encoded header/bool-word layout, positioned
immediately to the left of that live tail and halted on the right edge of the
encoded word.

The direct controller-initial header emitter is the model for the phase
structure, but cannot be reused unchanged because it writes into right-side
scratch and would overwrite the live tail.  The finite table for this leaf
should duplicate that phase structure with the following live-tail-safe order:

* preserve a recoverable count while scanning the raw bits;
* emit the cell-code suffix before the live tail without crossing unread bits;
* emit the unary length field from the preserved count markers;
* emit the header field;
* halt at the right edge of the emitted encoded word, immediately left of the
  live tail.

The parent count-window raw-source encoder module specializes this local
contract to the public count-window names.
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

/-!
## Structured raw-layout cell emitter

The first structured component for the raw-boundary emitter scans the raw
layout bits on logical tape 0 and appends their encoded cell forms to logical
tape 2.  Logical tape 1 is reserved for the length/header phases that will
wrap this suffix emitter.  The table is deliberately a three-tape
{name}`Structured.Description` in the read/write/move row fragment recognized
by the multi-tape lowerer.
-/

private abbrev structuredRow :=
  Structured.MultiTapeLowering.ThreeTape.row

private abbrev structuredStay :=
  Structured.MultiTapeLowering.ThreeTape.keepS

private def structuredPreserve
    (move : Structured.HeadMove) : Structured.TapeAction :=
  match move with
  | Structured.HeadMove.stay =>
      Structured.MultiTapeLowering.ThreeTape.keepS
  | Structured.HeadMove.left =>
      Structured.MultiTapeLowering.ThreeTape.keepL
  | Structured.HeadMove.right =>
      Structured.MultiTapeLowering.ThreeTape.keepR

private def structuredWriteBit
    (bit : Bool) (move : Structured.HeadMove) :
    Structured.TapeAction :=
  match move with
  | Structured.HeadMove.stay =>
      Structured.MultiTapeLowering.ThreeTape.writeS (some bit)
  | Structured.HeadMove.left =>
      Structured.MultiTapeLowering.ThreeTape.writeBitL bit
  | Structured.HeadMove.right =>
      Structured.MultiTapeLowering.ThreeTape.writeBitR bit

private def structuredRawBoundaryCellEmitInitialRow
    (read : Bool) (target : Nat) : Structured.Transition :=
  structuredRow 0 (some read) none none
    (structuredPreserve Structured.HeadMove.right)
    structuredStay
    (structuredWriteBit false Structured.HeadMove.right)
    target

private def structuredRawBoundaryCellEmitWriteRow
    (source : Nat) (read : Option Bool) (bit : Bool) (target : Nat) :
    Structured.Transition :=
  structuredRow source read none none
    structuredStay
    structuredStay
    (structuredWriteBit bit Structured.HeadMove.right)
    target

private def structuredRawBoundaryCellEmitHaltRow :
    Structured.Transition :=
  structuredRow 0 none none none
    structuredStay
    structuredStay
    structuredStay
    99

private def structuredRawBoundaryCellEmitWriteRows
    (source : Nat) (bit : Bool) (target : Nat) :
    List Structured.Transition :=
  [ structuredRawBoundaryCellEmitWriteRow source none bit target
  , structuredRawBoundaryCellEmitWriteRow source (some false) bit target
  , structuredRawBoundaryCellEmitWriteRow source (some true) bit target ]

/--
Three-tape structured suffix emitter for the raw-boundary right-edge encoder.

Tape 0 scans the raw layout bits.  Tape 1 is untouched scratch reserved for
the length/header phases.  Tape 2 receives
{name}`preservingCellPassCellBits` output at its current right blank.
-/
def structuredRawBoundaryRightEdgeCellEmitterDescription :
    Structured.Description where
  tapeCount := 3
  stateCount := 100
  start := 0
  halt := 99
  transitions :=
    [ structuredRawBoundaryCellEmitInitialRow false 10
    , structuredRawBoundaryCellEmitInitialRow true 20
    , structuredRawBoundaryCellEmitHaltRow ] ++
    structuredRawBoundaryCellEmitWriteRows 10 true 11 ++
    structuredRawBoundaryCellEmitWriteRows 11 false 12 ++
    structuredRawBoundaryCellEmitWriteRows 12 true 0 ++
    structuredRawBoundaryCellEmitWriteRows 20 true 21 ++
    structuredRawBoundaryCellEmitWriteRows 21 true 22 ++
    structuredRawBoundaryCellEmitWriteRows 22 false 0

theorem structuredRawBoundaryRightEdgeCellEmitterDescription_supportsReadWriteRows3 :
    Structured.MultiTapeLowering.supportsReadWriteRows3
      structuredRawBoundaryRightEdgeCellEmitterDescription = true := by
  decide

theorem structuredRawBoundaryRightEdgeCellEmitterDescription_supported :
    Structured.MultiTapeLowering.SupportsReadWriteRows3
      structuredRawBoundaryRightEdgeCellEmitterDescription :=
  Structured.MultiTapeLowering.supportedReadWriteRows3_of_supports_eq_true
    structuredRawBoundaryRightEdgeCellEmitterDescription_supportsReadWriteRows3

private def structuredAnySourceReadRows
    (mkRow : Option Bool -> Structured.Transition) :
    List Structured.Transition :=
  [ mkRow none, mkRow (some false), mkRow (some true) ]

private def structuredRawBoundaryWriteOutputRow
    (source : Nat) (sourceRead : Option Bool) (tape1Read : Option Bool)
    (bit : Bool) (target : Nat)
    (tape0Action tape1Action : Structured.TapeAction) :
    Structured.Transition :=
  structuredRow source sourceRead tape1Read none
    tape0Action
    tape1Action
    (structuredWriteBit bit Structured.HeadMove.right)
    target

private def structuredRawBoundaryHeaderRows
    (source target : Nat) :
    List Structured.Transition :=
  structuredAnySourceReadRows fun sourceRead =>
    structuredRawBoundaryWriteOutputRow source sourceRead none false target
      structuredStay
      structuredStay

private def structuredRawBoundaryCountRow
    (read : Bool) : Structured.Transition :=
  structuredRow 10 (some read) none none
    (structuredPreserve Structured.HeadMove.right)
    (structuredWriteBit true Structured.HeadMove.right)
    structuredStay
    10

private def structuredRawBoundaryCountDoneRow : Structured.Transition :=
  structuredRow 10 none none none
    structuredStay
    (structuredPreserve Structured.HeadMove.left)
    structuredStay
    20

private def structuredRawBoundaryLengthMarkerRows
    (source : Nat) (bit : Bool) (target : Nat)
    (moveTape1 : Structured.HeadMove := Structured.HeadMove.stay) :
    List Structured.Transition :=
  [ structuredRawBoundaryWriteOutputRow source none (some true) bit target
      structuredStay
      (structuredPreserve moveTape1) ]

private def structuredRawBoundaryLengthFinalRows
    (source : Nat) (bit : Bool) (target : Nat)
    (moveTape0 : Structured.HeadMove := Structured.HeadMove.stay) :
    List Structured.Transition :=
  [ structuredRawBoundaryWriteOutputRow source none none bit target
      (structuredPreserve moveTape0)
      structuredStay ]

private def structuredRawBoundaryRewindRow
    (read : Bool) : Structured.Transition :=
  structuredRow 41 (some read) none none
    (structuredPreserve Structured.HeadMove.left)
    structuredStay
    structuredStay
    41

private def structuredRawBoundaryRewindDoneRow : Structured.Transition :=
  structuredRow 41 none none none
    (structuredPreserve Structured.HeadMove.right)
    structuredStay
    structuredStay
    50

private def structuredRawBoundaryCellLoopInitialRow
    (read : Bool) (target : Nat) : Structured.Transition :=
  structuredRow 50 (some read) none none
    (structuredPreserve Structured.HeadMove.right)
    structuredStay
    (structuredWriteBit false Structured.HeadMove.right)
    target

private def structuredRawBoundaryCellLoopHaltRow :
    Structured.Transition :=
  structuredRow 50 none none none
    structuredStay
    structuredStay
    structuredStay
    99

/--
Three-tape structured source for the full logical raw-boundary right-edge
emitter.

The routine emits the header bits, counts the raw layout on tape 1, emits the
length field from that count, rewinds tape 0, and then emits the encoded
per-cell suffix.  It is intentionally written in the fragment accepted by
{name}`Structured.MultiTapeLowering.supportsReadWriteRows3`.
-/
def structuredRawBoundaryRightEdgeEmitterDescription :
    Structured.Description where
  tapeCount := 3
  stateCount := 100
  start := 0
  halt := 99
  transitions :=
    structuredRawBoundaryHeaderRows 0 1 ++
    structuredRawBoundaryHeaderRows 1 2 ++
    structuredRawBoundaryHeaderRows 2 3 ++
    structuredRawBoundaryHeaderRows 3 10 ++
    [ structuredRawBoundaryCountRow false
    , structuredRawBoundaryCountRow true
    , structuredRawBoundaryCountDoneRow ] ++
    structuredRawBoundaryLengthMarkerRows 20 false 21 ++
    structuredRawBoundaryLengthMarkerRows 21 false 22 ++
    structuredRawBoundaryLengthMarkerRows 22 true 23 ++
    structuredRawBoundaryLengthMarkerRows 23 false 20
      Structured.HeadMove.left ++
    structuredRawBoundaryLengthFinalRows 20 false 31 ++
    structuredRawBoundaryLengthFinalRows 31 false 32 ++
    structuredRawBoundaryLengthFinalRows 32 true 33 ++
    structuredRawBoundaryLengthFinalRows 33 true 41
      Structured.HeadMove.left ++
    [ structuredRawBoundaryRewindRow false
    , structuredRawBoundaryRewindRow true
    , structuredRawBoundaryRewindDoneRow
    , structuredRawBoundaryCellLoopInitialRow false 51
    , structuredRawBoundaryCellLoopInitialRow true 61
    , structuredRawBoundaryCellLoopHaltRow ] ++
    structuredRawBoundaryCellEmitWriteRows 51 true 52 ++
    structuredRawBoundaryCellEmitWriteRows 52 false 53 ++
    structuredRawBoundaryCellEmitWriteRows 53 true 50 ++
    structuredRawBoundaryCellEmitWriteRows 61 true 62 ++
    structuredRawBoundaryCellEmitWriteRows 62 true 63 ++
    structuredRawBoundaryCellEmitWriteRows 63 false 50

theorem structuredRawBoundaryRightEdgeEmitterDescription_supportsReadWriteRows3 :
    Structured.MultiTapeLowering.supportsReadWriteRows3
      structuredRawBoundaryRightEdgeEmitterDescription = true := by
  decide

theorem structuredRawBoundaryRightEdgeEmitterDescription_supported :
    Structured.MultiTapeLowering.SupportsReadWriteRows3
      structuredRawBoundaryRightEdgeEmitterDescription :=
  Structured.MultiTapeLowering.supportedReadWriteRows3_of_supports_eq_true
    structuredRawBoundaryRightEdgeEmitterDescription_supportsReadWriteRows3

theorem structuredRawBoundaryRightEdgeEmitterDescription_wellFormed :
    structuredRawBoundaryRightEdgeEmitterDescription.WellFormed :=
  structuredDescription_wellFormed_of_bool
    structuredRawBoundaryRightEdgeEmitterDescription (by decide)

theorem structuredRawBoundaryRightEdgeEmitterDescription_haltTransitionFree :
    structuredRawBoundaryRightEdgeEmitterDescription.HaltTransitionFree :=
  structuredDescription_haltTransitionFree_of_bool
    structuredRawBoundaryRightEdgeEmitterDescription (by decide)

def loweredStructuredRawBoundaryRightEdgeEmitterDescription :
    MachineDescription :=
  Structured.MultiTapeLowering.lowerStructured3Description
    structuredRawBoundaryRightEdgeEmitterDescription

theorem loweredStructuredRawBoundaryRightEdgeEmitterDescription_subroutineReady :
    loweredStructuredRawBoundaryRightEdgeEmitterDescription.SubroutineReady := by
  simpa [loweredStructuredRawBoundaryRightEdgeEmitterDescription] using
    Structured.MultiTapeLowering.lowerStructured3Description_subroutineReady
      structuredRawBoundaryRightEdgeEmitterDescription_wellFormed
      structuredRawBoundaryRightEdgeEmitterDescription_supported

def structuredRawBoundaryRightEdgeEmitterSourceTapes
    (layout : Word Bool) : List (Tape Bool) :=
  [ Tape.input layout, Tape.blank, Tape.blank ]

def structuredRawBoundaryOutputTape
    (bits : Word Bool) : Tape Bool where
  left := bits.reverse.map some
  head := none
  right := []

def structuredRawBoundaryRightEdgeEmitterOutputTape
    (layout : Word Bool) : Tape Bool :=
  structuredRawBoundaryOutputTape (encodedLayoutBits layout)

theorem structuredRawBoundaryOutputTape_cells
    (bits : Word Bool) :
    Tape.cells (structuredRawBoundaryOutputTape bits) =
      bits.map some ++ [none] := by
  simp [structuredRawBoundaryOutputTape, Tape.cells]

theorem structuredRawBoundaryOutputTape_normalizedOutput
    (bits : Word Bool) :
    Tape.normalizedOutput (structuredRawBoundaryOutputTape bits) = bits := by
  rw [Tape.normalizedOutput, structuredRawBoundaryOutputTape_cells,
    List.filterMap_append]
  simpa using! Tape.filterMap_id_map_some bits

theorem structuredRawBoundaryRightEdgeEmitterOutputTape_normalizedOutput
    (layout : Word Bool) :
    Tape.normalizedOutput
        (structuredRawBoundaryRightEdgeEmitterOutputTape layout) =
      encodedLayoutBits layout := by
  simpa [structuredRawBoundaryRightEdgeEmitterOutputTape] using
    structuredRawBoundaryOutputTape_normalizedOutput (encodedLayoutBits layout)

private def structuredRawBoundarySourceScanTape
    (processed remaining : Word Bool) : Tape Bool :=
  tapeAtCells (processed.reverse.map some) (remaining.map some)

private def structuredRawBoundaryCountMarkerTape
    (markers : Nat) : Tape Bool :=
  tapeAtCells (List.replicate markers (some true)) []

private def structuredRawBoundaryLengthReadTape
    (markers : Nat) : Tape Bool :=
  Tape.move Direction.left
    (structuredRawBoundaryCountMarkerTape markers)

private def structuredRawBoundaryLengthDoneCounterTape
    (markers : Nat) : Tape Bool :=
  tapeAtCells []
    (none ::
      List.append (List.replicate markers (some true)) [none])

private def structuredRawBoundaryLengthPhaseTape
    (remaining emitted : Nat) : Tape Bool :=
  match remaining with
  | 0 => structuredRawBoundaryLengthDoneCounterTape emitted
  | remaining' + 1 =>
      tapeAtCells (List.replicate remaining' (some true))
        (some true ::
          List.append (List.replicate emitted (some true)) [none])

private def structuredRawBoundaryLengthTickBits : Word Bool :=
  [false, false, true, false]

private def structuredRawBoundaryLengthDoneBits : Word Bool :=
  [false, false, true, true]

private def structuredRawBoundaryCellLoopSourceTape
    (layout : Word Bool) : Tape Bool :=
  tapeAtCells [none] (List.append (layout.map some) [none])

theorem structuredRawBoundaryRightEdgeEmitterDescription_run_header
    (source : Tape Bool) :
    structuredRawBoundaryRightEdgeEmitterDescription.runConfig 4
        { state := structuredRawBoundaryRightEdgeEmitterDescription.start
          tapes := [source, Tape.blank, Tape.blank] } =
      { state := 10
        tapes :=
          [ source
          , Tape.blank
          , structuredRawBoundaryOutputTape
              [false, false, false, false] ] } := by
  cases source with
  | mk left head right =>
      cases head with
      | none =>
          three_tape_step [
            structuredRawBoundaryRightEdgeEmitterDescription,
            structuredRawBoundaryHeaderRows,
            structuredAnySourceReadRows,
            structuredRawBoundaryWriteOutputRow,
            structuredRawBoundaryOutputTape,
            structuredWriteBit]
      | some bit =>
          cases bit <;>
            three_tape_step [
              structuredRawBoundaryRightEdgeEmitterDescription,
              structuredRawBoundaryHeaderRows,
              structuredAnySourceReadRows,
              structuredRawBoundaryWriteOutputRow,
              structuredRawBoundaryOutputTape,
              structuredWriteBit]

private theorem structuredRawBoundaryRightEdgeEmitterDescription_run_count_done
    (processed outputBits : Word Bool) (markers : Nat) :
    structuredRawBoundaryRightEdgeEmitterDescription.runConfig 1
        { state := 10
          tapes :=
            [ structuredRawBoundarySourceScanTape processed []
            , structuredRawBoundaryCountMarkerTape markers
            , structuredRawBoundaryOutputTape outputBits ] } =
      { state := 20
        tapes :=
          [ structuredRawBoundarySourceScanTape processed []
          , structuredRawBoundaryLengthReadTape markers
          , structuredRawBoundaryOutputTape outputBits ] } := by
  three_tape_step [
    structuredRawBoundaryRightEdgeEmitterDescription,
    structuredRawBoundaryHeaderRows,
    structuredAnySourceReadRows,
    structuredRawBoundaryWriteOutputRow,
    structuredRawBoundarySourceScanTape,
    structuredRawBoundaryCountMarkerTape,
    structuredRawBoundaryLengthReadTape,
    structuredRawBoundaryOutputTape,
    structuredRawBoundaryCountRow,
    structuredRawBoundaryCountDoneRow,
    structuredPreserve]

private theorem structuredRawBoundaryRightEdgeEmitterDescription_run_count_bit
    (processed rest outputBits : Word Bool) (markers : Nat)
    (bit : Bool) :
    structuredRawBoundaryRightEdgeEmitterDescription.runConfig 1
        { state := 10
          tapes :=
            [ structuredRawBoundarySourceScanTape processed (bit :: rest)
            , structuredRawBoundaryCountMarkerTape markers
            , structuredRawBoundaryOutputTape outputBits ] } =
      { state := 10
        tapes :=
          [ structuredRawBoundarySourceScanTape
              (List.append processed [bit]) rest
          , structuredRawBoundaryCountMarkerTape markers.succ
          , structuredRawBoundaryOutputTape outputBits ] } := by
  cases bit <;>
    three_tape_step [
      structuredRawBoundaryRightEdgeEmitterDescription,
      structuredRawBoundaryHeaderRows,
      structuredAnySourceReadRows,
      structuredRawBoundaryWriteOutputRow,
      structuredRawBoundarySourceScanTape,
      structuredRawBoundaryCountMarkerTape,
      structuredRawBoundaryOutputTape,
      structuredRawBoundaryCountRow,
      structuredPreserve, structuredWriteBit,
      List.reverse_append, List.replicate_succ]
  all_goals
    cases List.map some rest <;> rfl

private theorem structuredRawBoundaryRightEdgeEmitterDescription_run_count_loop
    (processed remaining : Word Bool) (markers : Nat)
    (outputBits : Word Bool) :
    structuredRawBoundaryRightEdgeEmitterDescription.runConfig
        (remaining.length + 1)
        { state := 10
          tapes :=
            [ structuredRawBoundarySourceScanTape processed remaining
            , structuredRawBoundaryCountMarkerTape markers
            , structuredRawBoundaryOutputTape outputBits ] } =
      { state := 20
        tapes :=
          [ structuredRawBoundarySourceScanTape
              (List.append processed remaining) []
          , structuredRawBoundaryLengthReadTape
              (markers + remaining.length)
          , structuredRawBoundaryOutputTape outputBits ] } := by
  induction remaining generalizing processed markers with
  | nil =>
      simpa using
        structuredRawBoundaryRightEdgeEmitterDescription_run_count_done
          processed outputBits markers
  | cons bit rest ih =>
      refine
        Structured.MultiTapeLowering.ThreeTape.runConfig_chain2_of_eq
          (D := structuredRawBoundaryRightEdgeEmitterDescription)
          (m := rest.length + 1)
          (htotal := ?_)
          (structuredRawBoundaryRightEdgeEmitterDescription_run_count_bit
            processed rest outputBits markers bit)
          ?_
      · simp [Nat.add_comm, Nat.add_left_comm]
      · simpa [List.append_assoc, Nat.succ_eq_add_one,
          Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using
          ih (List.append processed [bit]) markers.succ

private theorem structuredRawBoundaryRightEdgeEmitterDescription_run_count
    (layout outputBits : Word Bool) :
    structuredRawBoundaryRightEdgeEmitterDescription.runConfig
        (layout.length + 1)
        { state := 10
          tapes :=
            [ Tape.input layout
            , Tape.blank
            , structuredRawBoundaryOutputTape outputBits ] } =
      { state := 20
        tapes :=
          [ structuredRawBoundarySourceScanTape layout []
          , structuredRawBoundaryLengthReadTape layout.length
          , structuredRawBoundaryOutputTape outputBits ] } := by
  cases layout with
  | nil =>
      simpa [structuredRawBoundarySourceScanTape,
        structuredRawBoundaryCountMarkerTape,
        structuredRawBoundaryLengthReadTape,
        Tape.input, Tape.blank] using!
        structuredRawBoundaryRightEdgeEmitterDescription_run_count_loop
          [] [] 0 outputBits
  | cons bit rest =>
      simpa [structuredRawBoundarySourceScanTape,
        structuredRawBoundaryCountMarkerTape,
        structuredRawBoundaryLengthReadTape,
        Tape.input, Tape.blank] using!
        structuredRawBoundaryRightEdgeEmitterDescription_run_count_loop
          [] (bit :: rest) 0 outputBits

private theorem structuredRawBoundaryRightEdgeEmitterDescription_run_length_marker
    (remaining emitted : Nat) (sourceLeft : List (Option Bool))
    (outputBits : Word Bool) :
    structuredRawBoundaryRightEdgeEmitterDescription.runConfig 4
        { state := 20
          tapes :=
            [ tapeAtCells sourceLeft []
            , structuredRawBoundaryLengthPhaseTape remaining.succ emitted
            , structuredRawBoundaryOutputTape outputBits ] } =
      { state := 20
        tapes :=
          [ tapeAtCells sourceLeft []
          , structuredRawBoundaryLengthPhaseTape remaining emitted.succ
          , structuredRawBoundaryOutputTape
              (List.append outputBits
                structuredRawBoundaryLengthTickBits) ] } := by
  cases remaining <;>
    three_tape_step [
      structuredRawBoundaryRightEdgeEmitterDescription,
      structuredRawBoundaryHeaderRows,
      structuredAnySourceReadRows,
      structuredRawBoundaryWriteOutputRow,
      structuredRawBoundaryLengthPhaseTape,
      structuredRawBoundaryLengthDoneCounterTape,
      structuredRawBoundaryOutputTape,
      structuredRawBoundaryLengthTickBits,
      structuredRawBoundaryCountRow,
      structuredRawBoundaryCountDoneRow,
      structuredRawBoundaryLengthMarkerRows,
      structuredRawBoundaryLengthFinalRows,
      structuredPreserve, structuredWriteBit,
      List.reverse_append, List.replicate_succ,
      List.append_assoc]

private theorem structuredRawBoundaryRightEdgeEmitterDescription_run_length_final
    (emitted : Nat) (sourceLeft : List (Option Bool))
    (outputBits : Word Bool) :
    structuredRawBoundaryRightEdgeEmitterDescription.runConfig 4
        { state := 20
          tapes :=
            [ tapeAtCells sourceLeft []
            , structuredRawBoundaryLengthPhaseTape 0 emitted
            , structuredRawBoundaryOutputTape outputBits ] } =
      { state := 41
        tapes :=
          [ Tape.move Direction.left (tapeAtCells sourceLeft [])
          , structuredRawBoundaryLengthDoneCounterTape emitted
          , structuredRawBoundaryOutputTape
              (List.append outputBits
                structuredRawBoundaryLengthDoneBits) ] } := by
  three_tape_step [
    structuredRawBoundaryRightEdgeEmitterDescription,
    structuredRawBoundaryHeaderRows,
    structuredAnySourceReadRows,
    structuredRawBoundaryWriteOutputRow,
    structuredRawBoundaryLengthPhaseTape,
    structuredRawBoundaryLengthDoneCounterTape,
    structuredRawBoundaryOutputTape,
    structuredRawBoundaryLengthDoneBits,
    structuredRawBoundaryCountRow,
    structuredRawBoundaryCountDoneRow,
    structuredRawBoundaryLengthMarkerRows,
    structuredRawBoundaryLengthFinalRows,
    structuredPreserve, structuredWriteBit,
    List.reverse_append, List.append_assoc]

private theorem structuredRawBoundaryRightEdgeEmitterDescription_run_length_loop
    (remaining emitted : Nat) (sourceLeft : List (Option Bool))
    (outputBits : Word Bool) :
    structuredRawBoundaryRightEdgeEmitterDescription.runConfig
        (4 * remaining + 4)
        { state := 20
          tapes :=
            [ tapeAtCells sourceLeft []
            , structuredRawBoundaryLengthPhaseTape remaining emitted
            , structuredRawBoundaryOutputTape outputBits ] } =
      { state := 41
        tapes :=
          [ Tape.move Direction.left (tapeAtCells sourceLeft [])
          , structuredRawBoundaryLengthDoneCounterTape
              (emitted + remaining)
          , structuredRawBoundaryOutputTape
              (List.append outputBits
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  remaining)) ] } := by
  induction remaining generalizing emitted outputBits with
  | zero =>
      simpa [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_zero] using!
        structuredRawBoundaryRightEdgeEmitterDescription_run_length_final
          emitted sourceLeft outputBits
  | succ remaining ih =>
      refine
        Structured.MultiTapeLowering.ThreeTape.runConfig_chain2_of_eq
          (D := structuredRawBoundaryRightEdgeEmitterDescription)
          (m := 4 * remaining + 4)
          (htotal := ?_)
          (structuredRawBoundaryRightEdgeEmitterDescription_run_length_marker
            remaining emitted sourceLeft outputBits)
          ?_
      · lia
      · simpa [structuredRawBoundaryLengthTickBits,
          DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ,
          List.append_assoc, Nat.succ_eq_add_one, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using
          ih emitted.succ
            (List.append outputBits structuredRawBoundaryLengthTickBits)

private theorem structuredRawBoundaryLengthReadTape_eq_phaseTape
    (markers : Nat) :
    structuredRawBoundaryLengthReadTape markers =
      structuredRawBoundaryLengthPhaseTape markers 0 := by
  cases markers <;>
    simp [structuredRawBoundaryLengthReadTape,
      structuredRawBoundaryLengthPhaseTape,
      structuredRawBoundaryCountMarkerTape,
      structuredRawBoundaryLengthDoneCounterTape,
      Tape.move, Tape.moveLeft, tapeAtCells, List.replicate_succ]

private theorem structuredRawBoundaryRightEdgeEmitterDescription_run_length
    (layout outputBits : Word Bool) :
    structuredRawBoundaryRightEdgeEmitterDescription.runConfig
        (4 * layout.length + 4)
        { state := 20
          tapes :=
            [ structuredRawBoundarySourceScanTape layout []
            , structuredRawBoundaryLengthReadTape layout.length
            , structuredRawBoundaryOutputTape outputBits ] } =
      { state := 41
        tapes :=
          [ Tape.move Direction.left
              (structuredRawBoundarySourceScanTape layout [])
          , structuredRawBoundaryLengthDoneCounterTape layout.length
          , structuredRawBoundaryOutputTape
              (List.append outputBits
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  layout.length)) ] } := by
  simpa [structuredRawBoundarySourceScanTape,
    structuredRawBoundaryLengthReadTape_eq_phaseTape] using
    structuredRawBoundaryRightEdgeEmitterDescription_run_length_loop
      layout.length 0 (layout.reverse.map some) outputBits

private theorem structuredRawBoundaryRightEdgeEmitterDescription_run_header_count_length
    (layout : Word Bool) :
    structuredRawBoundaryRightEdgeEmitterDescription.runConfig
        (4 + ((layout.length + 1) + (4 * layout.length + 4)))
        { state := structuredRawBoundaryRightEdgeEmitterDescription.start
          tapes := [Tape.input layout, Tape.blank, Tape.blank] } =
      { state := 41
        tapes :=
          [ Tape.move Direction.left
              (structuredRawBoundarySourceScanTape layout [])
          , structuredRawBoundaryLengthDoneCounterTape layout.length
          , structuredRawBoundaryOutputTape
              (List.append [false, false, false, false]
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  layout.length)) ] } := by
  exact
    Structured.MultiTapeLowering.ThreeTape.runConfig_chain3_of_eq
      (D := structuredRawBoundaryRightEdgeEmitterDescription)
      (htotal := by lia)
      (structuredRawBoundaryRightEdgeEmitterDescription_run_header
        (Tape.input layout))
      (structuredRawBoundaryRightEdgeEmitterDescription_run_count
        layout [false, false, false, false])
      (structuredRawBoundaryRightEdgeEmitterDescription_run_length
        layout [false, false, false, false])

private def structuredRawBoundaryRewindTapeRev
    (remainingRev skipped : Word Bool) : Tape Bool :=
  match remainingRev with
  | [] =>
      tapeAtCells []
        (none :: List.append (skipped.map some) [none])
  | bit :: rest =>
      tapeAtCells (rest.map some)
        (some bit :: List.append (skipped.map some) [none])

private theorem structuredRawBoundaryRightEdgeEmitterDescription_run_rewind_bit
    (bit : Bool) (remainingRev skipped : Word Bool)
    (markers : Nat) (outputBits : Word Bool) :
    structuredRawBoundaryRightEdgeEmitterDescription.runConfig 1
        { state := 41
          tapes :=
            [ structuredRawBoundaryRewindTapeRev
                (bit :: remainingRev) skipped
            , structuredRawBoundaryLengthDoneCounterTape markers
            , structuredRawBoundaryOutputTape outputBits ] } =
      { state := 41
        tapes :=
          [ structuredRawBoundaryRewindTapeRev
              remainingRev (bit :: skipped)
          , structuredRawBoundaryLengthDoneCounterTape markers
          , structuredRawBoundaryOutputTape outputBits ] } := by
  cases bit <;> cases remainingRev <;>
    three_tape_step [
      structuredRawBoundaryRightEdgeEmitterDescription,
      structuredRawBoundaryHeaderRows,
      structuredAnySourceReadRows,
      structuredRawBoundaryWriteOutputRow,
      structuredRawBoundaryRewindTapeRev,
      structuredRawBoundaryLengthDoneCounterTape,
      structuredRawBoundaryOutputTape,
      structuredRawBoundaryCountRow,
      structuredRawBoundaryCountDoneRow,
      structuredRawBoundaryLengthMarkerRows,
      structuredRawBoundaryLengthFinalRows,
      structuredRawBoundaryRewindRow,
      structuredRawBoundaryRewindDoneRow,
      structuredPreserve, structuredWriteBit,
      List.append_assoc]

private theorem structuredRawBoundaryRightEdgeEmitterDescription_run_rewind_done
    (skipped : Word Bool) (markers : Nat) (outputBits : Word Bool) :
    structuredRawBoundaryRightEdgeEmitterDescription.runConfig 1
        { state := 41
          tapes :=
            [ structuredRawBoundaryRewindTapeRev [] skipped
            , structuredRawBoundaryLengthDoneCounterTape markers
            , structuredRawBoundaryOutputTape outputBits ] } =
      { state := 50
        tapes :=
          [ structuredRawBoundaryCellLoopSourceTape skipped
          , structuredRawBoundaryLengthDoneCounterTape markers
          , structuredRawBoundaryOutputTape outputBits ] } := by
  cases skipped <;>
    three_tape_step [
      structuredRawBoundaryRightEdgeEmitterDescription,
      structuredRawBoundaryHeaderRows,
      structuredAnySourceReadRows,
      structuredRawBoundaryWriteOutputRow,
      structuredRawBoundaryRewindTapeRev,
      structuredRawBoundaryCellLoopSourceTape,
      structuredRawBoundaryLengthDoneCounterTape,
      structuredRawBoundaryOutputTape,
      structuredRawBoundaryCountRow,
      structuredRawBoundaryCountDoneRow,
      structuredRawBoundaryLengthMarkerRows,
      structuredRawBoundaryLengthFinalRows,
      structuredRawBoundaryRewindRow,
      structuredRawBoundaryRewindDoneRow,
      structuredPreserve, structuredWriteBit,
      List.append_assoc]

private theorem structuredRawBoundaryRightEdgeEmitterDescription_run_rewind_loop
    (remainingRev skipped : Word Bool) (markers : Nat)
    (outputBits : Word Bool) :
    structuredRawBoundaryRightEdgeEmitterDescription.runConfig
        (remainingRev.length + 1)
        { state := 41
          tapes :=
            [ structuredRawBoundaryRewindTapeRev remainingRev skipped
            , structuredRawBoundaryLengthDoneCounterTape markers
            , structuredRawBoundaryOutputTape outputBits ] } =
      { state := 50
        tapes :=
          [ structuredRawBoundaryCellLoopSourceTape
              (List.append remainingRev.reverse skipped)
          , structuredRawBoundaryLengthDoneCounterTape markers
          , structuredRawBoundaryOutputTape outputBits ] } := by
  induction remainingRev generalizing skipped with
  | nil =>
      simpa using
        structuredRawBoundaryRightEdgeEmitterDescription_run_rewind_done
          skipped markers outputBits
  | cons bit rest ih =>
      refine
        Structured.MultiTapeLowering.ThreeTape.runConfig_chain2_of_eq
          (D := structuredRawBoundaryRightEdgeEmitterDescription)
          (m := rest.length + 1)
          (htotal := ?_)
          (structuredRawBoundaryRightEdgeEmitterDescription_run_rewind_bit
            bit rest skipped markers outputBits)
          ?_
      · simp [Nat.add_comm, Nat.add_left_comm]
      · simpa [List.append_assoc] using
          ih (bit :: skipped)

private theorem structuredRawBoundaryRightEdgeEmitterDescription_run_rewind
    (layout outputBits : Word Bool) :
    structuredRawBoundaryRightEdgeEmitterDescription.runConfig
        (layout.length + 1)
        { state := 41
          tapes :=
            [ Tape.move Direction.left
                (structuredRawBoundarySourceScanTape layout [])
            , structuredRawBoundaryLengthDoneCounterTape layout.length
            , structuredRawBoundaryOutputTape outputBits ] } =
      { state := 50
        tapes :=
          [ structuredRawBoundaryCellLoopSourceTape layout
          , structuredRawBoundaryLengthDoneCounterTape layout.length
          , structuredRawBoundaryOutputTape outputBits ] } := by
  have hstart :
      Tape.move Direction.left
          (structuredRawBoundarySourceScanTape layout []) =
        structuredRawBoundaryRewindTapeRev layout.reverse [] := by
    cases hrev : layout.reverse <;>
      simp [structuredRawBoundarySourceScanTape,
        structuredRawBoundaryRewindTapeRev,
        Tape.move, Tape.moveLeft, tapeAtCells, hrev]
  rw [hstart]
  simpa [List.length_reverse] using
    structuredRawBoundaryRightEdgeEmitterDescription_run_rewind_loop
      layout.reverse [] layout.length outputBits

private theorem structuredRawBoundaryRightEdgeEmitterDescription_run_to_cell_loop
    (layout : Word Bool) :
    structuredRawBoundaryRightEdgeEmitterDescription.runConfig
        ((4 + ((layout.length + 1) + (4 * layout.length + 4))) +
          (layout.length + 1))
        { state := structuredRawBoundaryRightEdgeEmitterDescription.start
          tapes := [Tape.input layout, Tape.blank, Tape.blank] } =
      { state := 50
        tapes :=
          [ structuredRawBoundaryCellLoopSourceTape layout
          , structuredRawBoundaryLengthDoneCounterTape layout.length
          , structuredRawBoundaryOutputTape
              (List.append [false, false, false, false]
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  layout.length)) ] } := by
  exact
    Structured.MultiTapeLowering.ThreeTape.runConfig_chain2
      (structuredRawBoundaryRightEdgeEmitterDescription_run_header_count_length
        layout)
      (structuredRawBoundaryRightEdgeEmitterDescription_run_rewind
        layout
        (List.append [false, false, false, false]
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            layout.length)))

private def structuredRawBoundaryCellLoopTape
    (processedRev remaining : Word Bool) : Tape Bool :=
  tapeAtCells (List.append (processedRev.map some) [none])
    (List.append (remaining.map some) [none])

private def structuredRawBoundaryCellChunkBits (bit : Bool) : Word Bool :=
  if bit then preservingCellPassOneBits else preservingCellPassZeroBits

private theorem structuredRawBoundaryCellLoopSourceTape_eq_loopTape
    (layout : Word Bool) :
    structuredRawBoundaryCellLoopSourceTape layout =
      structuredRawBoundaryCellLoopTape [] layout := by
  rfl

private theorem structuredRawBoundaryRightEdgeEmitterDescription_run_cell_bit
    (bit : Bool) (processedRev rest : Word Bool)
    (markers : Nat) (outputBits : Word Bool) :
    structuredRawBoundaryRightEdgeEmitterDescription.runConfig 4
        { state := 50
          tapes :=
            [ structuredRawBoundaryCellLoopTape
                processedRev (bit :: rest)
            , structuredRawBoundaryLengthDoneCounterTape markers
            , structuredRawBoundaryOutputTape outputBits ] } =
      { state := 50
        tapes :=
          [ structuredRawBoundaryCellLoopTape
              (bit :: processedRev) rest
          , structuredRawBoundaryLengthDoneCounterTape markers
          , structuredRawBoundaryOutputTape
              (List.append outputBits
                (structuredRawBoundaryCellChunkBits bit)) ] } := by
  cases bit <;> cases rest <;> (try cases ‹Bool›) <;>
    three_tape_step [
      structuredRawBoundaryRightEdgeEmitterDescription,
      structuredRawBoundaryHeaderRows,
      structuredAnySourceReadRows,
      structuredRawBoundaryWriteOutputRow,
      structuredRawBoundaryCellLoopTape,
      structuredRawBoundaryLengthDoneCounterTape,
      structuredRawBoundaryOutputTape,
      structuredRawBoundaryCellChunkBits,
      preservingCellPassZeroBits,
      preservingCellPassOneBits,
      structuredRawBoundaryCountRow,
      structuredRawBoundaryCountDoneRow,
      structuredRawBoundaryLengthMarkerRows,
      structuredRawBoundaryLengthFinalRows,
      structuredRawBoundaryRewindRow,
      structuredRawBoundaryRewindDoneRow,
      structuredRawBoundaryCellLoopInitialRow,
      structuredRawBoundaryCellLoopHaltRow,
      structuredRawBoundaryCellEmitWriteRows,
      structuredRawBoundaryCellEmitWriteRow,
      structuredPreserve, structuredWriteBit,
      List.reverse_append]

private theorem structuredRawBoundaryRightEdgeEmitterDescription_run_cell_done
    (processedRev : Word Bool) (markers : Nat) (outputBits : Word Bool) :
    structuredRawBoundaryRightEdgeEmitterDescription.runConfig 1
        { state := 50
          tapes :=
            [ structuredRawBoundaryCellLoopTape processedRev []
            , structuredRawBoundaryLengthDoneCounterTape markers
            , structuredRawBoundaryOutputTape outputBits ] } =
      { state := structuredRawBoundaryRightEdgeEmitterDescription.halt
        tapes :=
          [ structuredRawBoundaryCellLoopTape processedRev []
          , structuredRawBoundaryLengthDoneCounterTape markers
          , structuredRawBoundaryOutputTape outputBits ] } := by
  three_tape_step [
    structuredRawBoundaryRightEdgeEmitterDescription,
    structuredRawBoundaryHeaderRows,
    structuredAnySourceReadRows,
    structuredRawBoundaryWriteOutputRow,
    structuredRawBoundaryCellLoopTape,
    structuredRawBoundaryLengthDoneCounterTape,
    structuredRawBoundaryOutputTape,
    structuredRawBoundaryCountRow,
    structuredRawBoundaryCountDoneRow,
    structuredRawBoundaryLengthMarkerRows,
    structuredRawBoundaryLengthFinalRows,
    structuredRawBoundaryRewindRow,
    structuredRawBoundaryRewindDoneRow,
    structuredRawBoundaryCellLoopInitialRow,
    structuredRawBoundaryCellLoopHaltRow,
    structuredPreserve, structuredWriteBit]

private theorem structuredRawBoundaryRightEdgeEmitterDescription_run_cell_loop
    (processedRev remaining : Word Bool) (markers : Nat)
    (outputBits : Word Bool) :
    structuredRawBoundaryRightEdgeEmitterDescription.runConfig
        (4 * remaining.length + 1)
        { state := 50
          tapes :=
            [ structuredRawBoundaryCellLoopTape processedRev remaining
            , structuredRawBoundaryLengthDoneCounterTape markers
            , structuredRawBoundaryOutputTape outputBits ] } =
      { state := structuredRawBoundaryRightEdgeEmitterDescription.halt
        tapes :=
          [ structuredRawBoundaryCellLoopTape
              (List.append remaining.reverse processedRev) []
          , structuredRawBoundaryLengthDoneCounterTape markers
          , structuredRawBoundaryOutputTape
              (List.append outputBits
                (preservingCellPassCellBits remaining)) ] } := by
  induction remaining generalizing processedRev outputBits with
  | nil =>
      simpa [preservingCellPassCellBits] using
        structuredRawBoundaryRightEdgeEmitterDescription_run_cell_done
          processedRev markers outputBits
  | cons bit rest ih =>
      refine
        Structured.MultiTapeLowering.ThreeTape.runConfig_chain2_of_eq
          (D := structuredRawBoundaryRightEdgeEmitterDescription)
          (m := 4 * rest.length + 1)
          (htotal := ?_)
          (structuredRawBoundaryRightEdgeEmitterDescription_run_cell_bit
            bit processedRev rest markers outputBits)
          ?_
      · simp
        lia
      cases bit
      · simpa [structuredRawBoundaryCellChunkBits,
          preservingCellPassCellBits,
          preservingCellPassZeroBits,
          preservingCellPassOneBits,
          List.append_assoc] using
          ih (false :: processedRev)
            (List.append outputBits
              (structuredRawBoundaryCellChunkBits false))
      · simpa [structuredRawBoundaryCellChunkBits,
          preservingCellPassCellBits,
          preservingCellPassZeroBits,
          preservingCellPassOneBits,
          List.append_assoc] using
          ih (true :: processedRev)
            (List.append outputBits
              (structuredRawBoundaryCellChunkBits true))

private theorem structuredRawBoundaryRightEdgeEmitterDescription_run_cells
    (layout outputBits : Word Bool) :
    structuredRawBoundaryRightEdgeEmitterDescription.runConfig
        (4 * layout.length + 1)
        { state := 50
          tapes :=
            [ structuredRawBoundaryCellLoopSourceTape layout
            , structuredRawBoundaryLengthDoneCounterTape layout.length
            , structuredRawBoundaryOutputTape outputBits ] } =
      { state := structuredRawBoundaryRightEdgeEmitterDescription.halt
        tapes :=
          [ structuredRawBoundaryCellLoopTape layout.reverse []
          , structuredRawBoundaryLengthDoneCounterTape layout.length
          , structuredRawBoundaryOutputTape
              (List.append outputBits
                (preservingCellPassCellBits layout)) ] } := by
  simpa [structuredRawBoundaryCellLoopSourceTape_eq_loopTape] using
    structuredRawBoundaryRightEdgeEmitterDescription_run_cell_loop
      [] layout layout.length outputBits

theorem structuredRawBoundaryRightEdgeEmitterDescription_run
    (layout : Word Bool) :
    structuredRawBoundaryRightEdgeEmitterDescription.runConfig
        (10 * layout.length + 11)
        { state := structuredRawBoundaryRightEdgeEmitterDescription.start
          tapes := structuredRawBoundaryRightEdgeEmitterSourceTapes layout } =
      { state := structuredRawBoundaryRightEdgeEmitterDescription.halt
        tapes :=
          [ structuredRawBoundaryCellLoopTape layout.reverse []
          , structuredRawBoundaryLengthDoneCounterTape layout.length
          , structuredRawBoundaryRightEdgeEmitterOutputTape layout ] } := by
  rw [show 10 * layout.length + 11 =
      ((4 + ((layout.length + 1) + (4 * layout.length + 4))) +
        (layout.length + 1)) +
        (4 * layout.length + 1) by
    lia]
  simp [structuredRawBoundaryRightEdgeEmitterSourceTapes]
  rw [Structured.MultiTapeLowering.ThreeTape.runConfig_chain2
    (structuredRawBoundaryRightEdgeEmitterDescription_run_to_cell_loop layout)
    (structuredRawBoundaryRightEdgeEmitterDescription_run_cells
      layout
      (List.append [false, false, false, false]
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          layout.length)))]
  simp [structuredRawBoundaryRightEdgeEmitterOutputTape,
    encodedLayoutBits_eq_header_length_cells,
    encodeCodeSymbolAsInput]

def structuredRawBoundaryRightEdgeEmitterFinalTapes
    (layout : Word Bool) : List (Tape Bool) :=
  [ structuredRawBoundaryCellLoopTape layout.reverse []
  , structuredRawBoundaryLengthDoneCounterTape layout.length
  , structuredRawBoundaryRightEdgeEmitterOutputTape layout ]

theorem loweredStructuredRawBoundaryRightEdgeEmitterDescription_haltsFrom_structuredTapes
    (layout : Word Bool) :
    loweredStructuredRawBoundaryRightEdgeEmitterDescription.HaltsFromTapeEquiv
      (Structured.MultiTapeLowering.encodedGuardedStructuredTapes
        (structuredRawBoundaryRightEdgeEmitterSourceTapes layout))
      (Structured.MultiTapeLowering.encodedGuardedStructuredTapes
        (structuredRawBoundaryRightEdgeEmitterFinalTapes layout)) := by
  simpa [loweredStructuredRawBoundaryRightEdgeEmitterDescription,
    structuredRawBoundaryRightEdgeEmitterFinalTapes] using
    Structured.MultiTapeLowering.lowerStructured3Description_haltsFromConfigWithTapes
      structuredRawBoundaryRightEdgeEmitterDescription_wellFormed
      structuredRawBoundaryRightEdgeEmitterDescription_haltTransitionFree
      structuredRawBoundaryRightEdgeEmitterDescription_supported
      (c :=
        { state := structuredRawBoundaryRightEdgeEmitterDescription.start
          tapes := structuredRawBoundaryRightEdgeEmitterSourceTapes layout })
      (tapes := structuredRawBoundaryRightEdgeEmitterFinalTapes layout)
      rfl
      (by
        simp [structuredRawBoundaryRightEdgeEmitterSourceTapes,
          structuredRawBoundaryRightEdgeEmitterDescription])
      ⟨10 * layout.length + 11,
        by
          simpa [structuredRawBoundaryRightEdgeEmitterFinalTapes] using
            structuredRawBoundaryRightEdgeEmitterDescription_run layout⟩

theorem structuredRawBoundaryRightEdgeEmitterDescription_run_empty_halts :
    (structuredRawBoundaryRightEdgeEmitterDescription.runConfig 11
        { state := structuredRawBoundaryRightEdgeEmitterDescription.start
          tapes := structuredRawBoundaryRightEdgeEmitterSourceTapes [] }).state =
      structuredRawBoundaryRightEdgeEmitterDescription.halt := by
  decide

theorem structuredRawBoundaryRightEdgeEmitterDescription_run_empty_output :
    Structured.Description.tapeAt
        (structuredRawBoundaryRightEdgeEmitterDescription.runConfig 11
          { state := structuredRawBoundaryRightEdgeEmitterDescription.start
            tapes := structuredRawBoundaryRightEdgeEmitterSourceTapes [] }).tapes
        2 =
      structuredRawBoundaryRightEdgeEmitterOutputTape [] := by
  decide

theorem structuredRawBoundaryRightEdgeEmitterDescription_run_false_halts :
    (structuredRawBoundaryRightEdgeEmitterDescription.runConfig 21
        { state := structuredRawBoundaryRightEdgeEmitterDescription.start
          tapes := structuredRawBoundaryRightEdgeEmitterSourceTapes [false] }).state =
      structuredRawBoundaryRightEdgeEmitterDescription.halt := by
  decide

theorem structuredRawBoundaryRightEdgeEmitterDescription_run_false_output :
    Structured.Description.tapeAt
        (structuredRawBoundaryRightEdgeEmitterDescription.runConfig 21
          { state := structuredRawBoundaryRightEdgeEmitterDescription.start
            tapes := structuredRawBoundaryRightEdgeEmitterSourceTapes [false] }).tapes
        2 =
      structuredRawBoundaryRightEdgeEmitterOutputTape [false] := by
  decide

theorem structuredRawBoundaryRightEdgeEmitterDescription_run_true_halts :
    (structuredRawBoundaryRightEdgeEmitterDescription.runConfig 21
        { state := structuredRawBoundaryRightEdgeEmitterDescription.start
          tapes := structuredRawBoundaryRightEdgeEmitterSourceTapes [true] }).state =
      structuredRawBoundaryRightEdgeEmitterDescription.halt := by
  decide

theorem structuredRawBoundaryRightEdgeEmitterDescription_run_true_output :
    Structured.Description.tapeAt
        (structuredRawBoundaryRightEdgeEmitterDescription.runConfig 21
          { state := structuredRawBoundaryRightEdgeEmitterDescription.start
            tapes := structuredRawBoundaryRightEdgeEmitterSourceTapes [true] }).tapes
        2 =
      structuredRawBoundaryRightEdgeEmitterOutputTape [true] := by
  decide

private theorem tapeAtCells_moveRight_moveLeft_append_headerBits
    (pref right : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tapeAtCells
            (List.append pref
              [some false, some false, some false, some false])
            right)) =
      tapeAtCells
        (List.append pref
          [some false, some false, some false, some false])
        right := by
  cases pref <;> cases right <;>
    simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem preRewindTape_moveRight
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.right
        (preRewindTape skipped count tailFirst tail) =
      rightEdgeTape skipped count tailFirst tail := by
  rw [preRewindTape, rightEdgeTape, encodedLayoutBits]
  change
    Tape.move Direction.right
        (Tape.move Direction.left
          (tapeAtCells
            ((encodeCodeWordAsInput
              (MachineCodeSymbol.header ::
                encodeBoolWordAppend (List.append skipped count) [])).reverse.map
              some)
            (some tailFirst :: tail))) =
      tapeAtCells
        ((encodeCodeWordAsInput
          (MachineCodeSymbol.header ::
            encodeBoolWordAppend (List.append skipped count) [])).reverse.map
          some)
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
  exact
    tapeAtCells_moveRight_moveLeft_append_headerBits
      ((encodeCodeWordAsInput
        (encodeBoolWordAppend (List.append skipped count) [])).reverse.map
        some)
      (some tailFirst :: tail)

theorem rightEdgeTape_rewind_haltsFromTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    rightEdgeRewindDescription.HaltsFromTape
      (rightEdgeTape skipped count tailFirst tail)
      (tapeAtCells [none]
        (List.append
          ((encodedLayoutBits (List.append skipped count)).map some)
          (some tailFirst :: tail))) := by
  simpa [rightEdgeTape] using
    rightEdgeRewindDescription_haltsFrom_rightEdge_noDelimiter
      (encodedLayoutBits (List.append skipped count))
      tailFirst tail

theorem rightEdgeTape_rewind_target_cells
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.cells
        (tapeAtCells [none]
          (List.append
            ((encodedLayoutBits (List.append skipped count)).map some)
            (some tailFirst :: tail))) =
      none ::
        List.append
          ((encodedLayoutBits (List.append skipped count)).map some)
          (some tailFirst :: tail) := by
  rw [encodedLayoutBits]
  change
    Tape.cells
        (tapeAtCells [none]
          (List.append
            ((encodeCodeWordAsInput
              (MachineCodeSymbol.header ::
                encodeBoolWordAppend (List.append skipped count) [])).map
              some)
            (some tailFirst :: tail))) =
      none ::
        List.append
          ((encodeCodeWordAsInput
            (MachineCodeSymbol.header ::
              encodeBoolWordAppend (List.append skipped count) [])).map some)
          (some tailFirst :: tail)
  simp [Tape.cells, tapeAtCells, encodeCodeWordAsInput,
    encodeCodeSymbolAsInput]

-- The public count-window encoder composes the local emitter with this rewind;
-- this defaulted view records the shape after that packaging step.
theorem rightEdgeTape_rewind_target_defaultedCells
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (tapeAtCells [none]
            (List.append
              ((encodedLayoutBits (List.append skipped count)).map some)
              (some tailFirst :: tail)))) =
      false ::
        List.append
          (encodedLayoutBits (List.append skipped count))
          (tailFirst :: tail.map optionBitDefaultFalse) := by
  rw [rightEdgeTape_rewind_target_cells]
  simp [List.map_append,
    FoC.Computability.EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.optionBitDefaultFalse,
    FoC.Computability.EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.optionBitDefaultFalse_map_some]

/--
Left-edge endpoint for the raw-boundary emitter: the encoded layout sits
immediately left of the live tail with the head on the layout's first bit and
a single blank sentinel to its left.  This is the rewound shape the parent
count-window encoder consumes.  A uniform machine cannot instead halt on the
encoded word's right edge: the emitted block and the live tail are contiguous
nonblank cells with no detectable boundary, which is why the earlier
right-edge walkers were generated per layout.
-/
def encodedLeftEdgeTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells [none]
    (List.append
      ((encodedLayoutBits (List.append skipped count)).map some)
      (some tailFirst :: tail))

def rawBoundaryRightEdgeEmitterCoreDescription :
    MachineDescription :=
  rawBoundaryUniformEmitterCoreDescription

theorem rawBoundaryRightEdgeEmitterCoreDescription_subroutineReady :
    rawBoundaryRightEdgeEmitterCoreDescription.SubroutineReady := by
  rw [rawBoundaryRightEdgeEmitterCoreDescription]
  exact rawBoundaryUniformEmitterCoreDescription_subroutineReady

def rawBoundaryRightEdgeEmitterDescription :
    MachineDescription :=
  rawBoundaryRightEdgeEmitterCoreDescription

theorem rawBoundaryRightEdgeEmitterDescription_subroutineReady :
    rawBoundaryRightEdgeEmitterDescription.SubroutineReady :=
  rawBoundaryRightEdgeEmitterCoreDescription_subroutineReady

/--
Uniform core theorem: the two-pass emitter core halts, up to trailing blank
residue, on the encoded-layout left edge for every raw layout.  The proof is
the assembled uniform statement of the core stages restated on the folded
{name}`encodedLeftEdgeTape` endpoint.
-/
theorem rawBoundaryRightEdgeEmitterCoreDescription_haltsFrom_sourceTape_encodedLeftEdge
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    rawBoundaryRightEdgeEmitterCoreDescription.HaltsFromTapeEquiv
      (sourceTape skipped count (some tailFirst :: tail))
      (encodedLeftEdgeTape skipped count tailFirst tail) := by
  rw [rawBoundaryRightEdgeEmitterCoreDescription, encodedLeftEdgeTape]
  exact
    rawBoundaryUniformEmitterCoreDescription_haltsFrom_sourceTape_encodedLeftEdgeCells
      skipped count tailFirst tail

/--
Empty-layout specialization of the uniform core theorem.  The currency is
tape equivalence: the two-pass core leaves its pass-one footprint as trailing
blank residue left of the migrated block, so exact tape equality does not
hold for the empty layout either.
-/
theorem rawBoundaryRightEdgeEmitterCoreDescription_haltsFrom_sourceTape_encodedLeftEdge_empty
    (tailFirst : Bool) (tail : List (Option Bool)) :
    rawBoundaryRightEdgeEmitterCoreDescription.HaltsFromTapeEquiv
      (sourceTape [] [] (some tailFirst :: tail))
      (encodedLeftEdgeTape [] [] tailFirst tail) :=
  rawBoundaryRightEdgeEmitterCoreDescription_haltsFrom_sourceTape_encodedLeftEdge
    [] [] tailFirst tail

/--
Nonempty-layout specialization of the uniform core theorem.  The emptiness
hypothesis is retained for signature stability; the uniform theorem does not
need it.
-/
theorem rawBoundaryRightEdgeEmitterCoreDescription_haltsFrom_sourceTape_encodedLeftEdge_nonempty
    (skipped count : Word Bool)
    (_h : List.append skipped count ≠ [])
    (tailFirst : Bool) (tail : List (Option Bool)) :
    rawBoundaryRightEdgeEmitterCoreDescription.HaltsFromTapeEquiv
      (sourceTape skipped count (some tailFirst :: tail))
      (encodedLeftEdgeTape skipped count tailFirst tail) :=
  rawBoundaryRightEdgeEmitterCoreDescription_haltsFrom_sourceTape_encodedLeftEdge
    skipped count tailFirst tail

theorem rawBoundaryRightEdgeEmitterDescription_haltsFrom_sourceTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    rawBoundaryRightEdgeEmitterDescription.HaltsFromTapeEquiv
      (sourceTape skipped count (some tailFirst :: tail))
      (encodedLeftEdgeTape skipped count tailFirst tail) :=
  rawBoundaryRightEdgeEmitterCoreDescription_haltsFrom_sourceTape_encodedLeftEdge
    skipped count tailFirst tail

def Spec (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall (skipped count : Word Bool)
      (tailFirst : Bool) (tail : List (Option Bool)),
      emitter.HaltsFromTapeEquiv
        (sourceTape skipped count (some tailFirst :: tail))
        (encodedLeftEdgeTape skipped count tailFirst tail)

def Construction : Prop :=
  exists emitter : MachineDescription, Spec emitter

theorem construction_core : Construction := by
  refine ⟨rawBoundaryRightEdgeEmitterDescription, ?_⟩
  constructor
  · exact rawBoundaryRightEdgeEmitterDescription_subroutineReady
  · intro skipped count tailFirst tail
    exact
      rawBoundaryRightEdgeEmitterDescription_haltsFrom_sourceTape
        skipped count tailFirst tail

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
