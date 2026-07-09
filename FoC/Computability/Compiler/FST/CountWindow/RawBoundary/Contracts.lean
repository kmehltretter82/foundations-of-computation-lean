import FoC.Computability.Compiler.FST.CountWindow.RawBoundary
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Contracts.BlankSentinelFinalizer
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Contracts.CountedBoundary
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Contracts.EraseTailHeadBlankSentinel
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Contracts.EraseRawFootprintBlankSentinel
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Contracts.FixedBranchLoop
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Contracts.MarkerAwarePull
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Contracts.MarkedCellSuffixLoop
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Contracts.SourceBranchRoute

set_option doc.verso true

/-!
# Raw-boundary right-edge emitter route contracts

This module packages the endpoint facts around the count-window raw-boundary
right-edge emitter.  The concrete finite-table core leaf remains in
{module}`FoC.Computability.Compiler.FST.CountWindow.RawBoundary`;
the route contracts here expose the source tape, right-edge target, final
rewind handoff, structured debug samples, and public construction surface used
by the higher count-window raw-source encoder.
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
## Source endpoint route
-/

structure RawBoundarySourceEndpointShape
    (skipped count : Word Bool)
    (tail : List (Option Bool)) : Prop where
  sourceCells :
    Tape.cells (sourceTape skipped count tail) =
      none ::
        List.append ((List.append skipped count).map some)
          (none ::
            none ::
            none ::
            List.append
              (List.replicate count.length (none : Option Bool))
              tail)
  sourceDefaultedCells :
    List.map optionBitDefaultFalse
        (Tape.cells (sourceTape skipped count tail)) =
      false ::
        List.append (List.append skipped count)
          (false ::
            false ::
              false ::
                List.append (List.replicate count.length false)
                  (tail.map optionBitDefaultFalse))
  entryHalts :
    entryDescription.HaltsFromTape
      (sourceTape skipped count tail)
      (entryTape skipped count tail)
  entryRun :
    entryDescription.runConfig 1
        { state := entryDescription.start
          tape := sourceTape skipped count tail } =
      { state := entryDescription.halt
        tape := entryTape skipped count tail }
  entryMoveRight :
    Tape.move Direction.right (entryTape skipped count tail) =
      sourceTape skipped count tail
  entryReady :
    entryDescription.SubroutineReady

theorem rawBoundarySourceEndpointShape
    (skipped count : Word Bool)
    (tail : List (Option Bool)) :
    RawBoundarySourceEndpointShape skipped count tail :=
  { sourceCells :=
      sourceTape_cells skipped count tail
    sourceDefaultedCells :=
      sourceTape_defaultedCells skipped count tail
    entryHalts :=
      entryDescription_haltsFrom_sourceTape skipped count tail
    entryRun :=
      entryDescription_run_sourceTape skipped count tail
    entryMoveRight :=
      entryTape_moveRight skipped count tail
    entryReady :=
      entryDescription_subroutineReady }

theorem rawBoundary_source_cells
    (skipped count : Word Bool)
    (tail : List (Option Bool)) :
    Tape.cells (sourceTape skipped count tail) =
      none ::
        List.append ((List.append skipped count).map some)
          (none ::
            none ::
            none ::
            List.append
              (List.replicate count.length (none : Option Bool))
              tail) :=
  (rawBoundarySourceEndpointShape skipped count tail).sourceCells

theorem rawBoundary_source_defaultedCells
    (skipped count : Word Bool)
    (tail : List (Option Bool)) :
    List.map optionBitDefaultFalse
        (Tape.cells (sourceTape skipped count tail)) =
      false ::
        List.append (List.append skipped count)
          (false ::
            false ::
              false ::
                List.append (List.replicate count.length false)
                  (tail.map optionBitDefaultFalse)) :=
  (rawBoundarySourceEndpointShape skipped count tail).sourceDefaultedCells

theorem rawBoundary_entry_halts
    (skipped count : Word Bool)
    (tail : List (Option Bool)) :
    entryDescription.HaltsFromTape
      (sourceTape skipped count tail)
      (entryTape skipped count tail) :=
  (rawBoundarySourceEndpointShape skipped count tail).entryHalts

theorem rawBoundary_entry_moveRight
    (skipped count : Word Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.right (entryTape skipped count tail) =
      sourceTape skipped count tail :=
  (rawBoundarySourceEndpointShape skipped count tail).entryMoveRight

/-!
## Source-start rewind route
-/

structure RawBoundarySourceStartEndpointShape
    (skipped count : Word Bool)
    (tail : List (Option Bool)) : Prop where
  sourceStartCells :
    Tape.cells (sourceStartTape skipped count tail) =
      none ::
        List.append ((List.append skipped count).map some)
          (none ::
            none ::
              none ::
                List.append
                  (List.replicate count.length (none : Option Bool))
                  tail)
  sourceStartDefaultedCells :
    List.map optionBitDefaultFalse
        (Tape.cells (sourceStartTape skipped count tail)) =
      false ::
        List.append (List.append skipped count)
          (false ::
            false ::
              false ::
                List.append (List.replicate count.length false)
                  (tail.map optionBitDefaultFalse))
  rewindHalts :
    rightEdgeRewindDescription.HaltsFromTape
      (sourceTape skipped count tail)
      (sourceStartTape skipped count tail)

theorem rawBoundarySourceStartEndpointShape
    (skipped count : Word Bool)
    (tail : List (Option Bool)) :
    RawBoundarySourceStartEndpointShape skipped count tail :=
  { sourceStartCells :=
      sourceStartTape_cells skipped count tail
    sourceStartDefaultedCells :=
      sourceStartTape_defaultedCells skipped count tail
    rewindHalts :=
      rightEdgeRewindDescription_haltsFrom_sourceTape_sourceStart
        skipped count tail }

theorem rawBoundary_sourceStart_cells
    (skipped count : Word Bool)
    (tail : List (Option Bool)) :
    Tape.cells (sourceStartTape skipped count tail) =
      none ::
        List.append ((List.append skipped count).map some)
          (none ::
            none ::
              none ::
                List.append
                  (List.replicate count.length (none : Option Bool))
                  tail) :=
  (rawBoundarySourceStartEndpointShape
    skipped count tail).sourceStartCells

theorem rawBoundary_sourceStart_defaultedCells
    (skipped count : Word Bool)
    (tail : List (Option Bool)) :
    List.map optionBitDefaultFalse
        (Tape.cells (sourceStartTape skipped count tail)) =
      false ::
        List.append (List.append skipped count)
          (false ::
            false ::
              false ::
                List.append (List.replicate count.length false)
                  (tail.map optionBitDefaultFalse)) :=
  (rawBoundarySourceStartEndpointShape
    skipped count tail).sourceStartDefaultedCells

theorem rawBoundary_sourceStart_rewind_halts
    (skipped count : Word Bool)
    (tail : List (Option Bool)) :
    rightEdgeRewindDescription.HaltsFromTape
      (sourceTape skipped count tail)
      (sourceStartTape skipped count tail) :=
  (rawBoundarySourceStartEndpointShape
    skipped count tail).rewindHalts

/-!
## Tail-handoff endpoint route
-/

structure RawBoundaryTailHandoffEndpointShape
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) : Prop where
  tailLeftHalts :
    rightBlankRunTailFirstLeftHandoffDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (tailLeftHandoffTape skipped count tailFirst tail)
  tailLeftMoveRight :
    Tape.move Direction.right
        (tailLeftHandoffTape skipped count tailFirst tail) =
      tailHeadHandoffTape skipped count tailFirst tail
  tailHeadAsScratchBase :
    tailHeadHandoffTape skipped count tailFirst tail =
      tapeAtCells
        (List.append
          (List.replicate (tailHeadImmediateScratchCellCount count)
            (none : Option Bool))
          (tailHeadRawBaseLeft skipped count))
        (some tailFirst :: tail)
  immediateScratchGap :
    tailHeadImmediateScratchCellCount count <
      encodedLayoutScratchCellCount (List.append skipped count)
  scratchShortfall :
    tailHeadImmediateScratchCellCount count +
        tailHeadScratchShortfall skipped count =
      encodedLayoutScratchCellCount (List.append skipped count)
  scratchShortfallPositive :
    0 < tailHeadScratchShortfall skipped count

theorem rawBoundaryTailHandoffEndpointShape
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    RawBoundaryTailHandoffEndpointShape
      skipped count tailFirst tail :=
  { tailLeftHalts :=
      rightBlankRunTailFirstLeftHandoffDescription_haltsFrom_sourceTape
        skipped count tailFirst tail
    tailLeftMoveRight :=
      tailLeftHandoffTape_moveRight skipped count tailFirst tail
    tailHeadAsScratchBase :=
      tailHeadHandoffTape_eq_tapeAtCells_scratchBase
        skipped count tailFirst tail
    immediateScratchGap :=
      tailHeadImmediateScratchCellCount_lt_encodedLayoutScratchCellCount
        skipped count
    scratchShortfall :=
      tailHeadImmediateScratchCellCount_add_shortfall_eq_encodedLayoutScratchCellCount
        skipped count
    scratchShortfallPositive :=
      tailHeadScratchShortfall_pos skipped count }

theorem rawBoundary_tailHandoff_halts
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    rightBlankRunTailFirstLeftHandoffDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (tailLeftHandoffTape skipped count tailFirst tail) :=
  (rawBoundaryTailHandoffEndpointShape
    skipped count tailFirst tail).tailLeftHalts

theorem rawBoundary_tailHandoff_headShape
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    tailHeadHandoffTape skipped count tailFirst tail =
      tapeAtCells
        (List.append
          (List.replicate (tailHeadImmediateScratchCellCount count)
            (none : Option Bool))
          (tailHeadRawBaseLeft skipped count))
        (some tailFirst :: tail) :=
  (rawBoundaryTailHandoffEndpointShape
    skipped count tailFirst tail).tailHeadAsScratchBase

theorem rawBoundary_tailHandoff_immediateScratchGap
    (skipped count : Word Bool) :
    tailHeadImmediateScratchCellCount count <
      encodedLayoutScratchCellCount (List.append skipped count) :=
  (rawBoundaryTailHandoffEndpointShape
    skipped count true []).immediateScratchGap

theorem rawBoundary_tailHandoff_scratchShortfall
    (skipped count : Word Bool) :
    tailHeadImmediateScratchCellCount count +
        tailHeadScratchShortfall skipped count =
      encodedLayoutScratchCellCount (List.append skipped count) :=
  (rawBoundaryTailHandoffEndpointShape
    skipped count true []).scratchShortfall

/-!
## Nearest raw-bit pull route
-/

structure RawBoundaryNearestRawBitPullRoute
    (blankCount : Nat)
    (baseLeft : List (Option Bool))
    (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) : Prop where
  pullerReady :
    pullNearestRawBitToTailMarkerDescription.SubroutineReady
  pullerHalts :
    pullNearestRawBitToTailMarkerDescription.HaltsFromTape
      (pullNearestRawBitToTailMarkerSourceTape
        blankCount baseLeft rawBit tailFirst tail)
      (pullNearestRawBitToTailMarkerTargetTape
        blankCount baseLeft rawBit tailFirst tail)

theorem rawBoundaryNearestRawBitPullRoute
    (blankCount : Nat)
    (baseLeft : List (Option Bool))
    (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    RawBoundaryNearestRawBitPullRoute
      blankCount baseLeft rawBit tailFirst tail :=
  { pullerReady :=
      pullNearestRawBitToTailMarkerDescription_subroutineReady
    pullerHalts :=
      pullNearestRawBitToTailMarkerDescription_haltsFromTape
        blankCount baseLeft rawBit tailFirst tail }

theorem rawBoundary_nearestRawBitPull_halts
    (blankCount : Nat)
    (baseLeft : List (Option Bool))
    (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    pullNearestRawBitToTailMarkerDescription.HaltsFromTape
      (pullNearestRawBitToTailMarkerSourceTape
        blankCount baseLeft rawBit tailFirst tail)
      (pullNearestRawBitToTailMarkerTargetTape
        blankCount baseLeft rawBit tailFirst tail) :=
  (rawBoundaryNearestRawBitPullRoute
    blankCount baseLeft rawBit tailFirst tail).pullerHalts

structure RawBoundaryTailHeadNearestRawBitPullRoute
    (skipped count pref : Word Bool)
    (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) : Prop where
  splitLastRawBase :
    tailHeadRawBaseLeft skipped count =
      some rawBit :: List.append (pref.reverse.map some) [none]
  pullerHaltsFromTailHead :
    pullNearestRawBitToTailMarkerDescription.HaltsFromTape
      (tailHeadHandoffTape skipped count tailFirst tail)
      (tailHeadPulledNearestRawBitTape
        pref count rawBit tailFirst tail)

theorem rawBoundaryTailHeadNearestRawBitPullRoute
    (skipped count pref : Word Bool)
    (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) :
    RawBoundaryTailHeadNearestRawBitPullRoute
      skipped count pref rawBit tailFirst tail hlayout :=
  { splitLastRawBase :=
      tailHeadRawBaseLeft_eq_splitLast
        skipped count pref rawBit hlayout
    pullerHaltsFromTailHead :=
      pullNearestRawBitToTailMarkerDescription_haltsFrom_tailHeadHandoffTape
        skipped count pref rawBit tailFirst tail hlayout }

theorem rawBoundary_tailHead_nearestRawBitPull_halts
    (skipped count pref : Word Bool)
    (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) :
    pullNearestRawBitToTailMarkerDescription.HaltsFromTape
      (tailHeadHandoffTape skipped count tailFirst tail)
      (tailHeadPulledNearestRawBitTape
        pref count rawBit tailFirst tail) :=
  (rawBoundaryTailHeadNearestRawBitPullRoute
    skipped count pref rawBit tailFirst tail hlayout).pullerHaltsFromTailHead

theorem rawBoundary_tailHead_nearestRawBitPull_exists_of_nonempty
    (skipped count : Word Bool)
    (h : List.append skipped count ≠ [])
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    exists pref : Word Bool, exists rawBit : Bool,
      List.append skipped count = List.append pref [rawBit] ∧
        pullNearestRawBitToTailMarkerDescription.HaltsFromTape
          (tailHeadHandoffTape skipped count tailFirst tail)
          (tailHeadPulledNearestRawBitTape
            pref count rawBit tailFirst tail) :=
  pullNearestRawBitToTailMarkerDescription_haltsFrom_tailHeadHandoffTape_of_nonempty
    skipped count h tailFirst tail

/-!
## Emitted cell-suffix endpoint shape
-/

structure RawBoundaryEmittedCellSuffixShape
    (pref count cellSuffix : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) : Prop where
  suffixCells :
    Tape.cells
        (tailHeadEmittedCellSuffixTape
          pref count cellSuffix tailFirst tail) =
      none ::
        List.append (pref.map some)
          (List.append
            (List.replicate count.length (none : Option Bool))
            (List.append
              ((preservingCellPassCellBits cellSuffix).map some)
              (some tailFirst :: tail)))
  suffixDefaultedCells :
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
              (tailFirst :: tail.map optionBitDefaultFalse)))
  suffixLeftLength :
    (tailHeadEmittedCellSuffixTape
      pref count cellSuffix tailFirst tail).left.length =
      4 * cellSuffix.length + count.length + pref.length + 1

theorem rawBoundaryEmittedCellSuffixShape
    (pref count cellSuffix : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    RawBoundaryEmittedCellSuffixShape
      pref count cellSuffix tailFirst tail :=
  { suffixCells :=
      tailHeadEmittedCellSuffixTape_cells
        pref count cellSuffix tailFirst tail
    suffixDefaultedCells :=
      tailHeadEmittedCellSuffixTape_defaultedCells
        pref count cellSuffix tailFirst tail
    suffixLeftLength :=
      tailHeadEmittedCellSuffixTape_left_length
        pref count cellSuffix tailFirst tail }

theorem rawBoundary_emittedCellSuffix_cells
    (pref count cellSuffix : Word Bool)
    (tailFirst : Bool)
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
              (some tailFirst :: tail))) :=
  (rawBoundaryEmittedCellSuffixShape
    pref count cellSuffix tailFirst tail).suffixCells

theorem rawBoundary_emittedCellSuffix_defaultedCells
    (pref count cellSuffix : Word Bool)
    (tailFirst : Bool)
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
              (tailFirst :: tail.map optionBitDefaultFalse))) :=
  (rawBoundaryEmittedCellSuffixShape
    pref count cellSuffix tailFirst tail).suffixDefaultedCells

theorem rawBoundary_emittedCellSuffix_leftLength
    (pref count cellSuffix : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (tailHeadEmittedCellSuffixTape
      pref count cellSuffix tailFirst tail).left.length =
      4 * cellSuffix.length + count.length + pref.length + 1 :=
  (rawBoundaryEmittedCellSuffixShape
    pref count cellSuffix tailFirst tail).suffixLeftLength

theorem rawBoundary_emittedNearestRawBitCell_eq_cellSuffixSingleton
    (pref count : Word Bool)
    (rawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    tailHeadEmittedNearestRawBitCellTape pref count rawBit tailFirst tail =
      tailHeadEmittedCellSuffixTape pref count [rawBit] tailFirst tail :=
  tailHeadEmittedNearestRawBitCellTape_eq_cellSuffix_singleton
    pref count rawBit tailFirst tail

structure RawBoundaryFullCellSuffixEndpointShape
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) : Prop where
  fullSuffixCells :
    Tape.cells
        (tailHeadEmittedFullCellSuffixTape
          skipped count tailFirst tail) =
      none ::
        List.append
          (List.replicate count.length (none : Option Bool))
          (List.append
            ((preservingCellPassCellBits
              (List.append skipped count)).map some)
            (some tailFirst :: tail))
  fullSuffixDefaultedCells :
    List.map optionBitDefaultFalse
        (Tape.cells
          (tailHeadEmittedFullCellSuffixTape
            skipped count tailFirst tail)) =
      false ::
        List.append
          (List.replicate count.length false)
          (List.append
            (preservingCellPassCellBits (List.append skipped count))
            (tailFirst :: tail.map optionBitDefaultFalse))
  fullSuffixLeftLength :
    (tailHeadEmittedFullCellSuffixTape
      skipped count tailFirst tail).left.length =
      4 * skipped.length + 5 * count.length + 1
  postCellSuffixShortfallPositive :
    0 < tailHeadPostCellSuffixShortfall skipped count
  fullSuffixLeftLengthAddShortfall :
    (tailHeadEmittedFullCellSuffixTape
      skipped count tailFirst tail).left.length +
        tailHeadPostCellSuffixShortfall skipped count =
      encodedLayoutScratchCellCount (List.append skipped count)

theorem rawBoundaryFullCellSuffixEndpointShape
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    RawBoundaryFullCellSuffixEndpointShape
      skipped count tailFirst tail :=
  { fullSuffixCells :=
      tailHeadEmittedFullCellSuffixTape_cells
        skipped count tailFirst tail
    fullSuffixDefaultedCells :=
      tailHeadEmittedFullCellSuffixTape_defaultedCells
        skipped count tailFirst tail
    fullSuffixLeftLength :=
      tailHeadEmittedFullCellSuffixTape_left_length_eq
        skipped count tailFirst tail
    postCellSuffixShortfallPositive :=
      tailHeadPostCellSuffixShortfall_pos skipped count
    fullSuffixLeftLengthAddShortfall :=
      tailHeadEmittedFullCellSuffixTape_left_length_add_shortfall
        skipped count tailFirst tail }

theorem rawBoundary_fullCellSuffix_cells
    (skipped count : Word Bool)
    (tailFirst : Bool)
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
            (some tailFirst :: tail)) :=
  (rawBoundaryFullCellSuffixEndpointShape
    skipped count tailFirst tail).fullSuffixCells

theorem rawBoundary_fullCellSuffix_leftLengthAddShortfall
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (tailHeadEmittedFullCellSuffixTape
      skipped count tailFirst tail).left.length +
        tailHeadPostCellSuffixShortfall skipped count =
      encodedLayoutScratchCellCount (List.append skipped count) :=
  (rawBoundaryFullCellSuffixEndpointShape
    skipped count tailFirst tail).fullSuffixLeftLengthAddShortfall

/-!
## Nearest raw-bit pull-and-emit route
-/

structure RawBoundaryNearestRawBitPullAndEmitRoute
    (skipped count pref : Word Bool)
    (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) : Prop where
  emitterReady :
    emitPulledRawBitCellChunkDescription.SubroutineReady
  leftEdgeMoverReady :
    leftMoveAcrossFourNonblankCellsDescription.SubroutineReady
  combinedReady :
    pullAndEmitNearestRawBitCellDescription.SubroutineReady
  pulledAsEmitterSource :
    tailHeadPulledNearestRawBitTape pref count rawBit tailFirst tail =
      emitPulledRawBitCellChunkSourceTape
        count.length
        (List.append (pref.reverse.map some) [none])
        rawBit tailFirst tail
  emitterHaltsFromPulled :
    emitPulledRawBitCellChunkDescription.HaltsFromTape
      (tailHeadPulledNearestRawBitTape
        pref count rawBit tailFirst tail)
      (tailHeadEmittedNearestRawBitCellTape
        pref count rawBit tailFirst tail)
  combinedHaltsFromTailHead :
    pullAndEmitNearestRawBitCellDescription.HaltsFromTape
      (tailHeadHandoffTape skipped count tailFirst tail)
      (tailHeadEmittedNearestRawBitCellTape
        pref count rawBit tailFirst tail)
  leftEdgeMoverHalts :
    leftMoveAcrossFourNonblankCellsDescription.HaltsFromTape
      (tailHeadEmittedNearestRawBitCellTape
        pref count rawBit tailFirst tail)
      (tailHeadEmittedNearestRawBitCellLeftEdgeTape
        pref count rawBit tailFirst tail)
  leftEdgeCells :
    Tape.cells
        (tailHeadEmittedNearestRawBitCellLeftEdgeTape
          pref count rawBit tailFirst tail) =
      none ::
        List.append (pref.map some)
          (List.append
            (List.replicate count.length (none : Option Bool))
            (List.append
              ((pulledRawBitCellChunkBits rawBit).map some)
              (some tailFirst :: tail)))
  leftEdgeDefaultedCells :
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
              (tailFirst :: tail.map optionBitDefaultFalse)))
  leftEdgeLeftLength :
    (tailHeadEmittedNearestRawBitCellLeftEdgeTape
      pref count rawBit tailFirst tail).left.length =
      count.length + pref.length + 1
  emittedAsCellSuffixSingleton :
    tailHeadEmittedNearestRawBitCellTape pref count rawBit tailFirst tail =
      tailHeadEmittedCellSuffixTape pref count [rawBit] tailFirst tail
  emittedCells :
    Tape.cells
        (tailHeadEmittedNearestRawBitCellTape
          pref count rawBit tailFirst tail) =
      none ::
        List.append (pref.map some)
          (List.append
            (List.replicate count.length (none : Option Bool))
            (List.append
              ((pulledRawBitCellChunkBits rawBit).map some)
              (some tailFirst :: tail)))
  emittedDefaultedCells :
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
              (tailFirst :: tail.map optionBitDefaultFalse)))
  emittedCellsCanonical :
    Tape.cells
        (tailHeadEmittedNearestRawBitCellTape
          pref count rawBit tailFirst tail) =
      none ::
        List.append (pref.map some)
          (List.append
            (List.replicate count.length (none : Option Bool))
            (List.append
              ((preservingCellPassCellBits [rawBit]).map some)
              (some tailFirst :: tail)))
  emittedDefaultedCellsCanonical :
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
              (tailFirst :: tail.map optionBitDefaultFalse)))
  emittedLeftLength :
    (tailHeadEmittedNearestRawBitCellTape
      pref count rawBit tailFirst tail).left.length =
      4 + count.length + pref.length + 1

theorem rawBoundaryNearestRawBitPullAndEmitRoute
    (skipped count pref : Word Bool)
    (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) :
    RawBoundaryNearestRawBitPullAndEmitRoute
      skipped count pref rawBit tailFirst tail hlayout :=
  { emitterReady :=
      emitPulledRawBitCellChunkDescription_subroutineReady
    leftEdgeMoverReady :=
      leftMoveAcrossFourNonblankCellsDescription_subroutineReady
    combinedReady :=
      pullAndEmitNearestRawBitCellDescription_subroutineReady
    pulledAsEmitterSource :=
      tailHeadPulledNearestRawBitTape_eq_emitSource
        pref count rawBit tailFirst tail
    emitterHaltsFromPulled :=
      emitPulledRawBitCellChunkDescription_haltsFrom_tailHeadPulled
        pref count rawBit tailFirst tail
    combinedHaltsFromTailHead :=
      pullAndEmitNearestRawBitCellDescription_haltsFrom_tailHeadHandoffTape
        skipped count pref rawBit tailFirst tail hlayout
    leftEdgeMoverHalts :=
      leftMoveAcrossFourNonblankCellsDescription_haltsFrom_tailHeadEmittedNearestRawBitCell
        pref count rawBit tailFirst tail
    leftEdgeCells :=
      tailHeadEmittedNearestRawBitCellLeftEdgeTape_cells
        pref count rawBit tailFirst tail
    leftEdgeDefaultedCells :=
      tailHeadEmittedNearestRawBitCellLeftEdgeTape_defaultedCells
        pref count rawBit tailFirst tail
    leftEdgeLeftLength :=
      tailHeadEmittedNearestRawBitCellLeftEdgeTape_left_length
        pref count rawBit tailFirst tail
    emittedAsCellSuffixSingleton :=
      tailHeadEmittedNearestRawBitCellTape_eq_cellSuffix_singleton
        pref count rawBit tailFirst tail
    emittedCells :=
      tailHeadEmittedNearestRawBitCellTape_cells
        pref count rawBit tailFirst tail
    emittedDefaultedCells :=
      tailHeadEmittedNearestRawBitCellTape_defaultedCells
        pref count rawBit tailFirst tail
    emittedCellsCanonical :=
      tailHeadEmittedNearestRawBitCellTape_cells_canonical
        pref count rawBit tailFirst tail
    emittedDefaultedCellsCanonical :=
      tailHeadEmittedNearestRawBitCellTape_defaultedCells_canonical
        pref count rawBit tailFirst tail
    emittedLeftLength :=
      tailHeadEmittedNearestRawBitCellTape_left_length
        pref count rawBit tailFirst tail }

theorem rawBoundary_nearestRawBitPullAndEmit_halts
    (skipped count pref : Word Bool)
    (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) :
    pullAndEmitNearestRawBitCellDescription.HaltsFromTape
      (tailHeadHandoffTape skipped count tailFirst tail)
      (tailHeadEmittedNearestRawBitCellTape
        pref count rawBit tailFirst tail) :=
  (rawBoundaryNearestRawBitPullAndEmitRoute
    skipped count pref rawBit tailFirst tail hlayout).combinedHaltsFromTailHead

theorem rawBoundary_nearestRawBitCell_leftEdge_halts
    (skipped count pref : Word Bool)
    (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) :
    leftMoveAcrossFourNonblankCellsDescription.HaltsFromTape
      (tailHeadEmittedNearestRawBitCellTape
        pref count rawBit tailFirst tail)
      (tailHeadEmittedNearestRawBitCellLeftEdgeTape
        pref count rawBit tailFirst tail) :=
  (rawBoundaryNearestRawBitPullAndEmitRoute
    skipped count pref rawBit tailFirst tail hlayout).leftEdgeMoverHalts

/-!
## Generic head-gap raw-bit pull route
-/

structure RawBoundaryHeadGapPullRoute
    (gap : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool)
    (right : List (Option Bool)) : Prop where
  pullerReady :
    pullNearestRawBitToTailMarkerDescription.SubroutineReady
  pullerHalts :
    pullNearestRawBitToTailMarkerDescription.HaltsFromTape
      (pullNearestRawBitToHeadMarkerSourceTape
        gap baseLeft rawBit headBit right)
      (pullNearestRawBitToHeadMarkerTargetTape
        gap baseLeft rawBit headBit right)
  sourceCells :
    Tape.cells
        (pullNearestRawBitToHeadMarkerSourceTape
          gap baseLeft rawBit headBit right) =
      List.append baseLeft.reverse
        (some rawBit ::
          List.append (List.replicate gap (none : Option Bool))
            (some headBit :: right))
  targetCells :
    Tape.cells
        (pullNearestRawBitToHeadMarkerTargetTape
          gap baseLeft rawBit headBit right) =
      List.append baseLeft.reverse
        (List.append (List.replicate gap (none : Option Bool))
          (some rawBit :: some headBit :: right))
  sourceLeftLength :
    (pullNearestRawBitToHeadMarkerSourceTape
      gap baseLeft rawBit headBit right).left.length =
      gap + baseLeft.length + 1
  targetLeftLength :
    (pullNearestRawBitToHeadMarkerTargetTape
      gap baseLeft rawBit headBit right).left.length =
      gap + baseLeft.length + 1

theorem rawBoundaryHeadGapPullRoute
    (gap : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool)
    (right : List (Option Bool)) :
    RawBoundaryHeadGapPullRoute
      gap baseLeft rawBit headBit right :=
  { pullerReady :=
      pullNearestRawBitToTailMarkerDescription_subroutineReady
    pullerHalts :=
      pullNearestRawBitToTailMarkerDescription_haltsFromHeadGap
        gap baseLeft rawBit headBit right
    sourceCells :=
      pullNearestRawBitToHeadMarkerSourceTape_cells
        gap baseLeft rawBit headBit right
    targetCells :=
      pullNearestRawBitToHeadMarkerTargetTape_cells
        gap baseLeft rawBit headBit right
    sourceLeftLength :=
      pullNearestRawBitToHeadMarkerSourceTape_left_length
        gap baseLeft rawBit headBit right
    targetLeftLength :=
      pullNearestRawBitToHeadMarkerTargetTape_left_length
        gap baseLeft rawBit headBit right }

theorem rawBoundary_headGapPull_halts
    (gap : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool)
    (right : List (Option Bool)) :
    pullNearestRawBitToTailMarkerDescription.HaltsFromTape
      (pullNearestRawBitToHeadMarkerSourceTape
        gap baseLeft rawBit headBit right)
      (pullNearestRawBitToHeadMarkerTargetTape
        gap baseLeft rawBit headBit right) :=
  (rawBoundaryHeadGapPullRoute
    gap baseLeft rawBit headBit right).pullerHalts

/-!
## Generic head-gap raw-bit pull-and-emit route
-/

structure RawBoundaryHeadGapPullAndEmitRoute
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool)
    (right : List (Option Bool)) : Prop where
  combinedReady :
    pullAndEmitNearestRawBitCellDescription.SubroutineReady
  pulledAsEmitterSource :
    pullNearestRawBitToHeadMarkerTargetTape
        (scratchTail + 3) baseLeft rawBit headBit right =
      emitPulledRawBitCellChunkSourceTape
        scratchTail baseLeft rawBit headBit right
  emitterHaltsFromPulled :
    emitPulledRawBitCellChunkDescription.HaltsFromTape
      (pullNearestRawBitToHeadMarkerTargetTape
        (scratchTail + 3) baseLeft rawBit headBit right)
      (emitPulledRawBitCellChunkTargetTape
        scratchTail baseLeft rawBit headBit right)
  combinedHalts :
    pullAndEmitNearestRawBitCellDescription.HaltsFromTape
      (pullNearestRawBitToHeadMarkerSourceTape
        (scratchTail + 3) baseLeft rawBit headBit right)
      (emitPulledRawBitCellChunkTargetTape
        scratchTail baseLeft rawBit headBit right)
  targetCells :
    Tape.cells
        (emitPulledRawBitCellChunkTargetTape
          scratchTail baseLeft rawBit headBit right) =
      List.append baseLeft.reverse
        (List.append
          (List.replicate scratchTail (none : Option Bool))
          (List.append ((pulledRawBitCellChunkBits rawBit).map some)
            (some headBit :: right)))
  targetLeftLength :
    (emitPulledRawBitCellChunkTargetTape
      scratchTail baseLeft rawBit headBit right).left.length =
      scratchTail + baseLeft.length + 4

theorem rawBoundaryHeadGapPullAndEmitRoute
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool)
    (right : List (Option Bool)) :
    RawBoundaryHeadGapPullAndEmitRoute
      scratchTail baseLeft rawBit headBit right :=
  { combinedReady :=
      pullAndEmitNearestRawBitCellDescription_subroutineReady
    pulledAsEmitterSource :=
      pullNearestRawBitToHeadMarkerTargetTape_eq_emitSource
        scratchTail baseLeft rawBit headBit right
    emitterHaltsFromPulled :=
      emitPulledRawBitCellChunkDescription_haltsFrom_headGapPulled
        scratchTail baseLeft rawBit headBit right
    combinedHalts :=
      pullAndEmitNearestRawBitCellDescription_haltsFrom_headGap
        scratchTail baseLeft rawBit headBit right
    targetCells :=
      emitPulledRawBitCellChunkTargetTape_cells
        scratchTail baseLeft rawBit headBit right
    targetLeftLength :=
      emitPulledRawBitCellChunkTargetTape_left_length
        scratchTail baseLeft rawBit headBit right }

theorem rawBoundary_headGapPullAndEmit_halts
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool)
    (right : List (Option Bool)) :
    pullAndEmitNearestRawBitCellDescription.HaltsFromTape
      (pullNearestRawBitToHeadMarkerSourceTape
        (scratchTail + 3) baseLeft rawBit headBit right)
      (emitPulledRawBitCellChunkTargetTape
        scratchTail baseLeft rawBit headBit right) :=
  (rawBoundaryHeadGapPullAndEmitRoute
    scratchTail baseLeft rawBit headBit right).combinedHalts

/-!
## Generic head-gap raw-bit pull, emit, and left-edge route
-/

structure RawBoundaryHeadGapPullEmitLeftEdgeRoute
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool)
    (right : List (Option Bool)) : Prop where
  combinedReady :
    pullEmitAndMoveRawBitCellLeftEdgeDescription.SubroutineReady
  combinedHalts :
    pullEmitAndMoveRawBitCellLeftEdgeDescription.HaltsFromTape
      (pullNearestRawBitToHeadMarkerSourceTape
        (scratchTail + 3) baseLeft rawBit headBit right)
      (emitPulledRawBitCellChunkLeftEdgeTargetTape
        scratchTail baseLeft rawBit headBit right)
  targetCells :
    Tape.cells
        (emitPulledRawBitCellChunkLeftEdgeTargetTape
          scratchTail baseLeft rawBit headBit right) =
      List.append baseLeft.reverse
        (List.append
          (List.replicate scratchTail (none : Option Bool))
          (List.append ((pulledRawBitCellChunkBits rawBit).map some)
            (some headBit :: right)))
  targetLeftLength :
    (emitPulledRawBitCellChunkLeftEdgeTargetTape
      scratchTail baseLeft rawBit headBit right).left.length =
      scratchTail + baseLeft.length

theorem rawBoundaryHeadGapPullEmitLeftEdgeRoute
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool)
    (right : List (Option Bool)) :
    RawBoundaryHeadGapPullEmitLeftEdgeRoute
      scratchTail baseLeft rawBit headBit right :=
  { combinedReady :=
      pullEmitAndMoveRawBitCellLeftEdgeDescription_subroutineReady
    combinedHalts :=
      pullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_headGap
        scratchTail baseLeft rawBit headBit right
    targetCells :=
      emitPulledRawBitCellChunkLeftEdgeTargetTape_cells
        scratchTail baseLeft rawBit headBit right
    targetLeftLength :=
      emitPulledRawBitCellChunkLeftEdgeTargetTape_left_length
        scratchTail baseLeft rawBit headBit right }

theorem rawBoundary_headGapPullEmitLeftEdge_halts
    (scratchTail : Nat) (baseLeft : List (Option Bool))
    (rawBit headBit : Bool)
    (right : List (Option Bool)) :
    pullEmitAndMoveRawBitCellLeftEdgeDescription.HaltsFromTape
      (pullNearestRawBitToHeadMarkerSourceTape
        (scratchTail + 3) baseLeft rawBit headBit right)
      (emitPulledRawBitCellChunkLeftEdgeTargetTape
        scratchTail baseLeft rawBit headBit right) :=
  (rawBoundaryHeadGapPullEmitLeftEdgeRoute
    scratchTail baseLeft rawBit headBit right).combinedHalts

/-!
## Next raw-bit pull, emit, and left-edge route from an emitted cell
-/

structure RawBoundaryNextRawBitPullEmitLeftEdgeFromEmittedCellLeftEdgeRoute
    (pref count : Word Bool) (scratchTail : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hcount : count.length = scratchTail + 3) : Prop where
  combinedReady :
    pullEmitAndMoveRawBitCellLeftEdgeDescription.SubroutineReady
  combinedHalts :
    pullEmitAndMoveRawBitCellLeftEdgeDescription.HaltsFromTape
      (tailHeadEmittedNearestRawBitCellLeftEdgeTape
        (List.append pref [nextRawBit])
        count emittedRawBit tailFirst tail)
      (tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
        pref scratchTail nextRawBit emittedRawBit tailFirst tail)
  targetCells :
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
                (some tailFirst :: tail))))
  targetDefaultedCells :
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
                (tailFirst :: tail.map optionBitDefaultFalse))))
  targetLeftLength :
    (tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
      pref scratchTail nextRawBit emittedRawBit tailFirst tail).left.length =
      scratchTail + pref.length + 1

theorem rawBoundaryNextRawBitPullEmitLeftEdgeFromEmittedCellLeftEdgeRoute
    (pref count : Word Bool) (scratchTail : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hcount : count.length = scratchTail + 3) :
    RawBoundaryNextRawBitPullEmitLeftEdgeFromEmittedCellLeftEdgeRoute
      pref count scratchTail nextRawBit emittedRawBit tailFirst tail
      hcount :=
  { combinedReady :=
      pullEmitAndMoveRawBitCellLeftEdgeDescription_subroutineReady
    combinedHalts :=
      pullEmitAndMoveRawBitCellLeftEdgeDescription_haltsFrom_tailHeadEmittedNearestRawBitCellLeftEdge_of_count_length
        pref count scratchTail nextRawBit emittedRawBit tailFirst tail
        hcount
    targetCells :=
      tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_cells
        pref scratchTail nextRawBit emittedRawBit tailFirst tail
    targetDefaultedCells :=
      tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_defaultedCells
        pref scratchTail nextRawBit emittedRawBit tailFirst tail
    targetLeftLength :=
      tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_left_length
        pref scratchTail nextRawBit emittedRawBit tailFirst tail }

theorem rawBoundary_nextRawBitPullEmitLeftEdgeFromEmittedCellLeftEdge_halts
    (pref count : Word Bool) (scratchTail : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hcount : count.length = scratchTail + 3) :
    pullEmitAndMoveRawBitCellLeftEdgeDescription.HaltsFromTape
      (tailHeadEmittedNearestRawBitCellLeftEdgeTape
        (List.append pref [nextRawBit])
        count emittedRawBit tailFirst tail)
      (tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
        pref scratchTail nextRawBit emittedRawBit tailFirst tail) :=
  (rawBoundaryNextRawBitPullEmitLeftEdgeFromEmittedCellLeftEdgeRoute
    pref count scratchTail nextRawBit emittedRawBit tailFirst tail
    hcount).combinedHalts

theorem rawBoundary_nextRawBitPullEmitLeftEdgeFromEmittedCellLeftEdge_exists_of_three_le_count_length
    (pref count : Word Bool)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hcount : 3 <= count.length) :
    exists scratchTail : Nat,
      exists hscratch : count.length = scratchTail + 3,
        RawBoundaryNextRawBitPullEmitLeftEdgeFromEmittedCellLeftEdgeRoute
          pref count scratchTail nextRawBit emittedRawBit tailFirst tail
          hscratch := by
  rcases nat_exists_eq_add_of_le hcount with ⟨scratchTail, hscratch⟩
  exact
    ⟨scratchTail, hscratch,
      rawBoundaryNextRawBitPullEmitLeftEdgeFromEmittedCellLeftEdgeRoute
        pref count scratchTail nextRawBit emittedRawBit tailFirst tail
        hscratch⟩

theorem rawBoundary_nextRawBitPullEmitLeftEdgeFromEmittedCellLeftEdge_halts_exists_of_three_le_count_length
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
      rawBoundary_nextRawBitPullEmitLeftEdgeFromEmittedCellLeftEdge_halts
        pref count scratchTail nextRawBit emittedRawBit tailFirst tail
        hscratch⟩

/-!
## Next raw-bit pull from an emitted-cell left edge
-/

structure RawBoundaryNextRawBitPullFromEmittedCellLeftEdgeRoute
    (pref count : Word Bool)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool)) : Prop where
  pullerReady :
    pullNearestRawBitToTailMarkerDescription.SubroutineReady
  pullerHalts :
    pullNearestRawBitToTailMarkerDescription.HaltsFromTape
      (tailHeadEmittedNearestRawBitCellLeftEdgeTape
        (List.append pref [nextRawBit])
        count emittedRawBit tailFirst tail)
      (tailHeadPulledNextRawBitBeforeEmittedCellTape
        pref count nextRawBit emittedRawBit tailFirst tail)
  pulledCells :
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
                (some tailFirst :: tail)))
  pulledDefaultedCells :
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
                (tailFirst :: tail.map optionBitDefaultFalse)))
  pulledLeftLength :
    (tailHeadPulledNextRawBitBeforeEmittedCellTape
      pref count nextRawBit emittedRawBit tailFirst tail).left.length =
      count.length + pref.length + 2

theorem rawBoundaryNextRawBitPullFromEmittedCellLeftEdgeRoute
    (pref count : Word Bool)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    RawBoundaryNextRawBitPullFromEmittedCellLeftEdgeRoute
      pref count nextRawBit emittedRawBit tailFirst tail :=
  { pullerReady :=
      pullNearestRawBitToTailMarkerDescription_subroutineReady
    pullerHalts :=
      pullNearestRawBitToTailMarkerDescription_haltsFrom_tailHeadEmittedNearestRawBitCellLeftEdge
        pref count nextRawBit emittedRawBit tailFirst tail
    pulledCells :=
      tailHeadPulledNextRawBitBeforeEmittedCellTape_cells
        pref count nextRawBit emittedRawBit tailFirst tail
    pulledDefaultedCells :=
      tailHeadPulledNextRawBitBeforeEmittedCellTape_defaultedCells
        pref count nextRawBit emittedRawBit tailFirst tail
    pulledLeftLength :=
      tailHeadPulledNextRawBitBeforeEmittedCellTape_left_length
        pref count nextRawBit emittedRawBit tailFirst tail }

theorem rawBoundary_nextRawBitPullFromEmittedCellLeftEdge_halts
    (pref count : Word Bool)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    pullNearestRawBitToTailMarkerDescription.HaltsFromTape
      (tailHeadEmittedNearestRawBitCellLeftEdgeTape
        (List.append pref [nextRawBit])
        count emittedRawBit tailFirst tail)
      (tailHeadPulledNextRawBitBeforeEmittedCellTape
        pref count nextRawBit emittedRawBit tailFirst tail) :=
  (rawBoundaryNextRawBitPullFromEmittedCellLeftEdgeRoute
    pref count nextRawBit emittedRawBit tailFirst tail).pullerHalts

/-!
## Source first raw-bit cell emission route
-/

structure RawBoundarySourceFirstRawBitCellEmissionRoute
    (skipped count pref : Word Bool)
    (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) : Prop where
  sourceEmitterReady :
    sourceFirstRawBitCellEmissionDescription.SubroutineReady
  sourceEmitterHalts :
    sourceFirstRawBitCellEmissionDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (tailHeadEmittedNearestRawBitCellTape
        pref count rawBit tailFirst tail)
  sourceLeftEdgeEmitterReady :
    sourceFirstRawBitCellLeftEdgeEmissionDescription.SubroutineReady
  sourceLeftEdgeEmitterHalts :
    sourceFirstRawBitCellLeftEdgeEmissionDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (tailHeadEmittedNearestRawBitCellLeftEdgeTape
        pref count rawBit tailFirst tail)

theorem rawBoundarySourceFirstRawBitCellEmissionRoute
    (skipped count pref : Word Bool)
    (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) :
    RawBoundarySourceFirstRawBitCellEmissionRoute
      skipped count pref rawBit tailFirst tail hlayout :=
  { sourceEmitterReady :=
      sourceFirstRawBitCellEmissionDescription_subroutineReady
    sourceEmitterHalts :=
      sourceFirstRawBitCellEmissionDescription_haltsFrom_sourceTape
        skipped count pref rawBit tailFirst tail hlayout
    sourceLeftEdgeEmitterReady :=
      sourceFirstRawBitCellLeftEdgeEmissionDescription_subroutineReady
    sourceLeftEdgeEmitterHalts :=
      sourceFirstRawBitCellLeftEdgeEmissionDescription_haltsFrom_sourceTape
        skipped count pref rawBit tailFirst tail hlayout }

theorem rawBoundary_sourceFirstRawBitCellEmission_halts
    (skipped count pref : Word Bool)
    (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) :
    sourceFirstRawBitCellEmissionDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (tailHeadEmittedNearestRawBitCellTape
        pref count rawBit tailFirst tail) :=
  (rawBoundarySourceFirstRawBitCellEmissionRoute
    skipped count pref rawBit tailFirst tail hlayout).sourceEmitterHalts

theorem rawBoundary_sourceFirstRawBitCellLeftEdgeEmission_halts
    (skipped count pref : Word Bool)
    (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) :
    sourceFirstRawBitCellLeftEdgeEmissionDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (tailHeadEmittedNearestRawBitCellLeftEdgeTape
        pref count rawBit tailFirst tail) :=
  (rawBoundarySourceFirstRawBitCellEmissionRoute
    skipped count pref rawBit tailFirst tail hlayout).sourceLeftEdgeEmitterHalts

theorem rawBoundary_sourceFirstRawBitCellEmission_exists_of_nonempty
    (skipped count : Word Bool)
    (h : List.append skipped count ≠ [])
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    exists pref : Word Bool, exists rawBit : Bool,
      List.append skipped count = List.append pref [rawBit] ∧
        sourceFirstRawBitCellEmissionDescription.HaltsFromTape
          (sourceTape skipped count (some tailFirst :: tail))
          (tailHeadEmittedNearestRawBitCellTape
            pref count rawBit tailFirst tail) :=
  sourceFirstRawBitCellEmissionDescription_haltsFrom_sourceTape_of_nonempty
    skipped count h tailFirst tail

theorem rawBoundary_sourceFirstRawBitCellLeftEdgeEmission_exists_of_nonempty
    (skipped count : Word Bool)
    (h : List.append skipped count ≠ [])
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    exists pref : Word Bool, exists rawBit : Bool,
      List.append skipped count = List.append pref [rawBit] ∧
        sourceFirstRawBitCellLeftEdgeEmissionDescription.HaltsFromTape
          (sourceTape skipped count (some tailFirst :: tail))
          (tailHeadEmittedNearestRawBitCellLeftEdgeTape
            pref count rawBit tailFirst tail) :=
  sourceFirstRawBitCellLeftEdgeEmissionDescription_haltsFrom_sourceTape_of_nonempty
    skipped count h tailFirst tail

/-!
## Source first-two raw-bit cell emission route
-/

structure RawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionRoute
    (skipped count pref : Word Bool) (scratchTail : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count =
        List.append (List.append pref [nextRawBit]) [emittedRawBit])
    (hcount : count.length = scratchTail + 3) : Prop where
  sourceTwoEmitterReady :
    sourceFirstTwoRawBitCellsLeftEdgeEmissionDescription.SubroutineReady
  sourceTwoEmitterHalts :
    sourceFirstTwoRawBitCellsLeftEdgeEmissionDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
        pref scratchTail nextRawBit emittedRawBit tailFirst tail)
  targetCells :
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
                (some tailFirst :: tail))))
  targetDefaultedCells :
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
                (tailFirst :: tail.map optionBitDefaultFalse))))
  targetLeftLength :
    (tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
      pref scratchTail nextRawBit emittedRawBit tailFirst tail).left.length =
      scratchTail + pref.length + 1

theorem rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionRoute
    (skipped count pref : Word Bool) (scratchTail : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count =
        List.append (List.append pref [nextRawBit]) [emittedRawBit])
    (hcount : count.length = scratchTail + 3) :
    RawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionRoute
      skipped count pref scratchTail nextRawBit emittedRawBit tailFirst
      tail hlayout hcount :=
  { sourceTwoEmitterReady :=
      sourceFirstTwoRawBitCellsLeftEdgeEmissionDescription_subroutineReady
    sourceTwoEmitterHalts :=
      sourceFirstTwoRawBitCellsLeftEdgeEmissionDescription_haltsFrom_sourceTape_of_count_length
        skipped count pref scratchTail nextRawBit emittedRawBit tailFirst
        tail hlayout hcount
    targetCells :=
      tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_cells
        pref scratchTail nextRawBit emittedRawBit tailFirst tail
    targetDefaultedCells :=
      tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_defaultedCells
        pref scratchTail nextRawBit emittedRawBit tailFirst tail
    targetLeftLength :=
      tailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_left_length
        pref scratchTail nextRawBit emittedRawBit tailFirst tail }

theorem rawBoundary_sourceFirstTwoRawBitCellsLeftEdgeEmission_halts
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
  (rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionRoute
    skipped count pref scratchTail nextRawBit emittedRawBit tailFirst
    tail hlayout hcount).sourceTwoEmitterHalts

theorem rawBoundary_sourceFirstTwoRawBitCellsLeftEdgeEmission_exists_of_three_le_count_length
    (skipped count pref : Word Bool)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count =
        List.append (List.append pref [nextRawBit]) [emittedRawBit])
    (hcount : 3 <= count.length) :
    exists scratchTail : Nat,
      exists hscratch : count.length = scratchTail + 3,
        RawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionRoute
          skipped count pref scratchTail nextRawBit emittedRawBit tailFirst
          tail hlayout hscratch := by
  rcases nat_exists_eq_add_of_le hcount with ⟨scratchTail, hscratch⟩
  exact
    ⟨scratchTail, hscratch,
      rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionRoute
        skipped count pref scratchTail nextRawBit emittedRawBit tailFirst
        tail hlayout hscratch⟩

theorem rawBoundary_sourceFirstTwoRawBitCellsLeftEdgeEmission_halts_exists_of_three_le_count_length
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
      rawBoundary_sourceFirstTwoRawBitCellsLeftEdgeEmission_halts
        skipped count pref scratchTail nextRawBit emittedRawBit tailFirst
        tail hlayout hscratch⟩

theorem rawBoundary_sourceFirstTwoRawBitCellsLeftEdgeEmission_exists_of_two_le_layout_length_three_le_count_length
    (skipped count : Word Bool)
    (hlayoutLength : 2 <= (List.append skipped count).length)
    (hcount : 3 <= count.length)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    exists pref : Word Bool, exists nextRawBit : Bool,
      exists emittedRawBit : Bool, exists scratchTail : Nat,
        exists hlayout :
          List.append skipped count =
            List.append (List.append pref [nextRawBit]) [emittedRawBit],
        exists hscratch : count.length = scratchTail + 3,
          RawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionRoute
            skipped count pref scratchTail nextRawBit emittedRawBit tailFirst
            tail hlayout hscratch := by
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
    ⟨pref, nextRawBit, emittedRawBit, scratchTail, hlayout',
      hscratch,
      rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionRoute
        skipped count pref scratchTail nextRawBit emittedRawBit tailFirst
        tail hlayout' hscratch⟩

theorem rawBoundary_sourceFirstTwoRawBitCellsLeftEdgeEmission_halts_exists_of_two_le_layout_length_three_le_count_length
    (skipped count : Word Bool)
    (hlayoutLength : 2 <= (List.append skipped count).length)
    (hcount : 3 <= count.length)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
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
      rawBoundary_sourceFirstTwoRawBitCellsLeftEdgeEmission_exists_of_two_le_layout_length_three_le_count_length
        skipped count hlayoutLength hcount tailFirst tail with
    ⟨pref, nextRawBit, emittedRawBit, scratchTail, hlayout,
      hscratch, route⟩
  exact
    ⟨pref, nextRawBit, emittedRawBit, scratchTail,
      hlayout, hscratch, route.sourceTwoEmitterHalts⟩

/-!
## Source first-three raw-bit cell emission route
-/

structure RawBoundarySourceFirstThreeRawBitCellsLeftEdgeEmissionRoute
    (skipped count pref : Word Bool) (scratchOne scratchTail : Nat)
    (thirdRawBit secondRawBit firstRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count =
        List.append
          (List.append (List.append pref [thirdRawBit]) [secondRawBit])
          [firstRawBit])
    (hcount : count.length = scratchOne + 3)
    (hscratch : scratchOne = scratchTail + 3) : Prop where
  sourceThreeEmitterReady :
    sourceFirstThreeRawBitCellsLeftEdgeEmissionDescription.SubroutineReady
  sourceThreeEmitterHalts :
    sourceFirstThreeRawBitCellsLeftEdgeEmissionDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (tailHeadEmittedThirdRawBitCellBeforeTwoEmittedCellsLeftEdgeTape
        pref scratchTail thirdRawBit secondRawBit firstRawBit
        tailFirst tail)
  targetCells :
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
                  (some tailFirst :: tail)))))
  targetDefaultedCells :
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
                  (tailFirst :: tail.map optionBitDefaultFalse)))))
  targetLeftLength :
    (tailHeadEmittedThirdRawBitCellBeforeTwoEmittedCellsLeftEdgeTape
      pref scratchTail thirdRawBit secondRawBit firstRawBit
      tailFirst tail).left.length =
      scratchTail + pref.length + 1

theorem rawBoundarySourceFirstThreeRawBitCellsLeftEdgeEmissionRoute
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
    RawBoundarySourceFirstThreeRawBitCellsLeftEdgeEmissionRoute
      skipped count pref scratchOne scratchTail thirdRawBit secondRawBit
      firstRawBit tailFirst tail hlayout hcount hscratch :=
  { sourceThreeEmitterReady :=
      sourceFirstThreeRawBitCellsLeftEdgeEmissionDescription_subroutineReady
    sourceThreeEmitterHalts :=
      sourceFirstThreeRawBitCellsLeftEdgeEmissionDescription_haltsFrom_sourceTape_of_count_lengths
        skipped count pref scratchOne scratchTail thirdRawBit secondRawBit
        firstRawBit tailFirst tail hlayout hcount hscratch
    targetCells :=
      tailHeadEmittedThirdRawBitCellBeforeTwoEmittedCellsLeftEdgeTape_cells
        pref scratchTail thirdRawBit secondRawBit firstRawBit tailFirst tail
    targetDefaultedCells :=
      tailHeadEmittedThirdRawBitCellBeforeTwoEmittedCellsLeftEdgeTape_defaultedCells
        pref scratchTail thirdRawBit secondRawBit firstRawBit tailFirst tail
    targetLeftLength :=
      tailHeadEmittedThirdRawBitCellBeforeTwoEmittedCellsLeftEdgeTape_left_length
        pref scratchTail thirdRawBit secondRawBit firstRawBit tailFirst tail }

theorem rawBoundary_sourceFirstThreeRawBitCellsLeftEdgeEmission_halts
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
  (rawBoundarySourceFirstThreeRawBitCellsLeftEdgeEmissionRoute
    skipped count pref scratchOne scratchTail thirdRawBit secondRawBit
    firstRawBit tailFirst tail hlayout hcount hscratch).sourceThreeEmitterHalts

theorem rawBoundary_sourceFirstThreeRawBitCellsLeftEdgeEmission_exists_of_three_le_layout_length_six_le_count_length
    (skipped count : Word Bool)
    (hlayoutLength : 3 <= (List.append skipped count).length)
    (hcountLength : 6 <= count.length)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    exists pref : Word Bool, exists thirdRawBit : Bool,
      exists secondRawBit : Bool, exists firstRawBit : Bool,
        exists scratchOne : Nat, exists scratchTail : Nat,
          exists hlayout :
            List.append skipped count =
              List.append
                (List.append (List.append pref [thirdRawBit])
                  [secondRawBit])
                [firstRawBit],
          exists hcount : count.length = scratchOne + 3,
          exists hscratch : scratchOne = scratchTail + 3,
            RawBoundarySourceFirstThreeRawBitCellsLeftEdgeEmissionRoute
              skipped count pref scratchOne scratchTail thirdRawBit
              secondRawBit firstRawBit tailFirst tail
              hlayout hcount hscratch := by
  rcases
      FoC.Computability.list_exists_append_three_of_three_le_length
        (List.append skipped count) hlayoutLength with
    ⟨pref, thirdRawBit, secondRawBit, firstRawBit, hlayout⟩
  have hlayout' :
      List.append skipped count =
        List.append
          (List.append (List.append pref [thirdRawBit]) [secondRawBit])
          [firstRawBit] := by
    simpa [List.append_assoc] using hlayout
  rcases nat_exists_eq_add_of_le hcountLength with
    ⟨scratchTail, hlength⟩
  let scratchOne : Nat := scratchTail + 3
  have hcount : count.length = scratchOne + 3 := by
    dsimp [scratchOne]
    rw [hlength]
  have hscratch : scratchOne = scratchTail + 3 := rfl
  exact
    ⟨pref, thirdRawBit, secondRawBit, firstRawBit,
      scratchOne, scratchTail, hlayout', hcount, hscratch,
      rawBoundarySourceFirstThreeRawBitCellsLeftEdgeEmissionRoute
        skipped count pref scratchOne scratchTail thirdRawBit
        secondRawBit firstRawBit tailFirst tail hlayout'
        hcount hscratch⟩

theorem rawBoundary_sourceFirstThreeRawBitCellsLeftEdgeEmission_halts_exists_of_three_le_layout_length_six_le_count_length
    (skipped count : Word Bool)
    (hlayoutLength : 3 <= (List.append skipped count).length)
    (hcountLength : 6 <= count.length)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    exists pref : Word Bool, exists thirdRawBit : Bool,
      exists secondRawBit : Bool, exists firstRawBit : Bool,
        exists scratchOne : Nat, exists scratchTail : Nat,
          List.append skipped count =
              List.append
                (List.append (List.append pref [thirdRawBit])
                  [secondRawBit])
                [firstRawBit] ∧
            count.length = scratchOne + 3 ∧
              scratchOne = scratchTail + 3 ∧
                sourceFirstThreeRawBitCellsLeftEdgeEmissionDescription.HaltsFromTape
                  (sourceTape skipped count (some tailFirst :: tail))
                  (tailHeadEmittedThirdRawBitCellBeforeTwoEmittedCellsLeftEdgeTape
                    pref scratchTail thirdRawBit secondRawBit firstRawBit
                    tailFirst tail) := by
  rcases
      rawBoundary_sourceFirstThreeRawBitCellsLeftEdgeEmission_exists_of_three_le_layout_length_six_le_count_length
        skipped count hlayoutLength hcountLength tailFirst tail with
    ⟨pref, thirdRawBit, secondRawBit, firstRawBit,
      scratchOne, scratchTail, hlayout, hcount, hscratch, route⟩
  exact
    ⟨pref, thirdRawBit, secondRawBit, firstRawBit,
      scratchOne, scratchTail, hlayout, hcount, hscratch,
      route.sourceThreeEmitterHalts⟩

/-!
## Empty-layout fixed emission route
-/

structure RawBoundaryEmptyLayoutEmissionRoute
    (tailFirst : Bool)
    (tail : List (Option Bool)) : Prop where
  emptyPrependerReady :
    prependEmptyLayoutLeftOfHeadDescription.SubroutineReady
  emptyPrependerHaltsFromTailHead :
    prependEmptyLayoutLeftOfHeadDescription.HaltsFromTape
      (tailHeadHandoffTape [] [] tailFirst tail)
      (rightEdgeTape [] [] tailFirst tail)
  sourceToRightEdgeReady :
    emptyLayoutTailHandoffRightEdgeDescription.SubroutineReady
  sourceToRightEdgeHalts :
    emptyLayoutTailHandoffRightEdgeDescription.HaltsFromTape
      (sourceTape [] [] (some tailFirst :: tail))
      (rightEdgeTape [] [] tailFirst tail)
  coreDescriptionHalts :
    rawBoundaryRightEdgeEmitterCoreDescription.HaltsFromTapeEquiv
      (sourceTape [] [] (some tailFirst :: tail))
      (encodedLeftEdgeTape [] [] tailFirst tail)

theorem rawBoundaryEmptyLayoutEmissionRoute
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    RawBoundaryEmptyLayoutEmissionRoute tailFirst tail :=
  { emptyPrependerReady :=
      prependEmptyLayoutLeftOfHeadDescription_subroutineReady
    emptyPrependerHaltsFromTailHead :=
      prependEmptyLayoutLeftOfHeadDescription_haltsFrom_tailHeadHandoffTape
        tailFirst tail
    sourceToRightEdgeReady :=
      emptyLayoutTailHandoffRightEdgeDescription_subroutineReady
    sourceToRightEdgeHalts :=
      emptyLayoutTailHandoffRightEdgeDescription_haltsFrom_sourceTape
        tailFirst tail
    coreDescriptionHalts :=
      rawBoundaryRightEdgeEmitterCoreDescription_haltsFrom_sourceTape_encodedLeftEdge_empty
        tailFirst tail }

/-!
## Scratch-ready generated emission route
-/

structure RawBoundaryScratchReadyEmissionRoute
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) : Prop where
  scratchCells :
    Tape.cells (scratchReadyTape skipped count tailFirst tail) =
      List.append
        (List.replicate
          (encodedLayoutScratchCellCount (List.append skipped count))
          (none : Option Bool))
        (some tailFirst :: tail)
  scratchDefaultedCells :
    List.map optionBitDefaultFalse
        (Tape.cells (scratchReadyTape skipped count tailFirst tail)) =
      List.append
        (List.replicate
          (encodedLayoutScratchCellCount (List.append skipped count))
          false)
        (tailFirst :: tail.map optionBitDefaultFalse)
  scratchLeftLength :
    (scratchReadyTape skipped count tailFirst tail).left.length =
      encodedLayoutScratchCellCount (List.append skipped count)
  scratchLeftLengthAsEncodedBits :
    (scratchReadyTape skipped count tailFirst tail).left.length =
      (encodedLayoutBits (List.append skipped count)).length
  generatedEmitterReady :
    (prependEncodedLayoutLeftOfHeadDescription
      (List.append skipped count)).SubroutineReady
  generatedEmitterHalts :
    (prependEncodedLayoutLeftOfHeadDescription
      (List.append skipped count)).HaltsFromTape
      (scratchReadyTape skipped count tailFirst tail)
      (rightEdgeTape skipped count tailFirst tail)

theorem rawBoundaryScratchReadyEmissionRoute
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    RawBoundaryScratchReadyEmissionRoute
      skipped count tailFirst tail :=
  { scratchCells :=
      scratchReadyTape_cells skipped count tailFirst tail
    scratchDefaultedCells :=
      scratchReadyTape_defaultedCells skipped count tailFirst tail
    scratchLeftLength :=
      scratchReadyTape_left_length skipped count tailFirst tail
    scratchLeftLengthAsEncodedBits :=
      scratchReadyTape_left_length_eq_encodedLayoutBits_length
        skipped count tailFirst tail
    generatedEmitterReady :=
      prependEncodedLayoutLeftOfHeadDescription_subroutineReady
        (List.append skipped count)
    generatedEmitterHalts :=
      prependEncodedLayoutLeftOfHeadDescription_haltsFrom_scratchReadyTape
        skipped count tailFirst tail }

theorem rawBoundary_scratchReady_cells
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.cells (scratchReadyTape skipped count tailFirst tail) =
      List.append
        (List.replicate
          (encodedLayoutScratchCellCount (List.append skipped count))
          (none : Option Bool))
        (some tailFirst :: tail) :=
  (rawBoundaryScratchReadyEmissionRoute
    skipped count tailFirst tail).scratchCells

theorem rawBoundary_scratchReady_generatedEmitter_halts
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (prependEncodedLayoutLeftOfHeadDescription
      (List.append skipped count)).HaltsFromTape
      (scratchReadyTape skipped count tailFirst tail)
      (rightEdgeTape skipped count tailFirst tail) :=
  (rawBoundaryScratchReadyEmissionRoute
    skipped count tailFirst tail).generatedEmitterHalts

theorem rawBoundary_scratchReady_leftLengthAsEncodedBits
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (scratchReadyTape skipped count tailFirst tail).left.length =
      (encodedLayoutBits (List.append skipped count)).length :=
  (rawBoundaryScratchReadyEmissionRoute
    skipped count tailFirst tail).scratchLeftLengthAsEncodedBits

/-!
## Right-edge endpoint route
-/

structure RawBoundaryRightEdgeEndpointShape
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) : Prop where
  rightEdgeCells :
    Tape.cells (rightEdgeTape skipped count tailFirst tail) =
      List.append
        ((encodedLayoutBits (List.append skipped count)).map some)
        (some tailFirst :: tail)
  rightEdgeDefaultedCells :
    List.map optionBitDefaultFalse
        (Tape.cells (rightEdgeTape skipped count tailFirst tail)) =
      List.append
        (encodedLayoutBits (List.append skipped count))
        (tailFirst :: tail.map optionBitDefaultFalse)
  rightEdgeAsRightToLeftBits :
    rightEdgeTape skipped count tailFirst tail =
      tapeAtCells
        ((rightToLeftEncodedLayoutBits
          (List.append skipped count)).map some)
        (some tailFirst :: tail)
  preRewindAsRightToLeftBits :
    preRewindTape skipped count tailFirst tail =
      Tape.move Direction.left
        (tapeAtCells
          ((rightToLeftEncodedLayoutBits
            (List.append skipped count)).map some)
          (some tailFirst :: tail))
  preRewindMoveRight :
    Tape.move Direction.right
        (preRewindTape skipped count tailFirst tail) =
      rightEdgeTape skipped count tailFirst tail
  rightEdgeLeftLength :
    (rightEdgeTape skipped count tailFirst tail).left.length =
      encodedLayoutScratchCellCount (List.append skipped count)

theorem rawBoundaryRightEdgeEndpointShape
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    RawBoundaryRightEdgeEndpointShape skipped count tailFirst tail :=
  { rightEdgeCells :=
      rightEdgeTape_cells skipped count tailFirst tail
    rightEdgeDefaultedCells :=
      rightEdgeTape_defaultedCells skipped count tailFirst tail
    rightEdgeAsRightToLeftBits :=
      rightEdgeTape_eq_rightToLeftEncodedLayoutBits
        skipped count tailFirst tail
    preRewindAsRightToLeftBits :=
      preRewindTape_eq_rightToLeftEncodedLayoutBits
        skipped count tailFirst tail
    preRewindMoveRight :=
      preRewindTape_moveRight skipped count tailFirst tail
    rightEdgeLeftLength :=
      rightEdgeTape_left_length skipped count tailFirst tail }

theorem rawBoundary_rightEdge_cells
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.cells (rightEdgeTape skipped count tailFirst tail) =
      List.append
        ((encodedLayoutBits (List.append skipped count)).map some)
        (some tailFirst :: tail) :=
  (rawBoundaryRightEdgeEndpointShape
    skipped count tailFirst tail).rightEdgeCells

theorem rawBoundary_rightEdge_defaultedCells
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    List.map optionBitDefaultFalse
        (Tape.cells (rightEdgeTape skipped count tailFirst tail)) =
      List.append
        (encodedLayoutBits (List.append skipped count))
        (tailFirst :: tail.map optionBitDefaultFalse) :=
  (rawBoundaryRightEdgeEndpointShape
    skipped count tailFirst tail).rightEdgeDefaultedCells

theorem rawBoundary_preRewind_moveRight
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.right
        (preRewindTape skipped count tailFirst tail) =
      rightEdgeTape skipped count tailFirst tail :=
  (rawBoundaryRightEdgeEndpointShape
    skipped count tailFirst tail).preRewindMoveRight

theorem rawBoundary_rightEdge_leftLength
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (rightEdgeTape skipped count tailFirst tail).left.length =
      encodedLayoutScratchCellCount (List.append skipped count) :=
  (rawBoundaryRightEdgeEndpointShape
    skipped count tailFirst tail).rightEdgeLeftLength

/-!
## Final rewind endpoint route
-/

def rewindTargetTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells [none]
    (List.append
      ((encodedLayoutBits (List.append skipped count)).map some)
      (some tailFirst :: tail))

structure RawBoundaryRightEdgeRewindRoute
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) : Prop where
  rewindHalts :
    rightEdgeRewindDescription.HaltsFromTape
      (rightEdgeTape skipped count tailFirst tail)
      (rewindTargetTape skipped count tailFirst tail)
  targetCells :
    Tape.cells (rewindTargetTape skipped count tailFirst tail) =
      none ::
        List.append
          ((encodedLayoutBits (List.append skipped count)).map some)
          (some tailFirst :: tail)
  targetDefaultedCells :
    List.map optionBitDefaultFalse
        (Tape.cells (rewindTargetTape skipped count tailFirst tail)) =
      false ::
        List.append
          (encodedLayoutBits (List.append skipped count))
          (tailFirst :: tail.map optionBitDefaultFalse)
  sourceRightEdgeCells :
    Tape.cells (rightEdgeTape skipped count tailFirst tail) =
      List.append
        ((encodedLayoutBits (List.append skipped count)).map some)
        (some tailFirst :: tail)
  sourcePreRewind :
    Tape.move Direction.right
        (preRewindTape skipped count tailFirst tail) =
      rightEdgeTape skipped count tailFirst tail

theorem rawBoundaryRightEdgeRewindRoute
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    RawBoundaryRightEdgeRewindRoute skipped count tailFirst tail :=
  { rewindHalts := by
      simpa [rewindTargetTape] using
        rightEdgeTape_rewind_haltsFromTape
          skipped count tailFirst tail
    targetCells := by
      simpa [rewindTargetTape] using
        rightEdgeTape_rewind_target_cells
          skipped count tailFirst tail
    targetDefaultedCells := by
      simpa [rewindTargetTape] using
        rightEdgeTape_rewind_target_defaultedCells
          skipped count tailFirst tail
    sourceRightEdgeCells :=
      rightEdgeTape_cells skipped count tailFirst tail
    sourcePreRewind :=
      preRewindTape_moveRight skipped count tailFirst tail }

theorem rawBoundary_rewind_halts
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    rightEdgeRewindDescription.HaltsFromTape
      (rightEdgeTape skipped count tailFirst tail)
      (rewindTargetTape skipped count tailFirst tail) :=
  (rawBoundaryRightEdgeRewindRoute
    skipped count tailFirst tail).rewindHalts

theorem rawBoundary_rewind_target_cells
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.cells (rewindTargetTape skipped count tailFirst tail) =
      none ::
        List.append
          ((encodedLayoutBits (List.append skipped count)).map some)
          (some tailFirst :: tail) :=
  (rawBoundaryRightEdgeRewindRoute
    skipped count tailFirst tail).targetCells

theorem rawBoundary_rewind_target_defaultedCells
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    List.map optionBitDefaultFalse
        (Tape.cells (rewindTargetTape skipped count tailFirst tail)) =
      false ::
        List.append
          (encodedLayoutBits (List.append skipped count))
          (tailFirst :: tail.map optionBitDefaultFalse) :=
  (rawBoundaryRightEdgeRewindRoute
    skipped count tailFirst tail).targetDefaultedCells

/-!
## Structured emitter route
-/

structure StructuredRawBoundaryEmitterRoute : Prop where
  cellEmitterSupported :
    Structured.MultiTapeLowering.SupportsReadWriteRows3
      structuredRawBoundaryRightEdgeCellEmitterDescription
  emitterSupported :
    Structured.MultiTapeLowering.SupportsReadWriteRows3
      structuredRawBoundaryRightEdgeEmitterDescription
  emitterWellFormed :
    structuredRawBoundaryRightEdgeEmitterDescription.WellFormed
  emitterHaltTransitionFree :
    structuredRawBoundaryRightEdgeEmitterDescription.HaltTransitionFree
  loweredEmitterReady :
    MachineDescription.SubroutineReady
      loweredStructuredRawBoundaryRightEdgeEmitterDescription
  loweredEmitterRun :
    forall layout : Word Bool,
      MachineDescription.HaltsFromTapeEquiv
        loweredStructuredRawBoundaryRightEdgeEmitterDescription
        (Structured.MultiTapeLowering.encodedGuardedStructuredTapes
          (structuredRawBoundaryRightEdgeEmitterSourceTapes layout))
        (Structured.MultiTapeLowering.encodedGuardedStructuredTapes
          (structuredRawBoundaryRightEdgeEmitterFinalTapes layout))
  outputTapeNormalized :
    forall bits : Word Bool,
      Tape.normalizedOutput (structuredRawBoundaryOutputTape bits) = bits
  rightEdgeOutputTapeNormalized :
    forall layout : Word Bool,
      Tape.normalizedOutput
          (structuredRawBoundaryRightEdgeEmitterOutputTape layout) =
        encodedLayoutBits layout
  sourceTapesEmpty :
    structuredRawBoundaryRightEdgeEmitterSourceTapes [] =
      [ Tape.input ([] : Word Bool), Tape.blank, Tape.blank ]
  runEmptyHalts :
    (structuredRawBoundaryRightEdgeEmitterDescription.runConfig 11
        { state := structuredRawBoundaryRightEdgeEmitterDescription.start
          tapes := structuredRawBoundaryRightEdgeEmitterSourceTapes [] }).state =
      structuredRawBoundaryRightEdgeEmitterDescription.halt
  runEmptyOutput :
    Structured.Description.tapeAt
        (structuredRawBoundaryRightEdgeEmitterDescription.runConfig 11
          { state := structuredRawBoundaryRightEdgeEmitterDescription.start
            tapes := structuredRawBoundaryRightEdgeEmitterSourceTapes [] }).tapes
        2 =
      structuredRawBoundaryRightEdgeEmitterOutputTape []
  runFalseHalts :
    (structuredRawBoundaryRightEdgeEmitterDescription.runConfig 21
        { state := structuredRawBoundaryRightEdgeEmitterDescription.start
          tapes := structuredRawBoundaryRightEdgeEmitterSourceTapes [false] }).state =
      structuredRawBoundaryRightEdgeEmitterDescription.halt
  runFalseOutput :
    Structured.Description.tapeAt
        (structuredRawBoundaryRightEdgeEmitterDescription.runConfig 21
          { state := structuredRawBoundaryRightEdgeEmitterDescription.start
            tapes := structuredRawBoundaryRightEdgeEmitterSourceTapes [false] }).tapes
        2 =
      structuredRawBoundaryRightEdgeEmitterOutputTape [false]
  runTrueHalts :
    (structuredRawBoundaryRightEdgeEmitterDescription.runConfig 21
        { state := structuredRawBoundaryRightEdgeEmitterDescription.start
          tapes := structuredRawBoundaryRightEdgeEmitterSourceTapes [true] }).state =
      structuredRawBoundaryRightEdgeEmitterDescription.halt
  runTrueOutput :
    Structured.Description.tapeAt
        (structuredRawBoundaryRightEdgeEmitterDescription.runConfig 21
          { state := structuredRawBoundaryRightEdgeEmitterDescription.start
            tapes := structuredRawBoundaryRightEdgeEmitterSourceTapes [true] }).tapes
        2 =
      structuredRawBoundaryRightEdgeEmitterOutputTape [true]

theorem structuredRawBoundaryEmitterRoute :
    StructuredRawBoundaryEmitterRoute :=
  { cellEmitterSupported :=
      structuredRawBoundaryRightEdgeCellEmitterDescription_supported
    emitterSupported :=
      structuredRawBoundaryRightEdgeEmitterDescription_supported
    emitterWellFormed :=
      structuredRawBoundaryRightEdgeEmitterDescription_wellFormed
    emitterHaltTransitionFree :=
      structuredRawBoundaryRightEdgeEmitterDescription_haltTransitionFree
    loweredEmitterReady :=
      loweredStructuredRawBoundaryRightEdgeEmitterDescription_subroutineReady
    loweredEmitterRun :=
      loweredStructuredRawBoundaryRightEdgeEmitterDescription_haltsFrom_structuredTapes
    outputTapeNormalized :=
      structuredRawBoundaryOutputTape_normalizedOutput
    rightEdgeOutputTapeNormalized :=
      structuredRawBoundaryRightEdgeEmitterOutputTape_normalizedOutput
    sourceTapesEmpty := rfl
    runEmptyHalts :=
      structuredRawBoundaryRightEdgeEmitterDescription_run_empty_halts
    runEmptyOutput :=
      structuredRawBoundaryRightEdgeEmitterDescription_run_empty_output
    runFalseHalts :=
      structuredRawBoundaryRightEdgeEmitterDescription_run_false_halts
    runFalseOutput :=
      structuredRawBoundaryRightEdgeEmitterDescription_run_false_output
    runTrueHalts :=
      structuredRawBoundaryRightEdgeEmitterDescription_run_true_halts
    runTrueOutput :=
      structuredRawBoundaryRightEdgeEmitterDescription_run_true_output }

theorem structuredRawBoundaryEmitterRoute_outputTape_normalizedOutput
    (bits : Word Bool) :
    Tape.normalizedOutput (structuredRawBoundaryOutputTape bits) = bits :=
  structuredRawBoundaryEmitterRoute.outputTapeNormalized bits

theorem structuredRawBoundaryEmitterRoute_rightEdgeOutputTape_normalizedOutput
    (layout : Word Bool) :
    Tape.normalizedOutput
        (structuredRawBoundaryRightEdgeEmitterOutputTape layout) =
      encodedLayoutBits layout :=
  structuredRawBoundaryEmitterRoute.rightEdgeOutputTapeNormalized layout

/-!
## Core construction route
-/

structure RawBoundaryRightEdgeEmitterCoreRoute : Prop where
  coreWellFormed :
    rawBoundaryRightEdgeEmitterCoreDescription.WellFormed
  coreHaltTransitionFree :
    rawBoundaryRightEdgeEmitterCoreDescription.HaltTransitionFree
  coreReady :
    rawBoundaryRightEdgeEmitterCoreDescription.SubroutineReady
  wrapperWellFormed :
    rawBoundaryRightEdgeEmitterDescription.WellFormed
  wrapperHaltTransitionFree :
    rawBoundaryRightEdgeEmitterDescription.HaltTransitionFree
  wrapperReady :
    rawBoundaryRightEdgeEmitterDescription.SubroutineReady
  coreHaltsEncodedLeftEdge :
    forall skipped count : Word Bool,
    forall tailFirst : Bool,
    forall tail : List (Option Bool),
      rawBoundaryRightEdgeEmitterCoreDescription.HaltsFromTapeEquiv
        (sourceTape skipped count (some tailFirst :: tail))
        (encodedLeftEdgeTape skipped count tailFirst tail)
  wrapperHaltsEncodedLeftEdge :
    forall skipped count : Word Bool,
    forall tailFirst : Bool,
    forall tail : List (Option Bool),
      rawBoundaryRightEdgeEmitterDescription.HaltsFromTapeEquiv
        (sourceTape skipped count (some tailFirst :: tail))
        (encodedLeftEdgeTape skipped count tailFirst tail)
  spec :
    Spec rawBoundaryRightEdgeEmitterDescription
  construction :
    Construction

def RawBoundaryRightEdgeEmitterCoreRouteConstruction : Prop :=
  RawBoundaryRightEdgeEmitterCoreRoute

theorem rawBoundaryRightEdgeEmitterCoreRoute :
    RawBoundaryRightEdgeEmitterCoreRoute :=
  { coreWellFormed :=
      rawBoundaryRightEdgeEmitterCoreDescription_subroutineReady.left
    coreHaltTransitionFree :=
      rawBoundaryRightEdgeEmitterCoreDescription_subroutineReady.right
    coreReady :=
      rawBoundaryRightEdgeEmitterCoreDescription_subroutineReady
    wrapperWellFormed :=
      rawBoundaryRightEdgeEmitterDescription_subroutineReady.left
    wrapperHaltTransitionFree :=
      rawBoundaryRightEdgeEmitterDescription_subroutineReady.right
    wrapperReady :=
      rawBoundaryRightEdgeEmitterDescription_subroutineReady
    coreHaltsEncodedLeftEdge := by
      intro skipped count tailFirst tail
      exact
        rawBoundaryRightEdgeEmitterCoreDescription_haltsFrom_sourceTape_encodedLeftEdge
          skipped count tailFirst tail
    wrapperHaltsEncodedLeftEdge := by
      intro skipped count tailFirst tail
      exact
        rawBoundaryRightEdgeEmitterDescription_haltsFrom_sourceTape
          skipped count tailFirst tail
    spec := by
      constructor
      · exact rawBoundaryRightEdgeEmitterDescription_subroutineReady
      · intro skipped count tailFirst tail
        exact
          rawBoundaryRightEdgeEmitterDescription_haltsFrom_sourceTape
            skipped count tailFirst tail
    construction :=
      construction_core }

theorem rawBoundaryRightEdgeEmitterCoreRouteConstruction_core :
    RawBoundaryRightEdgeEmitterCoreRouteConstruction :=
  rawBoundaryRightEdgeEmitterCoreRoute

theorem construction_core_route : Construction :=
  rawBoundaryRightEdgeEmitterCoreRoute.construction

/-!
## Combined endpoint route
-/

structure RawBoundaryRightEdgeEmitterEndpointRoute
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) : Prop where
  sourceEndpoint :
    RawBoundarySourceEndpointShape
      skipped count (some tailFirst :: tail)
  rightEdgeEndpoint :
    RawBoundaryRightEdgeEndpointShape
      skipped count tailFirst tail
  rewindEndpoint :
    RawBoundaryRightEdgeRewindRoute
      skipped count tailFirst tail
  coreRoute :
    RawBoundaryRightEdgeEmitterCoreRoute
  sourceToEncodedLeftEdge :
    rawBoundaryRightEdgeEmitterCoreDescription.HaltsFromTapeEquiv
      (sourceTape skipped count (some tailFirst :: tail))
      (encodedLeftEdgeTape skipped count tailFirst tail)
  wrapperToEncodedLeftEdge :
    rawBoundaryRightEdgeEmitterDescription.HaltsFromTapeEquiv
      (sourceTape skipped count (some tailFirst :: tail))
      (encodedLeftEdgeTape skipped count tailFirst tail)
  rightEdgeMove :
    Tape.move Direction.right
        (preRewindTape skipped count tailFirst tail) =
      rightEdgeTape skipped count tailFirst tail

theorem rawBoundaryRightEdgeEmitterEndpointRoute
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    RawBoundaryRightEdgeEmitterEndpointRoute
      skipped count tailFirst tail :=
  { sourceEndpoint :=
      rawBoundarySourceEndpointShape
        skipped count (some tailFirst :: tail)
    rightEdgeEndpoint :=
      rawBoundaryRightEdgeEndpointShape
        skipped count tailFirst tail
    rewindEndpoint :=
      rawBoundaryRightEdgeRewindRoute
        skipped count tailFirst tail
    coreRoute :=
      rawBoundaryRightEdgeEmitterCoreRoute
    sourceToEncodedLeftEdge :=
      rawBoundaryRightEdgeEmitterCoreDescription_haltsFrom_sourceTape_encodedLeftEdge
        skipped count tailFirst tail
    wrapperToEncodedLeftEdge :=
      rawBoundaryRightEdgeEmitterDescription_haltsFrom_sourceTape
        skipped count tailFirst tail
    rightEdgeMove :=
      preRewindTape_moveRight skipped count tailFirst tail }

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
