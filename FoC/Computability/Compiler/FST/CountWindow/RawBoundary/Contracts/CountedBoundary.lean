import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.CountedBoundary

set_option doc.verso true

/-!
# Raw-boundary counted-boundary route contracts

This module packages the checked count-window bridge routes used by the
raw-boundary right-edge emitter construction.  It is split from the main route
contract file to keep the public route inventory below the large-file limit.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace CountWindowRawSourceEncoder
namespace RawBoundaryRightEdgeEmitter

structure RawBoundaryLeftMarkedStartRoute
    (skipped count : Word Bool)
    (h : List.append skipped count ≠ [])
    (tail : List (Option Bool)) : Prop where
  markedStartCells :
    Tape.cells (rawBoundaryLeftMarkedStartTape skipped count tail) =
      some false ::
        List.append ((List.append skipped count).map some)
          (none ::
            none ::
              none ::
                List.append
                  (List.replicate count.length (none : Option Bool))
                  tail)
  routeReady :
    rawBoundarySourceToLeftMarkedStartDescription.SubroutineReady
  routeHalts :
    rawBoundarySourceToLeftMarkedStartDescription.HaltsFromTape
      (sourceTape skipped count tail)
      (rawBoundaryLeftMarkedStartTape skipped count tail)

theorem rawBoundaryLeftMarkedStartRoute
    (skipped count : Word Bool)
    (h : List.append skipped count ≠ [])
    (tail : List (Option Bool)) :
    RawBoundaryLeftMarkedStartRoute skipped count h tail :=
  { markedStartCells :=
      rawBoundaryLeftMarkedStartTape_cells skipped count tail
    routeReady :=
      rawBoundarySourceToLeftMarkedStartDescription_ready
    routeHalts :=
      rawBoundarySourceToLeftMarkedStartDescription_haltsFrom_sourceTape
        skipped count h tail }

theorem rawBoundary_leftMarkedStart_halts
    (skipped count : Word Bool)
    (h : List.append skipped count ≠ [])
    (tail : List (Option Bool)) :
    rawBoundarySourceToLeftMarkedStartDescription.HaltsFromTape
      (sourceTape skipped count tail)
      (rawBoundaryLeftMarkedStartTape skipped count tail) :=
  (rawBoundaryLeftMarkedStartRoute skipped count h tail).routeHalts

structure RawBoundaryLeftMarkedTailHandoffRoute
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) : Prop where
  routeReady :
    rawBoundaryLeftMarkedStartToTailLeftHandoffDescription.SubroutineReady
  routeHalts :
    rawBoundaryLeftMarkedStartToTailLeftHandoffDescription.HaltsFromTape
      (rawBoundaryLeftMarkedStartTape
        skipped count (some tailFirst :: tail))
      (rawBoundaryLeftMarkedTailLeftHandoffTape
        skipped count tailFirst tail)
  tailLeftMoveRight :
    Tape.move Direction.right
        (rawBoundaryLeftMarkedTailLeftHandoffTape
          skipped count tailFirst tail) =
      rawBoundaryLeftMarkedTailHeadHandoffTape
        skipped count tailFirst tail

theorem rawBoundaryLeftMarkedTailHandoffRoute
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    RawBoundaryLeftMarkedTailHandoffRoute
      skipped count tailFirst tail :=
  { routeReady :=
      rawBoundaryLeftMarkedStartToTailLeftHandoffDescription_ready
    routeHalts :=
      rawBoundaryLeftMarkedStartToTailLeftHandoffDescription_haltsFrom
        skipped count tailFirst tail
    tailLeftMoveRight :=
      rawBoundaryLeftMarkedTailLeftHandoffTape_moveRight
        skipped count tailFirst tail }

theorem rawBoundary_leftMarkedTailHandoff_halts
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    rawBoundaryLeftMarkedStartToTailLeftHandoffDescription.HaltsFromTape
      (rawBoundaryLeftMarkedStartTape
        skipped count (some tailFirst :: tail))
      (rawBoundaryLeftMarkedTailLeftHandoffTape
        skipped count tailFirst tail) :=
  (rawBoundaryLeftMarkedTailHandoffRoute
    skipped count tailFirst tail).routeHalts

structure RawBoundarySourceToLeftMarkedTailHeadHandoffRoute
    (skipped count : Word Bool)
    (h : List.append skipped count ≠ [])
    (tailFirst : Bool)
    (tail : List (Option Bool)) : Prop where
  tailLeftRouteReady :
    rawBoundarySourceToLeftMarkedTailLeftHandoffDescription.SubroutineReady
  tailLeftRouteHalts :
    rawBoundarySourceToLeftMarkedTailLeftHandoffDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (rawBoundaryLeftMarkedTailLeftHandoffTape
        skipped count tailFirst tail)
  tailHeadRouteReady :
    rawBoundarySourceToLeftMarkedTailHeadHandoffDescription.SubroutineReady
  tailHeadRouteHalts :
    rawBoundarySourceToLeftMarkedTailHeadHandoffDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (rawBoundaryLeftMarkedTailHeadHandoffTape
        skipped count tailFirst tail)

theorem rawBoundarySourceToLeftMarkedTailHeadHandoffRoute
    (skipped count : Word Bool)
    (h : List.append skipped count ≠ [])
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    RawBoundarySourceToLeftMarkedTailHeadHandoffRoute
      skipped count h tailFirst tail :=
  { tailLeftRouteReady :=
      rawBoundarySourceToLeftMarkedTailLeftHandoffDescription_ready
    tailLeftRouteHalts :=
      rawBoundarySourceToLeftMarkedTailLeftHandoffDescription_haltsFrom_sourceTape
        skipped count h tailFirst tail
    tailHeadRouteReady :=
      rawBoundarySourceToLeftMarkedTailHeadHandoffDescription_ready
    tailHeadRouteHalts :=
      rawBoundarySourceToLeftMarkedTailHeadHandoffDescription_haltsFrom_sourceTape
        skipped count h tailFirst tail }

theorem rawBoundary_sourceToLeftMarkedTailHeadHandoff_halts
    (skipped count : Word Bool)
    (h : List.append skipped count ≠ [])
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    rawBoundarySourceToLeftMarkedTailHeadHandoffDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (rawBoundaryLeftMarkedTailHeadHandoffTape
        skipped count tailFirst tail) :=
  (rawBoundarySourceToLeftMarkedTailHeadHandoffRoute
    skipped count h tailFirst tail).tailHeadRouteHalts

structure RawBoundaryLeftMarkedTailHeadNearestRawBitPullRoute
    (skipped count pref : Word Bool)
    (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) : Prop where
  pullerReady :
    markerAwarePullNearestRawBitDescription.SubroutineReady
  sourceAsMarkerAwarePull :
    rawBoundaryLeftMarkedTailHeadHandoffTape
        skipped count tailFirst tail =
      markerAwarePullNearestRawBitSourceTape
        (count.length + 2)
        (List.append (pref.reverse.map some) [some false])
        rawBit tailFirst tail
  pullerHalts :
    markerAwarePullNearestRawBitDescription.HaltsFromTape
      (rawBoundaryLeftMarkedTailHeadHandoffTape
        skipped count tailFirst tail)
      (rawBoundaryLeftMarkedTailHeadPulledNearestRawBitTape
        pref count rawBit tailFirst tail)

theorem rawBoundaryLeftMarkedTailHeadNearestRawBitPullRoute
    (skipped count pref : Word Bool)
    (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) :
    RawBoundaryLeftMarkedTailHeadNearestRawBitPullRoute
      skipped count pref rawBit tailFirst tail hlayout :=
  { pullerReady :=
      markerAwarePullNearestRawBitDescription_subroutineReady
    sourceAsMarkerAwarePull :=
      rawBoundaryLeftMarkedTailHeadHandoffTape_eq_markerAwarePullSource
        skipped count pref rawBit tailFirst tail hlayout
    pullerHalts :=
      rawBoundaryLeftMarkedTailHeadPulledNearestRawBit_haltsFrom
        skipped count pref rawBit tailFirst tail hlayout }

theorem rawBoundary_leftMarkedTailHead_nearestRawBitPull_halts
    (skipped count pref : Word Bool)
    (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) :
    markerAwarePullNearestRawBitDescription.HaltsFromTape
      (rawBoundaryLeftMarkedTailHeadHandoffTape
        skipped count tailFirst tail)
      (rawBoundaryLeftMarkedTailHeadPulledNearestRawBitTape
        pref count rawBit tailFirst tail) :=
  (rawBoundaryLeftMarkedTailHeadNearestRawBitPullRoute
    skipped count pref rawBit tailFirst tail hlayout).pullerHalts

structure RawBoundaryLeftMarkedTailHeadNearestRawBitPullAndEmitRoute
    (skipped count pref : Word Bool)
    (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) : Prop where
  combinedReady :
    markerAwarePullAndEmitNearestRawBitCellDescription.SubroutineReady
  pulledAsEmitterSource :
    rawBoundaryLeftMarkedTailHeadPulledNearestRawBitTape
        pref count rawBit tailFirst tail =
      emitPulledRawBitCellChunkSourceTape
        count.length
        (List.append (pref.reverse.map some) [some false])
        rawBit tailFirst tail
  emitterHaltsFromPulled :
    emitPulledRawBitCellChunkDescription.HaltsFromTape
      (rawBoundaryLeftMarkedTailHeadPulledNearestRawBitTape
        pref count rawBit tailFirst tail)
      (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape
        pref count rawBit tailFirst tail)
  leftEdgeMoverReady :
    leftMoveAcrossFourNonblankCellsDescription.SubroutineReady
  combinedHalts :
    markerAwarePullAndEmitNearestRawBitCellDescription.HaltsFromTape
      (rawBoundaryLeftMarkedTailHeadHandoffTape
        skipped count tailFirst tail)
      (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape
        pref count rawBit tailFirst tail)
  leftEdgeMoverHalts :
    leftMoveAcrossFourNonblankCellsDescription.HaltsFromTape
      (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape
        pref count rawBit tailFirst tail)
      (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape
        pref count rawBit tailFirst tail)
  emittedCells :
    Tape.cells
        (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape
          pref count rawBit tailFirst tail) =
      some false ::
        List.append (pref.map some)
          (List.append
            (List.replicate count.length (none : Option Bool))
            (List.append
              ((pulledRawBitCellChunkBits rawBit).map some)
              (some tailFirst :: tail)))
  emittedLeftLength :
    (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape
      pref count rawBit tailFirst tail).left.length =
      4 + count.length + pref.length + 1
  leftEdgeCells :
    Tape.cells
        (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape
          pref count rawBit tailFirst tail) =
      some false ::
        List.append (pref.map some)
          (List.append
            (List.replicate count.length (none : Option Bool))
            (List.append
              ((pulledRawBitCellChunkBits rawBit).map some)
              (some tailFirst :: tail)))
  leftEdgeLeftLength :
    (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape
      pref count rawBit tailFirst tail).left.length =
      count.length + pref.length + 1

theorem rawBoundaryLeftMarkedTailHeadNearestRawBitPullAndEmitRoute
    (skipped count pref : Word Bool)
    (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) :
    RawBoundaryLeftMarkedTailHeadNearestRawBitPullAndEmitRoute
      skipped count pref rawBit tailFirst tail hlayout :=
  { combinedReady :=
      markerAwarePullAndEmitNearestRawBitCellDescription_subroutineReady
    pulledAsEmitterSource :=
      rawBoundaryLeftMarkedTailHeadPulledNearestRawBitTape_eq_emitSource
        pref count rawBit tailFirst tail
    emitterHaltsFromPulled :=
      emitPulledRawBitCellChunkDescription_haltsFrom_leftMarkedTailHeadPulled
        pref count rawBit tailFirst tail
    leftEdgeMoverReady :=
      leftMoveAcrossFourNonblankCellsDescription_subroutineReady
    combinedHalts :=
      markerAwarePullAndEmitNearestRawBitCellDescription_haltsFrom_leftMarkedTailHeadHandoff
        skipped count pref rawBit tailFirst tail hlayout
    leftEdgeMoverHalts :=
      leftMoveAcrossFourNonblankCellsDescription_haltsFrom_leftMarkedTailHeadEmittedNearestRawBitCell
        pref count rawBit tailFirst tail
    emittedCells :=
      rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape_cells
        pref count rawBit tailFirst tail
    emittedLeftLength :=
      rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape_left_length
        pref count rawBit tailFirst tail
    leftEdgeCells :=
      rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape_cells
        pref count rawBit tailFirst tail
    leftEdgeLeftLength :=
      rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape_left_length
        pref count rawBit tailFirst tail }

theorem rawBoundary_leftMarkedTailHead_nearestRawBitPullAndEmit_halts
    (skipped count pref : Word Bool)
    (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) :
    markerAwarePullAndEmitNearestRawBitCellDescription.HaltsFromTape
      (rawBoundaryLeftMarkedTailHeadHandoffTape
        skipped count tailFirst tail)
      (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape
        pref count rawBit tailFirst tail) :=
  (rawBoundaryLeftMarkedTailHeadNearestRawBitPullAndEmitRoute
    skipped count pref rawBit tailFirst tail hlayout).combinedHalts

theorem rawBoundary_leftMarkedTailHead_nearestRawBitCellLeftEdge_halts
    (skipped count pref : Word Bool)
    (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) :
    leftMoveAcrossFourNonblankCellsDescription.HaltsFromTape
      (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape
        pref count rawBit tailFirst tail)
      (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape
      pref count rawBit tailFirst tail) :=
  (rawBoundaryLeftMarkedTailHeadNearestRawBitPullAndEmitRoute
    skipped count pref rawBit tailFirst tail hlayout).leftEdgeMoverHalts

structure RawBoundarySourceFirstRawBitCellLeftEdgeViaLeftMarkedBoundaryRoute
    (skipped count pref : Word Bool)
    (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) : Prop where
  emissionReady :
    rawBoundarySourceFirstRawBitCellEmissionViaLeftMarkedBoundaryDescription.SubroutineReady
  emissionHalts :
    rawBoundarySourceFirstRawBitCellEmissionViaLeftMarkedBoundaryDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellTape
        pref count rawBit tailFirst tail)
  leftEdgeReady :
    rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaLeftMarkedBoundaryDescription.SubroutineReady
  leftEdgeHalts :
    rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaLeftMarkedBoundaryDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape
        pref count rawBit tailFirst tail)
  leftEdgeCells :
    Tape.cells
        (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape
          pref count rawBit tailFirst tail) =
      some false ::
        List.append (pref.map some)
          (List.append
            (List.replicate count.length (none : Option Bool))
            (List.append
              ((pulledRawBitCellChunkBits rawBit).map some)
              (some tailFirst :: tail)))
  leftEdgeLeftLength :
    (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape
      pref count rawBit tailFirst tail).left.length =
      count.length + pref.length + 1

theorem rawBoundarySourceFirstRawBitCellLeftEdgeViaLeftMarkedBoundaryRoute
    (skipped count pref : Word Bool)
    (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) :
    RawBoundarySourceFirstRawBitCellLeftEdgeViaLeftMarkedBoundaryRoute
      skipped count pref rawBit tailFirst tail hlayout :=
  { emissionReady :=
      rawBoundarySourceFirstRawBitCellEmissionViaLeftMarkedBoundaryDescription_ready
    emissionHalts :=
      rawBoundarySourceFirstRawBitCellEmissionViaLeftMarkedBoundaryDescription_haltsFrom_sourceTape
        skipped count pref rawBit tailFirst tail hlayout
    leftEdgeReady :=
      rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaLeftMarkedBoundaryDescription_ready
    leftEdgeHalts :=
      rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaLeftMarkedBoundaryDescription_haltsFrom_sourceTape
        skipped count pref rawBit tailFirst tail hlayout
    leftEdgeCells :=
      rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape_cells
        pref count rawBit tailFirst tail
    leftEdgeLeftLength :=
      rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape_left_length
        pref count rawBit tailFirst tail }

theorem rawBoundary_sourceFirstRawBitCellLeftEdgeViaLeftMarkedBoundary_halts
    (skipped count pref : Word Bool)
    (rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count = List.append pref [rawBit]) :
    rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaLeftMarkedBoundaryDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape
        pref count rawBit tailFirst tail) :=
  (rawBoundarySourceFirstRawBitCellLeftEdgeViaLeftMarkedBoundaryRoute
    skipped count pref rawBit tailFirst tail hlayout).leftEdgeHalts

theorem rawBoundary_sourceFirstRawBitCellLeftEdgeViaLeftMarkedBoundary_exists
    (skipped count : Word Bool)
    (h : List.append skipped count ≠ [])
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    exists pref : Word Bool, exists rawBit : Bool,
      List.append skipped count = List.append pref [rawBit] ∧
        rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaLeftMarkedBoundaryDescription.HaltsFromTape
          (sourceTape skipped count (some tailFirst :: tail))
          (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape
            pref count rawBit tailFirst tail) :=
  rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaLeftMarkedBoundaryDescription_exists
    skipped count h tailFirst tail

structure RawBoundaryLeftMarkedTailHeadNextRawBitPullRoute
    (pref count : Word Bool)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool)) : Prop where
  pullerReady :
    markerAwarePullNearestRawBitDescription.SubroutineReady
  pullerHalts :
    markerAwarePullNearestRawBitDescription.HaltsFromTape
      (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape
        (List.append pref [nextRawBit]) count emittedRawBit tailFirst tail)
      (rawBoundaryLeftMarkedTailHeadPulledNextRawBitBeforeEmittedCellTape
        pref count nextRawBit emittedRawBit tailFirst tail)
  pulledCells :
    Tape.cells
        (rawBoundaryLeftMarkedTailHeadPulledNextRawBitBeforeEmittedCellTape
          pref count nextRawBit emittedRawBit tailFirst tail) =
      some false ::
        List.append (pref.map some)
          (List.append
            (List.replicate count.length (none : Option Bool))
            (some nextRawBit ::
              List.append
                ((pulledRawBitCellChunkBits emittedRawBit).map some)
                (some tailFirst :: tail)))
  pulledLeftLength :
    (rawBoundaryLeftMarkedTailHeadPulledNextRawBitBeforeEmittedCellTape
      pref count nextRawBit emittedRawBit tailFirst tail).left.length =
      count.length + pref.length + 2

theorem rawBoundaryLeftMarkedTailHeadNextRawBitPullRoute
    (pref count : Word Bool)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    RawBoundaryLeftMarkedTailHeadNextRawBitPullRoute
      pref count nextRawBit emittedRawBit tailFirst tail :=
  { pullerReady :=
      markerAwarePullNearestRawBitDescription_subroutineReady
    pullerHalts :=
      markerAwarePullNearestRawBitDescription_haltsFrom_leftMarkedTailHeadEmittedNearestRawBitCellLeftEdge
        pref count nextRawBit emittedRawBit tailFirst tail
    pulledCells :=
      rawBoundaryLeftMarkedTailHeadPulledNextRawBitBeforeEmittedCellTape_cells
        pref count nextRawBit emittedRawBit tailFirst tail
    pulledLeftLength :=
      rawBoundaryLeftMarkedTailHeadPulledNextRawBitBeforeEmittedCellTape_left_length
        pref count nextRawBit emittedRawBit tailFirst tail }

theorem rawBoundary_leftMarkedTailHead_nextRawBitPull_halts
    (pref count : Word Bool)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.HaltsFromTape
      (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape
        (List.append pref [nextRawBit]) count emittedRawBit tailFirst tail)
      (rawBoundaryLeftMarkedTailHeadPulledNextRawBitBeforeEmittedCellTape
        pref count nextRawBit emittedRawBit tailFirst tail) :=
  (rawBoundaryLeftMarkedTailHeadNextRawBitPullRoute
    pref count nextRawBit emittedRawBit tailFirst tail).pullerHalts

structure RawBoundaryLeftMarkedTailHeadNextRawBitPullEmitMoveRoute
    (pref count : Word Bool) (scratchTail : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hcount : count.length = scratchTail + 3) : Prop where
  combinedReady :
    markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription.SubroutineReady
  combinedHalts :
    markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription.HaltsFromTape
      (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape
        (List.append pref [nextRawBit]) count emittedRawBit tailFirst tail)
      (rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
        pref scratchTail nextRawBit emittedRawBit tailFirst tail)
  outputCells :
    Tape.cells
        (rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
          pref scratchTail nextRawBit emittedRawBit tailFirst tail) =
      some false ::
        List.append (pref.map some)
          (List.append
            (List.replicate scratchTail (none : Option Bool))
            (List.append
              ((pulledRawBitCellChunkBits nextRawBit).map some)
              (List.append
                ((pulledRawBitCellChunkBits emittedRawBit).map some)
                (some tailFirst :: tail))))
  outputLeftLength :
    (rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
      pref scratchTail nextRawBit emittedRawBit tailFirst tail).left.length =
      scratchTail + pref.length + 1
  outputMoveLeftRight :
    Tape.move Direction.right
        (Tape.move Direction.left
          (rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
            pref scratchTail nextRawBit emittedRawBit tailFirst tail)) =
      rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
        pref scratchTail nextRawBit emittedRawBit tailFirst tail

theorem rawBoundaryLeftMarkedTailHeadNextRawBitPullEmitMoveRoute
    (pref count : Word Bool) (scratchTail : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hcount : count.length = scratchTail + 3) :
    RawBoundaryLeftMarkedTailHeadNextRawBitPullEmitMoveRoute
      pref count scratchTail nextRawBit emittedRawBit tailFirst tail hcount :=
  { combinedReady :=
      markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription_subroutineReady
    combinedHalts :=
      pullEmitMoveRawBit_haltsFrom_leftMarkedTail_countLength
        pref count scratchTail nextRawBit emittedRawBit tailFirst tail hcount
    outputCells :=
      rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_cells
        pref scratchTail nextRawBit emittedRawBit tailFirst tail
    outputLeftLength :=
      rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_left_length
        pref scratchTail nextRawBit emittedRawBit tailFirst tail
    outputMoveLeftRight :=
      rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_moveLeftRight
        pref scratchTail nextRawBit emittedRawBit tailFirst tail }

theorem rawBoundary_leftMarkedTailHead_nextRawBitPullEmitMove_halts
    (pref count : Word Bool) (scratchTail : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hcount : count.length = scratchTail + 3) :
    markerAwarePullEmitAndMoveRawBitCellLeftEdgeDescription.HaltsFromTape
      (rawBoundaryLeftMarkedTailHeadEmittedNearestRawBitCellLeftEdgeTape
        (List.append pref [nextRawBit]) count emittedRawBit tailFirst tail)
      (rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
        pref scratchTail nextRawBit emittedRawBit tailFirst tail) :=
  (rawBoundaryLeftMarkedTailHeadNextRawBitPullEmitMoveRoute
    pref count scratchTail nextRawBit emittedRawBit tailFirst tail hcount).combinedHalts

structure RawBoundarySourceFirstTwoRawBitCellsLeftEdgeViaLeftMarkedBoundaryRoute
    (skipped count pref : Word Bool) (scratchTail : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count =
        List.append (List.append pref [nextRawBit]) [emittedRawBit])
    (hcount : count.length = scratchTail + 3) : Prop where
  routeReady :
    rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionViaLeftMarkedBoundaryDescription.SubroutineReady
  routeHalts :
    rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionViaLeftMarkedBoundaryDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
        pref scratchTail nextRawBit emittedRawBit tailFirst tail)
  outputCells :
    Tape.cells
        (rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
          pref scratchTail nextRawBit emittedRawBit tailFirst tail) =
      some false ::
        List.append (pref.map some)
          (List.append
            (List.replicate scratchTail (none : Option Bool))
            (List.append
              ((pulledRawBitCellChunkBits nextRawBit).map some)
              (List.append
                ((pulledRawBitCellChunkBits emittedRawBit).map some)
                (some tailFirst :: tail))))
  outputLeftLength :
    (rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
      pref scratchTail nextRawBit emittedRawBit tailFirst tail).left.length =
      scratchTail + pref.length + 1
  outputMoveLeftRight :
    Tape.move Direction.right
        (Tape.move Direction.left
          (rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
            pref scratchTail nextRawBit emittedRawBit tailFirst tail)) =
      rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
        pref scratchTail nextRawBit emittedRawBit tailFirst tail

theorem rawBoundarySourceFirstTwoRawBitCellsLeftEdgeViaLeftMarkedBoundaryRoute
    (skipped count pref : Word Bool) (scratchTail : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count =
        List.append (List.append pref [nextRawBit]) [emittedRawBit])
    (hcount : count.length = scratchTail + 3) :
    RawBoundarySourceFirstTwoRawBitCellsLeftEdgeViaLeftMarkedBoundaryRoute
      skipped count pref scratchTail nextRawBit emittedRawBit tailFirst tail
      hlayout hcount :=
  { routeReady :=
      rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionViaLeftMarkedBoundaryDescription_ready
    routeHalts :=
      rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionViaLeftMarkedBoundaryDescription_haltsFrom_sourceTape_of_count_length
        skipped count pref scratchTail nextRawBit emittedRawBit tailFirst
        tail hlayout hcount
    outputCells :=
      rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_cells
        pref scratchTail nextRawBit emittedRawBit tailFirst tail
    outputLeftLength :=
      rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_left_length
        pref scratchTail nextRawBit emittedRawBit tailFirst tail
    outputMoveLeftRight :=
      rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape_moveLeftRight
        pref scratchTail nextRawBit emittedRawBit tailFirst tail }

theorem rawBoundary_sourceFirstTwoRawBitCellsLeftEdgeViaLeftMarkedBoundary_halts
    (skipped count pref : Word Bool) (scratchTail : Nat)
    (nextRawBit emittedRawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped count =
        List.append (List.append pref [nextRawBit]) [emittedRawBit])
    (hcount : count.length = scratchTail + 3) :
    rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionViaLeftMarkedBoundaryDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
        pref scratchTail nextRawBit emittedRawBit tailFirst tail) :=
  (rawBoundarySourceFirstTwoRawBitCellsLeftEdgeViaLeftMarkedBoundaryRoute
    skipped count pref scratchTail nextRawBit emittedRawBit tailFirst tail
    hlayout hcount).routeHalts

theorem rawBoundary_sourceFirstTwoRawBitCellsLeftEdgeViaLeftMarkedBoundary_halts_exists_of_two_le_layout_length_three_le_count_length
    (skipped count : Word Bool)
    (hlayoutLength : 2 <= (List.append skipped count).length)
    (hcount : 3 <= count.length)
    (tailFirst : Bool) (tail : List (Option Bool)) :
    exists pref : Word Bool, exists nextRawBit : Bool,
      exists emittedRawBit : Bool, exists scratchTail : Nat,
        List.append skipped count =
            List.append (List.append pref [nextRawBit]) [emittedRawBit] ∧
          count.length = scratchTail + 3 ∧
            rawBoundarySourceFirstTwoRawBitCellsLeftEdgeEmissionViaLeftMarkedBoundaryDescription.HaltsFromTape
              (sourceTape skipped count (some tailFirst :: tail))
              (rawBoundaryLeftMarkedTailHeadEmittedNextRawBitCellBeforeEmittedCellLeftEdgeTape
                pref scratchTail nextRawBit emittedRawBit tailFirst tail) :=
  firstTwoRawBitCells_haltsFrom_sourceTape_ofLayoutAndCount
    skipped count hlayoutLength hcount tailFirst tail

structure RawBoundaryCountWindowStartRoute
    (skipped count : Word Bool)
    (tail : List (Option Bool)) : Prop where
  routeReady :
    rawBoundarySourceToCountWindowStartDescription.SubroutineReady
  routeHalts :
    rawBoundarySourceToCountWindowStartDescription.HaltsFromTape
      (sourceTape skipped count tail)
      (rawBoundaryCountWindowStartTape skipped count tail)

theorem rawBoundaryCountWindowStartRoute
    (skipped count : Word Bool)
    (tail : List (Option Bool)) :
    RawBoundaryCountWindowStartRoute skipped count tail :=
  { routeReady :=
      rawBoundarySourceToCountWindowStartDescription_ready
    routeHalts :=
      rawBoundarySourceToCountWindowStartDescription_haltsFrom_sourceTape
        skipped count tail }

theorem rawBoundary_countWindowStart_halts
    (skipped count : Word Bool)
    (tail : List (Option Bool)) :
    rawBoundarySourceToCountWindowStartDescription.HaltsFromTape
      (sourceTape skipped count tail)
      (rawBoundaryCountWindowStartTape skipped count tail) :=
  (rawBoundaryCountWindowStartRoute skipped count tail).routeHalts

structure RawBoundaryCountWindowTailHeadRoute
    (skipped countRest : Word Bool)
    (countFirst tailFirst : Bool)
    (tail : List (Option Bool)) : Prop where
  leftRouteReady :
    rawBoundarySourceToTailLeftHandoffDescription.SubroutineReady
  leftRouteHalts :
    rawBoundarySourceToTailLeftHandoffDescription.HaltsFromTape
      (sourceTape skipped (countFirst :: countRest)
        (some tailFirst :: tail))
      (tailLeftHandoffTape
        skipped (countFirst :: countRest) tailFirst tail)
  headRouteReady :
    rawBoundarySourceToTailHeadHandoffDescription.SubroutineReady
  headRouteHalts :
    rawBoundarySourceToTailHeadHandoffDescription.HaltsFromTape
      (sourceTape skipped (countFirst :: countRest)
        (some tailFirst :: tail))
      (tailHeadHandoffTape
        skipped (countFirst :: countRest) tailFirst tail)

theorem rawBoundaryCountWindowTailHeadRoute
    (skipped countRest : Word Bool)
    (countFirst tailFirst : Bool)
    (tail : List (Option Bool)) :
    RawBoundaryCountWindowTailHeadRoute
      skipped countRest countFirst tailFirst tail :=
  { leftRouteReady :=
      rawBoundarySourceToTailLeftHandoffDescription_ready
    leftRouteHalts :=
      rawBoundarySourceToTailLeftHandoffDescription_haltsFrom_sourceTape
        skipped countRest countFirst tailFirst tail
    headRouteReady :=
      rawBoundarySourceToTailHeadHandoffDescription_ready
    headRouteHalts :=
      rawBoundarySourceToTailHeadHandoffDescription_haltsFrom_sourceTape
        skipped countRest countFirst tailFirst tail }

theorem rawBoundary_countWindowTailHead_halts
    (skipped countRest : Word Bool)
    (countFirst tailFirst : Bool)
    (tail : List (Option Bool)) :
    rawBoundarySourceToTailHeadHandoffDescription.HaltsFromTape
      (sourceTape skipped (countFirst :: countRest)
        (some tailFirst :: tail))
      (tailHeadHandoffTape
        skipped (countFirst :: countRest) tailFirst tail) :=
  (rawBoundaryCountWindowTailHeadRoute
    skipped countRest countFirst tailFirst tail).headRouteHalts

structure RawBoundaryCountWindowFirstRawBitEmissionRoute
    (skipped countRest pref : Word Bool)
    (countFirst rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped (countFirst :: countRest) =
        List.append pref [rawBit]) : Prop where
  emitRouteReady :
    (rawBoundarySourceFirstRawBitCellEmissionViaCountWindowDescription).SubroutineReady
  emitRouteHalts :
    (rawBoundarySourceFirstRawBitCellEmissionViaCountWindowDescription).HaltsFromTape
        (sourceTape skipped (countFirst :: countRest)
          (some tailFirst :: tail))
        (tailHeadEmittedNearestRawBitCellTape
          pref (countFirst :: countRest) rawBit tailFirst tail)
  leftEdgeRouteReady :
    (rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaCountWindowDescription).SubroutineReady
  leftEdgeRouteHalts :
    (rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaCountWindowDescription).HaltsFromTape
        (sourceTape skipped (countFirst :: countRest)
          (some tailFirst :: tail))
        (tailHeadEmittedNearestRawBitCellLeftEdgeTape
          pref (countFirst :: countRest) rawBit tailFirst tail)

theorem rawBoundaryCountWindowFirstRawBitEmissionRoute
    (skipped countRest pref : Word Bool)
    (countFirst rawBit tailFirst : Bool)
    (tail : List (Option Bool))
    (hlayout :
      List.append skipped (countFirst :: countRest) =
        List.append pref [rawBit]) :
    RawBoundaryCountWindowFirstRawBitEmissionRoute
      skipped countRest pref countFirst rawBit tailFirst tail hlayout :=
  { emitRouteReady :=
      rawBoundarySourceFirstRawBitCellEmissionViaCountWindowDescription_ready
    emitRouteHalts :=
      rawBoundarySourceFirstRawBitCellEmissionViaCountWindowDescription_haltsFrom_sourceTape
        skipped countRest pref countFirst rawBit tailFirst tail hlayout
    leftEdgeRouteReady :=
      rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaCountWindowDescription_ready
    leftEdgeRouteHalts :=
      rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaCountWindowDescription_haltsFrom_sourceTape
        skipped countRest pref countFirst rawBit tailFirst tail hlayout }

theorem rawBoundary_countWindowFirstRawBitLeftEdge_exists
    (skipped countRest : Word Bool)
    (countFirst tailFirst : Bool)
    (tail : List (Option Bool)) :
    exists pref : Word Bool, exists rawBit : Bool,
      List.append skipped (countFirst :: countRest) =
          List.append pref [rawBit] ∧
        (rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaCountWindowDescription).HaltsFromTape
            (sourceTape skipped (countFirst :: countRest)
              (some tailFirst :: tail))
            (tailHeadEmittedNearestRawBitCellLeftEdgeTape
              pref (countFirst :: countRest) rawBit tailFirst tail) :=
  rawBoundarySourceFirstRawBitCellLeftEdgeEmissionViaCountWindowDescription_exists
    skipped countRest countFirst tailFirst tail

structure RawBoundaryGuardedCountBoundaryLocatorRoute
    (skipped countRest : Word Bool)
    (countFirst guardBit tailFirst : Bool)
    (tail : List (Option Bool)) : Prop where
  routeReady :
    guardedCountBoundaryLocatorDescription.SubroutineReady
  routeHalts :
    guardedCountBoundaryLocatorDescription.HaltsFromTape
      (guardedCountBoundaryRightEdgeTape
        skipped (countFirst :: countRest) guardBit tailFirst tail)
      (guardedCountBoundaryLocatedTape
        skipped (countFirst :: countRest) guardBit tailFirst tail)

theorem rawBoundaryGuardedCountBoundaryLocatorRoute
    (skipped countRest : Word Bool)
    (countFirst guardBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    RawBoundaryGuardedCountBoundaryLocatorRoute
      skipped countRest countFirst guardBit tailFirst tail :=
  { routeReady :=
      guardedCountBoundaryLocatorDescription_ready
    routeHalts :=
      guardedCountBoundaryLocatorDescription_haltsFromTape
        skipped countRest countFirst guardBit tailFirst tail }

theorem rawBoundary_guardedCountBoundaryLocator_halts
    (skipped countRest : Word Bool)
    (countFirst guardBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    guardedCountBoundaryLocatorDescription.HaltsFromTape
      (guardedCountBoundaryRightEdgeTape
        skipped (countFirst :: countRest) guardBit tailFirst tail)
      (guardedCountBoundaryLocatedTape
        skipped (countFirst :: countRest) guardBit tailFirst tail) :=
  (rawBoundaryGuardedCountBoundaryLocatorRoute
    skipped countRest countFirst guardBit tailFirst tail).routeHalts

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround
end Computability
end FoC
