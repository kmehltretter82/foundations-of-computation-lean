import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawEncoder.RawBoundaryRightEdgeEmitter.EraseRawFootprintBlankSentinel

set_option doc.verso true

/-!
# Raw-footprint blank-sentinel clearing route contract

This module packages the checked bridge from the raw-left blank-sentinel shape
to the fully erased blank-sentinel shape consumed by the finalizer.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace CountWindowRawSourceEncoder
namespace RawBoundaryRightEdgeEmitter

structure RawBoundaryRawFootprintBlankSentinelRoute
    (skipped count : Word Bool) (tail : List (Option Bool)) : Prop where
  returnReady :
    (rawFootprintReturnToBlankSentinelDescription
      skipped count).SubroutineReady
  returnHalts :
    (rawFootprintReturnToBlankSentinelDescription
      skipped count).HaltsFromTape
      (tailHeadRawBaseErasedLeftBoundaryTape skipped count tail)
      (tailHeadErasedBlankSentinelTape skipped count tail)
  clearReady :
    (tailHeadRawFootprintClearToBlankSentinelDescription
      skipped count).SubroutineReady
  clearHalts :
    (tailHeadRawFootprintClearToBlankSentinelDescription
      skipped count).HaltsFromTape
      (tailHeadBlankSentinelRawLeftTape skipped count tail)
      (tailHeadErasedBlankSentinelTape skipped count tail)

theorem rawBoundaryRawFootprintBlankSentinelRoute
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    RawBoundaryRawFootprintBlankSentinelRoute skipped count tail :=
  { returnReady :=
      rawFootprintReturnToBlankSentinelDescription_subroutineReady
        skipped count
    returnHalts :=
      rawFootprintReturnToBlankSentinelDescription_haltsFrom_erasedLeftBoundary
        skipped count tail
    clearReady :=
      tailHeadRawFootprintClearToBlankSentinelDescription_subroutineReady
        skipped count
    clearHalts :=
      tailHeadRawFootprintClearToBlankSentinelDescription_haltsFrom_rawLeft
        skipped count tail }

theorem rawBoundary_rawFootprintReturn_halts
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    (rawFootprintReturnToBlankSentinelDescription
      skipped count).HaltsFromTape
      (tailHeadRawBaseErasedLeftBoundaryTape skipped count tail)
      (tailHeadErasedBlankSentinelTape skipped count tail) :=
  (rawBoundaryRawFootprintBlankSentinelRoute
    skipped count tail).returnHalts

theorem rawBoundary_rawFootprintClearToBlankSentinel_halts
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    (tailHeadRawFootprintClearToBlankSentinelDescription
      skipped count).HaltsFromTape
      (tailHeadBlankSentinelRawLeftTape skipped count tail)
      (tailHeadErasedBlankSentinelTape skipped count tail) :=
  (rawBoundaryRawFootprintBlankSentinelRoute
    skipped count tail).clearHalts

structure RawBoundaryBlankSentinelEndToEndRoute
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) : Prop where
  sourceToErasedReady :
    (rawBoundarySourceToErasedBlankSentinelDescription
      skipped count tailFirst).SubroutineReady
  sourceToErasedHalts :
    (rawBoundarySourceToErasedBlankSentinelDescription
      skipped count tailFirst).HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (tailHeadErasedBlankSentinelTape skipped count tail)
  routeReady :
    (rawBoundaryBlankSentinelRouteDescription
      skipped count tailFirst).SubroutineReady
  routeHaltsEquiv :
    (rawBoundaryBlankSentinelRouteDescription
      skipped count tailFirst).HaltsFromTapeEquiv
      (sourceTape skipped count (some tailFirst :: tail))
      (rightEdgeTape skipped count tailFirst tail)
  routeHaltsWithOutput :
    (rawBoundaryBlankSentinelRouteDescription
      skipped count tailFirst).HaltsFromTapeWithOutput
      (sourceTape skipped count (some tailFirst :: tail))
      (rightEdgeOutputWord skipped count tailFirst tail)

theorem rawBoundaryBlankSentinelEndToEndRoute
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    RawBoundaryBlankSentinelEndToEndRoute
      skipped count tailFirst tail :=
  { sourceToErasedReady :=
      rawBoundarySourceToErasedBlankSentinelDescription_subroutineReady
        skipped count tailFirst
    sourceToErasedHalts :=
      rawBoundarySourceToErasedBlankSentinelDescription_haltsFrom_sourceTape
        skipped count tailFirst tail
    routeReady :=
      rawBoundaryBlankSentinelRouteDescription_subroutineReady
        skipped count tailFirst
    routeHaltsEquiv :=
      rawBoundaryBlankSentinelRouteDescription_haltsFrom_sourceTape_rightEdgeTapeEquiv
        skipped count tailFirst tail
    routeHaltsWithOutput := by
      have hrun :=
        MachineDescription.haltsFromTapeWithOutput_of_haltsFromTapeEquiv
          (rawBoundaryBlankSentinelRouteDescription_haltsFrom_sourceTape_rightEdgeTapeEquiv
            skipped count tailFirst tail)
      simpa [rightEdgeTape_normalizedOutput] using hrun }

theorem rawBoundary_sourceToErasedBlankSentinel_halts
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (rawBoundarySourceToErasedBlankSentinelDescription
      skipped count tailFirst).HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (tailHeadErasedBlankSentinelTape skipped count tail) :=
  (rawBoundaryBlankSentinelEndToEndRoute
    skipped count tailFirst tail).sourceToErasedHalts

theorem rawBoundary_blankSentinelEndToEnd_haltsEquiv
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (rawBoundaryBlankSentinelRouteDescription
      skipped count tailFirst).HaltsFromTapeEquiv
      (sourceTape skipped count (some tailFirst :: tail))
      (rightEdgeTape skipped count tailFirst tail) :=
  (rawBoundaryBlankSentinelEndToEndRoute
    skipped count tailFirst tail).routeHaltsEquiv

theorem rawBoundary_blankSentinelEndToEnd_haltsWithOutput
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (rawBoundaryBlankSentinelRouteDescription
      skipped count tailFirst).HaltsFromTapeWithOutput
      (sourceTape skipped count (some tailFirst :: tail))
      (rightEdgeOutputWord skipped count tailFirst tail) :=
  (rawBoundaryBlankSentinelEndToEndRoute
    skipped count tailFirst tail).routeHaltsWithOutput

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
