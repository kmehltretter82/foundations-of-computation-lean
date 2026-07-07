import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.BlankSentinelFinalizer

set_option doc.verso true

/-!
# Blank-sentinel finalizer route contract

This module packages the delimiter-preserving encoded-layout finalizer route
against the public raw-boundary right-edge endpoint.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace CountWindowRawSourceEncoder
namespace RawBoundaryRightEdgeEmitter

structure RawBoundaryBlankSentinelFinalizerRoute
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) : Prop where
  routeReady :
    (rawBoundaryBlankSentinelFinalizerDescription
      skipped count tailFirst).SubroutineReady
  routeHalts :
    (rawBoundaryBlankSentinelFinalizerDescription
      skipped count tailFirst).HaltsFromTape
      (tapeAtCells [] (none :: tail))
      (rightEdgeTape skipped count tailFirst tail)
  routeHaltsFromBlankLeft :
    forall padding : Nat,
      (rawBoundaryBlankSentinelFinalizerDescription
        skipped count tailFirst).HaltsFromTapeEquiv
        (tapeAtCells
          (List.replicate padding (none : Option Bool))
          (none :: tail))
        (rightEdgeTape skipped count tailFirst tail)
  routeHaltsFromErasedTailHead :
    (rawBoundaryBlankSentinelFinalizerDescription
      skipped count tailFirst).HaltsFromTapeEquiv
      (tailHeadErasedBlankSentinelTape skipped count tail)
      (rightEdgeTape skipped count tailFirst tail)

theorem rawBoundaryBlankSentinelFinalizerRoute
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    RawBoundaryBlankSentinelFinalizerRoute
      skipped count tailFirst tail :=
  { routeReady :=
      rawBoundaryBlankSentinelFinalizerDescription_subroutineReady
        skipped count tailFirst
    routeHalts :=
      rawBoundaryBlankSentinelFinalizerDescription_haltsFrom_rightEdgeTape
        skipped count tailFirst tail
    routeHaltsFromBlankLeft := fun padding =>
      rawBoundaryBlankSentinelFinalizerDescription_haltsFrom_blankLeft_rightEdgeTapeEquiv
        skipped count tailFirst padding tail
    routeHaltsFromErasedTailHead :=
      rawBoundaryBlankSentinelFinalizerDescription_haltsFrom_erasedTailHeadHandoff_rightEdgeTapeEquiv
        skipped count tailFirst tail }

theorem rawBoundary_blankSentinelFinalizer_halts
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (rawBoundaryBlankSentinelFinalizerDescription
      skipped count tailFirst).HaltsFromTape
      (tapeAtCells [] (none :: tail))
      (rightEdgeTape skipped count tailFirst tail) :=
  (rawBoundaryBlankSentinelFinalizerRoute
    skipped count tailFirst tail).routeHalts

theorem rawBoundary_blankSentinelFinalizer_haltsFromBlankLeft
    (skipped count : Word Bool) (tailFirst : Bool)
    (padding : Nat) (tail : List (Option Bool)) :
    (rawBoundaryBlankSentinelFinalizerDescription
      skipped count tailFirst).HaltsFromTapeEquiv
      (tapeAtCells
        (List.replicate padding (none : Option Bool))
        (none :: tail))
      (rightEdgeTape skipped count tailFirst tail) :=
  (rawBoundaryBlankSentinelFinalizerRoute
    skipped count tailFirst tail).routeHaltsFromBlankLeft padding

theorem rawBoundary_blankSentinelFinalizer_haltsFromErasedTailHead
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (rawBoundaryBlankSentinelFinalizerDescription
      skipped count tailFirst).HaltsFromTapeEquiv
      (tailHeadErasedBlankSentinelTape skipped count tail)
      (rightEdgeTape skipped count tailFirst tail) :=
  (rawBoundaryBlankSentinelFinalizerRoute
    skipped count tailFirst tail).routeHaltsFromErasedTailHead

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
