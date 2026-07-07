import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.MarkerAwarePull

set_option doc.verso true

/-!
# Raw-boundary marker-aware pull route contracts

This module packages the fixed marker-aware nearest-bit puller.  The real-bit
branch is used when the nearest nonblank to the left of the scratch gap has a
nonblank predecessor.  The boundary branch is used when that predecessor is
blank, so the nearest nonblank is the left boundary marker rather than raw
data.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace CountWindowRawSourceEncoder
namespace RawBoundaryRightEdgeEmitter

structure RawBoundaryMarkerAwarePullRealRoute
    (blankCount : Nat) (leftBit rawBit : Bool)
    (baseTail : List (Option Bool))
    (tailFirst : Bool) (tail : List (Option Bool)) : Prop where
  pullerReady :
    markerAwarePullNearestRawBitDescription.SubroutineReady
  pullerHalts :
    markerAwarePullNearestRawBitDescription.HaltsFromTape
      (markerAwarePullNearestRawBitSourceTape
        blankCount (some leftBit :: baseTail) rawBit tailFirst tail)
      (markerAwarePullNearestRawBitTargetTape
        blankCount (some leftBit :: baseTail) rawBit tailFirst tail)

theorem rawBoundaryMarkerAwarePullRealRoute
    (blankCount : Nat) (leftBit rawBit : Bool)
    (baseTail : List (Option Bool))
    (tailFirst : Bool) (tail : List (Option Bool)) :
    RawBoundaryMarkerAwarePullRealRoute
      blankCount leftBit rawBit baseTail tailFirst tail :=
  { pullerReady :=
      markerAwarePullNearestRawBitDescription_subroutineReady
    pullerHalts :=
      markerAwarePullNearestRawBitDescription_haltsFromTape_real
        blankCount leftBit rawBit baseTail tailFirst tail }

theorem rawBoundary_markerAwarePullReal_halts
    (blankCount : Nat) (leftBit rawBit : Bool)
    (baseTail : List (Option Bool))
    (tailFirst : Bool) (tail : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.HaltsFromTape
      (markerAwarePullNearestRawBitSourceTape
        blankCount (some leftBit :: baseTail) rawBit tailFirst tail)
      (markerAwarePullNearestRawBitTargetTape
        blankCount (some leftBit :: baseTail) rawBit tailFirst tail) :=
  (rawBoundaryMarkerAwarePullRealRoute
    blankCount leftBit rawBit baseTail tailFirst tail).pullerHalts

structure RawBoundaryMarkerAwarePullBoundaryRoute
    (blankCount : Nat) (baseTail : List (Option Bool))
    (markerBit tailFirst : Bool)
    (tail : List (Option Bool)) : Prop where
  pullerReady :
    markerAwarePullNearestRawBitDescription.SubroutineReady
  pullerHalts :
    markerAwarePullNearestRawBitDescription.HaltsFromTape
      (markerAwarePullNearestRawBitSourceTape
        blankCount (none :: baseTail) markerBit tailFirst tail)
      (markerAwarePullNearestBoundaryTargetTape
        blankCount baseTail markerBit tailFirst tail)

theorem rawBoundaryMarkerAwarePullBoundaryRoute
    (blankCount : Nat) (baseTail : List (Option Bool))
    (markerBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    RawBoundaryMarkerAwarePullBoundaryRoute
      blankCount baseTail markerBit tailFirst tail :=
  { pullerReady :=
      markerAwarePullNearestRawBitDescription_subroutineReady
    pullerHalts :=
      markerAwarePullNearestRawBitDescription_haltsFromTape_boundary
        blankCount baseTail markerBit tailFirst tail }

theorem rawBoundary_markerAwarePullBoundary_halts
    (blankCount : Nat) (baseTail : List (Option Bool))
    (markerBit tailFirst : Bool)
    (tail : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.HaltsFromTape
      (markerAwarePullNearestRawBitSourceTape
        blankCount (none :: baseTail) markerBit tailFirst tail)
      (markerAwarePullNearestBoundaryTargetTape
        blankCount baseTail markerBit tailFirst tail) :=
  (rawBoundaryMarkerAwarePullBoundaryRoute
    blankCount baseTail markerBit tailFirst tail).pullerHalts

structure RawBoundaryMarkerAwareHeadGapPullRealRoute
    (gap : Nat) (leftBit rawBit headBit : Bool)
    (baseTail : List (Option Bool))
    (right : List (Option Bool)) : Prop where
  pullerReady :
    markerAwarePullNearestRawBitDescription.SubroutineReady
  pullerHalts :
    markerAwarePullNearestRawBitDescription.HaltsFromTape
      (markerAwarePullNearestRawBitToHeadMarkerSourceTape
        gap (some leftBit :: baseTail) rawBit headBit right)
      (markerAwarePullNearestRawBitToHeadMarkerTargetTape
        gap (some leftBit :: baseTail) rawBit headBit right)

theorem rawBoundaryMarkerAwareHeadGapPullRealRoute
    (gap : Nat) (leftBit rawBit headBit : Bool)
    (baseTail : List (Option Bool))
    (right : List (Option Bool)) :
    RawBoundaryMarkerAwareHeadGapPullRealRoute
      gap leftBit rawBit headBit baseTail right :=
  { pullerReady :=
      markerAwarePullNearestRawBitDescription_subroutineReady
    pullerHalts :=
      markerAwarePullNearestRawBitDescription_haltsFromHeadGap_real
        gap leftBit rawBit headBit baseTail right }

theorem rawBoundary_markerAwareHeadGapPullReal_halts
    (gap : Nat) (leftBit rawBit headBit : Bool)
    (baseTail : List (Option Bool))
    (right : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.HaltsFromTape
      (markerAwarePullNearestRawBitToHeadMarkerSourceTape
        gap (some leftBit :: baseTail) rawBit headBit right)
      (markerAwarePullNearestRawBitToHeadMarkerTargetTape
        gap (some leftBit :: baseTail) rawBit headBit right) :=
  (rawBoundaryMarkerAwareHeadGapPullRealRoute
    gap leftBit rawBit headBit baseTail right).pullerHalts

structure RawBoundaryMarkerAwareHeadGapPullBoundaryRoute
    (gap : Nat) (baseTail : List (Option Bool))
    (markerBit headBit : Bool)
    (right : List (Option Bool)) : Prop where
  pullerReady :
    markerAwarePullNearestRawBitDescription.SubroutineReady
  pullerHalts :
    markerAwarePullNearestRawBitDescription.HaltsFromTape
      (markerAwarePullNearestRawBitToHeadMarkerSourceTape
        gap (none :: baseTail) markerBit headBit right)
      (markerAwarePullNearestBoundaryToHeadMarkerTargetTape
        gap baseTail markerBit headBit right)

theorem rawBoundaryMarkerAwareHeadGapPullBoundaryRoute
    (gap : Nat) (baseTail : List (Option Bool))
    (markerBit headBit : Bool)
    (right : List (Option Bool)) :
    RawBoundaryMarkerAwareHeadGapPullBoundaryRoute
      gap baseTail markerBit headBit right :=
  { pullerReady :=
      markerAwarePullNearestRawBitDescription_subroutineReady
    pullerHalts :=
      markerAwarePullNearestRawBitDescription_haltsFromHeadGap_boundary
        gap baseTail markerBit headBit right }

theorem rawBoundary_markerAwareHeadGapPullBoundary_halts
    (gap : Nat) (baseTail : List (Option Bool))
    (markerBit headBit : Bool)
    (right : List (Option Bool)) :
    markerAwarePullNearestRawBitDescription.HaltsFromTape
      (markerAwarePullNearestRawBitToHeadMarkerSourceTape
        gap (none :: baseTail) markerBit headBit right)
      (markerAwarePullNearestBoundaryToHeadMarkerTargetTape
        gap baseTail markerBit headBit right) :=
  (rawBoundaryMarkerAwareHeadGapPullBoundaryRoute
    gap baseTail markerBit headBit right).pullerHalts

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
