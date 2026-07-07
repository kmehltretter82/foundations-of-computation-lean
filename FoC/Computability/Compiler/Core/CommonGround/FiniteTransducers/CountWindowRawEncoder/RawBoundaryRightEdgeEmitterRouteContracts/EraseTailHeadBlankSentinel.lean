import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawEncoder.RawBoundaryRightEdgeEmitter.EraseTailHeadBlankSentinel

set_option doc.verso true

/-!
# Tail-head blanker route contract

This module packages the checked adapter that turns the live tail head into a
blank sentinel while preserving the raw-boundary left footprint.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace CountWindowRawSourceEncoder
namespace RawBoundaryRightEdgeEmitter

structure RawBoundaryTailHeadBlankerRoute
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) : Prop where
  routeReady :
    (eraseTailHeadToBlankSentinelDescription tailFirst).SubroutineReady
  routeHalts :
    (eraseTailHeadToBlankSentinelDescription tailFirst).HaltsFromTape
      (tailHeadHandoffTape skipped count tailFirst tail)
      (tailHeadBlankSentinelRawLeftTape skipped count tail)
  leftLengthMatchesHandoff :
    (tailHeadBlankSentinelRawLeftTape skipped count tail).left.length =
      (tailHeadHandoffTape skipped count tailFirst tail).left.length
  sourceRouteReady :
    (sourceToTailHeadBlankSentinelDescription tailFirst).SubroutineReady
  sourceRouteHalts :
    (sourceToTailHeadBlankSentinelDescription tailFirst).HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (tailHeadBlankSentinelRawLeftTape skipped count tail)
  moveToRawBaseReady :
    (leftMoveAcrossBlanksDescription
      (tailHeadImmediateScratchCellCount count)).SubroutineReady
  moveToRawBaseHalts :
    (leftMoveAcrossBlanksDescription
      (tailHeadImmediateScratchCellCount count)).HaltsFromTape
      (tailHeadBlankSentinelRawLeftTape skipped count tail)
      (tailHeadBlankSentinelRawBaseEdgeTape skipped count tail)
  rawBaseEdgeMoveLeftEraserSource :
    Tape.move Direction.left
        (tailHeadBlankSentinelRawBaseEdgeTape skipped count tail) =
      leftBoundaryEraserSourceTape
        ([] : List (Option Bool))
        (List.append skipped count)
        none
        (List.append
          (List.replicate (count.length + 2) (none : Option Bool))
          (none :: tail))
  rawBaseEraserReady :
    eraseTailHeadRawBaseFromEdgeDescription.SubroutineReady
  rawBaseEraserHalts :
    eraseTailHeadRawBaseFromEdgeDescription.HaltsFromTape
      (tailHeadBlankSentinelRawBaseEdgeTape skipped count tail)
      (tailHeadRawBaseErasedLeftBoundaryTape skipped count tail)

theorem rawBoundaryTailHeadBlankerRoute
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    RawBoundaryTailHeadBlankerRoute
      skipped count tailFirst tail :=
  { routeReady :=
      eraseTailHeadToBlankSentinelDescription_subroutineReady tailFirst
    routeHalts :=
      eraseTailHeadToBlankSentinelDescription_haltsFrom_tailHeadHandoffTape
        skipped count tailFirst tail
    leftLengthMatchesHandoff :=
      tailHeadBlankSentinelRawLeftTape_left_length_eq_tailHeadHandoffTape
        skipped count tailFirst tail
    sourceRouteReady :=
      sourceToTailHeadBlankSentinelDescription_subroutineReady tailFirst
    sourceRouteHalts :=
      sourceToTailHeadBlankSentinelDescription_haltsFrom_sourceTape
        skipped count tailFirst tail
    moveToRawBaseReady :=
      leftMoveAcrossBlanksDescription_subroutineReady
        (tailHeadImmediateScratchCellCount count)
    moveToRawBaseHalts :=
      leftMoveAcrossBlanksDescription_haltsFrom_tailHeadBlankSentinelRawLeftTape
        skipped count tail
    rawBaseEdgeMoveLeftEraserSource :=
      tailHeadBlankSentinelRawBaseEdgeTape_moveLeft_eq_boundaryEraserSource
        skipped count tail
    rawBaseEraserReady :=
      eraseTailHeadRawBaseFromEdgeDescription_subroutineReady
    rawBaseEraserHalts :=
      eraseTailHeadRawBaseFromEdgeDescription_haltsFrom_rawBaseEdge
        skipped count tail }

theorem rawBoundary_tailHeadBlanker_halts
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (eraseTailHeadToBlankSentinelDescription tailFirst).HaltsFromTape
      (tailHeadHandoffTape skipped count tailFirst tail)
      (tailHeadBlankSentinelRawLeftTape skipped count tail) :=
  (rawBoundaryTailHeadBlankerRoute
    skipped count tailFirst tail).routeHalts

theorem rawBoundary_tailHeadBlanker_leftLengthMatchesHandoff
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (tailHeadBlankSentinelRawLeftTape skipped count tail).left.length =
      (tailHeadHandoffTape skipped count tailFirst tail).left.length :=
  (rawBoundaryTailHeadBlankerRoute
    skipped count tailFirst tail).leftLengthMatchesHandoff

theorem rawBoundary_sourceToTailHeadBlankSentinel_halts
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (sourceToTailHeadBlankSentinelDescription tailFirst).HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (tailHeadBlankSentinelRawLeftTape skipped count tail) :=
  (rawBoundaryTailHeadBlankerRoute
    skipped count tailFirst tail).sourceRouteHalts

theorem rawBoundary_tailHeadBlankSentinel_moveToRawBase_halts
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (leftMoveAcrossBlanksDescription
      (tailHeadImmediateScratchCellCount count)).HaltsFromTape
      (tailHeadBlankSentinelRawLeftTape skipped count tail)
      (tailHeadBlankSentinelRawBaseEdgeTape skipped count tail) :=
  (rawBoundaryTailHeadBlankerRoute
    skipped count tailFirst tail).moveToRawBaseHalts

theorem rawBoundary_tailHeadBlankSentinel_rawBaseEdge_moveLeft_erasesSource
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.left
        (tailHeadBlankSentinelRawBaseEdgeTape skipped count tail) =
      leftBoundaryEraserSourceTape
        ([] : List (Option Bool))
        (List.append skipped count)
        none
        (List.append
          (List.replicate (count.length + 2) (none : Option Bool))
          (none :: tail)) :=
  (rawBoundaryTailHeadBlankerRoute
    skipped count tailFirst tail).rawBaseEdgeMoveLeftEraserSource

theorem rawBoundary_tailHeadRawBaseEraser_halts
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    eraseTailHeadRawBaseFromEdgeDescription.HaltsFromTape
      (tailHeadBlankSentinelRawBaseEdgeTape skipped count tail)
      (tailHeadRawBaseErasedLeftBoundaryTape skipped count tail) :=
  (rawBoundaryTailHeadBlankerRoute
    skipped count tailFirst tail).rawBaseEraserHalts

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
