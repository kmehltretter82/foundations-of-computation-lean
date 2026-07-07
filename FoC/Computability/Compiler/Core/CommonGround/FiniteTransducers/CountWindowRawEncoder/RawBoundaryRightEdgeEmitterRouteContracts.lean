import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawEncoder.RawBoundaryRightEdgeEmitter

set_option doc.verso true

/-!
# Raw-boundary right-edge emitter route contracts

This module packages the endpoint facts around the count-window raw-boundary
right-edge emitter.  The concrete finite-table core leaf remains in
{module}`FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawEncoder.RawBoundaryRightEdgeEmitter`;
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
  encodedDefaultTarget :
    List.map optionBitDefaultFalse
        (Tape.cells (rightEdgeTape skipped count tailFirst tail)) =
      List.append
        (encodedLayoutBits (List.append skipped count))
        (tailFirst :: tail.map optionBitDefaultFalse)

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
    encodedDefaultTarget :=
      rightEdgeTape_defaultedCells skipped count tailFirst tail }

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

/-!
## Core construction route
-/

structure RawBoundaryRightEdgeEmitterCoreRoute : Prop where
  coreReady :
    rawBoundaryRightEdgeEmitterCoreDescription.SubroutineReady
  wrapperReady :
    rawBoundaryRightEdgeEmitterDescription.SubroutineReady
  coreHaltsRightEdge :
    forall skipped count : Word Bool,
    forall tailFirst : Bool,
    forall tail : List (Option Bool),
      rawBoundaryRightEdgeEmitterCoreDescription.HaltsFromTape
        (sourceTape skipped count (some tailFirst :: tail))
        (rightEdgeTape skipped count tailFirst tail)
  wrapperHaltsPreRewind :
    forall skipped count : Word Bool,
    forall tailFirst : Bool,
    forall tail : List (Option Bool),
      rawBoundaryRightEdgeEmitterDescription.HaltsFromTape
        (sourceTape skipped count (some tailFirst :: tail))
        (preRewindTape skipped count tailFirst tail)
  spec :
    Spec rawBoundaryRightEdgeEmitterDescription
  construction :
    Construction

def RawBoundaryRightEdgeEmitterCoreRouteConstruction : Prop :=
  RawBoundaryRightEdgeEmitterCoreRoute

theorem rawBoundaryRightEdgeEmitterCoreRoute :
    RawBoundaryRightEdgeEmitterCoreRoute :=
  { coreReady :=
      rawBoundaryRightEdgeEmitterCoreDescription_subroutineReady
    wrapperReady :=
      rawBoundaryRightEdgeEmitterDescription_subroutineReady
    coreHaltsRightEdge := by
      intro skipped count tailFirst tail
      exact
        rawBoundaryRightEdgeEmitterCoreDescription_haltsFrom_sourceTape_rightEdge
          skipped count tailFirst tail
    wrapperHaltsPreRewind := by
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

theorem rawBoundaryRightEdgeEmitterCoreDescription_haltsFrom_sourceTape_rightEdge_route
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    rawBoundaryRightEdgeEmitterCoreDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (rightEdgeTape skipped count tailFirst tail) :=
  (rawBoundaryRightEdgeEmitterCoreRoute).coreHaltsRightEdge
    skipped count tailFirst tail

theorem rawBoundaryRightEdgeEmitterDescription_haltsFrom_sourceTape_route
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    rawBoundaryRightEdgeEmitterDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (preRewindTape skipped count tailFirst tail) :=
  (rawBoundaryRightEdgeEmitterCoreRoute).wrapperHaltsPreRewind
    skipped count tailFirst tail

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
  sourceToRightEdge :
    rawBoundaryRightEdgeEmitterCoreDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (rightEdgeTape skipped count tailFirst tail)
  sourceToPreRewind :
    rawBoundaryRightEdgeEmitterDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (preRewindTape skipped count tailFirst tail)
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
    sourceToRightEdge :=
      rawBoundaryRightEdgeEmitterCoreDescription_haltsFrom_sourceTape_rightEdge
        skipped count tailFirst tail
    sourceToPreRewind :=
      rawBoundaryRightEdgeEmitterDescription_haltsFrom_sourceTape
        skipped count tailFirst tail
    rightEdgeMove :=
      preRewindTape_moveRight skipped count tailFirst tail }

theorem rawBoundaryRightEdgeEmitterEndpointRoute_sourceToPreRewind
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    rawBoundaryRightEdgeEmitterDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (preRewindTape skipped count tailFirst tail) :=
  (rawBoundaryRightEdgeEmitterEndpointRoute
    skipped count tailFirst tail).sourceToPreRewind

theorem rawBoundaryRightEdgeEmitterEndpointRoute_sourceToRightEdge
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    rawBoundaryRightEdgeEmitterCoreDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (rightEdgeTape skipped count tailFirst tail) :=
  (rawBoundaryRightEdgeEmitterEndpointRoute
    skipped count tailFirst tail).sourceToRightEdge

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
