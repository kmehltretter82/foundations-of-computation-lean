import FoC.Computability.Compiler.FST.CountWindow

set_option doc.verso true

/-!
# Count-window raw-source encoder route contracts

This module packages the public count-window raw-source encoder route.  The
low-level right-edge emitter finite leaf remains in
{module}`FoC.Computability.Compiler.FST.CountWindow.RawBoundary`;
the route contracts here expose the parent endpoint shape and the construction
chain from the raw-boundary right-edge emitter through the no-count-padding
equivalence endpoint to the public raw-source encoder equivalence
construction.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf

namespace CommonGround
namespace FiniteTransducers

/-!
## Static endpoint shape
-/

structure CountWindowRawSourceEncoderEndpointShape
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) : Prop where
  targetTapeEqOutputCells :
    countWindowRawSourceEncoderTargetTape
        skipped count (some tailFirst :: tail) =
      tapeAtCells [none]
        (countWindowRawSourceEncoderOutputCells
          skipped count (some tailFirst :: tail))
  noCountPaddingEqEncodedLayout :
    countWindowRawSourceEncoderTargetTapeNoCountPadding
        skipped count (some tailFirst :: tail) =
      tapeAtCells [none]
        (List.append
          (countWindowRawSourceEncoderEncodedLayoutCells
            (List.append skipped count))
          (some tailFirst :: tail))
  targetEquivNoCountPadding :
    Tape.Equiv
      (countWindowRawSourceEncoderTargetTape
        skipped count (some tailFirst :: tail))
      (countWindowRawSourceEncoderTargetTapeNoCountPadding
        skipped count (some tailFirst :: tail))
  noCountPaddingEqHeaderBoolWord :
    countWindowRawSourceEncoderTargetTapeNoCountPadding
        skipped count (some tailFirst :: tail) =
      tapeAtCells [none]
        (List.append
          ((encodeCodeWordAsInput
            (MachineCodeSymbol.header ::
              encodeBoolWordAppend (List.append skipped count) [])).map
              some)
          (some tailFirst :: tail))
  encodedRightEdgeRewind :
    rightEdgeRewindDescription.HaltsFromTape
      (countWindowRawSourceEncoderEncodedLayoutRightEdgeTape
        skipped count tailFirst tail)
      (countWindowRawSourceEncoderTargetTapeNoCountPadding
        skipped count (some tailFirst :: tail))
  encodedPreRewindMoveRight :
    Tape.move Direction.right
        (countWindowRawSourceEncoderEncodedLayoutPreRewindTape
          skipped count tailFirst tail) =
      countWindowRawSourceEncoderEncodedLayoutRightEdgeTape
        skipped count tailFirst tail
  encodedLengthGreaterThanSourcePrefix :
    (List.append skipped count).length + 3 + count.length <
      (countWindowRawSourceEncoderEncodedLayoutCells
        (List.append skipped count)).length

theorem countWindowRawSourceEncoderEndpointShape
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    CountWindowRawSourceEncoderEndpointShape
      skipped count tailFirst tail :=
  { targetTapeEqOutputCells :=
      countWindowRawSourceEncoderTargetTape_eq_outputCells
        skipped count (some tailFirst :: tail)
    noCountPaddingEqEncodedLayout :=
      countWindowRawSourceEncoderTargetTapeNoCountPadding_eq_encodedLayoutCells
        skipped count (some tailFirst :: tail)
    targetEquivNoCountPadding :=
      countWindowRawSourceEncoderTargetTape_equiv_noCountPadding
        skipped count (some tailFirst :: tail)
    noCountPaddingEqHeaderBoolWord :=
      countWindowRawSourceEncoderTargetTapeNoCountPadding_eq_headerBoolWord
        skipped count (some tailFirst :: tail)
    encodedRightEdgeRewind :=
      countWindowRawSourceEncoderEncodedLayoutRightEdgeTape_rewind_haltsFromTape
        skipped count tailFirst tail
    encodedPreRewindMoveRight :=
      countWindowRawSourceEncoderEncodedLayoutPreRewindTape_moveRight
        skipped count tailFirst tail
    encodedLengthGreaterThanSourcePrefix :=
      countWindowRawSourceEncoderEncodedLayoutCells_length_gt_sourcePrefix
        skipped count }

theorem countWindowRawSourceEncoder_endpoint_target_eq_outputCells
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    countWindowRawSourceEncoderTargetTape
        skipped count (some tailFirst :: tail) =
      tapeAtCells [none]
        (countWindowRawSourceEncoderOutputCells
          skipped count (some tailFirst :: tail)) :=
  (countWindowRawSourceEncoderEndpointShape
    skipped count tailFirst tail).targetTapeEqOutputCells

theorem countWindowRawSourceEncoder_endpoint_target_equiv_noCountPadding
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.Equiv
      (countWindowRawSourceEncoderTargetTape
        skipped count (some tailFirst :: tail))
      (countWindowRawSourceEncoderTargetTapeNoCountPadding
        skipped count (some tailFirst :: tail)) :=
  (countWindowRawSourceEncoderEndpointShape
    skipped count tailFirst tail).targetEquivNoCountPadding

theorem countWindowRawSourceEncoder_endpoint_preRewind_moveRight
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.right
        (countWindowRawSourceEncoderEncodedLayoutPreRewindTape
          skipped count tailFirst tail) =
      countWindowRawSourceEncoderEncodedLayoutRightEdgeTape
        skipped count tailFirst tail :=
  (countWindowRawSourceEncoderEndpointShape
    skipped count tailFirst tail).encodedPreRewindMoveRight

/-!
## Scan and positioning route
-/

structure CountWindowRawSourceEncoderScanRoute
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) : Prop where
  rightEdgeScan :
    rightEdgeScanDescription.HaltsFromTape
      (countWindowRawSourceEncoderSourceTape
        skipped count (some tailFirst :: tail))
      (countWindowRawSourceEncoderRightEdgeTape
        skipped count (some tailFirst :: tail))
  scanToCountWindowStartReady :
    countWindowRawSourceEncoderScanToCountWindowStartDescription.SubroutineReady
  scanToCountWindowStart :
    countWindowRawSourceEncoderScanToCountWindowStartDescription.HaltsFromTape
      (countWindowRawSourceEncoderSourceTape
        skipped count (some tailFirst :: tail))
      (countWindowRawSourceEncoderCountWindowStartTape
        skipped count (some tailFirst :: tail))
  scanToBeforeCountWindowReady :
    countWindowRawSourceEncoderScanToBeforeCountWindowDescription.SubroutineReady
  scanToBeforeCountWindow :
    countWindowRawSourceEncoderScanToBeforeCountWindowDescription.HaltsFromTape
      (countWindowRawSourceEncoderSourceTape
        skipped count (some tailFirst :: tail))
      (countWindowRawSourceEncoderBeforeCountWindowTape
        skipped count (some tailFirst :: tail))
  beforeCountWindowMoveRight :
    Tape.move Direction.right
        (countWindowRawSourceEncoderBeforeCountWindowTape
          skipped count (some tailFirst :: tail)) =
      countWindowRawSourceEncoderCountWindowStartTape
        skipped count (some tailFirst :: tail)
  tailPastFirstReady :
    countWindowRawSourceEncoderScanToTailPastFirstDescription.SubroutineReady
  scanToTailPastFirst :
    countWindowRawSourceEncoderScanToTailPastFirstDescription.HaltsFromTape
      (countWindowRawSourceEncoderSourceTape
        skipped count (some tailFirst :: tail))
      (countWindowRawSourceEncoderTailPastFirstTape
        skipped count tailFirst tail)

theorem countWindowRawSourceEncoderScanRoute
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    CountWindowRawSourceEncoderScanRoute
      skipped count tailFirst tail :=
  { rightEdgeScan :=
      countWindowRawSourceEncoderRightEdgeScan_haltsFromTape
        skipped count (some tailFirst :: tail)
    scanToCountWindowStartReady :=
      countWindowRawSourceEncoderScanToCountWindowStartDescription_subroutineReady
    scanToCountWindowStart :=
      countWindowRawSourceEncoderScanToCountWindowStartDescription_haltsFromTape
        skipped count (some tailFirst :: tail)
    scanToBeforeCountWindowReady :=
      countWindowRawSourceEncoderScanToBeforeCountWindowDescription_subroutineReady
    scanToBeforeCountWindow :=
      countWindowRawSourceEncoderScanToBeforeCountWindowDescription_haltsFromTape
        skipped count (some tailFirst :: tail)
    beforeCountWindowMoveRight :=
      countWindowRawSourceEncoderBeforeCountWindowTape_moveRight
        skipped count (some tailFirst :: tail)
    tailPastFirstReady :=
      countWindowRawSourceEncoderScanToTailPastFirstDescription_subroutineReady
    scanToTailPastFirst :=
      countWindowRawSourceEncoderScanToTailPastFirstDescription_haltsFromTape
        skipped count tailFirst tail }

theorem countWindowRawSourceEncoder_scanToCountWindowStart
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    countWindowRawSourceEncoderScanToCountWindowStartDescription.HaltsFromTape
      (countWindowRawSourceEncoderSourceTape
        skipped count (some tailFirst :: tail))
      (countWindowRawSourceEncoderCountWindowStartTape
        skipped count (some tailFirst :: tail)) :=
  (countWindowRawSourceEncoderScanRoute
    skipped count tailFirst tail).scanToCountWindowStart

theorem countWindowRawSourceEncoder_scanToBeforeCountWindow
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    countWindowRawSourceEncoderScanToBeforeCountWindowDescription.HaltsFromTape
      (countWindowRawSourceEncoderSourceTape
        skipped count (some tailFirst :: tail))
      (countWindowRawSourceEncoderBeforeCountWindowTape
        skipped count (some tailFirst :: tail)) :=
  (countWindowRawSourceEncoderScanRoute
    skipped count tailFirst tail).scanToBeforeCountWindow

theorem countWindowRawSourceEncoder_scanToTailPastFirst
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) :
    countWindowRawSourceEncoderScanToTailPastFirstDescription.HaltsFromTape
      (countWindowRawSourceEncoderSourceTape
        skipped count (some tailFirst :: tail))
      (countWindowRawSourceEncoderTailPastFirstTape
        skipped count tailFirst tail) :=
  (countWindowRawSourceEncoderScanRoute
    skipped count tailFirst tail).scanToTailPastFirst

/-!
## Raw-boundary equivalence route
-/

structure CountWindowRawSourceEncoderRawBoundaryEmitterEquivRoute
    (emitter : MachineDescription) : Prop where
  spec :
    CountWindowRawSourceEncoderRawBoundaryEmitterEquivSpec emitter
  subroutineReady :
    emitter.SubroutineReady
  haltsRawBoundaryEquiv :
    forall skipped count : Word Bool,
    forall tailFirst : Bool,
    forall tail : List (Option Bool),
      emitter.HaltsFromTapeEquiv
        (countWindowRawSourceEncoderRawBoundaryTape
          skipped count (some tailFirst :: tail))
        (countWindowRawSourceEncoderTargetTapeNoCountPadding
          skipped count (some tailFirst :: tail))

def CountWindowRawSourceEncoderRawBoundaryEmitterEquivRouteConstruction :
    Prop :=
  exists emitter : MachineDescription,
    CountWindowRawSourceEncoderRawBoundaryEmitterEquivRoute emitter

theorem countWindowRawSourceEncoderRawBoundaryEmitterEquivRoute_of_spec
    {emitter : MachineDescription}
    (h :
      CountWindowRawSourceEncoderRawBoundaryEmitterEquivSpec emitter) :
    CountWindowRawSourceEncoderRawBoundaryEmitterEquivRoute emitter :=
  { spec := h
    subroutineReady := h.left
    haltsRawBoundaryEquiv := h.right }

theorem countWindowRawSourceEncoderRawBoundaryEmitterEquivRoute_of_construction
    (h :
      CountWindowRawSourceEncoderRawBoundaryEmitterEquivConstruction) :
    CountWindowRawSourceEncoderRawBoundaryEmitterEquivRouteConstruction := by
  rcases h with ⟨emitter, hemits⟩
  exact
    ⟨emitter,
      countWindowRawSourceEncoderRawBoundaryEmitterEquivRoute_of_spec
        hemits⟩

/-!
## Count-window-start and no-count-padding routes
-/

structure CountWindowRawSourceEncoderCountWindowStartEmitterEquivRoute
    (emitter : MachineDescription) : Prop where
  spec :
    CountWindowRawSourceEncoderCountWindowStartEmitterEquivSpec emitter
  subroutineReady :
    emitter.SubroutineReady
  haltsCountWindowStartEquiv :
    forall skipped count : Word Bool,
    forall tailFirst : Bool,
    forall tail : List (Option Bool),
      emitter.HaltsFromTapeEquiv
        (countWindowRawSourceEncoderCountWindowStartTape
          skipped count (some tailFirst :: tail))
        (countWindowRawSourceEncoderTargetTapeNoCountPadding
          skipped count (some tailFirst :: tail))

def CountWindowRawSourceEncoderCountWindowStartEmitterEquivRouteConstruction :
    Prop :=
  exists emitter : MachineDescription,
    CountWindowRawSourceEncoderCountWindowStartEmitterEquivRoute emitter

theorem countWindowRawSourceEncoderCountWindowStartEmitterEquivRoute_of_spec
    {emitter : MachineDescription}
    (h :
      CountWindowRawSourceEncoderCountWindowStartEmitterEquivSpec emitter) :
    CountWindowRawSourceEncoderCountWindowStartEmitterEquivRoute emitter :=
  { spec := h
    subroutineReady := h.left
    haltsCountWindowStartEquiv := h.right }

theorem countWindowRawSourceEncoderCountWindowStartEmitterEquivRoute_of_construction
    (h :
      CountWindowRawSourceEncoderCountWindowStartEmitterEquivConstruction) :
    CountWindowRawSourceEncoderCountWindowStartEmitterEquivRouteConstruction := by
  rcases h with ⟨emitter, hemits⟩
  exact
    ⟨emitter,
      countWindowRawSourceEncoderCountWindowStartEmitterEquivRoute_of_spec
        hemits⟩

structure CountWindowRawSourceEncoderNoCountPaddingEquivRoute
    (encoder : MachineDescription) : Prop where
  spec :
    CountWindowRawSourceEncoderNoCountPaddingEquivSpec encoder
  subroutineReady :
    encoder.SubroutineReady
  haltsNoCountPaddingEquiv :
    forall skipped count : Word Bool,
    forall tailFirst : Bool,
    forall tail : List (Option Bool),
      encoder.HaltsFromTapeEquiv
        (countWindowRawSourceEncoderSourceTape
          skipped count (some tailFirst :: tail))
        (countWindowRawSourceEncoderTargetTapeNoCountPadding
          skipped count (some tailFirst :: tail))
  targetEquivNoCountPadding :
    forall skipped count : Word Bool,
    forall tailFirst : Bool,
    forall tail : List (Option Bool),
      Tape.Equiv
        (countWindowRawSourceEncoderTargetTape
          skipped count (some tailFirst :: tail))
        (countWindowRawSourceEncoderTargetTapeNoCountPadding
          skipped count (some tailFirst :: tail))

def CountWindowRawSourceEncoderNoCountPaddingEquivRouteConstruction :
    Prop :=
  exists encoder : MachineDescription,
    CountWindowRawSourceEncoderNoCountPaddingEquivRoute encoder

theorem countWindowRawSourceEncoderNoCountPaddingEquivRoute_of_spec
    {encoder : MachineDescription}
    (h :
      CountWindowRawSourceEncoderNoCountPaddingEquivSpec encoder) :
    CountWindowRawSourceEncoderNoCountPaddingEquivRoute encoder :=
  { spec := h
    subroutineReady := h.left
    haltsNoCountPaddingEquiv := h.right
    targetEquivNoCountPadding := by
      intro skipped count tailFirst tail
      exact
        countWindowRawSourceEncoderTargetTape_equiv_noCountPadding
          skipped count (some tailFirst :: tail) }

theorem countWindowRawSourceEncoderNoCountPaddingEquivRoute_of_construction
    (h :
      CountWindowRawSourceEncoderNoCountPaddingEquivConstruction) :
    CountWindowRawSourceEncoderNoCountPaddingEquivRouteConstruction := by
  rcases h with ⟨encoder, hencoder⟩
  exact
    ⟨encoder,
      countWindowRawSourceEncoderNoCountPaddingEquivRoute_of_spec
        hencoder⟩

/-!
## Public equivalence route
-/

structure CountWindowRawSourceEncoderEquivRoute
    (encoder : MachineDescription) : Prop where
  spec :
    CountWindowRawSourceEncoderEquivSpec encoder
  subroutineReady :
    encoder.SubroutineReady
  haltsTargetEquiv :
    forall skipped count : Word Bool,
    forall tailFirst : Bool,
    forall tail : List (Option Bool),
      encoder.HaltsFromTapeEquiv
        (countWindowRawSourceEncoderSourceTape
          skipped count (some tailFirst :: tail))
        (countWindowRawSourceEncoderTargetTape
          skipped count (some tailFirst :: tail))
  endpointShape :
    forall skipped count : Word Bool,
    forall tailFirst : Bool,
    forall tail : List (Option Bool),
      CountWindowRawSourceEncoderEndpointShape
        skipped count tailFirst tail
  scanRoute :
    forall skipped count : Word Bool,
    forall tailFirst : Bool,
    forall tail : List (Option Bool),
      CountWindowRawSourceEncoderScanRoute
        skipped count tailFirst tail

def CountWindowRawSourceEncoderEquivRouteConstruction : Prop :=
  exists encoder : MachineDescription,
    CountWindowRawSourceEncoderEquivRoute encoder

theorem countWindowRawSourceEncoderEquivRoute_of_spec
    {encoder : MachineDescription}
    (h :
      CountWindowRawSourceEncoderEquivSpec encoder) :
    CountWindowRawSourceEncoderEquivRoute encoder :=
  { spec := h
    subroutineReady := h.left
    haltsTargetEquiv := h.right
    endpointShape := by
      intro skipped count tailFirst tail
      exact
        countWindowRawSourceEncoderEndpointShape
          skipped count tailFirst tail
    scanRoute := by
      intro skipped count tailFirst tail
      exact
        countWindowRawSourceEncoderScanRoute
          skipped count tailFirst tail }

theorem countWindowRawSourceEncoderEquivRoute_of_construction
    (h :
      CountWindowRawSourceEncoderEquivConstruction) :
    CountWindowRawSourceEncoderEquivRouteConstruction := by
  rcases h with ⟨encoder, hencoder⟩
  exact
    ⟨encoder,
      countWindowRawSourceEncoderEquivRoute_of_spec hencoder⟩

/-!
## Construction-chain route
-/

structure CountWindowRawSourceEncoderConstructionChainRoute : Prop where
  rawBoundaryEquiv :
    CountWindowRawSourceEncoderRawBoundaryEmitterEquivConstruction
  rawBoundaryEquivRoute :
    CountWindowRawSourceEncoderRawBoundaryEmitterEquivRouteConstruction
  countWindowStartEquiv :
    CountWindowRawSourceEncoderCountWindowStartEmitterEquivConstruction
  countWindowStartEquivRoute :
    CountWindowRawSourceEncoderCountWindowStartEmitterEquivRouteConstruction
  noCountPaddingEquiv :
    CountWindowRawSourceEncoderNoCountPaddingEquivConstruction
  noCountPaddingEquivRoute :
    CountWindowRawSourceEncoderNoCountPaddingEquivRouteConstruction
  publicEquiv :
    CountWindowRawSourceEncoderEquivConstruction
  publicEquivRoute :
    CountWindowRawSourceEncoderEquivRouteConstruction
  liveTailExactImpossible :
    ¬ CountWindowRawSourceEncoderLiveTailEmitterConstruction
  arbitraryTailExactImpossible :
    forall encoder : MachineDescription,
      ¬ CountWindowRawSourceEncoderArbitraryTailSpec encoder

def CountWindowRawSourceEncoderConstructionChainRouteConstruction :
    Prop :=
  CountWindowRawSourceEncoderConstructionChainRoute

theorem countWindowRawSourceEncoderConstructionChainRoute_core :
    CountWindowRawSourceEncoderConstructionChainRoute :=
  { rawBoundaryEquiv :=
      countWindowRawSourceEncoderRawBoundaryEmitterEquivConstruction_core
    rawBoundaryEquivRoute :=
      countWindowRawSourceEncoderRawBoundaryEmitterEquivRoute_of_construction
        countWindowRawSourceEncoderRawBoundaryEmitterEquivConstruction_core
    countWindowStartEquiv :=
      countWindowRawSourceEncoderCountWindowStartEmitterEquivConstruction_core
    countWindowStartEquivRoute :=
      countWindowRawSourceEncoderCountWindowStartEmitterEquivRoute_of_construction
        countWindowRawSourceEncoderCountWindowStartEmitterEquivConstruction_core
    noCountPaddingEquiv :=
      countWindowRawSourceEncoderNoCountPaddingEquivConstruction_core
    noCountPaddingEquivRoute :=
      countWindowRawSourceEncoderNoCountPaddingEquivRoute_of_construction
        countWindowRawSourceEncoderNoCountPaddingEquivConstruction_core
    publicEquiv :=
      countWindowRawSourceEncoderEquivConstruction_core
    publicEquivRoute :=
      countWindowRawSourceEncoderEquivRoute_of_construction
        countWindowRawSourceEncoderEquivConstruction_core
    liveTailExactImpossible :=
      countWindowRawSourceEncoderLiveTailEmitterConstruction_impossible
    arbitraryTailExactImpossible := by
      intro encoder
      exact countWindowRawSourceEncoderArbitraryTailSpec_impossible encoder }

theorem countWindowRawSourceEncoderConstructionChainRouteConstruction_core :
    CountWindowRawSourceEncoderConstructionChainRouteConstruction :=
  countWindowRawSourceEncoderConstructionChainRoute_core

/-!
## Public aliases
-/

theorem countWindowRawSourceEncoderRawBoundaryEmitterEquivConstruction_route :
    CountWindowRawSourceEncoderRawBoundaryEmitterEquivConstruction :=
  countWindowRawSourceEncoderConstructionChainRoute_core.rawBoundaryEquiv

theorem countWindowRawSourceEncoderCountWindowStartEmitterEquivConstruction_route :
    CountWindowRawSourceEncoderCountWindowStartEmitterEquivConstruction :=
  countWindowRawSourceEncoderConstructionChainRoute_core.countWindowStartEquiv

theorem countWindowRawSourceEncoderNoCountPaddingEquivConstruction_route :
    CountWindowRawSourceEncoderNoCountPaddingEquivConstruction :=
  countWindowRawSourceEncoderConstructionChainRoute_core.noCountPaddingEquiv

theorem countWindowRawSourceEncoderEquivConstruction_route :
    CountWindowRawSourceEncoderEquivConstruction :=
  countWindowRawSourceEncoderConstructionChainRoute_core.publicEquiv

theorem countWindowRawSourceEncoderEquivRouteConstruction_route :
    CountWindowRawSourceEncoderEquivRouteConstruction :=
  countWindowRawSourceEncoderConstructionChainRoute_core.publicEquivRoute

end FiniteTransducers
end CommonGround

end Computability
end FoC
