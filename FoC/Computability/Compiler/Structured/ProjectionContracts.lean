import FoC.Computability.Compiler.Structured.Lowering.Projection

set_option doc.verso true

/-!
# Structured projection route contracts

This module packages the reusable projection side of structured multi-tape
lowering.  It records route-level views for tape projectors, segment
normalizers, selected-segment decoders, and the generated selected-segment
logical-tape decoder endpoint.  The file does not introduce new finite-machine
construction leaves; it packages existing specs and construction adapters.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

namespace ProjectionRouteContracts

/-!
## Projector routes
-/

structure Tape0ProjectorRouteSpec
    (projector : MachineDescription) : Prop where
  spec :
    StructuredTape0ProjectorSpec projector
  subroutineReady :
    projector.SubroutineReady
  halts :
    forall T0 T1 T2 : Tape Bool,
      projector.HaltsFromTapeEquiv
        (encodedGuardedStructured3Tapes T0 T1 T2)
        T0

def Tape0ProjectorRouteConstruction : Prop :=
  exists projector : MachineDescription,
    Tape0ProjectorRouteSpec projector

theorem tape0ProjectorRouteSpec_of_spec
    {projector : MachineDescription}
    (hprojector : StructuredTape0ProjectorSpec projector) :
    Tape0ProjectorRouteSpec projector :=
  { spec := hprojector
    subroutineReady := hprojector.left
    halts := hprojector.right }

theorem tape0ProjectorConstruction_of_routeConstruction
    (hroute : Tape0ProjectorRouteConstruction) :
    StructuredTape0ProjectorConstruction := by
  rcases hroute with ⟨projector, hprojector⟩
  exact ⟨projector, hprojector.spec⟩

theorem tape0ProjectorRouteConstruction_of_projectorConstruction
    (hprojector : StructuredTape0ProjectorConstruction) :
    Tape0ProjectorRouteConstruction := by
  rcases hprojector with ⟨projector, hspec⟩
  exact ⟨projector, tape0ProjectorRouteSpec_of_spec hspec⟩

theorem tape0ProjectorRouteConstruction_iff_projectorConstruction :
    Tape0ProjectorRouteConstruction ↔
      StructuredTape0ProjectorConstruction := by
  constructor
  · exact tape0ProjectorConstruction_of_routeConstruction
  · exact tape0ProjectorRouteConstruction_of_projectorConstruction

structure Tape1ProjectorRouteSpec
    (projector : MachineDescription) : Prop where
  spec :
    StructuredTape1ProjectorSpec projector
  subroutineReady :
    projector.SubroutineReady
  halts :
    forall T0 T1 T2 : Tape Bool,
      projector.HaltsFromTapeEquiv
        (encodedGuardedStructured3Tapes T0 T1 T2)
        T1

def Tape1ProjectorRouteConstruction : Prop :=
  exists projector : MachineDescription,
    Tape1ProjectorRouteSpec projector

theorem tape1ProjectorRouteSpec_of_spec
    {projector : MachineDescription}
    (hprojector : StructuredTape1ProjectorSpec projector) :
    Tape1ProjectorRouteSpec projector :=
  { spec := hprojector
    subroutineReady := hprojector.left
    halts := hprojector.right }

theorem tape1ProjectorConstruction_of_routeConstruction
    (hroute : Tape1ProjectorRouteConstruction) :
    StructuredTape1ProjectorConstruction := by
  rcases hroute with ⟨projector, hprojector⟩
  exact ⟨projector, hprojector.spec⟩

theorem tape1ProjectorRouteConstruction_of_projectorConstruction
    (hprojector : StructuredTape1ProjectorConstruction) :
    Tape1ProjectorRouteConstruction := by
  rcases hprojector with ⟨projector, hspec⟩
  exact ⟨projector, tape1ProjectorRouteSpec_of_spec hspec⟩

theorem tape1ProjectorRouteConstruction_iff_projectorConstruction :
    Tape1ProjectorRouteConstruction ↔
      StructuredTape1ProjectorConstruction := by
  constructor
  · exact tape1ProjectorConstruction_of_routeConstruction
  · exact tape1ProjectorRouteConstruction_of_projectorConstruction

structure Tape2ProjectorRouteSpec
    (projector : MachineDescription) : Prop where
  spec :
    StructuredTape2ProjectorSpec projector
  subroutineReady :
    projector.SubroutineReady
  halts :
    forall T0 T1 T2 : Tape Bool,
      projector.HaltsFromTapeEquiv
        (encodedGuardedStructured3Tapes T0 T1 T2)
        T2

def Tape2ProjectorRouteConstruction : Prop :=
  exists projector : MachineDescription,
    Tape2ProjectorRouteSpec projector

theorem tape2ProjectorRouteSpec_of_spec
    {projector : MachineDescription}
    (hprojector : StructuredTape2ProjectorSpec projector) :
    Tape2ProjectorRouteSpec projector :=
  { spec := hprojector
    subroutineReady := hprojector.left
    halts := hprojector.right }

theorem tape2ProjectorConstruction_of_routeConstruction
    (hroute : Tape2ProjectorRouteConstruction) :
    StructuredTape2ProjectorConstruction := by
  rcases hroute with ⟨projector, hprojector⟩
  exact ⟨projector, hprojector.spec⟩

theorem tape2ProjectorRouteConstruction_of_projectorConstruction
    (hprojector : StructuredTape2ProjectorConstruction) :
    Tape2ProjectorRouteConstruction := by
  rcases hprojector with ⟨projector, hspec⟩
  exact ⟨projector, tape2ProjectorRouteSpec_of_spec hspec⟩

theorem tape2ProjectorRouteConstruction_iff_projectorConstruction :
    Tape2ProjectorRouteConstruction ↔
      StructuredTape2ProjectorConstruction := by
  constructor
  · exact tape2ProjectorConstruction_of_routeConstruction
  · exact tape2ProjectorRouteConstruction_of_projectorConstruction

/-!
## Segment normalizer routes
-/

structure Tape0SegmentNormalizerRouteSpec
    (normalizer : MachineDescription) : Prop where
  spec :
    StructuredTape0SegmentNormalizerSpec normalizer
  subroutineReady :
    normalizer.SubroutineReady
  halts :
    forall (T0 T1 T2 : Tape Bool) (physical : Tape Bool),
      AtTapeSeparator (guardLogicalTapes [T0, T1, T2]) 0 physical ->
        normalizer.HaltsFromTapeEquiv physical T0

def Tape0SegmentNormalizerRouteConstruction : Prop :=
  exists normalizer : MachineDescription,
    Tape0SegmentNormalizerRouteSpec normalizer

theorem tape0SegmentNormalizerRouteSpec_of_spec
    {normalizer : MachineDescription}
    (hnormalizer :
      StructuredTape0SegmentNormalizerSpec normalizer) :
    Tape0SegmentNormalizerRouteSpec normalizer :=
  { spec := hnormalizer
    subroutineReady := hnormalizer.left
    halts := hnormalizer.right }

theorem tape0SegmentNormalizerRouteConstruction_of_construction
    (hnormalizer :
      StructuredTape0SegmentNormalizerConstruction) :
    Tape0SegmentNormalizerRouteConstruction := by
  rcases hnormalizer with ⟨normalizer, hspec⟩
  exact
    ⟨normalizer,
      tape0SegmentNormalizerRouteSpec_of_spec hspec⟩

theorem tape0SegmentNormalizerConstruction_of_routeConstruction
    (hroute :
      Tape0SegmentNormalizerRouteConstruction) :
    StructuredTape0SegmentNormalizerConstruction := by
  rcases hroute with ⟨normalizer, hnormalizer⟩
  exact ⟨normalizer, hnormalizer.spec⟩

structure Tape1SegmentNormalizerRouteSpec
    (normalizer : MachineDescription) : Prop where
  spec :
    StructuredTape1SegmentNormalizerSpec normalizer
  subroutineReady :
    normalizer.SubroutineReady
  halts :
    forall (T0 T1 T2 : Tape Bool) (physical : Tape Bool),
      AtTapeSeparator (guardLogicalTapes [T0, T1, T2]) 1 physical ->
        normalizer.HaltsFromTapeEquiv physical T1

def Tape1SegmentNormalizerRouteConstruction : Prop :=
  exists normalizer : MachineDescription,
    Tape1SegmentNormalizerRouteSpec normalizer

theorem tape1SegmentNormalizerRouteSpec_of_spec
    {normalizer : MachineDescription}
    (hnormalizer :
      StructuredTape1SegmentNormalizerSpec normalizer) :
    Tape1SegmentNormalizerRouteSpec normalizer :=
  { spec := hnormalizer
    subroutineReady := hnormalizer.left
    halts := hnormalizer.right }

theorem tape1SegmentNormalizerRouteConstruction_of_construction
    (hnormalizer :
      StructuredTape1SegmentNormalizerConstruction) :
    Tape1SegmentNormalizerRouteConstruction := by
  rcases hnormalizer with ⟨normalizer, hspec⟩
  exact
    ⟨normalizer,
      tape1SegmentNormalizerRouteSpec_of_spec hspec⟩

theorem tape1SegmentNormalizerConstruction_of_routeConstruction
    (hroute :
      Tape1SegmentNormalizerRouteConstruction) :
    StructuredTape1SegmentNormalizerConstruction := by
  rcases hroute with ⟨normalizer, hnormalizer⟩
  exact ⟨normalizer, hnormalizer.spec⟩

structure Tape2SegmentNormalizerRouteSpec
    (normalizer : MachineDescription) : Prop where
  spec :
    StructuredTape2SegmentNormalizerSpec normalizer
  subroutineReady :
    normalizer.SubroutineReady
  halts :
    forall (T0 T1 T2 : Tape Bool) (physical : Tape Bool),
      AtTapeSeparator (guardLogicalTapes [T0, T1, T2]) 2 physical ->
        normalizer.HaltsFromTapeEquiv physical T2

def Tape2SegmentNormalizerRouteConstruction : Prop :=
  exists normalizer : MachineDescription,
    Tape2SegmentNormalizerRouteSpec normalizer

theorem tape2SegmentNormalizerRouteSpec_of_spec
    {normalizer : MachineDescription}
    (hnormalizer :
      StructuredTape2SegmentNormalizerSpec normalizer) :
    Tape2SegmentNormalizerRouteSpec normalizer :=
  { spec := hnormalizer
    subroutineReady := hnormalizer.left
    halts := hnormalizer.right }

theorem tape2SegmentNormalizerRouteConstruction_of_construction
    (hnormalizer :
      StructuredTape2SegmentNormalizerConstruction) :
    Tape2SegmentNormalizerRouteConstruction := by
  rcases hnormalizer with ⟨normalizer, hspec⟩
  exact
    ⟨normalizer,
      tape2SegmentNormalizerRouteSpec_of_spec hspec⟩

theorem tape2SegmentNormalizerConstruction_of_routeConstruction
    (hroute :
      Tape2SegmentNormalizerRouteConstruction) :
    StructuredTape2SegmentNormalizerConstruction := by
  rcases hroute with ⟨normalizer, hnormalizer⟩
  exact ⟨normalizer, hnormalizer.spec⟩

/-!
## Projector routes from normalizer routes
-/

theorem tape0ProjectorRouteConstruction_of_segmentNormalizerRoute
    (hroute :
      Tape0SegmentNormalizerRouteConstruction) :
    Tape0ProjectorRouteConstruction :=
  tape0ProjectorRouteConstruction_of_projectorConstruction
    (structuredTape0ProjectorConstruction_of_segmentNormalizerConstruction
      (tape0SegmentNormalizerConstruction_of_routeConstruction hroute))

theorem tape1ProjectorRouteConstruction_of_segmentNormalizerRoute
    (hroute :
      Tape1SegmentNormalizerRouteConstruction) :
    Tape1ProjectorRouteConstruction :=
  tape1ProjectorRouteConstruction_of_projectorConstruction
    (structuredTape1ProjectorConstruction_of_segmentNormalizerConstruction
      (tape1SegmentNormalizerConstruction_of_routeConstruction hroute))

theorem tape2ProjectorRouteConstruction_of_segmentNormalizerRoute
    (hroute :
      Tape2SegmentNormalizerRouteConstruction) :
    Tape2ProjectorRouteConstruction :=
  tape2ProjectorRouteConstruction_of_projectorConstruction
    (structuredTape2ProjectorConstruction_of_segmentNormalizerConstruction
      (tape2SegmentNormalizerConstruction_of_routeConstruction hroute))

/-!
## Selected decoder endpoint shape
-/

structure SelectedSegmentLogicalTapeDecoderEndpointShape
    (target : Tape Bool)
    (encodedPrefix : List (Option Bool)) : Prop where
  decoderReady :
    selectedSegmentLogicalTapeDecoderDescription.SubroutineReady
  haltsFromSelectedPayload :
    selectedSegmentLogicalTapeDecoderDescription.HaltsFromTape
      (Tape.move Direction.right
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells [guardLogicalTape target])))
      (selectedSegmentLogicalTapeDecoderTargetTape
        target encodedPrefix)
  targetLeft :
    (selectedSegmentLogicalTapeDecoderTargetTape
        target encodedPrefix).left =
      none ::
        List.append
          (statefulOptionCellsFrom selectedSegmentLogicalTapeDecoderNext
            selectedSegmentLogicalTapeDecoderEmit
            selectedSegmentLogicalTapeDecoderStart
            (logicalTapeBits (guardLogicalTape target))).reverse
          (none :: encodedPrefix.reverse)
  targetHead :
    (selectedSegmentLogicalTapeDecoderTargetTape
        target encodedPrefix).head = none
  targetRight :
    (selectedSegmentLogicalTapeDecoderTargetTape
        target encodedPrefix).right = []
  targetCells :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTargetTape
          target encodedPrefix) =
      List.append encodedPrefix
        (none ::
          List.append
            (statefulOptionCellsFrom selectedSegmentLogicalTapeDecoderNext
              selectedSegmentLogicalTapeDecoderEmit
              selectedSegmentLogicalTapeDecoderStart
              (logicalTapeBits (guardLogicalTape target)))
            [none, none])
  normalizedOutput :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderTargetTape
          target encodedPrefix) =
      List.append (encodedPrefix.filterMap (fun cell => cell))
        (Tape.normalizedOutput target)
  outputGuardLogicalTapeBits :
    statefulOptionOutputFrom selectedSegmentLogicalTapeDecoderNext
        selectedSegmentLogicalTapeDecoderEmit 0
        (logicalTapeBits (guardLogicalTape target)) =
      Tape.normalizedOutput target
  cellsGuardLogicalTapeBits :
    statefulOptionCellsFrom selectedSegmentLogicalTapeDecoderNext
        selectedSegmentLogicalTapeDecoderEmit 0
        (logicalTapeBits (guardLogicalTape target)) =
      List.append
        (((guardLogicalTape target).left.reverse.map
          selectedSegmentLogicalTapeDecoderCellCells).flatten)
        (List.append [none, none]
          (List.append
            (selectedSegmentLogicalTapeDecoderCellCells
              (guardLogicalTape target).head)
            (((guardLogicalTape target).right.map
              selectedSegmentLogicalTapeDecoderCellCells).flatten)))

theorem selectedSegmentLogicalTapeDecoderEndpointShape
    (target : Tape Bool)
    (encodedPrefix : List (Option Bool)) :
    SelectedSegmentLogicalTapeDecoderEndpointShape
      target encodedPrefix :=
  { decoderReady :=
      selectedSegmentLogicalTapeDecoderDescription_subroutineReady
    haltsFromSelectedPayload :=
      selectedSegmentLogicalTapeDecoderDescription_haltsFrom_selectedSingletonPayload
        target encodedPrefix
    targetLeft :=
      selectedSegmentLogicalTapeDecoderTargetTape_left
        target encodedPrefix
    targetHead :=
      selectedSegmentLogicalTapeDecoderTargetTape_head
        target encodedPrefix
    targetRight :=
      selectedSegmentLogicalTapeDecoderTargetTape_right
        target encodedPrefix
    targetCells :=
      selectedSegmentLogicalTapeDecoderTargetTape_cells
        target encodedPrefix
    normalizedOutput :=
      selectedSegmentLogicalTapeDecoderTargetTape_normalizedOutput
        target encodedPrefix
    outputGuardLogicalTapeBits :=
      selectedSegmentLogicalTapeDecoder_output_guardLogicalTapeBits_zero
        target
    cellsGuardLogicalTapeBits :=
      selectedSegmentLogicalTapeDecoder_cells_logicalTapeBits_zero
        (guardLogicalTape target) }

theorem selectedSegmentLogicalTapeDecoder_endpoint_halts
    (target : Tape Bool)
    (encodedPrefix : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDescription.HaltsFromTape
      (Tape.move Direction.right
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells [guardLogicalTape target])))
      (selectedSegmentLogicalTapeDecoderTargetTape
        target encodedPrefix) :=
  (selectedSegmentLogicalTapeDecoderEndpointShape
    target encodedPrefix).haltsFromSelectedPayload

theorem selectedSegmentLogicalTapeDecoder_endpoint_normalizedOutput
    (target : Tape Bool)
    (encodedPrefix : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderTargetTape
          target encodedPrefix) =
      List.append (encodedPrefix.filterMap (fun cell => cell))
        (Tape.normalizedOutput target) :=
  (selectedSegmentLogicalTapeDecoderEndpointShape
    target encodedPrefix).normalizedOutput

/-!
## Selected-segment decoder routes
-/

structure SelectedSingletonDecoderRouteSpec
    (decoder : MachineDescription) : Prop where
  spec :
    StructuredSelectedSingletonSegmentDecoderSpec decoder
  subroutineReady :
    decoder.SubroutineReady
  halts :
    forall (target : Tape Bool)
      (encodedPrefix : List (Option Bool)),
      decoder.HaltsFromTapeEquiv
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells [guardLogicalTape target]))
        target

def SelectedSingletonDecoderRouteConstruction : Prop :=
  exists decoder : MachineDescription,
    SelectedSingletonDecoderRouteSpec decoder

theorem selectedSingletonDecoderRouteSpec_of_spec
    {decoder : MachineDescription}
    (hdecoder :
      StructuredSelectedSingletonSegmentDecoderSpec decoder) :
    SelectedSingletonDecoderRouteSpec decoder :=
  { spec := hdecoder
    subroutineReady := hdecoder.left
    halts := hdecoder.right }

theorem selectedSingletonDecoderConstruction_of_routeConstruction
    (hroute :
      SelectedSingletonDecoderRouteConstruction) :
    StructuredSelectedSingletonSegmentDecoderConstruction := by
  rcases hroute with ⟨decoder, hdecoder⟩
  exact ⟨decoder, hdecoder.spec⟩

theorem selectedSingletonDecoderRouteConstruction_of_construction
    (hdecoder :
      StructuredSelectedSingletonSegmentDecoderConstruction) :
    SelectedSingletonDecoderRouteConstruction := by
  rcases hdecoder with ⟨decoder, hspec⟩
  exact
    ⟨decoder,
      selectedSingletonDecoderRouteSpec_of_spec hspec⟩

structure SelectedHeadDecoderRouteSpec
    (decoder : MachineDescription) : Prop where
  spec :
    StructuredSelectedHeadSegmentDecoderSpec decoder
  subroutineReady :
    decoder.SubroutineReady
  halts :
    forall (target : Tape Bool) (rest : List (Tape Bool))
      (encodedPrefix : List (Option Bool)),
      decoder.HaltsFromTapeEquiv
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells (guardLogicalTape target :: rest)))
        target

def SelectedHeadDecoderRouteConstruction : Prop :=
  exists decoder : MachineDescription,
    SelectedHeadDecoderRouteSpec decoder

theorem selectedHeadDecoderRouteSpec_of_spec
    {decoder : MachineDescription}
    (hdecoder :
      StructuredSelectedHeadSegmentDecoderSpec decoder) :
    SelectedHeadDecoderRouteSpec decoder :=
  { spec := hdecoder
    subroutineReady := hdecoder.left
    halts := hdecoder.right }

theorem selectedHeadDecoderConstruction_of_routeConstruction
    (hroute :
      SelectedHeadDecoderRouteConstruction) :
    StructuredSelectedHeadSegmentDecoderConstruction := by
  rcases hroute with ⟨decoder, hdecoder⟩
  exact ⟨decoder, hdecoder.spec⟩

theorem selectedHeadDecoderRouteConstruction_of_construction
    (hdecoder :
      StructuredSelectedHeadSegmentDecoderConstruction) :
    SelectedHeadDecoderRouteConstruction := by
  rcases hdecoder with ⟨decoder, hspec⟩
  exact
    ⟨decoder,
      selectedHeadDecoderRouteSpec_of_spec hspec⟩

theorem selectedSingletonDecoderRouteConstruction_of_headDecoderRoute
    (hroute :
      SelectedHeadDecoderRouteConstruction) :
    SelectedSingletonDecoderRouteConstruction :=
  selectedSingletonDecoderRouteConstruction_of_construction
    (structuredSelectedSingletonSegmentDecoderConstruction_of_headDecoder
      (selectedHeadDecoderConstruction_of_routeConstruction hroute))

theorem tape0SegmentNormalizerRouteConstruction_of_headDecoderRoute
    (hroute :
      SelectedHeadDecoderRouteConstruction) :
    Tape0SegmentNormalizerRouteConstruction :=
  tape0SegmentNormalizerRouteConstruction_of_construction
    (structuredTape0SegmentNormalizerConstruction_of_selectedHeadDecoder
      (selectedHeadDecoderConstruction_of_routeConstruction hroute))

theorem tape1SegmentNormalizerRouteConstruction_of_headDecoderRoute
    (hroute :
      SelectedHeadDecoderRouteConstruction) :
    Tape1SegmentNormalizerRouteConstruction :=
  tape1SegmentNormalizerRouteConstruction_of_construction
    (structuredTape1SegmentNormalizerConstruction_of_selectedHeadDecoder
      (selectedHeadDecoderConstruction_of_routeConstruction hroute))

theorem tape2SegmentNormalizerRouteConstruction_of_headDecoderRoute
    (hroute :
      SelectedHeadDecoderRouteConstruction) :
    Tape2SegmentNormalizerRouteConstruction :=
  tape2SegmentNormalizerRouteConstruction_of_construction
    (structuredTape2SegmentNormalizerConstruction_of_selectedHeadDecoder
      (selectedHeadDecoderConstruction_of_routeConstruction hroute))

/-!
## Cleanup and extractor routes
-/

structure SelectedSegmentCleanupRouteSpec
    (cleanup : MachineDescription) : Prop where
  spec :
    SelectedSegmentLogicalTapeDecoderCleanupSpec cleanup
  subroutineReady :
    cleanup.SubroutineReady
  halts :
    forall (target : Tape Bool)
      (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTargetTape
          target encodedPrefix)
        target

def SelectedSegmentCleanupRouteConstruction : Prop :=
  exists cleanup : MachineDescription,
    SelectedSegmentCleanupRouteSpec cleanup

theorem selectedSegmentCleanupRouteSpec_of_spec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderCleanupSpec cleanup) :
    SelectedSegmentCleanupRouteSpec cleanup :=
  { spec := hcleanup
    subroutineReady := hcleanup.left
    halts := hcleanup.right }

theorem selectedSegmentCleanupRouteConstruction_of_construction
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderCleanupConstruction) :
    SelectedSegmentCleanupRouteConstruction := by
  rcases hcleanup with ⟨cleanup, hspec⟩
  exact
    ⟨cleanup,
      selectedSegmentCleanupRouteSpec_of_spec hspec⟩

theorem selectedSegmentCleanupConstruction_of_routeConstruction
    (hroute :
      SelectedSegmentCleanupRouteConstruction) :
    SelectedSegmentLogicalTapeDecoderCleanupConstruction := by
  rcases hroute with ⟨cleanup, hcleanup⟩
  exact ⟨cleanup, hcleanup.spec⟩

theorem selectedSingletonDecoderRouteConstruction_of_cleanupRoute
    (hroute :
      SelectedSegmentCleanupRouteConstruction) :
    SelectedSingletonDecoderRouteConstruction :=
  selectedSingletonDecoderRouteConstruction_of_construction
    (structuredSelectedSingletonSegmentDecoderConstruction_of_cleanup
      (selectedSegmentCleanupConstruction_of_routeConstruction hroute))

structure SelectedSingletonExtractorRouteSpec
    (extractor : MachineDescription) : Prop where
  spec :
    StructuredSelectedSingletonSegmentExtractorSpec extractor
  decoderSpec :
    StructuredSelectedSingletonSegmentDecoderSpec extractor
  subroutineReady :
    extractor.SubroutineReady
  halts :
    forall (target : Tape Bool)
      (encodedPrefix : List (Option Bool)),
      extractor.HaltsFromTapeEquiv
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells [guardLogicalTape target]))
        target

def SelectedSingletonExtractorRouteConstruction : Prop :=
  exists extractor : MachineDescription,
    SelectedSingletonExtractorRouteSpec extractor

theorem selectedSingletonExtractorRouteSpec_of_spec
    {extractor : MachineDescription}
    (hextractor :
      StructuredSelectedSingletonSegmentExtractorSpec extractor) :
    SelectedSingletonExtractorRouteSpec extractor :=
  { spec := hextractor
    decoderSpec := hextractor
    subroutineReady := hextractor.left
    halts := hextractor.right }

theorem selectedSingletonExtractorRouteConstruction_of_construction
    (hextractor :
      StructuredSelectedSingletonSegmentExtractorConstruction) :
    SelectedSingletonExtractorRouteConstruction := by
  rcases hextractor with ⟨extractor, hspec⟩
  exact
    ⟨extractor,
      selectedSingletonExtractorRouteSpec_of_spec hspec⟩

theorem selectedSingletonExtractorConstruction_of_routeConstruction
    (hroute :
      SelectedSingletonExtractorRouteConstruction) :
    StructuredSelectedSingletonSegmentExtractorConstruction := by
  rcases hroute with ⟨extractor, hextractor⟩
  exact ⟨extractor, hextractor.spec⟩

theorem selectedSingletonExtractorRouteConstruction_of_decoderRoute
    (hroute :
      SelectedSingletonDecoderRouteConstruction) :
    SelectedSingletonExtractorRouteConstruction :=
  selectedSingletonExtractorRouteConstruction_of_construction
    (structuredSelectedSingletonSegmentExtractorConstruction_of_decoder
      (selectedSingletonDecoderConstruction_of_routeConstruction hroute))

theorem tape2SegmentNormalizerRouteConstruction_of_singletonExtractorRoute
    (hroute :
      SelectedSingletonExtractorRouteConstruction) :
    Tape2SegmentNormalizerRouteConstruction :=
  tape2SegmentNormalizerRouteConstruction_of_construction
    (structuredTape2SegmentNormalizerConstruction_of_selectedSingletonExtractor
      (selectedSingletonExtractorConstruction_of_routeConstruction hroute))

/-!
## Combined route bundles
-/

structure SelectedHeadProjectionComponentRoute : Prop where
  headDecoder :
    SelectedHeadDecoderRouteConstruction
  singletonDecoder :
    SelectedSingletonDecoderRouteConstruction
  tape0Normalizer :
    Tape0SegmentNormalizerRouteConstruction
  tape1Normalizer :
    Tape1SegmentNormalizerRouteConstruction
  tape2Normalizer :
    Tape2SegmentNormalizerRouteConstruction
  tape0Projector :
    Tape0ProjectorRouteConstruction
  tape1Projector :
    Tape1ProjectorRouteConstruction
  tape2Projector :
    Tape2ProjectorRouteConstruction

def SelectedHeadProjectionComponentRouteConstruction : Prop :=
  SelectedHeadProjectionComponentRoute

theorem selectedHeadProjectionComponentRoute_of_headDecoder
    (hroute :
      SelectedHeadDecoderRouteConstruction) :
    SelectedHeadProjectionComponentRoute :=
  { headDecoder := hroute
    singletonDecoder :=
      selectedSingletonDecoderRouteConstruction_of_headDecoderRoute
        hroute
    tape0Normalizer :=
      tape0SegmentNormalizerRouteConstruction_of_headDecoderRoute
        hroute
    tape1Normalizer :=
      tape1SegmentNormalizerRouteConstruction_of_headDecoderRoute
        hroute
    tape2Normalizer :=
      tape2SegmentNormalizerRouteConstruction_of_headDecoderRoute
        hroute
    tape0Projector :=
      tape0ProjectorRouteConstruction_of_segmentNormalizerRoute
        (tape0SegmentNormalizerRouteConstruction_of_headDecoderRoute
          hroute)
    tape1Projector :=
      tape1ProjectorRouteConstruction_of_segmentNormalizerRoute
        (tape1SegmentNormalizerRouteConstruction_of_headDecoderRoute
          hroute)
    tape2Projector :=
      tape2ProjectorRouteConstruction_of_segmentNormalizerRoute
        (tape2SegmentNormalizerRouteConstruction_of_headDecoderRoute
          hroute) }

structure SelectedCleanupProjectionComponentRoute : Prop where
  cleanup :
    SelectedSegmentCleanupRouteConstruction
  singletonDecoder :
    SelectedSingletonDecoderRouteConstruction
  singletonExtractor :
    SelectedSingletonExtractorRouteConstruction
  tape2Normalizer :
    Tape2SegmentNormalizerRouteConstruction
  tape2Projector :
    Tape2ProjectorRouteConstruction

def SelectedCleanupProjectionComponentRouteConstruction : Prop :=
  SelectedCleanupProjectionComponentRoute

theorem selectedCleanupProjectionComponentRoute_of_cleanup
    (hroute :
      SelectedSegmentCleanupRouteConstruction) :
    SelectedCleanupProjectionComponentRoute :=
  { cleanup := hroute
    singletonDecoder :=
      selectedSingletonDecoderRouteConstruction_of_cleanupRoute
        hroute
    singletonExtractor :=
      selectedSingletonExtractorRouteConstruction_of_decoderRoute
        (selectedSingletonDecoderRouteConstruction_of_cleanupRoute
          hroute)
    tape2Normalizer :=
      tape2SegmentNormalizerRouteConstruction_of_singletonExtractorRoute
        (selectedSingletonExtractorRouteConstruction_of_decoderRoute
          (selectedSingletonDecoderRouteConstruction_of_cleanupRoute
            hroute))
    tape2Projector :=
      tape2ProjectorRouteConstruction_of_segmentNormalizerRoute
        (tape2SegmentNormalizerRouteConstruction_of_singletonExtractorRoute
          (selectedSingletonExtractorRouteConstruction_of_decoderRoute
            (selectedSingletonDecoderRouteConstruction_of_cleanupRoute
              hroute))) }

end ProjectionRouteContracts

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
