import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.ProjectionHeadRoutes

set_option doc.verso true

/-!
# Structured selected-head endpoint constructions

This module contains the concrete endpoint-construction leaves for the raw
selected-head three-tape route.  The route contracts and reusable adapters live
in {module}`FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.ProjectionHeadRoutes`;
the remaining endpoint bridge obligations are kept near the top here so they
are easy to find and work on independently.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

theorem selectedSegmentLogicalTapeDecoderRawHeadStructuredInputMaterializerConstruction_core :
    Structured3InputMaterializerConstruction
      selectedSegmentLogicalTapeDecoderRawHeadIngressMaterializerSource
      selectedSegmentLogicalTapeDecoderRawHeadIngressMaterializerOutput := by
  -- Generic endpoint materializer: wrap the current one-tape source as tape 0
  -- of a guarded three-tape encoding, with blank scratch/output tapes.
  sorry

theorem selectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitConstruction_core :
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitConstruction := by
  -- Remaining finite-table obligation for exact padded cleanup after the
  -- generated scanner.  The selected-head cleanup/projector route specializes
  -- this to the padding produced by the encoded structured suffix.
  sorry

theorem selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction_core :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction :=
  selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction_of_paddedExactCleanupForwardSplit
    selectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitConstruction_core

theorem selectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction_core :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction :=
  selectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction_of_forwardSplit
    selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction_core

theorem structuredSelectedHeadExactDecoderRouteConstruction_core :
    StructuredSelectedHeadExactDecoderRouteConstruction :=
  structuredSelectedHeadExactDecoderRouteConstruction_of_forwardSplit
    selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction_core

theorem structuredSelectedHeadSegmentDecoderExactConstruction_core :
    StructuredSelectedHeadSegmentDecoderExactConstruction :=
  structuredSelectedHeadExactDecoderRouteConstruction_core.exactHeadDecoder

theorem structuredTape2ExactProjectorConstruction_core :
    StructuredTape2ExactProjectorConstruction :=
  structuredSelectedHeadExactDecoderRouteConstruction_core.exactTape2Projector

theorem structuredTape2ProjectorStandaloneConstruction_from_exactCleanup_core :
    StructuredTape2ProjectorConstruction :=
  structuredSelectedHeadExactDecoderRouteConstruction_core.tape2Projector

theorem structuredTape2ProjectorStandaloneConstruction_core :
    StructuredTape2ProjectorConstruction :=
  structuredTape2ProjectorStandaloneConstruction_from_exactCleanup_core

theorem selectedSegmentLogicalTapeDecoderRawHeadIngressBridgeConstruction_core :
    SelectedSegmentLogicalTapeDecoderRawHeadIngressBridgeConstruction := by
  exact
    selectedSegmentLogicalTapeDecoderRawHeadIngressBridgeConstruction_of_structured3InputMaterializerConstruction
      selectedSegmentLogicalTapeDecoderRawHeadStructuredInputMaterializerConstruction_core

theorem selectedSegmentLogicalTapeDecoderRawHeadEgressBridgeConstruction_core :
    SelectedSegmentLogicalTapeDecoderRawHeadEgressBridgeConstruction := by
  exact
    selectedSegmentLogicalTapeDecoderRawHeadEgressBridgeConstruction_of_tape2ProjectorConstruction
      structuredTape2ProjectorStandaloneConstruction_core

theorem selectedSegmentLogicalTapeDecoderRawHeadThreeTapeNormalizerConstruction_core :
    SelectedSegmentLogicalTapeDecoderRawHeadThreeTapeNormalizerConstruction := by
  exact SelectedSegmentLogicalTapeDecoderRawHeadNormalizer.construction

theorem selectedSegmentLogicalTapeDecoderRawHeadThreeTapeBridgeConstruction_core :
    SelectedSegmentLogicalTapeDecoderRawHeadThreeTapeBridgeConstruction := by
  rcases
      selectedSegmentLogicalTapeDecoderRawHeadIngressBridgeConstruction_core with
    ⟨ingress, hingress⟩
  rcases
      selectedSegmentLogicalTapeDecoderRawHeadThreeTapeNormalizerConstruction_core with
    ⟨normalizer, hnormalizer⟩
  rcases
      selectedSegmentLogicalTapeDecoderRawHeadEgressBridgeConstruction_core with
    ⟨egress, hegress⟩
  exact ⟨ingress, normalizer, egress, hingress, hnormalizer, hegress⟩

theorem structuredSelectedHeadSegmentDecoderConstruction_core :
    StructuredSelectedHeadSegmentDecoderConstruction :=
  structuredSelectedHeadExactDecoderRouteConstruction_core.headDecoder

theorem structuredTape2SegmentNormalizerConstruction_core :
    StructuredTape2SegmentNormalizerConstruction :=
  structuredTape2SegmentNormalizerConstruction_of_exact
    (structuredTape2ExactSegmentNormalizerConstruction_of_exactHeadDecoder
      structuredSelectedHeadSegmentDecoderExactConstruction_core)

theorem structuredTape2ProjectorConstruction_core :
    StructuredTape2ProjectorConstruction :=
  structuredTape2ProjectorStandaloneConstruction_from_exactCleanup_core

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
