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

theorem selectedSegmentLogicalTapeDecoderRawHeadIngressBridgeConstruction_core :
    SelectedSegmentLogicalTapeDecoderRawHeadIngressBridgeConstruction := by
  -- Materialize the raw selected-head endpoint as tape 0 of the structured
  -- three-tape decoder input before the FST scanner erases head-marker bits.
  sorry

theorem selectedSegmentLogicalTapeDecoderRawHeadEgressBridgeConstruction_core :
    SelectedSegmentLogicalTapeDecoderRawHeadEgressBridgeConstruction := by
  -- Project tape 2 from the structured raw-head output back to the target
  -- one-tape endpoint.
  sorry

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
    StructuredSelectedHeadSegmentDecoderConstruction := by
  exact
    structuredSelectedHeadSegmentDecoderConstruction_of_rawHeadThreeTapeBridgeConstruction
      selectedSegmentLogicalTapeDecoderRawHeadThreeTapeBridgeConstruction_core

theorem structuredTape2SegmentNormalizerConstruction_core :
    StructuredTape2SegmentNormalizerConstruction :=
  structuredTape2SegmentNormalizerConstruction_of_selectedHeadDecoder
    structuredSelectedHeadSegmentDecoderConstruction_core

theorem structuredTape2ProjectorConstruction_core :
    StructuredTape2ProjectorConstruction :=
  structuredTape2ProjectorConstruction_of_segmentNormalizerConstruction
    structuredTape2SegmentNormalizerConstruction_core

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
