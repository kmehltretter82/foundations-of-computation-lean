import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredInputMaterializer
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

theorem selectedSegmentLogicalTapeDecoderRawHeadStructuredInputTargetFamilyConstruction_core :
    Structured3InputTargetFamilyConstruction
      selectedSegmentLogicalTapeDecoderRawHeadIngressMaterializerSource
      selectedSegmentLogicalTapeDecoderRawHeadIngressMaterializerTarget := by
  -- Remaining concrete ingress materializer obligation for the raw selected
  -- head route.  It targets the exact raw-head structured input tape; the
  -- canonical structured-input materializer contract is derived below.
  sorry

theorem selectedSegmentLogicalTapeDecoderRawHeadStructuredInputMaterializerConstruction_core :
    Structured3InputMaterializerConstruction
      selectedSegmentLogicalTapeDecoderRawHeadIngressMaterializerSource
      selectedSegmentLogicalTapeDecoderRawHeadIngressMaterializerOutput :=
  structured3InputMaterializerConstruction_of_targetFamilyConstruction
    selectedSegmentLogicalTapeDecoderRawHeadStructuredInputTargetFamilyConstruction_core
    selectedSegmentLogicalTapeDecoderRawHeadIngressMaterializerTarget_eq

theorem selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitConstruction_core :
    SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitConstruction := by
  -- Remaining finite-table obligation for representative cleanup after the
  -- generated scanner.  The nil/nonempty branches target the canonical padded
  -- representative, not an arbitrary public target literally.
  sorry

theorem selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupHandoffSplitConstruction_core :
    SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupHandoffSplitConstruction :=
  selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupHandoffSplitConstruction_of_forwardSplit
    selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitConstruction_core

theorem selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupConstruction_core :
    SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupConstruction :=
  selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupConstruction_of_forwardSplit
    selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitConstruction_core

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupConstruction_core :
    SelectedSegmentLogicalTapeDecoderPaddedCleanupConstruction :=
  selectedSegmentLogicalTapeDecoderPaddedCleanupConstruction_of_representative
    selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupConstruction_core

theorem selectedSegmentLogicalTapeDecoderHeadCleanupConstruction_core :
    SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction :=
  selectedSegmentLogicalTapeDecoderHeadCleanupConstruction_of_representative
    selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupConstruction_core

theorem structuredSelectedHeadDecoderRouteConstruction_core :
    StructuredSelectedHeadDecoderRouteConstruction :=
  structuredSelectedHeadDecoderRouteConstruction_of_representativeCleanup
    selectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupConstruction_core

theorem structuredTape2ProjectorStandaloneConstruction_core :
    StructuredTape2ProjectorConstruction :=
  selectedHeadRoute_tape2Projector
    structuredSelectedHeadDecoderRouteConstruction_core

theorem selectedSegmentLogicalTapeDecoderRawHeadIngressBridgeConstruction_core :
    SelectedSegmentLogicalTapeDecoderRawHeadIngressBridgeConstruction := by
  exact
    selectedSegmentLogicalTapeDecoderRawHeadIngressBridgeConstruction_of_targetFamilyConstruction
      selectedSegmentLogicalTapeDecoderRawHeadStructuredInputTargetFamilyConstruction_core

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
  selectedHeadRoute_headDecoder
    structuredSelectedHeadDecoderRouteConstruction_core

theorem structuredTape2SegmentNormalizerConstruction_core :
    StructuredTape2SegmentNormalizerConstruction :=
  selectedHeadRoute_tape2SegmentNormalizer
    structuredSelectedHeadDecoderRouteConstruction_core

theorem structuredTape2ProjectorConstruction_core :
    StructuredTape2ProjectorConstruction :=
  selectedHeadRoute_tape2Projector
    structuredSelectedHeadDecoderRouteConstruction_core

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
