import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredInputMaterializer
import FoC.Computability.Compiler.Structured.HeadRoutes
import FoC.Computability.Compiler.Structured.HeadRoutes.Tape2Projector.EndpointFrontier

set_option doc.verso true

/-!
# Structured selected-head endpoint constructions

This module contains the concrete endpoint-construction leaves for the raw
marker-preserving three-tape route.  The lossy post-scanner cleanup frontier is
retired: {module}`FoC.Computability.Compiler.Structured.HeadRoutes.ContractGuardrails`
proves that it cannot recover arbitrary logical tapes.  The live tape-2
projector therefore starts from the canonical guarded three-tape encoding.
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

theorem selectedSegmentLogicalTapeDecoderRawHeadIngressBridgeConstruction_core :
    SelectedSegmentLogicalTapeDecoderRawHeadIngressBridgeConstruction := by
  exact
    selectedSegmentLogicalTapeDecoderRawHeadIngressBridgeConstruction_of_targetFamilyConstruction
      selectedSegmentLogicalTapeDecoderRawHeadStructuredInputTargetFamilyConstruction_core

theorem selectedSegmentLogicalTapeDecoderRawHeadThreeTapeNormalizerConstruction_core :
    SelectedSegmentLogicalTapeDecoderRawHeadThreeTapeNormalizerConstruction := by
  exact SelectedSegmentLogicalTapeDecoderRawHeadNormalizer.construction

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
