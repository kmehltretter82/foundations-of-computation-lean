import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchExtOutput
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.Mat.Contracts
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.Mat.OutputRoutes
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.Routes.SelectedDecoder

set_option doc.verso true

/-!
# Threaded count-window bridge route contracts

This module packages the threaded count-window bridge as route-level exact and
normalized-output construction bundles.  The underlying finite leaves remain
the structured input materializer, the structured-prefix eraser, and the
selected-footprint compactor; this file records how the already-named route
packages feed the lowered extractor, output projector, scan-source
materializer, scratch-count materializer, scratch extender, and post-padding
scratch allocator.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

namespace CountWindowThreadedBridgeRouteContracts

/-!
## Exact threaded route
-/

structure ExactRouteConstruction : Prop where
  materializerRoute :
    CountWindowPostFieldDecodedPrefixStructuredMaterializerRouteContracts.ExactRouteConstruction
  selectedDecoderRoute :
    CountWindowSelectedDecoderRouteContracts.StructuredPrefixDensifierComponentConstruction
  inputInitializer :
    CountWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction
  loweredExtractor :
    LoweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction
  segmentNormalizer :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction
  outputProjector :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction
  scanSourceMaterializer :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction
  scratchCountWindowMaterializer :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction
  scratchCountWindowRestorer :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRestorerConstruction
  scratchCountWindowMaterializerAndRestorer :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction
  postPaddingScratchCountExtender :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction
  scratchExt :
    SelectedProjectionPaddedTailCleanupScratchExtConstruction
  postPaddingScratchAllocator :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction

theorem exactRouteConstruction_of_routes
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredMaterializerRouteContracts.ExactRouteConstruction)
    (hdecoder :
      CountWindowSelectedDecoderRouteContracts.StructuredPrefixDensifierComponentConstruction)
    (hextractor :
      LoweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction) :
    ExactRouteConstruction := by
  let hinitializer :
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction :=
    CountWindowPostFieldDecodedPrefixStructuredMaterializerRouteContracts.inputInitializerConstruction_of_exactRouteConstruction
      hmaterializer
  let hsegment :
      CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction :=
    CountWindowSelectedDecoderRouteContracts.segmentNormalizerConstruction_of_componentRoute
      hdecoder
  let hprojector :
      CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction :=
    countWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction_of_countWindowSegmentNormalizer
      hsegment
  let hscan :
      CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction :=
    countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_of_structuredParts
      hinitializer hextractor hprojector
  let hwindow :
      SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction :=
    selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction_of_scanSourceMaterializer
      hscan
  let hrestorer :
      SelectedProjectionPaddedTailCleanupScratchCountWindowRestorerConstruction :=
    selectedProjectionPaddedTailCleanupScratchCountWindowRestorerConstruction_core
  let hwindowBoth :
      SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction :=
    selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction_of_parts
      hwindow hrestorer
  let hcountExtender :
      SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction :=
    selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction_of_countWindowMaterializers
      hwindowBoth
  let hscratchExt :
      SelectedProjectionPaddedTailCleanupScratchExtConstruction :=
    selectedProjectionPaddedTailCleanupScratchExtConstruction_of_countExtenders
      hcountExtender
  let hallocator :
      SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction :=
    selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction_of_extenders
      hscratchExt
  exact
    { materializerRoute := hmaterializer
      selectedDecoderRoute := hdecoder
      inputInitializer := hinitializer
      loweredExtractor := hextractor
      segmentNormalizer := hsegment
      outputProjector := hprojector
      scanSourceMaterializer := hscan
      scratchCountWindowMaterializer := hwindow
      scratchCountWindowRestorer := hrestorer
      scratchCountWindowMaterializerAndRestorer := hwindowBoth
      postPaddingScratchCountExtender := hcountExtender
      scratchExt := hscratchExt
      postPaddingScratchAllocator := hallocator }

theorem exactRouteConstruction_core :
    ExactRouteConstruction :=
  exactRouteConstruction_of_routes
    CountWindowPostFieldDecodedPrefixStructuredMaterializerRouteContracts.exactRouteConstruction_core
    CountWindowSelectedDecoderRouteContracts.structuredPrefixDensifierComponentConstruction_core
    loweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction_core

theorem inputInitializerConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction :=
  exactRouteConstruction_core.inputInitializer

theorem segmentNormalizerConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction :=
  exactRouteConstruction_core.segmentNormalizer

theorem outputProjectorConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction :=
  exactRouteConstruction_core.outputProjector

theorem scanSourceMaterializerConstruction_core :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction :=
  exactRouteConstruction_core.scanSourceMaterializer

theorem scratchCountWindowMaterializerConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction :=
  exactRouteConstruction_core.scratchCountWindowMaterializer

theorem scratchCountWindowMaterializerAndRestorerConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction :=
  exactRouteConstruction_core.scratchCountWindowMaterializerAndRestorer

theorem postPaddingScratchCountExtenderConstruction_core :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction :=
  exactRouteConstruction_core.postPaddingScratchCountExtender

theorem scratchExtConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchExtConstruction :=
  exactRouteConstruction_core.scratchExt

theorem postPaddingScratchAllocatorConstruction_core :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction :=
  exactRouteConstruction_core.postPaddingScratchAllocator

/-!
## Output threaded route
-/

structure OutputRouteConstruction : Prop where
  exactRoute : ExactRouteConstruction
  materializerOutputRoute :
    CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts.OutputRouteConstruction
  materializerOutputBranches :
    CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts.OutputRouteBranchConstruction
  materializerAcceptOutputRoute :
    CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts.AcceptOutputRouteConstruction
  materializerRejectOutputRoute :
    CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts.RejectOutputRouteConstruction
  selectedDecoderOutputRoute :
    CountWindowSelectedDecoderRouteContracts.StructuredPrefixOutputComponentConstruction
  inputInitializerOutput :
    CountWindowPostFieldDecodedPrefixStructuredInputInitializerOutputConstruction
  segmentNormalizerOutput :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerOutputConstruction
  outputProjectorOutput :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorOutputConstruction
  scanSourceMaterializerOutput :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerOutputConstruction
  rejectScanSourceOutput :
    RejectPostFieldDecodedPrefixScanSourceOutputConstruction
  acceptScanSourceOutput :
    AcceptPostFieldRewoundToDecodedPrefixScanSourceOutputConstruction
  scratchCountWindowMaterializerOutput :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerOutputConstruction
  scratchCountWindowRestorerOutput :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRestorerOutputConstruction
  scratchCountWindowMaterializerAndRestorerOutput :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerOutputConstruction
  postPaddingScratchCountExtenderOutput :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderOutputConstruction
  scratchExtOutput :
    SelectedProjectionPaddedTailCleanupScratchExtOutputConstruction
  postPaddingScratchAllocatorOutput :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputConstruction

theorem outputRouteConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    OutputRouteConstruction := by
  let hmaterializerOutputRoute :
      CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts.OutputRouteConstruction :=
    CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts.outputRouteConstruction_of_exactRouteConstruction
      hroute.materializerRoute
  let hmaterializerOutputBranches :
      CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts.OutputRouteBranchConstruction :=
    CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts.outputRouteBranchConstruction_of_outputRouteConstruction
      hmaterializerOutputRoute
  let hmaterializerAcceptOutputRoute :
      CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts.AcceptOutputRouteConstruction :=
    CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts.acceptOutputRouteConstruction_of_outputRouteConstruction
      hmaterializerOutputRoute
  let hmaterializerRejectOutputRoute :
      CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts.RejectOutputRouteConstruction :=
    CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts.rejectOutputRouteConstruction_of_outputRouteConstruction
      hmaterializerOutputRoute
  let hdecoderOutputRoute :
      CountWindowSelectedDecoderRouteContracts.StructuredPrefixOutputComponentConstruction :=
    CountWindowSelectedDecoderRouteContracts.structuredPrefixOutputComponentConstruction_of_exactComponent
      hroute.selectedDecoderRoute
  let hinitializerOutput :
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerOutputConstruction :=
    CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts.initializerOutputConstruction_of_outputRouteConstruction
      hmaterializerOutputRoute
  let hsegmentOutput :
      CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerOutputConstruction :=
    countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerOutputConstruction_of_exact
      hroute.segmentNormalizer
  let hprojectorOutput :
      CountWindowPostFieldDecodedPrefixStructuredOutputProjectorOutputConstruction :=
    countWindowPostFieldDecodedPrefixStructuredOutputProjectorOutputConstruction_of_exact
      hroute.outputProjector
  let hscanOutput :
      CountWindowPostFieldDecodedPrefixScanSourceMaterializerOutputConstruction :=
    countWindowPostFieldDecodedPrefixScanSourceMaterializerOutputConstruction_of_exact
      hroute.scanSourceMaterializer
  let hrejectOutput :
      RejectPostFieldDecodedPrefixScanSourceOutputConstruction :=
    rejectPostFieldDecodedPrefixScanSourceOutputConstruction_of_countWindowMaterializerOutput
      hscanOutput
  let hacceptOutput :
      AcceptPostFieldRewoundToDecodedPrefixScanSourceOutputConstruction :=
    acceptPostFieldRewoundToDecodedPrefixScanSourceOutputConstruction_of_countWindowMaterializerOutput
      hscanOutput
  let hwindowOutput :
      SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerOutputConstruction :=
    selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerOutputConstruction_of_exact
      hroute.scratchCountWindowMaterializer
  let hrestorerOutput :
      SelectedProjectionPaddedTailCleanupScratchCountWindowRestorerOutputConstruction :=
    selectedProjectionPaddedTailCleanupScratchCountWindowRestorerOutputConstruction_of_exact
      hroute.scratchCountWindowRestorer
  let hwindowBothOutput :
      SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerOutputConstruction :=
    selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerOutputConstruction_of_exact
      hroute.scratchCountWindowMaterializerAndRestorer
  let hcountExtenderOutput :
      SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderOutputConstruction :=
    selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderOutputConstruction_of_exact
      hroute.postPaddingScratchCountExtender
  let hscratchExtOutput :
      SelectedProjectionPaddedTailCleanupScratchExtOutputConstruction :=
    selectedProjectionPaddedTailCleanupScratchExtOutputConstruction_of_countExtendersOutput
      hcountExtenderOutput
  let hallocatorOutput :
      SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputConstruction :=
    selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputConstruction_of_extendersOutput
      hscratchExtOutput
  exact
    { exactRoute := hroute
      materializerOutputRoute := hmaterializerOutputRoute
      materializerOutputBranches := hmaterializerOutputBranches
      materializerAcceptOutputRoute := hmaterializerAcceptOutputRoute
      materializerRejectOutputRoute := hmaterializerRejectOutputRoute
      selectedDecoderOutputRoute := hdecoderOutputRoute
      inputInitializerOutput := hinitializerOutput
      segmentNormalizerOutput := hsegmentOutput
      outputProjectorOutput := hprojectorOutput
      scanSourceMaterializerOutput := hscanOutput
      rejectScanSourceOutput := hrejectOutput
      acceptScanSourceOutput := hacceptOutput
      scratchCountWindowMaterializerOutput := hwindowOutput
      scratchCountWindowRestorerOutput := hrestorerOutput
      scratchCountWindowMaterializerAndRestorerOutput := hwindowBothOutput
      postPaddingScratchCountExtenderOutput := hcountExtenderOutput
      scratchExtOutput := hscratchExtOutput
      postPaddingScratchAllocatorOutput := hallocatorOutput }

theorem outputRouteConstruction_core :
    OutputRouteConstruction :=
  outputRouteConstruction_of_exactRoute exactRouteConstruction_core

theorem inputInitializerOutputConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredInputInitializerOutputConstruction :=
  outputRouteConstruction_core.inputInitializerOutput

theorem materializerOutputBranchConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts.OutputRouteBranchConstruction :=
  outputRouteConstruction_core.materializerOutputBranches

theorem materializerAcceptOutputRouteConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts.AcceptOutputRouteConstruction :=
  outputRouteConstruction_core.materializerAcceptOutputRoute

theorem materializerRejectOutputRouteConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts.RejectOutputRouteConstruction :=
  outputRouteConstruction_core.materializerRejectOutputRoute

theorem segmentNormalizerOutputConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerOutputConstruction :=
  outputRouteConstruction_core.segmentNormalizerOutput

theorem outputProjectorOutputConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorOutputConstruction :=
  outputRouteConstruction_core.outputProjectorOutput

theorem scanSourceMaterializerOutputConstruction_core :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerOutputConstruction :=
  outputRouteConstruction_core.scanSourceMaterializerOutput

theorem scratchCountWindowMaterializerOutputConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerOutputConstruction :=
  outputRouteConstruction_core.scratchCountWindowMaterializerOutput

theorem scratchCountWindowMaterializerAndRestorerOutputConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerOutputConstruction :=
  outputRouteConstruction_core.scratchCountWindowMaterializerAndRestorerOutput

theorem postPaddingScratchCountExtenderOutputConstruction_core :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderOutputConstruction :=
  outputRouteConstruction_core.postPaddingScratchCountExtenderOutput

theorem scratchExtOutputConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchExtOutputConstruction :=
  outputRouteConstruction_core.scratchExtOutput

theorem postPaddingScratchAllocatorOutputConstruction_core :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputConstruction :=
  outputRouteConstruction_core.postPaddingScratchAllocatorOutput

end CountWindowThreadedBridgeRouteContracts

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters
end Computability
end FoC
