import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.ScratchExtOutput
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.Mat.Contracts
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.Mat.OutputRoutes
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.ScratchExtCountWindowBridgeSelectedDecoderRouteContracts

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

/-!
## Exact projections
-/

theorem materializerRouteConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredMaterializerRouteContracts.ExactRouteConstruction :=
  hroute.materializerRoute

theorem selectedDecoderRouteConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    CountWindowSelectedDecoderRouteContracts.StructuredPrefixDensifierComponentConstruction :=
  hroute.selectedDecoderRoute

theorem inputInitializerConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction :=
  hroute.inputInitializer

theorem loweredExtractorConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    LoweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction :=
  hroute.loweredExtractor

theorem segmentNormalizerConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction :=
  hroute.segmentNormalizer

theorem outputProjectorConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction :=
  hroute.outputProjector

theorem scanSourceMaterializerConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction :=
  hroute.scanSourceMaterializer

theorem scratchCountWindowMaterializerConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction :=
  hroute.scratchCountWindowMaterializer

theorem scratchCountWindowRestorerConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRestorerConstruction :=
  hroute.scratchCountWindowRestorer

theorem scratchCountWindowMaterializerAndRestorerConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction :=
  hroute.scratchCountWindowMaterializerAndRestorer

theorem postPaddingScratchCountExtenderConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction :=
  hroute.postPaddingScratchCountExtender

theorem scratchExtConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    SelectedProjectionPaddedTailCleanupScratchExtConstruction :=
  hroute.scratchExt

theorem postPaddingScratchAllocatorConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction :=
  hroute.postPaddingScratchAllocator

theorem inputInitializerConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction :=
  inputInitializerConstruction_of_exactRoute exactRouteConstruction_core

theorem segmentNormalizerConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction :=
  segmentNormalizerConstruction_of_exactRoute exactRouteConstruction_core

theorem outputProjectorConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction :=
  outputProjectorConstruction_of_exactRoute exactRouteConstruction_core

theorem scanSourceMaterializerConstruction_core :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction :=
  scanSourceMaterializerConstruction_of_exactRoute exactRouteConstruction_core

theorem scratchCountWindowMaterializerConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction :=
  scratchCountWindowMaterializerConstruction_of_exactRoute
    exactRouteConstruction_core

theorem scratchCountWindowMaterializerAndRestorerConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction :=
  scratchCountWindowMaterializerAndRestorerConstruction_of_exactRoute
    exactRouteConstruction_core

theorem postPaddingScratchCountExtenderConstruction_core :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction :=
  postPaddingScratchCountExtenderConstruction_of_exactRoute
    exactRouteConstruction_core

theorem scratchExtConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchExtConstruction :=
  scratchExtConstruction_of_exactRoute exactRouteConstruction_core

theorem postPaddingScratchAllocatorConstruction_core :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction :=
  postPaddingScratchAllocatorConstruction_of_exactRoute
    exactRouteConstruction_core

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

/-!
## Output projections
-/

theorem exactRouteConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    ExactRouteConstruction :=
  hroute.exactRoute

theorem materializerOutputRouteConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts.OutputRouteConstruction :=
  hroute.materializerOutputRoute

theorem materializerOutputBranchConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts.OutputRouteBranchConstruction :=
  hroute.materializerOutputBranches

theorem materializerAcceptOutputRouteConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts.AcceptOutputRouteConstruction :=
  hroute.materializerAcceptOutputRoute

theorem materializerRejectOutputRouteConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts.RejectOutputRouteConstruction :=
  hroute.materializerRejectOutputRoute

theorem selectedDecoderOutputRouteConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    CountWindowSelectedDecoderRouteContracts.StructuredPrefixOutputComponentConstruction :=
  hroute.selectedDecoderOutputRoute

theorem inputInitializerOutputConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredInputInitializerOutputConstruction :=
  hroute.inputInitializerOutput

theorem segmentNormalizerOutputConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerOutputConstruction :=
  hroute.segmentNormalizerOutput

theorem outputProjectorOutputConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorOutputConstruction :=
  hroute.outputProjectorOutput

theorem scanSourceMaterializerOutputConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerOutputConstruction :=
  hroute.scanSourceMaterializerOutput

theorem rejectScanSourceOutputConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    RejectPostFieldDecodedPrefixScanSourceOutputConstruction :=
  hroute.rejectScanSourceOutput

theorem acceptScanSourceOutputConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    AcceptPostFieldRewoundToDecodedPrefixScanSourceOutputConstruction :=
  hroute.acceptScanSourceOutput

theorem scratchCountWindowMaterializerOutputConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerOutputConstruction :=
  hroute.scratchCountWindowMaterializerOutput

theorem scratchCountWindowRestorerOutputConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRestorerOutputConstruction :=
  hroute.scratchCountWindowRestorerOutput

theorem scratchCountWindowMaterializerAndRestorerOutputConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerOutputConstruction :=
  hroute.scratchCountWindowMaterializerAndRestorerOutput

theorem postPaddingScratchCountExtenderOutputConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderOutputConstruction :=
  hroute.postPaddingScratchCountExtenderOutput

theorem scratchExtOutputConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    SelectedProjectionPaddedTailCleanupScratchExtOutputConstruction :=
  hroute.scratchExtOutput

theorem postPaddingScratchAllocatorOutputConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputConstruction :=
  hroute.postPaddingScratchAllocatorOutput

theorem inputInitializerOutputConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredInputInitializerOutputConstruction :=
  inputInitializerOutputConstruction_of_outputRoute outputRouteConstruction_core

theorem materializerOutputBranchConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts.OutputRouteBranchConstruction :=
  materializerOutputBranchConstruction_of_outputRoute outputRouteConstruction_core

theorem materializerAcceptOutputRouteConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts.AcceptOutputRouteConstruction :=
  materializerAcceptOutputRouteConstruction_of_outputRoute
    outputRouteConstruction_core

theorem materializerRejectOutputRouteConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts.RejectOutputRouteConstruction :=
  materializerRejectOutputRouteConstruction_of_outputRoute
    outputRouteConstruction_core

theorem segmentNormalizerOutputConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerOutputConstruction :=
  segmentNormalizerOutputConstruction_of_outputRoute outputRouteConstruction_core

theorem outputProjectorOutputConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorOutputConstruction :=
  outputProjectorOutputConstruction_of_outputRoute outputRouteConstruction_core

theorem scanSourceMaterializerOutputConstruction_core :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerOutputConstruction :=
  scanSourceMaterializerOutputConstruction_of_outputRoute
    outputRouteConstruction_core

theorem scratchCountWindowMaterializerOutputConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerOutputConstruction :=
  scratchCountWindowMaterializerOutputConstruction_of_outputRoute
    outputRouteConstruction_core

theorem scratchCountWindowMaterializerAndRestorerOutputConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerOutputConstruction :=
  scratchCountWindowMaterializerAndRestorerOutputConstruction_of_outputRoute
    outputRouteConstruction_core

theorem postPaddingScratchCountExtenderOutputConstruction_core :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderOutputConstruction :=
  postPaddingScratchCountExtenderOutputConstruction_of_outputRoute
    outputRouteConstruction_core

theorem scratchExtOutputConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchExtOutputConstruction :=
  scratchExtOutputConstruction_of_outputRoute outputRouteConstruction_core

theorem postPaddingScratchAllocatorOutputConstruction_core :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputConstruction :=
  postPaddingScratchAllocatorOutputConstruction_of_outputRoute
    outputRouteConstruction_core

end CountWindowThreadedBridgeRouteContracts

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters
end Computability
end FoC
