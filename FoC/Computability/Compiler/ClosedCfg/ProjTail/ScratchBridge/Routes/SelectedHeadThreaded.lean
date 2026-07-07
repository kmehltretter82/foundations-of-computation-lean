import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchExtOutput
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.Mat.Contracts
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.Mat.OutputRoutes
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.Routes.SelectedHead

set_option doc.verso true

/-!
# Selected-head threaded count-window bridge route contracts

The standard threaded count-window bridge route packages the structured input
materializer, the structured-prefix selected decoder route, the lowered
extractor, and the downstream scratch-extension pipeline.

This module records the parallel threaded route when the selected decoder is
provided by the generic selected-head route from
{module}`FoC.Computability.Compiler.Structured.HeadRoutes`.
It is intentionally conditional: the remaining finite-machine work is still
the structured input materializer and the padded selected-head cleanup.  Once
those are available, this route threads them through the same scan-source
materializer, scratch-count materializer, scratch extender, and post-padding
scratch allocator endpoints as the existing count-window bridge.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

namespace CountWindowSelectedHeadThreadedRouteContracts

/-!
## Exact threaded route

The exact route is the backend-facing route.  It preserves the ordinary
{name}`MachineDescription` boundary and records every downstream construction
that the count-window bridge needs after selected-head projection.
-/

structure ExactRouteConstruction : Prop where
  materializerRoute :
    CountWindowPostFieldDecodedPrefixStructuredMaterializerRouteContracts.ExactRouteConstruction
  selectedHeadRoute :
    CountWindowSelectedHeadRouteContracts.ExactRouteConstruction
  inputInitializer :
    CountWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction
  loweredExtractor :
    LoweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction
  selectedSegmentDecoder :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction
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

/--
Thread the selected-head route through the exact count-window bridge
components.
-/
theorem exactRouteConstruction_of_routes
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredMaterializerRouteContracts.ExactRouteConstruction)
    (hselectedHead :
      CountWindowSelectedHeadRouteContracts.ExactRouteConstruction)
    (hextractor :
      LoweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction) :
    ExactRouteConstruction := by
  let hinitializer :
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction :=
    CountWindowPostFieldDecodedPrefixStructuredMaterializerRouteContracts.inputInitializerConstruction_of_exactRouteConstruction
      hmaterializer
  let hselected :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction :=
    hselectedHead.selectedSegmentDecoder
  let hsegment :
      CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction :=
    hselectedHead.segmentNormalizer
  let hprojector :
      CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction :=
    hselectedHead.outputProjector
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
      selectedHeadRoute := hselectedHead
      inputInitializer := hinitializer
      loweredExtractor := hextractor
      selectedSegmentDecoder := hselected
      segmentNormalizer := hsegment
      outputProjector := hprojector
      scanSourceMaterializer := hscan
      scratchCountWindowMaterializer := hwindow
      scratchCountWindowRestorer := hrestorer
      scratchCountWindowMaterializerAndRestorer := hwindowBoth
      postPaddingScratchCountExtender := hcountExtender
      scratchExt := hscratchExt
      postPaddingScratchAllocator := hallocator }

/--
Build the threaded exact route from the generic selected-head route bundle.
-/
theorem exactRouteConstruction_of_selectedHeadRoute
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredMaterializerRouteContracts.ExactRouteConstruction)
    (hselectedHead :
      StructuredSelectedHeadDecoderRouteConstruction)
    (hextractor :
      LoweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction) :
    ExactRouteConstruction :=
  exactRouteConstruction_of_routes
    hmaterializer
    (CountWindowSelectedHeadRouteContracts.exactRouteConstruction_of_selectedHeadRoute
      hselectedHead)
    hextractor

/--
Build the threaded exact route from the padded selected-head cleanup premise.
-/
theorem exactRouteConstruction_of_headCleanup
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredMaterializerRouteContracts.ExactRouteConstruction)
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction)
    (hextractor :
      LoweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction) :
    ExactRouteConstruction :=
  exactRouteConstruction_of_routes
    hmaterializer
    (CountWindowSelectedHeadRouteContracts.exactRouteConstruction_of_headCleanup
      hcleanup)
    hextractor

/-!
## Exact projections
-/

theorem materializerRouteConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredMaterializerRouteContracts.ExactRouteConstruction :=
  hroute.materializerRoute

theorem selectedHeadRouteConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    CountWindowSelectedHeadRouteContracts.ExactRouteConstruction :=
  hroute.selectedHeadRoute

theorem inputInitializerConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction :=
  hroute.inputInitializer

theorem loweredExtractorConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    LoweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction :=
  hroute.loweredExtractor

theorem selectedSegmentDecoderConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction :=
  hroute.selectedSegmentDecoder

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

/-!
## Output threaded route

The output route mirrors the exact route for downstream routes that only
consume normalized output words.  It is derived from exact endpoints and does
not add new machine obligations.
-/

structure OutputRouteConstruction : Prop where
  exactRoute :
    ExactRouteConstruction
  materializerOutputRoute :
    CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts.OutputRouteConstruction
  materializerOutputBranches :
    CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts.OutputRouteBranchConstruction
  materializerAcceptOutputRoute :
    CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts.AcceptOutputRouteConstruction
  materializerRejectOutputRoute :
    CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts.RejectOutputRouteConstruction
  selectedSegmentDecoderOutput :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderOutputConstruction
  segmentNormalizerOutput :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerOutputConstruction
  outputProjectorOutput :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorOutputConstruction
  inputInitializerOutput :
    CountWindowPostFieldDecodedPrefixStructuredInputInitializerOutputConstruction
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

/-- Weaken an exact selected-head threaded route to its output views. -/
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
  let hselectedOutput :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderOutputConstruction :=
    hroute.selectedHeadRoute.selectedSegmentDecoderOutput
  let hsegmentOutput :
      CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerOutputConstruction :=
    hroute.selectedHeadRoute.segmentNormalizerOutput
  let hprojectorOutput :
      CountWindowPostFieldDecodedPrefixStructuredOutputProjectorOutputConstruction :=
    hroute.selectedHeadRoute.outputProjectorOutput
  let hinitializerOutput :
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerOutputConstruction :=
    CountWindowPostFieldDecodedPrefixStructuredMaterializerOutputRouteContracts.initializerOutputConstruction_of_outputRouteConstruction
      hmaterializerOutputRoute
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
      selectedSegmentDecoderOutput := hselectedOutput
      segmentNormalizerOutput := hsegmentOutput
      outputProjectorOutput := hprojectorOutput
      inputInitializerOutput := hinitializerOutput
      scanSourceMaterializerOutput := hscanOutput
      rejectScanSourceOutput := hrejectOutput
      acceptScanSourceOutput := hacceptOutput
      scratchCountWindowMaterializerOutput := hwindowOutput
      scratchCountWindowRestorerOutput := hrestorerOutput
      scratchCountWindowMaterializerAndRestorerOutput := hwindowBothOutput
      postPaddingScratchCountExtenderOutput := hcountExtenderOutput
      scratchExtOutput := hscratchExtOutput
      postPaddingScratchAllocatorOutput := hallocatorOutput }

/-- Output route from generic selected-head route pieces. -/
theorem outputRouteConstruction_of_selectedHeadRoute
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredMaterializerRouteContracts.ExactRouteConstruction)
    (hselectedHead :
      StructuredSelectedHeadDecoderRouteConstruction)
    (hextractor :
      LoweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction) :
    OutputRouteConstruction :=
  outputRouteConstruction_of_exactRoute
    (exactRouteConstruction_of_selectedHeadRoute
      hmaterializer hselectedHead hextractor)

/-- Output route from the padded selected-head cleanup premise. -/
theorem outputRouteConstruction_of_headCleanup
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredMaterializerRouteContracts.ExactRouteConstruction)
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction)
    (hextractor :
      LoweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction) :
    OutputRouteConstruction :=
  outputRouteConstruction_of_exactRoute
    (exactRouteConstruction_of_headCleanup
      hmaterializer hcleanup hextractor)

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

theorem selectedSegmentDecoderOutputConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderOutputConstruction :=
  hroute.selectedSegmentDecoderOutput

theorem segmentNormalizerOutputConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerOutputConstruction :=
  hroute.segmentNormalizerOutput

theorem outputProjectorOutputConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorOutputConstruction :=
  hroute.outputProjectorOutput

theorem inputInitializerOutputConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredInputInitializerOutputConstruction :=
  hroute.inputInitializerOutput

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

/-!
## Bridge compatibility

These small bundles show that the selected-head threaded route exposes the
same downstream bridge endpoints as the older selected-prefix route.
-/

structure DownstreamBridgeConstruction : Prop where
  exactRoute :
    ExactRouteConstruction
  outputRoute :
    OutputRouteConstruction
  scanSourceMaterializer :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction
  scanSourceMaterializerOutput :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerOutputConstruction
  scratchCountWindowMaterializer :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction
  scratchCountWindowMaterializerOutput :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerOutputConstruction
  scratchCountWindowMaterializerAndRestorer :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction
  scratchCountWindowMaterializerAndRestorerOutput :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerOutputConstruction
  postPaddingScratchCountExtender :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction
  postPaddingScratchCountExtenderOutput :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderOutputConstruction
  scratchExt :
    SelectedProjectionPaddedTailCleanupScratchExtConstruction
  scratchExtOutput :
    SelectedProjectionPaddedTailCleanupScratchExtOutputConstruction
  postPaddingScratchAllocator :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction
  postPaddingScratchAllocatorOutput :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputConstruction

theorem downstreamBridgeConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    DownstreamBridgeConstruction := by
  let houtput : OutputRouteConstruction :=
    outputRouteConstruction_of_exactRoute hroute
  exact
    { exactRoute := hroute
      outputRoute := houtput
      scanSourceMaterializer := hroute.scanSourceMaterializer
      scanSourceMaterializerOutput := houtput.scanSourceMaterializerOutput
      scratchCountWindowMaterializer := hroute.scratchCountWindowMaterializer
      scratchCountWindowMaterializerOutput :=
        houtput.scratchCountWindowMaterializerOutput
      scratchCountWindowMaterializerAndRestorer :=
        hroute.scratchCountWindowMaterializerAndRestorer
      scratchCountWindowMaterializerAndRestorerOutput :=
        houtput.scratchCountWindowMaterializerAndRestorerOutput
      postPaddingScratchCountExtender :=
        hroute.postPaddingScratchCountExtender
      postPaddingScratchCountExtenderOutput :=
        houtput.postPaddingScratchCountExtenderOutput
      scratchExt := hroute.scratchExt
      scratchExtOutput := houtput.scratchExtOutput
      postPaddingScratchAllocator := hroute.postPaddingScratchAllocator
      postPaddingScratchAllocatorOutput :=
        houtput.postPaddingScratchAllocatorOutput }

theorem downstreamBridgeConstruction_of_selectedHeadRoute
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredMaterializerRouteContracts.ExactRouteConstruction)
    (hselectedHead :
      StructuredSelectedHeadDecoderRouteConstruction)
    (hextractor :
      LoweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction) :
    DownstreamBridgeConstruction :=
  downstreamBridgeConstruction_of_exactRoute
    (exactRouteConstruction_of_selectedHeadRoute
      hmaterializer hselectedHead hextractor)

theorem downstreamBridgeConstruction_of_headCleanup
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixStructuredMaterializerRouteContracts.ExactRouteConstruction)
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction)
    (hextractor :
      LoweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction) :
    DownstreamBridgeConstruction :=
  downstreamBridgeConstruction_of_exactRoute
    (exactRouteConstruction_of_headCleanup
      hmaterializer hcleanup hextractor)

theorem exactRouteConstruction_of_downstreamBridge
    (hbridge : DownstreamBridgeConstruction) :
    ExactRouteConstruction :=
  hbridge.exactRoute

theorem outputRouteConstruction_of_downstreamBridge
    (hbridge : DownstreamBridgeConstruction) :
    OutputRouteConstruction :=
  hbridge.outputRoute

theorem postPaddingScratchAllocatorConstruction_of_downstreamBridge
    (hbridge : DownstreamBridgeConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction :=
  hbridge.postPaddingScratchAllocator

theorem postPaddingScratchAllocatorOutputConstruction_of_downstreamBridge
    (hbridge : DownstreamBridgeConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputConstruction :=
  hbridge.postPaddingScratchAllocatorOutput

end CountWindowSelectedHeadThreadedRouteContracts

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters
end Computability
end FoC
