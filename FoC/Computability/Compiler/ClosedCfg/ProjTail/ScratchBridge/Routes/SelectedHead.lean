import FoC.Computability.Compiler.Structured.HeadRoutes
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.Output

set_option doc.verso true

/-!
# Count-window selected-head route contracts

The count-window bridge currently obtains its structured tape-2 normalizer
through the selected-prefix densifier route.  The generic selected-head route
introduced in
{module}`FoC.Computability.Compiler.Structured.HeadRoutes`
is another reusable way to expose the same downstream count-window surface:
selected-segment decoder, tape-2 segment normalizer, output projector, and
scan-source materializer inputs.

This module is a consumer-side route package.  It does not assert that the
generic padded selected-head cleanup has been constructed; instead it records
the count-window consequences of that premise so later finite-machine work can
plug into one narrow boundary.
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

open CanonicalLayouts.DovetailLayoutScanner

namespace CountWindowSelectedHeadRouteContracts

/-!
## Exact count-window adapters

The selected head decoder specializes to the count-window selected segment
decoder with an empty rest list.  The generic tape-2 segment normalizer then
specializes to the concrete count-window structured output shape.
-/

/-- Count-window selected-segment decoder from a generic selected-head decoder. -/
theorem selectedSegmentDecoderSpec_of_selectedHeadSpec
    {decoder : MachineDescription}
    (hdecoder : StructuredSelectedHeadSegmentDecoderSpec decoder) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderSpec decoder := by
  rcases hdecoder with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro useAccept L encodedPrefix
  simpa using
    hrun (postFieldDecodedPrefixScanSourceTape useAccept L) []
      encodedPrefix

/-- Construction-level selected-segment decoder adapter. -/
theorem selectedSegmentDecoderConstruction_of_selectedHead
    (hdecoder : StructuredSelectedHeadSegmentDecoderConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction := by
  rcases hdecoder with ⟨decoder, hspec⟩
  exact
    ⟨decoder,
      selectedSegmentDecoderSpec_of_selectedHeadSpec hspec⟩

/-- Count-window selected-segment decoder from padded selected-head cleanup. -/
theorem selectedSegmentDecoderConstruction_of_headCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction :=
  selectedSegmentDecoderConstruction_of_selectedHead
    (structuredSelectedHeadSegmentDecoderConstruction_of_headCleanup
      hcleanup)

/-- Count-window segment normalizer from a generic tape-2 segment normalizer. -/
theorem segmentNormalizerSpec_of_structuredTape2Spec
    {normalizer : MachineDescription}
    (hnormalizer : StructuredTape2SegmentNormalizerSpec normalizer) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerSpec
      normalizer := by
  rcases hnormalizer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro useAccept L deletedTail physical hseparator
  exact
    hrun
      (structuredBoolWordRawBitsDecoderSourceTargetTape
        (ParsedLayoutBits L)
        (countWindowPostFieldDecodedPrefixStructuredSuffixTail useAccept L)
        (countWindowPostFieldDecodedPrefixStructuredSourcePadding
          useAccept L deletedTail))
      (structuredBoolWordRawBitsDecoderCounterDecodeTape 0
        ((ParsedLayoutBits L).length + 1))
      (postFieldDecodedPrefixScanSourceTape useAccept L)
      physical hseparator

/-- Construction-level count-window segment normalizer adapter. -/
theorem segmentNormalizerConstruction_of_structuredTape2
    (hnormalizer : StructuredTape2SegmentNormalizerConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction := by
  rcases hnormalizer with ⟨normalizer, hspec⟩
  exact
    ⟨normalizer,
      segmentNormalizerSpec_of_structuredTape2Spec hspec⟩

/-- Count-window segment normalizer from a generic selected-head decoder. -/
theorem segmentNormalizerConstruction_of_selectedHead
    (hdecoder : StructuredSelectedHeadSegmentDecoderConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction :=
  segmentNormalizerConstruction_of_structuredTape2
    (structuredTape2SegmentNormalizerConstruction_of_selectedHeadDecoder
      hdecoder)

/-- Count-window segment normalizer from padded selected-head cleanup. -/
theorem segmentNormalizerConstruction_of_headCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction :=
  segmentNormalizerConstruction_of_selectedHead
    (structuredSelectedHeadSegmentDecoderConstruction_of_headCleanup
      hcleanup)

/-- Count-window output projector from a generic selected-head decoder. -/
theorem outputProjectorConstruction_of_selectedHead
    (hdecoder : StructuredSelectedHeadSegmentDecoderConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction :=
  countWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction_of_segmentNormalizer
    (structuredTape2SegmentNormalizerConstruction_of_selectedHeadDecoder
      hdecoder)

/-- Count-window output projector from the generic selected-head route bundle. -/
theorem outputProjectorConstruction_of_selectedHeadRoute
    (hroute : StructuredSelectedHeadDecoderRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction :=
  outputProjectorConstruction_of_selectedHead hroute.headDecoder

/-- Count-window output projector from padded selected-head cleanup. -/
theorem outputProjectorConstruction_of_headCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction :=
  outputProjectorConstruction_of_selectedHead
    (structuredSelectedHeadSegmentDecoderConstruction_of_headCleanup
      hcleanup)

/-!
## Output adapters

The output-level contracts follow from the exact count-window adapters.  They
are useful for downstream routes that only consume the decoded scan-source word
and do not need the final cursor position.
-/

/-- Output selected-segment decoder from a generic selected-head decoder. -/
theorem selectedSegmentDecoderOutputConstruction_of_selectedHead
    (hdecoder : StructuredSelectedHeadSegmentDecoderConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderOutputConstruction :=
  countWindowPostFieldDecodedPrefixSelectedSegmentDecoderOutputConstruction_of_exact
    (selectedSegmentDecoderConstruction_of_selectedHead hdecoder)

/-- Output selected-segment decoder from a selected-head route bundle. -/
theorem selectedSegmentDecoderOutputConstruction_of_selectedHeadRoute
    (hroute : StructuredSelectedHeadDecoderRouteConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderOutputConstruction :=
  selectedSegmentDecoderOutputConstruction_of_selectedHead hroute.headDecoder

/-- Output selected-segment decoder from padded selected-head cleanup. -/
theorem selectedSegmentDecoderOutputConstruction_of_headCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderOutputConstruction :=
  selectedSegmentDecoderOutputConstruction_of_selectedHead
    (structuredSelectedHeadSegmentDecoderConstruction_of_headCleanup
      hcleanup)

/-- Output segment normalizer from a generic tape-2 segment normalizer. -/
theorem segmentNormalizerOutputConstruction_of_structuredTape2
    (hnormalizer : StructuredTape2SegmentNormalizerConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerOutputConstruction :=
  countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerOutputConstruction_of_exact
    (segmentNormalizerConstruction_of_structuredTape2 hnormalizer)

/-- Output segment normalizer from a generic selected-head decoder. -/
theorem segmentNormalizerOutputConstruction_of_selectedHead
    (hdecoder : StructuredSelectedHeadSegmentDecoderConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerOutputConstruction :=
  segmentNormalizerOutputConstruction_of_structuredTape2
    (structuredTape2SegmentNormalizerConstruction_of_selectedHeadDecoder
      hdecoder)

/-- Output segment normalizer from a selected-head route bundle. -/
theorem segmentNormalizerOutputConstruction_of_selectedHeadRoute
    (hroute : StructuredSelectedHeadDecoderRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerOutputConstruction :=
  segmentNormalizerOutputConstruction_of_selectedHead hroute.headDecoder

/-- Output segment normalizer from padded selected-head cleanup. -/
theorem segmentNormalizerOutputConstruction_of_headCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerOutputConstruction :=
  segmentNormalizerOutputConstruction_of_selectedHead
    (structuredSelectedHeadSegmentDecoderConstruction_of_headCleanup
      hcleanup)

/-- Output projector route from a generic selected-head decoder. -/
theorem outputProjectorOutputConstruction_of_selectedHead
    (hdecoder : StructuredSelectedHeadSegmentDecoderConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorOutputConstruction :=
  countWindowPostFieldDecodedPrefixStructuredOutputProjectorOutputConstruction_of_exact
    (outputProjectorConstruction_of_selectedHead hdecoder)

/-- Output projector route from a selected-head route bundle. -/
theorem outputProjectorOutputConstruction_of_selectedHeadRoute
    (hroute : StructuredSelectedHeadDecoderRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorOutputConstruction :=
  outputProjectorOutputConstruction_of_selectedHead hroute.headDecoder

/-- Output projector route from padded selected-head cleanup. -/
theorem outputProjectorOutputConstruction_of_headCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorOutputConstruction :=
  outputProjectorOutputConstruction_of_selectedHead
    (structuredSelectedHeadSegmentDecoderConstruction_of_headCleanup
      hcleanup)

/-!
## Exact route bundle

The bundle records the count-window consequences of one generic selected-head
route.  The redundant fields are intentional: later endpoint proofs often need
only one of these constructions, and extracting it by field is cheaper than
rebuilding a chain of local adapters.
-/

structure ExactRouteConstruction : Prop where
  selectedHeadRoute :
    StructuredSelectedHeadDecoderRouteConstruction
  selectedSegmentDecoder :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction
  selectedSegmentDecoderOutput :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderOutputConstruction
  segmentNormalizer :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction
  segmentNormalizerOutput :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerOutputConstruction
  outputProjector :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction
  outputProjectorOutput :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorOutputConstruction

/-- Build the exact count-window selected-head route from the generic route. -/
theorem exactRouteConstruction_of_selectedHeadRoute
    (hroute : StructuredSelectedHeadDecoderRouteConstruction) :
    ExactRouteConstruction := by
  let hdecoder :
      StructuredSelectedHeadSegmentDecoderConstruction :=
    hroute.headDecoder
  let hselected :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction :=
    selectedSegmentDecoderConstruction_of_selectedHead hdecoder
  let hselectedOutput :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderOutputConstruction :=
    selectedSegmentDecoderOutputConstruction_of_selectedHead hdecoder
  let hnormalizer :
      CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction :=
    segmentNormalizerConstruction_of_selectedHead hdecoder
  let hnormalizerOutput :
      CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerOutputConstruction :=
    segmentNormalizerOutputConstruction_of_selectedHead hdecoder
  let hprojector :
      CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction :=
    outputProjectorConstruction_of_selectedHead hdecoder
  let hprojectorOutput :
      CountWindowPostFieldDecodedPrefixStructuredOutputProjectorOutputConstruction :=
    outputProjectorOutputConstruction_of_selectedHead hdecoder
  exact
    { selectedHeadRoute := hroute
      selectedSegmentDecoder := hselected
      selectedSegmentDecoderOutput := hselectedOutput
      segmentNormalizer := hnormalizer
      segmentNormalizerOutput := hnormalizerOutput
      outputProjector := hprojector
      outputProjectorOutput := hprojectorOutput }

/-- Build the exact count-window selected-head route from padded cleanup. -/
theorem exactRouteConstruction_of_headCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    ExactRouteConstruction :=
  exactRouteConstruction_of_selectedHeadRoute
    (structuredSelectedHeadDecoderRouteConstruction_of_headCleanup
      hcleanup)

/-!
## Exact route projections
-/

theorem selectedHeadRoute_of_exactRoute
    (hroute : ExactRouteConstruction) :
    StructuredSelectedHeadDecoderRouteConstruction :=
  hroute.selectedHeadRoute

theorem selectedSegmentDecoderConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction :=
  hroute.selectedSegmentDecoder

theorem selectedSegmentDecoderOutputConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderOutputConstruction :=
  hroute.selectedSegmentDecoderOutput

theorem segmentNormalizerConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction :=
  hroute.segmentNormalizer

theorem segmentNormalizerOutputConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerOutputConstruction :=
  hroute.segmentNormalizerOutput

theorem outputProjectorConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction :=
  hroute.outputProjector

theorem outputProjectorOutputConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorOutputConstruction :=
  hroute.outputProjectorOutput

/-!
## Scan-source materializer route

The count-window bridge uses the output projector together with the structured
input initializer and lowered extractor to build the scan-source materializer.
This section packages that downstream route with the selected-head projector
as its projector source.
-/

structure ScanSourceRouteConstruction : Prop where
  exactRoute : ExactRouteConstruction
  inputInitializer :
    CountWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction
  loweredExtractor :
    LoweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction
  scanSourceMaterializer :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction

/-- Build scan-source materialization from exact selected-head projector parts. -/
theorem scanSourceRouteConstruction_of_parts
    (hroute : ExactRouteConstruction)
    (hinitializer :
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction)
    (hextractor :
      LoweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction) :
    ScanSourceRouteConstruction := by
  let hscan :
      CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction :=
    countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_of_structuredParts
      hinitializer hextractor hroute.outputProjector
  exact
    { exactRoute := hroute
      inputInitializer := hinitializer
      loweredExtractor := hextractor
      scanSourceMaterializer := hscan }

/-- Build scan-source materialization from a selected-head route bundle. -/
theorem scanSourceRouteConstruction_of_selectedHeadRoute
    (hroute : StructuredSelectedHeadDecoderRouteConstruction)
    (hinitializer :
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction)
    (hextractor :
      LoweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction) :
    ScanSourceRouteConstruction :=
  scanSourceRouteConstruction_of_parts
    (exactRouteConstruction_of_selectedHeadRoute hroute)
    hinitializer hextractor

/-- Build scan-source materialization from padded selected-head cleanup. -/
theorem scanSourceRouteConstruction_of_headCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction)
    (hinitializer :
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction)
    (hextractor :
      LoweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction) :
    ScanSourceRouteConstruction :=
  scanSourceRouteConstruction_of_selectedHeadRoute
    (structuredSelectedHeadDecoderRouteConstruction_of_headCleanup
      hcleanup)
    hinitializer hextractor

theorem exactRouteConstruction_of_scanSourceRoute
    (hroute : ScanSourceRouteConstruction) :
    ExactRouteConstruction :=
  hroute.exactRoute

theorem inputInitializerConstruction_of_scanSourceRoute
    (hroute : ScanSourceRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction :=
  hroute.inputInitializer

theorem loweredExtractorConstruction_of_scanSourceRoute
    (hroute : ScanSourceRouteConstruction) :
    LoweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction :=
  hroute.loweredExtractor

theorem scanSourceMaterializerConstruction_of_scanSourceRoute
    (hroute : ScanSourceRouteConstruction) :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction :=
  hroute.scanSourceMaterializer

theorem outputProjectorConstruction_of_scanSourceRoute
    (hroute : ScanSourceRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction :=
  hroute.exactRoute.outputProjector

theorem segmentNormalizerConstruction_of_scanSourceRoute
    (hroute : ScanSourceRouteConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction :=
  hroute.exactRoute.segmentNormalizer

theorem selectedSegmentDecoderConstruction_of_scanSourceRoute
    (hroute : ScanSourceRouteConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction :=
  hroute.exactRoute.selectedSegmentDecoder

/-!
## Relationship to existing count-window selected-decoder route

The existing route packages the structured-prefix eraser and footprint
compactor path.  The selected-head route is a different premise, but once it
is available it supplies the same count-window normalizer and projector
surface expected by the later bridge.
-/

structure SelectedHeadCompatibilityConstruction : Prop where
  selectedHeadExact :
    ExactRouteConstruction
  selectedDecoder :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction
  structuredSegmentNormalizer :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction
  structuredOutputProjector :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction

/-- Compatibility bundle from the selected-head exact route. -/
theorem selectedHeadCompatibilityConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    SelectedHeadCompatibilityConstruction :=
  { selectedHeadExact := hroute
    selectedDecoder := hroute.selectedSegmentDecoder
    structuredSegmentNormalizer := hroute.segmentNormalizer
    structuredOutputProjector := hroute.outputProjector }

/-- Compatibility bundle from a generic selected-head route. -/
theorem selectedHeadCompatibilityConstruction_of_selectedHeadRoute
    (hroute : StructuredSelectedHeadDecoderRouteConstruction) :
    SelectedHeadCompatibilityConstruction :=
  selectedHeadCompatibilityConstruction_of_exactRoute
    (exactRouteConstruction_of_selectedHeadRoute hroute)

/-- Compatibility bundle from padded selected-head cleanup. -/
theorem selectedHeadCompatibilityConstruction_of_headCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    SelectedHeadCompatibilityConstruction :=
  selectedHeadCompatibilityConstruction_of_selectedHeadRoute
    (structuredSelectedHeadDecoderRouteConstruction_of_headCleanup
      hcleanup)

theorem selectedSegmentDecoderConstruction_of_compatibility
    (hcompat : SelectedHeadCompatibilityConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction :=
  hcompat.selectedDecoder

theorem exactRouteConstruction_of_compatibility
    (hcompat : SelectedHeadCompatibilityConstruction) :
    ExactRouteConstruction :=
  hcompat.selectedHeadExact

theorem segmentNormalizerConstruction_of_compatibility
    (hcompat : SelectedHeadCompatibilityConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction :=
  hcompat.structuredSegmentNormalizer

theorem outputProjectorConstruction_of_compatibility
    (hcompat : SelectedHeadCompatibilityConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction :=
  hcompat.structuredOutputProjector

end CountWindowSelectedHeadRouteContracts

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters
end Computability
end FoC
