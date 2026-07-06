import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.ScratchExtCountWindowBridgeOutput
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.SelectedFootprintCompactionRouteContracts
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.StructuredPrefixEraserRouteContracts

set_option doc.verso true

/-!
# Count-window selected-decoder route contracts

This module packages the count-window-specific selected-segment decoder
wrappers around the generic structured-prefix eraser and selected-footprint
compactor route contracts.  It does not close the remaining materializer leaf;
instead it records the already-available exact and normalized-output route
surface from the generic selected-segment primitives to the count-window
structured segment normalizer.
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

namespace CountWindowSelectedDecoderRouteContracts

/-!
## Count-window adapters from generic selected-segment routes
-/

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseSpec_of_twoTapeStructuredPrefixEraser
    {eraser : MachineDescription}
    (heraser :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSpec
        eraser) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseSpec
      eraser := by
  rcases heraser with ⟨hready, hrun⟩
  refine ⟨hready, ?_, ?_, ?_, ?_⟩
  · intro L
    simpa [
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape,
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape,
      countWindowPostFieldDecodedPrefixStructuredPrefixEraserSourceTape,
      countWindowPostFieldDecodedPrefixStructuredPrefixSelectedSegmentTargetTape,
      countWindowPostFieldDecodedPrefixStructuredPrefixEraserTargetTape,
      countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix_accept_eq_prefixCells,
      postFieldDecodedPrefixScanSourceTape] using
      hrun
        (structuredBoolWordRawBitsDecoderSourceTargetTape
          (ParsedLayoutBits L)
          (countWindowPostFieldDecodedPrefixStructuredSuffixTail true L)
          (countWindowPostFieldDecodedPrefixStructuredSourcePadding
            true L []))
        (structuredBoolWordRawBitsDecoderCounterDecodeTape 0
          ((ParsedLayoutBits L).length + 1))
        (ParsedLayoutBits L)
        (postFieldDecodedPrefixScanPadding true L)
  · intro L bit rest
    simpa [
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape,
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape,
      countWindowPostFieldDecodedPrefixStructuredPrefixEraserSourceTape,
      countWindowPostFieldDecodedPrefixStructuredPrefixSelectedSegmentTargetTape,
      countWindowPostFieldDecodedPrefixStructuredPrefixEraserTargetTape,
      countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix_accept_eq_prefixCells,
      postFieldDecodedPrefixScanSourceTape] using
      hrun
        (structuredBoolWordRawBitsDecoderSourceTargetTape
          (ParsedLayoutBits L)
          (countWindowPostFieldDecodedPrefixStructuredSuffixTail true L)
          (countWindowPostFieldDecodedPrefixStructuredSourcePadding
            true L (bit :: rest)))
        (structuredBoolWordRawBitsDecoderCounterDecodeTape 0
          ((ParsedLayoutBits L).length + 1))
        (ParsedLayoutBits L)
        (postFieldDecodedPrefixScanPadding true L)
  · intro L
    simpa [
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape,
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape,
      countWindowPostFieldDecodedPrefixStructuredPrefixEraserSourceTape,
      countWindowPostFieldDecodedPrefixStructuredPrefixSelectedSegmentTargetTape,
      countWindowPostFieldDecodedPrefixStructuredPrefixEraserTargetTape,
      countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix_reject_eq_prefixCells,
      postFieldDecodedPrefixScanSourceTape] using
      hrun
        (structuredBoolWordRawBitsDecoderSourceTargetTape
          (ParsedLayoutBits L)
          (countWindowPostFieldDecodedPrefixStructuredSuffixTail false L)
          (countWindowPostFieldDecodedPrefixStructuredSourcePadding
            false L []))
        (structuredBoolWordRawBitsDecoderCounterDecodeTape 0
          ((ParsedLayoutBits L).length + 1))
        (ParsedLayoutBits L)
        (postFieldDecodedPrefixScanPadding false L)
  · intro L bit rest
    simpa [
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape,
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape,
      countWindowPostFieldDecodedPrefixStructuredPrefixEraserSourceTape,
      countWindowPostFieldDecodedPrefixStructuredPrefixSelectedSegmentTargetTape,
      countWindowPostFieldDecodedPrefixStructuredPrefixEraserTargetTape,
      countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix_reject_eq_prefixCells,
      postFieldDecodedPrefixScanSourceTape] using
      hrun
        (structuredBoolWordRawBitsDecoderSourceTargetTape
          (ParsedLayoutBits L)
          (countWindowPostFieldDecodedPrefixStructuredSuffixTail false L)
          (countWindowPostFieldDecodedPrefixStructuredSourcePadding
            false L (bit :: rest)))
        (structuredBoolWordRawBitsDecoderCounterDecodeTape 0
          ((ParsedLayoutBits L).length + 1))
        (ParsedLayoutBits L)
        (postFieldDecodedPrefixScanPadding false L)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction_of_twoTapeStructuredPrefixEraser
    (heraser :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction := by
  rcases heraser with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseSpec_of_twoTapeStructuredPrefixEraser
        hspec⟩

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchSpec_of_branchCaseSpec
    {eraser : MachineDescription}
    (hcases :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseSpec
        eraser) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchSpec
      eraser := by
  rcases hcases with
    ⟨hready, hacceptNil, hacceptCons, hrejectNil, hrejectCons⟩
  refine ⟨hready, ?_, ?_⟩
  · intro L deletedTail
    cases deletedTail with
    | nil =>
        exact hacceptNil L
    | cons bit rest =>
        exact hacceptCons L bit rest
  · intro L deletedTail
    cases deletedTail with
    | nil =>
        exact hrejectNil L
    | cons bit rest =>
        exact hrejectCons L bit rest

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserSpec_of_branchSpec
    {eraser : MachineDescription}
    (hbranches :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchSpec
        eraser) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserSpec
      eraser := by
  rcases hbranches with ⟨hready, haccept, hreject⟩
  refine ⟨hready, ?_⟩
  intro useAccept L deletedTail
  cases useAccept
  · exact hreject L deletedTail
  · exact haccept L deletedTail

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseSpec_of_structuredPrefixRoute
    {eraser : MachineDescription}
    (hroute :
      StructuredPrefixEraserRouteContracts.ExactRouteSpec eraser) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseSpec
      eraser :=
  countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseSpec_of_twoTapeStructuredPrefixEraser
    hroute.selectedEraser

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserSpec_of_structuredPrefixRoute
    {eraser : MachineDescription}
    (hroute :
      StructuredPrefixEraserRouteContracts.ExactRouteSpec eraser) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserSpec
      eraser :=
  countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserSpec_of_branchSpec
    (countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchSpec_of_branchCaseSpec
      (countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseSpec_of_structuredPrefixRoute
        hroute))

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserConstruction_of_structuredPrefixRoute
    (hroute :
      StructuredPrefixEraserRouteContracts.ExactRouteConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserConstruction := by
  rcases hroute with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserSpec_of_structuredPrefixRoute
        hspec⟩

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorSpec_of_generic
    {compactor : MachineDescription}
    (hgeneric :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorSpec
        compactor) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorSpec
      compactor := by
  rcases hgeneric with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro useAccept L
  simpa [
    countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorSourceTape,
    countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorTargetTape,
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape,
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape,
    postFieldDecodedPrefixScanSourceTape] using
    hrun (ParsedLayoutBits L)
      (postFieldDecodedPrefixScanPadding useAccept L)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorSpec_of_selectedFootprintRoute
    {compactor : MachineDescription}
    (hroute :
      SelectedFootprintCompactorRouteContracts.ExactRouteSpec
        compactor) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorSpec
      compactor :=
  countWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorSpec_of_generic
    hroute.footprint

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction_of_selectedFootprintRoute
    (hroute :
      SelectedFootprintCompactorRouteContracts.ExactRouteConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction := by
  rcases hroute with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorSpec_of_selectedFootprintRoute
        hspec⟩

/-!
## Exact selected-decoder component route
-/

structure StructuredPrefixDensifierComponentSpec
    (eraser compactor : MachineDescription) : Prop where
  structuredPrefixRoute :
    StructuredPrefixEraserRouteContracts.ExactRouteSpec eraser
  selectedFootprintRoute :
    SelectedFootprintCompactorRouteContracts.ExactRouteSpec compactor
  eraserBranchCases :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseSpec
      eraser
  eraserBranches :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchSpec
      eraser
  eraserSpec :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserSpec
      eraser
  compactorSpec :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorSpec
      compactor

def StructuredPrefixDensifierComponentConstruction : Prop :=
  exists eraser compactor : MachineDescription,
    StructuredPrefixDensifierComponentSpec eraser compactor

theorem structuredPrefixDensifierComponentSpec_of_routes
    {eraser compactor : MachineDescription}
    (heraser :
      StructuredPrefixEraserRouteContracts.ExactRouteSpec eraser)
    (hcompactor :
      SelectedFootprintCompactorRouteContracts.ExactRouteSpec compactor) :
    StructuredPrefixDensifierComponentSpec eraser compactor := by
  have hcases :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseSpec
        eraser :=
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseSpec_of_structuredPrefixRoute
      heraser
  have hbranches :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchSpec
        eraser :=
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchSpec_of_branchCaseSpec
      hcases
  have heraserSpec :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserSpec
        eraser :=
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserSpec_of_branchSpec
      hbranches
  have hcompactorSpec :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorSpec
        compactor :=
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorSpec_of_selectedFootprintRoute
      hcompactor
  exact
    { structuredPrefixRoute := heraser
      selectedFootprintRoute := hcompactor
      eraserBranchCases := hcases
      eraserBranches := hbranches
      eraserSpec := heraserSpec
      compactorSpec := hcompactorSpec }

theorem structuredPrefixDensifierComponentConstruction_of_routes
    (heraser :
      StructuredPrefixEraserRouteContracts.ExactRouteConstruction)
    (hcompactor :
      SelectedFootprintCompactorRouteContracts.ExactRouteConstruction) :
    StructuredPrefixDensifierComponentConstruction := by
  rcases heraser with ⟨eraser, heraserSpec⟩
  rcases hcompactor with ⟨compactor, hcompactorSpec⟩
  exact
    ⟨eraser, compactor,
      structuredPrefixDensifierComponentSpec_of_routes
        heraserSpec hcompactorSpec⟩

theorem structuredPrefixDensifierComponentConstruction_core :
    StructuredPrefixDensifierComponentConstruction :=
  structuredPrefixDensifierComponentConstruction_of_routes
    StructuredPrefixEraserRouteContracts.exactRouteConstruction_core
    SelectedFootprintCompactorRouteContracts.exactRouteConstruction_core

theorem structuredPrefixEraserConstruction_of_componentRoute
    (hroute : StructuredPrefixDensifierComponentConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserConstruction := by
  rcases hroute with ⟨eraser, _compactor, hspec⟩
  exact ⟨eraser, hspec.eraserSpec⟩

theorem footprintCompactorConstruction_of_componentRoute
    (hroute : StructuredPrefixDensifierComponentConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction := by
  rcases hroute with ⟨_eraser, compactor, hspec⟩
  exact ⟨compactor, hspec.compactorSpec⟩

theorem structuredPrefixDensifierComponentsConstruction_of_componentRoute
    (hroute : StructuredPrefixDensifierComponentConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierComponentsConstruction := by
  exact
    ⟨structuredPrefixEraserConstruction_of_componentRoute hroute,
      footprintCompactorConstruction_of_componentRoute hroute⟩

theorem structuredPrefixDensifierConstruction_of_componentRoute
    (hroute : StructuredPrefixDensifierComponentConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction :=
  countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction_of_components
    (structuredPrefixDensifierComponentsConstruction_of_componentRoute
      hroute)

theorem structuredPrefixCleanupConstruction_of_componentRoute
    (hroute : StructuredPrefixDensifierComponentConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction :=
  countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction_of_densifier
    (structuredPrefixDensifierConstruction_of_componentRoute hroute)

theorem structuredPrefixDecoderConstruction_of_componentRoute
    (hroute : StructuredPrefixDensifierComponentConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction :=
  countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction_of_cleanup
    (structuredPrefixCleanupConstruction_of_componentRoute hroute)

theorem segmentNormalizerConstruction_of_componentRoute
    (hroute : StructuredPrefixDensifierComponentConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction :=
  countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_of_structuredPrefixSelectedSegmentDecoder
    (structuredPrefixDecoderConstruction_of_componentRoute hroute)

theorem structuredPrefixDensifierConstruction_core :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction :=
  structuredPrefixDensifierConstruction_of_componentRoute
    structuredPrefixDensifierComponentConstruction_core

theorem structuredPrefixCleanupConstruction_core :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction :=
  structuredPrefixCleanupConstruction_of_componentRoute
    structuredPrefixDensifierComponentConstruction_core

theorem structuredPrefixDecoderConstruction_core :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction :=
  structuredPrefixDecoderConstruction_of_componentRoute
    structuredPrefixDensifierComponentConstruction_core

theorem segmentNormalizerConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction :=
  segmentNormalizerConstruction_of_componentRoute
    structuredPrefixDensifierComponentConstruction_core

/-!
## Output selected-decoder component route
-/

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseOutputSpec_of_structuredPrefixOutputRoute
    {eraser : MachineDescription}
    (hroute :
      StructuredPrefixEraserRouteContracts.OutputRouteSpec eraser) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseOutputSpec
      eraser :=
  countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseOutputSpec_of_twoTapeStructuredPrefixEraserOutput
    hroute.eraserOutput

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserOutputSpec_of_structuredPrefixOutputRoute
    {eraser : MachineDescription}
    (hroute :
      StructuredPrefixEraserRouteContracts.OutputRouteSpec eraser) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserOutputSpec
      eraser :=
  countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserOutputSpec_of_branchesOutput
    (countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchOutputSpec_of_casesOutput
      (countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseOutputSpec_of_structuredPrefixOutputRoute
        hroute))

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorOutputSpec_of_selectedFootprintOutputRoute
    {compactor : MachineDescription}
    (hroute :
      SelectedFootprintCompactorRouteContracts.OutputRouteSpec
        compactor) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorOutputSpec
      compactor :=
  countWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorOutputSpec_of_generic
    hroute.footprintOutput

structure StructuredPrefixOutputComponentSpec
    (eraser compactor : MachineDescription) : Prop where
  structuredPrefixOutputRoute :
    StructuredPrefixEraserRouteContracts.OutputRouteSpec eraser
  selectedFootprintOutputRoute :
    SelectedFootprintCompactorRouteContracts.OutputRouteSpec compactor
  eraserBranchCasesOutput :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseOutputSpec
      eraser
  eraserBranchesOutput :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchOutputSpec
      eraser
  eraserOutput :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserOutputSpec
      eraser
  compactorOutput :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorOutputSpec
      compactor

def StructuredPrefixOutputComponentConstruction : Prop :=
  exists eraser compactor : MachineDescription,
    StructuredPrefixOutputComponentSpec eraser compactor

theorem structuredPrefixOutputComponentSpec_of_outputRoutes
    {eraser compactor : MachineDescription}
    (heraser :
      StructuredPrefixEraserRouteContracts.OutputRouteSpec eraser)
    (hcompactor :
      SelectedFootprintCompactorRouteContracts.OutputRouteSpec compactor) :
    StructuredPrefixOutputComponentSpec eraser compactor := by
  have hcases :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseOutputSpec
        eraser :=
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseOutputSpec_of_structuredPrefixOutputRoute
      heraser
  have hbranches :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchOutputSpec
        eraser :=
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchOutputSpec_of_casesOutput
      hcases
  have heraserOutput :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserOutputSpec
        eraser :=
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserOutputSpec_of_branchesOutput
      hbranches
  have hcompactorOutput :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorOutputSpec
        compactor :=
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorOutputSpec_of_selectedFootprintOutputRoute
      hcompactor
  exact
    { structuredPrefixOutputRoute := heraser
      selectedFootprintOutputRoute := hcompactor
      eraserBranchCasesOutput := hcases
      eraserBranchesOutput := hbranches
      eraserOutput := heraserOutput
      compactorOutput := hcompactorOutput }

theorem structuredPrefixOutputComponentSpec_of_exactComponentSpec
    {eraser compactor : MachineDescription}
    (hcomponent :
      StructuredPrefixDensifierComponentSpec eraser compactor) :
    StructuredPrefixOutputComponentSpec eraser compactor :=
  structuredPrefixOutputComponentSpec_of_outputRoutes
    (StructuredPrefixEraserRouteContracts.outputRouteSpec_of_exactRouteSpec
      hcomponent.structuredPrefixRoute)
    (SelectedFootprintCompactorRouteContracts.outputRouteSpec_of_exactRouteSpec
      hcomponent.selectedFootprintRoute)

theorem structuredPrefixOutputComponentConstruction_of_exactComponent
    (hcomponent : StructuredPrefixDensifierComponentConstruction) :
    StructuredPrefixOutputComponentConstruction := by
  rcases hcomponent with ⟨eraser, compactor, hspec⟩
  exact
    ⟨eraser, compactor,
      structuredPrefixOutputComponentSpec_of_exactComponentSpec hspec⟩

theorem structuredPrefixOutputComponentConstruction_core :
    StructuredPrefixOutputComponentConstruction :=
  structuredPrefixOutputComponentConstruction_of_exactComponent
    structuredPrefixDensifierComponentConstruction_core

theorem structuredPrefixEraserOutputConstruction_of_outputComponentRoute
    (hroute : StructuredPrefixOutputComponentConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserOutputConstruction := by
  rcases hroute with ⟨eraser, _compactor, hspec⟩
  exact ⟨eraser, hspec.eraserOutput⟩

theorem footprintCompactorOutputConstruction_of_outputComponentRoute
    (hroute : StructuredPrefixOutputComponentConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorOutputConstruction := by
  rcases hroute with ⟨_eraser, compactor, hspec⟩
  exact ⟨compactor, hspec.compactorOutput⟩

theorem structuredPrefixDensifierOutputConstruction_of_exactComponentRoute
    (hroute : StructuredPrefixDensifierComponentConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierOutputConstruction :=
  countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierOutputConstruction_of_exact
    (structuredPrefixDensifierConstruction_of_componentRoute hroute)

theorem structuredPrefixCleanupOutputConstruction_of_exactComponentRoute
    (hroute : StructuredPrefixDensifierComponentConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupOutputConstruction :=
  countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupOutputConstruction_of_exact
    (structuredPrefixCleanupConstruction_of_componentRoute hroute)

theorem structuredPrefixDecoderOutputConstruction_of_exactComponentRoute
    (hroute : StructuredPrefixDensifierComponentConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixOutputConstruction :=
  countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixOutputConstruction_of_exact
    (structuredPrefixDecoderConstruction_of_componentRoute hroute)

theorem segmentNormalizerOutputConstruction_of_exactComponentRoute
    (hroute : StructuredPrefixDensifierComponentConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerOutputConstruction :=
  countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerOutputConstruction_of_exact
    (segmentNormalizerConstruction_of_componentRoute hroute)

theorem structuredPrefixDensifierOutputConstruction_core :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierOutputConstruction :=
  structuredPrefixDensifierOutputConstruction_of_exactComponentRoute
    structuredPrefixDensifierComponentConstruction_core

theorem structuredPrefixCleanupOutputConstruction_core :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupOutputConstruction :=
  structuredPrefixCleanupOutputConstruction_of_exactComponentRoute
    structuredPrefixDensifierComponentConstruction_core

theorem structuredPrefixDecoderOutputConstruction_core :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixOutputConstruction :=
  structuredPrefixDecoderOutputConstruction_of_exactComponentRoute
    structuredPrefixDensifierComponentConstruction_core

theorem segmentNormalizerOutputConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerOutputConstruction :=
  segmentNormalizerOutputConstruction_of_exactComponentRoute
    structuredPrefixDensifierComponentConstruction_core

end CountWindowSelectedDecoderRouteContracts

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters
end Computability
end FoC
