import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.Mat.Output

set_option doc.verso true

/-!
# Scratch-extension output endpoints

This module records normalized-output views for the post-padding scratch
extension boundary.  The exact scratch-extension and count-window materializer
contracts remain the primary executable boundary; these weaker contracts are
for downstream routes that only consume the decoded output word and can ignore
the final cursor location.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

open CanonicalLayouts.DovetailLayoutScanner

private theorem haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
    {D : MachineDescription} {Tin Tout : Tape Bool}
    (h : D.HaltsFromTapeEquiv Tin Tout) :
    D.HaltsFromTapeWithOutput Tin (Tape.normalizedOutput Tout) :=
  MachineDescription.haltsFromTapeWithOutput_of_haltsFromTapeEquiv h

def CountWindowPostFieldDecodedPrefixScanSourceMaterializerOutputSpec
    (useAccept : Bool)
    (materializer : MachineDescription) : Prop :=
  materializer.SubroutineReady ∧
    forall (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
      (deletedTail : Word Bool),
      configurationFieldBits L.acceptConfig [] =
          false :: deletedTail ->
      countWindowPostFieldDecodedPrefixMaterializerPayload
          useAccept L =
        List.append pref [leftBit] ->
      materializer.HaltsFromTapeWithOutput
        (countWindowPostFieldDecodedPrefixMaterializerSourceTape
          useAccept L pref leftBit deletedTail)
        (Tape.normalizedOutput
          (postFieldDecodedPrefixScanSourceTape useAccept L))

def CountWindowPostFieldDecodedPrefixScanSourceMaterializerOutputConstruction :
    Prop :=
  forall useAccept : Bool,
  exists materializer : MachineDescription,
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerOutputSpec
      useAccept materializer

def RejectPostFieldDecodedPrefixScanSourceOutputSpec
    (materializer : MachineDescription) : Prop :=
  materializer.SubroutineReady ∧
    forall (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
      (deletedTail : Word Bool),
      configurationFieldBits L.acceptConfig [] =
          false :: deletedTail ->
      selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayload
          L =
        List.append pref [leftBit] ->
      materializer.HaltsFromTapeWithOutput
        (rejectPostFieldDecodedPrefixRestorerSourceTape
          L pref leftBit deletedTail)
        (Tape.normalizedOutput
          (postFieldDecodedPrefixScanSourceTape false L))

def RejectPostFieldDecodedPrefixScanSourceOutputConstruction : Prop :=
  exists materializer : MachineDescription,
    RejectPostFieldDecodedPrefixScanSourceOutputSpec materializer

def AcceptPostFieldRewoundToDecodedPrefixScanSourceOutputSpec
    (materializer : MachineDescription) : Prop :=
  materializer.SubroutineReady ∧
    forall (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
      (deletedTail : Word Bool),
      configurationFieldBits L.acceptConfig [] =
          false :: deletedTail ->
      selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload
          L =
        List.append pref [leftBit] ->
      materializer.HaltsFromTapeWithOutput
        (acceptPostFieldHandoffAfterRightEdgeRewindTape
          L pref leftBit deletedTail)
        (Tape.normalizedOutput
          (acceptPostFieldDecodedPrefixScanSourceTape L))

def AcceptPostFieldRewoundToDecodedPrefixScanSourceOutputConstruction :
    Prop :=
  exists materializer : MachineDescription,
    AcceptPostFieldRewoundToDecodedPrefixScanSourceOutputSpec materializer

def SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerOutputSpec
    (useAccept : Bool) (materializer : MachineDescription) : Prop :=
  materializer.SubroutineReady ∧
    forall L : DovetailLayout,
      materializer.HaltsFromTapeWithOutput
        (selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
          useAccept L 0)
        (Tape.normalizedOutput
          (selectedProjectionPaddedTailCleanupScratchCountCounterSourceTapeWithPostCountTail
            useAccept L 0))

def SelectedProjectionPaddedTailCleanupScratchCountWindowRestorerOutputSpec
    (useAccept : Bool) (restorer : MachineDescription) : Prop :=
  restorer.SubroutineReady ∧
    forall L : DovetailLayout,
      restorer.HaltsFromTapeWithOutput
        (selectedProjectionPaddedTailCleanupScratchCountCounterTargetTapeWithPostCountTail
          useAccept L 0)
        (Tape.normalizedOutput
          (selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
            useAccept L
            (selectedProjectionPaddedTailCleanupScratchCountBits
              useAccept L).length))

def SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerOutputConstruction :
    Prop :=
  forall useAccept : Bool,
    exists materializer : MachineDescription,
      SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerOutputSpec
        useAccept materializer

def SelectedProjectionPaddedTailCleanupScratchCountWindowRestorerOutputConstruction :
    Prop :=
  forall useAccept : Bool,
    exists restorer : MachineDescription,
      SelectedProjectionPaddedTailCleanupScratchCountWindowRestorerOutputSpec
        useAccept restorer

def SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerOutputConstruction :
    Prop :=
  forall useAccept : Bool,
    exists materializer : MachineDescription,
    exists restorer : MachineDescription,
      SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerOutputSpec
        useAccept materializer ∧
      SelectedProjectionPaddedTailCleanupScratchCountWindowRestorerOutputSpec
        useAccept restorer

def SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderOutputSpec
    (useAccept : Bool) (extender : MachineDescription) : Prop :=
  extender.SubroutineReady ∧
    forall L : DovetailLayout,
      extender.HaltsFromTapeWithOutput
        (selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
          useAccept L 0)
        (Tape.normalizedOutput
          (selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
            useAccept L
            (selectedProjectionPaddedTailCleanupScratchCountBits
              useAccept L).length))

def SelectedProjectionPaddedTailCleanupScratchExtOutputSpec
    (useAccept : Bool) (extender : MachineDescription) : Prop :=
  extender.SubroutineReady ∧
    forall L : DovetailLayout,
      extender.HaltsFromTapeWithOutput
        (selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
          useAccept L 0)
        (Tape.normalizedOutput
          (selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
            useAccept L
            (selectedProjectionPaddedTailCleanupSentinelExtraScratch
              useAccept L)))

def SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputSpec
    (useAccept : Bool) (allocator : MachineDescription) : Prop :=
  allocator.SubroutineReady ∧
    forall L : DovetailLayout,
      allocator.HaltsFromTapeWithOutput
        (selectedProjectionPaddedTailCleanupBaseSourceTape useAccept L)
        (Tape.normalizedOutput
          (selectedProjectionPaddedTailCleanupLayoutScratchSourceTape
            useAccept L))

def SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderOutputConstruction :
    Prop :=
  forall useAccept : Bool,
    exists extender : MachineDescription,
      SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderOutputSpec
        useAccept extender

def SelectedProjectionPaddedTailCleanupScratchExtOutputConstruction :
    Prop :=
  forall useAccept : Bool,
    exists extender : MachineDescription,
      SelectedProjectionPaddedTailCleanupScratchExtOutputSpec
        useAccept extender

def SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputConstruction :
    Prop :=
  forall useAccept : Bool,
    exists allocator : MachineDescription,
      SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputSpec
        useAccept allocator

theorem countWindowPostFieldDecodedPrefixScanSourceMaterializerOutputSpec_of_exact
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixScanSourceMaterializerSpec
        useAccept materializer) :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerOutputSpec
      useAccept materializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro L pref leftBit deletedTail hdeleted hpayload
  exact
    haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
      (hrun L pref leftBit deletedTail hdeleted hpayload)

theorem countWindowPostFieldDecodedPrefixScanSourceMaterializerOutputConstruction_of_exact
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction) :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerOutputConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      countWindowPostFieldDecodedPrefixScanSourceMaterializerOutputSpec_of_exact
        hspec⟩

theorem rejectPostFieldDecodedPrefixScanSourceOutputSpec_of_exact
    {materializer : MachineDescription}
    (hmaterializer :
      RejectPostFieldDecodedPrefixScanSourceSpec materializer) :
    RejectPostFieldDecodedPrefixScanSourceOutputSpec materializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro L pref leftBit deletedTail hdeleted hpayload
  exact
    haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
      (hrun L pref leftBit deletedTail hdeleted hpayload)

theorem rejectPostFieldDecodedPrefixScanSourceOutputConstruction_of_exact
    (hmaterializer :
      RejectPostFieldDecodedPrefixScanSourceConstruction) :
    RejectPostFieldDecodedPrefixScanSourceOutputConstruction := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      rejectPostFieldDecodedPrefixScanSourceOutputSpec_of_exact hspec⟩

theorem acceptPostFieldRewoundToDecodedPrefixScanSourceOutputSpec_of_exact
    {materializer : MachineDescription}
    (hmaterializer :
      AcceptPostFieldRewoundToDecodedPrefixScanSourceSpec materializer) :
    AcceptPostFieldRewoundToDecodedPrefixScanSourceOutputSpec
      materializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro L pref leftBit deletedTail hdeleted hpayload
  exact
    haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
      (hrun L pref leftBit deletedTail hdeleted hpayload)

theorem acceptPostFieldRewoundToDecodedPrefixScanSourceOutputConstruction_of_exact
    (hmaterializer :
      AcceptPostFieldRewoundToDecodedPrefixScanSourceConstruction) :
    AcceptPostFieldRewoundToDecodedPrefixScanSourceOutputConstruction := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      acceptPostFieldRewoundToDecodedPrefixScanSourceOutputSpec_of_exact
        hspec⟩

theorem rejectPostFieldDecodedPrefixScanSourceOutputSpec_of_countWindowMaterializerOutputSpec
    {materializer : MachineDescription}
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixScanSourceMaterializerOutputSpec
        false materializer) :
    RejectPostFieldDecodedPrefixScanSourceOutputSpec materializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro L pref leftBit deletedTail hdeleted hpayload
  simpa [
    countWindowPostFieldDecodedPrefixMaterializerPayload_false,
    countWindowPostFieldDecodedPrefixMaterializerSourceTape_false] using
    hrun L pref leftBit deletedTail hdeleted hpayload

theorem rejectPostFieldDecodedPrefixScanSourceOutputConstruction_of_countWindowMaterializerOutput
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixScanSourceMaterializerOutputConstruction) :
    RejectPostFieldDecodedPrefixScanSourceOutputConstruction := by
  rcases hmaterializer false with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      rejectPostFieldDecodedPrefixScanSourceOutputSpec_of_countWindowMaterializerOutputSpec
        hspec⟩

theorem acceptPostFieldRewoundToDecodedPrefixScanSourceOutputSpec_of_countWindowMaterializerOutputSpec
    {materializer : MachineDescription}
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixScanSourceMaterializerOutputSpec
        true materializer) :
    AcceptPostFieldRewoundToDecodedPrefixScanSourceOutputSpec
      materializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro L pref leftBit deletedTail hdeleted hpayload
  simpa [
    acceptPostFieldDecodedPrefixScanSourceTape,
    countWindowPostFieldDecodedPrefixMaterializerPayload_true,
    countWindowPostFieldDecodedPrefixMaterializerSourceTape_true] using
    hrun L pref leftBit deletedTail hdeleted hpayload

theorem acceptPostFieldRewoundToDecodedPrefixScanSourceOutputConstruction_of_countWindowMaterializerOutput
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixScanSourceMaterializerOutputConstruction) :
    AcceptPostFieldRewoundToDecodedPrefixScanSourceOutputConstruction := by
  rcases hmaterializer true with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      acceptPostFieldRewoundToDecodedPrefixScanSourceOutputSpec_of_countWindowMaterializerOutputSpec
        hspec⟩

theorem selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerOutputSpec_of_exact
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerSpec
        useAccept materializer) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerOutputSpec
      useAccept materializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro L
  exact
    haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
      (hrun L)

theorem selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerOutputConstruction_of_exact
    (hmaterializer :
      SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerOutputConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerOutputSpec_of_exact
        hspec⟩

theorem selectedProjectionPaddedTailCleanupScratchCountWindowRestorerOutputSpec_of_exact
    {useAccept : Bool} {restorer : MachineDescription}
    (hrestorer :
      SelectedProjectionPaddedTailCleanupScratchCountWindowRestorerSpec
        useAccept restorer) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRestorerOutputSpec
      useAccept restorer := by
  rcases hrestorer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro L
  exact
    haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
      (hrun L)

theorem selectedProjectionPaddedTailCleanupScratchCountWindowRestorerOutputConstruction_of_exact
    (hrestorer :
      SelectedProjectionPaddedTailCleanupScratchCountWindowRestorerConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRestorerOutputConstruction := by
  intro useAccept
  rcases hrestorer useAccept with ⟨restorer, hspec⟩
  exact
    ⟨restorer,
      selectedProjectionPaddedTailCleanupScratchCountWindowRestorerOutputSpec_of_exact
        hspec⟩

theorem selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerOutputConstruction_of_exact
    (h :
      SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerOutputConstruction := by
  intro useAccept
  rcases h useAccept with
    ⟨materializer, restorer, hmaterializer, hrestorer⟩
  exact
    ⟨materializer, restorer,
      selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerOutputSpec_of_exact
        hmaterializer,
      selectedProjectionPaddedTailCleanupScratchCountWindowRestorerOutputSpec_of_exact
        hrestorer⟩

theorem selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerOutputConstruction_of_materializerAndRestorerOutput
    (h :
      SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerOutputConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerOutputConstruction := by
  intro useAccept
  rcases h useAccept with
    ⟨materializer, restorer, hmaterializer, hrestorer⟩
  exact ⟨materializer, hmaterializer⟩

theorem selectedProjectionPaddedTailCleanupScratchCountWindowRestorerOutputConstruction_of_materializerAndRestorerOutput
    (h :
      SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerOutputConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRestorerOutputConstruction := by
  intro useAccept
  rcases h useAccept with
    ⟨materializer, restorer, hmaterializer, hrestorer⟩
  exact ⟨restorer, hrestorer⟩

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderOutputSpec_of_exact
    {useAccept : Bool} {extender : MachineDescription}
    (hextender :
      SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderSpec
        useAccept extender) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderOutputSpec
      useAccept extender := by
  rcases hextender with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro L
  exact
    haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
      (hrun L)

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderOutputConstruction_of_exact
    (hextender :
      SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderOutputConstruction := by
  intro useAccept
  rcases hextender useAccept with ⟨extender, hspec⟩
  exact
    ⟨extender,
      selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderOutputSpec_of_exact
        hspec⟩

theorem selectedProjectionPaddedTailCleanupScratchExtOutputSpec_of_exact
    {useAccept : Bool} {extender : MachineDescription}
    (hextender :
      SelectedProjectionPaddedTailCleanupScratchExtSpec useAccept extender) :
    SelectedProjectionPaddedTailCleanupScratchExtOutputSpec
      useAccept extender := by
  rcases hextender with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro L
  exact
    haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
      (hrun L)

theorem selectedProjectionPaddedTailCleanupScratchExtOutputConstruction_of_exact
    (hextender :
      SelectedProjectionPaddedTailCleanupScratchExtConstruction) :
    SelectedProjectionPaddedTailCleanupScratchExtOutputConstruction := by
  intro useAccept
  rcases hextender useAccept with ⟨extender, hspec⟩
  exact
    ⟨extender,
      selectedProjectionPaddedTailCleanupScratchExtOutputSpec_of_exact
        hspec⟩

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputSpec_of_exact
    {useAccept : Bool} {allocator : MachineDescription}
    (hallocator :
      SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorSpec
        useAccept allocator) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputSpec
      useAccept allocator := by
  rcases hallocator with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro L
  exact
    haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
      (hrun L)

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputConstruction_of_exact
    (hallocator :
      SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputConstruction := by
  intro useAccept
  rcases hallocator useAccept with ⟨allocator, hspec⟩
  exact
    ⟨allocator,
      selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputSpec_of_exact
        hspec⟩

theorem selectedProjectionPaddedTailCleanupScratchExtOutputSpec_of_countExtenderOutputSpec
    {useAccept : Bool} {extender : MachineDescription}
    (hextender :
      SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderOutputSpec
        useAccept extender) :
    SelectedProjectionPaddedTailCleanupScratchExtOutputSpec
      useAccept extender := by
  rcases hextender with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro L
  simpa [selectedProjectionPaddedTailCleanupScratchCountBits_length]
    using hrun L

theorem selectedProjectionPaddedTailCleanupScratchExtOutputConstruction_of_countExtendersOutput
    (h :
      SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderOutputConstruction) :
    SelectedProjectionPaddedTailCleanupScratchExtOutputConstruction := by
  intro useAccept
  rcases h useAccept with ⟨extender, hextender⟩
  exact
    ⟨extender,
      selectedProjectionPaddedTailCleanupScratchExtOutputSpec_of_countExtenderOutputSpec
        hextender⟩

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputSpec_of_extenderOutputSpec
    {useAccept : Bool} {extender : MachineDescription}
    (hextender :
      SelectedProjectionPaddedTailCleanupScratchExtOutputSpec
        useAccept extender) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputSpec
      useAccept extender := by
  rcases hextender with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro L
  simpa [
    selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch_zero,
    selectedProjectionPaddedTailCleanupBaseSourceTapeWithLayoutExtraScratch]
    using hrun L

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputConstruction_of_extendersOutput
    (h :
      SelectedProjectionPaddedTailCleanupScratchExtOutputConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputConstruction := by
  intro useAccept
  rcases h useAccept with ⟨extender, hextender⟩
  exact
    ⟨extender,
      selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputSpec_of_extenderOutputSpec
        hextender⟩

theorem countWindowPostFieldDecodedPrefixScanSourceMaterializerOutputConstruction_bridgeCore :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerOutputConstruction :=
  countWindowPostFieldDecodedPrefixScanSourceMaterializerOutputConstruction_of_exact
    countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_bridgeCore

theorem countWindowPostFieldDecodedPrefixScanSourceMaterializerOutputConstruction_bridgeCore_of_selectedSegmentDecoder
    (hdecoder :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction) :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerOutputConstruction :=
  countWindowPostFieldDecodedPrefixScanSourceMaterializerOutputConstruction_of_exact
    (countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_bridgeCore_of_selectedSegmentDecoder
      hdecoder)

theorem countWindowPostFieldDecodedPrefixScanSourceMaterializerOutputConstruction_bridgeCore_of_prefixAndFootprintCases
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerOutputConstruction :=
  countWindowPostFieldDecodedPrefixScanSourceMaterializerOutputConstruction_of_exact
    (countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_bridgeCore_of_prefixAndFootprintCases
      hprefix hcases)

theorem countWindowPostFieldDecodedPrefixScanSourceMaterializerOutputConstruction_bridgeCore_of_prefixAndFootprintBitPaddingCases
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerOutputConstruction :=
  countWindowPostFieldDecodedPrefixScanSourceMaterializerOutputConstruction_bridgeCore_of_prefixAndFootprintCases
    hprefix
    (selectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction_of_bitPaddingCases
      hcases)

theorem scanSourceMaterializerOutput_bridgeCore_ofBranchFootprintCases
    (heraser :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerOutputConstruction :=
  countWindowPostFieldDecodedPrefixScanSourceMaterializerOutputConstruction_of_exact
    (scanSourceMaterializerConstruction_bridgeCore_ofBranchFootprintCases
      heraser hcases)

theorem rejectPostFieldDecodedPrefixScanSourceOutputConstruction_bridgeCore :
    RejectPostFieldDecodedPrefixScanSourceOutputConstruction :=
  rejectPostFieldDecodedPrefixScanSourceOutputConstruction_of_countWindowMaterializerOutput
    countWindowPostFieldDecodedPrefixScanSourceMaterializerOutputConstruction_bridgeCore

theorem acceptPostFieldRewoundToDecodedPrefixScanSourceOutputConstruction_bridgeCore :
    AcceptPostFieldRewoundToDecodedPrefixScanSourceOutputConstruction :=
  acceptPostFieldRewoundToDecodedPrefixScanSourceOutputConstruction_of_countWindowMaterializerOutput
    countWindowPostFieldDecodedPrefixScanSourceMaterializerOutputConstruction_bridgeCore

theorem selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerOutputConstruction_bridgeCore :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerOutputConstruction :=
  selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerOutputConstruction_of_exact
    selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction_bridgeCore

theorem selectedProjectionPaddedTailCleanupScratchCountWindowRestorerOutputConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRestorerOutputConstruction :=
  selectedProjectionPaddedTailCleanupScratchCountWindowRestorerOutputConstruction_of_exact
    selectedProjectionPaddedTailCleanupScratchCountWindowRestorerConstruction_core

theorem selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerOutputConstruction_bridgeCore :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerOutputConstruction :=
  selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerOutputConstruction_of_exact
    selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction_bridgeCore

theorem scratchCountMatRestOutput_bridgeCore_ofPrefixFootprintCases
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerOutputConstruction :=
  selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerOutputConstruction_of_exact
    (selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction_bridgeCore_of_prefixAndFootprintCases
      hprefix hcases)

theorem scratchCountMatRestOutput_bridgeCore_ofBranchFootprintCases
    (heraser :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerOutputConstruction :=
  selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerOutputConstruction_of_exact
    (scratchCountMatRestConstruction_bridgeCore_ofBranchFootprintCases
      heraser hcases)

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderOutputConstruction_bridgeCore :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderOutputConstruction :=
  selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderOutputConstruction_of_exact
    selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderOutputConstruction_of_prefixAndFootprintCases
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderOutputConstruction :=
  selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderOutputConstruction_of_exact
    (selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction_of_prefixAndFootprintCases
      hprefix hcases)

theorem scratchCountExtenderOutput_ofBranchFootprintCases
    (heraser :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderOutputConstruction :=
  selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderOutputConstruction_of_exact
    (scratchCountExtenderConstruction_ofBranchFootprintCases
      heraser hcases)

theorem selectedProjectionPaddedTailCleanupScratchExtOutputConstruction_bridgeCore :
    SelectedProjectionPaddedTailCleanupScratchExtOutputConstruction :=
  selectedProjectionPaddedTailCleanupScratchExtOutputConstruction_of_countExtendersOutput
    selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderOutputConstruction_bridgeCore

theorem selectedProjectionPaddedTailCleanupScratchExtOutputConstruction_of_prefixAndFootprintCases
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    SelectedProjectionPaddedTailCleanupScratchExtOutputConstruction :=
  selectedProjectionPaddedTailCleanupScratchExtOutputConstruction_of_countExtendersOutput
    (selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderOutputConstruction_of_prefixAndFootprintCases
      hprefix hcases)

theorem selectedProjectionPaddedTailCleanupScratchExtOutputConstruction_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
    (heraser :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionPaddedTailCleanupScratchExtOutputConstruction :=
  selectedProjectionPaddedTailCleanupScratchExtOutputConstruction_of_countExtendersOutput
    (scratchCountExtenderOutput_ofBranchFootprintCases
      heraser hcases)

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputConstruction_bridgeCore :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputConstruction :=
  selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputConstruction_of_extendersOutput
    selectedProjectionPaddedTailCleanupScratchExtOutputConstruction_bridgeCore

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputConstruction_of_prefixAndFootprintCases
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputConstruction :=
  selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputConstruction_of_extendersOutput
    (selectedProjectionPaddedTailCleanupScratchExtOutputConstruction_of_prefixAndFootprintCases
      hprefix hcases)

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputConstruction_of_prefixAndFootprintBitPaddingCases
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputConstruction :=
  selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputConstruction_of_prefixAndFootprintCases
    hprefix
    (selectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction_of_bitPaddingCases
      hcases)

theorem scratchAllocatorOutput_ofBranchFootprintCases
    (heraser :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputConstruction :=
  selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorOutputConstruction_of_extendersOutput
    (selectedProjectionPaddedTailCleanupScratchExtOutputConstruction_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
      heraser hcases)

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters
end Computability
end FoC
