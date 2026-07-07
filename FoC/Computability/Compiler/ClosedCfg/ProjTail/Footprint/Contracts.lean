import FoC.Computability.Compiler.ClosedCfg.ProjTail.SelectedFootprintCompactionBridgeOutput

set_option doc.verso true

/-!
# Selected-footprint compactor route contracts

This module packages the selected logical-tape decoder footprint compactor
frontier into route-level exact and output contracts.  The remaining
finite-machine leaf is still the right-end nil/cons split construction in
`SelectedFootprintCompaction.lean`; the route contracts below expose the same
leaf simultaneously through the right-end bridge, guarded footprint,
padding-split, and normalized-output views.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

namespace SelectedFootprintCompactorRouteContracts

/-!
## Reverse guarded and padding-split adapters

The main compaction module already adapts the guarded footprint interface to
the public right-end bridge.  These reverse adapters are useful for proofs that
begin at the current right-end split leaf but want to compose through the more
generic guarded or padding-aware surfaces.
-/

theorem guardedLogicalTapeDecoderFootprintCompactorSpec_of_bridgeSpec
    {compactor : MachineDescription}
    (hbridge : SelectedFootprintCompactorBridgeSpec compactor) :
    GuardedLogicalTapeDecoderFootprintCompactorSpec compactor := by
  rcases hbridge with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  simpa [
    selectedSegmentLogicalTapeDecoderFootprintSourceTape_eq_fromPayload,
    selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload_eq] using
    hrun bits padding

theorem guardedLogicalTapeDecoderFootprintCompactorConstruction_of_bridge
    (hbridge : SelectedFootprintCompactorBridgeConstruction) :
    GuardedLogicalTapeDecoderFootprintCompactorConstruction := by
  rcases hbridge with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      guardedLogicalTapeDecoderFootprintCompactorSpec_of_bridgeSpec
        hspec⟩

theorem selectedFootprintCompactorBridgeSpec_iff_guardedSpec
    (compactor : MachineDescription) :
    SelectedFootprintCompactorBridgeSpec compactor ↔
      GuardedLogicalTapeDecoderFootprintCompactorSpec compactor := by
  constructor
  · exact guardedLogicalTapeDecoderFootprintCompactorSpec_of_bridgeSpec
  · exact selectedFootprintCompactorBridgeSpec_of_guardedFootprintSpec

theorem selectedFootprintCompactorBridgeConstruction_iff_guardedConstruction :
    SelectedFootprintCompactorBridgeConstruction ↔
      GuardedLogicalTapeDecoderFootprintCompactorConstruction := by
  constructor
  · exact guardedLogicalTapeDecoderFootprintCompactorConstruction_of_bridge
  · exact selectedFootprintCompactorBridgeConstruction_of_guardedFootprint

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSpec_of_bridgeSpec
    {compactor : MachineDescription}
    (hbridge : SelectedFootprintCompactorBridgeSpec compactor) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSpec
      compactor :=
  selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSpec_of_guardedSpec
    (guardedLogicalTapeDecoderFootprintCompactorSpec_of_bridgeSpec
      hbridge)

theorem selectedFootprintCompactorBridgeSpec_of_paddingSplitSpec
    {compactor : MachineDescription}
    (hpadding :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSpec
        compactor) :
    SelectedFootprintCompactorBridgeSpec compactor :=
  selectedFootprintCompactorBridgeSpec_of_guardedFootprintSpec
    (guardedLogicalTapeDecoderFootprintCompactorSpec_of_paddingSplitSpec
      hpadding)

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorConstruction_of_bridge
    (hbridge : SelectedFootprintCompactorBridgeConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorConstruction := by
  rcases hbridge with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSpec_of_bridgeSpec
        hspec⟩

theorem selectedFootprintCompactorBridgeConstruction_of_paddingSplit
    (hpadding :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorConstruction) :
    SelectedFootprintCompactorBridgeConstruction := by
  rcases hpadding with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedFootprintCompactorBridgeSpec_of_paddingSplitSpec
        hspec⟩

theorem selectedFootprintCompactorBridgeConstruction_iff_paddingSplitConstruction :
    SelectedFootprintCompactorBridgeConstruction ↔
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorConstruction := by
  constructor
  · exact selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorConstruction_of_bridge
  · exact selectedFootprintCompactorBridgeConstruction_of_paddingSplit

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSpec_of_splitSpec
    {compactor : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitSpec
        compactor) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSpec
      compactor := by
  rcases hsplit with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  exact
    ⟨hready, hnilNil, hnilNone, hnilSome,
      hconsNil, hconsNone, hconsSome⟩

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorSplitPadSymbolCaseSpec_of_rightEndBridgeSpec
    {compactor : MachineDescription}
    (hright :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSpec
        compactor) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorSplitPadSymbolCaseSpec
      compactor := by
  rcases hright with
    ⟨hready, hnilNil, hnilNone, hnilSome, hconsNil,
      hconsNone, hconsSome⟩
  refine ⟨?_, ?_⟩
  · refine ⟨hready, ?_, ?_, ?_⟩
    · simpa [
        selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape,
        selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape] using
        hnilNil
    · intro padding
      simpa [
        selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape,
        selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape] using
        hnilNone padding
    · intro padBit padding
      simpa [
        selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape,
        selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape] using
        hnilSome padBit padding
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro bit rest
      simpa [
        selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape,
        selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape] using
        hconsNil bit rest
    · intro bit rest padding
      simpa [
        selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape,
        selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape] using
        hconsNone bit rest padding
    · intro bit rest padBit padding
      simpa [
        selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape,
        selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape] using
        hconsSome bit rest padBit padding

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorPadSymbolCaseSpec_of_splitPadSymbolCaseSpec
    {compactor : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorSplitPadSymbolCaseSpec
        compactor) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorPadSymbolCaseSpec
      compactor := by
  rcases hsplit with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  exact
    ⟨hready, hnilNil, hnilNone, hnilSome,
      hconsNil, hconsNone, hconsSome⟩

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseSpec_of_padSymbolCaseSpec
    {compactor : MachineDescription}
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorPadSymbolCaseSpec
        compactor) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseSpec
      compactor := by
  rcases hcases with
    ⟨hready, hnilNil, hnilNone, hnilSome, hconsNil,
      hconsNone, hconsSome⟩
  refine ⟨hready, hnilNil, ?_, hconsNil, ?_⟩
  · intro pad padding
    cases pad with
    | none =>
        exact hnilNone padding
    | some padBit =>
        exact hnilSome padBit padding
  · intro bit rest pad padding
    cases pad with
    | none =>
        exact hconsNone bit rest padding
    | some padBit =>
        exact hconsSome bit rest padBit padding

/-!
## Exact route package
-/

structure ExactRouteSpec
    (compactor : MachineDescription) : Prop where
  rightEndSplit :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitSpec
      compactor
  rightEnd :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSpec
      compactor
  bridge : SelectedFootprintCompactorBridgeSpec compactor
  footprint :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorSpec compactor
  guarded : GuardedLogicalTapeDecoderFootprintCompactorSpec compactor
  guardedSplit : GuardedLogicalTapeDecoderFootprintCompactorSplitSpec compactor
  paddingSplit :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSpec
      compactor
  paddingSplitCases :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitSpec
      compactor
  rightEndNil :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeNilSpec
      compactor
  rightEndCons :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConsSpec
      compactor
  footprintPadSymbol :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorSplitPadSymbolCaseSpec
      compactor
  footprintPadSymbolFlat :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorPadSymbolCaseSpec
      compactor
  footprintBitPadding :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseSpec
      compactor

def ExactRouteConstruction : Prop :=
  exists compactor : MachineDescription,
    ExactRouteSpec compactor

theorem exactRouteSpec_of_rightEndSplitSpec
    {compactor : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitSpec
        compactor) :
    ExactRouteSpec compactor := by
  have hright :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSpec
        compactor :=
    selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSpec_of_splitSpec
      hsplit
  have hbridge : SelectedFootprintCompactorBridgeSpec compactor :=
    selectedFootprintCompactorBridgeSpec_of_rightEndBridgeSplitSpec
      hsplit
  have hcompactor :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorSpec compactor :=
    selectedSegmentLogicalTapeDecoderFootprintCompactorSpec_of_bridgeSpec
      hbridge
  have hguard :
      GuardedLogicalTapeDecoderFootprintCompactorSpec compactor :=
    guardedLogicalTapeDecoderFootprintCompactorSpec_of_bridgeSpec
      hbridge
  have hguardSplit :
      GuardedLogicalTapeDecoderFootprintCompactorSplitSpec compactor :=
    guardedLogicalTapeDecoderFootprintCompactorSplitSpec_of_spec
      hguard
  have hpadding :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSpec
        compactor :=
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSpec_of_guardedSpec
      hguard
  have hpaddingSplit :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitSpec
        compactor :=
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitSpec_of_spec
      hpadding
  have hrightNil :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeNilSpec
        compactor := hsplit.left
  have hrightCons :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConsSpec
        compactor := hsplit.right
  have hpadSymbol :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorSplitPadSymbolCaseSpec
        compactor := by
    exact
      selectedSegmentLogicalTapeDecoderFootprintCompactorSplitPadSymbolCaseSpec_of_rightEndBridgeSpec
        hright
  have hpadSymbolFlat :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorPadSymbolCaseSpec
        compactor := by
    exact
      selectedSegmentLogicalTapeDecoderFootprintCompactorPadSymbolCaseSpec_of_splitPadSymbolCaseSpec
        hpadSymbol
  have hbitPadding :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseSpec
        compactor := by
    exact
      selectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseSpec_of_padSymbolCaseSpec
        hpadSymbolFlat
  exact
    { rightEndSplit := hsplit
      rightEnd := hright
      bridge := hbridge
      footprint := hcompactor
      guarded := hguard
      guardedSplit := hguardSplit
      paddingSplit := hpadding
      paddingSplitCases := hpaddingSplit
      rightEndNil := hrightNil
      rightEndCons := hrightCons
      footprintPadSymbol := hpadSymbol
      footprintPadSymbolFlat := hpadSymbolFlat
      footprintBitPadding := hbitPadding }

theorem exactRouteSpec_of_rightEndBridgeSpec
    {compactor : MachineDescription}
    (hright :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSpec
        compactor) :
    ExactRouteSpec compactor :=
  exactRouteSpec_of_rightEndSplitSpec
    (selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitSpec_of_bridgeSpec
      (selectedFootprintCompactorBridgeSpec_of_rightEndBridgeSpec hright))

theorem exactRouteSpec_of_bridgeSpec
    {compactor : MachineDescription}
    (hbridge : SelectedFootprintCompactorBridgeSpec compactor) :
    ExactRouteSpec compactor :=
  exactRouteSpec_of_rightEndSplitSpec
    (selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitSpec_of_bridgeSpec
      hbridge)

theorem exactRouteSpec_of_compactorSpec
    {compactor : MachineDescription}
    (hcompactor :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorSpec compactor) :
    ExactRouteSpec compactor :=
  exactRouteSpec_of_bridgeSpec
    (selectedFootprintCompactorBridgeSpec_of_compactorSpec hcompactor)

theorem exactRouteSpec_of_guardedSpec
    {compactor : MachineDescription}
    (hguard : GuardedLogicalTapeDecoderFootprintCompactorSpec compactor) :
    ExactRouteSpec compactor :=
  exactRouteSpec_of_bridgeSpec
    (selectedFootprintCompactorBridgeSpec_of_guardedFootprintSpec hguard)

theorem exactRouteSpec_of_paddingSplitSpec
    {compactor : MachineDescription}
    (hpadding :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSpec
        compactor) :
    ExactRouteSpec compactor :=
  exactRouteSpec_of_guardedSpec
    (guardedLogicalTapeDecoderFootprintCompactorSpec_of_paddingSplitSpec
      hpadding)

theorem exactRouteConstruction_of_rightEndSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitConstruction) :
    ExactRouteConstruction := by
  rcases hsplit with ⟨compactor, hspec⟩
  exact ⟨compactor, exactRouteSpec_of_rightEndSplitSpec hspec⟩

theorem rightEndSplitConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitConstruction := by
  rcases hroute with ⟨compactor, hspec⟩
  exact ⟨compactor, hspec.rightEndSplit⟩

theorem exactRouteConstruction_iff_rightEndSplitConstruction :
    ExactRouteConstruction ↔
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitConstruction := by
  constructor
  · exact rightEndSplitConstruction_of_exactRoute
  · exact exactRouteConstruction_of_rightEndSplit

theorem exactRouteConstruction_of_bridge
    (hbridge : SelectedFootprintCompactorBridgeConstruction) :
    ExactRouteConstruction := by
  rcases hbridge with ⟨compactor, hspec⟩
  exact ⟨compactor, exactRouteSpec_of_bridgeSpec hspec⟩

theorem bridgeConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    SelectedFootprintCompactorBridgeConstruction := by
  rcases hroute with ⟨compactor, hspec⟩
  exact ⟨compactor, hspec.bridge⟩

theorem exactRouteConstruction_iff_bridgeConstruction :
    ExactRouteConstruction ↔ SelectedFootprintCompactorBridgeConstruction := by
  constructor
  · exact bridgeConstruction_of_exactRoute
  · exact exactRouteConstruction_of_bridge

theorem exactRouteConstruction_of_guarded
    (hguard : GuardedLogicalTapeDecoderFootprintCompactorConstruction) :
    ExactRouteConstruction := by
  rcases hguard with ⟨compactor, hspec⟩
  exact ⟨compactor, exactRouteSpec_of_guardedSpec hspec⟩

theorem guardedConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    GuardedLogicalTapeDecoderFootprintCompactorConstruction := by
  rcases hroute with ⟨compactor, hspec⟩
  exact ⟨compactor, hspec.guarded⟩

theorem exactRouteConstruction_iff_guardedConstruction :
    ExactRouteConstruction ↔
      GuardedLogicalTapeDecoderFootprintCompactorConstruction := by
  constructor
  · exact guardedConstruction_of_exactRoute
  · exact exactRouteConstruction_of_guarded

theorem exactRouteConstruction_of_paddingSplit
    (hpadding :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorConstruction) :
    ExactRouteConstruction := by
  rcases hpadding with ⟨compactor, hspec⟩
  exact ⟨compactor, exactRouteSpec_of_paddingSplitSpec hspec⟩

theorem paddingSplitConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorConstruction := by
  rcases hroute with ⟨compactor, hspec⟩
  exact ⟨compactor, hspec.paddingSplit⟩

theorem exactRouteConstruction_iff_paddingSplitConstruction :
    ExactRouteConstruction ↔
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorConstruction := by
  constructor
  · exact paddingSplitConstruction_of_exactRoute
  · exact exactRouteConstruction_of_paddingSplit

theorem exactRouteConstruction_core :
    ExactRouteConstruction :=
  exactRouteConstruction_of_rightEndSplit
    selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitConstruction_core

/-!
## Output route package
-/

structure OutputRouteSpec
    (compactor : MachineDescription) : Prop where
  bridgeOutput : SelectedFootprintCompactorBridgeOutputSpec compactor
  bridgeOutputCases :
    SelectedFootprintCompactorBridgeOutputCaseSpec compactor
  bridgeOutputBitPadding :
    SelectedFootprintCompactorBridgeOutputBitPaddingCaseSpec compactor
  bridgeOutputSplitPadSymbol :
    SelectedFootprintCompactorBridgeOutputSplitPadSymbolCaseSpec compactor
  bridgeOutputNil :
    SelectedFootprintCompactorBridgeOutputNilPadSymbolCaseSpec compactor
  bridgeOutputCons :
    SelectedFootprintCompactorBridgeOutputConsPadSymbolCaseSpec compactor
  footprintOutput :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorOutputSpec
      compactor
  rightEndOutput :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeOutputSpec
      compactor
  rightEndSplitOutput :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitOutputSpec
      compactor
  guardedOutput :
    GuardedLogicalTapeDecoderFootprintCompactorOutputSpec compactor
  paddingSplitOutput :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputSpec
      compactor
  paddingSplitCaseOutput :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorCaseOutputSpec
      compactor
  paddingSplitBitPaddingOutput :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorBitPaddingCaseOutputSpec
      compactor
  paddingSplitSplitOutput :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitPadSymbolCaseOutputSpec
      compactor

def OutputRouteConstruction : Prop :=
  exists compactor : MachineDescription,
    OutputRouteSpec compactor

theorem outputRouteSpec_of_bridgeOutputSpec
    {compactor : MachineDescription}
    (hbridge : SelectedFootprintCompactorBridgeOutputSpec compactor) :
    OutputRouteSpec compactor := by
  have hbridgeSplit :
      SelectedFootprintCompactorBridgeOutputSplitPadSymbolCaseSpec
        compactor :=
    selectedFootprintCompactorBridgeOutputSplitPadSymbolCaseSpec_of_outputSpec
      hbridge
  have hbridgeBit :
      SelectedFootprintCompactorBridgeOutputBitPaddingCaseSpec compactor :=
    selectedFootprintCompactorBridgeOutputBitPaddingCaseSpec_of_splitPadSymbolCaseSpec
      hbridgeSplit
  have hbridgeCase :
      SelectedFootprintCompactorBridgeOutputCaseSpec compactor :=
    selectedFootprintCompactorBridgeOutputCaseSpec_of_bitPaddingCaseSpec
      hbridgeBit
  have hfootprint :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorOutputSpec
        compactor :=
    selectedSegmentLogicalTapeDecoderFootprintCompactorOutputSpec_of_bridgeOutputSpec
      hbridge
  have hright :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeOutputSpec
        compactor :=
    selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeOutputSpec_of_bridgeOutputSpec
      hbridge
  have hrightSplit :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitOutputSpec
        compactor :=
    selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitOutputSpec_of_bridgeOutputSpec
      hbridge
  have hguard :
      GuardedLogicalTapeDecoderFootprintCompactorOutputSpec compactor := by
    rcases hbridge with ⟨hready, hrun⟩
    refine ⟨hready, ?_⟩
    intro bits padding
    simpa [
      selectedSegmentLogicalTapeDecoderFootprintSourceTape_eq_fromPayload,
      selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload_eq] using
      hrun bits padding
  have hpadding :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputSpec
        compactor :=
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputSpec_of_guardedOutputSpec
      hguard
  have hpaddingSplit :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitPadSymbolCaseOutputSpec
        compactor :=
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitPadSymbolCaseOutputSpec_of_outputSpec
      hpadding
  have hpaddingBit :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorBitPaddingCaseOutputSpec
        compactor :=
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorBitPaddingCaseOutputSpec_of_splitPadSymbolCaseOutputSpec
      hpaddingSplit
  have hpaddingCase :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorCaseOutputSpec
        compactor :=
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorCaseOutputSpec_of_bitPaddingCaseOutputSpec
      hpaddingBit
  exact
    { bridgeOutput := hbridge
      bridgeOutputCases := hbridgeCase
      bridgeOutputBitPadding := hbridgeBit
      bridgeOutputSplitPadSymbol := hbridgeSplit
      bridgeOutputNil :=
        SelectedFootprintCompactorBridgeOutputSplitPadSymbolCaseSpec.nilSpec
          hbridgeSplit
      bridgeOutputCons :=
        SelectedFootprintCompactorBridgeOutputSplitPadSymbolCaseSpec.consSpec
          hbridgeSplit
      footprintOutput := hfootprint
      rightEndOutput := hright
      rightEndSplitOutput := hrightSplit
      guardedOutput := hguard
      paddingSplitOutput := hpadding
      paddingSplitCaseOutput := hpaddingCase
      paddingSplitBitPaddingOutput := hpaddingBit
      paddingSplitSplitOutput := hpaddingSplit }

theorem outputRouteSpec_of_exactRouteSpec
    {compactor : MachineDescription}
    (hroute : ExactRouteSpec compactor) :
    OutputRouteSpec compactor :=
  outputRouteSpec_of_bridgeOutputSpec
    (selectedFootprintCompactorBridgeOutputSpec_of_exact
      hroute.bridge)

theorem outputRouteSpec_of_rightEndSplitSpec
    {compactor : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitSpec
        compactor) :
    OutputRouteSpec compactor :=
  outputRouteSpec_of_exactRouteSpec
    (exactRouteSpec_of_rightEndSplitSpec hsplit)

theorem outputRouteConstruction_of_bridgeOutput
    (hbridge : SelectedFootprintCompactorBridgeOutputConstruction) :
    OutputRouteConstruction := by
  rcases hbridge with ⟨compactor, hspec⟩
  exact ⟨compactor, outputRouteSpec_of_bridgeOutputSpec hspec⟩

theorem bridgeOutputConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    SelectedFootprintCompactorBridgeOutputConstruction := by
  rcases hroute with ⟨compactor, hspec⟩
  exact ⟨compactor, hspec.bridgeOutput⟩

theorem outputRouteConstruction_iff_bridgeOutputConstruction :
    OutputRouteConstruction ↔
      SelectedFootprintCompactorBridgeOutputConstruction := by
  constructor
  · exact bridgeOutputConstruction_of_outputRoute
  · exact outputRouteConstruction_of_bridgeOutput

theorem outputRouteConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    OutputRouteConstruction := by
  rcases hroute with ⟨compactor, hspec⟩
  exact ⟨compactor, outputRouteSpec_of_exactRouteSpec hspec⟩

theorem outputRouteConstruction_of_rightEndSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitConstruction) :
    OutputRouteConstruction :=
  outputRouteConstruction_of_exactRoute
    (exactRouteConstruction_of_rightEndSplit hsplit)

theorem outputRouteConstruction_core :
    OutputRouteConstruction :=
  outputRouteConstruction_of_exactRoute exactRouteConstruction_core

/-!
## Route field projections
-/

theorem rightEndConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConstruction := by
  rcases hroute with ⟨compactor, hspec⟩
  exact ⟨compactor, hspec.rightEnd⟩

theorem guardedSplitConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    GuardedLogicalTapeDecoderFootprintCompactorSplitConstruction := by
  rcases hroute with ⟨compactor, hspec⟩
  exact ⟨compactor, hspec.guardedSplit⟩

theorem paddingSplitCasesConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitConstruction := by
  rcases hroute with ⟨compactor, hspec⟩
  exact ⟨compactor, hspec.paddingSplitCases⟩

theorem footprintPadSymbolConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorSplitPadSymbolCaseConstruction := by
  rcases hroute with ⟨compactor, hspec⟩
  exact ⟨compactor, hspec.footprintPadSymbol⟩

theorem footprintBitPaddingConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction := by
  rcases hroute with ⟨compactor, hspec⟩
  exact ⟨compactor, hspec.footprintBitPadding⟩

theorem rightEndSplitOutputConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitOutputConstruction := by
  rcases hroute with ⟨compactor, hspec⟩
  exact ⟨compactor, hspec.rightEndSplitOutput⟩

theorem guardedOutputConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    GuardedLogicalTapeDecoderFootprintCompactorOutputConstruction := by
  rcases hroute with ⟨compactor, hspec⟩
  exact ⟨compactor, hspec.guardedOutput⟩

theorem paddingSplitOutputConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputConstruction := by
  rcases hroute with ⟨compactor, hspec⟩
  exact ⟨compactor, hspec.paddingSplitOutput⟩

theorem paddingSplitOutputCasesConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitPadSymbolCaseOutputConstruction := by
  rcases hroute with ⟨compactor, hspec⟩
  exact ⟨compactor, hspec.paddingSplitSplitOutput⟩

end SelectedFootprintCompactorRouteContracts

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters
end Computability
end FoC
