import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.StructuredPrefixEraserHandoff

set_option doc.verso true

/-!
# Structured-prefix eraser route contracts

This module packages the selected two-logical-tape structured-prefix eraser
frontier into route-level exact and output contracts.  The finite-machine leaf
is still the footprint-handoff nil/cons and padding-symbol split construction
in {lit}`StructuredPrefixEraserHandoff.lean`; the contracts below make the
same leaf available through the selected handoff, public eraser, generic
guarded eraser, branch-split, and normalized-output views.
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

namespace StructuredPrefixEraserRouteContracts

/-!
## Reverse guarded and selected-branch adapters

The handoff module already adapts the guarded eraser interface to the
selected-specific handoff surface.  These reverse adapters let later proofs
start from the current selected split leaf and recover the generic guarded
view without reopening the tape-shape equalities.
-/

theorem guardedTwoTapeStructuredPrefixEraserSpec_of_footprintHandoffSpec
    {eraser : MachineDescription}
    (hhandoff :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec
        eraser) :
    GuardedTwoTapeStructuredPrefixEraserSpec eraser := by
  rcases hhandoff with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro T0 T1 bits padding
  simpa [
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_eq_guardedTwoTapeStructuredPrefixEraserSourceTape,
    guardedTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
    hrun T0 T1 bits padding

theorem guardedTwoTapeStructuredPrefixEraserConstruction_of_footprintHandoff
    (hhandoff :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction) :
    GuardedTwoTapeStructuredPrefixEraserConstruction := by
  rcases hhandoff with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      guardedTwoTapeStructuredPrefixEraserSpec_of_footprintHandoffSpec
        hspec⟩

theorem guardedTwoTapeStructuredPrefixEraserSpec_of_selectedEraserSpec
    {eraser : MachineDescription}
    (heraser :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSpec
        eraser) :
    GuardedTwoTapeStructuredPrefixEraserSpec eraser :=
  guardedTwoTapeStructuredPrefixEraserSpec_of_footprintHandoffSpec
    (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec_of_eraserSpec
      heraser)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSpec_of_guardedSpec
    {eraser : MachineDescription}
    (hguard : GuardedTwoTapeStructuredPrefixEraserSpec eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSpec
      eraser :=
  (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec_iff_eraserSpec
    eraser).mp
    (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec_of_guardedPrefixEraserSpec
      hguard)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSpec_iff_guardedSpec
    (eraser : MachineDescription) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSpec
        eraser ↔
      GuardedTwoTapeStructuredPrefixEraserSpec eraser := by
  constructor
  · exact guardedTwoTapeStructuredPrefixEraserSpec_of_selectedEraserSpec
  · exact selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSpec_of_guardedSpec

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction_of_guarded
    (hguard : GuardedTwoTapeStructuredPrefixEraserConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction := by
  rcases hguard with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSpec_of_guardedSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction_iff_guardedConstruction :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction ↔
      GuardedTwoTapeStructuredPrefixEraserConstruction := by
  constructor
  · intro heraser
    rcases heraser with ⟨eraser, hspec⟩
    exact
      ⟨eraser,
        guardedTwoTapeStructuredPrefixEraserSpec_of_selectedEraserSpec
          hspec⟩
  · exact
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction_of_guarded

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec_of_spec
    {eraser : MachineDescription}
    (heraser :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec
      eraser := by
  rcases heraser with ⟨hready, hrun⟩
  refine ⟨?_, ?_⟩
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro T0 T1
      exact hrun T0 T1 [] []
    · intro T0 T1 padding
      exact hrun T0 T1 [] (none :: padding)
    · intro T0 T1 padBit padding
      exact hrun T0 T1 [] (some padBit :: padding)
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro T0 T1 bit rest
      exact hrun T0 T1 (bit :: rest) []
    · intro T0 T1 bit rest padding
      exact hrun T0 T1 (bit :: rest) (none :: padding)
    · intro T0 T1 bit rest padBit padding
      exact hrun T0 T1 (bit :: rest) (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSpec_of_splitPadSymbolCaseSpec
    {eraser : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSpec
      eraser := by
  rcases hsplit with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  refine ⟨hready, ?_⟩
  intro T0 T1 bits padding
  cases bits with
  | nil =>
      cases padding with
      | nil =>
          exact hnilNil T0 T1
      | cons pad padding =>
          cases pad with
          | none =>
              exact hnilNone T0 T1 padding
          | some padBit =>
              exact hnilSome T0 T1 padBit padding
  | cons bit rest =>
      cases padding with
      | nil =>
          exact hconsNil T0 T1 bit rest
      | cons pad padding =>
          cases pad with
          | none =>
              exact hconsNone T0 T1 bit rest padding
          | some padBit =>
              exact hconsSome T0 T1 bit rest padBit padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec_iff_spec
    (eraser : MachineDescription) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec
        eraser ↔
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSpec
        eraser := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSpec_of_splitPadSymbolCaseSpec
  · exact
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec_of_spec

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseSpec_of_splitPadSymbolCaseSpec
    {eraser : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseSpec
      eraser := by
  rcases hsplit with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  exact
    ⟨hready, hnilNil, hnilNone, hnilSome,
      hconsNil, hconsNone, hconsSome⟩

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseSpec_of_padSymbolCaseSpec
    {eraser : MachineDescription}
    (hpad :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseSpec
      eraser := by
  rcases hpad with
    ⟨hready, hnilNil, hnilNone, hnilSome, hconsNil,
      hconsNone, hconsSome⟩
  refine ⟨hready, hnilNil, ?_, hconsNil, ?_⟩
  · intro T0 T1 pad padding
    cases pad with
    | none =>
        exact hnilNone T0 T1 padding
    | some padBit =>
        exact hnilSome T0 T1 padBit padding
  · intro T0 T1 bit rest pad padding
    cases pad with
    | none =>
        exact hconsNone T0 T1 bit rest padding
    | some padBit =>
        exact hconsSome T0 T1 bit rest padBit padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseSpec_of_bitPaddingCaseSpec
    {eraser : MachineDescription}
    (hbit :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseSpec
      eraser := by
  rcases hbit with
    ⟨hready, hnilNil, hnilCons, hconsNil, hconsCons⟩
  refine ⟨hready, ?_, ?_⟩
  · intro T0 T1 padding
    cases padding with
    | nil =>
        exact hnilNil T0 T1
    | cons pad padding =>
        exact hnilCons T0 T1 pad padding
  · intro T0 T1 bit rest padding
    cases padding with
    | nil =>
        exact hconsNil T0 T1 bit rest
    | cons pad padding =>
        exact hconsCons T0 T1 bit rest pad padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec_of_selectedEraserSpec
    {eraser : MachineDescription}
    (heraser :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec
      eraser :=
  selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec_of_handoffSpec
    (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec_of_eraserSpec
      heraser)

theorem guardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec_of_footprintHandoffSplitPadSymbolCaseSpec
    {eraser : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec
        eraser) :
    GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec
      eraser :=
  guardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec_of_spec
    (guardedTwoTapeStructuredPrefixEraserSpec_of_footprintHandoffSpec
      (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec_of_splitPadSymbolCaseSpec
        hsplit))

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec_of_guardedSplit
    {eraser : MachineDescription}
    (hguard :
      GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec
      eraser :=
  selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec_of_guardedPrefixEraserSpec
    hguard

/-!
## Output adapters
-/

theorem guardedTwoTapeStructuredPrefixEraserOutputSpec_of_footprintHandoffOutputSpec
    {eraser : MachineDescription}
    (hhandoff :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputSpec
        eraser) :
    GuardedTwoTapeStructuredPrefixEraserOutputSpec eraser := by
  rcases hhandoff with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro T0 T1 bits padding
  simpa [
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_eq_guardedTwoTapeStructuredPrefixEraserSourceTape,
    guardedTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
    hrun T0 T1 bits padding

theorem guardedTwoTapeStructuredPrefixEraserFootprintOutputSpec_of_handoffOutputSpec
    {eraser : MachineDescription}
    (hhandoff :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputSpec
        eraser) :
    GuardedTwoTapeStructuredPrefixEraserFootprintOutputSpec
      eraser :=
  guardedTwoTapeStructuredPrefixEraserFootprintOutputSpec_of_outputSpec
    (guardedTwoTapeStructuredPrefixEraserOutputSpec_of_footprintHandoffOutputSpec
      hhandoff)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputSpec_of_guardedFootprintOutputSpec
    {eraser : MachineDescription}
    (hguard :
      GuardedTwoTapeStructuredPrefixEraserFootprintOutputSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputSpec
      eraser := by
  rcases hguard with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro T0 T1 bits padding
  simpa [
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_eq_guardedTwoTapeStructuredPrefixEraserSourceTape] using
    hrun T0 T1 bits padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputSpec_of_guardedOutputSpec
    {eraser : MachineDescription}
    (hguard : GuardedTwoTapeStructuredPrefixEraserOutputSpec eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputSpec
      eraser :=
  selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputSpec_of_footprintHandoffOutputSpec
    (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputSpec_of_guardedFootprintOutputSpec
      (guardedTwoTapeStructuredPrefixEraserFootprintOutputSpec_of_outputSpec
        hguard))

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputSpec_iff_guardedOutputSpec
    (eraser : MachineDescription) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputSpec
        eraser ↔
      GuardedTwoTapeStructuredPrefixEraserOutputSpec eraser := by
  constructor
  · intro heraser
    exact
      guardedTwoTapeStructuredPrefixEraserOutputSpec_of_footprintHandoffOutputSpec
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputSpec_of_eraserOutputSpec
          heraser)
  · exact
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputSpec_of_guardedOutputSpec

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseOutputSpec_of_outputSpec
    {eraser : MachineDescription}
    (heraser :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseOutputSpec
      eraser := by
  rcases heraser with ⟨hready, hrun⟩
  refine ⟨hready, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T0 T1
    exact hrun T0 T1 [] []
  · intro T0 T1 padding
    exact hrun T0 T1 [] (none :: padding)
  · intro T0 T1 padBit padding
    exact hrun T0 T1 [] (some padBit :: padding)
  · intro T0 T1 bit rest
    exact hrun T0 T1 (bit :: rest) []
  · intro T0 T1 bit rest padding
    exact hrun T0 T1 (bit :: rest) (none :: padding)
  · intro T0 T1 bit rest padBit padding
    exact hrun T0 T1 (bit :: rest) (some padBit :: padding)

/-!
## Exact route package
-/

structure ExactRouteSpec
    (eraser : MachineDescription) : Prop where
  footprintHandoffSplit :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec
      eraser
  footprintHandoff :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec
      eraser
  selectedEraser :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSpec
      eraser
  eraserCases :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseSpec
      eraser
  eraserBitPadding :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseSpec
      eraser
  eraserPadSymbol :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseSpec
      eraser
  eraserSplit :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec
      eraser
  eraserNil :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserNilPadSymbolCaseSpec
      eraser
  eraserCons :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConsPadSymbolCaseSpec
      eraser
  guarded : GuardedTwoTapeStructuredPrefixEraserSpec eraser
  guardedSplit :
    GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec
      eraser
  guardedNil :
    GuardedTwoTapeStructuredPrefixEraserNilPadSymbolCaseSpec
      eraser
  guardedCons :
    GuardedTwoTapeStructuredPrefixEraserConsPadSymbolCaseSpec
      eraser
  footprintHandoffNil :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffNilPadSymbolCaseSpec
      eraser
  footprintHandoffCons :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConsPadSymbolCaseSpec
      eraser

def ExactRouteConstruction : Prop :=
  exists eraser : MachineDescription,
    ExactRouteSpec eraser

theorem exactRouteSpec_of_footprintHandoffSplitSpec
    {eraser : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec
        eraser) :
    ExactRouteSpec eraser := by
  have hhandoff :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec
        eraser :=
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec_of_splitPadSymbolCaseSpec
      hsplit
  have heraser :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSpec
        eraser :=
    (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec_iff_eraserSpec
      eraser).mp hhandoff
  have heraserSplit :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec
        eraser :=
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec_of_spec
      heraser
  have heraserPad :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseSpec
        eraser :=
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseSpec_of_splitPadSymbolCaseSpec
      heraserSplit
  have heraserBit :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseSpec
        eraser :=
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseSpec_of_padSymbolCaseSpec
      heraserPad
  have heraserCases :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseSpec
        eraser :=
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseSpec_of_bitPaddingCaseSpec
      heraserBit
  have hguard :
      GuardedTwoTapeStructuredPrefixEraserSpec eraser :=
    guardedTwoTapeStructuredPrefixEraserSpec_of_footprintHandoffSpec
      hhandoff
  have hguardSplit :
      GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec
        eraser :=
    guardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec_of_spec
      hguard
  exact
    { footprintHandoffSplit := hsplit
      footprintHandoff := hhandoff
      selectedEraser := heraser
      eraserCases := heraserCases
      eraserBitPadding := heraserBit
      eraserPadSymbol := heraserPad
      eraserSplit := heraserSplit
      eraserNil := heraserSplit.left
      eraserCons := heraserSplit.right
      guarded := hguard
      guardedSplit := hguardSplit
      guardedNil := hguardSplit.left
      guardedCons := hguardSplit.right
      footprintHandoffNil := hsplit.left
      footprintHandoffCons := hsplit.right }

theorem exactRouteSpec_of_footprintHandoffSpec
    {eraser : MachineDescription}
    (hhandoff :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec
        eraser) :
    ExactRouteSpec eraser :=
  exactRouteSpec_of_footprintHandoffSplitSpec
    (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec_of_handoffSpec
      hhandoff)

theorem exactRouteSpec_of_selectedEraserSpec
    {eraser : MachineDescription}
    (heraser :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSpec
        eraser) :
    ExactRouteSpec eraser :=
  exactRouteSpec_of_footprintHandoffSpec
    (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec_of_eraserSpec
      heraser)

theorem exactRouteSpec_of_guardedSpec
    {eraser : MachineDescription}
    (hguard : GuardedTwoTapeStructuredPrefixEraserSpec eraser) :
    ExactRouteSpec eraser :=
  exactRouteSpec_of_footprintHandoffSpec
    (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec_of_guardedPrefixEraserSpec
      hguard)

theorem exactRouteConstruction_of_footprintHandoffSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction) :
    ExactRouteConstruction := by
  rcases hsplit with ⟨eraser, hspec⟩
  exact ⟨eraser, exactRouteSpec_of_footprintHandoffSplitSpec hspec⟩

theorem footprintHandoffSplitConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction := by
  rcases hroute with ⟨eraser, hspec⟩
  exact ⟨eraser, hspec.footprintHandoffSplit⟩

theorem exactRouteConstruction_iff_footprintHandoffSplitConstruction :
    ExactRouteConstruction ↔
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction := by
  constructor
  · exact footprintHandoffSplitConstruction_of_exactRoute
  · exact exactRouteConstruction_of_footprintHandoffSplit

theorem exactRouteConstruction_of_footprintHandoff
    (hhandoff :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction) :
    ExactRouteConstruction := by
  rcases hhandoff with ⟨eraser, hspec⟩
  exact ⟨eraser, exactRouteSpec_of_footprintHandoffSpec hspec⟩

theorem footprintHandoffConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction := by
  rcases hroute with ⟨eraser, hspec⟩
  exact ⟨eraser, hspec.footprintHandoff⟩

theorem exactRouteConstruction_iff_footprintHandoffConstruction :
    ExactRouteConstruction ↔
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction := by
  constructor
  · exact footprintHandoffConstruction_of_exactRoute
  · exact exactRouteConstruction_of_footprintHandoff

theorem exactRouteConstruction_of_selectedEraser
    (heraser :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction) :
    ExactRouteConstruction := by
  rcases heraser with ⟨eraser, hspec⟩
  exact ⟨eraser, exactRouteSpec_of_selectedEraserSpec hspec⟩

theorem selectedEraserConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction := by
  rcases hroute with ⟨eraser, hspec⟩
  exact ⟨eraser, hspec.selectedEraser⟩

theorem exactRouteConstruction_iff_selectedEraserConstruction :
    ExactRouteConstruction ↔
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction := by
  constructor
  · exact selectedEraserConstruction_of_exactRoute
  · exact exactRouteConstruction_of_selectedEraser

theorem exactRouteConstruction_of_guarded
    (hguard : GuardedTwoTapeStructuredPrefixEraserConstruction) :
    ExactRouteConstruction := by
  rcases hguard with ⟨eraser, hspec⟩
  exact ⟨eraser, exactRouteSpec_of_guardedSpec hspec⟩

theorem guardedConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    GuardedTwoTapeStructuredPrefixEraserConstruction := by
  rcases hroute with ⟨eraser, hspec⟩
  exact ⟨eraser, hspec.guarded⟩

theorem exactRouteConstruction_iff_guardedConstruction :
    ExactRouteConstruction ↔
      GuardedTwoTapeStructuredPrefixEraserConstruction := by
  constructor
  · exact guardedConstruction_of_exactRoute
  · exact exactRouteConstruction_of_guarded

theorem exactRouteConstruction_core :
    ExactRouteConstruction :=
  exactRouteConstruction_of_footprintHandoffSplit
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction_core

/-!
## Output route package
-/

structure OutputRouteSpec
    (eraser : MachineDescription) : Prop where
  footprintHandoffOutput :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputSpec
      eraser
  footprintHandoffSplitOutput :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseOutputSpec
      eraser
  footprintHandoffNilOutput :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffNilPadSymbolCaseOutputSpec
      eraser
  footprintHandoffConsOutput :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConsPadSymbolCaseOutputSpec
      eraser
  eraserOutput :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputSpec
      eraser
  eraserCaseOutput :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseOutputSpec
      eraser
  eraserBitPaddingOutput :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseOutputSpec
      eraser
  eraserPadSymbolOutput :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseOutputSpec
      eraser
  guardedOutput : GuardedTwoTapeStructuredPrefixEraserOutputSpec eraser
  guardedFootprintOutput :
    GuardedTwoTapeStructuredPrefixEraserFootprintOutputSpec eraser
  guardedCaseOutput :
    GuardedTwoTapeStructuredPrefixEraserCaseOutputSpec eraser
  guardedBitPaddingOutput :
    GuardedTwoTapeStructuredPrefixEraserBitPaddingCaseOutputSpec eraser
  guardedSplitOutput :
    GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseOutputSpec
      eraser
  guardedNilOutput :
    GuardedTwoTapeStructuredPrefixEraserNilPadSymbolCaseOutputSpec
      eraser
  guardedConsOutput :
    GuardedTwoTapeStructuredPrefixEraserConsPadSymbolCaseOutputSpec
      eraser

def OutputRouteConstruction : Prop :=
  exists eraser : MachineDescription,
    OutputRouteSpec eraser

theorem outputRouteSpec_of_footprintHandoffOutputSpec
    {eraser : MachineDescription}
    (hhandoff :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputSpec
        eraser) :
    OutputRouteSpec eraser := by
  have hhandoffSplit :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseOutputSpec
        eraser :=
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseOutputSpec_of_handoffOutputSpec
      hhandoff
  have heraserOutput :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputSpec
        eraser :=
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputSpec_of_footprintHandoffOutputSpec
      hhandoff
  have heraserCase :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseOutputSpec
        eraser :=
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseOutputSpec_of_outputSpec
      heraserOutput
  have heraserPad :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseOutputSpec
        eraser :=
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseOutputSpec_of_outputSpec
      heraserOutput
  have heraserBit :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseOutputSpec
        eraser :=
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseOutputSpec_of_padSymbolCaseOutputSpec
      heraserPad
  have hguard :
      GuardedTwoTapeStructuredPrefixEraserOutputSpec eraser :=
    guardedTwoTapeStructuredPrefixEraserOutputSpec_of_footprintHandoffOutputSpec
      hhandoff
  have hguardFootprint :
      GuardedTwoTapeStructuredPrefixEraserFootprintOutputSpec
        eraser :=
    guardedTwoTapeStructuredPrefixEraserFootprintOutputSpec_of_outputSpec
      hguard
  have hguardCase :
      GuardedTwoTapeStructuredPrefixEraserCaseOutputSpec eraser :=
    guardedTwoTapeStructuredPrefixEraserCaseOutputSpec_of_outputSpec
      hguard
  have hguardSplit :
      GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseOutputSpec
        eraser :=
    guardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseOutputSpec_of_outputSpec
      hguard
  have hguardBit :
      GuardedTwoTapeStructuredPrefixEraserBitPaddingCaseOutputSpec
        eraser :=
    guardedTwoTapeStructuredPrefixEraserBitPaddingCaseOutputSpec_of_padSymbolCaseOutputSpec
      hguardSplit
  exact
    { footprintHandoffOutput := hhandoff
      footprintHandoffSplitOutput := hhandoffSplit
      footprintHandoffNilOutput := hhandoffSplit.left
      footprintHandoffConsOutput := hhandoffSplit.right
      eraserOutput := heraserOutput
      eraserCaseOutput := heraserCase
      eraserBitPaddingOutput := heraserBit
      eraserPadSymbolOutput := heraserPad
      guardedOutput := hguard
      guardedFootprintOutput := hguardFootprint
      guardedCaseOutput := hguardCase
      guardedBitPaddingOutput := hguardBit
      guardedSplitOutput := hguardSplit
      guardedNilOutput := hguardSplit.left
      guardedConsOutput := hguardSplit.right }

theorem outputRouteSpec_of_selectedEraserOutputSpec
    {eraser : MachineDescription}
    (heraser :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputSpec
        eraser) :
    OutputRouteSpec eraser :=
  outputRouteSpec_of_footprintHandoffOutputSpec
    (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputSpec_of_eraserOutputSpec
      heraser)

theorem outputRouteSpec_of_guardedOutputSpec
    {eraser : MachineDescription}
    (hguard : GuardedTwoTapeStructuredPrefixEraserOutputSpec eraser) :
    OutputRouteSpec eraser :=
  outputRouteSpec_of_selectedEraserOutputSpec
    (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputSpec_of_guardedOutputSpec
      hguard)

theorem outputRouteSpec_of_exactRouteSpec
    {eraser : MachineDescription}
    (hroute : ExactRouteSpec eraser) :
    OutputRouteSpec eraser :=
  outputRouteSpec_of_footprintHandoffOutputSpec
    (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputSpec_of_exact
      hroute.footprintHandoff)

theorem outputRouteConstruction_of_footprintHandoffOutput
    (hhandoff :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputConstruction) :
    OutputRouteConstruction := by
  rcases hhandoff with ⟨eraser, hspec⟩
  exact ⟨eraser, outputRouteSpec_of_footprintHandoffOutputSpec hspec⟩

theorem footprintHandoffOutputConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputConstruction := by
  rcases hroute with ⟨eraser, hspec⟩
  exact ⟨eraser, hspec.footprintHandoffOutput⟩

theorem outputRouteConstruction_iff_footprintHandoffOutputConstruction :
    OutputRouteConstruction ↔
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputConstruction := by
  constructor
  · exact footprintHandoffOutputConstruction_of_outputRoute
  · exact outputRouteConstruction_of_footprintHandoffOutput

theorem outputRouteConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    OutputRouteConstruction := by
  rcases hroute with ⟨eraser, hspec⟩
  exact ⟨eraser, outputRouteSpec_of_exactRouteSpec hspec⟩

theorem outputRouteConstruction_of_footprintHandoffSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction) :
    OutputRouteConstruction :=
  outputRouteConstruction_of_exactRoute
    (exactRouteConstruction_of_footprintHandoffSplit hsplit)

theorem outputRouteConstruction_core :
    OutputRouteConstruction :=
  outputRouteConstruction_of_exactRoute exactRouteConstruction_core

/-!
## Boundary eraser output package

The two left-boundary eraser phases are already solved by the common
{lit}`leftBoundaryEraserDescription`.  This small package exposes that solved
piece independently from the still-open initial-positioner, between-fields
positioner, and erased-prefix compactor gaps.
-/

structure BoundaryEraserOutputRouteSpec
    (eraser : MachineDescription) : Prop where
  pairOutput :
    GuardedTwoTapeStructuredPrefixBoundaryEraserPairOutputSpec eraser
  secondOutput :
    GuardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserOutputSpec
      eraser
  firstOutput :
    GuardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserOutputSpec
      eraser
  secondEquiv :
    GuardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserEquivSpec
      eraser
  firstEquiv :
    GuardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserEquivSpec
      eraser

def BoundaryEraserOutputRouteConstruction : Prop :=
  exists eraser : MachineDescription,
    BoundaryEraserOutputRouteSpec eraser

theorem boundaryEraserOutputRouteSpec_of_exact
    {eraser : MachineDescription}
    (hpair : GuardedTwoTapeStructuredPrefixBoundaryEraserPairSpec eraser) :
    BoundaryEraserOutputRouteSpec eraser := by
  rcases hpair with ⟨hsecond, hfirst⟩
  exact
    { pairOutput :=
        guardedTwoTapeStructuredPrefixBoundaryEraserPairOutputSpec_of_exact
          ⟨hsecond, hfirst⟩
      secondOutput :=
        guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserOutputSpec_of_exact
          hsecond
      firstOutput :=
        guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserOutputSpec_of_exact
          hfirst
      secondEquiv :=
        guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserEquivSpec_of_exact
          hsecond
      firstEquiv :=
        guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserEquivSpec_of_exact
          hfirst }

theorem boundaryEraserOutputRouteConstruction_of_exact
    (hpair : GuardedTwoTapeStructuredPrefixBoundaryEraserPairConstruction) :
    BoundaryEraserOutputRouteConstruction := by
  rcases hpair with ⟨eraser, hspec⟩
  exact ⟨eraser, boundaryEraserOutputRouteSpec_of_exact hspec⟩

theorem boundaryEraserOutputRouteSpec_core :
    BoundaryEraserOutputRouteSpec leftBoundaryEraserDescription :=
  boundaryEraserOutputRouteSpec_of_exact
    guardedTwoTapeStructuredPrefixBoundaryEraserPairSpec_core

theorem boundaryEraserOutputRouteConstruction_core :
    BoundaryEraserOutputRouteConstruction :=
  ⟨leftBoundaryEraserDescription, boundaryEraserOutputRouteSpec_core⟩

/-!
## Route field projections
-/

theorem eraserSplitConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction := by
  rcases hroute with ⟨eraser, hspec⟩
  exact ⟨eraser, hspec.eraserSplit⟩

theorem eraserPadSymbolConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseConstruction := by
  rcases hroute with ⟨eraser, hspec⟩
  exact ⟨eraser, hspec.eraserPadSymbol⟩

theorem eraserBitPaddingConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseConstruction := by
  rcases hroute with ⟨eraser, hspec⟩
  exact ⟨eraser, hspec.eraserBitPadding⟩

theorem eraserCaseConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseConstruction := by
  rcases hroute with ⟨eraser, hspec⟩
  exact ⟨eraser, hspec.eraserCases⟩

theorem guardedSplitConstruction_of_exactRoute
    (hroute : ExactRouteConstruction) :
    GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction := by
  rcases hroute with ⟨eraser, hspec⟩
  exact ⟨eraser, hspec.guardedSplit⟩

theorem selectedEraserOutputConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputConstruction := by
  rcases hroute with ⟨eraser, hspec⟩
  exact ⟨eraser, hspec.eraserOutput⟩

theorem selectedEraserSplitOutputConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseOutputConstruction := by
  rcases hroute with ⟨eraser, hspec⟩
  exact ⟨eraser, hspec.footprintHandoffSplitOutput⟩

theorem guardedOutputConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    GuardedTwoTapeStructuredPrefixEraserOutputConstruction := by
  rcases hroute with ⟨eraser, hspec⟩
  exact ⟨eraser, hspec.guardedOutput⟩

theorem guardedFootprintOutputConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    GuardedTwoTapeStructuredPrefixEraserFootprintOutputConstruction := by
  rcases hroute with ⟨eraser, hspec⟩
  exact ⟨eraser, hspec.guardedFootprintOutput⟩

theorem guardedSplitOutputConstruction_of_outputRoute
    (hroute : OutputRouteConstruction) :
    GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseOutputConstruction := by
  rcases hroute with ⟨eraser, hspec⟩
  exact ⟨eraser, hspec.guardedSplitOutput⟩

theorem boundaryEraserPairOutputConstruction_of_route
    (hroute : BoundaryEraserOutputRouteConstruction) :
    GuardedTwoTapeStructuredPrefixBoundaryEraserPairOutputConstruction := by
  rcases hroute with ⟨eraser, hspec⟩
  exact ⟨eraser, hspec.pairOutput⟩

end StructuredPrefixEraserRouteContracts

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters
end Computability
end FoC
