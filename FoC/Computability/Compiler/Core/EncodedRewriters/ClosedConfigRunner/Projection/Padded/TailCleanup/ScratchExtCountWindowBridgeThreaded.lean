import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.ScratchExtCountWindowBridge

set_option doc.verso true

/-!
# Structured count-window bridge threading

This module carries the structured count-window bridge through the output
projector, scan-source materializer, scratch-count materializer, and
post-padding scratch-extension construction wrappers.  The lower-level endpoint
facts and remaining finite-machine leaves stay in
{module}`FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.ScratchExtCountWindowBridge`.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncodedRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

open CanonicalLayouts.DovetailLayoutScanner

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierComponentsConstruction_of_prefixAndFootprint
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hfootprint :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierComponentsConstruction :=
  ⟨countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserConstruction_of_prefixEraser
      hprefix,
    hfootprint⟩

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction_of_prefixAndFootprint
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hfootprint :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction := by
  exact
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction_of_components
      (countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierComponentsConstruction_of_prefixAndFootprint
        hprefix hfootprint)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction_of_prefixAndFootprint
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hfootprint :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction := by
  exact
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction_of_densifier
      (countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction_of_prefixAndFootprint
        hprefix hfootprint)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction_of_prefixAndFootprint
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hfootprint :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction := by
  exact
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction_of_cleanup
      (countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction_of_prefixAndFootprint
        hprefix hfootprint)

theorem countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_of_prefixAndFootprint
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hfootprint :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction := by
  exact
    countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_of_structuredPrefixSelectedSegmentDecoder
      (countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction_of_prefixAndFootprint
        hprefix hfootprint)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierComponentsConstruction_of_prefixAndGenericFootprint
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hgeneric :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierComponentsConstruction := by
  exact
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierComponentsConstruction_of_prefixAndFootprint
      hprefix
      (countWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction_of_generic
        hgeneric)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction_of_prefixAndGenericFootprint
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hgeneric :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction := by
  exact
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction_of_prefixAndFootprint
      hprefix
      (countWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction_of_generic
        hgeneric)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction_of_prefixAndGenericFootprint
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hgeneric :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction := by
  exact
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction_of_prefixAndFootprint
      hprefix
      (countWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction_of_generic
        hgeneric)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction_of_prefixAndGenericFootprint
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hgeneric :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction := by
  exact
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction_of_prefixAndFootprint
      hprefix
      (countWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction_of_generic
        hgeneric)

theorem countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_of_prefixAndGenericFootprint
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hgeneric :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction := by
  exact
    countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_of_prefixAndFootprint
      hprefix
      (countWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction_of_generic
        hgeneric)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierComponentsConstruction_of_prefixAndFootprintCases
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierComponentsConstruction := by
  exact
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierComponentsConstruction_of_prefixAndGenericFootprint
      hprefix
      (selectedSegmentLogicalTapeDecoderFootprintCompactorConstruction_of_cases
        hcases)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction_of_prefixAndFootprintCases
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction := by
  exact
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction_of_prefixAndGenericFootprint
      hprefix
      (selectedSegmentLogicalTapeDecoderFootprintCompactorConstruction_of_cases
        hcases)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction_of_prefixAndFootprintCases
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction := by
  exact
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction_of_prefixAndGenericFootprint
      hprefix
      (selectedSegmentLogicalTapeDecoderFootprintCompactorConstruction_of_cases
        hcases)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction_of_prefixAndFootprintCases
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction := by
  exact
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction_of_prefixAndGenericFootprint
      hprefix
      (selectedSegmentLogicalTapeDecoderFootprintCompactorConstruction_of_cases
        hcases)

theorem countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_of_prefixAndFootprintCases
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction := by
  exact
    countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_of_prefixAndGenericFootprint
      hprefix
      (selectedSegmentLogicalTapeDecoderFootprintCompactorConstruction_of_cases
        hcases)

theorem countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_of_prefixAndFootprintBitPaddingCases
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction := by
  exact
    countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_of_prefixAndFootprintCases
      hprefix
      (selectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction_of_bitPaddingCases
        hcases)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierComponentsConstruction_of_structuredPrefixBranchCasesAndFootprint
    (heraser :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hfootprint :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierComponentsConstruction :=
  ⟨countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserConstruction_of_branches
      (countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchConstruction_of_cases
        heraser),
    hfootprint⟩

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction_of_structuredPrefixBranchCasesAndGenericFootprint
    (heraser :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hgeneric :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction := by
  exact
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction_of_components
      (countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierComponentsConstruction_of_structuredPrefixBranchCasesAndFootprint
        heraser
        (countWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction_of_generic
          hgeneric))

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction_of_structuredPrefixBranchCasesAndFootprintCases
    (heraser :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction := by
  exact
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction_of_densifier
      (countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction_of_structuredPrefixBranchCasesAndGenericFootprint
        heraser
        (selectedSegmentLogicalTapeDecoderFootprintCompactorConstruction_of_cases
          hcases))

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction_of_structuredPrefixBranchCasesAndFootprintCases
    (heraser :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction := by
  exact
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction_of_cleanup
      (countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction_of_structuredPrefixBranchCasesAndFootprintCases
        heraser hcases)

theorem countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_of_structuredPrefixBranchCasesAndFootprintCases
    (heraser :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction := by
  exact
    countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_of_structuredPrefixSelectedSegmentDecoder
      (countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction_of_structuredPrefixBranchCasesAndFootprintCases
        heraser hcases)

theorem countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
    (heraser :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction := by
  exact
    countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_of_structuredPrefixBranchCasesAndFootprintCases
      heraser
      (selectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction_of_bitPaddingCases
        hcases)

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction_core :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction := by
  sorry

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction_core :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction := by
  exact
    selectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction_of_bitPaddingCases
      selectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction_core

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorConstruction_core :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorConstruction := by
  exact
    selectedSegmentLogicalTapeDecoderFootprintCompactorConstruction_of_cases
      selectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction_core


theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction_core :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction := by
  exact
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction_of_generic
      selectedSegmentLogicalTapeDecoderFootprintCompactorConstruction_core

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction_of_prefixEraser
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction := by
  rcases hprefix with ⟨eraser, hready, hrun⟩
  refine ⟨eraser, hready, ?_, ?_, ?_, ?_⟩
  · intro L
    simpa [
      countWindowPostFieldDecodedPrefixStructuredPrefixEraserSourceTape,
      countWindowPostFieldDecodedPrefixStructuredPrefixSelectedSegmentTargetTape,
      countWindowPostFieldDecodedPrefixStructuredPrefixEraserTargetTape] using
      hrun true L
        (countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
          true L [])
  · intro L bit rest
    simpa [
      countWindowPostFieldDecodedPrefixStructuredPrefixEraserSourceTape,
      countWindowPostFieldDecodedPrefixStructuredPrefixSelectedSegmentTargetTape,
      countWindowPostFieldDecodedPrefixStructuredPrefixEraserTargetTape] using
      hrun true L
        (countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
          true L (bit :: rest))
  · intro L
    simpa [
      countWindowPostFieldDecodedPrefixStructuredPrefixEraserSourceTape,
      countWindowPostFieldDecodedPrefixStructuredPrefixSelectedSegmentTargetTape,
      countWindowPostFieldDecodedPrefixStructuredPrefixEraserTargetTape] using
      hrun false L
        (countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
          false L [])
  · intro L bit rest
    simpa [
      countWindowPostFieldDecodedPrefixStructuredPrefixEraserSourceTape,
      countWindowPostFieldDecodedPrefixStructuredPrefixSelectedSegmentTargetTape,
      countWindowPostFieldDecodedPrefixStructuredPrefixEraserTargetTape] using
      hrun false L
        (countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
          false L (bit :: rest))

def selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) : Tape Bool :=
  selectedSegmentLogicalTapeDecoderTargetTape
    (rightEdgeScanSourceTapeFromLeft [none] bits padding)
    (encodedStructuredTapeCellsPrefix
      [guardLogicalTape T0, guardLogicalTape T1])

def selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
    (bits : Word Bool) (padding : List (Option Bool)) : Tape Bool :=
  selectedSegmentLogicalTapeDecoderTargetTape
    (rightEdgeScanSourceTapeFromLeft [none] bits padding)
    []

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    forall (T0 T1 : Tape Bool) (bits : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding)
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          bits padding)

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction :
    Prop :=
  exists eraser : MachineDescription,
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSpec eraser

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall (T0 T1 : Tape Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] padding)
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          [] padding)) ∧
    forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) padding)
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) padding)

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseConstruction :
    Prop :=
  exists eraser : MachineDescription,
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseSpec
      eraser

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall T0 T1 : Tape Bool,
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] [])
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          [] [])) ∧
    (forall (T0 T1 : Tape Bool) (pad : Option Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (pad :: padding))
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          [] (pad :: padding))) ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) [])
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) [])) ∧
    forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (pad : Option Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (pad :: padding))
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) (pad :: padding))

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseConstruction :
    Prop :=
  exists eraser : MachineDescription,
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseSpec
      eraser

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction_of_cases
    (hcases :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction := by
  rcases hcases with ⟨eraser, hready, hnil, hcons⟩
  refine ⟨eraser, hready, ?_⟩
  intro T0 T1 bits padding
  cases bits with
  | nil =>
      exact hnil T0 T1 padding
  | cons bit rest =>
      exact hcons T0 T1 bit rest padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseConstruction_of_bitPaddingCases
    (hcases :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseConstruction := by
  rcases hcases with
    ⟨eraser, hready, hnilNil, hnilCons, hconsNil,
      hconsCons⟩
  refine ⟨eraser, hready, ?_, ?_⟩
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

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction_of_twoTapeStructuredPrefixEraser
    (heraser :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction := by
  rcases heraser with ⟨eraser, hready, hrun⟩
  refine ⟨eraser, hready, ?_, ?_, ?_, ?_⟩
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

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseConstruction_core :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseConstruction := by
  sorry

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseConstruction_core :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseConstruction := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseConstruction_of_bitPaddingCases
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseConstruction_core

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction_core :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction_of_cases
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseConstruction_core

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction_core :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction := by
  exact
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction_of_twoTapeStructuredPrefixEraser
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction_core

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchConstruction_core :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchConstruction := by
  exact
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchConstruction_of_cases
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction_core

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserConstruction_core :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserConstruction := by
  exact
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserConstruction_of_branches
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchConstruction_core

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierComponentsConstruction_core :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierComponentsConstruction := by
  exact
    ⟨countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserConstruction_core,
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction_core⟩

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction_core :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction := by
  exact
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction_of_components
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierComponentsConstruction_core

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction_core :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction := by
  exact
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction_of_densifier
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction_core

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction_core :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction :=
  countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction_of_cleanup
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction_core


theorem countWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction_of_countWindowSegmentNormalizer
    (hnormalizer :
      CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction := by
  rcases hnormalizer with
    ⟨normalizer, hnormalizerReady, hnormalizerRun⟩
  refine
    ⟨structuredTape2ProjectorDescription normalizer, ?_⟩
  constructor
  · exact
      structuredTape2ProjectorDescription_subroutineReady
        hnormalizerReady
  · intro useAccept L deletedTail
    let T0 :=
      structuredBoolWordRawBitsDecoderSourceTargetTape
        (ParsedLayoutBits L)
        (countWindowPostFieldDecodedPrefixStructuredSuffixTail
          useAccept L)
        (countWindowPostFieldDecodedPrefixStructuredSourcePadding
          useAccept L deletedTail)
    let T1 :=
      structuredBoolWordRawBitsDecoderCounterDecodeTape 0
        ((ParsedLayoutBits L).length + 1)
    let T2 := postFieldDecodedPrefixScanSourceTape useAccept L
    have hsource :
        exists A : Tape Bool, exists B : Tape Bool, exists C : Tape Bool,
          guardLogicalTapes [T0, T1, T2] = [A, B, C] ∧
            AtEncodedBlockStart (guardLogicalTapes [T0, T1, T2])
              (countWindowPostFieldDecodedPrefixStructuredEncodedOutputTape
                useAccept L deletedTail) := by
      refine
        ⟨guardLogicalTape T0, guardLogicalTape T1,
          guardLogicalTape T2, ?_, ?_⟩
      · simp [guardLogicalTapes]
      · simpa [T0, T1, T2,
          countWindowPostFieldDecodedPrefixStructuredEncodedOutputTape] using
          atEncodedBlockStart_self (guardLogicalTapes [T0, T1, T2])
    rcases
        seekTape2Description_contract_three.realizes
          (guardLogicalTapes [T0, T1, T2])
          (countWindowPostFieldDecodedPrefixStructuredEncodedOutputTape
            useAccept L deletedTail)
          hsource with
      ⟨Tmid, hseek, hseparator⟩
    exact
      canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        seekTape2Description_subroutineReady
        hnormalizerReady
        hseek.toEquiv
        (hnormalizerRun useAccept L deletedTail Tmid
          (by
            simpa [T0, T1, T2] using hseparator))

theorem countWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction_of_selectedSegmentDecoder
    (hdecoder :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction :=
  countWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction_of_countWindowSegmentNormalizer
    (countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_of_selectedSegmentDecoder
      hdecoder)

theorem countWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction_of_prefixAndFootprintCases
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction :=
  countWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction_of_countWindowSegmentNormalizer
    (countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_of_prefixAndFootprintCases
      hprefix hcases)

theorem countWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction_of_prefixAndFootprintBitPaddingCases
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction :=
  countWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction_of_countWindowSegmentNormalizer
    (countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_of_prefixAndFootprintBitPaddingCases
      hprefix hcases)

theorem countWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
    (heraser :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction :=
  countWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction_of_countWindowSegmentNormalizer
    (countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
      heraser hcases)

theorem countWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction_of_segmentNormalizer
    (hnormalizer :
      Structured.MultiTapeLowering.StructuredTape2SegmentNormalizerConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction := by
  rcases
      structuredTape2ProjectorConstruction_of_segmentNormalizerConstruction
        hnormalizer with
    ⟨projector, hprojectorReady, hprojectorRun⟩
  refine ⟨projector, hprojectorReady, ?_⟩
  intro useAccept L deletedTail
  exact
    hprojectorRun
      (structuredBoolWordRawBitsDecoderSourceTargetTape
        (ParsedLayoutBits L)
        (countWindowPostFieldDecodedPrefixStructuredSuffixTail useAccept L)
        (countWindowPostFieldDecodedPrefixStructuredSourcePadding
          useAccept L deletedTail))
      (structuredBoolWordRawBitsDecoderCounterDecodeTape 0
        ((ParsedLayoutBits L).length + 1))
      (postFieldDecodedPrefixScanSourceTape useAccept L)

theorem countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_of_segmentNormalizer
    (hnormalizer :
      Structured.MultiTapeLowering.StructuredTape2SegmentNormalizerConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction := by
  rcases hnormalizer with ⟨normalizer, hnormalizerReady, hnormalizerRun⟩
  refine ⟨normalizer, hnormalizerReady, ?_⟩
  intro useAccept L deletedTail physical hseparator
  exact
    hnormalizerRun
      (structuredBoolWordRawBitsDecoderSourceTargetTape
        (ParsedLayoutBits L)
        (countWindowPostFieldDecodedPrefixStructuredSuffixTail useAccept L)
        (countWindowPostFieldDecodedPrefixStructuredSourcePadding
          useAccept L deletedTail))
      (structuredBoolWordRawBitsDecoderCounterDecodeTape 0
        ((ParsedLayoutBits L).length + 1))
      (postFieldDecodedPrefixScanSourceTape useAccept L)
      physical hseparator

theorem countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction := by
  exact
    countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_of_structuredPrefixSelectedSegmentDecoder
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction_core

theorem countWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction_core :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction := by
  exact
    countWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction_of_countWindowSegmentNormalizer
      countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_core

theorem countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_of_structuredParts
    (hinitializer :
      CountWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction)
    (hextractor :
      LoweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction)
    (hprojector :
      CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction) :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction := by
  intro useAccept
  rcases hinitializer useAccept with ⟨initializer, hinitializerSpec⟩
  rcases hextractor with ⟨extractor, hextractorReady, hextractorRun⟩
  rcases hprojector with ⟨projector, hprojectorSpec⟩
  refine
    ⟨structured3EndpointBridgeDescription
        initializer extractor projector,
      ?_⟩
  constructor
  · exact
      structured3EndpointBridgeDescription_subroutineReady
        hinitializerSpec.left hextractorReady
        hprojectorSpec.left
  · intro L pref leftBit deletedTail hdeleted hpayload
    have hinitializerRun :
        initializer.HaltsFromTapeEquiv
          (countWindowPostFieldDecodedPrefixMaterializerSourceTape
            useAccept L pref leftBit deletedTail)
          (countWindowPostFieldDecodedPrefixStructuredEncodedInputTape
            useAccept L pref leftBit deletedTail) :=
      hinitializerSpec.right L pref leftBit deletedTail hdeleted hpayload
    have hextractorRun :
        extractor.HaltsFromTapeEquiv
          (countWindowPostFieldDecodedPrefixStructuredEncodedInputTape
            useAccept L pref leftBit deletedTail)
          (countWindowPostFieldDecodedPrefixStructuredEncodedOutputTape
            useAccept L deletedTail) :=
      hextractorRun
        useAccept L pref leftBit deletedTail hdeleted hpayload
    have hprojectorRun :
        projector.HaltsFromTapeEquiv
          (countWindowPostFieldDecodedPrefixStructuredEncodedOutputTape
            useAccept L deletedTail)
          (postFieldDecodedPrefixScanSourceTape useAccept L) :=
      hprojectorSpec.right useAccept L deletedTail
    simpa [countWindowPostFieldDecodedPrefixStructuredEncodedInputTape,
      countWindowPostFieldDecodedPrefixStructuredEncodedOutputTape] using
      structured3EndpointBridgeDescription_haltsFromTapeEquiv
        hinitializerSpec.left hextractorReady hprojectorSpec.left
        hinitializerRun hextractorRun hprojectorRun

theorem countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_of_loweredStructuredExtractor
    (hextractor :
      LoweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction) :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction :=
  countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_of_structuredParts
    countWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction_core
    hextractor
    countWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction_core

theorem countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_of_selectedSegmentDecoder
    (hdecoder :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction)
    (hextractor :
      LoweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction) :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction :=
  countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_of_structuredParts
    countWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction_core
    hextractor
    (countWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction_of_selectedSegmentDecoder
      hdecoder)

theorem countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_bridgeCore :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction :=
  countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_of_loweredStructuredExtractor
    loweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction_core

theorem countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_bridgeCore_of_selectedSegmentDecoder
    (hdecoder :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction) :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction :=
  countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_of_selectedSegmentDecoder
    hdecoder
    loweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction_core

theorem countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_of_prefixAndFootprintCases
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction)
    (hextractor :
      LoweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction) :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction :=
  countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_of_structuredParts
    countWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction_core
    hextractor
    (countWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction_of_prefixAndFootprintCases
      hprefix hcases)

theorem countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_bridgeCore_of_prefixAndFootprintCases
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction :=
  countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_of_prefixAndFootprintCases
    hprefix hcases
    loweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction_core

theorem countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_bridgeCore_of_prefixAndFootprintBitPaddingCases
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction :=
  countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_bridgeCore_of_prefixAndFootprintCases
    hprefix
    (selectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction_of_bitPaddingCases
      hcases)

theorem countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_bridgeCore_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
    (heraser :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction :=
  countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_of_structuredParts
    countWindowPostFieldDecodedPrefixStructuredInputInitializerConstruction_core
    loweredStructuredCountWindowPostFieldDecodedPrefixExtractorConstruction_core
    (countWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
      heraser hcases)

theorem selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction_of_scanSourceMaterializer
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction := by
  let hrejectScan :
      RejectPostFieldDecodedPrefixScanSourceConstruction :=
    rejectPostFieldDecodedPrefixScanSourceConstruction_of_countWindowMaterializer
      hmaterializer
  let hrejectRestorer :
      RejectPostFieldDecodedPrefixRestorerConstruction :=
    rejectPostFieldDecodedPrefixRestorerConstruction_of_scanSource
      hrejectScan
  let hrejectRemaining :
      RejectPostFieldRemainingGapsConstruction :=
    rejectPostFieldRemainingGapsConstruction_of_rewinderAndRestorer
      rejectPostFieldHandoffRightEdgeRewinderConstruction_core
      hrejectRestorer
  let hacceptScan :
      AcceptPostFieldRewoundToDecodedPrefixScanSourceConstruction :=
    acceptPostFieldRewoundToDecodedPrefixScanSourceConstruction_of_countWindowMaterializer
      hmaterializer
  let hacceptRewound :
      AcceptPostFieldRewoundToDecodedPrefixConstruction :=
    acceptPostFieldRewoundToDecodedPrefixConstruction_of_scanSource
      hacceptScan
      acceptPostFieldDecodedPrefixScanToRewindConstruction_core
  let hacceptReposition :
      AcceptPostFieldRepositionToDecodedPrefixConstruction :=
    acceptPostFieldRepositionToDecodedPrefixConstruction_of_rewinderAndRestorer
      acceptPostFieldRepositionRightEdgeRewinderConstruction_core
      hacceptRewound
  let hacceptBoundary :
      AcceptPostFieldBoundaryToDecodedPrefixConstruction :=
    acceptPostFieldBoundaryToDecodedPrefixConstruction_of_reposition
      hacceptReposition
  exact
    selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction_of_openConstructions
      ⟨hacceptBoundary, hrejectRemaining⟩

theorem selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction_bridgeCore :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction :=
  selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction_of_scanSourceMaterializer
    countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_bridgeCore

theorem selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction_bridgeCore_of_selectedSegmentDecoder
    (hdecoder :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction :=
  selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction_of_scanSourceMaterializer
    (countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_bridgeCore_of_selectedSegmentDecoder
      hdecoder)

theorem selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction_bridgeCore_of_prefixAndFootprintCases
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction :=
  selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction_of_scanSourceMaterializer
    (countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_bridgeCore_of_prefixAndFootprintCases
      hprefix hcases)

theorem selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction_bridgeCore_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
    (heraser :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction :=
  selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction_of_scanSourceMaterializer
    (countWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction_bridgeCore_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
      heraser hcases)

theorem selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction_bridgeCore :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction :=
  selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction_of_parts
    selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction_bridgeCore
    selectedProjectionPaddedTailCleanupScratchCountWindowRestorerConstruction_core

theorem selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction_bridgeCore_of_prefixAndFootprintCases
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction :=
  selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction_of_parts
    (selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction_bridgeCore_of_prefixAndFootprintCases
      hprefix hcases)
    selectedProjectionPaddedTailCleanupScratchCountWindowRestorerConstruction_core

theorem selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction_bridgeCore_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
    (heraser :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction :=
  selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction_of_parts
    (selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction_bridgeCore_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
      heraser hcases)
    selectedProjectionPaddedTailCleanupScratchCountWindowRestorerConstruction_core

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction :=
  selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction_of_countWindowMaterializers
    selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction_bridgeCore

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction_of_prefixAndFootprintCases
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction :=
  selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction_of_countWindowMaterializers
    (selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction_bridgeCore_of_prefixAndFootprintCases
      hprefix hcases)

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
    (heraser :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction :=
  selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction_of_countWindowMaterializers
    (selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction_bridgeCore_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
      heraser hcases)

theorem selectedProjectionPaddedTailCleanupScratchExtConstruction :
    SelectedProjectionPaddedTailCleanupScratchExtConstruction :=
  selectedProjectionPaddedTailCleanupScratchExtConstruction_of_countExtenders
    selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction

theorem selectedProjectionPaddedTailCleanupScratchExtConstruction_of_prefixAndFootprintCases
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    SelectedProjectionPaddedTailCleanupScratchExtConstruction :=
  selectedProjectionPaddedTailCleanupScratchExtConstruction_of_countExtenders
    (selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction_of_prefixAndFootprintCases
      hprefix hcases)

theorem selectedProjectionPaddedTailCleanupScratchExtConstruction_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
    (heraser :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionPaddedTailCleanupScratchExtConstruction :=
  selectedProjectionPaddedTailCleanupScratchExtConstruction_of_countExtenders
    (selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
      heraser hcases)

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction :=
  selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction_of_extenders
    selectedProjectionPaddedTailCleanupScratchExtConstruction

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction_of_prefixAndFootprintCases
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction :=
  selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction_of_extenders
    (selectedProjectionPaddedTailCleanupScratchExtConstruction_of_prefixAndFootprintCases
      hprefix hcases)

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction_of_prefixAndFootprintBitPaddingCases
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction :=
  selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction_of_prefixAndFootprintCases
    hprefix
    (selectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction_of_bitPaddingCases
      hcases)

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
    (heraser :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction :=
  selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction_of_extenders
    (selectedProjectionPaddedTailCleanupScratchExtConstruction_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
      heraser hcases)

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncodedRewriters
end Computability
end FoC
