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

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_nil_nil :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] []) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells [] [] [] := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_nil
      []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_nil_cons
    (pad : Option Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (pad :: padding)) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        [] [] (pad :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_nil
      (pad :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_nil_none
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (none :: padding)) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        [] [] (none :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_nil_cons
      none padding

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_nil_some
    (padBit : Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (some padBit :: padding)) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        [] [] (some padBit :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_nil_cons
      (some padBit) padding

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_cons_nil
    (bit : Bool) (rest : Word Bool) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) []) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        [] (bit :: rest) [] := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_cons
      bit rest []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_cons_cons
    (bit : Bool) (rest : Word Bool)
    (pad : Option Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (pad :: padding)) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        [] (bit :: rest) (pad :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_cons
      bit rest (pad :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_cons_none
    (bit : Bool) (rest : Word Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (none :: padding)) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        [] (bit :: rest) (none :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_cons_cons
      bit rest none padding

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_cons_some
    (bit : Bool) (rest : Word Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (some padBit :: padding)) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        [] (bit :: rest) (some padBit :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_cons_cons
      bit rest (some padBit) padding

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_nil_nil :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] []) =
      selectedSegmentLogicalTapeDecoderDensifierPaddingPreservingCells [] [] := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_nil
      []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_nil_cons
    (pad : Option Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] (pad :: padding)) =
      selectedSegmentLogicalTapeDecoderDensifierPaddingPreservingCells
        [] (pad :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_nil
      (pad :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_nil_none
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] (none :: padding)) =
      selectedSegmentLogicalTapeDecoderDensifierPaddingPreservingCells
        [] (none :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_nil_cons
      none padding

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_nil_some
    (padBit : Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] (some padBit :: padding)) =
      selectedSegmentLogicalTapeDecoderDensifierPaddingPreservingCells
        [] (some padBit :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_nil_cons
      (some padBit) padding

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_cons_nil
    (bit : Bool) (rest : Word Bool) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) []) =
      selectedSegmentLogicalTapeDecoderDensifierPaddingPreservingCells
        (bit :: rest) [] := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_cons
      bit rest []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_cons_cons
    (bit : Bool) (rest : Word Bool)
    (pad : Option Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) (pad :: padding)) =
      selectedSegmentLogicalTapeDecoderDensifierPaddingPreservingCells
        (bit :: rest) (pad :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_cons
      bit rest (pad :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_cons_none
    (bit : Bool) (rest : Word Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) (none :: padding)) =
      selectedSegmentLogicalTapeDecoderDensifierPaddingPreservingCells
        (bit :: rest) (none :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_cons_cons
      bit rest none padding

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_cons_some
    (bit : Bool) (rest : Word Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) (some padBit :: padding)) =
      selectedSegmentLogicalTapeDecoderDensifierPaddingPreservingCells
        (bit :: rest) (some padBit :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_cons_cons
      bit rest (some padBit) padding

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape_nil_nil :
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] [] =
      rightEndCompactionSourceTape
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          [] []) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape
      [] []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape_nil_none
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] (none :: padding) =
      rightEndCompactionSourceTape
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          [] (none :: padding)) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape
      [] (none :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape_nil_some
    (padBit : Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] (some padBit :: padding) =
      rightEndCompactionSourceTape
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          [] (some padBit :: padding)) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape
      [] (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape_cons_nil
    (bit : Bool) (rest : Word Bool) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        (bit :: rest) [] =
      rightEndCompactionSourceTape
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          (bit :: rest) []) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape
      (bit :: rest) []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape_cons_none
    (bit : Bool) (rest : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        (bit :: rest) (none :: padding) =
      rightEndCompactionSourceTape
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          (bit :: rest) (none :: padding)) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape
      (bit :: rest) (none :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape_cons_some
    (bit : Bool) (rest : Word Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        (bit :: rest) (some padBit :: padding) =
      rightEndCompactionSourceTape
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          (bit :: rest) (some padBit :: padding)) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape
      (bit :: rest) (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          bits padding) =
      none ::
        List.append
          (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
            bits padding)
          [none, none] := by
  rw [selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells]
  simp [selectedSegmentLogicalTapeDecoderDensifierSourceCells]

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_eq_paddingPreserving
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          bits padding) =
      List.append (bits.map some) (none :: padding) := by
  rw [selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells]
  rfl

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint_nil_nil :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] []) =
      none ::
        List.append
          (selectedSegmentLogicalTapeDecoderDensifierFootprintCells [] [])
          [none, none] := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint
      [] []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint_nil_none
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (none :: padding)) =
      none ::
        List.append
          (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
            [] (none :: padding))
          [none, none] := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint
      [] (none :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint_nil_some
    (padBit : Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (some padBit :: padding)) =
      none ::
        List.append
          (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
            [] (some padBit :: padding))
          [none, none] := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint
      [] (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint_cons_nil
    (bit : Bool) (rest : Word Bool) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) []) =
      none ::
        List.append
          (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
            (bit :: rest) [])
          [none, none] := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint
      (bit :: rest) []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint_cons_none
    (bit : Bool) (rest : Word Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (none :: padding)) =
      none ::
        List.append
          (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
            (bit :: rest) (none :: padding))
          [none, none] := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint
      (bit :: rest) (none :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint_cons_some
    (bit : Bool) (rest : Word Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (some padBit :: padding)) =
      none ::
        List.append
          (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
            (bit :: rest) (some padBit :: padding))
          [none, none] := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint
      (bit :: rest) (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_eq_paddingPreserving_nil_nil :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] []) =
      List.append ([].map some) (none :: []) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_eq_paddingPreserving
      [] []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_eq_paddingPreserving_nil_none
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] (none :: padding)) =
      List.append ([].map some) (none :: none :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_eq_paddingPreserving
      [] (none :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_eq_paddingPreserving_nil_some
    (padBit : Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] (some padBit :: padding)) =
      List.append ([].map some) (none :: some padBit :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_eq_paddingPreserving
      [] (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_eq_paddingPreserving_cons_nil
    (bit : Bool) (rest : Word Bool) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) []) =
      List.append ((bit :: rest).map some) (none :: []) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_eq_paddingPreserving
      (bit :: rest) []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_eq_paddingPreserving_cons_none
    (bit : Bool) (rest : Word Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) (none :: padding)) =
      List.append ((bit :: rest).map some) (none :: none :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_eq_paddingPreserving
      (bit :: rest) (none :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_eq_paddingPreserving_cons_some
    (bit : Bool) (rest : Word Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) (some padBit :: padding)) =
      List.append ((bit :: rest).map some)
        (none :: some padBit :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_eq_paddingPreserving
      (bit :: rest) (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderCellCells_length
    (cell : Option Bool) :
    (selectedSegmentLogicalTapeDecoderCellCells cell).length = 2 := by
  cases cell with
  | none =>
      rfl
  | some bit =>
      cases bit <;> rfl

theorem list_map_const_two_sum {α : Type} (xs : List α) :
    (xs.map (fun _ => 2)).sum = 2 * xs.length := by
  induction xs with
  | nil =>
      rfl
  | cons _ rest ih =>
      change 2 + (rest.map (fun _ => 2)).sum =
        2 * (rest.length + 1)
      rw [ih]
      lia

theorem selectedSegmentLogicalTapeDecoderCellCells_length_sum
    (cells : List (Option Bool)) :
    (cells.map
        (fun cell =>
          (selectedSegmentLogicalTapeDecoderCellCells cell).length)).sum =
      2 * cells.length := by
  simpa [selectedSegmentLogicalTapeDecoderCellCells_length] using
    (list_map_const_two_sum cells)

theorem selectedSegmentLogicalTapeDecoderCellCells_length_comp_sum
    (cells : List (Option Bool)) :
    (List.map
        (List.length ∘ selectedSegmentLogicalTapeDecoderCellCells)
        cells).sum =
      2 * cells.length := by
  simpa [Function.comp_def] using
    selectedSegmentLogicalTapeDecoderCellCells_length_sum cells

theorem selectedSegmentLogicalTapeDecoderCellCells_some_length_comp_sum
    (bits : Word Bool) :
    (List.map
        (List.length ∘ selectedSegmentLogicalTapeDecoderCellCells ∘ some)
        bits).sum =
      2 * bits.length := by
  simpa [Function.comp_def,
    selectedSegmentLogicalTapeDecoderCellCells_length] using
    (list_map_const_two_sum bits)

theorem selectedSegmentLogicalTapeDecoderCellCells_flatten_length
    (cells : List (Option Bool)) :
    ((cells.map selectedSegmentLogicalTapeDecoderCellCells).flatten).length =
      2 * cells.length := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      simp [selectedSegmentLogicalTapeDecoderCellCells_length, ih]
      lia

theorem selectedSegmentLogicalTapeDecoderCellCells_flatten_length_append_none
    (padding : List (Option Bool)) :
    ((List.map selectedSegmentLogicalTapeDecoderCellCells
        (List.append padding [none])).flatten).length =
      2 * padding.length + 2 := by
  rw [selectedSegmentLogicalTapeDecoderCellCells_flatten_length]
  simp
  lia

theorem selectedSegmentLogicalTapeDecoderCellCells_flatten_length_rest_padding
    (rest : Word Bool) (padding : List (Option Bool)) :
    ((List.map selectedSegmentLogicalTapeDecoderCellCells
        (List.append (rest.map some)
          (none :: List.append padding [none]))).flatten).length =
      2 * rest.length + 2 * padding.length + 4 := by
  rw [selectedSegmentLogicalTapeDecoderCellCells_flatten_length]
  simp
  lia

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintCells_length
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
      bits padding).length =
      10 + 2 * bits.length + 2 * padding.length := by
  cases bits with
  | nil =>
      simp [selectedSegmentLogicalTapeDecoderDensifierFootprintCells,
        selectedSegmentLogicalTapeDecoderCellCells_length,
        list_map_const_two_sum,
        Function.comp_def]
      lia
  | cons bit rest =>
      simp [selectedSegmentLogicalTapeDecoderDensifierFootprintCells,
        selectedSegmentLogicalTapeDecoderCellCells_length,
        list_map_const_two_sum,
        Function.comp_def, List.length_append]
      lia

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_length
    (bits : Word Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          bits padding)).length =
      13 + 2 * bits.length + 2 * padding.length := by
  rw [selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint]
  simp [selectedSegmentLogicalTapeDecoderDensifierFootprintCells_length]
  lia

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_length
    (bits : Word Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          bits padding)).length =
      bits.length + padding.length + 1 := by
  rw [selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_eq_paddingPreserving]
  simp
  lia

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap
    (bits : Word Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          bits padding)).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint]
  simp [selectedSegmentLogicalTapeDecoderDensifierFootprintCells_filterMap,
    List.filterMap_append]

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_filterMap
    (bits : Word Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          bits padding)).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_eq_paddingPreserving]
  exact
    selectedSegmentLogicalTapeDecoderDensifierPaddingPreservingCells_filterMap
      bits padding

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap_eq_targetTape_cells_filterMap
    (bits : Word Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          bits padding)).filterMap (fun cell => cell) =
      (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          bits padding)).filterMap (fun cell => cell) := by
  rw [selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap,
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_filterMap]

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap_eq_targetTape_cells_filterMap_nil_nil :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] [])).filterMap (fun cell => cell) =
      (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] [])).filterMap (fun cell => cell) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap_eq_targetTape_cells_filterMap
      [] []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap_eq_targetTape_cells_filterMap_nil_none
    (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (none :: padding))).filterMap (fun cell => cell) =
      (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] (none :: padding))).filterMap (fun cell => cell) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap_eq_targetTape_cells_filterMap
      [] (none :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap_eq_targetTape_cells_filterMap_nil_some
    (padBit : Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (some padBit :: padding))).filterMap (fun cell => cell) =
      (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] (some padBit :: padding))).filterMap (fun cell => cell) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap_eq_targetTape_cells_filterMap
      [] (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap_eq_targetTape_cells_filterMap_cons_nil
    (bit : Bool) (rest : Word Bool) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) [])).filterMap (fun cell => cell) =
      (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) [])).filterMap (fun cell => cell) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap_eq_targetTape_cells_filterMap
      (bit :: rest) []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap_eq_targetTape_cells_filterMap_cons_none
    (bit : Bool) (rest : Word Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (none :: padding))).filterMap (fun cell => cell) =
      (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) (none :: padding))).filterMap (fun cell => cell) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap_eq_targetTape_cells_filterMap
      (bit :: rest) (none :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap_eq_targetTape_cells_filterMap_cons_some
    (bit : Bool) (rest : Word Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (some padBit :: padding))).filterMap
        (fun cell => cell) =
      (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) (some padBit :: padding))).filterMap
        (fun cell => cell) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap_eq_targetTape_cells_filterMap
      (bit :: rest) (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprint_normalizedOutput_eq_nil_nil :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] []) =
      Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] []) := by
  exact selectedSegmentLogicalTapeDecoderDensifierFootprint_normalizedOutput_eq
    [] []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprint_normalizedOutput_eq_nil_none
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (none :: padding)) =
      Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] (none :: padding)) := by
  exact selectedSegmentLogicalTapeDecoderDensifierFootprint_normalizedOutput_eq
    [] (none :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprint_normalizedOutput_eq_nil_some
    (padBit : Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (some padBit :: padding)) =
      Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] (some padBit :: padding)) := by
  exact selectedSegmentLogicalTapeDecoderDensifierFootprint_normalizedOutput_eq
    [] (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprint_normalizedOutput_eq_cons_nil
    (bit : Bool) (rest : Word Bool) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) []) =
      Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) []) := by
  exact selectedSegmentLogicalTapeDecoderDensifierFootprint_normalizedOutput_eq
    (bit :: rest) []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprint_normalizedOutput_eq_cons_none
    (bit : Bool) (rest : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (none :: padding)) =
      Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) (none :: padding)) := by
  exact selectedSegmentLogicalTapeDecoderDensifierFootprint_normalizedOutput_eq
    (bit :: rest) (none :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprint_normalizedOutput_eq_cons_some
    (bit : Bool) (rest : Word Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (some padBit :: padding)) =
      Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) (some padBit :: padding)) := by
  exact selectedSegmentLogicalTapeDecoderDensifierFootprint_normalizedOutput_eq
    (bit :: rest) (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        bits padding =
      rightEdgeRewindSourceTape bits padding := by
  rfl

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape_nil_nil :
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] [] =
      rightEdgeRewindSourceTape [] [] := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape
      [] []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape_nil_none
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] (none :: padding) =
      rightEdgeRewindSourceTape [] (none :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape
      [] (none :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape_nil_some
    (padBit : Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] (some padBit :: padding) =
      rightEdgeRewindSourceTape [] (some padBit :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape
      [] (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape_cons_nil
    (bit : Bool) (rest : Word Bool) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        (bit :: rest) [] =
      rightEdgeRewindSourceTape (bit :: rest) [] := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape
      (bit :: rest) []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape_cons_none
    (bit : Bool) (rest : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        (bit :: rest) (none :: padding) =
      rightEdgeRewindSourceTape (bit :: rest) (none :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape
      (bit :: rest) (none :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape_cons_some
    (bit : Bool) (rest : Word Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        (bit :: rest) (some padBit :: padding) =
      rightEdgeRewindSourceTape (bit :: rest) (some padBit :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape
      (bit :: rest) (some padBit :: padding)

theorem rightEdgeRewindDescription_haltsFrom_selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    rightEdgeRewindDescription.HaltsFromTape
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        bits padding)
      (rightEdgeRewindTargetTape bits padding) := by
  simpa [selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape] using
    rightEdgeRewindDescription_haltsFromTape bits padding

theorem rightEdgeRewindDescription_haltsFrom_selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_nil_nil :
    rightEdgeRewindDescription.HaltsFromTape
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] [])
      (rightEdgeRewindTargetTape [] []) := by
  exact
    rightEdgeRewindDescription_haltsFrom_selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
      [] []

theorem rightEdgeRewindDescription_haltsFrom_selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_nil_none
    (padding : List (Option Bool)) :
    rightEdgeRewindDescription.HaltsFromTape
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] (none :: padding))
      (rightEdgeRewindTargetTape [] (none :: padding)) := by
  exact
    rightEdgeRewindDescription_haltsFrom_selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
      [] (none :: padding)

theorem rightEdgeRewindDescription_haltsFrom_selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_nil_some
    (padBit : Bool) (padding : List (Option Bool)) :
    rightEdgeRewindDescription.HaltsFromTape
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] (some padBit :: padding))
      (rightEdgeRewindTargetTape [] (some padBit :: padding)) := by
  exact
    rightEdgeRewindDescription_haltsFrom_selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
      [] (some padBit :: padding)

theorem rightEdgeRewindDescription_haltsFrom_selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cons_nil
    (bit : Bool) (rest : Word Bool) :
    rightEdgeRewindDescription.HaltsFromTape
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        (bit :: rest) [])
      (rightEdgeRewindTargetTape (bit :: rest) []) := by
  exact
    rightEdgeRewindDescription_haltsFrom_selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
      (bit :: rest) []

theorem rightEdgeRewindDescription_haltsFrom_selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cons_none
    (bit : Bool) (rest : Word Bool) (padding : List (Option Bool)) :
    rightEdgeRewindDescription.HaltsFromTape
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        (bit :: rest) (none :: padding))
      (rightEdgeRewindTargetTape (bit :: rest) (none :: padding)) := by
  exact
    rightEdgeRewindDescription_haltsFrom_selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
      (bit :: rest) (none :: padding)

theorem rightEdgeRewindDescription_haltsFrom_selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cons_some
    (bit : Bool) (rest : Word Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    rightEdgeRewindDescription.HaltsFromTape
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        (bit :: rest) (some padBit :: padding))
      (rightEdgeRewindTargetTape (bit :: rest) (some padBit :: padding)) := by
  exact
    rightEdgeRewindDescription_haltsFrom_selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
      (bit :: rest) (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_nil_source_equiv_target :
    Tape.Equiv
      (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] [])
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] []) := by
  simp [Tape.Equiv,
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape,
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape,
    selectedSegmentLogicalTapeDecoderTargetTape,
    rightEdgeScanSourceTapeFromLeft, rightEdgeRewindSourceTape,
    FSTStatefulOptionAppendTargetTapeFromLeft,
    statefulOptionAppendWriteTargetTapeAtBlank, tapeAtCells,
    statefulOptionCellsFrom, logicalTapeBits, logicalCellListBits,
    logicalCellBits, guardLogicalTape,
    selectedSegmentLogicalTapeDecoderStart,
    selectedSegmentLogicalTapeDecoderNext,
    selectedSegmentLogicalTapeDecoderEmit,
    Tape.dropTrailingNone]

theorem exactIdentityDescription_haltsFromTapeEquiv_selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_nil :
    ExactIdentityDescription.HaltsFromTapeEquiv
      (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] [])
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] []) := by
  refine
    ⟨selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
      [] [], ?_, ?_⟩
  · refine ⟨0, ?_⟩
    constructor <;> rfl
  · exact
      selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_nil_source_equiv_target

theorem selectedSegmentLogicalTapeDecoder_statefulCells_logicalCellListBits_replicate_none_dropTrailingNone
    (n suffixWidth : Nat) :
    Tape.dropTrailingNone
        (List.append
          (statefulOptionCellsFrom selectedSegmentLogicalTapeDecoderNext
            selectedSegmentLogicalTapeDecoderEmit
            selectedSegmentLogicalTapeDecoderStart
            (List.append
              (logicalCellListBits
                (List.replicate n (none : Option Bool)))
              [false, false])).reverse
          (List.replicate suffixWidth (none : Option Bool))) =
      [] := by
  induction n generalizing suffixWidth with
  | zero =>
      simpa [statefulOptionCellsFrom, logicalCellListBits,
        selectedSegmentLogicalTapeDecoderStart,
        selectedSegmentLogicalTapeDecoderNext,
        selectedSegmentLogicalTapeDecoderEmit, List.replicate_succ,
        Nat.add_assoc] using
        FoC.Computability.dropTrailingNone_replicate_none
          (suffixWidth + 2)
  | succ n ih =>
      simpa [List.replicate_succ, logicalCellListBits, logicalCellBits,
        statefulOptionCellsFrom, selectedSegmentLogicalTapeDecoderStart,
        selectedSegmentLogicalTapeDecoderNext,
        selectedSegmentLogicalTapeDecoderEmit, Nat.add_assoc] using
        ih (suffixWidth + 2)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_replicate_none_source_equiv_target
    (n : Nat) :
    Tape.Equiv
      (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] (List.replicate n (none : Option Bool)))
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] (List.replicate n (none : Option Bool))) := by
  induction n with
  | zero =>
      simpa using
        selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_nil_source_equiv_target
  | succ n _ih =>
      simp [Tape.Equiv,
        selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape,
        selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape,
        selectedSegmentLogicalTapeDecoderTargetTape,
        rightEdgeScanSourceTapeFromLeft, rightEdgeRewindSourceTape,
        FSTStatefulOptionAppendTargetTapeFromLeft,
        statefulOptionAppendWriteTargetTapeAtBlank, tapeAtCells,
        statefulOptionCellsFrom, logicalTapeBits, logicalCellListBits,
        logicalCellBits, guardLogicalTape,
        selectedSegmentLogicalTapeDecoderStart,
        selectedSegmentLogicalTapeDecoderNext,
        selectedSegmentLogicalTapeDecoderEmit,
        FoC.Computability.dropTrailingNone_replicate_none,
        Tape.dropTrailingNone]
      simpa using
        selectedSegmentLogicalTapeDecoder_statefulCells_logicalCellListBits_replicate_none_dropTrailingNone
          (n + 1) 9

theorem exactIdentityDescription_haltsFromTapeEquiv_selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_replicate_none
    (n : Nat) :
    ExactIdentityDescription.HaltsFromTapeEquiv
      (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] (List.replicate n (none : Option Bool)))
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] (List.replicate n (none : Option Bool))) := by
  refine
    ⟨selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
      [] (List.replicate n (none : Option Bool)), ?_, ?_⟩
  · refine ⟨0, ?_⟩
    constructor <;> rfl
  · exact
      selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_replicate_none_source_equiv_target
        n

theorem optionList_eq_replicate_none_of_filterMap_eq_nil
    (padding : List (Option Bool))
    (hpadding : padding.filterMap (fun cell => cell) = []) :
    exists n : Nat, padding = List.replicate n (none : Option Bool) := by
  induction padding with
  | nil =>
      exact ⟨0, rfl⟩
  | cons cell rest ih =>
      cases cell with
      | none =>
          have hrest : rest.filterMap (fun cell => cell) = [] := by
            simpa using hpadding
          rcases ih hrest with ⟨n, hn⟩
          exact ⟨n + 1, by simp [hn, List.replicate_succ]⟩
      | some _bit =>
          simp at hpadding

theorem selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_blank_padding_source_equiv_target
    (padding : List (Option Bool))
    (hpadding : padding.filterMap (fun cell => cell) = []) :
    Tape.Equiv
      (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] padding)
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] padding) := by
  rcases optionList_eq_replicate_none_of_filterMap_eq_nil
      padding hpadding with
    ⟨n, rfl⟩
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_replicate_none_source_equiv_target
      n

theorem exactIdentityDescription_haltsFromTapeEquiv_selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_blank_padding
    (padding : List (Option Bool))
    (hpadding : padding.filterMap (fun cell => cell) = []) :
    ExactIdentityDescription.HaltsFromTapeEquiv
      (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] padding)
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] padding) := by
  refine
    ⟨selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
      [] padding, ?_, ?_⟩
  · refine ⟨0, ?_⟩
    constructor <;> rfl
  · exact
      selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_blank_padding_source_equiv_target
        padding hpadding

theorem selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_none_blank_padding_source_equiv_target
    (padding : List (Option Bool))
    (hpadding : padding.filterMap (fun cell => cell) = []) :
    Tape.Equiv
      (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] (none :: padding))
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] (none :: padding)) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_blank_padding_source_equiv_target
      (none :: padding) (by simp [hpadding])

theorem exactIdentityDescription_haltsFromTapeEquiv_selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_none_blank_padding
    (padding : List (Option Bool))
    (hpadding : padding.filterMap (fun cell => cell) = []) :
    ExactIdentityDescription.HaltsFromTapeEquiv
      (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] (none :: padding))
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] (none :: padding)) := by
  exact
    exactIdentityDescription_haltsFromTapeEquiv_selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_blank_padding
      (none :: padding) (by simp [hpadding])

def SelectedSegmentLogicalTapeDecoderFootprintCompactorBlankPaddingCaseSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    compactor.HaltsFromTapeEquiv
      (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] [])
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] []) ∧
    forall padding : List (Option Bool),
      padding.filterMap (fun cell => cell) = [] →
        compactor.HaltsFromTapeEquiv
          (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
            [] (none :: padding))
          (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
            [] (none :: padding))

def SelectedSegmentLogicalTapeDecoderFootprintCompactorBlankPaddingCaseConstruction :
    Prop :=
  exists compactor : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintCompactorBlankPaddingCaseSpec
      compactor

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorBlankPaddingCaseConstruction_core :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorBlankPaddingCaseConstruction := by
  refine
    ⟨ExactIdentityDescription,
      CommonGround.Identity.exactIdentityDescription_subroutineReady,
      ?_, ?_⟩
  · exact
      exactIdentityDescription_haltsFromTapeEquiv_selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_nil
  · intro padding hpadding
    exact
      exactIdentityDescription_haltsFromTapeEquiv_selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_none_blank_padding
        padding hpadding

def SelectedSegmentLogicalTapeDecoderFootprintCompactorPadSymbolCaseSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    compactor.HaltsFromTapeEquiv
      (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] [])
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] []) ∧
    (forall padding : List (Option Bool),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (none :: padding))
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] (none :: padding))) ∧
    (forall (padBit : Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] (some padBit :: padding))) ∧
    (forall (bit : Bool) (rest : Word Bool),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) [])
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) [])) ∧
    (forall (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (none :: padding))
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) (none :: padding))) ∧
    forall (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderFootprintCompactorPadSymbolCaseConstruction :
    Prop :=
  exists compactor : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintCompactorPadSymbolCaseSpec
      compactor

def SelectedSegmentLogicalTapeDecoderFootprintCompactorNilPadSymbolCaseSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    compactor.HaltsFromTapeEquiv
      (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] [])
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] []) ∧
    (forall padding : List (Option Bool),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (none :: padding))
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] (none :: padding))) ∧
    forall (padBit : Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderFootprintCompactorConsPadSymbolCaseSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    (forall (bit : Bool) (rest : Word Bool),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) [])
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) [])) ∧
    (forall (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (none :: padding))
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) (none :: padding))) ∧
    forall (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderFootprintCompactorSplitPadSymbolCaseSpec
    (compactor : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderFootprintCompactorNilPadSymbolCaseSpec
      compactor ∧
    SelectedSegmentLogicalTapeDecoderFootprintCompactorConsPadSymbolCaseSpec
      compactor

def SelectedSegmentLogicalTapeDecoderFootprintCompactorSplitPadSymbolCaseConstruction :
    Prop :=
  exists compactor : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintCompactorSplitPadSymbolCaseSpec
      compactor

def SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    compactor.HaltsFromTapeEquiv
      (rightEndCompactionSourceTape
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          [] []))
      (rightEdgeRewindSourceTape [] []) ∧
    (forall padding : List (Option Bool),
      compactor.HaltsFromTapeEquiv
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            [] (none :: padding)))
        (rightEdgeRewindSourceTape [] (none :: padding))) ∧
    (forall (padBit : Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            [] (some padBit :: padding)))
        (rightEdgeRewindSourceTape [] (some padBit :: padding))) ∧
    (forall (bit : Bool) (rest : Word Bool),
      compactor.HaltsFromTapeEquiv
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            (bit :: rest) []))
        (rightEdgeRewindSourceTape (bit :: rest) [])) ∧
    (forall (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            (bit :: rest) (none :: padding)))
        (rightEdgeRewindSourceTape (bit :: rest) (none :: padding))) ∧
    forall (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            (bit :: rest) (some padBit :: padding)))
        (rightEdgeRewindSourceTape
          (bit :: rest) (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConstruction :
    Prop :=
  exists compactor : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSpec
      compactor

def SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeNilSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    compactor.HaltsFromTapeEquiv
      (rightEndCompactionSourceTape
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          [] []))
      (rightEdgeRewindSourceTape [] []) ∧
    (forall padding : List (Option Bool),
      compactor.HaltsFromTapeEquiv
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            [] (none :: padding)))
        (rightEdgeRewindSourceTape [] (none :: padding))) ∧
    forall (padBit : Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            [] (some padBit :: padding)))
        (rightEdgeRewindSourceTape [] (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConsSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    (forall (bit : Bool) (rest : Word Bool),
      compactor.HaltsFromTapeEquiv
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            (bit :: rest) []))
        (rightEdgeRewindSourceTape (bit :: rest) [])) ∧
    (forall (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            (bit :: rest) (none :: padding)))
        (rightEdgeRewindSourceTape (bit :: rest) (none :: padding))) ∧
    forall (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            (bit :: rest) (some padBit :: padding)))
        (rightEdgeRewindSourceTape
          (bit :: rest) (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitSpec
    (compactor : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeNilSpec
      compactor ∧
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConsSpec
      compactor

def SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitConstruction :
    Prop :=
  exists compactor : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitSpec
      compactor

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorPadSymbolCaseConstruction_of_split
    (hsplit :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorSplitPadSymbolCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorPadSymbolCaseConstruction := by
  rcases hsplit with ⟨compactor, hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  exact
    ⟨compactor, hready, hnilNil, hnilNone, hnilSome,
      hconsNil, hconsNone, hconsSome⟩

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction_of_padSymbolCases
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorPadSymbolCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction := by
  rcases hcases with
    ⟨compactor, hready, hnilNil, hnilNone, hnilSome, hconsNil,
      hconsNone, hconsSome⟩
  refine ⟨compactor, hready, hnilNil, ?_, hconsNil, ?_⟩
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

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorSplitPadSymbolCaseConstruction_of_rightEndBridge
    (hbridge :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorSplitPadSymbolCaseConstruction := by
  rcases hbridge with
    ⟨compactor, hready, hnilNil, hnilNone, hnilSome, hconsNil,
      hconsNone, hconsSome⟩
  refine ⟨compactor, ?_, ?_⟩
  · refine ⟨hready, ?_, ?_, ?_⟩
    · simpa [
        selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape_nil_nil,
        selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape_nil_nil] using
        hnilNil
    · intro padding
      simpa [
        selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape_nil_none,
        selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape_nil_none] using
        hnilNone padding
    · intro padBit padding
      simpa [
        selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape_nil_some,
        selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape_nil_some] using
        hnilSome padBit padding
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro bit rest
      simpa [
        selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape_cons_nil,
        selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape_cons_nil] using
        hconsNil bit rest
    · intro bit rest padding
      simpa [
        selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape_cons_none,
        selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape_cons_none] using
        hconsNone bit rest padding
    · intro bit rest padBit padding
      simpa [
        selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape_cons_some,
        selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape_cons_some] using
        hconsSome bit rest padBit padding

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConstruction_of_split
    (hsplit :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConstruction := by
  rcases hsplit with ⟨compactor, hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  exact
    ⟨compactor, hready, hnilNil, hnilNone, hnilSome,
      hconsNil, hconsNone, hconsSome⟩

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitConstruction_core :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitConstruction := by
  sorry

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConstruction_core :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConstruction := by
  exact
    selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConstruction_of_split
      selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitConstruction_core

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorSplitPadSymbolCaseConstruction_core :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorSplitPadSymbolCaseConstruction := by
  exact
    selectedSegmentLogicalTapeDecoderFootprintCompactorSplitPadSymbolCaseConstruction_of_rightEndBridge
      selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConstruction_core

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorPadSymbolCaseConstruction_core :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorPadSymbolCaseConstruction := by
  exact
    selectedSegmentLogicalTapeDecoderFootprintCompactorPadSymbolCaseConstruction_of_split
      selectedSegmentLogicalTapeDecoderFootprintCompactorSplitPadSymbolCaseConstruction_core

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction_core :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction := by
  exact
    selectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction_of_padSymbolCases
      selectedSegmentLogicalTapeDecoderFootprintCompactorPadSymbolCaseConstruction_core

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

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        (encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1])
        bits padding := by
  exact
    selectedSegmentLogicalTapeDecoderTargetTape_cells_rightEdgeScanSourceTapeFromLeft_eq_densifierSource
      (encodedStructuredTapeCellsPrefix
        [guardLogicalTape T0, guardLogicalTape T1])
      bits padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_cells
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          bits padding) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        [] bits padding := by
  exact
    selectedSegmentLogicalTapeDecoderTargetTape_cells_rightEdgeScanSourceTapeFromLeft_eq_densifierSource
      [] bits padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
        bits padding =
      selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        bits padding := by
  rfl

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape_nil_nil :
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
        [] [] =
      selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] [] := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape
      [] []

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape_nil_none
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
        [] (none :: padding) =
      selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] (none :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape
      [] (none :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape_nil_some
    (padBit : Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
        [] (some padBit :: padding) =
      selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] (some padBit :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape
      [] (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape_cons_nil
    (bit : Bool) (rest : Word Bool) :
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
        (bit :: rest) [] =
      selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        (bit :: rest) [] := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape
      (bit :: rest) []

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape_cons_none
    (bit : Bool) (rest : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
        (bit :: rest) (none :: padding) =
      selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        (bit :: rest) (none :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape
      (bit :: rest) (none :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape_cons_some
    (bit : Bool) (rest : Word Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
        (bit :: rest) (some padBit :: padding) =
      selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        (bit :: rest) (some padBit :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape
      (bit :: rest) (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding) =
      List.append
        ((encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1]).filterMap
            (fun cell => cell))
        (List.append bits (padding.filterMap (fun cell => cell))) := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape]
  rw [selectedSegmentLogicalTapeDecoderTargetTape_normalizedOutput]
  rw [rightEdgeScanSourceTapeFromLeft_singleBlank_normalizedOutput]

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_normalizedOutput
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          bits padding) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape]
  rw [selectedSegmentLogicalTapeDecoderTargetTape_normalizedOutput]
  rw [rightEdgeScanSourceTapeFromLeft_singleBlank_normalizedOutput]
  simp

theorem encodedStructuredTapeCellsPrefix_two_guarded_filterMap
    (T0 T1 : Tape Bool) :
    (encodedStructuredTapeCellsPrefix
        [guardLogicalTape T0, guardLogicalTape T1]).filterMap
        (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (logicalTapeBits (guardLogicalTape T1)) := by
  simp [encodedStructuredTapeCellsPrefix, tapeSeparatorCells,
    logicalTapeCode_eq_map_some,
    List.filterMap_append, Function.comp_def]

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput_eq_guardedBits_append_targetTape_normalizedOutput
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (Tape.normalizedOutput
            (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
              bits padding))) := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput,
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_normalizedOutput]
  rw [encodedStructuredTapeCellsPrefix_two_guarded_filterMap]
  simp [List.append_assoc]

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput_eq_guardedBits_append_targetTape_normalizedOutput_nil_nil
    (T0 T1 : Tape Bool) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] []) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (Tape.normalizedOutput
            (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
              [] []))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput_eq_guardedBits_append_targetTape_normalizedOutput
      T0 T1 [] []

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput_eq_guardedBits_append_targetTape_normalizedOutput_nil_none
    (T0 T1 : Tape Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (none :: padding)) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (Tape.normalizedOutput
            (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
              [] (none :: padding)))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput_eq_guardedBits_append_targetTape_normalizedOutput
      T0 T1 [] (none :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput_eq_guardedBits_append_targetTape_normalizedOutput_nil_some
    (T0 T1 : Tape Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (some padBit :: padding)) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (Tape.normalizedOutput
            (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
              [] (some padBit :: padding)))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput_eq_guardedBits_append_targetTape_normalizedOutput
      T0 T1 [] (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput_eq_guardedBits_append_targetTape_normalizedOutput_cons_nil
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) []) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (Tape.normalizedOutput
            (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
              (bit :: rest) []))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput_eq_guardedBits_append_targetTape_normalizedOutput
      T0 T1 (bit :: rest) []

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput_eq_guardedBits_append_targetTape_normalizedOutput_cons_none
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (none :: padding)) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (Tape.normalizedOutput
            (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
              (bit :: rest) (none :: padding)))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput_eq_guardedBits_append_targetTape_normalizedOutput
      T0 T1 (bit :: rest) (none :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput_eq_guardedBits_append_targetTape_normalizedOutput_cons_some
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
    (padBit : Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (some padBit :: padding)) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (Tape.normalizedOutput
            (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
              (bit :: rest) (some padBit :: padding)))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput_eq_guardedBits_append_targetTape_normalizedOutput
      T0 T1 (bit :: rest) (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding)).filterMap (fun cell => cell) =
      List.append
        ((encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1]).filterMap
            (fun cell => cell))
        (List.append bits (padding.filterMap (fun cell => cell))) := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells]
  exact
    selectedSegmentLogicalTapeDecoderDensifierSourceCells_filterMap
      (encodedStructuredTapeCellsPrefix
        [guardLogicalTape T0, guardLogicalTape T1])
      bits padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding)).filterMap (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (List.append bits (padding.filterMap (fun cell => cell)))) := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap,
    encodedStructuredTapeCellsPrefix_two_guarded_filterMap]
  simp [List.append_assoc]

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_nil_nil
    (T0 T1 : Tape Bool) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] [])).filterMap (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (logicalTapeBits (guardLogicalTape T1)) := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits]
  simp

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_nil_none
    (T0 T1 : Tape Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (none :: padding))).filterMap (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (padding.filterMap (fun cell => cell))) := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits]
  simp

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_nil_some
    (T0 T1 : Tape Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (some padBit :: padding))).filterMap
        (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (padBit :: padding.filterMap (fun cell => cell))) := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits]
  simp

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_cons_nil
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) [])).filterMap (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (bit :: rest)) := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits]
  simp

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_cons_none
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (none :: padding))).filterMap
        (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (List.append (bit :: rest)
            (padding.filterMap (fun cell => cell)))) := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits]
  simp

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_cons_some
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
    (padBit : Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (some padBit :: padding))).filterMap
        (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (List.append (bit :: rest)
            (padBit :: padding.filterMap (fun cell => cell)))) := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits]
  simp

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_cells_filterMap
    (bits : Word Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          bits padding)).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_cells]
  simpa using
    selectedSegmentLogicalTapeDecoderDensifierSourceCells_filterMap
      [] bits padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_append_targetTape_cells_filterMap
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding)).filterMap (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          ((Tape.cells
            (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
              bits padding)).filterMap (fun cell => cell))) := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits,
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_cells_filterMap]

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_append_targetTape_cells_filterMap_nil_nil
    (T0 T1 : Tape Bool) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] [])).filterMap (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          ((Tape.cells
            (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
              [] [])).filterMap (fun cell => cell))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_append_targetTape_cells_filterMap
      T0 T1 [] []

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_append_targetTape_cells_filterMap_nil_none
    (T0 T1 : Tape Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (none :: padding))).filterMap (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          ((Tape.cells
            (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
              [] (none :: padding))).filterMap (fun cell => cell))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_append_targetTape_cells_filterMap
      T0 T1 [] (none :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_append_targetTape_cells_filterMap_nil_some
    (T0 T1 : Tape Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (some padBit :: padding))).filterMap
        (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          ((Tape.cells
            (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
              [] (some padBit :: padding))).filterMap
              (fun cell => cell))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_append_targetTape_cells_filterMap
      T0 T1 [] (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_append_targetTape_cells_filterMap_cons_nil
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) [])).filterMap (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          ((Tape.cells
            (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
              (bit :: rest) [])).filterMap (fun cell => cell))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_append_targetTape_cells_filterMap
      T0 T1 (bit :: rest) []

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_append_targetTape_cells_filterMap_cons_none
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (none :: padding))).filterMap
        (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          ((Tape.cells
            (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
              (bit :: rest) (none :: padding))).filterMap
              (fun cell => cell))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_append_targetTape_cells_filterMap
      T0 T1 (bit :: rest) (none :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_append_targetTape_cells_filterMap_cons_some
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
    (padBit : Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (some padBit :: padding))).filterMap
        (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          ((Tape.cells
            (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
              (bit :: rest) (some padBit :: padding))).filterMap
              (fun cell => cell))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_append_targetTape_cells_filterMap
      T0 T1 (bit :: rest) (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierSourceCells_eq_prefix_append_nil
    (encodedPrefix : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierSourceCells
        encodedPrefix bits padding =
      List.append encodedPrefix
        (selectedSegmentLogicalTapeDecoderDensifierSourceCells
          [] bits padding) := by
  simp [selectedSegmentLogicalTapeDecoderDensifierSourceCells]

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding) =
      List.append
        (encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1])
        (Tape.cells
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            bits padding)) := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells,
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_cells]
  exact
    selectedSegmentLogicalTapeDecoderDensifierSourceCells_eq_prefix_append_nil
      (encodedStructuredTapeCellsPrefix
        [guardLogicalTape T0, guardLogicalTape T1])
      bits padding

theorem encodedStructuredTapeCellsPrefix_two_guarded_eq
    (T0 T1 : Tape Bool) :
    encodedStructuredTapeCellsPrefix
        [guardLogicalTape T0, guardLogicalTape T1] =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape T0))
          (List.append tapeSeparatorCells
            (logicalTapeCode (guardLogicalTape T1)))) := by
  simp [encodedStructuredTapeCellsPrefix]

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_targetTape_cells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape T0))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode (guardLogicalTape T1))
              (Tape.cells
                (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
                  bits padding))))) := by
  rw [
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells,
    encodedStructuredTapeCellsPrefix_two_guarded_eq]
  simp [List.append_assoc]

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_targetTape_cells_nil_nil
    (T0 T1 : Tape Bool) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] []) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape T0))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode (guardLogicalTape T1))
              (Tape.cells
                (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
                  [] []))))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_targetTape_cells
      T0 T1 [] []

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_targetTape_cells_nil_none
    (T0 T1 : Tape Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (none :: padding)) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape T0))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode (guardLogicalTape T1))
              (Tape.cells
                (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
                  [] (none :: padding)))))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_targetTape_cells
      T0 T1 [] (none :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_targetTape_cells_nil_some
    (T0 T1 : Tape Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (some padBit :: padding)) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape T0))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode (guardLogicalTape T1))
              (Tape.cells
                (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
                  [] (some padBit :: padding)))))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_targetTape_cells
      T0 T1 [] (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_targetTape_cells_cons_nil
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) []) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape T0))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode (guardLogicalTape T1))
              (Tape.cells
                (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
                  (bit :: rest) []))))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_targetTape_cells
      T0 T1 (bit :: rest) []

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_targetTape_cells_cons_none
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (none :: padding)) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape T0))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode (guardLogicalTape T1))
              (Tape.cells
                (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
                  (bit :: rest) (none :: padding)))))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_targetTape_cells
      T0 T1 (bit :: rest) (none :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_targetTape_cells_cons_some
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
    (padBit : Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (some padBit :: padding)) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape T0))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode (guardLogicalTape T1))
              (Tape.cells
                (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
                  (bit :: rest) (some padBit :: padding)))))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_targetTape_cells
      T0 T1 (bit :: rest) (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells_nil_nil
    (T0 T1 : Tape Bool) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] []) =
      List.append
        (encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1])
        (Tape.cells
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            [] [])) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells
      T0 T1 [] []

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells_nil_cons
    (T0 T1 : Tape Bool) (pad : Option Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (pad :: padding)) =
      List.append
        (encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1])
        (Tape.cells
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            [] (pad :: padding))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells
      T0 T1 [] (pad :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells_nil_none
    (T0 T1 : Tape Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (none :: padding)) =
      List.append
        (encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1])
        (Tape.cells
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            [] (none :: padding))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells_nil_cons
      T0 T1 none padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells_nil_some
    (T0 T1 : Tape Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (some padBit :: padding)) =
      List.append
        (encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1])
        (Tape.cells
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            [] (some padBit :: padding))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells_nil_cons
      T0 T1 (some padBit) padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells_cons_nil
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) []) =
      List.append
        (encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1])
        (Tape.cells
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            (bit :: rest) [])) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells
      T0 T1 (bit :: rest) []

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells_cons_cons
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
    (pad : Option Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (pad :: padding)) =
      List.append
        (encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1])
        (Tape.cells
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            (bit :: rest) (pad :: padding))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells
      T0 T1 (bit :: rest) (pad :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells_cons_none
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (none :: padding)) =
      List.append
        (encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1])
        (Tape.cells
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            (bit :: rest) (none :: padding))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells_cons_cons
      T0 T1 bit rest none padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells_cons_some
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
    (padBit : Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (some padBit :: padding)) =
      List.append
        (encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1])
        (Tape.cells
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            (bit :: rest) (some padBit :: padding))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells_cons_cons
      T0 T1 bit rest (some padBit) padding

theorem logicalCellCode_length
    (cell : Option Bool) :
    (logicalCellCode cell).length = 2 := by
  cases cell with
  | none =>
      rfl
  | some bit =>
      cases bit <;> rfl

theorem logicalCellBits_length
    (cell : Option Bool) :
    (logicalCellBits cell).length = 2 := by
  cases cell with
  | none =>
      rfl
  | some bit =>
      cases bit <;> rfl

theorem logicalCellListBits_length
    (cells : List (Option Bool)) :
    (logicalCellListBits cells).length = 2 * cells.length := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      simp [logicalCellListBits, logicalCellBits_length, ih]
      lia

theorem logicalCellListCode_length
    (cells : List (Option Bool)) :
    (logicalCellListCode cells).length = 2 * cells.length := by
  rw [logicalCellListCode_eq_map_some]
  simp [logicalCellListBits_length]

theorem logicalTapeBits_length
    (T : Tape Bool) :
    (logicalTapeBits T).length =
      2 * T.left.length + 2 * T.right.length + 4 := by
  simp [logicalTapeBits, logicalCellListBits_length,
    logicalCellBits_length]
  lia

theorem logicalTapeCode_length
    (T : Tape Bool) :
    (logicalTapeCode T).length =
      2 * T.left.length + 2 * T.right.length + 4 := by
  rw [logicalTapeCode_eq_map_some]
  simp [logicalTapeBits_length]

theorem logicalTapeCode_guardLogicalTape_length
    (T : Tape Bool) :
    (logicalTapeCode (guardLogicalTape T)).length =
      2 * T.left.length + 2 * T.right.length + 8 := by
  simp [guardLogicalTape, logicalTapeCode_length]
  lia

theorem encodedStructuredTapeCellsPrefix_two_guarded_length
    (T0 T1 : Tape Bool) :
    (encodedStructuredTapeCellsPrefix
        [guardLogicalTape T0, guardLogicalTape T1]).length =
      2 * T0.left.length + 2 * T0.right.length +
        (2 * T1.left.length + 2 * T1.right.length) + 18 := by
  rw [encodedStructuredTapeCellsPrefix_two_guarded_eq]
  simp [logicalTapeCode_guardLogicalTape_length]
  lia

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_cells_length
    (bits : Word Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          bits padding)).length =
      13 + 2 * bits.length + 2 * padding.length := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_cells]
  simp [selectedSegmentLogicalTapeDecoderDensifierSourceCells,
    selectedSegmentLogicalTapeDecoderDensifierFootprintCells_length]
  lia

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_length
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding)).length =
      2 * T0.left.length + 2 * T0.right.length +
        (2 * T1.left.length + 2 * T1.right.length) +
          (31 + 2 * bits.length + 2 * padding.length) := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells]
  simp [logicalTapeCode_guardLogicalTape_length,
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_cells_length]
  lia

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

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall T0 T1 : Tape Bool,
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] [])
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          [] [])) ∧
    (forall (T0 T1 : Tape Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (none :: padding))
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          [] (none :: padding))) ∧
    (forall (T0 T1 : Tape Bool) (padBit : Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          [] (some padBit :: padding))) ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) [])
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) [])) ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (none :: padding))
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) (none :: padding))) ∧
    forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseConstruction :
    Prop :=
  exists eraser : MachineDescription,
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseSpec
      eraser

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserNilPadSymbolCaseSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall T0 T1 : Tape Bool,
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] [])
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          [] [])) ∧
    (forall (T0 T1 : Tape Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (none :: padding))
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          [] (none :: padding))) ∧
    forall (T0 T1 : Tape Bool) (padBit : Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          [] (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConsPadSymbolCaseSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) [])
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) [])) ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (none :: padding))
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) (none :: padding))) ∧
    forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec
    (eraser : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserNilPadSymbolCaseSpec
      eraser ∧
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConsPadSymbolCaseSpec
      eraser

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction :
    Prop :=
  exists eraser : MachineDescription,
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec
      eraser

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffNilPadSymbolCaseSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall T0 T1 : Tape Bool,
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] [])
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] [])) ∧
    (forall (T0 T1 : Tape Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (none :: padding))
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (none :: padding))) ∧
    forall (T0 T1 : Tape Bool) (padBit : Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConsPadSymbolCaseSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) [])
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) [])) ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (none :: padding))
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (none :: padding))) ∧
    forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec
    (eraser : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffNilPadSymbolCaseSpec
      eraser ∧
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConsPadSymbolCaseSpec
      eraser

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction :
    Prop :=
  exists eraser : MachineDescription,
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec
      eraser

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseConstruction_of_split
    (hsplit :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseConstruction := by
  rcases hsplit with ⟨eraser, hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  exact
    ⟨eraser, hready, hnilNil, hnilNone, hnilSome,
      hconsNil, hconsNone, hconsSome⟩

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseConstruction_of_padSymbolCases
    (hcases :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseConstruction := by
  rcases hcases with
    ⟨eraser, hready, hnilNil, hnilNone, hnilSome, hconsNil,
      hconsNone, hconsSome⟩
  refine ⟨eraser, hready, hnilNil, ?_, hconsNil, ?_⟩
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

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction_of_footprintHandoff
    (hhandoff :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction := by
  rcases hhandoff with ⟨eraser, hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  refine ⟨eraser, ?_, ?_⟩
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro T0 T1
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape_nil_nil] using
        hnilNil T0 T1
    · intro T0 T1 padding
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape_nil_none] using
        hnilNone T0 T1 padding
    · intro T0 T1 padBit padding
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape_nil_some] using
        hnilSome T0 T1 padBit padding
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro T0 T1 bit rest
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape_cons_nil] using
        hconsNil T0 T1 bit rest
    · intro T0 T1 bit rest padding
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape_cons_none] using
        hconsNone T0 T1 bit rest padding
    · intro T0 T1 bit rest padBit padding
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape_cons_some] using
        hconsSome T0 T1 bit rest padBit padding

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

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction_core :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction := by
  sorry

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction_core :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction_of_footprintHandoff
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction_core

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseConstruction_core :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseConstruction := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseConstruction_of_split
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction_core

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseConstruction_core :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseConstruction := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseConstruction_of_padSymbolCases
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseConstruction_core

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
