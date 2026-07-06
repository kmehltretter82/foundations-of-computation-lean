import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.Scaffold

set_option doc.verso true

/-!
# Padded tail-cleanup scaffold output endpoints

This module re-exports the post-padding normalized-output contracts at the
tail-emitter scaffold boundary.  The exact scaffold remains the construction
used by the executable selected-projection route; these wrappers give callers a
stable output-only interface when the final cursor position is irrelevant.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

abbrev SelectedProjectionPaddedTailCleanupOutputSpec
    (useAccept : Bool) (cleanup : MachineDescription) : Prop :=
  SelectedProjectionPaddedTailCleanup.SelectedProjectionPaddedTailCleanupOutputSpec
    useAccept cleanup

abbrev SelectedProjectionPaddedTailCleanupOutputConstruction : Prop :=
  SelectedProjectionPaddedTailCleanup.SelectedProjectionPaddedTailCleanupOutputConstruction

abbrev SelectedProjectionPaddedTailCleanupExactShapeOutputSpec
    (useAccept : Bool) (cleanup : MachineDescription) : Prop :=
  SelectedProjectionPaddedTailCleanup.SelectedProjectionPaddedTailCleanupExactShapeOutputSpec
    useAccept cleanup

abbrev SelectedProjectionPaddedTailCleanupExactShapeOutputConstruction :
    Prop :=
  SelectedProjectionPaddedTailCleanup.SelectedProjectionPaddedTailCleanupExactShapeOutputConstruction

abbrev SelectedProjectionPaddedTailEmitterOutputSpec
    (useAccept : Bool) (tail : MachineDescription) : Prop :=
  SelectedProjectionPaddedTailCleanup.SelectedProjectionPaddedTailEmitterOutputSpec
    useAccept tail

abbrev SelectedProjectionPaddedTailEmitterOutputConstruction : Prop :=
  SelectedProjectionPaddedTailCleanup.SelectedProjectionPaddedTailEmitterOutputConstruction

theorem selectedProjectionPaddedTailCleanupOutputSpec_of_exact
    {useAccept : Bool} {cleanup : MachineDescription}
    (hcleanup :
      SelectedProjectionPaddedTailCleanupSpec useAccept cleanup) :
    SelectedProjectionPaddedTailCleanupOutputSpec useAccept cleanup :=
  SelectedProjectionPaddedTailCleanup.selectedProjectionPaddedTailCleanupOutputSpec_of_exact
    hcleanup

theorem selectedProjectionPaddedTailCleanupOutputConstruction_of_exact
    (hcleanup :
      SelectedProjectionPaddedTailCleanupConstruction) :
    SelectedProjectionPaddedTailCleanupOutputConstruction :=
  SelectedProjectionPaddedTailCleanup.selectedProjectionPaddedTailCleanupOutputConstruction_of_exact
    hcleanup

theorem selectedProjectionPaddedTailCleanupExactShapeOutputSpec_of_exact
    {useAccept : Bool} {cleanup : MachineDescription}
    (hcleanup :
      SelectedProjectionPaddedTailCleanupExactShapeSpec useAccept cleanup) :
    SelectedProjectionPaddedTailCleanupExactShapeOutputSpec
      useAccept cleanup :=
  SelectedProjectionPaddedTailCleanup.selectedProjectionPaddedTailCleanupExactShapeOutputSpec_of_exact
    hcleanup

theorem selectedProjectionPaddedTailCleanupExactShapeOutputConstruction_of_exact
    (hcleanup :
      SelectedProjectionPaddedTailCleanupExactShapeConstruction) :
    SelectedProjectionPaddedTailCleanupExactShapeOutputConstruction :=
  SelectedProjectionPaddedTailCleanup.selectedProjectionPaddedTailCleanupExactShapeOutputConstruction_of_exact
    hcleanup

theorem selectedProjectionPaddedTailCleanupOutputSpec_of_exactShapeOutputSpec
    {useAccept : Bool} {cleanup : MachineDescription}
    (hcleanup :
      SelectedProjectionPaddedTailCleanupExactShapeOutputSpec
        useAccept cleanup) :
    SelectedProjectionPaddedTailCleanupOutputSpec useAccept cleanup :=
  SelectedProjectionPaddedTailCleanup.selectedProjectionPaddedTailCleanupOutputSpec_of_exactShapeOutputSpec
    hcleanup

theorem selectedProjectionPaddedTailCleanupOutputConstruction_of_exactShapeOutput
    (hcleanup :
      SelectedProjectionPaddedTailCleanupExactShapeOutputConstruction) :
    SelectedProjectionPaddedTailCleanupOutputConstruction :=
  SelectedProjectionPaddedTailCleanup.selectedProjectionPaddedTailCleanupOutputConstruction_of_exactShapeOutput
    hcleanup

theorem selectedProjectionPaddedTailEmitterOutputSpec_of_exact
    {useAccept : Bool} {tail : MachineDescription}
    (htail :
      SelectedProjectionPaddedTailEmitterSpec useAccept tail) :
    SelectedProjectionPaddedTailEmitterOutputSpec useAccept tail :=
  SelectedProjectionPaddedTailCleanup.selectedProjectionPaddedTailEmitterOutputSpec_of_exact
    htail

theorem selectedProjectionPaddedTailEmitterOutputConstruction_of_exact
    (htail :
      SelectedProjectionPaddedTailEmitterConstruction) :
    SelectedProjectionPaddedTailEmitterOutputConstruction :=
  SelectedProjectionPaddedTailCleanup.selectedProjectionPaddedTailEmitterOutputConstruction_of_exact
    htail

theorem selectedProjectionPaddedTailEmitterOutputConstruction_of_cleanup
    (hcleanup :
      SelectedProjectionPaddedTailCleanupConstruction) :
    SelectedProjectionPaddedTailEmitterOutputConstruction :=
  selectedProjectionPaddedTailEmitterOutputConstruction_of_exact
    (selectedProjectionPaddedTailEmitterConstruction_of_cleanup hcleanup)

theorem selectedProjectionPaddedTailCleanupExactShapeOutputConstruction_scaffold_of_postErase
    (hpostEraseConstruction :
      SelectedProjectionPaddedTailCleanup.SelectedProjectionPaddedTailCleanupPostEraseConstruction) :
    SelectedProjectionPaddedTailCleanupExactShapeOutputConstruction :=
  SelectedProjectionPaddedTailCleanup.selectedProjectionPaddedTailCleanupExactShapeOutputConstruction_of_postErase
    hpostEraseConstruction

theorem selectedProjectionPaddedTailCleanupOutputConstruction_scaffold_of_postErase
    (hpostEraseConstruction :
      SelectedProjectionPaddedTailCleanup.SelectedProjectionPaddedTailCleanupPostEraseConstruction) :
    SelectedProjectionPaddedTailCleanupOutputConstruction :=
  SelectedProjectionPaddedTailCleanup.selectedProjectionPaddedTailCleanupOutputConstruction_of_postErase
    hpostEraseConstruction

theorem selectedProjectionPaddedTailEmitterOutputConstruction_scaffold_of_postErase
    (hpostEraseConstruction :
      SelectedProjectionPaddedTailCleanup.SelectedProjectionPaddedTailCleanupPostEraseConstruction) :
    SelectedProjectionPaddedTailEmitterOutputConstruction :=
  selectedProjectionPaddedTailEmitterOutputConstruction_of_exact
    (selectedProjectionPaddedTailEmitterConstruction_scaffold_of_postErase
      hpostEraseConstruction)

theorem selectedProjectionPaddedTailCleanupOutputConstruction_scaffold :
    SelectedProjectionPaddedTailCleanupOutputConstruction :=
  selectedProjectionPaddedTailCleanupOutputConstruction_scaffold_of_postErase
    SelectedProjectionPaddedTailCleanup.selectedProjectionPaddedTailCleanupPostEraseConstruction

theorem selectedProjectionPaddedTailCleanupExactShapeOutputConstruction_scaffold :
    SelectedProjectionPaddedTailCleanupExactShapeOutputConstruction :=
  selectedProjectionPaddedTailCleanupExactShapeOutputConstruction_scaffold_of_postErase
    SelectedProjectionPaddedTailCleanup.selectedProjectionPaddedTailCleanupPostEraseConstruction

theorem selectedProjectionPaddedTailEmitterOutputConstruction_scaffold :
    SelectedProjectionPaddedTailEmitterOutputConstruction :=
  selectedProjectionPaddedTailEmitterOutputConstruction_scaffold_of_postErase
    SelectedProjectionPaddedTailCleanup.selectedProjectionPaddedTailCleanupPostEraseConstruction

theorem selectedProjectionPaddedTailEmitterOutputConstruction_scaffold_of_prefixAndFootprintCases
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    SelectedProjectionPaddedTailEmitterOutputConstruction :=
  selectedProjectionPaddedTailEmitterOutputConstruction_of_exact
    (selectedProjectionPaddedTailEmitterConstruction_scaffold_of_prefixAndFootprintCases
      hprefix hcases)

theorem selectedProjectionPaddedTailEmitterOutputConstruction_scaffold_of_prefixAndFootprintBitPaddingCases
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionPaddedTailEmitterOutputConstruction :=
  selectedProjectionPaddedTailEmitterOutputConstruction_of_exact
    (selectedProjectionPaddedTailEmitterConstruction_scaffold_of_prefixAndFootprintBitPaddingCases
      hprefix hcases)

theorem selectedProjectionPaddedTailEmitterOutputConstruction_scaffold_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
    (heraser :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionPaddedTailEmitterOutputConstruction :=
  selectedProjectionPaddedTailEmitterOutputConstruction_of_exact
    (selectedProjectionPaddedTailEmitterConstruction_scaffold_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
      heraser hcases)

theorem selectedProjectionPaddedTailCleanupOutputConstruction_scaffold_of_prefixAndFootprintCases
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    SelectedProjectionPaddedTailCleanupOutputConstruction :=
  selectedProjectionPaddedTailCleanupOutputConstruction_scaffold_of_postErase
    (SelectedProjectionPaddedTailCleanup.selectedProjectionPaddedTailCleanupPostEraseConstruction_of_prefixAndFootprintCases
      hprefix hcases)

theorem selectedProjectionPaddedTailCleanupOutputConstruction_scaffold_of_prefixAndFootprintBitPaddingCases
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionPaddedTailCleanupOutputConstruction :=
  selectedProjectionPaddedTailCleanupOutputConstruction_scaffold_of_postErase
    (SelectedProjectionPaddedTailCleanup.selectedProjectionPaddedTailCleanupPostEraseConstruction_of_prefixAndFootprintBitPaddingCases
      hprefix hcases)

theorem selectedProjectionPaddedTailCleanupOutputConstruction_scaffold_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
    (heraser :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionPaddedTailCleanupOutputConstruction :=
  selectedProjectionPaddedTailCleanupOutputConstruction_scaffold_of_postErase
    (SelectedProjectionPaddedTailCleanup.selectedProjectionPaddedTailCleanupPostEraseConstruction_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
      heraser hcases)

theorem selectedProjectionPaddedTailEmitterOutputConstruction_of_postPadding
    (hpostPadding :
      SelectedProjectionPaddedTailCleanup.SelectedProjectionPaddedTailCleanupPostPaddingConstruction) :
    SelectedProjectionPaddedTailEmitterOutputConstruction :=
  selectedProjectionPaddedTailEmitterOutputConstruction_scaffold_of_postErase
    (SelectedProjectionPaddedTailCleanup.selectedProjectionPaddedTailCleanupPostEraseConstruction_of_postPadding
      hpostPadding)

theorem selectedProjectionPaddedTailEmitterOutputConstruction_of_prefixAndFootprintCases
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    SelectedProjectionPaddedTailEmitterOutputConstruction :=
  selectedProjectionPaddedTailEmitterOutputConstruction_of_exact
    (selectedProjectionPaddedTailEmitterConstruction_scaffold_of_prefixAndFootprintCases
      hprefix hcases)

theorem selectedProjectionPaddedTailEmitterOutputConstruction_of_prefixAndFootprintBitPaddingCases
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionPaddedTailEmitterOutputConstruction :=
  selectedProjectionPaddedTailEmitterOutputConstruction_of_exact
    (selectedProjectionPaddedTailEmitterConstruction_scaffold_of_prefixAndFootprintBitPaddingCases
      hprefix hcases)

theorem selectedProjectionPaddedTailEmitterOutputConstruction_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
    (heraser :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionPaddedTailEmitterOutputConstruction :=
  selectedProjectionPaddedTailEmitterOutputConstruction_of_exact
    (selectedProjectionPaddedTailEmitterConstruction_scaffold_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
      heraser hcases)

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
