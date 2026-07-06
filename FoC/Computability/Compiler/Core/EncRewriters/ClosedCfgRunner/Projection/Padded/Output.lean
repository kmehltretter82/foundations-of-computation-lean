import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.Main

set_option doc.verso true

/-!
# Padded selected-projection output endpoints

This module gives the padded selected-projection assembly a normalized-output
interface parallel to the exact/equivalence construction in
{module}`FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.Main`.
It is intentionally weaker than the public finite-description construction:
the exact route still carries closedness and tape-equivalence obligations, while
the contracts here expose only the emitted decoded word.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

private theorem haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
    {D : MachineDescription} {Tin Tout : Tape Bool}
    (h : D.HaltsFromTapeEquiv Tin Tout) :
    D.HaltsFromTapeWithOutput Tin (Tape.normalizedOutput Tout) :=
  MachineDescription.haltsFromTapeWithOutput_of_haltsFromTapeEquiv h

def SelectedProjectionCheckedEquivPaddedEmitterOutputSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall L : DovetailLayout,
      emitter.HaltsFromTapeWithOutput
        (ParsedLayoutCheckedTape L)
        (Tape.normalizedOutput
          (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L))

def SelectedProjectionCheckedEquivPaddedEmitterOutputConstruction :
    Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedProjectionCheckedEquivPaddedEmitterOutputSpec
        useAccept emitter

def SelectedProjectionCheckedEquivEmitterOutputSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall L : DovetailLayout,
      emitter.HaltsFromTapeWithOutput
        (ParsedLayoutCheckedTape L)
        (Tape.normalizedOutput
          (SelectedProjectionOutputTape useAccept L))

def SelectedProjectionCheckedEquivEmitterOutputConstruction : Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedProjectionCheckedEquivEmitterOutputSpec useAccept emitter

def SelectedProjectionFiniteDescriptionForwardOutputSpec
    (useAccept : Bool)
    (runner : MachineDescription) : Prop :=
  runner.SubroutineReady ∧
    forall L : DovetailLayout,
      runner.HaltsFromTapeWithOutput
        (Tape.input (ParsedLayoutBits L))
        (Tape.normalizedOutput
          (SelectedProjectionOutputTape useAccept L))

def SelectedProjectionFiniteDescriptionForwardOutputConstruction :
    Prop :=
  forall useAccept : Bool,
    exists runner : MachineDescription,
      SelectedProjectionFiniteDescriptionForwardOutputSpec
        useAccept runner

def SelectedProjectionCheckedEquivPaddedEmitterOutputComponentConstruction :
    Prop :=
  SelectedProjectionInputQuoterConstruction ∧
    SelectedProjectionPaddedTailEmitterConstruction

theorem selectedProjectionCheckedEquivPaddedEmitterOutputSpec_of_exact
    {useAccept : Bool} {emitter : MachineDescription}
    (hemits :
      SelectedProjectionCheckedEquivPaddedEmitterSpec useAccept emitter) :
    SelectedProjectionCheckedEquivPaddedEmitterOutputSpec
      useAccept emitter := by
  rcases hemits with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro L
  exact haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target (hrun L)

theorem selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_of_exact
    (h :
      SelectedProjectionCheckedEquivPaddedEmitterConstruction) :
    SelectedProjectionCheckedEquivPaddedEmitterOutputConstruction := by
  intro useAccept
  rcases h useAccept with ⟨emitter, hemits⟩
  exact
    ⟨emitter,
      selectedProjectionCheckedEquivPaddedEmitterOutputSpec_of_exact
        hemits⟩

theorem selectedProjectionCheckedEquivPaddedEmitterOutputSpec_haltsToOutput
    {useAccept : Bool} {emitter : MachineDescription}
    (hemits :
      SelectedProjectionCheckedEquivPaddedEmitterOutputSpec
        useAccept emitter) :
    SelectedProjectionCheckedEquivEmitterOutputSpec useAccept emitter := by
  rcases hemits with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro L
  have hnorm :
      Tape.normalizedOutput
          (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L) =
        Tape.normalizedOutput
          (SelectedProjectionOutputTape useAccept L) :=
    Tape.Equiv.normalizedOutput_eq
      (SelectedProjectionEquivEmitterPaddedOutputTape_equiv
        useAccept L)
  simpa [hnorm] using hrun L

theorem selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_haltsToOutput
    (h :
      SelectedProjectionCheckedEquivPaddedEmitterOutputConstruction) :
    SelectedProjectionCheckedEquivEmitterOutputConstruction := by
  intro useAccept
  rcases h useAccept with ⟨emitter, hemits⟩
  exact
    ⟨emitter,
      selectedProjectionCheckedEquivPaddedEmitterOutputSpec_haltsToOutput
        hemits⟩

theorem selectedProjectionCheckedEquivEmitterOutputSpec_of_exact
    {useAccept : Bool} {emitter : MachineDescription}
    (hemits :
      SelectedProjectionCheckedEquivEmitterSpec useAccept emitter) :
    SelectedProjectionCheckedEquivEmitterOutputSpec useAccept emitter := by
  rcases hemits with ⟨hready, hrun, _hclosed⟩
  refine ⟨hready, ?_⟩
  intro L
  exact haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target (hrun L)

theorem selectedProjectionCheckedEquivEmitterOutputConstruction_of_exact
    (h :
      SelectedProjectionCheckedEquivEmitterConstruction) :
    SelectedProjectionCheckedEquivEmitterOutputConstruction := by
  intro useAccept
  rcases h useAccept with ⟨emitter, hemits⟩
  exact
    ⟨emitter,
      selectedProjectionCheckedEquivEmitterOutputSpec_of_exact hemits⟩

theorem selectedProjectionFiniteDescriptionForwardOutputSpec_of_exact
    {useAccept : Bool} {runner : MachineDescription}
    (hrunner :
      SelectedProjectionSpec useAccept runner) :
    SelectedProjectionFiniteDescriptionForwardOutputSpec useAccept runner := by
  rcases hrunner with ⟨hready, hforward, _hclosed⟩
  refine ⟨hready, ?_⟩
  intro L
  exact haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target (hforward L)

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_of_exact
    (h :
      SelectedProjectionFiniteDescriptionConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction := by
  intro useAccept
  rcases h useAccept with ⟨runner, hrunner⟩
  exact
    ⟨runner,
      selectedProjectionFiniteDescriptionForwardOutputSpec_of_exact
        hrunner⟩

theorem selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_of_components
    (hcomponents :
      SelectedProjectionCheckedEquivPaddedEmitterComponentConstruction) :
    SelectedProjectionCheckedEquivPaddedEmitterOutputConstruction :=
  selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_of_exact
    (selectedProjectionCheckedEquivPaddedEmitterConstruction_of_components
      hcomponents)

theorem selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_of_tailEmitter
    (htail :
      SelectedProjectionPaddedTailEmitterConstruction) :
    SelectedProjectionCheckedEquivPaddedEmitterOutputConstruction :=
  selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_of_components
    ⟨selectedProjectionInputQuoterConstruction_scaffold, htail⟩

theorem selectedProjectionCheckedEquivEmitterOutputConstruction_of_padded
    (h :
      SelectedProjectionCheckedEquivPaddedEmitterConstruction) :
    SelectedProjectionCheckedEquivEmitterOutputConstruction :=
  selectedProjectionCheckedEquivEmitterOutputConstruction_of_exact
    (selectedProjectionCheckedEquivEmitterConstruction_of_padded h)

theorem selectedProjectionCheckedEquivEmitterOutputConstruction_of_paddedOutput
    (h :
      SelectedProjectionCheckedEquivPaddedEmitterOutputConstruction) :
    SelectedProjectionCheckedEquivEmitterOutputConstruction :=
  selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_haltsToOutput h

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_scaffold_of_tailEmitter
    (htail : SelectedProjectionPaddedTailEmitterConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_exact
    (selectedProjectionFiniteDescriptionConstruction_scaffold_of_tailEmitter
      htail)

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_scaffold_of_postErase
    (hpostEraseConstruction :
      SelectedProjectionPaddedTailCleanup.SelectedProjectionPaddedTailCleanupPostEraseConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_exact
    (selectedProjectionFiniteDescriptionConstruction_scaffold_of_postErase
      hpostEraseConstruction)

theorem selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_scaffold_of_postErase
    (hpostEraseConstruction :
      SelectedProjectionPaddedTailCleanup.SelectedProjectionPaddedTailCleanupPostEraseConstruction) :
    SelectedProjectionCheckedEquivPaddedEmitterOutputConstruction :=
  selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_of_tailEmitter
    (selectedProjectionPaddedTailEmitterConstruction_scaffold_of_postErase
      hpostEraseConstruction)

theorem selectedProjectionCheckedEquivEmitterOutputConstruction_scaffold_of_postErase
    (hpostEraseConstruction :
      SelectedProjectionPaddedTailCleanup.SelectedProjectionPaddedTailCleanupPostEraseConstruction) :
    SelectedProjectionCheckedEquivEmitterOutputConstruction :=
  selectedProjectionCheckedEquivEmitterOutputConstruction_of_paddedOutput
    (selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_scaffold_of_postErase
      hpostEraseConstruction)

theorem selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_scaffold :
    SelectedProjectionCheckedEquivPaddedEmitterOutputConstruction :=
  selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_scaffold_of_postErase
    SelectedProjectionPaddedTailCleanup.selectedProjectionPaddedTailCleanupPostEraseConstruction

theorem selectedProjectionCheckedEquivEmitterOutputConstruction_scaffold :
    SelectedProjectionCheckedEquivEmitterOutputConstruction :=
  selectedProjectionCheckedEquivEmitterOutputConstruction_of_paddedOutput
    selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_scaffold

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_scaffold :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_exact
    selectedProjectionFiniteDescriptionConstruction_scaffold

theorem selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_scaffold_of_prefixAndFootprintCases
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    SelectedProjectionCheckedEquivPaddedEmitterOutputConstruction :=
  selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_of_tailEmitter
    (selectedProjectionPaddedTailEmitterConstruction_scaffold_of_prefixAndFootprintCases
      hprefix hcases)

theorem selectedProjectionCheckedEquivEmitterOutputConstruction_scaffold_of_prefixAndFootprintCases
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    SelectedProjectionCheckedEquivEmitterOutputConstruction :=
  selectedProjectionCheckedEquivEmitterOutputConstruction_of_paddedOutput
    (selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_scaffold_of_prefixAndFootprintCases
      hprefix hcases)

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_scaffold_of_prefixAndFootprintCases
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_exact
    (selectedProjectionFiniteDescriptionConstruction_scaffold_of_prefixAndFootprintCases
      hprefix hcases)

theorem selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_scaffold_of_prefixAndFootprintBitPaddingCases
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionCheckedEquivPaddedEmitterOutputConstruction :=
  selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_of_tailEmitter
    (selectedProjectionPaddedTailEmitterConstruction_scaffold_of_prefixAndFootprintBitPaddingCases
      hprefix hcases)

theorem selectedProjectionCheckedEquivEmitterOutputConstruction_scaffold_of_prefixAndFootprintBitPaddingCases
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionCheckedEquivEmitterOutputConstruction :=
  selectedProjectionCheckedEquivEmitterOutputConstruction_of_paddedOutput
    (selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_scaffold_of_prefixAndFootprintBitPaddingCases
      hprefix hcases)

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_scaffold_of_prefixAndFootprintBitPaddingCases
    (hprefix :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_exact
    (selectedProjectionFiniteDescriptionConstruction_scaffold_of_prefixAndFootprintBitPaddingCases
      hprefix hcases)

theorem selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_scaffold_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
    (heraser :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionCheckedEquivPaddedEmitterOutputConstruction :=
  selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_of_tailEmitter
    (selectedProjectionPaddedTailEmitterConstruction_scaffold_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
      heraser hcases)

theorem selectedProjectionCheckedEquivEmitterOutputConstruction_scaffold_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
    (heraser :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionCheckedEquivEmitterOutputConstruction :=
  selectedProjectionCheckedEquivEmitterOutputConstruction_of_paddedOutput
    (selectedProjectionCheckedEquivPaddedEmitterOutputConstruction_scaffold_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
      heraser hcases)

theorem selectedProjectionFiniteDescriptionForwardOutputConstruction_scaffold_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
    (heraser :
      SelectedProjectionPaddedTailCleanup.CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction)
    (hcases :
      SelectedProjectionPaddedTailCleanup.SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedProjectionFiniteDescriptionForwardOutputConstruction :=
  selectedProjectionFiniteDescriptionForwardOutputConstruction_of_exact
    (selectedProjectionFiniteDescriptionConstruction_scaffold_of_structuredPrefixBranchCasesAndFootprintBitPaddingCases
      heraser hcases)

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
