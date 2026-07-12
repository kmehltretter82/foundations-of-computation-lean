import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMatContracts

set_option doc.verso true

/-!
# Count-window selected-segment routes

Output projector and selected-segment route adapters for the count-window bridge.
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

/--
Count-window-specific output projection from the lowered structured extractor.

This is intentionally narrower than the reusable
{name}`Structured.MultiTapeLowering.StructuredTape2ProjectorSpec`: the bridge
only needs to extract the third tape from the concrete structured output shape
produced by the decoded-prefix extractor.
-/
def CountWindowPostFieldDecodedPrefixStructuredOutputProjectorSpec
    (projector : MachineDescription) : Prop :=
  projector.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout)
      (deletedTail : Word Bool),
      projector.HaltsFromTapeEquiv
        (countWindowPostFieldDecodedPrefixStructuredEncodedOutputTape
          useAccept L deletedTail)
        (postFieldDecodedPrefixScanSourceTape useAccept L)

def CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction :
    Prop :=
  exists projector : MachineDescription,
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorSpec projector

/--
Count-window-specific normalizer for the selected guarded tape-2 segment.

The input cursor has already been moved to the separator before the third
logical tape in the lowered structured output.  This is narrower than
{name}`Structured.MultiTapeLowering.StructuredTape2SegmentNormalizerSpec`
because it only has to decode the concrete right-edge scan-source tape shape
used by this bridge.
-/
def CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerSpec
    (normalizer : MachineDescription) : Prop :=
  normalizer.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout)
      (deletedTail : Word Bool) (physical : Tape Bool),
      AtTapeSeparator
        (guardLogicalTapes
          [ structuredBoolWordRawBitsDecoderSourceTargetTape
              (ParsedLayoutBits L)
              (countWindowPostFieldDecodedPrefixStructuredSuffixTail
                useAccept L)
              (countWindowPostFieldDecodedPrefixStructuredSourcePadding
                useAccept L deletedTail)
          , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
              ((ParsedLayoutBits L).length + 1)
          , postFieldDecodedPrefixScanSourceTape useAccept L ])
        2 physical ->
        normalizer.HaltsFromTapeEquiv physical
          (postFieldDecodedPrefixScanSourceTape useAccept L)

def CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction :
    Prop :=
  exists normalizer : MachineDescription,
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerSpec
      normalizer

/--
Count-window-specific decoder for the selected canonical tape-2 segment.

This is the concrete output-side finite-machine target from the bridge plan:
starting at the selected segment separator, decode the guarded structured
encoding of the right-edge scan-source tape back to that plain tape.  The
encoded prefix to the left is arbitrary because the tape-2 seeker leaves the
previous structured segments there.
-/
def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderSpec
    (decoder : MachineDescription) : Prop :=
  decoder.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout)
      (encodedPrefix : List (Option Bool)),
      decoder.HaltsFromTapeEquiv
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells
            [guardLogicalTape
              (postFieldDecodedPrefixScanSourceTape useAccept L)]))
        (postFieldDecodedPrefixScanSourceTape useAccept L)

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction :
    Prop :=
  exists decoder : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderSpec decoder

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixSpec
    (decoder : MachineDescription) : Prop :=
  decoder.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout)
      (deletedTail : Word Bool),
      decoder.HaltsFromTapeEquiv
        (tapeAtEncodedSplit
          (countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
            useAccept L deletedTail)
          (encodedStructuredTapeCells
            [guardLogicalTape
              (postFieldDecodedPrefixScanSourceTape useAccept L)]))
        (postFieldDecodedPrefixScanSourceTape useAccept L)

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction :
    Prop :=
  exists decoder : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixSpec
      decoder

/--
Count-window-specific cleanup after the selected-segment bit scan.

The generic arbitrary-tape cleanup is too strong for the simple bit scanner:
after scanning, the marker position has to be recovered from the concrete
right-edge scan-source layout.  This narrowed contract is the remaining
output-side adapter obligation for this bridge.
-/
def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout)
      (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTargetTape
          (postFieldDecodedPrefixScanSourceTape useAccept L)
          encodedPrefix)
        (postFieldDecodedPrefixScanSourceTape useAccept L)

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupConstruction :
    Prop :=
  exists cleanup : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupSpec cleanup

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout)
      (deletedTail : Word Bool),
      cleanup.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTargetTape
          (postFieldDecodedPrefixScanSourceTape useAccept L)
          (countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
            useAccept L deletedTail))
        (postFieldDecodedPrefixScanSourceTape useAccept L)

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction :
    Prop :=
  exists cleanup : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupSpec
      cleanup

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierSpec
    (densifier : MachineDescription) : Prop :=
  densifier.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout)
      (encodedPrefix : List (Option Bool)),
      densifier.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTargetTape
          (postFieldDecodedPrefixScanSourceTape useAccept L)
          encodedPrefix)
        (rightEdgeRewindSourceTape (ParsedLayoutBits L)
          (postFieldDecodedPrefixScanPadding useAccept L))

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierConstruction :
    Prop :=
  exists densifier : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierSpec
      densifier

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierSpec
    (densifier : MachineDescription) : Prop :=
  densifier.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout)
      (deletedTail : Word Bool),
      densifier.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTargetTape
          (postFieldDecodedPrefixScanSourceTape useAccept L)
          (countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
            useAccept L deletedTail))
        (rightEdgeRewindSourceTape (ParsedLayoutBits L)
          (postFieldDecodedPrefixScanPadding useAccept L))

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction :
    Prop :=
  exists densifier : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierSpec
      densifier

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout)
      (encodedPrefix : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTargetTape
          (postFieldDecodedPrefixScanSourceTape useAccept L)
          encodedPrefix)
        (selectedSegmentLogicalTapeDecoderTargetTape
          (postFieldDecodedPrefixScanSourceTape useAccept L)
          [])

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction :
    Prop :=
  exists eraser : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserSpec
      eraser

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout)
      (deletedTail : Word Bool),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTargetTape
          (postFieldDecodedPrefixScanSourceTape useAccept L)
          (countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
            useAccept L deletedTail))
        (selectedSegmentLogicalTapeDecoderTargetTape
          (postFieldDecodedPrefixScanSourceTape useAccept L)
          [])

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserConstruction :
    Prop :=
  exists eraser : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserSpec
      eraser

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall (L : DovetailLayout) (deletedTail : Word Bool),
      eraser.HaltsFromTapeEquiv
        (countWindowPostFieldDecodedPrefixStructuredPrefixEraserSourceTape
          true L deletedTail)
        (countWindowPostFieldDecodedPrefixStructuredPrefixEraserTargetTape
          true L)) ∧
    forall (L : DovetailLayout) (deletedTail : Word Bool),
      eraser.HaltsFromTapeEquiv
        (countWindowPostFieldDecodedPrefixStructuredPrefixEraserSourceTape
          false L deletedTail)
        (countWindowPostFieldDecodedPrefixStructuredPrefixEraserTargetTape
          false L)

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchConstruction :
    Prop :=
  exists eraser : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchSpec
      eraser

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall L : DovetailLayout,
      eraser.HaltsFromTapeEquiv
        (countWindowPostFieldDecodedPrefixStructuredPrefixEraserSourceTape
          true L [])
        (countWindowPostFieldDecodedPrefixStructuredPrefixEraserTargetTape
          true L)) ∧
    (forall (L : DovetailLayout) (bit : Bool) (rest : Word Bool),
      eraser.HaltsFromTapeEquiv
        (countWindowPostFieldDecodedPrefixStructuredPrefixEraserSourceTape
          true L (bit :: rest))
        (countWindowPostFieldDecodedPrefixStructuredPrefixEraserTargetTape
          true L)) ∧
    (forall L : DovetailLayout,
      eraser.HaltsFromTapeEquiv
        (countWindowPostFieldDecodedPrefixStructuredPrefixEraserSourceTape
          false L [])
        (countWindowPostFieldDecodedPrefixStructuredPrefixEraserTargetTape
          false L)) ∧
    forall (L : DovetailLayout) (bit : Bool) (rest : Word Bool),
      eraser.HaltsFromTapeEquiv
        (countWindowPostFieldDecodedPrefixStructuredPrefixEraserSourceTape
          false L (bit :: rest))
        (countWindowPostFieldDecodedPrefixStructuredPrefixEraserTargetTape
          false L)

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction :
    Prop :=
  exists eraser : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseSpec
      eraser

def SelectedSegmentLogicalTapeDecoderFootprintCompactorSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    forall (bits : Word Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          bits padding)
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          bits padding)

def SelectedSegmentLogicalTapeDecoderFootprintCompactorConstruction :
    Prop :=
  exists compactor : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintCompactorSpec compactor

def SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    (forall padding : List (Option Bool),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] padding)
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] padding)) ∧
    forall (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) padding)
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) padding)

def SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction :
    Prop :=
  exists compactor : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseSpec compactor

def SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    compactor.HaltsFromTapeEquiv
      (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] [])
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] []) ∧
    (forall (pad : Option Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (pad :: padding))
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] (pad :: padding))) ∧
    (forall (bit : Bool) (rest : Word Bool),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) [])
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) [])) ∧
    forall (bit : Bool) (rest : Word Bool)
      (pad : Option Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (pad :: padding))
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) (pad :: padding))

def SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction :
    Prop :=
  exists compactor : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseSpec
      compactor

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout),
      compactor.HaltsFromTapeEquiv
        (countWindowPostFieldDecodedPrefixSelectedSegmentMarkedFootprintCompactorSourceTape
          useAccept L)
        (countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorTargetTape
          useAccept L)

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction :
    Prop :=
  exists compactor : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorSpec
      compactor

/-- Historical unmarked contract retained only for implication-style wrappers
whose caller already assumes an arbitrary footprint compactor.  The live #15
construction uses the marker-bearing contract above. -/
def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderUnmarkedFootprintCompactorSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout),
      compactor.HaltsFromTapeEquiv
        (countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorSourceTape
          useAccept L)
        (countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorTargetTape
          useAccept L)

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderUnmarkedFootprintCompactorConstruction :
    Prop :=
  exists compactor : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderUnmarkedFootprintCompactorSpec
      compactor

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierComponentsConstruction :
    Prop :=
  CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction ∧
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderUnmarkedFootprintCompactorConstruction

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierComponentsConstruction :
    Prop :=
  CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserConstruction ∧
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderUnmarkedFootprintCompactorConstruction

def countWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierDescription
    (eraser compactor : MachineDescription) : MachineDescription :=
  canonicalSeqDescription eraser compactor

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierDescription_subroutineReady
    {eraser compactor : MachineDescription}
    (heraser : eraser.SubroutineReady)
    (hcompactor : compactor.SubroutineReady) :
    (countWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierDescription
      eraser compactor).SubroutineReady :=
  canonicalSeqDescription_subroutineReady heraser hcompactor

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierConstruction_of_components
    (hcomponents :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierComponentsConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierConstruction := by
  rcases hcomponents with
    ⟨⟨eraser, heraserReady, heraserRun⟩,
      ⟨compactor, hcompactorReady, hcompactorRun⟩⟩
  refine
    ⟨countWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierDescription
      eraser compactor, ?_⟩
  constructor
  · exact
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierDescription_subroutineReady
        heraserReady hcompactorReady
  · intro useAccept L encodedPrefix
    let Tmid :=
      selectedSegmentLogicalTapeDecoderTargetTape
        (postFieldDecodedPrefixScanSourceTape useAccept L)
        []
    have hcompactorFromBridge :
        compactor.HaltsFromTapeEquiv
          (Tape.move Direction.left (Tape.move Direction.right Tmid))
          (rightEdgeRewindSourceTape (ParsedLayoutBits L)
            (postFieldDecodedPrefixScanPadding useAccept L)) := by
      rcases hcompactorRun useAccept L with
        ⟨Tactual, hactual, hactualEquiv⟩
      rcases
        HaltsFromTapeEquiv_of_input_equiv
          (D := compactor)
          (Tin := Tmid)
          (Tin' :=
            Tape.move Direction.left (Tape.move Direction.right Tmid))
          (selectedSegmentLogicalTapeDecoderTargetTape_move_left_move_right_equiv
            (postFieldDecodedPrefixScanSourceTape useAccept L) [])
          hactual with
        ⟨Ttransported, htransported, htransportedEquiv⟩
      exact
        ⟨Ttransported, htransported,
          Tape.Equiv.trans htransportedEquiv hactualEquiv⟩
    exact
      canonicalSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv
        heraserReady
        hcompactorReady
        (heraserRun useAccept L encodedPrefix)
        rfl
        hcompactorFromBridge

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction_of_components
    (hcomponents :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierComponentsConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction := by
  rcases hcomponents with
    ⟨⟨eraser, heraserReady, heraserRun⟩,
      ⟨compactor, hcompactorReady, hcompactorRun⟩⟩
  refine
    ⟨countWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierDescription
      eraser compactor, ?_⟩
  constructor
  · exact
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierDescription_subroutineReady
        heraserReady hcompactorReady
  · intro useAccept L deletedTail
    let Tmid :=
      selectedSegmentLogicalTapeDecoderTargetTape
        (postFieldDecodedPrefixScanSourceTape useAccept L)
        []
    have hcompactorFromBridge :
        compactor.HaltsFromTapeEquiv
          (Tape.move Direction.left (Tape.move Direction.right Tmid))
          (rightEdgeRewindSourceTape (ParsedLayoutBits L)
            (postFieldDecodedPrefixScanPadding useAccept L)) := by
      rcases hcompactorRun useAccept L with
        ⟨Tactual, hactual, hactualEquiv⟩
      rcases
        HaltsFromTapeEquiv_of_input_equiv
          (D := compactor)
          (Tin := Tmid)
          (Tin' :=
            Tape.move Direction.left (Tape.move Direction.right Tmid))
          (selectedSegmentLogicalTapeDecoderTargetTape_move_left_move_right_equiv
            (postFieldDecodedPrefixScanSourceTape useAccept L) [])
          hactual with
        ⟨Ttransported, htransported, htransportedEquiv⟩
      exact
        ⟨Ttransported, htransported,
          Tape.Equiv.trans htransportedEquiv hactualEquiv⟩
    exact
      canonicalSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv
        heraserReady
        hcompactorReady
        (heraserRun useAccept L deletedTail)
        rfl
        hcompactorFromBridge

def countWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupDescription
    (densifier : MachineDescription) : MachineDescription :=
  canonicalSeqDescription densifier rightEdgeRewindDescription

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupDescription_subroutineReady
    {densifier : MachineDescription}
    (hdensifier : densifier.SubroutineReady) :
    (countWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupDescription
      densifier).SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    hdensifier rightEdgeRewindDescription_subroutineReady

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupConstruction_of_densifier
    (hdensifier :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupConstruction := by
  rcases hdensifier with
    ⟨densifier, hdensifierReady, hdensifierRun⟩
  refine
    ⟨countWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupDescription
      densifier, ?_⟩
  constructor
  · exact
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupDescription_subroutineReady
        hdensifierReady
  · intro useAccept L encodedPrefix
    have hbridge :
        Tape.move Direction.left
            (Tape.move Direction.right
              (rightEdgeRewindSourceTape (ParsedLayoutBits L)
                (postFieldDecodedPrefixScanPadding useAccept L))) =
          rightEdgeRewindSourceTape (ParsedLayoutBits L)
            (postFieldDecodedPrefixScanPadding useAccept L) := by
      simpa [postFieldDecodedPrefixScanPadding] using
        rightEdgeRewindSourceTape_move_left_move_right_padding_cons
          (ParsedLayoutBits L) (none : Option Bool)
          (List.append
            (List.replicate
              (selectedProjectionPaddedTailCleanupScratchCountBits
                useAccept L).length
              (none : Option Bool))
            (selectedProjectionPaddedTailCleanupPostCountTailCells
              useAccept L 0))
    have hrewind :
        rightEdgeRewindDescription.HaltsFromTapeEquiv
          (rightEdgeRewindSourceTape (ParsedLayoutBits L)
            (postFieldDecodedPrefixScanPadding useAccept L))
          (postFieldDecodedPrefixScanSourceTape useAccept L) := by
      simpa [postFieldDecodedPrefixScanSourceTape,
        rightEdgeRewindTargetTape, rightEdgeScanSourceTapeFromLeft] using
        (rightEdgeRewindDescription_haltsFromTape
          (ParsedLayoutBits L)
          (postFieldDecodedPrefixScanPadding useAccept L)).toEquiv
    exact
      canonicalSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv
        hdensifierReady
        rightEdgeRewindDescription_subroutineReady
        (hdensifierRun useAccept L encodedPrefix)
        hbridge
        hrewind

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction_of_densifier
    (hdensifier :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction := by
  rcases hdensifier with
    ⟨densifier, hdensifierReady, hdensifierRun⟩
  refine
    ⟨countWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupDescription
      densifier, ?_⟩
  constructor
  · exact
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupDescription_subroutineReady
        hdensifierReady
  · intro useAccept L deletedTail
    have hbridge :
        Tape.move Direction.left
            (Tape.move Direction.right
              (rightEdgeRewindSourceTape (ParsedLayoutBits L)
                (postFieldDecodedPrefixScanPadding useAccept L))) =
          rightEdgeRewindSourceTape (ParsedLayoutBits L)
            (postFieldDecodedPrefixScanPadding useAccept L) := by
      simpa [postFieldDecodedPrefixScanPadding] using
        rightEdgeRewindSourceTape_move_left_move_right_padding_cons
          (ParsedLayoutBits L) (none : Option Bool)
          (List.append
            (List.replicate
              (selectedProjectionPaddedTailCleanupScratchCountBits
                useAccept L).length
              (none : Option Bool))
            (selectedProjectionPaddedTailCleanupPostCountTailCells
              useAccept L 0))
    have hrewind :
        rightEdgeRewindDescription.HaltsFromTapeEquiv
          (rightEdgeRewindSourceTape (ParsedLayoutBits L)
            (postFieldDecodedPrefixScanPadding useAccept L))
          (postFieldDecodedPrefixScanSourceTape useAccept L) := by
      simpa [postFieldDecodedPrefixScanSourceTape,
        rightEdgeRewindTargetTape, rightEdgeScanSourceTapeFromLeft] using
        (rightEdgeRewindDescription_haltsFromTape
          (ParsedLayoutBits L)
          (postFieldDecodedPrefixScanPadding useAccept L)).toEquiv
    exact
      canonicalSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv
        hdensifierReady
        rightEdgeRewindDescription_subroutineReady
        (hdensifierRun useAccept L deletedTail)
        hbridge
        hrewind

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction_of_cleanup
    (hcleanup :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction := by
  rcases hcleanup with
    ⟨cleanup, hcleanupReady, hcleanupRun⟩
  refine
    ⟨selectedSegmentLogicalTapeDecoderPipelineDescription cleanup,
      ?_⟩
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderPipelineDescription_subroutineReady
        hcleanupReady
  · intro useAccept L encodedPrefix
    have hmove :
        (cursorMoveOnceDescription Direction.right).HaltsFromTapeEquiv
          (tapeAtEncodedSplit encodedPrefix
            (encodedStructuredTapeCells
              [guardLogicalTape
                (postFieldDecodedPrefixScanSourceTape useAccept L)]))
          (Tape.move Direction.right
            (tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells
                [guardLogicalTape
                  (postFieldDecodedPrefixScanSourceTape useAccept L)]))) :=
      (cursorMoveOnceDescription_haltsFromTape Direction.right
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells
            [guardLogicalTape
              (postFieldDecodedPrefixScanSourceTape useAccept L)]))).toEquiv
    have hscan :
        selectedSegmentLogicalTapeDecoderDescription.HaltsFromTapeEquiv
          (Tape.move Direction.right
            (tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells
                [guardLogicalTape
                  (postFieldDecodedPrefixScanSourceTape useAccept L)])))
          (selectedSegmentLogicalTapeDecoderTargetTape
            (postFieldDecodedPrefixScanSourceTape useAccept L)
            encodedPrefix) :=
      (selectedSegmentLogicalTapeDecoderDescription_haltsFrom_selectedSingletonPayload
        (postFieldDecodedPrefixScanSourceTape useAccept L)
        encodedPrefix).toEquiv
    have hpipelineScan :
        (canonicalPrimitiveSeqDescription
          (cursorMoveOnceDescription Direction.right)
          selectedSegmentLogicalTapeDecoderDescription).HaltsFromTapeEquiv
            (tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells
                [guardLogicalTape
                  (postFieldDecodedPrefixScanSourceTape useAccept L)]))
            (selectedSegmentLogicalTapeDecoderTargetTape
              (postFieldDecodedPrefixScanSourceTape useAccept L)
              encodedPrefix) :=
      canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        (cursorMoveOnceDescription_subroutineReady Direction.right)
        selectedSegmentLogicalTapeDecoderDescription_subroutineReady
        hmove
        hscan
    exact
      canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        (canonicalPrimitiveSeqDescription_subroutineReady
          (cursorMoveOnceDescription_subroutineReady Direction.right)
          selectedSegmentLogicalTapeDecoderDescription_subroutineReady)
        hcleanupReady
        hpipelineScan
        (hcleanupRun useAccept L encodedPrefix)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction_of_cleanup
    (hcleanup :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction := by
  rcases hcleanup with
    ⟨cleanup, hcleanupReady, hcleanupRun⟩
  refine
    ⟨selectedSegmentLogicalTapeDecoderPipelineDescription cleanup,
      ?_⟩
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderPipelineDescription_subroutineReady
        hcleanupReady
  · intro useAccept L deletedTail
    let encodedPrefix :=
      countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
        useAccept L deletedTail
    have hmove :
        (cursorMoveOnceDescription Direction.right).HaltsFromTapeEquiv
          (tapeAtEncodedSplit encodedPrefix
            (encodedStructuredTapeCells
              [guardLogicalTape
                (postFieldDecodedPrefixScanSourceTape useAccept L)]))
          (Tape.move Direction.right
            (tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells
                [guardLogicalTape
                  (postFieldDecodedPrefixScanSourceTape useAccept L)]))) :=
      (cursorMoveOnceDescription_haltsFromTape Direction.right
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells
            [guardLogicalTape
              (postFieldDecodedPrefixScanSourceTape useAccept L)]))).toEquiv
    have hscan :
        selectedSegmentLogicalTapeDecoderDescription.HaltsFromTapeEquiv
          (Tape.move Direction.right
            (tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells
                [guardLogicalTape
                  (postFieldDecodedPrefixScanSourceTape useAccept L)])))
          (selectedSegmentLogicalTapeDecoderTargetTape
            (postFieldDecodedPrefixScanSourceTape useAccept L)
            encodedPrefix) :=
      (selectedSegmentLogicalTapeDecoderDescription_haltsFrom_selectedSingletonPayload
        (postFieldDecodedPrefixScanSourceTape useAccept L)
        encodedPrefix).toEquiv
    have hpipelineScan :
        (canonicalPrimitiveSeqDescription
          (cursorMoveOnceDescription Direction.right)
          selectedSegmentLogicalTapeDecoderDescription).HaltsFromTapeEquiv
            (tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells
                [guardLogicalTape
                  (postFieldDecodedPrefixScanSourceTape useAccept L)]))
            (selectedSegmentLogicalTapeDecoderTargetTape
              (postFieldDecodedPrefixScanSourceTape useAccept L)
              encodedPrefix) :=
      canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        (cursorMoveOnceDescription_subroutineReady Direction.right)
        selectedSegmentLogicalTapeDecoderDescription_subroutineReady
        hmove
        hscan
    exact
      canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        (canonicalPrimitiveSeqDescription_subroutineReady
          (cursorMoveOnceDescription_subroutineReady Direction.right)
          selectedSegmentLogicalTapeDecoderDescription_subroutineReady)
        hcleanupReady
        hpipelineScan
        (hcleanupRun useAccept L deletedTail)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction_of_singletonDecoder
    (hdecoder :
      StructuredSelectedSingletonSegmentDecoderConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction := by
  unfold StructuredSelectedSingletonSegmentDecoderConstruction at hdecoder
  rcases hdecoder with ⟨decoder, hdecoderReady, hdecoderRun⟩
  refine ⟨decoder, hdecoderReady, ?_⟩
  intro useAccept L encodedPrefix
  exact hdecoderRun (postFieldDecodedPrefixScanSourceTape useAccept L)
    encodedPrefix

theorem countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_of_selectedSegmentDecoder
    (hdecoder :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction := by
  rcases hdecoder with ⟨decoder, hdecoderReady, hdecoderRun⟩
  refine ⟨decoder, hdecoderReady, ?_⟩
  intro useAccept L deletedTail physical hseparator
  rcases hseparator with ⟨_hindex, hphysical⟩
  rw [hphysical]
  simpa [encodedSuffixFromTape, guardLogicalTapes] using
    hdecoderRun useAccept L
      (encodedPrefixBeforeTape
        (guardLogicalTapes
          [ structuredBoolWordRawBitsDecoderSourceTargetTape
              (ParsedLayoutBits L)
              (countWindowPostFieldDecodedPrefixStructuredSuffixTail
                useAccept L)
              (countWindowPostFieldDecodedPrefixStructuredSourcePadding
                useAccept L deletedTail)
          , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
              ((ParsedLayoutBits L).length + 1)
          , postFieldDecodedPrefixScanSourceTape useAccept L ])
        2)

theorem countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction_of_structuredPrefixSelectedSegmentDecoder
    (hdecoder :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction := by
  rcases hdecoder with ⟨decoder, hdecoderReady, hdecoderRun⟩
  refine ⟨decoder, hdecoderReady, ?_⟩
  intro useAccept L deletedTail physical hseparator
  rcases hseparator with ⟨_hindex, hphysical⟩
  rw [hphysical]
  simpa [encodedSuffixFromTape, guardLogicalTapes,
    countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix] using
    hdecoderRun useAccept L deletedTail

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderUnmarkedFootprintCompactorConstruction_of_generic
    (hgeneric :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderUnmarkedFootprintCompactorConstruction := by
  rcases hgeneric with ⟨compactor, hready, hrun⟩
  refine ⟨compactor, hready, ?_⟩
  intro useAccept L
  simpa [
    countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorSourceTape,
    countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorTargetTape,
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape,
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape,
    postFieldDecodedPrefixScanSourceTape] using
    hrun (ParsedLayoutBits L)
      (postFieldDecodedPrefixScanPadding useAccept L)

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorConstruction_of_cases
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorConstruction := by
  rcases hcases with ⟨compactor, hready, hnil, hcons⟩
  refine ⟨compactor, hready, ?_⟩
  intro bits padding
  cases bits with
  | nil =>
      exact hnil padding
  | cons bit rest =>
      exact hcons bit rest padding

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction_of_bitPaddingCases
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction := by
  rcases hcases with
    ⟨compactor, hready, hnilNil, hnilCons, hconsNil,
      hconsCons⟩
  refine ⟨compactor, hready, ?_, ?_⟩
  · intro padding
    cases padding with
    | nil =>
        exact hnilNil
    | cons pad padding =>
        exact hnilCons pad padding
  · intro bit rest padding
    cases padding with
    | nil =>
        exact hconsNil bit rest
    | cons pad padding =>
        exact hconsCons bit rest pad padding

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchConstruction_of_prefixEraser
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchConstruction := by
  rcases hprefix with ⟨eraser, hready, hrun⟩
  refine ⟨eraser, hready, ?_, ?_⟩
  · intro L deletedTail
    simpa [
      countWindowPostFieldDecodedPrefixStructuredPrefixEraserSourceTape,
      countWindowPostFieldDecodedPrefixStructuredPrefixSelectedSegmentTargetTape,
      countWindowPostFieldDecodedPrefixStructuredPrefixEraserTargetTape] using
      hrun true L
        (countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
          true L deletedTail)
  · intro L deletedTail
    simpa [
      countWindowPostFieldDecodedPrefixStructuredPrefixEraserSourceTape,
      countWindowPostFieldDecodedPrefixStructuredPrefixSelectedSegmentTargetTape,
      countWindowPostFieldDecodedPrefixStructuredPrefixEraserTargetTape] using
      hrun false L
        (countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
          false L deletedTail)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchConstruction_of_cases
    (hcases :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchConstruction := by
  rcases hcases with
    ⟨eraser, hready, hacceptNil, hacceptCons, hrejectNil,
      hrejectCons⟩
  refine ⟨eraser, hready, ?_, ?_⟩
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

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserConstruction_of_branches
    (hbranches :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserConstruction := by
  rcases hbranches with ⟨eraser, hready, haccept, hreject⟩
  refine ⟨eraser, hready, ?_⟩
  intro useAccept L deletedTail
  cases useAccept
  · exact hreject L deletedTail
  · exact haccept L deletedTail

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserConstruction_of_prefixEraser
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserConstruction := by
  exact
    countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserConstruction_of_branches
      (countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchConstruction_of_prefixEraser
        hprefix)



end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
