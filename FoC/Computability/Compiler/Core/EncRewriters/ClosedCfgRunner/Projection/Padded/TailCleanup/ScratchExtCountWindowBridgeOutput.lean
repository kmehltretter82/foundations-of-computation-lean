import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.ScratchExtCountWindowBridgeThreaded

set_option doc.verso true

/-!
# Count-window bridge output endpoints

This module keeps normalized-output endpoint contracts for the structured
count-window bridge out of `ScratchExtCountWindowBridge.lean`, which is already
past the repository's large-file threshold.  The contracts here are weaker
views of the existing exact/equivalence selected-segment bridge specs and are
intended for downstream routes that only consume decoded output words.
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

private theorem haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
    {D : MachineDescription} {Tin Tout : Tape Bool}
    (h : D.HaltsFromTapeEquiv Tin Tout) :
    D.HaltsFromTapeWithOutput Tin (Tape.normalizedOutput Tout) :=
  MachineDescription.haltsFromTapeWithOutput_of_haltsFromTapeEquiv h

def CountWindowPostFieldDecodedPrefixStructuredOutputProjectorOutputSpec
    (projector : MachineDescription) : Prop :=
  projector.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout)
      (deletedTail : Word Bool),
      projector.HaltsFromTapeWithOutput
        (countWindowPostFieldDecodedPrefixStructuredEncodedOutputTape
          useAccept L deletedTail)
        (Tape.normalizedOutput
          (postFieldDecodedPrefixScanSourceTape useAccept L))

def CountWindowPostFieldDecodedPrefixStructuredOutputProjectorOutputConstruction :
    Prop :=
  exists projector : MachineDescription,
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorOutputSpec
      projector

def CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerOutputSpec
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
        normalizer.HaltsFromTapeWithOutput physical
          (Tape.normalizedOutput
            (postFieldDecodedPrefixScanSourceTape useAccept L))

def CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerOutputConstruction :
    Prop :=
  exists normalizer : MachineDescription,
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerOutputSpec
      normalizer

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderOutputSpec
    (decoder : MachineDescription) : Prop :=
  decoder.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout)
      (encodedPrefix : List (Option Bool)),
      decoder.HaltsFromTapeWithOutput
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells
            [guardLogicalTape
              (postFieldDecodedPrefixScanSourceTape useAccept L)]))
        (Tape.normalizedOutput
          (postFieldDecodedPrefixScanSourceTape useAccept L))

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderOutputConstruction :
    Prop :=
  exists decoder : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderOutputSpec
      decoder

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixOutputSpec
    (decoder : MachineDescription) : Prop :=
  decoder.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout)
      (deletedTail : Word Bool),
      decoder.HaltsFromTapeWithOutput
        (tapeAtEncodedSplit
          (countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
            useAccept L deletedTail)
          (encodedStructuredTapeCells
            [guardLogicalTape
              (postFieldDecodedPrefixScanSourceTape useAccept L)]))
        (Tape.normalizedOutput
          (postFieldDecodedPrefixScanSourceTape useAccept L))

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixOutputConstruction :
    Prop :=
  exists decoder : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixOutputSpec
      decoder

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupOutputSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout)
      (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderTargetTape
          (postFieldDecodedPrefixScanSourceTape useAccept L)
          encodedPrefix)
        (Tape.normalizedOutput
          (postFieldDecodedPrefixScanSourceTape useAccept L))

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupOutputConstruction :
    Prop :=
  exists cleanup : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupOutputSpec
      cleanup

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupOutputSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout)
      (deletedTail : Word Bool),
      cleanup.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderTargetTape
          (postFieldDecodedPrefixScanSourceTape useAccept L)
          (countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
            useAccept L deletedTail))
        (Tape.normalizedOutput
          (postFieldDecodedPrefixScanSourceTape useAccept L))

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupOutputConstruction :
    Prop :=
  exists cleanup : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupOutputSpec
      cleanup

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierOutputSpec
    (densifier : MachineDescription) : Prop :=
  densifier.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout)
      (encodedPrefix : List (Option Bool)),
      densifier.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderTargetTape
          (postFieldDecodedPrefixScanSourceTape useAccept L)
          encodedPrefix)
        (Tape.normalizedOutput
          (rightEdgeRewindSourceTape (ParsedLayoutBits L)
            (postFieldDecodedPrefixScanPadding useAccept L)))

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierOutputConstruction :
    Prop :=
  exists densifier : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierOutputSpec
      densifier

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierOutputSpec
    (densifier : MachineDescription) : Prop :=
  densifier.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout)
      (deletedTail : Word Bool),
      densifier.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderTargetTape
          (postFieldDecodedPrefixScanSourceTape useAccept L)
          (countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
            useAccept L deletedTail))
        (Tape.normalizedOutput
          (rightEdgeRewindSourceTape (ParsedLayoutBits L)
            (postFieldDecodedPrefixScanPadding useAccept L)))

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierOutputConstruction :
    Prop :=
  exists densifier : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierOutputSpec
      densifier

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserOutputSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout)
      (encodedPrefix : List (Option Bool)),
      eraser.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderTargetTape
          (postFieldDecodedPrefixScanSourceTape useAccept L)
          encodedPrefix)
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderTargetTape
            (postFieldDecodedPrefixScanSourceTape useAccept L)
            []))

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserOutputConstruction :
    Prop :=
  exists eraser : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserOutputSpec
      eraser

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserOutputSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout)
      (deletedTail : Word Bool),
      eraser.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderTargetTape
          (postFieldDecodedPrefixScanSourceTape useAccept L)
          (countWindowPostFieldDecodedPrefixSelectedSegmentEncodedPrefix
            useAccept L deletedTail))
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderTargetTape
            (postFieldDecodedPrefixScanSourceTape useAccept L)
            []))

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserOutputConstruction :
    Prop :=
  exists eraser : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserOutputSpec
      eraser

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchOutputSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall (L : DovetailLayout) (deletedTail : Word Bool),
      eraser.HaltsFromTapeWithOutput
        (countWindowPostFieldDecodedPrefixStructuredPrefixEraserSourceTape
          true L deletedTail)
        (Tape.normalizedOutput
          (countWindowPostFieldDecodedPrefixStructuredPrefixEraserTargetTape
            true L))) ∧
    forall (L : DovetailLayout) (deletedTail : Word Bool),
      eraser.HaltsFromTapeWithOutput
        (countWindowPostFieldDecodedPrefixStructuredPrefixEraserSourceTape
          false L deletedTail)
        (Tape.normalizedOutput
          (countWindowPostFieldDecodedPrefixStructuredPrefixEraserTargetTape
            false L))

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchOutputConstruction :
    Prop :=
  exists eraser : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchOutputSpec
      eraser

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseOutputSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall L : DovetailLayout,
      eraser.HaltsFromTapeWithOutput
        (countWindowPostFieldDecodedPrefixStructuredPrefixEraserSourceTape
          true L [])
        (Tape.normalizedOutput
          (countWindowPostFieldDecodedPrefixStructuredPrefixEraserTargetTape
            true L))) ∧
    (forall (L : DovetailLayout) (bit : Bool) (rest : Word Bool),
      eraser.HaltsFromTapeWithOutput
        (countWindowPostFieldDecodedPrefixStructuredPrefixEraserSourceTape
          true L (bit :: rest))
        (Tape.normalizedOutput
          (countWindowPostFieldDecodedPrefixStructuredPrefixEraserTargetTape
            true L))) ∧
    (forall L : DovetailLayout,
      eraser.HaltsFromTapeWithOutput
        (countWindowPostFieldDecodedPrefixStructuredPrefixEraserSourceTape
          false L [])
        (Tape.normalizedOutput
          (countWindowPostFieldDecodedPrefixStructuredPrefixEraserTargetTape
            false L))) ∧
    forall (L : DovetailLayout) (bit : Bool) (rest : Word Bool),
      eraser.HaltsFromTapeWithOutput
        (countWindowPostFieldDecodedPrefixStructuredPrefixEraserSourceTape
          false L (bit :: rest))
        (Tape.normalizedOutput
          (countWindowPostFieldDecodedPrefixStructuredPrefixEraserTargetTape
            false L))

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseOutputConstruction :
    Prop :=
  exists eraser : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseOutputSpec
      eraser

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorOutputSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    forall (useAccept : Bool) (L : DovetailLayout),
      compactor.HaltsFromTapeWithOutput
        (countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorSourceTape
          useAccept L)
        (Tape.normalizedOutput
          (countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorTargetTape
            useAccept L))

def CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorOutputConstruction :
    Prop :=
  exists compactor : MachineDescription,
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorOutputSpec
      compactor

theorem countWindowPostFieldDecodedPrefixStructuredOutputProjectorOutputSpec_of_exact
    {projector : MachineDescription}
    (hprojector :
      CountWindowPostFieldDecodedPrefixStructuredOutputProjectorSpec
        projector) :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorOutputSpec
      projector := by
  rcases hprojector with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro useAccept L deletedTail
  exact
    haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
      (hrun useAccept L deletedTail)

theorem countWindowPostFieldDecodedPrefixStructuredOutputProjectorOutputConstruction_of_exact
    (hprojector :
      CountWindowPostFieldDecodedPrefixStructuredOutputProjectorConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredOutputProjectorOutputConstruction := by
  rcases hprojector with ⟨projector, hspec⟩
  exact
    ⟨projector,
      countWindowPostFieldDecodedPrefixStructuredOutputProjectorOutputSpec_of_exact
        hspec⟩

theorem countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerOutputSpec_of_exact
    {normalizer : MachineDescription}
    (hnormalizer :
      CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerSpec
        normalizer) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerOutputSpec
      normalizer := by
  rcases hnormalizer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro useAccept L deletedTail physical hseparator
  exact
    haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
      (hrun useAccept L deletedTail physical hseparator)

theorem countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerOutputConstruction_of_exact
    (hnormalizer :
      CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerConstruction) :
    CountWindowPostFieldDecodedPrefixStructuredSegmentNormalizerOutputConstruction := by
  rcases hnormalizer with ⟨normalizer, hspec⟩
  exact
    ⟨normalizer,
      countWindowPostFieldDecodedPrefixStructuredSegmentNormalizerOutputSpec_of_exact
        hspec⟩

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderOutputSpec_of_exact
    {decoder : MachineDescription}
    (hdecoder :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderSpec
        decoder) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderOutputSpec
      decoder := by
  rcases hdecoder with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro useAccept L encodedPrefix
  exact
    haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
      (hrun useAccept L encodedPrefix)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderOutputConstruction_of_exact
    (hdecoder :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderOutputConstruction := by
  rcases hdecoder with ⟨decoder, hspec⟩
  exact
    ⟨decoder,
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderOutputSpec_of_exact
        hspec⟩

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixOutputSpec_of_exact
    {decoder : MachineDescription}
    (hdecoder :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixSpec
        decoder) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixOutputSpec
      decoder := by
  rcases hdecoder with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro useAccept L deletedTail
  exact
    haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
      (hrun useAccept L deletedTail)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixOutputConstruction_of_exact
    (hdecoder :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixOutputConstruction := by
  rcases hdecoder with ⟨decoder, hspec⟩
  exact
    ⟨decoder,
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixOutputSpec_of_exact
        hspec⟩

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupOutputSpec_of_exact
    {cleanup : MachineDescription}
    (hcleanup :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupSpec
        cleanup) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupOutputSpec
      cleanup := by
  rcases hcleanup with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro useAccept L encodedPrefix
  exact
    haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
      (hrun useAccept L encodedPrefix)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupOutputConstruction_of_exact
    (hcleanup :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupOutputConstruction := by
  rcases hcleanup with ⟨cleanup, hspec⟩
  exact
    ⟨cleanup,
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderCleanupOutputSpec_of_exact
        hspec⟩

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupOutputSpec_of_exact
    {cleanup : MachineDescription}
    (hcleanup :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupSpec
        cleanup) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupOutputSpec
      cleanup := by
  rcases hcleanup with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro useAccept L deletedTail
  exact
    haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
      (hrun useAccept L deletedTail)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupOutputConstruction_of_exact
    (hcleanup :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupOutputConstruction := by
  rcases hcleanup with ⟨cleanup, hspec⟩
  exact
    ⟨cleanup,
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixCleanupOutputSpec_of_exact
        hspec⟩

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierOutputSpec_of_exact
    {densifier : MachineDescription}
    (hdensifier :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierSpec
        densifier) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierOutputSpec
      densifier := by
  rcases hdensifier with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro useAccept L encodedPrefix
  exact
    haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
      (hrun useAccept L encodedPrefix)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierOutputConstruction_of_exact
    (hdensifier :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierOutputConstruction := by
  rcases hdensifier with ⟨densifier, hspec⟩
  exact
    ⟨densifier,
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderDensifierOutputSpec_of_exact
        hspec⟩

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierOutputSpec_of_exact
    {densifier : MachineDescription}
    (hdensifier :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierSpec
        densifier) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierOutputSpec
      densifier := by
  rcases hdensifier with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro useAccept L deletedTail
  exact
    haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
      (hrun useAccept L deletedTail)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierOutputConstruction_of_exact
    (hdensifier :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierOutputConstruction := by
  rcases hdensifier with ⟨densifier, hspec⟩
  exact
    ⟨densifier,
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixDensifierOutputSpec_of_exact
        hspec⟩

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserOutputSpec_of_exact
    {eraser : MachineDescription}
    (heraser :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserSpec
        eraser) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserOutputSpec
      eraser := by
  rcases heraser with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro useAccept L encodedPrefix
  exact
    haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
      (hrun useAccept L encodedPrefix)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserOutputConstruction_of_exact
    (heraser :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserOutputConstruction := by
  rcases heraser with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserOutputSpec_of_exact
        hspec⟩

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserOutputSpec_of_exact
    {eraser : MachineDescription}
    (heraser :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserSpec
        eraser) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserOutputSpec
      eraser := by
  rcases heraser with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro useAccept L deletedTail
  exact
    haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
      (hrun useAccept L deletedTail)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserOutputConstruction_of_exact
    (heraser :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserOutputConstruction := by
  rcases heraser with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserOutputSpec_of_exact
        hspec⟩

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchOutputSpec_of_exact
    {eraser : MachineDescription}
    (heraser :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchSpec
        eraser) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchOutputSpec
      eraser := by
  rcases heraser with ⟨hready, haccept, hreject⟩
  refine ⟨hready, ?_, ?_⟩
  · intro L deletedTail
    exact
      haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
        (haccept L deletedTail)
  · intro L deletedTail
    exact
      haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
        (hreject L deletedTail)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchOutputConstruction_of_exact
    (heraser :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchOutputConstruction := by
  rcases heraser with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchOutputSpec_of_exact
        hspec⟩

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseOutputSpec_of_exact
    {eraser : MachineDescription}
    (heraser :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseSpec
        eraser) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseOutputSpec
      eraser := by
  rcases heraser with
    ⟨hready, hacceptNil, hacceptCons, hrejectNil, hrejectCons⟩
  refine ⟨hready, ?_, ?_, ?_, ?_⟩
  · intro L
    exact
      haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
        (hacceptNil L)
  · intro L bit rest
    exact
      haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
        (hacceptCons L bit rest)
  · intro L
    exact
      haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
        (hrejectNil L)
  · intro L bit rest
    exact
      haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
        (hrejectCons L bit rest)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseOutputConstruction_of_exact
    (heraser :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseOutputConstruction := by
  rcases heraser with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseOutputSpec_of_exact
        hspec⟩

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorOutputSpec_of_exact
    {compactor : MachineDescription}
    (hcompactor :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorSpec
        compactor) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorOutputSpec
      compactor := by
  rcases hcompactor with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro useAccept L
  exact
    haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
      (hrun useAccept L)

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorOutputConstruction_of_exact
    (hcompactor :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorOutputConstruction := by
  rcases hcompactor with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorOutputSpec_of_exact
        hspec⟩

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorOutputSpec_of_generic
    {compactor : MachineDescription}
    (hgeneric :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorOutputSpec
        compactor) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorOutputSpec
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

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorOutputConstruction_of_generic
    (hgeneric :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorOutputConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorOutputConstruction := by
  rcases hgeneric with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderFootprintCompactorOutputSpec_of_generic
        hspec⟩

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchOutputSpec_of_casesOutput
    {eraser : MachineDescription}
    (hcases :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseOutputSpec
        eraser) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchOutputSpec
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

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchOutputConstruction_of_casesOutput
    (hcases :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseOutputConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchOutputConstruction := by
  rcases hcases with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchOutputSpec_of_casesOutput
        hspec⟩

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserOutputSpec_of_branchesOutput
    {eraser : MachineDescription}
    (hbranches :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchOutputSpec
        eraser) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserOutputSpec
      eraser := by
  rcases hbranches with ⟨hready, haccept, hreject⟩
  refine ⟨hready, ?_⟩
  intro useAccept L deletedTail
  cases useAccept
  · exact hreject L deletedTail
  · exact haccept L deletedTail

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserOutputConstruction_of_branchesOutput
    (hbranches :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchOutputConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserOutputConstruction := by
  rcases hbranches with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserOutputSpec_of_branchesOutput
        hspec⟩

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseOutputSpec_of_prefixEraserOutput
    {eraser : MachineDescription}
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserOutputSpec
        eraser) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseOutputSpec
      eraser := by
  rcases hprefix with ⟨hready, hrun⟩
  refine ⟨hready, ?_, ?_, ?_, ?_⟩
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

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseOutputConstruction_of_prefixEraserOutput
    (hprefix :
      CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderPrefixEraserOutputConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseOutputConstruction := by
  rcases hprefix with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseOutputSpec_of_prefixEraserOutput
        hspec⟩

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseOutputSpec_of_twoTapeStructuredPrefixEraserOutput
    {eraser : MachineDescription}
    (heraser :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputSpec
        eraser) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseOutputSpec
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

theorem countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseOutputConstruction_of_twoTapeStructuredPrefixEraserOutput
    (heraser :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputConstruction) :
    CountWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseOutputConstruction := by
  rcases heraser with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      countWindowPostFieldDecodedPrefixSelectedSegmentDecoderStructuredPrefixEraserBranchCaseOutputSpec_of_twoTapeStructuredPrefixEraserOutput
        hspec⟩

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters
end Computability
end FoC
