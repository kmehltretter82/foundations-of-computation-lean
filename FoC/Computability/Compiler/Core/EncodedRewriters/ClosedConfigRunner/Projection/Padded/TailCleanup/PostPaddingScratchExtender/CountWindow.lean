import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.PostPaddingScratchExtender.CountWindowPositioner

set_option doc.verso true

/-!
# Post-padding scratch-count window construction

This module contains the exact scratch-count counter source/target tapes, the
checked core run that appends blanks once the count window is exposed, and the
remaining finite-machine construction leaf for exposing that window.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncodedRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

open CanonicalLayouts.DovetailLayoutScanner

/-!
The source and target tapes expose the scratch-count field as a local counted
window. The extra-tail variants keep the same local shape while preserving the
post-count scratch suffix needed by the final cleanup route.
-/

def selectedProjectionPaddedTailCleanupScratchCountCounterSourceTape
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  tapeAtCells
    (none ::
      (selectedProjectionPaddedTailCleanupScratchSkippedBits
        useAccept L).reverse.map some)
    (List.append
      ((selectedProjectionPaddedTailCleanupScratchCountBits
        useAccept L).map some)
      (none ::
        none ::
        List.replicate
          (selectedProjectionPaddedTailCleanupScratchCountBits
            useAccept L).length
          (none : Option Bool)))

def selectedProjectionPaddedTailCleanupScratchCountCounterTargetTape
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  tapeAtCells
    (none ::
      (selectedProjectionPaddedTailCleanupScratchSkippedBits
        useAccept L).reverse.map some)
    (List.append
      ((selectedProjectionPaddedTailCleanupScratchCountBits
        useAccept L).map some)
      (none ::
        List.replicate
          ((selectedProjectionPaddedTailCleanupScratchCountBits
            useAccept L).length + 1)
          (none : Option Bool)))

def selectedProjectionPaddedTailCleanupScratchCountCounterSourceTapeWithPostCountTail
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    Tape Bool :=
  tapeAtCells
    (none ::
      (selectedProjectionPaddedTailCleanupScratchSkippedBits
        useAccept L).reverse.map some)
    (List.append
      ((selectedProjectionPaddedTailCleanupScratchCountBits
        useAccept L).map some)
      (none ::
        none ::
        List.append
          (List.replicate
            (selectedProjectionPaddedTailCleanupScratchCountBits
              useAccept L).length
            (none : Option Bool))
          (selectedProjectionPaddedTailCleanupPostCountTailCells
            useAccept L extraScratch)))

def selectedProjectionPaddedTailCleanupScratchCountCounterTargetTapeWithPostCountTail
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    Tape Bool :=
  tapeAtCells
    (none ::
      (selectedProjectionPaddedTailCleanupScratchSkippedBits
        useAccept L).reverse.map some)
    (List.append
      ((selectedProjectionPaddedTailCleanupScratchCountBits
        useAccept L).map some)
      (none ::
        List.append
          (List.replicate
            ((selectedProjectionPaddedTailCleanupScratchCountBits
              useAccept L).length + 1)
            (none : Option Bool))
          (selectedProjectionPaddedTailCleanupPostCountTailCells
            useAccept L extraScratch)))

theorem selectedProjectionPaddedTailCleanupScratchCountCounterSourceTapeWithPostCountTail_move_left_move_right
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (selectedProjectionPaddedTailCleanupScratchCountCounterSourceTapeWithPostCountTail
            useAccept L extraScratch)) =
      selectedProjectionPaddedTailCleanupScratchCountCounterSourceTapeWithPostCountTail
        useAccept L extraScratch := by
  unfold selectedProjectionPaddedTailCleanupScratchCountCounterSourceTapeWithPostCountTail
  cases hcount :
      selectedProjectionPaddedTailCleanupScratchCountBits useAccept L with
  | nil =>
      simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons bit rest =>
      cases rest <;>
        simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem selectedProjectionPaddedTailCleanupScratchCountCounterTargetTapeWithPostCountTail_move_left_move_right
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (selectedProjectionPaddedTailCleanupScratchCountCounterTargetTapeWithPostCountTail
            useAccept L extraScratch)) =
      selectedProjectionPaddedTailCleanupScratchCountCounterTargetTapeWithPostCountTail
        useAccept L extraScratch := by
  unfold selectedProjectionPaddedTailCleanupScratchCountCounterTargetTapeWithPostCountTail
  cases hcount :
      selectedProjectionPaddedTailCleanupScratchCountBits useAccept L with
  | nil =>
      simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons bit rest =>
      cases rest <;>
        simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem selectedProjectionPaddedTailCleanupScratchCountCounterSourceTape_normalizedOutput
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedProjectionPaddedTailCleanupScratchCountCounterSourceTape
          useAccept L) =
      ParsedLayoutBits L := by
  simpa [selectedProjectionPaddedTailCleanupScratchCountCounterSourceTape,
    tapeAtCells_normalizedOutput, List.filterMap_append,
    Function.comp_def, List.append_assoc] using
      (selectedProjectionPaddedTailCleanupParsedLayoutBits_eq_skipped_append_count
        useAccept L).symm

theorem selectedProjectionPaddedTailCleanupScratchCountCounterTargetTape_normalizedOutput
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedProjectionPaddedTailCleanupScratchCountCounterTargetTape
          useAccept L) =
      ParsedLayoutBits L := by
  simpa [selectedProjectionPaddedTailCleanupScratchCountCounterTargetTape,
    tapeAtCells_normalizedOutput, List.filterMap_append,
    Function.comp_def, List.append_assoc] using
      (selectedProjectionPaddedTailCleanupParsedLayoutBits_eq_skipped_append_count
        useAccept L).symm

theorem selectedProjectionPaddedTailCleanupScratchCountCounterSourceTapeWithPostCountTail_normalizedOutput
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    Tape.normalizedOutput
        (selectedProjectionPaddedTailCleanupScratchCountCounterSourceTapeWithPostCountTail
          useAccept L extraScratch) =
      List.append (ParsedLayoutBits L)
        ((selectedProjectionPaddedTailCleanupPostCountTailCells
          useAccept L extraScratch).filterMap id) := by
  have hprefix :=
    (selectedProjectionPaddedTailCleanupParsedLayoutBits_eq_skipped_append_count
      useAccept L).symm
  simpa [
    selectedProjectionPaddedTailCleanupScratchCountCounterSourceTapeWithPostCountTail,
    tapeAtCells_normalizedOutput, List.filterMap_append,
    Function.comp_def, List.append_assoc] using
      congrArg
        (fun pref =>
          List.append pref
            ((selectedProjectionPaddedTailCleanupPostCountTailCells
              useAccept L extraScratch).filterMap id))
        hprefix

theorem selectedProjectionPaddedTailCleanupScratchCountCounterTargetTapeWithPostCountTail_normalizedOutput
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    Tape.normalizedOutput
        (selectedProjectionPaddedTailCleanupScratchCountCounterTargetTapeWithPostCountTail
          useAccept L extraScratch) =
      List.append (ParsedLayoutBits L)
        ((selectedProjectionPaddedTailCleanupPostCountTailCells
          useAccept L extraScratch).filterMap id) := by
  have hprefix :=
    (selectedProjectionPaddedTailCleanupParsedLayoutBits_eq_skipped_append_count
      useAccept L).symm
  simpa [
    selectedProjectionPaddedTailCleanupScratchCountCounterTargetTapeWithPostCountTail,
    tapeAtCells_normalizedOutput, List.filterMap_append,
    Function.comp_def, List.append_assoc] using
      congrArg
        (fun pref =>
          List.append pref
            ((selectedProjectionPaddedTailCleanupPostCountTailCells
              useAccept L extraScratch).filterMap id))
        hprefix

/--
Executable core of the post-padding scratch extender after the branch-specific
navigation has exposed the scratch-count suffix under the head.
-/
theorem scratchCounterAppendBlanksDescription_haltsFrom_scratchCountWindow
    (useAccept : Bool) (L : DovetailLayout) :
    scratchCounterAppendBlanksDescription.HaltsFromTape
      (selectedProjectionPaddedTailCleanupScratchCountCounterSourceTape
        useAccept L)
      (selectedProjectionPaddedTailCleanupScratchCountCounterTargetTape
        useAccept L) := by
  simpa [
    selectedProjectionPaddedTailCleanupScratchCountCounterSourceTape,
    selectedProjectionPaddedTailCleanupScratchCountCounterTargetTape]
    using
      scratchCounterAppendBlanksDescription_haltsFrom_withRight
        ((selectedProjectionPaddedTailCleanupScratchSkippedBits
          useAccept L).reverse.map some)
        (selectedProjectionPaddedTailCleanupScratchCountBits useAccept L)
        []
        (selectedProjectionPaddedTailCleanupScratchCountBits_length_pos
          useAccept L)

/--
Executable raw-window counter with the branch-specific post-count tail
preserved as right context.  This is the shape the surrounding extender must
reach after it has decoded/exposed the selected parsed-layout count field; it
is not itself the original encoded branch source.
-/
theorem scratchCounterAppendBlanksDescription_haltsFrom_scratchCountWindowWithPostCountTail
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    scratchCounterAppendBlanksDescription.HaltsFromTape
      (selectedProjectionPaddedTailCleanupScratchCountCounterSourceTapeWithPostCountTail
        useAccept L extraScratch)
      (selectedProjectionPaddedTailCleanupScratchCountCounterTargetTapeWithPostCountTail
        useAccept L extraScratch) := by
  simpa [
    selectedProjectionPaddedTailCleanupScratchCountCounterSourceTapeWithPostCountTail,
    selectedProjectionPaddedTailCleanupScratchCountCounterTargetTapeWithPostCountTail,
    List.append_assoc]
    using
      scratchCounterAppendBlanksDescription_haltsFrom_withRight
        ((selectedProjectionPaddedTailCleanupScratchSkippedBits
          useAccept L).reverse.map some)
        (selectedProjectionPaddedTailCleanupScratchCountBits useAccept L)
        (selectedProjectionPaddedTailCleanupPostCountTailCells
          useAccept L extraScratch)
        (selectedProjectionPaddedTailCleanupScratchCountBits_length_pos
          useAccept L)

/--
The scratch-count materializer starts at the still-encoded count-window source
tape.  This tape names the source from the count split directly, separating it
from the raw counter window below.
-/
def selectedProjectionPaddedTailCleanupEncodedCountWindowTape
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    Tape Bool :=
  tapeAtCells [none]
    (selectedProjectionPaddedTailCleanupEncodedCountWindowSourceCells
      useAccept L extraScratch)

theorem selectedProjectionPaddedTailCleanupEncodedCountWindowTape_eq_baseSourceTapeWithExtraScratch
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    selectedProjectionPaddedTailCleanupEncodedCountWindowTape
        useAccept L extraScratch =
      selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
        useAccept L extraScratch := by
  rw [selectedProjectionPaddedTailCleanupEncodedCountWindowTape]
  exact
    (selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch_countSplit
      useAccept L extraScratch).symm

theorem selectedProjectionPaddedTailCleanupEncodedCountWindowTape_normalizedOutput
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    Tape.normalizedOutput
        (selectedProjectionPaddedTailCleanupEncodedCountWindowTape
          useAccept L extraScratch) =
      selectedProjectionPaddedTailCleanupPostPaddingSourceBits
        useAccept L := by
  rw [
    selectedProjectionPaddedTailCleanupEncodedCountWindowTape_eq_baseSourceTapeWithExtraScratch]
  exact
    selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch_normalizedOutput
      useAccept L extraScratch

/--
The materializer/restorer leaf is not a suffix scanner wrapper.  It must bridge
between an encoded count-window tape, whose selected layout fields are still
length-prefixed input cells, and the raw counter tape, where the parsed-layout
bits have been split into skipped and counted regions.
-/
def SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerSpec
    (useAccept : Bool) (materializer : MachineDescription) : Prop :=
  materializer.SubroutineReady ∧
    forall L : DovetailLayout,
      materializer.HaltsFromTape
        (selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
          useAccept L 0)
        (selectedProjectionPaddedTailCleanupScratchCountCounterSourceTapeWithPostCountTail
          useAccept L 0)

def SelectedProjectionPaddedTailCleanupScratchCountWindowRestorerSpec
    (useAccept : Bool) (restorer : MachineDescription) : Prop :=
  restorer.SubroutineReady ∧
    forall L : DovetailLayout,
      restorer.HaltsFromTape
        (selectedProjectionPaddedTailCleanupScratchCountCounterTargetTapeWithPostCountTail
          useAccept L 0)
        (selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
          useAccept L
          (selectedProjectionPaddedTailCleanupScratchCountBits
            useAccept L).length)

theorem selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerSpec_iff_encodedCountWindowTape
    (useAccept : Bool) (materializer : MachineDescription) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerSpec
        useAccept materializer ↔
      materializer.SubroutineReady ∧
        forall L : DovetailLayout,
          materializer.HaltsFromTape
            (selectedProjectionPaddedTailCleanupEncodedCountWindowTape
              useAccept L 0)
            (selectedProjectionPaddedTailCleanupScratchCountCounterSourceTapeWithPostCountTail
              useAccept L 0) := by
  constructor
  · intro h
    refine ⟨h.left, ?_⟩
    intro L
    rw [
      selectedProjectionPaddedTailCleanupEncodedCountWindowTape_eq_baseSourceTapeWithExtraScratch]
    exact h.right L
  · intro h
    refine ⟨h.left, ?_⟩
    intro L
    rw [←
      selectedProjectionPaddedTailCleanupEncodedCountWindowTape_eq_baseSourceTapeWithExtraScratch]
    exact h.right L

theorem selectedProjectionPaddedTailCleanupScratchCountWindowRestorerSpec_iff_encodedCountWindowTape
    (useAccept : Bool) (restorer : MachineDescription) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRestorerSpec
        useAccept restorer ↔
      restorer.SubroutineReady ∧
        forall L : DovetailLayout,
          restorer.HaltsFromTape
            (selectedProjectionPaddedTailCleanupScratchCountCounterTargetTapeWithPostCountTail
              useAccept L 0)
            (selectedProjectionPaddedTailCleanupEncodedCountWindowTape
              useAccept L
              (selectedProjectionPaddedTailCleanupScratchCountBits
                useAccept L).length) := by
  constructor
  · intro h
    refine ⟨h.left, ?_⟩
    intro L
    rw [
      selectedProjectionPaddedTailCleanupEncodedCountWindowTape_eq_baseSourceTapeWithExtraScratch]
    exact h.right L
  · intro h
    refine ⟨h.left, ?_⟩
    intro L
    rw [←
      selectedProjectionPaddedTailCleanupEncodedCountWindowTape_eq_baseSourceTapeWithExtraScratch]
    exact h.right L

def SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction :
    Prop :=
  forall useAccept : Bool,
    exists materializer : MachineDescription,
    exists restorer : MachineDescription,
      SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerSpec
        useAccept materializer ∧
      SelectedProjectionPaddedTailCleanupScratchCountWindowRestorerSpec
        useAccept restorer

def SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction :
    Prop :=
  forall useAccept : Bool,
    exists materializer : MachineDescription,
      SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerSpec
        useAccept materializer

def SelectedProjectionPaddedTailCleanupScratchCountWindowRestorerConstruction :
    Prop :=
  forall useAccept : Bool,
    exists restorer : MachineDescription,
      SelectedProjectionPaddedTailCleanupScratchCountWindowRestorerSpec
        useAccept restorer

def selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithPostCountTail
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    Tape Bool :=
  tapeAtCells [none]
    (List.append
      ((ParsedLayoutBits L).map some)
      (none ::
        none ::
        List.append
          (List.replicate
            (selectedProjectionPaddedTailCleanupScratchCountBits
              useAccept L).length
            (none : Option Bool))
          (selectedProjectionPaddedTailCleanupPostCountTailCells
            useAccept L extraScratch)))

def SelectedProjectionPaddedTailCleanupScratchCountWindowDecoderSpec
    (useAccept : Bool) (decoder : MachineDescription) : Prop :=
  decoder.SubroutineReady ∧
    forall L : DovetailLayout,
      decoder.HaltsFromTape
        (selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
          useAccept L 0)
        (selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithPostCountTail
          useAccept L 0)

def SelectedProjectionPaddedTailCleanupScratchCountWindowPrefixScannerSpec
    (useAccept : Bool) (scanner : MachineDescription) : Prop :=
  scanner.SubroutineReady ∧
    forall L : DovetailLayout,
      scanner.HaltsFromTape
        (selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
          useAccept L 0)
        (selectedProjectionPaddedTailCleanupAfterOutputPrefixScanTape
          useAccept L 0)

def selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRestorerSourceTape
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    Tape Bool :=
  Tape.move Direction.right
    (selectedProjectionPaddedTailCleanupAfterOutputPrefixScanTape
      useAccept L extraScratch)

def SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixRestorerSpec
    (useAccept : Bool) (restorer : MachineDescription) : Prop :=
  restorer.SubroutineReady ∧
    forall L : DovetailLayout,
      restorer.HaltsFromTape
        (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRestorerSourceTape
          useAccept L 0)
        (selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithPostCountTail
          useAccept L 0)

def selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    Tape Bool :=
  tapeAtCells ((ParsedLayoutBits L).reverse.map some)
    (none ::
      none ::
      List.append
        (List.replicate
          (selectedProjectionPaddedTailCleanupScratchCountBits
            useAccept L).length
          (none : Option Bool))
        (selectedProjectionPaddedTailCleanupPostCountTailCells
          useAccept L extraScratch))

def SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixNormalizerSpec
    (useAccept : Bool) (normalizer : MachineDescription) : Prop :=
  normalizer.SubroutineReady ∧
    forall L : DovetailLayout,
      normalizer.HaltsFromTape
        (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRestorerSourceTape
          useAccept L 0)
        (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape
          useAccept L 0)

def SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixRewinderSpec
    (useAccept : Bool) (rewinder : MachineDescription) : Prop :=
  rewinder.SubroutineReady ∧
    forall L : DovetailLayout,
      rewinder.HaltsFromTape
        (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape
          useAccept L 0)
        (selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithPostCountTail
          useAccept L 0)

def selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerSourceTape
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    Tape Bool :=
  tapeAtCells
    (List.append
      ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        L.stage).reverse.map some)
      (cellListCanonicalRestoredLeftWithBase
        ((ParsedLayoutBits L).map some)
        (postPaddingOutputPrefixHeaderBase [none])))
    (selectedProjectionPaddedTailCleanupAfterStageTailCells
      useAccept L extraScratch)

def SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixStageScannerSpec
    (useAccept : Bool) (scanner : MachineDescription) : Prop :=
  scanner.SubroutineReady ∧
    forall L : DovetailLayout,
      scanner.HaltsFromTape
        (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRestorerSourceTape
          useAccept L 0)
        (selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerSourceTape
          useAccept L 0)

def SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixTailNormalizerSpec
    (useAccept : Bool) (normalizer : MachineDescription) : Prop :=
  normalizer.SubroutineReady ∧
    forall L : DovetailLayout,
      normalizer.HaltsFromTape
        (selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerSourceTape
          useAccept L 0)
        (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape
          useAccept L 0)

def selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
    (L : DovetailLayout) : List (Option Bool) :=
  List.append
    ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
      L.stage).reverse.map some)
    (cellListCanonicalRestoredLeftWithBase
      ((ParsedLayoutBits L).map some)
      (postPaddingOutputPrefixHeaderBase [none]))

def selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload
    (L : DovetailLayout) : Word Bool :=
  List.append
    (selectedProjectionPaddedTailCleanupUnselectedConfigBits true L)
    (selectedProjectionPaddedTailCleanupSelectedHitBits true L)

def selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayload
    (L : DovetailLayout) : Word Bool :=
  selectedProjectionPaddedTailCleanupSelectedConfigBits false L

def selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayloadRest
    (L : DovetailLayout) : Word Bool :=
  (selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload
    L).tail

def selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayloadRest
    (L : DovetailLayout) : Word Bool :=
  (selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayload
    L).tail

def selectedProjectionPaddedTailCleanupScratchCountAcceptAfterFirstFieldEraseTape
    (L : DovetailLayout) (extraScratch : Nat) : Tape Bool :=
  rightBlankGapPayloadScanTargetTape
    (selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
      L)
    (configurationFieldBits L.acceptConfig []).length
    false
    (selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayloadRest
      L)
    (List.append (List.replicate 5 (none : Option Bool))
      (List.replicate extraScratch (none : Option Bool)))

def selectedProjectionPaddedTailCleanupScratchCountRejectAfterFirstFieldEraseTape
    (L : DovetailLayout) (extraScratch : Nat) : Tape Bool :=
  rightBlankGapPayloadScanTargetTape
    (selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
      L)
    (configurationFieldBits L.acceptConfig []).length
    false
    (selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayloadRest
      L)
    (List.append (List.replicate 3 (none : Option Bool))
      (List.append
        ((selectedProjectionPaddedTailCleanupSelectedHitBits
          false L).map some)
        (none :: none ::
          List.replicate extraScratch (none : Option Bool))))

def SelectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixFirstFieldEraserSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    forall L : DovetailLayout,
      eraser.HaltsFromTape
        (selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerSourceTape
          true L 0)
        (selectedProjectionPaddedTailCleanupScratchCountAcceptAfterFirstFieldEraseTape
          L 0)

def SelectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixFirstFieldEraserSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    forall L : DovetailLayout,
      eraser.HaltsFromTape
        (selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerSourceTape
          false L 0)
        (selectedProjectionPaddedTailCleanupScratchCountRejectAfterFirstFieldEraseTape
          L 0)

def SelectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixPostFieldNormalizerSpec
    (normalizer : MachineDescription) : Prop :=
  normalizer.SubroutineReady ∧
    forall L : DovetailLayout,
      normalizer.HaltsFromTape
        (selectedProjectionPaddedTailCleanupScratchCountAcceptAfterFirstFieldEraseTape
          L 0)
        (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape
          true L 0)

def SelectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixPostFieldNormalizerSpec
    (normalizer : MachineDescription) : Prop :=
  normalizer.SubroutineReady ∧
    forall L : DovetailLayout,
      normalizer.HaltsFromTape
        (selectedProjectionPaddedTailCleanupScratchCountRejectAfterFirstFieldEraseTape
          L 0)
        (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape
          false L 0)

def selectedProjectionPaddedTailCleanupScratchCountAfterFirstFieldEraseTape
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    Tape Bool :=
  if useAccept then
    selectedProjectionPaddedTailCleanupScratchCountAcceptAfterFirstFieldEraseTape
      L extraScratch
  else
    selectedProjectionPaddedTailCleanupScratchCountRejectAfterFirstFieldEraseTape
      L extraScratch

def SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixPostFieldNormalizerSpec
    (useAccept : Bool) (normalizer : MachineDescription) : Prop :=
  normalizer.SubroutineReady ∧
    forall L : DovetailLayout,
      normalizer.HaltsFromTape
        (selectedProjectionPaddedTailCleanupScratchCountAfterFirstFieldEraseTape
          useAccept L 0)
        (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape
          useAccept L 0)

def selectedProjectionPaddedTailCleanupScratchCountAcceptPostFieldHandoffTape
    (L : DovetailLayout) (extraScratch : Nat) : Tape Bool :=
  Tape.move Direction.right
    (selectedProjectionPaddedTailCleanupScratchCountAcceptAfterFirstFieldEraseTape
      L extraScratch)

def selectedProjectionPaddedTailCleanupScratchCountRejectPostFieldHandoffTape
    (L : DovetailLayout) (extraScratch : Nat) : Tape Bool :=
  Tape.move Direction.right
    (selectedProjectionPaddedTailCleanupScratchCountRejectAfterFirstFieldEraseTape
      L extraScratch)

def SelectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixPostFieldHandoffCoreSpec
    (normalizer : MachineDescription) : Prop :=
  normalizer.SubroutineReady ∧
    forall L : DovetailLayout,
      normalizer.HaltsFromTape
        (selectedProjectionPaddedTailCleanupScratchCountAcceptPostFieldHandoffTape
          L 0)
        (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape
          true L 0)

def SelectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixPostFieldHandoffCoreSpec
    (normalizer : MachineDescription) : Prop :=
  normalizer.SubroutineReady ∧
    forall L : DovetailLayout,
      normalizer.HaltsFromTape
        (selectedProjectionPaddedTailCleanupScratchCountRejectPostFieldHandoffTape
          L 0)
        (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape
          false L 0)

theorem selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRestorerSourceTape_eq
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRestorerSourceTape
        useAccept L extraScratch =
      tapeAtCells
        (cellListCanonicalRestoredLeftWithBase
          ((ParsedLayoutBits L).map some)
          (postPaddingOutputPrefixHeaderBase [none]))
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage).map some)
          (selectedProjectionPaddedTailCleanupAfterStageTailCells
            useAccept L extraScratch)) := by
  simpa [
    selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRestorerSourceTape]
    using
      selectedProjectionPaddedTailCleanupAfterOutputPrefixScanTape_move_right
        useAccept L extraScratch

theorem selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithPostCountTail_eq_skipped_count
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithPostCountTail
        useAccept L extraScratch =
      tapeAtCells [none]
        (List.append
          ((selectedProjectionPaddedTailCleanupScratchSkippedBits
            useAccept L).map some)
          (List.append
            ((selectedProjectionPaddedTailCleanupScratchCountBits
              useAccept L).map some)
            (none ::
              none ::
              List.append
                (List.replicate
                  (selectedProjectionPaddedTailCleanupScratchCountBits
                    useAccept L).length
                  (none : Option Bool))
                (selectedProjectionPaddedTailCleanupPostCountTailCells
                  useAccept L extraScratch)))) := by
  rw [selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithPostCountTail]
  rw [
    selectedProjectionPaddedTailCleanupParsedLayoutBits_eq_skipped_append_count
      useAccept L]
  simp [List.map_append, List.append_assoc]

theorem selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape_move_left_move_right
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape
            useAccept L extraScratch)) =
      selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape
        useAccept L extraScratch := by
  unfold selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape
  simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem sourceRewindDescription_step_finish_withRight
    (bits : Word Bool) (rightCells : List (Option Bool)) :
    sourceRewindDescription.runConfig 1
        { state := 1
          tape :=
            tapeAtCells []
              (none :: List.append (bits.map some) rightCells) } =
      { state := sourceRewindDescription.halt
        tape := tapeAtCells [none]
          (List.append (bits.map some) rightCells) } := by
  cases hright : List.append (bits.map some) rightCells with
  | nil =>
      simp [sourceRewindDescription, tapeAtCells, runConfig, stepConfig,
        lookupTransition, Matches, transition, Tape.read, Tape.move,
        Tape.moveRight, Tape.write]
  | cons cell rest =>
      simp [sourceRewindDescription, tapeAtCells, runConfig, stepConfig,
        lookupTransition, Matches, transition, Tape.read, Tape.move,
        Tape.moveRight, Tape.write]

theorem sourceRewindDescription_run_from_leftStack_withRight
    (leftStack : Word Bool) (rightCells : List (Option Bool)) :
    sourceRewindDescription.runConfig (leftStack.length + 2)
        { state := sourceRewindDescription.start
          tape :=
            tapeAtCells (leftStack.map some)
              (none :: rightCells) } =
      { state := sourceRewindDescription.halt
        tape :=
          tapeAtCells [none]
            (List.append (leftStack.reverse.map some)
              (none :: rightCells)) } := by
  cases leftStack with
  | nil =>
      simp [sourceRewindDescription, tapeAtCells, runConfig, stepConfig,
        lookupTransition, Matches, transition, Tape.read, Tape.move,
        Tape.moveLeft, Tape.moveRight, Tape.write]
  | cons current rest =>
      rw [show (current :: rest).length + 2 =
        1 + ((rest.length + 1) + 1) by
        simp
        lia]
      rw [runConfig_add]
      have hstart :
          sourceRewindDescription.runConfig 1
              { state := sourceRewindDescription.start
                tape :=
                  tapeAtCells ((current :: rest).map some)
                    (none :: rightCells) } =
            { state := 1
              tape :=
                tapeAtCells (rest.map some)
                  (some current :: none :: rightCells) } := by
        cases current <;>
          simp [sourceRewindDescription, tapeAtCells, runConfig,
            stepConfig, lookupTransition, Matches, transition, Tape.read,
            Tape.move, Tape.moveLeft, Tape.write]
      rw [hstart]
      rw [show (rest.length + 1) + 1 = (rest.length + 1) + 1 by rfl]
      rw [runConfig_add]
      have hscan :
          sourceRewindDescription.runConfig (rest.length + 1)
              { state := 1
                tape :=
                  tapeAtCells (rest.map some)
                    (some current :: none :: rightCells) } =
            { state := 1
              tape :=
                tapeAtCells []
                  (none ::
                    List.append
                      ((List.append rest.reverse [current]).map some)
                      (none :: rightCells)) } := by
        simpa [tapeAtCells, DovetailInitialLayoutInitializer.tapeAtCells,
          List.append_assoc] using
          sourceRewindDescription_run_scan rest current (none :: rightCells)
      rw [hscan]
      simpa [List.map_append, List.append_assoc] using
        sourceRewindDescription_step_finish_withRight
          (List.append rest.reverse [current]) (none :: rightCells)

theorem sourceRewindDescription_haltsFromTape_withRight
    (bits : Word Bool) (rightCells : List (Option Bool)) :
    sourceRewindDescription.HaltsFromTape
      (tapeAtCells (bits.reverse.map some) (none :: rightCells))
      (tapeAtCells [none]
        (List.append (bits.map some) (none :: rightCells))) := by
  refine ⟨bits.length + 2, ?_⟩
  constructor
  · simpa using
      congrArg MachineDescription.Configuration.state
        (sourceRewindDescription_run_from_leftStack_withRight
          bits.reverse rightCells)
  · simpa using
      congrArg MachineDescription.Configuration.tape
        (sourceRewindDescription_run_from_leftStack_withRight
          bits.reverse rightCells)

theorem sourceRewindDescription_haltsFrom_scratchCountDecodedPrefixRewindSourceTape
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    sourceRewindDescription.HaltsFromTape
      (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape
        useAccept L extraScratch)
      (selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithPostCountTail
        useAccept L extraScratch) := by
  rw [
    selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape,
    selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithPostCountTail]
  exact
    sourceRewindDescription_haltsFromTape_withRight
      (ParsedLayoutBits L)
      (none ::
        List.append
          (List.replicate
            (selectedProjectionPaddedTailCleanupScratchCountBits
              useAccept L).length
            (none : Option Bool))
          (selectedProjectionPaddedTailCleanupPostCountTailCells
            useAccept L extraScratch))

def SelectedProjectionPaddedTailCleanupScratchCountWindowPositionerSpec
    (useAccept : Bool) (positioner : MachineDescription) : Prop :=
  positioner.SubroutineReady ∧
    forall L : DovetailLayout,
      positioner.HaltsFromTape
        (selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithPostCountTail
          useAccept L 0)
        (selectedProjectionPaddedTailCleanupScratchCountCounterSourceTapeWithPostCountTail
          useAccept L 0)

def selectedProjectionPaddedTailCleanupScratchCountRawToCounterHandoffTape
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    Tape Bool :=
  Tape.move Direction.right
    (selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithPostCountTail
      useAccept L extraScratch)

def SelectedProjectionPaddedTailCleanupScratchCountWindowRawToCounterPositionerHandoffCoreSpec
    (useAccept : Bool) (positioner : MachineDescription) : Prop :=
  positioner.SubroutineReady ∧
    forall L : DovetailLayout,
      positioner.HaltsFromTape
        (selectedProjectionPaddedTailCleanupScratchCountRawToCounterHandoffTape
          useAccept L 0)
        (selectedProjectionPaddedTailCleanupScratchCountCounterSourceTapeWithPostCountTail
          useAccept L 0)

def SelectedProjectionPaddedTailCleanupScratchCountWindowDecoderConstruction :
    Prop :=
  forall useAccept : Bool,
    exists decoder : MachineDescription,
      SelectedProjectionPaddedTailCleanupScratchCountWindowDecoderSpec
        useAccept decoder

def SelectedProjectionPaddedTailCleanupScratchCountWindowPrefixScannerConstruction :
    Prop :=
  forall useAccept : Bool,
    exists scanner : MachineDescription,
      SelectedProjectionPaddedTailCleanupScratchCountWindowPrefixScannerSpec
        useAccept scanner

def SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixRestorerConstruction :
    Prop :=
  forall useAccept : Bool,
    exists restorer : MachineDescription,
      SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixRestorerSpec
        useAccept restorer

def SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixNormalizerConstruction :
    Prop :=
  forall useAccept : Bool,
    exists normalizer : MachineDescription,
      SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixNormalizerSpec
        useAccept normalizer

def SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixRewinderConstruction :
    Prop :=
  forall useAccept : Bool,
    exists rewinder : MachineDescription,
      SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixRewinderSpec
        useAccept rewinder

def SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixStageScannerConstruction :
    Prop :=
  forall useAccept : Bool,
    exists scanner : MachineDescription,
      SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixStageScannerSpec
        useAccept scanner

def SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixTailNormalizerConstruction :
    Prop :=
  forall useAccept : Bool,
    exists normalizer : MachineDescription,
      SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixTailNormalizerSpec
        useAccept normalizer

def SelectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixTailNormalizerConstruction :
    Prop :=
  exists normalizer : MachineDescription,
    SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixTailNormalizerSpec
      true normalizer

def SelectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixTailNormalizerConstruction :
    Prop :=
  exists normalizer : MachineDescription,
    SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixTailNormalizerSpec
      false normalizer

def SelectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixFirstFieldEraserConstruction :
    Prop :=
  exists eraser : MachineDescription,
    SelectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixFirstFieldEraserSpec
      eraser

def SelectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixFirstFieldEraserConstruction :
    Prop :=
  exists eraser : MachineDescription,
    SelectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixFirstFieldEraserSpec
      eraser

def SelectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixPostFieldNormalizerConstruction :
    Prop :=
  exists normalizer : MachineDescription,
    SelectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixPostFieldNormalizerSpec
      normalizer

def SelectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixPostFieldNormalizerConstruction :
    Prop :=
  exists normalizer : MachineDescription,
    SelectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixPostFieldNormalizerSpec
      normalizer

def SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixPostFieldNormalizerConstruction :
    Prop :=
  forall useAccept : Bool,
    exists normalizer : MachineDescription,
      SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixPostFieldNormalizerSpec
        useAccept normalizer

def SelectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixPostFieldHandoffCoreConstruction :
    Prop :=
  exists normalizer : MachineDescription,
    SelectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixPostFieldHandoffCoreSpec
      normalizer

def SelectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixPostFieldHandoffCoreConstruction :
    Prop :=
  exists normalizer : MachineDescription,
    SelectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixPostFieldHandoffCoreSpec
      normalizer

def SelectedProjectionPaddedTailCleanupScratchCountWindowPositionerConstruction :
    Prop :=
  forall useAccept : Bool,
    exists positioner : MachineDescription,
      SelectedProjectionPaddedTailCleanupScratchCountWindowPositionerSpec
        useAccept positioner

def SelectedProjectionPaddedTailCleanupScratchCountWindowRawToCounterPositionerHandoffCoreConstruction
    (useAccept : Bool) : Prop :=
  exists positioner : MachineDescription,
    SelectedProjectionPaddedTailCleanupScratchCountWindowRawToCounterPositionerHandoffCoreSpec
      useAccept positioner

def scratchCountSuffixRestorerRightEdgeTape
    (pref suffix : Word Bool) (rightTail : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells
    (none ::
      List.append
        (suffix.reverse.map some)
        (none :: pref.reverse.map some))
    (List.append
      (List.replicate (suffix.length + 1) (none : Option Bool))
      rightTail)

def scratchCountSuffixRestorerCompactedRightEdgeTape
    (pref suffix : Word Bool) (rightTail : List (Option Bool)) :
    Tape Bool :=
  leadingBlankLeftShiftTargetTapeWithPadding
    (pref.reverse.map some)
    suffix
    (none ::
      none ::
      List.append
        (List.replicate (suffix.length - 1) (none : Option Bool))
        rightTail)

def scratchCountSuffixRestorerExtraBlankRewindTape
    (pref suffix : Word Bool) (rightTail : List (Option Bool)) :
    Tape Bool :=
  rightEdgeRewindTargetTape
    (List.append pref suffix)
    (none ::
      none ::
      none ::
      List.append
        (List.replicate (suffix.length - 1) (none : Option Bool))
        rightTail)

def ScratchCountSuffixRightEdgeScannerSpec
    (scanner : MachineDescription) : Prop :=
  scanner.SubroutineReady ∧
    forall (pref suffix : Word Bool)
      (rightTail : List (Option Bool)),
      0 < suffix.length ->
        scanner.HaltsFromTape
          (scratchCountSuffixRestorerSourceTape
            pref suffix rightTail)
          (scratchCountSuffixRestorerRightEdgeTape
            pref suffix rightTail)

def ScratchCountSuffixRightEdgeScannerConstruction : Prop :=
  exists scanner : MachineDescription,
    ScratchCountSuffixRightEdgeScannerSpec scanner

def ScratchCountSuffixRightEdgeRestorerSpec
    (restorer : MachineDescription) : Prop :=
  restorer.SubroutineReady ∧
    forall (pref suffix : Word Bool)
      (rightTail : List (Option Bool)),
      0 < suffix.length ->
        restorer.HaltsFromTape
          (scratchCountSuffixRestorerRightEdgeTape
            pref suffix rightTail)
          (scratchCountSuffixPositionerSourceTape
            pref suffix rightTail)

def ScratchCountSuffixRightEdgeRestorerConstruction : Prop :=
  exists restorer : MachineDescription,
    ScratchCountSuffixRightEdgeRestorerSpec restorer

def ScratchCountSuffixRightEdgeLocalCompactorSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    forall (pref suffix : Word Bool)
      (rightTail : List (Option Bool)),
      0 < suffix.length ->
        compactor.HaltsFromTape
          (scratchCountSuffixRestorerRightEdgeTape
            pref suffix rightTail)
          (scratchCountSuffixRestorerCompactedRightEdgeTape
            pref suffix rightTail)

def ScratchCountSuffixRightEdgeLocalCompactorConstruction : Prop :=
  exists compactor : MachineDescription,
    ScratchCountSuffixRightEdgeLocalCompactorSpec compactor

def ScratchCountSuffixCompactedRightEdgeRestorerSpec
    (restorer : MachineDescription) : Prop :=
  restorer.SubroutineReady ∧
    forall (pref suffix : Word Bool)
      (rightTail : List (Option Bool)),
      0 < suffix.length ->
        restorer.HaltsFromTape
          (scratchCountSuffixRestorerCompactedRightEdgeTape
            pref suffix rightTail)
          (scratchCountSuffixPositionerSourceTape
            pref suffix rightTail)

def ScratchCountSuffixCompactedRightEdgeRestorerConstruction : Prop :=
  exists restorer : MachineDescription,
    ScratchCountSuffixCompactedRightEdgeRestorerSpec restorer

def ScratchCountSuffixCompactedRightEdgeRewinderSpec
    (rewinder : MachineDescription) : Prop :=
  rewinder.SubroutineReady ∧
    forall (pref suffix : Word Bool)
      (rightTail : List (Option Bool)),
      0 < suffix.length ->
        rewinder.HaltsFromTape
          (scratchCountSuffixRestorerCompactedRightEdgeTape
            pref suffix rightTail)
          (scratchCountSuffixRestorerExtraBlankRewindTape
            pref suffix rightTail)

def ScratchCountSuffixCompactedRightEdgeRewinderConstruction : Prop :=
  exists rewinder : MachineDescription,
    ScratchCountSuffixCompactedRightEdgeRewinderSpec rewinder

def ScratchCountSuffixExtraBlankRestorerSpec
    (restorer : MachineDescription) : Prop :=
  restorer.SubroutineReady ∧
    forall (pref suffix : Word Bool)
      (rightTail : List (Option Bool)),
      0 < suffix.length ->
        restorer.HaltsFromTape
          (scratchCountSuffixRestorerExtraBlankRewindTape
            pref suffix rightTail)
          (scratchCountSuffixPositionerSourceTape
            pref suffix rightTail)

def ScratchCountSuffixExtraBlankRestorerConstruction : Prop :=
  exists restorer : MachineDescription,
    ScratchCountSuffixExtraBlankRestorerSpec restorer

def ScratchCountSuffixRestorerSpec
    (restorer : MachineDescription) : Prop :=
  restorer.SubroutineReady ∧
    forall (pref suffix : Word Bool)
      (rightTail : List (Option Bool)),
      0 < suffix.length ->
        restorer.HaltsFromTape
          (scratchCountSuffixRestorerSourceTape
            pref suffix rightTail)
          (scratchCountSuffixPositionerSourceTape
            pref suffix rightTail)

def ScratchCountSuffixRestorerConstruction : Prop :=
  exists restorer : MachineDescription,
    ScratchCountSuffixRestorerSpec restorer

def SelectedProjectionPaddedTailCleanupScratchCountWindowRawSourceEncoderSpec
    (useAccept : Bool) (encoder : MachineDescription) : Prop :=
  encoder.SubroutineReady ∧
    forall L : DovetailLayout,
      encoder.HaltsFromTape
        (selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithPostCountTail
          useAccept L 0)
        (selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
          useAccept L
          (selectedProjectionPaddedTailCleanupScratchCountBits
            useAccept L).length)

def SelectedProjectionPaddedTailCleanupScratchCountWindowRawSourceEncoderConstruction :
    Prop :=
  forall useAccept : Bool,
    exists encoder : MachineDescription,
      SelectedProjectionPaddedTailCleanupScratchCountWindowRawSourceEncoderSpec
        useAccept encoder

theorem selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithPostCountTail_move_left_move_right
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithPostCountTail
            useAccept L extraScratch)) =
      selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithPostCountTail
        useAccept L extraScratch := by
  rcases parsedLayoutBits_eq_false_false_tail L with ⟨tail, htail⟩
  rw [selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithPostCountTail]
  rw [htail]
  simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerSourceTape_move_left_move_right
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerSourceTape
            useAccept L extraScratch)) =
      selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerSourceTape
        useAccept L extraScratch := by
  cases useAccept
  · rcases
        selectedProjectionPaddedTailCleanupRejectAfterStageTailCells_fieldSplit
          L extraScratch with
      ⟨fieldTail, htail⟩
    cases fieldTail <;>
      simp [
        selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerSourceTape,
        selectedProjectionPaddedTailCleanupAfterStageTailCells,
        htail, tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]
  · rcases
        selectedProjectionPaddedTailCleanupAcceptAfterStageTailCells_fieldSplit
          L extraScratch with
      ⟨fieldTail, htail⟩
    cases fieldTail <;>
      simp [
        selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerSourceTape,
        selectedProjectionPaddedTailCleanupAfterStageTailCells,
        htail, tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem postPaddingOutputPrefixStageScannerTargetTapeWithRight_move_left_move_right
    (quoted : Word Bool) (stage : Nat)
    (baseLeft : List (Option Bool)) (fieldTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (postPaddingOutputPrefixStageScannerTargetTapeWithRight
            quoted stage baseLeft fieldTail rightPadding)) =
      postPaddingOutputPrefixStageScannerTargetTapeWithRight
        quoted stage baseLeft fieldTail rightPadding := by
  rcases
      CanonicalLayouts.DovetailStagePrefix.stageNatBits_reverse_map_some_cons
        stage with
    ⟨tail, htail⟩
  unfold postPaddingOutputPrefixStageScannerTargetTapeWithRight
  unfold CanonicalLayouts.DovetailStagePrefix.nonemptyNatSuffixHandoffConfigWithBaseAndRight
  rw [htail]
  simp [DovetailInitialLayoutInitializer.tapeAtCells, Tape.move,
    Tape.moveLeft, Tape.moveRight]

theorem selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixStageScanner_haltsFrom
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    (canonicalSeqDescription
        CanonicalLayouts.DovetailStagePrefix.NonemptyNatSuffixScannerDescription
        rightMoveOnceDescription).HaltsFromTape
      (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRestorerSourceTape
        useAccept L extraScratch)
      (selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerSourceTape
        useAccept L extraScratch) := by
  rcases
      selectedProjectionPaddedTailCleanupAfterStageTailCells_fieldSplit
        useAccept L extraScratch with
    ⟨fieldTail, rightPadding, htail⟩
  let mid :=
    postPaddingOutputPrefixStageScannerTargetTapeWithRight
      (ParsedLayoutBits L) L.stage [none] fieldTail rightPadding
  have hstage :
      CanonicalLayouts.DovetailStagePrefix.NonemptyNatSuffixScannerDescription.HaltsFromTape
        (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRestorerSourceTape
          useAccept L extraScratch)
        mid := by
    rw [
      selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRestorerSourceTape_eq,
      htail]
    simpa [mid, postPaddingOutputPrefixStageHandoffBase,
      DovetailInitialLayoutInitializer.tapeAtCells,
      tapeAtCells, List.map_append, List.append_assoc] using
      nonemptyNatSuffixScannerDescription_haltsFrom_outputPrefixStage_withRight
        (ParsedLayoutBits L) L.stage [none] fieldTail rightPadding
  have hmove :
      Tape.move Direction.right mid =
        selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerSourceTape
          useAccept L extraScratch := by
    unfold mid
    rw [
      postPaddingOutputPrefixStageScannerTarget_move_right_eq_configSource_withRight,
      selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerSourceTape,
      postPaddingOutputPrefixAfterStageBase,
      postPaddingOutputPrefixStageHandoffBase,
      ← htail]
    simp [DovetailInitialLayoutInitializer.tapeAtCells, tapeAtCells]
    rfl
  have hright :
      rightMoveOnceDescription.HaltsFromTape mid
        (selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerSourceTape
          useAccept L extraScratch) := by
    rw [← hmove]
    exact rightMoveOnceDescription_haltsFromTape mid
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      CanonicalLayouts.DovetailStagePrefix.nonemptyNatSuffixScannerDescription_subroutineReady
      rightMoveOnceDescription_subroutineReady
      hstage
      (postPaddingOutputPrefixStageScannerTargetTapeWithRight_move_left_move_right
        (ParsedLayoutBits L) L.stage [none] fieldTail rightPadding)
      hright

theorem rightBlankGapPayloadScanTargetTape_move_left_move_right
    (baseLeft : List (Option Bool)) (gap : Nat)
    (current : Bool) (payloadRest : Word Bool)
    (padding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (rightBlankGapPayloadScanTargetTape
            baseLeft gap current payloadRest padding)) =
      rightBlankGapPayloadScanTargetTape
        baseLeft gap current payloadRest padding := by
  rw [rightBlankGapPayloadScanTargetTape]
  rw [show
      List.append ((current :: payloadRest).reverse.map some)
          (List.append (List.replicate gap (none : Option Bool)) baseLeft) =
        List.append (payloadRest.reverse.map some)
          (some current ::
            List.append (List.replicate gap (none : Option Bool))
              baseLeft) by
    simp [List.reverse_cons, List.map_append, List.append_assoc]]
  exact
    congrArg (Tape.move Direction.left)
      (tapeAtCells_move_right_move_left_append_cons
        (payloadRest.reverse.map some)
        (List.append (List.replicate gap (none : Option Bool)) baseLeft)
        (none :: padding)
        (some current))

theorem selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload_cons_false
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload
        L =
      false ::
        selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayloadRest
          L := by
  rcases
      configurationFieldBits_cons_false L.rejectConfig
        (selectedProjectionPaddedTailCleanupSelectedHitBits true L) with
    ⟨payloadRest, hpayloadRest⟩
  have hpayload :
      selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload
          L =
        false :: payloadRest := by
    rw [selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload]
    rw [selectedProjectionPaddedTailCleanupUnselectedConfigBits]
    exact
        (configurationFieldBits_append_nil
        L.rejectConfig
        (selectedProjectionPaddedTailCleanupSelectedHitBits true L)).trans
        hpayloadRest
  have htail :
      payloadRest =
        selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayloadRest
          L := by
    simpa [
      selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayloadRest]
      using (congrArg List.tail hpayload).symm
  rw [hpayload, htail]

theorem selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayload_cons_false
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayload
        L =
      false ::
        selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayloadRest
        L := by
  rcases configurationFieldBits_cons_false L.rejectConfig [] with
    ⟨payloadRest, hpayloadRest⟩
  have hpayload :
      selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayload
          L =
        false :: payloadRest := by
    simpa [
      selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayload,
      selectedProjectionPaddedTailCleanupSelectedConfigBits]
      using hpayloadRest
  have htail :
      payloadRest =
        selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayloadRest
        L := by
    simpa [
      selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayloadRest]
      using (congrArg List.tail hpayload).symm
  rw [hpayload, htail]

theorem selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload_append_last
    (L : DovetailLayout) :
    exists pref : Word Bool,
    exists leftBit : Bool,
      selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload
          L =
        List.append pref [leftBit] := by
  rcases selectedProjectionPaddedTailCleanupSelectedHit_true_reverse_cons
      L with
    ⟨current, leftRest, hhitRev⟩
  refine
    ⟨List.append
        (selectedProjectionPaddedTailCleanupUnselectedConfigBits true L)
        leftRest.reverse,
      current, ?_⟩
  have hhit :
      selectedProjectionPaddedTailCleanupSelectedHitBits true L =
        List.append leftRest.reverse [current] := by
    rw [←
      List.reverse_reverse
        (selectedProjectionPaddedTailCleanupSelectedHitBits true L)]
    rw [hhitRev]
    simp
  rw [
    selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload,
    hhit]
  simp [List.append_assoc]

theorem selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayload_append_last
    (L : DovetailLayout) :
    exists pref : Word Bool,
    exists leftBit : Bool,
      selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayload
          L =
        List.append pref [leftBit] := by
  rcases selectedProjectionPaddedTailCleanupSelectedConfig_false_append_last
      L with
    ⟨pref, leftBit, hcfg⟩
  exact ⟨pref, leftBit, by
    simpa [
      selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayload,
      selectedProjectionPaddedTailCleanupSelectedConfigBits] using hcfg⟩

theorem selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldEraser_haltsFrom
    (L : DovetailLayout) (extraScratch : Nat) :
    leftBoundaryBitConfigurationFieldEraseAndPayloadScanDescription.HaltsFromTape
      (selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerSourceTape
        true L extraScratch)
      (selectedProjectionPaddedTailCleanupScratchCountAcceptAfterFirstFieldEraseTape
        L extraScratch) := by
  rcases
      CanonicalLayouts.DovetailStagePrefix.stageNatBits_reverse_map_some_cons
        L.stage with
    ⟨stageTail, hstageTail⟩
  have hpayload :=
    selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload_cons_false
      L
  have h :=
    leftBoundaryBitConfigurationFieldEraseAndPayloadScanDescription_haltsFromTape
      true L.acceptConfig
      (List.append stageTail
        (cellListCanonicalRestoredLeftWithBase
          ((ParsedLayoutBits L).map some)
          (postPaddingOutputPrefixHeaderBase [none])))
      (selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayloadRest
        L)
      (List.append (List.replicate 5 (none : Option Bool))
        (List.replicate extraScratch (none : Option Bool)))
  have hpayloadBits :
      false ::
          (List.append (configurationFieldBits L.rejectConfig [])
            (selectedProjectionPaddedTailCleanupSelectedHitBits true L)).tail =
        List.append (configurationFieldBits L.rejectConfig [])
          (selectedProjectionPaddedTailCleanupSelectedHitBits true L) := by
    simpa [
      selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload,
      selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayloadRest,
      selectedProjectionPaddedTailCleanupUnselectedConfigBits]
      using hpayload.symm
  have hfield :
      configurationFieldBits L.acceptConfig
          (false ::
            (List.append (configurationFieldBits L.rejectConfig [])
              (selectedProjectionPaddedTailCleanupSelectedHitBits true L)).tail) =
        List.append (configurationFieldBits L.acceptConfig [])
          (List.append (configurationFieldBits L.rejectConfig [])
            (selectedProjectionPaddedTailCleanupSelectedHitBits true L)) := by
    rw [hpayloadBits]
    exact
      (configurationFieldBits_append_nil L.acceptConfig
        (List.append (configurationFieldBits L.rejectConfig [])
          (selectedProjectionPaddedTailCleanupSelectedHitBits true L))).symm
  simp only [
    selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload,
    selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayloadRest,
    selectedProjectionPaddedTailCleanupUnselectedConfigBits] at h
  simp only [if_true] at h
  rw [hfield] at h
  simpa [
    selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerSourceTape,
    selectedProjectionPaddedTailCleanupScratchCountAcceptAfterFirstFieldEraseTape,
    selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase,
    hstageTail, hpayload,
    selectedProjectionPaddedTailCleanupAcceptAfterStageTailCells,
    selectedProjectionPaddedTailCleanupAfterStageTailCells,
    selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload,
    selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayloadRest,
    selectedProjectionPaddedTailCleanupSelectedConfigBits,
    selectedProjectionPaddedTailCleanupUnselectedConfigBits,
    List.map_append, List.append_assoc] using h

theorem selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldEraser_haltsFrom
    (L : DovetailLayout) (extraScratch : Nat) :
    leftBoundaryBitConfigurationFieldEraseAndPayloadScanDescription.HaltsFromTape
      (selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerSourceTape
        false L extraScratch)
      (selectedProjectionPaddedTailCleanupScratchCountRejectAfterFirstFieldEraseTape
        L extraScratch) := by
  rcases
      CanonicalLayouts.DovetailStagePrefix.stageNatBits_reverse_map_some_cons
        L.stage with
    ⟨stageTail, hstageTail⟩
  have hpayload :=
    selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayload_cons_false
      L
  have h :=
    leftBoundaryBitConfigurationFieldEraseAndPayloadScanDescription_haltsFromTape
      true L.acceptConfig
      (List.append stageTail
        (cellListCanonicalRestoredLeftWithBase
          ((ParsedLayoutBits L).map some)
          (postPaddingOutputPrefixHeaderBase [none])))
      (selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayloadRest
        L)
      (List.append (List.replicate 3 (none : Option Bool))
        (List.append
          ((selectedProjectionPaddedTailCleanupSelectedHitBits
            false L).map some)
          (none :: none ::
            List.replicate extraScratch (none : Option Bool))))
  have hpayloadBits :
      false ::
          (configurationFieldBits L.rejectConfig []).tail =
        configurationFieldBits L.rejectConfig [] := by
    simpa [
      selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayload,
      selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayloadRest,
      selectedProjectionPaddedTailCleanupSelectedConfigBits]
      using hpayload.symm
  have hfield :
      configurationFieldBits L.acceptConfig
          (false :: (configurationFieldBits L.rejectConfig []).tail) =
        List.append (configurationFieldBits L.acceptConfig [])
          (configurationFieldBits L.rejectConfig []) := by
    rw [hpayloadBits]
    exact
      (configurationFieldBits_append_nil L.acceptConfig
        (configurationFieldBits L.rejectConfig [])).symm
  simp only [
    selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayload,
    selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayloadRest,
    selectedProjectionPaddedTailCleanupSelectedConfigBits] at h
  simp only [Bool.false_eq_true, if_false] at h
  rw [hfield] at h
  simpa [
    selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerSourceTape,
    selectedProjectionPaddedTailCleanupScratchCountRejectAfterFirstFieldEraseTape,
    selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase,
    hstageTail, hpayload,
    selectedProjectionPaddedTailCleanupRejectAfterStageTailCells,
    selectedProjectionPaddedTailCleanupAfterStageTailCells,
    selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayload,
    selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayloadRest,
    selectedProjectionPaddedTailCleanupSelectedConfigBits,
    selectedProjectionPaddedTailCleanupUnselectedConfigBits,
    List.map_append, List.append_assoc] using h

theorem selectedProjectionPaddedTailCleanupScratchCountAcceptAfterFirstFieldEraseTape_move_left_move_right
    (L : DovetailLayout) (extraScratch : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (selectedProjectionPaddedTailCleanupScratchCountAcceptAfterFirstFieldEraseTape
            L extraScratch)) =
      selectedProjectionPaddedTailCleanupScratchCountAcceptAfterFirstFieldEraseTape
        L extraScratch := by
  exact
    rightBlankGapPayloadScanTargetTape_move_left_move_right
      (selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
        L)
      (configurationFieldBits L.acceptConfig []).length
      false
      (selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayloadRest
        L)
      (List.append (List.replicate 5 (none : Option Bool))
        (List.replicate extraScratch (none : Option Bool)))

theorem selectedProjectionPaddedTailCleanupScratchCountRejectAfterFirstFieldEraseTape_move_left_move_right
    (L : DovetailLayout) (extraScratch : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (selectedProjectionPaddedTailCleanupScratchCountRejectAfterFirstFieldEraseTape
            L extraScratch)) =
      selectedProjectionPaddedTailCleanupScratchCountRejectAfterFirstFieldEraseTape
        L extraScratch := by
  exact
    rightBlankGapPayloadScanTargetTape_move_left_move_right
      (selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
        L)
      (configurationFieldBits L.acceptConfig []).length
      false
      (selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayloadRest
        L)
      (List.append (List.replicate 3 (none : Option Bool))
        (List.append
          ((selectedProjectionPaddedTailCleanupSelectedHitBits
            false L).map some)
          (none :: none ::
            List.replicate extraScratch (none : Option Bool))))

theorem selectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixTailNormalizerSpec_of_firstFieldAndPostField
    {eraser normalizer : MachineDescription}
    (heraser :
      SelectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixFirstFieldEraserSpec
        eraser)
    (hnormalizer :
      SelectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixPostFieldNormalizerSpec
        normalizer) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixTailNormalizerSpec
      true (canonicalSeqDescription eraser normalizer) := by
  constructor
  · exact
      canonicalSeqDescription_subroutineReady
        heraser.left hnormalizer.left
  · intro L
    exact
      canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        heraser.left
        hnormalizer.left
        (heraser.right L)
        (selectedProjectionPaddedTailCleanupScratchCountAcceptAfterFirstFieldEraseTape_move_left_move_right
          L 0)
        (hnormalizer.right L)

theorem selectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixTailNormalizerSpec_of_firstFieldAndPostField
    {eraser normalizer : MachineDescription}
    (heraser :
      SelectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixFirstFieldEraserSpec
        eraser)
    (hnormalizer :
      SelectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixPostFieldNormalizerSpec
        normalizer) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixTailNormalizerSpec
      false (canonicalSeqDescription eraser normalizer) := by
  constructor
  · exact
      canonicalSeqDescription_subroutineReady
        heraser.left hnormalizer.left
  · intro L
    exact
      canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        heraser.left
        hnormalizer.left
        (heraser.right L)
        (selectedProjectionPaddedTailCleanupScratchCountRejectAfterFirstFieldEraseTape_move_left_move_right
          L 0)
        (hnormalizer.right L)

theorem selectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixTailNormalizerConstruction_of_firstFieldAndPostField
    (heraser :
      SelectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixFirstFieldEraserConstruction)
    (hnormalizer :
      SelectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixPostFieldNormalizerConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixTailNormalizerConstruction := by
  rcases heraser with ⟨eraser, heraserSpec⟩
  rcases hnormalizer with ⟨normalizer, hnormalizerSpec⟩
  exact
    ⟨canonicalSeqDescription eraser normalizer,
      selectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixTailNormalizerSpec_of_firstFieldAndPostField
        heraserSpec hnormalizerSpec⟩

theorem selectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixTailNormalizerConstruction_of_firstFieldAndPostField
    (heraser :
      SelectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixFirstFieldEraserConstruction)
    (hnormalizer :
      SelectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixPostFieldNormalizerConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixTailNormalizerConstruction := by
  rcases heraser with ⟨eraser, heraserSpec⟩
  rcases hnormalizer with ⟨normalizer, hnormalizerSpec⟩
  exact
    ⟨canonicalSeqDescription eraser normalizer,
      selectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixTailNormalizerSpec_of_firstFieldAndPostField
        heraserSpec hnormalizerSpec⟩

theorem selectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixPostFieldNormalizerSpec_of_handoffCore
    {normalizer : MachineDescription}
    (h :
      SelectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixPostFieldHandoffCoreSpec
        normalizer) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixPostFieldNormalizerSpec
      (seqSubroutine ExactIdentityDescription normalizer Direction.right) := by
  constructor
  · exact
      seqSubroutine_subroutineReady
        CommonGround.Identity.exactIdentityDescription_subroutineReady
        h.left
  · intro L
    exact
      CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
        CommonGround.Identity.exactIdentityDescription_subroutineReady
        h.left
        (CommonGround.Identity.exactIdentityDescription_haltsFromTape
          (selectedProjectionPaddedTailCleanupScratchCountAcceptAfterFirstFieldEraseTape
            L 0))
        rfl
        (h.right L)

theorem selectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixPostFieldNormalizerSpec_of_handoffCore
    {normalizer : MachineDescription}
    (h :
      SelectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixPostFieldHandoffCoreSpec
        normalizer) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixPostFieldNormalizerSpec
      (seqSubroutine ExactIdentityDescription normalizer Direction.right) := by
  constructor
  · exact
      seqSubroutine_subroutineReady
        CommonGround.Identity.exactIdentityDescription_subroutineReady
        h.left
  · intro L
    exact
      CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
        CommonGround.Identity.exactIdentityDescription_subroutineReady
        h.left
        (CommonGround.Identity.exactIdentityDescription_haltsFromTape
          (selectedProjectionPaddedTailCleanupScratchCountRejectAfterFirstFieldEraseTape
            L 0))
        rfl
        (h.right L)

theorem selectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixPostFieldNormalizerConstruction_of_handoffCore
    (h :
      SelectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixPostFieldHandoffCoreConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixPostFieldNormalizerConstruction := by
  rcases h with ⟨normalizer, hnormalizer⟩
  exact
    ⟨seqSubroutine ExactIdentityDescription normalizer Direction.right,
      selectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixPostFieldNormalizerSpec_of_handoffCore
        hnormalizer⟩

theorem selectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixPostFieldNormalizerConstruction_of_handoffCore
    (h :
      SelectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixPostFieldHandoffCoreConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixPostFieldNormalizerConstruction := by
  rcases h with ⟨normalizer, hnormalizer⟩
  exact
    ⟨seqSubroutine ExactIdentityDescription normalizer Direction.right,
      selectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixPostFieldNormalizerSpec_of_handoffCore
        hnormalizer⟩

theorem selectedProjectionPaddedTailCleanupScratchCountWindowDecoderSpec_of_prefixScannerAndDecodedRestorer
    {useAccept : Bool} {scanner restorer : MachineDescription}
    (hscanner :
      SelectedProjectionPaddedTailCleanupScratchCountWindowPrefixScannerSpec
        useAccept scanner)
    (hrestorer :
      SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixRestorerSpec
        useAccept restorer) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowDecoderSpec
      useAccept (seqSubroutine scanner restorer Direction.right) := by
  constructor
  · exact seqSubroutine_subroutineReady hscanner.left hrestorer.left
  · intro L
    exact
      CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
        hscanner.left
        hrestorer.left
        (hscanner.right L)
        rfl
        (hrestorer.right L)

theorem selectedProjectionPaddedTailCleanupScratchCountWindowDecoderConstruction_of_prefixScannerAndDecodedRestorer
    (hscanner :
      SelectedProjectionPaddedTailCleanupScratchCountWindowPrefixScannerConstruction)
    (hrestorer :
      SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixRestorerConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowDecoderConstruction := by
  intro useAccept
  rcases hscanner useAccept with ⟨scanner, hscannerUseAccept⟩
  rcases hrestorer useAccept with ⟨restorer, hrestorerUseAccept⟩
  exact
    ⟨seqSubroutine scanner restorer Direction.right,
      selectedProjectionPaddedTailCleanupScratchCountWindowDecoderSpec_of_prefixScannerAndDecodedRestorer
        hscannerUseAccept hrestorerUseAccept⟩

theorem selectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixNormalizerSpec_of_stageScannerAndTailNormalizer
    {useAccept : Bool} {scanner normalizer : MachineDescription}
    (hscanner :
      SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixStageScannerSpec
        useAccept scanner)
    (hnormalizer :
      SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixTailNormalizerSpec
        useAccept normalizer) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixNormalizerSpec
      useAccept (canonicalSeqDescription scanner normalizer) := by
  constructor
  · exact
      canonicalSeqDescription_subroutineReady
        hscanner.left hnormalizer.left
  · intro L
    exact
      canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        hscanner.left
        hnormalizer.left
        (hscanner.right L)
        (selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerSourceTape_move_left_move_right
          useAccept L 0)
        (hnormalizer.right L)

theorem selectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixNormalizerConstruction_of_stageScannerAndTailNormalizer
    (hscanner :
      SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixStageScannerConstruction)
    (hnormalizer :
      SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixTailNormalizerConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixNormalizerConstruction := by
  intro useAccept
  rcases hscanner useAccept with
    ⟨scanner, hscannerUseAccept⟩
  rcases hnormalizer useAccept with
    ⟨normalizer, hnormalizerUseAccept⟩
  exact
    ⟨canonicalSeqDescription scanner normalizer,
      selectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixNormalizerSpec_of_stageScannerAndTailNormalizer
        hscannerUseAccept hnormalizerUseAccept⟩

theorem selectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixTailNormalizerConstruction_of_branches
    (haccept :
      SelectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixTailNormalizerConstruction)
    (hreject :
      SelectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixTailNormalizerConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixTailNormalizerConstruction := by
  intro useAccept
  cases useAccept
  · exact hreject
  · exact haccept

theorem selectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixRestorerSpec_of_normalizerAndRewinder
    {useAccept : Bool} {normalizer rewinder : MachineDescription}
    (hnormalizer :
      SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixNormalizerSpec
        useAccept normalizer)
    (hrewinder :
      SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixRewinderSpec
        useAccept rewinder) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixRestorerSpec
      useAccept (canonicalSeqDescription normalizer rewinder) := by
  constructor
  · exact
      canonicalSeqDescription_subroutineReady
        hnormalizer.left hrewinder.left
  · intro L
    exact
      canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        hnormalizer.left
        hrewinder.left
        (hnormalizer.right L)
        (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape_move_left_move_right
          useAccept L 0)
        (hrewinder.right L)

theorem selectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixRestorerConstruction_of_normalizerAndRewinder
    (hnormalizer :
      SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixNormalizerConstruction)
    (hrewinder :
      SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixRewinderConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixRestorerConstruction := by
  intro useAccept
  rcases hnormalizer useAccept with
    ⟨normalizer, hnormalizerUseAccept⟩
  rcases hrewinder useAccept with
    ⟨rewinder, hrewinderUseAccept⟩
  exact
    ⟨canonicalSeqDescription normalizer rewinder,
      selectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixRestorerSpec_of_normalizerAndRewinder
        hnormalizerUseAccept hrewinderUseAccept⟩

theorem selectedProjectionPaddedTailCleanupScratchCountWindowPositionerSpec_of_handoffCore
    {useAccept : Bool} {positioner : MachineDescription}
    (h :
      SelectedProjectionPaddedTailCleanupScratchCountWindowRawToCounterPositionerHandoffCoreSpec
        useAccept positioner) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowPositionerSpec
      useAccept
      (seqSubroutine ExactIdentityDescription positioner Direction.right) := by
  constructor
  · exact
      seqSubroutine_subroutineReady
        CommonGround.Identity.exactIdentityDescription_subroutineReady
        h.left
  · intro L
    exact
      CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
        CommonGround.Identity.exactIdentityDescription_subroutineReady
        h.left
        (CommonGround.Identity.exactIdentityDescription_haltsFromTape
          (selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithPostCountTail
            useAccept L 0))
        rfl
        (h.right L)

theorem selectedProjectionPaddedTailCleanupScratchCountWindowPositionerConstruction_of_handoffCore
    {useAccept : Bool}
    (h :
      SelectedProjectionPaddedTailCleanupScratchCountWindowRawToCounterPositionerHandoffCoreConstruction
        useAccept) :
    exists positioner : MachineDescription,
      SelectedProjectionPaddedTailCleanupScratchCountWindowPositionerSpec
        useAccept positioner := by
  rcases h with ⟨positioner, hpositioner⟩
  exact
    ⟨seqSubroutine ExactIdentityDescription positioner Direction.right,
      selectedProjectionPaddedTailCleanupScratchCountWindowPositionerSpec_of_handoffCore
        hpositioner⟩

theorem erasePreservingScanDescription_haltsFromTape_withRight
    (input : Word Bool) (left right : List (Option Bool)) :
    erasePreservingScanDescription.HaltsFromTape
      (tapeAtCells left
        (List.append (input.map some) (none :: right)))
      (tapeAtCells
        (none :: List.append (input.reverse.map some) left)
        right) := by
  refine ⟨input.length + 1, ?_⟩
  have hrun :=
    erasePreservingScanDescription_run_to_blank input left right
  constructor
  · simpa using
      congrArg MachineDescription.Configuration.state hrun
  · simpa using
      congrArg MachineDescription.Configuration.tape hrun

theorem erasePreservingScanDescription_haltsFrom_scratchCountSuffixRestorerSourceTape
    (pref suffix : Word Bool) (rightTail : List (Option Bool)) :
    erasePreservingScanDescription.HaltsFromTape
      (scratchCountSuffixRestorerSourceTape pref suffix rightTail)
      (scratchCountSuffixRestorerRightEdgeTape pref suffix rightTail) := by
  simpa [
    scratchCountSuffixRestorerSourceTape,
    scratchCountSuffixRestorerRightEdgeTape,
    List.append_assoc] using
    erasePreservingScanDescription_haltsFromTape_withRight
      suffix
      (none :: pref.reverse.map some)
      (List.append
        (List.replicate (suffix.length + 1) (none : Option Bool))
        rightTail)

theorem scratchCountSuffixRestorerRightEdgeTape_move_left_move_right
    (pref suffix : Word Bool) (rightTail : List (Option Bool))
    (hpos : 0 < suffix.length) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (scratchCountSuffixRestorerRightEdgeTape
            pref suffix rightTail)) =
      scratchCountSuffixRestorerRightEdgeTape
        pref suffix rightTail := by
  cases suffix with
  | nil =>
      simp at hpos
  | cons bit rest =>
      cases rest <;>
        simp [scratchCountSuffixRestorerRightEdgeTape,
          tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight,
          List.replicate_succ]

theorem scratchCountSuffixRestorerCompactedRightEdgeTape_move_left_move_right
    (pref suffix : Word Bool) (rightTail : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (scratchCountSuffixRestorerCompactedRightEdgeTape
            pref suffix rightTail)) =
      scratchCountSuffixRestorerCompactedRightEdgeTape
        pref suffix rightTail := by
  simpa [scratchCountSuffixRestorerCompactedRightEdgeTape] using
    leadingBlankLeftShiftTargetTapeWithPadding_move_left_move_right_padding_cons_cons
      (pref.reverse.map some) suffix
      (none : Option Bool) (none : Option Bool)
      (List.append
        (List.replicate (suffix.length - 1) (none : Option Bool))
        rightTail)

theorem rightBlankLocalGapCompactorDescription_haltsFrom_scratchCountSuffixRestorerRightEdgeTape
    (pref suffix : Word Bool) (rightTail : List (Option Bool))
    (hpos : 0 < suffix.length) :
    rightBlankLocalGapCompactorDescription.HaltsFromTape
      (scratchCountSuffixRestorerRightEdgeTape pref suffix rightTail)
      (scratchCountSuffixRestorerCompactedRightEdgeTape
        pref suffix rightTail) := by
  cases hrev : suffix.reverse with
  | nil =>
      have hsuffix : suffix = [] := by
        rw [← List.reverse_reverse suffix, hrev]
        rfl
      simp [hsuffix] at hpos
  | cons current leftRest =>
      have hsuffix : suffix = (current :: leftRest).reverse := by
        rw [← List.reverse_reverse suffix, hrev]
      have hrun :=
        rightBlankLocalGapCompactorDescription_haltsFromTapeWithBase_leftStack_rightPadding
          (baseLeft := pref.reverse.map some)
          (current := current)
          (leftRest := leftRest)
          (paddingScratch := 1)
          (pad := (none : Option Bool))
          (rightPadding :=
            List.append
              (List.replicate (suffix.length - 1) (none : Option Bool))
              rightTail)
      simpa [
        scratchCountSuffixRestorerRightEdgeTape,
        scratchCountSuffixRestorerCompactedRightEdgeTape,
        rightBlankLocalGapCompactorSourceTapeWithBaseAndRight,
        hsuffix, List.replicate_succ, List.append_assoc] using hrun

theorem scratchCountSuffixRightEdgeRestorerSpec_of_localCompactorAndCompactedRestorer
    {compactor restorer : MachineDescription}
    (hcompactor : ScratchCountSuffixRightEdgeLocalCompactorSpec compactor)
    (hrestorer : ScratchCountSuffixCompactedRightEdgeRestorerSpec restorer) :
    ScratchCountSuffixRightEdgeRestorerSpec
      (canonicalSeqDescription compactor restorer) := by
  constructor
  · exact
      canonicalSeqDescription_subroutineReady
        hcompactor.left hrestorer.left
  · intro pref suffix rightTail hpos
    exact
      canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        hcompactor.left
        hrestorer.left
        (hcompactor.right pref suffix rightTail hpos)
        (scratchCountSuffixRestorerCompactedRightEdgeTape_move_left_move_right
          pref suffix rightTail)
        (hrestorer.right pref suffix rightTail hpos)

theorem scratchCountSuffixRightEdgeRestorerConstruction_of_localCompactorAndCompactedRestorer
    (hcompactor : ScratchCountSuffixRightEdgeLocalCompactorConstruction)
    (hrestorer : ScratchCountSuffixCompactedRightEdgeRestorerConstruction) :
    ScratchCountSuffixRightEdgeRestorerConstruction := by
  rcases hcompactor with ⟨compactor, hcompactorSpec⟩
  rcases hrestorer with ⟨restorer, hrestorerSpec⟩
  exact
    ⟨canonicalSeqDescription compactor restorer,
      scratchCountSuffixRightEdgeRestorerSpec_of_localCompactorAndCompactedRestorer
        hcompactorSpec hrestorerSpec⟩

theorem sentinelRewindDescription_haltsFrom_scratchCountCompactedRightEdgeTape
    (pref suffix : Word Bool) (rightTail : List (Option Bool))
    (hpos : 0 < suffix.length) :
    selectedProjectionPaddedTailCleanupSentinelRewindDescription.HaltsFromTape
      (scratchCountSuffixRestorerCompactedRightEdgeTape
        pref suffix rightTail)
      (scratchCountSuffixRestorerExtraBlankRewindTape
        pref suffix rightTail) := by
  cases suffix with
  | nil =>
      simp at hpos
  | cons bit rest =>
      have hrun :=
        selectedProjectionPaddedTailCleanupSentinelRewindDescription_haltsFrom
          (List.append pref (bit :: rest))
          (none ::
            List.append
              (List.replicate rest.length (none : Option Bool))
              rightTail)
      simpa [
        scratchCountSuffixRestorerCompactedRightEdgeTape,
        scratchCountSuffixRestorerExtraBlankRewindTape,
        leadingBlankLeftShiftTargetTapeWithPadding,
        rightEdgeRewindTargetTape,
        List.reverse_append, List.map_append, List.append_assoc] using
        hrun

theorem scratchCountSuffixRestorerExtraBlankRewindTape_move_left_move_right
    (pref suffix : Word Bool) (rightTail : List (Option Bool))
    (hpos : 0 < suffix.length) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (scratchCountSuffixRestorerExtraBlankRewindTape
            pref suffix rightTail)) =
      scratchCountSuffixRestorerExtraBlankRewindTape
        pref suffix rightTail := by
  cases pref with
  | nil =>
      cases suffix with
      | nil =>
          simp at hpos
      | cons bit rest =>
          simpa [scratchCountSuffixRestorerExtraBlankRewindTape] using
            rightEdgeRewindTargetTape_move_left_move_right_cons
              bit rest
              (none ::
                none ::
                none ::
                List.append
                  (List.replicate rest.length (none : Option Bool))
                  rightTail)
  | cons bit prefRest =>
      simpa [scratchCountSuffixRestorerExtraBlankRewindTape,
        List.append_assoc] using
        rightEdgeRewindTargetTape_move_left_move_right_cons
          bit (List.append prefRest suffix)
          (none ::
            none ::
            none ::
            List.append
              (List.replicate (suffix.length - 1) (none : Option Bool))
              rightTail)

theorem scratchCountSuffixCompactedRightEdgeRestorerSpec_of_rewinderAndExtraBlankRestorer
    {rewinder restorer : MachineDescription}
    (hrewinder : ScratchCountSuffixCompactedRightEdgeRewinderSpec rewinder)
    (hrestorer : ScratchCountSuffixExtraBlankRestorerSpec restorer) :
    ScratchCountSuffixCompactedRightEdgeRestorerSpec
      (canonicalSeqDescription rewinder restorer) := by
  constructor
  · exact
      canonicalSeqDescription_subroutineReady
        hrewinder.left hrestorer.left
  · intro pref suffix rightTail hpos
    exact
      canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        hrewinder.left
        hrestorer.left
        (hrewinder.right pref suffix rightTail hpos)
        (scratchCountSuffixRestorerExtraBlankRewindTape_move_left_move_right
          pref suffix rightTail hpos)
        (hrestorer.right pref suffix rightTail hpos)

theorem scratchCountSuffixCompactedRightEdgeRestorerConstruction_of_rewinderAndExtraBlankRestorer
    (hrewinder : ScratchCountSuffixCompactedRightEdgeRewinderConstruction)
    (hrestorer : ScratchCountSuffixExtraBlankRestorerConstruction) :
    ScratchCountSuffixCompactedRightEdgeRestorerConstruction := by
  rcases hrewinder with ⟨rewinder, hrewinderSpec⟩
  rcases hrestorer with ⟨restorer, hrestorerSpec⟩
  exact
    ⟨canonicalSeqDescription rewinder restorer,
      scratchCountSuffixCompactedRightEdgeRestorerSpec_of_rewinderAndExtraBlankRestorer
        hrewinderSpec hrestorerSpec⟩

theorem scratchCountSuffixRestorerSpec_of_rightEdgeScannerAndRestorer
    {scanner restorer : MachineDescription}
    (hscanner : ScratchCountSuffixRightEdgeScannerSpec scanner)
    (hrestorer : ScratchCountSuffixRightEdgeRestorerSpec restorer) :
    ScratchCountSuffixRestorerSpec
      (canonicalSeqDescription scanner restorer) := by
  constructor
  · exact
      canonicalSeqDescription_subroutineReady
        hscanner.left hrestorer.left
  · intro pref suffix rightTail hpos
    exact
      canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        hscanner.left
        hrestorer.left
        (hscanner.right pref suffix rightTail hpos)
        (scratchCountSuffixRestorerRightEdgeTape_move_left_move_right
          pref suffix rightTail hpos)
        (hrestorer.right pref suffix rightTail hpos)

theorem scratchCountSuffixRestorerConstruction_of_rightEdgeScannerAndRestorer
    (hscanner : ScratchCountSuffixRightEdgeScannerConstruction)
    (hrestorer : ScratchCountSuffixRightEdgeRestorerConstruction) :
    ScratchCountSuffixRestorerConstruction := by
  rcases hscanner with ⟨scanner, hscannerSpec⟩
  rcases hrestorer with ⟨restorer, hrestorerSpec⟩
  exact
    ⟨canonicalSeqDescription scanner restorer,
      scratchCountSuffixRestorerSpec_of_rightEdgeScannerAndRestorer
        hscannerSpec hrestorerSpec⟩

theorem selectedProjectionPaddedTailCleanupScratchCountWindowSuffixRestorer_haltsFrom
    {restorer : MachineDescription}
    (hrestorer : ScratchCountSuffixRestorerSpec restorer)
    (useAccept : Bool) (L : DovetailLayout) :
    restorer.HaltsFromTape
      (selectedProjectionPaddedTailCleanupScratchCountCounterTargetTapeWithPostCountTail
        useAccept L 0)
      (selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithPostCountTail
        useAccept L 0) := by
  have hrun :=
    hrestorer.right
      (selectedProjectionPaddedTailCleanupScratchSkippedBits useAccept L)
      (selectedProjectionPaddedTailCleanupScratchCountBits useAccept L)
      (selectedProjectionPaddedTailCleanupPostCountTailCells useAccept L 0)
      (selectedProjectionPaddedTailCleanupScratchCountBits_length_pos
        useAccept L)
  rw [
    selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithPostCountTail_eq_skipped_count]
  simpa [
    scratchCountSuffixRestorerSourceTape,
    scratchCountSuffixPositionerSourceTape,
    selectedProjectionPaddedTailCleanupScratchCountCounterTargetTapeWithPostCountTail,
    List.append_assoc] using hrun

theorem selectedProjectionPaddedTailCleanupScratchCountWindowRestorerSpec_of_suffixRestorerAndRawSourceEncoder
    {useAccept : Bool} {suffixRestorer encoder : MachineDescription}
    (hsuffixRestorer : ScratchCountSuffixRestorerSpec suffixRestorer)
    (hencoder :
      SelectedProjectionPaddedTailCleanupScratchCountWindowRawSourceEncoderSpec
        useAccept encoder) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRestorerSpec
      useAccept (canonicalSeqDescription suffixRestorer encoder) := by
  constructor
  · exact
      canonicalSeqDescription_subroutineReady
        hsuffixRestorer.left hencoder.left
  · intro L
    exact
      canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        hsuffixRestorer.left
        hencoder.left
        (selectedProjectionPaddedTailCleanupScratchCountWindowSuffixRestorer_haltsFrom
          hsuffixRestorer useAccept L)
        (selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithPostCountTail_move_left_move_right
          useAccept L 0)
        (hencoder.right L)

theorem selectedProjectionPaddedTailCleanupScratchCountWindowRestorerConstruction_of_suffixRestorerAndRawSourceEncoder
    (hsuffixRestorer : ScratchCountSuffixRestorerConstruction)
    (hencoder :
      SelectedProjectionPaddedTailCleanupScratchCountWindowRawSourceEncoderConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRestorerConstruction := by
  rcases hsuffixRestorer with
    ⟨suffixRestorer, hsuffixRestorerSpec⟩
  intro useAccept
  rcases hencoder useAccept with ⟨encoder, hencoderSpec⟩
  exact
    ⟨canonicalSeqDescription suffixRestorer encoder,
      selectedProjectionPaddedTailCleanupScratchCountWindowRestorerSpec_of_suffixRestorerAndRawSourceEncoder
        hsuffixRestorerSpec hencoderSpec⟩

theorem selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerSpec_of_decoderAndPositioner
    {useAccept : Bool} {decoder positioner : MachineDescription}
    (hdecoder :
      SelectedProjectionPaddedTailCleanupScratchCountWindowDecoderSpec
        useAccept decoder)
    (hpositioner :
      SelectedProjectionPaddedTailCleanupScratchCountWindowPositionerSpec
        useAccept positioner) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerSpec
      useAccept (canonicalSeqDescription decoder positioner) := by
  constructor
  · exact
      canonicalSeqDescription_subroutineReady
        hdecoder.left hpositioner.left
  · intro L
    exact
      canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        hdecoder.left
        hpositioner.left
        (hdecoder.right L)
        (selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithPostCountTail_move_left_move_right
          useAccept L 0)
        (hpositioner.right L)

theorem selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction_of_decoderAndPositioner
    (hdecoder :
      SelectedProjectionPaddedTailCleanupScratchCountWindowDecoderConstruction)
    (hpositioner :
      SelectedProjectionPaddedTailCleanupScratchCountWindowPositionerConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction := by
  intro useAccept
  rcases hdecoder useAccept with ⟨decoder, hdecoderUseAccept⟩
  rcases hpositioner useAccept with
    ⟨positioner, hpositionerUseAccept⟩
  exact
    ⟨canonicalSeqDescription decoder positioner,
      selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerSpec_of_decoderAndPositioner
        hdecoderUseAccept hpositionerUseAccept⟩

theorem selectedProjectionPaddedTailCleanupPostCountTailCells_cons_false
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    exists tail : List (Option Bool),
      selectedProjectionPaddedTailCleanupPostCountTailCells
          useAccept L extraScratch =
        some false :: tail := by
  rcases
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_false_false_tail
        L.stage with
    ⟨stageTail, hstageTail⟩
  cases useAccept
  · refine
      ⟨some false ::
        List.append (stageTail.map some)
          (selectedProjectionPaddedTailCleanupRejectAfterStageTailCells
            L extraScratch), ?_⟩
    simp [
      selectedProjectionPaddedTailCleanupPostCountTailCells,
      selectedProjectionPaddedTailCleanupRejectPostCountTailCells,
      hstageTail]
  · refine
      ⟨some false ::
        List.append (stageTail.map some)
          (selectedProjectionPaddedTailCleanupAcceptAfterStageTailCells
            L extraScratch), ?_⟩
    simp [
      selectedProjectionPaddedTailCleanupPostCountTailCells,
      selectedProjectionPaddedTailCleanupAcceptPostCountTailCells,
      hstageTail]

theorem selectedProjectionPaddedTailCleanupScratchCountWindowRawToCounterHandoffCoreSpec_of_suffixPositioner
    {useAccept : Bool} {positioner : MachineDescription}
    (hpositioner : ScratchCountSuffixPositionerHandoffSpec positioner) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRawToCounterPositionerHandoffCoreSpec
      useAccept positioner := by
  constructor
  · exact hpositioner.left
  · intro L
    rcases
        selectedProjectionPaddedTailCleanupPostCountTailCells_cons_false
          useAccept L 0 with
      ⟨postCountTail, hpostCountTail⟩
    have hrun :=
      hpositioner.right
        (selectedProjectionPaddedTailCleanupScratchSkippedBits useAccept L)
        (selectedProjectionPaddedTailCleanupScratchCountBits useAccept L)
        false
        postCountTail
        (selectedProjectionPaddedTailCleanupScratchCountBits_length_pos
          useAccept L)
    rw [← hpostCountTail] at hrun
    simpa [
      selectedProjectionPaddedTailCleanupScratchCountRawToCounterHandoffTape,
      selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithPostCountTail_eq_skipped_count,
      selectedProjectionPaddedTailCleanupScratchCountCounterSourceTapeWithPostCountTail,
      scratchCountSuffixPositionerSourceTape,
      scratchCountSuffixRestorerSourceTape,
      List.replicate_succ,
      List.append_assoc] using hrun

theorem selectedProjectionPaddedTailCleanupScratchCountWindowRawToCounterHandoffCoreConstruction_of_suffixPositioner
    {useAccept : Bool}
    (hpositioner : ScratchCountSuffixPositionerHandoffConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRawToCounterPositionerHandoffCoreConstruction
      useAccept := by
  rcases hpositioner with ⟨positioner, hpositionerSpec⟩
  exact
    ⟨positioner,
      selectedProjectionPaddedTailCleanupScratchCountWindowRawToCounterHandoffCoreSpec_of_suffixPositioner
        hpositionerSpec⟩

theorem selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction_of_parts
    (hmaterializer :
      SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction)
    (hrestorer :
      SelectedProjectionPaddedTailCleanupScratchCountWindowRestorerConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction := by
  intro useAccept
  rcases hmaterializer useAccept with ⟨materializer, hmaterializerUseAccept⟩
  rcases hrestorer useAccept with ⟨restorer, hrestorerUseAccept⟩
  exact ⟨materializer, restorer, hmaterializerUseAccept, hrestorerUseAccept⟩

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderSpec_of_countWindowMaterializerAndRestorer
    {useAccept : Bool} {materializer restorer : MachineDescription}
    (hmaterializer :
      SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerSpec
        useAccept materializer)
    (hrestorer :
      SelectedProjectionPaddedTailCleanupScratchCountWindowRestorerSpec
        useAccept restorer) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderSpec
      useAccept
      (canonicalSeqDescription
        (canonicalSeqDescription materializer
          scratchCounterAppendBlanksDescription)
        restorer) := by
  constructor
  · exact
      canonicalSeqDescription_subroutineReady
        (canonicalSeqDescription_subroutineReady
          hmaterializer.left
          scratchCounterAppendBlanksDescription_subroutineReady)
        hrestorer.left
  · intro L
    have hcounterSeq :
        (canonicalSeqDescription materializer
          scratchCounterAppendBlanksDescription).HaltsFromTape
          (selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
            useAccept L 0)
          (selectedProjectionPaddedTailCleanupScratchCountCounterTargetTapeWithPostCountTail
            useAccept L 0) := by
      exact
        canonicalSeqDescription_haltsFromTape_of_haltsFromTape
          hmaterializer.left
          scratchCounterAppendBlanksDescription_subroutineReady
          (hmaterializer.right L)
          (selectedProjectionPaddedTailCleanupScratchCountCounterSourceTapeWithPostCountTail_move_left_move_right
            useAccept L 0)
          (scratchCounterAppendBlanksDescription_haltsFrom_scratchCountWindowWithPostCountTail
            useAccept L 0)
    exact
      canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        (canonicalSeqDescription_subroutineReady
          hmaterializer.left
          scratchCounterAppendBlanksDescription_subroutineReady)
        hrestorer.left
        hcounterSeq
        (selectedProjectionPaddedTailCleanupScratchCountCounterTargetTapeWithPostCountTail_move_left_move_right
          useAccept L 0)
        (hrestorer.right L)

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction_of_countWindowMaterializers
    (h :
      SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction := by
  intro useAccept
  rcases h useAccept with
    ⟨materializer, restorer, hmaterializer, hrestorer⟩
  exact
    ⟨canonicalSeqDescription
        (canonicalSeqDescription materializer
          scratchCounterAppendBlanksDescription)
        restorer,
    selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderSpec_of_countWindowMaterializerAndRestorer
        hmaterializer hrestorer⟩

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
