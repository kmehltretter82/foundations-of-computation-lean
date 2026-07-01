import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.PostPaddingScratchWindow

set_option doc.verso true

/-!
# Post-padding scratch extender tapes

This module names the base-source and layout-scratch source tapes used by the
post-padding scratch extender, together with pure normalized-output and
right-left handoff lemmas.
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

def selectedProjectionPaddedTailCleanupAcceptLayoutScratchSourceTape
    (L : DovetailLayout) : Tape Bool :=
  tapeAtCells [none]
    (List.append
      ((selectedProjectionPaddedTailCleanupPostPaddingSourceBits
        true L).map some)
      (none ::
        List.append (List.replicate 5 (none : Option Bool))
          (List.replicate
            (selectedProjectionPaddedTailCleanupSentinelExtraScratch
              true L)
            (none : Option Bool))))

def selectedProjectionPaddedTailCleanupRejectLayoutScratchSourceTape
    (L : DovetailLayout) : Tape Bool :=
  tapeAtCells [none]
    (List.append
      (List.append
        (List.append
          ((selectedProjectionPaddedTailCleanupPrefixBits L).map some)
          ((selectedProjectionPaddedTailCleanupUnselectedConfigBits
            false L).map some))
        ((selectedProjectionPaddedTailCleanupSelectedConfigBits
          false L).map some))
      (List.append (List.replicate 4 (none : Option Bool))
        (List.append
          ((selectedProjectionPaddedTailCleanupSelectedHitBits
            false L).map some)
          (none :: none ::
            List.replicate
              (selectedProjectionPaddedTailCleanupSentinelExtraScratch
                false L)
              (none : Option Bool)))))

def selectedProjectionPaddedTailCleanupLayoutScratchSourceTape
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  if useAccept then
    selectedProjectionPaddedTailCleanupAcceptLayoutScratchSourceTape L
  else
    selectedProjectionPaddedTailCleanupRejectLayoutScratchSourceTape L

def selectedProjectionPaddedTailCleanupAcceptBaseSourceTape
    (L : DovetailLayout) : Tape Bool :=
  tapeAtCells [none]
    (List.append
      ((selectedProjectionPaddedTailCleanupPostPaddingSourceBits
        true L).map some)
      (none :: List.replicate 5 (none : Option Bool)))

def selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithExtraScratch
    (L : DovetailLayout) (extraScratch : Nat) : Tape Bool :=
  tapeAtCells [none]
    (List.append
      ((selectedProjectionPaddedTailCleanupPostPaddingSourceBits
        true L).map some)
      (none ::
        List.append (List.replicate 5 (none : Option Bool))
          (List.replicate extraScratch (none : Option Bool))))

def selectedProjectionPaddedTailCleanupRejectBaseSourceTape
    (L : DovetailLayout) : Tape Bool :=
  tapeAtCells [none]
    (List.append
      (List.append
        (List.append
          ((selectedProjectionPaddedTailCleanupPrefixBits L).map some)
          ((selectedProjectionPaddedTailCleanupUnselectedConfigBits
            false L).map some))
        ((selectedProjectionPaddedTailCleanupSelectedConfigBits
          false L).map some))
      (List.append (List.replicate 4 (none : Option Bool))
        (List.append
          ((selectedProjectionPaddedTailCleanupSelectedHitBits
            false L).map some)
          (none :: none :: []))))

def selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithExtraScratch
    (L : DovetailLayout) (extraScratch : Nat) : Tape Bool :=
  tapeAtCells [none]
    (List.append
      (List.append
        (List.append
          ((selectedProjectionPaddedTailCleanupPrefixBits L).map some)
          ((selectedProjectionPaddedTailCleanupUnselectedConfigBits
            false L).map some))
        ((selectedProjectionPaddedTailCleanupSelectedConfigBits
          false L).map some))
      (List.append (List.replicate 4 (none : Option Bool))
        (List.append
          ((selectedProjectionPaddedTailCleanupSelectedHitBits
            false L).map some)
          (none :: none ::
            List.replicate extraScratch (none : Option Bool)))))

def selectedProjectionPaddedTailCleanupBaseSourceTape
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  if useAccept then
    selectedProjectionPaddedTailCleanupAcceptBaseSourceTape L
  else
    selectedProjectionPaddedTailCleanupRejectBaseSourceTape L

def selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    Tape Bool :=
  if useAccept then
    selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithExtraScratch
      L extraScratch
  else
    selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithExtraScratch
      L extraScratch

def selectedProjectionPaddedTailCleanupAcceptAfterStageTailCells
    (L : DovetailLayout) (extraScratch : Nat) : List (Option Bool) :=
  List.append
    ((selectedProjectionPaddedTailCleanupSelectedConfigBits
      true L).map some)
    (List.append
      ((selectedProjectionPaddedTailCleanupUnselectedConfigBits
        true L).map some)
      (List.append
        ((selectedProjectionPaddedTailCleanupSelectedHitBits
          true L).map some)
        (none ::
          List.append (List.replicate 5 (none : Option Bool))
            (List.replicate extraScratch (none : Option Bool)))))

def selectedProjectionPaddedTailCleanupRejectAfterStageTailCells
    (L : DovetailLayout) (extraScratch : Nat) : List (Option Bool) :=
  List.append
    ((selectedProjectionPaddedTailCleanupUnselectedConfigBits
      false L).map some)
    (List.append
      ((selectedProjectionPaddedTailCleanupSelectedConfigBits
        false L).map some)
      (List.append
        (List.replicate 4 (none : Option Bool))
        (List.append
          ((selectedProjectionPaddedTailCleanupSelectedHitBits
            false L).map some)
          (none :: none ::
            List.replicate extraScratch (none : Option Bool)))))

def selectedProjectionPaddedTailCleanupAfterStageTailCells
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    List (Option Bool) :=
  if useAccept then
    selectedProjectionPaddedTailCleanupAcceptAfterStageTailCells
      L extraScratch
  else
    selectedProjectionPaddedTailCleanupRejectAfterStageTailCells
      L extraScratch

theorem selectedProjectionPaddedTailCleanupAcceptAfterStageTailCells_fieldSplit
    (L : DovetailLayout) (extraScratch : Nat) :
    exists fieldTail : Word Bool,
      selectedProjectionPaddedTailCleanupAcceptAfterStageTailCells
          L extraScratch =
        List.append ((false :: fieldTail).map some)
          (none ::
            List.append (List.replicate 5 (none : Option Bool))
              (List.replicate extraScratch (none : Option Bool))) := by
  let wordTail :=
    List.append
      (selectedProjectionPaddedTailCleanupUnselectedConfigBits true L)
      (selectedProjectionPaddedTailCleanupSelectedHitBits true L)
  rcases configurationFieldBits_cons_false L.acceptConfig wordTail with
    ⟨fieldTail, hfield⟩
  refine ⟨fieldTail, ?_⟩
  have hword :
      List.append
          (selectedProjectionPaddedTailCleanupSelectedConfigBits true L)
          wordTail =
        false :: fieldTail := by
    simpa [wordTail,
      selectedProjectionPaddedTailCleanupSelectedConfigBits]
      using
        (configurationFieldBits_append_nil
          L.acceptConfig wordTail).trans hfield
  rw [selectedProjectionPaddedTailCleanupAcceptAfterStageTailCells]
  rw [← hword]
  simp [wordTail, List.map_append, List.append_assoc]

theorem selectedProjectionPaddedTailCleanupRejectAfterStageTailCells_fieldSplit
    (L : DovetailLayout) (extraScratch : Nat) :
    exists fieldTail : Word Bool,
      selectedProjectionPaddedTailCleanupRejectAfterStageTailCells
          L extraScratch =
        List.append ((false :: fieldTail).map some)
          (List.append (List.replicate 4 (none : Option Bool))
            (List.append
              ((selectedProjectionPaddedTailCleanupSelectedHitBits
                false L).map some)
              (none :: none ::
                List.replicate extraScratch (none : Option Bool)))) := by
  let wordTail := selectedProjectionPaddedTailCleanupSelectedConfigBits false L
  rcases configurationFieldBits_cons_false L.acceptConfig wordTail with
    ⟨fieldTail, hfield⟩
  refine ⟨fieldTail, ?_⟩
  have hword :
      List.append
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits false L)
          wordTail =
        false :: fieldTail := by
    simpa [wordTail,
      selectedProjectionPaddedTailCleanupUnselectedConfigBits]
      using
        (configurationFieldBits_append_nil
          L.acceptConfig wordTail).trans hfield
  rw [selectedProjectionPaddedTailCleanupRejectAfterStageTailCells]
  rw [← hword]
  simp [wordTail, List.map_append, List.append_assoc]

theorem selectedProjectionPaddedTailCleanupAfterStageTailCells_fieldSplit
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    exists fieldTail : Word Bool,
    exists rightPadding : List (Option Bool),
      selectedProjectionPaddedTailCleanupAfterStageTailCells
          useAccept L extraScratch =
        List.append ((false :: fieldTail).map some) rightPadding := by
  cases useAccept
  · rcases
      selectedProjectionPaddedTailCleanupRejectAfterStageTailCells_fieldSplit
        L extraScratch with
      ⟨fieldTail, hfieldTail⟩
    exact
      ⟨fieldTail,
        List.append (List.replicate 4 (none : Option Bool))
          (List.append
            ((selectedProjectionPaddedTailCleanupSelectedHitBits
              false L).map some)
            (none :: none ::
              List.replicate extraScratch (none : Option Bool))),
        by
          simpa [
            selectedProjectionPaddedTailCleanupAfterStageTailCells]
            using hfieldTail⟩
  · rcases
      selectedProjectionPaddedTailCleanupAcceptAfterStageTailCells_fieldSplit
        L extraScratch with
      ⟨fieldTail, hfieldTail⟩
    exact
      ⟨fieldTail,
        none ::
          List.append (List.replicate 5 (none : Option Bool))
            (List.replicate extraScratch (none : Option Bool)),
        by
          simpa [
            selectedProjectionPaddedTailCleanupAfterStageTailCells]
            using hfieldTail⟩

def selectedProjectionPaddedTailCleanupAcceptPostCountTailCells
    (L : DovetailLayout) (extraScratch : Nat) : List (Option Bool) :=
  List.append
    ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
      L.stage).map some)
    (selectedProjectionPaddedTailCleanupAcceptAfterStageTailCells
      L extraScratch)

def selectedProjectionPaddedTailCleanupRejectPostCountTailCells
    (L : DovetailLayout) (extraScratch : Nat) : List (Option Bool) :=
  List.append
    ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
      L.stage).map some)
    (selectedProjectionPaddedTailCleanupRejectAfterStageTailCells
      L extraScratch)

def selectedProjectionPaddedTailCleanupPostCountTailCells
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    List (Option Bool) :=
  if useAccept then
    selectedProjectionPaddedTailCleanupAcceptPostCountTailCells L extraScratch
  else
    selectedProjectionPaddedTailCleanupRejectPostCountTailCells L extraScratch

def selectedProjectionPaddedTailCleanupEncodedHeaderCells :
    List (Option Bool) :=
  (encodeCodeSymbolAsInput MachineCodeSymbol.header).map some

def selectedProjectionPaddedTailCleanupEncodedLayoutLengthCells
    (L : DovetailLayout) : List (Option Bool) :=
  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
    (ParsedLayoutBits L).length).map some

def selectedProjectionPaddedTailCleanupEncodedScratchSkippedCells
    (useAccept : Bool) (L : DovetailLayout) : List (Option Bool) :=
  (cellsCodeBits
    ((selectedProjectionPaddedTailCleanupScratchSkippedBits
      useAccept L).map some)).map some

def selectedProjectionPaddedTailCleanupEncodedScratchCountCells
    (useAccept : Bool) (L : DovetailLayout) : List (Option Bool) :=
  (cellsCodeBits
    ((selectedProjectionPaddedTailCleanupScratchCountBits
      useAccept L).map some)).map some

def selectedProjectionPaddedTailCleanupEncodedCountWindowSourceCells
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    List (Option Bool) :=
  List.append
    selectedProjectionPaddedTailCleanupEncodedHeaderCells
    (List.append
      (selectedProjectionPaddedTailCleanupEncodedLayoutLengthCells L)
      (List.append
        (selectedProjectionPaddedTailCleanupEncodedScratchSkippedCells
          useAccept L)
        (List.append
          (selectedProjectionPaddedTailCleanupEncodedScratchCountCells
            useAccept L)
          (selectedProjectionPaddedTailCleanupPostCountTailCells
            useAccept L extraScratch))))

def selectedProjectionPaddedTailCleanupAfterOutputPrefixScanTape
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    Tape Bool :=
  (boolWordCanonicalHandoffConfigWithBaseAndRight
    (ParsedLayoutBits L)
    (postPaddingOutputPrefixHeaderBase [none])
    (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
      L.stage)
    (selectedProjectionPaddedTailCleanupAfterStageTailCells
      useAccept L extraScratch)).tape

theorem selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch_afterStageTail
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
        useAccept L extraScratch =
      tapeAtCells [none]
        (List.append
          ((encodeCodeSymbolAsInput MachineCodeSymbol.header).map some)
          (List.append
            ((encodeCodeWordAsInput
              (encodeBoolWordAppend (ParsedLayoutBits L) [])).map some)
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                L.stage).map some)
              (selectedProjectionPaddedTailCleanupAfterStageTailCells
                useAccept L extraScratch)))) := by
  cases useAccept
  · simp [
      selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch,
      selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithExtraScratch,
      selectedProjectionPaddedTailCleanupAfterStageTailCells,
      selectedProjectionPaddedTailCleanupRejectAfterStageTailCells,
      selectedProjectionPaddedTailCleanupPrefixBits,
      SelectedProjectionTailProjector.outputPrefixBits,
      List.map_append, List.append_assoc]
  · simp [
      selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch,
      selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithExtraScratch,
      selectedProjectionPaddedTailCleanupAfterStageTailCells,
      selectedProjectionPaddedTailCleanupAcceptAfterStageTailCells,
      selectedProjectionPaddedTailCleanupPostPaddingSourceBits_true_eq_selected_unselected,
      selectedProjectionPaddedTailCleanupPrefixBits,
      SelectedProjectionTailProjector.outputPrefixBits,
      List.map_append, List.append_assoc]

theorem selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithExtraScratch_countSplit
    (L : DovetailLayout) (extraScratch : Nat) :
    selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithExtraScratch
        L extraScratch =
      tapeAtCells [none]
        (selectedProjectionPaddedTailCleanupEncodedCountWindowSourceCells
          true L extraScratch) := by
  simp [
    selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithExtraScratch,
    selectedProjectionPaddedTailCleanupEncodedCountWindowSourceCells,
    selectedProjectionPaddedTailCleanupEncodedHeaderCells,
    selectedProjectionPaddedTailCleanupEncodedLayoutLengthCells,
    selectedProjectionPaddedTailCleanupEncodedScratchSkippedCells,
    selectedProjectionPaddedTailCleanupEncodedScratchCountCells,
    selectedProjectionPaddedTailCleanupPostPaddingSourceBits_true_eq_selected_unselected,
    selectedProjectionPaddedTailCleanupPrefixBits,
    List.map_append, List.append_assoc]
  rw [selectedProjectionPaddedTailCleanupOutputPrefixCells_split true L]
  simp [selectedProjectionPaddedTailCleanupPostCountTailCells,
    selectedProjectionPaddedTailCleanupAcceptPostCountTailCells,
    selectedProjectionPaddedTailCleanupAcceptAfterStageTailCells,
    List.append_assoc]

theorem selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithExtraScratch_countSplit
    (L : DovetailLayout) (extraScratch : Nat) :
    selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithExtraScratch
        L extraScratch =
      tapeAtCells [none]
        (selectedProjectionPaddedTailCleanupEncodedCountWindowSourceCells
          false L extraScratch) := by
  simp [
    selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithExtraScratch,
    selectedProjectionPaddedTailCleanupEncodedCountWindowSourceCells,
    selectedProjectionPaddedTailCleanupEncodedHeaderCells,
    selectedProjectionPaddedTailCleanupEncodedLayoutLengthCells,
    selectedProjectionPaddedTailCleanupEncodedScratchSkippedCells,
    selectedProjectionPaddedTailCleanupEncodedScratchCountCells,
    selectedProjectionPaddedTailCleanupPrefixBits,
    List.map_append, List.append_assoc]
  rw [selectedProjectionPaddedTailCleanupOutputPrefixCells_split false L]
  simp [selectedProjectionPaddedTailCleanupPostCountTailCells,
    selectedProjectionPaddedTailCleanupRejectPostCountTailCells,
    selectedProjectionPaddedTailCleanupRejectAfterStageTailCells,
    List.append_assoc]

theorem selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch_countSplit
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
        useAccept L extraScratch =
      tapeAtCells [none]
        (selectedProjectionPaddedTailCleanupEncodedCountWindowSourceCells
          useAccept L extraScratch) := by
  cases useAccept
  · exact
      selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithExtraScratch_countSplit
        L extraScratch
  · exact
      selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithExtraScratch_countSplit
        L extraScratch

theorem selectedProjectionPaddedTailCleanupOutputPrefixScanner_haltsFrom_baseSourceTapeWithExtraScratch
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    postPaddingOutputPrefixScannerDescription.HaltsFromTape
      (selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
        useAccept L extraScratch)
      (selectedProjectionPaddedTailCleanupAfterOutputPrefixScanTape
        useAccept L extraScratch) := by
  rcases stageNatBits_cons_false L.stage with
    ⟨stageTail, hstage⟩
  cases useAccept
  · simpa [
      selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch,
      selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithExtraScratch,
      selectedProjectionPaddedTailCleanupAfterOutputPrefixScanTape,
      selectedProjectionPaddedTailCleanupAfterStageTailCells,
      selectedProjectionPaddedTailCleanupRejectAfterStageTailCells,
      selectedProjectionPaddedTailCleanupPrefixBits,
      selectedProjectionPaddedTailCleanupPostPaddingSourceBits_false_eq_unselected_selected,
      SelectedProjectionTailProjector.outputPrefixBits,
      hstage, List.map_append, List.append_assoc] using
        postPaddingOutputPrefixScannerDescription_haltsFrom_withRight
          (ParsedLayoutBits L) stageTail [none]
          (selectedProjectionPaddedTailCleanupRejectAfterStageTailCells
            L extraScratch)
  · simpa [
      selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch,
      selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithExtraScratch,
      selectedProjectionPaddedTailCleanupAfterOutputPrefixScanTape,
      selectedProjectionPaddedTailCleanupAfterStageTailCells,
      selectedProjectionPaddedTailCleanupAcceptAfterStageTailCells,
      selectedProjectionPaddedTailCleanupPrefixBits,
      selectedProjectionPaddedTailCleanupPostPaddingSourceBits_true_eq_selected_unselected,
      SelectedProjectionTailProjector.outputPrefixBits,
      hstage, List.map_append, List.append_assoc] using
        postPaddingOutputPrefixScannerDescription_haltsFrom_withRight
          (ParsedLayoutBits L) stageTail [none]
          (selectedProjectionPaddedTailCleanupAcceptAfterStageTailCells
            L extraScratch)

theorem selectedProjectionPaddedTailCleanupAfterOutputPrefixScanTape_move_right
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    Tape.move Direction.right
        (selectedProjectionPaddedTailCleanupAfterOutputPrefixScanTape
          useAccept L extraScratch) =
      tapeAtCells
        (cellListCanonicalRestoredLeftWithBase
          ((ParsedLayoutBits L).map some)
          (postPaddingOutputPrefixHeaderBase [none]))
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage).map some)
          (selectedProjectionPaddedTailCleanupAfterStageTailCells
            useAccept L extraScratch)) := by
  rcases stageNatBits_cons_false L.stage with
    ⟨stageTail, hstage⟩
  cases useAccept
  · simpa [
      selectedProjectionPaddedTailCleanupAfterOutputPrefixScanTape,
      selectedProjectionPaddedTailCleanupAfterStageTailCells,
      boolWordCanonicalHandoffConfigWithBaseAndRight,
      hstage,
      List.append_assoc] using
        cellListCanonicalHandoffConfigWithBaseAndRight_move_right
          ((ParsedLayoutBits L).map some)
          (postPaddingOutputPrefixHeaderBase [none])
          false stageTail
          (selectedProjectionPaddedTailCleanupRejectAfterStageTailCells
            L extraScratch)
  · simpa [
      selectedProjectionPaddedTailCleanupAfterOutputPrefixScanTape,
      selectedProjectionPaddedTailCleanupAfterStageTailCells,
      boolWordCanonicalHandoffConfigWithBaseAndRight,
      hstage,
      List.append_assoc] using
        cellListCanonicalHandoffConfigWithBaseAndRight_move_right
          ((ParsedLayoutBits L).map some)
          (postPaddingOutputPrefixHeaderBase [none])
          false stageTail
          (selectedProjectionPaddedTailCleanupAcceptAfterStageTailCells
            L extraScratch)

theorem selectedProjectionPaddedTailCleanupOutputPrefixStageScanner_haltsFrom_baseSourceTapeWithExtraScratch
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    exists fieldTail : Word Bool,
    exists rightPadding : List (Option Bool),
      selectedProjectionPaddedTailCleanupAfterStageTailCells
          useAccept L extraScratch =
        List.append ((false :: fieldTail).map some) rightPadding ∧
      postPaddingOutputPrefixStageScannerDescription.HaltsFromTape
        (selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
          useAccept L extraScratch)
        (postPaddingOutputPrefixStageScannerTargetTapeWithRight
          (ParsedLayoutBits L) L.stage [none] fieldTail rightPadding) ∧
      Tape.move Direction.right
          (postPaddingOutputPrefixStageScannerTargetTapeWithRight
            (ParsedLayoutBits L) L.stage [none] fieldTail rightPadding) =
        tapeAtCells
          (postPaddingOutputPrefixAfterStageBase
            (ParsedLayoutBits L) L.stage [none])
          (selectedProjectionPaddedTailCleanupAfterStageTailCells
            useAccept L extraScratch) := by
  rcases
      selectedProjectionPaddedTailCleanupAfterStageTailCells_fieldSplit
        useAccept L extraScratch with
    ⟨fieldTail, rightPadding, htail⟩
  refine ⟨fieldTail, rightPadding, htail, ?_, ?_⟩
  · rw [
      selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch_afterStageTail,
      htail]
    simpa [List.map_append, List.append_assoc] using
      postPaddingOutputPrefixStageScannerDescription_haltsFrom_raw_withRight
        (ParsedLayoutBits L) L.stage [none] fieldTail rightPadding
  · rw [
      postPaddingOutputPrefixStageScannerTarget_move_right_eq_configSource_withRight,
      ← htail]
    simp [DovetailInitialLayoutInitializer.tapeAtCells, tapeAtCells]
    rfl

theorem selectedProjectionPaddedTailCleanupOutputPrefixStageScanner_haltsFrom_baseSourceTapeWithExtraScratch_prefixBase
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    exists fieldTail : Word Bool,
    exists rightPadding : List (Option Bool),
      selectedProjectionPaddedTailCleanupAfterStageTailCells
          useAccept L extraScratch =
        List.append ((false :: fieldTail).map some) rightPadding ∧
      postPaddingOutputPrefixStageScannerDescription.HaltsFromTape
        (selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
          useAccept L extraScratch)
        (postPaddingOutputPrefixStageScannerTargetTapeWithRight
          (ParsedLayoutBits L) L.stage [none] fieldTail rightPadding) ∧
      Tape.move Direction.right
          (postPaddingOutputPrefixStageScannerTargetTapeWithRight
            (ParsedLayoutBits L) L.stage [none] fieldTail rightPadding) =
        tapeAtCells
          (List.append
            ((selectedProjectionPaddedTailCleanupPrefixBits L).reverse.map
              some)
            [none])
          (selectedProjectionPaddedTailCleanupAfterStageTailCells
            useAccept L extraScratch) := by
  rcases
      selectedProjectionPaddedTailCleanupOutputPrefixStageScanner_haltsFrom_baseSourceTapeWithExtraScratch
        useAccept L extraScratch with
    ⟨fieldTail, rightPadding, htail, hrun, hmove⟩
  refine ⟨fieldTail, rightPadding, htail, hrun, ?_⟩
  rw [hmove]
  rw [postPaddingOutputPrefixAfterStageBase_eq_prefixBits_reverse]

theorem selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithExtraScratch_zero
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithExtraScratch
        L 0 =
      selectedProjectionPaddedTailCleanupAcceptBaseSourceTape L := by
  simp [selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithExtraScratch,
    selectedProjectionPaddedTailCleanupAcceptBaseSourceTape]

theorem selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithExtraScratch_zero
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithExtraScratch
        L 0 =
      selectedProjectionPaddedTailCleanupRejectBaseSourceTape L := by
  simp [selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithExtraScratch,
    selectedProjectionPaddedTailCleanupRejectBaseSourceTape]

theorem selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch_zero
    (useAccept : Bool) (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
        useAccept L 0 =
      selectedProjectionPaddedTailCleanupBaseSourceTape useAccept L := by
  cases useAccept
  · exact
      selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithExtraScratch_zero
        L
  · exact
      selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithExtraScratch_zero
        L

theorem selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithLayoutExtraScratch
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithExtraScratch
        L
        (selectedProjectionPaddedTailCleanupSentinelExtraScratch true L) =
      selectedProjectionPaddedTailCleanupAcceptLayoutScratchSourceTape L := by
  rfl

theorem selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithLayoutExtraScratch
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithExtraScratch
        L
        (selectedProjectionPaddedTailCleanupSentinelExtraScratch false L) =
      selectedProjectionPaddedTailCleanupRejectLayoutScratchSourceTape L := by
  rfl

theorem selectedProjectionPaddedTailCleanupBaseSourceTapeWithLayoutExtraScratch
    (useAccept : Bool) (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
        useAccept L
        (selectedProjectionPaddedTailCleanupSentinelExtraScratch
          useAccept L) =
      selectedProjectionPaddedTailCleanupLayoutScratchSourceTape
        useAccept L := by
  cases useAccept
  · exact
      selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithLayoutExtraScratch
        L
  · exact
      selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithLayoutExtraScratch
        L

theorem selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithExtraScratch_normalizedOutput
    (L : DovetailLayout) (extraScratch : Nat) :
    Tape.normalizedOutput
        (selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithExtraScratch
          L extraScratch) =
      selectedProjectionPaddedTailCleanupPostPaddingSourceBits true L := by
  simp [
    selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithExtraScratch,
    tapeAtCells_normalizedOutput, Function.comp_def]

theorem selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithExtraScratch_normalizedOutput
    (L : DovetailLayout) (extraScratch : Nat) :
    Tape.normalizedOutput
        (selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithExtraScratch
          L extraScratch) =
      selectedProjectionPaddedTailCleanupPostPaddingSourceBits false L := by
  simp [
    selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithExtraScratch,
    selectedProjectionPaddedTailCleanupPostPaddingSourceBits,
    Function.comp_def, tapeAtCells_normalizedOutput, List.append_assoc]

theorem selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch_normalizedOutput
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    Tape.normalizedOutput
        (selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
          useAccept L extraScratch) =
      selectedProjectionPaddedTailCleanupPostPaddingSourceBits
        useAccept L := by
  cases useAccept
  · exact
      selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithExtraScratch_normalizedOutput
        L extraScratch
  · exact
      selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithExtraScratch_normalizedOutput
        L extraScratch

theorem selectedProjectionPaddedTailCleanupBaseSourceTape_normalizedOutput
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedProjectionPaddedTailCleanupBaseSourceTape useAccept L) =
      selectedProjectionPaddedTailCleanupPostPaddingSourceBits
        useAccept L := by
  simpa [
    selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch_zero]
    using
      selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch_normalizedOutput
        useAccept L 0

theorem selectedProjectionPaddedTailCleanupLayoutScratchSourceTape_normalizedOutput
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedProjectionPaddedTailCleanupLayoutScratchSourceTape
          useAccept L) =
      selectedProjectionPaddedTailCleanupPostPaddingSourceBits
        useAccept L := by
  simpa [
    selectedProjectionPaddedTailCleanupBaseSourceTapeWithLayoutExtraScratch]
    using
      selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch_normalizedOutput
        useAccept L
        (selectedProjectionPaddedTailCleanupSentinelExtraScratch
          useAccept L)

theorem selectedProjectionPaddedTailCleanupLayoutScratchSourceTape_move_left_move_right
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (selectedProjectionPaddedTailCleanupLayoutScratchSourceTape
            useAccept L)) =
      selectedProjectionPaddedTailCleanupLayoutScratchSourceTape
        useAccept L := by
  cases useAccept
  · simp [
      selectedProjectionPaddedTailCleanupLayoutScratchSourceTape,
      selectedProjectionPaddedTailCleanupRejectLayoutScratchSourceTape,
      selectedProjectionPaddedTailCleanupPrefixBits,
      SelectedProjectionTailProjector.outputPrefixBits,
      encodeCodeSymbolAsInput, tapeAtCells, Tape.move,
      Tape.moveLeft, Tape.moveRight, List.append_assoc]
  · simp [
      selectedProjectionPaddedTailCleanupLayoutScratchSourceTape,
      selectedProjectionPaddedTailCleanupAcceptLayoutScratchSourceTape,
      selectedProjectionPaddedTailCleanupPostPaddingSourceBits,
      selectedProjectionPaddedTailCleanupPrefixBits,
      SelectedProjectionTailProjector.outputPrefixBits,
      encodeCodeSymbolAsInput, tapeAtCells, Tape.move,
      Tape.moveLeft, Tape.moveRight, List.map_append,
      List.append_assoc]

theorem selectedProjectionPaddedTailCleanupBaseSourceTape_move_left_move_right
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (selectedProjectionPaddedTailCleanupBaseSourceTape
            useAccept L)) =
      selectedProjectionPaddedTailCleanupBaseSourceTape
        useAccept L := by
  cases useAccept
  · simp [
      selectedProjectionPaddedTailCleanupBaseSourceTape,
      selectedProjectionPaddedTailCleanupRejectBaseSourceTape,
      selectedProjectionPaddedTailCleanupPrefixBits,
      SelectedProjectionTailProjector.outputPrefixBits,
      encodeCodeSymbolAsInput, tapeAtCells, Tape.move,
      Tape.moveLeft, Tape.moveRight, List.append_assoc]
  · simp [
      selectedProjectionPaddedTailCleanupBaseSourceTape,
      selectedProjectionPaddedTailCleanupAcceptBaseSourceTape,
      selectedProjectionPaddedTailCleanupPostPaddingSourceBits,
      selectedProjectionPaddedTailCleanupPrefixBits,
      SelectedProjectionTailProjector.outputPrefixBits,
      encodeCodeSymbolAsInput, tapeAtCells, Tape.move,
      Tape.moveLeft, Tape.moveRight, List.map_append,
      List.append_assoc]

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
