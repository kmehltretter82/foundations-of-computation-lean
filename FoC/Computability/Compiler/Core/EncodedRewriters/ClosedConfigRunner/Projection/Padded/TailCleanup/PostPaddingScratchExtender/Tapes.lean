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

theorem selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithExtraScratch_countSplit
    (L : DovetailLayout) (extraScratch : Nat) :
    selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithExtraScratch
        L extraScratch =
      tapeAtCells [none]
        (List.append
          ((encodeCodeSymbolAsInput MachineCodeSymbol.header).map some)
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              (ParsedLayoutBits L).length).map some)
            (List.append
              ((cellsCodeBits
                ((selectedProjectionPaddedTailCleanupScratchSkippedBits
                  true L).map some)).map some)
              (List.append
                ((cellsCodeBits
                  ((selectedProjectionPaddedTailCleanupScratchCountBits
                    true L).map some)).map some)
                (selectedProjectionPaddedTailCleanupAcceptPostCountTailCells
                  L extraScratch))))) := by
  simp [
    selectedProjectionPaddedTailCleanupAcceptBaseSourceTapeWithExtraScratch,
    selectedProjectionPaddedTailCleanupPostPaddingSourceBits_true_eq_selected_unselected,
    selectedProjectionPaddedTailCleanupPrefixBits,
    selectedProjectionPaddedTailCleanupAcceptPostCountTailCells,
    List.map_append, List.append_assoc]
  rw [selectedProjectionPaddedTailCleanupOutputPrefixCells_split true L]
  simp [selectedProjectionPaddedTailCleanupAcceptAfterStageTailCells,
    List.append_assoc]

theorem selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithExtraScratch_countSplit
    (L : DovetailLayout) (extraScratch : Nat) :
    selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithExtraScratch
        L extraScratch =
      tapeAtCells [none]
        (List.append
          ((encodeCodeSymbolAsInput MachineCodeSymbol.header).map some)
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              (ParsedLayoutBits L).length).map some)
            (List.append
              ((cellsCodeBits
                ((selectedProjectionPaddedTailCleanupScratchSkippedBits
                  false L).map some)).map some)
              (List.append
                ((cellsCodeBits
                  ((selectedProjectionPaddedTailCleanupScratchCountBits
                    false L).map some)).map some)
                (selectedProjectionPaddedTailCleanupRejectPostCountTailCells
                  L extraScratch))))) := by
  simp [
    selectedProjectionPaddedTailCleanupRejectBaseSourceTapeWithExtraScratch,
    selectedProjectionPaddedTailCleanupPrefixBits,
    selectedProjectionPaddedTailCleanupRejectPostCountTailCells,
    List.map_append, List.append_assoc]
  rw [selectedProjectionPaddedTailCleanupOutputPrefixCells_split false L]
  simp [selectedProjectionPaddedTailCleanupRejectAfterStageTailCells,
    List.append_assoc]

theorem selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch_countSplit
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
        useAccept L extraScratch =
      tapeAtCells [none]
        (List.append
          ((encodeCodeSymbolAsInput MachineCodeSymbol.header).map some)
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              (ParsedLayoutBits L).length).map some)
            (List.append
              ((cellsCodeBits
                ((selectedProjectionPaddedTailCleanupScratchSkippedBits
                  useAccept L).map some)).map some)
              (List.append
                ((cellsCodeBits
                  ((selectedProjectionPaddedTailCleanupScratchCountBits
                    useAccept L).map some)).map some)
                (selectedProjectionPaddedTailCleanupPostCountTailCells
                  useAccept L extraScratch))))) := by
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
