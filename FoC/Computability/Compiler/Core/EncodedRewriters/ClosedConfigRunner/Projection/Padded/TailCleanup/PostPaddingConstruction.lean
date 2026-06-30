import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.PostPaddingFramework
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.PostPaddingPrefixScanner

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncodedRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

open CanonicalLayouts.DovetailLayoutScanner

def selectedProjectionPaddedTailCleanupAcceptSentinelTargetTape
    (L : DovetailLayout) : Tape Bool :=
  leadingBlankLeftShiftTargetTapeWithPadding []
    (selectedProjectionPaddedTailCleanupTargetBits true L)
    (none :: sentinelGapCompactorFinalPadding
      (selectedProjectionPaddedTailCleanupUnselectedConfigBits
        true L).length.pred
      5 [])

def selectedProjectionPaddedTailCleanupRejectSentinelTargetTape
    (L : DovetailLayout) : Tape Bool :=
  leadingBlankLeftShiftTargetTapeWithPadding []
    (selectedProjectionPaddedTailCleanupTargetBits false L)
    (none :: sentinelGapCompactorFinalPadding
      (selectedProjectionPaddedTailCleanupUnselectedConfigBits
        false L).length.pred
      2 (List.replicate 3 (none : Option Bool)))

def selectedProjectionPaddedTailCleanupAcceptSentinelTargetTapeWithRightPadding
    (L : DovetailLayout)
    (rightPadding : List (Option Bool)) : Tape Bool :=
  leadingBlankLeftShiftTargetTapeWithPadding []
    (selectedProjectionPaddedTailCleanupTargetBits true L)
    (none :: sentinelGapCompactorFinalPadding
      (selectedProjectionPaddedTailCleanupUnselectedConfigBits
        true L).length.pred
      5 rightPadding)

def selectedProjectionPaddedTailCleanupRejectSentinelTargetTapeWithRightPadding
    (L : DovetailLayout)
    (rightPadding : List (Option Bool)) : Tape Bool :=
  leadingBlankLeftShiftTargetTapeWithPadding []
    (selectedProjectionPaddedTailCleanupTargetBits false L)
    (none :: sentinelGapCompactorFinalPadding
      (selectedProjectionPaddedTailCleanupUnselectedConfigBits
        false L).length.pred
      2 (List.append (List.replicate 3 (none : Option Bool))
        rightPadding))

theorem selectedProjectionPaddedTailCleanupAcceptSentinelTargetTape_eq_withRightPadding_nil
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupAcceptSentinelTargetTape L =
      selectedProjectionPaddedTailCleanupAcceptSentinelTargetTapeWithRightPadding
        L [] := by
  rfl

theorem selectedProjectionPaddedTailCleanupRejectSentinelTargetTape_eq_withRightPadding_nil
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupRejectSentinelTargetTape L =
      selectedProjectionPaddedTailCleanupRejectSentinelTargetTapeWithRightPadding
        L [] := by
  simp [selectedProjectionPaddedTailCleanupRejectSentinelTargetTape,
    selectedProjectionPaddedTailCleanupRejectSentinelTargetTapeWithRightPadding]

def selectedProjectionPaddedTailCleanupSentinelBaseScratch
    (useAccept : Bool) (L : DovetailLayout) : Nat :=
  (selectedProjectionPaddedTailCleanupUnselectedConfigBits
    useAccept L).length.pred + 8

def selectedProjectionPaddedTailCleanupSentinelExtraScratch
    (useAccept : Bool) (L : DovetailLayout) : Nat :=
  (ParsedLayoutBits L).length -
    selectedProjectionPaddedTailCleanupSentinelBaseScratch useAccept L

theorem selectedProjectionPaddedTailCleanupSentinelBaseScratch_add_extraScratch
    (useAccept : Bool) (L : DovetailLayout)
    (hle :
      selectedProjectionPaddedTailCleanupSentinelBaseScratch useAccept L <=
        (ParsedLayoutBits L).length) :
    selectedProjectionPaddedTailCleanupSentinelBaseScratch useAccept L +
        selectedProjectionPaddedTailCleanupSentinelExtraScratch useAccept L =
      (ParsedLayoutBits L).length := by
  rw [selectedProjectionPaddedTailCleanupSentinelExtraScratch]
  omega

theorem selectedProjectionPaddedTailCleanupUnselectedConfigBits_length_pos
    (useAccept : Bool) (L : DovetailLayout) :
    0 <
      (selectedProjectionPaddedTailCleanupUnselectedConfigBits
        useAccept L).length := by
  cases useAccept
  · rcases
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_cons_false
        L.acceptConfig [] with
      ⟨tail, htail⟩
    simp [selectedProjectionPaddedTailCleanupUnselectedConfigBits, htail]
  · rcases
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_cons_false
        L.rejectConfig [] with
      ⟨tail, htail⟩
    simp [selectedProjectionPaddedTailCleanupUnselectedConfigBits, htail]

theorem selectedProjectionPaddedTailCleanupSentinelBaseScratch_le_parsed_true
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupSentinelBaseScratch true L <=
      (ParsedLayoutBits L).length := by
  have hsource :=
    SelectedProjectionTailProjector.sourceFieldBits_length_le_parsedLayoutBits
      L
  have hbools :
      8 <=
        (boolFieldBits L.acceptHit []).length +
          (boolFieldBits L.rejectHit []).length := by
    cases L.acceptHit <;> cases L.rejectHit <;>
      simp [boolFieldBits, cellFieldBits, cellCodeBits,
        encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput]
  have hsplit :
      (SelectedProjectionTailProjector.sourceFieldBits L).length =
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          L.stage).length +
          (configurationFieldBits L.acceptConfig []).length +
          (configurationFieldBits L.rejectConfig []).length +
          (boolFieldBits L.acceptHit []).length +
          (boolFieldBits L.rejectHit []).length := by
    rw [SelectedProjectionTailProjector.sourceFieldBits]
    rw [←
      configurationFieldBits_append_nil L.acceptConfig
        (configurationFieldBits L.rejectConfig
          (boolFieldBits L.acceptHit
            (boolFieldBits L.rejectHit [])))]
    rw [←
      configurationFieldBits_append_nil L.rejectConfig
        (boolFieldBits L.acceptHit
          (boolFieldBits L.rejectHit []))]
    rw [show
        boolFieldBits L.acceptHit (boolFieldBits L.rejectHit []) =
          List.append (boolFieldBits L.acceptHit [])
            (boolFieldBits L.rejectHit []) by
      simpa [boolFieldBits] using
        (cellFieldBits_append_nil (some L.acceptHit)
          (boolFieldBits L.rejectHit [])).symm]
    simp [List.length_append, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]
  apply Nat.le_trans ?_ hsource
  rw [hsplit]
  simp [selectedProjectionPaddedTailCleanupSentinelBaseScratch,
    selectedProjectionPaddedTailCleanupUnselectedConfigBits]
  omega

theorem selectedProjectionPaddedTailCleanupSentinelBaseScratch_le_parsed_false
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupSentinelBaseScratch false L <=
      (ParsedLayoutBits L).length := by
  have hsource :=
    SelectedProjectionTailProjector.sourceFieldBits_length_le_parsedLayoutBits
      L
  have hbools :
      8 <=
        (boolFieldBits L.acceptHit []).length +
          (boolFieldBits L.rejectHit []).length := by
    cases L.acceptHit <;> cases L.rejectHit <;>
      simp [boolFieldBits, cellFieldBits, cellCodeBits,
        encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput]
  have hsplit :
      (SelectedProjectionTailProjector.sourceFieldBits L).length =
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          L.stage).length +
          (configurationFieldBits L.acceptConfig []).length +
          (configurationFieldBits L.rejectConfig []).length +
          (boolFieldBits L.acceptHit []).length +
          (boolFieldBits L.rejectHit []).length := by
    rw [SelectedProjectionTailProjector.sourceFieldBits]
    rw [←
      configurationFieldBits_append_nil L.acceptConfig
        (configurationFieldBits L.rejectConfig
          (boolFieldBits L.acceptHit
            (boolFieldBits L.rejectHit [])))]
    rw [←
      configurationFieldBits_append_nil L.rejectConfig
        (boolFieldBits L.acceptHit
          (boolFieldBits L.rejectHit []))]
    rw [show
        boolFieldBits L.acceptHit (boolFieldBits L.rejectHit []) =
          List.append (boolFieldBits L.acceptHit [])
            (boolFieldBits L.rejectHit []) by
      simpa [boolFieldBits] using
        (cellFieldBits_append_nil (some L.acceptHit)
          (boolFieldBits L.rejectHit [])).symm]
    simp [List.length_append, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]
  apply Nat.le_trans ?_ hsource
  rw [hsplit]
  simp [selectedProjectionPaddedTailCleanupSentinelBaseScratch,
    selectedProjectionPaddedTailCleanupUnselectedConfigBits]
  omega

theorem selectedProjectionPaddedTailCleanupAcceptRightEndScratchWidth_eq_parsed
    (L : DovetailLayout) :
    1 +
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits
            true L).length + 6 +
        selectedProjectionPaddedTailCleanupSentinelExtraScratch true L =
      (ParsedLayoutBits L).length := by
  have hbase :=
    selectedProjectionPaddedTailCleanupSentinelBaseScratch_add_extraScratch
      true L
      (selectedProjectionPaddedTailCleanupSentinelBaseScratch_le_parsed_true
        L)
  have hpos :=
    selectedProjectionPaddedTailCleanupUnselectedConfigBits_length_pos
      true L
  simp [selectedProjectionPaddedTailCleanupSentinelBaseScratch] at hbase
  omega

theorem selectedProjectionPaddedTailCleanupRejectFixedGapScratchWidth_eq_parsed
    (L : DovetailLayout) :
    1 +
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits
            false L).length + 6 +
        selectedProjectionPaddedTailCleanupSentinelExtraScratch false L =
      (ParsedLayoutBits L).length := by
  have hbase :=
    selectedProjectionPaddedTailCleanupSentinelBaseScratch_add_extraScratch
      false L
      (selectedProjectionPaddedTailCleanupSentinelBaseScratch_le_parsed_false
        L)
  have hpos :=
    selectedProjectionPaddedTailCleanupUnselectedConfigBits_length_pos
      false L
  simp [selectedProjectionPaddedTailCleanupSentinelBaseScratch] at hbase
  omega

theorem selectedProjectionPaddedTailCleanupDeletedAcceptRightEnd_to_acceptSentinelTarget
    (L : DovetailLayout) :
    sentinelRightEndGapCompactorDescription.HaltsFromTape
      (rightEndCompactionSourceTape
        (selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells L))
      (selectedProjectionPaddedTailCleanupAcceptSentinelTargetTape L) := by
  simpa [selectedProjectionPaddedTailCleanupAcceptSentinelTargetTape] using
    selectedProjectionPaddedTailCleanupDeletedAcceptRightEnd_sentinelCompactor_haltsFrom
      L

theorem selectedProjectionPaddedTailCleanupDeletedAcceptRightEnd_to_acceptSentinelTargetWithRightPadding
    (L : DovetailLayout)
    (rightPadding : List (Option Bool)) :
    sentinelRightEndGapCompactorDescription.HaltsFromTape
      (rightEndCompactionSourceTapeWithRightPadding
        (selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells L)
        rightPadding)
      (selectedProjectionPaddedTailCleanupAcceptSentinelTargetTapeWithRightPadding
        L rightPadding) := by
  simpa [
    selectedProjectionPaddedTailCleanupAcceptSentinelTargetTapeWithRightPadding]
    using
      selectedProjectionPaddedTailCleanupDeletedAcceptRightEnd_sentinelCompactor_haltsFrom_withRightPadding
        L rightPadding

theorem selectedProjectionPaddedTailCleanupDeletedRejectFixedGapClosed_to_rejectSentinelTarget
    (L : DovetailLayout) :
    sentinelRightEndGapCompactorDescription.HaltsFromTape
      (rightEndCompactionSourceTapeWithRightPadding
        (selectedProjectionPaddedTailCleanupDeletedRejectFixedGapClosedLeftCells
          L)
        (List.replicate 3 (none : Option Bool)))
      (selectedProjectionPaddedTailCleanupRejectSentinelTargetTape L) := by
  simpa [selectedProjectionPaddedTailCleanupRejectSentinelTargetTape] using
    selectedProjectionPaddedTailCleanupDeletedRejectFixedGapClosed_sentinelCompactor_haltsFrom
      L

theorem selectedProjectionPaddedTailCleanupAcceptSentinelTargetTape_normalizedOutput
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedProjectionPaddedTailCleanupAcceptSentinelTargetTape L) =
      selectedProjectionPaddedTailCleanupTargetBits true L := by
  rw [selectedProjectionPaddedTailCleanupAcceptSentinelTargetTape,
    leadingBlankLeftShiftTargetTapeWithPadding_normalizedOutput]
  simp [sentinelGapCompactorFinalPadding_eq_replicate_append]

theorem selectedProjectionPaddedTailCleanupRejectSentinelTargetTape_normalizedOutput
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedProjectionPaddedTailCleanupRejectSentinelTargetTape L) =
      selectedProjectionPaddedTailCleanupTargetBits false L := by
  rw [selectedProjectionPaddedTailCleanupRejectSentinelTargetTape,
    leadingBlankLeftShiftTargetTapeWithPadding_normalizedOutput]
  simp [sentinelGapCompactorFinalPadding_eq_replicate_append,
    List.filterMap_append]

theorem selectedProjectionPaddedTailCleanupAcceptSentinelTargetTape_cells
    (L : DovetailLayout) :
    Tape.cells
        (selectedProjectionPaddedTailCleanupAcceptSentinelTargetTape L) =
      rightScratchOutputCells
        (selectedProjectionPaddedTailCleanupTargetBits true L)
        ((selectedProjectionPaddedTailCleanupUnselectedConfigBits
          true L).length.pred + 8) := by
  rw [selectedProjectionPaddedTailCleanupAcceptSentinelTargetTape,
    leadingBlankLeftShiftTargetTapeWithPadding_cells]
  simp [rightScratchOutputCells, leadingBlankLeftShiftTargetCellsWithPadding,
    leadingBlankLeftShiftTargetVisiblePadding]
  have hpad :
      sentinelGapCompactorFinalPadding
          (List.length
              (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                true L) -
            1)
          5 [] =
        List.replicate
          (5 +
            (List.length
                (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                  true L) -
              1))
          (none : Option Bool) := by
    simpa using
      sentinelGapCompactorFinalPadding_replicate
        (List.length
            (selectedProjectionPaddedTailCleanupUnselectedConfigBits
              true L) -
          1)
        4 0
  rw [hpad]
  rw [show
      (List.length
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits
            true L) -
        1) + 8 =
        Nat.succ
          (Nat.succ
            (Nat.succ
              (5 +
                (List.length
                    (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                      true L) -
                  1)))) by
    omega]
  simp [List.replicate_succ]

theorem selectedProjectionPaddedTailCleanupAcceptSentinelTargetTapeWithExtraScratch_cells
    (L : DovetailLayout)
    (extraScratch : Nat) :
    Tape.cells
        (selectedProjectionPaddedTailCleanupAcceptSentinelTargetTapeWithRightPadding
          L (List.replicate extraScratch (none : Option Bool))) =
      rightScratchOutputCells
        (selectedProjectionPaddedTailCleanupTargetBits true L)
        ((selectedProjectionPaddedTailCleanupUnselectedConfigBits
          true L).length.pred + 8 + extraScratch) := by
  rw [
    selectedProjectionPaddedTailCleanupAcceptSentinelTargetTapeWithRightPadding,
    leadingBlankLeftShiftTargetTapeWithPadding_cells]
  simp [rightScratchOutputCells, leadingBlankLeftShiftTargetCellsWithPadding,
    leadingBlankLeftShiftTargetVisiblePadding]
  have hpad :
      sentinelGapCompactorFinalPadding
          (List.length
              (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                true L) -
            1)
          5 (List.replicate extraScratch (none : Option Bool)) =
        List.replicate
          (5 +
            (List.length
                (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                  true L) -
              1) +
            extraScratch)
          (none : Option Bool) := by
    simpa using
      sentinelGapCompactorFinalPadding_replicate
        (List.length
            (selectedProjectionPaddedTailCleanupUnselectedConfigBits
              true L) -
          1)
        4 extraScratch
  rw [hpad]
  rw [show
      (List.length
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits
            true L) -
        1) + 8 + extraScratch =
        Nat.succ
          (Nat.succ
            (Nat.succ
              (5 +
                (List.length
                    (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                      true L) -
                  1) +
                extraScratch))) by
    omega]
  simp [List.replicate_succ]

theorem selectedProjectionPaddedTailCleanupAcceptSentinelTargetTapeWithExtraScratch_cells_eq_parsed
    (L : DovetailLayout) (extraScratch : Nat)
    (hscratch :
      selectedProjectionPaddedTailCleanupSentinelBaseScratch true L +
          extraScratch =
        (ParsedLayoutBits L).length) :
    Tape.cells
        (selectedProjectionPaddedTailCleanupAcceptSentinelTargetTapeWithRightPadding
          L (List.replicate extraScratch (none : Option Bool))) =
      rightScratchOutputCells
        (selectedProjectionPaddedTailCleanupTargetBits true L)
        (ParsedLayoutBits L).length := by
  rw [
    selectedProjectionPaddedTailCleanupAcceptSentinelTargetTapeWithExtraScratch_cells]
  change rightScratchOutputCells
      (selectedProjectionPaddedTailCleanupTargetBits true L)
      (selectedProjectionPaddedTailCleanupSentinelBaseScratch true L +
        extraScratch) =
    rightScratchOutputCells
      (selectedProjectionPaddedTailCleanupTargetBits true L)
      (ParsedLayoutBits L).length
  rw [hscratch]

theorem selectedProjectionPaddedTailCleanupAcceptSentinelTargetTapeWithLayoutExtraScratch_cells_eq_parsed
    (L : DovetailLayout)
    (hle :
      selectedProjectionPaddedTailCleanupSentinelBaseScratch true L <=
        (ParsedLayoutBits L).length) :
    Tape.cells
        (selectedProjectionPaddedTailCleanupAcceptSentinelTargetTapeWithRightPadding
          L
          (List.replicate
            (selectedProjectionPaddedTailCleanupSentinelExtraScratch true L)
            (none : Option Bool))) =
      rightScratchOutputCells
        (selectedProjectionPaddedTailCleanupTargetBits true L)
        (ParsedLayoutBits L).length :=
  selectedProjectionPaddedTailCleanupAcceptSentinelTargetTapeWithExtraScratch_cells_eq_parsed
    L
    (selectedProjectionPaddedTailCleanupSentinelExtraScratch true L)
    (selectedProjectionPaddedTailCleanupSentinelBaseScratch_add_extraScratch
      true L hle)

theorem selectedProjectionPaddedTailCleanupAcceptSentinelTargetTapeWithLayoutExtraScratch_cells_eq_output
    (L : DovetailLayout) :
    Tape.cells
        (selectedProjectionPaddedTailCleanupAcceptSentinelTargetTapeWithRightPadding
          L
          (List.replicate
            (selectedProjectionPaddedTailCleanupSentinelExtraScratch true L)
            (none : Option Bool))) =
      Tape.cells (SelectedProjectionEquivEmitterPaddedOutputTape true L) := by
  rw [
    selectedProjectionPaddedTailCleanupAcceptSentinelTargetTapeWithLayoutExtraScratch_cells_eq_parsed
      L
      (selectedProjectionPaddedTailCleanupSentinelBaseScratch_le_parsed_true
        L)]
  rw [selectedProjectionPaddedTailCleanupTargetTape_cells_eq_bits]
  rfl

theorem selectedProjectionPaddedTailCleanupRejectSentinelTargetTape_cells
    (L : DovetailLayout) :
    Tape.cells
        (selectedProjectionPaddedTailCleanupRejectSentinelTargetTape L) =
      rightScratchOutputCells
        (selectedProjectionPaddedTailCleanupTargetBits false L)
        ((selectedProjectionPaddedTailCleanupUnselectedConfigBits
          false L).length.pred + 8) := by
  rw [selectedProjectionPaddedTailCleanupRejectSentinelTargetTape,
    leadingBlankLeftShiftTargetTapeWithPadding_cells]
  simp [rightScratchOutputCells, leadingBlankLeftShiftTargetCellsWithPadding,
    leadingBlankLeftShiftTargetVisiblePadding]
  have hpad :
      sentinelGapCompactorFinalPadding
          (List.length
              (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                false L) -
            1)
          2 [none, none, none] =
        List.replicate
          (2 +
            (List.length
                (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                  false L) -
              1) +
            3)
          (none : Option Bool) := by
    simpa using
      sentinelGapCompactorFinalPadding_replicate
        (List.length
            (selectedProjectionPaddedTailCleanupUnselectedConfigBits
              false L) -
          1)
        1 3
  rw [hpad]
  rw [show
      (List.length
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits
            false L) -
        1) + 8 =
        Nat.succ
          (Nat.succ
            (Nat.succ
              (2 +
                (List.length
                    (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                      false L) -
                  1) +
                3))) by
    omega]
  simp [List.replicate_succ]

theorem selectedProjectionPaddedTailCleanupRejectSentinelTargetTapeWithExtraScratch_cells
    (L : DovetailLayout)
    (extraScratch : Nat) :
    Tape.cells
        (selectedProjectionPaddedTailCleanupRejectSentinelTargetTapeWithRightPadding
          L (List.replicate extraScratch (none : Option Bool))) =
      rightScratchOutputCells
        (selectedProjectionPaddedTailCleanupTargetBits false L)
        ((selectedProjectionPaddedTailCleanupUnselectedConfigBits
          false L).length.pred + 8 + extraScratch) := by
  rw [
    selectedProjectionPaddedTailCleanupRejectSentinelTargetTapeWithRightPadding,
    leadingBlankLeftShiftTargetTapeWithPadding_cells]
  simp [rightScratchOutputCells, leadingBlankLeftShiftTargetCellsWithPadding,
    leadingBlankLeftShiftTargetVisiblePadding]
  have hright :
      List.append (List.replicate 3 (none : Option Bool))
          (List.replicate extraScratch (none : Option Bool)) =
        List.replicate (3 + extraScratch) (none : Option Bool) :=
    replicate_none_append_replicate_none 3 extraScratch
  have hpad :
      sentinelGapCompactorFinalPadding
          (List.length
              (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                false L) -
            1)
          2
          (none :: none :: none ::
            List.replicate extraScratch (none : Option Bool)) =
        List.replicate
          (2 +
            (List.length
                (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                  false L) -
              1) +
            (3 + extraScratch))
          (none : Option Bool) := by
    change
      sentinelGapCompactorFinalPadding
          (List.length
              (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                false L) -
            1)
          2
          (List.append (List.replicate 3 (none : Option Bool))
            (List.replicate extraScratch (none : Option Bool))) =
        List.replicate
          (2 +
            (List.length
                (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                  false L) -
              1) +
            (3 + extraScratch))
          (none : Option Bool)
    rw [hright]
    simpa using
      sentinelGapCompactorFinalPadding_replicate
        (List.length
            (selectedProjectionPaddedTailCleanupUnselectedConfigBits
              false L) -
          1)
        1 (3 + extraScratch)
  rw [hpad]
  rw [show
      (List.length
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits
            false L) -
        1) + 8 + extraScratch =
        Nat.succ
          (Nat.succ
            (Nat.succ
              (2 +
                (List.length
                    (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                      false L) -
                  1) +
                (3 + extraScratch)))) by
    omega]
  simp [List.replicate_succ]

theorem selectedProjectionPaddedTailCleanupRejectSentinelTargetTapeWithExtraScratch_cells_eq_parsed
    (L : DovetailLayout) (extraScratch : Nat)
    (hscratch :
      selectedProjectionPaddedTailCleanupSentinelBaseScratch false L +
          extraScratch =
        (ParsedLayoutBits L).length) :
    Tape.cells
        (selectedProjectionPaddedTailCleanupRejectSentinelTargetTapeWithRightPadding
          L (List.replicate extraScratch (none : Option Bool))) =
      rightScratchOutputCells
        (selectedProjectionPaddedTailCleanupTargetBits false L)
        (ParsedLayoutBits L).length := by
  rw [
    selectedProjectionPaddedTailCleanupRejectSentinelTargetTapeWithExtraScratch_cells]
  change rightScratchOutputCells
      (selectedProjectionPaddedTailCleanupTargetBits false L)
      (selectedProjectionPaddedTailCleanupSentinelBaseScratch false L +
        extraScratch) =
    rightScratchOutputCells
      (selectedProjectionPaddedTailCleanupTargetBits false L)
      (ParsedLayoutBits L).length
  rw [hscratch]

theorem selectedProjectionPaddedTailCleanupRejectSentinelTargetTapeWithLayoutExtraScratch_cells_eq_parsed
    (L : DovetailLayout)
    (hle :
      selectedProjectionPaddedTailCleanupSentinelBaseScratch false L <=
        (ParsedLayoutBits L).length) :
    Tape.cells
        (selectedProjectionPaddedTailCleanupRejectSentinelTargetTapeWithRightPadding
          L
          (List.replicate
            (selectedProjectionPaddedTailCleanupSentinelExtraScratch false L)
            (none : Option Bool))) =
      rightScratchOutputCells
        (selectedProjectionPaddedTailCleanupTargetBits false L)
        (ParsedLayoutBits L).length :=
  selectedProjectionPaddedTailCleanupRejectSentinelTargetTapeWithExtraScratch_cells_eq_parsed
    L
    (selectedProjectionPaddedTailCleanupSentinelExtraScratch false L)
    (selectedProjectionPaddedTailCleanupSentinelBaseScratch_add_extraScratch
      false L hle)

theorem selectedProjectionPaddedTailCleanupRejectSentinelTargetTapeWithLayoutExtraScratch_cells_eq_output
    (L : DovetailLayout) :
    Tape.cells
        (selectedProjectionPaddedTailCleanupRejectSentinelTargetTapeWithRightPadding
          L
          (List.replicate
            (selectedProjectionPaddedTailCleanupSentinelExtraScratch false L)
            (none : Option Bool))) =
      Tape.cells (SelectedProjectionEquivEmitterPaddedOutputTape false L) := by
  rw [
    selectedProjectionPaddedTailCleanupRejectSentinelTargetTapeWithLayoutExtraScratch_cells_eq_parsed
      L
      (selectedProjectionPaddedTailCleanupSentinelBaseScratch_le_parsed_false
        L)]
  rw [selectedProjectionPaddedTailCleanupTargetTape_cells_eq_bits]
  rfl

theorem selectedProjectionPaddedTailCleanupTargetBits_headerPrefix
    (useAccept : Bool) (L : DovetailLayout) :
    exists rest : Word Bool,
      selectedProjectionPaddedTailCleanupTargetBits useAccept L =
        false :: false :: false :: false :: rest := by
  rcases selectedProjection_outputAllBits_headerPrefix useAccept L with
    ⟨rest, hbits⟩
  refine ⟨rest, ?_⟩
  rw [selectedProjectionPaddedTailCleanupTargetBits_eq_outputCode,
    selectedProjectionOutputBits_eq_tailProjector_outputAllBits]
  exact hbits

theorem selectedProjectionPaddedTailCleanupTargetBits_false_cons_cons
    (useAccept : Bool) (L : DovetailLayout) :
    exists rest : Word Bool,
      selectedProjectionPaddedTailCleanupTargetBits useAccept L =
        false :: false :: rest := by
  rcases
      selectedProjectionPaddedTailCleanupTargetBits_headerPrefix
        useAccept L with
    ⟨rest, hbits⟩
  exact ⟨false :: false :: rest, hbits⟩

theorem selectedProjectionPaddedTailCleanupFalseMarkerRestoreTarget_eq_output
    {useAccept : Bool} {L : DovetailLayout}
    {second : Bool} {rest : Word Bool}
    {padding : List (Option Bool)}
    (hbits :
      selectedProjectionPaddedTailCleanupTargetBits useAccept L =
        false :: second :: rest)
    (hpadding :
      none :: none ::
          leadingBlankLeftShiftTargetVisiblePadding padding =
        List.replicate (ParsedLayoutBits L).length
          (none : Option Bool)) :
    tapeAtCells [some false]
        (List.append ((second :: rest).map some)
          (none :: none ::
            leadingBlankLeftShiftTargetVisiblePadding padding)) =
      SelectedProjectionEquivEmitterPaddedOutputTape useAccept L := by
  have houtput :
      SelectedProjectionTailProjector.outputAllBits useAccept L =
        false :: second :: rest := by
    rw [← selectedProjectionOutputBits_eq_tailProjector_outputAllBits]
    rw [← selectedProjectionPaddedTailCleanupTargetBits_eq_outputCode]
    exact hbits
  have htape :=
    SelectedProjectionEquivEmitterPaddedOutputTape_eq_tapeAtCells_of_outputAllBits
      (useAccept := useAccept) (L := L) (first := false)
      (rest := second :: rest) houtput
  rw [htape]
  rw [hpadding]
  simp [DovetailInitialLayoutInitializer.tapeAtCells, tapeAtCells]

theorem selectedProjectionPaddedTailCleanupFalseMarkerRestoreDescription_haltsFrom
    {useAccept : Bool} (L : DovetailLayout)
    (second : Bool) (rest : Word Bool)
    (padding : List (Option Bool))
    (hbits :
      selectedProjectionPaddedTailCleanupTargetBits useAccept L =
        false :: second :: rest)
    (hpadding :
      none :: none ::
          leadingBlankLeftShiftTargetVisiblePadding padding =
        List.replicate (ParsedLayoutBits L).length
          (none : Option Bool)) :
    falseMarkerTargetRestoreDescription.HaltsFromTape
      (leadingBlankLeftShiftTargetTapeWithPadding
        [none] (second :: rest) padding)
      (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L) := by
  have htape :=
    selectedProjectionPaddedTailCleanupFalseMarkerRestoreTarget_eq_output
      (useAccept := useAccept) (L := L) (second := second)
      (rest := rest) (padding := padding) hbits hpadding
  have hrun :=
    falseMarkerTargetRestoreDescription_haltsFromTape_cons
      second rest padding
  rw [htape] at hrun
  exact hrun

theorem selectedProjectionPaddedTailCleanupAcceptFalseMarkerRestorePadding_eq_parsed
    (L : DovetailLayout) :
    none :: none ::
        leadingBlankLeftShiftTargetVisiblePadding
          (none ::
            sentinelGapCompactorFinalPadding
              (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                true L).length.pred
              5
              (List.replicate
                (selectedProjectionPaddedTailCleanupSentinelExtraScratch
                  true L)
                (none : Option Bool))) =
      List.replicate (ParsedLayoutBits L).length
        (none : Option Bool) := by
  simp [leadingBlankLeftShiftTargetVisiblePadding]
  have hpad :
      sentinelGapCompactorFinalPadding
          (List.length
            (selectedProjectionPaddedTailCleanupUnselectedConfigBits
              true L) - 1)
          5
          (List.replicate
            (selectedProjectionPaddedTailCleanupSentinelExtraScratch
              true L)
            (none : Option Bool)) =
        List.replicate
          (5 +
            (List.length
              (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                true L) - 1) +
            selectedProjectionPaddedTailCleanupSentinelExtraScratch
              true L)
          (none : Option Bool) := by
    simpa using
      sentinelGapCompactorFinalPadding_replicate
        (List.length
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits
            true L) - 1)
        4
        (selectedProjectionPaddedTailCleanupSentinelExtraScratch
          true L)
  rw [hpad]
  rw [← List.replicate_succ]
  rw [← List.replicate_succ]
  rw [← List.replicate_succ]
  rw [show
      5 +
              (List.length
                  (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                    true L) -
                1) +
              selectedProjectionPaddedTailCleanupSentinelExtraScratch
                true L +
            1 +
          1 +
        1 =
        selectedProjectionPaddedTailCleanupSentinelBaseScratch true L +
          selectedProjectionPaddedTailCleanupSentinelExtraScratch true L by
    simp [selectedProjectionPaddedTailCleanupSentinelBaseScratch]
    omega]
  rw [
    selectedProjectionPaddedTailCleanupSentinelBaseScratch_add_extraScratch
      true L
      (selectedProjectionPaddedTailCleanupSentinelBaseScratch_le_parsed_true
        L)]

theorem selectedProjectionPaddedTailCleanupRejectFalseMarkerRestorePadding_eq_parsed
    (L : DovetailLayout) :
    none :: none ::
        leadingBlankLeftShiftTargetVisiblePadding
          (none ::
            sentinelGapCompactorFinalPadding
              (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                false L).length.pred
              2
              (List.append (List.replicate 3 (none : Option Bool))
                (List.replicate
                  (selectedProjectionPaddedTailCleanupSentinelExtraScratch
                    false L)
                  (none : Option Bool)))) =
      List.replicate (ParsedLayoutBits L).length
        (none : Option Bool) := by
  simp [leadingBlankLeftShiftTargetVisiblePadding]
  have hright :
      List.append (List.replicate 3 (none : Option Bool))
          (List.replicate
            (selectedProjectionPaddedTailCleanupSentinelExtraScratch
              false L)
            (none : Option Bool)) =
        List.replicate
          (3 +
            selectedProjectionPaddedTailCleanupSentinelExtraScratch
              false L)
          (none : Option Bool) :=
    replicate_none_append_replicate_none 3
      (selectedProjectionPaddedTailCleanupSentinelExtraScratch false L)
  have hpad :
      sentinelGapCompactorFinalPadding
          (List.length
            (selectedProjectionPaddedTailCleanupUnselectedConfigBits
              false L) - 1)
          2
          (none :: none :: none ::
            List.replicate
              (selectedProjectionPaddedTailCleanupSentinelExtraScratch
                false L)
              (none : Option Bool)) =
        List.replicate
          (2 +
            (List.length
              (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                false L) - 1) +
            (3 +
              selectedProjectionPaddedTailCleanupSentinelExtraScratch
                false L))
          (none : Option Bool) := by
    change
      sentinelGapCompactorFinalPadding
          (List.length
            (selectedProjectionPaddedTailCleanupUnselectedConfigBits
              false L) - 1)
          2
          (List.append (List.replicate 3 (none : Option Bool))
            (List.replicate
              (selectedProjectionPaddedTailCleanupSentinelExtraScratch
                false L)
              (none : Option Bool))) =
        List.replicate
          (2 +
            (List.length
              (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                false L) - 1) +
            (3 +
              selectedProjectionPaddedTailCleanupSentinelExtraScratch
                false L))
          (none : Option Bool)
    rw [hright]
    simpa using
      sentinelGapCompactorFinalPadding_replicate
        (List.length
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits
            false L) - 1)
        1
        (3 +
          selectedProjectionPaddedTailCleanupSentinelExtraScratch
            false L)
  rw [hpad]
  rw [← List.replicate_succ]
  rw [← List.replicate_succ]
  rw [← List.replicate_succ]
  rw [show
      2 +
              (List.length
                  (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                    false L) -
                1) +
              (3 +
                selectedProjectionPaddedTailCleanupSentinelExtraScratch
                  false L) +
            1 +
          1 +
        1 =
        selectedProjectionPaddedTailCleanupSentinelBaseScratch false L +
          selectedProjectionPaddedTailCleanupSentinelExtraScratch false L by
    simp [selectedProjectionPaddedTailCleanupSentinelBaseScratch]
    omega]
  rw [
    selectedProjectionPaddedTailCleanupSentinelBaseScratch_add_extraScratch
      false L
      (selectedProjectionPaddedTailCleanupSentinelBaseScratch_le_parsed_false
        L)]

theorem selectedProjectionPaddedTailCleanupAcceptFalseMarkerRestoreDescription_haltsFrom
    (L : DovetailLayout) :
    exists rest : Word Bool,
      falseMarkerTargetRestoreDescription.HaltsFromTape
        (leadingBlankLeftShiftTargetTapeWithPadding
          [none] (false :: rest)
          (none ::
            sentinelGapCompactorFinalPadding
              (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                true L).length.pred
              5
              (List.replicate
                (selectedProjectionPaddedTailCleanupSentinelExtraScratch
                  true L)
                (none : Option Bool))))
        (SelectedProjectionEquivEmitterPaddedOutputTape true L) := by
  rcases
      selectedProjectionPaddedTailCleanupTargetBits_false_cons_cons
        true L with
    ⟨rest, hbits⟩
  refine ⟨rest, ?_⟩
  exact
    selectedProjectionPaddedTailCleanupFalseMarkerRestoreDescription_haltsFrom
      (useAccept := true) L false rest
      (none ::
        sentinelGapCompactorFinalPadding
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits
            true L).length.pred
          5
          (List.replicate
            (selectedProjectionPaddedTailCleanupSentinelExtraScratch
              true L)
            (none : Option Bool)))
      hbits
      (selectedProjectionPaddedTailCleanupAcceptFalseMarkerRestorePadding_eq_parsed
        L)

theorem selectedProjectionPaddedTailCleanupRejectFalseMarkerRestoreDescription_haltsFrom
    (L : DovetailLayout) :
    exists rest : Word Bool,
      falseMarkerTargetRestoreDescription.HaltsFromTape
        (leadingBlankLeftShiftTargetTapeWithPadding
          [none] (false :: rest)
          (none ::
            sentinelGapCompactorFinalPadding
              (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                false L).length.pred
              2
              (List.append (List.replicate 3 (none : Option Bool))
                (List.replicate
                  (selectedProjectionPaddedTailCleanupSentinelExtraScratch
                    false L)
                  (none : Option Bool)))))
        (SelectedProjectionEquivEmitterPaddedOutputTape false L) := by
  rcases
      selectedProjectionPaddedTailCleanupTargetBits_false_cons_cons
        false L with
    ⟨rest, hbits⟩
  refine ⟨rest, ?_⟩
  exact
    selectedProjectionPaddedTailCleanupFalseMarkerRestoreDescription_haltsFrom
      (useAccept := false) L false rest
      (none ::
        sentinelGapCompactorFinalPadding
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits
            false L).length.pred
          2
          (List.append (List.replicate 3 (none : Option Bool))
            (List.replicate
              (selectedProjectionPaddedTailCleanupSentinelExtraScratch
                false L)
              (none : Option Bool))))
      hbits
      (selectedProjectionPaddedTailCleanupRejectFalseMarkerRestorePadding_eq_parsed
        L)

def selectedProjectionPaddedTailCleanupFalseMarkerToEquivOutputDescription :
    MachineDescription :=
  canonicalSeqDescription
    sentinelFalseMarkerRightEndGapCompactorDescription
    falseMarkerTargetRestoreDescription

theorem selectedProjectionPaddedTailCleanupFalseMarkerToEquivOutputDescription_subroutineReady :
    selectedProjectionPaddedTailCleanupFalseMarkerToEquivOutputDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    sentinelFalseMarkerRightEndGapCompactorDescription_subroutineReady
    falseMarkerTargetRestoreDescription_subroutineReady

theorem selectedProjectionPaddedTailCleanupDeletedRejectFixedGapClosed_to_equivOutput_withLayoutExtraScratch
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupFalseMarkerToEquivOutputDescription.HaltsFromTape
      (rightEndCompactionSourceTapeWithRightPadding
        (selectedProjectionPaddedTailCleanupDeletedRejectFixedGapClosedLeftCells
          L)
        (List.append (List.replicate 3 (none : Option Bool))
          (List.replicate
            (selectedProjectionPaddedTailCleanupSentinelExtraScratch
              false L)
            (none : Option Bool))))
      (SelectedProjectionEquivEmitterPaddedOutputTape false L) := by
  rcases selectedProjectionPaddedTailCleanupPrefix_append_last L with
    ⟨pref, leftBit, hpref⟩
  rcases
      selectedProjectionPaddedTailCleanupSelectedHit_false_reverse_cons
        L with
    ⟨current, hitLeftRest, hhitRev⟩
  rcases
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_cons_false
        L.acceptConfig [] with
    ⟨deletedTail, hdeleted⟩
  rcases
      selectedProjectionPaddedTailCleanupTargetBits_false_cons_cons
        false L with
    ⟨rest, hbits⟩
  let payload : Word Bool :=
    List.append
      (selectedProjectionPaddedTailCleanupSelectedConfigBits false L)
      (selectedProjectionPaddedTailCleanupSelectedHitBits false L)
  let leftRest : Word Bool :=
    List.append hitLeftRest
      (selectedProjectionPaddedTailCleanupSelectedConfigBits false L).reverse
  have hpayload :
      (current :: leftRest).reverse = payload := by
    have hhit :
        hitLeftRest.reverse ++ [current] =
          selectedProjectionPaddedTailCleanupSelectedHitBits false L := by
      rw [←
        List.reverse_reverse
          (selectedProjectionPaddedTailCleanupSelectedHitBits false L)]
      rw [hhitRev]
      simp
    change
      (current ::
          List.append hitLeftRest
            (selectedProjectionPaddedTailCleanupSelectedConfigBits
              false L).reverse).reverse =
        List.append
          (selectedProjectionPaddedTailCleanupSelectedConfigBits false L)
          (selectedProjectionPaddedTailCleanupSelectedHitBits false L)
    rw [List.reverse_cons]
    simp [List.reverse_append, hhit, List.append_assoc]
  have hdeleteLen :
      (selectedProjectionPaddedTailCleanupUnselectedConfigBits
        false L).length =
        Nat.succ deletedTail.length := by
    simp [selectedProjectionPaddedTailCleanupUnselectedConfigBits,
      hdeleted]
  have htargetBits :
      List.append pref (leftBit :: (current :: leftRest).reverse) =
        false :: false :: rest := by
    have htarget :
        selectedProjectionPaddedTailCleanupTargetBits false L =
          List.append pref (leftBit :: (current :: leftRest).reverse) := by
      rw [selectedProjectionPaddedTailCleanupTargetBits_eq_selectedFields,
        hpref, hpayload]
      simp [payload, List.append_assoc]
    rw [← htarget]
    exact hbits
  have hsourceCells :
      selectedProjectionPaddedTailCleanupDeletedRejectFixedGapClosedLeftCells
          L =
        rightEndSentinelGapCompactorSourceLeftCells
          (List.append (pref.reverse.map some) [none])
          leftBit current leftRest deletedTail.length 2 := by
    rw [rightEndSentinelGapCompactorSourceLeftCells_eq_split]
    rw [selectedProjectionPaddedTailCleanupDeletedRejectFixedGapClosedLeftCells]
    rw [hdeleteLen, hpayload, ← hpref]
    simp [payload, List.map_append, List.append_assoc]
  have hmarker :
      sentinelFalseMarkerRightEndGapCompactorDescription.HaltsFromTape
        (rightEndCompactionSourceTapeWithRightPadding
          (selectedProjectionPaddedTailCleanupDeletedRejectFixedGapClosedLeftCells
            L)
          (List.append (List.replicate 3 (none : Option Bool))
            (List.replicate
              (selectedProjectionPaddedTailCleanupSentinelExtraScratch
                false L)
              (none : Option Bool))))
        (leadingBlankLeftShiftTargetTapeWithPadding
          [none] (false :: rest)
          (none ::
            sentinelGapCompactorFinalPadding
              (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                false L).length.pred
              2
              (List.append (List.replicate 3 (none : Option Bool))
                (List.replicate
                  (selectedProjectionPaddedTailCleanupSentinelExtraScratch
                    false L)
                  (none : Option Bool))))) := by
    rw [hsourceCells, hdeleteLen]
    simpa using
      sentinelFalseMarkerRightEndGapCompactorDescription_haltsFrom_rightEndGapSourceWithRightPadding
        deletedTail.length pref (false :: rest) leftBit current leftRest
        0
        (List.append (List.replicate 3 (none : Option Bool))
          (List.replicate
            (selectedProjectionPaddedTailCleanupSentinelExtraScratch
              false L)
            (none : Option Bool)))
        htargetBits
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      sentinelFalseMarkerRightEndGapCompactorDescription_subroutineReady
      falseMarkerTargetRestoreDescription_subroutineReady
      hmarker
      (by
        rw [sentinelGapCompactorFinalPadding_cons_cons_right]
        exact
          leadingBlankLeftShiftTargetTapeWithPadding_move_left_move_right_padding_cons_cons
            [none] (false :: rest) none none
            (none ::
              List.append
                (List.replicate
                  (0 +
                    (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                      false L).length.pred)
                  (none : Option Bool))
                (List.append (List.replicate 3 (none : Option Bool))
                  (List.replicate
                    (selectedProjectionPaddedTailCleanupSentinelExtraScratch
                      false L)
                    (none : Option Bool)))))
      (selectedProjectionPaddedTailCleanupFalseMarkerRestoreDescription_haltsFrom
        (useAccept := false) L false rest
        (none ::
          sentinelGapCompactorFinalPadding
            (selectedProjectionPaddedTailCleanupUnselectedConfigBits
              false L).length.pred
            2
            (List.append (List.replicate 3 (none : Option Bool))
              (List.replicate
                (selectedProjectionPaddedTailCleanupSentinelExtraScratch
                  false L)
                (none : Option Bool))))
        hbits
        (selectedProjectionPaddedTailCleanupRejectFalseMarkerRestorePadding_eq_parsed
          L))

theorem selectedProjectionPaddedTailCleanupDeletedAcceptRightEnd_to_equivOutput_withLayoutExtraScratch
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupFalseMarkerToEquivOutputDescription.HaltsFromTape
      (rightEndCompactionSourceTapeWithRightPadding
        (selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells L)
        (List.replicate
          (selectedProjectionPaddedTailCleanupSentinelExtraScratch
            true L)
          (none : Option Bool)))
      (SelectedProjectionEquivEmitterPaddedOutputTape true L) := by
  rcases selectedProjectionPaddedTailCleanupKeptPrefix_true_append_last
      L with
    ⟨pref, leftBit, hpref⟩
  rcases selectedProjectionPaddedTailCleanupSelectedHit_true_reverse_cons
      L with
    ⟨current, leftRest, hhitRev⟩
  rcases
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_cons_false
        L.rejectConfig [] with
    ⟨deletedTail, hdeleted⟩
  rcases
      selectedProjectionPaddedTailCleanupTargetBits_false_cons_cons
        true L with
    ⟨rest, hbits⟩
  have hhit : (current :: leftRest).reverse =
      selectedProjectionPaddedTailCleanupSelectedHitBits true L := by
    rw [← hhitRev]
    simp
  have hdeleteLen :
      (selectedProjectionPaddedTailCleanupUnselectedConfigBits true L).length =
        Nat.succ deletedTail.length := by
    simp [selectedProjectionPaddedTailCleanupUnselectedConfigBits,
      hdeleted]
  have htargetBits :
      List.append pref (leftBit :: (current :: leftRest).reverse) =
        false :: false :: rest := by
    have htarget :
        selectedProjectionPaddedTailCleanupTargetBits true L =
          List.append pref (leftBit :: (current :: leftRest).reverse) := by
      rw [selectedProjectionPaddedTailCleanupTargetBits_eq_kept,
        hpref, selectedProjectionPaddedTailCleanupKeptSuffixBits, hhit]
      simp [List.append_assoc]
    rw [← htarget]
    exact hbits
  have hsourceCells :
      selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells L =
        rightEndSentinelGapCompactorSourceLeftCells
          (List.append (pref.reverse.map some) [none])
          leftBit current leftRest deletedTail.length 5 := by
    rw [rightEndSentinelGapCompactorSourceLeftCells_eq_split]
    rw [selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells]
    rw [hdeleteLen]
    rw [← hhit]
    rw [← hpref]
    simp [selectedProjectionPaddedTailCleanupKeptPrefixBits,
      List.map_append, List.append_assoc]
  have hmarker :
      sentinelFalseMarkerRightEndGapCompactorDescription.HaltsFromTape
        (rightEndCompactionSourceTapeWithRightPadding
          (selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells L)
          (List.replicate
            (selectedProjectionPaddedTailCleanupSentinelExtraScratch
              true L)
            (none : Option Bool)))
        (leadingBlankLeftShiftTargetTapeWithPadding
          [none] (false :: rest)
          (none ::
            sentinelGapCompactorFinalPadding
              (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                true L).length.pred
              5
              (List.replicate
                (selectedProjectionPaddedTailCleanupSentinelExtraScratch
                  true L)
                (none : Option Bool)))) := by
    rw [hsourceCells, hdeleteLen]
    simpa using
      sentinelFalseMarkerRightEndGapCompactorDescription_haltsFrom_rightEndGapSourceWithRightPadding
        deletedTail.length pref (false :: rest) leftBit current leftRest
        3
        (List.replicate
          (selectedProjectionPaddedTailCleanupSentinelExtraScratch
            true L)
          (none : Option Bool))
        htargetBits
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      sentinelFalseMarkerRightEndGapCompactorDescription_subroutineReady
      falseMarkerTargetRestoreDescription_subroutineReady
      hmarker
      (by
        rw [sentinelGapCompactorFinalPadding_cons_cons_right]
        exact
          leadingBlankLeftShiftTargetTapeWithPadding_move_left_move_right_padding_cons_cons
            [none] (false :: rest) none none
            (none ::
              List.append
                (List.replicate
                  (3 +
                    (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                      true L).length.pred)
                  (none : Option Bool))
                (List.replicate
                  (selectedProjectionPaddedTailCleanupSentinelExtraScratch
                    true L)
                  (none : Option Bool))))
      (selectedProjectionPaddedTailCleanupFalseMarkerRestoreDescription_haltsFrom
        (useAccept := true) L false rest
        (none ::
          sentinelGapCompactorFinalPadding
            (selectedProjectionPaddedTailCleanupUnselectedConfigBits
              true L).length.pred
            5
            (List.replicate
              (selectedProjectionPaddedTailCleanupSentinelExtraScratch
                true L)
              (none : Option Bool)))
        hbits
        (selectedProjectionPaddedTailCleanupAcceptFalseMarkerRestorePadding_eq_parsed
          L))

def selectedProjectionPaddedTailCleanupSentinelRewindDescription :
    MachineDescription :=
  SeqViaCanonical leftMoveOnceDescription
    (SeqViaCanonical leftMoveOnceDescription rightEdgeRewindDescription)

def selectedProjectionPaddedTailCleanupAcceptRewindTargetTape
    (L : DovetailLayout) : Tape Bool :=
  rightEdgeRewindTargetTape
    (selectedProjectionPaddedTailCleanupTargetBits true L)
    (none :: none ::
      sentinelGapCompactorFinalPadding
        (selectedProjectionPaddedTailCleanupUnselectedConfigBits
          true L).length.pred
        5 [])

def selectedProjectionPaddedTailCleanupRejectRewindTargetTape
    (L : DovetailLayout) : Tape Bool :=
  rightEdgeRewindTargetTape
    (selectedProjectionPaddedTailCleanupTargetBits false L)
    (none :: none ::
      sentinelGapCompactorFinalPadding
        (selectedProjectionPaddedTailCleanupUnselectedConfigBits
          false L).length.pred
        2 (List.replicate 3 (none : Option Bool)))

theorem selectedProjectionPaddedTailCleanupSentinelRewindDescription_subroutineReady :
    selectedProjectionPaddedTailCleanupSentinelRewindDescription.SubroutineReady :=
  SeqViaCanonical_subroutineReady
    leftMoveOnceDescription_subroutineReady
    (SeqViaCanonical_subroutineReady
      leftMoveOnceDescription_subroutineReady
      rightEdgeRewindDescription_subroutineReady)

theorem leadingBlankLeftShiftTargetTapeWithPadding_first_left_stable
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (Tape.move Direction.left
            (leadingBlankLeftShiftTargetTapeWithPadding
              [] bits (none :: padding)))) =
      Tape.move Direction.left
        (leadingBlankLeftShiftTargetTapeWithPadding
          [] bits (none :: padding)) := by
  cases bits <;> cases padding <;>
    simp [leadingBlankLeftShiftTargetTapeWithPadding, tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]

theorem leadingBlankLeftShiftTargetTapeWithPadding_second_left_rewindSource
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.left
          (leadingBlankLeftShiftTargetTapeWithPadding
            [] bits (none :: padding))) =
      rightEdgeRewindSourceTape bits (none :: none :: padding) := by
  cases bits <;> cases padding <;>
    simp [leadingBlankLeftShiftTargetTapeWithPadding,
      rightEdgeRewindSourceTape, tapeAtCells, Tape.move, Tape.moveLeft,
      List.map_reverse]

theorem leadingBlankLeftShiftTargetTapeWithPadding_second_left_bridge
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (Tape.move Direction.left
            (Tape.move Direction.left
              (leadingBlankLeftShiftTargetTapeWithPadding
                [] bits (none :: padding))))) =
      rightEdgeRewindSourceTape bits (none :: none :: padding) := by
  rw [leadingBlankLeftShiftTargetTapeWithPadding_second_left_rewindSource]
  cases bits <;> cases padding <;>
    simp [rightEdgeRewindSourceTape, tapeAtCells, Tape.move,
      Tape.moveLeft, Tape.moveRight]

theorem selectedProjectionPaddedTailCleanupSentinelRewindDescription_haltsFrom
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedProjectionPaddedTailCleanupSentinelRewindDescription.HaltsFromTape
      (leadingBlankLeftShiftTargetTapeWithPadding
        [] bits (none :: padding))
      (rightEdgeRewindTargetTape bits (none :: none :: padding)) := by
  exact
    SeqViaCanonical_haltsFromTape_of_haltsFromTape
      leftMoveOnceDescription_subroutineReady
      (SeqViaCanonical_subroutineReady
        leftMoveOnceDescription_subroutineReady
        rightEdgeRewindDescription_subroutineReady)
      (leftMoveOnceDescription_haltsFromTape
        (leadingBlankLeftShiftTargetTapeWithPadding
          [] bits (none :: padding)))
      (leadingBlankLeftShiftTargetTapeWithPadding_first_left_stable
        bits padding)
      (SeqViaCanonical_haltsFromTape_of_haltsFromTape
        leftMoveOnceDescription_subroutineReady
        rightEdgeRewindDescription_subroutineReady
        (leftMoveOnceDescription_haltsFromTape
          (Tape.move Direction.left
            (leadingBlankLeftShiftTargetTapeWithPadding
              [] bits (none :: padding))))
        (leadingBlankLeftShiftTargetTapeWithPadding_second_left_bridge
          bits padding)
        (rightEdgeRewindDescription_haltsFromTape
          bits (none :: none :: padding)))

theorem selectedProjectionPaddedTailCleanupAcceptSentinelTarget_to_rewindTarget
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupSentinelRewindDescription.HaltsFromTape
      (selectedProjectionPaddedTailCleanupAcceptSentinelTargetTape L)
      (selectedProjectionPaddedTailCleanupAcceptRewindTargetTape L) := by
  simpa [selectedProjectionPaddedTailCleanupAcceptSentinelTargetTape] using
    selectedProjectionPaddedTailCleanupSentinelRewindDescription_haltsFrom
      (selectedProjectionPaddedTailCleanupTargetBits true L)
      (sentinelGapCompactorFinalPadding
        (selectedProjectionPaddedTailCleanupUnselectedConfigBits
          true L).length.pred
        5 [])

theorem selectedProjectionPaddedTailCleanupRejectSentinelTarget_to_rewindTarget
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupSentinelRewindDescription.HaltsFromTape
      (selectedProjectionPaddedTailCleanupRejectSentinelTargetTape L)
      (selectedProjectionPaddedTailCleanupRejectRewindTargetTape L) := by
  simpa [selectedProjectionPaddedTailCleanupRejectSentinelTargetTape] using
    selectedProjectionPaddedTailCleanupSentinelRewindDescription_haltsFrom
      (selectedProjectionPaddedTailCleanupTargetBits false L)
      (sentinelGapCompactorFinalPadding
        (selectedProjectionPaddedTailCleanupUnselectedConfigBits
          false L).length.pred
        2 (List.replicate 3 (none : Option Bool)))

theorem selectedProjectionPaddedTailCleanupAcceptRewindTargetTape_normalizedOutput
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedProjectionPaddedTailCleanupAcceptRewindTargetTape L) =
      selectedProjectionPaddedTailCleanupTargetBits true L := by
  rw [selectedProjectionPaddedTailCleanupAcceptRewindTargetTape,
    rightEdgeRewindTargetTape_normalizedOutput]
  simp [sentinelGapCompactorFinalPadding_eq_replicate_append]

theorem selectedProjectionPaddedTailCleanupRejectRewindTargetTape_normalizedOutput
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedProjectionPaddedTailCleanupRejectRewindTargetTape L) =
      selectedProjectionPaddedTailCleanupTargetBits false L := by
  rw [selectedProjectionPaddedTailCleanupRejectRewindTargetTape,
    rightEdgeRewindTargetTape_normalizedOutput]
  simp [sentinelGapCompactorFinalPadding_eq_replicate_append,
    List.filterMap_append]

theorem selectedProjectionPaddedTailCleanupAcceptRewindTargetTape_cells
    (L : DovetailLayout) :
    Tape.cells
        (selectedProjectionPaddedTailCleanupAcceptRewindTargetTape L) =
      none ::
        rightScratchOutputCells
          (selectedProjectionPaddedTailCleanupTargetBits true L)
          ((selectedProjectionPaddedTailCleanupUnselectedConfigBits
            true L).length.pred + 8) := by
  rw [selectedProjectionPaddedTailCleanupAcceptRewindTargetTape,
    rightEdgeRewindTargetTape_cells]
  simp [rightScratchOutputCells]
  have hpad :
      none :: none :: none ::
          sentinelGapCompactorFinalPadding
            (List.length
                (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                  true L) -
              1)
            5 [] =
        List.replicate
          ((List.length
              (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                true L) -
            1) + 8)
          (none : Option Bool) := by
    have hcore :
        sentinelGapCompactorFinalPadding
            (List.length
                (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                  true L) -
              1)
            5 [] =
          List.replicate
            (5 +
              (List.length
                  (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                    true L) -
                1))
            (none : Option Bool) := by
      simpa using
        sentinelGapCompactorFinalPadding_replicate
          (List.length
              (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                true L) -
            1)
          4 0
    rw [hcore]
    rw [show
        (List.length
            (selectedProjectionPaddedTailCleanupUnselectedConfigBits
              true L) -
          1) + 8 =
          Nat.succ
            (Nat.succ
              (Nat.succ
                (5 +
                  (List.length
                      (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                        true L) -
                    1)))) by
      omega]
    simp [List.replicate_succ]
  rw [hpad]

theorem selectedProjectionPaddedTailCleanupRejectRewindTargetTape_cells
    (L : DovetailLayout) :
    Tape.cells
        (selectedProjectionPaddedTailCleanupRejectRewindTargetTape L) =
      none ::
        rightScratchOutputCells
          (selectedProjectionPaddedTailCleanupTargetBits false L)
          ((selectedProjectionPaddedTailCleanupUnselectedConfigBits
            false L).length.pred + 8) := by
  rw [selectedProjectionPaddedTailCleanupRejectRewindTargetTape,
    rightEdgeRewindTargetTape_cells]
  simp [rightScratchOutputCells]
  have hpad :
      none :: none :: none ::
          sentinelGapCompactorFinalPadding
            (List.length
                (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                  false L) -
              1)
            2 [none, none, none] =
        List.replicate
          ((List.length
              (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                false L) -
            1) + 8)
          (none : Option Bool) := by
    have hcore :
        sentinelGapCompactorFinalPadding
            (List.length
                (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                  false L) -
              1)
            2 [none, none, none] =
          List.replicate
            (2 +
              (List.length
                  (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                    false L) -
                1) +
              3)
            (none : Option Bool) := by
      simpa using
        sentinelGapCompactorFinalPadding_replicate
          (List.length
              (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                false L) -
            1)
          1 3
    rw [hcore]
    rw [show
        (List.length
            (selectedProjectionPaddedTailCleanupUnselectedConfigBits
              false L) -
          1) + 8 =
          Nat.succ
            (Nat.succ
              (Nat.succ
                (2 +
                  (List.length
                      (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                        false L) -
                    1) +
                  3))) by
      omega]
    simp [List.replicate_succ]
  rw [hpad]

theorem tapeAtCells_move_right_move_left_append_cons_blank
    (pref tail : List (Option Bool)) (cell : Option Bool) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tapeAtCells (List.append pref (cell :: tail)) [])) =
      tapeAtCells (List.append pref (cell :: tail)) [none] := by
  cases pref <;>
    simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem tapeAtCells_move_right_move_left_append_cons
    (pref tail right : List (Option Bool)) (cell : Option Bool) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tapeAtCells (List.append pref (cell :: tail)) right)) =
      tapeAtCells (List.append pref (cell :: tail)) right := by
  cases pref <;> cases right <;>
    simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem rightBlankGapPayloadScanTargetTapeImplicit_move_right_eq_rightEndCompactionSourceTape
    (baseLeft : List (Option Bool)) (gap : Nat)
    (current : Bool) (payloadRest : Word Bool) :
    Tape.move Direction.right
        (rightBlankGapPayloadScanTargetTapeImplicit
          baseLeft gap current payloadRest) =
      rightEndCompactionSourceTape
        (List.append baseLeft.reverse
          (List.append
            (List.replicate gap (none : Option Bool))
            ((current :: payloadRest).map some))) := by
  rw [rightBlankGapPayloadScanTargetTapeImplicit,
    rightEndCompactionSourceTape]
  rw [show
      (List.append baseLeft.reverse
          (List.append
            (List.replicate gap (none : Option Bool))
            ((current :: payloadRest).map some))).reverse =
        List.append (payloadRest.reverse.map some)
              (some current ::
                List.append (List.replicate gap (none : Option Bool))
                  baseLeft) by
    simp [List.reverse_append, List.append_assoc]]
  simpa [List.reverse_cons, List.map_append, List.append_assoc] using
    tapeAtCells_move_right_move_left_append_cons_blank
      (payloadRest.reverse.map some)
      (List.append (List.replicate gap (none : Option Bool)) baseLeft)
      (some current)

theorem rightBlankGapPayloadScanTargetTape_move_right_eq_rightEndCompactionSourceTapeWithRightPadding
    (baseLeft : List (Option Bool)) (gap : Nat)
    (current : Bool) (payloadRest : Word Bool)
    (rightPadding : List (Option Bool)) :
    Tape.move Direction.right
        (rightBlankGapPayloadScanTargetTape
          baseLeft gap current payloadRest rightPadding) =
      rightEndCompactionSourceTapeWithRightPadding
        (List.append baseLeft.reverse
          (List.append
            (List.replicate gap (none : Option Bool))
            ((current :: payloadRest).map some)))
        rightPadding := by
  rw [rightBlankGapPayloadScanTargetTape,
    rightEndCompactionSourceTapeWithRightPadding]
  rw [show
      (List.append baseLeft.reverse
          (List.append
            (List.replicate gap (none : Option Bool))
            ((current :: payloadRest).map some))).reverse =
        List.append (payloadRest.reverse.map some)
              (some current ::
                List.append (List.replicate gap (none : Option Bool))
                  baseLeft) by
    simp [List.reverse_append, List.append_assoc]]
  simpa [List.reverse_cons, List.map_append, List.append_assoc] using
    tapeAtCells_move_right_move_left_append_cons
      (payloadRest.reverse.map some)
      (List.append (List.replicate gap (none : Option Bool)) baseLeft)
      (none :: rightPadding)
      (some current)

def rightMoveAcrossFiveBlanksDescription : MachineDescription :=
  SeqViaCanonical rightMoveAcrossFourBlanksDescription
    rightMoveOnceDescription

theorem rightMoveAcrossFiveBlanksDescription_subroutineReady :
    rightMoveAcrossFiveBlanksDescription.SubroutineReady :=
  SeqViaCanonical_subroutineReady
    rightMoveAcrossFourBlanksDescription_subroutineReady
    rightMoveOnceDescription_subroutineReady

theorem rightMoveAcrossFourBlanksTarget_move_left_move_right
    (leftCells : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (tapeAtCells
            (List.append (List.replicate 4 (none : Option Bool))
              leftCells.reverse)
            [none, none])) =
      tapeAtCells
        (List.append (List.replicate 4 (none : Option Bool))
          leftCells.reverse)
        [none, none] := by
  simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem rightMoveOnceDescription_haltsFrom_fourBlankTarget
    (leftCells : List (Option Bool)) :
    rightMoveOnceDescription.HaltsFromTape
      (tapeAtCells
        (List.append (List.replicate 4 (none : Option Bool))
          leftCells.reverse)
        [none, none])
      (rightEndCompactionSourceTape
        (List.append leftCells
          (List.replicate 5 (none : Option Bool)))) := by
  have hmove :=
    rightMoveOnceDescription_haltsFromTape
      (tapeAtCells
        (List.append (List.replicate 4 (none : Option Bool))
          leftCells.reverse)
        [none, none])
  simpa [rightEndCompactionSourceTape, tapeAtCells, Tape.move,
    Tape.moveRight, List.reverse_append, List.replicate_succ,
    List.append_assoc] using hmove

theorem rightMoveAcrossFiveBlanksDescription_haltsFrom_rightPadding
    (leftCells : List (Option Bool)) :
    rightMoveAcrossFiveBlanksDescription.HaltsFromTape
      (rightEndCompactionSourceTapeWithRightPadding
        leftCells (List.replicate 5 (none : Option Bool)))
      (rightEndCompactionSourceTape
        (List.append leftCells
          (List.replicate 5 (none : Option Bool)))) := by
  exact
    SeqViaCanonical_haltsFromTape_of_haltsFromTape
      rightMoveAcrossFourBlanksDescription_subroutineReady
      rightMoveOnceDescription_subroutineReady
      (by
        simpa [rightEndCompactionSourceTapeWithRightPadding,
          List.replicate_succ] using
          rightMoveAcrossFourBlanksDescription_haltsFromTape
            leftCells.reverse [none, none])
      (rightMoveAcrossFourBlanksTarget_move_left_move_right leftCells)
      (rightMoveOnceDescription_haltsFrom_fourBlankTarget leftCells)

theorem FSTStatefulOptionAppendSourceTapeWithPadding_eq_tapeAtCells
    (input : Word Bool) (leftScratch : Nat)
    (padding : List (Option Bool)) :
    FSTStatefulOptionAppendSourceTapeWithPadding input leftScratch padding =
      tapeAtCells (List.replicate leftScratch (none : Option Bool))
        (List.append (input.map some) (none :: padding)) := by
  rfl

theorem FSTStatefulOptionAppendSourceTapeWithPadding_one_eq_tapeAtCells
    (input : Word Bool) (padding : List (Option Bool)) :
    FSTStatefulOptionAppendSourceTapeWithPadding input 1 padding =
      tapeAtCells [none]
        (List.append (input.map some) (none :: padding)) := by
  simp [FSTStatefulOptionAppendSourceTapeWithPadding_eq_tapeAtCells]

theorem postPaddingAcceptSourceWithPadding_eq_tapeAtCells
    (L : DovetailLayout) (padding : List (Option Bool)) :
    FSTStatefulOptionAppendSourceTapeWithPadding
        (selectedProjectionPaddedTailCleanupPostPaddingSourceBits true L)
        1 padding =
      tapeAtCells [none]
        (List.append
          ((selectedProjectionPaddedTailCleanupPostPaddingSourceBits
            true L).map some)
          (none :: padding)) := by
  exact
    FSTStatefulOptionAppendSourceTapeWithPadding_one_eq_tapeAtCells
      (selectedProjectionPaddedTailCleanupPostPaddingSourceBits true L)
      padding

theorem postPaddingRejectSourceWithPadding_eq_tapeAtCells
    (L : DovetailLayout) (padding : List (Option Bool)) :
    FSTStatefulOptionAppendSourceTapeWithPadding
        (selectedProjectionPaddedTailCleanupPostPaddingSourceBits false L)
        1 padding =
      tapeAtCells [none]
        (List.append
          ((selectedProjectionPaddedTailCleanupPostPaddingSourceBits
            false L).map some)
          (none :: padding)) := by
  exact
    FSTStatefulOptionAppendSourceTapeWithPadding_one_eq_tapeAtCells
      (selectedProjectionPaddedTailCleanupPostPaddingSourceBits false L)
      padding

theorem postPaddingSourceWithPadding_eq_deleteBlock_tapeAtCells
    (useAccept : Bool) (L : DovetailLayout)
    (padding : List (Option Bool)) :
    FSTStatefulOptionAppendSourceTapeWithPadding
        (selectedProjectionPaddedTailCleanupPostPaddingSourceBits
          useAccept L)
        1 padding =
      tapeAtCells [none]
        (List.append
          ((selectedProjectionPaddedTailCleanupKeptPrefixBits
            useAccept L).map some)
          (List.append
            ((selectedProjectionPaddedTailCleanupUnselectedConfigBits
              useAccept L).map some)
            (List.append
              ((selectedProjectionPaddedTailCleanupKeptSuffixBits
                useAccept L).map some)
              (none :: padding)))) := by
  rw [FSTStatefulOptionAppendSourceTapeWithPadding_one_eq_tapeAtCells]
  rw [selectedProjectionPaddedTailCleanupPostPaddingSourceBits_eq_deleteBlock]
  simp [List.map_append, List.append_assoc]

theorem postPaddingAcceptSourceWithFivePadding_splitKeptPrefix
    (L : DovetailLayout) :
    exists hitTail : Word Bool,
    exists pref : Word Bool,
    exists leftBit : Bool,
      selectedProjectionPaddedTailCleanupKeptPrefixBits true L =
          List.append pref [leftBit] ∧
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.acceptHit [] =
        false :: hitTail ∧
      FSTStatefulOptionAppendSourceTapeWithPadding
          (selectedProjectionPaddedTailCleanupPostPaddingSourceBits
            true L)
          1 (List.replicate 5 (none : Option Bool)) =
        tapeAtCells [none]
          (List.append (pref.map some)
            (some leftBit ::
              List.append
                ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                  L.rejectConfig []).map some)
                (List.append ((false :: hitTail).map some)
                  (none ::
                    List.replicate 5 (none : Option Bool))))) := by
  rcases selectedProjectionPaddedTailCleanupKeptPrefix_true_append_last
      L with
    ⟨pref, leftBit, hpref⟩
  rcases
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits_cons_false
        (some L.acceptHit) [] with
    ⟨hitTail, hhitTail⟩
  refine ⟨hitTail, pref, leftBit, hpref, ?_, ?_⟩
  · simpa [CanonicalLayouts.DovetailLayoutScanner.boolFieldBits] using
      hhitTail
  · rw [postPaddingSourceWithPadding_eq_deleteBlock_tapeAtCells, hpref]
    have hhit :
        CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            L.acceptHit [] =
          false :: hitTail := by
      simpa [CanonicalLayouts.DovetailLayoutScanner.boolFieldBits] using
        hhitTail
    simp [selectedProjectionPaddedTailCleanupUnselectedConfigBits,
      selectedProjectionPaddedTailCleanupKeptSuffixBits,
      selectedProjectionPaddedTailCleanupSelectedHitBits, hhit,
      List.map_append, List.append_assoc]

theorem rightEdgeRewindDescription_haltsFrom_acceptAfterPadding_tapeAtCells
    (L : DovetailLayout) :
    rightEdgeRewindDescription.HaltsFromTape
      (selectedHitOtherFlagErasedAfterPaddingTape true L)
      (tapeAtCells [none]
        (List.append
          ((selectedProjectionPaddedTailCleanupPostPaddingSourceBits
            true L).map some)
          (none :: List.replicate 5 (none : Option Bool)))) := by
  rw [←
    postPaddingAcceptSourceWithPadding_eq_tapeAtCells
      L (List.replicate 5 (none : Option Bool))]
  exact rightEdgeRewindDescription_haltsFrom_acceptAfterPadding L

theorem rightEdgeRewindDescription_haltsFrom_acceptAfterPadding_splitKeptPrefix
    (L : DovetailLayout) :
    exists hitTail : Word Bool,
    exists pref : Word Bool,
    exists leftBit : Bool,
      selectedProjectionPaddedTailCleanupKeptPrefixBits true L =
          List.append pref [leftBit] ∧
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.acceptHit [] =
        false :: hitTail ∧
      rightEdgeRewindDescription.HaltsFromTape
        (selectedHitOtherFlagErasedAfterPaddingTape true L)
        (tapeAtCells [none]
          (List.append (pref.map some)
            (some leftBit ::
              List.append
                ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                  L.rejectConfig []).map some)
                (List.append ((false :: hitTail).map some)
                  (none ::
                    List.replicate 5 (none : Option Bool)))))) := by
  rcases postPaddingAcceptSourceWithFivePadding_splitKeptPrefix L with
    ⟨hitTail, pref, leftBit, hpref, hhit, htape⟩
  refine ⟨hitTail, pref, leftBit, hpref, hhit, ?_⟩
  rw [← htape]
  exact rightEdgeRewindDescription_haltsFrom_acceptAfterPadding L

theorem rightEndCompactionSourceTape_move_left_move_right_eq_withRightPadding
    (leftCells : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (rightEndCompactionSourceTape leftCells)) =
      rightEndCompactionSourceTapeWithRightPadding
        leftCells [none] := by
  simp [rightEndCompactionSourceTape,
    rightEndCompactionSourceTapeWithRightPadding, tapeAtCells, Tape.move,
    Tape.moveLeft, Tape.moveRight]

theorem rightEndCompactionSourceTapeWithRightPadding_move_left_move_right_cons
    (leftCells : List (Option Bool)) (cell : Option Bool)
    (rightPadding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (rightEndCompactionSourceTapeWithRightPadding
            leftCells (cell :: rightPadding))) =
      rightEndCompactionSourceTapeWithRightPadding
        leftCells (cell :: rightPadding) := by
  simp [rightEndCompactionSourceTapeWithRightPadding, tapeAtCells,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem sentinelGapCompactorDescription_haltsFromTape_gapBase_zero_cons_right
    (gap : Nat) (baseTail : List (Option Bool))
    (leftBit current : Bool) (leftRest : Word Bool)
    (rightPadding : List (Option Bool)) :
    sentinelGapCompactorDescription.HaltsFromTape
      (rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
        (rightBlankLocalGapBaseLeft (Nat.succ gap)
          (some leftBit :: baseTail))
        current leftRest 0 (none :: rightPadding))
      (leadingBlankLeftShiftTargetTapeWithPadding
        (some leftBit :: baseTail) (current :: leftRest).reverse
        (sentinelGapCompactorFinalPadding (Nat.succ gap) 0
          rightPadding)) := by
  rcases
      sentinelGapCompactorDescription_haltsFromTape_gapBase
        gap baseTail leftBit current leftRest 1 rightPadding with
    ⟨n, hn⟩
  let continueSteps : Nat :=
    ((0 + leftRest.length + 3) +
      (1 + (3 * (current :: leftRest).length + 2)))
  refine ⟨continueSteps + n, ?_⟩
  constructor
  · rw [runConfig_add]
    change (sentinelGapCompactorDescription.runConfig n
      (sentinelGapCompactorDescription.runConfig continueSteps
        { state := 0
          tape :=
            rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
              (rightBlankLocalGapBaseLeft (Nat.succ gap)
                (some leftBit :: baseTail))
              current leftRest 0 (none :: rightPadding) })).state =
        sentinelGapCompactorDescription.halt
    rw [show rightBlankLocalGapBaseLeft (Nat.succ gap)
          (some leftBit :: baseTail) =
        none :: rightBlankLocalGapBaseLeft gap
          (some leftBit :: baseTail) by
      exact rightBlankLocalGapBaseLeft_succ gap
        (some leftBit :: baseTail)]
    rw [show continueSteps =
        ((0 + leftRest.length + 3) +
          (1 + (3 * (current :: leftRest).length + 2))) by rfl]
    rw [sentinelGapCompactorDescription_run_continue_pass]
    change (sentinelGapCompactorDescription.runConfig n
      { state := 0
        tape :=
          leadingBlankLeftShiftTargetTapeWithPadding
            (none :: rightBlankLocalGapBaseLeft gap
              (some leftBit :: baseTail))
            (current :: leftRest).reverse
            (none :: rightPadding) }).state =
        sentinelGapCompactorDescription.halt
    rw [leadingBlankLeftShiftTargetTapeWithPadding_eq_nextRightBlankLocalGapSource]
    exact hn.left
  · rw [runConfig_add]
    change (sentinelGapCompactorDescription.runConfig n
      (sentinelGapCompactorDescription.runConfig continueSteps
        { state := 0
          tape :=
            rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
              (rightBlankLocalGapBaseLeft (Nat.succ gap)
                (some leftBit :: baseTail))
              current leftRest 0 (none :: rightPadding) })).tape =
        leadingBlankLeftShiftTargetTapeWithPadding
          (some leftBit :: baseTail) (current :: leftRest).reverse
          (sentinelGapCompactorFinalPadding (Nat.succ gap) 0
            rightPadding)
    rw [show rightBlankLocalGapBaseLeft (Nat.succ gap)
          (some leftBit :: baseTail) =
        none :: rightBlankLocalGapBaseLeft gap
          (some leftBit :: baseTail) by
      exact rightBlankLocalGapBaseLeft_succ gap
        (some leftBit :: baseTail)]
    rw [show continueSteps =
        ((0 + leftRest.length + 3) +
          (1 + (3 * (current :: leftRest).length + 2))) by rfl]
    rw [sentinelGapCompactorDescription_run_continue_pass]
    change (sentinelGapCompactorDescription.runConfig n
      { state := 0
        tape :=
          leadingBlankLeftShiftTargetTapeWithPadding
            (none :: rightBlankLocalGapBaseLeft gap
              (some leftBit :: baseTail))
            (current :: leftRest).reverse
            (none :: rightPadding) }).tape =
        leadingBlankLeftShiftTargetTapeWithPadding
          (some leftBit :: baseTail) (current :: leftRest).reverse
          (sentinelGapCompactorFinalPadding (Nat.succ gap) 0
            rightPadding)
    rw [leadingBlankLeftShiftTargetTapeWithPadding_eq_nextRightBlankLocalGapSource]
    simpa [sentinelGapCompactorFinalPadding] using hn.right

theorem selectedHitOtherFlagErasedRejectAfterPaddingRightEndLeftCells_eq_sourceFields
    (L : DovetailLayout) :
    selectedHitOtherFlagErasedRejectAfterPaddingRightEndLeftCells L =
      List.append [none]
        (List.append
          ((selectedProjectionPaddedTailCleanupPrefixBits L).map some)
          (List.append
            ((selectedProjectionPaddedTailCleanupUnselectedConfigBits
              false L).map some)
            (List.append
              ((selectedProjectionPaddedTailCleanupSelectedConfigBits
                false L).map some)
              (List.append
                (List.replicate 4 (none : Option Bool))
                ((selectedProjectionPaddedTailCleanupSelectedHitBits
                  false L).map some))))) := by
  rw [selectedHitOtherFlagErasedRejectAfterPaddingRightEndLeftCells,
    selectedHitOtherFlagErasedRejectAfterPaddingScanLeft,
    selectedHitOtherFlagErasedRejectBaseLeftRev]
  simp [selectedProjectionPaddedTailCleanupPrefixBits,
    selectedProjectionPaddedTailCleanupUnselectedConfigBits,
    selectedProjectionPaddedTailCleanupSelectedConfigBits,
    selectedProjectionPaddedTailCleanupSelectedHitBits,
    List.reverse_append, List.map_reverse, List.map_append,
    List.append_assoc]

theorem selectedProjectionPaddedTailCleanupDeletedRejectRightEnd_fixedGap_sentinelCompactor_haltsFrom_bridgePadding
    (L : DovetailLayout) :
    sentinelGapCompactorDescription.HaltsFromTape
      (rightEndCompactionSourceTapeWithRightPadding
        (selectedProjectionPaddedTailCleanupDeletedRejectRightEndLeftCells L)
        [none])
      (rightEndCompactionSourceTapeWithRightPadding
        (selectedProjectionPaddedTailCleanupDeletedRejectFixedGapClosedLeftCells
          L)
        (List.replicate 3 (none : Option Bool))) := by
  rcases
      selectedProjectionPaddedTailCleanupSelectedConfig_false_append_last
        L with
    ⟨cfgPref, leftBit, hcfg⟩
  rcases
      selectedProjectionPaddedTailCleanupSelectedHit_false_reverse_cons
        L with
    ⟨current, leftRest, hhitRev⟩
  let baseTail : List (Option Bool) :=
    List.append (cfgPref.reverse.map some)
      (List.append
        (List.replicate
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits
            false L).length
          (none : Option Bool))
        (List.append
          ((selectedProjectionPaddedTailCleanupPrefixBits L).reverse.map
            some)
          [none]))
  have hhit : (current :: leftRest).reverse =
      selectedProjectionPaddedTailCleanupSelectedHitBits false L := by
    rw [← hhitRev]
    simp
  have hsource :
      rightEndCompactionSourceTapeWithRightPadding
          (selectedProjectionPaddedTailCleanupDeletedRejectRightEndLeftCells
            L)
          [none] =
        rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
          (rightBlankLocalGapBaseLeft 3 (some leftBit :: baseTail))
          current leftRest 0 [none] := by
    simp [rightBlankLocalGapCompactorSourceTapeWithBaseAndRight,
      rightEndCompactionSourceTapeWithRightPadding,
      selectedProjectionPaddedTailCleanupDeletedRejectRightEndLeftCells,
      rightBlankLocalGapBaseLeft, baseTail, hcfg, ← hhit,
      tapeAtCells, List.reverse_append, List.map_reverse,
      List.map_append, List.append_assoc]
  have htarget :
      rightEndCompactionSourceTapeWithRightPadding
          (selectedProjectionPaddedTailCleanupDeletedRejectFixedGapClosedLeftCells
            L)
          (List.replicate 3 (none : Option Bool)) =
        leadingBlankLeftShiftTargetTapeWithPadding
          (some leftBit :: baseTail) (current :: leftRest).reverse
          (sentinelGapCompactorFinalPadding 3 0 []) := by
    simp [rightEndCompactionSourceTapeWithRightPadding,
      selectedProjectionPaddedTailCleanupDeletedRejectFixedGapClosedLeftCells,
      leadingBlankLeftShiftTargetTapeWithPadding, baseTail, hcfg,
      ← hhit, sentinelGapCompactorFinalPadding, tapeAtCells,
      List.reverse_append, List.map_reverse, List.map_append,
      List.append_assoc]
  rw [hsource, htarget]
  simpa using
    sentinelGapCompactorDescription_haltsFromTape_gapBase_zero_cons_right
      2 baseTail leftBit current leftRest []

def selectedProjectionPaddedTailCleanupDeletedRejectToSentinelDescription :
    MachineDescription :=
  SeqViaCanonical sentinelGapCompactorDescription
    sentinelRightEndGapCompactorDescription

theorem selectedProjectionPaddedTailCleanupDeletedRejectToSentinelDescription_subroutineReady :
    selectedProjectionPaddedTailCleanupDeletedRejectToSentinelDescription.SubroutineReady :=
  SeqViaCanonical_subroutineReady
    sentinelGapCompactorDescription_subroutineReady
    sentinelRightEndGapCompactorDescription_subroutineReady

theorem selectedProjectionPaddedTailCleanupDeletedRejectToSentinelDescription_haltsFrom
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupDeletedRejectToSentinelDescription.HaltsFromTape
      (rightEndCompactionSourceTapeWithRightPadding
        (selectedProjectionPaddedTailCleanupDeletedRejectRightEndLeftCells L)
        [none])
      (selectedProjectionPaddedTailCleanupRejectSentinelTargetTape L) := by
  exact
    SeqViaCanonical_haltsFromTape_of_haltsFromTape
      sentinelGapCompactorDescription_subroutineReady
      sentinelRightEndGapCompactorDescription_subroutineReady
      (selectedProjectionPaddedTailCleanupDeletedRejectRightEnd_fixedGap_sentinelCompactor_haltsFrom_bridgePadding
        L)
      (rightEndCompactionSourceTapeWithRightPadding_move_left_move_right_cons
        (selectedProjectionPaddedTailCleanupDeletedRejectFixedGapClosedLeftCells
          L)
        none
        (List.replicate 2 (none : Option Bool)))
      (selectedProjectionPaddedTailCleanupDeletedRejectFixedGapClosed_to_rejectSentinelTarget
        L)

theorem postPaddingOutputPrefixAfterStageBase_eq_prefixBits_reverse
    (L : DovetailLayout) :
    postPaddingOutputPrefixAfterStageBase
        (ParsedLayoutBits L) L.stage [none] =
      List.append
        ((selectedProjectionPaddedTailCleanupPrefixBits L).reverse.map some)
        [none] := by
  rw [postPaddingOutputPrefixAfterStageBase_eq_bits_reverse]
  rw [selectedProjectionPaddedTailCleanupPrefixBits]
  rw [SelectedProjectionTailProjector.outputPrefixBits]
  simp [postPaddingOutputPrefixHeaderBase, List.reverse_append,
    List.map_append, List.append_assoc]

theorem postPaddingOutputPrefixStageScannerDescription_rejectSourceBits_handoff_withRight
    (L : DovetailLayout) (rightPadding : List (Option Bool)) :
    exists fieldTail : Word Bool,
      postPaddingOutputPrefixStageScannerDescription.HaltsFromTape
        (tapeAtCells [none]
          (List.append
            ((selectedProjectionPaddedTailCleanupPostPaddingSourceBits
              false L).map some)
            rightPadding))
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
          (List.append
            ((configurationFieldBits L.acceptConfig
              (configurationFieldBits L.rejectConfig
                (boolFieldBits L.rejectHit []))).map some)
            rightPadding) := by
  rcases
      configurationFieldBits_cons_false
        L.acceptConfig
        (configurationFieldBits L.rejectConfig
          (boolFieldBits L.rejectHit [])) with
    ⟨fieldTail, hfieldTail⟩
  refine ⟨fieldTail, ?_, ?_⟩
  · rw [selectedProjectionPaddedTailCleanupPostPaddingSourceBits_false]
    rw [selectedProjectionPaddedTailCleanupPrefixBits]
    rw [SelectedProjectionTailProjector.outputPrefixBits]
    rw [
      configurationFieldBits_append_nil
        L.rejectConfig (boolFieldBits L.rejectHit [])]
    rw [
      configurationFieldBits_append_nil
        L.acceptConfig
        (configurationFieldBits L.rejectConfig
          (boolFieldBits L.rejectHit []))]
    rw [hfieldTail]
    simpa [List.map_append, List.append_assoc] using
      postPaddingOutputPrefixStageScannerDescription_haltsFrom_raw_withRight
        (ParsedLayoutBits L) L.stage [none] fieldTail rightPadding
  · have hmove :=
      postPaddingOutputPrefixStageScannerTarget_move_right_eq_configSource_withRight
        (ParsedLayoutBits L) L.stage [none] fieldTail rightPadding
    rw [postPaddingOutputPrefixAfterStageBase_eq_prefixBits_reverse] at hmove
    rw [hmove, ← hfieldTail]
    simp [DovetailInitialLayoutInitializer.tapeAtCells, tapeAtCells,
      List.map_reverse]
    rfl

theorem postPaddingAcceptConfigRestoredBase_eq_keptPrefix_reverse
    (L : DovetailLayout) :
    configurationRestoredLeftWithBase L.acceptConfig
        (postPaddingOutputPrefixAfterStageBase
          (ParsedLayoutBits L) L.stage [none]) =
      List.append
        ((selectedProjectionPaddedTailCleanupKeptPrefixBits true L).reverse.map
          some)
        [none] := by
  rw [configurationRestoredLeftWithBase_eq_fieldBits_reverse_append]
  rw [postPaddingOutputPrefixAfterStageBase_eq_prefixBits_reverse]
  simp [selectedProjectionPaddedTailCleanupKeptPrefixBits,
    selectedProjectionPaddedTailCleanupSelectedConfigBits,
    List.reverse_append, List.map_append, List.append_assoc]

theorem postPaddingOutputPrefixStageConfigScannerDescription_haltsFrom_acceptSourceBits
    (L : DovetailLayout) :
    exists suffixTail : Word Bool,
      postPaddingOutputPrefixStageConfigScannerDescription.HaltsFromTape
        (tapeAtCells [none]
          ((selectedProjectionPaddedTailCleanupPostPaddingSourceBits
            true L).map some))
        (postPaddingOutputPrefixStageConfigScannerTargetTape
          (ParsedLayoutBits L) L.stage L.acceptConfig [none] suffixTail) := by
  rcases
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_cons_false
        L.rejectConfig
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.acceptHit []) with
    ⟨suffixTail, hsuffix⟩
  refine ⟨suffixTail, ?_⟩
  rw [selectedProjectionPaddedTailCleanupPostPaddingSourceBits_true]
  rw [selectedProjectionPaddedTailCleanupPrefixBits]
  rw [SelectedProjectionTailProjector.outputPrefixBits]
  rw [
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
      L.rejectConfig
      (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
        L.acceptHit [])]
  rw [hsuffix]
  rw [
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
      L.acceptConfig (false :: suffixTail)]
  simpa [List.map_append, List.append_assoc] using
    postPaddingOutputPrefixStageConfigScannerDescription_haltsFrom_raw
      (ParsedLayoutBits L) L.stage L.acceptConfig [none] suffixTail

theorem postPaddingOutputPrefixStageConfigScannerTarget_accept_move_right_eq_unselectedSource
    (L : DovetailLayout) :
    exists suffixTail : Word Bool,
      Tape.move Direction.right
          (postPaddingOutputPrefixStageConfigScannerTargetTape
            (ParsedLayoutBits L) L.stage L.acceptConfig [none]
            suffixTail) =
        tapeAtCells
          (configurationRestoredLeftWithBase L.acceptConfig
            (postPaddingOutputPrefixAfterStageBase
              (ParsedLayoutBits L) L.stage [none]))
          ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.rejectConfig
            (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
              L.acceptHit [])).map some) := by
  rcases
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_cons_false
        L.rejectConfig
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.acceptHit []) with
    ⟨suffixTail, hsuffix⟩
  refine ⟨suffixTail, ?_⟩
  rw [hsuffix]
  exact
    postPaddingOutputPrefixStageConfigScannerTarget_move_right_eq_suffixSource
      (ParsedLayoutBits L) L.stage L.acceptConfig [none] suffixTail

theorem postPaddingOutputPrefixStageConfigScannerDescription_acceptSourceBits_handoff
    (L : DovetailLayout) :
    exists suffixTail : Word Bool,
      postPaddingOutputPrefixStageConfigScannerDescription.HaltsFromTape
        (tapeAtCells [none]
          ((selectedProjectionPaddedTailCleanupPostPaddingSourceBits
            true L).map some))
        (postPaddingOutputPrefixStageConfigScannerTargetTape
          (ParsedLayoutBits L) L.stage L.acceptConfig [none] suffixTail) ∧
      Tape.move Direction.right
          (postPaddingOutputPrefixStageConfigScannerTargetTape
            (ParsedLayoutBits L) L.stage L.acceptConfig [none]
            suffixTail) =
        tapeAtCells
          (List.append
            ((selectedProjectionPaddedTailCleanupKeptPrefixBits
              true L).reverse.map some)
            [none])
          ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.rejectConfig
            (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
              L.acceptHit [])).map some) := by
  rcases
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_cons_false
        L.rejectConfig
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.acceptHit []) with
    ⟨suffixTail, hsuffix⟩
  refine ⟨suffixTail, ?_, ?_⟩
  · rw [selectedProjectionPaddedTailCleanupPostPaddingSourceBits_true]
    rw [selectedProjectionPaddedTailCleanupPrefixBits]
    rw [SelectedProjectionTailProjector.outputPrefixBits]
    rw [
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
        L.rejectConfig
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.acceptHit [])]
    rw [hsuffix]
    rw [
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
        L.acceptConfig (false :: suffixTail)]
    simpa [List.map_append, List.append_assoc] using
      postPaddingOutputPrefixStageConfigScannerDescription_haltsFrom_raw
        (ParsedLayoutBits L) L.stage L.acceptConfig [none] suffixTail
  · rw [hsuffix]
    have hmove :=
      postPaddingOutputPrefixStageConfigScannerTarget_move_right_eq_suffixSource
        (ParsedLayoutBits L) L.stage L.acceptConfig [none] suffixTail
    rw [postPaddingAcceptConfigRestoredBase_eq_keptPrefix_reverse] at hmove
    exact hmove

theorem postPaddingOutputPrefixStageConfigScannerDescription_acceptSourceBits_handoff_splitKeptPrefix
    (L : DovetailLayout) :
    exists scannerTail : Word Bool,
    exists hitTail : Word Bool,
    exists pref : Word Bool,
    exists leftBit : Bool,
      selectedProjectionPaddedTailCleanupKeptPrefixBits true L =
          List.append pref [leftBit] ∧
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.acceptHit [] =
        false :: hitTail ∧
      postPaddingOutputPrefixStageConfigScannerDescription.HaltsFromTape
        (tapeAtCells [none]
          ((selectedProjectionPaddedTailCleanupPostPaddingSourceBits
            true L).map some))
        (postPaddingOutputPrefixStageConfigScannerTargetTape
          (ParsedLayoutBits L) L.stage L.acceptConfig [none]
          scannerTail) ∧
      Tape.move Direction.right
          (postPaddingOutputPrefixStageConfigScannerTargetTape
            (ParsedLayoutBits L) L.stage L.acceptConfig [none]
            scannerTail) =
        tapeAtCells
          (some leftBit ::
            List.append (pref.reverse.map some) [none])
          ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.rejectConfig (false :: hitTail)).map some) := by
  rcases selectedProjectionPaddedTailCleanupKeptPrefix_true_append_last
      L with
    ⟨pref, leftBit, hpref⟩
  rcases
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits_cons_false
        (some L.acceptHit) [] with
    ⟨hitTail, hhitTail⟩
  rcases
      postPaddingOutputPrefixStageConfigScannerDescription_acceptSourceBits_handoff
        L with
    ⟨scannerTail, hscan, hmove⟩
  refine ⟨scannerTail, hitTail, pref, leftBit, hpref, ?_, hscan, ?_⟩
  · simpa [CanonicalLayouts.DovetailLayoutScanner.boolFieldBits] using
      hhitTail
  · rw [hmove, hpref]
    have hhit :
        CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            L.acceptHit [] =
          false :: hitTail := by
      simpa [CanonicalLayouts.DovetailLayoutScanner.boolFieldBits] using
        hhitTail
    rw [hhit]
    simp [List.reverse_append]

theorem postPaddingOutputPrefixStageConfigScannerDescription_acceptSourceBits_handoff_splitKeptPrefix_withRight
    (L : DovetailLayout) (rightPadding : List (Option Bool)) :
    exists scannerTail : Word Bool,
    exists hitTail : Word Bool,
    exists pref : Word Bool,
    exists leftBit : Bool,
      selectedProjectionPaddedTailCleanupKeptPrefixBits true L =
          List.append pref [leftBit] ∧
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.acceptHit [] =
        false :: hitTail ∧
      postPaddingOutputPrefixStageConfigScannerDescription.HaltsFromTape
        (tapeAtCells [none]
          (List.append
            ((selectedProjectionPaddedTailCleanupPostPaddingSourceBits
              true L).map some)
            rightPadding))
        (postPaddingOutputPrefixStageConfigScannerTargetTapeWithRight
          (ParsedLayoutBits L) L.stage L.acceptConfig [none]
          scannerTail rightPadding) ∧
      Tape.move Direction.right
          (postPaddingOutputPrefixStageConfigScannerTargetTapeWithRight
            (ParsedLayoutBits L) L.stage L.acceptConfig [none]
            scannerTail rightPadding) =
        tapeAtCells
          (some leftBit ::
            List.append (pref.reverse.map some) [none])
          (List.append
            ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.rejectConfig (false :: hitTail)).map some)
            rightPadding) := by
  rcases selectedProjectionPaddedTailCleanupKeptPrefix_true_append_last
      L with
    ⟨pref, leftBit, hpref⟩
  rcases
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits_cons_false
        (some L.acceptHit) [] with
    ⟨hitTail, hhitTail⟩
  rcases
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_cons_false
        L.rejectConfig
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.acceptHit []) with
    ⟨scannerTail, hscannerTail⟩
  refine ⟨scannerTail, hitTail, pref, leftBit, hpref, ?_, ?_, ?_⟩
  · simpa [CanonicalLayouts.DovetailLayoutScanner.boolFieldBits] using
      hhitTail
  · rw [selectedProjectionPaddedTailCleanupPostPaddingSourceBits_true]
    rw [selectedProjectionPaddedTailCleanupPrefixBits]
    rw [SelectedProjectionTailProjector.outputPrefixBits]
    rw [
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
        L.rejectConfig
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.acceptHit [])]
    rw [hscannerTail]
    rw [
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
        L.acceptConfig (false :: scannerTail)]
    simpa [List.map_append, List.append_assoc] using
      postPaddingOutputPrefixStageConfigScannerDescription_haltsFrom_raw_withRight
        (ParsedLayoutBits L) L.stage L.acceptConfig [none]
        scannerTail rightPadding
  · have hmove :=
      postPaddingOutputPrefixStageConfigScannerTarget_move_right_eq_suffixSource_withRight
        (ParsedLayoutBits L) L.stage L.acceptConfig [none]
        scannerTail rightPadding
    rw [postPaddingAcceptConfigRestoredBase_eq_keptPrefix_reverse] at hmove
    rw [hmove, hpref]
    have hhit :
        CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            L.acceptHit [] =
          false :: hitTail := by
      simpa [CanonicalLayouts.DovetailLayoutScanner.boolFieldBits] using
        hhitTail
    rw [← hscannerTail]
    rw [hhit]
    simp [DovetailInitialLayoutInitializer.tapeAtCells, tapeAtCells,
      List.reverse_append]
    rfl

theorem postPaddingOutputPrefixStageConfigScannerDescription_haltsFrom_rejectSourceBits
    (L : DovetailLayout) :
    exists suffixTail : Word Bool,
      postPaddingOutputPrefixStageConfigScannerDescription.HaltsFromTape
        (tapeAtCells [none]
          ((selectedProjectionPaddedTailCleanupPostPaddingSourceBits
            false L).map some))
        (postPaddingOutputPrefixStageConfigScannerTargetTape
          (ParsedLayoutBits L) L.stage L.acceptConfig [none] suffixTail) := by
  rcases
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_cons_false
        L.rejectConfig
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.rejectHit []) with
    ⟨suffixTail, hsuffix⟩
  refine ⟨suffixTail, ?_⟩
  rw [selectedProjectionPaddedTailCleanupPostPaddingSourceBits_false]
  rw [selectedProjectionPaddedTailCleanupPrefixBits]
  rw [SelectedProjectionTailProjector.outputPrefixBits]
  rw [
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
      L.rejectConfig
      (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
        L.rejectHit [])]
  rw [hsuffix]
  rw [
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
      L.acceptConfig (false :: suffixTail)]
  simpa [List.map_append, List.append_assoc] using
    postPaddingOutputPrefixStageConfigScannerDescription_haltsFrom_raw
      (ParsedLayoutBits L) L.stage L.acceptConfig [none] suffixTail

theorem postPaddingOutputPrefixStageConfigScannerTarget_reject_move_right_eq_selectedSource
    (L : DovetailLayout) :
    exists suffixTail : Word Bool,
      Tape.move Direction.right
          (postPaddingOutputPrefixStageConfigScannerTargetTape
            (ParsedLayoutBits L) L.stage L.acceptConfig [none]
            suffixTail) =
        tapeAtCells
          (configurationRestoredLeftWithBase L.acceptConfig
            (postPaddingOutputPrefixAfterStageBase
              (ParsedLayoutBits L) L.stage [none]))
          ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.rejectConfig
            (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
              L.rejectHit [])).map some) := by
  rcases
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_cons_false
        L.rejectConfig
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.rejectHit []) with
    ⟨suffixTail, hsuffix⟩
  refine ⟨suffixTail, ?_⟩
  rw [hsuffix]
  exact
    postPaddingOutputPrefixStageConfigScannerTarget_move_right_eq_suffixSource
      (ParsedLayoutBits L) L.stage L.acceptConfig [none] suffixTail

theorem postPaddingOutputPrefixStageConfigScannerDescription_rejectSourceBits_handoff
    (L : DovetailLayout) :
    exists suffixTail : Word Bool,
      postPaddingOutputPrefixStageConfigScannerDescription.HaltsFromTape
        (tapeAtCells [none]
          ((selectedProjectionPaddedTailCleanupPostPaddingSourceBits
            false L).map some))
        (postPaddingOutputPrefixStageConfigScannerTargetTape
          (ParsedLayoutBits L) L.stage L.acceptConfig [none] suffixTail) ∧
      Tape.move Direction.right
          (postPaddingOutputPrefixStageConfigScannerTargetTape
            (ParsedLayoutBits L) L.stage L.acceptConfig [none]
            suffixTail) =
        tapeAtCells
          (List.append
            ((List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
              (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                false L)).reverse.map some)
            [none])
          ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.rejectConfig
            (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
              L.rejectHit [])).map some) := by
  rcases
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_cons_false
        L.rejectConfig
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.rejectHit []) with
    ⟨suffixTail, hsuffix⟩
  refine ⟨suffixTail, ?_, ?_⟩
  · rw [selectedProjectionPaddedTailCleanupPostPaddingSourceBits_false]
    rw [selectedProjectionPaddedTailCleanupPrefixBits]
    rw [SelectedProjectionTailProjector.outputPrefixBits]
    rw [
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
        L.rejectConfig
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.rejectHit [])]
    rw [hsuffix]
    rw [
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
        L.acceptConfig (false :: suffixTail)]
    simpa [List.map_append, List.append_assoc] using
      postPaddingOutputPrefixStageConfigScannerDescription_haltsFrom_raw
        (ParsedLayoutBits L) L.stage L.acceptConfig [none] suffixTail
  · rw [hsuffix]
    have hmove :=
      postPaddingOutputPrefixStageConfigScannerTarget_move_right_eq_suffixSource
        (ParsedLayoutBits L) L.stage L.acceptConfig [none] suffixTail
    rw [postPaddingAcceptConfigRestoredBase_eq_keptPrefix_reverse] at hmove
    simpa [selectedProjectionPaddedTailCleanupKeptPrefixBits,
      selectedProjectionPaddedTailCleanupSelectedConfigBits,
      selectedProjectionPaddedTailCleanupUnselectedConfigBits,
      List.append_assoc] using hmove

theorem postPaddingOutputPrefixStageConfigScannerDescription_rejectSourceBits_handoff_withRight
    (L : DovetailLayout) (rightPadding : List (Option Bool)) :
    exists suffixTail : Word Bool,
      postPaddingOutputPrefixStageConfigScannerDescription.HaltsFromTape
        (tapeAtCells [none]
          (List.append
            ((selectedProjectionPaddedTailCleanupPostPaddingSourceBits
              false L).map some)
            rightPadding))
        (postPaddingOutputPrefixStageConfigScannerTargetTapeWithRight
          (ParsedLayoutBits L) L.stage L.acceptConfig [none]
          suffixTail rightPadding) ∧
      Tape.move Direction.right
          (postPaddingOutputPrefixStageConfigScannerTargetTapeWithRight
            (ParsedLayoutBits L) L.stage L.acceptConfig [none]
            suffixTail rightPadding) =
        tapeAtCells
          (List.append
            ((List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
              (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                false L)).reverse.map some)
            [none])
          (List.append
            ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.rejectConfig
              (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                L.rejectHit [])).map some)
            rightPadding) := by
  rcases
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_cons_false
        L.rejectConfig
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.rejectHit []) with
    ⟨suffixTail, hsuffix⟩
  refine ⟨suffixTail, ?_, ?_⟩
  · rw [selectedProjectionPaddedTailCleanupPostPaddingSourceBits_false]
    rw [selectedProjectionPaddedTailCleanupPrefixBits]
    rw [SelectedProjectionTailProjector.outputPrefixBits]
    rw [
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
        L.rejectConfig
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.rejectHit [])]
    rw [hsuffix]
    rw [
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
        L.acceptConfig (false :: suffixTail)]
    simpa [List.map_append, List.append_assoc] using
      postPaddingOutputPrefixStageConfigScannerDescription_haltsFrom_raw_withRight
        (ParsedLayoutBits L) L.stage L.acceptConfig [none]
        suffixTail rightPadding
  · have hmove :=
      postPaddingOutputPrefixStageConfigScannerTarget_move_right_eq_suffixSource_withRight
        (ParsedLayoutBits L) L.stage L.acceptConfig [none]
        suffixTail rightPadding
    rw [postPaddingAcceptConfigRestoredBase_eq_keptPrefix_reverse] at hmove
    rw [hmove]
    rw [← hsuffix]
    simp [DovetailInitialLayoutInitializer.tapeAtCells, tapeAtCells,
      selectedProjectionPaddedTailCleanupKeptPrefixBits,
      selectedProjectionPaddedTailCleanupSelectedConfigBits,
      selectedProjectionPaddedTailCleanupUnselectedConfigBits,
      List.map_append, List.append_assoc]
    rfl

/--
Combined post-padding finite-machine leaf for selected-projection tail cleanup.
The branch wrappers below project this single obligation into the accepting and
rejecting branch contracts.
-/
theorem selectedProjectionPaddedTailCleanupPostPaddingCoreConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingConstruction := by
  sorry

def selectedHitOtherFlagErasedPostEraseFromPostPadding
    (useAccept : Bool) (postPadding : MachineDescription) :
    MachineDescription :=
  if useAccept then
    SeqViaCanonical skipCurrentAndFourBlankPaddingLeftDescription
      postPadding
  else
    SeqViaCanonical skipCurrentAndFourBlankPaddingRightDescription
      postPadding

theorem selectedProjectionPaddedTailCleanupPostEraseSpec_of_postPadding
    {useAccept : Bool} {postPadding : MachineDescription}
    (hpostPadding :
      SelectedProjectionPaddedTailCleanupPostPaddingSpec
        useAccept postPadding) :
    SelectedProjectionPaddedTailCleanupPostEraseSpec useAccept
      (selectedHitOtherFlagErasedPostEraseFromPostPadding
        useAccept postPadding) := by
  cases useAccept
  · constructor
    · simpa [selectedHitOtherFlagErasedPostEraseFromPostPadding] using
        SeqViaCanonical_subroutineReady
          skipCurrentAndFourBlankPaddingRightDescription_subroutineReady
          hpostPadding.left
    · intro L
      exact
        SeqViaCanonical_haltsFromTape_of_haltsFromTape
          skipCurrentAndFourBlankPaddingRightDescription_subroutineReady
          hpostPadding.left
          (skipCurrentAndFourBlankPaddingRightDescription_haltsFrom_rejectHandoff_named
            L)
          (by
            simpa [selectedHitOtherFlagErasedAfterPaddingTape] using
              selectedHitOtherFlagErasedAfterPaddingTape_move_left_move_right
                false L)
          (by
            simpa [selectedHitOtherFlagErasedAfterPaddingTape] using
              hpostPadding.right L)
  · constructor
    · simpa [selectedHitOtherFlagErasedPostEraseFromPostPadding] using
        SeqViaCanonical_subroutineReady
          skipCurrentAndFourBlankPaddingLeftDescription_subroutineReady
          hpostPadding.left
    · intro L
      exact
        SeqViaCanonical_haltsFromTape_of_haltsFromTape
          skipCurrentAndFourBlankPaddingLeftDescription_subroutineReady
          hpostPadding.left
          (skipCurrentAndFourBlankPaddingLeftDescription_haltsFrom_acceptHandoff
            L)
          (by
            simpa [selectedHitOtherFlagErasedAfterPaddingTape] using
              selectedHitOtherFlagErasedAfterPaddingTape_move_left_move_right
                true L)
          (by
            simpa [selectedHitOtherFlagErasedAfterPaddingTape] using
              hpostPadding.right L)

theorem selectedProjectionPaddedTailCleanupPostEraseConstruction_of_postPadding
    (h :
      SelectedProjectionPaddedTailCleanupPostPaddingConstruction) :
    SelectedProjectionPaddedTailCleanupPostEraseConstruction := by
  intro useAccept
  rcases h useAccept with ⟨postPadding, hpostPadding⟩
  exact
    ⟨selectedHitOtherFlagErasedPostEraseFromPostPadding
        useAccept postPadding,
      selectedProjectionPaddedTailCleanupPostEraseSpec_of_postPadding
        hpostPadding⟩

/--
Post-padding finite-machine leaf for selected-projection tail cleanup on the
accepting projection branch.
-/
theorem selectedProjectionPaddedTailCleanupPostPaddingAcceptConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingBranchConstruction true := by
  exact selectedProjectionPaddedTailCleanupPostPaddingCoreConstruction true

/--
Post-padding finite-machine leaf for selected-projection tail cleanup on the
rejecting projection branch.
-/
theorem selectedProjectionPaddedTailCleanupPostPaddingRejectConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingBranchConstruction false := by
  exact selectedProjectionPaddedTailCleanupPostPaddingCoreConstruction false

theorem selectedProjectionPaddedTailCleanupPostPaddingConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingConstruction :=
  selectedProjectionPaddedTailCleanupPostPaddingConstruction_of_branches
    selectedProjectionPaddedTailCleanupPostPaddingAcceptConstruction
    selectedProjectionPaddedTailCleanupPostPaddingRejectConstruction

theorem selectedProjectionPaddedTailCleanupPostEraseConstruction :
    SelectedProjectionPaddedTailCleanupPostEraseConstruction :=
  selectedProjectionPaddedTailCleanupPostEraseConstruction_of_postPadding
    selectedProjectionPaddedTailCleanupPostPaddingConstruction

end SelectedProjectionPaddedTailCleanup

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
