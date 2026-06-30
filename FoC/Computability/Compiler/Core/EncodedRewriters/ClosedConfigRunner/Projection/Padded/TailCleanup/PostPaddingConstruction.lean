import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.PostPaddingFramework

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncodedRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

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

theorem selectedProjectionPaddedTailCleanupDeletedAcceptRightEnd_to_acceptSentinelTarget
    (L : DovetailLayout) :
    sentinelRightEndGapCompactorDescription.HaltsFromTape
      (rightEndCompactionSourceTape
        (selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells L))
      (selectedProjectionPaddedTailCleanupAcceptSentinelTargetTape L) := by
  simpa [selectedProjectionPaddedTailCleanupAcceptSentinelTargetTape] using
    selectedProjectionPaddedTailCleanupDeletedAcceptRightEnd_sentinelCompactor_haltsFrom
      L

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
