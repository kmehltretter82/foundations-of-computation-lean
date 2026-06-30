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
