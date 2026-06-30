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
