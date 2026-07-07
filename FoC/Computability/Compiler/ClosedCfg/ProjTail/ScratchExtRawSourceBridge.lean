import FoC.Computability.Compiler.FST.CountWindow
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchExtCountWindow

set_option doc.verso true

/-!
# Count-window raw-source encoder bridge

This projection-side module adapts the common count-window raw-source encoder
construction to the selected-projection scratch-count window shape.  Keeping
this bridge here avoids importing selected-projection layout machinery into the
lower-level
{module}`FoC.Computability.Compiler.FST.CountWindow`.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

open CanonicalLayouts.DovetailLayoutScanner

theorem selectedProjectionPaddedTailCleanupPostCountTailCells_zero_append_replicate_bridge
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    List.append
        (selectedProjectionPaddedTailCleanupPostCountTailCells
          useAccept L 0)
        (List.replicate extraScratch (none : Option Bool)) =
      selectedProjectionPaddedTailCleanupPostCountTailCells
        useAccept L extraScratch := by
  cases useAccept <;>
    simp [selectedProjectionPaddedTailCleanupPostCountTailCells,
      selectedProjectionPaddedTailCleanupAcceptPostCountTailCells,
      selectedProjectionPaddedTailCleanupRejectPostCountTailCells,
      selectedProjectionPaddedTailCleanupAcceptAfterStageTailCells,
      selectedProjectionPaddedTailCleanupRejectAfterStageTailCells,
      selectedProjectionPaddedTailCleanupAcceptAfterStageTailCells,
      selectedProjectionPaddedTailCleanupRejectAfterStageTailCells,
      List.append_assoc]

theorem selectedProjectionPaddedTailCleanupScratchCountWindowRawSourceEncoderConstruction_of_countWindowRawSourceEncoder_bridge
    (hencoder : CountWindowRawSourceEncoderEquivConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRawSourceEncoderConstruction := by
  rcases hencoder with ⟨encoder, hencoderSpec⟩
  intro useAccept
  exact
    ⟨encoder,
      hencoderSpec.left,
      fun L => by
        have hsplit :
            ParsedLayoutBits L =
              List.append
                (selectedProjectionPaddedTailCleanupScratchSkippedBits
                  useAccept L)
                (selectedProjectionPaddedTailCleanupScratchCountBits
                  useAccept L) :=
          selectedProjectionPaddedTailCleanupParsedLayoutBits_eq_skipped_append_count
            useAccept L
        rcases
            selectedProjectionPaddedTailCleanupPostCountTailCells_cons_false
              useAccept L 0 with
          ⟨postCountTail, hpostCountTail⟩
        have htail :
            List.append
                (some false :: postCountTail)
                (List.replicate
                  (selectedProjectionPaddedTailCleanupScratchCountBits
                    useAccept L).length
                  (none : Option Bool)) =
              selectedProjectionPaddedTailCleanupPostCountTailCells
                useAccept L
                (selectedProjectionPaddedTailCleanupScratchCountBits
                  useAccept L).length := by
          rw [← hpostCountTail]
          exact
            selectedProjectionPaddedTailCleanupPostCountTailCells_zero_append_replicate_bridge
              useAccept L
              (selectedProjectionPaddedTailCleanupScratchCountBits
                useAccept L).length
        have hrun :=
          hencoderSpec.right
            (selectedProjectionPaddedTailCleanupScratchSkippedBits
              useAccept L)
            (selectedProjectionPaddedTailCleanupScratchCountBits
              useAccept L)
            false
            postCountTail
        have hsource :
            countWindowRawSourceEncoderSourceTape
                (selectedProjectionPaddedTailCleanupScratchSkippedBits
                  useAccept L)
                (selectedProjectionPaddedTailCleanupScratchCountBits
                  useAccept L)
                (some false :: postCountTail) =
              selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithExtraCountBlank
                useAccept L 0 := by
          simp [selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithExtraCountBlank,
            countWindowRawSourceEncoderSourceTape,
            hsplit, hpostCountTail, List.map_append, List.append_assoc]
        have htarget :
            countWindowRawSourceEncoderTargetTape
                (selectedProjectionPaddedTailCleanupScratchSkippedBits
                  useAccept L)
                (selectedProjectionPaddedTailCleanupScratchCountBits
                  useAccept L)
                (some false :: postCountTail) =
              selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
                useAccept L
                (selectedProjectionPaddedTailCleanupScratchCountBits
                  useAccept L).length := by
          unfold countWindowRawSourceEncoderTargetTape
          rw [htail]
          cases useAccept <;>
            simp [
              selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch_countSplit,
              selectedProjectionPaddedTailCleanupEncodedCountWindowSourceCells,
              selectedProjectionPaddedTailCleanupEncodedHeaderCells,
              selectedProjectionPaddedTailCleanupEncodedLayoutLengthCells,
              selectedProjectionPaddedTailCleanupEncodedScratchSkippedCells,
              selectedProjectionPaddedTailCleanupEncodedScratchCountCells,
              selectedProjectionPaddedTailCleanupPostCountTailCells,
              selectedProjectionPaddedTailCleanupAcceptPostCountTailCells,
              selectedProjectionPaddedTailCleanupRejectPostCountTailCells,
              selectedProjectionPaddedTailCleanupAcceptAfterStageTailCells,
              selectedProjectionPaddedTailCleanupRejectAfterStageTailCells,
              countWindowRawSourceEncoderHeaderCells,
              countWindowRawSourceEncoderLayoutLengthCells,
              countWindowRawSourceEncoderCellFieldCells,
              hsplit]
        rw [← hsource, ← htarget]
        exact hrun⟩

theorem selectedProjectionPaddedTailCleanupScratchCountWindowRawSourceEncoderConstruction_countWindowRawSourceEncoderBridge :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRawSourceEncoderConstruction := by
  exact
    selectedProjectionPaddedTailCleanupScratchCountWindowRawSourceEncoderConstruction_of_countWindowRawSourceEncoder_bridge
      countWindowRawSourceEncoderEquivConstruction_core

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
