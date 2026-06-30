import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.PostPaddingRejectRoute

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

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
