import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.PostPaddingCloseout

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner
/--
Finite-machine leaf for the selected-projection tail cleanup.  The reusable
stage/configuration/final-flag scanner has already consumed the remaining
layout fields and handed off one cell to the right; this cleanup may leave
trailing blank padding while emitting a tape equivalent to the right-shifted
selected simulator-layout output.
-/
theorem selectedProjectionPaddedTailCleanupExactShapeConstruction_scaffold :
    SelectedProjectionPaddedTailCleanupExactShapeConstruction := by
  intro useAccept
  rcases
      SelectedProjectionPaddedTailCleanup.selectedProjectionPaddedTailCleanupPostEraseConstruction
        useAccept with
    ⟨postErase, hpostErase⟩
  refine
    ⟨SeqViaCanonical
      (SelectedProjectionPaddedTailCleanup.selectedHitOtherFlagErasedFromScannerDescription
        useAccept)
      postErase, ?_⟩
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        (SelectedProjectionPaddedTailCleanup.selectedHitOtherFlagErasedFromScannerDescription_subroutineReady
          useAccept)
        hpostErase.left
  · intro L
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        (SelectedProjectionPaddedTailCleanup.selectedHitOtherFlagErasedFromScannerDescription_subroutineReady
          useAccept)
        hpostErase.left
        (SelectedProjectionPaddedTailCleanup.selectedHitOtherFlagErasedFromScannerDescription_haltsFrom_sourceScannerRightHandoffTape
          useAccept L)
        (by
          rfl)
        (hpostErase.right L)

theorem selectedProjectionPaddedTailCleanupConstruction_scaffold :
    SelectedProjectionPaddedTailCleanupConstruction :=
  selectedProjectionPaddedTailCleanupConstruction_of_exactShape
    selectedProjectionPaddedTailCleanupExactShapeConstruction_scaffold

theorem selectedProjectionPaddedTailEmitterConstruction_scaffold :
    SelectedProjectionPaddedTailEmitterConstruction :=
  selectedProjectionPaddedTailEmitterConstruction_of_cleanup
    selectedProjectionPaddedTailCleanupConstruction_scaffold


end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
