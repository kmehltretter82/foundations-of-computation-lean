import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.PostPaddingCloseout

set_option doc.verso true

/-!
This module assembles the padded selected-projection tail cleanup from its
source rewind, hit detection, erasure, post-padding, and closeout stages. It is
the scaffold that turns the named component constructions into the construction
consumed by the padded projection emitter.
-/

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
theorem selectedProjectionPaddedTailEmitterConstruction_scaffold :
    SelectedProjectionPaddedTailEmitterConstruction :=
  selectedProjectionPaddedTailEmitterConstruction_of_cleanup
    (selectedProjectionPaddedTailCleanupConstruction_of_exactShape
      (by
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
            SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
              (SelectedProjectionPaddedTailCleanup.selectedHitOtherFlagErasedFromScannerDescription_subroutineReady
                useAccept)
              hpostErase.left
              (SelectedProjectionPaddedTailCleanup.selectedHitOtherFlagErasedFromScannerDescription_haltsFrom_sourceScannerRightHandoffTape
                useAccept L).toEquiv
              (by
                exact Tape.Equiv.refl _)
              (hpostErase.right L)))


end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
