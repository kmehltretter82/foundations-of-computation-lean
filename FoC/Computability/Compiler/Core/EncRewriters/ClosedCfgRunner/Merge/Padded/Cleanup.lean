import FoC.Computability.Compiler.ClosedCfg.PostTrans

set_option doc.verso true

/-!
This module packages the padded merge emitter cleanup after a selected
transition has been processed. It connects the post-transition route,
hit-rewind route, and final right-handoff into the exact-shape construction
used by the closed configuration runner.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

def SelectedMergePaddedEmitterAfterHeaderScannerDescription :
    MachineDescription :=
  SeqViaCanonical SelectedMergePaddedEmitterCleanup.leftMoveOnceDescription
    SelectedMergePaddedEmitterSourceScannerDescription

theorem selectedMergePaddedEmitterAfterHeaderScanner_subroutineReady :
    SelectedMergePaddedEmitterAfterHeaderScannerDescription.SubroutineReady :=
  SeqViaCanonical_subroutineReady
    SelectedMergePaddedEmitterCleanup.leftMoveOnceDescription_subroutineReady
    selectedMergePaddedEmitterSourceScanner_subroutineReady

theorem selectedMergePaddedEmitterAfterHeaderScanner_haltsFromPayload
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterAfterHeaderScannerDescription.HaltsFromTape
      (SelectedMergePaddedEmitterAfterHeaderRightHandoffTape p)
      (SelectedMergePaddedEmitterAfterHitTape p) := by
  exact
    SeqViaCanonical_haltsFromTape_of_haltsFromTape
      SelectedMergePaddedEmitterCleanup.leftMoveOnceDescription_subroutineReady
      selectedMergePaddedEmitterSourceScanner_subroutineReady
      (SelectedMergePaddedEmitterCleanup.leftMoveOnceDescription_haltsFromTape
        (SelectedMergePaddedEmitterAfterHeaderRightHandoffTape p))
      (by
        simpa [SelectedMergePaddedEmitterAfterHeaderRightHandoffTape] using!
          selectedMergePaddedEmitterAfterHeaderTape_move_left_move_right p)
      (selectedMergePaddedEmitterSourceScanner_haltsFromPayload p)

theorem selectedMergePaddedEmitterAfterTransitionPaddedConstruction :
    SelectedMergePaddedEmitterAfterTransitionPaddedConstruction :=
  selectedMergePaddedEmitterAfterTransitionPaddedConstruction_of_branches
    selectedMergePaddedEmitterAfterTransitionPaddedAcceptConstruction
    selectedMergePaddedEmitterAfterTransitionPaddedRejectConstruction

/--
Post-rewind finite-machine leaf for selected merge under the padded equivalence
contract.  A checked transition-prefix skipper reduces this to the
post-transition padded obligation above.
-/
theorem selectedMergePaddedEmitterAfterHitRewindConstruction :
    SelectedMergePaddedEmitterAfterHitRewindConstruction :=
  SelectedMergePaddedEmitterAfterHitRewindConstruction_of_afterTransition
    selectedMergePaddedEmitterAfterTransitionPaddedConstruction

/--
Post-scan finite-machine leaf for selected merge under the padded equivalence
contract.  The source fields have been scanned and restored; the sequential
adapter has performed its canonical right-left handoff from the after-hit tape.
The reusable rewind prefix reduces the remaining machine to the post-rewind
emitter obligation above.
-/
theorem selectedMergePaddedEmitterAfterHitRightLeftHandoffConstruction :
    SelectedMergePaddedEmitterAfterHitRightLeftHandoffConstruction :=
  SelectedMergePaddedEmitterAfterHitRightLeftHandoffConstruction_of_rewind
    selectedMergePaddedEmitterAfterHitRewindConstruction

theorem selectedMergePaddedEmitterAfterHeaderRightHandoffConstruction :
    SelectedMergePaddedEmitterAfterHeaderRightHandoffConstruction := by
  intro useAccept
  rcases
      selectedMergePaddedEmitterAfterHitRightLeftHandoffConstruction
        useAccept with
    ⟨afterHit, hafterHit⟩
  refine
    ⟨SeqViaCanonical
      SelectedMergePaddedEmitterAfterHeaderScannerDescription
      afterHit, ?_⟩
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        selectedMergePaddedEmitterAfterHeaderScanner_subroutineReady
        hafterHit.left
  · intro p
    exact
      SeqViaCanonical_haltsFromTapeEquiv_of_haltsFromTape_handoff
        selectedMergePaddedEmitterAfterHeaderScanner_subroutineReady
        hafterHit.left
        (selectedMergePaddedEmitterAfterHeaderScanner_haltsFromPayload p)
        (by
          rfl)
        (hafterHit.right p)

theorem selectedMergeEquivConstruction_scaffold :
    SelectedMergeEquivConstruction :=
  selectedMergeEquivConstruction_of_forwardParser_emitter
    selectedMergeForwardParserConstruction_scaffold
    (selectedMergeEquivEmitterConstruction_of_exactShape
      (by
        intro useAccept
        rcases
            selectedMergePaddedEmitterAfterHeaderRightHandoffConstruction
              useAccept with
          ⟨postHeader, hpostHeader⟩
        refine
          ⟨seqSubroutine
            SelectedMergePaddedEmitterHeaderRewriterDescription
            postHeader Direction.right, ?_⟩
        constructor
        · exact
            seqSubroutine_subroutineReady
              selectedMergePaddedEmitterHeaderRewriter_subroutineReady
              hpostHeader.left
        · intro p
          exact
            CommonGround.SeqComposition.seqSubroutine_haltsFromTapeEquiv_of_haltsFromTape_eq
              selectedMergePaddedEmitterHeaderRewriter_subroutineReady
              hpostHeader.left
              (selectedMergePaddedEmitterHeaderRewriter_haltsFromPayload p)
              (by
                rfl)
              (hpostHeader.right p)))


end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
