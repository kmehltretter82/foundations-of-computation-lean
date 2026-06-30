import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Merge.Padded.PostTransition

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
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
        simpa [SelectedMergePaddedEmitterAfterHeaderRightHandoffTape] using
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
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        selectedMergePaddedEmitterAfterHeaderScanner_subroutineReady
        hafterHit.left
        (selectedMergePaddedEmitterAfterHeaderScanner_haltsFromPayload p)
        (by
          rfl)
        (hafterHit.right p)

/--
Finite-machine leaf for selected merge under the equivalence-based phase
contract.  It emits the merged dovetail-layout code at the left edge and leaves
blank padding in the old simulator-layout window, so the exact tape is
equivalent to the unshifted merged dovetail-layout tape without requiring a
context-length decrease.
-/
theorem selectedMergePaddedEmitterExactShapeConstruction_scaffold :
    SelectedMergePaddedEmitterExactShapeConstruction := by
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
      CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
        selectedMergePaddedEmitterHeaderRewriter_subroutineReady
        hpostHeader.left
        (selectedMergePaddedEmitterHeaderRewriter_haltsFromPayload p)
        (by
          rfl)
        (hpostHeader.right p)

theorem selectedMergeEquivPaddedEmitterConstruction_scaffold :
    SelectedMergeEquivPaddedEmitterConstruction :=
  selectedMergeEquivPaddedEmitterConstruction_of_exactShape
    selectedMergePaddedEmitterExactShapeConstruction_scaffold

theorem selectedMergeEquivEmitterConstruction_scaffold :
    SelectedMergeEquivEmitterConstruction :=
  selectedMergeEquivEmitterConstruction_of_padded
    selectedMergeEquivPaddedEmitterConstruction_scaffold

theorem selectedMergeEquivConstruction_scaffold :
    SelectedMergeEquivConstruction :=
  selectedMergeEquivConstruction_of_forwardParser_paddedEmitter
    selectedMergeForwardParserConstruction_scaffold
    selectedMergeEquivPaddedEmitterConstruction_scaffold


end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
