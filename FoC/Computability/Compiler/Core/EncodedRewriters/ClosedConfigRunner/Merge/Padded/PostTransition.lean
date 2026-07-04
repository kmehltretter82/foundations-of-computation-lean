import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Merge.Padded.PostTransition.BranchContracts
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Merge.Padded.PostTransition.NestedLayoutParser

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

/-!
# Padded merge post-transition wrapper

This wrapper composes the post-transition core shape lemmas with the
nested-layout parser and branch-parametric parsed-inner finite-machine leaves.
-/

theorem selectedMergePaddedEmitterAfterHitPaddedAcceptSourceFieldsConstruction :
    SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsConstruction true := by
  exact
    selectedMergePaddedEmitterAfterHitPaddedSourceFieldsConstruction_of_parsedInner
      selectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedConstruction
      (selectedMergePaddedEmitterAfterHitPaddedParsedInnerConstruction true)

theorem selectedMergePaddedEmitterAfterHitPaddedRejectSourceFieldsConstruction :
    SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsConstruction false := by
  exact
    selectedMergePaddedEmitterAfterHitPaddedSourceFieldsConstruction_of_parsedInner
      selectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedConstruction
      (selectedMergePaddedEmitterAfterHitPaddedParsedInnerConstruction false)

theorem selectedMergePaddedEmitterAfterHitPaddedAcceptDecodedConstruction :
    SelectedMergePaddedEmitterAfterHitPaddedDecodedConstruction true := by
  exact
    selectedMergePaddedEmitterAfterHitPaddedDecodedConstruction_of_sourceFields
      selectedMergePaddedEmitterAfterHitPaddedAcceptSourceFieldsConstruction

theorem selectedMergePaddedEmitterAfterHitPaddedRejectDecodedConstruction :
    SelectedMergePaddedEmitterAfterHitPaddedDecodedConstruction false := by
  exact
    selectedMergePaddedEmitterAfterHitPaddedDecodedConstruction_of_sourceFields
      selectedMergePaddedEmitterAfterHitPaddedRejectSourceFieldsConstruction

/--
Post-source-scanner finite-machine leaf for selected merge under the accepting
padded equivalence branch.
-/
theorem selectedMergePaddedEmitterAfterHitPaddedAcceptConstruction :
    SelectedMergePaddedEmitterAfterHitPaddedBranchConstruction true := by
  exact
    selectedMergePaddedEmitterAfterHitPaddedConstruction_of_decoded
      selectedMergePaddedEmitterAfterHitPaddedAcceptDecodedConstruction

/--
Post-source-scanner finite-machine leaf for selected merge under the rejecting
padded equivalence branch.
-/
theorem selectedMergePaddedEmitterAfterHitPaddedRejectConstruction :
    SelectedMergePaddedEmitterAfterHitPaddedBranchConstruction false := by
  exact
    selectedMergePaddedEmitterAfterHitPaddedConstruction_of_decoded
      selectedMergePaddedEmitterAfterHitPaddedRejectDecodedConstruction

/--
Post-transition finite-machine leaf for selected merge under the accepting
padded equivalence branch.  The common source scanner reduces this branch to
the post-source-scanner leaf.
-/
theorem selectedMergePaddedEmitterAfterTransitionPaddedAcceptConstruction :
    SelectedMergePaddedEmitterAfterTransitionPaddedBranchConstruction true := by
  exact
    SelectedMergePaddedEmitterAfterTransitionPaddedBranchConstruction_of_afterHitPadded
      selectedMergePaddedEmitterAfterHitPaddedAcceptConstruction

/--
Post-transition finite-machine leaf for selected merge under the rejecting
padded equivalence branch.  The common source scanner reduces this branch to
the post-source-scanner leaf.
-/
theorem selectedMergePaddedEmitterAfterTransitionPaddedRejectConstruction :
    SelectedMergePaddedEmitterAfterTransitionPaddedBranchConstruction false := by
  exact
    SelectedMergePaddedEmitterAfterTransitionPaddedBranchConstruction_of_afterHitPadded
      selectedMergePaddedEmitterAfterHitPaddedRejectConstruction

/--
Combined post-transition finite-machine leaf for selected merge under the
padded equivalence contract.  The construction is assembled from the two
branch-specific finite-machine leaves.
-/
theorem selectedMergePaddedEmitterAfterTransitionPaddedCoreConstruction :
    SelectedMergePaddedEmitterAfterTransitionPaddedConstruction := by
  exact selectedMergePaddedEmitterAfterTransitionPaddedConstruction_of_branches
    selectedMergePaddedEmitterAfterTransitionPaddedAcceptConstruction
    selectedMergePaddedEmitterAfterTransitionPaddedRejectConstruction

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
