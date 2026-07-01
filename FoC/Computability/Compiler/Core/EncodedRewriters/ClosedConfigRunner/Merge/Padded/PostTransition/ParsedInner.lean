import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Merge.Padded.PostTransition.ParsedInnerWindows
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Merge.Padded.PostTransition.Specs

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

/-!
# Merge post-transition parsed inner emitter

This module contains the branch-parametric finite-machine leaf that rewrites a
parsed nested layout plus the restored outer source fields into the decoded
merge field order for either padded branch.  The accepting and rejecting modules
are compatibility wrappers over this shared obligation.
-/

/--
Finite-machine leaf that rewrites the parsed nested layout plus outer source
fields into the decoded merge field order selected by {name}`useAccept`.
-/
theorem selectedMergePaddedEmitterAfterHitPaddedParsedInnerConstruction
    (useAccept : Bool) :
    SelectedMergePaddedEmitterAfterHitPaddedParsedInnerConstruction
      useAccept := by
  have htransport :
      SelectedMergePaddedEmitterParsedInnerPostPrefixFieldTransportConstruction
        useAccept := by
    sorry
  rcases htransport with ⟨transport, htransportReady, htransportHalts⟩
  refine
    ⟨CommonGround.FiniteTransducers.canonicalSeqDescription
        SelectedMergePaddedEmitterParsedInnerPrefixCleanupDescription
        transport,
      ?_⟩
  constructor
  · exact
      CommonGround.FiniteTransducers.canonicalSeqDescription_subroutineReady
        selectedMergePaddedEmitterParsedInnerPrefixCleanupDescription_subroutineReady
        htransportReady
  · intro p
    exact
      CommonGround.FiniteTransducers.canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        selectedMergePaddedEmitterParsedInnerPrefixCleanupDescription_subroutineReady
        htransportReady
        (selectedMergePaddedEmitterParsedInnerPrefixCleanupDescription_haltsFromParsedTape
          p)
        (SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape_move_left_move_right
          p)
        (htransportHalts p)

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
