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
  sorry

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
