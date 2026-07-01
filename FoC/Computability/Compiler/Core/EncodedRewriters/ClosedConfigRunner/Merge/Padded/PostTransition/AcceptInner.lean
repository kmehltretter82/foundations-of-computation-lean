import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Merge.Padded.PostTransition.BranchContracts

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

/-!
# Merge post-transition accepting inner emitter
-/

/--
Finite-machine leaf that rewrites the parsed nested layout plus outer source
fields into the decoded accepting-merge field order.
-/
theorem selectedMergePaddedEmitterAfterHitPaddedAcceptParsedInnerConstruction :
    SelectedMergePaddedEmitterAfterHitPaddedAcceptParsedInnerConstruction := by
  sorry

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
