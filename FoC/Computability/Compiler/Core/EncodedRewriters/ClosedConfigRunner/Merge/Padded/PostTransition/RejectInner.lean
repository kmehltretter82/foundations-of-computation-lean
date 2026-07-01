import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Merge.Padded.PostTransition.ParsedInner

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

/-!
# Merge post-transition rejecting inner emitter
-/

/--
Compatibility name for the rejecting branch of the branch-parametric parsed
inner emitter.
-/
theorem selectedMergePaddedEmitterAfterHitPaddedRejectParsedInnerConstruction :
    SelectedMergePaddedEmitterAfterHitPaddedRejectParsedInnerConstruction := by
  exact selectedMergePaddedEmitterAfterHitPaddedParsedInnerConstruction false

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
