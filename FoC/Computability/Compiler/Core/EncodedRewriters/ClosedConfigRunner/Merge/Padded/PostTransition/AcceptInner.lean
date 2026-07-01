import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Merge.Padded.PostTransition.ParsedInner

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
Compatibility name for the accepting branch of the branch-parametric parsed
inner emitter.
-/
theorem selectedMergePaddedEmitterAfterHitPaddedAcceptParsedInnerConstruction :
    SelectedMergePaddedEmitterAfterHitPaddedAcceptParsedInnerConstruction := by
  exact selectedMergePaddedEmitterAfterHitPaddedParsedInnerConstruction true

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
