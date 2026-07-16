import FoC.Computability.Compiler.Structured.HeadRoutes.Tape2Projector.Assembly

set_option doc.verso true

/-!
# Marker-preserving tape-2 projector construction

The retired selected-head cleanup source had already erased the logical head
marker and is refuted by the imported guardrails. The completed construction
starts from the canonical guarded three-tape encoding used by endpoint
consumers and exposes only the required tape-equivalence target.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

/--
The completed marker-preserving projector. Its source retains every separator
and logical head marker, while its target uses the equivalence contract
consumed by endpoint users.
-/
theorem structuredTape2ProjectorConstruction_core :
    StructuredTape2ProjectorConstruction := by
  exact
    ⟨Tape2Projector.endpointTape2ProjectorDescription,
      Tape2Projector.endpointTape2ProjectorDescription_spec⟩

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
