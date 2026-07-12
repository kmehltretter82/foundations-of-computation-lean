import FoC.Computability.Compiler.Structured.HeadRoutes.ContractGuardrails

set_option doc.verso true

/-!
# Marker-preserving tape-2 projector frontier

The former selected-head cleanup source had already erased the logical head
marker and is refuted by the imported guardrails.  The live #17 frontier starts
from the canonical guarded three-tape encoding used by every current endpoint
consumer and exposes only the required tape-equivalence target.
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
The live #17 construction frontier.  Its source retains every separator and
logical head marker, while its target uses the equivalence contract consumed
by all current endpoint users.
-/
theorem structuredTape2ProjectorConstruction_core :
    StructuredTape2ProjectorConstruction := by
  -- Remaining finite-machine obligation: project logical tape 2 directly
  -- from `encodedGuardedStructured3Tapes T0 T1 T2`.
  sorry

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
