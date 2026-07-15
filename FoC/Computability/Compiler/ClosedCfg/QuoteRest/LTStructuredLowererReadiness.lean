import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTableChecks
import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTEndpointContracts

set_option doc.verso true

/-!
# Live-tail emitter lowerer readiness

Static table checks and the premise-free lowered run used by the direct joined
QuoteRest endpoint.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionInputQuoterFiniteLeaf

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_wellFormed :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.WellFormed := by
  exact
    structuredDescription_wellFormed_of_transition_checks
      structuredMixedOptionCellQuoteLiveTailEmitterDescription
      (by decide)
      (by decide)
      (by decide)
      (by decide)
      (by decide)
      (by decide)

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_haltTransitionFree :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.HaltTransitionFree :=
  structuredDescription_haltTransitionFree_of_transition_checks
    structuredMixedOptionCellQuoteLiveTailEmitterDescription
    (by decide)

theorem structuredLiveTailEmitterStaticLowererReadiness :
    StructuredLiveTailEmitterStaticLowererReadiness :=
  ⟨structuredMixedOptionCellQuoteLiveTailEmitterDescription_wellFormed,
    structuredMixedOptionCellQuoteLiveTailEmitterDescription_haltTransitionFree⟩

theorem loweredStructuredLiveTailEmitterDescription_subroutineReady_static :
    loweredStructuredLiveTailEmitterDescription.SubroutineReady :=
  loweredStructuredLiveTailEmitterDescription_subroutineReady
    structuredLiveTailEmitterStaticLowererReadiness

theorem loweredStructuredLiveTailEmitterDescription_haltsFromAssemblyEncoded_static
    (p : AssemblySourceRestLiveTailEmitterParam) :
    loweredStructuredLiveTailEmitterDescription.HaltsFromTapeEquiv
      (structuredLiveTailEmitterAssemblyEncodedInitialTape p)
      (structuredLiveTailEmitterAssemblyEncodedFinalTape p) :=
  loweredStructuredLiveTailEmitterDescription_haltsFromAssemblyEncoded
    structuredLiveTailEmitterStaticLowererReadiness p

end SelectedProjectionInputQuoterFiniteLeaf
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
