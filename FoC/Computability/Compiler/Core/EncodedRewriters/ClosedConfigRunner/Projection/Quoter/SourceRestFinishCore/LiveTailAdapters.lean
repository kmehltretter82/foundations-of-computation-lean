import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.SourceRestFinishCore.LiveTail.EmitterConstruction
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.SourceRestFinishCore.LiveTail.JoinerConstruction

set_option doc.verso true

/-!
# Live-tail assembly adapters

This module keeps the assembly-specific export adapters separate from the
finite-table live-tail leaves.  The leaves live in the live-tail construction
modules; this module only turns the generic family constructions into concrete
assembly/source-rest constructions consumed by the final assembly module.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

/--
Reusable emitter obligation for the specialized assembly parser-prefix grammar.
It quotes the defaulted mixed option-cell prefix and stage prefix, leaves the
live raw tail to the right, and keeps the already-computed quote-rest separated
for the live-tail joiner.
-/
theorem
    mixedOptionCellQuoteLiveTailEmitterConstruction_for_assemblySourceRest :
    MixedOptionCellQuoteLiveTailEmitterConstructionForAssemblySourceRest := by
  exact
    MixedOptionCellQuoteLiveTailEmitterConstructionForAssemblySourceRest_of_family
      mixedOptionCellQuoteLiveTailEmitterAssemblyFamilyConstruction

/--
Specialized finite-table obligation for joining the reusable quote-rest field
in front of the source-rest live tail.  The arbitrary stage/source version is
too strong: the separated source tape does not carry a delimiter between an
arbitrary emitted prefix and the stage prefix, so this construction stays with
the assembly source-rest family required by the plan.
-/
theorem mixedOptionCellQuoteLiveTailJoinerConstruction :
    MixedOptionCellQuoteLiveTailJoinerConstructionForAssemblySourceRest := by
  exact
    MixedOptionCellQuoteLiveTailJoinerConstructionForAssemblySourceRest_of_family
      mixedOptionCellQuoteLiveTailJoinerAssemblyFamilyConstruction

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
