import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.EndpointAssembly

namespace FoC
namespace Computability
namespace StructuredConstructionTargets

/-- Concrete output-indexed bounded fuel-pair search family assembled from
the structured three-tape endpoint. -/
theorem boundedFuelPairSearchFamilyConstruction_core :
    PairedRecognizerDovetailControllerStageAttemptFuelPairSearchFamilyConstruction :=
  BoundedFuelPairSearch.U12EndpointAssembly.searchFamilyConstruction

end StructuredConstructionTargets
end Computability
end FoC
