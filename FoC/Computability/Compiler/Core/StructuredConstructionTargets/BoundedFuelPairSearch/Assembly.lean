import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.EndpointAssembly

namespace FoC
namespace Computability
namespace StructuredConstructionTargets

/-- Concrete output-indexed bounded fuel-pair search family assembled from
the structured three-tape endpoint. -/
theorem boundedFuelPairSearchFamilyConstruction_core :
    PairedRecognizerDovetailControllerStageAttemptFuelPairSearchFamilyConstruction := by
  apply boundedFuelPairSearchFamilyConstruction_of_structuredEndpoints
  intro runner _hrunner b
  exact BoundedFuelPairSearch.U12EndpointAssembly.endpointConstruction runner b

end StructuredConstructionTargets
end Computability
end FoC
