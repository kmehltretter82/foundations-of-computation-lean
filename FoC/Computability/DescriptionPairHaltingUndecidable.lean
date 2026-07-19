import FoC.Computability.Compiler.Core.PairHaltingReduction.Construction
import FoC.Computability.DescriptionCodeUndecidable

set_option doc.verso true

/-!
# Finite-description pair-halting undecidability

The checked self-append construction converts any stopped decider for the
self-delimiting pair-halting language into a stopped decider for valid
self-halting.  The latter is already ruled out by finite-description diagonal
nonrecognizability.
-/

namespace FoC
namespace Computability
namespace PairHaltingReduction

open Languages

/-- The self-delimiting finite-description pair-halting language has no
stopped finite-description decider. -/
theorem not_descriptionDecidableCodeLanguage_codePairHalting :
    ¬ DescriptionDecidableCodeLanguage CodePairHaltingLanguage := by
  rintro ⟨pairDecider, reject, accept, hpair⟩
  exact not_descriptionDecidableCodeLanguage_codeSelfHalting
    ⟨Description pairDecider reject, reject, accept,
      stoppedDecidesCodeSelfHalting_of_stoppedDecidesCodePairHalting hpair⟩

end PairHaltingReduction
end Computability
end FoC
