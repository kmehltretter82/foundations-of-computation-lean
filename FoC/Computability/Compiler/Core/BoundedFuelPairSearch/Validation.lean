import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.Layout
import FoC.Computability.Compiler.Structured.Lowering.Layout

set_option doc.verso true

/-!
# Candidate-output validation for bounded fuel-pair search

The search loop observes whether a decoded bounded run halted with the fixed
encoded Boolean output.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace BoundedFuelPairSearch

/-- Semantic success for a decoded bounded-run layout. -/
def CandidateLayoutSuccess
    (runner : MachineDescription) (b : Bool)
    (L : SimulatorLayout) : Prop :=
  L.config.state = runner.halt ∧
    Tape.normalizedOutput L.config.tape =
      encodeCodeWordAsInput (encodeBoolWord [b])

end BoundedFuelPairSearch
end Computability
end FoC
