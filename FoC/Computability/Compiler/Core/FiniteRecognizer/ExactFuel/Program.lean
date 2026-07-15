import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.StageRunner.Construction
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Update.Runs

set_option doc.verso true

/-!
# Exact-fuel staged program boundary

This module exposes the normalized finite-state runner for exact-fuel generated
calls.  The construction materializes the protected stage input and repeatedly
executes the selected-machine update kernel until the exact fuel is exhausted.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StageProgram

theorem finStateRunnerConstructionFiniteLeaf :
    FinStateRunnerConstruction stageCode := by
  intro stateCount M
  exact StrictProbe.StageRunner.runnerConstruction M
    (StrictProbe.Update.Kernel.kernel stateCount)
    (StrictProbe.CyclicDriverWitnesses.runWitnesses M
      (StrictProbe.Update.Kernel.kernel stateCount)
      ([] : Word MachineCodeSymbol)
      (StrictProbe.Update.Runs.selectedUpdateRuns M
        ([] : Word MachineCodeSymbol)))

end StageProgram
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
