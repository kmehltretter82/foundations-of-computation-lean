import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.LayoutCode

set_option doc.verso true

/-!
# Exact-fuel staged program boundary

This module isolates the normalized code-machine boundary for exact-fuel
generated calls.  The public generated-code runner can be obtained from any
finite machine that realizes this staged predicate; the remaining concrete
transition-table work is therefore focused on one exact parser/run program.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StageProgram

/--
Remaining concrete transition-table leaf for the normalized exact-fuel staged
program.  It must parse the unary fuel prefix, protect the payload as an
encoded work layout, run the fixed selected transition table for exactly that
fuel, and halt exactly when the final selected state is the selected halt
state.
-/
theorem codeMachineFinStateFiniteLeaf :
    FinStateCodeMachineConstruction := by
  intro stateCount M
  exact
    codeMachineConstruction_of_materializer_layoutCodeMachine_compose
      outputThenRecognizeConstructionFiniteLeaf
      (initialLayoutMaterializerConstructionFiniteLeaf M)
      (layoutCodeMachineFinStateFiniteLeaf stateCount M)

theorem finStateRunnerConstructionFiniteLeaf :
    FinStateRunnerConstruction stageCode :=
  finStateRunnerConstruction_of_codeMachine codeMachineFinStateFiniteLeaf

end StageProgram
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
