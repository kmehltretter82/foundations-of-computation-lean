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
Finite-state construction for the normalized exact-fuel staged program.
-/
theorem exactOutputPrimitiveFinStateFiniteLeaf :
    forall stateCount : Nat,
    forall M : TuringMachine MachineCodeSymbol (Fin stateCount),
      ExactOutputPrimitiveConstruction M := by
  intro stateCount M
  cases stateCount with
  | zero =>
      exact False.elim (Fin.elim0 M.start)
  | succ _ =>
      sorry

theorem codeMachineFinStateFiniteLeaf :
    FinStateCodeMachineConstruction := by
  intro stateCount M
  exact
    codeMachineConstruction_of_exactOutputPrimitive
      (exactOutputPrimitiveFinStateFiniteLeaf stateCount M)

theorem finStateRunnerConstructionFiniteLeaf :
    FinStateRunnerConstruction stageCode :=
  finStateRunnerConstruction_of_codeMachine codeMachineFinStateFiniteLeaf

end StageProgram
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
