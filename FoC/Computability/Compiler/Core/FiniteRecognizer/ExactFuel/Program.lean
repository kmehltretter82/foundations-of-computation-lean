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
Finite-state construction target for exact initial-layout materializers.
These machines parse the public unary generated call and emit the protected
layout on their concrete final tape.
-/
def FinStateInitialLayoutExactMaterializerConstruction : Prop :=
  forall stateCount : Nat,
  forall M : TuringMachine MachineCodeSymbol (Fin stateCount),
    InitialLayoutExactMaterializerConstruction M

/--
Component bundle for the normalized exact-fuel stage program.
-/
def FinStateExactProgramComponentsConstruction : Prop :=
  ExactOutputThenRecognizeConstruction ∧
    FinStateInitialLayoutExactMaterializerConstruction ∧
      FinStateLayoutFuelLoopCodeMachineConstruction

/--
Remaining finite-table leaf for exact-output sequencing.
-/
theorem exactOutputThenRecognizeFiniteLeaf :
    ExactOutputThenRecognizeConstruction :=
  exactOutputThenRecognizeConstruction

/--
Remaining finite-table leaf for the exact initial-layout materializer.
-/
theorem initialLayoutExactMaterializerFinStateFiniteLeaf :
    FinStateInitialLayoutExactMaterializerConstruction := by
  intro stateCount M
  exact
    initialLayoutExactMaterializerConstruction_of_exactOutputPrimitive
      (initialLayoutExactOutputPrimitiveFinStateFiniteLeaf
        stateCount M)

/--
Remaining finite-table leaf for the executable protected exact-fuel loop.
It must parse the protected layout, run the fixed selected transition table for
exactly the protected fuel, and halt exactly when the final selected state is
the selected halt state.
-/
theorem layoutFuelLoopCodeMachineFinStateFiniteLeaf :
    FinStateLayoutFuelLoopCodeMachineConstruction := by
  intro stateCount M
  exact
    layoutFuelLoopCodeMachineConstruction_of_exactOutputPrimitive
      (layoutFuelLoopExactOutputPrimitiveFinStateFiniteLeaf
        stateCount M)

theorem layoutCodeMachineFinStateFiniteLeaf :
    FinStateLayoutCodeMachineConstruction := by
  intro stateCount M
  exact
    layoutCodeMachineConstruction_of_fuelLoopCodeMachine
      (layoutFuelLoopCodeMachineFinStateFiniteLeaf stateCount M)

theorem exactProgramComponentsFiniteLeaf :
    FinStateExactProgramComponentsConstruction :=
  ⟨exactOutputThenRecognizeFiniteLeaf,
    initialLayoutExactMaterializerFinStateFiniteLeaf,
    layoutFuelLoopCodeMachineFinStateFiniteLeaf⟩

theorem codeMachineFinStateFiniteLeaf_of_components
    (hcomponents : FinStateExactProgramComponentsConstruction) :
    FinStateCodeMachineConstruction := by
  intro stateCount M
  rcases hcomponents with
    ⟨hcompose, hmaterializer, hlayout⟩
  exact
    codeMachineConstruction_of_exactMaterializer_layoutCodeMachine_compose
      hcompose (hmaterializer stateCount M)
      (layoutCodeMachineConstruction_of_fuelLoopCodeMachine
        (hlayout stateCount M))

/--
Finite-state construction for the normalized exact-fuel staged program.
-/
theorem codeMachineFinStateFiniteLeaf :
    FinStateCodeMachineConstruction :=
  codeMachineFinStateFiniteLeaf_of_components
    exactProgramComponentsFiniteLeaf

theorem finStateRunnerConstructionFiniteLeaf :
    FinStateRunnerConstruction stageCode :=
  finStateRunnerConstruction_of_codeMachine codeMachineFinStateFiniteLeaf

end StageProgram
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
