import FoC.Computability.Compiler.Core.ConstructionTargets

set_option doc.verso true

/-!
# Right-shifted fixed-description simulator code construction target

This module keeps the finite-machine leaf for compiling
{name}`FoC.Computability.FixedDescriptionBoundedSimulatorCode` with the other
fixed-description simulator construction targets.  Downstream config-runner
modules should consume this target as an input and remain adapter glue.
-/

namespace FoC
namespace Computability

open Languages

def FixedDescriptionBoundedSimulatorCodeOutputSubroutineConstruction :
    Prop :=
  forall D : MachineDescription,
    exists simulator : MachineDescription,
      TapeCodePrimitiveOutputCompiledSubroutineByDescription
        (FixedDescriptionBoundedSimulatorCode D) simulator

def FixedDescriptionBoundedSimulatorCodeRightShiftedClosureConstruction :
    Prop :=
  forall D simulator : MachineDescription,
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      (FixedDescriptionBoundedSimulatorCode D) simulator ->
      exists shiftedSimulator : MachineDescription,
        EncodedRewriters.RightShiftedOutputCompiledSubroutineByDescription
          (FixedDescriptionBoundedSimulatorCode D) shiftedSimulator

theorem fixedDescriptionBoundedSimulatorCodeRightShiftedConstruction_of_output_closure
    (houtput :
      FixedDescriptionBoundedSimulatorCodeOutputSubroutineConstruction)
    (hclosure :
      FixedDescriptionBoundedSimulatorCodeRightShiftedClosureConstruction) :
    FixedDescriptionBoundedSimulatorCodeRightShiftedConstruction := by
  intro D
  rcases houtput D with ⟨simulator, hsimulator⟩
  exact hclosure D simulator hsimulator

theorem fixedDescriptionBoundedSimulatorCodeOutputSubroutineConstruction_scaffold :
    FixedDescriptionBoundedSimulatorCodeOutputSubroutineConstruction := by
  sorry

theorem fixedDescriptionBoundedSimulatorCodeRightShiftedClosureConstruction_scaffold :
    FixedDescriptionBoundedSimulatorCodeRightShiftedClosureConstruction := by
  sorry

theorem fixedDescriptionBoundedSimulatorCodeRightShiftedConstruction_scaffold :
    FixedDescriptionBoundedSimulatorCodeRightShiftedConstruction := by
  exact
    fixedDescriptionBoundedSimulatorCodeRightShiftedConstruction_of_output_closure
      fixedDescriptionBoundedSimulatorCodeOutputSubroutineConstruction_scaffold
      fixedDescriptionBoundedSimulatorCodeRightShiftedClosureConstruction_scaffold

end Computability
end FoC
