import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedEmitter.TerminalCore.Core

set_option doc.verso true

/-!
# Padded simulator terminal construction specs

This module contains only the construction-family contracts for the padded
simulator terminal core.  Concrete finite-machine runs and adapter composition
lemmas live in sibling modules.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

def FixedDescriptionBoundedSimulatorPaddedEmitterBodySpec_configRunner
    (D body : MachineDescription) : Prop :=
  body.SubroutineReady ∧
    forall L : SimulatorLayout,
      body.HaltsFromTape
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterBodyConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists body : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterBodySpec_configRunner D body

def FixedDescriptionBoundedSimulatorPaddedEmitterAfterTerminalRightShiftedSourceSpec_configRunner
    (D afterRight : MachineDescription) : Prop :=
  afterRight.SubroutineReady ∧
    forall L : SimulatorLayout,
      afterRight.HaltsFromTape
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
          L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterAfterTerminalRightShiftedSourceConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists afterRight : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterAfterTerminalRightShiftedSourceSpec_configRunner
        D afterRight

def FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetSpec_configRunner
    (D body : MachineDescription) : Prop :=
  body.SubroutineReady ∧
    forall L : SimulatorLayout,
      body.HaltsFromTape
        (CommonGround.FiniteTransducers.FSTSourceTape
          (SimulatorLayout.asBoolInput L) 1)
        (CommonGround.FiniteTransducers.FSTTargetTape
          (FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner
            D L)
          (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
            L))

def FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists body : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetSpec_configRunner
        D body

def FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalRightShiftedSourceSpec_configRunner
    (D rightBody : MachineDescription) : Prop :=
  rightBody.SubroutineReady ∧
    forall L : SimulatorLayout,
      rightBody.HaltsFromTape
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
          L)
        (CommonGround.FiniteTransducers.FSTTargetTape
          (FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner
            D L)
          (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
            L))

def FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalRightShiftedSourceConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists rightBody : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalRightShiftedSourceSpec_configRunner
        D rightBody

def FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalSourceSpec_configRunner
    (D body : MachineDescription) : Prop :=
  body.SubroutineReady ∧
    forall L : SimulatorLayout,
      body.HaltsFromTape
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L)
        (CommonGround.FiniteTransducers.FSTTargetTape
          (FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner
            D L)
          (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
            L))

def FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalSourceConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists body : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalSourceSpec_configRunner
        D body

def FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetSpec_configRunner
    (D body : MachineDescription) : Prop :=
  body.SubroutineReady ∧
    forall L : SimulatorLayout,
      body.HaltsFromTape
        (CommonGround.FiniteTransducers.FSTSourceTape
          (SimulatorLayout.asBoolInput L) 1)
        (CommonGround.FiniteTransducers.FSTTargetTape
          (FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
            D L)
          (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
            L))

def FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists body : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetSpec_configRunner
        D body

def FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalSourceSpec_configRunner
    (D body : MachineDescription) : Prop :=
  body.SubroutineReady ∧
    forall L : SimulatorLayout,
      body.HaltsFromTape
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L)
        (CommonGround.FiniteTransducers.FSTTargetTape
          (FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
            D L)
          (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
            L))

def FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalSourceConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists body : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalSourceSpec_configRunner
        D body

def FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalRightShiftedSourceSpec_configRunner
    (D rightBody : MachineDescription) : Prop :=
  rightBody.SubroutineReady ∧
    forall L : SimulatorLayout,
      rightBody.HaltsFromTape
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
          L)
        (CommonGround.FiniteTransducers.FSTTargetTape
          (FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
            D L)
          (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
            L))

def FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalRightShiftedSourceConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists rightBody : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalRightShiftedSourceSpec_configRunner
        D rightBody

def FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceSpec_configRunner
    (D rightBody : MachineDescription) : Prop :=
  rightBody.SubroutineReady ∧
    forall L : SimulatorLayout,
      rightBody.HaltsFromTape
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
          L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists rightBody : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceSpec_configRunner
        D rightBody

def FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreSpec_configRunner
    (D post : MachineDescription) : Prop :=
  post.SubroutineReady ∧
    forall explicitLeftBlank : Bool,
    forall L : SimulatorLayout,
      post.HaltsFromTape
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalTape_configRunner
          explicitLeftBlank L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists post : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreSpec_configRunner
        D post

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
