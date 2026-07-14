import FoC.Computability.Compiler.ClosedCfg.TerminalCore.Core

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

namespace EncRewriters
namespace BoundedLayoutRunner

/-- Honest terminal body contract.  The output word and head position are
fixed, while irrelevant far-edge blank padding is retained only up to tape
equivalence. -/
def FixedDescriptionBoundedSimulatorPaddedEmitterBodyEquivSpec_configRunner
    (D body : MachineDescription) : Prop :=
  body.SubroutineReady ∧
    forall L : SimulatorLayout,
      body.HaltsFromTapeEquiv
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterBodyEquivConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists body : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterBodyEquivSpec_configRunner
        D body

def FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreEquivSpec_configRunner
    (D post : MachineDescription) : Prop :=
  post.SubroutineReady ∧
    forall explicitLeftBlank : Bool,
    forall L : SimulatorLayout,
      post.HaltsFromTapeEquiv
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalTape_configRunner
          explicitLeftBlank L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreEquivConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists post : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreEquivSpec_configRunner
        D post

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
