import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedEmitter.Shape
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedParser

set_option doc.verso true

/-!
# Padded simulator emitter terminal core

This module names the non-circular terminal/run-loop construction target for
the padded fixed-description simulator emitter.  The downstream terminal,
source-shape, run-loop, and public emitter modules consume this target as
adapter glue.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

def fixedDescriptionBoundedSimulatorPaddedEmitterTerminalTape_configRunner
    (explicitLeftBlank : Bool) (L : SimulatorLayout) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells
    (List.append
      ((SimulatorLayout.asBoolInput L).reverse.map some)
      (if explicitLeftBlank then [none] else []))
    []

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

/--
Finite-machine leaf for the exact terminal shapes of the padded
fixed-description simulator emitter.

For a fixed description {lean}`D`, this is the place where the restored
simulator layout is parsed, {lean}`D` is run for the encoded stage bound, the
hit bit is updated, and the exact padded scratch output is emitted.
-/
theorem fixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreConstruction_configRunner :
    FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreConstruction_configRunner := by
  intro D
  sorry

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
