import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Simulator.PaddedEmitter.Shape
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Basic

set_option doc.verso true

/-!
# Terminal simulator source tapes

This module contains the two terminal source-tape definitions used by the
padded simulator emitter terminal core.  Finite-machine construction leaves
and shape facts stay at their actual consumers.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

def fixedDescriptionBoundedSimulatorPaddedEmitterTerminalTape_configRunner
    (explicitLeftBlank : Bool) (L : SimulatorLayout) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells
    (List.append
      ((SimulatorLayout.asBoolInput L).reverse.map some)
      (if explicitLeftBlank then [none] else []))
    []

def fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
    (L : SimulatorLayout) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells [none]
    (List.append ((SimulatorLayout.asBoolInput L).map some) [none])

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
