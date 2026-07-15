import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.RawLayoutEmission
import FoC.Computability.Compiler.Core.CommonGround.Layouts

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets
namespace FuelSimulatorCore
namespace RawLayoutEmission

/-- The raw emitter's right-shifted endpoint is exactly the standard
simulator-layout handoff tape, so one left handoff move restores the canonical
simulator input without a cleanup phase. -/
theorem rawEmissionOutputTape_move_left
    (attempt : MachineDescription) (raw : Word Bool) (fuel : Nat) :
    Tape.move Direction.left
        (rawEmissionOutputTape attempt raw fuel) =
      SimulatorLayout.tape (SimulatorLayout.initial attempt raw fuel) := by
  let L := SimulatorLayout.initial attempt raw fuel
  simpa [rawEmissionOutputTape, L,
    EncRewriters.CanonicalLayouts.Simulator.handoffTape,
    EncRewriters.CanonicalLayouts.HandoffTape,
    EncRewriters.CanonicalLayouts.Simulator.inputTape,
    EncRewriters.CanonicalLayouts.InputTape,
    EncRewriters.CanonicalLayouts.Simulator.bits,
    EncRewriters.CanonicalLayouts.Bits,
    EncRewriters.CanonicalLayouts.Simulator.encode,
    SimulatorLayout.tape, SimulatorLayout.asBoolInput] using
      CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape L

end RawLayoutEmission
end FuelSimulatorCore
end StructuredConstructionTargets

end Computability
end FoC
