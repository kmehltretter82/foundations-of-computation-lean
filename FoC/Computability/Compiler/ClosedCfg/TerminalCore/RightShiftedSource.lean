import FoC.Computability.Compiler.ClosedCfg.TerminalCore.SourceTapes
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Simulator.PaddedParser.Return

set_option doc.verso true

/-!
# Terminal right-shifted source handoff

This module contains the tape movement fact needed when composing the terminal
rewind with the equivalence-valued emitter body.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_move_left_move_right_configRunner
    (L : SimulatorLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
            L)) =
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
        L := by
  have hlen : 1 <= (SimulatorLayout.asBoolInput L).length := by
    rw [fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_header_payloadBits_configRunner]
    simp [fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
      encodeCodeSymbolAsInput]
  cases hbits : SimulatorLayout.asBoolInput L with
  | nil =>
      simp [hbits] at hlen
  | cons first rest =>
      cases rest with
      | nil =>
          cases first <;>
            simp [
              fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner,
              DovetailInitialLayoutInitializer.tapeAtCells,
              Tape.move, Tape.moveLeft, Tape.moveRight, hbits]
      | cons second tail =>
          cases first <;> cases second <;>
            simp [
              fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner,
              DovetailInitialLayoutInitializer.tapeAtCells,
              Tape.move, Tape.moveLeft, Tape.moveRight, hbits]

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
