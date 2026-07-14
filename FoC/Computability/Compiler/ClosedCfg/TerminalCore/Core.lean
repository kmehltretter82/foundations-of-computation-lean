import FoC.Computability.Compiler.ClosedCfg.TerminalCore.SourceTapes
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.RightEdgeRewind
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Simulator.PaddedParser.Scanners

set_option doc.verso true

/-!
# Padded simulator emitter terminal core

Only the live right-scratch surface remains here. The former exact FST,
right-shifted-source, and tape-shape lattices had no declaration-level consumer
after the terminal route facade was retired.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

def FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
    (D : MachineDescription) (L : SimulatorLayout) : Tape Bool :=
  Tape.move Direction.right
    (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner D L)

private theorem fixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_length_ge_two_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    2 <= (FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
      D L).length := by
  rw [FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner,
    FixedDescriptionBoundedSimulatorOutput]
  rw [fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_header_payloadBits_configRunner]
  simp [fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
    encodeCodeSymbolAsInput]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_move_left_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    Tape.move Direction.left
        (FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner D L) =
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner D L := by
  have hlen :=
    fixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_length_ge_two_configRunner D L
  cases houtput :
      FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner D L with
  | nil => simp [houtput] at hlen
  | cons first rest =>
      cases rest with
      | nil => simp [houtput] at hlen
      | cons second tail =>
          cases first <;> cases second <;>
            simp [FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner,
              FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner,
              ScratchPaddedOutputTape, inputWithTrailingBlankPadding,
              houtput, Tape.move, Tape.moveLeft, Tape.moveRight]

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
