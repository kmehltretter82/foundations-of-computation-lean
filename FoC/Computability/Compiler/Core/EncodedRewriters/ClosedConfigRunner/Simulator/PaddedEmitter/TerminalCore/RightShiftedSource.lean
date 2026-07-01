import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedEmitter.TerminalCore.Core
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedParser.Return

set_option doc.verso true

/-!
# Terminal right-shifted source handoff

This module contains the exact finite-machine run and tape movement lemmas that
move a terminal source tape to the right-shifted terminal source expected by
downstream field/FST emitters.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
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

theorem fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_haltsFrom_terminalSource_configRunner
    (L : SimulatorLayout) :
    FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner.HaltsFromTape
      (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
        L)
      (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
        L) := by
  have hlen : 2 <= (SimulatorLayout.asBoolInput L).length := by
    rw [fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_header_payloadBits_configRunner]
    simp [fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
      encodeCodeSymbolAsInput]
  cases hbits : SimulatorLayout.asBoolInput L with
  | nil =>
      simp [hbits] at hlen
  | cons first rest =>
      cases rest with
      | nil =>
          simp [hbits] at hlen
      | cons second tail =>
          refine ⟨3, ?_⟩
          constructor
          · cases tail <;> cases first <;> cases second <;>
              simp [
                fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner,
                FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner,
                DovetailInitialLayoutInitializer.tapeAtCells,
                runConfig, stepConfig, lookupTransition, Matches,
                DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
                transition, Tape.read, Tape.write, Tape.move,
                Tape.moveLeft, Tape.moveRight, hbits]
          · cases tail <;> cases first <;> cases second <;>
              simp [
                fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner,
                fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner,
                FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner,
                DovetailInitialLayoutInitializer.tapeAtCells,
                runConfig, stepConfig, lookupTransition, Matches,
                DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
                transition, Tape.read, Tape.write, Tape.move,
                Tape.moveLeft, Tape.moveRight, hbits]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_move_left_move_right_configRunner
    (L : SimulatorLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
            L)) =
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
        L := by
  have hlen : 2 <= (SimulatorLayout.asBoolInput L).length := by
    rw [fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_header_payloadBits_configRunner]
    simp [fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
      encodeCodeSymbolAsInput]
  cases hbits : SimulatorLayout.asBoolInput L with
  | nil =>
      simp [hbits] at hlen
  | cons first rest =>
      cases rest with
      | nil =>
          simp [hbits] at hlen
      | cons second tail =>
          cases tail <;> cases first <;> cases second <;>
            simp [
              fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner,
              fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner,
              DovetailInitialLayoutInitializer.tapeAtCells,
              Tape.move, Tape.moveLeft, Tape.moveRight, hbits]

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
