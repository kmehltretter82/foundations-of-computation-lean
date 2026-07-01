import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedEmitter.Shape

set_option doc.verso true

/-!
# Padded simulator source-shape core

This module contains the basic source-rewind tape shapes shared by the padded
simulator emitter run-loop and terminal handoff code.  It deliberately avoids
depending on the terminal construction modules.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

namespace EncodedRewriters
namespace BoundedLayoutRunner

def FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindSourceTape_configRunner
    (bits : Word Bool) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells (bits.reverse.map some) []

def FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
    (bits : Word Bool) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells [none]
    (List.append (bits.map some) [none])

theorem fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTarget_cells_configRunner
    (w : Word Bool) :
    Tape.cells
        (FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
          w) =
      none :: List.append (w.map some) [none] := by
  cases w <;>
    simp [
      FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner,
      DovetailInitialLayoutInitializer.tapeAtCells, Tape.cells]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTarget_contextLength_configRunner
    (w : Word Bool) :
    Tape.contextLength
        (FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
          w) =
      w.length + 1 := by
  cases w <;>
    simp [
      FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner,
      DovetailInitialLayoutInitializer.tapeAtCells, Tape.contextLength] <;>
    omega

theorem fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTarget_normalizedOutput_configRunner
    (w : Word Bool) :
    Tape.normalizedOutput
      (FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
        w) =
      w := by
  cases w with
  | nil =>
      simp [
        FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner,
        DovetailInitialLayoutInitializer.tapeAtCells, Tape.normalizedOutput,
        Tape.cells]
  | cons bit rest =>
      simp [
        FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner,
        DovetailInitialLayoutInitializer.tapeAtCells, Tape.normalizedOutput,
        Tape.cells, Function.comp_def]

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

