import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedEmitter.SourceShapeCore
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Basic

set_option doc.verso true

/-!
# Terminal simulator source tapes

This module contains the pure terminal source-tape and encoded-field shape
facts used by the padded simulator emitter terminal core.  The finite-machine
construction leaves stay downstream in the terminal core module.
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

def fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
    (L : SimulatorLayout) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells [none]
    (List.append ((SimulatorLayout.asBoolInput L).map some) [none])

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_eq_FSTSourceTape_configRunner
    (L : SimulatorLayout) :
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner L =
    CommonGround.FiniteTransducers.FSTSourceTape
        (SimulatorLayout.asBoolInput L) 1 := by
  dsimp [
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner,
    CommonGround.FiniteTransducers.FSTSourceTape,
    DovetailInitialLayoutInitializer.tapeAtCells,
    CommonGround.FiniteTransducers.tapeAtCells]
  rfl

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_cells_configRunner
    (L : SimulatorLayout) :
    Tape.cells
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L) =
      none :: List.append ((SimulatorLayout.asBoolInput L).map some) [none] := by
  cases hbits : SimulatorLayout.asBoolInput L with
  | nil =>
      simp [
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner,
        DovetailInitialLayoutInitializer.tapeAtCells, Tape.cells, hbits]
  | cons bit rest =>
      simp [
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner,
        DovetailInitialLayoutInitializer.tapeAtCells, Tape.cells, hbits]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_normalizedOutput_configRunner
    (L : SimulatorLayout) :
    Tape.normalizedOutput
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L) =
      SimulatorLayout.asBoolInput L := by
  rw [Tape.normalizedOutput,
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_cells_configRunner]
  simp [Function.comp_def]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_contextLength_configRunner
    (L : SimulatorLayout) :
    Tape.contextLength
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L) =
      (SimulatorLayout.asBoolInput L).length + 1 := by
  cases hbits : SimulatorLayout.asBoolInput L with
  | nil =>
      simp [
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner,
        DovetailInitialLayoutInitializer.tapeAtCells, Tape.contextLength,
        hbits]
  | cons bit rest =>
      simp [
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner,
        DovetailInitialLayoutInitializer.tapeAtCells, Tape.contextLength,
        hbits]
      omega

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_contextLength_eq_scratchWidth_configRunner
    (L : SimulatorLayout) :
    Tape.contextLength
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L) =
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner L + 2 := by
  rw [
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_contextLength_configRunner,
    FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner,
    FixedDescriptionBoundedSimulatorInput]
  have hlen : 1 <= (SimulatorLayout.asBoolInput L).length := by
    rw [fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_header_payloadBits_configRunner]
    simp [fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
      encodeCodeSymbolAsInput]
  cases hbits : SimulatorLayout.asBoolInput L with
  | nil =>
      simp [hbits] at hlen
  | cons bit rest =>
      simp [Tape.input, Tape.contextLength]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_normalizedOutput_eq_fields_configRunner
    (L : SimulatorLayout) :
    Tape.normalizedOutput
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L) =
      encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          encodeBoolWordAppend L.input
            (encodeNatAppend L.stage
              (encodeConfigurationAppend L.config
                (encodeBoolAppend L.hit [])))) := by
  rw [
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_normalizedOutput_configRunner,
    fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_fields_configRunner]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_cells_eq_fields_configRunner
    (L : SimulatorLayout) :
    Tape.cells
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L) =
      none ::
        List.append
          ((encodeCodeWordAsInput
            (MachineCodeSymbol.header ::
              encodeBoolWordAppend L.input
                (encodeNatAppend L.stage
                  (encodeConfigurationAppend L.config
                    (encodeBoolAppend L.hit []))))).map some)
          [none] := by
  rw [
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_cells_configRunner,
    fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_fields_configRunner]

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

