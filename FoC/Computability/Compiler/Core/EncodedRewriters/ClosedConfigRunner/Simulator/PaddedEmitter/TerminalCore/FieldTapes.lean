import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedEmitter.TerminalCore.Core

set_option doc.verso true

/-!
# Terminal field FST source and target tapes

This module names the exact source and target cell layouts for the remaining
terminal run-config emitter leaf.  The source side is the simulator layout as
an FST input field, and the target side is the field-level padded FST target
containing the result of running the fixed description for the encoded stage
bound.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

def FixedDescriptionBoundedSimulatorPaddedEmitterFieldSourceBits_configRunner
    (L : SimulatorLayout) : Word Bool :=
  SimulatorLayout.asBoolInput L

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFieldSourceBits_eq_fields_configRunner
    (L : SimulatorLayout) :
    FixedDescriptionBoundedSimulatorPaddedEmitterFieldSourceBits_configRunner
        L =
      encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          encodeBoolWordAppend L.input
            (encodeNatAppend L.stage
              (encodeConfigurationAppend L.config
                (encodeBoolAppend L.hit [])))) := by
  exact fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_fields_configRunner
    L

def FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTSourceCells_configRunner
    (L : SimulatorLayout) : List (Option Bool) :=
  none ::
    List.append
      ((FixedDescriptionBoundedSimulatorPaddedEmitterFieldSourceBits_configRunner
        L).map some)
      [none]

def FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetCells_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    List (Option Bool) :=
  List.append
    ((FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner
      D L).map some)
    (List.replicate
      (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
        L)
      none)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceTape_cells_eq_fieldSourceCells_configRunner
    (L : SimulatorLayout) :
    Tape.cells
        (CommonGround.FiniteTransducers.FSTSourceTape
          (SimulatorLayout.asBoolInput L) 1) =
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTSourceCells_configRunner
        L := by
  rw [←
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_eq_FSTSourceTape_configRunner]
  rw [fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_cells_configRunner]
  rfl

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceTape_cells_eq_fields_configRunner
    (L : SimulatorLayout) :
    Tape.cells
        (CommonGround.FiniteTransducers.FSTSourceTape
          (SimulatorLayout.asBoolInput L) 1) =
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
    fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceTape_cells_eq_fieldSourceCells_configRunner]
  unfold FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTSourceCells_configRunner
  rw [
    fixedDescriptionBoundedSimulatorPaddedEmitterFieldSourceBits_eq_fields_configRunner]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceTape_normalizedOutput_eq_fieldSourceBits_configRunner
    (L : SimulatorLayout) :
    Tape.normalizedOutput
        (CommonGround.FiniteTransducers.FSTSourceTape
          (SimulatorLayout.asBoolInput L) 1) =
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldSourceBits_configRunner
        L := by
  rw [CommonGround.FiniteTransducers.FSTSourceTape_normalizedOutput]
  rfl

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetTape_cells_eq_fieldTargetCells_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    Tape.cells
        (CommonGround.FiniteTransducers.FSTTargetTape
          (FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner
            D L)
          (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
            L)) =
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetCells_configRunner
        D L := by
  unfold FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetCells_configRunner
  rw [←
    fixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_eq_fieldOutputBits_configRunner
      D L]
  rw [←
    fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_eq_FSTTargetTape_configRunner
      D L]
  exact
    fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_cells_eq_outputBits_configRunner
      D L

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetTape_cells_eq_fields_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    Tape.cells
        (CommonGround.FiniteTransducers.FSTTargetTape
          (FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner
            D L)
          (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
            L)) =
      List.append
        ((encodeCodeWordAsInput
          (MachineCodeSymbol.header ::
            encodeBoolWordAppend L.input
              (encodeNatAppend L.stage
                (encodeConfigurationAppend
                  (D.runConfig L.stage L.config)
                  (encodeBoolAppend
                    (L.hit ||
                      SimulatorLayout.hitsFromConfigByBool
                        D L.config L.stage)
                    []))))).map some)
        (List.replicate
          (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
            L)
          none) := by
  rw [
    fixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetTape_cells_eq_fieldTargetCells_configRunner]
  rfl

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetTape_normalizedOutput_eq_fieldOutputBits_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    Tape.normalizedOutput
        (CommonGround.FiniteTransducers.FSTTargetTape
          (FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner
            D L)
          (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
            L)) =
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner
        D L := by
  rw [CommonGround.FiniteTransducers.FSTTargetTape_normalizedOutput]

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
