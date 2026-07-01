import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedEmitter.TerminalCore.SourceTapes
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.RightEdgeRewind

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

def FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
    (D : MachineDescription) (L : SimulatorLayout) : Tape Bool :=
  Tape.move Direction.right
    (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
      D L)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_length_ge_two_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    2 <=
      (FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
        D L).length := by
  rw [FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner,
    FixedDescriptionBoundedSimulatorOutput]
  rw [fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_header_payloadBits_configRunner]
  simp [fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
    encodeCodeSymbolAsInput]

theorem fixedDescriptionBoundedSimulatorOutput_length_ge_header_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    4 <= (FixedDescriptionBoundedSimulatorOutput D L).length := by
  rw [FixedDescriptionBoundedSimulatorOutput]
  rw [fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_header_payloadBits_configRunner]
  simp [fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
    encodeCodeSymbolAsInput]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_move_left_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    Tape.move Direction.left
        (FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
          D L) =
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
        D L := by
  have hlen :=
    fixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_length_ge_two_configRunner
      D L
  cases houtput :
      FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
        D L with
  | nil =>
      simp [houtput] at hlen
  | cons first rest =>
      cases rest with
      | nil =>
          simp [houtput] at hlen
      | cons second tail =>
          cases first <;> cases second <;>
            simp [
              FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner,
              FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner,
              ScratchPaddedOutputTape, inputWithTrailingBlankPadding,
              houtput, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_eq_FSTTargetTape_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
        D L =
      CommonGround.FiniteTransducers.FSTTargetTape
        (FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
          D L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
          L) := by
  have hlen :=
    fixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_length_ge_two_configRunner
      D L
  cases houtput :
      FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
        D L with
  | nil =>
      simp [houtput] at hlen
  | cons first rest =>
      cases rest with
      | nil =>
          simp [houtput] at hlen
      | cons second tail =>
          cases first <;> cases second <;>
            simp [
              FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner,
              FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner,
              ScratchPaddedOutputTape,
              CommonGround.FiniteTransducers.FSTTargetTape,
              inputWithTrailingBlankPadding,
              CommonGround.FiniteTransducers.inputWithTrailingBlankPadding,
              FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner,
              houtput,
              Tape.move, Tape.moveRight]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_eq_tapeAtCells_cons_cons_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    exists first : Bool,
    exists second : Bool,
    exists rest : Word Bool,
      FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
          D L =
        first :: second :: rest ∧
        FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
            D L =
          DovetailInitialLayoutInitializer.tapeAtCells [some first]
            (some second :: List.append (rest.map some)
              (List.replicate
                (Tape.contextLength
                  (Tape.input (FixedDescriptionBoundedSimulatorInput L)))
                none)) := by
  have hlen :=
    fixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_length_ge_two_configRunner
      D L
  cases houtput :
      FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
        D L with
  | nil =>
      simp [houtput] at hlen
  | cons first rest =>
      cases rest with
      | nil =>
          simp [houtput] at hlen
      | cons second tail =>
          refine ⟨first, second, tail, ?_, ?_⟩
          · rfl
          · cases first <;> cases second <;>
              simp [
                FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner,
                FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner,
                ScratchPaddedOutputTape, inputWithTrailingBlankPadding,
                FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner,
                DovetailInitialLayoutInitializer.tapeAtCells,
                houtput, Tape.move, Tape.moveRight]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_cells_eq_outputBits_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    Tape.cells
        (FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
          D L) =
      List.append
        ((FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
          D L).map some)
        (List.replicate
          (Tape.contextLength
            (Tape.input (FixedDescriptionBoundedSimulatorInput L)))
          none) := by
  have hlen :=
    fixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_length_ge_two_configRunner
      D L
  cases houtput :
      FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
        D L with
  | nil =>
      simp [houtput] at hlen
  | cons first rest =>
      cases rest with
      | nil =>
          simp [houtput] at hlen
      | cons second tail =>
          cases first <;> cases second <;>
            simp [
              FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner,
              FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner,
              ScratchPaddedOutputTape, inputWithTrailingBlankPadding,
              FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner,
              houtput, Tape.cells, Tape.move, Tape.moveRight]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_cells_eq_fields_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    Tape.cells
        (FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
          D L) =
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
          (Tape.contextLength
            (Tape.input (FixedDescriptionBoundedSimulatorInput L)))
          none) := by
  rw [
    fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_cells_eq_outputBits_configRunner,
    fixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_eq_fields_configRunner]

def FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner
    (D : MachineDescription) (L : SimulatorLayout) : Word Bool :=
  encodeCodeWordAsInput
    (MachineCodeSymbol.header ::
      encodeBoolWordAppend L.input
        (encodeNatAppend L.stage
          (encodeConfigurationAppend
            (D.runConfig L.stage L.config)
            (encodeBoolAppend
              (L.hit ||
                SimulatorLayout.hitsFromConfigByBool
                  D L.config L.stage)
              []))))

theorem fixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_eq_fieldOutputBits_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
        D L =
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner
        D L := by
  simpa [
    FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner] using
    fixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_eq_fields_configRunner
      D L

theorem fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_eq_tapeAtCells_cons_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    exists first : Bool,
    exists rest : Word Bool,
      FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
          D L =
        first :: rest ∧
        FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
            D L =
          DovetailInitialLayoutInitializer.tapeAtCells []
            (some first :: List.append (rest.map some)
              (List.replicate
                (Tape.contextLength
                  (Tape.input (FixedDescriptionBoundedSimulatorInput L)))
                none)) := by
  have hlen :=
    fixedDescriptionBoundedSimulatorOutput_length_ge_header_configRunner
      D L
  cases houtput : FixedDescriptionBoundedSimulatorOutput D L with
  | nil =>
      simp [houtput] at hlen
  | cons first rest =>
      refine ⟨first, rest, ?_, ?_⟩
      · simp [FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner,
          houtput]
      rw [
        fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_eq_tapeAtCells_configRunner]
      simp [houtput, inputWithTrailingBlankPaddingCells]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_cells_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    Tape.cells
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L) =
      inputWithTrailingBlankPaddingCells
        (FixedDescriptionBoundedSimulatorOutput D L)
        (Tape.contextLength
          (Tape.input (FixedDescriptionBoundedSimulatorInput L))) := by
  rw [fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_eq_tapeAtCells_configRunner]
  cases houtput : FixedDescriptionBoundedSimulatorOutput D L with
  | nil =>
      simp [inputWithTrailingBlankPaddingCells,
        DovetailInitialLayoutInitializer.tapeAtCells, Tape.cells]
  | cons bit rest =>
      cases bit <;>
        simp [inputWithTrailingBlankPaddingCells,
          DovetailInitialLayoutInitializer.tapeAtCells, Tape.cells]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_cells_eq_outputBits_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    Tape.cells
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L) =
      List.append
        ((FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
          D L).map some)
        (List.replicate
          (Tape.contextLength
            (Tape.input (FixedDescriptionBoundedSimulatorInput L)))
          none) := by
  rw [fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_cells_configRunner]
  simp [FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner,
    FixedDescriptionBoundedSimulatorOutput,
    SimulatorLayout.asBoolInput, SimulatorLayout.encode,
    SimulatorLayout.encodeAppend,
    inputWithTrailingBlankPaddingCells, encodeCodeWordAsInput,
    encodeCodeSymbolAsInput]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_cells_eq_fields_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    Tape.cells
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L) =
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
          (Tape.contextLength
            (Tape.input (FixedDescriptionBoundedSimulatorInput L)))
          none) := by
  rw [fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_cells_eq_outputBits_configRunner]
  rw [fixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_eq_fields_configRunner]

def fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
    (L : SimulatorLayout) : Tape Bool :=
  Tape.move Direction.right
    (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
      L)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_normalizedOutput_configRunner
    (L : SimulatorLayout) :
    Tape.normalizedOutput
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
          L) =
      SimulatorLayout.asBoolInput L := by
  rw [
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner,
    Tape.normalizedOutput_move,
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_normalizedOutput_configRunner]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_cells_configRunner
    (L : SimulatorLayout) :
    Tape.cells
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
          L) =
      none :: List.append ((SimulatorLayout.asBoolInput L).map some) [none] := by
  have hlen : 1 <= (SimulatorLayout.asBoolInput L).length := by
    rw [fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_header_payloadBits_configRunner]
    simp [fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
      encodeCodeSymbolAsInput]
  cases hbits : SimulatorLayout.asBoolInput L with
  | nil =>
      simp [hbits] at hlen
  | cons first rest =>
      cases first <;> cases rest <;>
        simp [
          fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner,
          fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner,
          DovetailInitialLayoutInitializer.tapeAtCells,
          Tape.cells, Tape.move, Tape.moveRight, hbits]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_cells_eq_fields_configRunner
    (L : SimulatorLayout) :
    Tape.cells
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
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
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_cells_configRunner,
    fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_fields_configRunner]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_contextLength_configRunner
    (L : SimulatorLayout) :
    Tape.contextLength
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
          L) =
      (SimulatorLayout.asBoolInput L).length + 1 := by
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
          cases first <;> cases second <;>
            simp [
              fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner,
              fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner,
              DovetailInitialLayoutInitializer.tapeAtCells,
              Tape.contextLength, Tape.move, Tape.moveRight, hbits] <;>
            omega

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_eq_tapeAtCells_cons_cons_configRunner
    (L : SimulatorLayout) (first second : Bool) (rest : Word Bool)
    (hbits : SimulatorLayout.asBoolInput L = first :: second :: rest) :
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
        L =
      DovetailInitialLayoutInitializer.tapeAtCells
        [some first, none]
        (some second :: List.append (rest.map some) [none]) := by
  cases first <;> cases second <;>
    simp [
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner,
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner,
      DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.move, Tape.moveRight, hbits]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_exists_tapeAtCells_cons_cons_configRunner
    (L : SimulatorLayout) :
    exists first : Bool,
    exists second : Bool,
    exists rest : Word Bool,
      SimulatorLayout.asBoolInput L = first :: second :: rest ∧
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
            L =
          DovetailInitialLayoutInitializer.tapeAtCells
            [some first, none]
            (some second :: List.append (rest.map some) [none]) := by
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
          refine ⟨first, second, tail, rfl, ?_⟩
          exact
            fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_eq_tapeAtCells_cons_cons_configRunner
              L first second tail hbits

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
