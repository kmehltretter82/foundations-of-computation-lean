import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.PaddedIdentity
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedEmitter.SourceShapeCore
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedEmitter.TerminalCore

set_option doc.verso true

/-!
# Padded simulator emitter source shapes

This module is upstream of the run-loop sequencing proof.  It contains the
right-shifted source tape shape and the explicit finite-machine leaf that must
eventually implement the fixed-description bounded simulation and padded
emission from that handoff.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

namespace EncodedRewriters
namespace BoundedLayoutRunner

namespace FixedDescriptionBoundedSimulator
namespace PaddedEmitter

def sourceLeftMoveOnceDescription_configRunner : MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ transition 0 none none Direction.left 1
    , transition 0 (some false) (some false) Direction.left 1
    , transition 0 (some true) (some true) Direction.left 1 ]

theorem sourceLeftMoveOnceDescription_wellFormed_configRunner :
    sourceLeftMoveOnceDescription_configRunner.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := sourceLeftMoveOnceDescription_configRunner.transitions)
      (stateCount := sourceLeftMoveOnceDescription_configRunner.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := sourceLeftMoveOnceDescription_configRunner.transitions)
      (by decide)

theorem sourceLeftMoveOnceDescription_haltTransitionFree_configRunner :
    sourceLeftMoveOnceDescription_configRunner.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := sourceLeftMoveOnceDescription_configRunner.transitions)
    (state := sourceLeftMoveOnceDescription_configRunner.halt)
    (by decide)

theorem sourceLeftMoveOnceDescription_subroutineReady_configRunner :
    sourceLeftMoveOnceDescription_configRunner.SubroutineReady :=
  ⟨sourceLeftMoveOnceDescription_wellFormed_configRunner,
    sourceLeftMoveOnceDescription_haltTransitionFree_configRunner⟩

theorem sourceLeftMoveOnceDescription_haltsFromTape_configRunner
    (T : Tape Bool) :
    sourceLeftMoveOnceDescription_configRunner.HaltsFromTape T
      (Tape.move Direction.left T) := by
  refine ⟨1, ?_⟩
  constructor <;>
    cases T with
    | mk left head right =>
        cases head with
        | none =>
            simp [sourceLeftMoveOnceDescription_configRunner,
              runConfig, stepConfig, lookupTransition, Matches,
              transition, Tape.read, Tape.write, Tape.move]
        | some b =>
            cases b <;>
              simp [sourceLeftMoveOnceDescription_configRunner,
                runConfig, stepConfig, lookupTransition, Matches,
                transition, Tape.read, Tape.write, Tape.move]

namespace SourceRewindTargetTape

theorem move_left_move_right_cons_cons_configRunner
    (first second : Bool) (rest : Word Bool) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
            (first :: second :: rest))) =
      FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
        (first :: second :: rest) := by
  cases first <;> cases second <;>
    simp [
      FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner,
      DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]

theorem move_left_move_right_simulator_configRunner
    (L : SimulatorLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
            (SimulatorLayout.asBoolInput L))) =
      FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
        (SimulatorLayout.asBoolInput L) := by
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
          simpa [hbits] using
            move_left_move_right_cons_cons_configRunner
              first second tail

end SourceRewindTargetTape

def FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner
    (bits : Word Bool) : Tape Bool :=
  Tape.move Direction.right
    (FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
      bits)

namespace RightShiftedSourceTape

theorem normalizedOutput_configRunner
    (w : Word Bool) :
    Tape.normalizedOutput
        (FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner
          w) =
      w := by
  rw [FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner]
  rw [Tape.normalizedOutput_move]
  exact
    fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTarget_normalizedOutput_configRunner
      w

theorem cells_configRunner
    (w : Word Bool) (hlen : 1 <= w.length) :
    Tape.cells
        (FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner
          w) =
      none :: List.append (w.map some) [none] := by
  cases hbits : w with
  | nil =>
      simp [hbits] at hlen
  | cons first rest =>
      cases first <;> cases rest <;>
        simp [
          FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner,
          FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner,
          DovetailInitialLayoutInitializer.tapeAtCells,
          Tape.cells, Tape.move, Tape.moveRight]

theorem eq_tapeAtCells_cons_cons_configRunner
    (first second : Bool) (rest : Word Bool) :
    FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner
        (first :: second :: rest) =
      DovetailInitialLayoutInitializer.tapeAtCells
        [some first, none]
        (some second :: List.append (rest.map some) [none]) := by
  cases first <;> cases second <;>
    simp [
      FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner,
      FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner,
      DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.move, Tape.moveRight]

theorem simulator_eq_tapeAtCells_cons_cons_configRunner
    (L : SimulatorLayout) :
    exists first : Bool,
    exists second : Bool,
    exists rest : Word Bool,
      SimulatorLayout.asBoolInput L = first :: second :: rest ∧
        FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner
            (SimulatorLayout.asBoolInput L) =
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
          simpa [hbits] using
            eq_tapeAtCells_cons_cons_configRunner first second tail

theorem simulator_cells_configRunner
    (L : SimulatorLayout) :
    Tape.cells
        (FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner
          (SimulatorLayout.asBoolInput L)) =
      none :: List.append ((SimulatorLayout.asBoolInput L).map some)
        [none] := by
  have hlen : 1 <= (SimulatorLayout.asBoolInput L).length := by
    rw [fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_header_payloadBits_configRunner]
    simp [fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
      encodeCodeSymbolAsInput]
  exact cells_configRunner (SimulatorLayout.asBoolInput L) hlen

theorem contextLength_configRunner
    (w : Word Bool) (hlen : 2 <= w.length) :
    Tape.contextLength
      (FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner
        w) =
      w.length + 1 := by
  cases hbits : w with
  | nil =>
      simp [hbits] at hlen
  | cons first rest =>
      cases hrest : rest with
      | nil =>
          simp [hbits, hrest] at hlen
      | cons second tail =>
          cases first <;> cases second <;>
            simp [
              FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner,
              FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner,
              DovetailInitialLayoutInitializer.tapeAtCells,
              Tape.contextLength, Tape.move, Tape.moveRight] <;>
            omega

theorem simulator_contextLength_configRunner
    (L : SimulatorLayout) :
    Tape.contextLength
      (FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner
        (SimulatorLayout.asBoolInput L)) =
      (SimulatorLayout.asBoolInput L).length + 1 := by
  have hlen : 2 <= (SimulatorLayout.asBoolInput L).length := by
    rw [fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_header_payloadBits_configRunner]
    simp [fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
      encodeCodeSymbolAsInput]
  exact contextLength_configRunner (SimulatorLayout.asBoolInput L) hlen

theorem move_left_eq_sourceRewindTarget_configRunner
    (w : Word Bool) (hlen : 2 <= w.length) :
    Tape.move Direction.left
      (FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner
        w) =
    FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
      w := by
  cases hbits : w with
  | nil =>
      simp [hbits] at hlen
  | cons first rest =>
      cases hrest : rest with
      | nil =>
          simp [hbits, hrest] at hlen
      | cons second tail =>
          cases first <;> cases second <;>
            simp [
              FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner,
              FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner,
              DovetailInitialLayoutInitializer.tapeAtCells,
              Tape.move, Tape.moveLeft, Tape.moveRight]

theorem simulator_move_left_eq_sourceRewindTarget_configRunner
    (L : SimulatorLayout) :
    Tape.move Direction.left
      (FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner
        (SimulatorLayout.asBoolInput L)) =
    FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
      (SimulatorLayout.asBoolInput L) := by
  have hlen : 2 <= (SimulatorLayout.asBoolInput L).length := by
    rw [fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_header_payloadBits_configRunner]
    simp [fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
      encodeCodeSymbolAsInput]
  exact move_left_eq_sourceRewindTarget_configRunner
    (SimulatorLayout.asBoolInput L) hlen

theorem afterRightSource_move_left_eq_sourceTarget_configRunner
    (L : SimulatorLayout) :
    Tape.move Direction.left
      (FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner
        (SimulatorLayout.asBoolInput L)) =
    FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
      (SimulatorLayout.asBoolInput L) :=
  simulator_move_left_eq_sourceRewindTarget_configRunner L

theorem move_left_move_right_cons_cons_configRunner
    (first second : Bool) (rest : Word Bool) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner
            (first :: second :: rest))) =
      FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner
        (first :: second :: rest) := by
  cases first <;> cases second <;> cases rest <;>
    simp [
      FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner,
      FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner,
      DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]

theorem move_left_move_right_simulator_configRunner
    (L : SimulatorLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner
            (SimulatorLayout.asBoolInput L))) =
      FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner
        (SimulatorLayout.asBoolInput L) := by
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
          simpa [hbits] using
            move_left_move_right_cons_cons_configRunner
              first second tail

end RightShiftedSourceTape

theorem sourceLeftMoveOnceDescription_haltsFrom_rightShiftedSource_configRunner
    (L : SimulatorLayout) :
    sourceLeftMoveOnceDescription_configRunner.HaltsFromTape
      (FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner
        (SimulatorLayout.asBoolInput L))
      (FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
        (SimulatorLayout.asBoolInput L)) := by
  simpa [RightShiftedSourceTape.afterRightSource_move_left_eq_sourceTarget_configRunner
      L] using
    sourceLeftMoveOnceDescription_haltsFromTape_configRunner
      (FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner
        (SimulatorLayout.asBoolInput L))

theorem
    fixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_normalizedOutput_eq_fields_configRunner
    (L : SimulatorLayout) :
    Tape.normalizedOutput
        (FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner
          (SimulatorLayout.asBoolInput L)) =
      encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          encodeBoolWordAppend L.input
            (encodeNatAppend L.stage
              (encodeConfigurationAppend L.config
                (encodeBoolAppend L.hit [])))) := by
  rw [RightShiftedSourceTape.normalizedOutput_configRunner,
    fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_fields_configRunner]

theorem
    fixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_cells_eq_fields_configRunner
    (L : SimulatorLayout) :
    Tape.cells
        (FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner
          (SimulatorLayout.asBoolInput L)) =
      none ::
        List.append
          ((encodeCodeWordAsInput
            (MachineCodeSymbol.header ::
              encodeBoolWordAppend L.input
                (encodeNatAppend L.stage
                  (encodeConfigurationAppend L.config
                    (encodeBoolAppend L.hit []))))).map some)
          [none] := by
  rw [RightShiftedSourceTape.simulator_cells_configRunner,
    fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_fields_configRunner]

theorem
    fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTarget_normalizedOutput_eq_fields_configRunner
    (L : SimulatorLayout) :
    Tape.normalizedOutput
        (FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
          (SimulatorLayout.asBoolInput L)) =
      encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          encodeBoolWordAppend L.input
            (encodeNatAppend L.stage
              (encodeConfigurationAppend L.config
                (encodeBoolAppend L.hit [])))) := by
  rw [
    fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTarget_normalizedOutput_configRunner,
    fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_fields_configRunner]

theorem
    fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTarget_cells_eq_fields_configRunner
    (L : SimulatorLayout) :
    Tape.cells
        (FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
          (SimulatorLayout.asBoolInput L)) =
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
    fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTarget_cells_configRunner,
    fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_fields_configRunner]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_contextLength_ge_afterRight_source_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    Tape.contextLength
      (FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner
        (SimulatorLayout.asBoolInput L)) <=
      Tape.contextLength
      (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner D L) := by
  have hsource :=
    RightShiftedSourceTape.simulator_contextLength_configRunner L
  have houtput :=
    fixedDescriptionBoundedSimulatorOutput_length_ge_header_configRunner D L
  have hinputLen : 2 <= (SimulatorLayout.asBoolInput L).length := by
    rw [fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_header_payloadBits_configRunner]
    simp [fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
      encodeCodeSymbolAsInput]
  rw [hsource]
  rw [fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_eq_tapeAtCells_configRunner]
  cases hinput : SimulatorLayout.asBoolInput L with
  | nil =>
      simp [hinput] at hinputLen
  | cons inputHead inputRest =>
      cases houtputBits : FixedDescriptionBoundedSimulatorOutput D L with
      | nil =>
          simp [houtputBits] at houtput
      | cons outputHead outputRest =>
          simp [
            FixedDescriptionBoundedSimulatorInput,
            inputWithTrailingBlankPaddingCells,
            DovetailInitialLayoutInitializer.tapeAtCells,
            Tape.contextLength, Tape.input, hinput, houtputBits] at *
          omega

def sourceScanRightToBlankLeftDescription_configRunner : MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ transition 0 none none Direction.left 1
    , transition 0 (some false) (some false) Direction.right 0
    , transition 0 (some true) (some true) Direction.right 0 ]

theorem sourceScanRightToBlankLeftDescription_wellFormed_configRunner :
    sourceScanRightToBlankLeftDescription_configRunner.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := sourceScanRightToBlankLeftDescription_configRunner.transitions)
      (stateCount :=
        sourceScanRightToBlankLeftDescription_configRunner.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := sourceScanRightToBlankLeftDescription_configRunner.transitions)
      (by decide)

theorem sourceScanRightToBlankLeftDescription_haltTransitionFree_configRunner :
    sourceScanRightToBlankLeftDescription_configRunner.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := sourceScanRightToBlankLeftDescription_configRunner.transitions)
    (state := sourceScanRightToBlankLeftDescription_configRunner.halt)
    (by decide)

theorem sourceScanRightToBlankLeftDescription_subroutineReady_configRunner :
    sourceScanRightToBlankLeftDescription_configRunner.SubroutineReady :=
  ⟨sourceScanRightToBlankLeftDescription_wellFormed_configRunner,
    sourceScanRightToBlankLeftDescription_haltTransitionFree_configRunner⟩

def sourceRightEndLeftTape_configRunner
    (bits : Word Bool) : Tape Bool :=
  Tape.move Direction.left
    (DovetailInitialLayoutInitializer.tapeAtCells
      (List.append (bits.reverse.map some) [none]) [none])

theorem sourceRightEndLeftTape_cells_configRunner
    (bits : Word Bool) :
    Tape.cells (sourceRightEndLeftTape_configRunner bits) =
      none :: List.append (bits.map some) [none] := by
  cases bits with
  | nil =>
      simp [sourceRightEndLeftTape_configRunner,
        DovetailInitialLayoutInitializer.tapeAtCells, Tape.cells,
        Tape.move, Tape.moveLeft]
  | cons bit rest =>
      cases hrev : rest.reverse with
      | nil =>
          have hrest : rest = [] := by
            simpa using congrArg List.reverse hrev
          simp [sourceRightEndLeftTape_configRunner,
            DovetailInitialLayoutInitializer.tapeAtCells, Tape.cells,
            Tape.move, Tape.moveLeft, hrest]
      | cons head tail =>
          have hrest : rest = (head :: tail).reverse := by
            rw [← hrev, List.reverse_reverse]
          simp [sourceRightEndLeftTape_configRunner,
            DovetailInitialLayoutInitializer.tapeAtCells, Tape.cells,
            Tape.move, Tape.moveLeft, hrest, List.map_reverse,
            List.append_assoc]

theorem sourceRightEndLeftTape_normalizedOutput_configRunner
    (bits : Word Bool) :
    Tape.normalizedOutput (sourceRightEndLeftTape_configRunner bits) =
      bits := by
  rw [Tape.normalizedOutput]
  rw [sourceRightEndLeftTape_cells_configRunner]
  cases bits <;>
    simp [Function.comp_def]

theorem sourceRightEndLeftTape_move_right_eq_terminal_with_blank_configRunner
    (bits : Word Bool) :
    Tape.move Direction.right (sourceRightEndLeftTape_configRunner bits) =
      DovetailInitialLayoutInitializer.tapeAtCells
        (List.append (bits.reverse.map some) [none]) [] := by
  rw [sourceRightEndLeftTape_configRunner]
  cases hleft : bits.reverse.map some with
  | nil =>
      simp [DovetailInitialLayoutInitializer.tapeAtCells,
        Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons cell rest =>
      simp [DovetailInitialLayoutInitializer.tapeAtCells,
        Tape.move, Tape.moveLeft, Tape.moveRight]

theorem sourceRightEndLeftTape_move_right_eq_terminalCore_configRunner
    (L : SimulatorLayout) :
    Tape.move Direction.right
        (sourceRightEndLeftTape_configRunner
          (SimulatorLayout.asBoolInput L)) =
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalTape_configRunner
        true L := by
  simpa [fixedDescriptionBoundedSimulatorPaddedEmitterTerminalTape_configRunner]
    using
      sourceRightEndLeftTape_move_right_eq_terminal_with_blank_configRunner
        (SimulatorLayout.asBoolInput L)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalTape_true_move_right_move_left_configRunner
    (L : SimulatorLayout) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalTape_configRunner
            true L)) =
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalTape_configRunner
        true L := by
  cases hleft : (SimulatorLayout.asBoolInput L).reverse.map some with
  | nil =>
      simp [
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalTape_configRunner,
        DovetailInitialLayoutInitializer.tapeAtCells,
        Tape.move, Tape.moveLeft, Tape.moveRight, hleft]
  | cons cell rest =>
      simp [
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalTape_configRunner,
        DovetailInitialLayoutInitializer.tapeAtCells,
        Tape.move, Tape.moveLeft, Tape.moveRight, hleft]

theorem sourceRightEndLeftTape_move_right_equiv_terminal_configRunner
    (bits : Word Bool) :
    Tape.Equiv
      (Tape.move Direction.right (sourceRightEndLeftTape_configRunner bits))
      (DovetailInitialLayoutInitializer.tapeAtCells
        (bits.reverse.map some) []) := by
  rw [sourceRightEndLeftTape_move_right_eq_terminal_with_blank_configRunner]
  constructor
  · exact
      fixedDescriptionBoundedSimulator_dropTrailingNone_append_none
        (bits.reverse.map some)
  constructor <;>
    rfl

theorem sourceRightEndLeftTape_simulator_normalizedOutput_eq_fields_configRunner
    (L : SimulatorLayout) :
    Tape.normalizedOutput
        (sourceRightEndLeftTape_configRunner
          (SimulatorLayout.asBoolInput L)) =
      encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          encodeBoolWordAppend L.input
            (encodeNatAppend L.stage
              (encodeConfigurationAppend L.config
                (encodeBoolAppend L.hit [])))) := by
  rw [sourceRightEndLeftTape_normalizedOutput_configRunner,
    fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_fields_configRunner]

theorem sourceRightEndLeftTape_cells_eq_sourceRewindTarget_cells_configRunner
    (bits : Word Bool) :
    Tape.cells (sourceRightEndLeftTape_configRunner bits) =
      Tape.cells
        (FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
          bits) := by
  rw [sourceRightEndLeftTape_cells_configRunner,
    fixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTarget_cells_configRunner]

theorem sourceRightEndLeftTape_simulator_cells_eq_sourceRewindTarget_cells_configRunner
    (L : SimulatorLayout) :
    Tape.cells
        (sourceRightEndLeftTape_configRunner
          (SimulatorLayout.asBoolInput L)) =
      Tape.cells
        (FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
          (SimulatorLayout.asBoolInput L)) :=
  sourceRightEndLeftTape_cells_eq_sourceRewindTarget_cells_configRunner
    (SimulatorLayout.asBoolInput L)

theorem sourceRightEndLeftTape_simulator_cells_eq_fields_configRunner
    (L : SimulatorLayout) :
    Tape.cells
        (sourceRightEndLeftTape_configRunner
          (SimulatorLayout.asBoolInput L)) =
      none ::
        List.append
          ((encodeCodeWordAsInput
            (MachineCodeSymbol.header ::
              encodeBoolWordAppend L.input
                (encodeNatAppend L.stage
                  (encodeConfigurationAppend L.config
                    (encodeBoolAppend L.hit []))))).map some)
          [none] := by
  rw [sourceRightEndLeftTape_cells_configRunner,
    fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_fields_configRunner]

theorem sourceRightEndLeftTape_contextLength_configRunner
    (bits : Word Bool) :
    Tape.contextLength (sourceRightEndLeftTape_configRunner bits) =
      bits.length + 1 := by
  cases bits with
  | nil =>
      simp [sourceRightEndLeftTape_configRunner,
        DovetailInitialLayoutInitializer.tapeAtCells, Tape.contextLength,
        Tape.move, Tape.moveLeft]
  | cons bit rest =>
      cases hrev : rest.reverse with
      | nil =>
          have hrest : rest = [] := by
            simpa using congrArg List.reverse hrev
          cases bit <;>
            simp [sourceRightEndLeftTape_configRunner,
              DovetailInitialLayoutInitializer.tapeAtCells,
              Tape.contextLength, Tape.move, Tape.moveLeft, hrest]
      | cons head tail =>
          have hrest : rest = (head :: tail).reverse := by
            rw [← hrev, List.reverse_reverse]
          cases bit <;>
            simp [sourceRightEndLeftTape_configRunner,
              DovetailInitialLayoutInitializer.tapeAtCells,
              Tape.contextLength, Tape.move, Tape.moveLeft, hrest,
              List.append_assoc] <;>
            omega

theorem sourceRightEndLeftTape_simulator_contextLength_configRunner
    (L : SimulatorLayout) :
    Tape.contextLength
        (sourceRightEndLeftTape_configRunner
          (SimulatorLayout.asBoolInput L)) =
      (SimulatorLayout.asBoolInput L).length + 1 :=
  sourceRightEndLeftTape_contextLength_configRunner
    (SimulatorLayout.asBoolInput L)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_contextLength_ge_sourceRightEndLeft_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    Tape.contextLength
        (sourceRightEndLeftTape_configRunner
          (SimulatorLayout.asBoolInput L)) <=
      Tape.contextLength
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L) := by
  rw [sourceRightEndLeftTape_simulator_contextLength_configRunner]
  rw [← RightShiftedSourceTape.simulator_contextLength_configRunner]
  exact
    fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_contextLength_ge_afterRight_source_configRunner
      D L

def sourceScanRightToBlankLeftHaltTape_configRunner
    (leftRev : List (Option Bool)) (bits : Word Bool) : Tape Bool :=
  Tape.move Direction.left
    (DovetailInitialLayoutInitializer.tapeAtCells
      (List.append (bits.reverse.map some) leftRev) [none])

theorem sourceScanRightToBlankLeftDescription_run_configRunner
    (leftRev : List (Option Bool)) (bits : Word Bool) :
    sourceScanRightToBlankLeftDescription_configRunner.runConfig
        (bits.length + 1)
        { state := sourceScanRightToBlankLeftDescription_configRunner.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells leftRev
              (List.append (bits.map some) [none]) } =
      { state := sourceScanRightToBlankLeftDescription_configRunner.halt
        tape :=
          sourceScanRightToBlankLeftHaltTape_configRunner leftRev bits } := by
  induction bits generalizing leftRev with
  | nil =>
      simp [sourceScanRightToBlankLeftDescription_configRunner,
        sourceScanRightToBlankLeftHaltTape_configRunner,
        DovetailInitialLayoutInitializer.tapeAtCells,
        runConfig, stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft]
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 = 1 + (rest.length + 1) by
        simp
        omega]
      rw [runConfig_add]
      have hstep :
          sourceScanRightToBlankLeftDescription_configRunner.runConfig 1
              { state :=
                  sourceScanRightToBlankLeftDescription_configRunner.start
                tape :=
                  DovetailInitialLayoutInitializer.tapeAtCells leftRev
                    (List.append ((bit :: rest).map some) [none]) } =
            { state := sourceScanRightToBlankLeftDescription_configRunner.start
              tape :=
                DovetailInitialLayoutInitializer.tapeAtCells
                  (some bit :: leftRev)
                  (List.append (rest.map some) [none]) } := by
        cases bit <;>
          cases rest <;>
          simp [sourceScanRightToBlankLeftDescription_configRunner,
            DovetailInitialLayoutInitializer.tapeAtCells,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveRight]
      rw [hstep]
      simpa [sourceScanRightToBlankLeftHaltTape_configRunner,
        List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: leftRev)

theorem sourceScanRightToBlankLeftHaltTape_eq_sourceRightEndLeft_configRunner
    (bits : Word Bool) :
    sourceScanRightToBlankLeftHaltTape_configRunner [none] bits =
      sourceRightEndLeftTape_configRunner bits := by
  rfl

theorem sourceScanRightToBlankLeftDescription_haltsFrom_sourceRewindTarget_configRunner
    (bits : Word Bool) :
    sourceScanRightToBlankLeftDescription_configRunner.HaltsFromTape
      (FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
        bits)
      (sourceRightEndLeftTape_configRunner bits) := by
  refine ⟨bits.length + 1, ?_⟩
  have hrun :=
    sourceScanRightToBlankLeftDescription_run_configRunner [none] bits
  constructor
  · simpa [
      FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner,
      sourceScanRightToBlankLeftHaltTape_eq_sourceRightEndLeft_configRunner]
      using congrArg Configuration.state hrun
  · simpa [
      FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner,
      sourceScanRightToBlankLeftHaltTape_eq_sourceRightEndLeft_configRunner]
      using congrArg Configuration.tape hrun

theorem sourceRightEndLeftTape_move_left_move_right_configRunner
    (bits : Word Bool) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (sourceRightEndLeftTape_configRunner bits)) =
      sourceRightEndLeftTape_configRunner bits := by
  exact
    Tape.move_left_move_right_eq_self_of_right_cons
      (sourceRightEndLeftTape_configRunner bits)
      (cell := none) (right := [])
      (by
        cases hrev : bits.reverse with
        | nil =>
            simp [sourceRightEndLeftTape_configRunner,
              DovetailInitialLayoutInitializer.tapeAtCells,
              Tape.move, Tape.moveLeft, hrev]
        | cons head tail =>
            simp [sourceRightEndLeftTape_configRunner,
              DovetailInitialLayoutInitializer.tapeAtCells,
              Tape.move, Tape.moveLeft, hrev])

namespace AfterSourceRewindTarget

def Spec
    (D postLeft : MachineDescription) : Prop :=
  postLeft.SubroutineReady ∧
    forall L : SimulatorLayout,
      postLeft.HaltsFromTape
        (FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
          (SimulatorLayout.asBoolInput L))
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def Construction : Prop :=
  forall D : MachineDescription,
    exists postLeft : MachineDescription,
      Spec D postLeft

end AfterSourceRewindTarget

namespace AfterSourceRightEndLeft

def Spec
    (D postScan : MachineDescription) : Prop :=
  postScan.SubroutineReady ∧
    forall L : SimulatorLayout,
      postScan.HaltsFromTape
        (sourceRightEndLeftTape_configRunner
          (SimulatorLayout.asBoolInput L))
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def Construction : Prop :=
  forall D : MachineDescription,
    exists postScan : MachineDescription,
      Spec D postScan

/--
Core finite-machine leaf after the restored simulator-layout source has been
scanned to the final source bit immediately left of the terminal blank.  The
source-rewind-target construction below only performs the checked finite scan
into this shape.
-/
theorem finiteMachineCore : Construction := by
  intro D
  rcases
      fixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreConstruction_configRunner
        D with
    ⟨post, hpost⟩
  refine
    ⟨SeqViaCanonicalLeft
      CommonGround.FiniteTransducers.rightMoveOnceDescription post, ?_⟩
  constructor
  · exact
      SeqViaCanonicalLeft_subroutineReady
        CommonGround.FiniteTransducers.rightMoveOnceDescription_subroutineReady
        hpost.left
  · intro L
    have hright :
        CommonGround.FiniteTransducers.rightMoveOnceDescription.HaltsFromTape
          (sourceRightEndLeftTape_configRunner
            (SimulatorLayout.asBoolInput L))
          (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalTape_configRunner
            true L) := by
      simpa [sourceRightEndLeftTape_move_right_eq_terminalCore_configRunner L]
        using
          CommonGround.FiniteTransducers.rightMoveOnceDescription_haltsFromTape
            (sourceRightEndLeftTape_configRunner
              (SimulatorLayout.asBoolInput L))
    exact
      SeqViaCanonicalLeft_haltsFromTape_of_haltsFromTape
        CommonGround.FiniteTransducers.rightMoveOnceDescription_subroutineReady
        hpost.left
        hright
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalTape_true_move_right_move_left_configRunner
          L)
        (hpost.right true L)

end AfterSourceRightEndLeft

namespace AfterSourceRewindTarget

def fromAfterSourceRightEndLeft
    (postScan : MachineDescription) : MachineDescription :=
  SeqViaCanonical sourceScanRightToBlankLeftDescription_configRunner postScan

theorem spec_of_afterSourceRightEndLeft
    {D postScan : MachineDescription}
    (hpostScan :
      AfterSourceRightEndLeft.Spec D postScan) :
    Spec D (fromAfterSourceRightEndLeft postScan) := by
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        sourceScanRightToBlankLeftDescription_subroutineReady_configRunner
        hpostScan.left
  · intro L
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        sourceScanRightToBlankLeftDescription_subroutineReady_configRunner
        hpostScan.left
        (sourceScanRightToBlankLeftDescription_haltsFrom_sourceRewindTarget_configRunner
          (SimulatorLayout.asBoolInput L))
        (sourceRightEndLeftTape_move_left_move_right_configRunner
          (SimulatorLayout.asBoolInput L))
        (hpostScan.right L)

theorem construction_of_afterSourceRightEndLeft
    (hpostScan : AfterSourceRightEndLeft.Construction) :
    Construction := by
  intro D
  rcases hpostScan D with ⟨postScan, hpostScanD⟩
  exact
    ⟨fromAfterSourceRightEndLeft postScan,
      spec_of_afterSourceRightEndLeft hpostScanD⟩

/--
Core finite-machine leaf after the right-shifted source has been moved back to
the canonical source-rewind target.  A checked finite scan moves the head to the
right end of the restored source, where the remaining simulation/emission leaf
lives.
-/
theorem finiteMachineCore : Construction :=
  construction_of_afterSourceRightEndLeft
    AfterSourceRightEndLeft.finiteMachineCore

end AfterSourceRewindTarget

namespace AfterRightShiftedInput

def Spec
    (D afterRight : MachineDescription) : Prop :=
  afterRight.SubroutineReady ∧
    forall L : SimulatorLayout,
      afterRight.HaltsFromTape
        (FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner
          (SimulatorLayout.asBoolInput L))
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def Construction : Prop :=
  forall D : MachineDescription,
    exists afterRight : MachineDescription,
      Spec D afterRight

def fromAfterSourceRewindTarget
    (postLeft : MachineDescription) : MachineDescription :=
  SeqViaCanonical sourceLeftMoveOnceDescription_configRunner postLeft

theorem spec_of_afterSourceRewindTarget
    {D postLeft : MachineDescription}
    (hpostLeft :
      AfterSourceRewindTarget.Spec D postLeft) :
    Spec D (fromAfterSourceRewindTarget postLeft) := by
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        sourceLeftMoveOnceDescription_subroutineReady_configRunner
        hpostLeft.left
  · intro L
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        sourceLeftMoveOnceDescription_subroutineReady_configRunner
        hpostLeft.left
        (sourceLeftMoveOnceDescription_haltsFrom_rightShiftedSource_configRunner
          L)
        (SourceRewindTargetTape.move_left_move_right_simulator_configRunner
          L)
        (hpostLeft.right L)

theorem construction_of_afterSourceRewindTarget
    (hpostLeft : AfterSourceRewindTarget.Construction) :
    Construction := by
  intro D
  rcases hpostLeft D with ⟨postLeft, hpostLeftD⟩
  exact
    ⟨fromAfterSourceRewindTarget postLeft,
      spec_of_afterSourceRewindTarget hpostLeftD⟩

/--
Concrete finite-machine leaf for the padded fixed-description simulator
emitter after the scanner/rewind phases have handed off one cell to the right
of the validated simulator-layout source.

This is the non-circular obligation: for a fixed description {lean}`D`, parse
the source fields, run {lean}`D` for the encoded stage count with the stage-zero
hit check included, and emit the exact
{name}`FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner`.
-/
theorem finiteMachineCore : Construction := by
  exact construction_of_afterSourceRewindTarget
    AfterSourceRewindTarget.finiteMachineCore

end AfterRightShiftedInput

namespace AfterSourceRewindTarget

def fromAfterRightShiftedInput
    (afterRight : MachineDescription) : MachineDescription :=
  SeqViaCanonical
    FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner
    afterRight

theorem returnToRightShiftedInput_haltsFrom_sourceRewindTarget_configRunner
    (L : SimulatorLayout) :
    FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner.HaltsFromTape
      (FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
        (SimulatorLayout.asBoolInput L))
      (FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner
        (SimulatorLayout.asBoolInput L)) := by
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
          · cases first <;> cases second <;>
              simp [
                FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner,
                FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner,
                DovetailInitialLayoutInitializer.tapeAtCells,
                runConfig, stepConfig, lookupTransition, Matches,
                keepMove, transition, Tape.read, Tape.write, Tape.move,
                Tape.moveLeft, Tape.moveRight]
          · cases first <;> cases second <;>
              simp [
                FixedDescriptionBoundedSimulatorPaddedEmitterRightShiftedSourceTape_configRunner,
                FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner,
                FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner,
                DovetailInitialLayoutInitializer.tapeAtCells,
                runConfig, stepConfig, lookupTransition, Matches,
                keepMove, transition, Tape.read, Tape.write, Tape.move,
                Tape.moveLeft, Tape.moveRight]

theorem spec_of_afterRightShiftedInput
    {D afterRight : MachineDescription}
    (hafterRight :
      AfterRightShiftedInput.Spec D afterRight) :
    Spec D (fromAfterRightShiftedInput afterRight) := by
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_subroutineReady_configRunner
        hafterRight.left
  · intro L
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_subroutineReady_configRunner
        hafterRight.left
        (returnToRightShiftedInput_haltsFrom_sourceRewindTarget_configRunner
          L)
        (RightShiftedSourceTape.move_left_move_right_simulator_configRunner
          L)
        (hafterRight.right L)

theorem construction_of_afterRightShiftedInput
    (hafterRight : AfterRightShiftedInput.Construction) :
    Construction := by
  intro D
  rcases hafterRight D with ⟨afterRight, hafterRightD⟩
  exact
    ⟨fromAfterRightShiftedInput afterRight,
      spec_of_afterRightShiftedInput hafterRightD⟩

/--
Post-left construction for the padded simulator emitter, reduced to the
post-left finite-machine core.
-/
theorem construction : Construction :=
  finiteMachineCore

end AfterSourceRewindTarget

end PaddedEmitter
end FixedDescriptionBoundedSimulator

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
