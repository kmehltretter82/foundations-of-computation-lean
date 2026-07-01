import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedParser.Scanners
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


theorem fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_fields_configRunner
    (L : SimulatorLayout) :
    SimulatorLayout.asBoolInput L =
      encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          encodeBoolWordAppend L.input
            (encodeNatAppend L.stage
              (encodeConfigurationAppend L.config
                (encodeBoolAppend L.hit [])))) := by
  simp [SimulatorLayout.asBoolInput, SimulatorLayout.encode,
    SimulatorLayout.encodeAppend]


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


end PaddedEmitter
end FixedDescriptionBoundedSimulator

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

