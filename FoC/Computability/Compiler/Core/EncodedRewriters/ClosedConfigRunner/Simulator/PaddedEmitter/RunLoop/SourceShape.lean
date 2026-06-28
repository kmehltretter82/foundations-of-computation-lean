import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedEmitter.Terminal

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

def FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindSourceTape_configRunner
    (bits : Word Bool) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells (bits.reverse.map some) []

def FixedDescriptionBoundedSimulatorPaddedEmitterSourceRewindTargetTape_configRunner
    (bits : Word Bool) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells [none]
    (List.append (bits.map some) [none])

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

namespace FixedDescriptionBoundedSimulator
namespace PaddedEmitter
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

theorem fixedDescriptionBoundedSimulatorOutput_length_ge_header_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    4 <= (FixedDescriptionBoundedSimulatorOutput D L).length := by
  rw [FixedDescriptionBoundedSimulatorOutput]
  rw [fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_header_payloadBits_configRunner]
  simp [fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
    encodeCodeSymbolAsInput]

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
  intro D
  sorry

end AfterRightShiftedInput

end PaddedEmitter
end FixedDescriptionBoundedSimulator

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
