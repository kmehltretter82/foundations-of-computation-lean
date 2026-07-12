import FoC.Computability.Compiler.ClosedCfg.TerminalCore.SourceTapes
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.RightEdgeRewind

set_option doc.verso true

/-!
# Padded simulator emitter terminal core

Only the live right-scratch and right-shifted source surfaces remain here. The
former tape-shape/normalized-output lattice had no declaration-level consumer
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

theorem fixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_length_ge_two_configRunner
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

theorem fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_eq_FSTTargetTape_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner D L =
      CommonGround.FiniteTransducers.FSTTargetTape
        (FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner D L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner L) := by
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
              ScratchPaddedOutputTape,
              CommonGround.FiniteTransducers.FSTTargetTape,
              inputWithTrailingBlankPadding,
              CommonGround.FiniteTransducers.inputWithTrailingBlankPadding,
              FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner,
              houtput, Tape.move, Tape.moveRight]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_cells_eq_outputBits_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    Tape.cells
        (FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner D L) =
      List.append
        ((FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner D L).map some)
        (List.replicate
          (Tape.contextLength (Tape.input (FixedDescriptionBoundedSimulatorInput L)))
          none) := by
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
              FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner,
              houtput, Tape.cells, Tape.move, Tape.moveRight]

def FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner
    (D : MachineDescription) (L : SimulatorLayout) : Word Bool :=
  encodeCodeWordAsInput
    (MachineCodeSymbol.header ::
      encodeBoolWordAppend L.input
        (encodeNatAppend L.stage
          (encodeConfigurationAppend (D.runConfig L.stage L.config)
            (encodeBoolAppend
              (L.hit || SimulatorLayout.hitsFromConfigByBool D L.config L.stage)
              []))))

theorem fixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_eq_fieldOutputBits_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner D L =
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner D L := by
  simpa [FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner] using
    fixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_eq_fields_configRunner D L

def fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
    (L : SimulatorLayout) : Tape Bool :=
  Tape.move Direction.right
    (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner L)

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
