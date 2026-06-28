import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.PaddedEmitters
import FoC.Computability.Compiler.Core.FixedDescriptionBoundedSimulator.CodeRightShifted

set_option doc.verso true

/-!
# Padded simulator scaffold emitter shapes
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

def FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
    (D : MachineDescription)
    (L : SimulatorLayout) : Word Bool :=
  FixedDescriptionBoundedSimulatorOutput D L

def FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
    (L : SimulatorLayout) : Nat :=
  Tape.contextLength
    (Tape.input (FixedDescriptionBoundedSimulatorInput L))

def FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
    (D : MachineDescription)
    (L : SimulatorLayout) : Tape Bool :=
  ScratchPaddedOutputTape
    (FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner D)
    FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
    L

theorem fixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_eq_rightShiftedOutput_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner D L =
      encodeCodeWordAsInput
        (FixedDescriptionBoundedSimulatorCodeRightShiftedOutputCode D L) := by
  rfl

theorem fixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_eq_fields_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner D L =
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
                  [])))) := by
  rfl

theorem fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_eq_outputTape_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner D L =
      FixedDescriptionBoundedSimulatorPaddedOutputTape D L := by
  cases houtput : FixedDescriptionBoundedSimulatorOutput D L with
  | nil =>
      simp [FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner,
        ScratchPaddedOutputTape,
        FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner,
        FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner,
        FixedDescriptionBoundedSimulatorPaddedOutputTape,
        FixedDescriptionBoundedSimulatorPaddedTape,
        inputWithTrailingBlankPadding, houtput]
  | cons bit rest =>
      simp [FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner,
        ScratchPaddedOutputTape,
        FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner,
        FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner,
        FixedDescriptionBoundedSimulatorPaddedOutputTape,
        FixedDescriptionBoundedSimulatorPaddedTape,
        inputWithTrailingBlankPadding, houtput]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_normalizedOutput_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    Tape.normalizedOutput
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L) =
      FixedDescriptionBoundedSimulatorOutput D L := by
  simpa [FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner,
    FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner] using
    ScratchPaddedOutputTape_normalizedOutput
      (FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner D)
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
      L

theorem fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_eq_tapeAtCells_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner D L =
      DovetailInitialLayoutInitializer.tapeAtCells []
        (inputWithTrailingBlankPaddingCells
          (FixedDescriptionBoundedSimulatorOutput D L)
          (Tape.contextLength
            (Tape.input (FixedDescriptionBoundedSimulatorInput L)))) := by
  simpa [FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner,
    ScratchPaddedOutputTape,
    FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner,
    FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner] using
    inputWithTrailingBlankPadding_eq_tapeAtCells
      (FixedDescriptionBoundedSimulatorOutput D L)
      (Tape.contextLength
        (Tape.input (FixedDescriptionBoundedSimulatorInput L)))

theorem fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_equiv_canonical_configRunner
    (D : MachineDescription) (L : SimulatorLayout) :
    Tape.Equiv
      (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
        D L)
      (FixedDescriptionBoundedSimulatorCanonicalOutputTape D L) := by
  rw [
    fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_eq_outputTape_configRunner
      D L]
  exact FixedDescriptionBoundedSimulatorPaddedOutputTape_equiv_canonical D L

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
