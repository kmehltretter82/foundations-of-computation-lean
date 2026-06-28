import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.PaddedEmitters
import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.SimulatorScaffold.Padded.Parser

set_option doc.verso true

/-!
# Padded simulator scaffold emitter
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

namespace EncodedRewriters
namespace BoundedLayoutRunner

open CanonicalLayouts.DovetailLayoutScanner
open CanonicalLayouts.DovetailStagePrefix
open CommonGround.SeqComposition

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

def FixedDescriptionBoundedSimulatorPaddedScratchEmitterExactShapeSpec_configRunner
    (D emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall L : SimulatorLayout,
      emitter.HaltsWithTape
        (SimulatorLayout.asBoolInput L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedScratchEmitterExactShapeConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists emitter : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedScratchEmitterExactShapeSpec_configRunner
        D emitter

theorem fixedDescriptionBoundedSimulatorPaddedEmitterExactShapeSpec_of_scratch_configRunner
    {D emitter : MachineDescription}
    (hemits :
      FixedDescriptionBoundedSimulatorPaddedScratchEmitterExactShapeSpec_configRunner
        D emitter) :
    FixedDescriptionBoundedSimulatorPaddedEmitterExactShapeSpec_configRunner
      D emitter := by
  constructor
  · exact hemits.left
  · intro L
    simpa [
      fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_eq_outputTape_configRunner
        D L] using
      hemits.right L

theorem fixedDescriptionBoundedSimulatorPaddedEmitterExactShapeConstruction_of_scratch_configRunner
    (hemits :
      FixedDescriptionBoundedSimulatorPaddedScratchEmitterExactShapeConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterExactShapeConstruction_configRunner := by
  intro D
  rcases hemits D with ⟨emitter, hemitsD⟩
  exact
    ⟨emitter,
      fixedDescriptionBoundedSimulatorPaddedEmitterExactShapeSpec_of_scratch_configRunner
        hemitsD⟩

/--
Concrete finite-machine leaf for the padded fixed-description simulator
emitter.  On an already validated simulator layout tape, it must run the fixed
description for the encoded stage bound, emit the updated simulator-layout code
at the left edge, and leave the old simulator-layout window as trailing blank
padding.
-/
theorem fixedDescriptionBoundedSimulatorPaddedScratchEmitterExactShapeConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorPaddedScratchEmitterExactShapeConstruction_configRunner := by
  intro D
  sorry

theorem fixedDescriptionBoundedSimulatorPaddedEmitterExactShapeConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterExactShapeConstruction_configRunner :=
  fixedDescriptionBoundedSimulatorPaddedEmitterExactShapeConstruction_of_scratch_configRunner
    fixedDescriptionBoundedSimulatorPaddedScratchEmitterExactShapeConstruction_scaffold_configRunner

theorem fixedDescriptionBoundedSimulatorPaddedParserEquivEmitterConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorPaddedParserEquivEmitterConstruction_configRunner :=
  ⟨fixedDescriptionBoundedSimulatorPaddedParserEquivConstruction_scaffold_configRunner,
    fixedDescriptionBoundedSimulatorPaddedEmitterExactShapeConstruction_scaffold_configRunner⟩

/--
Finite-machine leaf for the config-runner fixed-description simulators.

The exact right-handoff skeleton target has a context-length shrink obstruction;
see {lit}`LEAN_COUNTEREXAMPLE_OVERVIEW.md` for the archived design note.  The
live config-runner assembly should use this padded target, whose output is
equivalent to the canonical simulator layout while preserving enough blank
window to avoid a forced shrink.
-/
theorem fixedDescriptionBoundedSimulatorEquivConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorEquivConstruction :=
  fixedDescriptionBoundedSimulatorEquivConstruction_of_parserEquivEmitter_configRunner
    fixedDescriptionBoundedSimulatorPaddedParserEquivEmitterConstruction_scaffold_configRunner

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
