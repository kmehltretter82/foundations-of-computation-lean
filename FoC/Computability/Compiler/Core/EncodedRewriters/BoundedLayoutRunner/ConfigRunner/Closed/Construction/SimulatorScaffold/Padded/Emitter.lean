import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.SimulatorScaffold.Padded.Emitter.PostScanner

set_option doc.verso true

/-!
# Padded simulator scaffold emitter
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

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
    FixedDescriptionBoundedSimulatorPaddedScratchEmitterExactShapeConstruction_configRunner :=
  fixedDescriptionBoundedSimulatorPaddedScratchEmitterExactShapeConstruction_of_terminal_configRunner
    fixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalConstruction_configRunner

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
