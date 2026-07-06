import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Simulator.PaddedEmitter.Terminal

set_option doc.verso true

/-!
# Padded simulator scaffold emitter
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
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
    ⟨fixedDescriptionBoundedSimulatorPaddedParserEquivConstruction_scaffold_configRunner,
      fixedDescriptionBoundedSimulatorPaddedEmitterExactShapeConstruction_of_scratch_configRunner
        (fixedDescriptionBoundedSimulatorPaddedScratchEmitterExactShapeConstruction_of_terminal_configRunner
          FixedDescriptionBoundedSimulator.PaddedEmitter.Terminal.construction)⟩

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
