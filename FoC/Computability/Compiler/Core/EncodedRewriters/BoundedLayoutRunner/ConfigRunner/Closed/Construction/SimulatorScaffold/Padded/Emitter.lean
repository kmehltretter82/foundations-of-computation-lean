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

/--
Concrete finite-machine leaf for the padded fixed-description simulator
emitter.  On an already validated simulator layout tape, it must run the fixed
description for the encoded stage bound, emit the updated simulator-layout code
at the left edge, and leave the old simulator-layout window as trailing blank
padding.
-/
theorem fixedDescriptionBoundedSimulatorPaddedEmitterExactShapeConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorPaddedEmitterExactShapeConstruction_configRunner := by
  intro D
  sorry

theorem fixedDescriptionBoundedSimulatorPaddedParserEmitterConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorPaddedParserEmitterConstruction_configRunner :=
  ⟨fixedDescriptionBoundedSimulatorPaddedParserConstruction_scaffold_configRunner,
    fixedDescriptionBoundedSimulatorPaddedEmitterExactShapeConstruction_scaffold_configRunner⟩

theorem fixedDescriptionBoundedSimulatorPaddedExactShapeConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorPaddedExactShapeConstruction_configRunner :=
  fixedDescriptionBoundedSimulatorPaddedExactShapeConstruction_of_parserEmitter_configRunner
    fixedDescriptionBoundedSimulatorPaddedParserEmitterConstruction_scaffold_configRunner

/--
Finite-machine leaf for the config-runner fixed-description simulators.

The exact right-handoff skeleton target has a context-length shrink obstruction;
see {lit}`LEAN_COUNTEREXAMPLE_OVERVIEW.md` for the archived design note.  The
live config-runner assembly should use this padded target, whose output is
equivalent to the canonical simulator layout while preserving enough blank
window to avoid a forced shrink.
-/
theorem fixedDescriptionBoundedSimulatorPaddedConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorPaddedConstruction :=
  fixedDescriptionBoundedSimulatorPaddedConstruction_of_exactShape_configRunner
    fixedDescriptionBoundedSimulatorPaddedExactShapeConstruction_scaffold_configRunner

theorem fixedDescriptionBoundedSimulatorPaddedPhaseConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorPaddedPhaseConstruction_configRunner :=
  fixedDescriptionBoundedSimulatorPaddedPhaseConstruction_of_exactShape_configRunner
    fixedDescriptionBoundedSimulatorPaddedExactShapeConstruction_scaffold_configRunner

theorem fixedDescriptionBoundedSimulatorEquivConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorEquivConstruction :=
  fixedDescriptionBoundedSimulatorEquivConstruction_of_paddedPhase_configRunner
    fixedDescriptionBoundedSimulatorPaddedPhaseConstruction_scaffold_configRunner

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
