import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterEquiv
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Simulator.PaddedEmitter.Equiv

set_option doc.verso true

/-!
# Fixed-description simulator construction from the #18 leaves

The parser and emitter already consume the honest equivalence-valued terminal
contract.  This module carries the two explicit finite leaves through that
adapter stack to the public fixed-description simulator construction.
-/

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner

theorem fixedDescriptionBoundedSimulatorEquivConstruction_of_runConfigEmitterLeaves_configRunner
    (hcfg :
      RunConfigEmitterCore.FullPipeline.CanonicalCfgHitConstruction)
    (hbridge :
      RunConfigEmitterCore.GuardedEgress.MetadataWitnessBridge.Construction) :
    FixedDescriptionBoundedSimulatorEquivConstruction := by
  exact
    fixedDescriptionBoundedSimulatorEquivConstruction_of_terminalCoreEquiv_configRunner
      (fixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreEquivConstruction_of_runConfigEmitterLeaves_configRunner
        hcfg hbridge)

end FoC.Computability.EncRewriters.BoundedLayoutRunner
