import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterEquiv
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Simulator.PaddedEmitter.Equiv

set_option doc.verso true

/-!
# Fixed-description simulator construction from the #18 pipeline

The parser and emitter consume the honest equivalence-valued terminal
contract.  This module carries the checked run-config pipeline through that
adapter stack to the public fixed-description simulator construction while
retaining the parameterized integration theorems.
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

theorem fixedDescriptionBoundedSimulatorEquivConstruction_of_metadataWitnessBridge_configRunner
    (hbridge :
      RunConfigEmitterCore.GuardedEgress.MetadataWitnessBridge.Construction) :
    FixedDescriptionBoundedSimulatorEquivConstruction := by
  exact
    fixedDescriptionBoundedSimulatorEquivConstruction_of_terminalCoreEquiv_configRunner
      (fixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreEquivConstruction_of_metadataWitnessBridge_configRunner
        hbridge)

/-- Premise-free fixed-description simulator construction through the checked
tape-equivalence terminal route. -/
theorem fixedDescriptionBoundedSimulatorEquivConstruction_configRunner :
    FixedDescriptionBoundedSimulatorEquivConstruction := by
  exact
    fixedDescriptionBoundedSimulatorEquivConstruction_of_terminalCoreEquiv_configRunner
      fixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreEquivConstruction_configRunner

end FoC.Computability.EncRewriters.BoundedLayoutRunner
