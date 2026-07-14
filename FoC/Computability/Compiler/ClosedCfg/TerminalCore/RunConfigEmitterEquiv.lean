import FoC.Computability.Compiler.ClosedCfg.TerminalCore.Equiv
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitter
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.FieldDecomposition.RepRepair
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.FullPipeline
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.Assembly

set_option doc.verso true

/-!
# Equivalence-valued fixed-description emitter construction

This module connects the checked guarded-egress construction to the
full-pipeline and terminal adapters.  It keeps the honest tape-equivalence
currency through the final scratch-output boundary while retaining the
parameterized integration theorems for reuse.
-/

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner

open Languages MachineDescription

theorem runConfigEmitterCanonicalCfgHitConstruction_configRunner :
    RunConfigEmitterCore.FullPipeline.CanonicalCfgHitConstruction := by
  exact
    RunConfigEmitterCore.FieldDecomposition.MetadataPrefix.ConfigTapeAndHit.canonical_construction_core

theorem runConfigEmitterFullPipelineConstruction_of_leaves
    (hcfg :
      RunConfigEmitterCore.FullPipeline.CanonicalCfgHitConstruction)
    (hbridge :
      RunConfigEmitterCore.GuardedEgress.MetadataWitnessBridge.Construction) :
    RunConfigEmitterCore.FullPipeline.Construction := by
  exact
    RunConfigEmitterCore.FullPipeline.construction_of_components
      hcfg
      (RunConfigEmitterCore.GuardedEgress.Assembly.construction_of_metadataWitnessBridge
        hbridge)

theorem runConfigEmitterFullPipelineConstruction_of_metadataWitnessBridge_configRunner
    (hbridge :
      RunConfigEmitterCore.GuardedEgress.MetadataWitnessBridge.Construction) :
    RunConfigEmitterCore.FullPipeline.Construction := by
  exact
    runConfigEmitterFullPipelineConstruction_of_leaves
      runConfigEmitterCanonicalCfgHitConstruction_configRunner hbridge

/-- The checked configuration/hit repair and guarded-egress construction give
the premise-free full run-config emitter pipeline. -/
theorem runConfigEmitterFullPipelineConstruction_configRunner :
    RunConfigEmitterCore.FullPipeline.Construction := by
  exact
    RunConfigEmitterCore.FullPipeline.construction_of_components
      runConfigEmitterCanonicalCfgHitConstruction_configRunner
      RunConfigEmitterCore.GuardedEgress.construction_core

theorem fixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreEquivConstruction_of_runConfigEmitterLeaves_configRunner
    (hcfg :
      RunConfigEmitterCore.FullPipeline.CanonicalCfgHitConstruction)
    (hbridge :
      RunConfigEmitterCore.GuardedEgress.MetadataWitnessBridge.Construction) :
    FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreEquivConstruction_configRunner := by
  exact
    fixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreEquivConstruction_of_rewind_body_configRunner
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindConstruction_configRunner
      (fixedDescriptionBoundedSimulatorPaddedEmitterBodyEquivConstruction_of_fullPipeline_configRunner
        (runConfigEmitterFullPipelineConstruction_of_leaves hcfg hbridge))

theorem fixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreEquivConstruction_of_metadataWitnessBridge_configRunner
    (hbridge :
      RunConfigEmitterCore.GuardedEgress.MetadataWitnessBridge.Construction) :
    FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreEquivConstruction_configRunner := by
  exact
    fixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreEquivConstruction_of_runConfigEmitterLeaves_configRunner
      runConfigEmitterCanonicalCfgHitConstruction_configRunner hbridge

/-- Premise-free terminal construction in the honest tape-equivalence
currency. -/
theorem fixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreEquivConstruction_configRunner :
    FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreEquivConstruction_configRunner := by
  exact
    fixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreEquivConstruction_of_rewind_body_configRunner
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindConstruction_configRunner
      (fixedDescriptionBoundedSimulatorPaddedEmitterBodyEquivConstruction_of_fullPipeline_configRunner
        runConfigEmitterFullPipelineConstruction_configRunner)

end FoC.Computability.EncRewriters.BoundedLayoutRunner
