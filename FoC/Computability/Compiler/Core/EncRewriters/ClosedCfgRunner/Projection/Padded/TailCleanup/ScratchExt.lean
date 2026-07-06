import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.ScratchExtCountWindowBridgeOutput

set_option doc.verso true

/-!
# Post-padding scratch extender

This wrapper re-exports the post-padding scratch extender implementation.  The
implementation is split by responsibility:

- {module}`FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.ScratchExtTapes` contains the base-source and
  layout-scratch tape shapes.
- {module}`FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.ScratchExtSpecs` contains the construction-family
  contracts.
- {module}`FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.ScratchExtAdapters` contains the logical adapters from
  count-sized extension to allocator construction.
- {module}`FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.ScratchExtCountWindow` contains the scratch-count counter
  tapes, checked counter run, and shared composition lemmas.
- {module}`FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.ScratchExtCountWindowConstructions` contains the reusable
  construction leaves for the scratch-count materializer and restorer.
- {module}`FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.ScratchExtCountWindowBridge` exposes the structured
  endpoint facts and remaining finite-machine leaves.
- {module}`FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.ScratchExtCountWindowBridgeThreaded` carries
  the lowered structured extractor bridge through the current scratch-count
  materializer scaffold.
- {module}`FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.ScratchExtCountWindowBridgeOutput` records
  normalized-output endpoint views for the count-window bridge wrappers.
-/
