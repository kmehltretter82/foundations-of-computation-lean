import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.Threaded

set_option doc.verso true

/-!
# Post-padding scratch extender

This wrapper re-exports the post-padding scratch extender implementation.  The
implementation is split by responsibility:

- {module}`FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchExtTapes` contains the base-source and
  layout-scratch tape shapes.
- {module}`FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchExtSpecs` contains the construction-family
  contracts.
- {module}`FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchExtAdapters` contains the logical adapters from
  count-sized extension to allocator construction.
- {module}`FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchExtCountWindow` contains the scratch-count counter
  tapes, checked counter run, and shared composition lemmas.
- {module}`FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchExtCountWindowConstructions` contains the reusable
  construction leaves for the scratch-count materializer and restorer.
- {module}`FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge` exposes the structured
  endpoint facts and remaining finite-machine leaves.
- {module}`FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.Threaded` carries
  the lowered structured extractor bridge through the current scratch-count
  materializer scaffold.
-/
