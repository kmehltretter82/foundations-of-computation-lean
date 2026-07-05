import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.PostPaddingScratchExtender.CountWindowStructuredMaterializerPilot

set_option doc.verso true

/-!
# Post-padding scratch extender

This wrapper re-exports the post-padding scratch extender implementation.  The
implementation is split by responsibility:

- `PostPaddingScratchExtender.Tapes` contains the base-source and
  layout-scratch tape shapes.
- `PostPaddingScratchExtender.Specs` contains the construction-family
  contracts.
- `PostPaddingScratchExtender.Adapters` contains the logical adapters from
  count-sized extension to allocator construction.
- `PostPaddingScratchExtender.CountWindow` contains the scratch-count counter
  tapes, checked counter run, and shared composition lemmas.
- `PostPaddingScratchExtender.CountWindowConstructions` contains the reusable
  construction leaves for the scratch-count materializer and restorer.
- `PostPaddingScratchExtender.CountWindowStructuredMaterializerPilot` exposes
  the lowered structured extractor bridge used by the current scratch-count
  materializer scaffold.
-/
