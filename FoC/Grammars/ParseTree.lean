import FoC.Grammars.ParseTree.Ambiguity

set_option doc.verso true

/-!
# Parse Trees

This wrapper exposes the reusable parse-tree API through semantic child
modules: syntax and measures, derivation correspondence, path selection,
pumping infrastructure, and ambiguity via canonical derivation traces.

Read this module for the complete API. Import a child module directly when a
consumer needs only an earlier layer.
-/
