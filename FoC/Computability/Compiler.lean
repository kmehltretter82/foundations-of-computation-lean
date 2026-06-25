import FoC.Computability.Compiler.DescriptionExecution
import FoC.Computability.Compiler.Core
import FoC.Computability.Compiler.Skeletons
import FoC.Computability.Compiler.Core.FixedDescriptionBoundedSimulator
import FoC.Computability.Compiler.UniversalAndRanges

set_option doc.verso true

/-!
# Compiler

This wrapper re-exports the Chapter 5 compiler layer. The implementation is
split into semantic execution of machine descriptions, tape-code and
subroutine contracts, encoded rewriter construction targets, finite scaffolds,
universal/range closeouts, and the fixed simulator skeletons used by the
dovetail pipeline.

For a grouped map of the public contracts and the remaining construction
leaves, see {lit}`FoC.Computability.APICrossReference`.
-/
