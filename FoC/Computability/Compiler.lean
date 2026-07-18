import FoC.Computability.Compiler.DescriptionExecution
import FoC.Computability.Compiler.Core
import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorDeterminismGate
import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorBooleanCloseout
import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorSuffixGate
import FoC.Computability.Compiler.Skeletons
import FoC.Computability.Compiler.Core.FixedDescBoundedSim
import FoC.Computability.Compiler.UniversalAndRanges

set_option doc.verso true

/-!
# Compiler

This wrapper re-exports the Chapter 5 compiler layer. The implementation is
split into semantic execution of machine descriptions, tape-code and
subroutine contracts, encoded rewriter construction targets, finite scaffolds,
universal/range closeouts, and the fixed simulator skeletons used by the
dovetail pipeline.  Contract-route notes live in the modules that own those
routes; broad API inventories should be generated from Lean documentation
rather than maintained by hand.
-/
