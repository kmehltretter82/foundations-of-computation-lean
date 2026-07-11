import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScaffoldOutput
import FoC.Computability.Compiler.ClosedCfg.ProjTail.PostPaddingPrefixScanner
import FoC.Computability.Compiler.ClosedCfg.ProjTail.PostPaddingScratchCounter

set_option doc.verso true

/-!
Wrapper module for padded selected-projection tail cleanup. It exports the
scaffold together with the post-padding prefix scanner and scratch-counter
pieces used by downstream padded projection assembly.
-/
