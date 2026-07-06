import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.ScaffoldOutput
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.ScratchExtCountWindowBridgeMaterializerRouteContracts
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.ScratchExtCountWindowBridgeMaterializerOutputRouteContracts
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.PostPaddingPrefixScanner
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.PostPaddingScratchCounter

set_option doc.verso true

/-!
Wrapper module for padded selected-projection tail cleanup. It exports the
scaffold together with the post-padding prefix scanner and scratch-counter
pieces used by downstream padded projection assembly.
-/
