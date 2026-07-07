import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScaffoldOutput
import FoC.Computability.Compiler.ClosedCfg.ProjTail.Footprint.Contracts
import FoC.Computability.Compiler.ClosedCfg.ProjTail.PrefixEraser.Contracts
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.Routes.SelectedDecoder
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.Routes.SelectedHead
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.Routes.SelectedHeadThreaded
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.Routes.Threaded
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.Mat.Contracts
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.Mat.OutputRoutes
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.Mat.BranchRoutes
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.Mat.EndpointRoutes
import FoC.Computability.Compiler.ClosedCfg.ProjTail.PostPaddingPrefixScanner
import FoC.Computability.Compiler.ClosedCfg.ProjTail.PostPaddingScratchCounter

set_option doc.verso true

/-!
Wrapper module for padded selected-projection tail cleanup. It exports the
scaffold together with the post-padding prefix scanner and scratch-counter
pieces used by downstream padded projection assembly.
-/
