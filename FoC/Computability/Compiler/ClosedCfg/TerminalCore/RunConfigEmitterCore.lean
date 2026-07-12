import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterTheory.Output
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.InputMaterializer
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.LoopDispatcherDoneWitnessCloseout
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.ExactTapeSerializer
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.FiniteRealization
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.FieldDecomposition.CfgHitClose
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.SelectorSplice

/-!
# Fixed-description bounded simulator run-config emitter core

Aggregator for the durable `#18` run-config emitter reconstruction split under
`RunConfigEmitterCore/` and the pure theory under `RunConfigEmitterTheory/`.
Importing the terminal leaves of that subtree keeps every checkpoint in the
build graph so latent breaks surface immediately.  These modules are the
sorry-free replacement stack for the terminal-core run/update/emission kernel;
the master terminal wrapper still runs on the older leaf until the core swap.
-/
