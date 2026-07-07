import FoC.Computability.Compiler.ClosedCfg.TerminalCore.Adapters
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.Routes

set_option doc.verso true

/-!
# Padded simulator terminal construction contracts

This wrapper re-exports the terminal construction-family specs, concrete
finite-machine handoff runs, and adapter lemmas used by the public terminal
core.  The implementation is split by responsibility:

- {module}`FoC.Computability.Compiler.ClosedCfg.TerminalCore.Specs`
  contains the construction-family contracts.
- {module}`FoC.Computability.Compiler.ClosedCfg.TerminalCore.Rewind`
  contains the terminal rewind finite-machine run.
- {module}`FoC.Computability.Compiler.ClosedCfg.TerminalCore.RightShiftedSource`
  contains the terminal source-to-right-shifted-source handoff run.
- {module}`FoC.Computability.Compiler.ClosedCfg.TerminalCore.Adapters`
  contains the composition adapters between these construction layers.
-/
