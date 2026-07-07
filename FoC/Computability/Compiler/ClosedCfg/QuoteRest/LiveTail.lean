import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTEmitterRuns
import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTJoinerStructured
import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTJoinerRuns

set_option doc.verso true

/-!
# Source-rest finish live-tail wrapper

This module preserves the public live-tail import surface while the emitter and
joiner run theory live in focused submodules.
-/
