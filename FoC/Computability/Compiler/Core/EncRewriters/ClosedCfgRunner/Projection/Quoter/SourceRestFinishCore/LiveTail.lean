import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Quoter.SourceRestFinishCore.LTEmitterRuns
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Quoter.SourceRestFinishCore.LTJoinerStructured
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Quoter.SourceRestFinishCore.LTJoinerRuns

set_option doc.verso true

/-!
# Source-rest finish live-tail wrapper

This module preserves the public live-tail import surface while the emitter and
joiner run theory live in focused submodules.
-/
