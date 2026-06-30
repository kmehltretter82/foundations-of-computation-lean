import FoC.Computability.Compiler.Core.CommonGround.BoolWordQuoters
import FoC.Computability.Compiler.Core.CommonGround.CodeWordEmitters
import FoC.Computability.Compiler.Core.CommonGround.Controller
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers
import FoC.Computability.Compiler.Core.CommonGround.Identity
import FoC.Computability.Compiler.Core.CommonGround.Layouts
import FoC.Computability.Compiler.Core.CommonGround.Scanners
import FoC.Computability.Compiler.Core.CommonGround.SeqComposition

set_option doc.verso true

/-!
# Common compiler helper surface

This compatibility wrapper re-exports the narrow CommonGround submodules used
by construction proofs:

* {module}`FoC.Computability.Compiler.Core.CommonGround.SeqComposition`
* {module}`FoC.Computability.Compiler.Core.CommonGround.Identity`
* {module}`FoC.Computability.Compiler.Core.CommonGround.Layouts`
* {module}`FoC.Computability.Compiler.Core.CommonGround.Scanners`
* {module}`FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers`
* {module}`FoC.Computability.Compiler.Core.CommonGround.CodeWordEmitters`
* {module}`FoC.Computability.Compiler.Core.CommonGround.Controller`
* {module}`FoC.Computability.Compiler.Core.CommonGround.BoolWordQuoters`

Prefer importing one of those submodules directly in construction files. The
old one-off left-boundary-return helper and unused append-return export block
are not part of this facade; their source modules remain available if a future
proof needs a narrow import.
-/
