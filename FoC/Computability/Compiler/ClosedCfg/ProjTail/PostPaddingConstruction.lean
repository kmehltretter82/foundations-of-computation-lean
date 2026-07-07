import FoC.Computability.Compiler.ClosedCfg.ProjTail.PostPadCore
import FoC.Computability.Compiler.ClosedCfg.ProjTail.PostPadPrefixErase

set_option doc.verso true

/-!
# Post-padding construction wrapper

This module preserves the original post-padding construction import surface
while the sentinel/rewind core and output-prefix erasure facts live in focused
submodules.
-/
