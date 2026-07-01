import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.PostPaddingConstruction.Core
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.PostPaddingConstruction.PrefixErase

set_option doc.verso true

/-!
# Post-padding construction wrapper

This module preserves the original post-padding construction import surface
while the sentinel/rewind core and output-prefix erasure facts live in focused
submodules.
-/
