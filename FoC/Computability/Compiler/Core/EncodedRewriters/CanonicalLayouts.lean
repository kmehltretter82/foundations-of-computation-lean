import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.Basic
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.Controller
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.Dovetail
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.Emitters
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.Fields
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.Simulator

set_option doc.verso true

/-!
# Canonical encoded-layout validator interfaces

This wrapper collects the shared canonical-layout contracts and concrete
specializations used by encoded rewriter phases.
-/
