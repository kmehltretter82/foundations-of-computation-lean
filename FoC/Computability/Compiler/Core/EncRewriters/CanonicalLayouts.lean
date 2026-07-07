import FoC.Computability.Compiler.Core.EncRewriters.CanonicalLayouts.Basic
import FoC.Computability.Compiler.Core.EncRewriters.CanonicalLayouts.Configuration
import FoC.Computability.Compiler.Core.EncRewriters.CanonicalLayouts.Controller
import FoC.Computability.Compiler.Core.EncRewriters.CanonicalLayouts.Dovetail
import FoC.Computability.Compiler.Dovetail.Scanner.ShapeClosed
import FoC.Computability.Compiler.Dovetail.Scanner.ConfigurationClosed
import FoC.Computability.Compiler.Core.EncRewriters.CanonicalLayouts.DovetailStagePrefix
import FoC.Computability.Compiler.Core.EncRewriters.CanonicalLayouts.Emitters
import FoC.Computability.Compiler.Core.EncRewriters.CanonicalLayouts.Fields
import FoC.Computability.Compiler.Core.EncRewriters.CanonicalLayouts.Simulator

set_option doc.verso true

/-!
# Canonical encoded-layout validator interfaces

This wrapper collects the shared canonical-layout contracts and concrete
specializations used by encoded rewriter phases.
-/
