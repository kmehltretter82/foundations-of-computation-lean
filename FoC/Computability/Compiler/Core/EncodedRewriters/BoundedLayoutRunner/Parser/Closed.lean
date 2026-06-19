import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.Parser.Basic

set_option doc.verso true

/-!
# Bounded-layout parser construction

This is the leaf for the complete-layout parser.  The corrected dependency
plan keeps this proof local to the parser phase: it should recognize exactly
complete canonical
{name (full := FoC.Computability.MachineDescription.DovetailLayout)}`MachineDescription.DovetailLayout`
encodings and preserve the input tape.
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace BoundedLayoutRunner

theorem layoutParserConstruction_scaffold :
    LayoutParserConstruction := by
  sorry

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
