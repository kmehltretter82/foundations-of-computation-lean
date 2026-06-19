import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.Basic

set_option doc.verso true

/-!
# Bounded-layout parser phase

The parser phase is responsible for recognizing exactly complete canonical
{name (full := FoC.Computability.MachineDescription.DovetailLayout)}`MachineDescription.DovetailLayout`
encodings before the bounded runner updates recognizer configurations.
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace BoundedLayoutRunner

def ParsedLayoutBits
    (L : MachineDescription.DovetailLayout) : Word Bool :=
  MachineDescription.encodeCodeWordAsInput
    (MachineDescription.DovetailLayout.encode L)

def ParsedLayoutTape
    (L : MachineDescription.DovetailLayout) : Tape Bool :=
  Tape.input (ParsedLayoutBits L)

def LayoutParserForwardSpec
    (parser : MachineDescription) : Prop :=
  forall L : MachineDescription.DovetailLayout,
    parser.HaltsWithTape
      (ParsedLayoutBits L)
      (ParsedLayoutTape L)

def LayoutParserClosedSpec
    (parser : MachineDescription) : Prop :=
  forall code : Word MachineCodeSymbol,
  forall T : Tape Bool,
    parser.HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) T ->
      exists L : MachineDescription.DovetailLayout,
        MachineDescription.DovetailLayout.decodeComplete code = some L ∧
          T = ParsedLayoutTape L

def LayoutParserSpec
    (parser : MachineDescription) : Prop :=
  ReadySpec parser ∧
    LayoutParserForwardSpec parser ∧
      LayoutParserClosedSpec parser

def LayoutParserConstruction : Prop :=
  exists parser : MachineDescription,
    LayoutParserSpec parser

theorem layoutParserConstruction_scaffold :
    LayoutParserConstruction := by
  sorry

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
