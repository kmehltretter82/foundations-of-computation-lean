import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.Basic

set_option doc.verso true

/-!
# Bounded-layout parser contract

This module contains the public parser-phase tape shapes and specifications.
The concrete finite parser implementation lives in the following parser
submodules, with this file kept small so later finite-machine lemmas can be
split by phase.
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

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
