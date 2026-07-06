import FoC.Computability.Compiler.Core.EncRewriters.BoundedLayoutRunner.Parser.Closed

set_option doc.verso true

/-!
# Bounded recognizer-configuration runner contract

This module states the config-runner phase contract and shared tape shapes.
The corrected construction plan treats the finite encoded-configuration
simulator as an upstream prerequisite for the concrete runner implementation;
the wrapper theorem names remain unchanged.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

def BoundedRunLayout
    (accept reject : MachineDescription)
    (L : DovetailLayout) :
    DovetailLayout :=
  DovetailLayout.run accept reject L.stage L

def ConfigRunnerOutputTape
    (accept reject : MachineDescription)
    (L : DovetailLayout) : Tape Bool :=
  ParsedLayoutTape (BoundedRunLayout accept reject L)

def ConfigRunnerOutputBits
    (accept reject : MachineDescription)
    (L : DovetailLayout) : Word Bool :=
  ParsedLayoutBits (BoundedRunLayout accept reject L)

def AcceptRejectConfigRunnerForwardSpec
    (accept reject runner : MachineDescription) : Prop :=
  forall L : DovetailLayout,
    runner.HaltsFromTapeEquiv
      (ParsedLayoutCheckedTape L)
      (ConfigRunnerOutputTape accept reject L)

def AcceptRejectConfigRunnerClosedSpec
    (accept reject runner : MachineDescription) : Prop :=
  forall L : DovetailLayout,
    runner.ClosedFromTapeEquiv
      (ParsedLayoutCheckedTape L)
      (ConfigRunnerOutputTape accept reject L)

def AcceptRejectConfigRunnerSpec
    (accept reject runner : MachineDescription) : Prop :=
  ReadySpec runner ∧
    AcceptRejectConfigRunnerForwardSpec accept reject runner ∧
      AcceptRejectConfigRunnerClosedSpec accept reject runner

def AcceptRejectConfigRunnerConstruction : Prop :=
  forall accept reject : MachineDescription,
    exists runner : MachineDescription,
      AcceptRejectConfigRunnerSpec accept reject runner

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
