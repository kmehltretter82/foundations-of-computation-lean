import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.Parser

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

namespace EncodedRewriters
namespace BoundedLayoutRunner

def BoundedRunLayout
    (accept reject : MachineDescription)
    (L : MachineDescription.DovetailLayout) :
    MachineDescription.DovetailLayout :=
  MachineDescription.DovetailLayout.run accept reject L.stage L

def ConfigRunnerOutputTape
    (accept reject : MachineDescription)
    (L : MachineDescription.DovetailLayout) : Tape Bool :=
  ParsedLayoutTape (BoundedRunLayout accept reject L)

def ConfigRunnerOutputBits
    (accept reject : MachineDescription)
    (L : MachineDescription.DovetailLayout) : Word Bool :=
  ParsedLayoutBits (BoundedRunLayout accept reject L)

def AcceptRejectConfigRunnerForwardSpec
    (accept reject runner : MachineDescription) : Prop :=
  forall L : MachineDescription.DovetailLayout,
    runner.HaltsFromTapeEquiv
      (ParsedLayoutCheckedTape L)
      (ConfigRunnerOutputTape accept reject L)

def AcceptRejectConfigRunnerClosedSpec
    (accept reject runner : MachineDescription) : Prop :=
  forall L : MachineDescription.DovetailLayout,
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

def AcceptRejectCheckedConfigRunnerForwardSpec
    (accept reject runner : MachineDescription) : Prop :=
  forall L : MachineDescription.DovetailLayout,
    runner.HaltsWithTape
      (ParsedLayoutBits L)
      (ParsedLayoutCheckedHandoffTape (BoundedRunLayout accept reject L))

def AcceptRejectCheckedConfigRunnerClosedSpec
    (accept reject runner : MachineDescription) : Prop :=
  forall L : MachineDescription.DovetailLayout,
  forall T : Tape Bool,
    runner.HaltsWithTape (ParsedLayoutBits L) T ->
      T = ParsedLayoutCheckedHandoffTape (BoundedRunLayout accept reject L)

def AcceptRejectCheckedConfigRunnerSpec
    (accept reject runner : MachineDescription) : Prop :=
  ReadySpec runner ∧
    AcceptRejectCheckedConfigRunnerForwardSpec accept reject runner ∧
      AcceptRejectCheckedConfigRunnerClosedSpec accept reject runner

def AcceptRejectCheckedConfigRunnerConstruction : Prop :=
  forall accept reject : MachineDescription,
    exists runner : MachineDescription,
      AcceptRejectCheckedConfigRunnerSpec accept reject runner

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
