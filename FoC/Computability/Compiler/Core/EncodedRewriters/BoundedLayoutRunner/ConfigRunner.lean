import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.Parser

set_option doc.verso true

/-!
# Bounded recognizer-configuration runner phase

The runner phase starts from a validated layout tape, simulates both stored
recognizer configurations for the layout stage, and preserves the exact updated
layout needed by the emitter phase.
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
    runner.HaltsWithTape
      (ParsedLayoutBits L)
      (ConfigRunnerOutputTape accept reject L)

def AcceptRejectConfigRunnerClosedSpec
    (accept reject runner : MachineDescription) : Prop :=
  forall L : MachineDescription.DovetailLayout,
  forall T : Tape Bool,
    runner.HaltsWithTape (ParsedLayoutBits L) T ->
      T = ConfigRunnerOutputTape accept reject L

def AcceptRejectConfigRunnerSpec
    (accept reject runner : MachineDescription) : Prop :=
  ReadySpec runner ∧
    AcceptRejectConfigRunnerForwardSpec accept reject runner ∧
      AcceptRejectConfigRunnerClosedSpec accept reject runner

def AcceptRejectConfigRunnerConstruction : Prop :=
  forall accept reject : MachineDescription,
    exists runner : MachineDescription,
      AcceptRejectConfigRunnerSpec accept reject runner

theorem acceptRejectConfigRunnerConstruction_scaffold :
    AcceptRejectConfigRunnerConstruction := by
  intro accept reject
  sorry

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
