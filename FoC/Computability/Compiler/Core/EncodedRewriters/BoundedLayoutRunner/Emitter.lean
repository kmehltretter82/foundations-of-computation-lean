import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner

set_option doc.verso true

/-!
# Bounded-layout output emitter phase

After the recognizer configurations have been advanced, the emitter phase
rewrites the preserved canonical layout tape into the right-shifted output tape
required by the encoded rewriter handoff contract.
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace BoundedLayoutRunner

def OutputEmitterForwardSpec
    (accept reject emitter : MachineDescription) : Prop :=
  forall L : MachineDescription.DovetailLayout,
    emitter.HaltsWithTape
      (ConfigRunnerOutputBits accept reject L)
      (OutputTape accept reject L)

def OutputEmitterClosedSpec
    (accept reject emitter : MachineDescription) : Prop :=
  forall L : MachineDescription.DovetailLayout,
  forall T : Tape Bool,
    emitter.HaltsWithTape
        (ConfigRunnerOutputBits accept reject L) T ->
      T = OutputTape accept reject L

def OutputEmitterSpec
    (accept reject emitter : MachineDescription) : Prop :=
  ReadySpec emitter ∧
    OutputEmitterForwardSpec accept reject emitter ∧
      OutputEmitterClosedSpec accept reject emitter

def OutputEmitterConstruction : Prop :=
  forall accept reject : MachineDescription,
    exists emitter : MachineDescription,
      OutputEmitterSpec accept reject emitter

theorem outputEmitterConstruction_scaffold :
    OutputEmitterConstruction := by
  intro accept reject
  sorry

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
