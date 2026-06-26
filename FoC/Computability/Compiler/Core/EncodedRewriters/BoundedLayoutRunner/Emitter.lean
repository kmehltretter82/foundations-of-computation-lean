import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner

set_option doc.verso true

/-!
# Bounded-layout output emitter

The config runner already returns the final layout bits, so this phase is exact
identity.
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

def OutputEmitterDescription : MachineDescription :=
  MachineDescription.ExactIdentityDescription

theorem outputEmitterDescription_ready :
    ReadySpec OutputEmitterDescription := by
  exact
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩

theorem outputEmitterDescription_haltsWithTape
    (accept reject : MachineDescription)
    (L : MachineDescription.DovetailLayout) :
    OutputEmitterDescription.HaltsWithTape
      (ConfigRunnerOutputBits accept reject L)
      (OutputTape accept reject L) := by
  refine ⟨0, ?_⟩
  constructor
  · simp [OutputEmitterDescription, MachineDescription.initial,
      MachineDescription.ExactIdentityDescription,
      MachineDescription.runConfig]
  · simp [OutputEmitterDescription, MachineDescription.initial,
      MachineDescription.ExactIdentityDescription, ConfigRunnerOutputBits,
      ParsedLayoutBits, BoundedRunLayout, OutputTape, OutputCode, Tape.output,
      MachineDescription.runConfig]

theorem outputEmitterConstruction_scaffold :
    OutputEmitterConstruction := by
  intro accept reject
  refine ⟨OutputEmitterDescription, ?_⟩
  constructor
  · exact outputEmitterDescription_ready
  constructor
  · intro L
    exact outputEmitterDescription_haltsWithTape accept reject L
  · intro L T hhalt
    exact
      MachineDescription.haltsWithTape_functional_of_haltTransitionFree
        outputEmitterDescription_ready.right
        hhalt
        (outputEmitterDescription_haltsWithTape accept reject L)

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
