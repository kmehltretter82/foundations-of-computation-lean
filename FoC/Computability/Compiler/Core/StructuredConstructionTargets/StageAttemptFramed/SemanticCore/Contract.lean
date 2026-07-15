import FoC.Computability.Compiler.Core.StructuredConstructionTargets.FuelSimulator
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.TwoStageEndpoints

set_option doc.verso true

/-!
# Framed stage-attempt semantic-core contract

The semantic index records the concrete attempt witness.  The structured core
carries its actual final logical tape-0 and tape-1 representatives; the public
endpoint observes only logical tape 2.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets

open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

/-- A controller layout, result word, and concrete fuel witness. -/
structure StageAttemptFramedStructuredIndex
    (attempt : MachineDescription) where
  C : DovetailControllerLayout
  result : Word Bool
  fuel : Nat
  attempt_halts :
    attempt.HaltsWithOutputIn fuel
      (encodeCodeWordAsInput
        (PairedRecognizerDovetailControllerStageInputCode C))
      (encodeCodeWordAsInput (encodeBoolWord result))

def stageAttemptFramedStructuredInputBits
    (C : DovetailControllerLayout) : Word Bool :=
  encodeCodeWordAsInput (DovetailControllerLayout.encode C)

def stageAttemptFramedStructuredOutputTape
    {attempt : MachineDescription}
    (i : StageAttemptFramedStructuredIndex attempt) : Tape Bool :=
  CommonGround.ControllerInvocation.StageAttemptFramedOutputTape
    i.C i.result

def stageAttemptFramedStructuredInitializedTape
    (C : DovetailControllerLayout) : Tape Bool :=
  CommonGround.FiniteTransducers.structured3InputMaterializerTargetTape
    (Tape.input (stageAttemptFramedStructuredInputBits C))
    Tape.blank

/--
Semantic-core data with the actual logical tape-0 and tape-1 representatives
left by the construction.  The endpoint immediately projects tape 2, so these
families are intentionally internal.

Audit guardrail: a valid nonempty-input stage-zero attempt reaches the exact
framed tape-2 result after 814 logical core steps while leaving tape 0 unequal
to the pristine controller input and tape 1 nonblank.  Since equivalence of
canonical guarded encodings forces equality of all three logical tapes, the
former fixed-representative contract demanded an unused cleanup phase.
-/
structure StageAttemptFramedStructuredSemanticCoreComponents
    (attempt : MachineDescription) where
  tape0 : StageAttemptFramedStructuredIndex attempt -> Tape Bool
  tape1 : StageAttemptFramedStructuredIndex attempt -> Tape Bool
  components :
    Structured3EndpointEquivSemanticCoreComponents
      (fun i : StageAttemptFramedStructuredIndex attempt => i.C)
      stageAttemptFramedStructuredInitializedTape
      (fun i =>
        encodedGuardedStructured3Tapes
          (tape0 i) (tape1 i) (stageAttemptFramedStructuredOutputTape i))
      stageAttemptFramedStructuredOutputTape
      tape0 tape1

def StageAttemptFramedStructuredSemanticCoreConstruction
    (attempt : MachineDescription) : Prop :=
  Nonempty (StageAttemptFramedStructuredSemanticCoreComponents attempt)

end StructuredConstructionTargets
end Computability
end FoC
