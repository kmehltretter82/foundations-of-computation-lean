import FoC.Computability.Compiler.Core.TapeCodePrimitives

set_option doc.verso true

/-!
# Total-output emitter encoded rewriter

This module isolates the finite-machine obligation for
{name (full := FoC.Computability.PairedRecognizerDovetailTotalOutputCode)}`PairedRecognizerDovetailTotalOutputCode`.
The machine-level target is a normalized canonical output word.  This is
intentionally not a handoff contract: this primitive can shrink a large encoded
layout to the encoding of an empty or singleton Boolean word, and tape context
length cannot decrease.
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace TotalOutputEmitter

def OutputCode
    (L : MachineDescription.DovetailLayout) : Word MachineCodeSymbol :=
  MachineDescription.encodeBoolWord
    (MachineDescription.DovetailLayout.outputWordFromHits L)

def OutputBits
    (L : MachineDescription.DovetailLayout) : Word Bool :=
  MachineDescription.encodeCodeWordAsInput
    (OutputCode L)

def ReadySpec
    (emitter : MachineDescription) : Prop :=
  emitter.WellFormed ∧ emitter.HaltTransitionFree

def ForwardSpec
    (emitter : MachineDescription) : Prop :=
  forall L : MachineDescription.DovetailLayout,
    emitter.HaltsWithOutput
      (MachineDescription.encodeCodeWordAsInput
        (MachineDescription.DovetailLayout.encode L))
      (OutputBits L)

def ClosedSpec
    (emitter : MachineDescription) : Prop :=
  forall code : Word MachineCodeSymbol,
  forall out : Word MachineCodeSymbol,
    emitter.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) ->
      PairedRecognizerDovetailTotalOutputCode.transform code = some out

def Spec
    (emitter : MachineDescription) : Prop :=
  ReadySpec emitter ∧ ForwardSpec emitter ∧ ClosedSpec emitter

def FiniteDescriptionConstruction : Prop :=
  exists emitter : MachineDescription,
    Spec emitter

theorem finiteDescriptionConstruction_scaffold :
    FiniteDescriptionConstruction := by
  sorry

def OutputCompiledConstruction : Prop :=
  exists emitter : MachineDescription,
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      PairedRecognizerDovetailTotalOutputCode
      emitter

theorem outputCompiled_of_spec
    {emitter : MachineDescription}
    (hemitter : Spec emitter) :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      PairedRecognizerDovetailTotalOutputCode
      emitter := by
  constructor
  · constructor
    · exact hemitter.left.left
    · intro code out
      constructor
      · intro hhalt
        exact hemitter.right.right code out hhalt
      · intro htransform
        rcases
            (pairedRecognizerDovetailTotalOutputCode_transform_eq_some_iff
              code out).mp htransform with
          ⟨L, hcode, hout⟩
        subst code
        subst out
        exact hemitter.right.left L
  · exact hemitter.left.right

theorem outputCompiledConstruction_scaffold :
    OutputCompiledConstruction := by
  rcases finiteDescriptionConstruction_scaffold with
    ⟨emitter, hemitter⟩
  exact
    ⟨emitter,
      outputCompiled_of_spec hemitter⟩

theorem outputCompiledSubroutine :
    exists emitter : MachineDescription,
      TapeCodePrimitiveOutputCompiledSubroutineByDescription
        PairedRecognizerDovetailTotalOutputCode
        emitter :=
  outputCompiledConstruction_scaffold

/- The remaining finite-machine obligation is the possible output-compiled
   construction above.  There is deliberately no closed-handoff theorem for
   this primitive: the output may be shorter than the input, so the exact
   right-shifted handoff tape is not reachable in general. -/

end TotalOutputEmitter
end EncodedRewriters

end Computability
end FoC
