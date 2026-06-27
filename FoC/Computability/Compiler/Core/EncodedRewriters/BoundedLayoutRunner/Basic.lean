import FoC.Computability.Compiler.Core.EncodedRewriters.RightShifted

set_option doc.verso true

/-!
# Bounded-layout runner contract

This module states the semantic contract for the finite machine realizing
{name (full := FoC.Computability.PairedRecognizerDovetailLayoutCode)}`PairedRecognizerDovetailLayoutCode`.
The machine must validate a complete
{name (full := FoC.Computability.MachineDescription.DovetailLayout)}`DovetailLayout`,
run both recognizer configurations for the encoded stage bound, update the hit
flags, and halt on the right-shifted encoding of the updated layout.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

def OutputCode
    (accept reject : MachineDescription)
    (L : DovetailLayout) : Word MachineCodeSymbol :=
  DovetailLayout.encode
    (DovetailLayout.run accept reject L.stage L)

def OutputTape
    (accept reject : MachineDescription)
    (L : DovetailLayout) : Tape Bool :=
  Tape.output
    (encodeCodeWordAsInput
      (OutputCode accept reject L))

def ReadySpec
    (runner : MachineDescription) : Prop :=
  runner.WellFormed ∧ runner.HaltTransitionFree

def ForwardSpec
    (accept reject runner : MachineDescription) : Prop :=
  forall L : DovetailLayout,
    runner.HaltsWithTapeEquiv
      (encodeCodeWordAsInput
        (DovetailLayout.encode L))
      (OutputTape accept reject L)

def ClosedSpec
    (accept reject runner : MachineDescription) : Prop :=
  forall code : Word MachineCodeSymbol,
  forall T : Tape Bool,
    runner.HaltsWithTapeEquiv
        (encodeCodeWordAsInput code) T ->
      exists L : DovetailLayout,
        code = DovetailLayout.encode L ∧
          Tape.Equiv T (OutputTape accept reject L)

def Spec
    (accept reject runner : MachineDescription) : Prop :=
  ReadySpec runner ∧
    ForwardSpec accept reject runner ∧
      ClosedSpec accept reject runner

def FiniteDescriptionConstruction : Prop :=
  forall accept reject : MachineDescription,
    exists runner : MachineDescription,
      Spec accept reject runner

theorem outputCompiledSubroutineByDescription_of_spec
    {accept reject runner : MachineDescription}
    (hrunner : Spec accept reject runner) :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      (PairedRecognizerDovetailLayoutCode accept reject)
      runner := by
  constructor
  · constructor
    · exact hrunner.left.left
    · intro code out
      constructor
      · intro houtput
        rcases houtput with ⟨n, hn⟩
        let T : Tape Bool :=
          (runner.runConfig n
            (runner.initial
              (encodeCodeWordAsInput code))).tape
        have hTapeEquiv :
            runner.HaltsWithTapeEquiv
              (encodeCodeWordAsInput code) T :=
          ⟨T, ⟨n, ⟨hn.left, rfl⟩⟩, Tape.Equiv.refl T⟩
        rcases hrunner.right.right code T hTapeEquiv with
          ⟨L, hcode, hT⟩
        have hexpected :
            Tape.normalizedOutput T =
              encodeCodeWordAsInput
                (OutputCode accept reject L) := by
          rw [Tape.Equiv.normalizedOutput_eq hT]
          exact
            Tape.normalizedOutput_output
              (encodeCodeWordAsInput
                (OutputCode accept reject L))
        have houtBits :
            encodeCodeWordAsInput out =
              encodeCodeWordAsInput
                (OutputCode accept reject L) := by
          have hactual : Tape.normalizedOutput T = encodeCodeWordAsInput out := hn.right
          exact hactual.symm.trans hexpected
        have hout : out = OutputCode accept reject L :=
          encodeCodeWordAsInput_injective houtBits
        exact
          (pairedRecognizerDovetailLayoutCode_transform_eq_some_iff
            accept reject code out).mpr
            ⟨L, hcode, hout⟩
      · intro htransform
        rcases
            (pairedRecognizerDovetailLayoutCode_transform_eq_some_iff
              accept reject code out).mp htransform with
          ⟨L, hcode, hout⟩
        subst code
        subst out
        simpa [OutputTape, OutputCode,
          Tape.normalizedOutput_output] using
          haltsWithOutput_of_haltsWithTapeEquiv
            (hrunner.right.left L)
  · exact hrunner.left.right

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
