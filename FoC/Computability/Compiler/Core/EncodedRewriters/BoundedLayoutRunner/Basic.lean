import FoC.Computability.Compiler.Core.EncodedRewriters.RightShifted

set_option doc.verso true

/-!
# Bounded-layout runner contract

This module states the semantic contract for the finite machine realizing
{name (full := FoC.Computability.PairedRecognizerDovetailLayoutCode)}`PairedRecognizerDovetailLayoutCode`.
The machine must validate a complete
{name (full := FoC.Computability.MachineDescription.DovetailLayout)}`MachineDescription.DovetailLayout`,
run both recognizer configurations for the encoded stage bound, update the hit
flags, and halt on the right-shifted encoding of the updated layout.
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace BoundedLayoutRunner

def OutputCode
    (accept reject : MachineDescription)
    (L : MachineDescription.DovetailLayout) : Word MachineCodeSymbol :=
  MachineDescription.DovetailLayout.encode
    (MachineDescription.DovetailLayout.run accept reject L.stage L)

def OutputTape
    (accept reject : MachineDescription)
    (L : MachineDescription.DovetailLayout) : Tape Bool :=
  Tape.output
    (MachineDescription.encodeCodeWordAsInput
      (OutputCode accept reject L))

def ReadySpec
    (runner : MachineDescription) : Prop :=
  runner.WellFormed ∧ runner.HaltTransitionFree

def ForwardSpec
    (accept reject runner : MachineDescription) : Prop :=
  forall L : MachineDescription.DovetailLayout,
    runner.HaltsWithTapeEquiv
      (MachineDescription.encodeCodeWordAsInput
        (MachineDescription.DovetailLayout.encode L))
      (OutputTape accept reject L)

def ClosedSpec
    (accept reject runner : MachineDescription) : Prop :=
  forall code : Word MachineCodeSymbol,
  forall T : Tape Bool,
    runner.HaltsWithTapeEquiv
        (MachineDescription.encodeCodeWordAsInput code) T ->
      exists L : MachineDescription.DovetailLayout,
        code = MachineDescription.DovetailLayout.encode L ∧
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
              (MachineDescription.encodeCodeWordAsInput code))).tape
        have hTapeEquiv :
            runner.HaltsWithTapeEquiv
              (MachineDescription.encodeCodeWordAsInput code) T :=
          ⟨T, ⟨n, ⟨hn.left, rfl⟩⟩, Tape.Equiv.refl T⟩
        rcases hrunner.right.right code T hTapeEquiv with
          ⟨L, hcode, hT⟩
        have hexpected :
            Tape.normalizedOutput T =
              MachineDescription.encodeCodeWordAsInput
                (OutputCode accept reject L) := by
          rw [Tape.Equiv.normalizedOutput_eq hT]
          exact
            Tape.normalizedOutput_output
              (MachineDescription.encodeCodeWordAsInput
                (OutputCode accept reject L))
        have houtBits :
            MachineDescription.encodeCodeWordAsInput out =
              MachineDescription.encodeCodeWordAsInput
                (OutputCode accept reject L) := by
          have hactual : Tape.normalizedOutput T = MachineDescription.encodeCodeWordAsInput out := hn.right
          exact hactual.symm.trans hexpected
        have hout : out = OutputCode accept reject L :=
          MachineDescription.encodeCodeWordAsInput_injective houtBits
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
          MachineDescription.haltsWithOutput_of_haltsWithTapeEquiv
            (hrunner.right.left L)
  · exact hrunner.left.right

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
