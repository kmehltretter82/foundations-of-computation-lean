import FoC.Computability.Compiler.Core.EncodedRewriters.RightShifted

set_option doc.verso true

/-!
# Bounded-layout runner encoded rewriter

This module isolates the finite-machine obligation for
{name (full := FoC.Computability.PairedRecognizerDovetailLayoutCode)}`PairedRecognizerDovetailLayoutCode`.
The real machine must validate a complete
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
  Tape.move Direction.right
    (Tape.input
      (MachineDescription.encodeCodeWordAsInput
        (OutputCode accept reject L)))

def ReadySpec
    (runner : MachineDescription) : Prop :=
  runner.WellFormed ∧ runner.HaltTransitionFree

def ForwardSpec
    (accept reject runner : MachineDescription) : Prop :=
  forall L : MachineDescription.DovetailLayout,
    runner.HaltsWithTape
      (MachineDescription.encodeCodeWordAsInput
        (MachineDescription.DovetailLayout.encode L))
      (OutputTape accept reject L)

def ClosedSpec
    (accept reject runner : MachineDescription) : Prop :=
  forall code : Word MachineCodeSymbol,
  forall T : Tape Bool,
    runner.HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) T ->
      exists L : MachineDescription.DovetailLayout,
        code = MachineDescription.DovetailLayout.encode L ∧
          T = OutputTape accept reject L

def Spec
    (accept reject runner : MachineDescription) : Prop :=
  ReadySpec runner ∧
    ForwardSpec accept reject runner ∧
      ClosedSpec accept reject runner

def FiniteDescriptionConstruction : Prop :=
  forall accept reject : MachineDescription,
    exists runner : MachineDescription,
      Spec accept reject runner

def RightShiftedOutputCompiledConstruction : Prop :=
  forall accept reject : MachineDescription,
    exists runner : MachineDescription,
      RightShiftedOutputCompiledSubroutineByDescription
        (PairedRecognizerDovetailLayoutCode accept reject)
        runner

theorem rightShiftedOutputCompiled_of_spec
    {accept reject runner : MachineDescription}
    (hrunner : Spec accept reject runner) :
    RightShiftedOutputCompiledSubroutineByDescription
      (PairedRecognizerDovetailLayoutCode accept reject)
      runner := by
  constructor
  · exact hrunner.left.left
  · constructor
    · exact hrunner.left.right
    · constructor
      · intro code out
        constructor
        · intro hhalt
          rcases hhalt with ⟨n, hn⟩
          let T : Tape Bool :=
            (runner.runConfig n
              (runner.initial
                (MachineDescription.encodeCodeWordAsInput code))).tape
          have hTape :
              runner.HaltsWithTape
                (MachineDescription.encodeCodeWordAsInput code) T := by
            exact ⟨n, ⟨hn.left, rfl⟩⟩
          rcases hrunner.right.right code T hTape with
            ⟨L, hcode, hT⟩
          have hactual :
              Tape.normalizedOutput T =
                MachineDescription.encodeCodeWordAsInput out := by
            simpa [T] using hn.right
          have hexpected :
              Tape.normalizedOutput T =
                MachineDescription.encodeCodeWordAsInput
                  (OutputCode accept reject L) := by
            rw [hT]
            exact
              tape_normalizedOutput_move_right_input
                (MachineDescription.encodeCodeWordAsInput
                  (OutputCode accept reject L))
          have houtBits :
              MachineDescription.encodeCodeWordAsInput out =
                MachineDescription.encodeCodeWordAsInput
                  (OutputCode accept reject L) :=
            hactual.symm.trans hexpected
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
            tape_normalizedOutput_move_right_input] using
            MachineDescription.haltsWithOutput_of_haltsWithTape
              (hrunner.right.left L)
      · intro code T hhalt
        rcases hrunner.right.right code T hhalt with
          ⟨L, hcode, hT⟩
        refine ⟨OutputCode accept reject L, ?_, hT⟩
        exact
          (pairedRecognizerDovetailLayoutCode_transform_eq_some_iff
            accept reject code (OutputCode accept reject L)).mpr
            ⟨L, hcode, rfl⟩

theorem finiteDescriptionConstruction_scaffold :
    FiniteDescriptionConstruction := by
  intro accept reject
  sorry

theorem rightShiftedOutputCompiledConstruction_scaffold :
    RightShiftedOutputCompiledConstruction := by
  intro accept reject
  rcases finiteDescriptionConstruction_scaffold accept reject with
    ⟨runner, hrunner⟩
  exact
    ⟨runner,
      rightShiftedOutputCompiled_of_spec hrunner⟩

theorem closedHandoffCompiledSubroutine
    (accept reject : MachineDescription) :
    exists runner : MachineDescription,
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (PairedRecognizerDovetailLayoutCode accept reject)
        runner tapeCodePrimitiveCodeWordHandoffMove := by
  rcases
      rightShiftedOutputCompiledConstruction_scaffold accept reject with
    ⟨runner, hrunner⟩
  refine ⟨runner, ?_⟩
  exact
    closedHandoffCompiled_of_rightShiftedOutputCompiled
      hrunner
      (by
        intro code out htransform
        rcases
            pairedRecognizerDovetailLayoutCode_transform_eq_some_cons
              htransform with
          ⟨tail, hout⟩
        exact ⟨MachineCodeSymbol.transition, tail, hout⟩)

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
