import FoC.Computability.Compiler.Core.EncodedRewriters.RightShifted

set_option doc.verso true

/-!
# Total-output emitter encoded rewriter

This module isolates the finite-machine obligation for
{name (full := FoC.Computability.PairedRecognizerDovetailTotalOutputCode)}`PairedRecognizerDovetailTotalOutputCode`.
The machine-level target is a right-shifted canonical output tape; the shared
code-word handoff adapter then packages it as a closed handoff subroutine.
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

def OutputTape
    (L : MachineDescription.DovetailLayout) : Tape Bool :=
  Tape.move Direction.right
    (Tape.input
      (MachineDescription.encodeCodeWordAsInput
        (OutputCode L)))

def ReadySpec
    (emitter : MachineDescription) : Prop :=
  emitter.WellFormed ∧ emitter.HaltTransitionFree

def ForwardSpec
    (emitter : MachineDescription) : Prop :=
  forall L : MachineDescription.DovetailLayout,
    emitter.HaltsWithTape
      (MachineDescription.encodeCodeWordAsInput
        (MachineDescription.DovetailLayout.encode L))
      (OutputTape L)

def ClosedSpec
    (emitter : MachineDescription) : Prop :=
  forall code : Word MachineCodeSymbol,
  forall T : Tape Bool,
    emitter.HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) T ->
      exists L : MachineDescription.DovetailLayout,
        code = MachineDescription.DovetailLayout.encode L ∧
          T = OutputTape L

def Spec
    (emitter : MachineDescription) : Prop :=
  ReadySpec emitter ∧ ForwardSpec emitter ∧ ClosedSpec emitter

def FiniteDescriptionConstruction : Prop :=
  exists emitter : MachineDescription,
    Spec emitter

def RightShiftedOutputCompiledConstruction : Prop :=
  exists emitter : MachineDescription,
    RightShiftedOutputCompiledSubroutineByDescription
      PairedRecognizerDovetailTotalOutputCode
      emitter

theorem rightShiftedOutputCompiled_of_spec
    {emitter : MachineDescription}
    (hemitter : Spec emitter) :
    RightShiftedOutputCompiledSubroutineByDescription
      PairedRecognizerDovetailTotalOutputCode
      emitter := by
  constructor
  · exact hemitter.left.left
  · constructor
    · exact hemitter.left.right
    · constructor
      · intro code out
        constructor
        · intro hhalt
          rcases hhalt with ⟨n, hn⟩
          let T : Tape Bool :=
            (emitter.runConfig n
              (emitter.initial
                (MachineDescription.encodeCodeWordAsInput code))).tape
          have hTape :
              emitter.HaltsWithTape
                (MachineDescription.encodeCodeWordAsInput code) T := by
            exact ⟨n, ⟨hn.left, rfl⟩⟩
          rcases hemitter.right.right code T hTape with
            ⟨L, hcode, hT⟩
          have hactual :
              Tape.normalizedOutput T =
                MachineDescription.encodeCodeWordAsInput out := by
            simpa [T] using hn.right
          have hexpected :
              Tape.normalizedOutput T =
                MachineDescription.encodeCodeWordAsInput (OutputCode L) := by
            rw [hT]
            exact
              tape_normalizedOutput_move_right_input
                (MachineDescription.encodeCodeWordAsInput (OutputCode L))
          have houtBits :
              MachineDescription.encodeCodeWordAsInput out =
                MachineDescription.encodeCodeWordAsInput (OutputCode L) :=
            hactual.symm.trans hexpected
          have hout : out = OutputCode L :=
            MachineDescription.encodeCodeWordAsInput_injective houtBits
          exact
            (pairedRecognizerDovetailTotalOutputCode_transform_eq_some_iff
              code out).mpr
              ⟨L, hcode, hout⟩
        · intro htransform
          rcases
              (pairedRecognizerDovetailTotalOutputCode_transform_eq_some_iff
                code out).mp htransform with
            ⟨L, hcode, hout⟩
          subst code
          subst out
          simpa [OutputTape, OutputCode,
            tape_normalizedOutput_move_right_input] using
            MachineDescription.haltsWithOutput_of_haltsWithTape
              (hemitter.right.left L)
      · intro code T hhalt
        rcases hemitter.right.right code T hhalt with
          ⟨L, hcode, hT⟩
        refine ⟨OutputCode L, ?_, hT⟩
        exact
          (pairedRecognizerDovetailTotalOutputCode_transform_eq_some_iff
            code (OutputCode L)).mpr
            ⟨L, hcode, rfl⟩

theorem finiteDescriptionConstruction_scaffold :
    FiniteDescriptionConstruction := by
  sorry

theorem rightShiftedOutputCompiledConstruction_scaffold :
    RightShiftedOutputCompiledConstruction := by
  rcases finiteDescriptionConstruction_scaffold with
    ⟨emitter, hemitter⟩
  exact
    ⟨emitter,
      rightShiftedOutputCompiled_of_spec hemitter⟩

theorem closedHandoffCompiledSubroutine :
    exists emitter : MachineDescription,
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        PairedRecognizerDovetailTotalOutputCode
        emitter tapeCodePrimitiveCodeWordHandoffMove := by
  rcases rightShiftedOutputCompiledConstruction_scaffold with
    ⟨emitter, hemitter⟩
  refine ⟨emitter, ?_⟩
  exact
    closedHandoffCompiled_of_rightShiftedOutputCompiled
      hemitter
      (by
        intro code out htransform
        exact
          pairedRecognizerDovetailTotalOutputCode_transform_eq_some_cons
            htransform)

end TotalOutputEmitter
end EncodedRewriters

end Computability
end FoC
