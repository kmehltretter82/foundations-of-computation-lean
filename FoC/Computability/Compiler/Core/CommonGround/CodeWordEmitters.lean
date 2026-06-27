import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts

set_option doc.verso true

/-!
# Common code-word emitter adapters

This module exposes the exact and right-shifted canonical code-word emitter
contracts plus the indexed adapter used by construction leaves.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace CodeWordEmitters

export EncodedRewriters
  ( tape_normalizedOutput_move_right_input
    tape_move_left_move_right_input_encodeCodeWordAsInput_cons )

export EncodedRewriters.CanonicalLayouts
  ( ExactOutputTape
    exactOutputTape_normalizedOutput
    ExactEmitterSpec
    ExactEmitterConstruction
    OutputTape
    outputTape_normalizedOutput
    RightShiftedOutputTape
    rightShiftedOutputTape_normalizedOutput
    EmitterSpec
    EmitterConstruction
    RightShiftedEmitterSpec
    RightShiftedEmitterConstruction )

theorem rightShiftedOutputCompiled_of_indexed_tape_spec
    {ι : Type}
    {P : MachineDescription.TapeCodePrimitive}
    {runner : MachineDescription}
    (hwell : runner.WellFormed)
    (hhaltFree : runner.HaltTransitionFree)
    (inputCode outputCode : ι -> Word MachineCodeSymbol)
    (outputTape : ι -> Tape Bool)
    (houtputTape :
      forall i : ι,
        outputTape i =
          Tape.move Direction.right
            (Tape.input
              (MachineDescription.encodeCodeWordAsInput
                (outputCode i))))
    (hforward :
      forall i : ι,
        runner.HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput (inputCode i))
          (outputTape i))
    (hclosed :
      forall code : Word MachineCodeSymbol,
      forall T : Tape Bool,
        runner.HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput code) T ->
        exists i : ι, code = inputCode i ∧ T = outputTape i)
    (htransform :
      forall code out : Word MachineCodeSymbol,
        P.transform code = some out <->
          exists i : ι, code = inputCode i ∧ out = outputCode i) :
    EncodedRewriters.RightShiftedOutputCompiledSubroutineByDescription
      P runner := by
  constructor
  · exact hwell
  constructor
  · exact hhaltFree
  constructor
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
      rcases hclosed code T hTape with ⟨i, hcode, hT⟩
      have hactual :
          Tape.normalizedOutput T =
            MachineDescription.encodeCodeWordAsInput out := by
        simpa [T] using hn.right
      have hexpected :
          Tape.normalizedOutput T =
            MachineDescription.encodeCodeWordAsInput (outputCode i) := by
        rw [hT, houtputTape i]
        exact
          EncodedRewriters.tape_normalizedOutput_move_right_input
            (MachineDescription.encodeCodeWordAsInput (outputCode i))
      have houtBits :
          MachineDescription.encodeCodeWordAsInput out =
            MachineDescription.encodeCodeWordAsInput (outputCode i) :=
        hactual.symm.trans hexpected
      have hout : out = outputCode i :=
        MachineDescription.encodeCodeWordAsInput_injective houtBits
      exact (htransform code out).mpr ⟨i, hcode, hout⟩
    · intro hP
      rcases (htransform code out).mp hP with ⟨i, hcode, hout⟩
      rw [hcode, hout]
      simpa [houtputTape i,
        EncodedRewriters.tape_normalizedOutput_move_right_input] using
        MachineDescription.haltsWithOutput_of_haltsWithTape
          (hforward i)
  · intro code T hhalt
    rcases hclosed code T hhalt with ⟨i, hcode, hT⟩
    refine ⟨outputCode i, ?_, ?_⟩
    · exact (htransform code (outputCode i)).mpr ⟨i, hcode, rfl⟩
    · rw [hT, houtputTape i]

end CodeWordEmitters
end CommonGround

end Computability
end FoC
