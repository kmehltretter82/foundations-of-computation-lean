import FoC.Computability.Compiler.Core.TapeCodePrimitives

set_option doc.verso true

/-!
# Right-shifted encoded-rewriter handoff helpers

Finite code-word rewriters in this directory halt one cell to the right of the
canonical Boolean encoding they emit.  These local helpers package that
machine-level shape as the closed handoff contract used by the controller
sequencing layer.
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters

theorem tape_normalizedOutput_move_right_input
    (w : Word Bool) :
    Tape.normalizedOutput
        (Tape.move Direction.right (Tape.input w)) = w := by
  cases w with
  | nil =>
      rfl
  | cons b rest =>
      cases rest with
      | nil =>
          cases b <;> rfl
      | cons c tail =>
          have htail :
              List.filterMap ((fun cell : Option Bool => cell) ∘ some)
                  tail = tail := by
            simpa [Function.comp] using Tape.filterMap_id_map_some tail
          cases b <;> cases c <;>
            simp [Tape.input, Tape.move, Tape.moveRight,
              Tape.normalizedOutput, Tape.cells, htail]

theorem tape_move_left_move_right_input_encodeCodeWordAsInput_cons
    (symbol : MachineCodeSymbol) (code : Word MachineCodeSymbol) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (Tape.input
            (MachineDescription.encodeCodeWordAsInput (symbol :: code)))) =
      Tape.input
        (MachineDescription.encodeCodeWordAsInput (symbol :: code)) := by
  cases symbol <;> rfl

theorem tapeCodePrimitiveCodeWord_handoff_tape
    (symbol : MachineCodeSymbol) (code : Word MachineCodeSymbol) :
    Tape.normalizedOutput
        (Tape.move Direction.right
          (Tape.input
            (MachineDescription.encodeCodeWordAsInput (symbol :: code)))) =
        MachineDescription.encodeCodeWordAsInput (symbol :: code) ∧
      Tape.move tapeCodePrimitiveCodeWordHandoffMove
        (Tape.move Direction.right
          (Tape.input
            (MachineDescription.encodeCodeWordAsInput (symbol :: code)))) =
        Tape.input
          (MachineDescription.encodeCodeWordAsInput (symbol :: code)) := by
  constructor
  · exact
      tape_normalizedOutput_move_right_input
        (MachineDescription.encodeCodeWordAsInput (symbol :: code))
  · simpa [tapeCodePrimitiveCodeWordHandoffMove] using
      tape_move_left_move_right_input_encodeCodeWordAsInput_cons
        symbol code

def RightShiftedOutputCompiledSubroutineByDescription
    (P : MachineDescription.TapeCodePrimitive)
    (D : MachineDescription) : Prop :=
  D.WellFormed ∧
    D.HaltTransitionFree ∧
      (forall code out : Word MachineCodeSymbol,
        D.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput code)
            (MachineDescription.encodeCodeWordAsInput out) <->
          P.transform code = some out) ∧
        forall code : Word MachineCodeSymbol,
        forall T : Tape Bool,
          D.HaltsWithTape
              (MachineDescription.encodeCodeWordAsInput code) T ->
            exists out : Word MachineCodeSymbol,
              P.transform code = some out ∧
              T =
                Tape.move Direction.right
                  (Tape.input
                    (MachineDescription.encodeCodeWordAsInput out))

/-!
**Accessor API.**  Right-shifted output is the exact-tape contract used by the
remaining encoded rewriter leaves.  These accessors keep later proofs from
depending on the nested conjunction layout of
{name}`RightShiftedOutputCompiledSubroutineByDescription`.
-/

theorem rightShiftedOutputCompiledSubroutineByDescription_wellFormed
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : RightShiftedOutputCompiledSubroutineByDescription P D) :
    D.WellFormed :=
  h.left

theorem rightShiftedOutputCompiledSubroutineByDescription_haltTransitionFree
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : RightShiftedOutputCompiledSubroutineByDescription P D) :
    D.HaltTransitionFree :=
  h.right.left

theorem rightShiftedOutputCompiledSubroutineByDescription_haltsWithOutput_iff
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : RightShiftedOutputCompiledSubroutineByDescription P D)
    (code out : Word MachineCodeSymbol) :
    D.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) <->
      P.transform code = some out :=
  h.right.right.left code out

theorem rightShiftedOutputCompiledSubroutineByDescription_haltsWithOutput_of_transform_eq_some
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : RightShiftedOutputCompiledSubroutineByDescription P D)
    {code out : Word MachineCodeSymbol}
    (hp : P.transform code = some out) :
    D.HaltsWithOutput
      (MachineDescription.encodeCodeWordAsInput code)
      (MachineDescription.encodeCodeWordAsInput out) :=
  (rightShiftedOutputCompiledSubroutineByDescription_haltsWithOutput_iff
    h code out).mpr hp

theorem rightShiftedOutputCompiledSubroutineByDescription_transform_eq_some_of_haltsWithOutput
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : RightShiftedOutputCompiledSubroutineByDescription P D)
    {code out : Word MachineCodeSymbol}
    (hD :
      D.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out)) :
    P.transform code = some out :=
  (rightShiftedOutputCompiledSubroutineByDescription_haltsWithOutput_iff
    h code out).mp hD

theorem rightShiftedOutputCompiledSubroutineByDescription_haltsWithTape_inv
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : RightShiftedOutputCompiledSubroutineByDescription P D)
    {code : Word MachineCodeSymbol} {T : Tape Bool}
    (hD :
      D.HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) T) :
    exists out : Word MachineCodeSymbol,
      P.transform code = some out ∧
        T =
          Tape.move Direction.right
            (Tape.input
              (MachineDescription.encodeCodeWordAsInput out)) :=
  h.right.right.right code T hD

theorem rightShiftedOutputCompiledSubroutineByDescription_outputCompiled
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : RightShiftedOutputCompiledSubroutineByDescription P D) :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription P D :=
  ⟨⟨h.left, h.right.right.left⟩, h.right.left⟩

theorem rightShiftedOutputCompiledSubroutineByDescription_subroutineReady
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : RightShiftedOutputCompiledSubroutineByDescription P D) :
    D.SubroutineReady :=
  ⟨h.left, h.right.left⟩

theorem rightShifted_haltsWithOutput_iff
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : RightShiftedOutputCompiledSubroutineByDescription P D)
    (code out : Word MachineCodeSymbol) :
    D.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) <->
      P.transform code = some out :=
  rightShiftedOutputCompiledSubroutineByDescription_haltsWithOutput_iff
    h code out

theorem rightShifted_haltsWithTape_inv
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : RightShiftedOutputCompiledSubroutineByDescription P D)
    {code : Word MachineCodeSymbol} {T : Tape Bool}
    (hD :
      D.HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) T) :
    exists out : Word MachineCodeSymbol,
      P.transform code = some out ∧
        T =
          Tape.move Direction.right
            (Tape.input
              (MachineDescription.encodeCodeWordAsInput out)) :=
  rightShiftedOutputCompiledSubroutineByDescription_haltsWithTape_inv
    h hD

theorem rightShifted_outputCompiled
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : RightShiftedOutputCompiledSubroutineByDescription P D) :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription P D :=
  rightShiftedOutputCompiledSubroutineByDescription_outputCompiled h

theorem rightShifted_subroutineReady
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : RightShiftedOutputCompiledSubroutineByDescription P D) :
    D.SubroutineReady :=
  rightShiftedOutputCompiledSubroutineByDescription_subroutineReady h

theorem closedHandoffCompiled_of_halt_tape_move_right
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (hwell : D.WellFormed)
    (hhaltFree : D.HaltTransitionFree)
    (houtput :
      forall code out : Word MachineCodeSymbol,
        D.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput code)
            (MachineDescription.encodeCodeWordAsInput out) <->
          P.transform code = some out)
    (houtCons :
      forall {code out : Word MachineCodeSymbol},
        P.transform code = some out ->
          exists symbol : MachineCodeSymbol,
          exists tail : Word MachineCodeSymbol,
            out = symbol :: tail)
    (htape :
      forall code : Word MachineCodeSymbol,
      forall T : Tape Bool,
        D.HaltsWithTape
            (MachineDescription.encodeCodeWordAsInput code) T ->
          exists out : Word MachineCodeSymbol,
            P.transform code = some out ∧
              T =
                Tape.move Direction.right
                  (Tape.input
                    (MachineDescription.encodeCodeWordAsInput out))) :
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      P D tapeCodePrimitiveCodeWordHandoffMove := by
  constructor
  · exact ⟨⟨hwell, houtput⟩, hhaltFree⟩
  · intro code T hD
    rcases htape code T hD with ⟨out, hp, hT⟩
    rcases houtCons hp with ⟨symbol, tail, hout⟩
    subst out
    subst T
    rcases tapeCodePrimitiveCodeWord_handoff_tape symbol tail with
      ⟨hnorm, hmove⟩
    exact ⟨symbol :: tail, hp, hnorm, hmove⟩

theorem closedHandoffCompiled_of_rightShiftedOutputCompiled
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (hD :
      RightShiftedOutputCompiledSubroutineByDescription P D)
    (houtCons :
      forall {code out : Word MachineCodeSymbol},
        P.transform code = some out ->
          exists symbol : MachineCodeSymbol,
          exists tail : Word MachineCodeSymbol,
            out = symbol :: tail) :
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      P D tapeCodePrimitiveCodeWordHandoffMove :=
  closedHandoffCompiled_of_halt_tape_move_right
    hD.left hD.right.left hD.right.right.left houtCons
    hD.right.right.right

theorem dovetailLayout_encode_cons
    (L : MachineDescription.DovetailLayout) :
    exists tail : Word MachineCodeSymbol,
      MachineDescription.DovetailLayout.encode L =
        MachineCodeSymbol.transition :: tail := by
  cases L
  refine ⟨_, rfl⟩

theorem pairedRecognizerDovetailLayoutCode_transform_eq_some_cons
    {accept reject : MachineDescription}
    {code out : Word MachineCodeSymbol}
    (h :
      (PairedRecognizerDovetailLayoutCode accept reject).transform code =
        some out) :
    exists tail : Word MachineCodeSymbol,
      out = MachineCodeSymbol.transition :: tail := by
  rcases
      (pairedRecognizerDovetailLayoutCode_transform_eq_some_iff
        accept reject code out).mp h with
    ⟨L, _hcode, hout⟩
  rcases
      dovetailLayout_encode_cons
        (MachineDescription.DovetailLayout.run accept reject L.stage L) with
    ⟨tail, htail⟩
  exact ⟨tail, by rw [hout, htail]⟩

theorem encodeNatAppend_cons
    (n : Nat) (suffix : Word MachineCodeSymbol) :
    exists symbol : MachineCodeSymbol,
    exists tail : Word MachineCodeSymbol,
      MachineDescription.encodeNatAppend n suffix = symbol :: tail := by
  cases n with
  | zero =>
      exact ⟨MachineCodeSymbol.done, suffix, rfl⟩
  | succ n =>
      exact
        ⟨MachineCodeSymbol.tick,
          MachineDescription.encodeNatAppend n suffix, rfl⟩

theorem encodeBoolWord_cons
    (w : Word Bool) :
    exists symbol : MachineCodeSymbol,
    exists tail : Word MachineCodeSymbol,
      MachineDescription.encodeBoolWord w = symbol :: tail := by
  simpa [MachineDescription.encodeBoolWord,
    MachineDescription.encodeBoolWordAppend,
    MachineDescription.encodeCellListAppend] using
      encodeNatAppend_cons (w.map some).length
        (MachineDescription.encodeCellsAppend (w.map some) [])

theorem pairedRecognizerDovetailTotalOutputCode_transform_eq_some_cons
    {code out : Word MachineCodeSymbol}
    (h :
      PairedRecognizerDovetailTotalOutputCode.transform code = some out) :
    exists symbol : MachineCodeSymbol,
    exists tail : Word MachineCodeSymbol,
      out = symbol :: tail := by
  rcases
      (pairedRecognizerDovetailTotalOutputCode_transform_eq_some_iff
        code out).mp h with
    ⟨L, _hcode, hout⟩
  rcases
      encodeBoolWord_cons
        (MachineDescription.DovetailLayout.outputWordFromHits L) with
    ⟨symbol, tail, htail⟩
  exact ⟨symbol, tail, by rw [hout, htail]⟩

end EncodedRewriters

end Computability
end FoC
