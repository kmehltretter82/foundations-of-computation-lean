import FoC.Computability.Compiler.Core.TapeCodePrimitives

set_option doc.verso true

/-!
# Right-shifted encoded-rewriter handoff helpers

Right-shifted rewriters halt one cell to the right of the canonical Boolean
encoding they emit.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

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
            (encodeCodeWordAsInput (symbol :: code)))) =
      Tape.input
        (encodeCodeWordAsInput (symbol :: code)) := by
  cases symbol <;> rfl

theorem tapeCodePrimitiveCodeWord_handoff_tape
    (symbol : MachineCodeSymbol) (code : Word MachineCodeSymbol) :
    Tape.normalizedOutput
        (Tape.move Direction.right
          (Tape.input
            (encodeCodeWordAsInput (symbol :: code)))) =
        encodeCodeWordAsInput (symbol :: code) ∧
      Tape.move tapeCodePrimitiveCodeWordHandoffMove
        (Tape.move Direction.right
          (Tape.input
            (encodeCodeWordAsInput (symbol :: code)))) =
        Tape.input
          (encodeCodeWordAsInput (symbol :: code)) :=
  ⟨tape_normalizedOutput_move_right_input
      (encodeCodeWordAsInput (symbol :: code)),
    by
      simpa [tapeCodePrimitiveCodeWordHandoffMove] using
      tape_move_left_move_right_input_encodeCodeWordAsInput_cons
        symbol code⟩

def RightShiftedOutputCompiledSubroutineByDescription
    (P : TapeCodePrimitive)
    (D : MachineDescription) : Prop :=
  D.WellFormed ∧
    D.HaltTransitionFree ∧
      (forall code out : Word MachineCodeSymbol,
        D.HaltsWithOutput
            (encodeCodeWordAsInput code)
            (encodeCodeWordAsInput out) <->
          P.transform code = some out) ∧
        forall code : Word MachineCodeSymbol,
        forall T : Tape Bool,
          D.HaltsWithTape
              (encodeCodeWordAsInput code) T ->
            exists out : Word MachineCodeSymbol,
              P.transform code = some out ∧
              T =
                Tape.move Direction.right
                  (Tape.input
                    (encodeCodeWordAsInput out))

def ExactRightShiftedOutputCompiledSubroutineByDescription
    (P : TapeCodePrimitive)
    (D : MachineDescription) : Prop :=
  D.WellFormed ∧
    D.HaltTransitionFree ∧
      (forall code out : Word MachineCodeSymbol,
        P.transform code = some out ->
          D.HaltsWithTape
            (encodeCodeWordAsInput code)
            (Tape.move Direction.right
              (Tape.input
                (encodeCodeWordAsInput out)))) ∧
        forall code : Word MachineCodeSymbol,
        forall T : Tape Bool,
          D.HaltsWithTape
              (encodeCodeWordAsInput code) T ->
            exists out : Word MachineCodeSymbol,
              P.transform code = some out ∧
              T =
                Tape.move Direction.right
                  (Tape.input
                    (encodeCodeWordAsInput out))

theorem rightShiftedOutputCompiledSubroutineByDescription_of_exact
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (h :
      ExactRightShiftedOutputCompiledSubroutineByDescription P D) :
    RightShiftedOutputCompiledSubroutineByDescription P D := by
  constructor
  · exact h.left
  constructor
  · exact h.right.left
  constructor
  · intro code out
    constructor
    · intro houtput
      rcases houtput with ⟨n, hn⟩
      let T : Tape Bool :=
        (D.runConfig n
          (D.initial
            (encodeCodeWordAsInput code))).tape
      have hhalt :
          D.HaltsWithTape (encodeCodeWordAsInput code) T :=
        ⟨n, ⟨hn.left, rfl⟩⟩
      rcases h.right.right.right code T hhalt with
        ⟨actual, hactual, hT⟩
      have hbits :
          encodeCodeWordAsInput out =
            encodeCodeWordAsInput actual := by
        have hnormalizedActual :
            Tape.normalizedOutput T =
              encodeCodeWordAsInput actual := by
          rw [hT]
          exact
            tape_normalizedOutput_move_right_input
              (encodeCodeWordAsInput actual)
        exact hn.right.symm.trans hnormalizedActual
      have hout : out = actual :=
        encodeCodeWordAsInput_injective hbits
      simpa [hout] using hactual
    · intro htransform
      simpa [tape_normalizedOutput_move_right_input] using
        haltsWithOutput_of_haltsWithTape
          (h.right.right.left code out htransform)
  · intro code T hhalt
    exact h.right.right.right code T hhalt

/-!
Accessor lemmas keep later proofs independent of the conjunction layout of
{name}`RightShiftedOutputCompiledSubroutineByDescription`.
-/

theorem rightShiftedOutputCompiledSubroutineByDescription_wellFormed
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (h : RightShiftedOutputCompiledSubroutineByDescription P D) :
    D.WellFormed :=
  h.left

theorem rightShiftedOutputCompiledSubroutineByDescription_haltTransitionFree
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (h : RightShiftedOutputCompiledSubroutineByDescription P D) :
    D.HaltTransitionFree :=
  h.right.left

theorem rightShiftedOutputCompiledSubroutineByDescription_haltsWithOutput_iff
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (h : RightShiftedOutputCompiledSubroutineByDescription P D)
    (code out : Word MachineCodeSymbol) :
    D.HaltsWithOutput
        (encodeCodeWordAsInput code)
        (encodeCodeWordAsInput out) <->
      P.transform code = some out :=
  h.right.right.left code out

theorem rightShiftedOutputCompiledSubroutineByDescription_haltsWithOutput_of_transform_eq_some
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (h : RightShiftedOutputCompiledSubroutineByDescription P D)
    {code out : Word MachineCodeSymbol}
    (hp : P.transform code = some out) :
    D.HaltsWithOutput
      (encodeCodeWordAsInput code)
      (encodeCodeWordAsInput out) :=
  (rightShiftedOutputCompiledSubroutineByDescription_haltsWithOutput_iff
    h code out).mpr hp

theorem rightShiftedOutputCompiledSubroutineByDescription_transform_eq_some_of_haltsWithOutput
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (h : RightShiftedOutputCompiledSubroutineByDescription P D)
    {code out : Word MachineCodeSymbol}
    (hD :
      D.HaltsWithOutput
        (encodeCodeWordAsInput code)
        (encodeCodeWordAsInput out)) :
    P.transform code = some out :=
  (rightShiftedOutputCompiledSubroutineByDescription_haltsWithOutput_iff
    h code out).mp hD

theorem rightShiftedOutputCompiledSubroutineByDescription_haltsWithTape_inv
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (h : RightShiftedOutputCompiledSubroutineByDescription P D)
    {code : Word MachineCodeSymbol} {T : Tape Bool}
    (hD :
      D.HaltsWithTape
        (encodeCodeWordAsInput code) T) :
    exists out : Word MachineCodeSymbol,
      P.transform code = some out ∧
        T =
          Tape.move Direction.right
            (Tape.input
              (encodeCodeWordAsInput out)) :=
  h.right.right.right code T hD

theorem rightShiftedOutputCompiledSubroutineByDescription_outputCompiled
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (h : RightShiftedOutputCompiledSubroutineByDescription P D) :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription P D :=
  ⟨⟨h.left, h.right.right.left⟩, h.right.left⟩

theorem rightShiftedOutputCompiledSubroutineByDescription_subroutineReady
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (h : RightShiftedOutputCompiledSubroutineByDescription P D) :
    D.SubroutineReady :=
  ⟨h.left, h.right.left⟩

theorem rightShifted_haltsWithOutput_iff
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (h : RightShiftedOutputCompiledSubroutineByDescription P D)
    (code out : Word MachineCodeSymbol) :
    D.HaltsWithOutput
        (encodeCodeWordAsInput code)
        (encodeCodeWordAsInput out) <->
      P.transform code = some out :=
  rightShiftedOutputCompiledSubroutineByDescription_haltsWithOutput_iff
    h code out

theorem rightShifted_haltsWithTape_inv
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (h : RightShiftedOutputCompiledSubroutineByDescription P D)
    {code : Word MachineCodeSymbol} {T : Tape Bool}
    (hD :
      D.HaltsWithTape
        (encodeCodeWordAsInput code) T) :
    exists out : Word MachineCodeSymbol,
      P.transform code = some out ∧
        T =
          Tape.move Direction.right
            (Tape.input
              (encodeCodeWordAsInput out)) :=
  rightShiftedOutputCompiledSubroutineByDescription_haltsWithTape_inv
    h hD

theorem rightShifted_outputCompiled
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (h : RightShiftedOutputCompiledSubroutineByDescription P D) :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription P D :=
  rightShiftedOutputCompiledSubroutineByDescription_outputCompiled h

theorem rightShifted_subroutineReady
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (h : RightShiftedOutputCompiledSubroutineByDescription P D) :
    D.SubroutineReady :=
  rightShiftedOutputCompiledSubroutineByDescription_subroutineReady h

theorem closedHandoffCompiled_of_halt_tape_move_right
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (hwell : D.WellFormed)
    (hhaltFree : D.HaltTransitionFree)
    (houtput :
      forall code out : Word MachineCodeSymbol,
        D.HaltsWithOutput
            (encodeCodeWordAsInput code)
            (encodeCodeWordAsInput out) <->
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
            (encodeCodeWordAsInput code) T ->
          exists out : Word MachineCodeSymbol,
            P.transform code = some out ∧
              T =
                Tape.move Direction.right
                  (Tape.input
                    (encodeCodeWordAsInput out))) :
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
    {P : TapeCodePrimitive}
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
    (L : DovetailLayout) :
    exists tail : Word MachineCodeSymbol,
      DovetailLayout.encode L =
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
        (DovetailLayout.run accept reject L.stage L) with
    ⟨tail, htail⟩
  exact ⟨tail, by rw [hout, htail]⟩

theorem encodeNatAppend_cons
    (n : Nat) (suffix : Word MachineCodeSymbol) :
    exists symbol : MachineCodeSymbol,
    exists tail : Word MachineCodeSymbol,
      encodeNatAppend n suffix = symbol :: tail := by
  cases n with
  | zero =>
      exact ⟨MachineCodeSymbol.done, suffix, rfl⟩
  | succ n =>
      exact
        ⟨MachineCodeSymbol.tick,
          encodeNatAppend n suffix, rfl⟩

theorem encodeBoolWord_cons
    (w : Word Bool) :
    exists symbol : MachineCodeSymbol,
    exists tail : Word MachineCodeSymbol,
      encodeBoolWord w = symbol :: tail := by
  simpa [encodeBoolWord,
    encodeBoolWordAppend,
    encodeCellListAppend] using
      encodeNatAppend_cons (w.map some).length
        (encodeCellsAppend (w.map some) [])

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
        (DovetailLayout.outputWordFromHits L) with
    ⟨symbol, tail, htail⟩
  exact ⟨symbol, tail, by rw [hout, htail]⟩

end EncodedRewriters

end Computability
end FoC
