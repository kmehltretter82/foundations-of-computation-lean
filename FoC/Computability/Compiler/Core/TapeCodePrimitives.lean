import FoC.Computability.Compiler.Core.DovetailCode

set_option doc.verso true

/-!
# Tape-code primitive compiler interfaces
-/

namespace FoC
namespace Computability

open Languages

/-!
The compiled dovetail subroutines hand their output to the next subroutine by
halting with the head just to the right of the emitted canonical Boolean word.
One left move then puts the next subroutine at the same canonical
{name}`Tape.input` layout.
-/

def tapeCodePrimitiveCodeWordHandoffMove : Direction :=
  Direction.left

theorem tape_move_right_ne_input {symbol : Type} (T : Tape symbol)
    (w : Word symbol) :
    Tape.move Direction.right T ≠ Tape.input w := by
  cases T with
  | mk left head right =>
      cases right with
      | nil =>
          cases w <;> simp [Tape.move, Tape.moveRight, Tape.input, Tape.blank]
      | cons cell rest =>
          cases w <;> simp [Tape.move, Tape.moveRight, Tape.input, Tape.blank]

def TapeCodePrimitiveCompiledByDescription
    (P : MachineDescription.TapeCodePrimitive)
    (D : MachineDescription) : Prop :=
  D.WellFormed ∧
    forall code out : Word MachineCodeSymbol,
      D.HaltsWithExactOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) <->
          P.transform code = some out

def TapeCodePrimitiveOutputRealizedByDescription
    (P : MachineDescription.TapeCodePrimitive)
    (D : MachineDescription) : Prop :=
  D.WellFormed ∧
    forall code out : Word MachineCodeSymbol,
      P.transform code = some out ->
        D.HaltsWithOutput
          (MachineDescription.encodeCodeWordAsInput code)
          (MachineDescription.encodeCodeWordAsInput out)

def TapeCodePrimitiveOutputCompiledByDescription
    (P : MachineDescription.TapeCodePrimitive)
    (D : MachineDescription) : Prop :=
  D.WellFormed ∧
    forall code out : Word MachineCodeSymbol,
      D.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) <->
          P.transform code = some out

def TapeCodePrimitiveOutputSubroutineRealizedByDescription
    (P : MachineDescription.TapeCodePrimitive)
    (D : MachineDescription) : Prop :=
  TapeCodePrimitiveOutputRealizedByDescription P D ∧
    D.HaltTransitionFree

def TapeCodePrimitiveOutputCompiledSubroutineByDescription
    (P : MachineDescription.TapeCodePrimitive)
    (D : MachineDescription) : Prop :=
  TapeCodePrimitiveOutputCompiledByDescription P D ∧
    D.HaltTransitionFree

def TapeCodePrimitiveHandoffSubroutineRealizedByDescription
    (P : MachineDescription.TapeCodePrimitive)
    (D : MachineDescription) (handoffMove : Direction) : Prop :=
  TapeCodePrimitiveOutputSubroutineRealizedByDescription P D ∧
    forall code out : Word MachineCodeSymbol,
      P.transform code = some out ->
        exists T : Tape Bool,
          D.HaltsWithTape
            (MachineDescription.encodeCodeWordAsInput code) T ∧
          Tape.move handoffMove T =
            Tape.input (MachineDescription.encodeCodeWordAsInput out)

def TapeCodePrimitiveHandoffCompiledSubroutineByDescription
    (P : MachineDescription.TapeCodePrimitive)
    (D : MachineDescription) (handoffMove : Direction) : Prop :=
  TapeCodePrimitiveOutputCompiledSubroutineByDescription P D ∧
    forall code out : Word MachineCodeSymbol,
      P.transform code = some out ->
        exists T : Tape Bool,
          D.HaltsWithTape
            (MachineDescription.encodeCodeWordAsInput code) T ∧
          Tape.move handoffMove T =
            Tape.input (MachineDescription.encodeCodeWordAsInput out)

def TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
    (P : MachineDescription.TapeCodePrimitive)
    (D : MachineDescription) (handoffMove : Direction) : Prop :=
  TapeCodePrimitiveOutputCompiledSubroutineByDescription P D ∧
    forall code : Word MachineCodeSymbol,
    forall T : Tape Bool,
      D.HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) T ->
        exists out : Word MachineCodeSymbol,
          P.transform code = some out ∧
            Tape.normalizedOutput T =
              MachineDescription.encodeCodeWordAsInput out ∧
            Tape.move handoffMove T =
              Tape.input (MachineDescription.encodeCodeWordAsInput out)

theorem not_tapeCodePrimitiveHandoffCompiledSubroutineByDescription_right_of_transform_eq_some
    {P : MachineDescription.TapeCodePrimitive} {D : MachineDescription}
    {code out : Word MachineCodeSymbol}
    (hp : P.transform code = some out) :
    ¬ TapeCodePrimitiveHandoffCompiledSubroutineByDescription
        P D Direction.right := by
  intro hD
  rcases hD.right code out hp with ⟨T, _hhalt, hmove⟩
  exact tape_move_right_ne_input T
    (MachineDescription.encodeCodeWordAsInput out) hmove

theorem not_tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_right_of_transform_eq_some
    {P : MachineDescription.TapeCodePrimitive} {D : MachineDescription}
    {code out : Word MachineCodeSymbol}
    (hp : P.transform code = some out) :
    ¬ TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        P D Direction.right := by
  intro hD
  have hOut :
      D.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) :=
    (hD.left.left.right code out).mpr hp
  rcases hOut with ⟨n, hn⟩
  let T : Tape Bool :=
    (D.runConfig n
      (D.initial (MachineDescription.encodeCodeWordAsInput code))).tape
  have hTape :
      D.HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) T := by
    refine ⟨n, ?_⟩
    exact ⟨hn.left, rfl⟩
  rcases hD.right code T hTape with ⟨out', _hp', _hnorm, hmove⟩
  exact tape_move_right_ne_input T
    (MachineDescription.encodeCodeWordAsInput out') hmove

theorem tapeCodePrimitiveOutputCompiledByDescription_wellFormed
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledByDescription P D) :
    D.WellFormed :=
  h.left

theorem tapeCodePrimitiveOutputCompiledByDescription_haltsWithOutput_iff
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledByDescription P D)
    (code out : Word MachineCodeSymbol) :
    D.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) <->
      P.transform code = some out :=
  h.right code out

theorem tapeCodePrimitiveOutputCompiledByDescription_haltsWithOutput_of_transform_eq_some
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledByDescription P D)
    {code out : Word MachineCodeSymbol}
    (hp : P.transform code = some out) :
    D.HaltsWithOutput
      (MachineDescription.encodeCodeWordAsInput code)
      (MachineDescription.encodeCodeWordAsInput out) :=
  (h.right code out).mpr hp

theorem tapeCodePrimitiveOutputCompiledByDescription_transform_eq_some_of_haltsWithOutput
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledByDescription P D)
    {code out : Word MachineCodeSymbol}
    (hD :
      D.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out)) :
    P.transform code = some out :=
  (h.right code out).mp hD

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_wellFormed
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledSubroutineByDescription P D) :
    D.WellFormed :=
  h.left.left

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_haltTransitionFree
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledSubroutineByDescription P D) :
    D.HaltTransitionFree :=
  h.right

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_haltsWithOutput_iff
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledSubroutineByDescription P D)
    (code out : Word MachineCodeSymbol) :
    D.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) <->
      P.transform code = some out :=
  h.left.right code out

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_haltsWithOutput_of_transform_eq_some
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledSubroutineByDescription P D)
    {code out : Word MachineCodeSymbol}
    (hp : P.transform code = some out) :
    D.HaltsWithOutput
      (MachineDescription.encodeCodeWordAsInput code)
      (MachineDescription.encodeCodeWordAsInput out) :=
  (h.left.right code out).mpr hp

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_transform_eq_some_of_haltsWithOutput
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledSubroutineByDescription P D)
    {code out : Word MachineCodeSymbol}
    (hD :
      D.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out)) :
    P.transform code = some out :=
  (h.left.right code out).mp hD

theorem tapeCodePrimitiveHandoffSubroutineRealizedByDescription_outputRealized
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveHandoffSubroutineRealizedByDescription
      P D handoffMove) :
    TapeCodePrimitiveOutputSubroutineRealizedByDescription P D :=
  h.left

theorem tapeCodePrimitiveHandoffSubroutineRealizedByDescription_haltTransitionFree
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveHandoffSubroutineRealizedByDescription
      P D handoffMove) :
    D.HaltTransitionFree :=
  h.left.right

theorem tapeCodePrimitiveHandoffSubroutineRealizedByDescription_subroutineReady
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveHandoffSubroutineRealizedByDescription
      P D handoffMove) :
    D.SubroutineReady :=
  ⟨h.left.left.left, h.left.right⟩

theorem tapeCodePrimitiveHandoffSubroutineRealizedByDescription_haltsWithOutput_of_transform_eq_some
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveHandoffSubroutineRealizedByDescription
      P D handoffMove)
    {code out : Word MachineCodeSymbol}
    (hp : P.transform code = some out) :
    D.HaltsWithOutput
      (MachineDescription.encodeCodeWordAsInput code)
      (MachineDescription.encodeCodeWordAsInput out) :=
  h.left.left.right code out hp

theorem tapeCodePrimitiveHandoffSubroutineRealizedByDescription_haltsWithTape_of_transform_eq_some
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveHandoffSubroutineRealizedByDescription
      P D handoffMove)
    {code out : Word MachineCodeSymbol}
    (hp : P.transform code = some out) :
    exists T : Tape Bool,
      D.HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) T ∧
      Tape.move handoffMove T =
        Tape.input (MachineDescription.encodeCodeWordAsInput out) :=
  h.right code out hp

theorem tapeCodePrimitiveHandoffCompiledSubroutineByDescription_outputCompiled
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveHandoffCompiledSubroutineByDescription
      P D handoffMove) :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription P D :=
  h.left

theorem tapeCodePrimitiveHandoffCompiledSubroutineByDescription_subroutineReady
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveHandoffCompiledSubroutineByDescription
      P D handoffMove) :
    D.SubroutineReady :=
  ⟨h.left.left.left, h.left.right⟩

theorem tapeCodePrimitiveHandoffCompiledSubroutineByDescription_haltsWithOutput_of_transform_eq_some
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveHandoffCompiledSubroutineByDescription
      P D handoffMove)
    {code out : Word MachineCodeSymbol}
    (hp : P.transform code = some out) :
    D.HaltsWithOutput
      (MachineDescription.encodeCodeWordAsInput code)
      (MachineDescription.encodeCodeWordAsInput out) :=
  tapeCodePrimitiveOutputCompiledSubroutineByDescription_haltsWithOutput_of_transform_eq_some
    h.left hp

theorem tapeCodePrimitiveHandoffCompiledSubroutineByDescription_haltsWithTape_of_transform_eq_some
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveHandoffCompiledSubroutineByDescription
      P D handoffMove)
    {code out : Word MachineCodeSymbol}
    (hp : P.transform code = some out) :
    exists T : Tape Bool,
      D.HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) T ∧
      Tape.move handoffMove T =
        Tape.input (MachineDescription.encodeCodeWordAsInput out) :=
  h.right code out hp

theorem tapeCodePrimitiveHandoffSubroutineRealizedByDescription_of_handoffCompiled
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveHandoffCompiledSubroutineByDescription
      P D handoffMove) :
    TapeCodePrimitiveHandoffSubroutineRealizedByDescription
      P D handoffMove :=
  ⟨⟨⟨h.left.left.left,
        fun code out hp => (h.left.left.right code out).mpr hp⟩,
      h.left.right⟩,
    h.right⟩

theorem tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_outputCompiled
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      P D handoffMove) :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription P D :=
  h.left

theorem tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_haltsWithTape_output
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      P D handoffMove)
    {code : Word MachineCodeSymbol} {T : Tape Bool}
    (hhalt :
      D.HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) T) :
    exists out : Word MachineCodeSymbol,
      P.transform code = some out ∧
        Tape.normalizedOutput T =
          MachineDescription.encodeCodeWordAsInput out ∧
        Tape.move handoffMove T =
          Tape.input (MachineDescription.encodeCodeWordAsInput out) :=
  h.right code T hhalt

theorem tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffCompiled
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      P D handoffMove) :
    TapeCodePrimitiveHandoffCompiledSubroutineByDescription
      P D handoffMove := by
  constructor
  · exact h.left
  · intro code out hp
    rcases
        tapeCodePrimitiveOutputCompiledSubroutineByDescription_haltsWithOutput_of_transform_eq_some
          h.left hp with
      ⟨n, hn⟩
    let T : Tape Bool :=
      (D.runConfig n
        (D.initial (MachineDescription.encodeCodeWordAsInput code))).tape
    have hTape :
        D.HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput code) T := by
      refine ⟨n, ?_⟩
      exact ⟨hn.left, rfl⟩
    rcases h.right code T hTape with
      ⟨out', hp', _hnorm, hmove⟩
    have hout' : out' = out := by
      rw [hp] at hp'
      cases hp'
      rfl
    exact ⟨T, hTape, by simpa [hout'] using hmove⟩

theorem tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffRealized
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      P D handoffMove) :
    TapeCodePrimitiveHandoffSubroutineRealizedByDescription
      P D handoffMove :=
  tapeCodePrimitiveHandoffSubroutineRealizedByDescription_of_handoffCompiled
    (tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffCompiled
      h)

theorem haltsWithEncodedCodeOutput_functional_of_haltTransitionFree
    {D : MachineDescription}
    {w : Word Bool}
    {out₁ out₂ : Word MachineCodeSymbol}
    (hD : D.HaltTransitionFree)
    (h₁ :
      D.HaltsWithOutput w
        (MachineDescription.encodeCodeWordAsInput out₁))
    (h₂ :
      D.HaltsWithOutput w
        (MachineDescription.encodeCodeWordAsInput out₂)) :
    out₁ = out₂ :=
  MachineDescription.encodeCodeWordAsInput_injective
    (MachineDescription.haltsWithOutput_functional_of_haltTransitionFree
      hD h₁ h₂)

theorem tapeCodePrimitiveOutputSubroutineRealizedByDescription_output_eq_of_haltsWithOutput
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputSubroutineRealizedByDescription P D)
    {code expected actual : Word MachineCodeSymbol}
    (hp : P.transform code = some expected)
    (hD :
      D.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput actual)) :
    expected = actual :=
  haltsWithEncodedCodeOutput_functional_of_haltTransitionFree h.right
    (h.left.right code expected hp) hD

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_congr
    {P Q : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (hPQ : forall code : Word MachineCodeSymbol,
      P.transform code = Q.transform code)
    (hD : TapeCodePrimitiveOutputCompiledSubroutineByDescription P D) :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription Q D := by
  constructor
  · constructor
    · exact hD.left.left
    · intro code out
      simpa [hPQ code] using hD.left.right code out
  · exact hD.right

theorem tapeCodePrimitiveHandoffSubroutineRealizedByDescription_congr
    {P Q : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (hPQ : forall code : Word MachineCodeSymbol,
      P.transform code = Q.transform code)
    (hD : TapeCodePrimitiveHandoffSubroutineRealizedByDescription
      P D handoffMove) :
    TapeCodePrimitiveHandoffSubroutineRealizedByDescription
      Q D handoffMove := by
  constructor
  · constructor
    · constructor
      · exact hD.left.left.left
      · intro code out hQ
        exact hD.left.left.right code out
          (by simpa [hPQ code] using hQ)
    · exact hD.left.right
  · intro code out hQ
    exact hD.right code out
      (by simpa [hPQ code] using hQ)

theorem tapeCodePrimitiveOutputRealizedByDescription_of_outputCompiled
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledByDescription P D) :
    TapeCodePrimitiveOutputRealizedByDescription P D := by
  constructor
  · exact h.left
  · intro code out hp
    exact (h.right code out).mpr hp

theorem tapeCodePrimitiveOutputSubroutineRealizedByDescription_of_outputCompiled
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledSubroutineByDescription P D) :
    TapeCodePrimitiveOutputSubroutineRealizedByDescription P D :=
  ⟨tapeCodePrimitiveOutputRealizedByDescription_of_outputCompiled h.left,
    h.right⟩

theorem tapeCodePrimitiveOutputRealizedByDescription_of_exact
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveCompiledByDescription P D) :
    TapeCodePrimitiveOutputRealizedByDescription P D := by
  constructor
  · exact h.left
  · intro code out hp
    exact MachineDescription.haltsWithOutput_of_haltsWithExactOutput
      ((h.right code out).mpr hp)

theorem tapeCodePrimitiveOutputRealizedByDescription_of_subroutine
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputSubroutineRealizedByDescription P D) :
    TapeCodePrimitiveOutputRealizedByDescription P D :=
  h.left

theorem tapeCodePrimitiveOutputSubroutineRealizedByDescription_subroutineReady
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputSubroutineRealizedByDescription P D) :
    D.SubroutineReady :=
  ⟨h.left.left, h.right⟩

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_subroutineReady
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledSubroutineByDescription P D) :
    D.SubroutineReady :=
  ⟨h.left.left, h.right⟩

theorem tapeCodePrimitiveCompiledByDescription_identity :
    TapeCodePrimitiveCompiledByDescription
      MachineDescription.TapeCodePrimitive.identity
      MachineDescription.ExactIdentityDescription := by
  constructor
  · exact MachineDescription.exactIdentityDescription_wellFormed
  · intro code out
    constructor
    · intro h
      have hbool :
          MachineDescription.encodeCodeWordAsInput out =
            MachineDescription.encodeCodeWordAsInput code :=
        (MachineDescription.exactIdentityDescription_haltsWithExactOutput_iff
          (MachineDescription.encodeCodeWordAsInput code)
          (MachineDescription.encodeCodeWordAsInput out)).mp h
      have hout : out = code :=
        MachineDescription.encodeCodeWordAsInput_injective hbool
      simp [MachineDescription.TapeCodePrimitive.identity, hout]
    · intro h
      simp [MachineDescription.TapeCodePrimitive.identity] at h
      rw [← h]
      exact
        (MachineDescription.exactIdentityDescription_haltsWithExactOutput_iff
          (MachineDescription.encodeCodeWordAsInput code)
          (MachineDescription.encodeCodeWordAsInput code)).mpr rfl

theorem tapeCodePrimitiveOutputRealizedByDescription_identity :
    TapeCodePrimitiveOutputRealizedByDescription
      MachineDescription.TapeCodePrimitive.identity
      MachineDescription.ExactIdentityDescription :=
  tapeCodePrimitiveOutputRealizedByDescription_of_exact
    tapeCodePrimitiveCompiledByDescription_identity

theorem tapeCodePrimitiveOutputCompiledByDescription_identity :
    TapeCodePrimitiveOutputCompiledByDescription
      MachineDescription.TapeCodePrimitive.identity
      MachineDescription.ExactIdentityDescription := by
  constructor
  · exact MachineDescription.exactIdentityDescription_wellFormed
  · intro code out
    constructor
    · intro h
      have hbool :
          MachineDescription.encodeCodeWordAsInput out =
            MachineDescription.encodeCodeWordAsInput code :=
        (MachineDescription.exactIdentityDescription_haltsWithOutput_iff
          (MachineDescription.encodeCodeWordAsInput code)
          (MachineDescription.encodeCodeWordAsInput out)).mp h
      have hout : out = code :=
        MachineDescription.encodeCodeWordAsInput_injective hbool
      simp [MachineDescription.TapeCodePrimitive.identity, hout]
    · intro h
      simp [MachineDescription.TapeCodePrimitive.identity] at h
      rw [← h]
      exact (MachineDescription.exactIdentityDescription_haltsWithOutput_iff
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput code)).mpr rfl

theorem tapeCodePrimitiveOutputSubroutineRealizedByDescription_identity :
    TapeCodePrimitiveOutputSubroutineRealizedByDescription
      MachineDescription.TapeCodePrimitive.identity
      MachineDescription.ExactIdentityDescription :=
  ⟨tapeCodePrimitiveOutputRealizedByDescription_identity,
    MachineDescription.exactIdentityDescription_haltTransitionFree⟩

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_identity :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      MachineDescription.TapeCodePrimitive.identity
      MachineDescription.ExactIdentityDescription :=
  ⟨tapeCodePrimitiveOutputCompiledByDescription_identity,
    MachineDescription.exactIdentityDescription_haltTransitionFree⟩

theorem pairedRecognizerDovetailControllerRawOutputCodeOutputRealizedByDescription :
    TapeCodePrimitiveOutputRealizedByDescription
      PairedRecognizerDovetailControllerRawOutputCode
      MachineDescription.ExactIdentityDescription := by
  constructor
  · exact MachineDescription.exactIdentityDescription_wellFormed
  · intro code out h
    have hout : out = code :=
      pairedRecognizerDovetailControllerRawOutputCode_eq_some_self h
    rw [hout]
    exact
      (MachineDescription.exactIdentityDescription_haltsWithOutput_iff
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput code)).mpr rfl

theorem tapeCodePrimitiveOutputRealizedByDescription_erase :
    TapeCodePrimitiveOutputRealizedByDescription
      MachineDescription.TapeCodePrimitive.erase
      MachineDescription.EraseRightDescription := by
  constructor
  · exact MachineDescription.eraseRightDescription_wellFormed
  · intro code out h
    simp [MachineDescription.TapeCodePrimitive.erase] at h
    rw [← h]
    exact MachineDescription.eraseRightDescription_haltsWithOutput_empty
      (MachineDescription.encodeCodeWordAsInput code)

theorem tapeCodePrimitiveOutputCompiledByDescription_erase :
    TapeCodePrimitiveOutputCompiledByDescription
      MachineDescription.TapeCodePrimitive.erase
      MachineDescription.EraseRightDescription := by
  constructor
  · exact MachineDescription.eraseRightDescription_wellFormed
  · intro code out
    constructor
    · intro h
      have hnil :
          MachineDescription.EraseRightDescription.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput code)
            (MachineDescription.encodeCodeWordAsInput
              ([] : Word MachineCodeSymbol)) := by
        simpa [MachineDescription.encodeCodeWordAsInput] using
          MachineDescription.eraseRightDescription_haltsWithOutput_empty
            (MachineDescription.encodeCodeWordAsInput code)
      have hbool :
          MachineDescription.encodeCodeWordAsInput out =
            MachineDescription.encodeCodeWordAsInput
              ([] : Word MachineCodeSymbol) :=
        MachineDescription.haltsWithOutput_functional_of_haltTransitionFree
          MachineDescription.eraseRightDescription_haltTransitionFree h hnil
      have hout : out = [] :=
        MachineDescription.encodeCodeWordAsInput_injective hbool
      simp [MachineDescription.TapeCodePrimitive.erase, hout]
    · intro h
      exact (tapeCodePrimitiveOutputRealizedByDescription_erase.right
        code out) h

theorem tapeCodePrimitiveOutputSubroutineRealizedByDescription_erase :
    TapeCodePrimitiveOutputSubroutineRealizedByDescription
      MachineDescription.TapeCodePrimitive.erase
      MachineDescription.EraseRightDescription :=
  ⟨tapeCodePrimitiveOutputRealizedByDescription_erase,
    MachineDescription.eraseRightDescription_haltTransitionFree⟩

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_erase :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      MachineDescription.TapeCodePrimitive.erase
      MachineDescription.EraseRightDescription :=
  ⟨tapeCodePrimitiveOutputCompiledByDescription_erase,
    MachineDescription.eraseRightDescription_haltTransitionFree⟩

theorem tapeCodePrimitiveOutputRealizedByDescription_append_singleton
    (symbol : MachineCodeSymbol) :
    TapeCodePrimitiveOutputRealizedByDescription
      (MachineDescription.TapeCodePrimitive.append [symbol])
      (MachineDescription.AppendCodeSymbolRightDescription symbol) := by
  constructor
  · exact MachineDescription.appendCodeSymbolRightDescription_wellFormed
      symbol
  · intro code out h
    simp [MachineDescription.TapeCodePrimitive.append] at h
    rw [← h]
    have hencoded :
        MachineDescription.encodeCodeWordAsInput
            (List.append code [symbol]) =
          List.append (MachineDescription.encodeCodeWordAsInput code)
            (MachineDescription.encodeCodeSymbolAsInput symbol) := by
      rw [MachineDescription.encodeCodeWordAsInput_append,
        MachineDescription.encodeCodeWordAsInput_singleton]
    change
      (MachineDescription.AppendCodeSymbolRightDescription symbol).HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput
          (List.append code [symbol]))
    rw [hencoded]
    exact
      MachineDescription.appendCodeSymbolRightDescription_haltsWithOutput_append
        symbol (MachineDescription.encodeCodeWordAsInput code)

theorem tapeCodePrimitiveOutputCompiledByDescription_append_singleton
    (symbol : MachineCodeSymbol) :
    TapeCodePrimitiveOutputCompiledByDescription
      (MachineDescription.TapeCodePrimitive.append [symbol])
      (MachineDescription.AppendCodeSymbolRightDescription symbol) := by
  constructor
  · exact MachineDescription.appendCodeSymbolRightDescription_wellFormed
      symbol
  · intro code out
    constructor
    · intro h
      have hencoded :
          MachineDescription.encodeCodeWordAsInput
              (List.append code [symbol]) =
            List.append (MachineDescription.encodeCodeWordAsInput code)
              (MachineDescription.encodeCodeSymbolAsInput symbol) := by
        rw [MachineDescription.encodeCodeWordAsInput_append,
          MachineDescription.encodeCodeWordAsInput_singleton]
      have htarget :
          (MachineDescription.AppendCodeSymbolRightDescription
            symbol).HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput code)
            (MachineDescription.encodeCodeWordAsInput
              (List.append code [symbol])) := by
        rw [hencoded]
        exact
          MachineDescription.appendCodeSymbolRightDescription_haltsWithOutput_append
            symbol (MachineDescription.encodeCodeWordAsInput code)
      have hbool :
          MachineDescription.encodeCodeWordAsInput out =
            MachineDescription.encodeCodeWordAsInput
              (List.append code [symbol]) :=
        MachineDescription.haltsWithOutput_functional_of_haltTransitionFree
          (MachineDescription.appendCodeSymbolRightDescription_haltTransitionFree
            symbol) h htarget
      have hout : out = List.append code [symbol] :=
        MachineDescription.encodeCodeWordAsInput_injective hbool
      simp [MachineDescription.TapeCodePrimitive.append, hout]
    · intro h
      exact
        (tapeCodePrimitiveOutputRealizedByDescription_append_singleton
          symbol).right code out h

theorem tapeCodePrimitiveOutputSubroutineRealizedByDescription_append_singleton
    (symbol : MachineCodeSymbol) :
    TapeCodePrimitiveOutputSubroutineRealizedByDescription
      (MachineDescription.TapeCodePrimitive.append [symbol])
      (MachineDescription.AppendCodeSymbolRightDescription symbol) :=
  ⟨tapeCodePrimitiveOutputRealizedByDescription_append_singleton symbol,
    MachineDescription.appendCodeSymbolRightDescription_haltTransitionFree
      symbol⟩

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_append_singleton
    (symbol : MachineCodeSymbol) :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      (MachineDescription.TapeCodePrimitive.append [symbol])
      (MachineDescription.AppendCodeSymbolRightDescription symbol) :=
  ⟨tapeCodePrimitiveOutputCompiledByDescription_append_singleton symbol,
    MachineDescription.appendCodeSymbolRightDescription_haltTransitionFree
      symbol⟩

theorem not_tapeCodePrimitiveCompiledByDescription_erase :
    ¬ exists D : MachineDescription,
      TapeCodePrimitiveCompiledByDescription
        MachineDescription.TapeCodePrimitive.erase D := by
  intro h
  rcases h with ⟨D, hD⟩
  have herase :
      D.HaltsWithExactOutput
        (MachineDescription.encodeCodeWordAsInput
          [MachineCodeSymbol.header])
        (MachineDescription.encodeCodeWordAsInput []) := by
    exact (hD.right [MachineCodeSymbol.header] []).mpr rfl
  have hctx :
      0 <
        Tape.contextLength
          (Tape.input
            (MachineDescription.encodeCodeWordAsInput
              [MachineCodeSymbol.header])) := by
    simp [MachineDescription.encodeCodeWordAsInput,
      MachineDescription.encodeCodeSymbolAsInput, Tape.input,
      Tape.contextLength]
  simpa [MachineDescription.encodeCodeWordAsInput] using
    MachineDescription.not_haltsWithExactOutput_empty_of_input_contextLength_pos
      (D := D)
      (w := MachineDescription.encodeCodeWordAsInput
        [MachineCodeSymbol.header])
      hctx herase

structure MachineDescriptionPrimitiveCompilerCore where
  identityCompiled :
    TapeCodePrimitiveCompiledByDescription
      MachineDescription.TapeCodePrimitive.identity
      MachineDescription.ExactIdentityDescription
  identityOutputRealized :
    TapeCodePrimitiveOutputRealizedByDescription
      MachineDescription.TapeCodePrimitive.identity
      MachineDescription.ExactIdentityDescription
  identityOutputCompiled :
    TapeCodePrimitiveOutputCompiledByDescription
      MachineDescription.TapeCodePrimitive.identity
      MachineDescription.ExactIdentityDescription
  identityOutputCompiledSubroutine :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      MachineDescription.TapeCodePrimitive.identity
      MachineDescription.ExactIdentityDescription
  eraseOutputRealized :
    TapeCodePrimitiveOutputRealizedByDescription
      MachineDescription.TapeCodePrimitive.erase
      MachineDescription.EraseRightDescription
  eraseOutputCompiled :
    TapeCodePrimitiveOutputCompiledByDescription
      MachineDescription.TapeCodePrimitive.erase
      MachineDescription.EraseRightDescription
  eraseOutputCompiledSubroutine :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      MachineDescription.TapeCodePrimitive.erase
      MachineDescription.EraseRightDescription
  eraseNotExactlyCompiled :
    ¬ exists D : MachineDescription,
      TapeCodePrimitiveCompiledByDescription
        MachineDescription.TapeCodePrimitive.erase D
  appendSingletonOutputRealized :
    forall symbol : MachineCodeSymbol,
      TapeCodePrimitiveOutputRealizedByDescription
        (MachineDescription.TapeCodePrimitive.append [symbol])
        (MachineDescription.AppendCodeSymbolRightDescription symbol)
  appendSingletonOutputCompiled :
    forall symbol : MachineCodeSymbol,
      TapeCodePrimitiveOutputCompiledByDescription
        (MachineDescription.TapeCodePrimitive.append [symbol])
        (MachineDescription.AppendCodeSymbolRightDescription symbol)
  appendSingletonOutputCompiledSubroutine :
    forall symbol : MachineCodeSymbol,
      TapeCodePrimitiveOutputCompiledSubroutineByDescription
        (MachineDescription.TapeCodePrimitive.append [symbol])
        (MachineDescription.AppendCodeSymbolRightDescription symbol)
  controllerRawOutputOutputRealized :
    TapeCodePrimitiveOutputRealizedByDescription
      PairedRecognizerDovetailControllerRawOutputCode
      MachineDescription.ExactIdentityDescription

def machineDescriptionPrimitiveCompilerCore :
    MachineDescriptionPrimitiveCompilerCore where
  identityCompiled := tapeCodePrimitiveCompiledByDescription_identity
  identityOutputRealized :=
    tapeCodePrimitiveOutputRealizedByDescription_identity
  identityOutputCompiled :=
    tapeCodePrimitiveOutputCompiledByDescription_identity
  identityOutputCompiledSubroutine :=
    tapeCodePrimitiveOutputCompiledSubroutineByDescription_identity
  eraseOutputRealized :=
    tapeCodePrimitiveOutputRealizedByDescription_erase
  eraseOutputCompiled :=
    tapeCodePrimitiveOutputCompiledByDescription_erase
  eraseOutputCompiledSubroutine :=
    tapeCodePrimitiveOutputCompiledSubroutineByDescription_erase
  eraseNotExactlyCompiled :=
    not_tapeCodePrimitiveCompiledByDescription_erase
  appendSingletonOutputRealized :=
    tapeCodePrimitiveOutputRealizedByDescription_append_singleton
  appendSingletonOutputCompiled :=
    tapeCodePrimitiveOutputCompiledByDescription_append_singleton
  appendSingletonOutputCompiledSubroutine :=
    tapeCodePrimitiveOutputCompiledSubroutineByDescription_append_singleton
  controllerRawOutputOutputRealized :=
    pairedRecognizerDovetailControllerRawOutputCodeOutputRealizedByDescription

structure MachineDescriptionPrimitiveSubroutineCore where
  identityReady :
    MachineDescription.SubroutineReady
      MachineDescription.ExactIdentityDescription
  eraseReady :
    MachineDescription.SubroutineReady
      MachineDescription.EraseRightDescription
  boolOutputReady :
    forall b : Bool,
      MachineDescription.SubroutineReady
        (MachineDescription.BoolOutputDescription b)
  boolOutputOnly :
    forall b : Bool,
      forall w out : Word Bool,
        (MachineDescription.BoolOutputDescription b).HaltsWithOutput w out <->
          out = [b]
  appendSingletonReady :
    forall symbol : MachineCodeSymbol,
      MachineDescription.SubroutineReady
        (MachineDescription.AppendCodeSymbolRightDescription symbol)

def machineDescriptionPrimitiveSubroutineCore :
    MachineDescriptionPrimitiveSubroutineCore where
  identityReady :=
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩
  eraseReady :=
    ⟨MachineDescription.eraseRightDescription_wellFormed,
      MachineDescription.eraseRightDescription_haltTransitionFree⟩
  boolOutputReady := by
    intro b
    exact
      ⟨MachineDescription.boolOutputDescription_wellFormed b,
        MachineDescription.boolOutputDescription_haltTransitionFree b⟩
  boolOutputOnly :=
    MachineDescription.boolOutputDescription_haltsWithOutput_iff
  appendSingletonReady := by
    intro symbol
    exact
      ⟨MachineDescription.appendCodeSymbolRightDescription_wellFormed symbol,
        MachineDescription.appendCodeSymbolRightDescription_haltTransitionFree
          symbol⟩

end Computability
end FoC
