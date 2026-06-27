import FoC.Computability.Compiler.Core.DovetailCode

set_option doc.verso true

/-!
# Tape-code primitive compiler interfaces
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

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
    (P : TapeCodePrimitive)
    (D : MachineDescription) : Prop :=
  D.WellFormed ∧
    forall code out : Word MachineCodeSymbol,
      D.HaltsWithExactOutput
        (encodeCodeWordAsInput code)
        (encodeCodeWordAsInput out) <->
          P.transform code = some out

def TapeCodePrimitiveOutputRealizedByDescription
    (P : TapeCodePrimitive)
    (D : MachineDescription) : Prop :=
  D.WellFormed ∧
    forall code out : Word MachineCodeSymbol,
      P.transform code = some out ->
        D.HaltsWithOutput
          (encodeCodeWordAsInput code)
          (encodeCodeWordAsInput out)

def TapeCodePrimitiveOutputCompiledByDescription
    (P : TapeCodePrimitive)
    (D : MachineDescription) : Prop :=
  D.WellFormed ∧
    forall code out : Word MachineCodeSymbol,
      D.HaltsWithOutput
        (encodeCodeWordAsInput code)
        (encodeCodeWordAsInput out) <->
          P.transform code = some out

def TapeCodePrimitiveOutputSubroutineRealizedByDescription
    (P : TapeCodePrimitive)
    (D : MachineDescription) : Prop :=
  TapeCodePrimitiveOutputRealizedByDescription P D ∧
    D.HaltTransitionFree

def TapeCodePrimitiveOutputCompiledSubroutineByDescription
    (P : TapeCodePrimitive)
    (D : MachineDescription) : Prop :=
  TapeCodePrimitiveOutputCompiledByDescription P D ∧
    D.HaltTransitionFree

def TapeCodePrimitiveHandoffSubroutineRealizedByDescription
    (P : TapeCodePrimitive)
    (D : MachineDescription) (handoffMove : Direction) : Prop :=
  TapeCodePrimitiveOutputSubroutineRealizedByDescription P D ∧
    forall code out : Word MachineCodeSymbol,
      P.transform code = some out ->
        exists T : Tape Bool,
          D.HaltsWithTape
            (encodeCodeWordAsInput code) T ∧
          Tape.move handoffMove T =
            Tape.input (encodeCodeWordAsInput out)

def TapeCodePrimitiveHandoffCompiledSubroutineByDescription
    (P : TapeCodePrimitive)
    (D : MachineDescription) (handoffMove : Direction) : Prop :=
  TapeCodePrimitiveOutputCompiledSubroutineByDescription P D ∧
    forall code out : Word MachineCodeSymbol,
      P.transform code = some out ->
        exists T : Tape Bool,
          D.HaltsWithTape
            (encodeCodeWordAsInput code) T ∧
          Tape.move handoffMove T =
            Tape.input (encodeCodeWordAsInput out)

def TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
    (P : TapeCodePrimitive)
    (D : MachineDescription) (handoffMove : Direction) : Prop :=
  TapeCodePrimitiveOutputCompiledSubroutineByDescription P D ∧
    forall code : Word MachineCodeSymbol,
    forall T : Tape Bool,
      D.HaltsWithTape
        (encodeCodeWordAsInput code) T ->
        exists out : Word MachineCodeSymbol,
          P.transform code = some out ∧
            Tape.normalizedOutput T =
              encodeCodeWordAsInput out ∧
            Tape.move handoffMove T =
              Tape.input (encodeCodeWordAsInput out)

theorem not_tapeCodePrimitiveHandoffCompiledSubroutineByDescription_right_of_transform_eq_some
    {P : TapeCodePrimitive} {D : MachineDescription}
    {code out : Word MachineCodeSymbol}
    (hp : P.transform code = some out) :
    ¬ TapeCodePrimitiveHandoffCompiledSubroutineByDescription
        P D Direction.right := by
  intro hD
  rcases hD.right code out hp with ⟨T, _hhalt, hmove⟩
  exact tape_move_right_ne_input T
    (encodeCodeWordAsInput out) hmove

theorem not_tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_right_of_transform_eq_some
    {P : TapeCodePrimitive} {D : MachineDescription}
    {code out : Word MachineCodeSymbol}
    (hp : P.transform code = some out) :
    ¬ TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        P D Direction.right := by
  intro hD
  have hOut :
      D.HaltsWithOutput
        (encodeCodeWordAsInput code)
        (encodeCodeWordAsInput out) :=
    (hD.left.left.right code out).mpr hp
  rcases hOut with ⟨n, hn⟩
  let T : Tape Bool :=
    (D.runConfig n
      (D.initial (encodeCodeWordAsInput code))).tape
  have hTape :
      D.HaltsWithTape
        (encodeCodeWordAsInput code) T := by
    refine ⟨n, ?_⟩
    exact ⟨hn.left, rfl⟩
  rcases hD.right code T hTape with ⟨out', _hp', _hnorm, hmove⟩
  exact tape_move_right_ne_input T
    (encodeCodeWordAsInput out') hmove

theorem tapeCodePrimitiveOutputCompiledByDescription_wellFormed
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledByDescription P D) :
    D.WellFormed :=
  h.left

theorem tapeCodePrimitiveOutputCompiledByDescription_haltsWithOutput_iff
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledByDescription P D)
    (code out : Word MachineCodeSymbol) :
    D.HaltsWithOutput
        (encodeCodeWordAsInput code)
        (encodeCodeWordAsInput out) <->
      P.transform code = some out :=
  h.right code out

theorem tapeCodePrimitiveOutputCompiledByDescription_haltsWithOutput_of_transform_eq_some
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledByDescription P D)
    {code out : Word MachineCodeSymbol}
    (hp : P.transform code = some out) :
    D.HaltsWithOutput
      (encodeCodeWordAsInput code)
      (encodeCodeWordAsInput out) :=
  (h.right code out).mpr hp

theorem tapeCodePrimitiveOutputCompiledByDescription_transform_eq_some_of_haltsWithOutput
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledByDescription P D)
    {code out : Word MachineCodeSymbol}
    (hD :
      D.HaltsWithOutput
        (encodeCodeWordAsInput code)
        (encodeCodeWordAsInput out)) :
    P.transform code = some out :=
  (h.right code out).mp hD

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_wellFormed
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledSubroutineByDescription P D) :
    D.WellFormed :=
  h.left.left

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_haltTransitionFree
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledSubroutineByDescription P D) :
    D.HaltTransitionFree :=
  h.right

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_haltsWithOutput_iff
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledSubroutineByDescription P D)
    (code out : Word MachineCodeSymbol) :
    D.HaltsWithOutput
        (encodeCodeWordAsInput code)
        (encodeCodeWordAsInput out) <->
      P.transform code = some out :=
  h.left.right code out

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_haltsWithOutput_of_transform_eq_some
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledSubroutineByDescription P D)
    {code out : Word MachineCodeSymbol}
    (hp : P.transform code = some out) :
    D.HaltsWithOutput
      (encodeCodeWordAsInput code)
      (encodeCodeWordAsInput out) :=
  (h.left.right code out).mpr hp

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_transform_eq_some_of_haltsWithOutput
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledSubroutineByDescription P D)
    {code out : Word MachineCodeSymbol}
    (hD :
      D.HaltsWithOutput
        (encodeCodeWordAsInput code)
        (encodeCodeWordAsInput out)) :
    P.transform code = some out :=
  (h.left.right code out).mp hD

theorem tapeCodePrimitiveHandoffSubroutineRealizedByDescription_outputRealized
    {P : TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveHandoffSubroutineRealizedByDescription
      P D handoffMove) :
    TapeCodePrimitiveOutputSubroutineRealizedByDescription P D :=
  h.left

theorem tapeCodePrimitiveHandoffSubroutineRealizedByDescription_haltTransitionFree
    {P : TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveHandoffSubroutineRealizedByDescription
      P D handoffMove) :
    D.HaltTransitionFree :=
  h.left.right

theorem tapeCodePrimitiveHandoffSubroutineRealizedByDescription_subroutineReady
    {P : TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveHandoffSubroutineRealizedByDescription
      P D handoffMove) :
    D.SubroutineReady :=
  ⟨h.left.left.left, h.left.right⟩

theorem tapeCodePrimitiveHandoffSubroutineRealizedByDescription_haltsWithOutput_of_transform_eq_some
    {P : TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveHandoffSubroutineRealizedByDescription
      P D handoffMove)
    {code out : Word MachineCodeSymbol}
    (hp : P.transform code = some out) :
    D.HaltsWithOutput
      (encodeCodeWordAsInput code)
      (encodeCodeWordAsInput out) :=
  h.left.left.right code out hp

theorem tapeCodePrimitiveHandoffSubroutineRealizedByDescription_haltsWithTape_of_transform_eq_some
    {P : TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveHandoffSubroutineRealizedByDescription
      P D handoffMove)
    {code out : Word MachineCodeSymbol}
    (hp : P.transform code = some out) :
    exists T : Tape Bool,
      D.HaltsWithTape
        (encodeCodeWordAsInput code) T ∧
      Tape.move handoffMove T =
        Tape.input (encodeCodeWordAsInput out) :=
  h.right code out hp

theorem tapeCodePrimitiveHandoffCompiledSubroutineByDescription_outputCompiled
    {P : TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveHandoffCompiledSubroutineByDescription
      P D handoffMove) :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription P D :=
  h.left

theorem tapeCodePrimitiveHandoffCompiledSubroutineByDescription_subroutineReady
    {P : TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveHandoffCompiledSubroutineByDescription
      P D handoffMove) :
    D.SubroutineReady :=
  ⟨h.left.left.left, h.left.right⟩

theorem tapeCodePrimitiveHandoffCompiledSubroutineByDescription_haltsWithOutput_of_transform_eq_some
    {P : TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveHandoffCompiledSubroutineByDescription
      P D handoffMove)
    {code out : Word MachineCodeSymbol}
    (hp : P.transform code = some out) :
    D.HaltsWithOutput
      (encodeCodeWordAsInput code)
      (encodeCodeWordAsInput out) :=
  tapeCodePrimitiveOutputCompiledSubroutineByDescription_haltsWithOutput_of_transform_eq_some
    h.left hp

theorem tapeCodePrimitiveHandoffCompiledSubroutineByDescription_haltsWithTape_of_transform_eq_some
    {P : TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveHandoffCompiledSubroutineByDescription
      P D handoffMove)
    {code out : Word MachineCodeSymbol}
    (hp : P.transform code = some out) :
    exists T : Tape Bool,
      D.HaltsWithTape
        (encodeCodeWordAsInput code) T ∧
      Tape.move handoffMove T =
        Tape.input (encodeCodeWordAsInput out) :=
  h.right code out hp

theorem tapeCodePrimitiveHandoffSubroutineRealizedByDescription_of_handoffCompiled
    {P : TapeCodePrimitive}
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
    {P : TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      P D handoffMove) :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription P D :=
  h.left

theorem tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_haltsWithTape_output
    {P : TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      P D handoffMove)
    {code : Word MachineCodeSymbol} {T : Tape Bool}
    (hhalt :
      D.HaltsWithTape
        (encodeCodeWordAsInput code) T) :
    exists out : Word MachineCodeSymbol,
      P.transform code = some out ∧
        Tape.normalizedOutput T =
          encodeCodeWordAsInput out ∧
        Tape.move handoffMove T =
          Tape.input (encodeCodeWordAsInput out) :=
  h.right code T hhalt

/-!
Short closed-handoff aliases.  The full theorem names above remain the stable
descriptive API, while these aliases make proof scripts that repeatedly peel a
closed handoff contract easier to read.
-/

theorem closedHandoffCompiled_haltsWithTape_inv
    {P : TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      P D handoffMove)
    {code : Word MachineCodeSymbol} {T : Tape Bool}
    (hhalt :
      D.HaltsWithTape
        (encodeCodeWordAsInput code) T) :
    exists out : Word MachineCodeSymbol,
      P.transform code = some out ∧
        Tape.normalizedOutput T =
          encodeCodeWordAsInput out ∧
        Tape.move handoffMove T =
          Tape.input (encodeCodeWordAsInput out) :=
  tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_haltsWithTape_output
    h hhalt

theorem tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffCompiled
    {P : TapeCodePrimitive}
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
        (D.initial (encodeCodeWordAsInput code))).tape
    have hTape :
        D.HaltsWithTape
          (encodeCodeWordAsInput code) T := by
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
    {P : TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      P D handoffMove) :
    TapeCodePrimitiveHandoffSubroutineRealizedByDescription
      P D handoffMove :=
  tapeCodePrimitiveHandoffSubroutineRealizedByDescription_of_handoffCompiled
    (tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffCompiled
      h)

theorem closedHandoffCompiled_outputCompiled
    {P : TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      P D handoffMove) :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription P D :=
  tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_outputCompiled
    h

theorem closedHandoffCompiled_handoffCompiled
    {P : TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      P D handoffMove) :
    TapeCodePrimitiveHandoffCompiledSubroutineByDescription
      P D handoffMove :=
  tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffCompiled
    h

theorem closedHandoffCompiled_handoffRealized
    {P : TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      P D handoffMove) :
    TapeCodePrimitiveHandoffSubroutineRealizedByDescription
      P D handoffMove :=
  tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffRealized
    h

theorem haltsWithEncodedCodeOutput_functional_of_haltTransitionFree
    {D : MachineDescription}
    {w : Word Bool}
    {out₁ out₂ : Word MachineCodeSymbol}
    (hD : D.HaltTransitionFree)
    (h₁ :
      D.HaltsWithOutput w
        (encodeCodeWordAsInput out₁))
    (h₂ :
      D.HaltsWithOutput w
        (encodeCodeWordAsInput out₂)) :
    out₁ = out₂ :=
  encodeCodeWordAsInput_injective
    (haltsWithOutput_functional_of_haltTransitionFree
      hD h₁ h₂)

theorem tapeCodePrimitiveOutputSubroutineRealizedByDescription_output_eq_of_haltsWithOutput
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputSubroutineRealizedByDescription P D)
    {code expected actual : Word MachineCodeSymbol}
    (hp : P.transform code = some expected)
    (hD :
      D.HaltsWithOutput
        (encodeCodeWordAsInput code)
        (encodeCodeWordAsInput actual)) :
    expected = actual :=
  haltsWithEncodedCodeOutput_functional_of_haltTransitionFree h.right
    (h.left.right code expected hp) hD

theorem tapeCodePrimitiveOutputSubroutineRealizedByDescription_congr
    {P Q : TapeCodePrimitive}
    {D : MachineDescription}
    (hPQ : forall code : Word MachineCodeSymbol,
      P.transform code = Q.transform code)
    (hD : TapeCodePrimitiveOutputSubroutineRealizedByDescription P D) :
    TapeCodePrimitiveOutputSubroutineRealizedByDescription Q D :=
  ⟨⟨hD.left.left, fun code out hQ =>
      hD.left.right code out (by simpa [hPQ code] using hQ)⟩,
    hD.right⟩

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_congr
    {P Q : TapeCodePrimitive}
    {D : MachineDescription}
    (hPQ : forall code : Word MachineCodeSymbol,
      P.transform code = Q.transform code)
    (hD : TapeCodePrimitiveOutputCompiledSubroutineByDescription P D) :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription Q D :=
  ⟨⟨hD.left.left, fun code out =>
      by simpa [hPQ code] using hD.left.right code out⟩,
    hD.right⟩

theorem tapeCodePrimitiveHandoffCompiledSubroutineByDescription_congr
    {P Q : TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (hPQ : forall code : Word MachineCodeSymbol,
      P.transform code = Q.transform code)
    (hD : TapeCodePrimitiveHandoffCompiledSubroutineByDescription
      P D handoffMove) :
    TapeCodePrimitiveHandoffCompiledSubroutineByDescription
      Q D handoffMove :=
  ⟨tapeCodePrimitiveOutputCompiledSubroutineByDescription_congr hPQ hD.left,
    fun code out hQ => by
    have hP : P.transform code = some out := by
      simpa [hPQ code] using hQ
    exact hD.right code out hP⟩

theorem tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_congr
    {P Q : TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (hPQ : forall code : Word MachineCodeSymbol,
      P.transform code = Q.transform code)
    (hD : TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      P D handoffMove) :
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      Q D handoffMove :=
  ⟨tapeCodePrimitiveOutputCompiledSubroutineByDescription_congr hPQ hD.left,
    fun code T hhalt => by
    rcases hD.right code T hhalt with ⟨out, hP, hnorm, hmove⟩
    exact ⟨out, by simpa [← hPQ code] using hP, hnorm, hmove⟩⟩

theorem tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_subroutineReady
    {P : TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      P D handoffMove) :
    D.SubroutineReady :=
  ⟨h.left.left.left, h.left.right⟩

theorem tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_haltsWithOutput_iff
    {P : TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (h : TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      P D handoffMove)
    (code out : Word MachineCodeSymbol) :
    D.HaltsWithOutput
        (encodeCodeWordAsInput code)
        (encodeCodeWordAsInput out) <->
      P.transform code = some out :=
  h.left.left.right code out

theorem tapeCodePrimitiveHandoffSubroutineRealizedByDescription_congr
    {P Q : TapeCodePrimitive}
    {D : MachineDescription} {handoffMove : Direction}
    (hPQ : forall code : Word MachineCodeSymbol,
      P.transform code = Q.transform code)
    (hD : TapeCodePrimitiveHandoffSubroutineRealizedByDescription
      P D handoffMove) :
    TapeCodePrimitiveHandoffSubroutineRealizedByDescription
      Q D handoffMove :=
  ⟨⟨⟨hD.left.left.left, fun code out hQ =>
        hD.left.left.right code out (by simpa [hPQ code] using hQ)⟩,
      hD.left.right⟩,
    fun code out hQ =>
      hD.right code out (by simpa [hPQ code] using hQ)⟩

theorem tapeCodePrimitiveOutputRealizedByDescription_of_outputCompiled
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledByDescription P D) :
    TapeCodePrimitiveOutputRealizedByDescription P D :=
  ⟨h.left, fun code out hp => (h.right code out).mpr hp⟩

theorem tapeCodePrimitiveOutputSubroutineRealizedByDescription_of_outputCompiled
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledSubroutineByDescription P D) :
    TapeCodePrimitiveOutputSubroutineRealizedByDescription P D :=
  ⟨tapeCodePrimitiveOutputRealizedByDescription_of_outputCompiled h.left,
    h.right⟩

theorem tapeCodePrimitiveOutputRealizedByDescription_of_exact
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveCompiledByDescription P D) :
    TapeCodePrimitiveOutputRealizedByDescription P D :=
  ⟨h.left, fun code out hp =>
    haltsWithOutput_of_haltsWithExactOutput
      ((h.right code out).mpr hp)⟩

theorem tapeCodePrimitiveOutputRealizedByDescription_of_subroutine
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputSubroutineRealizedByDescription P D) :
    TapeCodePrimitiveOutputRealizedByDescription P D :=
  h.left

theorem tapeCodePrimitiveOutputSubroutineRealizedByDescription_subroutineReady
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputSubroutineRealizedByDescription P D) :
    D.SubroutineReady :=
  ⟨h.left.left, h.right⟩

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_subroutineReady
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledSubroutineByDescription P D) :
    D.SubroutineReady :=
  ⟨h.left.left, h.right⟩

theorem tapeCodePrimitiveCompiledByDescription_identity :
    TapeCodePrimitiveCompiledByDescription
      TapeCodePrimitive.identity
      ExactIdentityDescription := by
  constructor
  · exact exactIdentityDescription_wellFormed
  · intro code out
    constructor
    · intro h
      have hbool :
          encodeCodeWordAsInput out =
            encodeCodeWordAsInput code :=
        (exactIdentityDescription_haltsWithExactOutput_iff
          (encodeCodeWordAsInput code)
          (encodeCodeWordAsInput out)).mp h
      have hout : out = code :=
        encodeCodeWordAsInput_injective hbool
      simp [TapeCodePrimitive.identity, hout]
    · intro h
      simp [TapeCodePrimitive.identity] at h
      rw [← h]
      exact
        (exactIdentityDescription_haltsWithExactOutput_iff
          (encodeCodeWordAsInput code)
          (encodeCodeWordAsInput code)).mpr rfl

theorem tapeCodePrimitiveOutputRealizedByDescription_identity :
    TapeCodePrimitiveOutputRealizedByDescription
      TapeCodePrimitive.identity
      ExactIdentityDescription :=
  tapeCodePrimitiveOutputRealizedByDescription_of_exact
    tapeCodePrimitiveCompiledByDescription_identity

theorem tapeCodePrimitiveOutputCompiledByDescription_identity :
    TapeCodePrimitiveOutputCompiledByDescription
      TapeCodePrimitive.identity
      ExactIdentityDescription := by
  constructor
  · exact exactIdentityDescription_wellFormed
  · intro code out
    constructor
    · intro h
      have hbool :
          encodeCodeWordAsInput out =
            encodeCodeWordAsInput code :=
        (exactIdentityDescription_haltsWithOutput_iff
          (encodeCodeWordAsInput code)
          (encodeCodeWordAsInput out)).mp h
      have hout : out = code :=
        encodeCodeWordAsInput_injective hbool
      simp [TapeCodePrimitive.identity, hout]
    · intro h
      simp [TapeCodePrimitive.identity] at h
      rw [← h]
      exact (exactIdentityDescription_haltsWithOutput_iff
        (encodeCodeWordAsInput code)
        (encodeCodeWordAsInput code)).mpr rfl

theorem tapeCodePrimitiveOutputSubroutineRealizedByDescription_identity :
    TapeCodePrimitiveOutputSubroutineRealizedByDescription
      TapeCodePrimitive.identity
      ExactIdentityDescription :=
  ⟨tapeCodePrimitiveOutputRealizedByDescription_identity,
    exactIdentityDescription_haltTransitionFree⟩

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_identity :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      TapeCodePrimitive.identity
      ExactIdentityDescription :=
  ⟨tapeCodePrimitiveOutputCompiledByDescription_identity,
    exactIdentityDescription_haltTransitionFree⟩

theorem pairedRecognizerDovetailControllerRawOutputCodeOutputRealizedByDescription :
    TapeCodePrimitiveOutputRealizedByDescription
      PairedRecognizerDovetailControllerRawOutputCode
      ExactIdentityDescription := by
  constructor
  · exact exactIdentityDescription_wellFormed
  · intro code out h
    have hout : out = code :=
      pairedRecognizerDovetailControllerRawOutputCode_eq_some_self h
    rw [hout]
    exact
      (exactIdentityDescription_haltsWithOutput_iff
        (encodeCodeWordAsInput code)
        (encodeCodeWordAsInput code)).mpr rfl

theorem tapeCodePrimitiveOutputRealizedByDescription_erase :
    TapeCodePrimitiveOutputRealizedByDescription
      TapeCodePrimitive.erase
      EraseRightDescription := by
  constructor
  · exact eraseRightDescription_wellFormed
  · intro code out h
    simp [TapeCodePrimitive.erase] at h
    rw [← h]
    exact eraseRightDescription_haltsWithOutput_empty
      (encodeCodeWordAsInput code)

theorem tapeCodePrimitiveOutputCompiledByDescription_erase :
    TapeCodePrimitiveOutputCompiledByDescription
      TapeCodePrimitive.erase
      EraseRightDescription := by
  constructor
  · exact eraseRightDescription_wellFormed
  · intro code out
    constructor
    · intro h
      have hnil :
          EraseRightDescription.HaltsWithOutput
            (encodeCodeWordAsInput code)
            (encodeCodeWordAsInput
              ([] : Word MachineCodeSymbol)) := by
        simpa [encodeCodeWordAsInput] using
          eraseRightDescription_haltsWithOutput_empty
            (encodeCodeWordAsInput code)
      have hbool :
          encodeCodeWordAsInput out =
            encodeCodeWordAsInput
              ([] : Word MachineCodeSymbol) :=
        haltsWithOutput_functional_of_haltTransitionFree
          eraseRightDescription_haltTransitionFree h hnil
      have hout : out = [] :=
        encodeCodeWordAsInput_injective hbool
      simp [TapeCodePrimitive.erase, hout]
    · intro h
      exact (tapeCodePrimitiveOutputRealizedByDescription_erase.right
        code out) h

theorem tapeCodePrimitiveOutputSubroutineRealizedByDescription_erase :
    TapeCodePrimitiveOutputSubroutineRealizedByDescription
      TapeCodePrimitive.erase
      EraseRightDescription :=
  ⟨tapeCodePrimitiveOutputRealizedByDescription_erase,
    eraseRightDescription_haltTransitionFree⟩

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_erase :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      TapeCodePrimitive.erase
      EraseRightDescription :=
  ⟨tapeCodePrimitiveOutputCompiledByDescription_erase,
    eraseRightDescription_haltTransitionFree⟩

theorem tapeCodePrimitiveOutputRealizedByDescription_append_singleton
    (symbol : MachineCodeSymbol) :
    TapeCodePrimitiveOutputRealizedByDescription
      (TapeCodePrimitive.append [symbol])
      (AppendCodeSymbolRightDescription symbol) := by
  constructor
  · exact appendCodeSymbolRightDescription_wellFormed
      symbol
  · intro code out h
    simp [TapeCodePrimitive.append] at h
    rw [← h]
    have hencoded :
        encodeCodeWordAsInput
            (List.append code [symbol]) =
          List.append (encodeCodeWordAsInput code)
            (encodeCodeSymbolAsInput symbol) := by
      rw [encodeCodeWordAsInput_append,
        encodeCodeWordAsInput_singleton]
    change
      (AppendCodeSymbolRightDescription symbol).HaltsWithOutput
        (encodeCodeWordAsInput code)
        (encodeCodeWordAsInput
          (List.append code [symbol]))
    rw [hencoded]
    exact
      appendCodeSymbolRightDescription_haltsWithOutput_append
        symbol (encodeCodeWordAsInput code)

theorem tapeCodePrimitiveOutputCompiledByDescription_append_singleton
    (symbol : MachineCodeSymbol) :
    TapeCodePrimitiveOutputCompiledByDescription
      (TapeCodePrimitive.append [symbol])
      (AppendCodeSymbolRightDescription symbol) := by
  constructor
  · exact appendCodeSymbolRightDescription_wellFormed
      symbol
  · intro code out
    constructor
    · intro h
      have hencoded :
          encodeCodeWordAsInput
              (List.append code [symbol]) =
            List.append (encodeCodeWordAsInput code)
              (encodeCodeSymbolAsInput symbol) := by
        rw [encodeCodeWordAsInput_append,
          encodeCodeWordAsInput_singleton]
      have htarget :
          (AppendCodeSymbolRightDescription
            symbol).HaltsWithOutput
            (encodeCodeWordAsInput code)
            (encodeCodeWordAsInput
              (List.append code [symbol])) := by
        rw [hencoded]
        exact
          appendCodeSymbolRightDescription_haltsWithOutput_append
            symbol (encodeCodeWordAsInput code)
      have hbool :
          encodeCodeWordAsInput out =
            encodeCodeWordAsInput
              (List.append code [symbol]) :=
        haltsWithOutput_functional_of_haltTransitionFree
          (appendCodeSymbolRightDescription_haltTransitionFree
            symbol) h htarget
      have hout : out = List.append code [symbol] :=
        encodeCodeWordAsInput_injective hbool
      simp [TapeCodePrimitive.append, hout]
    · intro h
      exact
        (tapeCodePrimitiveOutputRealizedByDescription_append_singleton
          symbol).right code out h

theorem tapeCodePrimitiveOutputSubroutineRealizedByDescription_append_singleton
    (symbol : MachineCodeSymbol) :
    TapeCodePrimitiveOutputSubroutineRealizedByDescription
      (TapeCodePrimitive.append [symbol])
      (AppendCodeSymbolRightDescription symbol) :=
  ⟨tapeCodePrimitiveOutputRealizedByDescription_append_singleton symbol,
    appendCodeSymbolRightDescription_haltTransitionFree
      symbol⟩

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_append_singleton
    (symbol : MachineCodeSymbol) :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      (TapeCodePrimitive.append [symbol])
      (AppendCodeSymbolRightDescription symbol) :=
  ⟨tapeCodePrimitiveOutputCompiledByDescription_append_singleton symbol,
    appendCodeSymbolRightDescription_haltTransitionFree
      symbol⟩

theorem not_tapeCodePrimitiveCompiledByDescription_erase :
    ¬ exists D : MachineDescription,
      TapeCodePrimitiveCompiledByDescription
        TapeCodePrimitive.erase D := by
  intro h
  rcases h with ⟨D, hD⟩
  have herase :
      D.HaltsWithExactOutput
        (encodeCodeWordAsInput
          [MachineCodeSymbol.header])
        (encodeCodeWordAsInput []) := by
    exact (hD.right [MachineCodeSymbol.header] []).mpr rfl
  have hctx :
      0 <
        Tape.contextLength
          (Tape.input
            (encodeCodeWordAsInput
              [MachineCodeSymbol.header])) := by
    simp [encodeCodeWordAsInput,
      encodeCodeSymbolAsInput, Tape.input,
      Tape.contextLength]
  simpa [encodeCodeWordAsInput] using
    not_haltsWithExactOutput_empty_of_input_contextLength_pos
      (D := D)
      (w := encodeCodeWordAsInput
        [MachineCodeSymbol.header])
      hctx herase

structure MachineDescriptionPrimitiveCompilerCore where
  identityCompiled :
    TapeCodePrimitiveCompiledByDescription
      TapeCodePrimitive.identity
      ExactIdentityDescription
  identityOutputRealized :
    TapeCodePrimitiveOutputRealizedByDescription
      TapeCodePrimitive.identity
      ExactIdentityDescription
  identityOutputCompiled :
    TapeCodePrimitiveOutputCompiledByDescription
      TapeCodePrimitive.identity
      ExactIdentityDescription
  identityOutputCompiledSubroutine :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      TapeCodePrimitive.identity
      ExactIdentityDescription
  eraseOutputRealized :
    TapeCodePrimitiveOutputRealizedByDescription
      TapeCodePrimitive.erase
      EraseRightDescription
  eraseOutputCompiled :
    TapeCodePrimitiveOutputCompiledByDescription
      TapeCodePrimitive.erase
      EraseRightDescription
  eraseOutputCompiledSubroutine :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      TapeCodePrimitive.erase
      EraseRightDescription
  eraseNotExactlyCompiled :
    ¬ exists D : MachineDescription,
      TapeCodePrimitiveCompiledByDescription
        TapeCodePrimitive.erase D
  appendSingletonOutputRealized :
    forall symbol : MachineCodeSymbol,
      TapeCodePrimitiveOutputRealizedByDescription
        (TapeCodePrimitive.append [symbol])
        (AppendCodeSymbolRightDescription symbol)
  appendSingletonOutputCompiled :
    forall symbol : MachineCodeSymbol,
      TapeCodePrimitiveOutputCompiledByDescription
        (TapeCodePrimitive.append [symbol])
        (AppendCodeSymbolRightDescription symbol)
  appendSingletonOutputCompiledSubroutine :
    forall symbol : MachineCodeSymbol,
      TapeCodePrimitiveOutputCompiledSubroutineByDescription
        (TapeCodePrimitive.append [symbol])
        (AppendCodeSymbolRightDescription symbol)
  controllerRawOutputOutputRealized :
    TapeCodePrimitiveOutputRealizedByDescription
      PairedRecognizerDovetailControllerRawOutputCode
      ExactIdentityDescription

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
    SubroutineReady
      ExactIdentityDescription
  eraseReady :
    SubroutineReady
      EraseRightDescription
  boolOutputReady :
    forall b : Bool,
      SubroutineReady
        (BoolOutputDescription b)
  boolOutputOnly :
    forall b : Bool,
      forall w out : Word Bool,
        (BoolOutputDescription b).HaltsWithOutput w out <->
          out = [b]
  appendSingletonReady :
    forall symbol : MachineCodeSymbol,
      SubroutineReady
        (AppendCodeSymbolRightDescription symbol)

def machineDescriptionPrimitiveSubroutineCore :
    MachineDescriptionPrimitiveSubroutineCore where
  identityReady :=
    ⟨exactIdentityDescription_wellFormed,
      exactIdentityDescription_haltTransitionFree⟩
  eraseReady :=
    ⟨eraseRightDescription_wellFormed,
      eraseRightDescription_haltTransitionFree⟩
  boolOutputReady := by
    intro b
    exact
      ⟨boolOutputDescription_wellFormed b,
        boolOutputDescription_haltTransitionFree b⟩
  boolOutputOnly :=
    boolOutputDescription_haltsWithOutput_iff
  appendSingletonReady := by
    intro symbol
    exact
      ⟨appendCodeSymbolRightDescription_wellFormed symbol,
        appendCodeSymbolRightDescription_haltTransitionFree
          symbol⟩

end Computability
end FoC
