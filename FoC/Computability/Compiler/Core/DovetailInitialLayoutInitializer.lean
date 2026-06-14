import FoC.Computability.Compiler.Core.TapeCodePrimitives

set_option doc.verso true

/-!
# Dovetail initial-layout initializer

This module isolates the finite-source obligation for the
{name}`FoC.Computability.PairedRecognizerDovetailInitialLayoutCode`
initializer.  The exported
right-shifted-output contract is the natural machine-level target: the
initializer emits the canonical encoded dovetail layout and halts one cell to
the right, so the standard code-word handoff move restores the canonical input
tape for the next subroutine.
-/

namespace FoC
namespace Computability

open Languages

private theorem tape_normalizedOutput_move_right_input
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

private theorem tape_move_left_move_right_input_encodeCodeWordAsInput_cons
    (symbol : MachineCodeSymbol) (code : Word MachineCodeSymbol) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (Tape.input
            (MachineDescription.encodeCodeWordAsInput (symbol :: code)))) =
      Tape.input
        (MachineDescription.encodeCodeWordAsInput (symbol :: code)) := by
  cases symbol <;> rfl

private theorem tapeCodePrimitiveCodeWord_handoff_tape
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

private theorem encodeConfigurationAppend_initial
    (D : MachineDescription) (w : Word Bool)
    (suffix : Word MachineCodeSymbol) :
    MachineDescription.encodeConfigurationAppend (D.initial w) suffix =
      MachineDescription.encodeNatAppend D.start
        (MachineDescription.encodeTapeAppend (Tape.input w) suffix) := by
  rfl

private theorem dovetailInitialLayoutCode_output_eq_transition_cons
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    MachineDescription.DovetailLayout.encode
        (MachineDescription.DovetailLayout.initial
          accept reject w stage) =
      MachineCodeSymbol.transition ::
        MachineDescription.encodeBoolWordAppend w
          (MachineDescription.encodeNatAppend stage
            (MachineDescription.encodeConfigurationAppend
              (accept.initial w)
              (MachineDescription.encodeConfigurationAppend
                (reject.initial w)
                (MachineDescription.encodeBoolAppend false
                  (MachineDescription.encodeBoolAppend false []))))) := by
  rfl

theorem dovetailInitialLayoutCode_output_eq_expanded
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    MachineDescription.DovetailLayout.encode
        (MachineDescription.DovetailLayout.initial
          accept reject w stage) =
      MachineCodeSymbol.transition ::
        MachineDescription.encodeBoolWordAppend w
          (MachineDescription.encodeNatAppend stage
            (MachineDescription.encodeNatAppend accept.start
              (MachineDescription.encodeTapeAppend (Tape.input w)
                (MachineDescription.encodeNatAppend reject.start
                  (MachineDescription.encodeTapeAppend (Tape.input w)
                    (MachineDescription.encodeBoolAppend false
                      (MachineDescription.encodeBoolAppend false []))))))) := by
  rw [dovetailInitialLayoutCode_output_eq_transition_cons,
    encodeConfigurationAppend_initial,
    encodeConfigurationAppend_initial]

theorem pairedRecognizerDovetailInitialLayoutCode_transform_eq_some_cons
    {accept reject : MachineDescription}
    {code out : Word MachineCodeSymbol}
    (h :
      (PairedRecognizerDovetailInitialLayoutCode accept reject).transform
          code = some out) :
    exists tail : Word MachineCodeSymbol,
      out = MachineCodeSymbol.transition :: tail := by
  rcases
      (pairedRecognizerDovetailInitialLayoutCode_transform_eq_some_iff
        accept reject code out).mp h with
    ⟨w, stage, _hcode, hout⟩
  refine
    ⟨MachineDescription.encodeBoolWordAppend w
      (MachineDescription.encodeNatAppend stage
        (MachineDescription.encodeConfigurationAppend
          (accept.initial w)
          (MachineDescription.encodeConfigurationAppend
            (reject.initial w)
            (MachineDescription.encodeBoolAppend false
              (MachineDescription.encodeBoolAppend false []))))), ?_⟩
  rw [hout, dovetailInitialLayoutCode_output_eq_transition_cons]

private theorem tapeCodePrimitiveClosedHandoffCompiled_of_halt_tape_move_right
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

def TapeCodePrimitiveRightShiftedOutputCompiledSubroutineByDescription
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

def DovetailInitialLayoutInitializerOutputCode
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) : Word MachineCodeSymbol :=
  MachineDescription.DovetailLayout.encode
    (MachineDescription.DovetailLayout.initial accept reject w stage)

def DovetailInitialLayoutInitializerOutputTape
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) : Tape Bool :=
  Tape.move Direction.right
    (Tape.input
      (MachineDescription.encodeCodeWordAsInput
        (DovetailInitialLayoutInitializerOutputCode
          accept reject w stage)))

def DovetailInitialLayoutInitializerReadySpec
    (initializer : MachineDescription) : Prop :=
  initializer.WellFormed ∧ initializer.HaltTransitionFree

def DovetailInitialLayoutInitializerForwardSpec
    (accept reject initializer : MachineDescription) : Prop :=
  forall w : Word Bool,
  forall stage : Nat,
    initializer.HaltsWithTape
      (MachineDescription.encodeCodeWordAsInput
        (PairedRecognizerDovetailStageInputCode w stage))
      (DovetailInitialLayoutInitializerOutputTape
        accept reject w stage)

def DovetailInitialLayoutInitializerClosedSpec
    (accept reject initializer : MachineDescription) : Prop :=
  forall code : Word MachineCodeSymbol,
  forall T : Tape Bool,
    initializer.HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) T ->
      exists w : Word Bool,
      exists stage : Nat,
        code = PairedRecognizerDovetailStageInputCode w stage ∧
          T =
            DovetailInitialLayoutInitializerOutputTape
              accept reject w stage

def DovetailInitialLayoutInitializerRightShiftedSpec
    (accept reject initializer : MachineDescription) : Prop :=
  DovetailInitialLayoutInitializerReadySpec initializer ∧
    DovetailInitialLayoutInitializerForwardSpec
      accept reject initializer ∧
      DovetailInitialLayoutInitializerClosedSpec
        accept reject initializer

def DovetailInitialLayoutInitializerMachineConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists initializer : MachineDescription,
      DovetailInitialLayoutInitializerReadySpec initializer ∧
        DovetailInitialLayoutInitializerForwardSpec
          accept reject initializer ∧
          DovetailInitialLayoutInitializerClosedSpec
            accept reject initializer

def PairedRecognizerDovetailInitialLayoutCodeRightShiftedSpecConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists initializer : MachineDescription,
      DovetailInitialLayoutInitializerRightShiftedSpec
        accept reject initializer

private theorem dovetailInitialLayoutInitializerRightShiftedSpec_haltsWithOutput_iff
    {accept reject initializer : MachineDescription}
    (hinit :
      DovetailInitialLayoutInitializerRightShiftedSpec
        accept reject initializer)
    (code out : Word MachineCodeSymbol) :
    initializer.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) <->
      (PairedRecognizerDovetailInitialLayoutCode accept reject).transform
        code = some out := by
  constructor
  · intro hhalt
    rcases hhalt with ⟨n, hn⟩
    let T :=
      (initializer.runConfig n
        (initializer.initial
          (MachineDescription.encodeCodeWordAsInput code))).tape
    have hTape :
        initializer.HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput code) T := by
      exact ⟨n, ⟨hn.left, rfl⟩⟩
    rcases hinit.right.right code T hTape with
      ⟨w, stage, hcode, hT⟩
    let expected :=
      MachineDescription.DovetailLayout.encode
        (MachineDescription.DovetailLayout.initial accept reject w stage)
    have hactual :
        Tape.normalizedOutput T =
          MachineDescription.encodeCodeWordAsInput out := by
      simpa [T] using hn.right
    have hexpected :
        Tape.normalizedOutput T =
          MachineDescription.encodeCodeWordAsInput expected := by
      rw [hT]
      exact
        tape_normalizedOutput_move_right_input
          (MachineDescription.encodeCodeWordAsInput expected)
    have houtBits :
        MachineDescription.encodeCodeWordAsInput out =
          MachineDescription.encodeCodeWordAsInput expected := by
      rw [← hactual]
      exact hexpected
    have hout : out = expected :=
      MachineDescription.encodeCodeWordAsInput_injective houtBits
    exact
      (pairedRecognizerDovetailInitialLayoutCode_transform_eq_some_iff
        accept reject code out).mpr
        ⟨w, stage, hcode, hout⟩
  · intro htransform
    rcases
        (pairedRecognizerDovetailInitialLayoutCode_transform_eq_some_iff
          accept reject code out).mp htransform with
      ⟨w, stage, hcode, hout⟩
    subst code
    subst out
    simpa [DovetailInitialLayoutInitializerOutputTape,
      DovetailInitialLayoutInitializerOutputCode,
      tape_normalizedOutput_move_right_input] using
      MachineDescription.haltsWithOutput_of_haltsWithTape
        (hinit.right.left w stage)

private theorem tapeCodePrimitiveRightShiftedOutputCompiled_of_dovetailInitialLayoutSpec
    {accept reject initializer : MachineDescription}
    (hinit :
      DovetailInitialLayoutInitializerRightShiftedSpec
        accept reject initializer) :
    TapeCodePrimitiveRightShiftedOutputCompiledSubroutineByDescription
      (PairedRecognizerDovetailInitialLayoutCode accept reject)
      initializer := by
  constructor
  · exact hinit.left.left
  · constructor
    · exact hinit.left.right
    · constructor
      · exact
          dovetailInitialLayoutInitializerRightShiftedSpec_haltsWithOutput_iff
            hinit
      · intro code T hhalt
        rcases hinit.right.right code T hhalt with
          ⟨w, stage, hcode, hT⟩
        refine
          ⟨MachineDescription.DovetailLayout.encode
            (MachineDescription.DovetailLayout.initial
              accept reject w stage), ?_, hT⟩
        exact
          (pairedRecognizerDovetailInitialLayoutCode_transform_eq_some_iff
            accept reject code
              (MachineDescription.DovetailLayout.encode
                (MachineDescription.DovetailLayout.initial
                  accept reject w stage))).mpr
            ⟨w, stage, hcode, rfl⟩

theorem tapeCodePrimitiveClosedHandoffCompiled_of_rightShiftedOutputCompiled
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (hD :
      TapeCodePrimitiveRightShiftedOutputCompiledSubroutineByDescription
        P D)
    (houtCons :
      forall {code out : Word MachineCodeSymbol},
        P.transform code = some out ->
          exists symbol : MachineCodeSymbol,
          exists tail : Word MachineCodeSymbol,
            out = symbol :: tail) :
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      P D tapeCodePrimitiveCodeWordHandoffMove :=
  tapeCodePrimitiveClosedHandoffCompiled_of_halt_tape_move_right
    hD.left hD.right.left hD.right.right.left houtCons
    hD.right.right.right

theorem dovetailInitialLayoutInitializerMachineConstruction :
    DovetailInitialLayoutInitializerMachineConstruction := by
  intro accept reject
  sorry

theorem pairedRecognizerDovetailInitialLayoutCode_rightShiftedSpecConstruction :
    PairedRecognizerDovetailInitialLayoutCodeRightShiftedSpecConstruction := by
  intro accept reject
  rcases
      dovetailInitialLayoutInitializerMachineConstruction accept reject with
    ⟨initializer, hready, hforward, hclosed⟩
  exact ⟨initializer, hready, hforward, hclosed⟩

theorem pairedRecognizerDovetailInitialLayoutCode_rightShiftedOutputCompiledSubroutine
    (accept reject : MachineDescription) :
    exists initializer : MachineDescription,
      TapeCodePrimitiveRightShiftedOutputCompiledSubroutineByDescription
        (PairedRecognizerDovetailInitialLayoutCode accept reject)
        initializer := by
  rcases
      pairedRecognizerDovetailInitialLayoutCode_rightShiftedSpecConstruction
        accept reject with
    ⟨initializer, hinit⟩
  exact
    ⟨initializer,
      tapeCodePrimitiveRightShiftedOutputCompiled_of_dovetailInitialLayoutSpec
        hinit⟩

theorem pairedRecognizerDovetailInitialLayoutCode_closedHandoffCompiledSubroutine
    (accept reject : MachineDescription) :
    exists initializer : MachineDescription,
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (PairedRecognizerDovetailInitialLayoutCode accept reject)
        initializer tapeCodePrimitiveCodeWordHandoffMove := by
  rcases
      pairedRecognizerDovetailInitialLayoutCode_rightShiftedOutputCompiledSubroutine
        accept reject with
    ⟨initializer, hinitializer⟩
  refine ⟨initializer, ?_⟩
  have houtCons :
      forall {code out : Word MachineCodeSymbol},
        (PairedRecognizerDovetailInitialLayoutCode accept reject).transform
            code = some out ->
          exists symbol : MachineCodeSymbol,
          exists tail : Word MachineCodeSymbol,
            out = symbol :: tail := by
    intro code out hp
    rcases
        pairedRecognizerDovetailInitialLayoutCode_transform_eq_some_cons hp with
      ⟨tail, hout⟩
    exact ⟨MachineCodeSymbol.transition, tail, hout⟩
  exact
    tapeCodePrimitiveClosedHandoffCompiled_of_rightShiftedOutputCompiled
      hinitializer houtCons

end Computability
end FoC
