import FoC.Computability.Compiler.Core.TransitionTableChecks
import FoC.Computability.Compiler.Core.ControllerCloseout

set_option doc.verso true

/-!
# Encoded rewriter contracts
-/

namespace FoC
namespace Computability

open Languages

/-!
**Milestone 2 parser/rewriter leaves.**  The remaining finite-source work is
not a generic compiler for arbitrary {name}`MachineDescription.TapeCodePrimitive`
values.  It is a fixed family of code-word parsers and rewriters for the
canonical encodings used by the dovetail controller.  The declarations below
name those finite transition-table obligations explicitly.  Each one is a
single concrete machine family over the existing encodings, and the older
scaffold names are derived from them rather than carrying anonymous broad
holes.
-/

def EncodedCodeWordCanonicalRecognizerConstruction : Prop :=
  exists recognizer : MachineDescription,
    recognizer.SubroutineReady ∧
      forall bits : Word Bool,
      forall code : Word MachineCodeSymbol,
        recognizer.HaltsWithOutput bits
            (MachineDescription.encodeCodeWordAsInput code) <->
          MachineDescription.decodeCodeWordAsInput bits = some code

theorem encodedCodeWordCanonicalRecognizerConstruction_scaffold :
    EncodedCodeWordCanonicalRecognizerConstruction := by
  refine
    ⟨MachineDescription.ExactIdentityDescription,
      ⟨MachineDescription.exactIdentityDescription_wellFormed,
        MachineDescription.exactIdentityDescription_haltTransitionFree⟩,
      ?_⟩
  intro bits code
  constructor
  · intro h
    have hbits :
        MachineDescription.encodeCodeWordAsInput code = bits :=
      (MachineDescription.exactIdentityDescription_haltsWithOutput_iff
        bits (MachineDescription.encodeCodeWordAsInput code)).mp h
    rw [← hbits]
    exact
      MachineDescription.decodeCodeWordAsInput_encodeCodeWordAsInput code
  · intro h
    have hbits :
        bits = MachineDescription.encodeCodeWordAsInput code :=
      MachineDescription.decodeCodeWordAsInput_eq_some_encodeCodeWordAsInput h
    rw [hbits]
    exact
      (MachineDescription.exactIdentityDescription_haltsWithOutput_iff
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput code)).mpr rfl

def EncodedDovetailStageInputToInitialLayoutRewriterConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists initializer : MachineDescription,
      initializer.SubroutineReady ∧
        forall code out : Word MachineCodeSymbol,
          initializer.HaltsWithOutput
              (MachineDescription.encodeCodeWordAsInput code)
              (MachineDescription.encodeCodeWordAsInput out) <->
            (PairedRecognizerDovetailInitialLayoutCode
              accept reject).transform code = some out

def EncodedDovetailLayoutBoundedRunnerRewriterConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists runner : MachineDescription,
      runner.SubroutineReady ∧
        forall code out : Word MachineCodeSymbol,
          runner.HaltsWithOutput
              (MachineDescription.encodeCodeWordAsInput code)
              (MachineDescription.encodeCodeWordAsInput out) <->
            (PairedRecognizerDovetailLayoutCode
              accept reject).transform code = some out

def EncodedDovetailTotalOutputEmitterRewriterConstruction :
    Prop :=
  exists emitter : MachineDescription,
    emitter.SubroutineReady ∧
      forall code out : Word MachineCodeSymbol,
        emitter.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput code)
            (MachineDescription.encodeCodeWordAsInput out) <->
          PairedRecognizerDovetailTotalOutputCode.transform code = some out

def EncodedDovetailStageInputToInitialLayoutHandoffRewriterConstruction :
    Prop :=
  PairedRecognizerDovetailStageInputInitializerHandoffCompiledSubroutineConstruction

def EncodedDovetailLayoutBoundedRunnerHandoffRewriterConstruction :
    Prop :=
  PairedRecognizerDovetailBoundedLayoutRunnerHandoffCompiledSubroutineConstruction

def EncodedDovetailTotalOutputEmitterHandoffRewriterConstruction :
    Prop :=
  PairedRecognizerDovetailTotalOutputEmitterHandoffCompiledSubroutineConstruction

def EncodedDovetailStageInputToInitialLayoutClosedHandoffRewriterConstruction :
    Prop :=
  PairedRecognizerDovetailStageInputInitializerClosedHandoffCompiledSubroutineConstruction

def EncodedDovetailLayoutBoundedRunnerClosedHandoffRewriterConstruction :
    Prop :=
  PairedRecognizerDovetailBoundedLayoutRunnerClosedHandoffCompiledSubroutineConstruction

def EncodedDovetailTotalOutputEmitterClosedHandoffRewriterConstruction :
    Prop :=
  PairedRecognizerDovetailTotalOutputEmitterClosedHandoffCompiledSubroutineConstruction

/-!
**Encoded rewriter handoff.**  Several controller components are ordinary
code-word transducers: they consume a canonical encoded
{name}`MachineCodeSymbol` word and produce another one.  For those components,
an output-compiled subroutine already gives the exact encoded rewriter
interface, so the remaining leaves can target subroutine construction instead
of restating the encoded input/output behavior.
-/

def EncodedTapeCodePrimitiveRewriterConstruction
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  exists rewriter : MachineDescription,
    rewriter.SubroutineReady ∧
      forall code out : Word MachineCodeSymbol,
        rewriter.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput code)
            (MachineDescription.encodeCodeWordAsInput out) <->
          P.transform code = some out

def EncodedTapeCodePrimitiveOutputCompiledSubroutineConstruction
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  exists rewriter : MachineDescription,
    TapeCodePrimitiveOutputCompiledSubroutineByDescription P rewriter

theorem encodedTapeCodePrimitiveRewriterConstruction_of_outputCompiledSubroutine
    {P : MachineDescription.TapeCodePrimitive}
    (h : EncodedTapeCodePrimitiveOutputCompiledSubroutineConstruction P) :
    EncodedTapeCodePrimitiveRewriterConstruction P := by
  rcases h with ⟨rewriter, hrewriter⟩
  exact
    ⟨rewriter,
      tapeCodePrimitiveOutputCompiledSubroutineByDescription_subroutineReady
        hrewriter,
      hrewriter.left.right⟩

def EncodedControllerInputInitializerRewriterConstruction :
    Prop :=
  exists initializer : MachineDescription,
    initializer.SubroutineReady ∧
      forall w : Word Bool,
        initializer.HaltsWithOutput w
          (MachineDescription.encodeCodeWordAsInput
            (PairedRecognizerDovetailControllerInitialCode w))

def EncodedControllerStageInputProjectionRewriterConstruction :
    Prop :=
  exists encoder : MachineDescription,
    encoder.SubroutineReady ∧
      forall code out : Word MachineCodeSymbol,
        encoder.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput code)
            (MachineDescription.encodeCodeWordAsInput out) <->
          PairedRecognizerDovetailControllerStageInputCodePrimitive.transform
            code = some out

def EncodedControllerResultEmitterRewriterConstruction :
    Prop :=
  exists emitter : MachineDescription,
    emitter.SubroutineReady ∧
      forall C : MachineDescription.DovetailControllerLayout,
      forall b : Bool,
        emitter.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.DovetailControllerLayout.encode C))
            [b] <->
          PairedRecognizerDovetailControllerRawOutput C.result = some [b]

def EncodedControllerContinueRewriterConstruction :
    Prop :=
  exists continuer : MachineDescription,
    continuer.SubroutineReady ∧
      forall C : MachineDescription.DovetailControllerLayout,
        continuer.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.DovetailControllerLayout.encode C))
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.DovetailControllerLayout.encode
                (MachineDescription.DovetailControllerLayout.nextStage C))) <->
          PairedRecognizerDovetailControllerRawOutput C.result = none

def EncodedControllerStageInputProjectionCodeWordSubroutineConstruction :
    Prop :=
  EncodedTapeCodePrimitiveOutputCompiledSubroutineConstruction
    PairedRecognizerDovetailControllerStageInputCodePrimitive

def EncodedControllerResultContinueCodeWordSubroutineConstruction :
    Prop :=
  EncodedTapeCodePrimitiveOutputCompiledSubroutineConstruction
    PairedRecognizerDovetailControllerResultContinueCode

theorem encodedControllerStageInputProjectionRewriterConstruction_of_codeWordSubroutine
    (h :
      EncodedControllerStageInputProjectionCodeWordSubroutineConstruction) :
    EncodedControllerStageInputProjectionRewriterConstruction :=
  encodedTapeCodePrimitiveRewriterConstruction_of_outputCompiledSubroutine h

theorem encodedControllerContinueRewriterConstruction_of_resultContinueCodeWordSubroutine
    (h : EncodedControllerResultContinueCodeWordSubroutineConstruction) :
    EncodedControllerContinueRewriterConstruction := by
  rcases
      encodedTapeCodePrimitiveRewriterConstruction_of_outputCompiledSubroutine h with
    ⟨continuer, hready, hspec⟩
  refine ⟨continuer, hready, ?_⟩
  intro C
  exact
    Iff.trans
      (hspec (MachineDescription.DovetailControllerLayout.encode C)
        (MachineDescription.DovetailControllerLayout.encode
          (MachineDescription.DovetailControllerLayout.nextStage C)))
      pairedRecognizerDovetailControllerResultContinueCode_encode_nextStage_iff

/-!
**Initial-layout initializer.**  The first closed-handoff leaf is a concrete
finite transducer for {name}`PairedRecognizerDovetailInitialLayoutCode`.  It
must parse a canonical stage-input code word, preserve the encoded input and
stage fields, insert the fixed initial configurations for the supplied accept
and reject descriptions, emit the complete dovetail-layout encoding, and halt
with the head positioned for the canonical code-word handoff move.
-/

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

private theorem tape_move_left_move_right_input_two
    (b0 b1 : Bool) (rest : Word Bool) :
    Tape.move Direction.left
        (Tape.move Direction.right (Tape.input (b0 :: b1 :: rest))) =
      Tape.input (b0 :: b1 :: rest) := by
  rfl

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

private theorem pairedRecognizerDovetailStageInputCode_eq
    (w : Word Bool) (stage : Nat) :
    PairedRecognizerDovetailStageInputCode w stage =
      MachineDescription.encodeBoolWordAppend w
        (MachineDescription.encodeNatAppend stage []) := by
  rfl

private theorem encodeConfigurationAppend_initial
    (D : MachineDescription) (w : Word Bool)
    (suffix : Word MachineCodeSymbol) :
    MachineDescription.encodeConfigurationAppend (D.initial w) suffix =
      MachineDescription.encodeNatAppend D.start
        (MachineDescription.encodeTapeAppend (Tape.input w) suffix) := by
  rfl

private theorem encodeTapeAppend_input_nil
    (suffix : Word MachineCodeSymbol) :
    MachineDescription.encodeTapeAppend (Tape.input ([] : Word Bool))
        suffix =
      MachineDescription.encodeCellListAppend []
        (MachineDescription.encodeCellAppend none
          (MachineDescription.encodeCellListAppend [] suffix)) := by
  rfl

private theorem encodeTapeAppend_input_cons
    (b : Bool) (rest : Word Bool)
    (suffix : Word MachineCodeSymbol) :
    MachineDescription.encodeTapeAppend (Tape.input (b :: rest)) suffix =
      MachineDescription.encodeCellListAppend []
        (MachineDescription.encodeCellAppend (some b)
          (MachineDescription.encodeCellListAppend (rest.map some)
            suffix)) := by
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

private theorem dovetailInitialLayoutCode_output_eq_expanded
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

private theorem pairedRecognizerDovetailInitialLayoutCode_transform_eq_some_cons
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

private def TapeCodePrimitiveRightShiftedOutputCompiledSubroutineByDescription
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

private theorem tapeCodePrimitiveClosedHandoffCompiled_of_rightShiftedOutputCompiled
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

private theorem pairedRecognizerDovetailInitialLayoutCode_rightShiftedOutputCompiledSubroutine
    (accept reject : MachineDescription) :
    exists initializer : MachineDescription,
      TapeCodePrimitiveRightShiftedOutputCompiledSubroutineByDescription
        (PairedRecognizerDovetailInitialLayoutCode accept reject)
        initializer := by
  sorry

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

theorem encodedDovetailStageInputToInitialLayoutClosedHandoffRewriterConstruction_scaffold :
    EncodedDovetailStageInputToInitialLayoutClosedHandoffRewriterConstruction := by
  intro accept reject
  exact
    pairedRecognizerDovetailInitialLayoutCode_closedHandoffCompiledSubroutine
      accept reject

theorem encodedDovetailLayoutBoundedRunnerClosedHandoffRewriterConstruction_scaffold :
    EncodedDovetailLayoutBoundedRunnerClosedHandoffRewriterConstruction := by
  sorry

theorem encodedDovetailTotalOutputEmitterClosedHandoffRewriterConstruction_scaffold :
    EncodedDovetailTotalOutputEmitterClosedHandoffRewriterConstruction := by
  sorry

theorem encodedDovetailStageInputToInitialLayoutRewriterConstruction_scaffold :
    EncodedDovetailStageInputToInitialLayoutRewriterConstruction := by
  intro accept reject
  rcases
      encodedDovetailStageInputToInitialLayoutClosedHandoffRewriterConstruction_scaffold
        accept reject with
    ⟨initializer, hinitializer⟩
  exact
    ⟨initializer,
      tapeCodePrimitiveOutputCompiledSubroutineByDescription_subroutineReady
        hinitializer.left,
      hinitializer.left.left.right⟩

theorem encodedDovetailLayoutBoundedRunnerRewriterConstruction_scaffold :
    EncodedDovetailLayoutBoundedRunnerRewriterConstruction := by
  intro accept reject
  rcases
      encodedDovetailLayoutBoundedRunnerClosedHandoffRewriterConstruction_scaffold
        accept reject with
    ⟨runner, hrunner⟩
  exact
    ⟨runner,
      tapeCodePrimitiveOutputCompiledSubroutineByDescription_subroutineReady
        hrunner.left,
      hrunner.left.left.right⟩

theorem encodedDovetailTotalOutputEmitterRewriterConstruction_scaffold :
    EncodedDovetailTotalOutputEmitterRewriterConstruction := by
  rcases
      encodedDovetailTotalOutputEmitterClosedHandoffRewriterConstruction_scaffold with
    ⟨emitter, hemitter⟩
  exact
    ⟨emitter,
      tapeCodePrimitiveOutputCompiledSubroutineByDescription_subroutineReady
        hemitter.left,
      hemitter.left.left.right⟩

theorem encodedDovetailStageInputToInitialLayoutHandoffRewriterConstruction_scaffold :
    EncodedDovetailStageInputToInitialLayoutHandoffRewriterConstruction :=
  pairedRecognizerDovetailStageInputInitializerHandoffCompiledSubroutineConstruction_of_closedHandoff
    encodedDovetailStageInputToInitialLayoutClosedHandoffRewriterConstruction_scaffold

theorem encodedDovetailLayoutBoundedRunnerHandoffRewriterConstruction_scaffold :
    EncodedDovetailLayoutBoundedRunnerHandoffRewriterConstruction :=
  pairedRecognizerDovetailBoundedLayoutRunnerHandoffCompiledSubroutineConstruction_of_closedHandoff
    encodedDovetailLayoutBoundedRunnerClosedHandoffRewriterConstruction_scaffold

theorem encodedDovetailTotalOutputEmitterHandoffRewriterConstruction_scaffold :
    EncodedDovetailTotalOutputEmitterHandoffRewriterConstruction :=
  pairedRecognizerDovetailTotalOutputEmitterHandoffCompiledSubroutineConstruction_of_closedHandoff
    encodedDovetailTotalOutputEmitterClosedHandoffRewriterConstruction_scaffold

end Computability
end FoC
