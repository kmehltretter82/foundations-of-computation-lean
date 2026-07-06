import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StageProgram.Spec

set_option doc.verso true

/-!
# Stage-program composition contracts

Contract layer for composing an output-producing finite machine with a
recognizer.  The exact-fuel stage-program construction will use this to keep
raw generated-code parsing and protected-layout recognition separate.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StageProgram

universe uProducer uRecognizer uPipeline

inductive OutputThenRecognizeState
    (producerState recognizerState : Type) where
  | producer : producerState ->
      OutputThenRecognizeState producerState recognizerState
  | handoff :
      OutputThenRecognizeState producerState recognizerState
  | recognizer : recognizerState ->
      OutputThenRecognizeState producerState recognizerState

namespace OutputThenRecognizeState

def finite
    {producerState recognizerState : Type}
    (producerFinite : Foundation.FiniteType producerState)
    (recognizerFinite : Foundation.FiniteType recognizerState) :
    Foundation.FiniteType
      (OutputThenRecognizeState producerState recognizerState) where
  elems :=
    producerFinite.elems.map OutputThenRecognizeState.producer ++
      OutputThenRecognizeState.handoff ::
        recognizerFinite.elems.map OutputThenRecognizeState.recognizer
  complete := by
    intro state
    cases state with
    | producer state =>
        simp
        exact producerFinite.complete state
    | handoff =>
        simp
    | recognizer state =>
        simp
        exact recognizerFinite.complete state

end OutputThenRecognizeState

noncomputable def outputThenRecognizePipeline
    {producerState recognizerState : Type}
    (producer : TuringMachine MachineCodeSymbol producerState)
    (recognizer : TuringMachine MachineCodeSymbol recognizerState) :
    TuringMachine MachineCodeSymbol
      (OutputThenRecognizeState producerState recognizerState) where
  start := OutputThenRecognizeState.producer producer.start
  halt := OutputThenRecognizeState.recognizer recognizer.halt
  transition := by
    classical
    exact fun state cell =>
      match state with
      | OutputThenRecognizeState.producer producerState =>
          if producerState = producer.halt then
            some (cell, Direction.right,
              OutputThenRecognizeState.handoff)
          else
            match producer.transition producerState cell with
            | none => none
            | some (write, dir, nextState) =>
                some (write, dir,
                  OutputThenRecognizeState.producer nextState)
      | OutputThenRecognizeState.handoff =>
          some (cell, Direction.left,
            OutputThenRecognizeState.recognizer recognizer.start)
      | OutputThenRecognizeState.recognizer recognizerState =>
          match recognizer.transition recognizerState cell with
          | none => none
          | some (write, dir, nextState) =>
              some (write, dir,
                OutputThenRecognizeState.recognizer nextState)
  statesFinite :=
    OutputThenRecognizeState.finite
      producer.statesFinite recognizer.statesFinite

theorem outputThenRecognizePipeline_haltingTransitionsDisabled
    {producerState recognizerState : Type}
    {producer : TuringMachine MachineCodeSymbol producerState}
    {recognizer : TuringMachine MachineCodeSymbol recognizerState}
    (hstop : TuringMachine.HaltingTransitionsDisabled recognizer) :
    TuringMachine.HaltingTransitionsDisabled
      (outputThenRecognizePipeline producer recognizer) := by
  intro cell
  change
    (match recognizer.transition recognizer.halt cell with
    | none => none
    | some (write, dir, nextState) =>
        some (write, dir,
          OutputThenRecognizeState.recognizer nextState)) = none
  rw [hstop cell]

theorem outputThenRecognizePipeline_producer_step
    {producerState recognizerState : Type}
    {producer : TuringMachine MachineCodeSymbol producerState}
    {recognizer : TuringMachine MachineCodeSymbol recognizerState}
    {c d : TuringMachine.Configuration MachineCodeSymbol producerState}
    (hnotHalt : c.state ≠ producer.halt)
    (hstep : TuringMachine.Step producer c d) :
    TuringMachine.Step
      (outputThenRecognizePipeline producer recognizer)
      { state := OutputThenRecognizeState.producer c.state
        tape := c.tape }
      { state := OutputThenRecognizeState.producer d.state
        tape := d.tape } := by
  cases hstep with
  | mk haction =>
      exact TuringMachine.Step.mk (by
        simp [outputThenRecognizePipeline, hnotHalt, haction])

theorem outputThenRecognizePipeline_producer_computes
    {producerState recognizerState : Type}
    {producer : TuringMachine MachineCodeSymbol producerState}
    {recognizer : TuringMachine MachineCodeSymbol recognizerState}
    (hstop : TuringMachine.HaltingTransitionsDisabled producer)
    {c d : TuringMachine.Configuration MachineCodeSymbol producerState}
    (hcomp : TuringMachine.Computes producer c d) :
    TuringMachine.Computes
      (outputThenRecognizePipeline producer recognizer)
      { state := OutputThenRecognizeState.producer c.state
        tape := c.tape }
      { state := OutputThenRecognizeState.producer d.state
        tape := d.tape } := by
  induction hcomp with
  | refl c =>
      exact TuringMachine.Computes.refl _
  | @step c d e hstep hcomp ih =>
      have hnotHalt : c.state ≠ producer.halt := by
        intro hhalt
        exact TuringMachine.no_step_from_halted hstop hhalt hstep
      exact TuringMachine.Computes.step
        (outputThenRecognizePipeline_producer_step
          hnotHalt hstep)
        ih

theorem outputThenRecognizePipeline_recognizer_step
    {producerState recognizerState : Type}
    {producer : TuringMachine MachineCodeSymbol producerState}
    {recognizer : TuringMachine MachineCodeSymbol recognizerState}
    {c d : TuringMachine.Configuration MachineCodeSymbol recognizerState}
    (hstep : TuringMachine.Step recognizer c d) :
    TuringMachine.Step
      (outputThenRecognizePipeline producer recognizer)
      { state := OutputThenRecognizeState.recognizer c.state
        tape := c.tape }
      { state := OutputThenRecognizeState.recognizer d.state
        tape := d.tape } := by
  cases hstep with
  | mk haction =>
      exact TuringMachine.Step.mk (by
        simp [outputThenRecognizePipeline, haction])

theorem outputThenRecognizePipeline_recognizer_computes
    {producerState recognizerState : Type}
    {producer : TuringMachine MachineCodeSymbol producerState}
    {recognizer : TuringMachine MachineCodeSymbol recognizerState}
    {c d : TuringMachine.Configuration MachineCodeSymbol recognizerState}
    (hcomp : TuringMachine.Computes recognizer c d) :
    TuringMachine.Computes
      (outputThenRecognizePipeline producer recognizer)
      { state := OutputThenRecognizeState.recognizer c.state
        tape := c.tape }
      { state := OutputThenRecognizeState.recognizer d.state
        tape := d.tape } := by
  induction hcomp with
  | refl c =>
      exact TuringMachine.Computes.refl _
  | step hstep _ ih =>
      exact TuringMachine.Computes.step
        (outputThenRecognizePipeline_recognizer_step hstep)
        ih

theorem outputThenRecognizePipeline_handoff_right_step
    {producerState recognizerState : Type}
    (producer : TuringMachine MachineCodeSymbol producerState)
    (recognizer : TuringMachine MachineCodeSymbol recognizerState)
    (T : Tape MachineCodeSymbol) :
    TuringMachine.Step
      (outputThenRecognizePipeline producer recognizer)
      { state := OutputThenRecognizeState.producer producer.halt
        tape := T }
      { state := OutputThenRecognizeState.handoff
        tape := Tape.move Direction.right
          (Tape.write (Tape.read T) T) } := by
  exact TuringMachine.Step.mk (by
    simp [outputThenRecognizePipeline])

theorem outputThenRecognizePipeline_handoff_left_step
    {producerState recognizerState : Type}
    (producer : TuringMachine MachineCodeSymbol producerState)
    (recognizer : TuringMachine MachineCodeSymbol recognizerState)
    (T : Tape MachineCodeSymbol) :
    TuringMachine.Step
      (outputThenRecognizePipeline producer recognizer)
      { state := OutputThenRecognizeState.handoff
        tape := T }
      { state :=
          OutputThenRecognizeState.recognizer recognizer.start
        tape := Tape.move Direction.left
          (Tape.write (Tape.read T) T) } := by
  exact TuringMachine.Step.mk (by
    simp [outputThenRecognizePipeline])

theorem outputThenRecognizePipeline_handoff_computes
    {producerState recognizerState : Type}
    (producer : TuringMachine MachineCodeSymbol producerState)
    (recognizer : TuringMachine MachineCodeSymbol recognizerState)
    (T : Tape MachineCodeSymbol) :
    TuringMachine.Computes
      (outputThenRecognizePipeline producer recognizer)
      { state := OutputThenRecognizeState.producer producer.halt
        tape := T }
      { state := OutputThenRecognizeState.recognizer recognizer.start
        tape :=
          Tape.move Direction.left
            (Tape.write
              (Tape.read
                (Tape.move Direction.right
                  (Tape.write (Tape.read T) T)))
              (Tape.move Direction.right
                (Tape.write (Tape.read T) T))) } := by
  exact
    TuringMachine.Computes.step
      (outputThenRecognizePipeline_handoff_right_step
        producer recognizer T)
      (TuringMachine.Computes.step
        (outputThenRecognizePipeline_handoff_left_step
          producer recognizer
          (Tape.move Direction.right
            (Tape.write (Tape.read T) T)))
        (TuringMachine.Computes.refl _))

theorem tape_write_read_eq
    (T : Tape MachineCodeSymbol) :
    Tape.write (Tape.read T) T = T := by
  cases T
  rfl

theorem tape_move_left_move_right_equiv
    (T : Tape MachineCodeSymbol) :
    Tape.Equiv (Tape.move Direction.left (Tape.move Direction.right T)) T := by
  cases T with
  | mk left head right =>
      cases right with
      | nil =>
          cases head <;>
            simp [Tape.Equiv, Tape.move, Tape.moveLeft,
              Tape.moveRight, Tape.dropTrailingNone]
      | cons cell rest =>
          simp [Tape.Equiv, Tape.move, Tape.moveLeft,
            Tape.moveRight]

def outputThenRecognizeHandoffTape
    (T : Tape MachineCodeSymbol) : Tape MachineCodeSymbol :=
  Tape.move Direction.left
    (Tape.write
      (Tape.read
        (Tape.move Direction.right
          (Tape.write (Tape.read T) T)))
      (Tape.move Direction.right
        (Tape.write (Tape.read T) T)))

theorem outputThenRecognizeHandoffTape_output_cons_cons
    (first second : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    outputThenRecognizeHandoffTape
        (Tape.output (first :: second :: rest)) =
      Tape.input (first :: second :: rest) := by
  rfl

theorem outputThenRecognizePipeline_handoff_tape_equiv
    (T : Tape MachineCodeSymbol) :
    Tape.Equiv
      (Tape.move Direction.left
        (Tape.write
          (Tape.read
            (Tape.move Direction.right
              (Tape.write (Tape.read T) T)))
          (Tape.move Direction.right
            (Tape.write (Tape.read T) T))))
      T := by
  rw [tape_write_read_eq T]
  rw [tape_write_read_eq
    (Tape.move Direction.right T)]
  exact tape_move_left_move_right_equiv T

theorem turingMachine_step_of_tape_equiv
    {M : TuringMachine symbol state}
    {c d : TuringMachine.Configuration symbol state}
    {tape : Tape symbol}
    (hstep : TuringMachine.Step M c d)
    (htape : Tape.Equiv c.tape tape) :
    exists nextTape : Tape symbol,
      TuringMachine.Step M
        { state := c.state, tape := tape }
        { state := d.state, tape := nextTape } ∧
        Tape.Equiv d.tape nextTape := by
  cases hstep with
  | mk haction =>
      rename_i write dir nextState
      refine
        ⟨Tape.move dir (Tape.write write tape), ?_, ?_⟩
      · exact TuringMachine.Step.mk (by
          rw [← Tape.Equiv.read_eq htape]
          exact haction)
      · exact Tape.Equiv.move (Tape.Equiv.write htape write) dir

theorem turingMachine_computes_of_tape_equiv
    {M : TuringMachine symbol state}
    {c e : TuringMachine.Configuration symbol state}
    {tape : Tape symbol}
    (hcomp : TuringMachine.Computes M c e)
    (htape : Tape.Equiv c.tape tape) :
    exists e' : TuringMachine.Configuration symbol state,
      TuringMachine.Computes M { state := c.state, tape := tape } e' ∧
        e'.state = e.state ∧
        Tape.Equiv e.tape e'.tape := by
  induction hcomp generalizing tape with
  | refl c =>
      exact
        ⟨{ state := c.state, tape := tape },
          TuringMachine.Computes.refl _, rfl, htape⟩
  | step hstep hrest ih =>
      rcases turingMachine_step_of_tape_equiv hstep htape with
        ⟨nextTape, hstep', htape'⟩
      rcases ih htape' with
        ⟨e', hcomp', hstate, htape''⟩
      exact
        ⟨e', TuringMachine.Computes.step hstep' hcomp',
          hstate, htape''⟩

theorem turingMachine_haltsFrom_of_tape_equiv
    {M : TuringMachine symbol state}
    {state : state} {tape tape' : Tape symbol}
    (htape : Tape.Equiv tape tape')
    (hhalt : TuringMachine.HaltsFrom M { state := state, tape := tape }) :
    TuringMachine.HaltsFrom M { state := state, tape := tape' } := by
  rcases hhalt with ⟨final, hcomp, hfinal⟩
  rcases turingMachine_computes_of_tape_equiv hcomp htape with
    ⟨final', hcomp', hstate, _htape'⟩
  exact
    ⟨final', hcomp',
      by simpa [TuringMachine.Halted, hstate] using hfinal⟩

/--
Unbounded halting from equivalent starting tapes is equivalent.
-/
theorem turingMachine_haltsFrom_tape_equiv_iff
    (M : TuringMachine symbol state)
    (state : state) {tape tape' : Tape symbol}
    (htape : Tape.Equiv tape tape') :
    TuringMachine.HaltsFrom M { state := state, tape := tape } <->
      TuringMachine.HaltsFrom M { state := state, tape := tape' } := by
  constructor
  · exact turingMachine_haltsFrom_of_tape_equiv htape
  · exact
      turingMachine_haltsFrom_of_tape_equiv
        (Tape.Equiv.symm htape)

/--
Exact computations are stable under tape equivalence at the starting tape,
with the same step count and final state.
-/
theorem turingMachine_computesIn_of_tape_equiv
    {M : TuringMachine symbol state}
    {n : Nat}
    {c e : TuringMachine.Configuration symbol state}
    {tape : Tape symbol}
    (hcomp : TuringMachine.ComputesIn M n c e)
    (htape : Tape.Equiv c.tape tape) :
    exists e' : TuringMachine.Configuration symbol state,
      TuringMachine.ComputesIn M n
        { state := c.state, tape := tape } e' ∧
        e'.state = e.state ∧
        Tape.Equiv e.tape e'.tape := by
  induction hcomp generalizing tape with
  | zero c =>
      exact
        ⟨{ state := c.state, tape := tape },
          TuringMachine.ComputesIn.zero _, rfl, htape⟩
  | succ hstep hrest ih =>
      rcases turingMachine_step_of_tape_equiv hstep htape with
        ⟨nextTape, hstep', htape'⟩
      rcases ih htape' with
        ⟨e', hcomp', hstate, htape''⟩
      exact
        ⟨e', TuringMachine.ComputesIn.succ hstep' hcomp',
          hstate, htape''⟩

/--
Exact halting from a configuration is stable under tape equivalence at the
starting tape, preserving the same step bound.
-/
theorem turingMachine_haltsFromIn_of_tape_equiv
    {M : TuringMachine symbol state}
    {n : Nat} {state : state} {tape tape' : Tape symbol}
    (htape : Tape.Equiv tape tape')
    (hhalt :
      TuringMachine.HaltsFromIn M n { state := state, tape := tape }) :
    TuringMachine.HaltsFromIn M n { state := state, tape := tape' } := by
  rcases hhalt with ⟨final, hcomp, hfinal⟩
  rcases turingMachine_computesIn_of_tape_equiv hcomp htape with
    ⟨final', hcomp', hstate, _htape'⟩
  exact
    ⟨final', hcomp',
      by simpa [TuringMachine.Halted, hstate] using hfinal⟩

/--
Exact halting from equivalent starting tapes is equivalent for the same step
bound.
-/
theorem turingMachine_haltsFromIn_tape_equiv_iff
    (M : TuringMachine symbol state)
    (n : Nat) (state : state) {tape tape' : Tape symbol}
    (htape : Tape.Equiv tape tape') :
    TuringMachine.HaltsFromIn M n { state := state, tape := tape } <->
      TuringMachine.HaltsFromIn M n { state := state, tape := tape' } := by
  constructor
  · exact turingMachine_haltsFromIn_of_tape_equiv htape
  · exact
      turingMachine_haltsFromIn_of_tape_equiv
        (Tape.Equiv.symm htape)

/-- A machine realizes a partial output transformer on code words. -/
def OutputSpec
    (machine : TuringMachine MachineCodeSymbol producerState)
    (f : Word MachineCodeSymbol -> Option (Word MachineCodeSymbol)) :
    Prop :=
  forall input output : Word MachineCodeSymbol,
    TuringMachine.HaltsWithOutput machine input output <->
      f input = some output

/--
Exact-output variant of {name}`OutputSpec`.  It is stronger than normalized
output and is the right contract for the concrete pipeline below, because the
handoff starts the recognizer from the producer's actual final tape.
-/
def ExactOutputSpec
    (machine : TuringMachine MachineCodeSymbol producerState)
    (f : Word MachineCodeSymbol -> Option (Word MachineCodeSymbol)) :
    Prop :=
  forall input output : Word MachineCodeSymbol,
    TuringMachine.HaltsWithExactOutput machine input output <->
      f input = some output

/--
Every halted producer final tape is a canonical exact output governed by the
same partial transformer.  This side condition is needed for sequencing:
{name}`ExactOutputSpec` alone only characterizes already-canonical output
tapes, and an arbitrary producer could otherwise halt on a non-output-shaped
tape.
-/
def ExactOutputCanonicalSpec
    (machine : TuringMachine MachineCodeSymbol producerState)
    (f : Word MachineCodeSymbol -> Option (Word MachineCodeSymbol)) :
    Prop :=
  forall input : Word MachineCodeSymbol,
  forall final : TuringMachine.Configuration MachineCodeSymbol producerState,
    TuringMachine.Computes machine (TuringMachine.initial machine input)
      final ->
    TuringMachine.Halted machine final ->
      exists output : Word MachineCodeSymbol,
        f input = some output /\ final.tape = Tape.output output

theorem outputSpec_of_exactOutput_canonical
    {machine : TuringMachine MachineCodeSymbol producerState}
    {f : Word MachineCodeSymbol -> Option (Word MachineCodeSymbol)}
    (hexact : ExactOutputSpec machine f)
    (hcanonical : ExactOutputCanonicalSpec machine f) :
    OutputSpec machine f := by
  intro input output
  constructor
  · intro houtput
    rcases houtput with
      ⟨final, hcomp, hhalt, hnormalized⟩
    rcases hcanonical input final hcomp hhalt with
      ⟨exactOutput, hf, htape⟩
    have hnormalizedExact :
        Tape.normalizedOutput final.tape = exactOutput := by
      rw [htape]
      exact Tape.normalizedOutput_output exactOutput
    have houtputEq : output = exactOutput :=
      hnormalized.symm.trans hnormalizedExact
    simpa [houtputEq] using hf
  · intro hf
    exact
      TuringMachine.halts_with_exact_output_to_halts_with_output
        ((hexact input output).mpr hf)

theorem haltsOnInput_iff_some_empty_of_exactOutput
    {machine : TuringMachine MachineCodeSymbol producerState}
    {f : Word MachineCodeSymbol -> Option (Word MachineCodeSymbol)}
    (hexact : ExactOutputSpec machine f)
    (hcanonical : ExactOutputCanonicalSpec machine f)
    (hempty :
      forall {input output : Word MachineCodeSymbol},
        f input = some output -> output = ([] : Word MachineCodeSymbol))
    (input : Word MachineCodeSymbol) :
    TuringMachine.HaltsOnInput machine input <->
      f input = some ([] : Word MachineCodeSymbol) := by
  constructor
  · intro hhalt
    rcases hhalt with ⟨final, hcomp, hfinalHalt⟩
    rcases hcanonical input final hcomp hfinalHalt with
      ⟨output, houtput, _htape⟩
    have houtputEmpty : output = ([] : Word MachineCodeSymbol) :=
      hempty houtput
    subst output
    exact houtput
  · intro houtput
    rcases (hexact input ([] : Word MachineCodeSymbol)).mpr houtput with
      ⟨final, hcomp, hfinalHalt, _htape⟩
    exact ⟨final, hcomp, hfinalHalt⟩

theorem outputThenRecognizePipeline_haltsOnInput_of_exactOutput
    {producerState recognizerState : Type}
    {producer : TuringMachine MachineCodeSymbol producerState}
    {recognizer : TuringMachine MachineCodeSymbol recognizerState}
    {f : Word MachineCodeSymbol -> Option (Word MachineCodeSymbol)}
    {P : Word MachineCodeSymbol -> Prop}
    (hstop : TuringMachine.HaltingTransitionsDisabled producer)
    (hproducer : ExactOutputSpec producer f)
    (hrecognizer : FiniteRecognizer.Recognizes recognizer P)
    {input output : Word MachineCodeSymbol}
    (hf : f input = some output)
    (hP : P output) :
    TuringMachine.HaltsOnInput
      (outputThenRecognizePipeline producer recognizer) input := by
  rcases (hproducer input output).mpr hf with
    ⟨producerFinal, hproducerComputes,
      hproducerHalt, hproducerTape⟩
  let handoffTape : Tape MachineCodeSymbol :=
    Tape.move Direction.left
      (Tape.write
        (Tape.read
          (Tape.move Direction.right
            (Tape.write
              (Tape.read producerFinal.tape) producerFinal.tape)))
        (Tape.move Direction.right
          (Tape.write
            (Tape.read producerFinal.tape) producerFinal.tape)))
  have hproducerPipeline :
      TuringMachine.Computes
        (outputThenRecognizePipeline producer recognizer)
        (TuringMachine.initial
          (outputThenRecognizePipeline producer recognizer) input)
        { state := OutputThenRecognizeState.producer producerFinal.state
          tape := producerFinal.tape } := by
    simpa [TuringMachine.initial, outputThenRecognizePipeline] using
      outputThenRecognizePipeline_producer_computes
        (recognizer := recognizer) hstop hproducerComputes
  have hhandoff :
      TuringMachine.Computes
        (outputThenRecognizePipeline producer recognizer)
        { state := OutputThenRecognizeState.producer producerFinal.state
          tape := producerFinal.tape }
        { state := OutputThenRecognizeState.recognizer recognizer.start
          tape := handoffTape } := by
    have hstate : producerFinal.state = producer.halt := hproducerHalt
    rw [hstate]
    simpa [handoffTape] using
      outputThenRecognizePipeline_handoff_computes
        producer recognizer producerFinal.tape
  have hrecognizerHalt :
      TuringMachine.HaltsFrom recognizer
        { state := recognizer.start, tape := Tape.input output } := by
    simpa [TuringMachine.HaltsOnInput, TuringMachine.initial] using
      (hrecognizer output).mpr hP
  have hhandoffEquiv :
      Tape.Equiv handoffTape producerFinal.tape := by
    simpa [handoffTape] using
      outputThenRecognizePipeline_handoff_tape_equiv producerFinal.tape
  have hinputEquiv :
      Tape.Equiv (Tape.input output) producerFinal.tape := by
    rw [hproducerTape]
    exact Tape.Equiv.refl _
  have hinputHandoffEquiv :
      Tape.Equiv (Tape.input output) handoffTape :=
    Tape.Equiv.trans hinputEquiv (Tape.Equiv.symm hhandoffEquiv)
  have hrecognizerFromHandoff :
      TuringMachine.HaltsFrom recognizer
        { state := recognizer.start, tape := handoffTape } :=
    turingMachine_haltsFrom_of_tape_equiv
      hinputHandoffEquiv hrecognizerHalt
  rcases hrecognizerFromHandoff with
    ⟨recognizerFinal, hrecognizerComputes, hrecognizerFinal⟩
  have hrecognizerPipeline :
      TuringMachine.Computes
        (outputThenRecognizePipeline producer recognizer)
        { state := OutputThenRecognizeState.recognizer recognizer.start
          tape := handoffTape }
        { state := OutputThenRecognizeState.recognizer recognizerFinal.state
          tape := recognizerFinal.tape } :=
    outputThenRecognizePipeline_recognizer_computes
      (producer := producer) hrecognizerComputes
  refine
    ⟨{ state := OutputThenRecognizeState.recognizer recognizerFinal.state
       tape := recognizerFinal.tape },
      ?_, ?_⟩
  · exact TuringMachine.computes_trans hproducerPipeline
      (TuringMachine.computes_trans hhandoff hrecognizerPipeline)
  · simpa [TuringMachine.Halted, outputThenRecognizePipeline] using
      hrecognizerFinal

theorem outputThenRecognizePipeline_haltsFrom_recognizer
    {producerState recognizerState : Type}
    {producer : TuringMachine MachineCodeSymbol producerState}
    {recognizer : TuringMachine MachineCodeSymbol recognizerState}
    {state : recognizerState} {tape : Tape MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFrom
        (outputThenRecognizePipeline producer recognizer)
        { state := OutputThenRecognizeState.recognizer state,
          tape := tape }) :
    TuringMachine.HaltsFrom recognizer
      { state := state, tape := tape } := by
  rcases h with ⟨final, hcomp, hhalt⟩
  generalize hstart :
      ({ state := OutputThenRecognizeState.recognizer state,
         tape := tape } :
        TuringMachine.Configuration MachineCodeSymbol
          (OutputThenRecognizeState producerState recognizerState)) =
        start at hcomp
  induction hcomp generalizing state tape with
  | refl c =>
      cases hstart
      refine ⟨{ state := state, tape := tape },
        TuringMachine.Computes.refl _, ?_⟩
      simpa [TuringMachine.Halted, outputThenRecognizePipeline]
        using hhalt
  | @step c d e hstep hrest ih =>
      cases hstart
      cases hstep with
      | mk haction =>
          rename_i writeP dirP nextStateP
          cases htrans :
              recognizer.transition state (Tape.read tape) with
          | none =>
              simp [outputThenRecognizePipeline, htrans] at haction
          | some action =>
              rcases action with ⟨write, dir, nextState⟩
              simp [outputThenRecognizePipeline, htrans] at haction
              rcases haction with ⟨hwrite, hdir, hstate⟩
              subst writeP
              subst dirP
              subst nextStateP
              have htail := ih (state := nextState)
                (tape := Tape.move dir (Tape.write write tape))
                hhalt rfl
              rcases htail with ⟨recognizerFinal, hcompR, hhaltR⟩
              refine ⟨recognizerFinal, ?_, hhaltR⟩
              exact TuringMachine.Computes.step
                (TuringMachine.Step.mk htrans) hcompR

theorem outputThenRecognizePipeline_haltsFrom_handoff
    {producerState recognizerState : Type}
    {producer : TuringMachine MachineCodeSymbol producerState}
    {recognizer : TuringMachine MachineCodeSymbol recognizerState}
    {tape : Tape MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFrom
        (outputThenRecognizePipeline producer recognizer)
        { state := OutputThenRecognizeState.handoff,
          tape := tape }) :
    TuringMachine.HaltsFrom recognizer
      { state := recognizer.start,
        tape :=
          Tape.move Direction.left
            (Tape.write (Tape.read tape) tape) } := by
  rcases h with ⟨final, hcomp, hhalt⟩
  generalize hstart :
      ({ state := OutputThenRecognizeState.handoff,
         tape := tape } :
        TuringMachine.Configuration MachineCodeSymbol
          (OutputThenRecognizeState producerState recognizerState)) =
        start at hcomp
  induction hcomp generalizing tape with
  | refl c =>
      cases hstart
      simp [TuringMachine.Halted, outputThenRecognizePipeline] at hhalt
  | @step c d e hstep hrest ih =>
      cases hstart
      cases hstep with
      | mk haction =>
          rename_i writeP dirP nextStateP
          simp [outputThenRecognizePipeline] at haction
          rcases haction with ⟨hwrite, hdir, hstate⟩
          subst writeP
          subst dirP
          subst nextStateP
          exact outputThenRecognizePipeline_haltsFrom_recognizer
            (producer := producer) (recognizer := recognizer)
            ⟨e, hrest, hhalt⟩

theorem outputThenRecognizePipeline_haltsFrom_producer
    {producerState recognizerState : Type}
    {producer : TuringMachine MachineCodeSymbol producerState}
    {recognizer : TuringMachine MachineCodeSymbol recognizerState}
    {state : producerState} {tape : Tape MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFrom
        (outputThenRecognizePipeline producer recognizer)
        { state := OutputThenRecognizeState.producer state,
          tape := tape }) :
    exists producerFinal :
      TuringMachine.Configuration MachineCodeSymbol producerState,
      TuringMachine.Computes producer
        { state := state, tape := tape } producerFinal ∧
        TuringMachine.Halted producer producerFinal ∧
          TuringMachine.HaltsFrom recognizer
            { state := recognizer.start,
              tape :=
                Tape.move Direction.left
                  (Tape.write
                    (Tape.read
                      (Tape.move Direction.right
                        (Tape.write (Tape.read producerFinal.tape)
                          producerFinal.tape)))
                    (Tape.move Direction.right
                      (Tape.write (Tape.read producerFinal.tape)
                        producerFinal.tape))) } := by
  rcases h with ⟨final, hcomp, hhalt⟩
  generalize hstart :
      ({ state := OutputThenRecognizeState.producer state,
         tape := tape } :
        TuringMachine.Configuration MachineCodeSymbol
          (OutputThenRecognizeState producerState recognizerState)) =
        start at hcomp
  induction hcomp generalizing state tape with
  | refl c =>
      cases hstart
      simp [TuringMachine.Halted, outputThenRecognizePipeline] at hhalt
  | @step c d e hstep hrest ih =>
      cases hstart
      cases hstep with
      | mk haction =>
          rename_i writeP dirP nextStateP
          by_cases hstate : state = producer.halt
          · simp [outputThenRecognizePipeline, hstate] at haction
            rcases haction with ⟨hwrite, hdir, hnext⟩
            subst writeP
            subst dirP
            subst nextStateP
            refine
              ⟨{ state := state, tape := tape },
                TuringMachine.Computes.refl _, ?_, ?_⟩
            · exact hstate
            · exact outputThenRecognizePipeline_haltsFrom_handoff
                (producer := producer) (recognizer := recognizer)
                ⟨e, hrest, hhalt⟩
          · cases htrans :
                producer.transition state (Tape.read tape) with
            | none =>
                simp [outputThenRecognizePipeline, hstate, htrans]
                  at haction
            | some action =>
                rcases action with ⟨write, dir, nextState⟩
                simp [outputThenRecognizePipeline, hstate, htrans]
                  at haction
                rcases haction with ⟨hwrite, hdir, hnext⟩
                subst writeP
                subst dirP
                subst nextStateP
                rcases ih (state := nextState)
                    (tape := Tape.move dir (Tape.write write tape))
                    hhalt rfl with
                  ⟨producerFinal, hcompP, hhaltP, hrecognizer⟩
                refine ⟨producerFinal, ?_, hhaltP, hrecognizer⟩
                exact TuringMachine.Computes.step
                  (TuringMachine.Step.mk htrans) hcompP

/--
A pipeline first applies a partial output transformer and then recognizes the
produced word with predicate {lean}`P`.
-/
def OutputThenRecognizeSpec
    (pipeline : TuringMachine MachineCodeSymbol pipelineState)
    (producer : Word MachineCodeSymbol -> Option (Word MachineCodeSymbol))
    (P : Word MachineCodeSymbol -> Prop) : Prop :=
  forall input : Word MachineCodeSymbol,
    TuringMachine.HaltsOnInput pipeline input <->
      exists output : Word MachineCodeSymbol,
        producer input = some output /\ P output

/--
Finite-machine construction boundary for output-then-recognize composition.
This is intentionally a contract, not a semantic shortcut: a later construction
must provide the concrete sequencing machine.
-/
def OutputThenRecognizeConstruction : Prop :=
  forall {producerState recognizerState : Type}
    (producer : TuringMachine MachineCodeSymbol producerState)
    (recognizer : TuringMachine MachineCodeSymbol recognizerState)
    (f : Word MachineCodeSymbol -> Option (Word MachineCodeSymbol))
    (P : Word MachineCodeSymbol -> Prop),
      OutputSpec producer f ->
      FiniteRecognizer.Recognizes recognizer P ->
        exists pipelineState : Type,
        exists pipeline : TuringMachine MachineCodeSymbol pipelineState,
          OutputThenRecognizeSpec pipeline f P

/--
Exact-output sequencing boundary.  This is the appropriate target when the
second phase starts from the producer's concrete final tape rather than from a
fresh canonical input tape.
-/
def ExactOutputThenRecognizeConstruction : Prop :=
  forall {producerState recognizerState : Type}
    (producer : TuringMachine MachineCodeSymbol producerState)
    (recognizer : TuringMachine MachineCodeSymbol recognizerState)
    (f : Word MachineCodeSymbol -> Option (Word MachineCodeSymbol))
    (P : Word MachineCodeSymbol -> Prop),
      ExactOutputSpec producer f ->
      ExactOutputCanonicalSpec producer f ->
      TuringMachine.HaltingTransitionsDisabled producer ->
      FiniteRecognizer.Recognizes recognizer P ->
        exists pipelineState : Type,
        exists pipeline : TuringMachine MachineCodeSymbol pipelineState,
          OutputThenRecognizeSpec pipeline f P

theorem outputThenRecognizePipeline_exactOutputSpec
    {producerState recognizerState : Type}
    {producer : TuringMachine MachineCodeSymbol producerState}
    {recognizer : TuringMachine MachineCodeSymbol recognizerState}
    {f : Word MachineCodeSymbol -> Option (Word MachineCodeSymbol)}
    {P : Word MachineCodeSymbol -> Prop}
    (hstop : TuringMachine.HaltingTransitionsDisabled producer)
    (hproducer : ExactOutputSpec producer f)
    (hcanonical : ExactOutputCanonicalSpec producer f)
    (hrecognizer : FiniteRecognizer.Recognizes recognizer P) :
    OutputThenRecognizeSpec
      (outputThenRecognizePipeline producer recognizer) f P := by
  intro input
  constructor
  · intro hpipeline
    rcases
        outputThenRecognizePipeline_haltsFrom_producer
          (producer := producer) (recognizer := recognizer)
          hpipeline with
      ⟨producerFinal, hproducerComputes, hproducerHalt,
        hrecognizerFromHandoff⟩
    rcases
        hcanonical input producerFinal hproducerComputes
          hproducerHalt with
      ⟨output, hf, hproducerTape⟩
    have hhandoffEquiv :
        Tape.Equiv
          (Tape.move Direction.left
            (Tape.write
              (Tape.read
                (Tape.move Direction.right
                  (Tape.write
                    (Tape.read producerFinal.tape)
                    producerFinal.tape)))
              (Tape.move Direction.right
                (Tape.write
                  (Tape.read producerFinal.tape)
                  producerFinal.tape))))
          producerFinal.tape := by
      simpa using
        outputThenRecognizePipeline_handoff_tape_equiv
          producerFinal.tape
    have hinputEquiv :
        Tape.Equiv (Tape.input output) producerFinal.tape := by
      rw [hproducerTape]
      exact Tape.Equiv.refl _
    have hhandoffInputEquiv :
        Tape.Equiv
          (Tape.move Direction.left
            (Tape.write
              (Tape.read
                (Tape.move Direction.right
                  (Tape.write
                    (Tape.read producerFinal.tape)
                    producerFinal.tape)))
              (Tape.move Direction.right
                (Tape.write
                  (Tape.read producerFinal.tape)
                  producerFinal.tape))))
          (Tape.input output) :=
      Tape.Equiv.trans hhandoffEquiv
        (Tape.Equiv.symm hinputEquiv)
    have hrecognizerInput :
        TuringMachine.HaltsOnInput recognizer output := by
      simpa [TuringMachine.HaltsOnInput, TuringMachine.initial]
        using
          turingMachine_haltsFrom_of_tape_equiv
            hhandoffInputEquiv hrecognizerFromHandoff
    exact ⟨output, hf, (hrecognizer output).mp hrecognizerInput⟩
  · intro h
    rcases h with ⟨output, hf, hP⟩
    exact
      outputThenRecognizePipeline_haltsOnInput_of_exactOutput
        hstop hproducer hrecognizer hf hP

theorem exactOutputThenRecognizeConstruction :
    ExactOutputThenRecognizeConstruction := by
  intro producerState recognizerState producer recognizer f P
    hproducer hcanonical hstop hrecognizer
  exact
    ⟨OutputThenRecognizeState producerState recognizerState,
      outputThenRecognizePipeline producer recognizer,
      outputThenRecognizePipeline_exactOutputSpec
        hstop hproducer hcanonical hrecognizer⟩

theorem outputThenRecognizeSpec_of_recognizer
    {pipelineState recognizerState : Type}
    {pipeline : TuringMachine MachineCodeSymbol pipelineState}
    {recognizer : TuringMachine MachineCodeSymbol recognizerState}
    {producer : Word MachineCodeSymbol -> Option (Word MachineCodeSymbol)}
    {P : Word MachineCodeSymbol -> Prop}
    (hpipeline : OutputThenRecognizeSpec pipeline producer P)
    (hrecognizer : FiniteRecognizer.Recognizes recognizer P) :
    forall input : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput pipeline input <->
        exists output : Word MachineCodeSymbol,
          producer input = some output /\
            TuringMachine.HaltsOnInput recognizer output := by
  intro input
  rw [hpipeline input]
  constructor
  · intro h
    rcases h with ⟨output, hproducer, hP⟩
    exact ⟨output, hproducer, (hrecognizer output).mpr hP⟩
  · intro h
    rcases h with ⟨output, hproducer, hhalt⟩
    exact ⟨output, hproducer, (hrecognizer output).mp hhalt⟩

end StageProgram
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
