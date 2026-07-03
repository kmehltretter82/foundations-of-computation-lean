import FoC.Computability.Compiler.UniversalAndRanges.Basic

set_option doc.verso true

/-!
# Stage Code Decoder

This module exposes the finite machine that recognizes canonical unary
stage-code prefixes without depending on the decoded bounded-simulator layer.
-/

namespace FoC
namespace Computability

open Languages

def StageCodeDecoderConstruction : Prop :=
  exists state : Type,
  exists decoder : TuringMachine MachineCodeSymbol state,
    forall tokens : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput decoder tokens <->
        exists stage : Nat,
        exists encoded : Word MachineCodeSymbol,
          tokens = CodePrefixRecognizerStageCode encoded stage

inductive StageCodeDecoderState where
  | scan : StageCodeDecoderState
  | halt : StageCodeDecoderState
deriving DecidableEq

namespace StageCodeDecoderState

def finite : Foundation.FiniteType StageCodeDecoderState where
  elems := [scan, halt]
  complete := by
    intro state
    cases state <;> simp

end StageCodeDecoderState

def stageCodeDecoderTape
    (leftRev rest : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match rest with
  | [] =>
      { left := leftRev.map some
        head := none
        right := [] }
  | symbol :: suffix =>
      { left := leftRev.map some
        head := some symbol
        right := suffix.map some }

theorem stageCodeDecoderTape_move_right
    (leftRev : Word MachineCodeSymbol)
    (symbol : MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol) :
    Tape.move Direction.right
        (Tape.write (some symbol)
          (stageCodeDecoderTape leftRev (symbol :: suffix))) =
      stageCodeDecoderTape (symbol :: leftRev) suffix := by
  cases suffix <;>
    simp [stageCodeDecoderTape, Tape.move, Tape.moveRight,
      Tape.write]

theorem stageCodeDecoderTape_nil_eq_input
    (tokens : Word MachineCodeSymbol) :
    stageCodeDecoderTape [] tokens = Tape.input tokens := by
  cases tokens <;> rfl

def stageCodeDecoderMachine :
    TuringMachine MachineCodeSymbol StageCodeDecoderState where
  start := StageCodeDecoderState.scan
  halt := StageCodeDecoderState.halt
  transition := fun state cell =>
    match state, cell with
    | StageCodeDecoderState.scan, some MachineCodeSymbol.tick =>
        some
          (some MachineCodeSymbol.tick, Direction.right,
            StageCodeDecoderState.scan)
    | StageCodeDecoderState.scan, some MachineCodeSymbol.done =>
        some
          (some MachineCodeSymbol.done, Direction.right,
            StageCodeDecoderState.halt)
    | _, _ => none
  statesFinite := StageCodeDecoderState.finite

theorem stageCodeDecoderMachine_step_tick
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step stageCodeDecoderMachine
      { state := StageCodeDecoderState.scan
        tape :=
          stageCodeDecoderTape leftRev
            (MachineCodeSymbol.tick :: suffix) }
      { state := StageCodeDecoderState.scan
        tape :=
          stageCodeDecoderTape
            (MachineCodeSymbol.tick :: leftRev) suffix } := by
  rw [← stageCodeDecoderTape_move_right leftRev
    MachineCodeSymbol.tick suffix]
  exact TuringMachine.Step.mk (by
    simp [stageCodeDecoderMachine,
      stageCodeDecoderTape, Tape.read])

theorem stageCodeDecoderMachine_step_done
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step stageCodeDecoderMachine
      { state := StageCodeDecoderState.scan
        tape :=
          stageCodeDecoderTape leftRev
            (MachineCodeSymbol.done :: suffix) }
      { state := StageCodeDecoderState.halt
        tape :=
          stageCodeDecoderTape
            (MachineCodeSymbol.done :: leftRev) suffix } := by
  rw [← stageCodeDecoderTape_move_right leftRev
    MachineCodeSymbol.done suffix]
  exact TuringMachine.Step.mk (by
    simp [stageCodeDecoderMachine,
      stageCodeDecoderTape, Tape.read])

theorem stageCodeDecoderMachine_haltsFromIn_encodeNatAppend
    (leftRev : Word MachineCodeSymbol)
    (stage : Nat)
    (encoded : Word MachineCodeSymbol) :
    TuringMachine.HaltsFromIn stageCodeDecoderMachine
      (stage + 1)
      { state := StageCodeDecoderState.scan
        tape :=
          stageCodeDecoderTape leftRev
            (CodePrefixRecognizerStageCode encoded stage) } := by
  induction stage generalizing leftRev with
  | zero =>
      refine
        ⟨{ state := StageCodeDecoderState.halt,
            tape :=
              stageCodeDecoderTape
                (MachineCodeSymbol.done :: leftRev) encoded },
          ?_, rfl⟩
      exact TuringMachine.ComputesIn.succ
        (by
          simpa [CodePrefixRecognizerStageCode,
            MachineDescription.encodeNatAppend,
            MachineDescription.encodeNat] using
            stageCodeDecoderMachine_step_done leftRev encoded)
        (TuringMachine.ComputesIn.zero _)
  | succ stage ih =>
      rcases ih (MachineCodeSymbol.tick :: leftRev) with
        ⟨final, hcomp, hhalt⟩
      refine ⟨final, ?_, hhalt⟩
      exact TuringMachine.ComputesIn.succ
        (by
          simpa [CodePrefixRecognizerStageCode,
            MachineDescription.encodeNatAppend,
            MachineDescription.encodeNat] using
            stageCodeDecoderMachine_step_tick leftRev
              (CodePrefixRecognizerStageCode encoded stage))
        hcomp

theorem stageCodeDecoderMachine_haltsFromIn_only_encodeNatAppend
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn stageCodeDecoderMachine steps
        { state := StageCodeDecoderState.scan
          tape := stageCodeDecoderTape leftRev rest }) :
    exists stage : Nat,
    exists encoded : Word MachineCodeSymbol,
      rest = CodePrefixRecognizerStageCode encoded stage := by
  induction steps generalizing leftRev rest with
  | zero =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp
      cases hhalt
  | succ steps ih =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp with
      | succ hstep hrest =>
          cases rest with
          | nil =>
              cases hstep with
              | mk haction =>
                  simp [stageCodeDecoderMachine,
                    stageCodeDecoderTape, Tape.read] at haction
          | cons symbol suffix =>
              cases symbol with
              | header =>
                  cases hstep with
                  | mk haction =>
                      simp [stageCodeDecoderMachine,
                        stageCodeDecoderTape, Tape.read] at haction
              | transition =>
                  cases hstep with
                  | mk haction =>
                      simp [stageCodeDecoderMachine,
                        stageCodeDecoderTape, Tape.read] at haction
              | tick =>
                  cases hstep with
                  | mk haction =>
                      rename_i write dir nextState
                      cases write with
                      | none =>
                          simp [stageCodeDecoderMachine,
                            stageCodeDecoderTape, Tape.read]
                            at haction
                      | some writeSymbol =>
                          cases writeSymbol <;>
                            cases dir <;>
                            cases nextState <;>
                              simp [stageCodeDecoderMachine,
                                stageCodeDecoderTape, Tape.read]
                                at haction
                          have htail :
                              TuringMachine.HaltsFromIn
                                stageCodeDecoderMachine steps
                                { state := StageCodeDecoderState.scan
                                  tape :=
                                    stageCodeDecoderTape
                                      (MachineCodeSymbol.tick :: leftRev)
                                      suffix } := by
                            refine ⟨final, ?_, hhalt⟩
                            cases suffix <;>
                              simpa [stageCodeDecoderMachine,
                                stageCodeDecoderTape,
                                stageCodeDecoderTape_move_right,
                                Tape.write, Tape.move, Tape.moveRight]
                                using hrest
                          rcases ih htail with ⟨stage, encoded, hsuffix⟩
                          exact ⟨stage + 1, encoded, by
                            simp [CodePrefixRecognizerStageCode,
                              MachineDescription.encodeNatAppend,
                              MachineDescription.encodeNat, hsuffix]⟩
              | done =>
                  exact ⟨0, suffix, by
                    simp [CodePrefixRecognizerStageCode,
                      MachineDescription.encodeNatAppend,
                      MachineDescription.encodeNat]⟩
              | blank =>
                  cases hstep with
                  | mk haction =>
                      simp [stageCodeDecoderMachine,
                        stageCodeDecoderTape, Tape.read] at haction
              | zero =>
                  cases hstep with
                  | mk haction =>
                      simp [stageCodeDecoderMachine,
                        stageCodeDecoderTape, Tape.read] at haction
              | one =>
                  cases hstep with
                  | mk haction =>
                      simp [stageCodeDecoderMachine,
                        stageCodeDecoderTape, Tape.read] at haction
              | moveLeft =>
                  cases hstep with
                  | mk haction =>
                      simp [stageCodeDecoderMachine,
                        stageCodeDecoderTape, Tape.read] at haction
              | moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [stageCodeDecoderMachine,
                        stageCodeDecoderTape, Tape.read] at haction

theorem stageCodeDecoderMachine_spec
    (tokens : Word MachineCodeSymbol) :
    TuringMachine.HaltsOnInput stageCodeDecoderMachine tokens <->
      exists stage : Nat,
      exists encoded : Word MachineCodeSymbol,
        tokens = CodePrefixRecognizerStageCode encoded stage := by
  constructor
  · intro h
    rcases
        (TuringMachine.halts_on_input_to_halts_on_input_in h) with
      ⟨steps, hsteps⟩
    have hfrom :
        TuringMachine.HaltsFromIn stageCodeDecoderMachine steps
          { state := StageCodeDecoderState.scan
            tape := stageCodeDecoderTape [] tokens } := by
      simpa [TuringMachine.HaltsOnInputIn, TuringMachine.initial,
        stageCodeDecoderMachine,
        stageCodeDecoderTape_nil_eq_input] using hsteps
    exact
      stageCodeDecoderMachine_haltsFromIn_only_encodeNatAppend
        (steps := steps) (leftRev := []) (rest := tokens) hfrom
  · intro h
    rcases h with ⟨stage, encoded, rfl⟩
    have hfrom :=
      stageCodeDecoderMachine_haltsFromIn_encodeNatAppend
        ([] : Word MachineCodeSymbol) stage encoded
    have hin :
        TuringMachine.HaltsOnInputIn stageCodeDecoderMachine
          (stage + 1) (CodePrefixRecognizerStageCode encoded stage) := by
      simpa [TuringMachine.HaltsOnInputIn, TuringMachine.initial,
        stageCodeDecoderMachine,
        stageCodeDecoderTape_nil_eq_input] using hfrom
    exact
      TuringMachine.halts_on_input_in_to_halts_on_input
        (n := stage + 1) hin

theorem stageCodeDecoderConstruction_scaffold :
    StageCodeDecoderConstruction :=
  ⟨StageCodeDecoderState,
    stageCodeDecoderMachine,
    stageCodeDecoderMachine_spec⟩

end Computability
end FoC
