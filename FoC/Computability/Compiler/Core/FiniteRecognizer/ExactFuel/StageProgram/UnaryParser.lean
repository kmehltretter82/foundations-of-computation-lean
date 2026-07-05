import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StageProgram.Spec

set_option doc.verso true

/-!
# Exact-fuel unary stage parser

Core finite machine for recognizing canonical unary fuel prefixes.  This is a
lower-level version of the stage-code parser used by Universal/Ranges, kept in
the exact-fuel core so later construction phases do not depend upward on that
workstream.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StageProgram

def UnaryParserSpec
    (parser : TuringMachine MachineCodeSymbol state) : Prop :=
  forall tokens : Word MachineCodeSymbol,
    TuringMachine.HaltsOnInput parser tokens <->
      exists fuel : Nat,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens = some (fuel, input)

def UnaryParserConstruction : Prop :=
  exists state : Type,
  exists parser : TuringMachine MachineCodeSymbol state,
    UnaryParserSpec parser

inductive UnaryParserState where
  | scan : UnaryParserState
  | halt : UnaryParserState
deriving DecidableEq

namespace UnaryParserState

def finite : Foundation.FiniteType UnaryParserState where
  elems := [scan, halt]
  complete := by
    intro state
    cases state <;> simp

end UnaryParserState

def unaryParserTape
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

theorem unaryParserTape_move_right
    (leftRev : Word MachineCodeSymbol)
    (symbol : MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol) :
    Tape.move Direction.right
        (Tape.write (some symbol)
          (unaryParserTape leftRev (symbol :: suffix))) =
      unaryParserTape (symbol :: leftRev) suffix := by
  cases suffix <;>
    simp [unaryParserTape, Tape.move, Tape.moveRight,
      Tape.write]

theorem unaryParserTape_nil_eq_input
    (tokens : Word MachineCodeSymbol) :
    unaryParserTape [] tokens = Tape.input tokens := by
  cases tokens <;> rfl

def unaryParserMachine :
    TuringMachine MachineCodeSymbol UnaryParserState where
  start := UnaryParserState.scan
  halt := UnaryParserState.halt
  transition := fun state cell =>
    match state, cell with
    | UnaryParserState.scan, some MachineCodeSymbol.tick =>
        some
          (some MachineCodeSymbol.tick, Direction.right,
            UnaryParserState.scan)
    | UnaryParserState.scan, some MachineCodeSymbol.done =>
        some
          (some MachineCodeSymbol.done, Direction.right,
            UnaryParserState.halt)
    | _, _ => none
  statesFinite := UnaryParserState.finite

private theorem unaryParserMachine_step_tick
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step unaryParserMachine
      { state := UnaryParserState.scan
        tape :=
          unaryParserTape leftRev
            (MachineCodeSymbol.tick :: suffix) }
      { state := UnaryParserState.scan
        tape :=
          unaryParserTape
            (MachineCodeSymbol.tick :: leftRev) suffix } := by
  rw [← unaryParserTape_move_right leftRev
    MachineCodeSymbol.tick suffix]
  exact TuringMachine.Step.mk (by
    simp [unaryParserMachine, unaryParserTape, Tape.read])

private theorem unaryParserMachine_step_done
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step unaryParserMachine
      { state := UnaryParserState.scan
        tape :=
          unaryParserTape leftRev
            (MachineCodeSymbol.done :: suffix) }
      { state := UnaryParserState.halt
        tape :=
          unaryParserTape
            (MachineCodeSymbol.done :: leftRev) suffix } := by
  rw [← unaryParserTape_move_right leftRev
    MachineCodeSymbol.done suffix]
  exact TuringMachine.Step.mk (by
    simp [unaryParserMachine, unaryParserTape, Tape.read])

theorem unaryParserMachine_haltsFromIn_stageCode
    (leftRev : Word MachineCodeSymbol)
    (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.HaltsFromIn unaryParserMachine
      (fuel + 1)
      { state := UnaryParserState.scan
        tape := unaryParserTape leftRev (stageCode input fuel) } := by
  induction fuel generalizing leftRev with
  | zero =>
      refine
        ⟨{ state := UnaryParserState.halt,
            tape :=
              unaryParserTape
                (MachineCodeSymbol.done :: leftRev) input },
          ?_, rfl⟩
      exact TuringMachine.ComputesIn.succ
        (by
          simpa [stageCode, MachineDescription.encodeNatAppend,
            MachineDescription.encodeNat] using
            unaryParserMachine_step_done leftRev input)
        (TuringMachine.ComputesIn.zero _)
  | succ fuel ih =>
      rcases ih (MachineCodeSymbol.tick :: leftRev) with
        ⟨final, hcomp, hhalt⟩
      refine ⟨final, ?_, hhalt⟩
      exact TuringMachine.ComputesIn.succ
        (by
          simpa [stageCode, MachineDescription.encodeNatAppend,
            MachineDescription.encodeNat] using
            unaryParserMachine_step_tick leftRev
              (stageCode input fuel))
        hcomp

theorem unaryParserMachine_haltsFromIn_only_stageCode
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn unaryParserMachine steps
        { state := UnaryParserState.scan
          tape := unaryParserTape leftRev rest }) :
    exists fuel : Nat,
    exists input : Word MachineCodeSymbol,
      rest = stageCode input fuel := by
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
                  simp [unaryParserMachine,
                    unaryParserTape, Tape.read] at haction
          | cons symbol suffix =>
              cases symbol with
              | header =>
                  cases hstep with
                  | mk haction =>
                      simp [unaryParserMachine,
                        unaryParserTape, Tape.read] at haction
              | transition =>
                  cases hstep with
                  | mk haction =>
                      simp [unaryParserMachine,
                        unaryParserTape, Tape.read] at haction
              | tick =>
                  cases hstep with
                  | mk haction =>
                      rename_i write dir nextState
                      cases write with
                      | none =>
                          simp [unaryParserMachine,
                            unaryParserTape, Tape.read] at haction
                      | some writeSymbol =>
                          cases writeSymbol <;>
                            cases dir <;>
                            cases nextState <;>
                              simp [unaryParserMachine,
                                unaryParserTape, Tape.read] at haction
                          have htail :
                              TuringMachine.HaltsFromIn
                                unaryParserMachine steps
                                { state := UnaryParserState.scan
                                  tape :=
                                    unaryParserTape
                                      (MachineCodeSymbol.tick :: leftRev)
                                      suffix } := by
                            refine ⟨final, ?_, hhalt⟩
                            cases suffix <;>
                              simpa [unaryParserMachine,
                                unaryParserTape,
                                unaryParserTape_move_right,
                                Tape.write, Tape.move, Tape.moveRight]
                                using hrest
                          rcases ih htail with ⟨fuel, input, hsuffix⟩
                          exact ⟨fuel + 1, input, by
                            simp [stageCode,
                              MachineDescription.encodeNatAppend,
                              MachineDescription.encodeNat, hsuffix]⟩
              | done =>
                  exact ⟨0, suffix, by
                    simp [stageCode, MachineDescription.encodeNatAppend,
                      MachineDescription.encodeNat]⟩
              | blank =>
                  cases hstep with
                  | mk haction =>
                      simp [unaryParserMachine,
                        unaryParserTape, Tape.read] at haction
              | zero =>
                  cases hstep with
                  | mk haction =>
                      simp [unaryParserMachine,
                        unaryParserTape, Tape.read] at haction
              | one =>
                  cases hstep with
                  | mk haction =>
                      simp [unaryParserMachine,
                        unaryParserTape, Tape.read] at haction
              | moveLeft =>
                  cases hstep with
                  | mk haction =>
                      simp [unaryParserMachine,
                        unaryParserTape, Tape.read] at haction
              | moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [unaryParserMachine,
                        unaryParserTape, Tape.read] at haction

theorem unaryParserMachine_haltsFromIn_only_decodeNat
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn unaryParserMachine steps
        { state := UnaryParserState.scan
          tape := unaryParserTape leftRev rest }) :
    exists fuel : Nat,
    exists input : Word MachineCodeSymbol,
      MachineDescription.decodeNat rest = some (fuel, input) := by
  rcases unaryParserMachine_haltsFromIn_only_stageCode h with
    ⟨fuel, input, hrest⟩
  exact ⟨fuel, input, by
    rw [hrest]
    exact stageCode_decodeNat input fuel⟩

theorem unaryParserMachine_spec :
    UnaryParserSpec unaryParserMachine := by
  intro tokens
  constructor
  · intro h
    rcases
        (TuringMachine.halts_on_input_to_halts_on_input_in h) with
      ⟨steps, hsteps⟩
    have hfrom :
        TuringMachine.HaltsFromIn unaryParserMachine steps
          { state := UnaryParserState.scan
            tape := unaryParserTape [] tokens } := by
      simpa [TuringMachine.HaltsOnInputIn, TuringMachine.initial,
        unaryParserMachine,
        unaryParserTape_nil_eq_input] using hsteps
    exact unaryParserMachine_haltsFromIn_only_decodeNat hfrom
  · intro h
    rcases h with ⟨fuel, input, hdecode⟩
    have htokens : tokens = stageCode input fuel :=
      stageCode_eq_of_decodeNat hdecode
    subst tokens
    have hfrom :=
      unaryParserMachine_haltsFromIn_stageCode
        ([] : Word MachineCodeSymbol) fuel input
    have hin :
        TuringMachine.HaltsOnInputIn unaryParserMachine
          (fuel + 1) (stageCode input fuel) := by
      simpa [TuringMachine.HaltsOnInputIn, TuringMachine.initial,
        unaryParserMachine,
        unaryParserTape_nil_eq_input] using hfrom
    exact
      TuringMachine.halts_on_input_in_to_halts_on_input
        (n := fuel + 1) hin

theorem unaryParserConstruction :
    UnaryParserConstruction :=
  ⟨UnaryParserState, unaryParserMachine, unaryParserMachine_spec⟩

end StageProgram
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
