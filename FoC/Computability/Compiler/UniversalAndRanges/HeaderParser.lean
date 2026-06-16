import FoC.Computability.Compiler.UniversalAndRanges.Basic

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

/-!
**Section 5.3 finite-source scaffold.**  The universal-machine construction
target is the prefix version.  The finite-source scaffold below is the active
deferred fixed-alphabet prefix recognizer machine target.  Row coverage over all
recursively enumerable code-symbol languages still requires an explicit
encoded-input description compiler, as in
{name}`codeUniversalPrefixRowsCoverConstruction_of_finiteSourceCloseout`.
-/

def HeaderFieldsParserConstruction : Prop :=
  exists state : Type,
  exists parser : TuringMachine MachineCodeSymbol state,
    forall tokens : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput parser tokens <->
        exists stateCount start halt transitionCount : Nat,
        exists rest : Word MachineCodeSymbol,
          tokens =
            MachineCodeSymbol.header ::
            MachineDescription.encodeNatAppend stateCount
              (MachineDescription.encodeNatAppend start
                (MachineDescription.encodeNatAppend halt
                  (MachineDescription.encodeNatAppend transitionCount
                    rest)))

inductive HeaderFieldsParserState where
  | needHeader : HeaderFieldsParserState
  | stateCount : HeaderFieldsParserState
  | startField : HeaderFieldsParserState
  | haltField : HeaderFieldsParserState
  | transitionCount : HeaderFieldsParserState
  | done : HeaderFieldsParserState
deriving DecidableEq

namespace HeaderFieldsParserState

def finite : Foundation.FiniteType
    HeaderFieldsParserState where
  elems :=
    [needHeader, stateCount, startField, haltField, transitionCount, done]
  complete := by
    intro state
    cases state <;> simp

end HeaderFieldsParserState

def headerFieldsParserTape
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

theorem headerFieldsParserTape_move_right
    (leftRev : Word MachineCodeSymbol)
    (symbol : MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol) :
    Tape.move Direction.right
        (Tape.write (some symbol)
          (headerFieldsParserTape leftRev
            (symbol :: suffix))) =
      headerFieldsParserTape
        (symbol :: leftRev) suffix := by
  cases suffix <;>
    simp [headerFieldsParserTape, Tape.move,
      Tape.moveRight, Tape.write]

theorem headerFieldsParserTape_nil_eq_input
    (tokens : Word MachineCodeSymbol) :
    headerFieldsParserTape [] tokens =
      Tape.input tokens := by
  cases tokens <;> rfl

def headerFieldsParserMachine :
    TuringMachine MachineCodeSymbol
      HeaderFieldsParserState where
  start := HeaderFieldsParserState.needHeader
  halt := HeaderFieldsParserState.done
  transition := fun state cell =>
    match state, cell with
    | HeaderFieldsParserState.needHeader,
        some MachineCodeSymbol.header =>
        some
          (some MachineCodeSymbol.header, Direction.right,
            HeaderFieldsParserState.stateCount)
    | HeaderFieldsParserState.stateCount,
        some MachineCodeSymbol.tick =>
        some
          (some MachineCodeSymbol.tick, Direction.right,
            HeaderFieldsParserState.stateCount)
    | HeaderFieldsParserState.stateCount,
        some MachineCodeSymbol.done =>
        some
          (some MachineCodeSymbol.done, Direction.right,
            HeaderFieldsParserState.startField)
    | HeaderFieldsParserState.startField,
        some MachineCodeSymbol.tick =>
        some
          (some MachineCodeSymbol.tick, Direction.right,
            HeaderFieldsParserState.startField)
    | HeaderFieldsParserState.startField,
        some MachineCodeSymbol.done =>
        some
          (some MachineCodeSymbol.done, Direction.right,
            HeaderFieldsParserState.haltField)
    | HeaderFieldsParserState.haltField,
        some MachineCodeSymbol.tick =>
        some
          (some MachineCodeSymbol.tick, Direction.right,
            HeaderFieldsParserState.haltField)
    | HeaderFieldsParserState.haltField,
        some MachineCodeSymbol.done =>
        some
          (some MachineCodeSymbol.done, Direction.right,
            HeaderFieldsParserState.transitionCount)
    | HeaderFieldsParserState.transitionCount,
        some MachineCodeSymbol.tick =>
        some
          (some MachineCodeSymbol.tick, Direction.right,
            HeaderFieldsParserState.transitionCount)
    | HeaderFieldsParserState.transitionCount,
        some MachineCodeSymbol.done =>
        some
          (some MachineCodeSymbol.done, Direction.right,
            HeaderFieldsParserState.done)
    | _, _ => none
  statesFinite := HeaderFieldsParserState.finite

theorem headerFieldsParserMachine_step_header
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step headerFieldsParserMachine
      { state := HeaderFieldsParserState.needHeader
        tape :=
          headerFieldsParserTape leftRev
            (MachineCodeSymbol.header :: suffix) }
      { state := HeaderFieldsParserState.stateCount
        tape :=
          headerFieldsParserTape
            (MachineCodeSymbol.header :: leftRev) suffix } := by
  rw [← headerFieldsParserTape_move_right leftRev
    MachineCodeSymbol.header suffix]
  exact TuringMachine.Step.mk (by
    simp [headerFieldsParserMachine,
      headerFieldsParserTape, Tape.read])

theorem headerFieldsParserMachine_step_tick_stateCount
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step headerFieldsParserMachine
      { state := HeaderFieldsParserState.stateCount
        tape :=
          headerFieldsParserTape leftRev
            (MachineCodeSymbol.tick :: suffix) }
      { state := HeaderFieldsParserState.stateCount
        tape :=
          headerFieldsParserTape
            (MachineCodeSymbol.tick :: leftRev) suffix } := by
  rw [← headerFieldsParserTape_move_right leftRev
    MachineCodeSymbol.tick suffix]
  exact TuringMachine.Step.mk (by
    simp [headerFieldsParserMachine,
      headerFieldsParserTape, Tape.read])

theorem headerFieldsParserMachine_step_done_stateCount
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step headerFieldsParserMachine
      { state := HeaderFieldsParserState.stateCount
        tape :=
          headerFieldsParserTape leftRev
            (MachineCodeSymbol.done :: suffix) }
      { state := HeaderFieldsParserState.startField
        tape :=
          headerFieldsParserTape
            (MachineCodeSymbol.done :: leftRev) suffix } := by
  rw [← headerFieldsParserTape_move_right leftRev
    MachineCodeSymbol.done suffix]
  exact TuringMachine.Step.mk (by
    simp [headerFieldsParserMachine,
      headerFieldsParserTape, Tape.read])

theorem headerFieldsParserMachine_step_tick_startField
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step headerFieldsParserMachine
      { state := HeaderFieldsParserState.startField
        tape :=
          headerFieldsParserTape leftRev
            (MachineCodeSymbol.tick :: suffix) }
      { state := HeaderFieldsParserState.startField
        tape :=
          headerFieldsParserTape
            (MachineCodeSymbol.tick :: leftRev) suffix } := by
  rw [← headerFieldsParserTape_move_right leftRev
    MachineCodeSymbol.tick suffix]
  exact TuringMachine.Step.mk (by
    simp [headerFieldsParserMachine,
      headerFieldsParserTape, Tape.read])

theorem headerFieldsParserMachine_step_done_startField
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step headerFieldsParserMachine
      { state := HeaderFieldsParserState.startField
        tape :=
          headerFieldsParserTape leftRev
            (MachineCodeSymbol.done :: suffix) }
      { state := HeaderFieldsParserState.haltField
        tape :=
          headerFieldsParserTape
            (MachineCodeSymbol.done :: leftRev) suffix } := by
  rw [← headerFieldsParserTape_move_right leftRev
    MachineCodeSymbol.done suffix]
  exact TuringMachine.Step.mk (by
    simp [headerFieldsParserMachine,
      headerFieldsParserTape, Tape.read])

theorem headerFieldsParserMachine_step_tick_haltField
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step headerFieldsParserMachine
      { state := HeaderFieldsParserState.haltField
        tape :=
          headerFieldsParserTape leftRev
            (MachineCodeSymbol.tick :: suffix) }
      { state := HeaderFieldsParserState.haltField
        tape :=
          headerFieldsParserTape
            (MachineCodeSymbol.tick :: leftRev) suffix } := by
  rw [← headerFieldsParserTape_move_right leftRev
    MachineCodeSymbol.tick suffix]
  exact TuringMachine.Step.mk (by
    simp [headerFieldsParserMachine,
      headerFieldsParserTape, Tape.read])

theorem headerFieldsParserMachine_step_done_haltField
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step headerFieldsParserMachine
      { state := HeaderFieldsParserState.haltField
        tape :=
          headerFieldsParserTape leftRev
            (MachineCodeSymbol.done :: suffix) }
      { state := HeaderFieldsParserState.transitionCount
        tape :=
          headerFieldsParserTape
            (MachineCodeSymbol.done :: leftRev) suffix } := by
  rw [← headerFieldsParserTape_move_right leftRev
    MachineCodeSymbol.done suffix]
  exact TuringMachine.Step.mk (by
    simp [headerFieldsParserMachine,
      headerFieldsParserTape, Tape.read])

theorem headerFieldsParserMachine_step_tick_transitionCount
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step headerFieldsParserMachine
      { state := HeaderFieldsParserState.transitionCount
        tape :=
          headerFieldsParserTape leftRev
            (MachineCodeSymbol.tick :: suffix) }
      { state := HeaderFieldsParserState.transitionCount
        tape :=
          headerFieldsParserTape
            (MachineCodeSymbol.tick :: leftRev) suffix } := by
  rw [← headerFieldsParserTape_move_right leftRev
    MachineCodeSymbol.tick suffix]
  exact TuringMachine.Step.mk (by
    simp [headerFieldsParserMachine,
      headerFieldsParserTape, Tape.read])

theorem headerFieldsParserMachine_step_done_transitionCount
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step headerFieldsParserMachine
      { state := HeaderFieldsParserState.transitionCount
        tape :=
          headerFieldsParserTape leftRev
            (MachineCodeSymbol.done :: suffix) }
      { state := HeaderFieldsParserState.done
        tape :=
          headerFieldsParserTape
            (MachineCodeSymbol.done :: leftRev) suffix } := by
  rw [← headerFieldsParserTape_move_right leftRev
    MachineCodeSymbol.done suffix]
  exact TuringMachine.Step.mk (by
    simp [headerFieldsParserMachine,
      headerFieldsParserTape, Tape.read])

theorem headerFieldsParserMachine_computesIn_nat
    {current next : HeaderFieldsParserState}
    (htick :
      forall leftRev suffix : Word MachineCodeSymbol,
        TuringMachine.Step headerFieldsParserMachine
          { state := current
            tape :=
              headerFieldsParserTape leftRev
                (MachineCodeSymbol.tick :: suffix) }
          { state := current
            tape :=
              headerFieldsParserTape
                (MachineCodeSymbol.tick :: leftRev) suffix })
    (hdone :
      forall leftRev suffix : Word MachineCodeSymbol,
        TuringMachine.Step headerFieldsParserMachine
          { state := current
            tape :=
              headerFieldsParserTape leftRev
                (MachineCodeSymbol.done :: suffix) }
          { state := next
            tape :=
              headerFieldsParserTape
                (MachineCodeSymbol.done :: leftRev) suffix })
    (leftRev : Word MachineCodeSymbol) (n : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.ComputesIn headerFieldsParserMachine
      (n + 1)
      { state := current
        tape :=
          headerFieldsParserTape leftRev
            (MachineDescription.encodeNatAppend n suffix) }
      { state := next
        tape :=
          headerFieldsParserTape
            (List.append (MachineDescription.encodeNat n).reverse leftRev)
            suffix } := by
  induction n generalizing leftRev with
  | zero =>
      simpa [MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat] using
        TuringMachine.ComputesIn.succ
          (hdone leftRev suffix)
          (TuringMachine.ComputesIn.zero _)
  | succ n ih =>
      have htail := ih (MachineCodeSymbol.tick :: leftRev)
      have hcomp :
          TuringMachine.ComputesIn
            headerFieldsParserMachine
            (n + 1 + 1)
            { state := current
              tape :=
                headerFieldsParserTape leftRev
                  (MachineCodeSymbol.tick ::
                    MachineDescription.encodeNatAppend n suffix) }
            { state := next
              tape :=
                headerFieldsParserTape
                  (List.append (MachineDescription.encodeNat n).reverse
                    (MachineCodeSymbol.tick :: leftRev))
                  suffix } :=
        TuringMachine.ComputesIn.succ
          (htick leftRev (MachineDescription.encodeNatAppend n suffix))
          htail
      simpa [MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat, List.append_assoc] using hcomp

theorem headerFieldsParserMachine_haltsFromIn_only_transitionCount
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn
        headerFieldsParserMachine steps
        { state :=
            HeaderFieldsParserState.transitionCount
          tape :=
            headerFieldsParserTape leftRev rest }) :
    exists transitionCount : Nat,
    exists suffix : Word MachineCodeSymbol,
      rest = MachineDescription.encodeNatAppend transitionCount suffix := by
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
                  simp [headerFieldsParserMachine,
                    headerFieldsParserTape, Tape.read]
                    at haction
          | cons symbol suffix =>
              cases symbol with
              | header =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | transition =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | tick =>
                  cases hstep with
                  | mk haction =>
                      rename_i write dir nextState
                      cases write with
                      | none =>
                          simp [headerFieldsParserMachine,
                            headerFieldsParserTape,
                            Tape.read] at haction
                      | some writeSymbol =>
                          cases writeSymbol <;>
                            cases dir <;>
                            cases nextState <;>
                              simp [headerFieldsParserMachine,
                                headerFieldsParserTape,
                                Tape.read] at haction
                          have htail :
                              TuringMachine.HaltsFromIn
                                headerFieldsParserMachine
                                steps
                                { state :=
                                    HeaderFieldsParserState.transitionCount
                                  tape :=
                                    headerFieldsParserTape
                                      (MachineCodeSymbol.tick :: leftRev)
                                      suffix } := by
                            refine ⟨final, ?_, hhalt⟩
                            cases suffix <;>
                              simpa [headerFieldsParserMachine,
                                headerFieldsParserTape,
                                headerFieldsParserTape_move_right,
                                Tape.write, Tape.move, Tape.moveRight]
                                using hrest
                          rcases ih htail with
                            ⟨transitionCount, parsedSuffix, hsuffix⟩
                          exact ⟨transitionCount + 1, parsedSuffix, by
                            simp [MachineDescription.encodeNatAppend,
                              MachineDescription.encodeNat, hsuffix]⟩
              | done =>
                  exact ⟨0, suffix, by
                    simp [MachineDescription.encodeNatAppend,
                      MachineDescription.encodeNat]⟩
              | blank =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | zero =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | one =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | moveLeft =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction

theorem headerFieldsParserMachine_haltsFromIn_only_haltField
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn
        headerFieldsParserMachine steps
        { state := HeaderFieldsParserState.haltField
          tape :=
            headerFieldsParserTape leftRev rest }) :
    exists halt transitionCount : Nat,
    exists suffix : Word MachineCodeSymbol,
      rest =
        MachineDescription.encodeNatAppend halt
          (MachineDescription.encodeNatAppend transitionCount suffix) := by
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
                  simp [headerFieldsParserMachine,
                    headerFieldsParserTape, Tape.read]
                    at haction
          | cons symbol suffix =>
              cases symbol with
              | header =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | transition =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | tick =>
                  cases hstep with
                  | mk haction =>
                      rename_i write dir nextState
                      cases write with
                      | none =>
                          simp [headerFieldsParserMachine,
                            headerFieldsParserTape,
                            Tape.read] at haction
                      | some writeSymbol =>
                          cases writeSymbol <;>
                            cases dir <;>
                            cases nextState <;>
                              simp [headerFieldsParserMachine,
                                headerFieldsParserTape,
                                Tape.read] at haction
                          have htail :
                              TuringMachine.HaltsFromIn
                                headerFieldsParserMachine
                                steps
                                { state :=
                                    HeaderFieldsParserState.haltField
                                  tape :=
                                    headerFieldsParserTape
                                      (MachineCodeSymbol.tick :: leftRev)
                                      suffix } := by
                            refine ⟨final, ?_, hhalt⟩
                            cases suffix <;>
                              simpa [headerFieldsParserMachine,
                                headerFieldsParserTape,
                                headerFieldsParserTape_move_right,
                                Tape.write, Tape.move, Tape.moveRight]
                                using hrest
                          rcases ih htail with
                            ⟨halt, transitionCount, parsedSuffix,
                              hsuffix⟩
                          exact
                            ⟨halt + 1, transitionCount, parsedSuffix, by
                              simp [MachineDescription.encodeNatAppend,
                                MachineDescription.encodeNat, hsuffix]⟩
              | done =>
                  cases hstep with
                  | mk haction =>
                      rename_i write dir nextState
                      cases write with
                      | none =>
                          simp [headerFieldsParserMachine,
                            headerFieldsParserTape,
                            Tape.read] at haction
                      | some writeSymbol =>
                          cases writeSymbol <;>
                            cases dir <;>
                            cases nextState <;>
                              simp [headerFieldsParserMachine,
                                headerFieldsParserTape,
                                Tape.read] at haction
                          have htail :
                              TuringMachine.HaltsFromIn
                                headerFieldsParserMachine
                                steps
                                { state :=
                                    HeaderFieldsParserState.transitionCount
                                  tape :=
                                    headerFieldsParserTape
                                      (MachineCodeSymbol.done :: leftRev)
                                      suffix } := by
                            refine ⟨final, ?_, hhalt⟩
                            cases suffix <;>
                              simpa [headerFieldsParserMachine,
                                headerFieldsParserTape,
                                headerFieldsParserTape_move_right,
                                Tape.write, Tape.move, Tape.moveRight]
                                using hrest
                          rcases
                            headerFieldsParserMachine_haltsFromIn_only_transitionCount
                              htail with
                            ⟨transitionCount, parsedSuffix, hsuffix⟩
                          exact ⟨0, transitionCount, parsedSuffix, by
                            simp [MachineDescription.encodeNatAppend,
                              MachineDescription.encodeNat, hsuffix]⟩
              | blank =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | zero =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | one =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | moveLeft =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction

theorem headerFieldsParserMachine_haltsFromIn_only_startField
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn
        headerFieldsParserMachine steps
        { state := HeaderFieldsParserState.startField
          tape :=
            headerFieldsParserTape leftRev rest }) :
    exists start halt transitionCount : Nat,
    exists suffix : Word MachineCodeSymbol,
      rest =
        MachineDescription.encodeNatAppend start
          (MachineDescription.encodeNatAppend halt
            (MachineDescription.encodeNatAppend transitionCount suffix)) := by
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
                  simp [headerFieldsParserMachine,
                    headerFieldsParserTape, Tape.read]
                    at haction
          | cons symbol suffix =>
              cases symbol with
              | header =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | transition =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | tick =>
                  cases hstep with
                  | mk haction =>
                      rename_i write dir nextState
                      cases write with
                      | none =>
                          simp [headerFieldsParserMachine,
                            headerFieldsParserTape,
                            Tape.read] at haction
                      | some writeSymbol =>
                          cases writeSymbol <;>
                            cases dir <;>
                            cases nextState <;>
                              simp [headerFieldsParserMachine,
                                headerFieldsParserTape,
                                Tape.read] at haction
                          have htail :
                              TuringMachine.HaltsFromIn
                                headerFieldsParserMachine
                                steps
                                { state :=
                                    HeaderFieldsParserState.startField
                                  tape :=
                                    headerFieldsParserTape
                                      (MachineCodeSymbol.tick :: leftRev)
                                      suffix } := by
                            refine ⟨final, ?_, hhalt⟩
                            cases suffix <;>
                              simpa [headerFieldsParserMachine,
                                headerFieldsParserTape,
                                headerFieldsParserTape_move_right,
                                Tape.write, Tape.move, Tape.moveRight]
                                using hrest
                          rcases ih htail with
                            ⟨start, halt, transitionCount, parsedSuffix,
                              hsuffix⟩
                          exact
                            ⟨start + 1, halt, transitionCount,
                              parsedSuffix, by
                              simp [MachineDescription.encodeNatAppend,
                                MachineDescription.encodeNat, hsuffix]⟩
              | done =>
                  cases hstep with
                  | mk haction =>
                      rename_i write dir nextState
                      cases write with
                      | none =>
                          simp [headerFieldsParserMachine,
                            headerFieldsParserTape,
                            Tape.read] at haction
                      | some writeSymbol =>
                          cases writeSymbol <;>
                            cases dir <;>
                            cases nextState <;>
                              simp [headerFieldsParserMachine,
                                headerFieldsParserTape,
                                Tape.read] at haction
                          have htail :
                              TuringMachine.HaltsFromIn
                                headerFieldsParserMachine
                                steps
                                { state :=
                                    HeaderFieldsParserState.haltField
                                  tape :=
                                    headerFieldsParserTape
                                      (MachineCodeSymbol.done :: leftRev)
                                      suffix } := by
                            refine ⟨final, ?_, hhalt⟩
                            cases suffix <;>
                              simpa [headerFieldsParserMachine,
                                headerFieldsParserTape,
                                headerFieldsParserTape_move_right,
                                Tape.write, Tape.move, Tape.moveRight]
                                using hrest
                          rcases
                            headerFieldsParserMachine_haltsFromIn_only_haltField
                              htail with
                            ⟨halt, transitionCount, parsedSuffix,
                              hsuffix⟩
                          exact ⟨0, halt, transitionCount, parsedSuffix, by
                            simp [MachineDescription.encodeNatAppend,
                              MachineDescription.encodeNat, hsuffix]⟩
              | blank =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | zero =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | one =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | moveLeft =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction

theorem headerFieldsParserMachine_haltsFromIn_only_stateCount
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn
        headerFieldsParserMachine steps
        { state := HeaderFieldsParserState.stateCount
          tape :=
            headerFieldsParserTape leftRev rest }) :
    exists stateCount start halt transitionCount : Nat,
    exists suffix : Word MachineCodeSymbol,
      rest =
        MachineDescription.encodeNatAppend stateCount
          (MachineDescription.encodeNatAppend start
            (MachineDescription.encodeNatAppend halt
              (MachineDescription.encodeNatAppend transitionCount suffix))) := by
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
                  simp [headerFieldsParserMachine,
                    headerFieldsParserTape, Tape.read]
                    at haction
          | cons symbol suffix =>
              cases symbol with
              | header =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | transition =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | tick =>
                  cases hstep with
                  | mk haction =>
                      rename_i write dir nextState
                      cases write with
                      | none =>
                          simp [headerFieldsParserMachine,
                            headerFieldsParserTape,
                            Tape.read] at haction
                      | some writeSymbol =>
                          cases writeSymbol <;>
                            cases dir <;>
                            cases nextState <;>
                              simp [headerFieldsParserMachine,
                                headerFieldsParserTape,
                                Tape.read] at haction
                          have htail :
                              TuringMachine.HaltsFromIn
                                headerFieldsParserMachine
                                steps
                                { state :=
                                    HeaderFieldsParserState.stateCount
                                  tape :=
                                    headerFieldsParserTape
                                      (MachineCodeSymbol.tick :: leftRev)
                                      suffix } := by
                            refine ⟨final, ?_, hhalt⟩
                            cases suffix <;>
                              simpa [headerFieldsParserMachine,
                                headerFieldsParserTape,
                                headerFieldsParserTape_move_right,
                                Tape.write, Tape.move, Tape.moveRight]
                                using hrest
                          rcases ih htail with
                            ⟨stateCount, start, halt, transitionCount,
                              parsedSuffix, hsuffix⟩
                          exact
                            ⟨stateCount + 1, start, halt, transitionCount,
                              parsedSuffix, by
                              simp [MachineDescription.encodeNatAppend,
                                MachineDescription.encodeNat, hsuffix]⟩
              | done =>
                  cases hstep with
                  | mk haction =>
                      rename_i write dir nextState
                      cases write with
                      | none =>
                          simp [headerFieldsParserMachine,
                            headerFieldsParserTape,
                            Tape.read] at haction
                      | some writeSymbol =>
                          cases writeSymbol <;>
                            cases dir <;>
                            cases nextState <;>
                              simp [headerFieldsParserMachine,
                                headerFieldsParserTape,
                                Tape.read] at haction
                          have htail :
                              TuringMachine.HaltsFromIn
                                headerFieldsParserMachine
                                steps
                                { state :=
                                    HeaderFieldsParserState.startField
                                  tape :=
                                    headerFieldsParserTape
                                      (MachineCodeSymbol.done :: leftRev)
                                      suffix } := by
                            refine ⟨final, ?_, hhalt⟩
                            cases suffix <;>
                              simpa [headerFieldsParserMachine,
                                headerFieldsParserTape,
                                headerFieldsParserTape_move_right,
                                Tape.write, Tape.move, Tape.moveRight]
                                using hrest
                          rcases
                            headerFieldsParserMachine_haltsFromIn_only_startField
                              htail with
                            ⟨start, halt, transitionCount, parsedSuffix,
                              hsuffix⟩
                          exact
                            ⟨0, start, halt, transitionCount,
                              parsedSuffix, by
                              simp [MachineDescription.encodeNatAppend,
                                MachineDescription.encodeNat, hsuffix]⟩
              | blank =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | zero =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | one =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | moveLeft =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction

theorem headerFieldsParserMachine_haltsFromIn_only_header
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn
        headerFieldsParserMachine steps
        { state := HeaderFieldsParserState.needHeader
          tape :=
            headerFieldsParserTape leftRev rest }) :
    exists stateCount start halt transitionCount : Nat,
    exists suffix : Word MachineCodeSymbol,
      rest =
        MachineCodeSymbol.header ::
          MachineDescription.encodeNatAppend stateCount
            (MachineDescription.encodeNatAppend start
              (MachineDescription.encodeNatAppend halt
                (MachineDescription.encodeNatAppend transitionCount
                  suffix))) := by
  cases steps with
  | zero =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp
      cases hhalt
  | succ steps =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp with
      | succ hstep hrest =>
          cases rest with
          | nil =>
              cases hstep with
              | mk haction =>
                  simp [headerFieldsParserMachine,
                    headerFieldsParserTape, Tape.read]
                    at haction
          | cons symbol suffix =>
              cases symbol with
              | header =>
                  cases hstep with
                  | mk haction =>
                      rename_i write dir nextState
                      cases write with
                      | none =>
                          simp [headerFieldsParserMachine,
                            headerFieldsParserTape,
                            Tape.read] at haction
                      | some writeSymbol =>
                          cases writeSymbol <;>
                            cases dir <;>
                            cases nextState <;>
                              simp [headerFieldsParserMachine,
                                headerFieldsParserTape,
                                Tape.read] at haction
                          have htail :
                              TuringMachine.HaltsFromIn
                                headerFieldsParserMachine
                                steps
                                { state :=
                                    HeaderFieldsParserState.stateCount
                                  tape :=
                                    headerFieldsParserTape
                                      (MachineCodeSymbol.header :: leftRev)
                                      suffix } := by
                            refine ⟨final, ?_, hhalt⟩
                            cases suffix <;>
                              simpa [headerFieldsParserMachine,
                                headerFieldsParserTape,
                                headerFieldsParserTape_move_right,
                                Tape.write, Tape.move, Tape.moveRight]
                                using hrest
                          rcases
                            headerFieldsParserMachine_haltsFromIn_only_stateCount
                              htail with
                            ⟨stateCount, start, halt, transitionCount,
                              parsedSuffix, hsuffix⟩
                          exact
                            ⟨stateCount, start, halt, transitionCount,
                              parsedSuffix, by simp [hsuffix]⟩
              | transition =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | tick =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | done =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | blank =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | zero =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | one =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | moveLeft =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction
              | moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [headerFieldsParserMachine,
                        headerFieldsParserTape,
                        Tape.read] at haction


end Computability
end FoC
