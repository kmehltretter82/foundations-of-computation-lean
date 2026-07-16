import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.Stack.Iteration
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.FinalCompare
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.NoMatch.Exhausted
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Dispatch.NeighborProbe

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.FinalGateMaterializer

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep.RuntimeKeySingleKeyRepair
open FiniteRecognizer.Interpreter.LoopRestagingAudit
open FiniteRecognizer.Interpreter.StackIteration

/-! `false` carries a unary `tick`; `true` carries unary `done`. -/
def tokenSymbol : Bool -> MachineCodeSymbol
  | false => MachineCodeSymbol.tick
  | true => MachineCodeSymbol.done

def firstToken : Nat -> Bool
  | 0 => true
  | _ + 1 => false

def tokenTail (value : Nat) : Word MachineCodeSymbol :=
  match value with
  | 0 => []
  | rest + 1 => MachineDescription.encodeNat rest

theorem encodeNat_eq_firstToken_cons_tail (value : Nat) :
    MachineDescription.encodeNat value =
      tokenSymbol (firstToken value) :: tokenTail value := by
  cases value <;> rfl
  done

namespace HaltMarker

inductive Control where
  | enter
  | ready (token : Bool)
  | halt
deriving DecidableEq

namespace Control

def elems : List Control := [.enter, .ready false, .ready true, .halt]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | enter => simp [elems]
    | ready token => cases token <;> simp [elems]
    | halt => simp [elems]

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .enter, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.moveRight, Direction.left, .ready false)
  | .enter, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.moveRight, Direction.left, .ready true)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .enter
  halt := .halt
  transition := transition
  statesFinite := Control.finite

def sourceConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (value : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .enter
  tape := SerializedShift.cursorTape baseLeftRev
    (MachineDescription.encodeNatAppend value suffix)

def targetConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (value : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .ready (firstToken value)
  tape := Tape.move Direction.left
    (SerializedShift.cursorTape baseLeftRev
      (MachineCodeSymbol.moveRight ::
        List.append (tokenTail value) suffix))

theorem run_exact
    (baseLeftRev : Word MachineCodeSymbol)
    (value : Nat)
    (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? 1
        (sourceConfig baseLeftRev value suffix) =
      some (targetConfig baseLeftRev value suffix) := by
  rw [TuringMachine.runConfigExact?]
  cases value <;> cases baseLeftRev <;> rfl
  done

end HaltMarker

namespace PrefixBuilder

inductive Control where
  | start (haltToken : Bool)
  | shift (haltToken targetToken : Bool)
  | blank (haltToken : Bool)
  | separator (haltToken : Bool)
  | destination (haltToken : Bool)
  | ready (haltToken : Bool)
  | halt
deriving DecidableEq

namespace Control

def elems : List Control :=
  [.start false, .start true,
   .shift false false, .shift false true,
   .shift true false, .shift true true,
   .blank false, .blank true,
   .separator false, .separator true,
   .destination false, .destination true,
   .ready false, .ready true, .halt]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | start token => cases token <;> simp [elems]
    | shift haltToken targetToken =>
        cases haltToken <;> cases targetToken <;> simp [elems]
    | blank token => cases token <;> simp [elems]
    | separator token => cases token <;> simp [elems]
    | destination token => cases token <;> simp [elems]
    | ready token => cases token <;> simp [elems]
    | halt => simp [elems]

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .start haltToken, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.header, Direction.right,
        .shift haltToken false)
  | .start haltToken, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.header, Direction.right,
        .shift haltToken true)
  | .shift haltToken targetToken, some MachineCodeSymbol.tick =>
      some (some (tokenSymbol targetToken), Direction.right,
        .shift haltToken false)
  | .shift haltToken targetToken, some MachineCodeSymbol.done =>
      some (some (tokenSymbol targetToken), Direction.right,
        .shift haltToken true)
  | .shift haltToken targetToken, some MachineCodeSymbol.header =>
      some (some (tokenSymbol targetToken), Direction.right,
        .blank haltToken)
  | .blank haltToken, _ =>
      some (some MachineCodeSymbol.blank, Direction.right,
        .separator haltToken)
  | .separator haltToken, _ =>
      some (some MachineCodeSymbol.transition, Direction.right,
        .destination haltToken)
  | .destination haltToken, _ =>
      some (some MachineCodeSymbol.header, Direction.right,
        .ready haltToken)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .start false
  halt := .halt
  transition := transition
  statesFinite := Control.finite

def comparatorPrefix (currentState : Nat) : Word MachineCodeSymbol :=
  MachineCodeSymbol.header ::
    MachineDescription.encodeNatAppend currentState
      [MachineCodeSymbol.blank, MachineCodeSymbol.transition]

def sourceWord
    (currentState : Nat)
    (firstContext secondContext : MachineCodeSymbol)
    (gap : Word MachineCodeSymbol)
    (haltTail suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend currentState
    (MachineCodeSymbol.header :: MachineCodeSymbol.header ::
      firstContext :: secondContext ::
      List.append gap
        (MachineCodeSymbol.moveRight ::
          List.append haltTail suffix))

def sourceConfig
    (haltToken : Bool)
    (currentState : Nat)
    (firstContext secondContext : MachineCodeSymbol)
    (gap : Word MachineCodeSymbol)
    (haltTail suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .start haltToken
  tape := Tape.input
    (sourceWord currentState firstContext secondContext gap haltTail suffix)

def targetConfig
    (haltToken : Bool)
    (currentState : Nat)
    (gap : Word MachineCodeSymbol)
    (haltTail suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .ready haltToken
  tape := SerializedShift.cursorTape
    (MachineCodeSymbol.header :: (comparatorPrefix currentState).reverse)
    (List.append gap
      (MachineCodeSymbol.moveRight :: List.append haltTail suffix))

theorem step_shift_tick
    (haltToken targetToken : Bool)
    (leftRev rest : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := .shift haltToken targetToken
          tape := SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.tick :: rest) } =
      some
        { state := .shift haltToken false
          tape := SerializedShift.cursorTape
            (tokenSymbol targetToken :: leftRev) rest } := by
  cases haltToken <;> cases targetToken <;> cases rest <;> rfl
  done

theorem step_start_tick
    (haltToken : Bool)
    (leftRev rest : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := .start haltToken
          tape := SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.tick :: rest) } =
      some
        { state := .shift haltToken false
          tape := SerializedShift.cursorTape
            (MachineCodeSymbol.header :: leftRev) rest } := by
  cases haltToken <;> cases rest <;> rfl
  done

theorem step_start_done
    (haltToken : Bool)
    (leftRev rest : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := .start haltToken
          tape := SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.done :: rest) } =
      some
        { state := .shift haltToken true
          tape := SerializedShift.cursorTape
            (MachineCodeSymbol.header :: leftRev) rest } := by
  cases haltToken <;> cases rest <;> rfl
  done

theorem step_shift_header
    (haltToken targetToken : Bool)
    (leftRev rest : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := .shift haltToken targetToken
          tape := SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.header :: rest) } =
      some
        { state := .blank haltToken
          tape := SerializedShift.cursorTape
            (tokenSymbol targetToken :: leftRev) rest } := by
  cases haltToken <;> cases targetToken <;> cases rest <;> rfl
  done

theorem run_finish
    (haltToken : Bool)
    (leftRev : Word MachineCodeSymbol)
    (firstContext secondContext : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    machine.runConfigExact? 3
        { state := .blank haltToken
          tape := SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.header :: firstContext :: secondContext ::
              rest) } =
      some
        { state := .ready haltToken
          tape := SerializedShift.cursorTape
            (MachineCodeSymbol.header :: MachineCodeSymbol.transition ::
              MachineCodeSymbol.blank :: leftRev)
            rest } := by
  cases haltToken <;> cases rest <;> rfl
  done

theorem runConfigExact_trans
    {first second : Nat}
    {source middle target :
      TuringMachine.Configuration MachineCodeSymbol Control}
    (hfirst : machine.runConfigExact? first source = some middle)
    (hsecond : machine.runConfigExact? second middle = some target) :
    machine.runConfigExact? (first + second) source = some target := by
  apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr
  exact TuringMachine.computesIn_trans
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hfirst)
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hsecond)
  done

theorem run_shift
    (haltToken targetToken : Bool)
    (remaining : Nat)
    (leftRev : Word MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    machine.runConfigExact? (remaining + 2)
        { state := .shift haltToken targetToken
          tape := SerializedShift.cursorTape leftRev
            (MachineDescription.encodeNatAppend remaining
              (MachineCodeSymbol.header :: rest)) } =
      some
        { state := .blank haltToken
          tape := SerializedShift.cursorTape
            (List.append (MachineDescription.encodeNat remaining).reverse
              (tokenSymbol targetToken :: leftRev))
            rest } := by
  induction remaining generalizing leftRev targetToken with
  | zero =>
      cases haltToken <;> cases targetToken <;> cases rest <;> rfl
  | succ remaining ih =>
      change machine.runConfigExact? ((remaining + 2) + 1)
        { state := .shift haltToken targetToken
          tape := SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.tick ::
              MachineDescription.encodeNatAppend remaining
                (MachineCodeSymbol.header :: rest)) } = _
      rw [TuringMachine.runConfigExact?]
      rw [step_shift_tick]
      simp only
      simpa [tokenSymbol, MachineDescription.encodeNat, List.reverse_cons,
        List.append_assoc] using
        ih false (tokenSymbol targetToken :: leftRev)
  done

theorem run_exact
    (haltToken : Bool)
    (currentState : Nat)
    (firstContext secondContext : MachineCodeSymbol)
    (gap : Word MachineCodeSymbol)
    (haltTail suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (currentState + 5)
        (sourceConfig haltToken currentState firstContext secondContext
          gap haltTail suffix) =
      some (targetConfig haltToken currentState gap haltTail suffix) := by
  let tail : Word MachineCodeSymbol :=
    List.append gap
      (MachineCodeSymbol.moveRight :: List.append haltTail suffix)
  cases currentState with
  | zero =>
      have hstart :
          machine.runConfigExact? 1
              (sourceConfig haltToken 0 firstContext secondContext
                gap haltTail suffix) =
            some
              { state := .shift haltToken true
                tape := SerializedShift.cursorTape
                  [MachineCodeSymbol.header]
                  (MachineCodeSymbol.header :: MachineCodeSymbol.header ::
                    firstContext :: secondContext :: tail) } := by
        change machine.runConfigExact? 1
          { state := .start haltToken
            tape := SerializedShift.cursorTape []
              (MachineCodeSymbol.done :: MachineCodeSymbol.header ::
                MachineCodeSymbol.header :: firstContext :: secondContext ::
                tail) } = _
        rw [TuringMachine.runConfigExact?]
        rw [step_start_done]
        rfl
      have hheader :
          machine.runConfigExact? 1
              { state := .shift haltToken true
                tape := SerializedShift.cursorTape
                  [MachineCodeSymbol.header]
                  (MachineCodeSymbol.header :: MachineCodeSymbol.header ::
                    firstContext :: secondContext :: tail) } =
            some
              { state := .blank haltToken
                tape := SerializedShift.cursorTape
                  [MachineCodeSymbol.done, MachineCodeSymbol.header]
                  (MachineCodeSymbol.header :: firstContext ::
                    secondContext :: tail) } := by
        rw [TuringMachine.runConfigExact?]
        rw [step_shift_header]
        rfl
      have hfinish := run_finish haltToken
        [MachineCodeSymbol.done, MachineCodeSymbol.header]
        firstContext secondContext tail
      have hall := runConfigExact_trans
        (runConfigExact_trans hstart hheader) hfinish
      simpa [sourceConfig, targetConfig, comparatorPrefix, tail,
        MachineDescription.encodeNat, MachineDescription.encodeNatAppend,
        List.append_assoc] using hall
  | succ remaining =>
      have hstart :
          machine.runConfigExact? 1
              (sourceConfig haltToken (remaining + 1)
                firstContext secondContext gap haltTail suffix) =
            some
              { state := .shift haltToken false
                tape := SerializedShift.cursorTape
                  [MachineCodeSymbol.header]
                  (MachineDescription.encodeNatAppend remaining
                    (MachineCodeSymbol.header :: MachineCodeSymbol.header ::
                      firstContext :: secondContext :: tail)) } := by
        change machine.runConfigExact? 1
          { state := .start haltToken
            tape := SerializedShift.cursorTape []
              (MachineCodeSymbol.tick ::
                MachineDescription.encodeNatAppend remaining
                  (MachineCodeSymbol.header :: MachineCodeSymbol.header ::
                    firstContext :: secondContext :: tail)) } = _
        rw [TuringMachine.runConfigExact?]
        rw [step_start_tick]
        rfl
      have hshift := run_shift haltToken false remaining
        [MachineCodeSymbol.header]
        (MachineCodeSymbol.header :: firstContext :: secondContext :: tail)
      have hfinish := run_finish haltToken
        (List.append (MachineDescription.encodeNat remaining).reverse
          [MachineCodeSymbol.tick, MachineCodeSymbol.header])
        firstContext secondContext tail
      have hall := runConfigExact_trans
        (runConfigExact_trans hstart hshift) hfinish
      simpa [sourceConfig, targetConfig, comparatorPrefix, tail,
        MachineDescription.encodeNat, MachineDescription.encodeNatAppend,
        List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hall
  done

end PrefixBuilder

end FiniteRecognizer.Interpreter.FinalGateMaterializer

end Computability
end FoC
