import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.Lookup
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.Action
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.EncodedList.Pop
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.TapeShapes

namespace FoC
namespace Computability

open Languages

namespace Section53DirectContextUpdate

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open Section53UniformInterpreterOneStep

abbrev Action := Section53RuntimeAction.Action

def apply (action : Action) (tape : Tape Bool) : Tape Bool :=
  Tape.move action.move (Tape.write action.write tape)

/-- Canonical post-cleanup word.  The dynamic state occurs once, before the
guard; the protected payload contains only the two tape contexts and the
persistent caller-owned data. -/
def contextSourceWord
    (target : Nat) (tape : Tape Bool)
    (persistent : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend target
    (MachineCodeSymbol.header ::
      RuntimeKeySingleKeyRepair.protectedTapeContextsAppend tape persistent)

/-- Canonical direct-update endpoint.  The next head is returned in finite
control; the word retains the unique dynamic target state and the updated
left/right contexts. -/
def contextTargetWord
    (target : Nat) (action : Action) (tape : Tape Bool)
    (persistent : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  contextSourceWord target (apply action tape) persistent

/-- The persistent raw table is delimited independently of its row count. -/
def persistentTable
    (transitions : List TransitionDescription)
    (callerSuffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeTransitionsAppend transitions
    (MachineCodeSymbol.header :: callerSuffix)

/-- Work currency consumed by the next table-restaging phase. -/
def nextSingleKeyWorkWord
    (target : Nat) (nextHead : Option Bool)
    (tape : Tape Bool)
    (transitions : List TransitionDescription)
    (callerSuffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (runtimeKeyBuilderKeyCode target nextHead)
    (RuntimeKeySingleKeyRepair.protectedTapeContextsAppend tape
      (persistentTable transitions callerSuffix))

theorem contextTargetWord_preserves_persistent_table
    (target : Nat) (action : Action) (tape : Tape Bool)
    (transitions : List TransitionDescription)
    (callerSuffix : Word MachineCodeSymbol) :
    contextTargetWord target action tape
        (persistentTable transitions callerSuffix) =
      MachineDescription.encodeNatAppend target
        (MachineCodeSymbol.header ::
          RuntimeKeySingleKeyRepair.protectedTapeContextsAppend
            (apply action tape)
            (MachineDescription.encodeTransitionsAppend transitions
              (MachineCodeSymbol.header :: callerSuffix))) := by
  rfl
  done

theorem nextSingleKeyWorkWord_exact
    (target : Nat) (nextHead : Option Bool)
    (tape : Tape Bool)
    (transitions : List TransitionDescription)
    (callerSuffix : Word MachineCodeSymbol) :
    nextSingleKeyWorkWord target nextHead tape transitions callerSuffix =
      List.append (runtimeKeyBuilderKeyCode target nextHead)
        (RuntimeKeySingleKeyRepair.protectedTapeContextsAppend tape
          (MachineDescription.encodeTransitionsAppend transitions
            (MachineCodeSymbol.header :: callerSuffix))) := by
  rfl

/-!
### Dynamic-state/header positioner

The cleanup phase leaves the head at the first target-state tick.  This small
finite scanner crosses that unary state and its following guard, retaining the
finite write/move action and stopping on the first left-context count token.
-/

namespace Prefix

inductive Control where
  | target (action : Action)
  | guard (action : Action)
  | ready (action : Action)
  | halt
deriving DecidableEq

namespace Control

def elems : List Control :=
  Section53RuntimeAction.Action.finite.elems.map target ++
    Section53RuntimeAction.Action.finite.elems.map guard ++
    Section53RuntimeAction.Action.finite.elems.map ready ++ [halt]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | target action =>
        simp [elems,
          Section53RuntimeAction.Action.finite.complete action]
    | guard action =>
        simp [elems,
          Section53RuntimeAction.Action.finite.complete action]
    | ready action =>
        simp [elems,
          Section53RuntimeAction.Action.finite.complete action]
    | halt => simp [elems]

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .target action, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .target action)
  | .target action, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .guard action)
  | .guard action, some MachineCodeSymbol.header =>
      some (some MachineCodeSymbol.header, Direction.right, .ready action)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .target { write := none, move := Direction.left }
  halt := .halt
  transition := transition
  statesFinite := Control.finite

def sourceConfig
    (action : Action) (target : Nat)
    (rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .target action
  tape := SerializedShift.cursorTape []
    (MachineDescription.encodeNatAppend target
      (MachineCodeSymbol.header :: rest))

def targetBaseLeftRev (target : Nat) : Word MachineCodeSymbol :=
  MachineCodeSymbol.header ::
    (MachineDescription.encodeNat target).reverse

def targetConfig
    (action : Action) (target : Nat)
    (rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .ready action
  tape := SerializedShift.cursorTape (targetBaseLeftRev target) rest

theorem source_tape_eq_input
    (action : Action) (target : Nat)
    (rest : Word MachineCodeSymbol) :
    (sourceConfig action target rest).tape =
      Tape.input
        (MachineDescription.encodeNatAppend target
          (MachineCodeSymbol.header :: rest)) := by
  cases target <;> rfl
  done

theorem step_target_tick
    (action : Action) (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := Control.target action
          tape := SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.tick :: suffix) } =
      some
        { state := Control.target action
          tape := SerializedShift.cursorTape
            (MachineCodeSymbol.tick :: leftRev) suffix } := by
  cases suffix <;> rfl
  done

theorem step_target_done
    (action : Action) (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := Control.target action
          tape := SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.done :: suffix) } =
      some
        { state := Control.guard action
          tape := SerializedShift.cursorTape
            (MachineCodeSymbol.done :: leftRev) suffix } := by
  cases suffix <;> rfl
  done

theorem step_guard
    (action : Action) (leftRev rest : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := Control.guard action
          tape := SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.header :: rest) } =
      some
        { state := Control.ready action
          tape := SerializedShift.cursorTape
            (MachineCodeSymbol.header :: leftRev) rest } := by
  cases rest <;> rfl
  done

theorem run_target
    (action : Action) (target : Nat)
    (leftRev : Word MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (target + 1)
        { state := Control.target action
          tape := SerializedShift.cursorTape leftRev
            (MachineDescription.encodeNatAppend target suffix) } =
      some
        { state := Control.guard action
          tape := SerializedShift.cursorTape
            (List.append (MachineDescription.encodeNat target).reverse
              leftRev) suffix } := by
  induction target generalizing leftRev with
  | zero =>
      change machine.runConfigExact? 1
        { state := Control.target action
          tape := SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.done :: suffix) } = _
      rw [TuringMachine.runConfigExact?]
      rw [step_target_done]
      rfl
  | succ target ih =>
      change machine.runConfigExact? ((target + 1) + 1)
        { state := Control.target action
          tape := SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.tick ::
              MachineDescription.encodeNatAppend target suffix) } = _
      rw [TuringMachine.runConfigExact?]
      rw [step_target_tick]
      simp only
      simpa [MachineDescription.encodeNat, List.reverse_cons,
        List.append_assoc] using
        ih (MachineCodeSymbol.tick :: leftRev)

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

theorem run_exact
    (action : Action) (target : Nat)
    (rest : Word MachineCodeSymbol) :
    machine.runConfigExact? (target + 2)
        (sourceConfig action target rest) =
      some (targetConfig action target rest) := by
  have htarget :
      machine.runConfigExact? (target + 1)
          { state := Control.target action
            tape := SerializedShift.cursorTape []
              (MachineDescription.encodeNatAppend target
                (MachineCodeSymbol.header :: rest)) } =
        some
          { state := Control.guard action
            tape := SerializedShift.cursorTape
              (MachineDescription.encodeNat target).reverse
              (MachineCodeSymbol.header :: rest) } := by
    simpa using
      run_target action target [] (MachineCodeSymbol.header :: rest)
  have hguard :
      machine.runConfigExact? 1
          { state := Control.guard action
            tape := SerializedShift.cursorTape
              (MachineDescription.encodeNat target).reverse
              (MachineCodeSymbol.header :: rest) } =
        some
          { state := Control.ready action
            tape := SerializedShift.cursorTape
              (MachineCodeSymbol.header ::
                (MachineDescription.encodeNat target).reverse) rest } := by
    rw [TuringMachine.runConfigExact?]
    rw [step_guard]
    rfl
  simpa [sourceConfig, targetConfig, targetBaseLeftRev] using
    runConfigExact_trans htarget hguard

end Prefix

end Section53DirectContextUpdate

end Computability
end FoC
