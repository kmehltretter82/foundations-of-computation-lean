import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.ActionUpdate
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.Action
import FoC.Computability.TapeLemmas

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.RuntimeLeftCleanup

abbrev Action := FiniteRecognizer.Interpreter.RuntimeAction.Action

inductive Control where
  | enter (action : Action)
  | erase (action : Action)
  | seek (action : Action)
  | bounce (action : Action)
  | ready (action : Action)
  | halt
deriving DecidableEq

namespace Control

def elems : List Control :=
  List.append
    (FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.elems.map Control.enter)
    (List.append
      (FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.elems.map Control.erase)
      (List.append
        (FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.elems.map Control.seek)
        (List.append
          (FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.elems.map
            Control.bounce)
          (List.append
            (FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.elems.map
              Control.ready)
            [.halt]))))

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | enter action =>
        simp [elems,
          FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.complete action]
    | erase action =>
        simp [elems,
          FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.complete action]
    | seek action =>
        simp [elems,
          FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.complete action]
    | bounce action =>
        simp [elems,
          FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.complete action]
    | ready action =>
        simp [elems,
          FiniteRecognizer.Interpreter.RuntimeAction.Action.finite.complete action]
    | halt => simp [elems]

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .enter action, read =>
      some (read, Direction.left, .erase action)
  | .erase action, some _ =>
      some (none, Direction.left, .erase action)
  | .erase action, none =>
      some (none, Direction.right, .seek action)
  | .seek action, none =>
      some (none, Direction.right, .seek action)
  | .seek action, some current =>
      some (some current, Direction.right, .bounce action)
  | .bounce action, read =>
      some (read, Direction.left, .ready action)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .enter { write := none, move := Direction.left }
  halt := .halt
  transition := transition
  statesFinite := Control.finite

def optionalTape
    (leftRev rest : List (Option MachineCodeSymbol)) :
    Tape MachineCodeSymbol :=
  match rest with
  | [] => { left := leftRev, head := none, right := [] }
  | first :: tail => { left := leftRev, head := first, right := tail }

def wordTape
    (leftRev rest : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  optionalTape (leftRev.map some) (rest.map some)

def sourceConfig
    (action : Action)
    (leftRev rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .enter action
  tape := wordTape leftRev rest

def eraseConfig
    (action : Action)
    (remaining : Word MachineCodeSymbol)
    (cleared : Nat)
    (rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  match remaining with
  | [] =>
      { state := .erase action
        tape := optionalTape []
          (none :: List.append (List.replicate cleared none)
            (rest.map some)) }
  | current :: more =>
      { state := .erase action
        tape := optionalTape (more.map some)
          (some current :: List.append (List.replicate cleared none)
            (rest.map some)) }

def seekConfig
    (action : Action)
    (leftBlanks remainingBlanks : Nat)
    (rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .seek action
  tape := optionalTape (List.replicate leftBlanks none)
    (List.append (List.replicate remainingBlanks none) (rest.map some))

def bounceConfig
    (action : Action)
    (leftBlanks : Nat)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .bounce action
  tape := optionalTape
    (some first :: List.replicate leftBlanks none)
    (rest.map some)

def targetConfig
    (action : Action)
    (leftBlanks : Nat)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .ready action
  tape :=
    { left := List.replicate leftBlanks none
      head := some first
      right :=
        match rest with
        | [] => [none]
        | _ => rest.map some }

theorem step_enter
    (action : Action)
    (leftRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    machine.stepConfig (sourceConfig action leftRev (first :: rest)) =
      some (eraseConfig action leftRev 0 (first :: rest)) := by
  cases leftRev <;> cases rest <;> rfl

theorem step_erase_cons
    (action : Action)
    (current : MachineCodeSymbol)
    (remaining : Word MachineCodeSymbol)
    (cleared : Nat)
    (rest : Word MachineCodeSymbol) :
    machine.stepConfig
        (eraseConfig action (current :: remaining) cleared rest) =
      some (eraseConfig action remaining cleared.succ rest) := by
  cases remaining <;> cases rest <;>
    simp [TuringMachine.stepConfig, machine, transition,
      eraseConfig, optionalTape,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      List.replicate_succ]

theorem step_erase_nil
    (action : Action)
    (cleared : Nat)
    (rest : Word MachineCodeSymbol) :
    machine.stepConfig (eraseConfig action [] cleared rest) =
      some (seekConfig action 1 cleared rest) := by
  cases cleared <;> cases rest <;> rfl

theorem step_seek_succ
    (action : Action)
    (leftBlanks remainingBlanks : Nat)
    (rest : Word MachineCodeSymbol) :
    machine.stepConfig
        (seekConfig action leftBlanks remainingBlanks.succ rest) =
      some (seekConfig action leftBlanks.succ remainingBlanks rest) := by
  cases remainingBlanks <;> cases rest <;>
    simp [TuringMachine.stepConfig, machine, transition,
      seekConfig, optionalTape,
      Tape.read, Tape.write, Tape.move, Tape.moveRight,
      List.replicate_succ]

theorem step_seek_found
    (action : Action)
    (leftBlanks : Nat)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    machine.stepConfig
        (seekConfig action leftBlanks 0 (first :: rest)) =
      some (bounceConfig action leftBlanks first rest) := by
  cases rest <;> rfl

theorem step_bounce
    (action : Action)
    (leftBlanks : Nat)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    machine.stepConfig (bounceConfig action leftBlanks first rest) =
      some (targetConfig action leftBlanks first rest) := by
  cases rest <;> rfl

theorem erase_run_exact
    (action : Action)
    (remaining : Word MachineCodeSymbol)
    (cleared : Nat)
    (rest : Word MachineCodeSymbol) :
    machine.runConfigExact? (remaining.length + 1)
        (eraseConfig action remaining cleared rest) =
      some
        (seekConfig action 1 (remaining.length + cleared) rest) := by
  induction remaining generalizing cleared with
  | nil =>
      rw [TuringMachine.runConfigExact?]
      rw [step_erase_nil]
      simp [TuringMachine.runConfigExact?]
  | cons current remaining ih =>
      change machine.runConfigExact? ((remaining.length + 1) + 1)
          (eraseConfig action (current :: remaining) cleared rest) = _
      rw [TuringMachine.runConfigExact?]
      rw [step_erase_cons]
      simp only
      rw [ih cleared.succ]
      simp [Nat.add_comm, Nat.add_left_comm]
  done

theorem seek_run_exact
    (action : Action)
    (leftBlanks remainingBlanks : Nat)
    (rest : Word MachineCodeSymbol) :
    machine.runConfigExact? remainingBlanks
        (seekConfig action leftBlanks remainingBlanks rest) =
      some
        (seekConfig action (leftBlanks + remainingBlanks) 0 rest) := by
  induction remainingBlanks generalizing leftBlanks with
  | zero =>
      rfl
  | succ remainingBlanks ih =>
      rw [TuringMachine.runConfigExact?]
      rw [step_seek_succ]
      simp only
      rw [ih leftBlanks.succ]
      simp [Nat.add_comm, Nat.add_left_comm]
  done

theorem finish_run_exact
    (action : Action)
    (leftBlanks : Nat)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        (seekConfig action leftBlanks 0 (first :: rest)) =
      some (targetConfig action leftBlanks first rest) := by
  rw [TuringMachine.runConfigExact?]
  rw [step_seek_found]
  simp only
  rw [TuringMachine.runConfigExact?]
  rw [step_bounce]
  rfl
  done

def runSteps (leftRev : Word MachineCodeSymbol) : Nat :=
  ((1 + (leftRev.length + 1)) + leftRev.length) + 2

theorem run_exact
    (action : Action)
    (leftRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    machine.runConfigExact? (runSteps leftRev)
        (sourceConfig action leftRev (first :: rest)) =
      some
        (targetConfig action (1 + leftRev.length) first rest) := by
  have hentry :
      machine.runConfigExact? 1
          (sourceConfig action leftRev (first :: rest)) =
        some (eraseConfig action leftRev 0 (first :: rest)) := by
    rw [TuringMachine.runConfigExact?]
    rw [step_enter]
    rfl
  have herase :=
    erase_run_exact action leftRev 0 (first :: rest)
  simp only [Nat.add_zero] at herase
  have hseek :=
    seek_run_exact action 1 leftRev.length (first :: rest)
  have hfinish :=
    finish_run_exact action (1 + leftRev.length) first rest
  exact TuringMachine.runConfigExact?_trans
    (TuringMachine.runConfigExact?_trans
      (TuringMachine.runConfigExact?_trans hentry herase) hseek)
    hfinish
  done

theorem target_tape_equiv_input
    (action : Action)
    (leftBlanks : Nat)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    Tape.Equiv (targetConfig action leftBlanks first rest).tape
      (Tape.input (first :: rest)) := by
  cases rest with
  | nil =>
      simp [targetConfig, Tape.Equiv, Tape.input,
        dropTrailingNone_replicate_none,
        Tape.dropTrailingNone]
  | cons next tail =>
      simp [targetConfig, Tape.Equiv, Tape.input,
        dropTrailingNone_replicate_none]
      rfl
  done

def selectedAction
    (selected : TransitionDescription) : Action :=
  { write := selected.write, move := selected.move }

def actionLeftRev
    (baseLeftRev : Word MachineCodeSymbol)
    (selected : TransitionDescription) : Word MachineCodeSymbol :=
  List.append
    (FiniteRecognizer.Interpreter.RuntimeActionPrefix.consumedPrefix selected).reverse
    baseLeftRev

theorem source_tape_eq_action_target
    (baseLeftRev : Word MachineCodeSymbol)
    (selected : TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    (sourceConfig (selectedAction selected)
      (actionLeftRev baseLeftRev selected)
      (MachineDescription.encodeNatAppend selected.target suffix)).tape =
    (FiniteRecognizer.Interpreter.RuntimeActionPrefix.targetConfig
      baseLeftRev selected suffix).tape := by
  cases selected with
  | mk source read write move target =>
      cases target <;> cases suffix <;> rfl
  done

def fromActionConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (selected : TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .enter (selectedAction selected)
  tape :=
    (FiniteRecognizer.Interpreter.RuntimeActionPrefix.targetConfig
      baseLeftRev selected suffix).tape

theorem computes_from_action_target
    (baseLeftRev : Word MachineCodeSymbol)
    (selected : TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
          (fromActionConfig baseLeftRev selected suffix)
          { state := .ready (selectedAction selected)
            tape := targetTape } ∧
        Tape.Equiv targetTape
          (Tape.input
            (MachineDescription.encodeNatAppend selected.target suffix)) := by
  let leftRev := actionLeftRev baseLeftRev selected
  cases htarget : selected.target with
  | zero =>
      let endpoint :=
        targetConfig (selectedAction selected)
          (1 + leftRev.length) MachineCodeSymbol.done suffix
      have hrun :=
        run_exact (selectedAction selected) leftRev
          MachineCodeSymbol.done suffix
      have hcomp := TuringMachine.computesIn_to_computes
        (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hrun)
      refine ⟨endpoint.tape, ?_, ?_⟩
      · unfold fromActionConfig
        rw [← source_tape_eq_action_target]
        simpa [fromActionConfig, sourceConfig, targetConfig,
          endpoint, leftRev, htarget,
          MachineDescription.encodeNatAppend,
          MachineDescription.encodeNat] using hcomp
      · simpa [endpoint, htarget,
          MachineDescription.encodeNatAppend,
          MachineDescription.encodeNat] using
          target_tape_equiv_input
            (selectedAction selected) (1 + leftRev.length)
            MachineCodeSymbol.done suffix
  | succ target =>
      let endpoint :=
        targetConfig (selectedAction selected)
          (1 + leftRev.length) MachineCodeSymbol.tick
          (MachineDescription.encodeNatAppend target suffix)
      have hrun :=
        run_exact (selectedAction selected) leftRev
          MachineCodeSymbol.tick
          (MachineDescription.encodeNatAppend target suffix)
      have hcomp := TuringMachine.computesIn_to_computes
        (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hrun)
      refine ⟨endpoint.tape, ?_, ?_⟩
      · unfold fromActionConfig
        rw [← source_tape_eq_action_target]
        simpa [fromActionConfig, sourceConfig, targetConfig,
          endpoint, leftRev, htarget,
          MachineDescription.encodeNatAppend,
          MachineDescription.encodeNat] using hcomp
      · simpa [endpoint, htarget,
          MachineDescription.encodeNatAppend,
          MachineDescription.encodeNat] using
          target_tape_equiv_input
            (selectedAction selected) (1 + leftRev.length)
            MachineCodeSymbol.tick
            (MachineDescription.encodeNatAppend target suffix)
  done


end FiniteRecognizer.Interpreter.RuntimeLeftCleanup

end Computability
end FoC
