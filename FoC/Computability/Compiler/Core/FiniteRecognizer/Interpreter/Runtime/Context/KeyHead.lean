import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.Context.Boundary

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.DirectContextUpdate

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep

/-!
### Next-key materializer

After the contexts have been updated, the target state is followed by the
temporary context guard.  This finite phase replaces that guard by the next
head-cell token and rewinds to the start, yielding the exact single-key work
word.  It does not claim to perform the later table-copy permutation.
-/

namespace KeyHead

inductive Control where
  | target (head : Option Bool)
  | guard (head : Option Bool)
  | rewind
  | ready
  | halt
deriving DecidableEq

namespace Control

def elems : List Control :=
  FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.optionBools.map target ++
    FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.optionBools.map guard ++
    [rewind, ready, halt]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | target head =>
        simp [elems, FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.optionBools_complete head]
    | guard head =>
        simp [elems, FiniteRecognizer.Interpreter.RuntimeEncodedList.Pop.optionBools_complete head]
    | rewind => simp [elems]
    | ready => simp [elems]
    | halt => simp [elems]

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .target head, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .target head)
  | .target head, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .guard head)
  | .guard head, some MachineCodeSymbol.header =>
      some
        (some (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.cellSymbol head),
          Direction.left, .rewind)
  | .rewind, some symbol =>
      some (some symbol, Direction.left, .rewind)
  | .rewind, none => some (none, Direction.right, .ready)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .target none
  halt := .halt
  transition := transition
  statesFinite := Control.finite

def sourceWord
    (target : Nat) (rest : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend target
    (MachineCodeSymbol.header :: rest)

def targetWord
    (target : Nat) (head : Option Bool)
    (rest : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (runtimeKeyBuilderKeyCode target head) rest

def sourceConfig
    (target : Nat) (head : Option Bool)
    (rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .target head
  tape := SerializedShift.cursorTape [] (sourceWord target rest)

def afterTargetConfig
    (target : Nat) (head : Option Bool)
    (rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .guard head
  tape := SerializedShift.cursorTape
    (MachineDescription.encodeNat target).reverse
    (MachineCodeSymbol.header :: rest)

def rewindTape
    (remainingRev crossed : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match remainingRev with
  | [] =>
      { left := [], head := none, right := crossed.map some }
  | current :: remaining =>
      { left := remaining.map some
        head := some current
        right := crossed.map some }

def rewindConfig
    (remainingRev crossed : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .rewind
  tape := rewindTape remainingRev crossed

def readyTape (word : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  Tape.move Direction.right (rewindTape [] word)

def targetConfig
    (target : Nat) (head : Option Bool)
    (rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .ready
  tape := readyTape (targetWord target head rest)

theorem source_tape_eq_input
    (target : Nat) (head : Option Bool)
    (rest : Word MachineCodeSymbol) :
    (sourceConfig target head rest).tape =
      Tape.input (sourceWord target rest) := by
  cases target <;> rfl

theorem step_target_tick
    (head : Option Bool)
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := Control.target head
          tape := SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.tick :: suffix) } =
      some
        { state := Control.target head
          tape := SerializedShift.cursorTape
            (MachineCodeSymbol.tick :: leftRev) suffix } := by
  cases suffix <;> rfl

theorem step_target_done
    (head : Option Bool)
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := Control.target head
          tape := SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.done :: suffix) } =
      some
        { state := Control.guard head
          tape := SerializedShift.cursorTape
            (MachineCodeSymbol.done :: leftRev) suffix } := by
  cases suffix <;> rfl

theorem run_target
    (head : Option Bool) (target : Nat)
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (target + 1)
        { state := Control.target head
          tape := SerializedShift.cursorTape leftRev
            (MachineDescription.encodeNatAppend target suffix) } =
      some
        { state := Control.guard head
          tape := SerializedShift.cursorTape
            (List.append (MachineDescription.encodeNat target).reverse
              leftRev) suffix } := by
  induction target generalizing leftRev with
  | zero =>
      change machine.runConfigExact? 1
        { state := Control.target head
          tape := SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.done :: suffix) } = _
      rw [TuringMachine.runConfigExact?]
      rw [step_target_done]
      rfl
  | succ target ih =>
      change machine.runConfigExact? ((target + 1) + 1)
        { state := Control.target head
          tape := SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.tick ::
              MachineDescription.encodeNatAppend target suffix) } = _
      rw [TuringMachine.runConfigExact?]
      rw [step_target_tick]
      simp only
      simpa [MachineDescription.encodeNat, List.reverse_cons,
        List.append_assoc] using
        ih (MachineCodeSymbol.tick :: leftRev)

theorem guard_rewrite_from_nonempty_exact
    (head : Option Bool)
    (current : MachineCodeSymbol)
    (remainingRev rest : Word MachineCodeSymbol) :
    machine.runConfigExact? 1
        { state := Control.guard head
          tape := SerializedShift.cursorTape (current :: remainingRev)
            (MachineCodeSymbol.header :: rest) } =
      some
        (rewindConfig (current :: remainingRev)
          (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.cellSymbol head :: rest)) := by
  cases head with
  | none => rfl
  | some bit => cases bit <;> rfl

theorem encodeNat_reverse_ne_nil (target : Nat) :
    (MachineDescription.encodeNat target).reverse ≠ [] := by
  cases target <;>
    simp [MachineDescription.encodeNat]

theorem guard_rewrite_exact
    (target : Nat) (head : Option Bool)
    (rest : Word MachineCodeSymbol) :
    machine.runConfigExact? 1 (afterTargetConfig target head rest) =
      some
        (rewindConfig (MachineDescription.encodeNat target).reverse
          (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.cellSymbol head :: rest)) := by
  have hnonempty := encodeNat_reverse_ne_nil target
  cases hrev : (MachineDescription.encodeNat target).reverse with
  | nil => contradiction
  | cons current remainingRev =>
      simpa [afterTargetConfig, hrev] using
        guard_rewrite_from_nonempty_exact head current remainingRev rest

theorem step_rewind_cons
    (current : MachineCodeSymbol)
    (remainingRev crossed : Word MachineCodeSymbol) :
    machine.stepConfig (rewindConfig (current :: remainingRev) crossed) =
      some (rewindConfig remainingRev (current :: crossed)) := by
  cases remainingRev <;> rfl

theorem rewind_nil_ready_exact
    (crossed : Word MachineCodeSymbol) :
    machine.runConfigExact? 1 (rewindConfig [] crossed) =
      some { state := Control.ready, tape := readyTape crossed } := by
  cases crossed <;> rfl

theorem run_rewind
    (remainingRev crossed : Word MachineCodeSymbol) :
    machine.runConfigExact? (remainingRev.length + 1)
        (rewindConfig remainingRev crossed) =
      some
        { state := Control.ready
          tape := readyTape (List.append remainingRev.reverse crossed) } := by
  induction remainingRev generalizing crossed with
  | nil =>
      simpa using rewind_nil_ready_exact crossed
  | cons current remainingRev ih =>
      change machine.runConfigExact? ((remainingRev.length + 1) + 1)
        (rewindConfig (current :: remainingRev) crossed) = _
      rw [TuringMachine.runConfigExact?]
      rw [step_rewind_cons]
      simp only
      simpa [List.reverse_cons, List.append_assoc] using
        ih (current :: crossed)

theorem readyTape_equiv_input (word : Word MachineCodeSymbol) :
    Tape.Equiv (readyTape word) (Tape.input word) := by
  cases word <;>
    simp [readyTape, rewindTape, Tape.input, Tape.blank,
      Tape.move, Tape.moveRight, Tape.Equiv, Tape.dropTrailingNone]

theorem rewoundWord_eq_targetWord
    (target : Nat) (head : Option Bool)
    (rest : Word MachineCodeSymbol) :
    List.append
        (MachineDescription.encodeNat target).reverse.reverse
        (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.cellSymbol head :: rest) =
      targetWord target head rest := by
  rw [List.reverse_reverse]
  unfold targetWord runtimeKeyBuilderKeyCode
  cases head with
  | none =>
      simp [FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.cellSymbol,
        MachineDescription.encodeCell,
        MachineDescription.encodeNatAppend, List.append_assoc]
  | some bit =>
      cases bit <;>
        simp [FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.cellSymbol,
          MachineDescription.encodeCell,
          MachineDescription.encodeNatAppend, List.append_assoc]

def runSteps (target : Nat) : Nat :=
  ((target + 1) + 1) +
    ((MachineDescription.encodeNat target).reverse.length + 1)

theorem run_exact
    (target : Nat) (head : Option Bool)
    (rest : Word MachineCodeSymbol) :
    machine.runConfigExact? (runSteps target)
        (sourceConfig target head rest) =
      some (targetConfig target head rest) := by
  have htarget :
      machine.runConfigExact? (target + 1)
          (sourceConfig target head rest) =
        some (afterTargetConfig target head rest) := by
    simpa [sourceConfig, sourceWord, afterTargetConfig] using
      run_target head target [] (MachineCodeSymbol.header :: rest)
  have hguard := guard_rewrite_exact target head rest
  have hpref := TuringMachine.runConfigExact?_trans htarget hguard
  have hrewind := run_rewind
    (MachineDescription.encodeNat target).reverse
    (FiniteRecognizer.Interpreter.RuntimeEncodedList.Prepend.cellSymbol head :: rest)
  have hrun := TuringMachine.runConfigExact?_trans hpref hrewind
  have hword := rewoundWord_eq_targetWord target head rest
  simp only [List.reverse_reverse] at hword
  simp only [List.reverse_reverse] at hrun
  rw [hword] at hrun
  simpa [runSteps, targetConfig] using hrun

theorem run_exact_target_tape_equiv_input
    (target : Nat) (head : Option Bool)
    (rest : Word MachineCodeSymbol) :
    Tape.Equiv (targetConfig target head rest).tape
      (Tape.input (targetWord target head rest)) := by
  exact readyTape_equiv_input _

end KeyHead

end FiniteRecognizer.Interpreter.DirectContextUpdate

end Computability
end FoC
