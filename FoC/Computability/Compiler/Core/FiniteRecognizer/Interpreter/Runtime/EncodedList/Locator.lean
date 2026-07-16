import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.TapeShapes

namespace FoC
namespace Computability

open Languages

namespace Section53RuntimeEncodedList

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer

/-!
**Encoded-list payload locator.** This locator finds the payload boundary of a
unary-counted Boolean-cell list independently of its surrounding runtime
layout. It preserves an arbitrary reversed prefix and leaves the head on the
first token of the arbitrary suffix.
-/

namespace PayloadLocator

inductive Control where
  | count
  | gate
deriving DecidableEq

namespace Control

def finite : Foundation.FiniteType Control where
  elems := [.count, .gate]
  complete := by
    intro control
    cases control <;> simp

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .count, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .count)
  | .count, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .gate)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .count
  halt := .gate
  transition := transition
  statesFinite := Control.finite

def ticks (count : Nat) : Word MachineCodeSymbol :=
  List.replicate count MachineCodeSymbol.tick

theorem ticks_succ_append (count : Nat) :
    ticks (count + 1) =
      List.append (ticks count) [MachineCodeSymbol.tick] := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [ticks, List.replicate_succ] at ih ⊢
      exact congrArg (fun word => MachineCodeSymbol.tick :: word) ih

def sourceConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (count : Nat) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .count
  tape := SerializedShift.cursorTape baseLeftRev
    (MachineDescription.encodeNatAppend count suffix)

def targetLeftRev
    (baseLeftRev : Word MachineCodeSymbol) (count : Nat) :
    Word MachineCodeSymbol :=
  MachineCodeSymbol.done :: List.append (ticks count) baseLeftRev

def targetConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (count : Nat) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .gate
  tape := SerializedShift.cursorTape
    (targetLeftRev baseLeftRev count) suffix

theorem encodeNatAppend_eq_ticks
    (count : Nat) (suffix : Word MachineCodeSymbol) :
    MachineDescription.encodeNatAppend count suffix =
      List.append (ticks count)
        (MachineCodeSymbol.done :: suffix) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat, ticks,
        List.replicate_succ]
      exact congrArg (fun word => MachineCodeSymbol.tick :: word) ih

theorem cursor_step_tick
    (baseLeftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := Control.count
          tape := SerializedShift.cursorTape baseLeftRev
            (MachineCodeSymbol.tick :: suffix) } =
      some
        { state := Control.count
          tape := SerializedShift.cursorTape
            (MachineCodeSymbol.tick :: baseLeftRev) suffix } := by
  cases suffix <;> rfl

theorem cursor_step_done
    (baseLeftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := Control.count
          tape := SerializedShift.cursorTape baseLeftRev
            (MachineCodeSymbol.done :: suffix) } =
      some
        { state := Control.gate
          tape := SerializedShift.cursorTape
            (MachineCodeSymbol.done :: baseLeftRev) suffix } := by
  cases suffix <;> rfl

theorem run_exact
    (baseLeftRev : Word MachineCodeSymbol)
    (count : Nat) (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (count + 1)
        (sourceConfig baseLeftRev count suffix) =
      some (targetConfig baseLeftRev count suffix) := by
  induction count generalizing baseLeftRev with
  | zero =>
      rw [show 0 + 1 = 1 by rfl]
      rw [TuringMachine.runConfigExact?]
      exact cursor_step_done baseLeftRev suffix
  | succ count ih =>
      change
        machine.runConfigExact? ((count + 1) + 1)
            (sourceConfig baseLeftRev (count + 1) suffix) = _
      rw [TuringMachine.runConfigExact?]
      have hstep :
          machine.stepConfig
              (sourceConfig baseLeftRev (count + 1) suffix) =
            some
              (sourceConfig
                (MachineCodeSymbol.tick :: baseLeftRev)
                count suffix) := by
        simpa [sourceConfig, MachineDescription.encodeNatAppend,
          MachineDescription.encodeNat] using
          cursor_step_tick baseLeftRev
            (MachineDescription.encodeNatAppend count suffix)
      rw [hstep]
      simp only
      rw [ih]
      simp [targetConfig, targetLeftRev, ticks_succ_append,
        List.append_assoc]

theorem computes_exact
    (baseLeftRev : Word MachineCodeSymbol)
    (count : Nat) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (sourceConfig baseLeftRev count suffix)
      (targetConfig baseLeftRev count suffix) := by
  exact TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
      (run_exact baseLeftRev count suffix))


end PayloadLocator

end Section53RuntimeEncodedList

end Computability
end FoC
