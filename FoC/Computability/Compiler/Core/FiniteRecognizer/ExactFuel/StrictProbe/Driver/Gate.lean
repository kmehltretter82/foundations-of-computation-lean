import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame.Fuel

set_option doc.verso true

/-!
# Carried-fuel loop gate

The loop-entry classifier distinguishes exhausted fuel from a positive fuel
budget while preserving the serialized protected frame.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace CarriedFuelGate

open SerializedFieldComposer

/-- Two-token loop-entry classifier. Both exits are deliberately
transitionless so the zero and positive loop bodies can retarget them. -/
inductive Control (stateCount : Nat) where
  | header (carriedState : Fin stateCount)
  | inspectFuel (carriedState : Fin stateCount)
  | zeroEntry (carriedState : Fin stateCount)
  | positiveEntry (carriedState : Fin stateCount)
deriving DecidableEq

namespace Control

def elems (stateCount : Nat) : List (Control stateCount) :=
  List.append
    ((List.finRange stateCount).map Control.header)
    (List.append
      ((List.finRange stateCount).map Control.inspectFuel)
      (List.append
        ((List.finRange stateCount).map Control.zeroEntry)
        ((List.finRange stateCount).map Control.positiveEntry)))

def finite (stateCount : Nat) : Foundation.FiniteType (Control stateCount) where
  elems := elems stateCount
  complete := by
    intro control
    cases control with
    | header carriedState =>
        simp [elems, List.mem_finRange]
    | inspectFuel carriedState =>
        simp [elems, List.mem_finRange]
    | zeroEntry carriedState =>
        simp [elems, List.mem_finRange]
    | positiveEntry carriedState =>
        simp [elems, List.mem_finRange]

end Control

def transition {stateCount : Nat} :
    Control stateCount -> Option MachineCodeSymbol ->
      Option
        (Option MachineCodeSymbol × Direction × Control stateCount)
  | .header carriedState, some MachineCodeSymbol.header =>
      some
        (some MachineCodeSymbol.header, Direction.right,
          .inspectFuel carriedState)
  | .inspectFuel carriedState, some MachineCodeSymbol.done =>
      some
        (some MachineCodeSymbol.done, Direction.left,
          .zeroEntry carriedState)
  | .inspectFuel carriedState, some MachineCodeSymbol.tick =>
      some
        (some MachineCodeSymbol.tick, Direction.left,
          .positiveEntry carriedState)
  | _, _ => none

def machine {stateCount : Nat} (initialCarriedState : Fin stateCount) :
    TuringMachine MachineCodeSymbol (Control stateCount) where
  start := .header initialCarriedState
  halt := .zeroEntry initialCarriedState
  transition := transition
  statesFinite := Control.finite stateCount

def sourceConfig {stateCount : Nat}
    (F : CarriedStateFrame.LoopFrame stateCount)
    (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount) where
  state := .header F.carriedState
  tape := Tape.input (Frame.protectedWord F.physicalFrame callerData)

def roundTripTape (T : Tape MachineCodeSymbol) : Tape MachineCodeSymbol :=
  Tape.move Direction.left (Tape.move Direction.right T)

def zeroConfig {stateCount : Nat} (carriedState : Fin stateCount)
    (T : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount) where
  state := .zeroEntry carriedState
  tape := roundTripTape T

def positiveConfig {stateCount : Nat} (carriedState : Fin stateCount)
    (T : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount) where
  state := .positiveEntry carriedState
  tape := roundTripTape T

theorem zero_run_exact_on_tape {stateCount : Nat}
    (initialCarriedState carriedState : Fin stateCount)
    (T : Tape MachineCodeSymbol)
    (hheader : Tape.read T = some MachineCodeSymbol.header)
    (hzero :
      Tape.read (Tape.move Direction.right T) =
        some MachineCodeSymbol.done) :
    (machine initialCarriedState).runConfigExact? 2
        { state := Control.header carriedState, tape := T } =
      some (zeroConfig carriedState T) := by
  have hwriteHeader :
      Tape.write (some MachineCodeSymbol.header) T = T := by
    rw [← hheader]
    exact Tape.write_read_eq_self T
  have hwriteZero :
      Tape.write (some MachineCodeSymbol.done)
          (Tape.move Direction.right T) =
        Tape.move Direction.right T := by
    rw [← hzero]
    exact Tape.write_read_eq_self (Tape.move Direction.right T)
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, hheader, hwriteHeader, hzero, hwriteZero,
    zeroConfig, roundTripTape]

theorem positive_run_exact_on_tape {stateCount : Nat}
    (initialCarriedState carriedState : Fin stateCount)
    (T : Tape MachineCodeSymbol)
    (hheader : Tape.read T = some MachineCodeSymbol.header)
    (hpositive :
      Tape.read (Tape.move Direction.right T) =
        some MachineCodeSymbol.tick) :
    (machine initialCarriedState).runConfigExact? 2
        { state := Control.header carriedState, tape := T } =
      some (positiveConfig carriedState T) := by
  have hwriteHeader :
      Tape.write (some MachineCodeSymbol.header) T = T := by
    rw [← hheader]
    exact Tape.write_read_eq_self T
  have hwritePositive :
      Tape.write (some MachineCodeSymbol.tick)
          (Tape.move Direction.right T) =
        Tape.move Direction.right T := by
    rw [← hpositive]
    exact Tape.write_read_eq_self (Tape.move Direction.right T)
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, hheader, hwriteHeader, hpositive, hwritePositive,
    positiveConfig, roundTripTape]

theorem roundTrip_protected_input_eq {stateCount : Nat}
    (F : CarriedStateFrame.LoopFrame stateCount)
    (callerData : Word MachineCodeSymbol) :
    roundTripTape
        (Tape.input (Frame.protectedWord F.physicalFrame callerData)) =
      Tape.input (Frame.protectedWord F.physicalFrame callerData) := by
  cases F with
  | mk carriedState physicalFrame =>
      cases physicalFrame with
      | mk fuel state left head right =>
          cases fuel <;> rfl

end CarriedFuelGate
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
