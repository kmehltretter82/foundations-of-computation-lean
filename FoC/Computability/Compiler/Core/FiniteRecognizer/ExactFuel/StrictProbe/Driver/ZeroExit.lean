import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Machine

set_option doc.verso true

/-!
# Zero-fuel exit classifier

The classifier compares the carried state with the selected-machine halt state
while preserving the serialized tape up to a right/left round trip.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace ZeroExitRoundTrip

/- A generic fuel-zero classifier for the carried-state design.  The physical
serialized state may remain a stable placeholder; the actual selected state
is carried in finite control. -/

inductive Control (stateCount : Nat) where
  | check (carriedState : Fin stateCount)
  | successReturn
  | failureReturn
  | successContinuation
  | failureContinuation
deriving DecidableEq

namespace Control

def elems (stateCount : Nat) : List (Control stateCount) :=
  List.append
    ((List.finRange stateCount).map Control.check)
    [.successReturn, .failureReturn,
      .successContinuation, .failureContinuation]

def finite (stateCount : Nat) :
    Foundation.FiniteType (Control stateCount) where
  elems := elems stateCount
  complete := by
    intro control
    cases control with
    | check state =>
        simp [elems, List.mem_finRange]
    | successReturn => simp [elems]
    | failureReturn => simp [elems]
    | successContinuation => simp [elems]
    | failureContinuation => simp [elems]

end Control

def transition {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    Control stateCount -> Option MachineCodeSymbol ->
      Option
        (Option MachineCodeSymbol × Direction × Control stateCount)
  | .check carriedState, cell =>
      if carriedState = M.halt then
        some (cell, Direction.right, .successReturn)
      else
        some (cell, Direction.right, .failureReturn)
  | .successReturn, cell =>
      some (cell, Direction.left, .successContinuation)
  | .failureReturn, cell =>
      some (cell, Direction.left, .failureContinuation)
  | .successContinuation, _ => none
  | .failureContinuation, _ => none

def machine {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    TuringMachine MachineCodeSymbol (Control stateCount) where
  start := .check M.start
  halt := .successContinuation
  transition := transition M
  statesFinite := Control.finite stateCount


private theorem write_read_eq_self
    (T : Tape MachineCodeSymbol) :
    Tape.write (Tape.read T) T = T := by
  cases T
  rfl

def checkTapeConfig {stateCount : Nat}
    (carriedState : Fin stateCount) (tape : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount) where
  state := .check carriedState
  tape := tape

def continuationTapeConfig {stateCount : Nat}
    (continuation : Control stateCount) (tape : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount) where
  state := continuation
  tape := Tape.move Direction.left (Tape.move Direction.right tape)

theorem success_run_exact_on_tape {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (carriedState : Fin stateCount) (tape : Tape MachineCodeSymbol)
    (hhalt : carriedState = M.halt) :
    (machine M).runConfigExact? 2 (checkTapeConfig carriedState tape) =
      some (continuationTapeConfig .successContinuation tape) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, checkTapeConfig, continuationTapeConfig, hhalt,
    write_read_eq_self] <;> done

theorem failure_run_exact_on_tape {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (carriedState : Fin stateCount) (tape : Tape MachineCodeSymbol)
    (hnotHalt : carriedState ≠ M.halt) :
    (machine M).runConfigExact? 2 (checkTapeConfig carriedState tape) =
      some (continuationTapeConfig .failureContinuation tape) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, checkTapeConfig, continuationTapeConfig, hnotHalt,
    write_read_eq_self] <;> done

end ZeroExitRoundTrip
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
