import FoC.Computability.Compiler.Core.FiniteRecognizer.Basic

set_option doc.verso true

/-!
# Strict exact-fuel probe semantics

This module exposes the two semantic exits used by a strict exact-fuel probe.
The definition delegates execution to
{name (full := FoC.Computability.TuringMachine.runConfigExact?)}`TuringMachine.runConfigExact?`;
it does not introduce another recursive machine semantics.
-/

namespace FoC
namespace Computability

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe

/-- Result of executing a machine for exactly the requested fuel. -/
inductive Outcome (stateCount : Nat) where
  /-- Exact execution ended in the selected halt state. -/
  | success
      (final : TuringMachine.Configuration MachineCodeSymbol (Fin stateCount))
  /-- Exact execution was stuck or ended outside the selected halt state. -/
  | failure

/--
Run a finite-state code-symbol machine for exactly {lean}`fuel` transitions
and classify the resulting configuration by its halt state.
-/
def semanticOutcome {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (fuel : Nat)
    (c : TuringMachine.Configuration MachineCodeSymbol (Fin stateCount)) :
    Outcome stateCount :=
  match M.runConfigExact? fuel c with
  | none => .failure
  | some final =>
      if final.state = M.halt then .success final else .failure

/-- A successful strict outcome is exactly bounded halting from the source. -/
theorem semanticOutcome_success_iff_haltsFromIn
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (fuel : Nat)
    (c : TuringMachine.Configuration MachineCodeSymbol (Fin stateCount)) :
    (exists final,
      semanticOutcome M fuel c = Outcome.success final) <->
      TuringMachine.HaltsFromIn M fuel c := by
  rw [TuringMachine.haltsFromIn_iff_runConfigExact?]
  unfold semanticOutcome
  cases hrun : M.runConfigExact? fuel c with
  | none =>
      simp
  | some final =>
      by_cases hhalt : final.state = M.halt
      · simp [hhalt, TuringMachine.Halted]
      · simp [hhalt, TuringMachine.Halted]

/-- A failed strict outcome is exactly failure of bounded halting. -/
theorem semanticOutcome_failure_iff_not_haltsFromIn
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (fuel : Nat)
    (c : TuringMachine.Configuration MachineCodeSymbol (Fin stateCount)) :
    semanticOutcome M fuel c = Outcome.failure <->
      ¬ TuringMachine.HaltsFromIn M fuel c := by
  rw [TuringMachine.haltsFromIn_iff_runConfigExact?]
  unfold semanticOutcome
  cases hrun : M.runConfigExact? fuel c with
  | none =>
      simp
  | some final =>
      by_cases hhalt : final.state = M.halt
      · simp [hhalt, TuringMachine.Halted]
      · simp [hhalt, TuringMachine.Halted]

/-- A missing next transition produces failure at every positive fuel. -/
theorem semanticOutcome_succ_of_transition_eq_none
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {fuel : Nat}
    {c : TuringMachine.Configuration MachineCodeSymbol (Fin stateCount)}
    (htransition :
      M.transition c.state (Tape.read c.tape) = none) :
    semanticOutcome M (fuel + 1) c = Outcome.failure := by
  simp [semanticOutcome, TuringMachine.runConfigExact?,
    TuringMachine.stepConfig, htransition]

/--
A present next transition reduces strict execution to the updated
configuration with one less unit of fuel.
-/
theorem semanticOutcome_succ_of_transition_eq_some
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {fuel : Nat}
    {c : TuringMachine.Configuration MachineCodeSymbol (Fin stateCount)}
    {write : Option MachineCodeSymbol}
    {dir : Direction}
    {nextState : Fin stateCount}
    (htransition :
      M.transition c.state (Tape.read c.tape) =
        some (write, dir, nextState)) :
    semanticOutcome M (fuel + 1) c =
      semanticOutcome M fuel
        { state := nextState
          tape := Tape.move dir (Tape.write write c.tape) } := by
  simp [semanticOutcome, TuringMachine.runConfigExact?,
    TuringMachine.stepConfig, htransition]

/--
With fuel one, an outgoing transition from the halt state is executed.  If it
lands outside the halt state, the strict outcome is failure.
-/
theorem semanticOutcome_one_of_transition_out_of_halt
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {c : TuringMachine.Configuration MachineCodeSymbol (Fin stateCount)}
    {write : Option MachineCodeSymbol}
    {dir : Direction}
    {nextState : Fin stateCount}
    (hstate : c.state = M.halt)
    (htransition :
      M.transition M.halt (Tape.read c.tape) =
        some (write, dir, nextState))
    (hnext : nextState ≠ M.halt) :
    semanticOutcome M 1 c = Outcome.failure := by
  have htransition' :
      M.transition c.state (Tape.read c.tape) =
        some (write, dir, nextState) := by
    simpa [hstate] using htransition
  rw [semanticOutcome_succ_of_transition_eq_some htransition']
  simp [semanticOutcome, TuringMachine.runConfigExact?, hnext]

end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
