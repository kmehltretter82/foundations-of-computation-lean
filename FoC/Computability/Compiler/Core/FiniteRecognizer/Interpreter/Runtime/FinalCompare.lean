import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.Lookup
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.StuckSink

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.UniformInterpreterOneStep

def finalComparatorSourceConfig
    (haltState currentState : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol RuntimeKeyComparatorState :=
  { state := RuntimeKeyComparatorState.needHeader
    tape :=
      runtimeKeyComparatorTape []
        (MachineCodeSymbol.header ::
          runtimeKeyComparatorBody
            (List.replicate haltState MachineCodeSymbol.tick)
            none
            (List.replicate currentState MachineCodeSymbol.tick)
            none suffix) }

def finalComparatorTargetConfig
    (haltState currentState : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol RuntimeKeyComparatorState :=
  { state :=
      if haltState = currentState then
        RuntimeKeyComparatorState.matched
      else
        RuntimeKeyComparatorState.missed
    tape :=
      runtimeKeyComparatorTape
        (runtimeKeyComparatorRestoredLeft
          (List.replicate haltState MachineCodeSymbol.tick) none
          (List.replicate currentState MachineCodeSymbol.tick) none
          [MachineCodeSymbol.header])
        suffix }

theorem finalComparator_computes_exact
    (haltState currentState : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes runtimeKeyComparatorMachine
      (finalComparatorSourceConfig haltState currentState suffix)
      (finalComparatorTargetConfig haltState currentState suffix) := by
  by_cases heq : haltState = currentState
  · simpa [finalComparatorSourceConfig, finalComparatorTargetConfig,
      runtimeKeyComparatorRowOutcome, runtimeKeyComparatorReadOutcome,
      runtimeKeyComparatorOutcomeState, heq] using
      (runtimeKeyComparatorMachine_computes_one_row_from_header
        haltState none currentState none suffix)
  · simpa [finalComparatorSourceConfig, finalComparatorTargetConfig,
      runtimeKeyComparatorRowOutcome, runtimeKeyComparatorReadOutcome,
      runtimeKeyComparatorOutcomeState, heq] using
      (runtimeKeyComparatorMachine_computes_one_row_from_header
        haltState none currentState none suffix)

theorem finalComparator_haltsFrom_iff
    (haltState currentState : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.HaltsFrom runtimeKeyComparatorMachine
        (finalComparatorSourceConfig haltState currentState suffix) <->
      haltState = currentState := by
  constructor
  · intro hhalt
    by_cases heq : haltState = currentState
    · exact heq
    · have hrun :=
        runtimeKeyComparatorMachine_computes_one_row_from_header
          haltState none currentState none suffix
      have hnot :=
        TuringMachine.StuckSink.not_haltsFrom_of_computes_to_stuck_nonhalt
          (M := runtimeKeyComparatorMachine)
          (by intro read; rfl)
          (by
            simpa [finalComparatorSourceConfig] using hrun)
          (by
            simp [TuringMachine.Halted, runtimeKeyComparatorMachine,
              runtimeKeyComparatorRowOutcome, heq,
              runtimeKeyComparatorOutcomeState])
          (by
            intro next
            apply TuringMachine.not_step_of_transition_eq_none
            simp [runtimeKeyComparatorMachine,
              runtimeKeyComparatorRowOutcome, heq,
              runtimeKeyComparatorOutcomeState])
      exact False.elim (hnot hhalt)
  · intro heq
    subst currentState
    have hrun :=
      runtimeKeyComparatorMachine_computes_one_row_from_header
        haltState none haltState none suffix
    apply TuringMachine.halts_from_of_computes
      (by simpa [finalComparatorSourceConfig] using hrun)
    simp [TuringMachine.Halted, runtimeKeyComparatorMachine,
      runtimeKeyComparatorRowOutcome, runtimeKeyComparatorReadOutcome,
      runtimeKeyComparatorOutcomeState]


end FiniteRecognizer.Interpreter.UniformInterpreterOneStep

end Computability
end FoC
