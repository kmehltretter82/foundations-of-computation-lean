import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.PhaseSum.Routes

namespace FoC
namespace Computability

open Languages

namespace Section53RuntimeAcceptance

open Section53BoundedLoopInduction
open Section53RuntimePhaseSum

/-- The concrete bounded runtime halts exactly when the simulated bounded run
ends in the requested halt state.  The physical loop-entry tape may differ
from the canonical source by trailing-blank padding. -/
theorem haltsFrom_iff_runConfig_state_eq
    (D : MachineDescription)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (htransitions : D.transitions = first :: rest)
    (copies : Nat)
    (current : MachineDescription.Configuration)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (loopSourceConfig current (first :: rest) copies haltState
        callerSuffix).tape sourceTape) :
    TuringMachine.HaltsFrom machine
        (outerLoopConfig scanEmbed current (first :: rest) copies
          haltState callerSuffix sourceTape) <->
      (D.runConfig (copies + 1) current).state = haltState := by
  constructor
  · intro hhalts
    by_cases heq : (D.runConfig (copies + 1) current).state = haltState
    · exact heq
    · rcases runtime_bounded_loop_computes D first rest htransitions copies
          current haltState callerSuffix sourceTape hsource with
        ⟨terminalTape, hrun⟩
      have hnot :=
        TuringMachine.StuckSink.not_haltsFrom_of_computes_to_stuck_nonhalt
          (M := machine)
          haltingTransitionsDisabled
          (by
            simpa [outerTerminalConfig, finalCompareEmbed, heq] using hrun)
          (by simp [TuringMachine.Halted, machine])
          (by
            intro next
            apply TuringMachine.not_step_of_transition_eq_none
            exact reject_transition_none (Tape.read terminalTape))
      exact False.elim (hnot hhalts)
  · intro heq
    rcases runtime_bounded_loop_computes D first rest htransitions copies
        current haltState callerSuffix sourceTape hsource with
      ⟨terminalTape, hrun⟩
    apply TuringMachine.halts_from_of_computes hrun
    simp [TuringMachine.Halted, outerTerminalConfig, finalCompareEmbed,
      machine, heq]


end Section53RuntimeAcceptance

end Computability
end FoC
