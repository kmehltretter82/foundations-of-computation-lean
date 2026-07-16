import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Outer.Direct.EmptyBypass
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Initializer.Frontier
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Parser.Branch.PhaseSum
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.Acceptance

namespace FoC
namespace Computability

open Languages

namespace Section53SemanticAcceptance

open Section53EmptyTableFinalBypass
open Section53InitializerFrontier
open Section53BoundedLoopInduction
open Section53RuntimePhaseSum

/-- The two direct parser branches observe exactly the public bounded-halting
predicate: either fuel is zero, or an empty transition table stutters for all
remaining fuel. -/
theorem direct_state_eq_iff_haltsIn
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol)
    (hbranch : fuel = 0 ∨ D.transitions = []) :
    D.start = D.halt ↔
      D.HaltsIn fuel
        (MachineDescription.encodeCodeWordAsInput input) := by
  unfold MachineDescription.HaltsIn
  change D.start = D.halt ↔
    (D.runConfig fuel
      (Section53EmptyTableFinalBypass.initialConfiguration D input)).state =
        D.halt
  rcases hbranch with hzero | hempty
  · subst fuel
    exact (zeroFuel_semanticFinal_iff D input).symm
  · exact (emptyTable_semanticFinal_iff D fuel input hempty).symm

/-- Once either direct parser branch has reached its shared decision endpoint,
its operational halting behavior is exactly the public semantic predicate. -/
theorem parser_direct_haltsFrom_iff_haltsIn
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol)
    (hbranch : fuel = 0 ∨ D.transitions = [])
    (source : TuringMachine.Configuration MachineCodeSymbol
      Section53ParserBranchPhaseSum.Control)
    (finalTape : Tape MachineCodeSymbol)
    (hrun : TuringMachine.Computes
      Section53ParserBranchPhaseSum.machine source
      (Section53ParserBranchPhaseSum.directDecisionConfig
        D.start D.halt finalTape)) :
    TuringMachine.HaltsFrom Section53ParserBranchPhaseSum.machine source ↔
      D.HaltsIn fuel
        (MachineDescription.encodeCodeWordAsInput input) := by
  exact Iff.trans
    (Section53ParserBranchPhaseSum.haltsFrom_iff_of_computes_to_directDecision
        D.start D.halt finalTape hrun)
    (direct_state_eq_iff_haltsIn D fuel input hbranch)

/-- Specialize the concrete runtime acceptance theorem to the initial Boolean
configuration constructed from the parsed input word. -/
theorem positive_runtime_haltsFrom_iff_haltsIn
    (D : MachineDescription)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (htransitions : D.transitions = first :: rest)
    (remainingFuel : Nat)
    (input : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (loopSourceConfig
        (Section53InitializerFrontier.initialConfiguration D input)
        (first :: rest) remainingFuel D.halt []).tape sourceTape) :
    TuringMachine.HaltsFrom Section53RuntimePhaseSum.machine
        (outerLoopConfig scanEmbed
          (Section53InitializerFrontier.initialConfiguration D input)
          (first :: rest) remainingFuel D.halt [] sourceTape) ↔
      D.HaltsIn (remainingFuel + 1)
        (MachineDescription.encodeCodeWordAsInput input) := by
  simpa [MachineDescription.HaltsIn,
    Section53InitializerFrontier.initialConfiguration,
    Section53InitializerFrontier.inputBits] using
    Section53RuntimeAcceptance.haltsFrom_iff_runConfig_state_eq
      D first rest htransitions remainingFuel
      (Section53InitializerFrontier.initialConfiguration D input)
      D.halt [] sourceTape hsource


end Section53SemanticAcceptance
end Computability
end FoC
