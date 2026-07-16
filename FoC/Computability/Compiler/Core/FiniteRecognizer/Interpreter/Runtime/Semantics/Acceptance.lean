import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Outer.Direct.EmptyBypass
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Initializer.Frontier
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Parser.Branch.PhaseSum
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.Acceptance

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.SemanticAcceptance

open FiniteRecognizer.Interpreter.EmptyTableFinalBypass
open FiniteRecognizer.Interpreter.InitializerFrontier
open FiniteRecognizer.Interpreter.BoundedLoopInduction
open FiniteRecognizer.Interpreter.RuntimePhaseSum

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
      (FiniteRecognizer.Interpreter.EmptyTableFinalBypass.initialConfiguration D input)).state =
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
      FiniteRecognizer.Interpreter.ParserBranchPhaseSum.Control)
    (finalTape : Tape MachineCodeSymbol)
    (hrun : TuringMachine.Computes
      FiniteRecognizer.Interpreter.ParserBranchPhaseSum.machine source
      (FiniteRecognizer.Interpreter.ParserBranchPhaseSum.directDecisionConfig
        D.start D.halt finalTape)) :
    TuringMachine.HaltsFrom FiniteRecognizer.Interpreter.ParserBranchPhaseSum.machine source ↔
      D.HaltsIn fuel
        (MachineDescription.encodeCodeWordAsInput input) := by
  exact Iff.trans
    (FiniteRecognizer.Interpreter.ParserBranchPhaseSum.haltsFrom_iff_of_computes_to_directDecision
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
        (FiniteRecognizer.Interpreter.InitializerFrontier.initialConfiguration D input)
        (first :: rest) remainingFuel D.halt []).tape sourceTape) :
    TuringMachine.HaltsFrom FiniteRecognizer.Interpreter.RuntimePhaseSum.machine
        (outerLoopConfig scanEmbed
          (FiniteRecognizer.Interpreter.InitializerFrontier.initialConfiguration D input)
          (first :: rest) remainingFuel D.halt [] sourceTape) ↔
      D.HaltsIn (remainingFuel + 1)
        (MachineDescription.encodeCodeWordAsInput input) := by
  simpa [MachineDescription.HaltsIn,
    FiniteRecognizer.Interpreter.InitializerFrontier.initialConfiguration,
    FiniteRecognizer.Interpreter.InitializerFrontier.inputBits] using
    FiniteRecognizer.Interpreter.RuntimeAcceptance.haltsFrom_iff_runConfig_state_eq
      D first rest htransitions remainingFuel
      (FiniteRecognizer.Interpreter.InitializerFrontier.initialConfiguration D input)
      D.halt [] sourceTape hsource


end FiniteRecognizer.Interpreter.SemanticAcceptance
end Computability
end FoC
