import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Parser.Prefix.PhaseSum
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Outer.PhaseSum

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.SuccessfulPrefixEvidence

/-!
# Successful parser-prefix evidence

This small integration module instantiates the generic final phase sum's
parser-evidence interface with the concrete parser-prefix inversion theorem.
-/

def contract :
    FiniteRecognizer.Interpreter.OuterPhaseSumGeneric.SuccessfulPrefixEvidenceContract where
  project := by
    intro tokens steps target hrun hterminal
    exact
      FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.successfulTerminal_outerParserPhaseEvidence_of_computesIn
        hrun hterminal


end FiniteRecognizer.Interpreter.SuccessfulPrefixEvidence
end Computability
end FoC
