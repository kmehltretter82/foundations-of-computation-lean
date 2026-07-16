import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Parser.Prefix.PhaseSum
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Outer.PhaseSum

namespace FoC
namespace Computability

open Languages

namespace Section53SuccessfulPrefixEvidence

/-!
# Successful parser-prefix evidence

This small integration module instantiates the generic final phase sum's
parser-evidence interface with the concrete parser-prefix inversion theorem.
-/

def contract :
    Section53OuterPhaseSumGeneric.SuccessfulPrefixEvidenceContract where
  project := by
    intro tokens steps target hrun hterminal
    exact
      Section53ParserPrefixPhaseSum.successfulTerminal_outerParserPhaseEvidence_of_computesIn
        hrun hterminal


end Section53SuccessfulPrefixEvidence
end Computability
end FoC
