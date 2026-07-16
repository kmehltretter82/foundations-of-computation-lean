import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Outer.PublicBoundary
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Outer.Construction

set_option doc.verso true

/-!
# Decoded-description interpreter construction

Public finite-state construction for the uniform interpreter over encoded
machine-description data.  The semantic contracts are defined in
{module}`FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Outer.PublicBoundary`;
the concrete finite runner is assembled by
{module}`FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Outer.Construction`.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer

/--
Finite-state interpreter construction. Its contract observes ordinary
halting and decoded input shape; it deliberately makes no claim that the
runner erases its complete physical tape.
-/
theorem decodedDescriptionInterpreterFinStateFiniteLeaf :
    DecodedDescriptionInterpreterFinStateConstruction :=
  FiniteRecognizer.Interpreter.Construction.finStateConstruction

theorem decodedDescriptionInterpreterFiniteLeaf :
    DecodedDescriptionInterpreterConstruction :=
  decodedDescriptionInterpreterConstruction_of_finState
    decodedDescriptionInterpreterFinStateFiniteLeaf

theorem decodedDescriptionInterpreterComponentsFiniteLeaf :
    DecodedDescriptionInterpreterComponentsConstruction := by
  rcases decodedDescriptionInterpreterFiniteLeaf with
    ⟨runnerState, runner, htotal⟩
  exact
    ⟨runnerState, runner,
      decodedDescriptionCanonicalStageSpec_of_total htotal,
      decodedDescriptionTotalShapeSpec_of_total htotal⟩

end FiniteRecognizer

end Computability
end FoC
