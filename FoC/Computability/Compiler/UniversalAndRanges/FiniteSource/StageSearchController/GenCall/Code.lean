import FoC.Computability.Compiler.Core.FiniteRecognizer.GeneratedCode
import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.StageSearchController.GenCall.Basic

set_option doc.verso true

/-!
# Generated-code API for generated-call search

Compatibility wrapper for the public Universal/Ranges generated-call names.
The generic stage and nested-code API now lives in
{module}`FoC.Computability.Compiler.Core.FiniteRecognizer.GeneratedCode`.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace GeneratedCode

theorem stageCode_eq
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    stageCode input fuel = CodePrefixRecognizerStageCode input fuel := by
  rfl

theorem nestedStageCode_eq_codePrefix
    (input : Word MachineCodeSymbol) (inner outer : Nat) :
    nestedStageCode input inner outer =
      NestedCodePrefixRecognizerStageCode input inner outer := by
  rfl

end GeneratedCode
end FiniteRecognizer

end Computability
end FoC
