import FoC.Computability.Compiler.Core.FiniteRecognizer.GeneratedCode
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.Layout
import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.StageSearchController.GeneratedCallSearch.Basic

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

theorem stageCodeToExactFuelInitialLayoutCode_stageCode
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    ExactFuel.Layout.stageCodeToInitialLayoutCode M
        (stageCode input fuel) =
      some
        (ExactFuel.Layout.encode
          (ExactFuel.Layout.initial M input fuel)) := by
  simpa [stageCode] using
    ExactFuel.Layout.stageCodeToInitialLayoutCode_stageCode
      M input fuel

end GeneratedCode
end FiniteRecognizer

end Computability
end FoC
