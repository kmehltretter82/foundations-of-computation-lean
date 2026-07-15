import FoC.Computability.Compiler.Core.FiniteRecognizer.GeneratedCode

set_option doc.verso true

/-!
# Exact-fuel staged program code

Canonical unary-fuel stage code shared by the exact-fuel construction.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StageProgram

/-- Canonical unary-fuel stage code, independent of the Universal/Ranges API. -/
def stageCode
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    Word MachineCodeSymbol :=
  GeneratedCode.stageCode input fuel

end StageProgram
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
