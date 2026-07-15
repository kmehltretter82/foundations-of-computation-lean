import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.Layout
import FoC.Computability.TapeLemmas

set_option doc.verso true

/-!
# Delimiter-protected strict-probe frames

The strict exact-fuel runner serializes its current layout before an immutable
caller tag and caller-owned suffix.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace Frame

/-- Immutable boundary between the strict-probe frame and caller-owned data. -/
def callerTag : MachineCodeSymbol := MachineCodeSymbol.moveRight

/-- A canonical exact-fuel layout followed by its protected caller suffix. -/
def protectedWord {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  Layout.encodeAppend L (callerTag :: callerData)

end Frame
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
