import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.Layout

set_option doc.verso true

/-!
# Strict-probe semantic transition helpers

The production strict-probe runner uses these two semantic shapes when it
threads a selected transition through the serialized frame implementation.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace Machine

/-- Exact semantic layout produced by one selected transition. -/
def transitionTarget {stateCount : Nat}
    (fuel : Nat) (write : Option MachineCodeSymbol)
    (direction : Direction) (nextState : Fin stateCount)
    (L : Layout stateCount) : Layout stateCount :=
  Layout.ofConfig fuel
    { state := nextState
      tape := Tape.move direction (Tape.write write L.tape) }

/-- A right/left bounce preserves a tape up to far-edge blank padding. -/
theorem moveLeft_moveRight_equiv_self
    (T : Tape MachineCodeSymbol) :
    Tape.Equiv
      (Tape.move Direction.left (Tape.move Direction.right T)) T := by
  cases T with
  | mk left head right =>
      simp [Tape.Equiv, Tape.move, Tape.moveLeft, Tape.moveRight]
      cases right <;> simp [Tape.dropTrailingNone]

end Machine
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
