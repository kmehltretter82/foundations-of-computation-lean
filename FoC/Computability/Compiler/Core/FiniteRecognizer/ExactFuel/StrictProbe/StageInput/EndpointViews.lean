import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.StageInput.Materializer

set_option doc.verso true

/-!
# Exact-fuel materializer endpoint views

Tape-equivalence views of the exact-fuel stage-input materializer endpoints.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace StageInput
namespace EndpointViews

def bouncedEmptyTape {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (fuel : Nat) : Tape MachineCodeSymbol :=
  Tape.move Direction.left
    (InitialMaterializer.FullMaterializerMachine.emptyHaltTape M fuel)

theorem bouncedEmptyTape_equiv_protectedInput {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (fuel : Nat) :
    Tape.Equiv (bouncedEmptyTape M fuel)
      (Tape.input
        (Frame.protectedWord
          (Layout.initial M ([] : Word MachineCodeSymbol) fuel) [])) := by
  have hword :
      Frame.protectedWord
          (Layout.initial M ([] : Word MachineCodeSymbol) fuel) [] =
        MachineCodeSymbol.header ::
          InitialMaterializer.EmptyInputSuffix.body M fuel := by
    rw [Layout.initial_empty_eq]
    rfl
  unfold bouncedEmptyTape
    InitialMaterializer.FullMaterializerMachine.emptyHaltTape
  rw [hword]
  cases hbody : InitialMaterializer.EmptyInputSuffix.body M fuel with
  | nil =>
      simp [InitialMaterializer.PrependHeader.gateTape,
        Tape.input, Tape.move, Tape.moveLeft, Tape.Equiv]
      exact FoC.Computability.dropTrailingNone_append_none []
  | cons first rest =>
      simp [InitialMaterializer.PrependHeader.gateTape,
        Tape.input, Tape.move, Tape.moveLeft, Tape.Equiv]
      exact Tape.dropTrailingNone_cons_eq rfl
        (FoC.Computability.dropTrailingNone_append_none (rest.map some))

end EndpointViews
end StageInput
end StrictProbe
end ExactFuel
end FiniteRecognizer
end Computability
end FoC
