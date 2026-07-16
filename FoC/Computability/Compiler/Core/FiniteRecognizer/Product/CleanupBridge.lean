import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.Prefix

set_option doc.verso true

/-!
# Product-prefix cleanup handoff

The product prefix stops on the first right-frame fuel symbol. One left
handoff move exposes the protected-frame header while preserving the retained
raw pair call on the left. Empty and nonempty inputs keep their exact physical
blank layouts.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace ProductCleanupBridge

def emptyShiftSourceTape {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) : Tape MachineCodeSymbol :=
  { left :=
      (ProductPrefix.retainedOuterRev
        ([] : Word MachineCodeSymbol) leftFuel rightFuel).map some
    head := some MachineCodeSymbol.header
    right := List.append
      ((InitialMaterializer.EmptyInputSuffix.body right rightFuel).map some)
      [none] }

def nonemptyShiftSourceTape {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) : Tape MachineCodeSymbol :=
  { left :=
      (ProductPrefix.retainedOuterRev
        (headSymbol :: rest) leftFuel rightFuel).map some
    head := some MachineCodeSymbol.header
    right := List.append
      ((MachineDescription.encodeNat rightFuel).map some)
      (none :: none :: List.append
        ((List.append
          (InitialMaterializer.NonemptyFixedPrefix.fixedPrefix
            right headSymbol)
          (InitialMaterializer.NonemptyRightRegion.region rest)).map some)
        [none]) }

def shiftSourceTape {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    Tape MachineCodeSymbol :=
  match input with
  | [] => emptyShiftSourceTape right leftFuel rightFuel
  | headSymbol :: rest =>
      nonemptyShiftSourceTape right headSymbol rest leftFuel rightFuel

theorem prefix_run_to_shift_source {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    exists (steps : Nat)
        (endpoint : TuringMachine.Configuration MachineCodeSymbol
          (ProductContextual.Full.Control right)),
      (ProductPrefix.machine right).runConfigExact? steps
          (TuringMachine.initial (ProductPrefix.machine right)
            (GeneratedCode.nestedStageCode input rightFuel leftFuel)) =
        some (ProductPrefix.materializerConfig endpoint) ∧
      endpoint.state = ProductPrefix.rightTerminalState right input ∧
      Tape.Equiv (shiftSourceTape right input leftFuel rightFuel)
        (Tape.move Direction.left endpoint.tape) := by
  rcases ProductPrefix.prefix_run right input leftFuel rightFuel with
    ⟨steps, endpoint, hrun, hstate, htape⟩
  refine ⟨steps, endpoint, hrun, hstate, ?_⟩
  have hcanonical :
      Tape.move Direction.left
          (ProductPrefix.canonicalRightEndpointTape
            right input leftFuel rightFuel) =
        shiftSourceTape right input leftFuel rightFuel := by
    cases input <;> cases rightFuel <;> rfl
  rw [← hcanonical]
  exact Tape.Equiv.move htape Direction.left

end ProductCleanupBridge
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
