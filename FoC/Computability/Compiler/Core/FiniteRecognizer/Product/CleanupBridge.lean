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

theorem move_left_canonical_empty_eq {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) :
    Tape.move Direction.left
        (ProductPrefix.canonicalRightEndpointTape
          right [] leftFuel rightFuel) =
      emptyShiftSourceTape right leftFuel rightFuel := by
  cases rightFuel <;> rfl

theorem move_left_canonical_nonempty_eq {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) :
    Tape.move Direction.left
        (ProductPrefix.canonicalRightEndpointTape
          right (headSymbol :: rest) leftFuel rightFuel) =
      nonemptyShiftSourceTape right headSymbol rest leftFuel rightFuel := by
  cases rightFuel <;> rfl

theorem move_left_canonical_eq_shiftSourceTape {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    Tape.move Direction.left
        (ProductPrefix.canonicalRightEndpointTape
          right input leftFuel rightFuel) =
      shiftSourceTape right input leftFuel rightFuel := by
  cases input with
  | nil => exact move_left_canonical_empty_eq right leftFuel rightFuel
  | cons headSymbol rest =>
      exact move_left_canonical_nonempty_eq
        right headSymbol rest leftFuel rightFuel

theorem moved_endpoint_equiv_shiftSourceTape {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat)
    (endpointTape : Tape MachineCodeSymbol)
    (htape : Tape.Equiv
      (ProductPrefix.canonicalRightEndpointTape
        right input leftFuel rightFuel)
      endpointTape) :
    Tape.Equiv
      (shiftSourceTape right input leftFuel rightFuel)
      (Tape.move Direction.left endpointTape) := by
  rw [← move_left_canonical_eq_shiftSourceTape]
  exact Tape.Equiv.move htape Direction.left

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
  exact ⟨steps, endpoint, hrun, hstate,
    moved_endpoint_equiv_shiftSourceTape
      right input leftFuel rightFuel endpoint.tape htape⟩

theorem empty_prefix_run_to_shift_source {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) :
    exists (steps : Nat)
        (endpoint : TuringMachine.Configuration MachineCodeSymbol
          (ProductContextual.Full.Control right)),
      (ProductPrefix.machine right).runConfigExact? steps
          (TuringMachine.initial (ProductPrefix.machine right)
            (GeneratedCode.nestedStageCode [] rightFuel leftFuel)) =
        some (ProductPrefix.materializerConfig endpoint) ∧
      endpoint.state = .emptyPrepend .gate ∧
      Tape.Equiv (emptyShiftSourceTape right leftFuel rightFuel)
        (Tape.move Direction.left endpoint.tape) := by
  rcases ProductPrefix.empty_prefix_run right leftFuel rightFuel with
    ⟨steps, endpoint, hrun, hstate, htape⟩
  refine ⟨steps, endpoint, hrun, hstate, ?_⟩
  rw [← move_left_canonical_empty_eq]
  exact Tape.Equiv.move htape Direction.left

theorem nonempty_prefix_run_to_shift_source {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) :
    exists (steps : Nat)
        (endpoint : TuringMachine.Configuration MachineCodeSymbol
          (ProductContextual.Full.Control right)),
      (ProductPrefix.machine right).runConfigExact? steps
          (TuringMachine.initial (ProductPrefix.machine right)
            (GeneratedCode.nestedStageCode
              (headSymbol :: rest) rightFuel leftFuel)) =
        some (ProductPrefix.materializerConfig endpoint) ∧
      endpoint.state = .header .halt ∧
      Tape.Equiv
        (nonemptyShiftSourceTape right headSymbol rest leftFuel rightFuel)
        (Tape.move Direction.left endpoint.tape) := by
  rcases ProductPrefix.nonempty_prefix_run
      right headSymbol rest leftFuel rightFuel with
    ⟨steps, endpoint, hrun, hstate, htape⟩
  refine ⟨steps, endpoint, hrun, hstate, ?_⟩
  rw [← move_left_canonical_nonempty_eq]
  exact Tape.Equiv.move htape Direction.left

end ProductCleanupBridge
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
