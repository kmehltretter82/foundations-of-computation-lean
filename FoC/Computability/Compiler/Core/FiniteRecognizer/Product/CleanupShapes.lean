import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.CleanupBridge

set_option doc.verso true

/-!
# Product cleanup source shapes

The retained raw pair call is the only part exposed to cleanup. All cells at
and to the right of the protected-frame header are carried as opaque physical
cells, preserving the nonempty branch's two internal blanks exactly.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace ProductCleanupShapes

def retainedRawPrefix (input : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) : Word MachineCodeSymbol :=
  List.append (MachineDescription.encodeNat leftFuel)
    (MachineDescription.encodeNatAppend rightFuel input)

theorem retainedOuterRev_reverse_eq_retainedRawPrefix
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    (ProductPrefix.retainedOuterRev input leftFuel rightFuel).reverse =
      retainedRawPrefix input leftFuel rightFuel := by
  exact ProductRightPrefix.retainedOuterRev_reverse
    input leftFuel rightFuel

theorem retainedOuterRev_eq_retainedRawPrefix_reverse
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    ProductPrefix.retainedOuterRev input leftFuel rightFuel =
      (retainedRawPrefix input leftFuel rightFuel).reverse := by
  rw [← retainedOuterRev_reverse_eq_retainedRawPrefix]
  simp

def emptyOpaqueRightCells {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (rightFuel : Nat) : List (Option MachineCodeSymbol) :=
  List.append
    ((InitialMaterializer.EmptyInputSuffix.body right rightFuel).map some)
    [none]

def nonemptyOpaqueRightCells {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (rightFuel : Nat) : List (Option MachineCodeSymbol) :=
  List.append
    ((MachineDescription.encodeNat rightFuel).map some)
    (none :: none :: List.append
      ((List.append
        (InitialMaterializer.NonemptyFixedPrefix.fixedPrefix
          right headSymbol)
        (InitialMaterializer.NonemptyRightRegion.region rest)).map some)
      [none])

def opaqueRightCells {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (input : Word MachineCodeSymbol) (rightFuel : Nat) :
    List (Option MachineCodeSymbol) :=
  match input with
  | [] => emptyOpaqueRightCells right rightFuel
  | headSymbol :: rest =>
      nonemptyOpaqueRightCells right headSymbol rest rightFuel

def prefixShiftSourceTape
    (prefixRev : Word MachineCodeSymbol)
    (opaqueRight : List (Option MachineCodeSymbol)) :
    Tape MachineCodeSymbol :=
  { left := prefixRev.map some
    head := some MachineCodeSymbol.header
    right := opaqueRight }

theorem empty_shiftSourceTape_eq_prefixShiftSourceTape
    {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) :
    ProductCleanupBridge.emptyShiftSourceTape right leftFuel rightFuel =
      prefixShiftSourceTape
        (ProductPrefix.retainedOuterRev
          ([] : Word MachineCodeSymbol) leftFuel rightFuel)
        (emptyOpaqueRightCells right rightFuel) := by
  rfl

theorem nonempty_shiftSourceTape_eq_prefixShiftSourceTape
    {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) :
    ProductCleanupBridge.nonemptyShiftSourceTape
        right headSymbol rest leftFuel rightFuel =
      prefixShiftSourceTape
        (ProductPrefix.retainedOuterRev
          (headSymbol :: rest) leftFuel rightFuel)
        (nonemptyOpaqueRightCells right headSymbol rest rightFuel) := by
  rfl

theorem shiftSourceTape_eq_prefixShiftSourceTape
    {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    ProductCleanupBridge.shiftSourceTape
        right input leftFuel rightFuel =
      prefixShiftSourceTape
        (ProductPrefix.retainedOuterRev input leftFuel rightFuel)
        (opaqueRightCells right input rightFuel) := by
  cases input <;> rfl

theorem prefix_run_to_opaque_prefix_shift_source
    {rightCount : Nat}
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
      Tape.Equiv
        (prefixShiftSourceTape
          (ProductPrefix.retainedOuterRev input leftFuel rightFuel)
          (opaqueRightCells right input rightFuel))
        (Tape.move Direction.left endpoint.tape) := by
  rcases ProductCleanupBridge.prefix_run_to_shift_source
      right input leftFuel rightFuel with
    ⟨steps, endpoint, hrun, hstate, htape⟩
  refine ⟨steps, endpoint, hrun, hstate, ?_⟩
  rw [← shiftSourceTape_eq_prefixShiftSourceTape]
  exact htape

end ProductCleanupShapes
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
