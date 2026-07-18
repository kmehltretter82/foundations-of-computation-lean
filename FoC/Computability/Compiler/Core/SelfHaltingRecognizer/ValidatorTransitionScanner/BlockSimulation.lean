import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.BlockMachine

set_option doc.verso true

/-! # Exact-code validator: generated block-machine simulation -/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer

open Languages

open FoC.Computability.DovetailInitialLayoutInitializer

private theorem flatMap_validatorBlockCellBits_map_some
    (blocks : List ValidatorBlockSymbol) :
    (blocks.map some).flatMap validatorBlockCellBits =
      (blocks.flatMap ValidatorBlockSymbol.bits).map some := by
  induction blocks with
  | nil => rfl
  | cons symbol rest ih =>
      simp [validatorBlockCellBits, ih,
        List.map_append]

private theorem flatMap_reverse_validatorBlockCellBits_map_some_reverse
    (blocks : List ValidatorBlockSymbol) :
    (blocks.map some).reverse.flatMap
        (fun cell => (validatorBlockCellBits cell).reverse) =
      ((blocks.flatMap ValidatorBlockSymbol.bits).map some).reverse := by
  induction blocks with
  | nil => rfl
  | cons symbol rest ih =>
      rw [List.map_cons, List.reverse_cons, List.flatMap_append]
      simp only [List.flatMap_singleton]
      rw [ih]
      simp [validatorBlockCellBits,
        List.map_append, List.reverse_append]

theorem validatorPhysicalizeBlockTape_logical
    (left right : Word ValidatorBlockSymbol) :
    validatorPhysicalizeBlockTape
        (validatorLogicalBlockTape left right) =
      validatorBlockTape left right := by
  unfold validatorPhysicalizeBlockTape validatorLogicalBlockTape
  unfold validatorBlockTape validatorBlockBits
  change List ValidatorBlockSymbol at left right
  cases right <;>
    simp [flatMap_validatorBlockCellBits_map_some,
      flatMap_reverse_validatorBlockCellBits_map_some_reverse,
      List.map_reverse, List.map_append, List.append_assoc] <;>
    simp [validatorBlockCellBits]

/-- Four physical left moves cross exactly one aligned block. -/
theorem validatorBlockTape_moveLeft_four
    (left right : Word ValidatorBlockSymbol)
    (previous : ValidatorBlockSymbol) :
    Tape.move Direction.left
        (Tape.move Direction.left
          (Tape.move Direction.left
            (Tape.move Direction.left
              (validatorBlockTape
                (List.append left [previous]) right)))) =
      validatorBlockTape left (previous :: right) := by
  unfold validatorBlockTape validatorBlockBits
  change List ValidatorBlockSymbol at left right
  cases right <;>
    simp [ValidatorBlockSymbol.bits_eq_components,
      Tape.move, Tape.moveLeft, tapeAtCells, List.reverse_append]

end SelfHaltingRecognizer
end Computability
end FoC
