import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.Runner

set_option doc.verso true

/-!
# Product fuel-field order guardrail

A concrete nonmonotone pair distinguishes the outer left fuel from the inner
right fuel in generated product calls.
-/

namespace FoC.Computability.FiniteRecognizer.ProductFuelOrder

open Languages

def zeroOnly : TuringMachine MachineCodeSymbol (Fin 1) where
  start := 0
  halt := 0
  transition := fun _ _ => none
  statesFinite := Foundation.FiniteType.fin 1

def oneOnlyTransition :
    Fin 2 -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Fin 2)
  | 0, read => some (read, Direction.right, 1)
  | 1, _ => none

def oneOnly : TuringMachine MachineCodeSymbol (Fin 2) where
  start := 0
  halt := 1
  transition := oneOnlyTransition
  statesFinite := Foundation.FiniteType.fin 2

theorem zeroOnly_accepts_zero (input : Word MachineCodeSymbol) :
    TuringMachine.HaltsOnInputIn zeroOnly 0 input := by
  exact TuringMachine.haltsOnInputIn_zero_iff.mpr rfl

theorem zeroOnly_rejects_one (input : Word MachineCodeSymbol) :
    ¬ TuringMachine.HaltsOnInputIn zeroOnly 1 input := by
  exact TuringMachine.not_haltsFromIn_succ_of_transition_eq_none rfl

def oneOnlyTarget (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Fin 2) where
  state := 1
  tape := Tape.move Direction.right
    (Tape.write (Tape.read (Tape.input input)) (Tape.input input))

theorem oneOnly_accepts_one (input : Word MachineCodeSymbol) :
    TuringMachine.HaltsOnInputIn oneOnly 1 input := by
  apply TuringMachine.haltsOnInputIn_succ_iff.mpr
  refine ⟨oneOnlyTarget input, ?_, ?_⟩
  · exact TuringMachine.Step.mk rfl
  · exact TuringMachine.haltsFromIn_zero_iff.mpr rfl

theorem oneOnly_rejects_zero (input : Word MachineCodeSymbol) :
    ¬ TuringMachine.HaltsOnInputIn oneOnly 0 input := by
  intro h
  have hhalt := TuringMachine.haltsOnInputIn_zero_iff.mp h
  simp [TuringMachine.Halted, TuringMachine.initial, oneOnly] at hhalt

theorem ordered_fuels_succeed (input : Word MachineCodeSymbol) :
    TuringMachine.HaltsOnInputIn zeroOnly 0 input ∧
      TuringMachine.HaltsOnInputIn oneOnly 1 input := by
  exact ⟨zeroOnly_accepts_zero input, oneOnly_accepts_one input⟩

theorem swapped_fuels_fail (input : Word MachineCodeSymbol) :
    ¬ (TuringMachine.HaltsOnInputIn zeroOnly 1 input ∧
      TuringMachine.HaltsOnInputIn oneOnly 0 input) := by
  intro h
  exact zeroOnly_rejects_one input h.1

theorem nestedStageCode_fuel_order_regression
    (input : Word MachineCodeSymbol) :
    generatedProductExactFuelRun zeroOnly oneOnly
          (GeneratedCode.nestedStageCode input 1 0) =
        some ([] : Word MachineCodeSymbol) ∧
      generatedProductExactFuelRun zeroOnly oneOnly
          (GeneratedCode.nestedStageCode input 0 1) = none := by
  constructor
  · exact
      (generatedProductExactFuelRun_nestedStageCode_eq_some_iff
        zeroOnly oneOnly input 0 1).mpr
        (ordered_fuels_succeed input)
  · unfold generatedProductExactFuelRun
    simp [GeneratedCode.nestedStageCode_decodeNat_outer,
      GeneratedCode.nestedStageCode_decodeNat_inner,
      zeroOnly_rejects_one input]

end FoC.Computability.FiniteRecognizer.ProductFuelOrder
