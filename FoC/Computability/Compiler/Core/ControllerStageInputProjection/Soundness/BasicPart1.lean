import FoC.Computability.Compiler.Core.CommonGround.SeqComposition
import FoC.Computability.Compiler.Core.ControllerStageInputProjection.ResultRun

set_option doc.verso true

/-!
# BasicPart1

First-stage closed soundness helpers for controller stage-input projection.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace ControllerStageInputProjection

theorem final_normalizedOutput
    (input result : Word Bool) (stage : Nat) :
    Tape.normalizedOutput
        (projectionTapeAtCells
          (List.append (List.replicate (4 * result.length + 1) none)
            (List.append [none, none, none, none]
              (List.append (List.replicate (4 * result.length) none)
                (List.append projectionDoneCodeCells.reverse
                  (List.append (projectionStageTickCellsRev stage)
                    (List.append
                      (projectionCodeCells
                        (encodeBoolWord input)).reverse
                      [none, none, none, none])))))) []) =
      encodeCodeWordAsInput
        (DovetailLayout.stageInputCode input stage) := by
  simp [Tape.normalizedOutput, Tape.cells, projectionTapeAtCells,
    DovetailLayout.stageInputCode,
    DovetailLayout.stageInputCodeAppend,
    projectionStageTickCellsRev, projectionCodeCells_filterMap,
    projectionDoneCodeCells_filterMap]
  rw [encodeCodeWordAsInput_encodeBoolWordAppend]
  simp [encodeNatAppend]
  rw [encodeCodeWordAsInput_encodeNat]
  simp

def finalInputLeftRev
    (input : Word Bool) : List (Option Bool) :=
  List.append
    (projectionCodeCells (encodeBoolWord input)).reverse
    ([none, none, none, none] : List (Option Bool))

def finalStageLeftRev
    (input : Word Bool) (stage : Nat) : List (Option Bool) :=
  List.append [none, none, none, none]
    (List.append (projectionStageTickCellsRev stage)
      (finalInputLeftRev input))

def finalLeftRev
    (input result : Word Bool) (stage : Nat) : List (Option Bool) :=
  List.append (List.replicate (4 * result.length + 1) none)
    (List.append [none, none, none, none]
      (List.append (List.replicate (4 * result.length) none)
        (List.append projectionDoneCodeCells.reverse
          (List.append (projectionStageTickCellsRev stage)
            (finalInputLeftRev input)))))

def finalTape
    (C : DovetailControllerLayout) : Tape Bool :=
  projectionTapeAtCells
    (finalLeftRev C.input C.result C.stage) []

theorem haltsWithTape_encode
    (C : DovetailControllerLayout) :
    Description.HaltsWithTape
      (encodeCodeWordAsInput
        (DovetailControllerLayout.encode C))
      (finalTape C) := by
  rcases C with ⟨input, stage, result⟩
  let inputLeftRev := finalInputLeftRev input
  let stageLeftRev := finalStageLeftRev input stage
  let finalLeftRev := finalLeftRev input result stage
  have hrun :
      Description.runConfig
          (4 + projectionInputBoolWordCost input + (4 * stage + 12) +
            projectionResultBoolWordCost result + (8 * result.length + 5))
          (Description.initial
            (encodeCodeWordAsInput
              (DovetailControllerLayout.encode
                { input := input, stage := stage, result := result }))) =
        projectionConfig 999 finalLeftRev [] := by
    rw [show
        4 + projectionInputBoolWordCost input + (4 * stage + 12) +
              projectionResultBoolWordCost result +
              (8 * result.length + 5) =
            4 +
              (projectionInputBoolWordCost input +
                ((4 * stage + 12) +
                  (projectionResultBoolWordCost result +
                    (8 * result.length + 5)))) by
        omega]
    rw [runConfig_add]
    change
      Description.runConfig
        (projectionInputBoolWordCost input +
          ((4 * stage + 12) +
            (projectionResultBoolWordCost result +
              (8 * result.length + 5))))
        (Description.runConfig 4
          (Description.initial
            (encodeCodeWordAsInput
              (DovetailControllerLayout.encode
                { input := input, stage := stage, result := result })))) =
        projectionConfig 999 finalLeftRev []
    simp [DovetailControllerLayout.encode,
      DovetailControllerLayout.encodeAppend,
      encodeCodeWordAsInput,
      encodeCodeSymbolAsInput]
    change
      Description.runConfig
        (projectionInputBoolWordCost input +
          ((4 * stage + 12) +
            (projectionResultBoolWordCost result +
              (8 * result.length + 5))))
        (Description.runConfig 4
          (Description.initial
            (List.append [false, false, false, false]
              (encodeCodeWordAsInput
                (DovetailLayout.stageInputCodeAppend input
                  stage (encodeBoolWordAppend result [])))))) =
        projectionConfig 999 finalLeftRev []
    rw [run_header]
    change
      Description.runConfig
        (projectionInputBoolWordCost input +
          ((4 * stage + 12) +
            (projectionResultBoolWordCost result +
              (8 * result.length + 5))))
        (projectionConfig 100 [none, none, none, none]
          (projectionCodeCells
            (DovetailLayout.stageInputCodeAppend input stage
              (encodeBoolWord result)))) =
        projectionConfig 999 finalLeftRev []
    simp [DovetailLayout.stageInputCodeAppend]
    rw [runConfig_add]
    change
      Description.runConfig
        ((4 * stage + 12) +
          (projectionResultBoolWordCost result + (8 * result.length + 5)))
        (Description.runConfig
          (projectionInputBoolWordCost input)
          (projectionConfig 100
            (List.append [none, none, none, none]
              ([] : List (Option Bool)))
            (projectionCodeCells
              (encodeBoolWordAppend input
                (encodeNatAppend stage
                  (encodeBoolWord result)))))) =
        projectionConfig 999 finalLeftRev []
    rw [run_input_bool_word
      (stage := stage) (result := result) (baseLeftRev := [])]
    rw [runConfig_add]
    change
      Description.runConfig
        (projectionResultBoolWordCost result + (8 * result.length + 5))
        (Description.runConfig
          (4 * stage + 12)
          (projectionConfig 200 inputLeftRev
            (projectionCodeCells
              (encodeNatAppend stage
                (encodeBoolWord result))))) =
        projectionConfig 999 finalLeftRev []
    rw [run_stage_nat]
    change
      Description.runConfig
        (projectionResultBoolWordCost result + (8 * result.length + 5))
        (projectionConfig 300 stageLeftRev
          (projectionCodeCells (encodeBoolWord result))) =
        projectionConfig 999 finalLeftRev []
    rw [runConfig_add]
    change
      Description.runConfig
        (8 * result.length + 5)
        (Description.runConfig
          (projectionResultBoolWordCost result)
          (projectionConfig 300
            (List.append [none, none, none, none]
              (List.append (projectionStageTickCellsRev stage) inputLeftRev))
            (projectionCodeCells
              (encodeBoolWord result)))) =
        projectionConfig 999 finalLeftRev []
    rw [run_result_bool_word]
    change
      Description.runConfig
        (8 * result.length + 5)
        (projectionConfig 367
          (List.append projectionDoneCodeCells.reverse
            (List.append (projectionStageTickCellsRev stage) inputLeftRev))
          (List.append (projectionAllMarkedBoolWordCells result) [none])) =
        projectionConfig 999 finalLeftRev []
    rw [show 8 * result.length + 5 = (8 * result.length + 4) + 1 by
      omega,
      runConfig_add]
    rw [run_cleanup_all_marked_to_tail]
    rfl
  refine
    ⟨4 + projectionInputBoolWordCost input + (4 * stage + 12) +
        projectionResultBoolWordCost result + (8 * result.length + 5), ?_⟩
  constructor
  · rw [hrun]
    rfl
  · rw [hrun]
    rfl

theorem haltsWithOutput_encode
    (C : DovetailControllerLayout) :
    Description.HaltsWithOutput
      (encodeCodeWordAsInput
        (DovetailControllerLayout.encode C))
      (encodeCodeWordAsInput
        (DovetailControllerLayout.stageInputCode C)) := by
  rcases C with ⟨input, stage, result⟩
  let inputLeftRev :=
    List.append
      (projectionCodeCells (encodeBoolWord input)).reverse
      ([none, none, none, none] : List (Option Bool))
  let stageLeftRev :=
    List.append [none, none, none, none]
      (List.append (projectionStageTickCellsRev stage) inputLeftRev)
  let finalLeftRev :=
    List.append (List.replicate (4 * result.length + 1) none)
      (List.append [none, none, none, none]
        (List.append (List.replicate (4 * result.length) none)
          (List.append projectionDoneCodeCells.reverse
            (List.append (projectionStageTickCellsRev stage) inputLeftRev))))
  have hrun :
      Description.runConfig
          (4 + projectionInputBoolWordCost input + (4 * stage + 12) +
            projectionResultBoolWordCost result + (8 * result.length + 5))
          (Description.initial
            (encodeCodeWordAsInput
              (DovetailControllerLayout.encode
                { input := input, stage := stage, result := result }))) =
        projectionConfig 999 finalLeftRev [] := by
    rw [show
        4 + projectionInputBoolWordCost input + (4 * stage + 12) +
              projectionResultBoolWordCost result +
              (8 * result.length + 5) =
            4 +
              (projectionInputBoolWordCost input +
                ((4 * stage + 12) +
                  (projectionResultBoolWordCost result +
                    (8 * result.length + 5)))) by
        omega]
    rw [runConfig_add]
    change
      Description.runConfig
        (projectionInputBoolWordCost input +
          ((4 * stage + 12) +
            (projectionResultBoolWordCost result +
              (8 * result.length + 5))))
        (Description.runConfig 4
          (Description.initial
            (encodeCodeWordAsInput
              (DovetailControllerLayout.encode
                { input := input, stage := stage, result := result })))) =
        projectionConfig 999 finalLeftRev []
    simp [DovetailControllerLayout.encode,
      DovetailControllerLayout.encodeAppend,
      encodeCodeWordAsInput,
      encodeCodeSymbolAsInput]
    change
      Description.runConfig
        (projectionInputBoolWordCost input +
          ((4 * stage + 12) +
            (projectionResultBoolWordCost result +
              (8 * result.length + 5))))
        (Description.runConfig 4
          (Description.initial
            (List.append [false, false, false, false]
              (encodeCodeWordAsInput
                (DovetailLayout.stageInputCodeAppend input
                  stage (encodeBoolWordAppend result [])))))) =
        projectionConfig 999 finalLeftRev []
    rw [run_header]
    change
      Description.runConfig
        (projectionInputBoolWordCost input +
          ((4 * stage + 12) +
            (projectionResultBoolWordCost result +
              (8 * result.length + 5))))
        (projectionConfig 100 [none, none, none, none]
          (projectionCodeCells
            (DovetailLayout.stageInputCodeAppend input stage
              (encodeBoolWord result)))) =
        projectionConfig 999 finalLeftRev []
    simp [DovetailLayout.stageInputCodeAppend]
    rw [runConfig_add]
    change
      Description.runConfig
        ((4 * stage + 12) +
          (projectionResultBoolWordCost result + (8 * result.length + 5)))
        (Description.runConfig
          (projectionInputBoolWordCost input)
          (projectionConfig 100
            (List.append [none, none, none, none]
              ([] : List (Option Bool)))
            (projectionCodeCells
              (encodeBoolWordAppend input
                (encodeNatAppend stage
                  (encodeBoolWord result)))))) =
        projectionConfig 999 finalLeftRev []
    rw [run_input_bool_word
      (stage := stage) (result := result) (baseLeftRev := [])]
    rw [runConfig_add]
    change
      Description.runConfig
        (projectionResultBoolWordCost result + (8 * result.length + 5))
        (Description.runConfig
          (4 * stage + 12)
          (projectionConfig 200 inputLeftRev
            (projectionCodeCells
              (encodeNatAppend stage
                (encodeBoolWord result))))) =
        projectionConfig 999 finalLeftRev []
    rw [run_stage_nat]
    change
      Description.runConfig
        (projectionResultBoolWordCost result + (8 * result.length + 5))
        (projectionConfig 300 stageLeftRev
          (projectionCodeCells (encodeBoolWord result))) =
        projectionConfig 999 finalLeftRev []
    rw [runConfig_add]
    change
      Description.runConfig
        (8 * result.length + 5)
        (Description.runConfig
          (projectionResultBoolWordCost result)
          (projectionConfig 300
            (List.append [none, none, none, none]
              (List.append (projectionStageTickCellsRev stage) inputLeftRev))
            (projectionCodeCells
              (encodeBoolWord result)))) =
        projectionConfig 999 finalLeftRev []
    rw [run_result_bool_word]
    change
      Description.runConfig
        (8 * result.length + 5)
        (projectionConfig 367
          (List.append projectionDoneCodeCells.reverse
            (List.append (projectionStageTickCellsRev stage) inputLeftRev))
          (List.append (projectionAllMarkedBoolWordCells result) [none])) =
        projectionConfig 999 finalLeftRev []
    rw [show 8 * result.length + 5 = (8 * result.length + 4) + 1 by
      omega,
      runConfig_add]
    rw [run_cleanup_all_marked_to_tail]
    rfl
  refine
    ⟨4 + projectionInputBoolWordCost input + (4 * stage + 12) +
        projectionResultBoolWordCost result + (8 * result.length + 5), ?_⟩
  constructor
  · rw [hrun]
    rfl
  · rw [hrun]
    change
      Tape.normalizedOutput
          (projectionTapeAtCells finalLeftRev []) =
        encodeCodeWordAsInput
          (DovetailControllerLayout.stageInputCode
            { input := input, stage := stage, result := result })
    simpa [finalLeftRev, inputLeftRev,
      DovetailControllerLayout.stageInputCode] using
        final_normalizedOutput
          input result stage

theorem state_ne_halt_of_later_ne_halt
    {c : Configuration} {n k : Nat}
    (hle : n ≤ k)
    (hlater :
      (Description.runConfig k c).state ≠
        Description.halt) :
    (Description.runConfig n c).state ≠
      Description.halt :=
  CommonGround.SeqComposition.runConfig_state_ne_halt_of_later_ne_halt
    haltTransitionFree hle hlater

theorem ne_halt_of_reaches_stuck
    {c stuck : Configuration} {k n : Nat}
    (hrun :
      Description.runConfig k c = stuck)
    (hstep :
      Description.stepConfig stuck =
        none)
    (hstuck :
      stuck.state ≠ Description.halt) :
    (Description.runConfig n c).state ≠
      Description.halt :=
  CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
    haltTransitionFree hrun hstep hstuck

theorem ne_halt_of_reaches_stepConfig_none
    {c : Configuration} {k n : Nat}
    (hstep :
      Description.stepConfig
        (Description.runConfig k c) =
        none)
    (hstate :
      (Description.runConfig k c).state ≠
        Description.halt) :
    (Description.runConfig n c).state ≠
      Description.halt := by
  exact
    ne_halt_of_reaches_stuck
      (k := k) (stuck := Description.runConfig k c)
      rfl hstep hstate
private theorem stepConfig_projectionConfig_nil_none
    {state : Nat}
    (hlookup : Description.lookupTransition state none = none)
    (leftRev : List (Option Bool)) :
    Description.stepConfig (projectionConfig state leftRev []) = none := by
  simp [stepConfig, projectionConfig,
    projectionTapeAtCells, Tape.read, hlookup]
private theorem stepConfig_projectionConfig_cons_none
    {state : Nat} {cell : Option Bool}
    (hlookup : Description.lookupTransition state cell = none)
    (leftRev tail : List (Option Bool)) :
    Description.stepConfig
        (projectionConfig state leftRev (cell :: tail)) =
      none := by
  simp [stepConfig, projectionConfig,
    projectionTapeAtCells, Tape.read, hlookup]
private theorem lookupTransition_100_none :
    Description.lookupTransition 100 none = none := by
  native_decide
private theorem lookupTransition_100_true :
    Description.lookupTransition 100 (some true) = none := by
  native_decide
private theorem lookupTransition_101_true :
    Description.lookupTransition 101 (some true) = none := by
  native_decide
private theorem lookupTransition_102_false :
    Description.lookupTransition 102 (some false) = none := by
  native_decide
private theorem lookupTransition_120_none :
    Description.lookupTransition 120 none = none := by
  native_decide
private theorem lookupTransition_120_true :
    Description.lookupTransition 120 (some true) = none := by
  native_decide
private theorem lookupTransition_121_true :
    Description.lookupTransition 121 (some true) = none := by
  native_decide
private theorem lookupTransition_122_false :
    Description.lookupTransition 122 (some false) = none := by
  native_decide
private theorem lookupTransition_130_none :
    Description.lookupTransition 130 none = none := by
  native_decide
private theorem lookupTransition_130_true :
    Description.lookupTransition 130 (some true) = none := by
  native_decide
private theorem lookupTransition_131_false :
    Description.lookupTransition 131 (some false) = none := by
  native_decide
private theorem lookupTransition_133_false :
    Description.lookupTransition 133 (some false) = none := by
  native_decide
private theorem lookupTransition_134_true :
    Description.lookupTransition 134 (some true) = none := by
  native_decide
private theorem lookupTransition_200_none :
    Description.lookupTransition 200 none = none := by
  native_decide
private theorem lookupTransition_200_true :
    Description.lookupTransition 200 (some true) = none := by
  native_decide
private theorem lookupTransition_201_true :
    Description.lookupTransition 201 (some true) = none := by
  native_decide
private theorem lookupTransition_202_false :
    Description.lookupTransition 202 (some false) = none := by
  native_decide
private theorem lookupTransition_300_none :
    Description.lookupTransition 300 none = none := by
  native_decide
private theorem lookupTransition_300_true :
    Description.lookupTransition 300 (some true) = none := by
  native_decide
private theorem lookupTransition_301_true :
    Description.lookupTransition 301 (some true) = none := by
  native_decide
private theorem lookupTransition_302_false :
    Description.lookupTransition 302 (some false) = none := by
  native_decide
private theorem lookupTransition_320_none :
    Description.lookupTransition 320 none = none := by
  native_decide
private theorem lookupTransition_320_true :
    Description.lookupTransition 320 (some true) = none := by
  native_decide
private theorem lookupTransition_321_true :
    Description.lookupTransition 321 (some true) = none := by
  native_decide
private theorem lookupTransition_322_false :
    Description.lookupTransition 322 (some false) = none := by
  native_decide
private theorem lookupTransition_330_none :
    Description.lookupTransition 330 none = none := by
  native_decide
private theorem lookupTransition_330_true :
    Description.lookupTransition 330 (some true) = none := by
  native_decide
private theorem lookupTransition_331_false :
    Description.lookupTransition 331 (some false) = none := by
  native_decide
private theorem lookupTransition_333_false :
    Description.lookupTransition 333 (some false) = none := by
  native_decide
private theorem lookupTransition_334_true :
    Description.lookupTransition 334 (some true) = none := by
  native_decide

theorem ne_halt_of_reaches_ne_halt_region
    {c mid : Configuration} {k n : Nat}
    (hrun :
      Description.runConfig k c = mid)
    (hmid :
      forall m : Nat,
        (Description.runConfig m
          mid).state ≠
          Description.halt) :
    (Description.runConfig n c).state ≠
      Description.halt :=
  CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_ne_halt_region
    haltTransitionFree hrun hmid

theorem run_state200_decodeNat_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : decodeNat tokens = none) (n : Nat) :
    (Description.runConfig n
      (projectionConfig 200 leftRev (projectionCodeCells tokens))).state ≠
      Description.halt := by
  induction tokens generalizing leftRev n with
  | nil =>
      exact
        ne_halt_of_reaches_stepConfig_none
          (k := 0) (by
            change Description.stepConfig (projectionConfig 200 _ []) = none
            exact stepConfig_projectionConfig_nil_none
              lookupTransition_200_none _) (by
            change (200 : Nat) ≠ 999
            omega)
  | cons symbol rest ih =>
      cases symbol with
      | header =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 2) (by
                change Description.stepConfig
                  (projectionConfig 202 _ (some false :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_202_false _ _) (by
                change (202 : Nat) ≠ 999
                omega)
      | transition =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 2) (by
                change Description.stepConfig
                  (projectionConfig 202 _ (some false :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_202_false _ _) (by
                change (202 : Nat) ≠ 999
                omega)
      | tick =>
          cases hrest : decodeNat rest with
          | none =>
              apply
                ne_halt_of_reaches_ne_halt_region
                  (k := 4)
                  (mid :=
                    projectionConfig 200
                      (List.append projectionTickCodeCellsRev leftRev)
                      (projectionCodeCells rest))
              · change
                  Description.runConfig 4
                    (projectionConfig 200 leftRev
                      (List.append projectionTickCodeCells
                        (projectionCodeCells rest))) =
                    projectionConfig 200
                      (List.append projectionTickCodeCellsRev leftRev)
                      (projectionCodeCells rest)
                rw [run_stage_tick]
              · intro m
                exact ih (List.append projectionTickCodeCellsRev leftRev)
                  hrest m
          | some parsed =>
              simp [decodeNat, hrest] at hdecode
      | done =>
          simp [decodeNat] at hdecode
      | blank =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                change Description.stepConfig
                  (projectionConfig 201 _ (some true :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_201_true _ _) (by
                change (201 : Nat) ≠ 999
                omega)
      | zero =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                change Description.stepConfig
                  (projectionConfig 201 _ (some true :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_201_true _ _) (by
                change (201 : Nat) ≠ 999
                omega)
      | one =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                change Description.stepConfig
                  (projectionConfig 201 _ (some true :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_201_true _ _) (by
                change (201 : Nat) ≠ 999
                omega)
      | moveLeft =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                change Description.stepConfig
                  (projectionConfig 201 _ (some true :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_201_true _ _) (by
                change (201 : Nat) ≠ 999
                omega)
      | moveRight =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 0) (by
                change Description.stepConfig
                  (projectionConfig 200 _ (some true :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_200_true _ _) (by
                change (200 : Nat) ≠ 999
                omega)

theorem run_state120_decodeNat_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : decodeNat tokens = none) (n : Nat) :
    (Description.runConfig n
      (projectionConfig 120 leftRev (projectionCodeCells tokens))).state ≠
      Description.halt := by
  induction tokens generalizing leftRev n with
  | nil =>
      exact
        ne_halt_of_reaches_stepConfig_none
          (k := 0) (by
            change Description.stepConfig (projectionConfig 120 _ []) = none
            exact stepConfig_projectionConfig_nil_none
              lookupTransition_120_none _) (by
            change (120 : Nat) ≠ 999
            omega)
  | cons symbol rest ih =>
      cases symbol with
      | header =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 2) (by
                change Description.stepConfig
                  (projectionConfig 122 _ (some false :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_122_false _ _) (by
                change (122 : Nat) ≠ 999
                omega)
      | transition =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 2) (by
                change Description.stepConfig
                  (projectionConfig 122 _ (some false :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_122_false _ _) (by
                change (122 : Nat) ≠ 999
                omega)
      | tick =>
          cases hrest : decodeNat rest with
          | none =>
              apply
                ne_halt_of_reaches_ne_halt_region
                  (k := 4)
                  (mid :=
                    projectionConfig 120
                      (List.append projectionTickCodeCellsRev leftRev)
                      (projectionCodeCells rest))
              · change
                  Description.runConfig 4
                    (projectionConfig 120 leftRev
                      (List.append projectionTickCodeCells
                        (projectionCodeCells rest))) =
                    projectionConfig 120
                      (List.append projectionTickCodeCellsRev leftRev)
                      (projectionCodeCells rest)
                rw [run_state120_tick]
                rfl
              · intro m
                exact ih (List.append projectionTickCodeCellsRev leftRev)
                  hrest m
          | some parsed =>
              simp [decodeNat, hrest] at hdecode
      | done =>
          simp [decodeNat] at hdecode
      | blank =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                change Description.stepConfig
                  (projectionConfig 121 _ (some true :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_121_true _ _) (by
                change (121 : Nat) ≠ 999
                omega)
      | zero =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                change Description.stepConfig
                  (projectionConfig 121 _ (some true :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_121_true _ _) (by
                change (121 : Nat) ≠ 999
                omega)
      | one =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                change Description.stepConfig
                  (projectionConfig 121 _ (some true :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_121_true _ _) (by
                change (121 : Nat) ≠ 999
                omega)
      | moveLeft =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                change Description.stepConfig
                  (projectionConfig 121 _ (some true :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_121_true _ _) (by
                change (121 : Nat) ≠ 999
                omega)
      | moveRight =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 0) (by
                change Description.stepConfig
                  (projectionConfig 120 _ (some true :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_120_true _ _) (by
                change (120 : Nat) ≠ 999
                omega)

theorem run_state100_decodeNat_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : decodeNat tokens = none) (n : Nat) :
    (Description.runConfig n
      (projectionConfig 100 leftRev (projectionCodeCells tokens))).state ≠
      Description.halt := by
  induction tokens generalizing leftRev n with
  | nil =>
      exact
        ne_halt_of_reaches_stepConfig_none
          (k := 0) (by
            change Description.stepConfig (projectionConfig 100 _ []) = none
            exact stepConfig_projectionConfig_nil_none
              lookupTransition_100_none _) (by
            change (100 : Nat) ≠ 999
            omega)
  | cons symbol rest ih =>
      cases symbol with
      | header =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 2) (by
                change Description.stepConfig
                  (projectionConfig 102 _ (some false :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_102_false _ _) (by
                change (102 : Nat) ≠ 999
                omega)
      | transition =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 2) (by
                change Description.stepConfig
                  (projectionConfig 102 _ (some false :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_102_false _ _) (by
                change (102 : Nat) ≠ 999
                omega)
      | tick =>
          cases hrest : decodeNat rest with
          | none =>
              apply
                ne_halt_of_reaches_ne_halt_region
                  (k := 4)
                  (mid :=
                    projectionConfig 120
                      (List.append projectionMarkedTickCodeCells.reverse
                        leftRev)
                      (projectionCodeCells rest))
              · change
                  Description.runConfig 4
                    (projectionConfig 100 leftRev
                      (List.append projectionTickCodeCells
                        (projectionCodeCells rest))) =
                    projectionConfig 120
                      (List.append projectionMarkedTickCodeCells.reverse
                        leftRev)
                      (projectionCodeCells rest)
                rw [run_state100_mark_tick]
              · intro m
                exact
                  run_state120_decodeNat_none_ne_halt
                    rest
                    (List.append projectionMarkedTickCodeCells.reverse leftRev)
                    hrest m
          | some parsed =>
              simp [decodeNat, hrest] at hdecode
      | done =>
          simp [decodeNat] at hdecode
      | blank =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                change Description.stepConfig
                  (projectionConfig 101 _ (some true :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_101_true _ _) (by
                change (101 : Nat) ≠ 999
                omega)
      | zero =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                change Description.stepConfig
                  (projectionConfig 101 _ (some true :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_101_true _ _) (by
                change (101 : Nat) ≠ 999
                omega)
      | one =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                change Description.stepConfig
                  (projectionConfig 101 _ (some true :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_101_true _ _) (by
                change (101 : Nat) ≠ 999
                omega)
      | moveLeft =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                change Description.stepConfig
                  (projectionConfig 101 _ (some true :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_101_true _ _) (by
                change (101 : Nat) ≠ 999
                omega)
      | moveRight =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 0) (by
                change Description.stepConfig
                  (projectionConfig 100 _ (some true :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_100_true _ _) (by
                change (100 : Nat) ≠ 999
                omega)

theorem run_state320_decodeNat_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : decodeNat tokens = none) (n : Nat) :
    (Description.runConfig n
      (projectionConfig 320 leftRev (projectionCodeCells tokens))).state ≠
      Description.halt := by
  induction tokens generalizing leftRev n with
  | nil =>
      exact
        ne_halt_of_reaches_stepConfig_none
          (k := 0) (by
            change Description.stepConfig (projectionConfig 320 _ []) = none
            exact stepConfig_projectionConfig_nil_none
              lookupTransition_320_none _) (by
            change (320 : Nat) ≠ 999
            omega)
  | cons symbol rest ih =>
      cases symbol with
      | header =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 2) (by
                change Description.stepConfig
                  (projectionConfig 322 _ (some false :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_322_false _ _) (by
                change (322 : Nat) ≠ 999
                omega)
      | transition =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 2) (by
                change Description.stepConfig
                  (projectionConfig 322 _ (some false :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_322_false _ _) (by
                change (322 : Nat) ≠ 999
                omega)
      | tick =>
          cases hrest : decodeNat rest with
          | none =>
              apply
                ne_halt_of_reaches_ne_halt_region
                  (k := 4)
                  (mid :=
                    projectionConfig 320
                      (List.append projectionTickCodeCellsRev leftRev)
                      (projectionCodeCells rest))
              · change
                  Description.runConfig 4
                    (projectionConfig 320 leftRev
                      (List.append projectionTickCodeCells
                        (projectionCodeCells rest))) =
                    projectionConfig 320
                      (List.append projectionTickCodeCellsRev leftRev)
                      (projectionCodeCells rest)
                rw [run_state320_tick]
                rfl
              · intro m
                exact ih (List.append projectionTickCodeCellsRev leftRev)
                  hrest m
          | some parsed =>
              simp [decodeNat, hrest] at hdecode
      | done =>
          simp [decodeNat] at hdecode
      | blank =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                change Description.stepConfig
                  (projectionConfig 321 _ (some true :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_321_true _ _) (by
                change (321 : Nat) ≠ 999
                omega)
      | zero =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                change Description.stepConfig
                  (projectionConfig 321 _ (some true :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_321_true _ _) (by
                change (321 : Nat) ≠ 999
                omega)
      | one =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                change Description.stepConfig
                  (projectionConfig 321 _ (some true :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_321_true _ _) (by
                change (321 : Nat) ≠ 999
                omega)
      | moveLeft =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                change Description.stepConfig
                  (projectionConfig 321 _ (some true :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_321_true _ _) (by
                change (321 : Nat) ≠ 999
                omega)
      | moveRight =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 0) (by
                change Description.stepConfig
                  (projectionConfig 320 _ (some true :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_320_true _ _) (by
                change (320 : Nat) ≠ 999
                omega)

theorem run_state300_decodeNat_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : decodeNat tokens = none) (n : Nat) :
    (Description.runConfig n
      (projectionConfig 300 leftRev (projectionCodeCells tokens))).state ≠
      Description.halt := by
  induction tokens generalizing leftRev n with
  | nil =>
      exact
        ne_halt_of_reaches_stepConfig_none
          (k := 0) (by
            change Description.stepConfig (projectionConfig 300 _ []) = none
            exact stepConfig_projectionConfig_nil_none
              lookupTransition_300_none _) (by
            change (300 : Nat) ≠ 999
            omega)
  | cons symbol rest ih =>
      cases symbol with
      | header =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 2) (by
                change Description.stepConfig
                  (projectionConfig 302 _ (some false :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_302_false _ _) (by
                change (302 : Nat) ≠ 999
                omega)
      | transition =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 2) (by
                change Description.stepConfig
                  (projectionConfig 302 _ (some false :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_302_false _ _) (by
                change (302 : Nat) ≠ 999
                omega)
      | tick =>
          cases hrest : decodeNat rest with
          | none =>
              apply
                ne_halt_of_reaches_ne_halt_region
                  (k := 4)
                  (mid :=
                    projectionConfig 320
                      (List.append projectionMarkedTickCodeCells.reverse leftRev)
                      (projectionCodeCells rest))
              · change
                  Description.runConfig 4
                    (projectionConfig 300 leftRev
                      (List.append projectionTickCodeCells
                        (projectionCodeCells rest))) =
                    projectionConfig 320
                      (List.append projectionMarkedTickCodeCells.reverse leftRev)
                      (projectionCodeCells rest)
                rw [run_state300_mark_tick]
              · intro m
                exact
                  run_state320_decodeNat_none_ne_halt
                    rest
                    (List.append projectionMarkedTickCodeCells.reverse leftRev)
                    hrest m
          | some parsed =>
              simp [decodeNat, hrest] at hdecode
      | done =>
          simp [decodeNat] at hdecode
      | blank =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                change Description.stepConfig
                  (projectionConfig 301 _ (some true :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_301_true _ _) (by
                change (301 : Nat) ≠ 999
                omega)
      | zero =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                change Description.stepConfig
                  (projectionConfig 301 _ (some true :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_301_true _ _) (by
                change (301 : Nat) ≠ 999
                omega)
      | one =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                change Description.stepConfig
                  (projectionConfig 301 _ (some true :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_301_true _ _) (by
                change (301 : Nat) ≠ 999
                omega)
      | moveLeft =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                change Description.stepConfig
                  (projectionConfig 301 _ (some true :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_301_true _ _) (by
                change (301 : Nat) ≠ 999
                omega)
      | moveRight =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 0) (by
                change Description.stepConfig
                  (projectionConfig 300 _ (some true :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_300_true _ _) (by
                change (300 : Nat) ≠ 999
                omega)

theorem run_state330_decodeCell_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : decodeCell tokens = none) (n : Nat) :
    (Description.runConfig n
      (projectionConfig 330 leftRev (projectionCodeCells tokens))).state ≠
      Description.halt := by
  cases tokens with
  | nil =>
      exact
        ne_halt_of_reaches_stepConfig_none
          (k := 0) (by
            change Description.stepConfig (projectionConfig 330 _ []) = none
            exact stepConfig_projectionConfig_nil_none
              lookupTransition_330_none _) (by
            change (330 : Nat) ≠ 999
            omega)
  | cons symbol rest =>
      cases symbol with
      | header =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                change Description.stepConfig
                  (projectionConfig 331 _ (some false :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_331_false _ _) (by
                change (331 : Nat) ≠ 999
                omega)
      | transition =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                change Description.stepConfig
                  (projectionConfig 331 _ (some false :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_331_false _ _) (by
                change (331 : Nat) ≠ 999
                omega)
      | tick =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                change Description.stepConfig
                  (projectionConfig 331 _ (some false :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_331_false _ _) (by
                change (331 : Nat) ≠ 999
                omega)
      | done =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                change Description.stepConfig
                  (projectionConfig 331 _ (some false :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_331_false _ _) (by
                change (331 : Nat) ≠ 999
                omega)
      | blank =>
          simp [decodeCell] at hdecode
      | zero =>
          simp [decodeCell] at hdecode
      | one =>
          simp [decodeCell] at hdecode
      | moveLeft =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 3) (by
                change Description.stepConfig
                  (projectionConfig 334 _ (some true :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_334_true _ _) (by
                change (334 : Nat) ≠ 999
                omega)
      | moveRight =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 0) (by
                change Description.stepConfig
                  (projectionConfig 330 _ (some true :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_330_true _ _) (by
                change (330 : Nat) ≠ 999
                omega)

theorem run_state330_blank_cell_ne_halt
    (suffix : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (n : Nat) :
    (Description.runConfig n
      (projectionConfig 330 leftRev
        (projectionCodeCells
          (encodeCellAppend none suffix)))).state ≠
      Description.halt := by
  exact
    ne_halt_of_reaches_stepConfig_none
      (k := 3) (by
        change Description.stepConfig
          (projectionConfig 333 _ (some false :: _)) = none
        exact stepConfig_projectionConfig_cons_none
          lookupTransition_333_false _ _) (by
        change (333 : Nat) ≠ 999
        omega)

theorem run_state130_decodeCell_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : decodeCell tokens = none) (n : Nat) :
    (Description.runConfig n
      (projectionConfig 130 leftRev (projectionCodeCells tokens))).state ≠
      Description.halt := by
  cases tokens with
  | nil =>
      exact
        ne_halt_of_reaches_stepConfig_none
          (k := 0) (by
            change Description.stepConfig (projectionConfig 130 _ []) = none
            exact stepConfig_projectionConfig_nil_none
              lookupTransition_130_none _) (by
            change (130 : Nat) ≠ 999
            omega)
  | cons symbol rest =>
      cases symbol with
      | header =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                change Description.stepConfig
                  (projectionConfig 131 _ (some false :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_131_false _ _) (by
                change (131 : Nat) ≠ 999
                omega)
      | transition =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                change Description.stepConfig
                  (projectionConfig 131 _ (some false :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_131_false _ _) (by
                change (131 : Nat) ≠ 999
                omega)
      | tick =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                change Description.stepConfig
                  (projectionConfig 131 _ (some false :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_131_false _ _) (by
                change (131 : Nat) ≠ 999
                omega)
      | done =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by
                change Description.stepConfig
                  (projectionConfig 131 _ (some false :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_131_false _ _) (by
                change (131 : Nat) ≠ 999
                omega)
      | blank =>
          simp [decodeCell] at hdecode
      | zero =>
          simp [decodeCell] at hdecode
      | one =>
          simp [decodeCell] at hdecode
      | moveLeft =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 3) (by
                change Description.stepConfig
                  (projectionConfig 134 _ (some true :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_134_true _ _) (by
                change (134 : Nat) ≠ 999
                omega)
      | moveRight =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 0) (by
                change Description.stepConfig
                  (projectionConfig 130 _ (some true :: _)) = none
                exact stepConfig_projectionConfig_cons_none
                  lookupTransition_130_true _ _) (by
                change (130 : Nat) ≠ 999
                omega)

theorem run_state130_blank_cell_ne_halt
    (suffix : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (n : Nat) :
    (Description.runConfig n
      (projectionConfig 130 leftRev
        (projectionCodeCells
          (encodeCellAppend none suffix)))).state ≠
      Description.halt := by
  exact
    ne_halt_of_reaches_stepConfig_none
      (k := 3) (by
        change Description.stepConfig
          (projectionConfig 133 _ (some false :: _)) = none
        exact stepConfig_projectionConfig_cons_none
          lookupTransition_133_false _ _) (by
        change (133 : Nat) ≠ 999
        omega)

theorem run_result_tail_decodeCells_none_ne_halt
    (marked : Word Bool) (len : Nat)
    (tokens : Word MachineCodeSymbol)
    (baseLeftRev : List (Option Bool))
    (hdecode : decodeCells len tokens = none)
    (n : Nat) :
    (Description.runConfig n
      (projectionConfig 300
        (List.append [none, none, none, none] baseLeftRev)
        (projectionResultTailWorkCells marked len
          (projectionCodeCells tokens)))).state ≠
      Description.halt := by
  induction len generalizing marked tokens baseLeftRev n with
  | zero =>
      simp [decodeCells] at hdecode
  | succ len ih =>
      cases hcell : decodeCell tokens with
      | none =>
          apply
            ne_halt_of_reaches_ne_halt_region
              (k := 8 * marked.length + 4 * len + 8)
              (mid :=
                projectionConfig 330
                  (projectionResultTailPayloadLeftRev marked len baseLeftRev)
                  (projectionCodeCells tokens))
          · exact
              run_result_tail_to_first_payload
                marked len (projectionCodeCells tokens) baseLeftRev
          · intro m
            exact
              run_state330_decodeCell_none_ne_halt
                tokens
                (projectionResultTailPayloadLeftRev marked len baseLeftRev)
                hcell m
      | some parsedCell =>
          rcases parsedCell with ⟨cell, restAfterCell⟩
          have htokens :
              tokens =
                encodeCellAppend cell restAfterCell :=
            decodeCell_eq_some_encodeCellAppend hcell
          cases cell with
          | none =>
              apply
                ne_halt_of_reaches_ne_halt_region
                  (k := 8 * marked.length + 4 * len + 8)
                  (mid :=
                    projectionConfig 330
                      (projectionResultTailPayloadLeftRev marked len
                        baseLeftRev)
                      (projectionCodeCells
                        (encodeCellAppend none
                          restAfterCell)))
              · rw [htokens]
                exact
                  run_result_tail_to_first_payload
                    marked len
                    (projectionCodeCells
                      (encodeCellAppend none
                        restAfterCell))
                    baseLeftRev
              · intro m
                exact
                  run_state330_blank_cell_ne_halt
                    restAfterCell
                    (projectionResultTailPayloadLeftRev marked len
                      baseLeftRev)
                    m
          | some b =>
              cases hrest :
                  decodeCells len restAfterCell with
              | none =>
                  apply
                    ne_halt_of_reaches_ne_halt_region
                      (k := projectionResultMarkTailStepCost marked len)
                      (mid :=
                        projectionConfig 300
                          (List.append [none, none, none, none]
                            baseLeftRev)
                          (projectionResultTailWorkCells
                            (List.append marked [b]) len
                            (projectionCodeCells restAfterCell)))
                  · rw [htokens]
                    cases b with
                    | false =>
                        change
                          Description.runConfig
                            (projectionResultMarkTailStepCost marked len)
                            (projectionConfig 300
                              (List.append [none, none, none, none]
                                baseLeftRev)
                              (projectionResultTailWorkCells marked
                                (len + 1)
                                (List.append
                                  (projectionBoolCellCodeCells false)
                                  (projectionCodeCells restAfterCell)))) =
                            projectionConfig 300
                              (List.append [none, none, none, none]
                                baseLeftRev)
                              (projectionResultTailWorkCells
                                (List.append marked [false]) len
                                (projectionCodeCells restAfterCell))
                        rw [run_result_mark_one_tail]
                    | true =>
                        change
                        Description.runConfig
                          (projectionResultMarkTailStepCost marked len)
                          (projectionConfig 300
                            (List.append [none, none, none, none]
                              baseLeftRev)
                            (projectionResultTailWorkCells marked
                              (len + 1)
                              (List.append
                                (projectionBoolCellCodeCells true)
                                (projectionCodeCells restAfterCell)))) =
                          projectionConfig 300
                            (List.append [none, none, none, none]
                              baseLeftRev)
                            (projectionResultTailWorkCells
                              (List.append marked [true]) len
                              (projectionCodeCells restAfterCell))
                        rw [run_result_mark_one_tail]
                  · intro m
                    exact
                      ih (List.append marked [b]) restAfterCell
                        baseLeftRev hrest m
              | some parsedRest =>
                  simp [decodeCells, hcell, hrest] at hdecode

theorem run_result_tail_cellsToWord_none_ne_halt
    (marked : Word Bool) (cells : List (Option Bool))
    (suffix : Word MachineCodeSymbol)
    (baseLeftRev : List (Option Bool))
    (hword : cellsToWord? cells = none)
    (n : Nat) :
    (Description.runConfig n
      (projectionConfig 300
        (List.append [none, none, none, none] baseLeftRev)
        (projectionResultTailWorkCells marked cells.length
          (projectionCodeCells
            (encodeCellsAppend cells suffix))))).state ≠
      Description.halt := by
  induction cells generalizing marked suffix baseLeftRev n with
  | nil =>
      simp [cellsToWord?] at hword
  | cons cell rest ih =>
      cases cell with
      | none =>
          apply
            ne_halt_of_reaches_ne_halt_region
              (k := 8 * marked.length + 4 * rest.length + 8)
              (mid :=
                projectionConfig 330
                  (projectionResultTailPayloadLeftRev marked rest.length
                    baseLeftRev)
                  (projectionCodeCells
                    (encodeCellAppend none
                      (encodeCellsAppend rest suffix))))
          · change
              Description.runConfig
                  (8 * marked.length + 4 * rest.length + 8)
                  (projectionConfig 300
                    (List.append [none, none, none, none] baseLeftRev)
                    (projectionResultTailWorkCells marked
                      (rest.length + 1)
                      (projectionCodeCells
                        (encodeCellAppend none
                          (encodeCellsAppend rest suffix))))) =
                projectionConfig 330
                  (projectionResultTailPayloadLeftRev marked rest.length
                    baseLeftRev)
                  (projectionCodeCells
                    (encodeCellAppend none
                      (encodeCellsAppend rest suffix)))
            rw [run_result_tail_to_first_payload]
          · intro m
            exact
              run_state330_blank_cell_ne_halt
                (encodeCellsAppend rest suffix)
                (projectionResultTailPayloadLeftRev marked rest.length
                  baseLeftRev)
                m
      | some b =>
          cases hrest : cellsToWord? rest with
          | none =>
              apply
                ne_halt_of_reaches_ne_halt_region
                  (k := projectionResultMarkTailStepCost marked rest.length)
                  (mid :=
                    projectionConfig 300
                      (List.append [none, none, none, none] baseLeftRev)
                      (projectionResultTailWorkCells
                        (List.append marked [b]) rest.length
                        (projectionCodeCells
                          (encodeCellsAppend rest
                            suffix))))
              · cases b with
                | false =>
                    change
                      Description.runConfig
                        (projectionResultMarkTailStepCost marked rest.length)
                        (projectionConfig 300
                          (List.append [none, none, none, none] baseLeftRev)
                          (projectionResultTailWorkCells marked
                            (rest.length + 1)
                            (List.append (projectionBoolCellCodeCells false)
                              (projectionCodeCells
                                (encodeCellsAppend rest
                                  suffix))))) =
                        projectionConfig 300
                          (List.append [none, none, none, none] baseLeftRev)
                          (projectionResultTailWorkCells
                            (List.append marked [false]) rest.length
                            (projectionCodeCells
                              (encodeCellsAppend rest
                                suffix)))
                    rw [run_result_mark_one_tail]
                | true =>
                    change
                      Description.runConfig
                        (projectionResultMarkTailStepCost marked rest.length)
                        (projectionConfig 300
                          (List.append [none, none, none, none] baseLeftRev)
                          (projectionResultTailWorkCells marked
                            (rest.length + 1)
                            (List.append (projectionBoolCellCodeCells true)
                              (projectionCodeCells
                                (encodeCellsAppend rest
                                  suffix))))) =
                        projectionConfig 300
                          (List.append [none, none, none, none] baseLeftRev)
                          (projectionResultTailWorkCells
                            (List.append marked [true]) rest.length
                            (projectionCodeCells
                              (encodeCellsAppend rest
                                suffix)))
                    rw [run_result_mark_one_tail]
              · intro m
                exact
                  ih (List.append marked [b]) suffix baseLeftRev hrest m
          | some decoded =>
              simp [cellsToWord?, hrest] at hword

end ControllerStageInputProjection
end Computability
end FoC
