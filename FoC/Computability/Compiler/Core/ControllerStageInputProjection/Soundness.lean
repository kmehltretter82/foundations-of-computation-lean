import FoC.Computability.Compiler.Core.ControllerStageInputProjection.ResultRun

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

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
                        (MachineDescription.encodeBoolWord input)).reverse
                      [none, none, none, none])))))) []) =
      MachineDescription.encodeCodeWordAsInput
        (MachineDescription.DovetailLayout.stageInputCode input stage) := by
  simp [Tape.normalizedOutput, Tape.cells, projectionTapeAtCells,
    MachineDescription.DovetailLayout.stageInputCode,
    MachineDescription.DovetailLayout.stageInputCodeAppend,
    projectionStageTickCellsRev, projectionCodeCells_filterMap,
    projectionDoneCodeCells_filterMap]
  rw [encodeCodeWordAsInput_encodeBoolWordAppend]
  simp [MachineDescription.encodeNatAppend]
  rw [encodeCodeWordAsInput_encodeNat]
  simp

theorem haltsWithOutput_encode
    (C : MachineDescription.DovetailControllerLayout) :
    Description.HaltsWithOutput
      (MachineDescription.encodeCodeWordAsInput
        (MachineDescription.DovetailControllerLayout.encode C))
      (MachineDescription.encodeCodeWordAsInput
        (MachineDescription.DovetailControllerLayout.stageInputCode C)) := by
  rcases C with ⟨input, stage, result⟩
  let inputLeftRev :=
    List.append
      (projectionCodeCells (MachineDescription.encodeBoolWord input)).reverse
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
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.DovetailControllerLayout.encode
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
    rw [MachineDescription.runConfig_add]
    change
      Description.runConfig
        (projectionInputBoolWordCost input +
          ((4 * stage + 12) +
            (projectionResultBoolWordCost result +
              (8 * result.length + 5))))
        (Description.runConfig 4
          (Description.initial
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.DovetailControllerLayout.encode
                { input := input, stage := stage, result := result })))) =
        projectionConfig 999 finalLeftRev []
    simp [MachineDescription.DovetailControllerLayout.encode,
      MachineDescription.DovetailControllerLayout.encodeAppend,
      MachineDescription.encodeCodeWordAsInput,
      MachineDescription.encodeCodeSymbolAsInput]
    change
      Description.runConfig
        (projectionInputBoolWordCost input +
          ((4 * stage + 12) +
            (projectionResultBoolWordCost result +
              (8 * result.length + 5))))
        (Description.runConfig 4
          (Description.initial
            (List.append [false, false, false, false]
              (MachineDescription.encodeCodeWordAsInput
                (MachineDescription.DovetailLayout.stageInputCodeAppend input
                  stage (MachineDescription.encodeBoolWordAppend result [])))))) =
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
            (MachineDescription.DovetailLayout.stageInputCodeAppend input stage
              (MachineDescription.encodeBoolWord result)))) =
        projectionConfig 999 finalLeftRev []
    simp [MachineDescription.DovetailLayout.stageInputCodeAppend]
    rw [MachineDescription.runConfig_add]
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
              (MachineDescription.encodeBoolWordAppend input
                (MachineDescription.encodeNatAppend stage
                  (MachineDescription.encodeBoolWord result)))))) =
        projectionConfig 999 finalLeftRev []
    rw [run_input_bool_word
      (stage := stage) (result := result) (baseLeftRev := [])]
    rw [MachineDescription.runConfig_add]
    change
      Description.runConfig
        (projectionResultBoolWordCost result + (8 * result.length + 5))
        (Description.runConfig
          (4 * stage + 12)
          (projectionConfig 200 inputLeftRev
            (projectionCodeCells
              (MachineDescription.encodeNatAppend stage
                (MachineDescription.encodeBoolWord result))))) =
        projectionConfig 999 finalLeftRev []
    rw [run_stage_nat]
    change
      Description.runConfig
        (projectionResultBoolWordCost result + (8 * result.length + 5))
        (projectionConfig 300 stageLeftRev
          (projectionCodeCells (MachineDescription.encodeBoolWord result))) =
        projectionConfig 999 finalLeftRev []
    rw [MachineDescription.runConfig_add]
    change
      Description.runConfig
        (8 * result.length + 5)
        (Description.runConfig
          (projectionResultBoolWordCost result)
          (projectionConfig 300
            (List.append [none, none, none, none]
              (List.append (projectionStageTickCellsRev stage) inputLeftRev))
            (projectionCodeCells
              (MachineDescription.encodeBoolWord result)))) =
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
      MachineDescription.runConfig_add]
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
        MachineDescription.encodeCodeWordAsInput
          (MachineDescription.DovetailControllerLayout.stageInputCode
            { input := input, stage := stage, result := result })
    simpa [finalLeftRev, inputLeftRev,
      MachineDescription.DovetailControllerLayout.stageInputCode] using
        final_normalizedOutput
          input result stage

theorem state_ne_halt_of_later_ne_halt
    {c : MachineDescription.Configuration} {n k : Nat}
    (hle : n ≤ k)
    (hlater :
      (Description.runConfig k c).state ≠
        Description.halt) :
    (Description.runConfig n c).state ≠
      Description.halt := by
  intro hhalt
  have hk : k = n + (k - n) := by omega
  have hcfg :
      Description.runConfig n c =
        { state := Description.halt
          tape :=
            (Description.runConfig n c).tape } := by
    cases hrunN :
        Description.runConfig n c with
    | mk state tape =>
        simp [hrunN] at hhalt
        simp [hhalt]
  have hfinal :
      (Description.runConfig k c).state =
        Description.halt := by
    rw [hk, MachineDescription.runConfig_add, hcfg,
      MachineDescription.runConfig_halt
        haltTransitionFree]
  exact hlater hfinal

theorem ne_halt_of_reaches_stuck
    {c stuck : MachineDescription.Configuration} {k n : Nat}
    (hrun :
      Description.runConfig k c = stuck)
    (hstep :
      Description.stepConfig stuck =
        none)
    (hstuck :
      stuck.state ≠ Description.halt) :
    (Description.runConfig n c).state ≠
      Description.halt := by
  by_cases hle : n ≤ k
  · apply
      state_ne_halt_of_later_ne_halt
        hle
    rw [hrun]
    exact hstuck
  · have hkn : k ≤ n := by omega
    have hn : n = k + (n - k) := by omega
    rw [hn, MachineDescription.runConfig_add, hrun,
      MachineDescription.runConfig_of_stepConfig_none hstep]
    exact hstuck

theorem ne_halt_of_reaches_stepConfig_none
    {c : MachineDescription.Configuration} {k n : Nat}
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

theorem ne_halt_of_reaches_ne_halt_region
    {c mid : MachineDescription.Configuration} {k n : Nat}
    (hrun :
      Description.runConfig k c = mid)
    (hmid :
      forall m : Nat,
        (Description.runConfig m
          mid).state ≠
          Description.halt) :
    (Description.runConfig n c).state ≠
      Description.halt := by
  by_cases hle : n ≤ k
  · apply
      state_ne_halt_of_later_ne_halt
        hle
    rw [hrun]
    exact hmid 0
  · have hkn : k ≤ n := by omega
    have hn : n = k + (n - k) := by omega
    rw [hn, MachineDescription.runConfig_add, hrun]
    exact hmid (n - k)

theorem run_state200_decodeNat_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : MachineDescription.decodeNat tokens = none) (n : Nat) :
    (Description.runConfig n
      (projectionConfig 200 leftRev (projectionCodeCells tokens))).state ≠
      Description.halt := by
  induction tokens generalizing leftRev n with
  | nil =>
      exact
        ne_halt_of_reaches_stepConfig_none
          (k := 0) (by rfl) (by
            change (200 : Nat) ≠ 999
            omega)
  | cons symbol rest ih =>
      cases symbol with
      | header =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 2) (by rfl) (by
                change (202 : Nat) ≠ 999
                omega)
      | transition =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 2) (by rfl) (by
                change (202 : Nat) ≠ 999
                omega)
      | tick =>
          cases hrest : MachineDescription.decodeNat rest with
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
              simp [MachineDescription.decodeNat, hrest] at hdecode
      | done =>
          simp [MachineDescription.decodeNat] at hdecode
      | blank =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (201 : Nat) ≠ 999
                omega)
      | zero =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (201 : Nat) ≠ 999
                omega)
      | one =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (201 : Nat) ≠ 999
                omega)
      | moveLeft =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (201 : Nat) ≠ 999
                omega)
      | moveRight =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 0) (by rfl) (by
                change (200 : Nat) ≠ 999
                omega)

theorem run_state120_decodeNat_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : MachineDescription.decodeNat tokens = none) (n : Nat) :
    (Description.runConfig n
      (projectionConfig 120 leftRev (projectionCodeCells tokens))).state ≠
      Description.halt := by
  induction tokens generalizing leftRev n with
  | nil =>
      exact
        ne_halt_of_reaches_stepConfig_none
          (k := 0) (by rfl) (by
            change (120 : Nat) ≠ 999
            omega)
  | cons symbol rest ih =>
      cases symbol with
      | header =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 2) (by rfl) (by
                change (122 : Nat) ≠ 999
                omega)
      | transition =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 2) (by rfl) (by
                change (122 : Nat) ≠ 999
                omega)
      | tick =>
          cases hrest : MachineDescription.decodeNat rest with
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
              simp [MachineDescription.decodeNat, hrest] at hdecode
      | done =>
          simp [MachineDescription.decodeNat] at hdecode
      | blank =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (121 : Nat) ≠ 999
                omega)
      | zero =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (121 : Nat) ≠ 999
                omega)
      | one =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (121 : Nat) ≠ 999
                omega)
      | moveLeft =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (121 : Nat) ≠ 999
                omega)
      | moveRight =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 0) (by rfl) (by
                change (120 : Nat) ≠ 999
                omega)

theorem run_state100_decodeNat_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : MachineDescription.decodeNat tokens = none) (n : Nat) :
    (Description.runConfig n
      (projectionConfig 100 leftRev (projectionCodeCells tokens))).state ≠
      Description.halt := by
  induction tokens generalizing leftRev n with
  | nil =>
      exact
        ne_halt_of_reaches_stepConfig_none
          (k := 0) (by rfl) (by
            change (100 : Nat) ≠ 999
            omega)
  | cons symbol rest ih =>
      cases symbol with
      | header =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 2) (by rfl) (by
                change (102 : Nat) ≠ 999
                omega)
      | transition =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 2) (by rfl) (by
                change (102 : Nat) ≠ 999
                omega)
      | tick =>
          cases hrest : MachineDescription.decodeNat rest with
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
              simp [MachineDescription.decodeNat, hrest] at hdecode
      | done =>
          simp [MachineDescription.decodeNat] at hdecode
      | blank =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (101 : Nat) ≠ 999
                omega)
      | zero =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (101 : Nat) ≠ 999
                omega)
      | one =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (101 : Nat) ≠ 999
                omega)
      | moveLeft =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (101 : Nat) ≠ 999
                omega)
      | moveRight =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 0) (by rfl) (by
                change (100 : Nat) ≠ 999
                omega)

theorem run_state320_decodeNat_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : MachineDescription.decodeNat tokens = none) (n : Nat) :
    (Description.runConfig n
      (projectionConfig 320 leftRev (projectionCodeCells tokens))).state ≠
      Description.halt := by
  induction tokens generalizing leftRev n with
  | nil =>
      exact
        ne_halt_of_reaches_stepConfig_none
          (k := 0) (by rfl) (by
            change (320 : Nat) ≠ 999
            omega)
  | cons symbol rest ih =>
      cases symbol with
      | header =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 2) (by rfl) (by
                change (322 : Nat) ≠ 999
                omega)
      | transition =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 2) (by rfl) (by
                change (322 : Nat) ≠ 999
                omega)
      | tick =>
          cases hrest : MachineDescription.decodeNat rest with
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
              simp [MachineDescription.decodeNat, hrest] at hdecode
      | done =>
          simp [MachineDescription.decodeNat] at hdecode
      | blank =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (321 : Nat) ≠ 999
                omega)
      | zero =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (321 : Nat) ≠ 999
                omega)
      | one =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (321 : Nat) ≠ 999
                omega)
      | moveLeft =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (321 : Nat) ≠ 999
                omega)
      | moveRight =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 0) (by rfl) (by
                change (320 : Nat) ≠ 999
                omega)

theorem run_state300_decodeNat_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : MachineDescription.decodeNat tokens = none) (n : Nat) :
    (Description.runConfig n
      (projectionConfig 300 leftRev (projectionCodeCells tokens))).state ≠
      Description.halt := by
  induction tokens generalizing leftRev n with
  | nil =>
      exact
        ne_halt_of_reaches_stepConfig_none
          (k := 0) (by rfl) (by
            change (300 : Nat) ≠ 999
            omega)
  | cons symbol rest ih =>
      cases symbol with
      | header =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 2) (by rfl) (by
                change (302 : Nat) ≠ 999
                omega)
      | transition =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 2) (by rfl) (by
                change (302 : Nat) ≠ 999
                omega)
      | tick =>
          cases hrest : MachineDescription.decodeNat rest with
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
              simp [MachineDescription.decodeNat, hrest] at hdecode
      | done =>
          simp [MachineDescription.decodeNat] at hdecode
      | blank =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (301 : Nat) ≠ 999
                omega)
      | zero =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (301 : Nat) ≠ 999
                omega)
      | one =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (301 : Nat) ≠ 999
                omega)
      | moveLeft =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (301 : Nat) ≠ 999
                omega)
      | moveRight =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 0) (by rfl) (by
                change (300 : Nat) ≠ 999
                omega)

theorem run_state330_decodeCell_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : MachineDescription.decodeCell tokens = none) (n : Nat) :
    (Description.runConfig n
      (projectionConfig 330 leftRev (projectionCodeCells tokens))).state ≠
      Description.halt := by
  cases tokens with
  | nil =>
      exact
        ne_halt_of_reaches_stepConfig_none
          (k := 0) (by rfl) (by
            change (330 : Nat) ≠ 999
            omega)
  | cons symbol rest =>
      cases symbol with
      | header =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (331 : Nat) ≠ 999
                omega)
      | transition =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (331 : Nat) ≠ 999
                omega)
      | tick =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (331 : Nat) ≠ 999
                omega)
      | done =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (331 : Nat) ≠ 999
                omega)
      | blank =>
          simp [MachineDescription.decodeCell] at hdecode
      | zero =>
          simp [MachineDescription.decodeCell] at hdecode
      | one =>
          simp [MachineDescription.decodeCell] at hdecode
      | moveLeft =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 3) (by rfl) (by
                change (334 : Nat) ≠ 999
                omega)
      | moveRight =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 0) (by rfl) (by
                change (330 : Nat) ≠ 999
                omega)

theorem run_state330_blank_cell_ne_halt
    (suffix : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (n : Nat) :
    (Description.runConfig n
      (projectionConfig 330 leftRev
        (projectionCodeCells
          (MachineDescription.encodeCellAppend none suffix)))).state ≠
      Description.halt := by
  exact
    ne_halt_of_reaches_stepConfig_none
      (k := 3) (by
        cases suffix <;> rfl) (by
        change (333 : Nat) ≠ 999
        omega)

theorem run_state130_decodeCell_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : MachineDescription.decodeCell tokens = none) (n : Nat) :
    (Description.runConfig n
      (projectionConfig 130 leftRev (projectionCodeCells tokens))).state ≠
      Description.halt := by
  cases tokens with
  | nil =>
      exact
        ne_halt_of_reaches_stepConfig_none
          (k := 0) (by rfl) (by
            change (130 : Nat) ≠ 999
            omega)
  | cons symbol rest =>
      cases symbol with
      | header =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (131 : Nat) ≠ 999
                omega)
      | transition =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (131 : Nat) ≠ 999
                omega)
      | tick =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (131 : Nat) ≠ 999
                omega)
      | done =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (131 : Nat) ≠ 999
                omega)
      | blank =>
          simp [MachineDescription.decodeCell] at hdecode
      | zero =>
          simp [MachineDescription.decodeCell] at hdecode
      | one =>
          simp [MachineDescription.decodeCell] at hdecode
      | moveLeft =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 3) (by rfl) (by
                change (134 : Nat) ≠ 999
                omega)
      | moveRight =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 0) (by rfl) (by
                change (130 : Nat) ≠ 999
                omega)

theorem run_state130_blank_cell_ne_halt
    (suffix : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (n : Nat) :
    (Description.runConfig n
      (projectionConfig 130 leftRev
        (projectionCodeCells
          (MachineDescription.encodeCellAppend none suffix)))).state ≠
      Description.halt := by
  exact
    ne_halt_of_reaches_stepConfig_none
      (k := 3) (by
        cases suffix <;> rfl) (by
        change (133 : Nat) ≠ 999
        omega)

theorem run_result_tail_decodeCells_none_ne_halt
    (marked : Word Bool) (len : Nat)
    (tokens : Word MachineCodeSymbol)
    (baseLeftRev : List (Option Bool))
    (hdecode : MachineDescription.decodeCells len tokens = none)
    (n : Nat) :
    (Description.runConfig n
      (projectionConfig 300
        (List.append [none, none, none, none] baseLeftRev)
        (projectionResultTailWorkCells marked len
          (projectionCodeCells tokens)))).state ≠
      Description.halt := by
  induction len generalizing marked tokens baseLeftRev n with
  | zero =>
      simp [MachineDescription.decodeCells] at hdecode
  | succ len ih =>
      cases hcell : MachineDescription.decodeCell tokens with
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
                MachineDescription.encodeCellAppend cell restAfterCell :=
            MachineDescription.decodeCell_eq_some_encodeCellAppend hcell
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
                        (MachineDescription.encodeCellAppend none
                          restAfterCell)))
              · rw [htokens]
                exact
                  run_result_tail_to_first_payload
                    marked len
                    (projectionCodeCells
                      (MachineDescription.encodeCellAppend none
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
                  MachineDescription.decodeCells len restAfterCell with
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
                  simp [MachineDescription.decodeCells, hcell, hrest] at hdecode

theorem run_result_tail_cellsToWord_none_ne_halt
    (marked : Word Bool) (cells : List (Option Bool))
    (suffix : Word MachineCodeSymbol)
    (baseLeftRev : List (Option Bool))
    (hword : MachineDescription.cellsToWord? cells = none)
    (n : Nat) :
    (Description.runConfig n
      (projectionConfig 300
        (List.append [none, none, none, none] baseLeftRev)
        (projectionResultTailWorkCells marked cells.length
          (projectionCodeCells
            (MachineDescription.encodeCellsAppend cells suffix))))).state ≠
      Description.halt := by
  induction cells generalizing marked suffix baseLeftRev n with
  | nil =>
      simp [MachineDescription.cellsToWord?] at hword
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
                    (MachineDescription.encodeCellAppend none
                      (MachineDescription.encodeCellsAppend rest suffix))))
          · change
              Description.runConfig
                  (8 * marked.length + 4 * rest.length + 8)
                  (projectionConfig 300
                    (List.append [none, none, none, none] baseLeftRev)
                    (projectionResultTailWorkCells marked
                      (rest.length + 1)
                      (projectionCodeCells
                        (MachineDescription.encodeCellAppend none
                          (MachineDescription.encodeCellsAppend rest suffix))))) =
                projectionConfig 330
                  (projectionResultTailPayloadLeftRev marked rest.length
                    baseLeftRev)
                  (projectionCodeCells
                    (MachineDescription.encodeCellAppend none
                      (MachineDescription.encodeCellsAppend rest suffix)))
            rw [run_result_tail_to_first_payload]
          · intro m
            exact
              run_state330_blank_cell_ne_halt
                (MachineDescription.encodeCellsAppend rest suffix)
                (projectionResultTailPayloadLeftRev marked rest.length
                  baseLeftRev)
                m
      | some b =>
          cases hrest : MachineDescription.cellsToWord? rest with
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
                          (MachineDescription.encodeCellsAppend rest
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
                                (MachineDescription.encodeCellsAppend rest
                                  suffix))))) =
                        projectionConfig 300
                          (List.append [none, none, none, none] baseLeftRev)
                          (projectionResultTailWorkCells
                            (List.append marked [false]) rest.length
                            (projectionCodeCells
                              (MachineDescription.encodeCellsAppend rest
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
                                (MachineDescription.encodeCellsAppend rest
                                  suffix))))) =
                        projectionConfig 300
                          (List.append [none, none, none, none] baseLeftRev)
                          (projectionResultTailWorkCells
                            (List.append marked [true]) rest.length
                            (projectionCodeCells
                              (MachineDescription.encodeCellsAppend rest
                                suffix)))
                    rw [run_result_mark_one_tail]
              · intro m
                exact
                  ih (List.append marked [b]) suffix baseLeftRev hrest m
          | some decoded =>
              simp [MachineDescription.cellsToWord?, hrest] at hword

theorem run_state300_decodeBoolWord_none_ne_halt
    (tokens : Word MachineCodeSymbol)
    (baseLeftRev : List (Option Bool))
    (hdecode : MachineDescription.decodeBoolWord tokens = none)
    (n : Nat) :
    (Description.runConfig n
      (projectionConfig 300
        (List.append [none, none, none, none] baseLeftRev)
        (projectionCodeCells tokens))).state ≠
      Description.halt := by
  unfold MachineDescription.decodeBoolWord at hdecode
  cases hcells : MachineDescription.decodeCellList tokens with
  | none =>
      unfold MachineDescription.decodeCellList at hcells
      cases hnat : MachineDescription.decodeNat tokens with
      | none =>
          exact
            run_state300_decodeNat_none_ne_halt
              tokens (List.append [none, none, none, none] baseLeftRev)
              hnat n
      | some parsedNat =>
          rcases parsedNat with ⟨len, restAfterLen⟩
          simp [hnat] at hcells
          have htokens :
              tokens =
                MachineDescription.encodeNatAppend len restAfterLen :=
            MachineDescription.decodeNat_eq_some_encodeNatAppend hnat
          rw [htokens]
          rw [projectionCodeCells_encodeNatAppend]
          change
            (Description.runConfig n
              (projectionConfig 300
                (List.append [none, none, none, none] baseLeftRev)
                (projectionResultTailWorkCells ([] : Word Bool) len
                  (projectionCodeCells restAfterLen)))).state ≠
              Description.halt
          exact
            run_result_tail_decodeCells_none_ne_halt
              ([] : Word Bool) len restAfterLen baseLeftRev hcells n
  | some parsedCells =>
      rcases parsedCells with ⟨cells, suffix⟩
      cases hword : MachineDescription.cellsToWord? cells with
      | none =>
          have htokens :
              tokens =
                MachineDescription.encodeCellListAppend cells suffix :=
            MachineDescription.decodeCellList_eq_some_encodeCellListAppend
              hcells
          rw [htokens]
          rw [MachineDescription.encodeCellListAppend,
            projectionCodeCells_encodeNatAppend]
          change
            (Description.runConfig n
              (projectionConfig 300
                (List.append [none, none, none, none] baseLeftRev)
                (projectionResultTailWorkCells ([] : Word Bool) cells.length
                  (projectionCodeCells
                    (MachineDescription.encodeCellsAppend cells
                      suffix))))).state ≠
              Description.halt
          exact
            run_result_tail_cellsToWord_none_ne_halt
              ([] : Word Bool) cells suffix baseLeftRev hword n
      | some decoded =>
          simp [hcells, hword] at hdecode

theorem run_input_tail_decodeCells_none_ne_halt
    (marked : Word Bool) (len : Nat)
    (tokens : Word MachineCodeSymbol)
    (baseLeftRev : List (Option Bool))
    (hdecode : MachineDescription.decodeCells len tokens = none)
    (n : Nat) :
    (Description.runConfig n
      (projectionConfig 100
        (List.append [none, none, none, none] baseLeftRev)
        (projectionResultTailWorkCells marked len
          (projectionCodeCells tokens)))).state ≠
      Description.halt := by
  induction len generalizing marked tokens baseLeftRev n with
  | zero =>
      simp [MachineDescription.decodeCells] at hdecode
  | succ len ih =>
      cases hcell : MachineDescription.decodeCell tokens with
      | none =>
          apply
            ne_halt_of_reaches_ne_halt_region
              (k := 8 * marked.length + 4 * len + 8)
              (mid :=
                projectionConfig 130
                  (projectionResultTailPayloadLeftRev marked len baseLeftRev)
                  (projectionCodeCells tokens))
          · exact
              run_input_tail_to_first_payload
                marked len (projectionCodeCells tokens) baseLeftRev
          · intro m
            exact
              run_state130_decodeCell_none_ne_halt
                tokens
                (projectionResultTailPayloadLeftRev marked len baseLeftRev)
                hcell m
      | some parsedCell =>
          rcases parsedCell with ⟨cell, restAfterCell⟩
          have htokens :
              tokens =
                MachineDescription.encodeCellAppend cell restAfterCell :=
            MachineDescription.decodeCell_eq_some_encodeCellAppend hcell
          cases cell with
          | none =>
              apply
                ne_halt_of_reaches_ne_halt_region
                  (k := 8 * marked.length + 4 * len + 8)
                  (mid :=
                    projectionConfig 130
                      (projectionResultTailPayloadLeftRev marked len
                        baseLeftRev)
                      (projectionCodeCells
                        (MachineDescription.encodeCellAppend none
                          restAfterCell)))
              · rw [htokens]
                exact
                  run_input_tail_to_first_payload
                    marked len
                    (projectionCodeCells
                      (MachineDescription.encodeCellAppend none
                        restAfterCell))
                    baseLeftRev
              · intro m
                exact
                  run_state130_blank_cell_ne_halt
                    restAfterCell
                    (projectionResultTailPayloadLeftRev marked len
                      baseLeftRev)
                    m
          | some b =>
              cases hrest :
                  MachineDescription.decodeCells len restAfterCell with
              | none =>
                  apply
                    ne_halt_of_reaches_ne_halt_region
                      (k := projectionResultMarkTailStepCost marked len)
                      (mid :=
                        projectionConfig 100
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
                            (projectionConfig 100
                              (List.append [none, none, none, none]
                                baseLeftRev)
                              (projectionResultTailWorkCells marked
                                (len + 1)
                                (List.append
                                  (projectionBoolCellCodeCells false)
                                  (projectionCodeCells restAfterCell)))) =
                            projectionConfig 100
                              (List.append [none, none, none, none]
                                baseLeftRev)
                              (projectionResultTailWorkCells
                                (List.append marked [false]) len
                                (projectionCodeCells restAfterCell))
                        rw [run_input_mark_one_tail]
                    | true =>
                        change
                          Description.runConfig
                            (projectionResultMarkTailStepCost marked len)
                            (projectionConfig 100
                              (List.append [none, none, none, none]
                                baseLeftRev)
                              (projectionResultTailWorkCells marked
                                (len + 1)
                                (List.append
                                  (projectionBoolCellCodeCells true)
                                  (projectionCodeCells restAfterCell)))) =
                            projectionConfig 100
                              (List.append [none, none, none, none]
                                baseLeftRev)
                              (projectionResultTailWorkCells
                                (List.append marked [true]) len
                                (projectionCodeCells restAfterCell))
                        rw [run_input_mark_one_tail]
                  · intro m
                    exact
                      ih (List.append marked [b]) restAfterCell
                        baseLeftRev hrest m
              | some parsedRest =>
                  simp [MachineDescription.decodeCells, hcell, hrest] at hdecode

theorem run_input_tail_cellsToWord_none_ne_halt
    (marked : Word Bool) (cells : List (Option Bool))
    (suffix : Word MachineCodeSymbol)
    (baseLeftRev : List (Option Bool))
    (hword : MachineDescription.cellsToWord? cells = none)
    (n : Nat) :
    (Description.runConfig n
      (projectionConfig 100
        (List.append [none, none, none, none] baseLeftRev)
        (projectionResultTailWorkCells marked cells.length
          (projectionCodeCells
            (MachineDescription.encodeCellsAppend cells suffix))))).state ≠
      Description.halt := by
  induction cells generalizing marked suffix baseLeftRev n with
  | nil =>
      simp [MachineDescription.cellsToWord?] at hword
  | cons cell rest ih =>
      cases cell with
      | none =>
          apply
            ne_halt_of_reaches_ne_halt_region
              (k := 8 * marked.length + 4 * rest.length + 8)
              (mid :=
                projectionConfig 130
                  (projectionResultTailPayloadLeftRev marked rest.length
                    baseLeftRev)
                  (projectionCodeCells
                    (MachineDescription.encodeCellAppend none
                      (MachineDescription.encodeCellsAppend rest suffix))))
          · change
              Description.runConfig
                  (8 * marked.length + 4 * rest.length + 8)
                  (projectionConfig 100
                    (List.append [none, none, none, none] baseLeftRev)
                    (projectionResultTailWorkCells marked
                      (rest.length + 1)
                      (projectionCodeCells
                        (MachineDescription.encodeCellAppend none
                          (MachineDescription.encodeCellsAppend rest suffix))))) =
                projectionConfig 130
                  (projectionResultTailPayloadLeftRev marked rest.length
                    baseLeftRev)
                  (projectionCodeCells
                    (MachineDescription.encodeCellAppend none
                      (MachineDescription.encodeCellsAppend rest suffix)))
            rw [run_input_tail_to_first_payload]
          · intro m
            exact
              run_state130_blank_cell_ne_halt
                (MachineDescription.encodeCellsAppend rest suffix)
                (projectionResultTailPayloadLeftRev marked rest.length
                  baseLeftRev)
                m
      | some b =>
          cases hrest : MachineDescription.cellsToWord? rest with
          | none =>
              apply
                ne_halt_of_reaches_ne_halt_region
                  (k := projectionResultMarkTailStepCost marked rest.length)
                  (mid :=
                    projectionConfig 100
                      (List.append [none, none, none, none] baseLeftRev)
                      (projectionResultTailWorkCells
                        (List.append marked [b]) rest.length
                        (projectionCodeCells
                          (MachineDescription.encodeCellsAppend rest
                            suffix))))
              · cases b with
                | false =>
                    change
                      Description.runConfig
                        (projectionResultMarkTailStepCost marked rest.length)
                        (projectionConfig 100
                          (List.append [none, none, none, none] baseLeftRev)
                          (projectionResultTailWorkCells marked
                            (rest.length + 1)
                            (List.append (projectionBoolCellCodeCells false)
                              (projectionCodeCells
                                (MachineDescription.encodeCellsAppend rest
                                  suffix))))) =
                        projectionConfig 100
                          (List.append [none, none, none, none] baseLeftRev)
                          (projectionResultTailWorkCells
                            (List.append marked [false]) rest.length
                            (projectionCodeCells
                              (MachineDescription.encodeCellsAppend rest
                                suffix)))
                    rw [run_input_mark_one_tail]
                | true =>
                    change
                      Description.runConfig
                        (projectionResultMarkTailStepCost marked rest.length)
                        (projectionConfig 100
                          (List.append [none, none, none, none] baseLeftRev)
                          (projectionResultTailWorkCells marked
                            (rest.length + 1)
                            (List.append (projectionBoolCellCodeCells true)
                              (projectionCodeCells
                                (MachineDescription.encodeCellsAppend rest
                                  suffix))))) =
                        projectionConfig 100
                          (List.append [none, none, none, none] baseLeftRev)
                          (projectionResultTailWorkCells
                            (List.append marked [true]) rest.length
                            (projectionCodeCells
                              (MachineDescription.encodeCellsAppend rest
                                suffix)))
                    rw [run_input_mark_one_tail]
              · intro m
                exact
                  ih (List.append marked [b]) suffix baseLeftRev hrest m
          | some decoded =>
              simp [MachineDescription.cellsToWord?, hrest] at hword

theorem run_state100_decodeBoolWord_none_ne_halt
    (tokens : Word MachineCodeSymbol)
    (baseLeftRev : List (Option Bool))
    (hdecode : MachineDescription.decodeBoolWord tokens = none)
    (n : Nat) :
    (Description.runConfig n
      (projectionConfig 100
        (List.append [none, none, none, none] baseLeftRev)
        (projectionCodeCells tokens))).state ≠
      Description.halt := by
  unfold MachineDescription.decodeBoolWord at hdecode
  cases hcells : MachineDescription.decodeCellList tokens with
  | none =>
      unfold MachineDescription.decodeCellList at hcells
      cases hnat : MachineDescription.decodeNat tokens with
      | none =>
          exact
            run_state100_decodeNat_none_ne_halt
              tokens (List.append [none, none, none, none] baseLeftRev)
              hnat n
      | some parsedNat =>
          rcases parsedNat with ⟨len, restAfterLen⟩
          simp [hnat] at hcells
          have htokens :
              tokens =
                MachineDescription.encodeNatAppend len restAfterLen :=
            MachineDescription.decodeNat_eq_some_encodeNatAppend hnat
          rw [htokens]
          rw [projectionCodeCells_encodeNatAppend]
          change
            (Description.runConfig n
              (projectionConfig 100
                (List.append [none, none, none, none] baseLeftRev)
                (projectionResultTailWorkCells ([] : Word Bool) len
                  (projectionCodeCells restAfterLen)))).state ≠
              Description.halt
          exact
            run_input_tail_decodeCells_none_ne_halt
              ([] : Word Bool) len restAfterLen baseLeftRev hcells n
  | some parsedCells =>
      rcases parsedCells with ⟨cells, suffix⟩
      cases hword : MachineDescription.cellsToWord? cells with
      | none =>
          have htokens :
              tokens =
                MachineDescription.encodeCellListAppend cells suffix :=
            MachineDescription.decodeCellList_eq_some_encodeCellListAppend
              hcells
          rw [htokens]
          rw [MachineDescription.encodeCellListAppend,
            projectionCodeCells_encodeNatAppend]
          change
            (Description.runConfig n
              (projectionConfig 100
                (List.append [none, none, none, none] baseLeftRev)
                (projectionResultTailWorkCells ([] : Word Bool) cells.length
                  (projectionCodeCells
                    (MachineDescription.encodeCellsAppend cells
                      suffix))))).state ≠
              Description.halt
          exact
            run_input_tail_cellsToWord_none_ne_halt
              ([] : Word Bool) cells suffix baseLeftRev hword n
      | some decoded =>
          simp [hcells, hword] at hdecode

theorem run_input_bool_word_acc_stage_decodeNat_none_ne_halt
    (marked restInput : Word Bool) (tokens : Word MachineCodeSymbol)
    (baseLeftRev : List (Option Bool))
    (hdecode : MachineDescription.decodeNat tokens = none)
    (n : Nat) :
    (Description.runConfig n
      (projectionConfig 100
        (List.append [none, none, none, none] baseLeftRev)
        (projectionBoolWordWorkCells marked restInput tokens))).state ≠
      Description.halt := by
  induction restInput generalizing marked baseLeftRev n with
  | nil =>
      cases tokens with
      | nil =>
          apply
            ne_halt_of_reaches_ne_halt_region
              (k := 8 * marked.length + 4)
              (mid :=
                projectionConfig 150
                  (List.append (projectionMarkedBoolPayloadCells marked).reverse
                    (List.append projectionDoneCodeCells.reverse
                      (List.append
                        (projectionRepeatedCells projectionMarkedTickCodeCells
                          marked.length).reverse
                        (List.append [none, none, none, none] baseLeftRev))))
                  (projectionCodeCells ([] : Word MachineCodeSymbol)))
          · exact
              run_input_finish_marked_to_state150_tail
                marked ([] : Word MachineCodeSymbol) baseLeftRev
          · intro m
            exact
              state_ne_halt_of_stepConfig_none
                (n := m) (by rfl) (by
                  change (150 : Nat) ≠ 999
                  omega)
      | cons symbol suffix =>
          cases symbol with
          | header =>
              apply
                ne_halt_of_reaches_ne_halt_region
                  (k := projectionInputRemainingCost marked ([] : Word Bool))
                  (mid :=
                    projectionConfig 200
                      (List.append
                        (projectionCodeCells
                          (MachineDescription.encodeBoolWord marked)).reverse
                        (List.append [none, none, none, none] baseLeftRev))
                      (projectionCodeCells
                        (MachineCodeSymbol.header :: suffix)))
              · simpa using
                  run_input_bool_word_acc_false_false_suffix
                    marked ([] : Word Bool)
                    (MachineCodeSymbol.header :: suffix)
                    (some false :: some false ::
                      projectionCodeCells suffix)
                    baseLeftRev (by rfl)
              · intro m
                exact
                  run_state200_decodeNat_none_ne_halt
                    (MachineCodeSymbol.header :: suffix)
                    (List.append
                      (projectionCodeCells
                        (MachineDescription.encodeBoolWord marked)).reverse
                      (List.append [none, none, none, none] baseLeftRev))
                    hdecode m
          | transition =>
              apply
                ne_halt_of_reaches_ne_halt_region
                  (k := projectionInputRemainingCost marked ([] : Word Bool))
                  (mid :=
                    projectionConfig 200
                      (List.append
                        (projectionCodeCells
                          (MachineDescription.encodeBoolWord marked)).reverse
                        (List.append [none, none, none, none] baseLeftRev))
                      (projectionCodeCells
                        (MachineCodeSymbol.transition :: suffix)))
              · simpa using
                  run_input_bool_word_acc_false_false_suffix
                    marked ([] : Word Bool)
                    (MachineCodeSymbol.transition :: suffix)
                    (some false :: some true ::
                      projectionCodeCells suffix)
                    baseLeftRev (by rfl)
              · intro m
                exact
                  run_state200_decodeNat_none_ne_halt
                    (MachineCodeSymbol.transition :: suffix)
                    (List.append
                      (projectionCodeCells
                        (MachineDescription.encodeBoolWord marked)).reverse
                      (List.append [none, none, none, none] baseLeftRev))
                    hdecode m
          | tick =>
              apply
                ne_halt_of_reaches_ne_halt_region
                  (k := projectionInputRemainingCost marked ([] : Word Bool))
                  (mid :=
                    projectionConfig 200
                      (List.append
                        (projectionCodeCells
                          (MachineDescription.encodeBoolWord marked)).reverse
                        (List.append [none, none, none, none] baseLeftRev))
                      (projectionCodeCells (MachineCodeSymbol.tick :: suffix)))
              · simpa using
                  run_input_bool_word_acc_false_false_suffix
                    marked ([] : Word Bool)
                    (MachineCodeSymbol.tick :: suffix)
                    (some true :: some false ::
                      projectionCodeCells suffix)
                    baseLeftRev (by rfl)
              · intro m
                exact
                  run_state200_decodeNat_none_ne_halt
                    (MachineCodeSymbol.tick :: suffix)
                    (List.append
                      (projectionCodeCells
                        (MachineDescription.encodeBoolWord marked)).reverse
                      (List.append [none, none, none, none] baseLeftRev))
                    hdecode m
          | done =>
              simp [MachineDescription.decodeNat] at hdecode
          | blank =>
              apply
                ne_halt_of_reaches_ne_halt_region
                  (k := 8 * marked.length + 4)
                  (mid :=
                    projectionConfig 150
                      (List.append (projectionMarkedBoolPayloadCells marked).reverse
                        (List.append projectionDoneCodeCells.reverse
                          (List.append
                            (projectionRepeatedCells projectionMarkedTickCodeCells
                              marked.length).reverse
                            (List.append [none, none, none, none]
                              baseLeftRev))))
                      (projectionCodeCells
                        (MachineCodeSymbol.blank :: suffix)))
              · exact
                  run_input_finish_marked_to_state150_tail
                    marked (MachineCodeSymbol.blank :: suffix) baseLeftRev
              · intro m
                exact
                  ne_halt_of_reaches_stepConfig_none
                    (k := 1) (by rfl) (by
                      change (151 : Nat) ≠ 999
                      omega)
          | zero =>
              apply
                ne_halt_of_reaches_ne_halt_region
                  (k := 8 * marked.length + 4)
                  (mid :=
                    projectionConfig 150
                      (List.append (projectionMarkedBoolPayloadCells marked).reverse
                        (List.append projectionDoneCodeCells.reverse
                          (List.append
                            (projectionRepeatedCells projectionMarkedTickCodeCells
                              marked.length).reverse
                            (List.append [none, none, none, none]
                              baseLeftRev))))
                      (projectionCodeCells
                        (MachineCodeSymbol.zero :: suffix)))
              · exact
                  run_input_finish_marked_to_state150_tail
                    marked (MachineCodeSymbol.zero :: suffix) baseLeftRev
              · intro m
                exact
                  ne_halt_of_reaches_stepConfig_none
                    (k := 1) (by rfl) (by
                      change (151 : Nat) ≠ 999
                      omega)
          | one =>
              apply
                ne_halt_of_reaches_ne_halt_region
                  (k := 8 * marked.length + 4)
                  (mid :=
                    projectionConfig 150
                      (List.append (projectionMarkedBoolPayloadCells marked).reverse
                        (List.append projectionDoneCodeCells.reverse
                          (List.append
                            (projectionRepeatedCells projectionMarkedTickCodeCells
                              marked.length).reverse
                            (List.append [none, none, none, none]
                              baseLeftRev))))
                      (projectionCodeCells
                        (MachineCodeSymbol.one :: suffix)))
              · exact
                  run_input_finish_marked_to_state150_tail
                    marked (MachineCodeSymbol.one :: suffix) baseLeftRev
              · intro m
                exact
                  ne_halt_of_reaches_stepConfig_none
                    (k := 1) (by rfl) (by
                      change (151 : Nat) ≠ 999
                      omega)
          | moveLeft =>
              apply
                ne_halt_of_reaches_ne_halt_region
                  (k := 8 * marked.length + 4)
                  (mid :=
                    projectionConfig 150
                      (List.append (projectionMarkedBoolPayloadCells marked).reverse
                        (List.append projectionDoneCodeCells.reverse
                          (List.append
                            (projectionRepeatedCells projectionMarkedTickCodeCells
                              marked.length).reverse
                            (List.append [none, none, none, none]
                              baseLeftRev))))
                      (projectionCodeCells
                        (MachineCodeSymbol.moveLeft :: suffix)))
              · exact
                  run_input_finish_marked_to_state150_tail
                    marked (MachineCodeSymbol.moveLeft :: suffix) baseLeftRev
              · intro m
                exact
                  ne_halt_of_reaches_stepConfig_none
                    (k := 1) (by rfl) (by
                      change (151 : Nat) ≠ 999
                      omega)
          | moveRight =>
              apply
                ne_halt_of_reaches_ne_halt_region
                  (k := 8 * marked.length + 4)
                  (mid :=
                    projectionConfig 150
                      (List.append (projectionMarkedBoolPayloadCells marked).reverse
                        (List.append projectionDoneCodeCells.reverse
                          (List.append
                            (projectionRepeatedCells projectionMarkedTickCodeCells
                              marked.length).reverse
                            (List.append [none, none, none, none]
                              baseLeftRev))))
                      (projectionCodeCells
                        (MachineCodeSymbol.moveRight :: suffix)))
              · exact
                  run_input_finish_marked_to_state150_tail
                    marked (MachineCodeSymbol.moveRight :: suffix) baseLeftRev
              · intro m
                exact
                  state_ne_halt_of_stepConfig_none
                    (n := m) (by rfl) (by
                      change (150 : Nat) ≠ 999
                      omega)
  | cons b restInput ih =>
      apply
        ne_halt_of_reaches_ne_halt_region
          (k := projectionInputMarkStepCost marked restInput)
          (mid :=
            projectionConfig 100
              (List.append [none, none, none, none] baseLeftRev)
              (projectionBoolWordWorkCells (List.append marked [b])
                restInput tokens))
      · exact
          run_input_mark_one
            marked restInput b tokens baseLeftRev
      · intro m
        exact ih (List.append marked [b]) baseLeftRev m

theorem run_state100_input_bool_word_stage_decodeNat_none_ne_halt
    (w : Word Bool) (tokens : Word MachineCodeSymbol)
    (baseLeftRev : List (Option Bool))
    (hdecode : MachineDescription.decodeNat tokens = none)
    (n : Nat) :
    (Description.runConfig n
      (projectionConfig 100
        (List.append [none, none, none, none] baseLeftRev)
        (projectionCodeCells
          (MachineDescription.encodeBoolWordAppend w tokens)))).state ≠
      Description.halt := by
  have h :=
    run_input_bool_word_acc_stage_decodeNat_none_ne_halt
      ([] : Word Bool) w tokens baseLeftRev hdecode n
  simpa [projectionBoolWordWorkCells_nil_eq_encodeBoolWordAppend] using h

theorem run_state200_stage_nat_result_decodeBoolWord_none_ne_halt
    (stage : Nat) (tokens : Word MachineCodeSymbol)
    (leftRev : List (Option Bool))
    (hdecode : MachineDescription.decodeBoolWord tokens = none)
    (n : Nat) :
    (Description.runConfig n
      (projectionConfig 200 leftRev
        (projectionCodeCells
          (MachineDescription.encodeNatAppend stage tokens)))).state ≠
      Description.halt := by
  induction stage generalizing leftRev n with
  | zero =>
      cases tokens with
      | nil =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 4) (by rfl) (by
                change (210 : Nat) ≠ 999
                omega)
      | cons symbol rest =>
          cases symbol with
          | moveRight =>
              exact
                ne_halt_of_reaches_stepConfig_none
                  (k := 4) (by rfl) (by
                    change (210 : Nat) ≠ 999
                    omega)
          | header =>
              apply
                ne_halt_of_reaches_ne_halt_region
                  (k := 12)
                  (mid :=
                    projectionConfig 300
                      (List.append [none, none, none, none] leftRev)
                      (projectionCodeCells
                        (MachineCodeSymbol.header :: rest)))
              · rfl
              · intro m
                exact
                  run_state300_decodeBoolWord_none_ne_halt
                    (MachineCodeSymbol.header :: rest) leftRev hdecode m
          | transition =>
              apply
                ne_halt_of_reaches_ne_halt_region
                  (k := 12)
                  (mid :=
                    projectionConfig 300
                      (List.append [none, none, none, none] leftRev)
                      (projectionCodeCells
                        (MachineCodeSymbol.transition :: rest)))
              · rfl
              · intro m
                exact
                  run_state300_decodeBoolWord_none_ne_halt
                    (MachineCodeSymbol.transition :: rest) leftRev hdecode m
          | tick =>
              apply
                ne_halt_of_reaches_ne_halt_region
                  (k := 12)
                  (mid :=
                    projectionConfig 300
                      (List.append [none, none, none, none] leftRev)
                      (projectionCodeCells (MachineCodeSymbol.tick :: rest)))
              · rfl
              · intro m
                exact
                  run_state300_decodeBoolWord_none_ne_halt
                    (MachineCodeSymbol.tick :: rest) leftRev hdecode m
          | done =>
              apply
                ne_halt_of_reaches_ne_halt_region
                  (k := 12)
                  (mid :=
                    projectionConfig 300
                      (List.append [none, none, none, none] leftRev)
                      (projectionCodeCells (MachineCodeSymbol.done :: rest)))
              · rfl
              · intro m
                exact
                  run_state300_decodeBoolWord_none_ne_halt
                    (MachineCodeSymbol.done :: rest) leftRev hdecode m
          | blank =>
              apply
                ne_halt_of_reaches_ne_halt_region
                  (k := 12)
                  (mid :=
                    projectionConfig 300
                      (List.append [none, none, none, none] leftRev)
                      (projectionCodeCells (MachineCodeSymbol.blank :: rest)))
              · rfl
              · intro m
                exact
                  run_state300_decodeBoolWord_none_ne_halt
                    (MachineCodeSymbol.blank :: rest) leftRev hdecode m
          | zero =>
              apply
                ne_halt_of_reaches_ne_halt_region
                  (k := 12)
                  (mid :=
                    projectionConfig 300
                      (List.append [none, none, none, none] leftRev)
                      (projectionCodeCells (MachineCodeSymbol.zero :: rest)))
              · rfl
              · intro m
                exact
                  run_state300_decodeBoolWord_none_ne_halt
                    (MachineCodeSymbol.zero :: rest) leftRev hdecode m
          | one =>
              apply
                ne_halt_of_reaches_ne_halt_region
                  (k := 12)
                  (mid :=
                    projectionConfig 300
                      (List.append [none, none, none, none] leftRev)
                      (projectionCodeCells (MachineCodeSymbol.one :: rest)))
              · rfl
              · intro m
                exact
                  run_state300_decodeBoolWord_none_ne_halt
                    (MachineCodeSymbol.one :: rest) leftRev hdecode m
          | moveLeft =>
              apply
                ne_halt_of_reaches_ne_halt_region
                  (k := 12)
                  (mid :=
                    projectionConfig 300
                      (List.append [none, none, none, none] leftRev)
                      (projectionCodeCells
                        (MachineCodeSymbol.moveLeft :: rest)))
              · rfl
              · intro m
                exact
                  run_state300_decodeBoolWord_none_ne_halt
                    (MachineCodeSymbol.moveLeft :: rest) leftRev hdecode m
  | succ stage ih =>
      apply
        ne_halt_of_reaches_ne_halt_region
          (k := 4)
          (mid :=
            projectionConfig 200
              (List.append projectionTickCodeCellsRev leftRev)
              (projectionCodeCells
                (MachineDescription.encodeNatAppend stage tokens)))
      · change
          Description.runConfig 4
            (projectionConfig 200 leftRev
              (List.append projectionTickCodeCells
                (projectionCodeCells
                  (MachineDescription.encodeNatAppend stage tokens)))) =
            projectionConfig 200
              (List.append projectionTickCodeCellsRev leftRev)
              (projectionCodeCells
                (MachineDescription.encodeNatAppend stage tokens))
        rw [run_stage_tick]
      · intro m
        exact ih (List.append projectionTickCodeCellsRev leftRev) m

theorem run_state350_code_symbol_ne_halt
    (symbol : MachineCodeSymbol) (suffix : Word MachineCodeSymbol)
    (leftRev : List (Option Bool)) (n : Nat) :
    (Description.runConfig n
      (projectionConfig 350 leftRev
        (projectionCodeCells (symbol :: suffix)))).state ≠
      Description.halt := by
  cases n with
  | zero =>
      change (350 : Nat) ≠ 999
      omega
  | succ n =>
      cases symbol <;>
        simp [projectionCodeCells, MachineDescription.encodeCodeWordAsInput,
          MachineDescription.encodeCodeSymbolAsInput]
      · change
          (Description.runConfig n
            (projectionConfig 351 (some false :: leftRev)
              (some false :: some false :: some false ::
                List.map some
                  (MachineDescription.encodeCodeWordAsInput suffix)))).state ≠
            Description.halt
        exact
          state_ne_halt_of_stepConfig_none
            (by rfl)
            (by
              simp [projectionConfig,
                Description])
      · change
          (Description.runConfig n
            (projectionConfig 351 (some false :: leftRev)
              (some false :: some false :: some true ::
                List.map some
                  (MachineDescription.encodeCodeWordAsInput suffix)))).state ≠
            Description.halt
        exact
          state_ne_halt_of_stepConfig_none
            (by rfl)
            (by
              simp [projectionConfig,
                Description])
      · change
          (Description.runConfig n
            (projectionConfig 351 (some false :: leftRev)
              (some false :: some true :: some false ::
                List.map some
                  (MachineDescription.encodeCodeWordAsInput suffix)))).state ≠
            Description.halt
        exact
          state_ne_halt_of_stepConfig_none
            (by rfl)
            (by
              simp [projectionConfig,
                Description])
      · change
          (Description.runConfig n
            (projectionConfig 351 (some false :: leftRev)
              (some false :: some true :: some true ::
                List.map some
                  (MachineDescription.encodeCodeWordAsInput suffix)))).state ≠
            Description.halt
        exact
          state_ne_halt_of_stepConfig_none
            (by rfl)
            (by
              simp [projectionConfig,
                Description])
      · change
          (Description.runConfig n
            (projectionConfig 351 (some false :: leftRev)
              (some true :: some false :: some false ::
                List.map some
                  (MachineDescription.encodeCodeWordAsInput suffix)))).state ≠
            Description.halt
        exact
          state_ne_halt_of_stepConfig_none
            (by rfl)
            (by
              simp [projectionConfig,
                Description])
      · change
          (Description.runConfig n
            (projectionConfig 351 (some false :: leftRev)
              (some true :: some false :: some true ::
                List.map some
                  (MachineDescription.encodeCodeWordAsInput suffix)))).state ≠
            Description.halt
        exact
          state_ne_halt_of_stepConfig_none
            (by rfl)
            (by
              simp [projectionConfig,
                Description])
      · change
          (Description.runConfig n
            (projectionConfig 351 (some false :: leftRev)
              (some true :: some true :: some false ::
                List.map some
                  (MachineDescription.encodeCodeWordAsInput suffix)))).state ≠
            Description.halt
        exact
          state_ne_halt_of_stepConfig_none
            (by rfl)
            (by
              simp [projectionConfig,
                Description])
      · change
          (Description.runConfig n
            (projectionConfig 351 (some false :: leftRev)
              (some true :: some true :: some true ::
                List.map some
                  (MachineDescription.encodeCodeWordAsInput suffix)))).state ≠
            Description.halt
        exact
          state_ne_halt_of_stepConfig_none
            (by rfl)
            (by
              simp [projectionConfig,
                Description])
      · exact
          state_ne_halt_of_stepConfig_none
            (by rfl)
            (by
              simp [projectionConfig,
                Description])


end ControllerStageInputProjection
end Computability
end FoC
