import FoC.Computability.Compiler.Core.ControllerStageInputProjection.Soundness.BasicPart1


/-!
# BasicPart2

Supporting declarations and helper lemmas for Computability Compiler Core ControllerStageInputProjection Soundness BasicPart2.
-/

namespace FoC
namespace Computability
namespace ControllerStageInputProjection
open Languages

 /-- `run_state300_decodeBoolWord_none_ne_halt` states the corresponding theorem run form. -/
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

 /-- `run_input_tail_decodeCells_none_ne_halt` states the corresponding theorem run form. -/
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

 /-- `run_input_tail_cellsToWord_none_ne_halt` states the corresponding theorem run form. -/
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

 /-- `run_state100_decodeBoolWord_none_ne_halt` states the corresponding theorem run form. -/
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

 /-- `run_input_bool_word_acc_stage_decodeNat_none_ne_halt` states the corresponding theorem run form. -/
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

 /-- `run_state100_input_bool_word_stage_decodeNat_none_ne_halt` states the corresponding theorem run form. -/
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

 /-- `run_state200_stage_nat_result_decodeBoolWord_none_ne_halt` states the corresponding theorem run form. -/
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

 /-- `run_state350_code_symbol_ne_halt` states the corresponding theorem run form. -/
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
