import FoC.Computability.Compiler.Core.ControllerStageInputProjection.InputRun

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

namespace ControllerStageInputProjection


def projectionScanState340 : Nat -> Nat
  | 0 => 340
  | 1 => 341
  | 2 => 342
  | _ => 343

theorem run_scan340_step
    (count : Nat) (hcount : count ≤ 3)
    (cell : Option Bool) (rest leftOfBoundary tail : List (Option Bool))
    (boundaryHead : Option Bool)
    (hsafe : count ≠ 3 ∨ cell ≠ none) :
    Description.runConfig 1
        (projectionScanLeftConfig (projectionScanState340 count)
          leftOfBoundary boundaryHead (cell :: rest) tail) =
      projectionScanLeftConfig
        (projectionScanState340 (projectionScanCountStep count cell))
        leftOfBoundary boundaryHead rest (cell :: tail) := by
  cases rest with
  | nil =>
      cases count with
      | zero =>
          cases cell with
          | none =>
              rfl
          | some b =>
              cases b <;> rfl
      | succ count =>
          cases count with
          | zero =>
              cases cell with
              | none =>
                  rfl
              | some b =>
                  cases b <;> rfl
          | succ count =>
              cases count with
              | zero =>
                  cases cell with
                  | none =>
                      rfl
                  | some b =>
                      cases b <;> rfl
              | succ count =>
                  cases count with
                  | zero =>
                      cases cell with
                      | none =>
                          exact False.elim
                            (hsafe.elim (fun h => h rfl) (fun h => h rfl))
                      | some b =>
                          cases b <;> rfl
                  | succ count =>
                      have hfalse : False := by omega
                      exact False.elim hfalse
  | cons next more =>
      cases count with
      | zero =>
          cases cell with
          | none =>
              rfl
          | some b =>
              cases b <;> rfl
      | succ count =>
          cases count with
          | zero =>
              cases cell with
              | none =>
                  rfl
              | some b =>
                  cases b <;> rfl
          | succ count =>
              cases count with
              | zero =>
                  cases cell with
                  | none =>
                      rfl
                  | some b =>
                      cases b <;> rfl
              | succ count =>
                  cases count with
                  | zero =>
                      cases cell with
                      | none =>
                          exact False.elim
                            (hsafe.elim (fun h => h rfl) (fun h => h rfl))
                      | some b =>
                          cases b <;> rfl
                  | succ count =>
                      have hfalse : False := by omega
                      exact False.elim hfalse

theorem run_scan340_cells
    (cellsRev : List (Option Bool)) (count : Nat) (hcount : count ≤ 3)
    (hsafe : projectionScanSafe count cellsRev)
    (leftOfBoundary : List (Option Bool)) (boundaryHead : Option Bool)
    (tail : List (Option Bool)) :
    Description.runConfig cellsRev.length
        (projectionScanLeftConfig (projectionScanState340 count)
          leftOfBoundary boundaryHead cellsRev tail) =
      projectionConfig
        (projectionScanState340
          (projectionScanCountFold count cellsRev))
        leftOfBoundary
        (boundaryHead :: List.append cellsRev.reverse tail) := by
  induction cellsRev generalizing count tail with
  | nil =>
      rfl
  | cons cell rest ih =>
      rcases hsafe with ⟨hcell, hrest⟩
      have hnext :
          projectionScanCountStep count cell ≤ 3 :=
        projectionScanCountStep_le_three hcount cell
      rw [show (cell :: rest).length = 1 + rest.length by
        simp
        omega,
        MachineDescription.runConfig_add]
      change
        Description.runConfig
            rest.length
            (Description.runConfig 1
              (projectionScanLeftConfig (projectionScanState340 count)
                leftOfBoundary boundaryHead (cell :: rest) tail)) =
          projectionConfig
            (projectionScanState340
              (projectionScanCountFold count (cell :: rest)))
            leftOfBoundary
            (boundaryHead :: List.append (cell :: rest).reverse tail)
      rw [run_scan340_step
        count hcount cell rest leftOfBoundary tail boundaryHead hcell]
      rw [ih (projectionScanCountStep count cell) hnext hrest
        (cell :: tail)]
      simp [projectionScanCountFold, List.append_assoc]

theorem run_scan340_boundary
    (base tail : List (Option Bool)) :
    Description.runConfig 7
        (projectionConfig 340 (none :: none :: none :: base) (none :: tail)) =
      projectionConfig 300
        (List.append [none, none, none, none] base) tail := by
  cases tail with
  | nil =>
      rfl
  | cons cell rest =>
      cases cell with
      | none =>
          rfl
      | some b =>
          cases b <;> rfl

theorem run_scan340_cells_to_boundary
    (cellsRev : List (Option Bool))
    (hsafe : projectionScanSafe 0 cellsRev)
    (hcount : projectionScanCountFold 0 cellsRev = 0)
    (base tail : List (Option Bool)) :
    Description.runConfig
        (cellsRev.length + 7)
        (projectionScanLeftConfig 340
          (List.append ([none, none, none] : List (Option Bool)) base) none
          cellsRev tail) =
      projectionConfig 300
        (List.append [none, none, none, none] base)
        (List.append cellsRev.reverse tail) := by
  rw [MachineDescription.runConfig_add]
  change
    Description.runConfig 7
        (Description.runConfig
        cellsRev.length
        (projectionScanLeftConfig (projectionScanState340 0)
          (List.append ([none, none, none] : List (Option Bool)) base) none
          cellsRev tail)) =
      projectionConfig 300
        (List.append [none, none, none, none] base)
        (List.append cellsRev.reverse tail)
  rw [run_scan340_cells
    cellsRev 0 (by omega) hsafe
    (List.append ([none, none, none] : List (Option Bool)) base) none tail]
  rw [hcount]
  simpa [List.append_assoc] using
    run_scan340_boundary
      base (List.append cellsRev.reverse tail)

theorem run_state300_marked_tick
    (leftRev tail : List (Option Bool)) :
    Description.runConfig 4
        (projectionConfig 300 leftRev
          (List.append projectionMarkedTickCodeCells tail)) =
      projectionConfig 300
        (List.append projectionMarkedTickCodeCells.reverse leftRev) tail := by
  cases tail with
  | nil =>
      rfl
  | cons cell rest =>
      cases cell with
      | none =>
          rfl
      | some b =>
          cases b <;> rfl

theorem run_state300_marked_ticks
    (count : Nat) (leftRev tail : List (Option Bool)) :
    Description.runConfig (4 * count)
        (projectionConfig 300 leftRev
          (List.append
            (projectionRepeatedCells projectionMarkedTickCodeCells count)
            tail)) =
      projectionConfig 300
        (List.append
          (projectionRepeatedCells projectionMarkedTickCodeCells count).reverse
          leftRev)
        tail := by
  induction count generalizing leftRev with
  | zero =>
      rfl
  | succ count ih =>
      have hsteps : 4 * (count + 1) = 4 + 4 * count := by omega
      rw [hsteps, MachineDescription.runConfig_add]
      change Description.runConfig
          (4 * count)
          (Description.runConfig 4
            (projectionConfig 300 leftRev
              (List.append
                (projectionRepeatedCells projectionMarkedTickCodeCells
                  (count + 1)) tail))) = _
      rw [show projectionRepeatedCells projectionMarkedTickCodeCells
          (count + 1) =
          List.append projectionMarkedTickCodeCells
            (projectionRepeatedCells projectionMarkedTickCodeCells count) by
        rfl]
      change Description.runConfig
          (4 * count)
          (Description.runConfig 4
            (projectionConfig 300 leftRev
              (List.append projectionMarkedTickCodeCells
                (List.append
                  (projectionRepeatedCells projectionMarkedTickCodeCells count)
                  tail)))) = _
      rw [run_state300_marked_tick]
      rw [ih]
      simp [List.reverse_append, List.append_assoc]

theorem run_state300_mark_tick
    (leftRev tail : List (Option Bool)) :
    Description.runConfig 4
        (projectionConfig 300 leftRev
          (List.append projectionTickCodeCells tail)) =
      projectionConfig 320
        (List.append projectionMarkedTickCodeCells.reverse leftRev) tail := by
  cases tail with
  | nil =>
      rfl
  | cons cell rest =>
      cases cell with
      | none =>
          rfl
      | some b =>
          cases b <;> rfl

theorem run_state320_tick
    (leftRev tail : List (Option Bool)) :
    Description.runConfig 4
        (projectionConfig 320 leftRev
          (List.append projectionTickCodeCells tail)) =
      projectionConfig 320
        (List.append projectionTickCodeCells.reverse leftRev) tail := by
  cases tail with
  | nil =>
      rfl
  | cons cell rest =>
      cases cell with
      | none =>
          rfl
      | some b =>
          cases b <;> rfl

theorem run_state320_ticks
    (count : Nat) (leftRev tail : List (Option Bool)) :
    Description.runConfig (4 * count)
        (projectionConfig 320 leftRev
          (List.append
            (projectionRepeatedCells projectionTickCodeCells count)
            tail)) =
      projectionConfig 320
        (List.append
          (projectionRepeatedCells projectionTickCodeCells count).reverse
          leftRev)
        tail := by
  induction count generalizing leftRev with
  | zero =>
      rfl
  | succ count ih =>
      have hsteps : 4 * (count + 1) = 4 + 4 * count := by omega
      rw [hsteps, MachineDescription.runConfig_add]
      change Description.runConfig
          (4 * count)
          (Description.runConfig 4
            (projectionConfig 320 leftRev
              (List.append
                (projectionRepeatedCells projectionTickCodeCells
                  (count + 1)) tail))) = _
      rw [show projectionRepeatedCells projectionTickCodeCells
          (count + 1) =
          List.append projectionTickCodeCells
            (projectionRepeatedCells projectionTickCodeCells count) by
        rfl]
      change Description.runConfig
          (4 * count)
          (Description.runConfig 4
            (projectionConfig 320 leftRev
              (List.append projectionTickCodeCells
                (List.append
                  (projectionRepeatedCells projectionTickCodeCells count)
                  tail)))) = _
      rw [run_state320_tick]
      rw [ih]
      simp [List.reverse_append, List.append_assoc]

theorem run_state320_done
    (leftRev tail : List (Option Bool)) :
    Description.runConfig 4
        (projectionConfig 320 leftRev
          (List.append projectionDoneCodeCells tail)) =
      projectionConfig 330
        (List.append projectionDoneCodeCells.reverse leftRev) tail := by
  cases tail with
  | nil =>
      rfl
  | cons cell rest =>
      cases cell with
      | none =>
          rfl
      | some b =>
          cases b <;> rfl

theorem run_state300_done
    (leftRev tail : List (Option Bool)) :
    Description.runConfig 4
        (projectionConfig 300 leftRev
          (List.append projectionDoneCodeCells tail)) =
      projectionConfig 350
        (List.append projectionDoneCodeCells.reverse leftRev) tail := by
  cases tail with
  | nil =>
      rfl
  | cons cell rest =>
      cases cell with
      | none =>
          rfl
      | some b =>
          cases b <;> rfl

theorem run_state330_marked_payload_cell
    (b : Bool) (leftRev tail : List (Option Bool)) :
    Description.runConfig 4
        (projectionConfig 330 leftRev
          (List.append (projectionMarkedBoolCellCodeCells b) tail)) =
      projectionConfig 330
        (List.append (projectionMarkedBoolCellCodeCells b).reverse leftRev)
        tail := by
  cases b <;>
    cases tail with
    | nil =>
        rfl
    | cons cell rest =>
        cases cell with
        | none =>
            rfl
        | some b =>
            cases b <;> rfl

theorem run_state330_marked_payload_cell_append
    (b : Bool) (leftRev middle tail : List (Option Bool)) :
    Description.runConfig 4
        (projectionConfig 330 leftRev
          (List.append (projectionMarkedBoolCellCodeCells b) middle ++
            tail)) =
      projectionConfig 330
        (List.append (projectionMarkedBoolCellCodeCells b).reverse leftRev)
        (List.append middle tail) := by
  cases b <;>
    cases middle with
    | nil =>
        cases tail with
        | nil =>
            rfl
        | cons cell rest =>
            cases cell with
            | none =>
                rfl
            | some b =>
                cases b <;> rfl
    | cons cell rest =>
        cases cell with
        | none =>
            rfl
        | some b =>
            cases b <;> rfl

theorem run_state330_marked_payload
    (w : Word Bool) (leftRev tail : List (Option Bool)) :
    Description.runConfig (4 * w.length)
        (projectionConfig 330 leftRev
          (List.append (projectionMarkedBoolPayloadCells w) tail)) =
      projectionConfig 330
        (List.append (projectionMarkedBoolPayloadCells w).reverse leftRev)
        tail := by
  induction w generalizing leftRev with
  | nil =>
      rfl
  | cons b rest ih =>
      have hsteps : 4 * (b :: rest).length = 4 + 4 * rest.length := by
        simp
        omega
      rw [hsteps, MachineDescription.runConfig_add]
      change Description.runConfig
          (4 * rest.length)
          (Description.runConfig 4
            (projectionConfig 330 leftRev
              (projectionMarkedBoolPayloadCells (b :: rest) ++ tail))) = _
      rw [show projectionMarkedBoolPayloadCells (b :: rest) =
          List.append (projectionMarkedBoolCellCodeCells b)
            (projectionMarkedBoolPayloadCells rest) by
        rfl]
      rw [run_state330_marked_payload_cell_append]
      rw [ih]
      simp [List.reverse_append, List.append_assoc]

theorem run_state330_mark_payload_cell
    (b : Bool) (leftRev tail : List (Option Bool)) :
    Description.runConfig 4
        (projectionConfig 330 leftRev
          (List.append (projectionBoolCellCodeCells b) tail)) =
      projectionConfig 340 (none :: some false :: leftRev)
        (List.append
          (match b with
          | false => [some false, some true]
          | true => [some true, some false])
          tail) := by
  cases b <;>
    cases tail with
    | nil =>
        rfl
    | cons cell rest =>
        cases cell with
        | none =>
            rfl
        | some b =>
            cases b <;> rfl

theorem run_state350_marked_payload_cell
    (b : Bool) (leftRev tail : List (Option Bool)) :
    Description.runConfig 4
        (projectionConfig 350 leftRev
          (List.append (projectionMarkedBoolCellCodeCells b) tail)) =
      projectionConfig 350
        (List.append (projectionMarkedBoolCellCodeCells b).reverse leftRev)
        tail := by
  cases b <;>
    cases tail with
    | nil =>
        rfl
    | cons cell rest =>
        cases cell with
        | none =>
            rfl
        | some b =>
            cases b <;> rfl

theorem run_state350_marked_payload_cell_append
    (b : Bool) (leftRev middle tail : List (Option Bool)) :
    Description.runConfig 4
        (projectionConfig 350 leftRev
          (List.append (projectionMarkedBoolCellCodeCells b) middle ++
            tail)) =
      projectionConfig 350
        (List.append (projectionMarkedBoolCellCodeCells b).reverse leftRev)
        (List.append middle tail) := by
  cases b <;>
    cases middle with
    | nil =>
        cases tail with
        | nil =>
            rfl
        | cons cell rest =>
            cases cell with
            | none =>
                rfl
            | some b =>
                cases b <;> rfl
    | cons cell rest =>
        cases cell with
        | none =>
            rfl
        | some b =>
            cases b <;> rfl

theorem run_state350_marked_payload
    (w : Word Bool) (leftRev tail : List (Option Bool)) :
    Description.runConfig (4 * w.length)
        (projectionConfig 350 leftRev
          (List.append (projectionMarkedBoolPayloadCells w) tail)) =
      projectionConfig 350
        (List.append (projectionMarkedBoolPayloadCells w).reverse leftRev)
        tail := by
  induction w generalizing leftRev with
  | nil =>
      rfl
  | cons b rest ih =>
      have hsteps : 4 * (b :: rest).length = 4 + 4 * rest.length := by
        simp
        omega
      rw [hsteps, MachineDescription.runConfig_add]
      change Description.runConfig
          (4 * rest.length)
          (Description.runConfig 4
            (projectionConfig 350 leftRev
              (projectionMarkedBoolPayloadCells (b :: rest) ++ tail))) = _
      rw [show projectionMarkedBoolPayloadCells (b :: rest) =
          List.append (projectionMarkedBoolCellCodeCells b)
            (projectionMarkedBoolPayloadCells rest) by
        rfl]
      rw [run_state350_marked_payload_cell_append]
      rw [ih]
      simp [List.reverse_append, List.append_assoc]

def projectionScanState360 : Nat -> Nat
  | 0 => 360
  | 1 => 361
  | 2 => 362
  | _ => 363

theorem run_scan360_step
    (count : Nat) (hcount : count ≤ 3)
    (cell : Option Bool) (rest leftOfBoundary tail : List (Option Bool))
    (boundaryHead : Option Bool)
    (hsafe : count ≠ 3 ∨ cell ≠ none) :
    Description.runConfig 1
        (projectionScanLeftConfig (projectionScanState360 count)
          leftOfBoundary boundaryHead (cell :: rest) tail) =
      projectionScanLeftConfig
        (projectionScanState360 (projectionScanCountStep count cell))
        leftOfBoundary boundaryHead rest (cell :: tail) := by
  cases rest with
  | nil =>
      cases count with
      | zero =>
          cases cell with
          | none =>
              rfl
          | some b =>
              cases b <;> rfl
      | succ count =>
          cases count with
          | zero =>
              cases cell with
              | none =>
                  rfl
              | some b =>
                  cases b <;> rfl
          | succ count =>
              cases count with
              | zero =>
                  cases cell with
                  | none =>
                      rfl
                  | some b =>
                      cases b <;> rfl
              | succ count =>
                  cases count with
                  | zero =>
                      cases cell with
                      | none =>
                          exact False.elim
                            (hsafe.elim (fun h => h rfl) (fun h => h rfl))
                      | some b =>
                          cases b <;> rfl
                  | succ count =>
                      have hfalse : False := by omega
                      exact False.elim hfalse
  | cons next more =>
      cases count with
      | zero =>
          cases cell with
          | none =>
              rfl
          | some b =>
              cases b <;> rfl
      | succ count =>
          cases count with
          | zero =>
              cases cell with
              | none =>
                  rfl
              | some b =>
                  cases b <;> rfl
          | succ count =>
              cases count with
              | zero =>
                  cases cell with
                  | none =>
                      rfl
                  | some b =>
                      cases b <;> rfl
              | succ count =>
                  cases count with
                  | zero =>
                      cases cell with
                      | none =>
                          exact False.elim
                            (hsafe.elim (fun h => h rfl) (fun h => h rfl))
                      | some b =>
                          cases b <;> rfl
                  | succ count =>
                      have hfalse : False := by omega
                      exact False.elim hfalse

theorem run_scan360_cells
    (cellsRev : List (Option Bool)) (count : Nat) (hcount : count ≤ 3)
    (hsafe : projectionScanSafe count cellsRev)
    (leftOfBoundary : List (Option Bool)) (boundaryHead : Option Bool)
    (tail : List (Option Bool)) :
    Description.runConfig cellsRev.length
        (projectionScanLeftConfig (projectionScanState360 count)
          leftOfBoundary boundaryHead cellsRev tail) =
      projectionConfig
        (projectionScanState360
          (projectionScanCountFold count cellsRev))
        leftOfBoundary
        (boundaryHead :: List.append cellsRev.reverse tail) := by
  induction cellsRev generalizing count tail with
  | nil =>
      rfl
  | cons cell rest ih =>
      rcases hsafe with ⟨hcell, hrest⟩
      have hnext :
          projectionScanCountStep count cell ≤ 3 :=
        projectionScanCountStep_le_three hcount cell
      rw [show (cell :: rest).length = 1 + rest.length by
        simp
        omega,
        MachineDescription.runConfig_add]
      change
        Description.runConfig
            rest.length
            (Description.runConfig 1
              (projectionScanLeftConfig (projectionScanState360 count)
                leftOfBoundary boundaryHead (cell :: rest) tail)) =
          projectionConfig
            (projectionScanState360
              (projectionScanCountFold count (cell :: rest)))
            leftOfBoundary
            (boundaryHead :: List.append (cell :: rest).reverse tail)
      rw [run_scan360_step
        count hcount cell rest leftOfBoundary tail boundaryHead hcell]
      rw [ih (projectionScanCountStep count cell) hnext hrest
        (cell :: tail)]
      simp [projectionScanCountFold, List.append_assoc]

theorem run_scan360_boundary
    (base tail : List (Option Bool)) :
    Description.runConfig 7
        (projectionConfig 360
          (List.append ([none, none, none] : List (Option Bool)) base)
          (none :: tail)) =
      projectionConfig 367
        (List.append projectionDoneCodeCells.reverse base) tail := by
  cases tail with
  | nil =>
      rfl
  | cons cell rest =>
      cases cell with
      | none =>
          rfl
      | some b =>
          cases b <;> rfl

theorem run_scan360_cells_to_boundary
    (cellsRev : List (Option Bool))
    (hsafe : projectionScanSafe 0 cellsRev)
    (hcount : projectionScanCountFold 0 cellsRev = 0)
    (base tail : List (Option Bool)) :
    Description.runConfig
        (cellsRev.length + 7)
        (projectionScanLeftConfig 360
          (List.append ([none, none, none] : List (Option Bool)) base) none
          cellsRev tail) =
      projectionConfig 367
        (List.append projectionDoneCodeCells.reverse base)
        (List.append cellsRev.reverse tail) := by
  rw [MachineDescription.runConfig_add]
  change
    Description.runConfig 7
        (Description.runConfig
        cellsRev.length
        (projectionScanLeftConfig (projectionScanState360 0)
          (List.append ([none, none, none] : List (Option Bool)) base) none
          cellsRev tail)) =
      projectionConfig 367
        (List.append projectionDoneCodeCells.reverse base)
        (List.append cellsRev.reverse tail)
  rw [run_scan360_cells
    cellsRev 0 (by omega) hsafe
    (List.append ([none, none, none] : List (Option Bool)) base) none tail]
  rw [hcount]
  simpa [List.append_assoc] using
    run_scan360_boundary
      base (List.append cellsRev.reverse tail)

theorem run_state350_blank_to_scan360
    (cellsRev base : List (Option Bool)) :
    Description.runConfig 1
        (projectionConfig 350
          (List.append cellsRev
            (List.append ([none, none, none, none] : List (Option Bool))
              base))
          ([] : List (Option Bool))) =
      projectionScanLeftConfig 360
        (List.append ([none, none, none] : List (Option Bool)) base)
        none cellsRev [none] := by
  cases cellsRev with
  | nil =>
      rfl
  | cons cell rest =>
      cases cell with
      | none =>
          rfl
      | some b =>
          cases b <;> rfl

def projectionResultFinishScanBackCellsRev
    (marked : Word Bool) : List (Option Bool) :=
  List.append (projectionMarkedBoolPayloadCells marked).reverse
    (List.append projectionDoneCodeCells.reverse
      (projectionRepeatedCells projectionMarkedTickCodeCells
        marked.length).reverse)

theorem projectionResultFinishScanBackCellsRev_scanCountFold
    (marked : Word Bool) :
    projectionScanCountFold 0
        (projectionResultFinishScanBackCellsRev marked) = 0 := by
  unfold projectionResultFinishScanBackCellsRev
  rw [projectionScanCountFold_append,
    projectionMarkedBoolPayloadCells_scanCountFold_reverse,
    projectionScanCountFold_append,
    projectionDoneCodeCells_scanCountFold_reverse,
    projectionMarkedTickRepeated_scanCountFold_reverse]

theorem projectionResultFinishScanBackCellsRev_scanSafe
    (marked : Word Bool) :
    projectionScanSafe 0
        (projectionResultFinishScanBackCellsRev marked) := by
  unfold projectionResultFinishScanBackCellsRev
  apply projectionScanSafe_append
  · exact projectionMarkedBoolPayloadCells_scanSafe_reverse marked
  · rw [projectionMarkedBoolPayloadCells_scanCountFold_reverse]
    apply projectionScanSafe_append
    · exact projectionDoneCodeCells_scanSafe_reverse
    · rw [projectionDoneCodeCells_scanCountFold_reverse]
      exact projectionMarkedTickRepeated_scanSafe_reverse marked.length

theorem projectionResultFinishScanBackCellsRev_length
    (marked : Word Bool) :
    (projectionResultFinishScanBackCellsRev marked).length =
      8 * marked.length + 4 := by
  simp [projectionResultFinishScanBackCellsRev,
    projectionMarkedBoolPayloadCells_length,
    projectionRepeatedCells_length, projectionMarkedTickCodeCells,
    projectionDoneCodeCells, MachineDescription.encodeCodeSymbolAsInput]
  omega

theorem run_result_tail_to_first_payload
    (marked : Word Bool) (restCount : Nat)
    (payload : List (Option Bool))
    (baseLeftRev : List (Option Bool)) :
    Description.runConfig
        (8 * marked.length + 4 * restCount + 8)
        (projectionConfig 300
          (List.append [none, none, none, none] baseLeftRev)
          (projectionResultTailWorkCells marked (restCount + 1)
            payload)) =
      projectionConfig 330
        (projectionResultTailPayloadLeftRev marked restCount baseLeftRev)
        payload := by
  rw [show
      8 * marked.length + 4 * restCount + 8 =
        4 * marked.length +
          (4 + (4 * restCount + (4 + 4 * marked.length))) by
    omega,
    MachineDescription.runConfig_add]
  simp only [projectionResultTailWorkCells]
  rw [run_state300_marked_ticks]
  have htickCells :
      projectionCodeCells
          (List.replicate (restCount + 1) MachineCodeSymbol.tick) =
        List.append projectionTickCodeCells
          (projectionCodeCells
            (List.replicate restCount MachineCodeSymbol.tick)) := by
    rw [show restCount + 1 = Nat.succ restCount by omega]
    rfl
  rw [MachineDescription.runConfig_add]
  rw [htickCells]
  change
    Description.runConfig
        (4 * restCount + (4 + 4 * marked.length))
        (Description.runConfig 4
          (projectionConfig 300
            (List.append
              (projectionRepeatedCells projectionMarkedTickCodeCells
                marked.length).reverse
              (List.append [none, none, none, none] baseLeftRev))
            (List.append projectionTickCodeCells
              (List.append
                (projectionCodeCells
                  (List.replicate restCount MachineCodeSymbol.tick))
                (List.append projectionDoneCodeCells
                  (List.append (projectionMarkedBoolPayloadCells marked)
                    payload)))))) =
      projectionConfig 330
        (projectionResultTailPayloadLeftRev marked restCount baseLeftRev)
        payload
  rw [run_state300_mark_tick]
  rw [MachineDescription.runConfig_add]
  rw [projectionCodeCells_replicate_tick]
  rw [run_state320_ticks]
  rw [MachineDescription.runConfig_add]
  rw [run_state320_done]
  rw [run_state330_marked_payload]
  simp [projectionResultTailPayloadLeftRev]

theorem run_result_mark_one_tail
    (marked : Word Bool) (restCount : Nat) (b : Bool)
    (tail : List (Option Bool))
    (baseLeftRev : List (Option Bool)) :
    Description.runConfig
        (projectionResultMarkTailStepCost marked restCount)
        (projectionConfig 300
          (List.append [none, none, none, none] baseLeftRev)
          (projectionResultTailWorkCells marked (restCount + 1)
            (List.append (projectionBoolCellCodeCells b) tail))) =
      projectionConfig 300
        (List.append [none, none, none, none] baseLeftRev)
        (projectionResultTailWorkCells (List.append marked [b])
          restCount tail) := by
  let rest : Word Bool := List.replicate restCount false
  have hrestLen : rest.length = restCount := by
    simp [rest]
  have hcost :
      projectionResultMarkTailStepCost marked restCount =
        4 * marked.length +
          (4 + (4 * rest.length +
            (4 + (4 * marked.length +
              (4 + ((projectionInputMarkScanBackCellsRev marked rest b).length +
                7)))))) := by
    rw [projectionInputMarkScanBackCellsRev_length]
    simp [projectionResultMarkTailStepCost, hrestLen]
    omega
  rw [hcost, MachineDescription.runConfig_add]
  change
    Description.runConfig
        (4 + (4 * rest.length +
          (4 + (4 * marked.length +
            (4 + ((projectionInputMarkScanBackCellsRev marked rest b).length +
              7))))))
        (Description.runConfig
          (4 * marked.length)
          (projectionConfig 300
            (List.append [none, none, none, none] baseLeftRev)
            (projectionResultTailWorkCells marked (restCount + 1)
              (List.append (projectionBoolCellCodeCells b) tail)))) =
      projectionConfig 300
        (List.append [none, none, none, none] baseLeftRev)
        (projectionResultTailWorkCells (List.append marked [b])
          restCount tail)
  simp only [projectionResultTailWorkCells]
  rw [run_state300_marked_ticks]
  have htickCells :
      projectionCodeCells
          (List.replicate (restCount + 1) MachineCodeSymbol.tick) =
        List.append projectionTickCodeCells
          (projectionCodeCells
            (List.replicate restCount MachineCodeSymbol.tick)) := by
    rw [show restCount + 1 = Nat.succ restCount by omega]
    rfl
  rw [MachineDescription.runConfig_add]
  rw [htickCells]
  rw [show rest.length = restCount by exact hrestLen]
  change
    Description.runConfig
        (4 * restCount +
          (4 + (4 * marked.length +
            (4 + ((projectionInputMarkScanBackCellsRev marked rest b).length +
              7)))))
        (Description.runConfig 4
          (projectionConfig 300
            (List.append
              (projectionRepeatedCells projectionMarkedTickCodeCells
                marked.length).reverse
              (List.append [none, none, none, none] baseLeftRev))
            (List.append projectionTickCodeCells
              (List.append
                (projectionCodeCells
                  (List.replicate restCount MachineCodeSymbol.tick))
                (List.append projectionDoneCodeCells
                  (List.append (projectionMarkedBoolPayloadCells marked)
                    (List.append (projectionBoolCellCodeCells b) tail))))))) =
      projectionConfig 300
        (List.append [none, none, none, none] baseLeftRev)
        (projectionResultTailWorkCells (List.append marked [b])
          restCount tail)
  rw [run_state300_mark_tick]
  rw [MachineDescription.runConfig_add]
  rw [projectionCodeCells_replicate_tick]
  change
    Description.runConfig
        (4 + (4 * marked.length +
          (4 + ((projectionInputMarkScanBackCellsRev marked rest b).length +
            7))))
        (Description.runConfig
          (4 * restCount)
          (projectionConfig 320
            (List.append projectionMarkedTickCodeCells.reverse
              (List.append
                (projectionRepeatedCells projectionMarkedTickCodeCells
                  marked.length).reverse
                (List.append [none, none, none, none] baseLeftRev)))
            (List.append
              (projectionRepeatedCells projectionTickCodeCells restCount)
              (List.append projectionDoneCodeCells
                (List.append (projectionMarkedBoolPayloadCells marked)
                  (List.append (projectionBoolCellCodeCells b) tail)))))) =
      projectionConfig 300
        (List.append [none, none, none, none] baseLeftRev)
        (projectionResultTailWorkCells (List.append marked [b])
          restCount tail)
  rw [run_state320_ticks]
  rw [MachineDescription.runConfig_add]
  change
    Description.runConfig
        (4 * marked.length +
          (4 + ((projectionInputMarkScanBackCellsRev marked rest b).length +
            7)))
        (Description.runConfig 4
          (projectionConfig 320
            (List.append
              (projectionRepeatedCells projectionTickCodeCells
                restCount).reverse
              (List.append projectionMarkedTickCodeCells.reverse
                (List.append
                  (projectionRepeatedCells projectionMarkedTickCodeCells
                    marked.length).reverse
                  (List.append [none, none, none, none] baseLeftRev))))
            (List.append projectionDoneCodeCells
              (List.append (projectionMarkedBoolPayloadCells marked)
                (List.append (projectionBoolCellCodeCells b) tail))))) =
      projectionConfig 300
        (List.append [none, none, none, none] baseLeftRev)
        (projectionResultTailWorkCells (List.append marked [b])
          restCount tail)
  rw [run_state320_done]
  rw [MachineDescription.runConfig_add]
  change
    Description.runConfig
        (4 + ((projectionInputMarkScanBackCellsRev marked rest b).length + 7))
        (Description.runConfig
          (4 * marked.length)
          (projectionConfig 330
            (List.append projectionDoneCodeCells.reverse
              (List.append
                (projectionRepeatedCells projectionTickCodeCells
                  restCount).reverse
                (List.append projectionMarkedTickCodeCells.reverse
                  (List.append
                    (projectionRepeatedCells projectionMarkedTickCodeCells
                      marked.length).reverse
                    (List.append [none, none, none, none] baseLeftRev)))))
            (List.append (projectionMarkedBoolPayloadCells marked)
              (List.append (projectionBoolCellCodeCells b) tail)))) =
      projectionConfig 300
        (List.append [none, none, none, none] baseLeftRev)
        (projectionResultTailWorkCells (List.append marked [b])
          restCount tail)
  rw [run_state330_marked_payload]
  rw [MachineDescription.runConfig_add]
  change
    Description.runConfig
        ((projectionInputMarkScanBackCellsRev marked rest b).length + 7)
        (Description.runConfig 4
          (projectionConfig 330
            (List.append (projectionMarkedBoolPayloadCells marked).reverse
              (List.append projectionDoneCodeCells.reverse
                (List.append
                  (projectionRepeatedCells projectionTickCodeCells
                    restCount).reverse
                  (List.append projectionMarkedTickCodeCells.reverse
                    (List.append
                      (projectionRepeatedCells projectionMarkedTickCodeCells
                        marked.length).reverse
                      (List.append [none, none, none, none] baseLeftRev))))))
            (List.append (projectionBoolCellCodeCells b) tail))) =
      projectionConfig 300
        (List.append [none, none, none, none] baseLeftRev)
        (projectionResultTailWorkCells (List.append marked [b])
          restCount tail)
  rw [run_state330_mark_payload_cell]
  cases b
  · simp only [projectionResultTailWorkCells,
      projectionMarkedBoolPayloadCells_append_false,
      projectionCodeCells_replicate_tick]
    simpa [projectionScanLeftConfig, projectionInputMarkScanBackCellsRev,
      projectionInputMarkPreviousCells,
      projectionMarkedBoolCellScanPrefixRev,
      projectionMarkedBoolCellScanTailHead,
      projectionMarkedBoolPayloadCells_append,
      projectionMarkedBoolPayloadCells, projectionBoolPayloadCells,
      projectionCodeCells_replicate_tick, projectionRepeatedCells_succ_right,
      List.reverse_append, List.append_assoc, rest, hrestLen] using
        (run_scan340_cells_to_boundary
          (cellsRev := projectionInputMarkScanBackCellsRev marked rest false)
          (hsafe := projectionInputMarkScanBackCellsRev_scanSafe marked rest false)
          (hcount := projectionInputMarkScanBackCellsRev_scanCountFold marked rest false)
          (base := baseLeftRev)
          (tail := projectionMarkedBoolCellScanTailHead false :: tail))
  · simp only [projectionResultTailWorkCells,
      projectionMarkedBoolPayloadCells_append_true,
      projectionCodeCells_replicate_tick]
    simpa [projectionScanLeftConfig, projectionInputMarkScanBackCellsRev,
      projectionInputMarkPreviousCells,
      projectionMarkedBoolCellScanPrefixRev,
      projectionMarkedBoolCellScanTailHead,
      projectionMarkedBoolPayloadCells_append,
      projectionMarkedBoolPayloadCells, projectionBoolPayloadCells,
      projectionCodeCells_replicate_tick, projectionRepeatedCells_succ_right,
      List.reverse_append, List.append_assoc, rest, hrestLen] using
        (run_scan340_cells_to_boundary
          (cellsRev := projectionInputMarkScanBackCellsRev marked rest true)
          (hsafe := projectionInputMarkScanBackCellsRev_scanSafe marked rest true)
          (hcount := projectionInputMarkScanBackCellsRev_scanCountFold marked rest true)
          (base := baseLeftRev)
          (tail := projectionMarkedBoolCellScanTailHead true :: tail))

theorem run_input_tail_to_first_payload
    (marked : Word Bool) (restCount : Nat)
    (payload : List (Option Bool))
    (baseLeftRev : List (Option Bool)) :
    Description.runConfig
        (8 * marked.length + 4 * restCount + 8)
        (projectionConfig 100
          (List.append [none, none, none, none] baseLeftRev)
          (projectionResultTailWorkCells marked (restCount + 1)
            payload)) =
      projectionConfig 130
        (projectionResultTailPayloadLeftRev marked restCount baseLeftRev)
        payload := by
  rw [show
      8 * marked.length + 4 * restCount + 8 =
        4 * marked.length +
          (4 + (4 * restCount + (4 + 4 * marked.length))) by
    omega,
    MachineDescription.runConfig_add]
  simp only [projectionResultTailWorkCells]
  rw [run_state100_marked_ticks]
  have htickCells :
      projectionCodeCells
          (List.replicate (restCount + 1) MachineCodeSymbol.tick) =
        List.append projectionTickCodeCells
          (projectionCodeCells
            (List.replicate restCount MachineCodeSymbol.tick)) := by
    rw [show restCount + 1 = Nat.succ restCount by omega]
    rfl
  rw [MachineDescription.runConfig_add]
  rw [htickCells]
  change
    Description.runConfig
        (4 * restCount + (4 + 4 * marked.length))
        (Description.runConfig 4
          (projectionConfig 100
            (List.append
              (projectionRepeatedCells projectionMarkedTickCodeCells
                marked.length).reverse
              (List.append [none, none, none, none] baseLeftRev))
            (List.append projectionTickCodeCells
              (List.append
                (projectionCodeCells
                  (List.replicate restCount MachineCodeSymbol.tick))
                (List.append projectionDoneCodeCells
                  (List.append (projectionMarkedBoolPayloadCells marked)
                    payload)))))) =
      projectionConfig 130
        (projectionResultTailPayloadLeftRev marked restCount baseLeftRev)
        payload
  rw [run_state100_mark_tick]
  rw [MachineDescription.runConfig_add]
  rw [projectionCodeCells_replicate_tick]
  rw [run_state120_ticks]
  rw [MachineDescription.runConfig_add]
  rw [run_state120_done]
  rw [run_state130_marked_payload]
  simp [projectionResultTailPayloadLeftRev]

theorem run_input_mark_one_tail
    (marked : Word Bool) (restCount : Nat) (b : Bool)
    (tail : List (Option Bool))
    (baseLeftRev : List (Option Bool)) :
    Description.runConfig
        (projectionResultMarkTailStepCost marked restCount)
        (projectionConfig 100
          (List.append [none, none, none, none] baseLeftRev)
          (projectionResultTailWorkCells marked (restCount + 1)
            (List.append (projectionBoolCellCodeCells b) tail))) =
      projectionConfig 100
        (List.append [none, none, none, none] baseLeftRev)
        (projectionResultTailWorkCells (List.append marked [b])
          restCount tail) := by
  let rest : Word Bool := List.replicate restCount false
  have hrestLen : rest.length = restCount := by
    simp [rest]
  have hcost :
      projectionResultMarkTailStepCost marked restCount =
        4 * marked.length +
          (4 + (4 * rest.length +
            (4 + (4 * marked.length +
              (4 + ((projectionInputMarkScanBackCellsRev marked rest b).length +
                7)))))) := by
    rw [projectionInputMarkScanBackCellsRev_length]
    simp [projectionResultMarkTailStepCost, hrestLen]
    omega
  rw [hcost, MachineDescription.runConfig_add]
  change
    Description.runConfig
        (4 + (4 * rest.length +
          (4 + (4 * marked.length +
            (4 + ((projectionInputMarkScanBackCellsRev marked rest b).length +
              7))))))
        (Description.runConfig
          (4 * marked.length)
          (projectionConfig 100
            (List.append [none, none, none, none] baseLeftRev)
            (projectionResultTailWorkCells marked (restCount + 1)
              (List.append (projectionBoolCellCodeCells b) tail)))) =
      projectionConfig 100
        (List.append [none, none, none, none] baseLeftRev)
        (projectionResultTailWorkCells (List.append marked [b])
          restCount tail)
  simp only [projectionResultTailWorkCells]
  rw [run_state100_marked_ticks]
  have htickCells :
      projectionCodeCells
          (List.replicate (restCount + 1) MachineCodeSymbol.tick) =
        List.append projectionTickCodeCells
          (projectionCodeCells
            (List.replicate restCount MachineCodeSymbol.tick)) := by
    rw [show restCount + 1 = Nat.succ restCount by omega]
    rfl
  rw [MachineDescription.runConfig_add]
  rw [htickCells]
  rw [show rest.length = restCount by exact hrestLen]
  change
    Description.runConfig
        (4 * restCount +
          (4 + (4 * marked.length +
            (4 + ((projectionInputMarkScanBackCellsRev marked rest b).length +
              7)))))
        (Description.runConfig 4
          (projectionConfig 100
            (List.append
              (projectionRepeatedCells projectionMarkedTickCodeCells
                marked.length).reverse
              (List.append [none, none, none, none] baseLeftRev))
            (List.append projectionTickCodeCells
              (List.append
                (projectionCodeCells
                  (List.replicate restCount MachineCodeSymbol.tick))
                (List.append projectionDoneCodeCells
                  (List.append (projectionMarkedBoolPayloadCells marked)
                    (List.append (projectionBoolCellCodeCells b) tail))))))) =
      projectionConfig 100
        (List.append [none, none, none, none] baseLeftRev)
        (projectionResultTailWorkCells (List.append marked [b])
          restCount tail)
  rw [run_state100_mark_tick]
  rw [MachineDescription.runConfig_add]
  rw [projectionCodeCells_replicate_tick]
  change
    Description.runConfig
        (4 + (4 * marked.length +
          (4 + ((projectionInputMarkScanBackCellsRev marked rest b).length +
            7))))
        (Description.runConfig
          (4 * restCount)
          (projectionConfig 120
            (List.append projectionMarkedTickCodeCells.reverse
              (List.append
                (projectionRepeatedCells projectionMarkedTickCodeCells
                  marked.length).reverse
                (List.append [none, none, none, none] baseLeftRev)))
            (List.append
              (projectionRepeatedCells projectionTickCodeCells restCount)
              (List.append projectionDoneCodeCells
                (List.append (projectionMarkedBoolPayloadCells marked)
                  (List.append (projectionBoolCellCodeCells b) tail)))))) =
      projectionConfig 100
        (List.append [none, none, none, none] baseLeftRev)
        (projectionResultTailWorkCells (List.append marked [b])
          restCount tail)
  rw [run_state120_ticks]
  rw [MachineDescription.runConfig_add]
  change
    Description.runConfig
        (4 * marked.length +
          (4 + ((projectionInputMarkScanBackCellsRev marked rest b).length +
            7)))
        (Description.runConfig 4
          (projectionConfig 120
            (List.append
              (projectionRepeatedCells projectionTickCodeCells
                restCount).reverse
              (List.append projectionMarkedTickCodeCells.reverse
                (List.append
                  (projectionRepeatedCells projectionMarkedTickCodeCells
                    marked.length).reverse
                  (List.append [none, none, none, none] baseLeftRev))))
            (List.append projectionDoneCodeCells
              (List.append (projectionMarkedBoolPayloadCells marked)
                (List.append (projectionBoolCellCodeCells b) tail))))) =
      projectionConfig 100
        (List.append [none, none, none, none] baseLeftRev)
        (projectionResultTailWorkCells (List.append marked [b])
          restCount tail)
  rw [run_state120_done]
  rw [MachineDescription.runConfig_add]
  change
    Description.runConfig
        (4 + ((projectionInputMarkScanBackCellsRev marked rest b).length + 7))
        (Description.runConfig
          (4 * marked.length)
          (projectionConfig 130
            (List.append projectionDoneCodeCells.reverse
              (List.append
                (projectionRepeatedCells projectionTickCodeCells
                  restCount).reverse
                (List.append projectionMarkedTickCodeCells.reverse
                  (List.append
                    (projectionRepeatedCells projectionMarkedTickCodeCells
                      marked.length).reverse
                    (List.append [none, none, none, none] baseLeftRev)))))
            (List.append (projectionMarkedBoolPayloadCells marked)
              (List.append (projectionBoolCellCodeCells b) tail)))) =
      projectionConfig 100
        (List.append [none, none, none, none] baseLeftRev)
        (projectionResultTailWorkCells (List.append marked [b])
          restCount tail)
  rw [run_state130_marked_payload]
  rw [MachineDescription.runConfig_add]
  change
    Description.runConfig
        ((projectionInputMarkScanBackCellsRev marked rest b).length + 7)
        (Description.runConfig 4
          (projectionConfig 130
            (List.append (projectionMarkedBoolPayloadCells marked).reverse
              (List.append projectionDoneCodeCells.reverse
                (List.append
                  (projectionRepeatedCells projectionTickCodeCells
                    restCount).reverse
                  (List.append projectionMarkedTickCodeCells.reverse
                    (List.append
                      (projectionRepeatedCells projectionMarkedTickCodeCells
                        marked.length).reverse
                      (List.append [none, none, none, none] baseLeftRev))))))
            (List.append (projectionBoolCellCodeCells b) tail))) =
      projectionConfig 100
        (List.append [none, none, none, none] baseLeftRev)
        (projectionResultTailWorkCells (List.append marked [b])
          restCount tail)
  rw [run_state130_mark_payload_cell]
  cases b
  · simp only [projectionResultTailWorkCells,
      projectionMarkedBoolPayloadCells_append_false,
      projectionCodeCells_replicate_tick]
    simpa [projectionScanLeftConfig, projectionInputMarkScanBackCellsRev,
      projectionInputMarkPreviousCells,
      projectionMarkedBoolCellScanPrefixRev,
      projectionMarkedBoolCellScanTailHead,
      projectionMarkedBoolPayloadCells_append,
      projectionMarkedBoolPayloadCells, projectionBoolPayloadCells,
      projectionCodeCells_replicate_tick, projectionRepeatedCells_succ_right,
      List.reverse_append, List.append_assoc, rest, hrestLen] using
        (run_scan140_cells_to_boundary
          (cellsRev := projectionInputMarkScanBackCellsRev marked rest false)
          (hsafe := projectionInputMarkScanBackCellsRev_scanSafe marked rest false)
          (hcount := projectionInputMarkScanBackCellsRev_scanCountFold marked rest false)
          (base := baseLeftRev)
          (tail := projectionMarkedBoolCellScanTailHead false :: tail))
  · simp only [projectionResultTailWorkCells,
      projectionMarkedBoolPayloadCells_append_true,
      projectionCodeCells_replicate_tick]
    simpa [projectionScanLeftConfig, projectionInputMarkScanBackCellsRev,
      projectionInputMarkPreviousCells,
      projectionMarkedBoolCellScanPrefixRev,
      projectionMarkedBoolCellScanTailHead,
      projectionMarkedBoolPayloadCells_append,
      projectionMarkedBoolPayloadCells, projectionBoolPayloadCells,
      projectionCodeCells_replicate_tick, projectionRepeatedCells_succ_right,
      List.reverse_append, List.append_assoc, rest, hrestLen] using
        (run_scan140_cells_to_boundary
          (cellsRev := projectionInputMarkScanBackCellsRev marked rest true)
          (hsafe := projectionInputMarkScanBackCellsRev_scanSafe marked rest true)
          (hcount := projectionInputMarkScanBackCellsRev_scanCountFold marked rest true)
          (base := baseLeftRev)
          (tail := projectionMarkedBoolCellScanTailHead true :: tail))

theorem run_result_mark_one
    (marked rest : Word Bool) (b : Bool)
    (suffix : Word MachineCodeSymbol)
    (baseLeftRev : List (Option Bool)) :
    Description.runConfig
        (projectionInputMarkStepCost marked rest)
        (projectionConfig 300
          (List.append [none, none, none, none] baseLeftRev)
          (projectionBoolWordWorkCells marked (b :: rest) suffix)) =
      projectionConfig 300
        (List.append [none, none, none, none] baseLeftRev)
        (projectionBoolWordWorkCells (List.append marked [b]) rest suffix) := by
  have hcost :
      projectionInputMarkStepCost marked rest =
        4 * marked.length +
          (4 + (4 * rest.length +
            (4 + (4 * marked.length +
              (4 + ((projectionInputMarkScanBackCellsRev marked rest b).length +
                7)))))) := by
    rw [projectionInputMarkScanBackCellsRev_length]
    simp [projectionInputMarkStepCost]
    omega
  rw [hcost, MachineDescription.runConfig_add]
  change
    Description.runConfig
        (4 + (4 * rest.length +
          (4 + (4 * marked.length +
            (4 + ((projectionInputMarkScanBackCellsRev marked rest b).length +
              7))))))
        (Description.runConfig
          (4 * marked.length)
          (projectionConfig 300
            (List.append [none, none, none, none] baseLeftRev)
            (projectionBoolWordWorkCells marked (b :: rest) suffix))) =
      projectionConfig 300
        (List.append [none, none, none, none] baseLeftRev)
        (projectionBoolWordWorkCells (List.append marked [b]) rest suffix)
  simp only [projectionBoolWordWorkCells]
  rw [run_state300_marked_ticks]
  have htickCells :
      projectionCodeCells
          (List.replicate (b :: rest).length MachineCodeSymbol.tick) =
        List.append projectionTickCodeCells
          (projectionCodeCells
            (List.replicate rest.length MachineCodeSymbol.tick)) := by
    change
      projectionCodeCells
          (List.replicate (rest.length + 1) MachineCodeSymbol.tick) =
        List.append projectionTickCodeCells
          (projectionCodeCells
            (List.replicate rest.length MachineCodeSymbol.tick))
    rw [show rest.length + 1 = Nat.succ rest.length by omega]
    rfl
  rw [MachineDescription.runConfig_add]
  rw [htickCells]
  change
    Description.runConfig
        (4 * rest.length +
          (4 + (4 * marked.length +
            (4 + ((projectionInputMarkScanBackCellsRev marked rest b).length +
              7)))))
        (Description.runConfig 4
          (projectionConfig 300
            (List.append
              (projectionRepeatedCells projectionMarkedTickCodeCells
                marked.length).reverse
              (List.append [none, none, none, none] baseLeftRev))
            (List.append projectionTickCodeCells
              (List.append
                (projectionCodeCells
                  (List.replicate rest.length MachineCodeSymbol.tick))
                (List.append projectionDoneCodeCells
                  (List.append (projectionMarkedBoolPayloadCells marked)
                    (List.append (projectionBoolPayloadCells (b :: rest))
                      (projectionCodeCells suffix)))))))) =
      projectionConfig 300
        (List.append [none, none, none, none] baseLeftRev)
        (projectionBoolWordWorkCells (List.append marked [b]) rest suffix)
  rw [run_state300_mark_tick]
  rw [MachineDescription.runConfig_add]
  rw [projectionCodeCells_replicate_tick]
  change
    Description.runConfig
        (4 + (4 * marked.length +
          (4 + ((projectionInputMarkScanBackCellsRev marked rest b).length +
            7))))
        (Description.runConfig
          (4 * rest.length)
          (projectionConfig 320
            (List.append projectionMarkedTickCodeCells.reverse
              (List.append
                (projectionRepeatedCells projectionMarkedTickCodeCells
                  marked.length).reverse
                (List.append [none, none, none, none] baseLeftRev)))
            (List.append
              (projectionRepeatedCells projectionTickCodeCells rest.length)
              (List.append projectionDoneCodeCells
                (List.append (projectionMarkedBoolPayloadCells marked)
                  (List.append (projectionBoolPayloadCells (b :: rest))
                    (projectionCodeCells suffix))))))) =
      projectionConfig 300
        (List.append [none, none, none, none] baseLeftRev)
        (projectionBoolWordWorkCells (List.append marked [b]) rest suffix)
  rw [run_state320_ticks]
  rw [MachineDescription.runConfig_add]
  change
    Description.runConfig
        (4 * marked.length +
          (4 + ((projectionInputMarkScanBackCellsRev marked rest b).length +
            7)))
        (Description.runConfig 4
          (projectionConfig 320
            (List.append
              (projectionRepeatedCells projectionTickCodeCells
                rest.length).reverse
              (List.append projectionMarkedTickCodeCells.reverse
                (List.append
                  (projectionRepeatedCells projectionMarkedTickCodeCells
                    marked.length).reverse
                  (List.append [none, none, none, none] baseLeftRev))))
            (List.append projectionDoneCodeCells
              (List.append (projectionMarkedBoolPayloadCells marked)
                (List.append (projectionBoolPayloadCells (b :: rest))
                  (projectionCodeCells suffix)))))) =
      projectionConfig 300
        (List.append [none, none, none, none] baseLeftRev)
        (projectionBoolWordWorkCells (List.append marked [b]) rest suffix)
  rw [run_state320_done]
  rw [MachineDescription.runConfig_add]
  change
    Description.runConfig
        (4 + ((projectionInputMarkScanBackCellsRev marked rest b).length + 7))
        (Description.runConfig
          (4 * marked.length)
          (projectionConfig 330
            (List.append projectionDoneCodeCells.reverse
              (List.append
                (projectionRepeatedCells projectionTickCodeCells
                  rest.length).reverse
                (List.append projectionMarkedTickCodeCells.reverse
                  (List.append
                    (projectionRepeatedCells projectionMarkedTickCodeCells
                      marked.length).reverse
                    (List.append [none, none, none, none] baseLeftRev)))))
            (List.append (projectionMarkedBoolPayloadCells marked)
              (List.append (projectionBoolPayloadCells (b :: rest))
                (projectionCodeCells suffix))))) =
      projectionConfig 300
        (List.append [none, none, none, none] baseLeftRev)
        (projectionBoolWordWorkCells (List.append marked [b]) rest suffix)
  rw [run_state330_marked_payload]
  rw [MachineDescription.runConfig_add]
  change
    Description.runConfig
        ((projectionInputMarkScanBackCellsRev marked rest b).length + 7)
        (Description.runConfig 4
          (projectionConfig 330
            (List.append (projectionMarkedBoolPayloadCells marked).reverse
              (List.append projectionDoneCodeCells.reverse
                (List.append
                  (projectionRepeatedCells projectionTickCodeCells
                    rest.length).reverse
                  (List.append projectionMarkedTickCodeCells.reverse
                    (List.append
                      (projectionRepeatedCells projectionMarkedTickCodeCells
                        marked.length).reverse
                      (List.append [none, none, none, none] baseLeftRev))))))
            (List.append (projectionBoolPayloadCells (b :: rest))
              (projectionCodeCells suffix)))) =
      projectionConfig 300
        (List.append [none, none, none, none] baseLeftRev)
        (projectionBoolWordWorkCells (List.append marked [b]) rest suffix)
  rw [show projectionBoolPayloadCells (b :: rest) =
      List.append (projectionBoolCellCodeCells b)
        (projectionBoolPayloadCells rest) by
    rfl]
  rw [show
      List.append
          (List.append (projectionBoolCellCodeCells b)
            (projectionBoolPayloadCells rest))
          (projectionCodeCells suffix) =
        List.append (projectionBoolCellCodeCells b)
          (List.append (projectionBoolPayloadCells rest)
            (projectionCodeCells suffix)) by
    simp [List.append_assoc]]
  rw [run_state330_mark_payload_cell]
  cases b
  · simp only [projectionBoolWordWorkCells,
      projectionMarkedBoolPayloadCells_append_false,
      projectionCodeCells_replicate_tick]
    simpa [projectionScanLeftConfig, projectionInputMarkScanBackCellsRev,
      projectionInputMarkPreviousCells, projectionInputMarkScanTail,
      projectionMarkedBoolCellScanPrefixRev,
      projectionMarkedBoolCellScanTailHead, projectionBoolWordWorkCells,
      projectionMarkedBoolPayloadCells_append,
      projectionMarkedBoolPayloadCells, projectionBoolPayloadCells,
      projectionCodeCells_replicate_tick, projectionRepeatedCells_succ_right,
      List.reverse_append, List.append_assoc] using
        (run_scan340_cells_to_boundary
          (cellsRev := projectionInputMarkScanBackCellsRev marked rest false)
          (hsafe := projectionInputMarkScanBackCellsRev_scanSafe marked rest false)
          (hcount := projectionInputMarkScanBackCellsRev_scanCountFold marked rest false)
          (base := baseLeftRev)
          (tail := projectionInputMarkScanTail rest false suffix))
  · simp only [projectionBoolWordWorkCells,
      projectionMarkedBoolPayloadCells_append_true,
      projectionCodeCells_replicate_tick]
    simpa [projectionScanLeftConfig, projectionInputMarkScanBackCellsRev,
      projectionInputMarkPreviousCells, projectionInputMarkScanTail,
      projectionMarkedBoolCellScanPrefixRev,
      projectionMarkedBoolCellScanTailHead, projectionBoolWordWorkCells,
      projectionMarkedBoolPayloadCells_append,
      projectionMarkedBoolPayloadCells, projectionBoolPayloadCells,
      projectionCodeCells_replicate_tick, projectionRepeatedCells_succ_right,
      List.reverse_append, List.append_assoc] using
        (run_scan340_cells_to_boundary
          (cellsRev := projectionInputMarkScanBackCellsRev marked rest true)
          (hsafe := projectionInputMarkScanBackCellsRev_scanSafe marked rest true)
          (hcount := projectionInputMarkScanBackCellsRev_scanCountFold marked rest true)
          (base := baseLeftRev)
          (tail := projectionInputMarkScanTail rest true suffix))

theorem run_result_finish_marked
    (marked : Word Bool) (baseLeftRev : List (Option Bool)) :
    Description.runConfig
        (16 * marked.length + 16)
        (projectionConfig 300
          (List.append [none, none, none, none] baseLeftRev)
          (projectionBoolWordWorkCells marked [] [])) =
      projectionConfig 367
        (List.append projectionDoneCodeCells.reverse baseLeftRev)
        (List.append (projectionAllMarkedBoolWordCells marked) [none]) := by
  have hcost :
      16 * marked.length + 16 =
        4 * marked.length +
          (4 + (4 * marked.length +
            (1 + ((projectionResultFinishScanBackCellsRev marked).length +
              7)))) := by
    rw [projectionResultFinishScanBackCellsRev_length]
    omega
  have hnil :
      projectionCodeCells ([] : Word MachineCodeSymbol) = [] := rfl
  rw [hcost, MachineDescription.runConfig_add]
  simp only [projectionBoolWordWorkCells]
  rw [run_state300_marked_ticks]
  simp [List.length_nil, hnil, projectionBoolPayloadCells]
  rw [MachineDescription.runConfig_add]
  change
    Description.runConfig
        (4 * marked.length +
          (1 + ((projectionResultFinishScanBackCellsRev marked).length + 7)))
        (Description.runConfig 4
          (projectionConfig 300
            (List.append
              (projectionRepeatedCells projectionMarkedTickCodeCells
                marked.length).reverse
              (List.append [none, none, none, none] baseLeftRev))
            (List.append projectionDoneCodeCells
              (projectionMarkedBoolPayloadCells marked)))) =
      projectionConfig 367
        (List.append projectionDoneCodeCells.reverse baseLeftRev)
        (List.append (projectionAllMarkedBoolWordCells marked) [none])
  rw [run_state300_done]
  rw [MachineDescription.runConfig_add]
  change
    Description.runConfig
        (1 + ((projectionResultFinishScanBackCellsRev marked).length + 7))
        (Description.runConfig
          (4 * marked.length)
          (projectionConfig 350
            (List.append projectionDoneCodeCells.reverse
              (List.append
                (projectionRepeatedCells projectionMarkedTickCodeCells
                  marked.length).reverse
                (List.append [none, none, none, none] baseLeftRev)))
            (projectionMarkedBoolPayloadCells marked))) =
      projectionConfig 367
        (List.append projectionDoneCodeCells.reverse baseLeftRev)
        (List.append (projectionAllMarkedBoolWordCells marked) [none])
  rw [show projectionMarkedBoolPayloadCells marked =
      List.append (projectionMarkedBoolPayloadCells marked)
        ([] : List (Option Bool)) by
    simp]
  rw [run_state350_marked_payload]
  rw [show
      1 + ((projectionResultFinishScanBackCellsRev marked).length + 7) =
        1 + ((projectionResultFinishScanBackCellsRev marked).length + 7) by
    rfl,
    MachineDescription.runConfig_add]
  change
    Description.runConfig
        ((projectionResultFinishScanBackCellsRev marked).length + 7)
        (Description.runConfig 1
          (projectionConfig 350
            (List.append (projectionMarkedBoolPayloadCells marked).reverse
              (List.append projectionDoneCodeCells.reverse
                (List.append
                  (projectionRepeatedCells projectionMarkedTickCodeCells
                    marked.length).reverse
                  (List.append [none, none, none, none] baseLeftRev))))
            ([] : List (Option Bool)))) =
      projectionConfig 367
        (List.append projectionDoneCodeCells.reverse baseLeftRev)
        (List.append (projectionAllMarkedBoolWordCells marked) [none])
  have hscanStart :
      Description.runConfig 1
          (projectionConfig 350
            (List.append (projectionMarkedBoolPayloadCells marked).reverse
              (List.append projectionDoneCodeCells.reverse
                (List.append
                  (projectionRepeatedCells projectionMarkedTickCodeCells
                    marked.length).reverse
                  (List.append [none, none, none, none] baseLeftRev))))
            ([] : List (Option Bool))) =
        projectionScanLeftConfig 360
          (List.append ([none, none, none] : List (Option Bool)) baseLeftRev)
          none (projectionResultFinishScanBackCellsRev marked) [none] := by
    simpa [projectionResultFinishScanBackCellsRev, List.append_assoc] using
      (run_state350_blank_to_scan360
        (cellsRev := projectionResultFinishScanBackCellsRev marked)
        (base := baseLeftRev))
  rw [hscanStart]
  rw [run_scan360_cells_to_boundary
    (hsafe := projectionResultFinishScanBackCellsRev_scanSafe marked)
    (hcount := projectionResultFinishScanBackCellsRev_scanCountFold marked)]
  simp [projectionResultFinishScanBackCellsRev, projectionAllMarkedBoolWordCells,
    List.reverse_append, List.append_assoc]

def projectionResultRemainingCost
    (marked rest : Word Bool) : Nat :=
  12 * rest.length * rest.length +
    16 * marked.length * rest.length +
    34 * rest.length + 16 * marked.length + 16

theorem run_result_bool_word_acc
    (marked rest : Word Bool) (baseLeftRev : List (Option Bool)) :
    Description.runConfig
        (projectionResultRemainingCost marked rest)
        (projectionConfig 300
          (List.append [none, none, none, none] baseLeftRev)
          (projectionBoolWordWorkCells marked rest [])) =
      projectionConfig 367
        (List.append projectionDoneCodeCells.reverse baseLeftRev)
        (List.append
          (projectionAllMarkedBoolWordCells (List.append marked rest))
          [none]) := by
  induction rest generalizing marked baseLeftRev with
  | nil =>
      simp [projectionResultRemainingCost]
      exact
        run_result_finish_marked
          marked baseLeftRev
  | cons b rest ih =>
      have hcost :
          projectionResultRemainingCost marked (b :: rest) =
            projectionInputMarkStepCost marked rest +
              projectionResultRemainingCost (List.append marked [b]) rest := by
        simp [projectionResultRemainingCost, projectionInputMarkStepCost,
          Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
        omega
      rw [hcost, MachineDescription.runConfig_add]
      rw [run_result_mark_one]
      rw [ih]
      have hword :
          List.append (List.append marked [b]) rest =
            List.append marked (b :: rest) := by
        simp [List.append_assoc]
      rw [hword]

theorem run_result_bool_word
    (w : Word Bool) (baseLeftRev : List (Option Bool)) :
    Description.runConfig
        (projectionResultBoolWordCost w)
        (projectionConfig 300
          (List.append [none, none, none, none] baseLeftRev)
          (projectionCodeCells (MachineDescription.encodeBoolWord w))) =
      projectionConfig 367
        (List.append projectionDoneCodeCells.reverse baseLeftRev)
        (List.append (projectionAllMarkedBoolWordCells w) [none]) := by
  have h :=
    run_result_bool_word_acc
      ([] : Word Bool) w baseLeftRev
  simpa [projectionResultRemainingCost, projectionResultBoolWordCost,
    projectionBoolWordWorkCells_nil_eq_encodeBoolWordAppend] using h

end ControllerStageInputProjection
end Computability
end FoC
