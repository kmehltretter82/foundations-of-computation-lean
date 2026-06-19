import FoC.Computability.Compiler.Core.ControllerStageInputProjection.Base

set_option doc.verso true

/-!
# ScanInput

Supporting declarations and helper lemmas for Computability Compiler Core ControllerStageInputProjection ScanInput.
-/


namespace FoC
namespace Computability

open Languages

namespace ControllerStageInputProjection


def projectionScanState140 : Nat -> Nat
  | 0 => 140
  | 1 => 141
  | 2 => 142
  | _ => 143

def projectionScanCountStep (count : Nat) :
    Option Bool -> Nat
  | some _ => 0
  | none =>
      match count with
      | 0 => 1
      | 1 => 2
      | _ => 3

def projectionScanCountFold : Nat -> List (Option Bool) -> Nat
  | count, [] => count
  | count, cell :: rest =>
      projectionScanCountFold (projectionScanCountStep count cell) rest

def projectionScanSafe : Nat -> List (Option Bool) -> Prop
  | _, [] => True
  | count, cell :: rest =>
      (count ≠ 3 ∨ cell ≠ none) ∧
        projectionScanSafe (projectionScanCountStep count cell) rest

def projectionScanLeftConfig
    (state : Nat) (leftOfBoundary : List (Option Bool))
    (boundaryHead : Option Bool) :
    List (Option Bool) -> List (Option Bool) ->
      MachineDescription.Configuration
  | [], tail =>
      projectionConfig state leftOfBoundary (boundaryHead :: tail)
  | cell :: rest, tail =>
      projectionConfig state
        (List.append rest (boundaryHead :: leftOfBoundary)) (cell :: tail)

 /-- `projectionScanCountStep_le_three` characterizes a scan safety phase. -/
theorem projectionScanCountStep_le_three
    {count : Nat} (hcount : count ≤ 3) (cell : Option Bool) :
    projectionScanCountStep count cell ≤ 3 := by
  cases cell with
  | none =>
      cases count with
      | zero =>
          simp [projectionScanCountStep]
      | succ count =>
          cases count with
          | zero =>
              simp [projectionScanCountStep]
          | succ count =>
              simp [projectionScanCountStep]
  | some b =>
      cases b <;> simp [projectionScanCountStep]

 /-- `projectionScanCountFold_append` characterizes a scan safety phase. -/
theorem projectionScanCountFold_append
    (count : Nat) (left right : List (Option Bool)) :
    projectionScanCountFold count (List.append left right) =
      projectionScanCountFold
        (projectionScanCountFold count left) right := by
  induction left generalizing count with
  | nil =>
      rfl
  | cons cell rest ih =>
      change
        projectionScanCountFold (projectionScanCountStep count cell)
            (List.append rest right) =
          projectionScanCountFold
            (projectionScanCountFold (projectionScanCountStep count cell)
              rest) right
      rw [ih]

 /-- `projectionScanSafe_append` characterizes a scan safety phase. -/
theorem projectionScanSafe_append
    {count : Nat} {left right : List (Option Bool)}
    (hleft : projectionScanSafe count left)
    (hright :
      projectionScanSafe (projectionScanCountFold count left) right) :
    projectionScanSafe count (List.append left right) := by
  induction left generalizing count with
  | nil =>
      exact hright
  | cons cell rest ih =>
      rcases hleft with ⟨hcell, hrest⟩
      exact ⟨hcell, ih hrest hright⟩

 /-- `projectionScanCountFold_repeated_zero` characterizes a scan safety phase. -/
theorem projectionScanCountFold_repeated_zero
    (chunk : List (Option Bool))
    (hchunk : projectionScanCountFold 0 chunk = 0)
    (count : Nat) :
    projectionScanCountFold 0 (projectionRepeatedCells chunk count) = 0 := by
  induction count with
  | zero =>
      rfl
  | succ count ih =>
      change
        projectionScanCountFold 0
            (List.append chunk (projectionRepeatedCells chunk count)) = 0
      rw [projectionScanCountFold_append, hchunk, ih]

 /-- `projectionScanSafe_repeated_zero` characterizes a scan safety phase. -/
theorem projectionScanSafe_repeated_zero
    (chunk : List (Option Bool))
    (hsafe : projectionScanSafe 0 chunk)
    (hchunk : projectionScanCountFold 0 chunk = 0)
    (count : Nat) :
    projectionScanSafe 0 (projectionRepeatedCells chunk count) := by
  induction count with
  | zero =>
      trivial
  | succ count ih =>
      change
        projectionScanSafe 0
          (List.append chunk (projectionRepeatedCells chunk count))
      apply projectionScanSafe_append
      · exact hsafe
      · rw [hchunk]
        exact ih

 /-- `projectionMarkedTickCodeCells_scanSafe_reverse` characterizes a scan safety phase. -/
theorem projectionMarkedTickCodeCells_scanSafe_reverse :
    projectionScanSafe 0 projectionMarkedTickCodeCells.reverse := by
  simp [projectionMarkedTickCodeCells, projectionScanSafe,
    projectionScanCountStep]

 /-- `projectionMarkedTickCodeCells_scanCountFold_reverse` characterizes a scan safety phase. -/
theorem projectionMarkedTickCodeCells_scanCountFold_reverse :
    projectionScanCountFold 0 projectionMarkedTickCodeCells.reverse = 0 := by
  simp [projectionMarkedTickCodeCells, projectionScanCountFold,
    projectionScanCountStep]

 /-- `projectionTickCodeCells_scanSafe_reverse` characterizes a scan safety phase. -/
theorem projectionTickCodeCells_scanSafe_reverse :
    projectionScanSafe 0 projectionTickCodeCells.reverse := by
  simp [projectionTickCodeCells, MachineDescription.encodeCodeSymbolAsInput,
    projectionScanSafe, projectionScanCountStep]

 /-- `projectionTickCodeCells_scanCountFold_reverse` characterizes a scan safety phase. -/
theorem projectionTickCodeCells_scanCountFold_reverse :
    projectionScanCountFold 0 projectionTickCodeCells.reverse = 0 := by
  simp [projectionTickCodeCells, MachineDescription.encodeCodeSymbolAsInput,
    projectionScanCountFold, projectionScanCountStep]

 /-- `projectionDoneCodeCells_scanSafe_reverse` characterizes a scan safety phase. -/
theorem projectionDoneCodeCells_scanSafe_reverse :
    projectionScanSafe 0 projectionDoneCodeCells.reverse := by
  simp [projectionDoneCodeCells, MachineDescription.encodeCodeSymbolAsInput,
    projectionScanSafe, projectionScanCountStep]

 /-- `projectionDoneCodeCells_scanCountFold_reverse` characterizes a scan safety phase. -/
theorem projectionDoneCodeCells_scanCountFold_reverse :
    projectionScanCountFold 0 projectionDoneCodeCells.reverse = 0 := by
  simp [projectionDoneCodeCells, MachineDescription.encodeCodeSymbolAsInput,
    projectionScanCountFold, projectionScanCountStep]

 /-- `projectionMarkedBoolCellCodeCells_scanSafe_reverse` characterizes a scan safety phase. -/
theorem projectionMarkedBoolCellCodeCells_scanSafe_reverse
    (b : Bool) :
    projectionScanSafe 0 (projectionMarkedBoolCellCodeCells b).reverse := by
  cases b <;>
    simp [projectionMarkedBoolCellCodeCells, projectionScanSafe,
      projectionScanCountStep]

 /-- `projectionMarkedBoolCellCodeCells_scanCountFold_reverse` characterizes a scan safety phase. -/
theorem projectionMarkedBoolCellCodeCells_scanCountFold_reverse
    (b : Bool) :
    projectionScanCountFold 0 (projectionMarkedBoolCellCodeCells b).reverse =
      0 := by
  cases b <;>
    simp [projectionMarkedBoolCellCodeCells, projectionScanCountFold,
      projectionScanCountStep]

 /-- `projectionMarkedBoolPayloadCells_scanCountFold_reverse` characterizes a scan safety phase. -/
theorem projectionMarkedBoolPayloadCells_scanCountFold_reverse
    (w : Word Bool) :
    projectionScanCountFold 0
        (projectionMarkedBoolPayloadCells w).reverse = 0 := by
  induction w with
  | nil =>
      rfl
  | cons b rest ih =>
      rw [show
          (projectionMarkedBoolPayloadCells (b :: rest)).reverse =
            List.append (projectionMarkedBoolPayloadCells rest).reverse
              (projectionMarkedBoolCellCodeCells b).reverse by
        simp [projectionMarkedBoolPayloadCells, List.reverse_append]]
      rw [projectionScanCountFold_append, ih,
        projectionMarkedBoolCellCodeCells_scanCountFold_reverse]

 /-- `projectionMarkedBoolPayloadCells_scanSafe_reverse` characterizes a scan safety phase. -/
theorem projectionMarkedBoolPayloadCells_scanSafe_reverse
    (w : Word Bool) :
    projectionScanSafe 0 (projectionMarkedBoolPayloadCells w).reverse := by
  induction w with
  | nil =>
      trivial
  | cons b rest ih =>
      rw [show
          (projectionMarkedBoolPayloadCells (b :: rest)).reverse =
            List.append (projectionMarkedBoolPayloadCells rest).reverse
              (projectionMarkedBoolCellCodeCells b).reverse by
        simp [projectionMarkedBoolPayloadCells, List.reverse_append]]
      apply projectionScanSafe_append
      · exact ih
      · rw [projectionMarkedBoolPayloadCells_scanCountFold_reverse rest]
        exact projectionMarkedBoolCellCodeCells_scanSafe_reverse b

 /-- `run_scan140_step` states the corresponding theorem run form. -/
theorem run_scan140_step
    (count : Nat) (hcount : count ≤ 3)
    (cell : Option Bool) (rest leftOfBoundary tail : List (Option Bool))
    (boundaryHead : Option Bool)
    (hsafe : count ≠ 3 ∨ cell ≠ none) :
    Description.runConfig 1
        (projectionScanLeftConfig (projectionScanState140 count)
          leftOfBoundary boundaryHead (cell :: rest) tail) =
      projectionScanLeftConfig
        (projectionScanState140 (projectionScanCountStep count cell))
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

 /-- `run_scan140_cells` states the corresponding theorem run form. -/
theorem run_scan140_cells
    (cellsRev : List (Option Bool)) (count : Nat) (hcount : count ≤ 3)
    (hsafe : projectionScanSafe count cellsRev)
    (leftOfBoundary : List (Option Bool)) (boundaryHead : Option Bool)
    (tail : List (Option Bool)) :
    Description.runConfig cellsRev.length
        (projectionScanLeftConfig (projectionScanState140 count)
          leftOfBoundary boundaryHead cellsRev tail) =
      projectionConfig
        (projectionScanState140
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
              (projectionScanLeftConfig (projectionScanState140 count)
                leftOfBoundary boundaryHead (cell :: rest) tail)) =
          projectionConfig
            (projectionScanState140
              (projectionScanCountFold count (cell :: rest)))
            leftOfBoundary
            (boundaryHead :: List.append (cell :: rest).reverse tail)
      rw [run_scan140_step
        count hcount cell rest leftOfBoundary tail boundaryHead hcell]
      rw [ih (projectionScanCountStep count cell) hnext hrest
        (cell :: tail)]
      simp [projectionScanCountFold, List.append_assoc]

 /-- `run_scan140_boundary` states the corresponding theorem run form. -/
theorem run_scan140_boundary
    (base tail : List (Option Bool)) :
    Description.runConfig 7
        (projectionConfig 140 (none :: none :: none :: base) (none :: tail)) =
      projectionConfig 100
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

 /-- `run_scan140_cells_to_boundary` states the corresponding theorem run form. -/
theorem run_scan140_cells_to_boundary
    (cellsRev : List (Option Bool))
    (hsafe : projectionScanSafe 0 cellsRev)
    (hcount : projectionScanCountFold 0 cellsRev = 0)
    (base tail : List (Option Bool)) :
    Description.runConfig
        (cellsRev.length + 7)
        (projectionScanLeftConfig 140
          (List.append ([none, none, none] : List (Option Bool)) base) none
          cellsRev tail) =
      projectionConfig 100
        (List.append [none, none, none, none] base)
        (List.append cellsRev.reverse tail) := by
  rw [MachineDescription.runConfig_add]
  change
    Description.runConfig 7
        (Description.runConfig
        cellsRev.length
        (projectionScanLeftConfig (projectionScanState140 0)
          (List.append ([none, none, none] : List (Option Bool)) base) none
          cellsRev tail)) =
      projectionConfig 100
        (List.append [none, none, none, none] base)
        (List.append cellsRev.reverse tail)
  rw [run_scan140_cells
    cellsRev 0 (by omega) hsafe
    (List.append ([none, none, none] : List (Option Bool)) base) none tail]
  rw [hcount]
  simpa [List.append_assoc] using
    run_scan140_boundary
      base (List.append cellsRev.reverse tail)

def projectionScanState160 : Nat -> Nat
  | 0 => 160
  | 1 => 161
  | 2 => 162
  | _ => 163

 /-- `run_scan160_step` states the corresponding theorem run form. -/
theorem run_scan160_step
    (count : Nat) (hcount : count ≤ 3)
    (cell : Option Bool) (rest leftOfBoundary tail : List (Option Bool))
    (boundaryHead : Option Bool)
    (hsafe : count ≠ 3 ∨ cell ≠ none) :
    Description.runConfig 1
        (projectionScanLeftConfig (projectionScanState160 count)
          leftOfBoundary boundaryHead (cell :: rest) tail) =
      projectionScanLeftConfig
        (projectionScanState160 (projectionScanCountStep count cell))
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

 /-- `run_scan160_cells` states the corresponding theorem run form. -/
theorem run_scan160_cells
    (cellsRev : List (Option Bool)) (count : Nat) (hcount : count ≤ 3)
    (hsafe : projectionScanSafe count cellsRev)
    (leftOfBoundary : List (Option Bool)) (boundaryHead : Option Bool)
    (tail : List (Option Bool)) :
    Description.runConfig cellsRev.length
        (projectionScanLeftConfig (projectionScanState160 count)
          leftOfBoundary boundaryHead cellsRev tail) =
      projectionConfig
        (projectionScanState160
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
              (projectionScanLeftConfig (projectionScanState160 count)
                leftOfBoundary boundaryHead (cell :: rest) tail)) =
          projectionConfig
            (projectionScanState160
              (projectionScanCountFold count (cell :: rest)))
            leftOfBoundary
            (boundaryHead :: List.append (cell :: rest).reverse tail)
      rw [run_scan160_step
        count hcount cell rest leftOfBoundary tail boundaryHead hcell]
      rw [ih (projectionScanCountStep count cell) hnext hrest
        (cell :: tail)]
      simp [projectionScanCountFold, List.append_assoc]

 /-- `run_scan160_boundary` states the corresponding theorem run form. -/
theorem run_scan160_boundary
    (base tail : List (Option Bool)) :
    Description.runConfig 7
        (projectionConfig 160 (none :: none :: none :: base) (none :: tail)) =
      projectionConfig 170
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

 /-- `run_scan160_cells_to_boundary` states the corresponding theorem run form. -/
theorem run_scan160_cells_to_boundary
    (cellsRev : List (Option Bool))
    (hsafe : projectionScanSafe 0 cellsRev)
    (hcount : projectionScanCountFold 0 cellsRev = 0)
    (base tail : List (Option Bool)) :
    Description.runConfig
        (cellsRev.length + 7)
        (projectionScanLeftConfig 160
          (List.append ([none, none, none] : List (Option Bool)) base) none
          cellsRev tail) =
      projectionConfig 170
        (List.append [none, none, none, none] base)
        (List.append cellsRev.reverse tail) := by
  rw [MachineDescription.runConfig_add]
  change
    Description.runConfig 7
        (Description.runConfig
        cellsRev.length
        (projectionScanLeftConfig (projectionScanState160 0)
          (List.append ([none, none, none] : List (Option Bool)) base) none
          cellsRev tail)) =
      projectionConfig 170
        (List.append [none, none, none, none] base)
        (List.append cellsRev.reverse tail)
  rw [run_scan160_cells
    cellsRev 0 (by omega) hsafe
    (List.append ([none, none, none] : List (Option Bool)) base) none tail]
  rw [hcount]
  simpa [List.append_assoc] using
    run_scan160_boundary
      base (List.append cellsRev.reverse tail)

 /-- `run_state100_marked_tick` states the corresponding theorem run form. -/
theorem run_state100_marked_tick
    (leftRev tail : List (Option Bool)) :
    Description.runConfig 4
        (projectionConfig 100 leftRev
          (List.append projectionMarkedTickCodeCells tail)) =
      projectionConfig 100
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

 /-- `run_state100_marked_ticks` states the corresponding theorem run form. -/
theorem run_state100_marked_ticks
    (count : Nat) (leftRev tail : List (Option Bool)) :
    Description.runConfig (4 * count)
        (projectionConfig 100 leftRev
          (List.append
            (projectionRepeatedCells projectionMarkedTickCodeCells count)
            tail)) =
      projectionConfig 100
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
            (projectionConfig 100 leftRev
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
            (projectionConfig 100 leftRev
              (List.append projectionMarkedTickCodeCells
                (List.append
                  (projectionRepeatedCells projectionMarkedTickCodeCells count)
                  tail)))) = _
      rw [run_state100_marked_tick]
      rw [ih]
      simp [List.reverse_append, List.append_assoc]

 /-- `run_state100_mark_tick` states the corresponding theorem run form. -/
theorem run_state100_mark_tick
    (leftRev tail : List (Option Bool)) :
    Description.runConfig 4
        (projectionConfig 100 leftRev
          (List.append projectionTickCodeCells tail)) =
      projectionConfig 120
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

 /-- `run_state120_tick` states the corresponding theorem run form. -/
theorem run_state120_tick
    (leftRev tail : List (Option Bool)) :
    Description.runConfig 4
        (projectionConfig 120 leftRev
          (List.append projectionTickCodeCells tail)) =
      projectionConfig 120
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

 /-- `run_state120_ticks` states the corresponding theorem run form. -/
theorem run_state120_ticks
    (count : Nat) (leftRev tail : List (Option Bool)) :
    Description.runConfig (4 * count)
        (projectionConfig 120 leftRev
          (List.append
            (projectionRepeatedCells projectionTickCodeCells count)
            tail)) =
      projectionConfig 120
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
            (projectionConfig 120 leftRev
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
            (projectionConfig 120 leftRev
              (List.append projectionTickCodeCells
                (List.append
                  (projectionRepeatedCells projectionTickCodeCells count)
                  tail)))) = _
      rw [run_state120_tick]
      rw [ih]
      simp [List.reverse_append, List.append_assoc]

 /-- `run_state120_done` states the corresponding theorem run form. -/
theorem run_state120_done
    (leftRev tail : List (Option Bool)) :
    Description.runConfig 4
        (projectionConfig 120 leftRev
          (List.append projectionDoneCodeCells tail)) =
      projectionConfig 130
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

 /-- `run_state130_marked_payload_cell` states the corresponding theorem run form. -/
theorem run_state130_marked_payload_cell
    (b : Bool) (leftRev tail : List (Option Bool)) :
    Description.runConfig 4
        (projectionConfig 130 leftRev
          (List.append (projectionMarkedBoolCellCodeCells b) tail)) =
      projectionConfig 130
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

 /-- `run_state130_marked_payload_cell_append` states the corresponding theorem run form. -/
theorem run_state130_marked_payload_cell_append
    (b : Bool) (leftRev middle tail : List (Option Bool)) :
    Description.runConfig 4
        (projectionConfig 130 leftRev
          (List.append (projectionMarkedBoolCellCodeCells b) middle ++
            tail)) =
      projectionConfig 130
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

 /-- `run_state130_marked_payload` states the corresponding theorem run form. -/
theorem run_state130_marked_payload
    (w : Word Bool) (leftRev tail : List (Option Bool)) :
    Description.runConfig (4 * w.length)
        (projectionConfig 130 leftRev
          (List.append (projectionMarkedBoolPayloadCells w) tail)) =
      projectionConfig 130
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
            (projectionConfig 130 leftRev
              (projectionMarkedBoolPayloadCells (b :: rest) ++ tail))) = _
      rw [show projectionMarkedBoolPayloadCells (b :: rest) =
          List.append (projectionMarkedBoolCellCodeCells b)
            (projectionMarkedBoolPayloadCells rest) by
        rfl]
      rw [run_state130_marked_payload_cell_append]
      rw [ih]
      simp [List.reverse_append, List.append_assoc]

 /-- `run_state100_done` states the corresponding theorem run form. -/
theorem run_state100_done
    (leftRev tail : List (Option Bool)) :
    Description.runConfig 4
        (projectionConfig 100 leftRev
          (List.append projectionDoneCodeCells tail)) =
      projectionConfig 150
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

 /-- `run_state150_marked_payload_cell` states the corresponding theorem run form. -/
theorem run_state150_marked_payload_cell
    (b : Bool) (leftRev tail : List (Option Bool)) :
    Description.runConfig 4
        (projectionConfig 150 leftRev
          (List.append (projectionMarkedBoolCellCodeCells b) tail)) =
      projectionConfig 150
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

 /-- `run_state150_marked_payload_cell_append` states the corresponding theorem run form. -/
theorem run_state150_marked_payload_cell_append
    (b : Bool) (leftRev middle tail : List (Option Bool)) :
    Description.runConfig 4
        (projectionConfig 150 leftRev
          (List.append (projectionMarkedBoolCellCodeCells b) middle ++
            tail)) =
      projectionConfig 150
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

 /-- `run_state150_marked_payload` states the corresponding theorem run form. -/
theorem run_state150_marked_payload
    (w : Word Bool) (leftRev tail : List (Option Bool)) :
    Description.runConfig (4 * w.length)
        (projectionConfig 150 leftRev
          (List.append (projectionMarkedBoolPayloadCells w) tail)) =
      projectionConfig 150
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
            (projectionConfig 150 leftRev
              (projectionMarkedBoolPayloadCells (b :: rest) ++ tail))) = _
      rw [show projectionMarkedBoolPayloadCells (b :: rest) =
          List.append (projectionMarkedBoolCellCodeCells b)
            (projectionMarkedBoolPayloadCells rest) by
        rfl]
      rw [run_state150_marked_payload_cell_append]
      rw [ih]
      simp [List.reverse_append, List.append_assoc]

 /-- `run_state150_to_scan160` states the corresponding theorem run form. -/
theorem run_state150_to_scan160
    (leftRev tail : List (Option Bool)) :
    Description.runConfig 2
        (projectionConfig 150 leftRev
          (some false :: some false :: tail)) =
      projectionConfig 160 leftRev
        (some false :: some false :: tail) := by
  rfl

 /-- `run_state170_marked_tick` states the corresponding theorem run form. -/
theorem run_state170_marked_tick
    (leftRev tail : List (Option Bool)) :
    Description.runConfig 4
        (projectionConfig 170 leftRev
          (List.append projectionMarkedTickCodeCells tail)) =
      projectionConfig 170
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

 /-- `run_state170_marked_ticks` states the corresponding theorem run form. -/
theorem run_state170_marked_ticks
    (count : Nat) (leftRev tail : List (Option Bool)) :
    Description.runConfig (4 * count)
        (projectionConfig 170 leftRev
          (List.append
            (projectionRepeatedCells projectionMarkedTickCodeCells count)
            tail)) =
      projectionConfig 170
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
            (projectionConfig 170 leftRev
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
            (projectionConfig 170 leftRev
              (List.append projectionMarkedTickCodeCells
                (List.append
                  (projectionRepeatedCells projectionMarkedTickCodeCells count)
                  tail)))) = _
      rw [run_state170_marked_tick]
      rw [ih]
      rw [projectionRepeatedCells_reverse]
      rw [projectionRepeatedCells_reverse
        (chunk := projectionTickCodeCells) (n := count + 1)]
      rw [projectionRepeatedCells_succ_right]
      simp [List.append_assoc]

 /-- `run_state170_done` states the corresponding theorem run form. -/
theorem run_state170_done
    (leftRev tail : List (Option Bool)) :
    Description.runConfig 4
        (projectionConfig 170 leftRev
          (List.append projectionDoneCodeCells tail)) =
      projectionConfig 180
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

 /-- `run_state180_marked_payload_cell` states the corresponding theorem run form. -/
theorem run_state180_marked_payload_cell
    (b : Bool) (leftRev tail : List (Option Bool)) :
    Description.runConfig 4
        (projectionConfig 180 leftRev
          (List.append (projectionMarkedBoolCellCodeCells b) tail)) =
      projectionConfig 180
        (List.append (projectionBoolCellCodeCells b).reverse leftRev)
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

 /-- `run_state180_marked_payload_cell_append` states the corresponding theorem run form. -/
theorem run_state180_marked_payload_cell_append
    (b : Bool) (leftRev middle tail : List (Option Bool)) :
    Description.runConfig 4
        (projectionConfig 180 leftRev
          (List.append (projectionMarkedBoolCellCodeCells b) middle ++
            tail)) =
      projectionConfig 180
        (List.append (projectionBoolCellCodeCells b).reverse leftRev)
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

 /-- `run_state180_marked_payload` states the corresponding theorem run form. -/
theorem run_state180_marked_payload
    (w : Word Bool) (leftRev tail : List (Option Bool)) :
    Description.runConfig (4 * w.length)
        (projectionConfig 180 leftRev
          (List.append (projectionMarkedBoolPayloadCells w) tail)) =
      projectionConfig 180
        (List.append (projectionBoolPayloadCells w).reverse leftRev)
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
            (projectionConfig 180 leftRev
              (projectionMarkedBoolPayloadCells (b :: rest) ++ tail))) = _
      rw [show projectionMarkedBoolPayloadCells (b :: rest) =
          List.append (projectionMarkedBoolCellCodeCells b)
            (projectionMarkedBoolPayloadCells rest) by
        rfl]
      rw [run_state180_marked_payload_cell_append]
      rw [ih]
      simp [projectionBoolPayloadCells, List.reverse_append,
        List.append_assoc]

 /-- `run_state180_to_200` states the corresponding theorem run form. -/
theorem run_state180_to_200
    (leftRev tail : List (Option Bool)) :
    Description.runConfig 2
        (projectionConfig 180 leftRev
          (some false :: some false :: tail)) =
      projectionConfig 200 leftRev
        (some false :: some false :: tail) := by
  rfl

def projectionMarkedBoolCellScanPrefixRev (b : Bool) :
    List (Option Bool) :=
  match b with
  | false => [some false, none, some false]
  | true => [some true, none, some false]

def projectionMarkedBoolCellScanTailHead (b : Bool) :
    Option Bool :=
  match b with
  | false => some true
  | true => some false

 /-- `run_state130_mark_payload_cell` states the corresponding theorem run form. -/
theorem run_state130_mark_payload_cell
    (b : Bool) (leftRev tail : List (Option Bool)) :
    Description.runConfig 4
        (projectionConfig 130 leftRev
          (List.append (projectionBoolCellCodeCells b) tail)) =
      projectionConfig 140 (none :: some false :: leftRev)
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

def projectionInputMarkPreviousCells
    (marked rest : Word Bool) : List (Option Bool) :=
  List.append
    (projectionRepeatedCells projectionMarkedTickCodeCells
      (marked.length + 1))
    (List.append
      (projectionCodeCells (List.replicate rest.length
        MachineCodeSymbol.tick))
      (List.append projectionDoneCodeCells
        (projectionMarkedBoolPayloadCells marked)))

def projectionInputMarkScanBackCellsRev
    (marked rest : Word Bool) (b : Bool) : List (Option Bool) :=
  List.append (projectionMarkedBoolCellScanPrefixRev b)
    (projectionInputMarkPreviousCells marked rest).reverse

def projectionInputMarkScanTail
    (rest : Word Bool) (b : Bool) (suffix : Word MachineCodeSymbol) :
    List (Option Bool) :=
  projectionMarkedBoolCellScanTailHead b ::
    List.append (projectionBoolPayloadCells rest) (projectionCodeCells suffix)

 /-- `projectionMarkedBoolCellScanPrefixRev_scanSafe` characterizes a scan safety phase. -/
theorem projectionMarkedBoolCellScanPrefixRev_scanSafe
    (b : Bool) :
    projectionScanSafe 0 (projectionMarkedBoolCellScanPrefixRev b) := by
  cases b <;>
    simp [projectionMarkedBoolCellScanPrefixRev, projectionScanSafe,
      projectionScanCountStep]

 /-- `projectionMarkedBoolCellScanPrefixRev_scanCountFold` characterizes a scan safety phase. -/
theorem projectionMarkedBoolCellScanPrefixRev_scanCountFold
    (b : Bool) :
    projectionScanCountFold 0 (projectionMarkedBoolCellScanPrefixRev b) =
      0 := by
  cases b <;>
    simp [projectionMarkedBoolCellScanPrefixRev, projectionScanCountFold,
      projectionScanCountStep]

 /-- `projectionCodeCells_replicate_tick_length` tracks the relevant length or shape invariant. -/
theorem projectionCodeCells_replicate_tick_length
    (n : Nat) :
    (projectionCodeCells
      (List.replicate n MachineCodeSymbol.tick)).length = 4 * n := by
  rw [projectionCodeCells_replicate_tick, projectionRepeatedCells_length]
  simp [projectionTickCodeCells, MachineDescription.encodeCodeSymbolAsInput]

 /-- `projectionCodeCells_replicate_tick_scanCountFold_reverse` characterizes a scan safety phase. -/
theorem projectionCodeCells_replicate_tick_scanCountFold_reverse
    (n : Nat) :
    projectionScanCountFold 0
        (projectionCodeCells
          (List.replicate n MachineCodeSymbol.tick)).reverse = 0 := by
  rw [projectionCodeCells_replicate_tick, projectionRepeatedCells_reverse]
  exact
    projectionScanCountFold_repeated_zero projectionTickCodeCells.reverse
      projectionTickCodeCells_scanCountFold_reverse n

 /-- `projectionCodeCells_replicate_tick_scanSafe_reverse` characterizes a scan safety phase. -/
theorem projectionCodeCells_replicate_tick_scanSafe_reverse
    (n : Nat) :
    projectionScanSafe 0
        (projectionCodeCells
          (List.replicate n MachineCodeSymbol.tick)).reverse := by
  rw [projectionCodeCells_replicate_tick, projectionRepeatedCells_reverse]
  exact
    projectionScanSafe_repeated_zero projectionTickCodeCells.reverse
      projectionTickCodeCells_scanSafe_reverse
      projectionTickCodeCells_scanCountFold_reverse n

 /-- `projectionMarkedTickRepeated_scanCountFold_reverse` characterizes a scan safety phase. -/
theorem projectionMarkedTickRepeated_scanCountFold_reverse
    (count : Nat) :
    projectionScanCountFold 0
        (projectionRepeatedCells projectionMarkedTickCodeCells count).reverse =
      0 := by
  rw [projectionRepeatedCells_reverse]
  exact
    projectionScanCountFold_repeated_zero
      projectionMarkedTickCodeCells.reverse
      projectionMarkedTickCodeCells_scanCountFold_reverse count

 /-- `projectionMarkedTickRepeated_scanSafe_reverse` characterizes a scan safety phase. -/
theorem projectionMarkedTickRepeated_scanSafe_reverse
    (count : Nat) :
    projectionScanSafe 0
        (projectionRepeatedCells projectionMarkedTickCodeCells count).reverse := by
  rw [projectionRepeatedCells_reverse]
  exact
    projectionScanSafe_repeated_zero
      projectionMarkedTickCodeCells.reverse
      projectionMarkedTickCodeCells_scanSafe_reverse
      projectionMarkedTickCodeCells_scanCountFold_reverse count

 /-- `projectionInputMarkPreviousCells_scanCountFold_reverse` characterizes a scan safety phase. -/
theorem projectionInputMarkPreviousCells_scanCountFold_reverse
    (marked rest : Word Bool) :
    projectionScanCountFold 0
        (projectionInputMarkPreviousCells marked rest).reverse = 0 := by
  rw [show
      (projectionInputMarkPreviousCells marked rest).reverse =
        List.append (projectionMarkedBoolPayloadCells marked).reverse
          (List.append projectionDoneCodeCells.reverse
            (List.append
              (projectionCodeCells
                (List.replicate rest.length
                  MachineCodeSymbol.tick)).reverse
              (projectionRepeatedCells projectionMarkedTickCodeCells
                (marked.length + 1)).reverse)) by
    simp [projectionInputMarkPreviousCells, List.reverse_append,
      List.append_assoc]]
  rw [projectionScanCountFold_append,
    projectionMarkedBoolPayloadCells_scanCountFold_reverse,
    projectionScanCountFold_append,
    projectionDoneCodeCells_scanCountFold_reverse,
    projectionScanCountFold_append,
    projectionCodeCells_replicate_tick_scanCountFold_reverse,
    projectionMarkedTickRepeated_scanCountFold_reverse]

 /-- `projectionInputMarkPreviousCells_scanSafe_reverse` characterizes a scan safety phase. -/
theorem projectionInputMarkPreviousCells_scanSafe_reverse
    (marked rest : Word Bool) :
    projectionScanSafe 0
        (projectionInputMarkPreviousCells marked rest).reverse := by
  rw [show
      (projectionInputMarkPreviousCells marked rest).reverse =
        List.append (projectionMarkedBoolPayloadCells marked).reverse
          (List.append projectionDoneCodeCells.reverse
            (List.append
              (projectionCodeCells
                (List.replicate rest.length
                  MachineCodeSymbol.tick)).reverse
              (projectionRepeatedCells projectionMarkedTickCodeCells
                (marked.length + 1)).reverse)) by
    simp [projectionInputMarkPreviousCells, List.reverse_append,
      List.append_assoc]]
  apply projectionScanSafe_append
  · exact projectionMarkedBoolPayloadCells_scanSafe_reverse marked
  · rw [projectionMarkedBoolPayloadCells_scanCountFold_reverse]
    apply projectionScanSafe_append
    · exact projectionDoneCodeCells_scanSafe_reverse
    · rw [projectionDoneCodeCells_scanCountFold_reverse]
      apply projectionScanSafe_append
      · exact projectionCodeCells_replicate_tick_scanSafe_reverse rest.length
      · rw [projectionCodeCells_replicate_tick_scanCountFold_reverse]
        exact
          projectionMarkedTickRepeated_scanSafe_reverse (marked.length + 1)

 /-- `projectionInputMarkScanBackCellsRev_scanCountFold` characterizes a scan safety phase. -/
theorem projectionInputMarkScanBackCellsRev_scanCountFold
    (marked rest : Word Bool) (b : Bool) :
    projectionScanCountFold 0
        (projectionInputMarkScanBackCellsRev marked rest b) = 0 := by
  unfold projectionInputMarkScanBackCellsRev
  rw [projectionScanCountFold_append,
    projectionMarkedBoolCellScanPrefixRev_scanCountFold,
    projectionInputMarkPreviousCells_scanCountFold_reverse]

 /-- `projectionInputMarkScanBackCellsRev_scanSafe` characterizes a scan safety phase. -/
theorem projectionInputMarkScanBackCellsRev_scanSafe
    (marked rest : Word Bool) (b : Bool) :
    projectionScanSafe 0
        (projectionInputMarkScanBackCellsRev marked rest b) := by
  unfold projectionInputMarkScanBackCellsRev
  apply projectionScanSafe_append
  · exact projectionMarkedBoolCellScanPrefixRev_scanSafe b
  · rw [projectionMarkedBoolCellScanPrefixRev_scanCountFold]
    exact projectionInputMarkPreviousCells_scanSafe_reverse marked rest

 /-- `projectionInputMarkScanBackCellsRev_length` characterizes a scan safety phase. -/
theorem projectionInputMarkScanBackCellsRev_length
    (marked rest : Word Bool) (b : Bool) :
    (projectionInputMarkScanBackCellsRev marked rest b).length =
      8 * marked.length + 4 * rest.length + 11 := by
  cases b <;>
    simp [projectionInputMarkScanBackCellsRev,
      projectionMarkedBoolCellScanPrefixRev, projectionInputMarkPreviousCells,
      projectionRepeatedCells_length,
      projectionCodeCells_replicate_tick_length,
      projectionMarkedBoolPayloadCells_length,
      projectionMarkedTickCodeCells, projectionDoneCodeCells,
      MachineDescription.encodeCodeSymbolAsInput] <;>
    omega

def projectionInputFinishScanBackCellsRev
    (marked : Word Bool) : List (Option Bool) :=
  some false ::
    List.append (projectionMarkedBoolPayloadCells marked).reverse
      (List.append projectionDoneCodeCells.reverse
        (projectionRepeatedCells projectionMarkedTickCodeCells
          marked.length).reverse)

 /-- `projectionInputFinishScanBackCellsRev_scanCountFold` characterizes a scan safety phase. -/
theorem projectionInputFinishScanBackCellsRev_scanCountFold
    (marked : Word Bool) :
    projectionScanCountFold 0
        (projectionInputFinishScanBackCellsRev marked) = 0 := by
  unfold projectionInputFinishScanBackCellsRev
  simp [projectionScanCountFold, projectionScanCountStep]
  change
    projectionScanCountFold 0
        (List.append (projectionMarkedBoolPayloadCells marked).reverse
          (List.append projectionDoneCodeCells.reverse
            (projectionRepeatedCells projectionMarkedTickCodeCells
              marked.length).reverse)) = 0
  rw [projectionScanCountFold_append,
    projectionMarkedBoolPayloadCells_scanCountFold_reverse,
    projectionScanCountFold_append,
    projectionDoneCodeCells_scanCountFold_reverse,
    projectionMarkedTickRepeated_scanCountFold_reverse]

 /-- `projectionInputFinishScanBackCellsRev_scanSafe` characterizes a scan safety phase. -/
theorem projectionInputFinishScanBackCellsRev_scanSafe
    (marked : Word Bool) :
    projectionScanSafe 0
        (projectionInputFinishScanBackCellsRev marked) := by
  unfold projectionInputFinishScanBackCellsRev
  simp [projectionScanSafe, projectionScanCountStep]
  apply projectionScanSafe_append
  · exact projectionMarkedBoolPayloadCells_scanSafe_reverse marked
  · rw [projectionMarkedBoolPayloadCells_scanCountFold_reverse]
    apply projectionScanSafe_append
    · exact projectionDoneCodeCells_scanSafe_reverse
    · rw [projectionDoneCodeCells_scanCountFold_reverse]
      exact projectionMarkedTickRepeated_scanSafe_reverse marked.length

 /-- `projectionInputFinishScanBackCellsRev_length` characterizes a scan safety phase. -/
theorem projectionInputFinishScanBackCellsRev_length
    (marked : Word Bool) :
    (projectionInputFinishScanBackCellsRev marked).length =
      8 * marked.length + 5 := by
  simp [projectionInputFinishScanBackCellsRev,
    projectionMarkedBoolPayloadCells_length,
    projectionRepeatedCells_length, projectionMarkedTickCodeCells,
    projectionDoneCodeCells, MachineDescription.encodeCodeSymbolAsInput]
  omega

def projectionInputFinishSuffixTail
    (stage : Nat) (result : Word Bool) : List (Option Bool) :=
  match stage with
  | 0 =>
      [some true, some true] ++
        projectionCodeCells (MachineDescription.encodeBoolWord result)
  | n + 1 =>
      [some true, some false] ++
        projectionCodeCells
          (MachineDescription.encodeNatAppend n
            (MachineDescription.encodeBoolWord result))

 /-- `projectionCodeCells_encodeNatAppend_cons_cons` captures the core lemma for this local construction. -/
theorem projectionCodeCells_encodeNatAppend_cons_cons
    (stage : Nat) (result : Word Bool) :
    projectionCodeCells
        (MachineDescription.encodeNatAppend stage
          (MachineDescription.encodeBoolWord result)) =
      some false :: some false ::
        projectionInputFinishSuffixTail stage result := by
  cases stage <;> rfl

def projectionInputFinishSuffixTailFor
    (stage : Nat) (suffix : Word MachineCodeSymbol) : List (Option Bool) :=
  match stage with
  | 0 =>
      [some true, some true] ++ projectionCodeCells suffix
  | n + 1 =>
      [some true, some false] ++
        projectionCodeCells (MachineDescription.encodeNatAppend n suffix)

 /-- `projectionCodeCells_encodeNatAppend_cons_cons_suffix` captures the core lemma for this local construction. -/
theorem projectionCodeCells_encodeNatAppend_cons_cons_suffix
    (stage : Nat) (suffix : Word MachineCodeSymbol) :
    projectionCodeCells (MachineDescription.encodeNatAppend stage suffix) =
      some false :: some false ::
        projectionInputFinishSuffixTailFor stage suffix := by
  cases stage <;> rfl

end ControllerStageInputProjection
end Computability
end FoC
