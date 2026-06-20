import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailStagePrefix

set_option doc.verso true

/-!
# Dovetail-layout scanner components

This module contains concrete field scanners for the complete
{name (full := FoC.Computability.MachineDescription.DovetailLayout)}`MachineDescription.DovetailLayout`
recognizer.  The first reusable component is a suffix-aware scanner for
length-prefixed cell lists.  It is adapted from the marked stage-input scanner:
the length prefix is marked one tick at a time, each payload cell is checked and
temporarily marked, and the finish pass restores the payload before halting just
to the left of the next field.
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace CanonicalLayouts
namespace DovetailLayoutScanner

open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

/-!
## Suffix-aware cell-list scanner

The scanner starts with the head on the first bit of an encoded
{name (full := FoC.Computability.MachineDescription.encodeCellListAppend)}`MachineDescription.encodeCellListAppend`
field.  It accepts arbitrary cell payloads
({lit}`blank`, {lit}`zero`, and {lit}`one`) and halts one cell to the left of the first bit of
the nonempty suffix.  Downstream sequencing uses a right handoff move to place
the next scanner on that suffix bit.
-/

def CellListSuffixScannerDescription : MachineDescription where
  stateCount := 1000
  start := 100
  halt := 999
  transitions :=
    [ keep 100 false 101
    , keep 101 false 102
    , keep 102 true 103
    , writeMove 103 (some false) none Direction.right 120
    , keep 103 true 150
    , keepMove 103 none Direction.right 100

    , keep 120 false 121
    , keep 121 false 122
    , keep 122 true 123
    , keep 123 false 120
    , keep 123 true 130
    , keepMove 123 none Direction.right 120

    , keep 130 false 131
    , keepMove 130 (some true) Direction.right 135
    , keepMove 131 (some true) Direction.left 132
    , writeMove 132 (some false) (some true) Direction.right 133
    , keep 133 true 134
    , keep 134 false 139
    , keep 134 true 145
    , keepMove 139 (some false) Direction.left 140
    , keepMove 139 (some true) Direction.left 140
    , keepMove 145 (some false) Direction.left 140
    , keep 135 true 136
    , keep 136 false 137
    , keep 136 true 138
    , keep 137 false 130
    , keep 137 true 130
    , keep 138 false 130

    , writeMove 150 (some true) (some false) Direction.right 152
    , keepMove 150 (some false) Direction.left 999
    , keep 152 true 153
    , keep 153 false 154
    , keep 153 true 155
    , keep 154 false 150
    , keep 154 true 150
    , keep 155 false 150
    ]
      ++ scanLeftToSentinelRestart 140 141 142

theorem cellListSuffixScannerDescription_wellFormed :
    CellListSuffixScannerDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · intro t ht
    exact transition_wellFormed_of_all
      (l := CellListSuffixScannerDescription.transitions)
      (stateCount := CellListSuffixScannerDescription.stateCount)
      (by
        native_decide) t ht
  · intro t u ht hu hkey
    exact transition_deterministic_of_all
      (l := CellListSuffixScannerDescription.transitions)
      (by
        native_decide) t u ht hu hkey

theorem cellListSuffixScannerDescription_haltTransitionFree :
    CellListSuffixScannerDescription.HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l := CellListSuffixScannerDescription.transitions)
    (state := CellListSuffixScannerDescription.halt)
    (by
      native_decide) t ht

theorem cellListSuffixScannerDescription_subroutineReady :
    CellListSuffixScannerDescription.SubroutineReady :=
  ⟨cellListSuffixScannerDescription_wellFormed,
    cellListSuffixScannerDescription_haltTransitionFree⟩

theorem cellListSuffix_lookup_150_false :
    CellListSuffixScannerDescription.lookupTransition 150 (some false) =
      some (keepMove 150 (some false) Direction.left
        CellListSuffixScannerDescription.halt) := by
  native_decide

def cellCodeBits (cell : Option Bool) : Word Bool :=
  MachineDescription.encodeCodeWordAsInput
    (MachineDescription.encodeCell cell)

def markedCellCodeBits : Option Bool -> Word Bool
  | none => [true, true, false, false]
  | some false => [true, true, false, true]
  | some true => [true, true, true, false]

def cellCodeTailCells : Option Bool -> List (Option Bool)
  | none => [some false, some false]
  | some false => [some false, some true]
  | some true => [some true, some false]

def cellsCodeBits : List (Option Bool) -> Word Bool
  | [] => []
  | cell :: rest =>
      List.append (cellCodeBits cell) (cellsCodeBits rest)

def markedCellsCodeBits : List (Option Bool) -> Word Bool
  | [] => []
  | cell :: rest =>
      List.append (markedCellCodeBits cell) (markedCellsCodeBits rest)

@[simp] theorem cellsCodeBits_append
    (left right : List (Option Bool)) :
    cellsCodeBits (List.append left right) =
      List.append (cellsCodeBits left) (cellsCodeBits right) := by
  induction left with
  | nil =>
      rfl
  | cons cell rest ih =>
      change
        List.append (cellCodeBits cell)
            (cellsCodeBits (List.append rest right)) =
          List.append
            (List.append (cellCodeBits cell) (cellsCodeBits rest))
            (cellsCodeBits right)
      rw [ih]
      simp [List.append_assoc]

@[simp] theorem markedCellsCodeBits_append
    (left right : List (Option Bool)) :
    markedCellsCodeBits (List.append left right) =
      List.append (markedCellsCodeBits left)
        (markedCellsCodeBits right) := by
  induction left with
  | nil =>
      rfl
  | cons cell rest ih =>
      change
        List.append (markedCellCodeBits cell)
            (markedCellsCodeBits (List.append rest right)) =
          List.append
            (List.append (markedCellCodeBits cell)
              (markedCellsCodeBits rest))
            (markedCellsCodeBits right)
      rw [ih]
      simp [List.append_assoc]

@[simp] theorem markedCellsCodeBits_append_single
    (cells : List (Option Bool)) (cell : Option Bool) :
    markedCellsCodeBits (List.append cells [cell]) =
      List.append (markedCellsCodeBits cells)
        (markedCellCodeBits cell) := by
  simpa [markedCellsCodeBits] using
    markedCellsCodeBits_append cells [cell]

theorem map_some_append (left right : Word Bool) :
    List.map some (List.append left right) =
      List.append (List.map some left) (List.map some right) := by
  induction left with
  | nil =>
      rfl
  | cons b rest ih =>
      simp

@[simp] theorem map_markedCellsCodeBits_append_single
    (cells : List (Option Bool)) (cell : Option Bool) :
    List.map some (markedCellsCodeBits (List.append cells [cell])) =
      List.append (List.map some (markedCellsCodeBits cells))
        (List.map some (markedCellCodeBits cell)) := by
  rw [markedCellsCodeBits_append_single]
  exact map_some_append (markedCellsCodeBits cells)
    (markedCellCodeBits cell)

theorem cellCodeBits_eq
    (cell : Option Bool) :
    cellCodeBits cell =
      MachineDescription.encodeCodeWordAsInput
        (MachineDescription.encodeCell cell) := rfl

theorem run_cellList_state130_currentCell
    (cell : Option Bool) (left right : List (Option Bool)) :
    CellListSuffixScannerDescription.runConfig 6
        (config 130 left
          (List.append ((cellCodeBits cell).map some) right)) =
      config 140 (some true :: some true :: left)
        (List.append (cellCodeTailCells cell) right) := by
  cases cell with
  | none =>
      cases right <;>
        simp [CellListSuffixScannerDescription, cellCodeBits,
          cellCodeTailCells, config, tapeAtCells, keep, keepMove,
          writeMove, scanLeftToSentinelRestart,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition,
          MachineDescription.encodeCell,
          MachineDescription.encodeCodeWordAsInput,
          MachineDescription.encodeCodeSymbolAsInput,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight]
  | some b =>
      cases b <;> cases right <;>
        simp [CellListSuffixScannerDescription, cellCodeBits,
          cellCodeTailCells, config, tapeAtCells, keep, keepMove,
          writeMove, scanLeftToSentinelRestart,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition,
          MachineDescription.encodeCell,
          MachineDescription.encodeCodeWordAsInput,
          MachineDescription.encodeCodeSymbolAsInput,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight]

theorem run_cellList_state100_tick
    (left tail : List (Option Bool)) :
    CellListSuffixScannerDescription.runConfig 4
        (config 100 left
          (List.append (tickBits.map some) tail)) =
      config 120 (List.append markedTickRev left) tail := by
  cases tail with
  | nil =>
      rfl
  | cons cell rest =>
      cases cell with
      | none =>
          rfl
      | some b =>
          cases b <;> rfl

theorem run_cellList_state100_done
    (left tail : List (Option Bool)) :
    CellListSuffixScannerDescription.runConfig 4
        (config 100 left
          (List.append (doneBits.map some) tail)) =
      config 150
        (List.append (doneBits.reverse.map some) left) tail := by
  cases tail with
  | nil =>
      rfl
  | cons cell rest =>
      cases cell with
      | none =>
          rfl
      | some b =>
          cases b <;> rfl

theorem run_cellList_state120_tick
    (left right : List (Option Bool)) :
    CellListSuffixScannerDescription.runConfig 4
        (config 120 left
          (List.append (tickBits.map some) right)) =
      config 120
        (List.append (tickBits.reverse.map some) left) right := by
  cases right <;>
  simp [CellListSuffixScannerDescription, tickBits,
    config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition,
    MachineDescription.encodeCodeSymbolAsInput,
    Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem run_cellList_state120_done
    (left right : List (Option Bool)) :
    CellListSuffixScannerDescription.runConfig 4
        (config 120 left
          (List.append (doneBits.map some) right)) =
      config 130
        (List.append (doneBits.reverse.map some) left) right := by
  cases right <;>
  simp [CellListSuffixScannerDescription, doneBits,
    config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition,
    MachineDescription.encodeCodeSymbolAsInput,
    Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem run_cellList_state120_stageNat
    (n : Nat) (left right : List (Option Bool)) :
    CellListSuffixScannerDescription.runConfig (4 * n + 4)
        (config 120 left
          (List.append ((stageNatBits n).map some) right)) =
      config 130
        (List.append ((stageNatBits n).reverse.map some) left)
        right := by
  induction n generalizing left with
  | zero =>
      simpa [stageNatBits_zero] using
        run_cellList_state120_done left right
  | succ n ih =>
      rw [show 4 * (n + 1) + 4 =
          4 + (4 * n + 4) by omega]
      rw [MachineDescription.runConfig_add]
      rw [show
          List.append ((stageNatBits (n + 1)).map some) right =
            List.append (tickBits.map some)
              (List.append ((stageNatBits n).map some) right) by
          simp [stageNatBits_succ, tickBits,
            MachineDescription.encodeCodeSymbolAsInput]]
      rw [run_cellList_state120_tick]
      rw [ih]
      simp [stageNatBits_succ, tickBits,
        MachineDescription.encodeCodeSymbolAsInput,
        List.map_append, List.append_assoc]

theorem run_cellList_state130_markedCell
    (cell : Option Bool) (left right : List (Option Bool)) :
    CellListSuffixScannerDescription.runConfig 4
        (config 130 left
          (List.append ((markedCellCodeBits cell).map some) right)) =
      config 130
        (List.append ((markedCellCodeBits cell).reverse.map some) left)
        right := by
  cases cell with
  | none =>
      cases right <;>
        simp [CellListSuffixScannerDescription, markedCellCodeBits,
          config, tapeAtCells, keep, keepMove, writeMove,
          scanLeftToSentinelRestart,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition,
          Tape.read, Tape.write, Tape.move, Tape.moveRight]
  | some b =>
      cases b <;> cases right <;>
        simp [CellListSuffixScannerDescription, markedCellCodeBits,
          config, tapeAtCells, keep, keepMove, writeMove,
          scanLeftToSentinelRestart,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition,
          Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem run_cellList_state130_markedCells
    (processed : List (Option Bool))
    (left right : List (Option Bool)) :
    CellListSuffixScannerDescription.runConfig
        (4 * processed.length)
        (config 130 left
          (List.append ((markedCellsCodeBits processed).map some)
            right)) =
      config 130
        (List.append ((markedCellsCodeBits processed).reverse.map some)
          left)
        right := by
  induction processed generalizing left with
  | nil =>
      rfl
  | cons cell rest ih =>
      rw [show 4 * (cell :: rest).length =
          4 + 4 * rest.length by simp; omega]
      rw [MachineDescription.runConfig_add]
      rw [show
          List.append ((markedCellsCodeBits (cell :: rest)).map some)
              right =
            List.append ((markedCellCodeBits cell).map some)
              (List.append ((markedCellsCodeBits rest).map some)
                right) by
          simp [markedCellsCodeBits, List.map_append, List.append_assoc]]
      rw [run_cellList_state130_markedCell]
      rw [ih]
      simp [markedCellsCodeBits, List.reverse_append, List.map_append,
        List.append_assoc]

theorem run_cellList_state140_returnToLengthMarker
    (scanRev : Word Bool) (headBit : Bool)
    (leftTail right : List (Option Bool)) :
    CellListSuffixScannerDescription.runConfig
        (scanRev.length + 4)
        (config 140
          (List.append (scanRev.map some)
            (none :: some true :: leftTail))
          (some headBit :: right)) =
      config 100 (some false :: some true :: leftTail)
        (List.append (scanRev.reverse.map some)
          (some headBit :: right)) := by
  induction scanRev generalizing headBit right with
  | nil =>
      cases headBit <;> cases right <;>
        simp [CellListSuffixScannerDescription, config, tapeAtCells,
          keep, keepMove, writeMove, scanLeftToSentinelRestart,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight]
  | cons b rest ih =>
      rw [show (b :: rest).length + 4 =
          1 + (rest.length + 4) by
        simp
        omega]
      rw [MachineDescription.runConfig_add]
      change
        CellListSuffixScannerDescription.runConfig (rest.length + 4)
          (CellListSuffixScannerDescription.runConfig 1
            (config 140
              (some b :: List.append (List.map some rest)
                (none :: some true :: leftTail))
              (some headBit :: right))) =
          config 100 (some false :: some true :: leftTail)
            (List.append (List.map some (b :: rest).reverse)
              (some headBit :: right))
      rw [show
          CellListSuffixScannerDescription.runConfig 1
            (config 140
              (some b :: List.append (List.map some rest)
                (none :: some true :: leftTail))
              (some headBit :: right)) =
          config 140
            (List.append (List.map some rest)
              (none :: some true :: leftTail))
            (some b :: some headBit :: right) by
        cases headBit <;> cases b <;> cases right <;>
        simp [CellListSuffixScannerDescription,
          config, tapeAtCells, keep, keepMove, writeMove,
          scanLeftToSentinelRestart,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft]]
      rw [ih]
      simp [List.map_append, List.append_assoc]

theorem run_cellList_state150_markedCell
    (cell : Option Bool) (left right : List (Option Bool)) :
    CellListSuffixScannerDescription.runConfig 4
        (config 150 left
          (List.append ((markedCellCodeBits cell).map some) right)) =
      config 150
        (List.append ((cellCodeBits cell).reverse.map some) left)
        right := by
  cases cell with
  | none =>
      cases right <;>
        simp [CellListSuffixScannerDescription, markedCellCodeBits,
          cellCodeBits, config, tapeAtCells, keep, keepMove, writeMove,
          scanLeftToSentinelRestart,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, MachineDescription.encodeCell,
          MachineDescription.encodeCodeWordAsInput,
          MachineDescription.encodeCodeSymbolAsInput,
          Tape.read, Tape.write, Tape.move, Tape.moveRight]
  | some b =>
      cases b <;> cases right <;>
        simp [CellListSuffixScannerDescription, markedCellCodeBits,
          cellCodeBits, config, tapeAtCells, keep, keepMove, writeMove,
          scanLeftToSentinelRestart,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, MachineDescription.encodeCell,
          MachineDescription.encodeCodeWordAsInput,
          MachineDescription.encodeCodeSymbolAsInput,
          Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem run_cellList_state150_markedCells
    (cells : List (Option Bool))
    (left right : List (Option Bool)) :
    CellListSuffixScannerDescription.runConfig
        (4 * cells.length)
        (config 150 left
          (List.append ((markedCellsCodeBits cells).map some)
            right)) =
      config 150
        (List.append ((cellsCodeBits cells).reverse.map some)
          left)
        right := by
  induction cells generalizing left with
  | nil =>
      rfl
  | cons cell rest ih =>
      rw [show 4 * (cell :: rest).length =
          4 + 4 * rest.length by simp; omega]
      rw [MachineDescription.runConfig_add]
      rw [show
          List.append ((markedCellsCodeBits (cell :: rest)).map some)
              right =
            List.append ((markedCellCodeBits cell).map some)
              (List.append ((markedCellsCodeBits rest).map some)
                right) by
          simp [markedCellsCodeBits, List.map_append, List.append_assoc]]
      rw [run_cellList_state150_markedCell]
      rw [ih]
      simp [cellsCodeBits, List.reverse_append, List.map_append,
        List.append_assoc]

def cellListFinishStartLeft : List (Option Bool) -> List (Option Bool)
  | [] => doneBits.reverse.map some
  | _ :: rest =>
      List.append (doneBits.reverse.map some)
        (finishLengthPrefixRev rest.length)

def cellListFinishStartConfig
    (cells : List (Option Bool)) (suffixBits : Word Bool) :
    MachineDescription.Configuration :=
  config 150 (cellListFinishStartLeft cells)
    (List.append ((markedCellsCodeBits cells).map some)
      (suffixBits.map some))

def cellListRestoredLeft
    (cells : List (Option Bool)) : List (Option Bool) :=
  List.append ((cellsCodeBits cells).reverse.map some)
    (cellListFinishStartLeft cells)

def cellListHandoffConfig
    (cells : List (Option Bool)) (suffixBits : Word Bool) :
    MachineDescription.Configuration :=
  { state := CellListSuffixScannerDescription.halt
    tape :=
      Tape.move Direction.left
        (tapeAtCells (cellListRestoredLeft cells)
          (suffixBits.map some)) }

def cellListMarkingState120
    (processed : List (Option Bool)) (cell : Option Bool)
    (rest : List (Option Bool)) (suffixBits : Word Bool) :
    MachineDescription.Configuration :=
  config 120 (activeLengthPrefixRev processed.length)
    (List.append ((stageNatBits rest.length).map some)
      (List.append ((markedCellsCodeBits processed).map some)
        (List.append ((cellCodeBits cell).map some)
          (List.append ((cellsCodeBits rest).map some)
            (suffixBits.map some)))))

def cellListState100AfterMarked
    (processed : List (Option Bool)) (cell : Option Bool)
    (rest : List (Option Bool)) (suffixBits : Word Bool) :
    MachineDescription.Configuration :=
  config 100 (finishLengthPrefixRev processed.length)
    (List.append ((stageNatBits rest.length).map some)
      (List.append ((markedCellsCodeBits processed).map some)
        (List.append ((markedCellCodeBits cell).map some)
          (List.append ((cellsCodeBits rest).map some)
            (suffixBits.map some)))))

def cellListMarkingReturnScanRev
    (processed rest : List (Option Bool)) : Word Bool :=
  List.append [true, true]
    (List.append (markedCellsCodeBits processed).reverse
      (stageNatBits rest.length).reverse)

theorem run_cellList_mark_current_to_state100
    (processed : List (Option Bool)) (cell : Option Bool)
    (rest : List (Option Bool)) (suffixBits : Word Bool) :
    exists steps : Nat,
      CellListSuffixScannerDescription.runConfig steps
          (cellListMarkingState120 processed cell rest suffixBits) =
        cellListState100AfterMarked processed cell rest suffixBits := by
  let scanRev := cellListMarkingReturnScanRev processed rest
  refine
    ⟨(4 * rest.length + 4) +
        (4 * processed.length + (6 + (scanRev.length + 4))), ?_⟩
  rw [MachineDescription.runConfig_add]
  unfold cellListMarkingState120
  rw [run_cellList_state120_stageNat]
  rw [MachineDescription.runConfig_add]
  rw [run_cellList_state130_markedCells]
  rw [MachineDescription.runConfig_add]
  rw [run_cellList_state130_currentCell]
  cases cell with
  | none =>
      have hreturn :=
        run_cellList_state140_returnToLengthMarker scanRev false
          (activeLengthPrefixTail processed.length)
          (some false ::
            List.append ((cellsCodeBits rest).map some)
              (suffixBits.map some))
      simpa [cellListState100AfterMarked, scanRev,
        cellListMarkingReturnScanRev, activeLengthPrefixRev,
        activeLengthPrefixRestored, markedCellCodeBits,
        cellCodeTailCells, List.map_append, List.reverse_append,
        List.append_assoc] using hreturn
  | some b =>
      cases b
      · have hreturn :=
          run_cellList_state140_returnToLengthMarker scanRev false
            (activeLengthPrefixTail processed.length)
            (some true ::
              List.append ((cellsCodeBits rest).map some)
                (suffixBits.map some))
        simpa [cellListState100AfterMarked, scanRev,
          cellListMarkingReturnScanRev, activeLengthPrefixRev,
          activeLengthPrefixRestored, markedCellCodeBits,
          cellCodeTailCells, List.map_append, List.reverse_append,
          List.append_assoc] using hreturn
      · have hreturn :=
          run_cellList_state140_returnToLengthMarker scanRev true
            (activeLengthPrefixTail processed.length)
            (some false ::
              List.append ((cellsCodeBits rest).map some)
                (suffixBits.map some))
        simpa [cellListState100AfterMarked, scanRev,
          cellListMarkingReturnScanRev, activeLengthPrefixRev,
          activeLengthPrefixRestored, markedCellCodeBits,
          cellCodeTailCells, List.map_append, List.reverse_append,
          List.append_assoc] using hreturn

theorem run_cellList_marking_loop_from_state120
    (processed : List (Option Bool)) (cell : Option Bool)
    (rest : List (Option Bool)) (suffixBits : Word Bool) :
    exists steps : Nat,
      CellListSuffixScannerDescription.runConfig steps
          (cellListMarkingState120 processed cell rest suffixBits) =
        cellListFinishStartConfig
          (List.append processed (cell :: rest)) suffixBits := by
  induction rest generalizing processed cell with
  | nil =>
      rcases run_cellList_mark_current_to_state100
          processed cell [] suffixBits with
        ⟨markSteps, hmark⟩
      refine ⟨markSteps + 4, ?_⟩
      rw [MachineDescription.runConfig_add]
      rw [hmark]
      unfold cellListState100AfterMarked
      change
        CellListSuffixScannerDescription.runConfig 4
            (config 100 (finishLengthPrefixRev processed.length)
              (List.append (doneBits.map some)
                (List.append ((markedCellsCodeBits processed).map some)
                  (List.append ((markedCellCodeBits cell).map some)
                    (suffixBits.map some))))) =
          cellListFinishStartConfig (List.append processed [cell])
            suffixBits
      rw [run_cellList_state100_done]
      unfold cellListFinishStartConfig cellListFinishStartLeft
      cases processed with
      | nil =>
          simp [markedCellsCodeBits]
      | cons first processedTail =>
          rw [map_markedCellsCodeBits_append_single
            (first :: processedTail) cell]
          simp [markedCellsCodeBits, List.length_append,
            List.map_append, List.append_assoc]
  | cons next rest ih =>
      rcases run_cellList_mark_current_to_state100 processed cell
          (next :: rest) suffixBits with
        ⟨markSteps, hmark⟩
      rcases ih (List.append processed [cell]) next with
        ⟨recSteps, hrec⟩
      refine ⟨markSteps + 4 + recSteps, ?_⟩
      rw [show markSteps + 4 + recSteps =
          markSteps + (4 + recSteps) by omega]
      rw [MachineDescription.runConfig_add]
      rw [hmark]
      rw [MachineDescription.runConfig_add]
      unfold cellListState100AfterMarked
      rw [show
          (stageNatBits (next :: rest).length).map some =
            List.append (tickBits.map some)
              ((stageNatBits rest.length).map some) by
        simp [stageNatBits_succ, tickBits,
          MachineDescription.encodeCodeSymbolAsInput]]
      change
        CellListSuffixScannerDescription.runConfig recSteps
            (CellListSuffixScannerDescription.runConfig 4
              (config 100 (finishLengthPrefixRev processed.length)
                (List.append (tickBits.map some)
                  (List.append ((stageNatBits rest.length).map some)
                    (List.append ((markedCellsCodeBits processed).map some)
                      (List.append ((markedCellCodeBits cell).map some)
                        (List.append
                          ((cellsCodeBits (next :: rest)).map some)
                          (suffixBits.map some)))))))) =
          cellListFinishStartConfig
            (List.append processed (cell :: next :: rest)) suffixBits
      rw [run_cellList_state100_tick]
      unfold cellListMarkingState120 at hrec
      rw [map_markedCellsCodeBits_append_single processed cell] at hrec
      simpa [activeLengthPrefixRev_succ, markedCellsCodeBits,
        markedCellsCodeBits_append,
        cellsCodeBits, List.length_append, List.map_append,
        List.append_assoc] using hrec

theorem run_cellList_state150_handoff_false
    (cell : Option Bool) (left right : List (Option Bool)) :
    CellListSuffixScannerDescription.runConfig 1
        (config 150 (cell :: left) (some false :: right)) =
      config CellListSuffixScannerDescription.halt left
        (cell :: some false :: right) := by
  cases cell <;> cases right <;>
    simp [config, tapeAtCells, keepMove,
      cellListSuffix_lookup_150_false,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.transition,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem run_cellList_finish_to_handoff
    (cells : List (Option Bool)) (suffixTail : Word Bool) :
    exists steps : Nat,
      CellListSuffixScannerDescription.runConfig steps
          (cellListFinishStartConfig cells (false :: suffixTail)) =
        cellListHandoffConfig cells (false :: suffixTail) := by
  refine ⟨4 * cells.length + 1, ?_⟩
  rw [MachineDescription.runConfig_add]
  unfold cellListFinishStartConfig
  rw [run_cellList_state150_markedCells]
  change
    CellListSuffixScannerDescription.runConfig 1
      (config 150 (cellListRestoredLeft cells)
        (some false :: suffixTail.map some)) =
      cellListHandoffConfig cells (false :: suffixTail)
  unfold cellListHandoffConfig
  cases hleft : cellListRestoredLeft cells with
  | nil =>
      simp [config, tapeAtCells,
        cellListSuffix_lookup_150_false, keepMove,
        MachineDescription.runConfig, MachineDescription.stepConfig,
        MachineDescription.transition, Tape.read, Tape.write,
        Tape.move, Tape.moveLeft]
  | cons cell left =>
      simpa [config, tapeAtCells, hleft] using
        run_cellList_state150_handoff_false cell left
          (suffixTail.map some)

end DovetailLayoutScanner
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC
