import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.PrimitiveClosed

set_option doc.verso true

/-!
# Cell-list closed scanner inversions

This module contains code-origin closed inversions for the counted cell-list
scanner.  The same scanner is the first reusable component behind tape and
configuration field validation.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace CanonicalLayouts
namespace DovetailLayoutScanner

open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

private abbrev CLSS := CellListSuffixScannerDescription
private theorem CLSS_htf : CLSS.HaltTransitionFree :=
  cellListSuffixScannerDescription_haltTransitionFree

theorem runConfig_state_ne_halt_of_reaches_ne_halt_region
    {D : MachineDescription}
    {c mid : Configuration} {k n : Nat}
    (hD : D.HaltTransitionFree)
    (hrun : D.runConfig k c = mid)
    (hmid : forall m : Nat, (D.runConfig m mid).state ≠ D.halt) :
    (D.runConfig n c).state ≠ D.halt :=
  CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_ne_halt_region
    hD hrun hmid

theorem cellListSuffixScannerDescription_runConfig_state120_decodeNat_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : decodeNat tokens = none) (n : Nat) :
    (CLSS.runConfig n
      (config 120 leftRev
        ((encodeCodeWordAsInput tokens).map some))).state ≠
      CLSS.halt := by
  induction tokens generalizing leftRev n with
  | nil =>
      exact
        primitive_runConfig_state_ne_halt_of_reaches_stuck
          CLSS_htf
          (D := CLSS)
          (c :=
            config 120 leftRev
              ((encodeCodeWordAsInput
                ([] : Word MachineCodeSymbol)).map some))
          (stuck :=
            config 120 leftRev
              ((encodeCodeWordAsInput
                ([] : Word MachineCodeSymbol)).map some))
          (k := 0) (n := n)
          rfl
          (by rfl)
          (by
            change (120 : Nat) ≠ 999
            omega)
  | cons symbol rest ih =>
      cases symbol with
      | header =>
          exact
            primitive_runConfig_state_ne_halt_of_reaches_stuck
              CLSS_htf
              (D := CLSS)
              (c :=
                config 120 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.header :: rest)).map some))
              (stuck :=
                CLSS.runConfig 2
                  (config 120 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.header :: rest)).map some)))
              (k := 2) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CellListSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (122 : Nat) ≠ 999
                omega)
      | transition =>
          exact
            primitive_runConfig_state_ne_halt_of_reaches_stuck
              CLSS_htf
              (D := CLSS)
              (c :=
                config 120 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.transition :: rest)).map some))
              (stuck :=
                CLSS.runConfig 2
                  (config 120 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.transition :: rest)).map some)))
              (k := 2) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CellListSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (122 : Nat) ≠ 999
                omega)
      | tick =>
          simp [decodeNat] at hdecode
          cases hrest : decodeNat rest with
          | none =>
              simp [hrest] at hdecode
              apply
                runConfig_state_ne_halt_of_reaches_ne_halt_region
                  CLSS_htf
                  (k := 4)
                  (mid :=
                    config 120
                      (List.append (tickBits.reverse.map some) leftRev)
                      ((encodeCodeWordAsInput rest).map
                        some))
              · simpa [tickBits, encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput] using
                  run_cellList_state120_tick leftRev
                    ((encodeCodeWordAsInput rest).map some)
              · intro m
                exact ih
                  (List.append (tickBits.reverse.map some) leftRev)
                  hrest m
          | some _parsed =>
              simp [hrest] at hdecode
      | done =>
          simp [decodeNat] at hdecode
      | blank =>
          exact
            primitive_runConfig_state_ne_halt_of_reaches_stuck
              CLSS_htf
              (D := CLSS)
              (c :=
                config 120 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.blank :: rest)).map some))
              (stuck :=
                CLSS.runConfig 1
                  (config 120 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.blank :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CellListSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (121 : Nat) ≠ 999
                omega)
      | zero =>
          exact
            primitive_runConfig_state_ne_halt_of_reaches_stuck
              CLSS_htf
              (D := CLSS)
              (c :=
                config 120 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.zero :: rest)).map some))
              (stuck :=
                CLSS.runConfig 1
                  (config 120 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.zero :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CellListSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (121 : Nat) ≠ 999
                omega)
      | one =>
          exact
            primitive_runConfig_state_ne_halt_of_reaches_stuck
              CLSS_htf
              (D := CLSS)
              (c :=
                config 120 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.one :: rest)).map some))
              (stuck :=
                CLSS.runConfig 1
                  (config 120 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.one :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CellListSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (121 : Nat) ≠ 999
                omega)
      | moveLeft =>
          exact
            primitive_runConfig_state_ne_halt_of_reaches_stuck
              CLSS_htf
              (D := CLSS)
              (c :=
                config 120 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.moveLeft :: rest)).map some))
              (stuck :=
                CLSS.runConfig 1
                  (config 120 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.moveLeft :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CellListSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (121 : Nat) ≠ 999
                omega)
      | moveRight =>
          exact
            primitive_runConfig_state_ne_halt_of_reaches_stuck
              CLSS_htf
              (D := CLSS)
              (c :=
                config 120 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.moveRight :: rest)).map some))
              (stuck :=
                config 120 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.moveRight :: rest)).map some))
              (k := 0) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CellListSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read])
              (by
                change (120 : Nat) ≠ 999
                omega)

theorem cellListSuffixScannerDescription_runConfig_state130_decodeCell_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : decodeCell tokens = none) (n : Nat) :
    (CLSS.runConfig n
      (config 130 leftRev
        ((encodeCodeWordAsInput tokens).map some))).state ≠
      CLSS.halt := by
  cases tokens with
  | nil =>
      exact
        primitive_runConfig_state_ne_halt_of_reaches_stuck
          CLSS_htf
          (D := CLSS)
          (c :=
            config 130 leftRev
              ((encodeCodeWordAsInput
                ([] : Word MachineCodeSymbol)).map some))
          (stuck :=
            config 130 leftRev
              ((encodeCodeWordAsInput
                ([] : Word MachineCodeSymbol)).map some))
          (k := 0) (n := n)
          rfl
          (by rfl)
          (by
            change (130 : Nat) ≠ 999
            omega)
  | cons symbol rest =>
      cases symbol with
      | header =>
          exact
            primitive_runConfig_state_ne_halt_of_reaches_stuck
              CLSS_htf
              (D := CLSS)
              (c :=
                config 130 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.header :: rest)).map some))
              (stuck :=
                CLSS.runConfig 1
                  (config 130 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.header :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CellListSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (131 : Nat) ≠ 999
                omega)
      | transition =>
          exact
            primitive_runConfig_state_ne_halt_of_reaches_stuck
              CLSS_htf
              (D := CLSS)
              (c :=
                config 130 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.transition :: rest)).map some))
              (stuck :=
                CLSS.runConfig 1
                  (config 130 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.transition :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CellListSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (131 : Nat) ≠ 999
                omega)
      | tick =>
          exact
            primitive_runConfig_state_ne_halt_of_reaches_stuck
              CLSS_htf
              (D := CLSS)
              (c :=
                config 130 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.tick :: rest)).map some))
              (stuck :=
                CLSS.runConfig 1
                  (config 130 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.tick :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CellListSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (131 : Nat) ≠ 999
                omega)
      | done =>
          exact
            primitive_runConfig_state_ne_halt_of_reaches_stuck
              CLSS_htf
              (D := CLSS)
              (c :=
                config 130 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.done :: rest)).map some))
              (stuck :=
                CLSS.runConfig 1
                  (config 130 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.done :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CellListSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
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
            primitive_runConfig_state_ne_halt_of_reaches_stuck
              CLSS_htf
              (D := CLSS)
              (c :=
                config 130 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.moveLeft :: rest)).map some))
              (stuck :=
                config 145
                  (some true :: some true :: some true :: leftRev)
                  (some true ::
                    (encodeCodeWordAsInput rest).map
                      some))
              (k := 5) (n := n)
              (by
                cases rest <;>
                simp [CellListSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveLeft,
                  Tape.moveRight])
              (by
                cases rest <;>
                simp [CellListSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read])
              (by
                change (145 : Nat) ≠ 999
                omega)
      | moveRight =>
          exact
            primitive_runConfig_state_ne_halt_of_reaches_stuck
              CLSS_htf
              (D := CLSS)
              (c :=
                config 130 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.moveRight :: rest)).map some))
              (stuck :=
                CLSS.runConfig 1
                  (config 130 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.moveRight :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CellListSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart,
                  runConfig,
                  stepConfig,
                  lookupTransition,
                  Matches,
                  transition,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (135 : Nat) ≠ 999
                omega)

def cellListMarkingTailConfig
    (baseLeft marked : List (Option Bool))
    (remainingCells : Nat) (tokens : Word MachineCodeSymbol) :
    Configuration :=
  config 120
    (List.append markedTickRev
      (List.append (cellListCanonicalLengthPrefixRev marked.length)
        baseLeft))
    (List.append ((stageNatBits (remainingCells - 1)).map some)
      (List.append ((markedCellsCodeBits marked).map some)
        ((encodeCodeWordAsInput tokens).map some)))

def cellListMarkingTailPayloadLeftRev
    (baseLeft marked : List (Option Bool))
    (remainingLengthTail : Nat) : List (Option Bool) :=
  List.append ((markedCellsCodeBits marked).reverse.map some)
    (List.append ((stageNatBits remainingLengthTail).reverse.map some)
      (List.append markedTickRev
        (List.append (cellListCanonicalLengthPrefixRev marked.length)
          baseLeft)))

def cellListMarkingTailReturnScanRev
    (marked : List (Option Bool)) (remainingLengthTail : Nat) :
    Word Bool :=
  List.append [true, true]
    (List.append (markedCellsCodeBits marked).reverse
      (stageNatBits remainingLengthTail).reverse)

theorem cellListMarkingTail_to_first_payload
    (baseLeft marked : List (Option Bool))
    (remainingLengthTail : Nat) (tokens : Word MachineCodeSymbol) :
    CLSS.runConfig
        ((4 * remainingLengthTail + 4) + 4 * marked.length)
        (cellListMarkingTailConfig baseLeft marked
          (remainingLengthTail + 1) tokens) =
      config 130
        (cellListMarkingTailPayloadLeftRev baseLeft marked
          remainingLengthTail)
        ((encodeCodeWordAsInput tokens).map some) := by
  unfold cellListMarkingTailConfig
    cellListMarkingTailPayloadLeftRev
  simp only [Nat.add_sub_cancel_right]
  change
    CLSS.runConfig
        ((4 * remainingLengthTail + 4) + 4 * marked.length)
        (config 120
          (List.append markedTickRev
            (List.append (cellListCanonicalLengthPrefixRev marked.length)
              baseLeft))
          (List.append ((stageNatBits remainingLengthTail).map some)
            (List.append ((markedCellsCodeBits marked).map some)
              ((encodeCodeWordAsInput tokens).map
                some)))) =
      config 130
        (List.append ((markedCellsCodeBits marked).reverse.map some)
          (List.append ((stageNatBits remainingLengthTail).reverse.map some)
            (List.append markedTickRev
              (List.append (cellListCanonicalLengthPrefixRev marked.length)
                baseLeft))))
        ((encodeCodeWordAsInput tokens).map some)
  rw [runConfig_add]
  rw [run_cellList_state120_stageNat]
  rw [run_cellList_state130_markedCells]

theorem cellListMarkingTail_mark_one
    (baseLeft marked : List (Option Bool))
    (remainingLengthTail : Nat) (cell : Option Bool)
    (restAfterCell : Word MachineCodeSymbol) :
    exists steps : Nat,
      CLSS.runConfig steps
          (cellListMarkingTailConfig baseLeft marked
            (remainingLengthTail + 2)
            (encodeCellAppend cell restAfterCell)) =
        cellListMarkingTailConfig baseLeft (List.append marked [cell])
          (remainingLengthTail + 1) restAfterCell := by
  let scanRev :=
    cellListMarkingTailReturnScanRev marked (remainingLengthTail + 1)
  refine
    ⟨((4 * (remainingLengthTail + 1) + 4) +
        4 * marked.length) +
        ((6 + (scanRev.length + 4)) + 4), ?_⟩
  rw [runConfig_add]
  rw [cellListMarkingTail_to_first_payload]
  rw [show 6 + (scanRev.length + 4) + 4 =
      6 + ((scanRev.length + 4) + 4) by omega]
  rw [runConfig_add]
  have hcellBits :
      (encodeCodeWordAsInput
          (encodeCellAppend cell restAfterCell)).map
        some =
      List.append ((cellCodeBits cell).map some)
        ((encodeCodeWordAsInput restAfterCell).map
          some) := by
    cases cell with
    | none =>
        simp [encodeCellAppend,
          encodeCell,
          encodeCodeWordAsInput,
          encodeCodeSymbolAsInput, cellCodeBits]
    | some b =>
        cases b <;>
        simp [encodeCellAppend,
          encodeCell,
          encodeCodeWordAsInput,
          encodeCodeSymbolAsInput, cellCodeBits]
  rw [hcellBits]
  change
    CLSS.runConfig
        ((scanRev.length + 4) + 4)
        (CLSS.runConfig 6
          (config 130
            (cellListMarkingTailPayloadLeftRev baseLeft marked
              (remainingLengthTail + 1))
            (List.append ((cellCodeBits cell).map some)
              ((encodeCodeWordAsInput
                restAfterCell).map some)))) =
      cellListMarkingTailConfig baseLeft (List.append marked [cell])
        (remainingLengthTail + 1) restAfterCell
  rw [run_cellList_state130_currentCell]
  rw [runConfig_add]
  have hleft :
      some true :: some true ::
          cellListMarkingTailPayloadLeftRev baseLeft marked
            (remainingLengthTail + 1) =
        List.append (scanRev.map some)
          (none :: some true :: some false :: some false ::
            List.append (cellListCanonicalLengthPrefixRev marked.length)
              baseLeft) := by
    simp [scanRev, cellListMarkingTailReturnScanRev,
      cellListMarkingTailPayloadLeftRev, markedTickRev,
      List.map_append, List.append_assoc]
  rw [hleft]
  cases cell with
  | none =>
      rw [show
          List.append (cellCodeTailCells none)
              ((encodeCodeWordAsInput restAfterCell).map
                some) =
            some false :: some false ::
              (encodeCodeWordAsInput restAfterCell).map
                some by
        simp [cellCodeTailCells]]
      rw [run_cellList_state140_returnToLengthMarker]
      have hright :
          List.append (scanRev.reverse.map some)
              (some false :: some false ::
                (encodeCodeWordAsInput restAfterCell).map
                  some) =
            List.append (tickBits.map some)
              (List.append ((stageNatBits remainingLengthTail).map some)
                (List.append
                  ((markedCellsCodeBits (List.append marked [none])).map
                    some)
                  ((encodeCodeWordAsInput
                    restAfterCell).map some))) := by
        rw [map_markedCellsCodeBits_append_single marked none]
        simp [scanRev, cellListMarkingTailReturnScanRev,
          markedCellCodeBits, stageNatBits_succ, tickBits,
          encodeCodeSymbolAsInput, List.map_append,
          List.reverse_append, List.append_assoc]
      rw [hright]
      rw [run_cellList_state100_tick]
      have hleftNext :
          List.append markedTickRev
              (some false :: some true :: some false :: some false ::
                List.append (cellListCanonicalLengthPrefixRev marked.length)
                  baseLeft) =
            List.append markedTickRev
              (List.append
                (cellListCanonicalLengthPrefixRev
                  (List.append marked [none]).length)
                baseLeft) := by
        rw [show (List.append marked [none]).length =
            marked.length + 1 by simp]
        simp [cellListCanonicalLengthPrefixRev, tickBits,
          encodeCodeSymbolAsInput]
      unfold cellListMarkingTailConfig
      rw [hleftNext]
      simp
  | some b =>
      cases b
      · rw [show
            List.append (cellCodeTailCells (some false))
                ((encodeCodeWordAsInput restAfterCell).map
                  some) =
              some false :: some true ::
                (encodeCodeWordAsInput restAfterCell).map
                  some by
          simp [cellCodeTailCells]]
        rw [run_cellList_state140_returnToLengthMarker]
        have hright :
            List.append (scanRev.reverse.map some)
                (some false :: some true ::
                  (encodeCodeWordAsInput restAfterCell).map
                    some) =
              List.append (tickBits.map some)
                (List.append ((stageNatBits remainingLengthTail).map some)
                  (List.append
                    ((markedCellsCodeBits
                      (List.append marked [some false])).map some)
                    ((encodeCodeWordAsInput
                      restAfterCell).map some))) := by
          rw [map_markedCellsCodeBits_append_single marked (some false)]
          simp [scanRev, cellListMarkingTailReturnScanRev,
            markedCellCodeBits, stageNatBits_succ, tickBits,
            encodeCodeSymbolAsInput, List.map_append,
            List.reverse_append, List.append_assoc]
        rw [hright]
        rw [run_cellList_state100_tick]
        have hleftNext :
            List.append markedTickRev
                (some false :: some true :: some false :: some false ::
                  List.append
                    (cellListCanonicalLengthPrefixRev marked.length)
                    baseLeft) =
              List.append markedTickRev
                (List.append
                  (cellListCanonicalLengthPrefixRev
                    (List.append marked [some false]).length)
                  baseLeft) := by
          rw [show (List.append marked [some false]).length =
              marked.length + 1 by simp]
          simp [cellListCanonicalLengthPrefixRev, tickBits,
            encodeCodeSymbolAsInput]
        unfold cellListMarkingTailConfig
        rw [hleftNext]
        simp
      · rw [show
            List.append (cellCodeTailCells (some true))
                ((encodeCodeWordAsInput restAfterCell).map
                  some) =
              some true :: some false ::
                (encodeCodeWordAsInput restAfterCell).map
                  some by
          simp [cellCodeTailCells]]
        rw [run_cellList_state140_returnToLengthMarker]
        have hright :
            List.append (scanRev.reverse.map some)
                (some true :: some false ::
                  (encodeCodeWordAsInput restAfterCell).map
                    some) =
              List.append (tickBits.map some)
                (List.append ((stageNatBits remainingLengthTail).map some)
                  (List.append
                    ((markedCellsCodeBits
                      (List.append marked [some true])).map some)
                    ((encodeCodeWordAsInput
                      restAfterCell).map some))) := by
          rw [map_markedCellsCodeBits_append_single marked (some true)]
          simp [scanRev, cellListMarkingTailReturnScanRev,
            markedCellCodeBits, stageNatBits_succ, tickBits,
            encodeCodeSymbolAsInput, List.map_append,
            List.reverse_append, List.append_assoc]
        rw [hright]
        rw [run_cellList_state100_tick]
        have hleftNext :
            List.append markedTickRev
                (some false :: some true :: some false :: some false ::
                  List.append
                    (cellListCanonicalLengthPrefixRev marked.length)
                    baseLeft) =
              List.append markedTickRev
                (List.append
                  (cellListCanonicalLengthPrefixRev
                    (List.append marked [some true]).length)
                  baseLeft) := by
          rw [show (List.append marked [some true]).length =
              marked.length + 1 by simp]
          simp [cellListCanonicalLengthPrefixRev, tickBits,
            encodeCodeSymbolAsInput]
        unfold cellListMarkingTailConfig
        rw [hleftNext]
        simp

theorem cellListMarkingTail_decodeCells_none_ne_halt
    (baseLeft marked : List (Option Bool))
    (remainingCells : Nat) (tokens : Word MachineCodeSymbol)
    (hdecode :
      decodeCells remainingCells tokens = none)
    (n : Nat) :
    (CLSS.runConfig n
      (cellListMarkingTailConfig baseLeft marked remainingCells tokens)).state ≠
      CLSS.halt := by
  induction remainingCells generalizing marked tokens n with
  | zero =>
      simp [decodeCells] at hdecode
  | succ remainingTail ih =>
      cases hcell : decodeCell tokens with
      | none =>
          apply
            runConfig_state_ne_halt_of_reaches_ne_halt_region
              CLSS_htf
              (k := (4 * remainingTail + 4) + 4 * marked.length)
              (mid :=
                config 130
                  (cellListMarkingTailPayloadLeftRev baseLeft marked
                    remainingTail)
                  ((encodeCodeWordAsInput tokens).map
                    some))
          · exact
              cellListMarkingTail_to_first_payload
                baseLeft marked remainingTail tokens
          · intro m
            exact
              cellListSuffixScannerDescription_runConfig_state130_decodeCell_none_ne_halt
                tokens
                (cellListMarkingTailPayloadLeftRev baseLeft marked
                  remainingTail)
                hcell m
      | some parsedCell =>
          rcases parsedCell with ⟨cell, restAfterCell⟩
          have htokens :
              tokens =
                encodeCellAppend cell restAfterCell :=
            decodeCell_eq_some_encodeCellAppend hcell
          cases hrest :
              decodeCells remainingTail
                restAfterCell with
          | none =>
              cases remainingTail with
              | zero =>
                  simp [decodeCells, hcell] at hdecode
              | succ nextTail =>
                  rcases
                      cellListMarkingTail_mark_one
                        baseLeft marked nextTail cell restAfterCell with
                    ⟨steps, hsteps⟩
                  apply
                    runConfig_state_ne_halt_of_reaches_ne_halt_region
                      CLSS_htf
                      (k := steps)
                      (mid :=
                        cellListMarkingTailConfig baseLeft
                          (List.append marked [cell])
                          (nextTail + 1) restAfterCell)
                  · rw [htokens]
                    exact hsteps
                  · intro m
                    exact
                      ih (List.append marked [cell])
                        restAfterCell hrest m
          | some parsedRest =>
              simp [decodeCells, hcell, hrest]
                at hdecode

theorem cellListSuffixScannerDescription_runConfig_state120_tick_decodeCellList_none_ne_halt
    (baseLeft : List (Option Bool)) (rest : Word MachineCodeSymbol)
    (hdecode :
      decodeCellList (MachineCodeSymbol.tick :: rest) =
        none)
    (n : Nat) :
    (CLSS.runConfig n
      (config 120 (List.append markedTickRev baseLeft)
        ((encodeCodeWordAsInput rest).map some))).state ≠
      CLSS.halt := by
  cases hnat : decodeNat rest with
  | none =>
      exact
        cellListSuffixScannerDescription_runConfig_state120_decodeNat_none_ne_halt
          rest (List.append markedTickRev baseLeft) hnat n
  | some parsedNat =>
      rcases parsedNat with ⟨remainingTail, tokensAfterLen⟩
      have hrest :
          rest =
            encodeNatAppend
              remainingTail tokensAfterLen :=
        decodeNat_eq_some_encodeNatAppend hnat
      rw [hrest]
      change
        (CLSS.runConfig n
          (config 120 (List.append markedTickRev baseLeft)
            (List.map some
              (encodeCodeWordAsInput
                (encodeNatAppend remainingTail
                  tokensAfterLen))))).state ≠
          CLSS.halt
      unfold encodeNatAppend
      rw [encodeCodeWordAsInput_append]
      have hbits :
          List.map some
              (List.append
                (encodeCodeWordAsInput
                  (encodeNat remainingTail))
                (encodeCodeWordAsInput tokensAfterLen)) =
            List.append ((stageNatBits remainingTail).map some)
              ((encodeCodeWordAsInput tokensAfterLen).map
                some) := by
        simp [stageNatBits, List.map_append]
      rw [hbits]
      cases hcells :
          decodeCells (remainingTail + 1)
            tokensAfterLen with
      | none =>
          simpa [cellListMarkingTailConfig] using
            cellListMarkingTail_decodeCells_none_ne_halt
              baseLeft ([] : List (Option Bool)) (remainingTail + 1)
              tokensAfterLen hcells n
      | some _parsedCells =>
          simp [decodeCellList,
            decodeNat, hnat, hcells]
            at hdecode

theorem cellListSuffixScannerDescription_runConfig_state120_tick_code_inv
    (baseLeft : List (Option Bool)) (rest : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      CLSS.runConfig n
          (config 120 (List.append markedTickRev baseLeft)
            ((encodeCodeWordAsInput rest).map some)) =
        { state := CLSS.halt
          tape := Tout }) :
    exists cells : List (Option Bool),
    exists suffix : Word MachineCodeSymbol,
      MachineCodeSymbol.tick :: rest =
        encodeCellListAppend cells suffix := by
  cases hdecode :
      decodeCellList (MachineCodeSymbol.tick :: rest) with
  | none =>
      have hne :=
        cellListSuffixScannerDescription_runConfig_state120_tick_decodeCellList_none_ne_halt
          baseLeft rest hdecode n
      have hstate :
          (CLSS.runConfig n
            (config 120 (List.append markedTickRev baseLeft)
              ((encodeCodeWordAsInput rest).map
                some))).state =
            CLSS.halt := by
        simpa using congrArg Configuration.state h
      exact False.elim (hne hstate)
  | some parsed =>
      rcases parsed with ⟨cells, suffix⟩
      exact
        ⟨cells, suffix,
          decodeCellList_eq_some_encodeCellListAppend
            hdecode⟩

theorem cellListSuffixScannerDescription_runConfig_code_inv
    (baseLeft : List (Option Bool)) (code : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      CLSS.runConfig n
          (config CLSS.start baseLeft
            ((encodeCodeWordAsInput code).map some)) =
        { state := CLSS.halt
          tape := Tout }) :
    exists cells : List (Option Bool),
    exists suffix : Word MachineCodeSymbol,
      code = encodeCellListAppend cells suffix := by
  rcases
      cellListSuffixScannerDescription_runConfig_start_nat_prefix_inv
        baseLeft (encodeCodeWordAsInput code) h with
    ⟨doneBit, tail, hprefix⟩
  cases code with
  | nil =>
      simp [encodeCodeWordAsInput] at hprefix
  | cons symbol rest =>
      cases symbol <;>
        simp [encodeCodeWordAsInput,
          encodeCodeSymbolAsInput] at hprefix
      · cases hprefix
      · cases hprefix
      · let c0 : Configuration :=
          config CLSS.start baseLeft
            ((encodeCodeWordAsInput
              (MachineCodeSymbol.tick :: rest)).map some)
        let c1 : Configuration :=
          config 120 (List.append markedTickRev baseLeft)
            ((encodeCodeWordAsInput rest).map some)
        have hforward :
            CLSS.runConfig 4 c0 = c1 := by
          dsimp [c0, c1]
          simpa [encodeCodeWordAsInput,
            encodeCodeSymbolAsInput, tickBits] using
            run_cellList_state100_tick baseLeft
              ((encodeCodeWordAsInput rest).map some)
        have hhalt :
            CLSS.runConfig n c0 =
              { state := CLSS.halt
                tape := Tout } := by
          simpa [c0] using h
        rcases
            runConfig_forward_inv CLSS
              c0 c1 n 4 hhalt hforward
              CLSS_htf with
          ⟨_m, _hm_le, hm_halt⟩
        exact
          cellListSuffixScannerDescription_runConfig_state120_tick_code_inv
            baseLeft rest hm_halt
      · exact ⟨[], rest, by
          simp [encodeCellListAppend,
            encodeNatAppend,
            encodeNat,
            encodeCellsAppend]⟩
      · cases hprefix
      · cases hprefix
      · cases hprefix
      · cases hprefix
      · cases hprefix

theorem cellListSuffixScannerDescription_runConfig_encodeCellListAppend_handoff_false
    (baseLeft cells : List (Option Bool))
    (suffix : Word MachineCodeSymbol) (suffixTail : Word Bool)
    {Tout : Tape Bool} {n : Nat}
    (hsuffix :
      encodeCodeWordAsInput suffix =
        false :: suffixTail)
    (h :
      CLSS.runConfig n
          (config CLSS.start baseLeft
            ((encodeCodeWordAsInput
              (encodeCellListAppend cells
                suffix)).map some)) =
        { state := CLSS.halt
          tape := Tout }) :
      Tout =
        (cellListCanonicalHandoffConfigWithBase cells baseLeft
          (false :: suffixTail)).tape := by
  exact
    cellListSuffixScannerDescription_runConfig_canonical_false_suffix_inv
      cells baseLeft suffixTail
      (by
        simpa [cellListBits_eq_encodeCellListAppend, hsuffix,
          List.map_append, cellListFieldBits] using h)

theorem cellListCanonicalFinishStartConfigWithBase_nil_suffix_ne_halt
    (cells baseLeft : List (Option Bool)) (n : Nat) :
    (CLSS.runConfig n
      (cellListCanonicalFinishStartConfigWithBase cells baseLeft [])).state ≠
      CLSS.halt := by
  let stuck : Configuration :=
    config 150
      (cellListCanonicalRestoredLeftWithBase cells baseLeft)
      ([] : List (Option Bool))
  apply
    primitive_runConfig_state_ne_halt_of_reaches_stuck
      CLSS_htf
      (D := CLSS)
      (c := cellListCanonicalFinishStartConfigWithBase cells baseLeft [])
      (stuck := stuck)
      (k := 4 * cells.length) (n := n)
  · unfold stuck cellListCanonicalFinishStartConfigWithBase
    simpa [cellListCanonicalRestoredLeftWithBase] using
      run_cellList_state150_markedCells cells
        (cellListCanonicalFinishStartLeftWithBase cells baseLeft)
        ([] : List (Option Bool))
  · simp [stuck, config, tapeAtCells, CellListSuffixScannerDescription,
      keep, keepMove, writeMove, scanLeftToSentinelRestart,
      stepConfig, lookupTransition,
      Matches, transition, Tape.read]
  · change (150 : Nat) ≠ 999
    omega

theorem cellListCanonicalFinishStartConfigWithBase_moveRight_suffix_ne_halt
    (cells baseLeft : List (Option Bool)) (tail : Word Bool) (n : Nat) :
    (CLSS.runConfig n
      (cellListCanonicalFinishStartConfigWithBase cells baseLeft
        (true :: false :: false :: false :: tail))).state ≠
      CLSS.halt := by
  let stuck : Configuration :=
    CLSS.runConfig 1
      (config 150
        (cellListCanonicalRestoredLeftWithBase cells baseLeft)
        ((true :: false :: false :: false :: tail).map some))
  apply
    primitive_runConfig_state_ne_halt_of_reaches_stuck
      CLSS_htf
      (D := CLSS)
      (c :=
        cellListCanonicalFinishStartConfigWithBase cells baseLeft
          (true :: false :: false :: false :: tail))
      (stuck := stuck)
      (k := 4 * cells.length + 1) (n := n)
  · rw [show 4 * cells.length + 1 = 4 * cells.length + 1 by rfl]
    rw [runConfig_add]
    unfold stuck cellListCanonicalFinishStartConfigWithBase
    rw [show
        CLSS.runConfig (4 * cells.length)
            (config 150
              (cellListCanonicalFinishStartLeftWithBase cells baseLeft)
              (List.append ((markedCellsCodeBits cells).map some)
                (List.map some
                  (true :: false :: false :: false :: tail)))) =
          config 150
            (cellListCanonicalRestoredLeftWithBase cells baseLeft)
            (List.map some
              (true :: false :: false :: false :: tail)) by
      simpa [cellListCanonicalRestoredLeftWithBase] using
        run_cellList_state150_markedCells cells
          (cellListCanonicalFinishStartLeftWithBase cells baseLeft)
          (List.map some
            (true :: false :: false :: false :: tail))]
  · unfold stuck
    cases tail <;>
      simp [CellListSuffixScannerDescription, config, tapeAtCells,
        keep, keepMove, writeMove, scanLeftToSentinelRestart,
        runConfig, stepConfig,
        lookupTransition, Matches,
        transition, Tape.read, Tape.write, Tape.move,
        Tape.moveRight]
  · unfold stuck
    change
      (CLSS.runConfig 1
        (config 150
          (cellListCanonicalRestoredLeftWithBase cells baseLeft)
          ((true :: false :: false :: false :: tail).map some))).state ≠
        999
    cases tail <;>
      simp [CellListSuffixScannerDescription, config, tapeAtCells,
        keep, keepMove, writeMove, scanLeftToSentinelRestart,
        runConfig, stepConfig,
        lookupTransition, Matches,
        transition, Tape.read, Tape.write, Tape.move,
        Tape.moveRight]

theorem cellListSuffixScannerDescription_runConfig_encodeCellListAppend_suffix_false
    (baseLeft cells : List (Option Bool))
    (suffix : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      CLSS.runConfig n
          (config CLSS.start baseLeft
            ((encodeCodeWordAsInput
              (encodeCellListAppend cells suffix)).map
              some)) =
        { state := CLSS.halt
          tape := Tout }) :
    exists suffixTail : Word Bool,
      encodeCodeWordAsInput suffix =
        false :: suffixTail := by
  let suffixBits := encodeCodeWordAsInput suffix
  cases suffix with
  | nil =>
      have hstate :
          (CLSS.runConfig n
            (config CLSS.start baseLeft
              ((encodeCodeWordAsInput
                (encodeCellListAppend cells
                  ([] : Word MachineCodeSymbol))).map some))).state =
            CLSS.halt := by
        simpa using congrArg Configuration.state h
      rcases
          run_cellList_raw_marking_loop_from_state100_withBase
            baseLeft ([] : List (Option Bool)) cells
            ([] : Word Bool) with
        ⟨steps, hsteps⟩
      have hprefix :
          CLSS.runConfig steps
              (config CLSS.start baseLeft
                ((encodeCodeWordAsInput
                  (encodeCellListAppend cells
                    ([] : Word MachineCodeSymbol))).map some)) =
          cellListCanonicalFinishStartConfigWithBase cells baseLeft
              ([] : Word Bool) := by
        simpa [CellListSuffixScannerDescription, cellListBits_eq_encodeCellListAppend,
          cellListFieldBits, cellListCanonicalLengthPrefixRev,
          markedCellsCodeBits, encodeCodeWordAsInput,
          List.map_append, List.append_assoc] using hsteps
      exact False.elim
        ((runConfig_state_ne_halt_of_reaches_ne_halt_region
            CLSS_htf
            hprefix
            (by
              intro m
              simpa [suffixBits,
                encodeCodeWordAsInput] using
                cellListCanonicalFinishStartConfigWithBase_nil_suffix_ne_halt
                  cells baseLeft m)
            (n := n)) hstate)
  | cons symbol rest =>
      cases symbol with
      | moveRight =>
          have hstate :
              (CLSS.runConfig n
                (config CLSS.start baseLeft
                  ((encodeCodeWordAsInput
                    (encodeCellListAppend cells
                      (MachineCodeSymbol.moveRight :: rest))).map some))).state =
                CLSS.halt := by
            simpa using congrArg Configuration.state h
          rcases
              run_cellList_raw_marking_loop_from_state100_withBase
                baseLeft ([] : List (Option Bool)) cells
                (encodeCodeWordAsInput
                  (MachineCodeSymbol.moveRight :: rest)) with
            ⟨steps, hsteps⟩
          have hprefix :
              CLSS.runConfig steps
                  (config CLSS.start baseLeft
                    ((encodeCodeWordAsInput
                      (encodeCellListAppend cells
                        (MachineCodeSymbol.moveRight :: rest))).map some)) =
                cellListCanonicalFinishStartConfigWithBase cells baseLeft
                  (encodeCodeWordAsInput
                    (MachineCodeSymbol.moveRight :: rest)) := by
            simpa [CellListSuffixScannerDescription,
              cellListBits_eq_encodeCellListAppend, cellListFieldBits,
              cellListCanonicalLengthPrefixRev, markedCellsCodeBits,
              List.map_append, List.append_assoc] using hsteps
          exact False.elim
            ((runConfig_state_ne_halt_of_reaches_ne_halt_region
                CLSS_htf
                hprefix
                (by
                  intro m
                  simpa [suffixBits, encodeCodeWordAsInput,
                    encodeCodeSymbolAsInput] using
                    cellListCanonicalFinishStartConfigWithBase_moveRight_suffix_ne_halt
                      cells baseLeft
                      (encodeCodeWordAsInput rest) m)
                (n := n)) hstate)
      | header =>
          refine ⟨false :: false :: false ::
            encodeCodeWordAsInput rest, ?_⟩
          simp [encodeCodeWordAsInput,
            encodeCodeSymbolAsInput]
      | transition =>
          refine ⟨false :: false :: true ::
            encodeCodeWordAsInput rest, ?_⟩
          simp [encodeCodeWordAsInput,
            encodeCodeSymbolAsInput]
      | tick =>
          refine ⟨false :: true :: false ::
            encodeCodeWordAsInput rest, ?_⟩
          simp [encodeCodeWordAsInput,
            encodeCodeSymbolAsInput]
      | done =>
          refine ⟨false :: true :: true ::
            encodeCodeWordAsInput rest, ?_⟩
          simp [encodeCodeWordAsInput,
            encodeCodeSymbolAsInput]
      | blank =>
          refine ⟨true :: false :: false ::
            encodeCodeWordAsInput rest, ?_⟩
          simp [encodeCodeWordAsInput,
            encodeCodeSymbolAsInput]
      | zero =>
          refine ⟨true :: false :: true ::
            encodeCodeWordAsInput rest, ?_⟩
          simp [encodeCodeWordAsInput,
            encodeCodeSymbolAsInput]
      | one =>
          refine ⟨true :: true :: false ::
            encodeCodeWordAsInput rest, ?_⟩
          simp [encodeCodeWordAsInput,
            encodeCodeSymbolAsInput]
      | moveLeft =>
          refine ⟨true :: true :: true ::
            encodeCodeWordAsInput rest, ?_⟩
          simp [encodeCodeWordAsInput,
            encodeCodeSymbolAsInput]

end DovetailLayoutScanner
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC
