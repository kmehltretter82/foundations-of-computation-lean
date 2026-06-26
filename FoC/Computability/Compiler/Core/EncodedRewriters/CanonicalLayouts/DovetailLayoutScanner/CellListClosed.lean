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

namespace EncodedRewriters
namespace CanonicalLayouts
namespace DovetailLayoutScanner

open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

theorem runConfig_state_ne_halt_of_reaches_ne_halt_region
    {D : MachineDescription}
    {c mid : MachineDescription.Configuration} {k n : Nat}
    (hD : D.HaltTransitionFree)
    (hrun : D.runConfig k c = mid)
    (hmid : forall m : Nat, (D.runConfig m mid).state ≠ D.halt) :
    (D.runConfig n c).state ≠ D.halt := by
  by_cases hle : n ≤ k
  · intro hhalt
    let rem := k - n
    have hk : k = n + rem := by
      omega
    have hcfg :
        D.runConfig n c =
          { state := D.halt
            tape := (D.runConfig n c).tape } := by
      cases hrunN : D.runConfig n c with
      | mk state tape =>
          simp [hrunN] at hhalt
          simp [hhalt]
    have hhaltAtK :
        (D.runConfig k c).state = D.halt := by
      rw [hk, MachineDescription.runConfig_add, hcfg,
        MachineDescription.runConfig_halt hD]
    rw [hrun] at hhaltAtK
    exact hmid 0 hhaltAtK
  · have hn : n = k + (n - k) := by
      omega
    rw [hn, MachineDescription.runConfig_add, hrun]
    exact hmid (n - k)

theorem cellListSuffixScannerDescription_runConfig_state120_decodeNat_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : MachineDescription.decodeNat tokens = none) (n : Nat) :
    (CellListSuffixScannerDescription.runConfig n
      (config 120 leftRev
        ((MachineDescription.encodeCodeWordAsInput tokens).map some))).state ≠
      CellListSuffixScannerDescription.halt := by
  induction tokens generalizing leftRev n with
  | nil =>
      exact
        primitive_runConfig_state_ne_halt_of_reaches_stuck
          cellListSuffixScannerDescription_haltTransitionFree
          (D := CellListSuffixScannerDescription)
          (c :=
            config 120 leftRev
              ((MachineDescription.encodeCodeWordAsInput
                ([] : Word MachineCodeSymbol)).map some))
          (stuck :=
            config 120 leftRev
              ((MachineDescription.encodeCodeWordAsInput
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
              cellListSuffixScannerDescription_haltTransitionFree
              (D := CellListSuffixScannerDescription)
              (c :=
                config 120 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.header :: rest)).map some))
              (stuck :=
                CellListSuffixScannerDescription.runConfig 2
                  (config 120 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.header :: rest)).map some)))
              (k := 2) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CellListSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (122 : Nat) ≠ 999
                omega)
      | transition =>
          exact
            primitive_runConfig_state_ne_halt_of_reaches_stuck
              cellListSuffixScannerDescription_haltTransitionFree
              (D := CellListSuffixScannerDescription)
              (c :=
                config 120 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.transition :: rest)).map some))
              (stuck :=
                CellListSuffixScannerDescription.runConfig 2
                  (config 120 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.transition :: rest)).map some)))
              (k := 2) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CellListSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (122 : Nat) ≠ 999
                omega)
      | tick =>
          simp [MachineDescription.decodeNat] at hdecode
          cases hrest : MachineDescription.decodeNat rest with
          | none =>
              simp [hrest] at hdecode
              apply
                runConfig_state_ne_halt_of_reaches_ne_halt_region
                  cellListSuffixScannerDescription_haltTransitionFree
                  (k := 4)
                  (mid :=
                    config 120
                      (List.append (tickBits.reverse.map some) leftRev)
                      ((MachineDescription.encodeCodeWordAsInput rest).map
                        some))
              · simpa [tickBits, MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput] using
                  run_cellList_state120_tick leftRev
                    ((MachineDescription.encodeCodeWordAsInput rest).map some)
              · intro m
                exact ih
                  (List.append (tickBits.reverse.map some) leftRev)
                  hrest m
          | some _parsed =>
              simp [hrest] at hdecode
      | done =>
          simp [MachineDescription.decodeNat] at hdecode
      | blank =>
          exact
            primitive_runConfig_state_ne_halt_of_reaches_stuck
              cellListSuffixScannerDescription_haltTransitionFree
              (D := CellListSuffixScannerDescription)
              (c :=
                config 120 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.blank :: rest)).map some))
              (stuck :=
                CellListSuffixScannerDescription.runConfig 1
                  (config 120 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.blank :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CellListSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (121 : Nat) ≠ 999
                omega)
      | zero =>
          exact
            primitive_runConfig_state_ne_halt_of_reaches_stuck
              cellListSuffixScannerDescription_haltTransitionFree
              (D := CellListSuffixScannerDescription)
              (c :=
                config 120 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.zero :: rest)).map some))
              (stuck :=
                CellListSuffixScannerDescription.runConfig 1
                  (config 120 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.zero :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CellListSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (121 : Nat) ≠ 999
                omega)
      | one =>
          exact
            primitive_runConfig_state_ne_halt_of_reaches_stuck
              cellListSuffixScannerDescription_haltTransitionFree
              (D := CellListSuffixScannerDescription)
              (c :=
                config 120 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.one :: rest)).map some))
              (stuck :=
                CellListSuffixScannerDescription.runConfig 1
                  (config 120 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.one :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CellListSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (121 : Nat) ≠ 999
                omega)
      | moveLeft =>
          exact
            primitive_runConfig_state_ne_halt_of_reaches_stuck
              cellListSuffixScannerDescription_haltTransitionFree
              (D := CellListSuffixScannerDescription)
              (c :=
                config 120 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.moveLeft :: rest)).map some))
              (stuck :=
                CellListSuffixScannerDescription.runConfig 1
                  (config 120 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.moveLeft :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CellListSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (121 : Nat) ≠ 999
                omega)
      | moveRight =>
          exact
            primitive_runConfig_state_ne_halt_of_reaches_stuck
              cellListSuffixScannerDescription_haltTransitionFree
              (D := CellListSuffixScannerDescription)
              (c :=
                config 120 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.moveRight :: rest)).map some))
              (stuck :=
                config 120 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.moveRight :: rest)).map some))
              (k := 0) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CellListSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read])
              (by
                change (120 : Nat) ≠ 999
                omega)

theorem cellListSuffixScannerDescription_runConfig_state130_decodeCell_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : MachineDescription.decodeCell tokens = none) (n : Nat) :
    (CellListSuffixScannerDescription.runConfig n
      (config 130 leftRev
        ((MachineDescription.encodeCodeWordAsInput tokens).map some))).state ≠
      CellListSuffixScannerDescription.halt := by
  cases tokens with
  | nil =>
      exact
        primitive_runConfig_state_ne_halt_of_reaches_stuck
          cellListSuffixScannerDescription_haltTransitionFree
          (D := CellListSuffixScannerDescription)
          (c :=
            config 130 leftRev
              ((MachineDescription.encodeCodeWordAsInput
                ([] : Word MachineCodeSymbol)).map some))
          (stuck :=
            config 130 leftRev
              ((MachineDescription.encodeCodeWordAsInput
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
              cellListSuffixScannerDescription_haltTransitionFree
              (D := CellListSuffixScannerDescription)
              (c :=
                config 130 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.header :: rest)).map some))
              (stuck :=
                CellListSuffixScannerDescription.runConfig 1
                  (config 130 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.header :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CellListSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (131 : Nat) ≠ 999
                omega)
      | transition =>
          exact
            primitive_runConfig_state_ne_halt_of_reaches_stuck
              cellListSuffixScannerDescription_haltTransitionFree
              (D := CellListSuffixScannerDescription)
              (c :=
                config 130 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.transition :: rest)).map some))
              (stuck :=
                CellListSuffixScannerDescription.runConfig 1
                  (config 130 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.transition :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CellListSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (131 : Nat) ≠ 999
                omega)
      | tick =>
          exact
            primitive_runConfig_state_ne_halt_of_reaches_stuck
              cellListSuffixScannerDescription_haltTransitionFree
              (D := CellListSuffixScannerDescription)
              (c :=
                config 130 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.tick :: rest)).map some))
              (stuck :=
                CellListSuffixScannerDescription.runConfig 1
                  (config 130 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.tick :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CellListSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (131 : Nat) ≠ 999
                omega)
      | done =>
          exact
            primitive_runConfig_state_ne_halt_of_reaches_stuck
              cellListSuffixScannerDescription_haltTransitionFree
              (D := CellListSuffixScannerDescription)
              (c :=
                config 130 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.done :: rest)).map some))
              (stuck :=
                CellListSuffixScannerDescription.runConfig 1
                  (config 130 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.done :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CellListSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
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
            primitive_runConfig_state_ne_halt_of_reaches_stuck
              cellListSuffixScannerDescription_haltTransitionFree
              (D := CellListSuffixScannerDescription)
              (c :=
                config 130 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.moveLeft :: rest)).map some))
              (stuck :=
                config 145
                  (some true :: some true :: some true :: leftRev)
                  (some true ::
                    (MachineDescription.encodeCodeWordAsInput rest).map
                      some))
              (k := 5) (n := n)
              (by
                cases rest <;>
                simp [CellListSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveLeft,
                  Tape.moveRight])
              (by
                cases rest <;>
                simp [CellListSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read])
              (by
                change (145 : Nat) ≠ 999
                omega)
      | moveRight =>
          exact
            primitive_runConfig_state_ne_halt_of_reaches_stuck
              cellListSuffixScannerDescription_haltTransitionFree
              (D := CellListSuffixScannerDescription)
              (c :=
                config 130 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.moveRight :: rest)).map some))
              (stuck :=
                CellListSuffixScannerDescription.runConfig 1
                  (config 130 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.moveRight :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CellListSuffixScannerDescription, config,
                  tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (135 : Nat) ≠ 999
                omega)

def cellListMarkingTailConfig
    (baseLeft marked : List (Option Bool))
    (remainingCells : Nat) (tokens : Word MachineCodeSymbol) :
    MachineDescription.Configuration :=
  config 120
    (List.append markedTickRev
      (List.append (cellListCanonicalLengthPrefixRev marked.length)
        baseLeft))
    (List.append ((stageNatBits (remainingCells - 1)).map some)
      (List.append ((markedCellsCodeBits marked).map some)
        ((MachineDescription.encodeCodeWordAsInput tokens).map some)))

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
    CellListSuffixScannerDescription.runConfig
        ((4 * remainingLengthTail + 4) + 4 * marked.length)
        (cellListMarkingTailConfig baseLeft marked
          (remainingLengthTail + 1) tokens) =
      config 130
        (cellListMarkingTailPayloadLeftRev baseLeft marked
          remainingLengthTail)
        ((MachineDescription.encodeCodeWordAsInput tokens).map some) := by
  unfold cellListMarkingTailConfig
    cellListMarkingTailPayloadLeftRev
  simp only [Nat.add_sub_cancel_right]
  change
    CellListSuffixScannerDescription.runConfig
        ((4 * remainingLengthTail + 4) + 4 * marked.length)
        (config 120
          (List.append markedTickRev
            (List.append (cellListCanonicalLengthPrefixRev marked.length)
              baseLeft))
          (List.append ((stageNatBits remainingLengthTail).map some)
            (List.append ((markedCellsCodeBits marked).map some)
              ((MachineDescription.encodeCodeWordAsInput tokens).map
                some)))) =
      config 130
        (List.append ((markedCellsCodeBits marked).reverse.map some)
          (List.append ((stageNatBits remainingLengthTail).reverse.map some)
            (List.append markedTickRev
              (List.append (cellListCanonicalLengthPrefixRev marked.length)
                baseLeft))))
        ((MachineDescription.encodeCodeWordAsInput tokens).map some)
  rw [MachineDescription.runConfig_add]
  rw [run_cellList_state120_stageNat]
  rw [run_cellList_state130_markedCells]

theorem cellListMarkingTail_mark_one
    (baseLeft marked : List (Option Bool))
    (remainingLengthTail : Nat) (cell : Option Bool)
    (restAfterCell : Word MachineCodeSymbol) :
    exists steps : Nat,
      CellListSuffixScannerDescription.runConfig steps
          (cellListMarkingTailConfig baseLeft marked
            (remainingLengthTail + 2)
            (MachineDescription.encodeCellAppend cell restAfterCell)) =
        cellListMarkingTailConfig baseLeft (List.append marked [cell])
          (remainingLengthTail + 1) restAfterCell := by
  let scanRev :=
    cellListMarkingTailReturnScanRev marked (remainingLengthTail + 1)
  refine
    ⟨((4 * (remainingLengthTail + 1) + 4) +
        4 * marked.length) +
        ((6 + (scanRev.length + 4)) + 4), ?_⟩
  rw [MachineDescription.runConfig_add]
  rw [cellListMarkingTail_to_first_payload]
  rw [show 6 + (scanRev.length + 4) + 4 =
      6 + ((scanRev.length + 4) + 4) by omega]
  rw [MachineDescription.runConfig_add]
  have hcellBits :
      (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeCellAppend cell restAfterCell)).map
        some =
      List.append ((cellCodeBits cell).map some)
        ((MachineDescription.encodeCodeWordAsInput restAfterCell).map
          some) := by
    cases cell with
    | none =>
        simp [MachineDescription.encodeCellAppend,
          MachineDescription.encodeCell,
          MachineDescription.encodeCodeWordAsInput,
          MachineDescription.encodeCodeSymbolAsInput, cellCodeBits]
    | some b =>
        cases b <;>
        simp [MachineDescription.encodeCellAppend,
          MachineDescription.encodeCell,
          MachineDescription.encodeCodeWordAsInput,
          MachineDescription.encodeCodeSymbolAsInput, cellCodeBits]
  rw [hcellBits]
  change
    CellListSuffixScannerDescription.runConfig
        ((scanRev.length + 4) + 4)
        (CellListSuffixScannerDescription.runConfig 6
          (config 130
            (cellListMarkingTailPayloadLeftRev baseLeft marked
              (remainingLengthTail + 1))
            (List.append ((cellCodeBits cell).map some)
              ((MachineDescription.encodeCodeWordAsInput
                restAfterCell).map some)))) =
      cellListMarkingTailConfig baseLeft (List.append marked [cell])
        (remainingLengthTail + 1) restAfterCell
  rw [run_cellList_state130_currentCell]
  rw [MachineDescription.runConfig_add]
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
              ((MachineDescription.encodeCodeWordAsInput restAfterCell).map
                some) =
            some false :: some false ::
              (MachineDescription.encodeCodeWordAsInput restAfterCell).map
                some by
        simp [cellCodeTailCells]]
      rw [run_cellList_state140_returnToLengthMarker]
      have hright :
          List.append (scanRev.reverse.map some)
              (some false :: some false ::
                (MachineDescription.encodeCodeWordAsInput restAfterCell).map
                  some) =
            List.append (tickBits.map some)
              (List.append ((stageNatBits remainingLengthTail).map some)
                (List.append
                  ((markedCellsCodeBits (List.append marked [none])).map
                    some)
                  ((MachineDescription.encodeCodeWordAsInput
                    restAfterCell).map some))) := by
        rw [map_markedCellsCodeBits_append_single marked none]
        simp [scanRev, cellListMarkingTailReturnScanRev,
          markedCellCodeBits, stageNatBits_succ, tickBits,
          MachineDescription.encodeCodeSymbolAsInput, List.map_append,
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
          MachineDescription.encodeCodeSymbolAsInput]
      unfold cellListMarkingTailConfig
      rw [hleftNext]
      simp
  | some b =>
      cases b
      · rw [show
            List.append (cellCodeTailCells (some false))
                ((MachineDescription.encodeCodeWordAsInput restAfterCell).map
                  some) =
              some false :: some true ::
                (MachineDescription.encodeCodeWordAsInput restAfterCell).map
                  some by
          simp [cellCodeTailCells]]
        rw [run_cellList_state140_returnToLengthMarker]
        have hright :
            List.append (scanRev.reverse.map some)
                (some false :: some true ::
                  (MachineDescription.encodeCodeWordAsInput restAfterCell).map
                    some) =
              List.append (tickBits.map some)
                (List.append ((stageNatBits remainingLengthTail).map some)
                  (List.append
                    ((markedCellsCodeBits
                      (List.append marked [some false])).map some)
                    ((MachineDescription.encodeCodeWordAsInput
                      restAfterCell).map some))) := by
          rw [map_markedCellsCodeBits_append_single marked (some false)]
          simp [scanRev, cellListMarkingTailReturnScanRev,
            markedCellCodeBits, stageNatBits_succ, tickBits,
            MachineDescription.encodeCodeSymbolAsInput, List.map_append,
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
            MachineDescription.encodeCodeSymbolAsInput]
        unfold cellListMarkingTailConfig
        rw [hleftNext]
        simp
      · rw [show
            List.append (cellCodeTailCells (some true))
                ((MachineDescription.encodeCodeWordAsInput restAfterCell).map
                  some) =
              some true :: some false ::
                (MachineDescription.encodeCodeWordAsInput restAfterCell).map
                  some by
          simp [cellCodeTailCells]]
        rw [run_cellList_state140_returnToLengthMarker]
        have hright :
            List.append (scanRev.reverse.map some)
                (some true :: some false ::
                  (MachineDescription.encodeCodeWordAsInput restAfterCell).map
                    some) =
              List.append (tickBits.map some)
                (List.append ((stageNatBits remainingLengthTail).map some)
                  (List.append
                    ((markedCellsCodeBits
                      (List.append marked [some true])).map some)
                    ((MachineDescription.encodeCodeWordAsInput
                      restAfterCell).map some))) := by
          rw [map_markedCellsCodeBits_append_single marked (some true)]
          simp [scanRev, cellListMarkingTailReturnScanRev,
            markedCellCodeBits, stageNatBits_succ, tickBits,
            MachineDescription.encodeCodeSymbolAsInput, List.map_append,
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
            MachineDescription.encodeCodeSymbolAsInput]
        unfold cellListMarkingTailConfig
        rw [hleftNext]
        simp

theorem cellListMarkingTail_decodeCells_none_ne_halt
    (baseLeft marked : List (Option Bool))
    (remainingCells : Nat) (tokens : Word MachineCodeSymbol)
    (hdecode :
      MachineDescription.decodeCells remainingCells tokens = none)
    (n : Nat) :
    (CellListSuffixScannerDescription.runConfig n
      (cellListMarkingTailConfig baseLeft marked remainingCells tokens)).state ≠
      CellListSuffixScannerDescription.halt := by
  induction remainingCells generalizing marked tokens n with
  | zero =>
      simp [MachineDescription.decodeCells] at hdecode
  | succ remainingTail ih =>
      cases hcell : MachineDescription.decodeCell tokens with
      | none =>
          apply
            runConfig_state_ne_halt_of_reaches_ne_halt_region
              cellListSuffixScannerDescription_haltTransitionFree
              (k := (4 * remainingTail + 4) + 4 * marked.length)
              (mid :=
                config 130
                  (cellListMarkingTailPayloadLeftRev baseLeft marked
                    remainingTail)
                  ((MachineDescription.encodeCodeWordAsInput tokens).map
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
                MachineDescription.encodeCellAppend cell restAfterCell :=
            MachineDescription.decodeCell_eq_some_encodeCellAppend hcell
          cases hrest :
              MachineDescription.decodeCells remainingTail
                restAfterCell with
          | none =>
              cases remainingTail with
              | zero =>
                  simp [MachineDescription.decodeCells, hcell] at hdecode
              | succ nextTail =>
                  rcases
                      cellListMarkingTail_mark_one
                        baseLeft marked nextTail cell restAfterCell with
                    ⟨steps, hsteps⟩
                  apply
                    runConfig_state_ne_halt_of_reaches_ne_halt_region
                      cellListSuffixScannerDescription_haltTransitionFree
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
              simp [MachineDescription.decodeCells, hcell, hrest]
                at hdecode

theorem cellListSuffixScannerDescription_runConfig_state120_tick_decodeCellList_none_ne_halt
    (baseLeft : List (Option Bool)) (rest : Word MachineCodeSymbol)
    (hdecode :
      MachineDescription.decodeCellList (MachineCodeSymbol.tick :: rest) =
        none)
    (n : Nat) :
    (CellListSuffixScannerDescription.runConfig n
      (config 120 (List.append markedTickRev baseLeft)
        ((MachineDescription.encodeCodeWordAsInput rest).map some))).state ≠
      CellListSuffixScannerDescription.halt := by
  cases hnat : MachineDescription.decodeNat rest with
  | none =>
      exact
        cellListSuffixScannerDescription_runConfig_state120_decodeNat_none_ne_halt
          rest (List.append markedTickRev baseLeft) hnat n
  | some parsedNat =>
      rcases parsedNat with ⟨remainingTail, tokensAfterLen⟩
      have hrest :
          rest =
            MachineDescription.encodeNatAppend
              remainingTail tokensAfterLen :=
        MachineDescription.decodeNat_eq_some_encodeNatAppend hnat
      rw [hrest]
      change
        (CellListSuffixScannerDescription.runConfig n
          (config 120 (List.append markedTickRev baseLeft)
            (List.map some
              (MachineDescription.encodeCodeWordAsInput
                (MachineDescription.encodeNatAppend remainingTail
                  tokensAfterLen))))).state ≠
          CellListSuffixScannerDescription.halt
      unfold MachineDescription.encodeNatAppend
      rw [MachineDescription.encodeCodeWordAsInput_append]
      have hbits :
          List.map some
              (List.append
                (MachineDescription.encodeCodeWordAsInput
                  (MachineDescription.encodeNat remainingTail))
                (MachineDescription.encodeCodeWordAsInput tokensAfterLen)) =
            List.append ((stageNatBits remainingTail).map some)
              ((MachineDescription.encodeCodeWordAsInput tokensAfterLen).map
                some) := by
        simp [stageNatBits, List.map_append]
      rw [hbits]
      cases hcells :
          MachineDescription.decodeCells (remainingTail + 1)
            tokensAfterLen with
      | none =>
          simpa [cellListMarkingTailConfig] using
            cellListMarkingTail_decodeCells_none_ne_halt
              baseLeft ([] : List (Option Bool)) (remainingTail + 1)
              tokensAfterLen hcells n
      | some _parsedCells =>
          simp [MachineDescription.decodeCellList,
            MachineDescription.decodeNat, hnat, hcells]
            at hdecode

theorem cellListSuffixScannerDescription_runConfig_state120_tick_code_inv
    (baseLeft : List (Option Bool)) (rest : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      CellListSuffixScannerDescription.runConfig n
          (config 120 (List.append markedTickRev baseLeft)
            ((MachineDescription.encodeCodeWordAsInput rest).map some)) =
        { state := CellListSuffixScannerDescription.halt
          tape := Tout }) :
    exists cells : List (Option Bool),
    exists suffix : Word MachineCodeSymbol,
      MachineCodeSymbol.tick :: rest =
        MachineDescription.encodeCellListAppend cells suffix := by
  cases hdecode :
      MachineDescription.decodeCellList (MachineCodeSymbol.tick :: rest) with
  | none =>
      have hne :=
        cellListSuffixScannerDescription_runConfig_state120_tick_decodeCellList_none_ne_halt
          baseLeft rest hdecode n
      have hstate :
          (CellListSuffixScannerDescription.runConfig n
            (config 120 (List.append markedTickRev baseLeft)
              ((MachineDescription.encodeCodeWordAsInput rest).map
                some))).state =
            CellListSuffixScannerDescription.halt := by
        simpa using congrArg MachineDescription.Configuration.state h
      exact False.elim (hne hstate)
  | some parsed =>
      rcases parsed with ⟨cells, suffix⟩
      exact
        ⟨cells, suffix,
          MachineDescription.decodeCellList_eq_some_encodeCellListAppend
            hdecode⟩

theorem cellListSuffixScannerDescription_runConfig_code_inv
    (baseLeft : List (Option Bool)) (code : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      CellListSuffixScannerDescription.runConfig n
          (config CellListSuffixScannerDescription.start baseLeft
            ((MachineDescription.encodeCodeWordAsInput code).map some)) =
        { state := CellListSuffixScannerDescription.halt
          tape := Tout }) :
    exists cells : List (Option Bool),
    exists suffix : Word MachineCodeSymbol,
      code = MachineDescription.encodeCellListAppend cells suffix := by
  rcases
      cellListSuffixScannerDescription_runConfig_start_nat_prefix_inv
        baseLeft (MachineDescription.encodeCodeWordAsInput code) h with
    ⟨doneBit, tail, hprefix⟩
  cases code with
  | nil =>
      simp [MachineDescription.encodeCodeWordAsInput] at hprefix
  | cons symbol rest =>
      cases symbol <;>
        simp [MachineDescription.encodeCodeWordAsInput,
          MachineDescription.encodeCodeSymbolAsInput] at hprefix
      · cases hprefix
      · cases hprefix
      · let c0 : MachineDescription.Configuration :=
          config CellListSuffixScannerDescription.start baseLeft
            ((MachineDescription.encodeCodeWordAsInput
              (MachineCodeSymbol.tick :: rest)).map some)
        let c1 : MachineDescription.Configuration :=
          config 120 (List.append markedTickRev baseLeft)
            ((MachineDescription.encodeCodeWordAsInput rest).map some)
        have hforward :
            CellListSuffixScannerDescription.runConfig 4 c0 = c1 := by
          dsimp [c0, c1]
          simpa [MachineDescription.encodeCodeWordAsInput,
            MachineDescription.encodeCodeSymbolAsInput, tickBits] using
            run_cellList_state100_tick baseLeft
              ((MachineDescription.encodeCodeWordAsInput rest).map some)
        have hhalt :
            CellListSuffixScannerDescription.runConfig n c0 =
              { state := CellListSuffixScannerDescription.halt
                tape := Tout } := by
          simpa [c0] using h
        rcases
            runConfig_forward_inv CellListSuffixScannerDescription
              c0 c1 n 4 hhalt hforward
              cellListSuffixScannerDescription_haltTransitionFree with
          ⟨_m, _hm_le, hm_halt⟩
        exact
          cellListSuffixScannerDescription_runConfig_state120_tick_code_inv
            baseLeft rest hm_halt
      · exact ⟨[], rest, by
          simp [MachineDescription.encodeCellListAppend,
            MachineDescription.encodeNatAppend,
            MachineDescription.encodeNat,
            MachineDescription.encodeCellsAppend]⟩
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
      MachineDescription.encodeCodeWordAsInput suffix =
        false :: suffixTail)
    (h :
      CellListSuffixScannerDescription.runConfig n
          (config CellListSuffixScannerDescription.start baseLeft
            ((MachineDescription.encodeCodeWordAsInput
              (MachineDescription.encodeCellListAppend cells
                suffix)).map some)) =
        { state := CellListSuffixScannerDescription.halt
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
    (CellListSuffixScannerDescription.runConfig n
      (cellListCanonicalFinishStartConfigWithBase cells baseLeft [])).state ≠
      CellListSuffixScannerDescription.halt := by
  let stuck : MachineDescription.Configuration :=
    config 150
      (cellListCanonicalRestoredLeftWithBase cells baseLeft)
      ([] : List (Option Bool))
  apply
    primitive_runConfig_state_ne_halt_of_reaches_stuck
      cellListSuffixScannerDescription_haltTransitionFree
      (D := CellListSuffixScannerDescription)
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
      MachineDescription.stepConfig, MachineDescription.lookupTransition,
      MachineDescription.Matches, MachineDescription.transition, Tape.read]
  · change (150 : Nat) ≠ 999
    omega

theorem cellListCanonicalFinishStartConfigWithBase_moveRight_suffix_ne_halt
    (cells baseLeft : List (Option Bool)) (tail : Word Bool) (n : Nat) :
    (CellListSuffixScannerDescription.runConfig n
      (cellListCanonicalFinishStartConfigWithBase cells baseLeft
        (true :: false :: false :: false :: tail))).state ≠
      CellListSuffixScannerDescription.halt := by
  let stuck : MachineDescription.Configuration :=
    CellListSuffixScannerDescription.runConfig 1
      (config 150
        (cellListCanonicalRestoredLeftWithBase cells baseLeft)
        ((true :: false :: false :: false :: tail).map some))
  apply
    primitive_runConfig_state_ne_halt_of_reaches_stuck
      cellListSuffixScannerDescription_haltTransitionFree
      (D := CellListSuffixScannerDescription)
      (c :=
        cellListCanonicalFinishStartConfigWithBase cells baseLeft
          (true :: false :: false :: false :: tail))
      (stuck := stuck)
      (k := 4 * cells.length + 1) (n := n)
  · rw [show 4 * cells.length + 1 = 4 * cells.length + 1 by rfl]
    rw [MachineDescription.runConfig_add]
    unfold stuck cellListCanonicalFinishStartConfigWithBase
    rw [show
        CellListSuffixScannerDescription.runConfig (4 * cells.length)
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
        MachineDescription.runConfig, MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition, Tape.read, Tape.write, Tape.move,
        Tape.moveRight]
  · unfold stuck
    change
      (CellListSuffixScannerDescription.runConfig 1
        (config 150
          (cellListCanonicalRestoredLeftWithBase cells baseLeft)
          ((true :: false :: false :: false :: tail).map some))).state ≠
        999
    cases tail <;>
      simp [CellListSuffixScannerDescription, config, tapeAtCells,
        keep, keepMove, writeMove, scanLeftToSentinelRestart,
        MachineDescription.runConfig, MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition, Tape.read, Tape.write, Tape.move,
        Tape.moveRight]

theorem cellListSuffixScannerDescription_runConfig_encodeCellListAppend_suffix_false
    (baseLeft cells : List (Option Bool))
    (suffix : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      CellListSuffixScannerDescription.runConfig n
          (config CellListSuffixScannerDescription.start baseLeft
            ((MachineDescription.encodeCodeWordAsInput
              (MachineDescription.encodeCellListAppend cells suffix)).map
              some)) =
        { state := CellListSuffixScannerDescription.halt
          tape := Tout }) :
    exists suffixTail : Word Bool,
      MachineDescription.encodeCodeWordAsInput suffix =
        false :: suffixTail := by
  let suffixBits := MachineDescription.encodeCodeWordAsInput suffix
  cases suffix with
  | nil =>
      have hstate :
          (CellListSuffixScannerDescription.runConfig n
            (config CellListSuffixScannerDescription.start baseLeft
              ((MachineDescription.encodeCodeWordAsInput
                (MachineDescription.encodeCellListAppend cells
                  ([] : Word MachineCodeSymbol))).map some))).state =
            CellListSuffixScannerDescription.halt := by
        simpa using congrArg MachineDescription.Configuration.state h
      rcases
          run_cellList_raw_marking_loop_from_state100_withBase
            baseLeft ([] : List (Option Bool)) cells
            ([] : Word Bool) with
        ⟨steps, hsteps⟩
      have hprefix :
          CellListSuffixScannerDescription.runConfig steps
              (config CellListSuffixScannerDescription.start baseLeft
                ((MachineDescription.encodeCodeWordAsInput
                  (MachineDescription.encodeCellListAppend cells
                    ([] : Word MachineCodeSymbol))).map some)) =
          cellListCanonicalFinishStartConfigWithBase cells baseLeft
              ([] : Word Bool) := by
        simpa [CellListSuffixScannerDescription, cellListBits_eq_encodeCellListAppend,
          cellListFieldBits, cellListCanonicalLengthPrefixRev,
          markedCellsCodeBits, MachineDescription.encodeCodeWordAsInput,
          List.map_append, List.append_assoc] using hsteps
      exact False.elim
        ((runConfig_state_ne_halt_of_reaches_ne_halt_region
            cellListSuffixScannerDescription_haltTransitionFree
            hprefix
            (by
              intro m
              simpa [suffixBits,
                MachineDescription.encodeCodeWordAsInput] using
                cellListCanonicalFinishStartConfigWithBase_nil_suffix_ne_halt
                  cells baseLeft m)
            (n := n)) hstate)
  | cons symbol rest =>
      cases symbol with
      | moveRight =>
          have hstate :
              (CellListSuffixScannerDescription.runConfig n
                (config CellListSuffixScannerDescription.start baseLeft
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineDescription.encodeCellListAppend cells
                      (MachineCodeSymbol.moveRight :: rest))).map some))).state =
                CellListSuffixScannerDescription.halt := by
            simpa using congrArg MachineDescription.Configuration.state h
          rcases
              run_cellList_raw_marking_loop_from_state100_withBase
                baseLeft ([] : List (Option Bool)) cells
                (MachineDescription.encodeCodeWordAsInput
                  (MachineCodeSymbol.moveRight :: rest)) with
            ⟨steps, hsteps⟩
          have hprefix :
              CellListSuffixScannerDescription.runConfig steps
                  (config CellListSuffixScannerDescription.start baseLeft
                    ((MachineDescription.encodeCodeWordAsInput
                      (MachineDescription.encodeCellListAppend cells
                        (MachineCodeSymbol.moveRight :: rest))).map some)) =
                cellListCanonicalFinishStartConfigWithBase cells baseLeft
                  (MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.moveRight :: rest)) := by
            simpa [CellListSuffixScannerDescription,
              cellListBits_eq_encodeCellListAppend, cellListFieldBits,
              cellListCanonicalLengthPrefixRev, markedCellsCodeBits,
              List.map_append, List.append_assoc] using hsteps
          exact False.elim
            ((runConfig_state_ne_halt_of_reaches_ne_halt_region
                cellListSuffixScannerDescription_haltTransitionFree
                hprefix
                (by
                  intro m
                  simpa [suffixBits, MachineDescription.encodeCodeWordAsInput,
                    MachineDescription.encodeCodeSymbolAsInput] using
                    cellListCanonicalFinishStartConfigWithBase_moveRight_suffix_ne_halt
                      cells baseLeft
                      (MachineDescription.encodeCodeWordAsInput rest) m)
                (n := n)) hstate)
      | header =>
          refine ⟨false :: false :: false ::
            MachineDescription.encodeCodeWordAsInput rest, ?_⟩
          simp [MachineDescription.encodeCodeWordAsInput,
            MachineDescription.encodeCodeSymbolAsInput]
      | transition =>
          refine ⟨false :: false :: true ::
            MachineDescription.encodeCodeWordAsInput rest, ?_⟩
          simp [MachineDescription.encodeCodeWordAsInput,
            MachineDescription.encodeCodeSymbolAsInput]
      | tick =>
          refine ⟨false :: true :: false ::
            MachineDescription.encodeCodeWordAsInput rest, ?_⟩
          simp [MachineDescription.encodeCodeWordAsInput,
            MachineDescription.encodeCodeSymbolAsInput]
      | done =>
          refine ⟨false :: true :: true ::
            MachineDescription.encodeCodeWordAsInput rest, ?_⟩
          simp [MachineDescription.encodeCodeWordAsInput,
            MachineDescription.encodeCodeSymbolAsInput]
      | blank =>
          refine ⟨true :: false :: false ::
            MachineDescription.encodeCodeWordAsInput rest, ?_⟩
          simp [MachineDescription.encodeCodeWordAsInput,
            MachineDescription.encodeCodeSymbolAsInput]
      | zero =>
          refine ⟨true :: false :: true ::
            MachineDescription.encodeCodeWordAsInput rest, ?_⟩
          simp [MachineDescription.encodeCodeWordAsInput,
            MachineDescription.encodeCodeSymbolAsInput]
      | one =>
          refine ⟨true :: true :: false ::
            MachineDescription.encodeCodeWordAsInput rest, ?_⟩
          simp [MachineDescription.encodeCodeWordAsInput,
            MachineDescription.encodeCodeSymbolAsInput]
      | moveLeft =>
          refine ⟨true :: true :: true ::
            MachineDescription.encodeCodeWordAsInput rest, ?_⟩
          simp [MachineDescription.encodeCodeWordAsInput,
            MachineDescription.encodeCodeSymbolAsInput]

end DovetailLayoutScanner
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC
