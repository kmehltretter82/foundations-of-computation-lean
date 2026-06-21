import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.Basic

set_option doc.verso true

/-!
# Boolean-word suffix scanner

This module contains the input-field specialization of the cell-list scanner.
It has the same length-prefix marking loop as
{name (full := FoC.Computability.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.CellListSuffixScannerDescription)}`CellListSuffixScannerDescription`, but it rejects payload cells encoded
as {lit}`blank`.  This matches
{name (full := FoC.Computability.MachineDescription.decodeBoolWord)}`MachineDescription.decodeBoolWord`,
which is the field decoder used by
{name (full := FoC.Computability.MachineDescription.DovetailLayout.decode)}`MachineDescription.DovetailLayout.decode`.
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace CanonicalLayouts
namespace DovetailLayoutScanner

open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

def BoolWordSuffixScannerDescription : MachineDescription where
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

theorem boolWordSuffixScannerDescription_wellFormed :
    BoolWordSuffixScannerDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · intro t ht
    exact transition_wellFormed_of_all
      (l := BoolWordSuffixScannerDescription.transitions)
      (stateCount := BoolWordSuffixScannerDescription.stateCount)
      (by
        native_decide) t ht
  · intro t u ht hu hkey
    exact transition_deterministic_of_all
      (l := BoolWordSuffixScannerDescription.transitions)
      (by
        native_decide) t u ht hu hkey

theorem boolWordSuffixScannerDescription_haltTransitionFree :
    BoolWordSuffixScannerDescription.HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l := BoolWordSuffixScannerDescription.transitions)
    (state := BoolWordSuffixScannerDescription.halt)
    (by
      native_decide) t ht

theorem boolWordSuffixScannerDescription_subroutineReady :
    BoolWordSuffixScannerDescription.SubroutineReady :=
  ⟨boolWordSuffixScannerDescription_wellFormed,
    boolWordSuffixScannerDescription_haltTransitionFree⟩

theorem boolWordSuffixScannerDescription_initial_eq_config
    (bits : Word Bool) :
    BoolWordSuffixScannerDescription.initial bits =
      config 100 [] (bits.map some) := by
  cases bits <;> rfl

theorem boolWordSuffix_lookup_150_false :
    BoolWordSuffixScannerDescription.lookupTransition 150 (some false) =
      some (keepMove 150 (some false) Direction.left
        BoolWordSuffixScannerDescription.halt) := by
  native_decide

theorem run_boolWordSuffix_state130_currentBit
    (bit : Bool) (left right : List (Option Bool)) :
    BoolWordSuffixScannerDescription.runConfig 6
        (config 130 left
          (List.append ((cellCodeBits (some bit)).map some) right)) =
      config 140 (some true :: some true :: left)
        (List.append (cellCodeTailCells (some bit)) right) := by
  cases bit <;> cases right <;>
    simp [BoolWordSuffixScannerDescription, cellCodeBits,
      cellCodeTailCells, config, tapeAtCells, keep, keepMove,
      writeMove, scanLeftToSentinelRestart,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition,
      MachineDescription.encodeCell,
      MachineDescription.encodeCodeWordAsInput,
      MachineDescription.encodeCodeSymbolAsInput,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem run_boolWordSuffix_state100_tick
    (left tail : List (Option Bool)) :
    BoolWordSuffixScannerDescription.runConfig 4
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

theorem run_boolWordSuffix_state100_done
    (left tail : List (Option Bool)) :
    BoolWordSuffixScannerDescription.runConfig 4
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

theorem run_boolWordSuffix_state120_tick
    (left right : List (Option Bool)) :
    BoolWordSuffixScannerDescription.runConfig 4
        (config 120 left
          (List.append (tickBits.map some) right)) =
      config 120
        (List.append (tickBits.reverse.map some) left) right := by
  cases right <;>
  simp [BoolWordSuffixScannerDescription, tickBits,
    config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition,
    MachineDescription.encodeCodeSymbolAsInput,
    Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem run_boolWordSuffix_state120_done
    (left right : List (Option Bool)) :
    BoolWordSuffixScannerDescription.runConfig 4
        (config 120 left
          (List.append (doneBits.map some) right)) =
      config 130
        (List.append (doneBits.reverse.map some) left) right := by
  cases right <;>
  simp [BoolWordSuffixScannerDescription, doneBits,
    config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition,
    MachineDescription.encodeCodeSymbolAsInput,
    Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem run_boolWordSuffix_state120_stageNat
    (n : Nat) (left right : List (Option Bool)) :
    BoolWordSuffixScannerDescription.runConfig (4 * n + 4)
        (config 120 left
          (List.append ((stageNatBits n).map some) right)) =
      config 130
        (List.append ((stageNatBits n).reverse.map some) left)
        right := by
  induction n generalizing left with
  | zero =>
      simpa [stageNatBits_zero] using
        run_boolWordSuffix_state120_done left right
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
      rw [run_boolWordSuffix_state120_tick]
      rw [ih]
      simp [stageNatBits_succ, tickBits,
        MachineDescription.encodeCodeSymbolAsInput,
        List.map_append, List.append_assoc]

theorem run_boolWordSuffix_state130_markedBit
    (bit : Bool) (left right : List (Option Bool)) :
    BoolWordSuffixScannerDescription.runConfig 4
        (config 130 left
          (List.append ((markedCellCodeBits (some bit)).map some) right)) =
      config 130
        (List.append ((markedCellCodeBits (some bit)).reverse.map some)
          left)
        right := by
  cases bit <;> cases right <;>
    simp [BoolWordSuffixScannerDescription, markedCellCodeBits,
      config, tapeAtCells, keep, keepMove, writeMove,
      scanLeftToSentinelRestart,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem run_boolWordSuffix_state130_markedBits
    (processed : Word Bool) (left right : List (Option Bool)) :
    BoolWordSuffixScannerDescription.runConfig
        (4 * processed.length)
        (config 130 left
          (List.append
            ((markedCellsCodeBits (processed.map some)).map some)
            right)) =
      config 130
        (List.append
          ((markedCellsCodeBits (processed.map some)).reverse.map some)
          left)
        right := by
  induction processed generalizing left with
  | nil =>
      rfl
  | cons bit rest ih =>
      rw [show 4 * (bit :: rest).length =
          4 + 4 * rest.length by simp; omega]
      rw [MachineDescription.runConfig_add]
      rw [show
          List.append
              ((markedCellsCodeBits ((bit :: rest).map some)).map some)
              right =
            List.append ((markedCellCodeBits (some bit)).map some)
              (List.append
                ((markedCellsCodeBits (rest.map some)).map some)
                right) by
          simp [markedCellsCodeBits, List.map_append, List.append_assoc]]
      rw [run_boolWordSuffix_state130_markedBit]
      rw [ih]
      simp [markedCellsCodeBits, List.reverse_append, List.map_append,
        List.append_assoc]

theorem run_boolWordSuffix_state140_returnToLengthMarker
    (scanRev : Word Bool) (headBit : Bool)
    (leftTail right : List (Option Bool)) :
    BoolWordSuffixScannerDescription.runConfig
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
        simp [BoolWordSuffixScannerDescription, config, tapeAtCells,
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
        BoolWordSuffixScannerDescription.runConfig (rest.length + 4)
          (BoolWordSuffixScannerDescription.runConfig 1
            (config 140
              (some b :: List.append (List.map some rest)
                (none :: some true :: leftTail))
              (some headBit :: right))) =
          config 100 (some false :: some true :: leftTail)
            (List.append (List.map some (b :: rest).reverse)
              (some headBit :: right))
      rw [show
          BoolWordSuffixScannerDescription.runConfig 1
            (config 140
              (some b :: List.append (List.map some rest)
                (none :: some true :: leftTail))
              (some headBit :: right)) =
          config 140
            (List.append (List.map some rest)
              (none :: some true :: leftTail))
            (some b :: some headBit :: right) by
        cases headBit <;> cases b <;> cases right <;>
        simp [BoolWordSuffixScannerDescription,
          config, tapeAtCells, keep, keepMove, writeMove,
          scanLeftToSentinelRestart,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft]]
      rw [ih]
      simp [List.map_append, List.append_assoc]

theorem run_boolWordSuffix_state150_markedBit
    (bit : Bool) (left right : List (Option Bool)) :
    BoolWordSuffixScannerDescription.runConfig 4
        (config 150 left
          (List.append ((markedCellCodeBits (some bit)).map some) right)) =
      config 150
        (List.append ((cellCodeBits (some bit)).reverse.map some) left)
        right := by
  cases bit <;> cases right <;>
    simp [BoolWordSuffixScannerDescription, markedCellCodeBits,
      cellCodeBits, config, tapeAtCells, keep, keepMove, writeMove,
      scanLeftToSentinelRestart,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, MachineDescription.encodeCell,
      MachineDescription.encodeCodeWordAsInput,
      MachineDescription.encodeCodeSymbolAsInput,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem run_boolWordSuffix_state150_markedBits
    (cells : Word Bool) (left right : List (Option Bool)) :
    BoolWordSuffixScannerDescription.runConfig
        (4 * cells.length)
        (config 150 left
          (List.append
            ((markedCellsCodeBits (cells.map some)).map some)
            right)) =
      config 150
        (List.append ((cellsCodeBits (cells.map some)).reverse.map some)
          left)
        right := by
  induction cells generalizing left with
  | nil =>
      rfl
  | cons bit rest ih =>
      rw [show 4 * (bit :: rest).length =
          4 + 4 * rest.length by simp; omega]
      rw [MachineDescription.runConfig_add]
      rw [show
          List.append
              ((markedCellsCodeBits ((bit :: rest).map some)).map some)
              right =
            List.append ((markedCellCodeBits (some bit)).map some)
              (List.append
                ((markedCellsCodeBits (rest.map some)).map some)
                right) by
          simp [markedCellsCodeBits, List.map_append, List.append_assoc]]
      rw [run_boolWordSuffix_state150_markedBit]
      rw [ih]
      simp [cellsCodeBits, List.reverse_append, List.map_append,
        List.append_assoc]

theorem run_boolWordSuffix_raw_mark_current_to_state100_withBase
    (baseLeft : List (Option Bool)) (processed : Word Bool)
    (bit : Bool) (rest : Word Bool) (suffixBits : Word Bool) :
    exists steps : Nat,
      BoolWordSuffixScannerDescription.runConfig steps
          (cellListRawMarkingState120WithBase baseLeft
            (processed.map some) (some bit) (rest.map some) suffixBits) =
        cellListRawState100AfterMarkedWithBase baseLeft
          (processed.map some) (some bit) (rest.map some) suffixBits := by
  let scanRev := cellListMarkingReturnScanRev
    (processed.map some) (rest.map some)
  refine
    ⟨(4 * rest.length + 4) +
        (4 * processed.length + (6 + (scanRev.length + 4))), ?_⟩
  rw [MachineDescription.runConfig_add]
  unfold cellListRawMarkingState120WithBase
  simp only [List.length_map]
  rw [run_boolWordSuffix_state120_stageNat]
  rw [MachineDescription.runConfig_add]
  rw [run_boolWordSuffix_state130_markedBits]
  rw [MachineDescription.runConfig_add]
  rw [run_boolWordSuffix_state130_currentBit]
  cases bit
  · have hreturn :=
      run_boolWordSuffix_state140_returnToLengthMarker scanRev false
        (some false :: some false ::
          List.append
            (cellListCanonicalLengthPrefixRev processed.length)
            baseLeft)
        (some true ::
          List.append ((cellsCodeBits (rest.map some)).map some)
            (suffixBits.map some))
    simpa [cellListRawState100AfterMarkedWithBase, scanRev,
      cellListMarkingReturnScanRev, markedCellCodeBits,
      cellCodeTailCells, cellListCanonicalLengthPrefixRev,
      List.map_append, List.reverse_append, List.append_assoc] using
        hreturn
  · have hreturn :=
      run_boolWordSuffix_state140_returnToLengthMarker scanRev true
        (some false :: some false ::
          List.append
            (cellListCanonicalLengthPrefixRev processed.length)
            baseLeft)
        (some false ::
          List.append ((cellsCodeBits (rest.map some)).map some)
            (suffixBits.map some))
    simpa [cellListRawState100AfterMarkedWithBase, scanRev,
      cellListMarkingReturnScanRev, markedCellCodeBits,
      cellCodeTailCells, cellListCanonicalLengthPrefixRev,
      List.map_append, List.reverse_append, List.append_assoc] using
        hreturn

theorem run_boolWordSuffix_raw_marking_loop_from_state100_withBase
    (baseLeft : List (Option Bool)) (processed cells : Word Bool)
    (suffixBits : Word Bool) :
    exists steps : Nat,
      BoolWordSuffixScannerDescription.runConfig steps
          (config 100
            (List.append
              (cellListCanonicalLengthPrefixRev processed.length)
              baseLeft)
            (List.append ((stageNatBits cells.length).map some)
              (List.append
                ((markedCellsCodeBits (processed.map some)).map some)
                (List.append ((cellsCodeBits (cells.map some)).map some)
                  (suffixBits.map some))))) =
        cellListCanonicalFinishStartConfigWithBase
          ((List.append processed cells).map some) baseLeft suffixBits := by
  induction cells generalizing processed with
  | nil =>
      refine ⟨4, ?_⟩
      rw [show (stageNatBits ([] : Word Bool).length).map some =
          doneBits.map some by
        simp [stageNatBits_zero, doneBits,
          MachineDescription.encodeCodeSymbolAsInput]]
      change
        BoolWordSuffixScannerDescription.runConfig 4
            (config 100
              (List.append
                (cellListCanonicalLengthPrefixRev processed.length)
                baseLeft)
              (List.append (doneBits.map some)
                (List.append
                  ((markedCellsCodeBits (processed.map some)).map some)
                  (suffixBits.map some)))) =
          cellListCanonicalFinishStartConfigWithBase
            ((List.append processed []).map some) baseLeft suffixBits
      rw [run_boolWordSuffix_state100_done]
      simp [cellListCanonicalFinishStartConfigWithBase,
        cellListCanonicalFinishStartLeftWithBase]
  | cons bit rest ih =>
      rcases run_boolWordSuffix_raw_mark_current_to_state100_withBase
          baseLeft processed bit rest suffixBits with
        ⟨markSteps, hmark⟩
      rcases ih (List.append processed [bit]) with
        ⟨recSteps, hrec⟩
      refine ⟨4 + markSteps + recSteps, ?_⟩
      rw [show 4 + markSteps + recSteps =
          4 + (markSteps + recSteps) by omega]
      rw [MachineDescription.runConfig_add]
      rw [show
          (stageNatBits (bit :: rest).length).map some =
            List.append (tickBits.map some)
              ((stageNatBits rest.length).map some) by
        simp [stageNatBits_succ, tickBits,
          MachineDescription.encodeCodeSymbolAsInput]]
      rw [show
          List.append
              (List.append (tickBits.map some)
                ((stageNatBits rest.length).map some))
              (List.append
                ((markedCellsCodeBits (processed.map some)).map some)
                (List.append
                  ((cellsCodeBits ((bit :: rest).map some)).map some)
                  (suffixBits.map some))) =
            List.append (tickBits.map some)
              (List.append ((stageNatBits rest.length).map some)
                (List.append
                  ((markedCellsCodeBits (processed.map some)).map some)
                  (List.append ((cellCodeBits (some bit)).map some)
                    (List.append
                      ((cellsCodeBits (rest.map some)).map some)
                      (suffixBits.map some))))) by
        simp [cellsCodeBits, List.map_append, List.append_assoc]]
      change
        BoolWordSuffixScannerDescription.runConfig (markSteps + recSteps)
            (BoolWordSuffixScannerDescription.runConfig 4
              (config 100
                (List.append
                  (cellListCanonicalLengthPrefixRev processed.length)
                  baseLeft)
                (List.append (tickBits.map some)
                  (List.append ((stageNatBits rest.length).map some)
                    (List.append
                      ((markedCellsCodeBits (processed.map some)).map some)
                      (List.append ((cellCodeBits (some bit)).map some)
                        (List.append
                          ((cellsCodeBits (rest.map some)).map some)
                          (suffixBits.map some)))))))) =
          cellListCanonicalFinishStartConfigWithBase
            ((List.append processed (bit :: rest)).map some) baseLeft
            suffixBits
      rw [run_boolWordSuffix_state100_tick]
      rw [MachineDescription.runConfig_add]
      rw [show
          config 120
              (List.append markedTickRev
                (List.append
                  (cellListCanonicalLengthPrefixRev processed.length)
                  baseLeft))
              (List.append ((stageNatBits rest.length).map some)
                (List.append
                  ((markedCellsCodeBits (processed.map some)).map some)
                  (List.append ((cellCodeBits (some bit)).map some)
                    (List.append
                      ((cellsCodeBits (rest.map some)).map some)
                      (suffixBits.map some))))) =
            cellListRawMarkingState120WithBase baseLeft
              (processed.map some) (some bit) (rest.map some)
              suffixBits by
        simp [cellListRawMarkingState120WithBase]]
      rw [hmark]
      rw [show (List.append processed [bit]).map some =
          List.append (processed.map some) [some bit] by
        simp [List.map_append]] at hrec
      rw [map_markedCellsCodeBits_append_single
        (processed.map some) (some bit)] at hrec
      have hrec' := hrec
      simpa [cellListRawState100AfterMarkedWithBase,
        markedCellsCodeBits, markedCellsCodeBits_append, cellsCodeBits,
        List.length_append, List.map_append, List.append_assoc] using hrec'

theorem run_boolWordSuffix_state150_handoff_false
    (cell : Option Bool) (left right : List (Option Bool)) :
    BoolWordSuffixScannerDescription.runConfig 1
        (config 150 (cell :: left) (some false :: right)) =
      config BoolWordSuffixScannerDescription.halt left
        (cell :: some false :: right) := by
  cases cell <;> cases right <;>
    simp [config, tapeAtCells, keepMove,
      boolWordSuffix_lookup_150_false,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.transition,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem run_boolWordSuffix_canonical_finish_to_handoff_withBase
    (w : Word Bool) (baseLeft : List (Option Bool))
    (suffixTail : Word Bool) :
    exists steps : Nat,
      BoolWordSuffixScannerDescription.runConfig steps
          (cellListCanonicalFinishStartConfigWithBase
            (w.map some) baseLeft (false :: suffixTail)) =
        { state := BoolWordSuffixScannerDescription.halt
          tape :=
            (boolWordCanonicalHandoffConfigWithBase w baseLeft
              (false :: suffixTail)).tape } := by
  refine ⟨4 * w.length + 1, ?_⟩
  rw [MachineDescription.runConfig_add]
  unfold cellListCanonicalFinishStartConfigWithBase
  rw [run_boolWordSuffix_state150_markedBits]
  change
    BoolWordSuffixScannerDescription.runConfig 1
      (config 150
        (cellListCanonicalRestoredLeftWithBase (w.map some) baseLeft)
        (some false :: suffixTail.map some)) =
      { state := BoolWordSuffixScannerDescription.halt
        tape :=
          (boolWordCanonicalHandoffConfigWithBase w baseLeft
            (false :: suffixTail)).tape }
  unfold boolWordCanonicalHandoffConfigWithBase
  unfold cellListCanonicalHandoffConfigWithBase
  cases hleft : cellListCanonicalRestoredLeftWithBase
      (w.map some) baseLeft with
  | nil =>
      simp [config, tapeAtCells,
        boolWordSuffix_lookup_150_false, keepMove,
        MachineDescription.runConfig, MachineDescription.stepConfig,
        MachineDescription.transition, Tape.read, Tape.write,
        Tape.move, Tape.moveLeft]
  | cons cell left =>
      simpa [config, tapeAtCells, hleft] using
        run_boolWordSuffix_state150_handoff_false cell left
          (suffixTail.map some)

theorem run_boolWordSuffix_raw_to_canonical_handoff_withBase
    (w : Word Bool) (baseLeft : List (Option Bool))
    (suffixTail : Word Bool) :
    exists steps : Nat,
      BoolWordSuffixScannerDescription.runConfig steps
          (config 100 baseLeft
            (List.append ((stageNatBits w.length).map some)
              (List.append ((cellsCodeBits (w.map some)).map some)
                (some false :: suffixTail.map some)))) =
        { state := BoolWordSuffixScannerDescription.halt
          tape :=
            (boolWordCanonicalHandoffConfigWithBase w baseLeft
              (false :: suffixTail)).tape } := by
  rcases run_boolWordSuffix_raw_marking_loop_from_state100_withBase
      baseLeft ([] : Word Bool) w (false :: suffixTail) with
    ⟨markSteps, hmark⟩
  have hmark' :
      BoolWordSuffixScannerDescription.runConfig markSteps
          (config 100 baseLeft
            (List.append ((stageNatBits w.length).map some)
              (List.append ((cellsCodeBits (w.map some)).map some)
                (some false :: suffixTail.map some)))) =
        cellListCanonicalFinishStartConfigWithBase
          (w.map some) baseLeft (false :: suffixTail) := by
    simpa using hmark
  rcases run_boolWordSuffix_canonical_finish_to_handoff_withBase
      w baseLeft suffixTail with
    ⟨finishSteps, hfinish⟩
  refine ⟨markSteps + finishSteps, ?_⟩
  rw [MachineDescription.runConfig_add]
  rw [hmark']
  exact hfinish

end DovetailLayoutScanner
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC
