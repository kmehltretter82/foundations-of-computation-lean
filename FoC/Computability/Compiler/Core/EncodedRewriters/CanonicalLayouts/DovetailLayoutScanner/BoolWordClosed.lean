import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.PrimitiveClosed

set_option doc.verso true

/-!
# Bool-word closed scanner inversions

The bool-word scanner is the first length-prefixed payload in a checked
dovetail-layout scan.  This module keeps the code-origin closed inversions for
that scanner separate from the primitive field facts in
{module}`FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.PrimitiveClosed`.
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

private abbrev BWSS := BoolWordSuffixScannerDescription
private theorem BWSS_htf : BWSS.HaltTransitionFree :=
  boolWordSuffixScannerDescription_haltTransitionFree

theorem boolWordSuffixScannerDescription_ne_halt_of_reaches_ne_halt_region
    {c mid : Configuration} {k n : Nat}
    (hrun :
      BWSS.runConfig k c = mid)
    (hmid :
      forall m : Nat,
        (BWSS.runConfig m mid).state ≠
          BWSS.halt) :
    (BWSS.runConfig n c).state ≠
      BWSS.halt :=
  CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_ne_halt_region
    BWSS_htf hrun hmid

theorem boolWordSuffixScannerDescription_runConfig_state120_decodeNat_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : decodeNat tokens = none) (n : Nat) :
    (BWSS.runConfig n
      (config 120 leftRev
        ((encodeCodeWordAsInput tokens).map some))).state ≠
      BWSS.halt := by
  induction tokens generalizing leftRev n with
  | nil =>
      exact
        primitive_runConfig_state_ne_halt_of_reaches_stuck
          BWSS_htf
          (D := BWSS)
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
              BWSS_htf
              (D := BWSS)
              (c :=
                config 120 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.header :: rest)).map some))
              (stuck :=
                BWSS.runConfig 2
                  (config 120 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.header :: rest)).map some)))
              (k := 2) (n := n)
              rfl
              (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
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
              BWSS_htf
              (D := BWSS)
              (c :=
                config 120 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.transition :: rest)).map some))
              (stuck :=
                BWSS.runConfig 2
                  (config 120 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.transition :: rest)).map some)))
              (k := 2) (n := n)
              rfl
              (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
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
                boolWordSuffixScannerDescription_ne_halt_of_reaches_ne_halt_region
                  (k := 4)
                  (mid :=
                    config 120
                      (List.append (tickBits.reverse.map some) leftRev)
                      ((encodeCodeWordAsInput rest).map
                        some))
              · simpa [tickBits, encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput] using
                  run_boolWordSuffix_state120_tick leftRev
                    ((encodeCodeWordAsInput rest).map some)
              · intro m
                exact ih
                  (List.append (tickBits.reverse.map some) leftRev)
                  hrest m
          | some parsed =>
              simp [hrest] at hdecode
      | done =>
          simp [decodeNat] at hdecode
      | blank =>
          exact
            primitive_runConfig_state_ne_halt_of_reaches_stuck
              BWSS_htf
              (D := BWSS)
              (c :=
                config 120 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.blank :: rest)).map some))
              (stuck :=
                BWSS.runConfig 1
                  (config 120 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.blank :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
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
              BWSS_htf
              (D := BWSS)
              (c :=
                config 120 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.zero :: rest)).map some))
              (stuck :=
                BWSS.runConfig 1
                  (config 120 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.zero :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
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
              BWSS_htf
              (D := BWSS)
              (c :=
                config 120 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.one :: rest)).map some))
              (stuck :=
                BWSS.runConfig 1
                  (config 120 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.one :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
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
              BWSS_htf
              (D := BWSS)
              (c :=
                config 120 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.moveLeft :: rest)).map some))
              (stuck :=
                BWSS.runConfig 1
                  (config 120 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.moveLeft :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
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
              BWSS_htf
              (D := BWSS)
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
                simp [BoolWordSuffixScannerDescription, config,
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

theorem boolWordSuffixScannerDescription_runConfig_state130_decodeCell_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : decodeCell tokens = none) (n : Nat) :
    (BWSS.runConfig n
      (config 130 leftRev
        ((encodeCodeWordAsInput tokens).map some))).state ≠
      BWSS.halt := by
  cases tokens with
  | nil =>
      exact
        primitive_runConfig_state_ne_halt_of_reaches_stuck
          BWSS_htf
          (D := BWSS)
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
              BWSS_htf
              (D := BWSS)
              (c :=
                config 130 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.header :: rest)).map some))
              (stuck :=
                BWSS.runConfig 1
                  (config 130 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.header :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
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
              BWSS_htf
              (D := BWSS)
              (c :=
                config 130 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.transition :: rest)).map some))
              (stuck :=
                BWSS.runConfig 1
                  (config 130 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.transition :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
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
              BWSS_htf
              (D := BWSS)
              (c :=
                config 130 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.tick :: rest)).map some))
              (stuck :=
                BWSS.runConfig 1
                  (config 130 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.tick :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
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
              BWSS_htf
              (D := BWSS)
              (c :=
                config 130 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.done :: rest)).map some))
              (stuck :=
                BWSS.runConfig 1
                  (config 130 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.done :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
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
              BWSS_htf
              (D := BWSS)
              (c :=
                config 130 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.moveLeft :: rest)).map some))
              (stuck :=
                BWSS.runConfig 5
                  (config 130 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.moveLeft :: rest)).map some)))
              (k := 5) (n := n)
              rfl
              (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
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
                change (145 : Nat) ≠ 999
                omega)
      | moveRight =>
          exact
            primitive_runConfig_state_ne_halt_of_reaches_stuck
              BWSS_htf
              (D := BWSS)
              (c :=
                config 130 leftRev
                  ((encodeCodeWordAsInput
                    (MachineCodeSymbol.moveRight :: rest)).map some))
              (stuck :=
                BWSS.runConfig 1
                  (config 130 leftRev
                    ((encodeCodeWordAsInput
                      (MachineCodeSymbol.moveRight :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
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

theorem boolWordSuffixScannerDescription_runConfig_state130_blank_cell_ne_halt
    (suffix : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (n : Nat) :
    (BWSS.runConfig n
      (config 130 leftRev
        ((encodeCodeWordAsInput
          (encodeCellAppend none suffix)).map some))).state ≠
      BWSS.halt := by
  exact
    primitive_runConfig_state_ne_halt_of_reaches_stuck
      BWSS_htf
      (D := BWSS)
      (c :=
        config 130 leftRev
          ((encodeCodeWordAsInput
            (encodeCellAppend none suffix)).map some))
      (stuck :=
        BWSS.runConfig 5
          (config 130 leftRev
            ((encodeCodeWordAsInput
              (encodeCellAppend none suffix)).map some)))
      (k := 5) (n := n)
      rfl
      (by
        cases suffix <;>
        simp [BoolWordSuffixScannerDescription, config, tapeAtCells,
          keep, keepMove, writeMove, scanLeftToSentinelRestart,
          runConfig,
          stepConfig,
          lookupTransition, Matches,
          transition, encodeCellAppend,
          encodeCell,
          encodeCodeWordAsInput,
          encodeCodeSymbolAsInput,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight])
      (by
        change (139 : Nat) ≠ 999
        omega)

def boolWordMarkingTailConfig
    (baseLeft : List (Option Bool)) (marked : Word Bool)
    (remainingCells : Nat) (tokens : Word MachineCodeSymbol) :
    Configuration :=
  config 120
    (List.append markedTickRev
      (List.append (cellListCanonicalLengthPrefixRev marked.length)
        baseLeft))
    (List.append ((stageNatBits (remainingCells - 1)).map some)
      (List.append ((markedCellsCodeBits (marked.map some)).map some)
        ((encodeCodeWordAsInput tokens).map some)))

def boolWordMarkingTailPayloadLeftRev
    (baseLeft : List (Option Bool)) (marked : Word Bool)
    (remainingLengthTail : Nat) : List (Option Bool) :=
  List.append ((markedCellsCodeBits (marked.map some)).reverse.map some)
    (List.append ((stageNatBits remainingLengthTail).reverse.map some)
      (List.append markedTickRev
        (List.append (cellListCanonicalLengthPrefixRev marked.length)
          baseLeft)))

def boolWordMarkingTailReturnScanRev
    (marked : Word Bool) (remainingLengthTail : Nat) : Word Bool :=
  List.append [true, true]
    (List.append (markedCellsCodeBits (marked.map some)).reverse
      (stageNatBits remainingLengthTail).reverse)

theorem boolWordMarkingTail_to_first_payload
    (baseLeft : List (Option Bool)) (marked : Word Bool)
    (remainingLengthTail : Nat) (tokens : Word MachineCodeSymbol) :
    BWSS.runConfig
        ((4 * remainingLengthTail + 4) + 4 * marked.length)
        (boolWordMarkingTailConfig baseLeft marked
          (remainingLengthTail + 1) tokens) =
      config 130
        (boolWordMarkingTailPayloadLeftRev baseLeft marked
          remainingLengthTail)
        ((encodeCodeWordAsInput tokens).map some) := by
  unfold boolWordMarkingTailConfig
    boolWordMarkingTailPayloadLeftRev
  simp only [Nat.add_sub_cancel_right]
  change
    BWSS.runConfig
        ((4 * remainingLengthTail + 4) + 4 * marked.length)
        (config 120
          (List.append markedTickRev
            (List.append (cellListCanonicalLengthPrefixRev marked.length)
              baseLeft))
          (List.append ((stageNatBits remainingLengthTail).map some)
            (List.append
              ((markedCellsCodeBits (marked.map some)).map some)
              ((encodeCodeWordAsInput tokens).map
                some)))) =
      config 130
        (List.append
          ((markedCellsCodeBits (marked.map some)).reverse.map some)
          (List.append ((stageNatBits remainingLengthTail).reverse.map some)
            (List.append markedTickRev
              (List.append (cellListCanonicalLengthPrefixRev marked.length)
                baseLeft))))
        ((encodeCodeWordAsInput tokens).map some)
  rw [runConfig_add]
  rw [run_boolWordSuffix_state120_stageNat]
  rw [run_boolWordSuffix_state130_markedBits]

theorem boolWordMarkingTail_mark_one
    (baseLeft : List (Option Bool)) (marked : Word Bool)
    (remainingLengthTail : Nat) (b : Bool)
    (restAfterCell : Word MachineCodeSymbol) :
    exists steps : Nat,
      BWSS.runConfig steps
          (boolWordMarkingTailConfig baseLeft marked
            (remainingLengthTail + 2)
            (encodeCellAppend (some b)
              restAfterCell)) =
        boolWordMarkingTailConfig baseLeft (List.append marked [b])
          (remainingLengthTail + 1) restAfterCell := by
  let scanRev :=
    boolWordMarkingTailReturnScanRev marked (remainingLengthTail + 1)
  refine
    ⟨((4 * (remainingLengthTail + 1) + 4) +
        4 * marked.length) +
        ((6 + (scanRev.length + 4)) + 4), ?_⟩
  rw [runConfig_add]
  rw [boolWordMarkingTail_to_first_payload]
  rw [show 6 + (scanRev.length + 4) + 4 =
      6 + ((scanRev.length + 4) + 4) by omega]
  rw [runConfig_add]
  have hcellBits :
      (encodeCodeWordAsInput
          (encodeCellAppend (some b) restAfterCell)).map
        some =
      List.append ((cellCodeBits (some b)).map some)
        ((encodeCodeWordAsInput restAfterCell).map
          some) := by
    cases b <;>
    simp [encodeCellAppend,
      encodeCell,
      encodeCodeWordAsInput,
      encodeCodeSymbolAsInput, cellCodeBits]
  rw [hcellBits]
  change
    BWSS.runConfig
        ((scanRev.length + 4) + 4)
        (BWSS.runConfig 6
          (config 130
            (boolWordMarkingTailPayloadLeftRev baseLeft marked
              (remainingLengthTail + 1))
            (List.append ((cellCodeBits (some b)).map some)
              ((encodeCodeWordAsInput
                restAfterCell).map some)))) =
      boolWordMarkingTailConfig baseLeft (List.append marked [b])
        (remainingLengthTail + 1) restAfterCell
  rw [run_boolWordSuffix_state130_currentBit]
  rw [runConfig_add]
  have hleft :
      some true :: some true ::
          boolWordMarkingTailPayloadLeftRev baseLeft marked
            (remainingLengthTail + 1) =
        List.append (scanRev.map some)
          (none :: some true :: some false :: some false ::
            List.append (cellListCanonicalLengthPrefixRev marked.length)
              baseLeft) := by
    simp [scanRev, boolWordMarkingTailReturnScanRev,
      boolWordMarkingTailPayloadLeftRev, markedTickRev,
      List.map_append, List.append_assoc]
  rw [hleft]
  have htail :
      List.append (cellCodeTailCells (some b))
          ((encodeCodeWordAsInput restAfterCell).map
            some) =
        some b :: some (!b) ::
          (encodeCodeWordAsInput restAfterCell).map
            some := by
    cases b <;> simp [cellCodeTailCells]
  rw [htail]
  rw [run_boolWordSuffix_state140_returnToLengthMarker]
  have hright :
      List.append (scanRev.reverse.map some)
          (some b :: some (!b) ::
            (encodeCodeWordAsInput restAfterCell).map
              some) =
        List.append (tickBits.map some)
          (List.append ((stageNatBits remainingLengthTail).map some)
            (List.append
              ((markedCellsCodeBits
                ((List.append marked [b]).map some)).map some)
              ((encodeCodeWordAsInput restAfterCell).map
                some))) := by
    cases b
    · rw [show (List.append marked [false]).map some =
          List.append (marked.map some) [some false] by
        simp [List.map_append]]
      rw [map_markedCellsCodeBits_append_single
        (marked.map some) (some false)]
      simp [scanRev, boolWordMarkingTailReturnScanRev,
        markedCellCodeBits, stageNatBits_succ, tickBits,
        encodeCodeSymbolAsInput,
        List.reverse_append, List.map_append, List.append_assoc]
    · rw [show (List.append marked [true]).map some =
          List.append (marked.map some) [some true] by
        simp [List.map_append]]
      rw [map_markedCellsCodeBits_append_single
        (marked.map some) (some true)]
      simp [scanRev, boolWordMarkingTailReturnScanRev,
        markedCellCodeBits, stageNatBits_succ, tickBits,
        encodeCodeSymbolAsInput,
        List.reverse_append, List.map_append, List.append_assoc]
  rw [hright]
  rw [run_boolWordSuffix_state100_tick]
  have hleftNext :
      List.append markedTickRev
          (some false :: some true :: some false :: some false ::
            List.append (cellListCanonicalLengthPrefixRev marked.length)
              baseLeft) =
        List.append markedTickRev
          (List.append
            (cellListCanonicalLengthPrefixRev
              (List.append marked [b]).length)
            baseLeft) := by
    rw [show (List.append marked [b]).length = marked.length + 1 by
      simp]
    simp [cellListCanonicalLengthPrefixRev, tickBits,
      encodeCodeSymbolAsInput]
  unfold boolWordMarkingTailConfig
  rw [hleftNext]
  simp

theorem boolWordMarkingTail_decodeCells_none_ne_halt
    (baseLeft : List (Option Bool)) (marked : Word Bool)
    (remainingCells : Nat) (tokens : Word MachineCodeSymbol)
    (hdecode :
      decodeCells remainingCells tokens = none)
    (n : Nat) :
    (BWSS.runConfig n
      (boolWordMarkingTailConfig baseLeft marked remainingCells tokens)).state ≠
      BWSS.halt := by
  induction remainingCells generalizing marked tokens n with
  | zero =>
      simp [decodeCells] at hdecode
  | succ remainingTail ih =>
      cases hcell : decodeCell tokens with
      | none =>
          apply
            boolWordSuffixScannerDescription_ne_halt_of_reaches_ne_halt_region
              (k := (4 * remainingTail + 4) + 4 * marked.length)
              (mid :=
                config 130
                  (boolWordMarkingTailPayloadLeftRev baseLeft marked
                    remainingTail)
                  ((encodeCodeWordAsInput tokens).map
                    some))
          · exact
              boolWordMarkingTail_to_first_payload
                baseLeft marked remainingTail tokens
          · intro m
            exact
              boolWordSuffixScannerDescription_runConfig_state130_decodeCell_none_ne_halt
                tokens
                (boolWordMarkingTailPayloadLeftRev baseLeft marked
                  remainingTail)
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
                boolWordSuffixScannerDescription_ne_halt_of_reaches_ne_halt_region
                  (k := (4 * remainingTail + 4) + 4 * marked.length)
                  (mid :=
                    config 130
                      (boolWordMarkingTailPayloadLeftRev baseLeft marked
                        remainingTail)
                      ((encodeCodeWordAsInput
                        (encodeCellAppend none
                          restAfterCell)).map some))
              · rw [htokens]
                exact
                  boolWordMarkingTail_to_first_payload
                    baseLeft marked remainingTail
                    (encodeCellAppend none
                      restAfterCell)
              · intro m
                exact
                  boolWordSuffixScannerDescription_runConfig_state130_blank_cell_ne_halt
                    restAfterCell
                    (boolWordMarkingTailPayloadLeftRev baseLeft marked
                      remainingTail)
                    m
          | some b =>
              cases hrest :
                  decodeCells remainingTail
                    restAfterCell with
              | none =>
                  cases remainingTail with
                  | zero =>
                      simp [decodeCells, hcell]
                        at hdecode
                  | succ nextTail =>
                      rcases
                          boolWordMarkingTail_mark_one
                            baseLeft marked nextTail b restAfterCell with
                        ⟨steps, hsteps⟩
                      apply
                        boolWordSuffixScannerDescription_ne_halt_of_reaches_ne_halt_region
                          (k := steps)
                          (mid :=
                            boolWordMarkingTailConfig baseLeft
                              (List.append marked [b])
                              (nextTail + 1) restAfterCell)
                      · rw [htokens]
                        exact hsteps
                      · intro m
                        exact
                          ih (List.append marked [b])
                            restAfterCell hrest m
              | some parsedRest =>
                  simp [decodeCells, hcell, hrest]
                    at hdecode

theorem boolWordMarkingTail_cellsToWord_none_ne_halt
    (baseLeft : List (Option Bool)) (marked : Word Bool)
    (cells : List (Option Bool)) (suffix : Word MachineCodeSymbol)
    (hword : cellsToWord? cells = none)
    (n : Nat) :
    (BWSS.runConfig n
      (boolWordMarkingTailConfig baseLeft marked cells.length
        (encodeCellsAppend cells suffix))).state ≠
      BWSS.halt := by
  induction cells generalizing marked suffix n with
  | nil =>
      simp [cellsToWord?] at hword
  | cons cell rest ih =>
      cases cell with
      | none =>
          apply
            boolWordSuffixScannerDescription_ne_halt_of_reaches_ne_halt_region
              (k := (4 * rest.length + 4) + 4 * marked.length)
              (mid :=
                config 130
                  (boolWordMarkingTailPayloadLeftRev baseLeft marked
                    rest.length)
                  ((encodeCodeWordAsInput
                    (encodeCellAppend none
                      (encodeCellsAppend rest
                        suffix))).map some))
          · change
              BWSS.runConfig
                  ((4 * rest.length + 4) + 4 * marked.length)
                  (boolWordMarkingTailConfig baseLeft marked
                    (rest.length + 1)
                    (encodeCellAppend none
                      (encodeCellsAppend rest suffix))) =
                config 130
                  (boolWordMarkingTailPayloadLeftRev baseLeft marked
                    rest.length)
                  ((encodeCodeWordAsInput
                    (encodeCellAppend none
                      (encodeCellsAppend rest
                        suffix))).map some)
            exact
              boolWordMarkingTail_to_first_payload
                baseLeft marked rest.length
                (encodeCellAppend none
                  (encodeCellsAppend rest suffix))
          · intro m
            exact
              boolWordSuffixScannerDescription_runConfig_state130_blank_cell_ne_halt
                (encodeCellsAppend rest suffix)
                (boolWordMarkingTailPayloadLeftRev baseLeft marked
                  rest.length)
                m
      | some b =>
          cases hrest : cellsToWord? rest with
          | none =>
              cases rest with
              | nil =>
                  simp [cellsToWord?] at hrest
              | cons nextCell restTail =>
                  rcases
                      boolWordMarkingTail_mark_one
                        baseLeft marked restTail.length b
                        (encodeCellsAppend
                          (nextCell :: restTail) suffix) with
                    ⟨steps, hsteps⟩
                  apply
                    boolWordSuffixScannerDescription_ne_halt_of_reaches_ne_halt_region
                      (k := steps)
                      (mid :=
                        boolWordMarkingTailConfig baseLeft
                          (List.append marked [b])
                          (restTail.length + 1)
                          (encodeCellsAppend
                            (nextCell :: restTail) suffix))
                  · change
                      BWSS.runConfig steps
                        (boolWordMarkingTailConfig baseLeft marked
                          (restTail.length + 2)
                          (encodeCellAppend (some b)
                            (encodeCellsAppend
                              (nextCell :: restTail) suffix))) =
                        boolWordMarkingTailConfig baseLeft
                          (List.append marked [b])
                          (restTail.length + 1)
                          (encodeCellsAppend
                            (nextCell :: restTail) suffix)
                    exact hsteps
                  · intro m
                    exact
                      ih (List.append marked [b]) suffix hrest m
          | some decoded =>
              simp [cellsToWord?, hrest] at hword

theorem boolWordSuffixScannerDescription_runConfig_state120_tick_decodeBoolWord_none_ne_halt
    (baseLeft : List (Option Bool)) (rest : Word MachineCodeSymbol)
    (hdecode :
      decodeBoolWord (MachineCodeSymbol.tick :: rest) =
        none)
    (n : Nat) :
    (BWSS.runConfig n
      (config 120 (List.append markedTickRev baseLeft)
        ((encodeCodeWordAsInput rest).map some))).state ≠
      BWSS.halt := by
  cases hnat : decodeNat rest with
  | none =>
      exact
        boolWordSuffixScannerDescription_runConfig_state120_decodeNat_none_ne_halt
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
        (BWSS.runConfig n
          (config 120 (List.append markedTickRev baseLeft)
            (List.map some
              (encodeCodeWordAsInput
                (encodeNatAppend remainingTail
                  tokensAfterLen))))).state ≠
          BWSS.halt
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
          simpa [boolWordMarkingTailConfig] using
            boolWordMarkingTail_decodeCells_none_ne_halt
              baseLeft ([] : Word Bool) (remainingTail + 1)
              tokensAfterLen hcells n
      | some parsedCells =>
          rcases parsedCells with ⟨cells, suffix⟩
          cases hword : cellsToWord? cells with
          | none =>
              have hcellsShape :
                  remainingTail + 1 = cells.length ∧
                    tokensAfterLen =
                      encodeCellsAppend cells suffix :=
                decodeCells_eq_some_encodeCellsAppend
                  hcells
              have hlengthTail : cells.length - 1 = remainingTail := by
                omega
              rw [hcellsShape.right]
              simpa [boolWordMarkingTailConfig, hlengthTail] using
                boolWordMarkingTail_cellsToWord_none_ne_halt
                  baseLeft ([] : Word Bool) cells suffix hword n
          | some decoded =>
              simp [decodeBoolWord,
                decodeCellList,
                decodeNat, hnat, hcells, hword]
                at hdecode

theorem boolWordSuffixScannerDescription_runConfig_state120_tick_code_inv
    (baseLeft : List (Option Bool)) (rest : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      BWSS.runConfig n
          (config 120 (List.append markedTickRev baseLeft)
            ((encodeCodeWordAsInput rest).map some)) =
        { state := BWSS.halt
          tape := Tout }) :
    exists bits : Word Bool,
    exists suffix : Word MachineCodeSymbol,
      MachineCodeSymbol.tick :: rest =
        encodeBoolWordAppend bits suffix := by
  cases hdecode :
      decodeBoolWord (MachineCodeSymbol.tick :: rest) with
  | none =>
      have hne :=
        boolWordSuffixScannerDescription_runConfig_state120_tick_decodeBoolWord_none_ne_halt
          baseLeft rest hdecode n
      have hstate :
          (BWSS.runConfig n
            (config 120 (List.append markedTickRev baseLeft)
              ((encodeCodeWordAsInput rest).map
                some))).state =
            BWSS.halt := by
        simpa using congrArg Configuration.state h
      exact False.elim (hne hstate)
  | some parsed =>
      rcases parsed with ⟨bits, suffix⟩
      exact
        ⟨bits, suffix,
          decodeBoolWord_eq_some_encodeBoolWordAppend
            hdecode⟩

theorem boolWordSuffixScannerDescription_runConfig_code_inv
    (baseLeft : List (Option Bool)) (code : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      BWSS.runConfig n
          (config BWSS.start baseLeft
            ((encodeCodeWordAsInput code).map some)) =
        { state := BWSS.halt
          tape := Tout }) :
    exists bits : Word Bool,
    exists suffix : Word MachineCodeSymbol,
      code = encodeBoolWordAppend bits suffix := by
  rcases
      boolWordSuffixScannerDescription_runConfig_start_nat_prefix_inv
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
          config BWSS.start baseLeft
            ((encodeCodeWordAsInput
              (MachineCodeSymbol.tick :: rest)).map some)
        let c1 : Configuration :=
          config 120 (List.append markedTickRev baseLeft)
            ((encodeCodeWordAsInput rest).map some)
        have hforward :
            BWSS.runConfig 4 c0 = c1 := by
          dsimp [c0, c1]
          simpa [encodeCodeWordAsInput,
            encodeCodeSymbolAsInput, tickBits] using
            run_boolWordSuffix_state100_tick baseLeft
              ((encodeCodeWordAsInput rest).map some)
        have hhalt :
            BWSS.runConfig n c0 =
              { state := BWSS.halt
                tape := Tout } := by
          simpa [c0] using h
        rcases
            runConfig_forward_inv BWSS
              c0 c1 n 4 hhalt hforward
              BWSS_htf with
          ⟨m, _hm_le, hm_halt⟩
        exact
          boolWordSuffixScannerDescription_runConfig_state120_tick_code_inv
            baseLeft rest hm_halt
      · exact ⟨[], rest, by
          simp [encodeBoolWordAppend,
            encodeCellListAppend,
            encodeNatAppend,
            encodeNat,
            encodeCellsAppend]⟩
      · cases hprefix
      · cases hprefix
      · cases hprefix
      · cases hprefix
      · cases hprefix

theorem cellListCanonicalHandoffConfigWithBase_move_right_all
    (cells baseLeft : List (Option Bool)) (suffixBits : Word Bool) :
    Tape.move Direction.right
        (cellListCanonicalHandoffConfigWithBase cells baseLeft
          suffixBits).tape =
      tapeAtCells
        (cellListCanonicalRestoredLeftWithBase cells baseLeft)
        (suffixBits.map some) := by
  unfold cellListCanonicalHandoffConfigWithBase
  cases hleft :
      cellListCanonicalRestoredLeftWithBase cells baseLeft with
  | nil =>
      exfalso
      exact cellListCanonicalRestoredLeftWithBase_ne_nil cells baseLeft
        hleft
  | cons cell left =>
      cases suffixBits <;>
        simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem boolWordCanonicalHandoffConfigWithBase_move_right_all
    (bits : Word Bool) (baseLeft : List (Option Bool))
    (suffixBits : Word Bool) :
    Tape.move Direction.right
        (boolWordCanonicalHandoffConfigWithBase bits baseLeft
          suffixBits).tape =
      tapeAtCells
        (cellListCanonicalRestoredLeftWithBase (bits.map some) baseLeft)
        (suffixBits.map some) := by
  simpa [boolWordCanonicalHandoffConfigWithBase] using
    cellListCanonicalHandoffConfigWithBase_move_right_all
      (bits.map some) baseLeft suffixBits

theorem boolWordSuffix_lookup_150_none :
    BWSS.lookupTransition 150 none = none := by
  native_decide

theorem boolWordSuffix_lookup_150_true :
    BWSS.lookupTransition 150 (some true) =
      some
        (writeMove 150 (some true) (some false) Direction.right 152) := by
  native_decide

theorem boolWordSuffix_lookup_152_false :
    BWSS.lookupTransition 152 (some false) =
      none := by
  native_decide

theorem boolWordSuffixScannerDescription_runConfig_finish_empty_suffix_ne_halt
    (bits : Word Bool) (baseLeft : List (Option Bool))
    (n : Nat) :
    (BWSS.runConfig n
      (cellListCanonicalFinishStartConfigWithBase
        (bits.map some) baseLeft ([] : Word Bool))).state ≠
      BWSS.halt := by
  let stuck : Configuration :=
    config 150
      (cellListCanonicalRestoredLeftWithBase (bits.map some) baseLeft)
      (([] : Word Bool).map some)
  have hreach :
      BWSS.runConfig (4 * bits.length)
        (cellListCanonicalFinishStartConfigWithBase
          (bits.map some) baseLeft ([] : Word Bool)) =
        stuck := by
    dsimp [stuck]
    unfold cellListCanonicalFinishStartConfigWithBase
    unfold cellListCanonicalRestoredLeftWithBase
    simpa [List.append_assoc] using
      run_boolWordSuffix_state150_markedBits bits
        (cellListCanonicalFinishStartLeftWithBase
          (bits.map some) baseLeft)
        ((([] : Word Bool).map some))
  have hstep : BWSS.stepConfig stuck = none := by
    simp [stuck, config, tapeAtCells,
      stepConfig, boolWordSuffix_lookup_150_none,
      Tape.read]
  have hstuck : stuck.state ≠ BWSS.halt := by
    simp [stuck, config, BoolWordSuffixScannerDescription]
  exact
    primitive_runConfig_state_ne_halt_of_reaches_stuck
      BWSS_htf
      (D := BWSS)
      (c :=
        cellListCanonicalFinishStartConfigWithBase
          (bits.map some) baseLeft ([] : Word Bool))
      (stuck := stuck) (k := 4 * bits.length) (n := n)
      hreach hstep hstuck

theorem boolWordSuffixScannerDescription_runConfig_finish_moveRight_suffix_ne_halt
    (bits : Word Bool) (baseLeft : List (Option Bool))
    (suffixTail : Word Bool) (n : Nat) :
    (BWSS.runConfig n
      (cellListCanonicalFinishStartConfigWithBase
        (bits.map some) baseLeft
        (List.append
          (encodeCodeSymbolAsInput
            MachineCodeSymbol.moveRight)
          suffixTail))).state ≠
      BWSS.halt := by
  let mid : Configuration :=
    config 150
      (cellListCanonicalRestoredLeftWithBase (bits.map some) baseLeft)
      ((List.append
        (encodeCodeSymbolAsInput
          MachineCodeSymbol.moveRight)
        suffixTail).map some)
  let stuck : Configuration :=
    BWSS.runConfig 1 mid
  have hfinish :
      BWSS.runConfig (4 * bits.length)
        (cellListCanonicalFinishStartConfigWithBase
          (bits.map some) baseLeft
          (List.append
            (encodeCodeSymbolAsInput
              MachineCodeSymbol.moveRight)
            suffixTail)) =
        mid := by
    dsimp [mid]
    unfold cellListCanonicalFinishStartConfigWithBase
    unfold cellListCanonicalRestoredLeftWithBase
    simpa [List.append_assoc] using
      run_boolWordSuffix_state150_markedBits bits
        (cellListCanonicalFinishStartLeftWithBase
          (bits.map some) baseLeft)
        ((List.append
          (encodeCodeSymbolAsInput
            MachineCodeSymbol.moveRight)
          suffixTail).map some)
  have hreach :
      BWSS.runConfig (4 * bits.length + 1)
        (cellListCanonicalFinishStartConfigWithBase
          (bits.map some) baseLeft
          (List.append
            (encodeCodeSymbolAsInput
              MachineCodeSymbol.moveRight)
            suffixTail)) =
        stuck := by
    rw [runConfig_add, hfinish]
  have hstep : BWSS.stepConfig stuck = none := by
    simp [stuck, mid, config, tapeAtCells,
      encodeCodeSymbolAsInput,
      runConfig, stepConfig,
      boolWordSuffix_lookup_150_true, boolWordSuffix_lookup_152_false,
      transition, writeMove, Tape.read, Tape.write,
      Tape.move, Tape.moveRight]
  have hstuck : stuck.state ≠ BWSS.halt := by
    dsimp [stuck, mid]
    simp [config, tapeAtCells,
      encodeCodeSymbolAsInput,
      runConfig, stepConfig,
      boolWordSuffix_lookup_150_true,
      transition, writeMove, Tape.read, Tape.write,
      Tape.move, Tape.moveRight]
    change (152 : Nat) ≠ 999
    omega
  exact
    primitive_runConfig_state_ne_halt_of_reaches_stuck
      BWSS_htf
      (D := BWSS)
      (c :=
        cellListCanonicalFinishStartConfigWithBase
          (bits.map some) baseLeft
          (List.append
            (encodeCodeSymbolAsInput
              MachineCodeSymbol.moveRight)
            suffixTail))
      (stuck := stuck) (k := 4 * bits.length + 1) (n := n)
      hreach hstep hstuck

theorem boolWordSuffixScannerDescription_runConfig_encodeBoolWordAppend_empty_suffix_ne_halt
    (baseLeft : List (Option Bool)) (bits : Word Bool) (n : Nat) :
    (BWSS.runConfig n
      (config BWSS.start baseLeft
        ((encodeCodeWordAsInput
          (encodeBoolWordAppend bits
            ([] : Word MachineCodeSymbol))).map some))).state ≠
      BWSS.halt := by
  rcases
      run_boolWordSuffix_raw_marking_loop_from_state100_withBase
        baseLeft ([] : Word Bool) bits ([] : Word Bool) with
    ⟨markSteps, hmark⟩
  have hreach :
      BWSS.runConfig markSteps
        (config BWSS.start baseLeft
          ((encodeCodeWordAsInput
            (encodeBoolWordAppend bits
              ([] : Word MachineCodeSymbol))).map some)) =
        cellListCanonicalFinishStartConfigWithBase
          (bits.map some) baseLeft ([] : Word Bool) := by
    rw [boolWordBits_eq_encodeBoolWordAppend]
    simpa [encodeCodeWordAsInput, markedCellsCodeBits,
      cellListCanonicalLengthPrefixRev, List.map_append,
      List.append_assoc] using hmark
  exact
    boolWordSuffixScannerDescription_ne_halt_of_reaches_ne_halt_region
      (k := markSteps)
      (mid :=
        cellListCanonicalFinishStartConfigWithBase
          (bits.map some) baseLeft ([] : Word Bool))
      hreach
      (fun m =>
        boolWordSuffixScannerDescription_runConfig_finish_empty_suffix_ne_halt
          bits baseLeft m)

theorem boolWordSuffixScannerDescription_runConfig_encodeBoolWordAppend_moveRight_suffix_ne_halt
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (rest : Word MachineCodeSymbol) (n : Nat) :
    (BWSS.runConfig n
      (config BWSS.start baseLeft
        ((encodeCodeWordAsInput
          (encodeBoolWordAppend bits
            (MachineCodeSymbol.moveRight :: rest))).map some))).state ≠
      BWSS.halt := by
  let suffixTail : Word Bool :=
    encodeCodeWordAsInput rest
  rcases
      run_boolWordSuffix_raw_marking_loop_from_state100_withBase
        baseLeft ([] : Word Bool) bits
          (List.append
            (encodeCodeSymbolAsInput
              MachineCodeSymbol.moveRight)
            suffixTail) with
    ⟨markSteps, hmark⟩
  have hreach :
      BWSS.runConfig markSteps
        (config BWSS.start baseLeft
          ((encodeCodeWordAsInput
            (encodeBoolWordAppend bits
              (MachineCodeSymbol.moveRight :: rest))).map some)) =
        cellListCanonicalFinishStartConfigWithBase
          (bits.map some) baseLeft
          (List.append
            (encodeCodeSymbolAsInput
              MachineCodeSymbol.moveRight)
            suffixTail) := by
    rw [boolWordBits_eq_encodeBoolWordAppend]
    simp [encodeCodeWordAsInput, suffixTail,
      markedCellsCodeBits, cellListCanonicalLengthPrefixRev,
      List.map_append] at hmark ⊢
    exact hmark
  exact
    boolWordSuffixScannerDescription_ne_halt_of_reaches_ne_halt_region
      (k := markSteps)
      (mid :=
        cellListCanonicalFinishStartConfigWithBase
          (bits.map some) baseLeft
          (List.append
            (encodeCodeSymbolAsInput
              MachineCodeSymbol.moveRight)
            suffixTail))
      hreach
      (fun m =>
        boolWordSuffixScannerDescription_runConfig_finish_moveRight_suffix_ne_halt
          bits baseLeft suffixTail m)

theorem
    boolWordSuffixScannerDescription_runConfig_encodeBoolWordAppend_handoff_phaseBridge
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (suffix : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      BWSS.runConfig n
          (config BWSS.start baseLeft
            ((encodeCodeWordAsInput
              (encodeBoolWordAppend bits
                suffix)).map some)) =
        { state := BWSS.halt
          tape := Tout }) :
    exists suffixTail : Word Bool,
      encodeCodeWordAsInput suffix = false :: suffixTail ∧
        Tout =
          (boolWordCanonicalHandoffConfigWithBase bits baseLeft
            (false :: suffixTail)).tape := by
  cases suffix with
  | nil =>
      have hstate :
          (BWSS.runConfig n
            (config BWSS.start baseLeft
              ((encodeCodeWordAsInput
                (encodeBoolWordAppend bits
                  ([] : Word MachineCodeSymbol))).map some))).state =
            BWSS.halt := by
        simpa using congrArg Configuration.state h
      exact False.elim
        (boolWordSuffixScannerDescription_runConfig_encodeBoolWordAppend_empty_suffix_ne_halt
          baseLeft bits n hstate)
  | cons symbol rest =>
      cases symbol with
      | moveRight =>
          have hstate :
              (BWSS.runConfig n
                (config BWSS.start baseLeft
                  ((encodeCodeWordAsInput
                    (encodeBoolWordAppend bits
                      (MachineCodeSymbol.moveRight :: rest))).map some))).state =
                BWSS.halt := by
            simpa using congrArg Configuration.state h
          exact False.elim
            (boolWordSuffixScannerDescription_runConfig_encodeBoolWordAppend_moveRight_suffix_ne_halt
              baseLeft bits rest n hstate)
      | header =>
          refine ⟨false :: false :: false ::
            encodeCodeWordAsInput rest, ?_, ?_⟩
          · simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput]
          · exact
              boolWordSuffixScannerDescription_runConfig_canonical_false_suffix_inv
                bits baseLeft
                  (false :: false :: false ::
                    encodeCodeWordAsInput rest)
                (by
                  simpa [boolWordBits_eq_encodeBoolWordAppend,
                    encodeCodeWordAsInput,
                    encodeCodeSymbolAsInput,
                    List.map_append, List.append_assoc] using h)
      | transition =>
          refine ⟨false :: false :: true ::
            encodeCodeWordAsInput rest, ?_, ?_⟩
          · simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput]
          · exact
              boolWordSuffixScannerDescription_runConfig_canonical_false_suffix_inv
                bits baseLeft
                  (false :: false :: true ::
                    encodeCodeWordAsInput rest)
                (by
                  simpa [boolWordBits_eq_encodeBoolWordAppend,
                    encodeCodeWordAsInput,
                    encodeCodeSymbolAsInput,
                    List.map_append, List.append_assoc] using h)
      | tick =>
          refine ⟨false :: true :: false ::
            encodeCodeWordAsInput rest, ?_, ?_⟩
          · simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput]
          · exact
              boolWordSuffixScannerDescription_runConfig_canonical_false_suffix_inv
                bits baseLeft
                  (false :: true :: false ::
                    encodeCodeWordAsInput rest)
                (by
                  simpa [boolWordBits_eq_encodeBoolWordAppend,
                    encodeCodeWordAsInput,
                    encodeCodeSymbolAsInput,
                    List.map_append, List.append_assoc] using h)
      | done =>
          refine ⟨false :: true :: true ::
            encodeCodeWordAsInput rest, ?_, ?_⟩
          · simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput]
          · exact
              boolWordSuffixScannerDescription_runConfig_canonical_false_suffix_inv
                bits baseLeft
                  (false :: true :: true ::
                    encodeCodeWordAsInput rest)
                (by
                  simpa [boolWordBits_eq_encodeBoolWordAppend,
                    encodeCodeWordAsInput,
                    encodeCodeSymbolAsInput,
                    List.map_append, List.append_assoc] using h)
      | blank =>
          refine ⟨true :: false :: false ::
            encodeCodeWordAsInput rest, ?_, ?_⟩
          · simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput]
          · exact
              boolWordSuffixScannerDescription_runConfig_canonical_false_suffix_inv
                bits baseLeft
                  (true :: false :: false ::
                    encodeCodeWordAsInput rest)
                (by
                  simpa [boolWordBits_eq_encodeBoolWordAppend,
                    encodeCodeWordAsInput,
                    encodeCodeSymbolAsInput,
                    List.map_append, List.append_assoc] using h)
      | zero =>
          refine ⟨true :: false :: true ::
            encodeCodeWordAsInput rest, ?_, ?_⟩
          · simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput]
          · exact
              boolWordSuffixScannerDescription_runConfig_canonical_false_suffix_inv
                bits baseLeft
                  (true :: false :: true ::
                    encodeCodeWordAsInput rest)
                (by
                  simpa [boolWordBits_eq_encodeBoolWordAppend,
                    encodeCodeWordAsInput,
                    encodeCodeSymbolAsInput,
                    List.map_append, List.append_assoc] using h)
      | one =>
          refine ⟨true :: true :: false ::
            encodeCodeWordAsInput rest, ?_, ?_⟩
          · simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput]
          · exact
              boolWordSuffixScannerDescription_runConfig_canonical_false_suffix_inv
                bits baseLeft
                  (true :: true :: false ::
                    encodeCodeWordAsInput rest)
                (by
                  simpa [boolWordBits_eq_encodeBoolWordAppend,
                    encodeCodeWordAsInput,
                    encodeCodeSymbolAsInput,
                    List.map_append, List.append_assoc] using h)
      | moveLeft =>
          refine ⟨true :: true :: true ::
            encodeCodeWordAsInput rest, ?_, ?_⟩
          · simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput]
          · exact
              boolWordSuffixScannerDescription_runConfig_canonical_false_suffix_inv
                bits baseLeft
                  (true :: true :: true ::
                    encodeCodeWordAsInput rest)
                (by
                  simpa [boolWordBits_eq_encodeBoolWordAppend,
                    encodeCodeWordAsInput,
                    encodeCodeSymbolAsInput,
                    List.map_append, List.append_assoc] using h)

theorem boolWordSuffixScannerDescription_runConfig_encodeBoolWordAppend_handoff
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (suffix : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      BWSS.runConfig n
          (config BWSS.start baseLeft
            ((encodeCodeWordAsInput
              (encodeBoolWordAppend bits
                suffix)).map some)) =
        { state := BWSS.halt
          tape := Tout }) :
    exists suffixTail : Word Bool,
      encodeCodeWordAsInput suffix = false :: suffixTail ∧
        Tout =
          (boolWordCanonicalHandoffConfigWithBase bits baseLeft
            (false :: suffixTail)).tape :=
  boolWordSuffixScannerDescription_runConfig_encodeBoolWordAppend_handoff_phaseBridge
    baseLeft bits suffix h

end DovetailLayoutScanner
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC
