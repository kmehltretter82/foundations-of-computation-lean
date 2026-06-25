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

namespace EncodedRewriters
namespace CanonicalLayouts
namespace DovetailLayoutScanner

open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

theorem boolWordSuffixScannerDescription_ne_halt_of_reaches_ne_halt_region
    {c mid : MachineDescription.Configuration} {k n : Nat}
    (hrun :
      BoolWordSuffixScannerDescription.runConfig k c = mid)
    (hmid :
      forall m : Nat,
        (BoolWordSuffixScannerDescription.runConfig m mid).state ≠
          BoolWordSuffixScannerDescription.halt) :
    (BoolWordSuffixScannerDescription.runConfig n c).state ≠
      BoolWordSuffixScannerDescription.halt := by
  by_cases hle : n ≤ k
  · intro hhalt
    let rem := k - n
    have hk : k = n + rem := by
      omega
    have hcfg :
        BoolWordSuffixScannerDescription.runConfig n c =
          { state := BoolWordSuffixScannerDescription.halt
            tape :=
              (BoolWordSuffixScannerDescription.runConfig n c).tape } := by
      cases hrunN :
          BoolWordSuffixScannerDescription.runConfig n c with
      | mk state tape =>
          simp [hrunN] at hhalt
          simp [hhalt]
    have hhaltAtK :
        (BoolWordSuffixScannerDescription.runConfig k c).state =
          BoolWordSuffixScannerDescription.halt := by
      rw [hk, MachineDescription.runConfig_add, hcfg,
        MachineDescription.runConfig_halt
          boolWordSuffixScannerDescription_haltTransitionFree]
    rw [hrun] at hhaltAtK
    exact hmid 0 hhaltAtK
  · have hn : n = k + (n - k) := by
      omega
    rw [hn, MachineDescription.runConfig_add, hrun]
    exact hmid (n - k)

theorem boolWordSuffixScannerDescription_runConfig_state120_decodeNat_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : MachineDescription.decodeNat tokens = none) (n : Nat) :
    (BoolWordSuffixScannerDescription.runConfig n
      (config 120 leftRev
        ((MachineDescription.encodeCodeWordAsInput tokens).map some))).state ≠
      BoolWordSuffixScannerDescription.halt := by
  induction tokens generalizing leftRev n with
  | nil =>
      exact
        primitive_runConfig_state_ne_halt_of_reaches_stuck
          boolWordSuffixScannerDescription_haltTransitionFree
          (D := BoolWordSuffixScannerDescription)
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
              boolWordSuffixScannerDescription_haltTransitionFree
              (D := BoolWordSuffixScannerDescription)
              (c :=
                config 120 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.header :: rest)).map some))
              (stuck :=
                BoolWordSuffixScannerDescription.runConfig 2
                  (config 120 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.header :: rest)).map some)))
              (k := 2) (n := n)
              rfl
              (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
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
              boolWordSuffixScannerDescription_haltTransitionFree
              (D := BoolWordSuffixScannerDescription)
              (c :=
                config 120 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.transition :: rest)).map some))
              (stuck :=
                BoolWordSuffixScannerDescription.runConfig 2
                  (config 120 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.transition :: rest)).map some)))
              (k := 2) (n := n)
              rfl
              (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
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
                boolWordSuffixScannerDescription_ne_halt_of_reaches_ne_halt_region
                  (k := 4)
                  (mid :=
                    config 120
                      (List.append (tickBits.reverse.map some) leftRev)
                      ((MachineDescription.encodeCodeWordAsInput rest).map
                        some))
              · simpa [tickBits, MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput] using
                  run_boolWordSuffix_state120_tick leftRev
                    ((MachineDescription.encodeCodeWordAsInput rest).map some)
              · intro m
                exact ih
                  (List.append (tickBits.reverse.map some) leftRev)
                  hrest m
          | some parsed =>
              simp [hrest] at hdecode
      | done =>
          simp [MachineDescription.decodeNat] at hdecode
      | blank =>
          exact
            primitive_runConfig_state_ne_halt_of_reaches_stuck
              boolWordSuffixScannerDescription_haltTransitionFree
              (D := BoolWordSuffixScannerDescription)
              (c :=
                config 120 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.blank :: rest)).map some))
              (stuck :=
                BoolWordSuffixScannerDescription.runConfig 1
                  (config 120 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.blank :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
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
              boolWordSuffixScannerDescription_haltTransitionFree
              (D := BoolWordSuffixScannerDescription)
              (c :=
                config 120 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.zero :: rest)).map some))
              (stuck :=
                BoolWordSuffixScannerDescription.runConfig 1
                  (config 120 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.zero :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
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
              boolWordSuffixScannerDescription_haltTransitionFree
              (D := BoolWordSuffixScannerDescription)
              (c :=
                config 120 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.one :: rest)).map some))
              (stuck :=
                BoolWordSuffixScannerDescription.runConfig 1
                  (config 120 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.one :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
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
              boolWordSuffixScannerDescription_haltTransitionFree
              (D := BoolWordSuffixScannerDescription)
              (c :=
                config 120 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.moveLeft :: rest)).map some))
              (stuck :=
                BoolWordSuffixScannerDescription.runConfig 1
                  (config 120 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.moveLeft :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
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
              boolWordSuffixScannerDescription_haltTransitionFree
              (D := BoolWordSuffixScannerDescription)
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
                simp [BoolWordSuffixScannerDescription, config,
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

theorem boolWordSuffixScannerDescription_runConfig_state130_decodeCell_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : MachineDescription.decodeCell tokens = none) (n : Nat) :
    (BoolWordSuffixScannerDescription.runConfig n
      (config 130 leftRev
        ((MachineDescription.encodeCodeWordAsInput tokens).map some))).state ≠
      BoolWordSuffixScannerDescription.halt := by
  cases tokens with
  | nil =>
      exact
        primitive_runConfig_state_ne_halt_of_reaches_stuck
          boolWordSuffixScannerDescription_haltTransitionFree
          (D := BoolWordSuffixScannerDescription)
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
              boolWordSuffixScannerDescription_haltTransitionFree
              (D := BoolWordSuffixScannerDescription)
              (c :=
                config 130 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.header :: rest)).map some))
              (stuck :=
                BoolWordSuffixScannerDescription.runConfig 1
                  (config 130 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.header :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
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
              boolWordSuffixScannerDescription_haltTransitionFree
              (D := BoolWordSuffixScannerDescription)
              (c :=
                config 130 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.transition :: rest)).map some))
              (stuck :=
                BoolWordSuffixScannerDescription.runConfig 1
                  (config 130 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.transition :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
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
              boolWordSuffixScannerDescription_haltTransitionFree
              (D := BoolWordSuffixScannerDescription)
              (c :=
                config 130 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.tick :: rest)).map some))
              (stuck :=
                BoolWordSuffixScannerDescription.runConfig 1
                  (config 130 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.tick :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
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
              boolWordSuffixScannerDescription_haltTransitionFree
              (D := BoolWordSuffixScannerDescription)
              (c :=
                config 130 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.done :: rest)).map some))
              (stuck :=
                BoolWordSuffixScannerDescription.runConfig 1
                  (config 130 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.done :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
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
              boolWordSuffixScannerDescription_haltTransitionFree
              (D := BoolWordSuffixScannerDescription)
              (c :=
                config 130 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.moveLeft :: rest)).map some))
              (stuck :=
                BoolWordSuffixScannerDescription.runConfig 5
                  (config 130 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.moveLeft :: rest)).map some)))
              (k := 5) (n := n)
              rfl
              (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
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
                change (145 : Nat) ≠ 999
                omega)
      | moveRight =>
          exact
            primitive_runConfig_state_ne_halt_of_reaches_stuck
              boolWordSuffixScannerDescription_haltTransitionFree
              (D := BoolWordSuffixScannerDescription)
              (c :=
                config 130 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.moveRight :: rest)).map some))
              (stuck :=
                BoolWordSuffixScannerDescription.runConfig 1
                  (config 130 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.moveRight :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [BoolWordSuffixScannerDescription, config,
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

theorem boolWordSuffixScannerDescription_runConfig_state130_blank_cell_ne_halt
    (suffix : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (n : Nat) :
    (BoolWordSuffixScannerDescription.runConfig n
      (config 130 leftRev
        ((MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeCellAppend none suffix)).map some))).state ≠
      BoolWordSuffixScannerDescription.halt := by
  exact
    primitive_runConfig_state_ne_halt_of_reaches_stuck
      boolWordSuffixScannerDescription_haltTransitionFree
      (D := BoolWordSuffixScannerDescription)
      (c :=
        config 130 leftRev
          ((MachineDescription.encodeCodeWordAsInput
            (MachineDescription.encodeCellAppend none suffix)).map some))
      (stuck :=
        BoolWordSuffixScannerDescription.runConfig 5
          (config 130 leftRev
            ((MachineDescription.encodeCodeWordAsInput
              (MachineDescription.encodeCellAppend none suffix)).map some)))
      (k := 5) (n := n)
      rfl
      (by
        cases suffix <;>
        simp [BoolWordSuffixScannerDescription, config, tapeAtCells,
          keep, keepMove, writeMove, scanLeftToSentinelRestart,
          MachineDescription.runConfig,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, MachineDescription.encodeCellAppend,
          MachineDescription.encodeCell,
          MachineDescription.encodeCodeWordAsInput,
          MachineDescription.encodeCodeSymbolAsInput,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight])
      (by
        change (139 : Nat) ≠ 999
        omega)

def boolWordMarkingTailConfig
    (baseLeft : List (Option Bool)) (marked : Word Bool)
    (remainingCells : Nat) (tokens : Word MachineCodeSymbol) :
    MachineDescription.Configuration :=
  config 120
    (List.append markedTickRev
      (List.append (cellListCanonicalLengthPrefixRev marked.length)
        baseLeft))
    (List.append ((stageNatBits (remainingCells - 1)).map some)
      (List.append ((markedCellsCodeBits (marked.map some)).map some)
        ((MachineDescription.encodeCodeWordAsInput tokens).map some)))

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
    BoolWordSuffixScannerDescription.runConfig
        ((4 * remainingLengthTail + 4) + 4 * marked.length)
        (boolWordMarkingTailConfig baseLeft marked
          (remainingLengthTail + 1) tokens) =
      config 130
        (boolWordMarkingTailPayloadLeftRev baseLeft marked
          remainingLengthTail)
        ((MachineDescription.encodeCodeWordAsInput tokens).map some) := by
  unfold boolWordMarkingTailConfig
    boolWordMarkingTailPayloadLeftRev
  simp only [Nat.add_sub_cancel_right]
  change
    BoolWordSuffixScannerDescription.runConfig
        ((4 * remainingLengthTail + 4) + 4 * marked.length)
        (config 120
          (List.append markedTickRev
            (List.append (cellListCanonicalLengthPrefixRev marked.length)
              baseLeft))
          (List.append ((stageNatBits remainingLengthTail).map some)
            (List.append
              ((markedCellsCodeBits (marked.map some)).map some)
              ((MachineDescription.encodeCodeWordAsInput tokens).map
                some)))) =
      config 130
        (List.append
          ((markedCellsCodeBits (marked.map some)).reverse.map some)
          (List.append ((stageNatBits remainingLengthTail).reverse.map some)
            (List.append markedTickRev
              (List.append (cellListCanonicalLengthPrefixRev marked.length)
                baseLeft))))
        ((MachineDescription.encodeCodeWordAsInput tokens).map some)
  rw [MachineDescription.runConfig_add]
  rw [run_boolWordSuffix_state120_stageNat]
  rw [run_boolWordSuffix_state130_markedBits]

theorem boolWordMarkingTail_mark_one
    (baseLeft : List (Option Bool)) (marked : Word Bool)
    (remainingLengthTail : Nat) (b : Bool)
    (restAfterCell : Word MachineCodeSymbol) :
    exists steps : Nat,
      BoolWordSuffixScannerDescription.runConfig steps
          (boolWordMarkingTailConfig baseLeft marked
            (remainingLengthTail + 2)
            (MachineDescription.encodeCellAppend (some b)
              restAfterCell)) =
        boolWordMarkingTailConfig baseLeft (List.append marked [b])
          (remainingLengthTail + 1) restAfterCell := by
  let scanRev :=
    boolWordMarkingTailReturnScanRev marked (remainingLengthTail + 1)
  refine
    ⟨((4 * (remainingLengthTail + 1) + 4) +
        4 * marked.length) +
        ((6 + (scanRev.length + 4)) + 4), ?_⟩
  rw [MachineDescription.runConfig_add]
  rw [boolWordMarkingTail_to_first_payload]
  rw [show 6 + (scanRev.length + 4) + 4 =
      6 + ((scanRev.length + 4) + 4) by omega]
  rw [MachineDescription.runConfig_add]
  have hcellBits :
      (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeCellAppend (some b) restAfterCell)).map
        some =
      List.append ((cellCodeBits (some b)).map some)
        ((MachineDescription.encodeCodeWordAsInput restAfterCell).map
          some) := by
    cases b <;>
    simp [MachineDescription.encodeCellAppend,
      MachineDescription.encodeCell,
      MachineDescription.encodeCodeWordAsInput,
      MachineDescription.encodeCodeSymbolAsInput, cellCodeBits]
  rw [hcellBits]
  change
    BoolWordSuffixScannerDescription.runConfig
        ((scanRev.length + 4) + 4)
        (BoolWordSuffixScannerDescription.runConfig 6
          (config 130
            (boolWordMarkingTailPayloadLeftRev baseLeft marked
              (remainingLengthTail + 1))
            (List.append ((cellCodeBits (some b)).map some)
              ((MachineDescription.encodeCodeWordAsInput
                restAfterCell).map some)))) =
      boolWordMarkingTailConfig baseLeft (List.append marked [b])
        (remainingLengthTail + 1) restAfterCell
  rw [run_boolWordSuffix_state130_currentBit]
  rw [MachineDescription.runConfig_add]
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
          ((MachineDescription.encodeCodeWordAsInput restAfterCell).map
            some) =
        some b :: some (!b) ::
          (MachineDescription.encodeCodeWordAsInput restAfterCell).map
            some := by
    cases b <;> simp [cellCodeTailCells]
  rw [htail]
  rw [run_boolWordSuffix_state140_returnToLengthMarker]
  have hright :
      List.append (scanRev.reverse.map some)
          (some b :: some (!b) ::
            (MachineDescription.encodeCodeWordAsInput restAfterCell).map
              some) =
        List.append (tickBits.map some)
          (List.append ((stageNatBits remainingLengthTail).map some)
            (List.append
              ((markedCellsCodeBits
                ((List.append marked [b]).map some)).map some)
              ((MachineDescription.encodeCodeWordAsInput restAfterCell).map
                some))) := by
    cases b
    · rw [show (List.append marked [false]).map some =
          List.append (marked.map some) [some false] by
        simp [List.map_append]]
      rw [map_markedCellsCodeBits_append_single
        (marked.map some) (some false)]
      simp [scanRev, boolWordMarkingTailReturnScanRev,
        markedCellCodeBits, stageNatBits_succ, tickBits,
        MachineDescription.encodeCodeSymbolAsInput,
        List.reverse_append, List.map_append, List.append_assoc]
    · rw [show (List.append marked [true]).map some =
          List.append (marked.map some) [some true] by
        simp [List.map_append]]
      rw [map_markedCellsCodeBits_append_single
        (marked.map some) (some true)]
      simp [scanRev, boolWordMarkingTailReturnScanRev,
        markedCellCodeBits, stageNatBits_succ, tickBits,
        MachineDescription.encodeCodeSymbolAsInput,
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
      MachineDescription.encodeCodeSymbolAsInput]
  unfold boolWordMarkingTailConfig
  rw [hleftNext]
  simp

theorem boolWordMarkingTail_decodeCells_none_ne_halt
    (baseLeft : List (Option Bool)) (marked : Word Bool)
    (remainingCells : Nat) (tokens : Word MachineCodeSymbol)
    (hdecode :
      MachineDescription.decodeCells remainingCells tokens = none)
    (n : Nat) :
    (BoolWordSuffixScannerDescription.runConfig n
      (boolWordMarkingTailConfig baseLeft marked remainingCells tokens)).state ≠
      BoolWordSuffixScannerDescription.halt := by
  induction remainingCells generalizing marked tokens n with
  | zero =>
      simp [MachineDescription.decodeCells] at hdecode
  | succ remainingTail ih =>
      cases hcell : MachineDescription.decodeCell tokens with
      | none =>
          apply
            boolWordSuffixScannerDescription_ne_halt_of_reaches_ne_halt_region
              (k := (4 * remainingTail + 4) + 4 * marked.length)
              (mid :=
                config 130
                  (boolWordMarkingTailPayloadLeftRev baseLeft marked
                    remainingTail)
                  ((MachineDescription.encodeCodeWordAsInput tokens).map
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
                MachineDescription.encodeCellAppend cell restAfterCell :=
            MachineDescription.decodeCell_eq_some_encodeCellAppend hcell
          cases cell with
          | none =>
              apply
                boolWordSuffixScannerDescription_ne_halt_of_reaches_ne_halt_region
                  (k := (4 * remainingTail + 4) + 4 * marked.length)
                  (mid :=
                    config 130
                      (boolWordMarkingTailPayloadLeftRev baseLeft marked
                        remainingTail)
                      ((MachineDescription.encodeCodeWordAsInput
                        (MachineDescription.encodeCellAppend none
                          restAfterCell)).map some))
              · rw [htokens]
                exact
                  boolWordMarkingTail_to_first_payload
                    baseLeft marked remainingTail
                    (MachineDescription.encodeCellAppend none
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
                  MachineDescription.decodeCells remainingTail
                    restAfterCell with
              | none =>
                  cases remainingTail with
                  | zero =>
                      simp [MachineDescription.decodeCells, hcell]
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
                  simp [MachineDescription.decodeCells, hcell, hrest]
                    at hdecode

theorem boolWordMarkingTail_cellsToWord_none_ne_halt
    (baseLeft : List (Option Bool)) (marked : Word Bool)
    (cells : List (Option Bool)) (suffix : Word MachineCodeSymbol)
    (hword : MachineDescription.cellsToWord? cells = none)
    (n : Nat) :
    (BoolWordSuffixScannerDescription.runConfig n
      (boolWordMarkingTailConfig baseLeft marked cells.length
        (MachineDescription.encodeCellsAppend cells suffix))).state ≠
      BoolWordSuffixScannerDescription.halt := by
  induction cells generalizing marked suffix n with
  | nil =>
      simp [MachineDescription.cellsToWord?] at hword
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
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineDescription.encodeCellAppend none
                      (MachineDescription.encodeCellsAppend rest
                        suffix))).map some))
          · change
              BoolWordSuffixScannerDescription.runConfig
                  ((4 * rest.length + 4) + 4 * marked.length)
                  (boolWordMarkingTailConfig baseLeft marked
                    (rest.length + 1)
                    (MachineDescription.encodeCellAppend none
                      (MachineDescription.encodeCellsAppend rest suffix))) =
                config 130
                  (boolWordMarkingTailPayloadLeftRev baseLeft marked
                    rest.length)
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineDescription.encodeCellAppend none
                      (MachineDescription.encodeCellsAppend rest
                        suffix))).map some)
            exact
              boolWordMarkingTail_to_first_payload
                baseLeft marked rest.length
                (MachineDescription.encodeCellAppend none
                  (MachineDescription.encodeCellsAppend rest suffix))
          · intro m
            exact
              boolWordSuffixScannerDescription_runConfig_state130_blank_cell_ne_halt
                (MachineDescription.encodeCellsAppend rest suffix)
                (boolWordMarkingTailPayloadLeftRev baseLeft marked
                  rest.length)
                m
      | some b =>
          cases hrest : MachineDescription.cellsToWord? rest with
          | none =>
              cases rest with
              | nil =>
                  simp [MachineDescription.cellsToWord?] at hrest
              | cons nextCell restTail =>
                  rcases
                      boolWordMarkingTail_mark_one
                        baseLeft marked restTail.length b
                        (MachineDescription.encodeCellsAppend
                          (nextCell :: restTail) suffix) with
                    ⟨steps, hsteps⟩
                  apply
                    boolWordSuffixScannerDescription_ne_halt_of_reaches_ne_halt_region
                      (k := steps)
                      (mid :=
                        boolWordMarkingTailConfig baseLeft
                          (List.append marked [b])
                          (restTail.length + 1)
                          (MachineDescription.encodeCellsAppend
                            (nextCell :: restTail) suffix))
                  · change
                      BoolWordSuffixScannerDescription.runConfig steps
                        (boolWordMarkingTailConfig baseLeft marked
                          (restTail.length + 2)
                          (MachineDescription.encodeCellAppend (some b)
                            (MachineDescription.encodeCellsAppend
                              (nextCell :: restTail) suffix))) =
                        boolWordMarkingTailConfig baseLeft
                          (List.append marked [b])
                          (restTail.length + 1)
                          (MachineDescription.encodeCellsAppend
                            (nextCell :: restTail) suffix)
                    exact hsteps
                  · intro m
                    exact
                      ih (List.append marked [b]) suffix hrest m
          | some decoded =>
              simp [MachineDescription.cellsToWord?, hrest] at hword

theorem boolWordSuffixScannerDescription_runConfig_state120_tick_decodeBoolWord_none_ne_halt
    (baseLeft : List (Option Bool)) (rest : Word MachineCodeSymbol)
    (hdecode :
      MachineDescription.decodeBoolWord (MachineCodeSymbol.tick :: rest) =
        none)
    (n : Nat) :
    (BoolWordSuffixScannerDescription.runConfig n
      (config 120 (List.append markedTickRev baseLeft)
        ((MachineDescription.encodeCodeWordAsInput rest).map some))).state ≠
      BoolWordSuffixScannerDescription.halt := by
  cases hnat : MachineDescription.decodeNat rest with
  | none =>
      exact
        boolWordSuffixScannerDescription_runConfig_state120_decodeNat_none_ne_halt
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
        (BoolWordSuffixScannerDescription.runConfig n
          (config 120 (List.append markedTickRev baseLeft)
            (List.map some
              (MachineDescription.encodeCodeWordAsInput
                (MachineDescription.encodeNatAppend remainingTail
                  tokensAfterLen))))).state ≠
          BoolWordSuffixScannerDescription.halt
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
          simpa [boolWordMarkingTailConfig] using
            boolWordMarkingTail_decodeCells_none_ne_halt
              baseLeft ([] : Word Bool) (remainingTail + 1)
              tokensAfterLen hcells n
      | some parsedCells =>
          rcases parsedCells with ⟨cells, suffix⟩
          cases hword : MachineDescription.cellsToWord? cells with
          | none =>
              have hcellsShape :
                  remainingTail + 1 = cells.length ∧
                    tokensAfterLen =
                      MachineDescription.encodeCellsAppend cells suffix :=
                MachineDescription.decodeCells_eq_some_encodeCellsAppend
                  hcells
              have hlengthTail : cells.length - 1 = remainingTail := by
                omega
              rw [hcellsShape.right]
              simpa [boolWordMarkingTailConfig, hlengthTail] using
                boolWordMarkingTail_cellsToWord_none_ne_halt
                  baseLeft ([] : Word Bool) cells suffix hword n
          | some decoded =>
              simp [MachineDescription.decodeBoolWord,
                MachineDescription.decodeCellList,
                MachineDescription.decodeNat, hnat, hcells, hword]
                at hdecode

theorem boolWordSuffixScannerDescription_runConfig_state120_tick_code_inv
    (baseLeft : List (Option Bool)) (rest : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      BoolWordSuffixScannerDescription.runConfig n
          (config 120 (List.append markedTickRev baseLeft)
            ((MachineDescription.encodeCodeWordAsInput rest).map some)) =
        { state := BoolWordSuffixScannerDescription.halt
          tape := Tout }) :
    exists bits : Word Bool,
    exists suffix : Word MachineCodeSymbol,
      MachineCodeSymbol.tick :: rest =
        MachineDescription.encodeBoolWordAppend bits suffix := by
  cases hdecode :
      MachineDescription.decodeBoolWord (MachineCodeSymbol.tick :: rest) with
  | none =>
      have hne :=
        boolWordSuffixScannerDescription_runConfig_state120_tick_decodeBoolWord_none_ne_halt
          baseLeft rest hdecode n
      have hstate :
          (BoolWordSuffixScannerDescription.runConfig n
            (config 120 (List.append markedTickRev baseLeft)
              ((MachineDescription.encodeCodeWordAsInput rest).map
                some))).state =
            BoolWordSuffixScannerDescription.halt := by
        simpa using congrArg MachineDescription.Configuration.state h
      exact False.elim (hne hstate)
  | some parsed =>
      rcases parsed with ⟨bits, suffix⟩
      exact
        ⟨bits, suffix,
          MachineDescription.decodeBoolWord_eq_some_encodeBoolWordAppend
            hdecode⟩

theorem boolWordSuffixScannerDescription_runConfig_code_inv
    (baseLeft : List (Option Bool)) (code : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      BoolWordSuffixScannerDescription.runConfig n
          (config BoolWordSuffixScannerDescription.start baseLeft
            ((MachineDescription.encodeCodeWordAsInput code).map some)) =
        { state := BoolWordSuffixScannerDescription.halt
          tape := Tout }) :
    exists bits : Word Bool,
    exists suffix : Word MachineCodeSymbol,
      code = MachineDescription.encodeBoolWordAppend bits suffix := by
  rcases
      boolWordSuffixScannerDescription_runConfig_start_nat_prefix_inv
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
          config BoolWordSuffixScannerDescription.start baseLeft
            ((MachineDescription.encodeCodeWordAsInput
              (MachineCodeSymbol.tick :: rest)).map some)
        let c1 : MachineDescription.Configuration :=
          config 120 (List.append markedTickRev baseLeft)
            ((MachineDescription.encodeCodeWordAsInput rest).map some)
        have hforward :
            BoolWordSuffixScannerDescription.runConfig 4 c0 = c1 := by
          dsimp [c0, c1]
          simpa [MachineDescription.encodeCodeWordAsInput,
            MachineDescription.encodeCodeSymbolAsInput, tickBits] using
            run_boolWordSuffix_state100_tick baseLeft
              ((MachineDescription.encodeCodeWordAsInput rest).map some)
        have hhalt :
            BoolWordSuffixScannerDescription.runConfig n c0 =
              { state := BoolWordSuffixScannerDescription.halt
                tape := Tout } := by
          simpa [c0] using h
        rcases
            runConfig_forward_inv BoolWordSuffixScannerDescription
              c0 c1 n 4 hhalt hforward
              boolWordSuffixScannerDescription_haltTransitionFree with
          ⟨m, _hm_le, hm_halt⟩
        exact
          boolWordSuffixScannerDescription_runConfig_state120_tick_code_inv
            baseLeft rest hm_halt
      · exact ⟨[], rest, by
          simp [MachineDescription.encodeBoolWordAppend,
            MachineDescription.encodeCellListAppend,
            MachineDescription.encodeNatAppend,
            MachineDescription.encodeNat,
            MachineDescription.encodeCellsAppend]⟩
      · cases hprefix
      · cases hprefix
      · cases hprefix
      · cases hprefix
      · cases hprefix

end DovetailLayoutScanner
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC
