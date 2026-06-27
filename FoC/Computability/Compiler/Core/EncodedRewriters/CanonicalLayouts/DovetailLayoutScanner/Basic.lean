import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailStagePrefix

set_option doc.verso true

/-!
# Dovetail-layout scanner components

Concrete field scanners for the complete
{name (full := FoC.Computability.MachineDescription.DovetailLayout)}`DovetailLayout`
recognizer. The cell-list scanner marks length ticks and payload cells, then
restores the payload before halting just left of the next field.
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

/-!
## Suffix-aware cell-list scanner

The scanner starts with the head on the first bit of an encoded
{name (full := FoC.Computability.MachineDescription.encodeCellListAppend)}`encodeCellListAppend`
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

private abbrev CLSS := CellListSuffixScannerDescription

theorem cellListSuffixScannerDescription_wellFormed :
    CLSS.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := CLSS.transitions)
      (stateCount := CLSS.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := CLSS.transitions)
      (by decide)

theorem cellListSuffixScannerDescription_haltTransitionFree :
    CLSS.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := CLSS.transitions)
    (state := CLSS.halt)
    (by decide)

theorem cellListSuffixScannerDescription_subroutineReady :
    CLSS.SubroutineReady :=
  ⟨cellListSuffixScannerDescription_wellFormed,
    cellListSuffixScannerDescription_haltTransitionFree⟩

theorem cellListSuffixScannerDescription_initial_eq_config
    (bits : Word Bool) :
    CLSS.initial bits =
      config 100 [] (bits.map some) := by
  cases bits <;> rfl

theorem cellListSuffix_lookup_150_false :
    CLSS.lookupTransition 150 (some false) =
      some (keepMove 150 (some false) Direction.left
        CLSS.halt) := by
  decide

def cellCodeBits (cell : Option Bool) : Word Bool :=
  encodeCodeWordAsInput
    (encodeCell cell)

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
      encodeCodeWordAsInput
        (encodeCell cell) := rfl

theorem cellsCodeBits_eq_encodeCellsAppend
    (cells : List (Option Bool)) :
    cellsCodeBits cells =
      encodeCodeWordAsInput
        (encodeCellsAppend cells []) := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      change
        List.append (cellCodeBits cell) (cellsCodeBits rest) =
          encodeCodeWordAsInput
            (encodeCellAppend cell
              (encodeCellsAppend rest []))
      rw [encodeCellAppend]
      rw [encodeCodeWordAsInput_append]
      rw [ih]
      rfl

theorem cellListBits_eq_encodeCellListAppend
    (cells : List (Option Bool))
    (suffix : Word MachineCodeSymbol) :
    encodeCodeWordAsInput
        (encodeCellListAppend cells suffix) =
      List.append (stageNatBits cells.length)
        (List.append (cellsCodeBits cells)
          (encodeCodeWordAsInput suffix)) := by
  rw [encodeCellListAppend]
  change
    encodeCodeWordAsInput
        (encodeNatAppend cells.length
          (encodeCellsAppend cells suffix)) =
      List.append (stageNatBits cells.length)
        (List.append (cellsCodeBits cells)
          (encodeCodeWordAsInput suffix))
  rw [encodeNatAppend]
  rw [encodeCodeWordAsInput_append]
  rw [show
      encodeCodeWordAsInput
          (encodeCellsAppend cells suffix) =
        List.append (cellsCodeBits cells)
          (encodeCodeWordAsInput suffix) by
    rw [show
        encodeCellsAppend cells suffix =
          List.append (encodeCellsAppend cells [])
            suffix by
      simpa using encodeCellsAppend_append cells [] suffix]
    rw [encodeCodeWordAsInput_append]
    rw [← cellsCodeBits_eq_encodeCellsAppend cells]]
  rfl

theorem boolWordBits_eq_encodeBoolWordAppend
    (w : Word Bool) (suffix : Word MachineCodeSymbol) :
    encodeCodeWordAsInput
        (encodeBoolWordAppend w suffix) =
      List.append (stageNatBits w.length)
        (List.append (cellsCodeBits (w.map some))
          (encodeCodeWordAsInput suffix)) := by
  simpa [encodeBoolWordAppend] using
    cellListBits_eq_encodeCellListAppend (w.map some) suffix

theorem cellBits_eq_encodeCellAppend
    (cell : Option Bool) (suffix : Word MachineCodeSymbol) :
    encodeCodeWordAsInput
        (encodeCellAppend cell suffix) =
      List.append (cellCodeBits cell)
        (encodeCodeWordAsInput suffix) := by
  rw [encodeCellAppend]
  rw [encodeCodeWordAsInput_append]
  rfl

theorem boolBits_eq_encodeBoolAppend
    (b : Bool) (suffix : Word MachineCodeSymbol) :
    encodeCodeWordAsInput
        (encodeBoolAppend b suffix) =
      List.append (cellCodeBits (some b))
        (encodeCodeWordAsInput suffix) := by
  simpa [encodeBoolAppend] using
    cellBits_eq_encodeCellAppend (some b) suffix

theorem tapeBits_eq_encodeTapeAppend
    (T : Tape Bool) (suffix : Word MachineCodeSymbol) :
    encodeCodeWordAsInput
        (encodeTapeAppend T suffix) =
      List.append (stageNatBits T.left.length)
        (List.append (cellsCodeBits T.left)
          (List.append (cellCodeBits T.head)
            (List.append (stageNatBits T.right.length)
              (List.append (cellsCodeBits T.right)
                (encodeCodeWordAsInput suffix))))) := by
  cases T with
  | mk left head right =>
      rw [encodeTapeAppend]
      rw [cellListBits_eq_encodeCellListAppend]
      rw [cellBits_eq_encodeCellAppend]
      rw [cellListBits_eq_encodeCellListAppend]

theorem configurationBits_eq_encodeConfigurationAppend
    (cfg : Configuration)
    (suffix : Word MachineCodeSymbol) :
    encodeCodeWordAsInput
        (encodeConfigurationAppend cfg suffix) =
      List.append (stageNatBits cfg.state)
        (List.append (stageNatBits cfg.tape.left.length)
          (List.append (cellsCodeBits cfg.tape.left)
            (List.append (cellCodeBits cfg.tape.head)
              (List.append (stageNatBits cfg.tape.right.length)
                (List.append (cellsCodeBits cfg.tape.right)
                  (encodeCodeWordAsInput suffix)))))) := by
  cases cfg with
  | mk state tape =>
      rw [encodeConfigurationAppend]
      rw [DovetailStagePrefix.natBits_eq_encodeNatAppend]
      rw [tapeBits_eq_encodeTapeAppend]

def transitionPrefixBits : Word Bool :=
  encodeCodeSymbolAsInput
    MachineCodeSymbol.transition

def cellListFieldBits
    (cells : List (Option Bool)) (suffixBits : Word Bool) :
    Word Bool :=
  List.append (stageNatBits cells.length)
    (List.append (cellsCodeBits cells) suffixBits)

theorem stageNatBits_cons_false (n : Nat) :
    exists tail : Word Bool,
      stageNatBits n = false :: tail := by
  cases n with
  | zero =>
      refine ⟨[false, true, true], ?_⟩
      simp [stageNatBits_zero]
  | succ n =>
      refine ⟨false :: true :: false :: stageNatBits n, ?_⟩
      simp [stageNatBits_succ]

theorem cellListFieldBits_cons_false
    (cells : List (Option Bool)) (suffixBits : Word Bool) :
    exists tail : Word Bool,
      cellListFieldBits cells suffixBits = false :: tail := by
  rcases stageNatBits_cons_false cells.length with ⟨tail, htail⟩
  refine ⟨List.append tail
      (List.append (cellsCodeBits cells) suffixBits), ?_⟩
  simp [cellListFieldBits, htail]

def boolWordFieldBits
    (w : Word Bool) (suffixBits : Word Bool) : Word Bool :=
  cellListFieldBits (w.map some) suffixBits

def cellFieldBits
    (cell : Option Bool) (suffixBits : Word Bool) : Word Bool :=
  List.append (cellCodeBits cell) suffixBits

theorem cellCodeBits_cons_false (cell : Option Bool) :
    exists tail : Word Bool,
      cellCodeBits cell = false :: tail := by
  cases cell with
  | none =>
      refine ⟨[true, false, false], ?_⟩
      simp [cellCodeBits, encodeCell,
        encodeCodeWordAsInput,
        encodeCodeSymbolAsInput]
  | some b =>
      cases b
      · refine ⟨[true, false, true], ?_⟩
        simp [cellCodeBits, encodeCell,
          encodeCodeWordAsInput,
          encodeCodeSymbolAsInput]
      · refine ⟨[true, true, false], ?_⟩
        simp [cellCodeBits, encodeCell,
          encodeCodeWordAsInput,
          encodeCodeSymbolAsInput]

theorem cellFieldBits_cons_false
    (cell : Option Bool) (suffixBits : Word Bool) :
    exists tail : Word Bool,
      cellFieldBits cell suffixBits = false :: tail := by
  rcases cellCodeBits_cons_false cell with ⟨tail, htail⟩
  refine ⟨List.append tail suffixBits, ?_⟩
  simp [cellFieldBits, htail]

def boolFieldBits (b : Bool) (suffixBits : Word Bool) :
    Word Bool :=
  cellFieldBits (some b) suffixBits

def tapeFieldBits (T : Tape Bool) (suffixBits : Word Bool) :
    Word Bool :=
  cellListFieldBits T.left
    (cellFieldBits T.head
      (cellListFieldBits T.right suffixBits))

theorem tapeFieldBits_cons_false
    (T : Tape Bool) (suffixBits : Word Bool) :
    exists tail : Word Bool,
      tapeFieldBits T suffixBits = false :: tail :=
  cellListFieldBits_cons_false T.left
    (cellFieldBits T.head
      (cellListFieldBits T.right suffixBits))

def configurationFieldBits
    (cfg : Configuration)
    (suffixBits : Word Bool) : Word Bool :=
  List.append (stageNatBits cfg.state)
    (tapeFieldBits cfg.tape suffixBits)

def dovetailLayoutFieldBits
    (L : DovetailLayout)
    (suffixBits : Word Bool) : Word Bool :=
  List.append transitionPrefixBits
    (boolWordFieldBits L.input
      (List.append (stageNatBits L.stage)
        (configurationFieldBits L.acceptConfig
          (configurationFieldBits L.rejectConfig
            (boolFieldBits L.acceptHit
              (boolFieldBits L.rejectHit suffixBits))))))

theorem tapeFieldBits_eq_encodeTapeAppend
    (T : Tape Bool) (suffix : Word MachineCodeSymbol) :
    encodeCodeWordAsInput
        (encodeTapeAppend T suffix) =
      tapeFieldBits T
        (encodeCodeWordAsInput suffix) := by
  rw [tapeBits_eq_encodeTapeAppend]
  rfl

theorem configurationFieldBits_eq_encodeConfigurationAppend
    (cfg : Configuration)
    (suffix : Word MachineCodeSymbol) :
    encodeCodeWordAsInput
        (encodeConfigurationAppend cfg suffix) =
      configurationFieldBits cfg
        (encodeCodeWordAsInput suffix) := by
  rw [configurationBits_eq_encodeConfigurationAppend]
  rfl

theorem dovetailLayoutFieldBits_eq_encodeAppend
    (L : DovetailLayout)
    (suffix : Word MachineCodeSymbol) :
    encodeCodeWordAsInput
        (DovetailLayout.encodeAppend L suffix) =
      dovetailLayoutFieldBits L
        (encodeCodeWordAsInput suffix) := by
  rw [DovetailLayout.encodeAppend]
  change
    List.append transitionPrefixBits
        (encodeCodeWordAsInput
          (encodeBoolWordAppend L.input
            (encodeNatAppend L.stage
              (encodeConfigurationAppend L.acceptConfig
                (encodeConfigurationAppend L.rejectConfig
                  (encodeBoolAppend L.acceptHit
                    (encodeBoolAppend L.rejectHit
                      suffix))))))) =
      dovetailLayoutFieldBits L
        (encodeCodeWordAsInput suffix)
  rw [boolWordBits_eq_encodeBoolWordAppend]
  rw [DovetailStagePrefix.natBits_eq_encodeNatAppend]
  rw [configurationFieldBits_eq_encodeConfigurationAppend]
  rw [configurationFieldBits_eq_encodeConfigurationAppend]
  rw [boolBits_eq_encodeBoolAppend]
  rw [boolBits_eq_encodeBoolAppend]
  simp [dovetailLayoutFieldBits, boolWordFieldBits,
    cellListFieldBits, boolFieldBits, cellFieldBits]

/-!
## Suffix-aware single-cell scanner

Configurations and the final hit flags need a scanner for one encoded cell
field.  This concrete table validates the three legal cell symbols
({lit}`blank`, {lit}`zero`, and {lit}`one`), preserves their bits, and halts
one cell to the left of the nonempty suffix.
-/

def CellSuffixScannerDescription : MachineDescription where
  stateCount := 100
  start := 10
  halt := 99
  transitions :=
    [ keepMove 10 (some false) Direction.right 11
    , keepMove 11 (some true) Direction.right 12
    , keepMove 12 (some false) Direction.right 13
    , keepMove 12 (some true) Direction.right 14
    , keepMove 13 (some false) Direction.right 20
    , keepMove 13 (some true) Direction.right 20
    , keepMove 14 (some false) Direction.right 20
    , keepMove 20 (some false) Direction.left 99
    , keepMove 20 (some true) Direction.left 99
    ]

private abbrev CSS := CellSuffixScannerDescription

theorem cellSuffixScannerDescription_wellFormed :
    CSS.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := CSS.transitions)
      (stateCount := CSS.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := CSS.transitions)
      (by decide)

theorem cellSuffixScannerDescription_haltTransitionFree :
    CSS.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := CSS.transitions)
    (state := CSS.halt)
    (by decide)

theorem cellSuffixScannerDescription_subroutineReady :
    CSS.SubroutineReady :=
  ⟨cellSuffixScannerDescription_wellFormed,
    cellSuffixScannerDescription_haltTransitionFree⟩

def cellSuffixHandoffConfigWithBase
    (cell : Option Bool) (baseLeft : List (Option Bool))
    (suffixBits : Word Bool) : Configuration :=
  { state := CSS.halt
    tape :=
      Tape.move Direction.left
        (tapeAtCells
          (List.append ((cellCodeBits cell).reverse.map some) baseLeft)
          (suffixBits.map some)) }

def boolSuffixHandoffConfigWithBase
    (b : Bool) (baseLeft : List (Option Bool))
    (suffixBits : Word Bool) : Configuration :=
  cellSuffixHandoffConfigWithBase (some b) baseLeft suffixBits

theorem run_cellSuffix_raw_to_handoff_withBase
    (cell : Option Bool) (baseLeft : List (Option Bool))
    (b : Bool) (suffixTail : Word Bool) :
    exists steps : Nat,
      CSS.runConfig steps
          (config 10 baseLeft
            (List.append ((cellCodeBits cell).map some)
              (some b :: suffixTail.map some))) =
        cellSuffixHandoffConfigWithBase cell baseLeft
          (b :: suffixTail) := by
  refine ⟨5, ?_⟩
  cases cell with
  | none =>
      cases b <;>
        simp [CellSuffixScannerDescription,
          cellSuffixHandoffConfigWithBase, cellCodeBits,
          config, tapeAtCells, keepMove,
          runConfig, stepConfig,
          lookupTransition, Matches,
          transition, encodeCell,
          encodeCodeWordAsInput,
          encodeCodeSymbolAsInput,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight]
  | some c =>
      cases c <;> cases b <;>
        simp [CellSuffixScannerDescription,
          cellSuffixHandoffConfigWithBase, cellCodeBits,
          config, tapeAtCells, keepMove,
          runConfig, stepConfig,
          lookupTransition, Matches,
          transition, encodeCell,
          encodeCodeWordAsInput,
          encodeCodeSymbolAsInput,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight]

theorem run_boolSuffix_raw_to_handoff_withBase
    (cellBit : Bool) (baseLeft : List (Option Bool))
    (b : Bool) (suffixTail : Word Bool) :
    exists steps : Nat,
      CSS.runConfig steps
          (config 10 baseLeft
            (List.append ((cellCodeBits (some cellBit)).map some)
              (some b :: suffixTail.map some))) =
        boolSuffixHandoffConfigWithBase cellBit baseLeft
          (b :: suffixTail) := by
  simpa [boolSuffixHandoffConfigWithBase] using
    run_cellSuffix_raw_to_handoff_withBase
      (some cellBit) baseLeft b suffixTail

theorem cellSuffixHandoffConfigWithBase_move_right
    (cell : Option Bool) (baseLeft : List (Option Bool))
    (b : Bool) (suffixTail : Word Bool) :
    Tape.move Direction.right
        (cellSuffixHandoffConfigWithBase cell baseLeft
          (b :: suffixTail)).tape =
      tapeAtCells
        (List.append ((cellCodeBits cell).reverse.map some) baseLeft)
        ((b :: suffixTail).map some) := by
  unfold cellSuffixHandoffConfigWithBase
  cases cell with
  | none =>
      simpa [cellCodeBits, encodeCell,
        encodeCodeWordAsInput,
        encodeCodeSymbolAsInput, List.append_assoc] using
        DovetailStagePrefix.tapeAtCells_move_right_move_left_cons
          (some false)
          (some false :: some true :: some false :: baseLeft)
          (some b) (suffixTail.map some)
  | some c =>
      cases c
      · simpa [cellCodeBits, encodeCell,
          encodeCodeWordAsInput,
          encodeCodeSymbolAsInput, List.append_assoc]
          using
            DovetailStagePrefix.tapeAtCells_move_right_move_left_cons
              (some true)
              (some false :: some true :: some false :: baseLeft)
              (some b) (suffixTail.map some)
      · simpa [cellCodeBits, encodeCell,
          encodeCodeWordAsInput,
          encodeCodeSymbolAsInput, List.append_assoc]
          using
            DovetailStagePrefix.tapeAtCells_move_right_move_left_cons
              (some false)
              (some true :: some true :: some false :: baseLeft)
              (some b) (suffixTail.map some)

theorem boolSuffixHandoffConfigWithBase_move_right
    (cellBit : Bool) (baseLeft : List (Option Bool))
    (b : Bool) (suffixTail : Word Bool) :
    Tape.move Direction.right
        (boolSuffixHandoffConfigWithBase cellBit baseLeft
          (b :: suffixTail)).tape =
      tapeAtCells
        (List.append ((cellCodeBits (some cellBit)).reverse.map some)
          baseLeft)
        ((b :: suffixTail).map some) := by
  simpa [boolSuffixHandoffConfigWithBase] using
    cellSuffixHandoffConfigWithBase_move_right
      (some cellBit) baseLeft b suffixTail

/-!
## Boolean-field scanners

The generic single-cell scanner is appropriate for tape-head cells, where
{lit}`blank` is a legal value.  The layout hit flags are genuine Boolean
fields, so their scanner accepts only the encoded {lit}`zero` and {lit}`one`
symbols.
-/

def BoolSuffixScannerDescription : MachineDescription where
  stateCount := 100
  start := 10
  halt := 99
  transitions :=
    [ keepMove 10 (some false) Direction.right 11
    , keepMove 11 (some true) Direction.right 12
    , keepMove 12 (some false) Direction.right 13
    , keepMove 12 (some true) Direction.right 14
    , keepMove 13 (some true) Direction.right 20
    , keepMove 14 (some false) Direction.right 20
    , keepMove 20 (some false) Direction.left 99
    , keepMove 20 (some true) Direction.left 99
    ]

private abbrev BSS := BoolSuffixScannerDescription

theorem boolSuffixScannerDescription_wellFormed :
    BSS.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := BSS.transitions)
      (stateCount := BSS.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := BSS.transitions)
      (by decide)

theorem boolSuffixScannerDescription_haltTransitionFree :
    BSS.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := BSS.transitions)
    (state := BSS.halt)
    (by decide)

theorem boolSuffixScannerDescription_subroutineReady :
    BSS.SubroutineReady :=
  ⟨boolSuffixScannerDescription_wellFormed,
    boolSuffixScannerDescription_haltTransitionFree⟩

def boolOnlySuffixHandoffConfigWithBase
    (flag : Bool) (baseLeft : List (Option Bool))
    (suffixBits : Word Bool) : Configuration :=
  { state := BSS.halt
    tape :=
      Tape.move Direction.left
        (tapeAtCells
          (List.append ((cellCodeBits (some flag)).reverse.map some)
            baseLeft)
          (suffixBits.map some)) }

theorem run_boolOnlySuffix_raw_to_handoff_withBase
    (flag : Bool) (baseLeft : List (Option Bool))
    (b : Bool) (suffixTail : Word Bool) :
    exists steps : Nat,
      BSS.runConfig steps
          (config 10 baseLeft
            (List.append ((cellCodeBits (some flag)).map some)
              (some b :: suffixTail.map some))) =
        boolOnlySuffixHandoffConfigWithBase flag baseLeft
          (b :: suffixTail) := by
  refine ⟨5, ?_⟩
  cases flag <;> cases b <;>
    simp [BoolSuffixScannerDescription,
      boolOnlySuffixHandoffConfigWithBase, cellCodeBits,
      config, tapeAtCells, keepMove,
      runConfig, stepConfig,
      lookupTransition, Matches,
      transition, encodeCell,
      encodeCodeWordAsInput,
      encodeCodeSymbolAsInput,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      Tape.moveRight]

theorem boolOnlySuffixHandoffConfigWithBase_move_right
    (flag : Bool) (baseLeft : List (Option Bool))
    (b : Bool) (suffixTail : Word Bool) :
    Tape.move Direction.right
        (boolOnlySuffixHandoffConfigWithBase flag baseLeft
          (b :: suffixTail)).tape =
      tapeAtCells
        (List.append ((cellCodeBits (some flag)).reverse.map some)
          baseLeft)
        ((b :: suffixTail).map some) := by
  unfold boolOnlySuffixHandoffConfigWithBase
  cases flag
  · simpa [cellCodeBits, encodeCell,
      encodeCodeWordAsInput,
      encodeCodeSymbolAsInput, List.append_assoc] using
      DovetailStagePrefix.tapeAtCells_move_right_move_left_cons
        (some true)
        (some false :: some true :: some false :: baseLeft)
        (some b) (suffixTail.map some)
  · simpa [cellCodeBits, encodeCell,
      encodeCodeWordAsInput,
      encodeCodeSymbolAsInput, List.append_assoc] using
      DovetailStagePrefix.tapeAtCells_move_right_move_left_cons
        (some false)
        (some true :: some true :: some false :: baseLeft)
        (some b) (suffixTail.map some)

def BoolFinalScannerDescription : MachineDescription where
  stateCount := 100
  start := 10
  halt := 99
  transitions :=
    [ keepMove 10 (some false) Direction.right 11
    , keepMove 11 (some true) Direction.right 12
    , keepMove 12 (some false) Direction.right 13
    , keepMove 12 (some true) Direction.right 14
    , keepMove 13 (some true) Direction.right 20
    , keepMove 14 (some false) Direction.right 20
    , keepMove 20 none Direction.left 99
    ]

private abbrev BFS := BoolFinalScannerDescription

theorem boolFinalScannerDescription_wellFormed :
    BFS.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := BFS.transitions)
      (stateCount := BFS.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := BFS.transitions)
      (by decide)

theorem boolFinalScannerDescription_haltTransitionFree :
    BFS.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := BFS.transitions)
    (state := BFS.halt)
    (by decide)

theorem boolFinalScannerDescription_subroutineReady :
    BFS.SubroutineReady :=
  ⟨boolFinalScannerDescription_wellFormed,
    boolFinalScannerDescription_haltTransitionFree⟩

def boolFinalHandoffConfigWithBase
    (flag : Bool) (baseLeft : List (Option Bool)) :
    Configuration :=
  { state := BFS.halt
    tape :=
      Tape.move Direction.left
        (tapeAtCells
          (List.append ((cellCodeBits (some flag)).reverse.map some)
            baseLeft)
          []) }

theorem run_boolFinal_raw_to_handoff_withBase
    (flag : Bool) (baseLeft : List (Option Bool)) :
    exists steps : Nat,
      BFS.runConfig steps
          (config 10 baseLeft
            ((cellCodeBits (some flag)).map some)) =
        boolFinalHandoffConfigWithBase flag baseLeft := by
  refine ⟨5, ?_⟩
  cases flag <;>
    simp [BoolFinalScannerDescription,
      boolFinalHandoffConfigWithBase, cellCodeBits,
      config, tapeAtCells, keepMove,
      runConfig, stepConfig,
      lookupTransition, Matches,
      transition, encodeCell,
      encodeCodeWordAsInput,
      encodeCodeSymbolAsInput,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      Tape.moveRight]

theorem boolFinalHandoffConfigWithBase_move_right
    (flag : Bool) (baseLeft : List (Option Bool)) :
    Tape.move Direction.right
        (boolFinalHandoffConfigWithBase flag baseLeft).tape =
      tapeAtCells
        (List.append ((cellCodeBits (some flag)).reverse.map some)
          baseLeft)
        [] := by
  cases flag <;>
    simp [boolFinalHandoffConfigWithBase, cellCodeBits,
      tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight,
      encodeCell,
      encodeCodeWordAsInput,
      encodeCodeSymbolAsInput]

/-!
## Leading transition marker scanner

Complete dovetail layouts begin with the code symbol
{name (full := FoC.Computability.MachineCodeSymbol.transition)}`MachineCodeSymbol.transition`.
This fixed-prefix scanner validates that marker and hands off to the first
layout field.
-/

def TransitionPrefixScannerDescription : MachineDescription where
  stateCount := 100
  start := 30
  halt := 99
  transitions :=
    [ keepMove 30 (some false) Direction.right 31
    , keepMove 31 (some false) Direction.right 32
    , keepMove 32 (some false) Direction.right 33
    , keepMove 33 (some true) Direction.right 40
    , keepMove 40 (some false) Direction.left 99
    , keepMove 40 (some true) Direction.left 99
    ]

private abbrev TPS := TransitionPrefixScannerDescription

theorem transitionPrefixScannerDescription_wellFormed :
    TPS.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := TPS.transitions)
      (stateCount := TPS.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := TPS.transitions)
      (by decide)

theorem transitionPrefixScannerDescription_haltTransitionFree :
    TPS.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := TPS.transitions)
    (state := TPS.halt)
    (by decide)

theorem transitionPrefixScannerDescription_subroutineReady :
    TPS.SubroutineReady :=
  ⟨transitionPrefixScannerDescription_wellFormed,
    transitionPrefixScannerDescription_haltTransitionFree⟩

def transitionPrefixHandoffConfigWithBase
    (baseLeft : List (Option Bool)) (suffixBits : Word Bool) :
    Configuration :=
  { state := TPS.halt
    tape :=
      Tape.move Direction.left
        (tapeAtCells
          (List.append (transitionPrefixBits.reverse.map some)
            baseLeft)
          (suffixBits.map some)) }

theorem run_transitionPrefix_raw_to_handoff_withBase
    (baseLeft : List (Option Bool)) (b : Bool)
    (suffixTail : Word Bool) :
    exists steps : Nat,
      TPS.runConfig steps
          (config 30 baseLeft
            (List.append (transitionPrefixBits.map some)
              (some b :: suffixTail.map some))) =
        transitionPrefixHandoffConfigWithBase baseLeft
          (b :: suffixTail) := by
  refine ⟨5, ?_⟩
  cases b <;>
    simp [TransitionPrefixScannerDescription,
      transitionPrefixHandoffConfigWithBase, transitionPrefixBits,
      config, tapeAtCells, keepMove,
      runConfig, stepConfig,
      lookupTransition, Matches,
      transition,
      encodeCodeSymbolAsInput,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      Tape.moveRight]

theorem transitionPrefixHandoffConfigWithBase_move_right
    (baseLeft : List (Option Bool)) (b : Bool)
    (suffixTail : Word Bool) :
    Tape.move Direction.right
        (transitionPrefixHandoffConfigWithBase baseLeft
          (b :: suffixTail)).tape =
      tapeAtCells
        (List.append (transitionPrefixBits.reverse.map some) baseLeft)
        ((b :: suffixTail).map some) := by
  unfold transitionPrefixHandoffConfigWithBase transitionPrefixBits
  simpa [encodeCodeSymbolAsInput, List.append_assoc]
    using
      DovetailStagePrefix.tapeAtCells_move_right_move_left_cons
        (some true)
        (some false :: some false :: some false :: baseLeft)
        (some b) (suffixTail.map some)

theorem run_cellList_state130_currentCell
    (cell : Option Bool) (left right : List (Option Bool)) :
    CLSS.runConfig 6
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
          runConfig, stepConfig,
          lookupTransition, Matches,
          transition,
          encodeCell,
          encodeCodeWordAsInput,
          encodeCodeSymbolAsInput,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight]
  | some b =>
      cases b <;> cases right <;>
        simp [CellListSuffixScannerDescription, cellCodeBits,
          cellCodeTailCells, config, tapeAtCells, keep, keepMove,
          writeMove, scanLeftToSentinelRestart,
          runConfig, stepConfig,
          lookupTransition, Matches,
          transition,
          encodeCell,
          encodeCodeWordAsInput,
          encodeCodeSymbolAsInput,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight]

theorem run_cellList_state100_tick
    (left tail : List (Option Bool)) :
    CLSS.runConfig 4
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
    CLSS.runConfig 4
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
    CLSS.runConfig 4
        (config 120 left
          (List.append (tickBits.map some) right)) =
      config 120
        (List.append (tickBits.reverse.map some) left) right := by
  cases right <;>
  simp [CellListSuffixScannerDescription, tickBits,
    config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart,
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition,
    encodeCodeSymbolAsInput,
    Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem run_cellList_state120_done
    (left right : List (Option Bool)) :
    CLSS.runConfig 4
        (config 120 left
          (List.append (doneBits.map some) right)) =
      config 130
        (List.append (doneBits.reverse.map some) left) right := by
  cases right <;>
  simp [CellListSuffixScannerDescription, doneBits,
    config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart,
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition,
    encodeCodeSymbolAsInput,
    Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem run_cellList_state120_stageNat
    (n : Nat) (left right : List (Option Bool)) :
    CLSS.runConfig (4 * n + 4)
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
      rw [runConfig_add]
      rw [show
          List.append ((stageNatBits (n + 1)).map some) right =
            List.append (tickBits.map some)
              (List.append ((stageNatBits n).map some) right) by
          simp [stageNatBits_succ, tickBits,
            encodeCodeSymbolAsInput]]
      rw [run_cellList_state120_tick]
      rw [ih]
      simp [stageNatBits_succ, tickBits,
        encodeCodeSymbolAsInput,
        List.map_append, List.append_assoc]

theorem run_cellList_state130_markedCell
    (cell : Option Bool) (left right : List (Option Bool)) :
    CLSS.runConfig 4
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
          runConfig, stepConfig,
          lookupTransition, Matches,
          transition,
          Tape.read, Tape.write, Tape.move, Tape.moveRight]
  | some b =>
      cases b <;> cases right <;>
        simp [CellListSuffixScannerDescription, markedCellCodeBits,
          config, tapeAtCells, keep, keepMove, writeMove,
          scanLeftToSentinelRestart,
          runConfig, stepConfig,
          lookupTransition, Matches,
          transition,
          Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem run_cellList_state130_markedCells
    (processed : List (Option Bool))
    (left right : List (Option Bool)) :
    CLSS.runConfig
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
      rw [runConfig_add]
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
    CLSS.runConfig
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
          runConfig, stepConfig,
          lookupTransition, Matches,
          transition,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight]
  | cons b rest ih =>
      rw [show (b :: rest).length + 4 =
          1 + (rest.length + 4) by
        simp
        omega]
      rw [runConfig_add]
      change
        CLSS.runConfig (rest.length + 4)
          (CLSS.runConfig 1
            (config 140
              (some b :: List.append (List.map some rest)
                (none :: some true :: leftTail))
              (some headBit :: right))) =
          config 100 (some false :: some true :: leftTail)
            (List.append (List.map some (b :: rest).reverse)
              (some headBit :: right))
      rw [show
          CLSS.runConfig 1
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
          runConfig, stepConfig,
          lookupTransition, Matches,
          transition,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft]]
      rw [ih]
      simp [List.map_append, List.append_assoc]

theorem run_cellList_state150_markedCell
    (cell : Option Bool) (left right : List (Option Bool)) :
    CLSS.runConfig 4
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
          runConfig, stepConfig,
          lookupTransition, Matches,
          transition, encodeCell,
          encodeCodeWordAsInput,
          encodeCodeSymbolAsInput,
          Tape.read, Tape.write, Tape.move, Tape.moveRight]
  | some b =>
      cases b <;> cases right <;>
        simp [CellListSuffixScannerDescription, markedCellCodeBits,
          cellCodeBits, config, tapeAtCells, keep, keepMove, writeMove,
          scanLeftToSentinelRestart,
          runConfig, stepConfig,
          lookupTransition, Matches,
          transition, encodeCell,
          encodeCodeWordAsInput,
          encodeCodeSymbolAsInput,
          Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem run_cellList_state150_markedCells
    (cells : List (Option Bool))
    (left right : List (Option Bool)) :
    CLSS.runConfig
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
      rw [runConfig_add]
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
    Configuration :=
  config 150 (cellListFinishStartLeft cells)
    (List.append ((markedCellsCodeBits cells).map some)
      (suffixBits.map some))

def cellListRestoredLeft
    (cells : List (Option Bool)) : List (Option Bool) :=
  List.append ((cellsCodeBits cells).reverse.map some)
    (cellListFinishStartLeft cells)

def cellListHandoffConfig
    (cells : List (Option Bool)) (suffixBits : Word Bool) :
    Configuration :=
  { state := CLSS.halt
    tape :=
      Tape.move Direction.left
        (tapeAtCells (cellListRestoredLeft cells)
          (suffixBits.map some)) }

def cellListMarkingState120
    (processed : List (Option Bool)) (cell : Option Bool)
    (rest : List (Option Bool)) (suffixBits : Word Bool) :
    Configuration :=
  config 120 (activeLengthPrefixRev processed.length)
    (List.append ((stageNatBits rest.length).map some)
      (List.append ((markedCellsCodeBits processed).map some)
        (List.append ((cellCodeBits cell).map some)
          (List.append ((cellsCodeBits rest).map some)
            (suffixBits.map some)))))

def cellListState100AfterMarked
    (processed : List (Option Bool)) (cell : Option Bool)
    (rest : List (Option Bool)) (suffixBits : Word Bool) :
    Configuration :=
  config 100 (finishLengthPrefixRev processed.length)
    (List.append ((stageNatBits rest.length).map some)
      (List.append ((markedCellsCodeBits processed).map some)
        (List.append ((markedCellCodeBits cell).map some)
          (List.append ((cellsCodeBits rest).map some)
            (suffixBits.map some)))))

def cellListCanonicalLengthPrefixRev : Nat -> List (Option Bool)
  | 0 => []
  | n + 1 =>
      List.append (tickBits.reverse.map some)
        (cellListCanonicalLengthPrefixRev n)

def cellListRawMarkingState120
    (processed : List (Option Bool)) (cell : Option Bool)
    (rest : List (Option Bool)) (suffixBits : Word Bool) :
    Configuration :=
  config 120
    (List.append markedTickRev
      (cellListCanonicalLengthPrefixRev processed.length))
    (List.append ((stageNatBits rest.length).map some)
      (List.append ((markedCellsCodeBits processed).map some)
        (List.append ((cellCodeBits cell).map some)
          (List.append ((cellsCodeBits rest).map some)
            (suffixBits.map some)))))

def cellListRawState100AfterMarked
    (processed : List (Option Bool)) (cell : Option Bool)
    (rest : List (Option Bool)) (suffixBits : Word Bool) :
    Configuration :=
  config 100 (cellListCanonicalLengthPrefixRev (processed.length + 1))
    (List.append ((stageNatBits rest.length).map some)
      (List.append ((markedCellsCodeBits processed).map some)
        (List.append ((markedCellCodeBits cell).map some)
          (List.append ((cellsCodeBits rest).map some)
            (suffixBits.map some)))))

def cellListCanonicalFinishStartLeft
    (cells : List (Option Bool)) : List (Option Bool) :=
  List.append (doneBits.reverse.map some)
    (cellListCanonicalLengthPrefixRev cells.length)

def cellListCanonicalFinishStartConfig
    (cells : List (Option Bool)) (suffixBits : Word Bool) :
    Configuration :=
  config 150 (cellListCanonicalFinishStartLeft cells)
    (List.append ((markedCellsCodeBits cells).map some)
      (suffixBits.map some))

def cellListCanonicalRestoredLeft
    (cells : List (Option Bool)) : List (Option Bool) :=
  List.append ((cellsCodeBits cells).reverse.map some)
    (cellListCanonicalFinishStartLeft cells)

def cellListCanonicalHandoffConfig
    (cells : List (Option Bool)) (suffixBits : Word Bool) :
    Configuration :=
  { state := CLSS.halt
    tape :=
      Tape.move Direction.left
        (tapeAtCells (cellListCanonicalRestoredLeft cells)
          (suffixBits.map some)) }

def cellListRawMarkingState120WithBase
    (baseLeft processed : List (Option Bool)) (cell : Option Bool)
    (rest : List (Option Bool)) (suffixBits : Word Bool) :
    Configuration :=
  config 120
    (List.append markedTickRev
      (List.append (cellListCanonicalLengthPrefixRev processed.length)
        baseLeft))
    (List.append ((stageNatBits rest.length).map some)
      (List.append ((markedCellsCodeBits processed).map some)
        (List.append ((cellCodeBits cell).map some)
          (List.append ((cellsCodeBits rest).map some)
            (suffixBits.map some)))))

def cellListRawState100AfterMarkedWithBase
    (baseLeft processed : List (Option Bool)) (cell : Option Bool)
    (rest : List (Option Bool)) (suffixBits : Word Bool) :
    Configuration :=
  config 100
    (List.append
      (cellListCanonicalLengthPrefixRev (processed.length + 1))
      baseLeft)
    (List.append ((stageNatBits rest.length).map some)
      (List.append ((markedCellsCodeBits processed).map some)
        (List.append ((markedCellCodeBits cell).map some)
          (List.append ((cellsCodeBits rest).map some)
            (suffixBits.map some)))))

def cellListCanonicalFinishStartLeftWithBase
    (cells baseLeft : List (Option Bool)) : List (Option Bool) :=
  List.append (doneBits.reverse.map some)
    (List.append (cellListCanonicalLengthPrefixRev cells.length)
      baseLeft)

def cellListCanonicalFinishStartConfigWithBase
    (cells baseLeft : List (Option Bool)) (suffixBits : Word Bool) :
    Configuration :=
  config 150 (cellListCanonicalFinishStartLeftWithBase cells baseLeft)
    (List.append ((markedCellsCodeBits cells).map some)
      (suffixBits.map some))

def cellListCanonicalRestoredLeftWithBase
    (cells baseLeft : List (Option Bool)) : List (Option Bool) :=
  List.append ((cellsCodeBits cells).reverse.map some)
    (cellListCanonicalFinishStartLeftWithBase cells baseLeft)

def cellListCanonicalHandoffConfigWithBase
    (cells baseLeft : List (Option Bool)) (suffixBits : Word Bool) :
    Configuration :=
  { state := CLSS.halt
    tape :=
      Tape.move Direction.left
        (tapeAtCells
          (cellListCanonicalRestoredLeftWithBase cells baseLeft)
          (suffixBits.map some)) }

def boolWordCanonicalHandoffConfigWithBase
    (w : Word Bool) (baseLeft : List (Option Bool))
    (suffixBits : Word Bool) : Configuration :=
  cellListCanonicalHandoffConfigWithBase (w.map some) baseLeft suffixBits

def cellListMarkingReturnScanRev
    (processed rest : List (Option Bool)) : Word Bool :=
  List.append [true, true]
    (List.append (markedCellsCodeBits processed).reverse
      (stageNatBits rest.length).reverse)

theorem run_cellList_raw_mark_current_to_state100
    (processed : List (Option Bool)) (cell : Option Bool)
    (rest : List (Option Bool)) (suffixBits : Word Bool) :
    exists steps : Nat,
      CLSS.runConfig steps
          (cellListRawMarkingState120 processed cell rest suffixBits) =
        cellListRawState100AfterMarked processed cell rest suffixBits := by
  let scanRev := cellListMarkingReturnScanRev processed rest
  refine
    ⟨(4 * rest.length + 4) +
        (4 * processed.length + (6 + (scanRev.length + 4))), ?_⟩
  rw [runConfig_add]
  unfold cellListRawMarkingState120
  rw [run_cellList_state120_stageNat]
  rw [runConfig_add]
  rw [run_cellList_state130_markedCells]
  rw [runConfig_add]
  rw [run_cellList_state130_currentCell]
  cases cell with
  | none =>
      have hreturn :=
        run_cellList_state140_returnToLengthMarker scanRev false
          (some false :: some false ::
            cellListCanonicalLengthPrefixRev processed.length)
          (some false ::
            List.append ((cellsCodeBits rest).map some)
              (suffixBits.map some))
      simpa [cellListRawState100AfterMarked, scanRev,
        cellListMarkingReturnScanRev, markedCellCodeBits,
        cellCodeTailCells, cellListCanonicalLengthPrefixRev,
        List.map_append, List.reverse_append, List.append_assoc] using hreturn
  | some b =>
      cases b
      · have hreturn :=
          run_cellList_state140_returnToLengthMarker scanRev false
            (some false :: some false ::
              cellListCanonicalLengthPrefixRev processed.length)
            (some true ::
              List.append ((cellsCodeBits rest).map some)
                (suffixBits.map some))
        simpa [cellListRawState100AfterMarked, scanRev,
          cellListMarkingReturnScanRev, markedCellCodeBits,
          cellCodeTailCells, cellListCanonicalLengthPrefixRev,
          List.map_append, List.reverse_append, List.append_assoc] using
            hreturn
      · have hreturn :=
          run_cellList_state140_returnToLengthMarker scanRev true
            (some false :: some false ::
              cellListCanonicalLengthPrefixRev processed.length)
            (some false ::
              List.append ((cellsCodeBits rest).map some)
                (suffixBits.map some))
        simpa [cellListRawState100AfterMarked, scanRev,
          cellListMarkingReturnScanRev, markedCellCodeBits,
          cellCodeTailCells, cellListCanonicalLengthPrefixRev,
          List.map_append, List.reverse_append, List.append_assoc] using
            hreturn

theorem run_cellList_raw_mark_current_to_state100_withBase
    (baseLeft processed : List (Option Bool)) (cell : Option Bool)
    (rest : List (Option Bool)) (suffixBits : Word Bool) :
    exists steps : Nat,
      CLSS.runConfig steps
          (cellListRawMarkingState120WithBase baseLeft processed cell rest
            suffixBits) =
        cellListRawState100AfterMarkedWithBase baseLeft processed cell rest
          suffixBits := by
  let scanRev := cellListMarkingReturnScanRev processed rest
  refine
    ⟨(4 * rest.length + 4) +
        (4 * processed.length + (6 + (scanRev.length + 4))), ?_⟩
  rw [runConfig_add]
  unfold cellListRawMarkingState120WithBase
  rw [run_cellList_state120_stageNat]
  rw [runConfig_add]
  rw [run_cellList_state130_markedCells]
  rw [runConfig_add]
  rw [run_cellList_state130_currentCell]
  cases cell with
  | none =>
      have hreturn :=
        run_cellList_state140_returnToLengthMarker scanRev false
          (some false :: some false ::
            List.append
              (cellListCanonicalLengthPrefixRev processed.length)
              baseLeft)
          (some false ::
            List.append ((cellsCodeBits rest).map some)
              (suffixBits.map some))
      simpa [cellListRawState100AfterMarkedWithBase, scanRev,
        cellListMarkingReturnScanRev, markedCellCodeBits,
        cellCodeTailCells, cellListCanonicalLengthPrefixRev,
        List.map_append, List.reverse_append, List.append_assoc] using hreturn
  | some b =>
      cases b
      · have hreturn :=
          run_cellList_state140_returnToLengthMarker scanRev false
            (some false :: some false ::
              List.append
                (cellListCanonicalLengthPrefixRev processed.length)
                baseLeft)
            (some true ::
              List.append ((cellsCodeBits rest).map some)
                (suffixBits.map some))
        simpa [cellListRawState100AfterMarkedWithBase, scanRev,
          cellListMarkingReturnScanRev, markedCellCodeBits,
          cellCodeTailCells, cellListCanonicalLengthPrefixRev,
          List.map_append, List.reverse_append, List.append_assoc] using
            hreturn
      · have hreturn :=
          run_cellList_state140_returnToLengthMarker scanRev true
            (some false :: some false ::
              List.append
                (cellListCanonicalLengthPrefixRev processed.length)
                baseLeft)
            (some false ::
              List.append ((cellsCodeBits rest).map some)
                (suffixBits.map some))
        simpa [cellListRawState100AfterMarkedWithBase, scanRev,
          cellListMarkingReturnScanRev, markedCellCodeBits,
          cellCodeTailCells, cellListCanonicalLengthPrefixRev,
          List.map_append, List.reverse_append, List.append_assoc] using
            hreturn

theorem run_cellList_raw_marking_loop_from_state100
    (processed cells : List (Option Bool)) (suffixBits : Word Bool) :
    exists steps : Nat,
      CLSS.runConfig steps
          (config 100
            (cellListCanonicalLengthPrefixRev processed.length)
            (List.append ((stageNatBits cells.length).map some)
              (List.append ((markedCellsCodeBits processed).map some)
                (List.append ((cellsCodeBits cells).map some)
                  (suffixBits.map some))))) =
        cellListCanonicalFinishStartConfig
          (List.append processed cells) suffixBits := by
  induction cells generalizing processed with
  | nil =>
      refine ⟨4, ?_⟩
      rw [show (stageNatBits ([] : List (Option Bool)).length).map some =
          doneBits.map some by
        simp [stageNatBits_zero, doneBits,
          encodeCodeSymbolAsInput]]
      change
        CLSS.runConfig 4
            (config 100
              (cellListCanonicalLengthPrefixRev processed.length)
              (List.append (doneBits.map some)
                (List.append ((markedCellsCodeBits processed).map some)
                  (suffixBits.map some)))) =
          cellListCanonicalFinishStartConfig
            (List.append processed []) suffixBits
      rw [run_cellList_state100_done]
      simp [cellListCanonicalFinishStartConfig,
        cellListCanonicalFinishStartLeft]
  | cons cell rest ih =>
      rcases run_cellList_raw_mark_current_to_state100
          processed cell rest suffixBits with
        ⟨markSteps, hmark⟩
      rcases ih (List.append processed [cell]) with
        ⟨recSteps, hrec⟩
      refine ⟨4 + markSteps + recSteps, ?_⟩
      rw [show 4 + markSteps + recSteps =
          4 + (markSteps + recSteps) by omega]
      rw [runConfig_add]
      rw [show
          (stageNatBits (cell :: rest).length).map some =
            List.append (tickBits.map some)
              ((stageNatBits rest.length).map some) by
        simp [stageNatBits_succ, tickBits,
          encodeCodeSymbolAsInput]]
      rw [show
          List.append
              (List.append (tickBits.map some)
                ((stageNatBits rest.length).map some))
              (List.append ((markedCellsCodeBits processed).map some)
                (List.append ((cellsCodeBits (cell :: rest)).map some)
                  (suffixBits.map some))) =
            List.append (tickBits.map some)
              (List.append ((stageNatBits rest.length).map some)
                (List.append
                  ((markedCellsCodeBits processed).map some)
                  (List.append ((cellCodeBits cell).map some)
                    (List.append ((cellsCodeBits rest).map some)
                      (suffixBits.map some))))) by
        simp [cellsCodeBits, List.map_append, List.append_assoc]]
      change
        CLSS.runConfig (markSteps + recSteps)
            (CLSS.runConfig 4
              (config 100
                (cellListCanonicalLengthPrefixRev processed.length)
                (List.append (tickBits.map some)
                  (List.append ((stageNatBits rest.length).map some)
                    (List.append
                      ((markedCellsCodeBits processed).map some)
                      (List.append ((cellCodeBits cell).map some)
                        (List.append ((cellsCodeBits rest).map some)
                          (suffixBits.map some)))))))) =
          cellListCanonicalFinishStartConfig
            (List.append processed (cell :: rest)) suffixBits
      rw [run_cellList_state100_tick]
      rw [runConfig_add]
      change
        CLSS.runConfig recSteps
            (CLSS.runConfig markSteps
              (cellListRawMarkingState120 processed cell rest
                suffixBits)) =
          cellListCanonicalFinishStartConfig
            (List.append processed (cell :: rest)) suffixBits
      rw [hmark]
      rw [map_markedCellsCodeBits_append_single processed cell] at hrec
      simpa [cellListRawState100AfterMarked, markedCellsCodeBits,
        markedCellsCodeBits_append, cellsCodeBits, List.length_append,
        List.map_append, List.append_assoc] using hrec

theorem run_cellList_raw_marking_loop_from_state100_withBase
    (baseLeft processed cells : List (Option Bool))
    (suffixBits : Word Bool) :
    exists steps : Nat,
      CLSS.runConfig steps
          (config 100
            (List.append
              (cellListCanonicalLengthPrefixRev processed.length)
              baseLeft)
            (List.append ((stageNatBits cells.length).map some)
              (List.append ((markedCellsCodeBits processed).map some)
                (List.append ((cellsCodeBits cells).map some)
                  (suffixBits.map some))))) =
        cellListCanonicalFinishStartConfigWithBase
          (List.append processed cells) baseLeft suffixBits := by
  induction cells generalizing processed with
  | nil =>
      refine ⟨4, ?_⟩
      rw [show (stageNatBits ([] : List (Option Bool)).length).map some =
          doneBits.map some by
        simp [stageNatBits_zero, doneBits,
          encodeCodeSymbolAsInput]]
      change
        CLSS.runConfig 4
            (config 100
              (List.append
                (cellListCanonicalLengthPrefixRev processed.length)
                baseLeft)
              (List.append (doneBits.map some)
                (List.append ((markedCellsCodeBits processed).map some)
                  (suffixBits.map some)))) =
          cellListCanonicalFinishStartConfigWithBase
            (List.append processed []) baseLeft suffixBits
      rw [run_cellList_state100_done]
      simp [cellListCanonicalFinishStartConfigWithBase,
        cellListCanonicalFinishStartLeftWithBase]
  | cons cell rest ih =>
      rcases run_cellList_raw_mark_current_to_state100_withBase
          baseLeft processed cell rest suffixBits with
        ⟨markSteps, hmark⟩
      rcases ih (List.append processed [cell]) with
        ⟨recSteps, hrec⟩
      refine ⟨4 + markSteps + recSteps, ?_⟩
      rw [show 4 + markSteps + recSteps =
          4 + (markSteps + recSteps) by omega]
      rw [runConfig_add]
      rw [show
          (stageNatBits (cell :: rest).length).map some =
            List.append (tickBits.map some)
              ((stageNatBits rest.length).map some) by
        simp [stageNatBits_succ, tickBits,
          encodeCodeSymbolAsInput]]
      rw [show
          List.append
              (List.append (tickBits.map some)
                ((stageNatBits rest.length).map some))
              (List.append ((markedCellsCodeBits processed).map some)
                (List.append ((cellsCodeBits (cell :: rest)).map some)
                  (suffixBits.map some))) =
            List.append (tickBits.map some)
              (List.append ((stageNatBits rest.length).map some)
                (List.append
                  ((markedCellsCodeBits processed).map some)
                  (List.append ((cellCodeBits cell).map some)
                    (List.append ((cellsCodeBits rest).map some)
                      (suffixBits.map some))))) by
        simp [cellsCodeBits, List.map_append, List.append_assoc]]
      change
        CLSS.runConfig (markSteps + recSteps)
            (CLSS.runConfig 4
              (config 100
                (List.append
                  (cellListCanonicalLengthPrefixRev processed.length)
                  baseLeft)
                (List.append (tickBits.map some)
                  (List.append ((stageNatBits rest.length).map some)
                    (List.append
                      ((markedCellsCodeBits processed).map some)
                      (List.append ((cellCodeBits cell).map some)
                        (List.append ((cellsCodeBits rest).map some)
                          (suffixBits.map some)))))))) =
          cellListCanonicalFinishStartConfigWithBase
            (List.append processed (cell :: rest)) baseLeft suffixBits
      rw [run_cellList_state100_tick]
      rw [runConfig_add]
      change
        CLSS.runConfig recSteps
            (CLSS.runConfig markSteps
              (cellListRawMarkingState120WithBase baseLeft processed cell
                rest suffixBits)) =
          cellListCanonicalFinishStartConfigWithBase
            (List.append processed (cell :: rest)) baseLeft suffixBits
      rw [hmark]
      rw [map_markedCellsCodeBits_append_single processed cell] at hrec
      simpa [cellListRawState100AfterMarkedWithBase,
        markedCellsCodeBits, markedCellsCodeBits_append, cellsCodeBits,
        List.length_append, List.map_append, List.append_assoc] using hrec

theorem run_cellList_mark_current_to_state100
    (processed : List (Option Bool)) (cell : Option Bool)
    (rest : List (Option Bool)) (suffixBits : Word Bool) :
    exists steps : Nat,
      CLSS.runConfig steps
          (cellListMarkingState120 processed cell rest suffixBits) =
        cellListState100AfterMarked processed cell rest suffixBits := by
  let scanRev := cellListMarkingReturnScanRev processed rest
  refine
    ⟨(4 * rest.length + 4) +
        (4 * processed.length + (6 + (scanRev.length + 4))), ?_⟩
  rw [runConfig_add]
  unfold cellListMarkingState120
  rw [run_cellList_state120_stageNat]
  rw [runConfig_add]
  rw [run_cellList_state130_markedCells]
  rw [runConfig_add]
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
      CLSS.runConfig steps
          (cellListMarkingState120 processed cell rest suffixBits) =
        cellListFinishStartConfig
          (List.append processed (cell :: rest)) suffixBits := by
  induction rest generalizing processed cell with
  | nil =>
      rcases run_cellList_mark_current_to_state100
          processed cell [] suffixBits with
        ⟨markSteps, hmark⟩
      refine ⟨markSteps + 4, ?_⟩
      rw [runConfig_add]
      rw [hmark]
      unfold cellListState100AfterMarked
      change
        CLSS.runConfig 4
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
      rw [runConfig_add]
      rw [hmark]
      rw [runConfig_add]
      unfold cellListState100AfterMarked
      rw [show
          (stageNatBits (next :: rest).length).map some =
            List.append (tickBits.map some)
              ((stageNatBits rest.length).map some) by
        simp [stageNatBits_succ, tickBits,
          encodeCodeSymbolAsInput]]
      change
        CLSS.runConfig recSteps
            (CLSS.runConfig 4
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
    CLSS.runConfig 1
        (config 150 (cell :: left) (some false :: right)) =
      config CLSS.halt left
        (cell :: some false :: right) := by
  cases cell <;> cases right <;>
    simp [config, tapeAtCells, keepMove,
      cellListSuffix_lookup_150_false,
      runConfig, stepConfig,
      transition,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem run_cellList_finish_to_handoff
    (cells : List (Option Bool)) (suffixTail : Word Bool) :
    exists steps : Nat,
      CLSS.runConfig steps
          (cellListFinishStartConfig cells (false :: suffixTail)) =
        cellListHandoffConfig cells (false :: suffixTail) := by
  refine ⟨4 * cells.length + 1, ?_⟩
  rw [runConfig_add]
  unfold cellListFinishStartConfig
  rw [run_cellList_state150_markedCells]
  change
    CLSS.runConfig 1
      (config 150 (cellListRestoredLeft cells)
        (some false :: suffixTail.map some)) =
      cellListHandoffConfig cells (false :: suffixTail)
  unfold cellListHandoffConfig
  cases hleft : cellListRestoredLeft cells with
  | nil =>
      simp [config, tapeAtCells,
        cellListSuffix_lookup_150_false, keepMove,
        runConfig, stepConfig,
        transition, Tape.read, Tape.write,
        Tape.move, Tape.moveLeft]
  | cons cell left =>
      simpa [config, tapeAtCells, hleft] using
        run_cellList_state150_handoff_false cell left
          (suffixTail.map some)

theorem run_cellList_canonical_finish_to_handoff
    (cells : List (Option Bool)) (suffixTail : Word Bool) :
    exists steps : Nat,
      CLSS.runConfig steps
          (cellListCanonicalFinishStartConfig cells
            (false :: suffixTail)) =
        cellListCanonicalHandoffConfig cells (false :: suffixTail) := by
  refine ⟨4 * cells.length + 1, ?_⟩
  rw [runConfig_add]
  unfold cellListCanonicalFinishStartConfig
  rw [run_cellList_state150_markedCells]
  change
    CLSS.runConfig 1
      (config 150 (cellListCanonicalRestoredLeft cells)
        (some false :: suffixTail.map some)) =
      cellListCanonicalHandoffConfig cells (false :: suffixTail)
  unfold cellListCanonicalHandoffConfig
  cases hleft : cellListCanonicalRestoredLeft cells with
  | nil =>
      simp [config, tapeAtCells,
        cellListSuffix_lookup_150_false, keepMove,
        runConfig, stepConfig,
        transition, Tape.read, Tape.write,
        Tape.move, Tape.moveLeft]
  | cons cell left =>
      simpa [config, tapeAtCells, hleft] using
        run_cellList_state150_handoff_false cell left
          (suffixTail.map some)

theorem run_cellList_canonical_finish_to_handoff_withBase
    (cells baseLeft : List (Option Bool)) (suffixTail : Word Bool) :
    exists steps : Nat,
      CLSS.runConfig steps
          (cellListCanonicalFinishStartConfigWithBase cells baseLeft
            (false :: suffixTail)) =
        cellListCanonicalHandoffConfigWithBase cells baseLeft
          (false :: suffixTail) := by
  refine ⟨4 * cells.length + 1, ?_⟩
  rw [runConfig_add]
  unfold cellListCanonicalFinishStartConfigWithBase
  rw [run_cellList_state150_markedCells]
  change
    CLSS.runConfig 1
      (config 150
        (cellListCanonicalRestoredLeftWithBase cells baseLeft)
        (some false :: suffixTail.map some)) =
      cellListCanonicalHandoffConfigWithBase cells baseLeft
        (false :: suffixTail)
  unfold cellListCanonicalHandoffConfigWithBase
  cases hleft : cellListCanonicalRestoredLeftWithBase cells baseLeft with
  | nil =>
      simp [config, tapeAtCells,
        cellListSuffix_lookup_150_false, keepMove,
        runConfig, stepConfig,
        transition, Tape.read, Tape.write,
        Tape.move, Tape.moveLeft]
  | cons cell left =>
      simpa [config, tapeAtCells, hleft] using
        run_cellList_state150_handoff_false cell left
          (suffixTail.map some)

theorem run_cellList_raw_to_canonical_handoff
    (cells : List (Option Bool)) (suffixTail : Word Bool) :
    exists steps : Nat,
      CLSS.runConfig steps
          (CLSS.initial
            (List.append (stageNatBits cells.length)
              (List.append (cellsCodeBits cells)
                (false :: suffixTail)))) =
        cellListCanonicalHandoffConfig cells (false :: suffixTail) := by
  rcases run_cellList_raw_marking_loop_from_state100
      ([] : List (Option Bool)) cells (false :: suffixTail) with
    ⟨markSteps, hmark⟩
  have hmark' :
      CLSS.runConfig markSteps
          (config 100 []
            (List.append ((stageNatBits cells.length).map some)
              (List.append ((cellsCodeBits cells).map some)
                (some false :: suffixTail.map some)))) =
        cellListCanonicalFinishStartConfig cells
          (false :: suffixTail) := by
    simpa using hmark
  rcases run_cellList_canonical_finish_to_handoff cells suffixTail with
    ⟨finishSteps, hfinish⟩
  refine ⟨markSteps + finishSteps, ?_⟩
  rw [runConfig_add]
  rw [cellListSuffixScannerDescription_initial_eq_config]
  rw [show
      (List.append (stageNatBits cells.length)
        (List.append (cellsCodeBits cells)
          (false :: suffixTail))).map some =
        List.append ((stageNatBits cells.length).map some)
          (List.append ((cellsCodeBits cells).map some)
            (some false :: suffixTail.map some)) by
    simp [List.map_append]]
  rw [hmark']
  exact hfinish

theorem run_cellList_raw_to_canonical_handoff_withBase
    (cells baseLeft : List (Option Bool)) (suffixTail : Word Bool) :
    exists steps : Nat,
      CLSS.runConfig steps
          (config 100 baseLeft
            (List.append ((stageNatBits cells.length).map some)
              (List.append ((cellsCodeBits cells).map some)
                (some false :: suffixTail.map some)))) =
        cellListCanonicalHandoffConfigWithBase cells baseLeft
          (false :: suffixTail) := by
  rcases run_cellList_raw_marking_loop_from_state100_withBase
      baseLeft ([] : List (Option Bool)) cells
      (false :: suffixTail) with
    ⟨markSteps, hmark⟩
  have hmark' :
      CLSS.runConfig markSteps
          (config 100 baseLeft
            (List.append ((stageNatBits cells.length).map some)
              (List.append ((cellsCodeBits cells).map some)
                (some false :: suffixTail.map some)))) =
        cellListCanonicalFinishStartConfigWithBase cells baseLeft
          (false :: suffixTail) := by
    simpa using hmark
  rcases run_cellList_canonical_finish_to_handoff_withBase
      cells baseLeft suffixTail with
    ⟨finishSteps, hfinish⟩
  refine ⟨markSteps + finishSteps, ?_⟩
  rw [runConfig_add]
  rw [hmark']
  exact hfinish

theorem cellListCanonicalRestoredLeftWithBase_ne_nil
    (cells baseLeft : List (Option Bool)) :
    cellListCanonicalRestoredLeftWithBase cells baseLeft ≠ [] := by
  cases cells with
  | nil =>
      simp [cellListCanonicalRestoredLeftWithBase,
        cellListCanonicalFinishStartLeftWithBase, doneBits,
        encodeCodeSymbolAsInput]
  | cons cell rest =>
      cases cell with
      | none =>
          simp [cellListCanonicalRestoredLeftWithBase, cellsCodeBits,
            cellCodeBits, encodeCell,
            encodeCodeWordAsInput,
            encodeCodeSymbolAsInput]
      | some b =>
          cases b <;>
            simp [cellListCanonicalRestoredLeftWithBase, cellsCodeBits,
              cellCodeBits, encodeCell,
              encodeCodeWordAsInput,
              encodeCodeSymbolAsInput]

theorem cellListCanonicalHandoffConfigWithBase_move_right
    (cells baseLeft : List (Option Bool))
    (b : Bool) (suffixTail : Word Bool) :
    Tape.move Direction.right
        (cellListCanonicalHandoffConfigWithBase cells baseLeft
          (b :: suffixTail)).tape =
      tapeAtCells
        (cellListCanonicalRestoredLeftWithBase cells baseLeft)
        ((b :: suffixTail).map some) := by
  unfold cellListCanonicalHandoffConfigWithBase
  cases hleft :
      cellListCanonicalRestoredLeftWithBase cells baseLeft with
  | nil =>
      exfalso
      exact cellListCanonicalRestoredLeftWithBase_ne_nil cells baseLeft
        hleft
  | cons cell left =>
      simpa [hleft] using
        DovetailStagePrefix.tapeAtCells_move_right_move_left_cons
          cell left (some b) (suffixTail.map some)

theorem run_boolWord_raw_to_canonical_handoff_withBase
    (w : Word Bool) (baseLeft : List (Option Bool))
    (suffixTail : Word Bool) :
    exists steps : Nat,
      CLSS.runConfig steps
          (config 100 baseLeft
            (List.append ((stageNatBits w.length).map some)
              (List.append ((cellsCodeBits (w.map some)).map some)
                (some false :: suffixTail.map some)))) =
        boolWordCanonicalHandoffConfigWithBase w baseLeft
          (false :: suffixTail) := by
  simpa [boolWordCanonicalHandoffConfigWithBase] using
    run_cellList_raw_to_canonical_handoff_withBase
      (w.map some) baseLeft suffixTail

theorem run_cellList_marking_loop_to_handoff
    (processed : List (Option Bool)) (cell : Option Bool)
    (rest : List (Option Bool)) (suffixTail : Word Bool) :
    exists steps : Nat,
      CLSS.runConfig steps
          (cellListMarkingState120 processed cell rest
            (false :: suffixTail)) =
        cellListHandoffConfig (List.append processed (cell :: rest))
          (false :: suffixTail) := by
  rcases run_cellList_marking_loop_from_state120 processed cell rest
      (false :: suffixTail) with
    ⟨markSteps, hmark⟩
  rcases run_cellList_finish_to_handoff
      (List.append processed (cell :: rest)) suffixTail with
    ⟨finishSteps, hfinish⟩
  refine ⟨markSteps + finishSteps, ?_⟩
  rw [runConfig_add]
  rw [hmark]
  exact hfinish

end DovetailLayoutScanner
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC
