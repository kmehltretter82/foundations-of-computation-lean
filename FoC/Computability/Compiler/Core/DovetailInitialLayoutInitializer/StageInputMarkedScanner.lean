import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.StageInputValidator

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

namespace DovetailInitialLayoutInitializer
namespace StageInputMarkedScanner

def keep (source : Nat) (read : Bool) (target : Nat) :
    TransitionDescription :=
  MachineDescription.transition source (some read) (some read)
    Direction.right target

def keepMove (source : Nat) (read : Option Bool)
    (move : Direction) (target : Nat) :
    TransitionDescription :=
  MachineDescription.transition source read read move target

def writeMove (source : Nat) (read write : Option Bool)
    (move : Direction) (target : Nat) :
    TransitionDescription :=
  MachineDescription.transition source read write move target

def scanLeftToSentinelRestart
    (scan checkLeft restoreMarker : Nat) :
    List TransitionDescription :=
  [ keepMove scan (some false) Direction.left scan
  , keepMove scan (some true) Direction.left scan
  , keepMove scan none Direction.left checkLeft
  , keepMove checkLeft (some true) Direction.right restoreMarker
  , writeMove restoreMarker none (some false) Direction.right 100
  ]

def scanLeftToSentinelHalt (scan : Nat) :
    List TransitionDescription :=
  [ keepMove scan (some false) Direction.left scan
  , keepMove scan (some true) Direction.left scan
  , keepMove scan none Direction.right 999
  ]

def tickBits : Word Bool :=
  MachineDescription.encodeCodeSymbolAsInput MachineCodeSymbol.tick

def doneBits : Word Bool :=
  MachineDescription.encodeCodeSymbolAsInput MachineCodeSymbol.done

def stageNatBits (stage : Nat) : Word Bool :=
  MachineDescription.encodeCodeWordAsInput
    (MachineDescription.encodeNat stage)

def cellBits (b : Bool) : Word Bool :=
  MachineDescription.encodeCodeSymbolAsInput
    (if b then MachineCodeSymbol.one else MachineCodeSymbol.zero)

def markedCellBits (b : Bool) : Word Bool :=
  if b then
    [true, true, true, false]
  else
    [true, true, false, true]

def cellsBits (w : Word Bool) : Word Bool :=
  MachineDescription.encodeCodeWordAsInput
    (MachineDescription.encodeCellsAppend (w.map some) [])

def markedCellsBits : Word Bool -> Word Bool
  | [] => []
  | b :: rest => List.append (markedCellBits b) (markedCellsBits rest)

@[simp] theorem cellsBits_nil :
    cellsBits ([] : Word Bool) = [] := by
  rfl

@[simp] theorem cellsBits_cons
    (b : Bool) (rest : Word Bool) :
    cellsBits (b :: rest) =
      List.append (cellBits b) (cellsBits rest) := by
  cases b
  · change
      MachineDescription.encodeCodeWordAsInput
          (List.append [MachineCodeSymbol.zero]
            (MachineDescription.encodeCellsAppend
              (List.map some rest) [])) = _
    rw [MachineDescription.encodeCodeWordAsInput_append]
    rfl
  · change
      MachineDescription.encodeCodeWordAsInput
          (List.append [MachineCodeSymbol.one]
            (MachineDescription.encodeCellsAppend
              (List.map some rest) [])) = _
    rw [MachineDescription.encodeCodeWordAsInput_append]
    rfl

@[simp] theorem markedCellsBits_nil :
    markedCellsBits ([] : Word Bool) = [] := by
  rfl

@[simp] theorem markedCellsBits_cons
    (b : Bool) (rest : Word Bool) :
    markedCellsBits (b :: rest) =
      List.append (markedCellBits b) (markedCellsBits rest) := by
  rfl

theorem markedCellsBits_append
    (w tail : Word Bool) :
    markedCellsBits (List.append w tail) =
      List.append (markedCellsBits w) (markedCellsBits tail) := by
  induction w with
  | nil =>
      rfl
  | cons b rest ih =>
      simp [markedCellsBits]
      exact congrArg (fun bits =>
        List.append (markedCellBits b) bits) ih

theorem stageInputSecondBitTail_nil
    (stage : Nat) :
    stageInputSecondBitTail ([] : Word Bool) stage =
      true :: true :: stageNatBits stage := by
  unfold stageInputSecondBitTail stageInputBits
  simp [PairedRecognizerDovetailStageInputCode,
    MachineDescription.DovetailLayout.stageInputCode,
    MachineDescription.DovetailLayout.stageInputCodeAppend,
    MachineDescription.encodeBoolWordAppend,
    MachineDescription.encodeCellListAppend,
    MachineDescription.encodeCellsAppend,
    MachineDescription.encodeNatAppend,
    MachineDescription.encodeNat,
    MachineDescription.encodeCodeWordAsInput,
    MachineDescription.encodeCodeSymbolAsInput,
    stageNatBits]

theorem stageInputSecondBitTail_cons
    (b : Bool) (rest : Word Bool) (stage : Nat) :
    stageInputSecondBitTail (b :: rest) stage =
      true :: false ::
        List.append (stageNatBits rest.length)
          (List.append (cellBits b)
            (List.append (cellsBits rest) (stageNatBits stage))) := by
  cases b <;>
  simp [stageInputSecondBitTail, stageInputBits,
    PairedRecognizerDovetailStageInputCode,
    MachineDescription.DovetailLayout.stageInputCode,
    MachineDescription.DovetailLayout.stageInputCodeAppend,
    MachineDescription.encodeBoolWordAppend,
    MachineDescription.encodeCellListAppend,
    MachineDescription.encodeNatAppend,
    MachineDescription.encodeNat,
    MachineDescription.encodeCellAppend,
    MachineDescription.encodeCell,
    MachineDescription.encodeCellsAppend,
    MachineDescription.encodeCodeSymbolAsInput,
    stageNatBits, cellBits, cellsBits]
  · rw [show
        MachineDescription.encodeCellsAppend (List.map some rest)
            (MachineDescription.encodeNat stage) =
          List.append
            (MachineDescription.encodeCellsAppend
              (List.map some rest) [])
            (MachineDescription.encodeNat stage) by
        simpa using
          (encodeCellsAppend_append (List.map some rest)
            ([] : Word MachineCodeSymbol)
            (MachineDescription.encodeNat stage))]
    change true :: false ::
        MachineDescription.encodeCodeWordAsInput
          (List.append (MachineDescription.encodeNat rest.length)
            (List.append [MachineCodeSymbol.zero]
              (List.append
                (MachineDescription.encodeCellsAppend
                  (List.map some rest) [])
                (MachineDescription.encodeNat stage)))) = _
    rw [MachineDescription.encodeCodeWordAsInput_append]
    rw [MachineDescription.encodeCodeWordAsInput_append]
    rw [MachineDescription.encodeCodeWordAsInput_append]
    simp [MachineDescription.encodeCodeWordAsInput,
      MachineDescription.encodeCodeSymbolAsInput]
  · rw [show
        MachineDescription.encodeCellsAppend (List.map some rest)
            (MachineDescription.encodeNat stage) =
          List.append
            (MachineDescription.encodeCellsAppend
              (List.map some rest) [])
            (MachineDescription.encodeNat stage) by
        simpa using
          (encodeCellsAppend_append (List.map some rest)
            ([] : Word MachineCodeSymbol)
            (MachineDescription.encodeNat stage))]
    change true :: false ::
        MachineDescription.encodeCodeWordAsInput
          (List.append (MachineDescription.encodeNat rest.length)
            (List.append [MachineCodeSymbol.one]
              (List.append
                (MachineDescription.encodeCellsAppend
                  (List.map some rest) [])
                (MachineDescription.encodeNat stage)))) = _
    rw [MachineDescription.encodeCodeWordAsInput_append]
    rw [MachineDescription.encodeCodeWordAsInput_append]
    rw [MachineDescription.encodeCodeWordAsInput_append]
    simp [MachineDescription.encodeCodeWordAsInput,
      MachineDescription.encodeCodeSymbolAsInput]

@[simp] theorem stageNatBits_zero :
    stageNatBits 0 = [false, false, true, true] := by
  rfl

@[simp] theorem stageNatBits_succ (stage : Nat) :
    stageNatBits (stage + 1) =
      false :: false :: true :: false ::
        stageNatBits stage := by
  rfl

theorem stageNatBits_length (stage : Nat) :
    (stageNatBits stage).length = 4 * stage + 4 := by
  induction stage with
  | zero =>
      rfl
  | succ stage ih =>
      simp [stageNatBits_succ, ih]
      omega

def StageInputMarkedScannerDescription :
    MachineDescription where
  stateCount := 1000
  start := 0
  halt := 999
  transitions :=
    [ keepMove 0 (some true) Direction.left 1
    , keepMove 1 none Direction.left 100

    , keep 100 false 101
    , keep 101 false 102
    , keepMove 101 none Direction.right 102
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
    , keep 137 true 130
    , keep 138 false 130

    , writeMove 150 (some true) (some false) Direction.right 152
    , keep 150 false 151
    , writeMove 151 (some false) none Direction.left 160
    , keep 152 true 153
    , keep 153 false 154
    , keep 153 true 155
    , keep 154 true 150
    , keep 155 false 150

    , keepMove 160 (some false) Direction.left 160
    , keepMove 160 (some true) Direction.left 160
    , keepMove 160 none Direction.left 161
    , keepMove 161 (some true) Direction.right 164
    , keepMove 161 (some false) Direction.right 170
    , writeMove 164 none (some false) Direction.left 160
    , keepMove 170 none Direction.right 180

    , keepMove 180 (some false) Direction.right 180
    , keepMove 180 (some true) Direction.right 180
    , writeMove 180 none (some false) Direction.left 200
    , keep 200 false 201
    , keep 201 false 202
    , keep 202 true 203
    , keep 203 false 200
    , keepMove 203 (some true) Direction.right 210
    , keepMove 210 none Direction.left 220
    ]
      ++ scanLeftToSentinelRestart 140 141 142
      ++ scanLeftToSentinelHalt 220

theorem stageInputMarkedScannerDescription_wellFormed :
    StageInputMarkedScannerDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · intro t ht
    exact transition_wellFormed_of_all
      (l := StageInputMarkedScannerDescription.transitions)
      (stateCount := StageInputMarkedScannerDescription.stateCount)
      (by
        native_decide) t ht
  · intro t u ht hu hkey
    exact transition_deterministic_of_all
      (l := StageInputMarkedScannerDescription.transitions)
      (by
        native_decide) t u ht hu hkey

theorem stageInputMarkedScannerDescription_haltTransitionFree :
    StageInputMarkedScannerDescription.HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l := StageInputMarkedScannerDescription.transitions)
    (state := StageInputMarkedScannerDescription.halt)
    (by
      native_decide) t ht

theorem stageInputMarkedScannerDescription_subroutineReady :
    StageInputMarkedScannerDescription.SubroutineReady :=
  ⟨stageInputMarkedScannerDescription_wellFormed,
    stageInputMarkedScannerDescription_haltTransitionFree⟩

theorem run_state180_some
    (b : Bool) (left right : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig 1
        (config 180 left (some b :: right)) =
      config 180 (some b :: left) right := by
  cases b <;> cases right <;>
  simp [StageInputMarkedScannerDescription, config, tapeAtCells,
    keep, keepMove, writeMove, scanLeftToSentinelRestart,
    scanLeftToSentinelHalt,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition, Tape.read, Tape.write,
    Tape.move, Tape.moveRight]

theorem run_state180_bits
    (bits : Word Bool) (left right : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig bits.length
        (config 180 left (List.append (bits.map some) right)) =
      config 180
        (List.append (bits.reverse.map some) left) right := by
  induction bits generalizing left right with
  | nil =>
      rfl
  | cons b rest ih =>
      change
        StageInputMarkedScannerDescription.runConfig
            (rest.length + 1)
            (config 180 left
              (some b :: List.append (rest.map some) right)) =
          config 180
            (List.append ((b :: rest).reverse.map some) left) right
      rw [show rest.length + 1 = 1 + rest.length by omega]
      rw [MachineDescription.runConfig_add]
      rw [run_state180_some]
      rw [ih]
      simp [List.map_append, List.append_assoc]

theorem run_state180_none_cons
    (cell : Option Bool) (left right : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig 1
        (config 180 (cell :: left) (none :: right)) =
      config 200 left (cell :: some false :: right) := by
  cases cell <;>
  simp [StageInputMarkedScannerDescription, config, tapeAtCells,
    keep, keepMove, writeMove, scanLeftToSentinelRestart,
    scanLeftToSentinelHalt,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft]

theorem run_state200_tick
    (left right : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig 4
        (config 200 left
          (List.append (tickBits.map some) right)) =
      config 200
        (List.append (tickBits.reverse.map some) left) right := by
  cases right <;>
  simp [StageInputMarkedScannerDescription, tickBits, config, tapeAtCells,
    keep, keepMove, writeMove, scanLeftToSentinelRestart,
    scanLeftToSentinelHalt,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition, MachineDescription.encodeCodeSymbolAsInput,
    Tape.read, Tape.write, Tape.move, Tape.moveRight]

def donePrefixRev : List (Option Bool) :=
  [some true, some false, some false]

theorem run_state200_done_blank
    (left right : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig 5
        (config 200 left
          (List.append (doneBits.map some) (none :: right))) =
      config 220
        (List.append donePrefixRev left)
        (some true :: none :: right) := by
  cases right <;>
  simp [StageInputMarkedScannerDescription, doneBits, donePrefixRev,
    config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition, MachineDescription.encodeCodeSymbolAsInput,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem run_state120_tick
    (left right : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig 4
        (config 120 left
          (List.append (tickBits.map some) right)) =
      config 120
        (List.append (tickBits.reverse.map some) left) right := by
  cases right <;>
  simp [StageInputMarkedScannerDescription, tickBits,
    config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition,
    MachineDescription.encodeCodeSymbolAsInput,
    Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem run_state120_done
    (left right : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig 4
        (config 120 left
          (List.append (doneBits.map some) right)) =
      config 130
        (List.append (doneBits.reverse.map some) left) right := by
  cases right <;>
  simp [StageInputMarkedScannerDescription, doneBits,
    config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition,
    MachineDescription.encodeCodeSymbolAsInput,
    Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem run_state120_stageNat
    (n : Nat) (left right : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig (4 * n + 4)
        (config 120 left
          (List.append ((stageNatBits n).map some) right)) =
      config 130
        (List.append ((stageNatBits n).reverse.map some) left)
        right := by
  induction n generalizing left with
  | zero =>
      simpa [stageNatBits_zero] using
        run_state120_done left right
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
      rw [run_state120_tick]
      rw [ih]
      simp [stageNatBits_succ, tickBits,
        MachineDescription.encodeCodeSymbolAsInput,
        List.map_append, List.append_assoc]

theorem run_state130_markedCell
    (b : Bool) (left right : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig 4
        (config 130 left
          (List.append ((markedCellBits b).map some) right)) =
      config 130
        (List.append ((markedCellBits b).reverse.map some) left)
        right := by
  cases b <;> cases right <;>
  simp [StageInputMarkedScannerDescription, markedCellBits,
    config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition,
    Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem run_state130_markedCells
    (processed : Word Bool)
    (left right : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig
        (4 * processed.length)
        (config 130 left
          (List.append ((markedCellsBits processed).map some)
            right)) =
      config 130
        (List.append ((markedCellsBits processed).reverse.map some)
          left)
        right := by
  induction processed generalizing left with
  | nil =>
      rfl
  | cons b rest ih =>
      rw [show 4 * (b :: rest).length =
          4 + 4 * rest.length by simp; omega]
      rw [MachineDescription.runConfig_add]
      rw [show
          List.append ((markedCellsBits (b :: rest)).map some)
              right =
            List.append ((markedCellBits b).map some)
              (List.append ((markedCellsBits rest).map some)
                right) by
          simp [markedCellsBits, List.map_append, List.append_assoc]]
      rw [run_state130_markedCell]
      rw [ih]
      simp [markedCellsBits, List.reverse_append, List.map_append,
        List.append_assoc]

theorem run_state130_currentCell
    (b : Bool) (left right : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig 6
        (config 130 left
          (List.append ((cellBits b).map some) right)) =
      config 140 (some true :: some true :: left)
        (some b :: some (!b) :: right) := by
  cases b <;> cases right <;>
  simp [StageInputMarkedScannerDescription, cellBits,
    config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition,
    MachineDescription.encodeCodeSymbolAsInput,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem run_state140_returnToLengthMarker
    (scanRev : Word Bool) (headBit : Bool)
    (leftTail right : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig
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
      simp [StageInputMarkedScannerDescription,
        config, tapeAtCells, keep, keepMove, writeMove,
        scanLeftToSentinelRestart, scanLeftToSentinelHalt,
        MachineDescription.runConfig, MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons b rest ih =>
      rw [show (b :: rest).length + 4 =
          1 + (rest.length + 4) by
        simp
        omega]
      rw [MachineDescription.runConfig_add]
      change
        StageInputMarkedScannerDescription.runConfig (rest.length + 4)
          (StageInputMarkedScannerDescription.runConfig 1
            (config 140
              (some b :: List.append (List.map some rest)
                (none :: some true :: leftTail))
              (some headBit :: right))) =
          config 100 (some false :: some true :: leftTail)
            (List.append (List.map some (b :: rest).reverse)
              (some headBit :: right))
      rw [show
          StageInputMarkedScannerDescription.runConfig 1
            (config 140
              (some b :: List.append (List.map some rest)
                (none :: some true :: leftTail))
              (some headBit :: right)) =
          config 140
            (List.append (List.map some rest)
              (none :: some true :: leftTail))
            (some b :: some headBit :: right) by
        cases headBit <;> cases b <;> cases right <;>
        simp [StageInputMarkedScannerDescription,
          config, tapeAtCells, keep, keepMove, writeMove,
          scanLeftToSentinelRestart, scanLeftToSentinelHalt,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft]]
      rw [ih]
      simp [List.map_append, List.append_assoc]

theorem run_state220_some_cons
    (b : Bool) (left : List (Option Bool))
    (cell : Option Bool) (right : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig 1
        (config 220 (cell :: left) (some b :: right)) =
      config 220 left (cell :: some b :: right) := by
  cases b <;> cases cell <;>
  simp [StageInputMarkedScannerDescription, config, tapeAtCells,
    keep, keepMove, writeMove, scanLeftToSentinelRestart,
    scanLeftToSentinelHalt,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft]

theorem run_state220_some_nil
    (b : Bool) (right : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig 1
        (config 220 [] (some b :: right)) =
      config 220 [] (none :: some b :: right) := by
  cases b <;>
  simp [StageInputMarkedScannerDescription, config, tapeAtCells,
    keep, keepMove, writeMove, scanLeftToSentinelRestart,
    scanLeftToSentinelHalt,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft]

theorem run_state220_none
    (left right : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig 1
        (config 220 left (none :: right)) =
      config 999 (none :: left) right := by
  cases right <;>
  simp [StageInputMarkedScannerDescription, config, tapeAtCells,
    keep, keepMove, writeMove, scanLeftToSentinelRestart,
    scanLeftToSentinelHalt,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition, Tape.read, Tape.write,
    Tape.move, Tape.moveRight]

def state220ScanConfig
    (bitsToLeft : Word Bool) (boundary : Option Bool)
    (leftTail right : List (Option Bool)) :
    MachineDescription.Configuration :=
  match bitsToLeft with
  | [] => config 220 leftTail (boundary :: right)
  | b :: rest =>
      config 220 (List.append (rest.map some) (boundary :: leftTail))
        (some b :: right)

theorem run_state220_bits_to_boundary
    (bitsToLeft : Word Bool) (boundary : Option Bool)
    (leftTail right : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig bitsToLeft.length
        (state220ScanConfig bitsToLeft boundary leftTail right) =
      config 220 leftTail
        (boundary ::
          List.append (bitsToLeft.reverse.map some) right) := by
  induction bitsToLeft generalizing boundary leftTail right with
  | nil =>
      rfl
  | cons b rest ih =>
      rw [show (b :: rest).length = rest.length + 1 by simp]
      rw [show rest.length + 1 = 1 + rest.length by omega]
      rw [MachineDescription.runConfig_add]
      cases rest with
      | nil =>
          change
            StageInputMarkedScannerDescription.runConfig 0
                (StageInputMarkedScannerDescription.runConfig 1
                  (config 220 (boundary :: leftTail)
                    (some b :: right))) =
              config 220 leftTail (boundary :: some b :: right)
          rw [run_state220_some_cons]
          rfl
      | cons b' rest =>
          change
            StageInputMarkedScannerDescription.runConfig
                (b' :: rest).length
                (StageInputMarkedScannerDescription.runConfig 1
                  (config 220
                    (some b' ::
                      List.append (rest.map some)
                        (boundary :: leftTail))
                    (some b :: right))) =
              config 220 leftTail
                (boundary ::
                  List.append
                    ((b :: b' :: rest).reverse.map some)
                    right)
          rw [run_state220_some_cons]
          have h := ih boundary leftTail (some b :: right)
          simp [state220ScanConfig] at h
          simpa [List.map_append, List.append_assoc] using h

theorem run_state200_done_end
    (pre : Word Bool) (boundary : Option Bool)
    (leftTail : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig 5
        (config 200
          (List.append (pre.reverse.map some) (boundary :: leftTail))
          (doneBits.map some)) =
      state220ScanConfig ((List.append pre doneBits).reverse)
        boundary leftTail [none] := by
  simp [StageInputMarkedScannerDescription, doneBits,
    state220ScanConfig, config, tapeAtCells, keep, keepMove,
    writeMove, scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition,
    MachineDescription.encodeCodeSymbolAsInput,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
    List.reverse_append]

theorem run_state200_stageNat_end
    (stage : Nat) (pre : Word Bool) (boundary : Option Bool)
    (leftTail : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig (4 * stage + 5)
        (config 200
          (List.append (pre.reverse.map some) (boundary :: leftTail))
          ((stageNatBits stage).map some)) =
      state220ScanConfig
        ((List.append pre (stageNatBits stage)).reverse)
        boundary leftTail [none] := by
  induction stage generalizing pre with
  | zero =>
      simpa [stageNatBits_zero] using
        run_state200_done_end pre boundary leftTail
  | succ stage ih =>
      rw [show 4 * (stage + 1) + 5 =
          4 + (4 * stage + 5) by omega]
      rw [MachineDescription.runConfig_add]
      rw [show
          (stageNatBits (stage + 1)).map some =
            List.append (tickBits.map some)
              ((stageNatBits stage).map some) by
          simp [stageNatBits_succ, tickBits,
            MachineDescription.encodeCodeSymbolAsInput]]
      rw [run_state200_tick]
      have h := ih (List.append pre tickBits)
      simpa [stageNatBits_succ, tickBits,
        MachineDescription.encodeCodeSymbolAsInput,
        List.reverse_append, List.map_append, List.append_assoc] using h

theorem run_start_nil_to_state200
    (stage : Nat) :
    StageInputMarkedScannerDescription.runConfig 18
        { state := StageInputMarkedScannerDescription.start
          tape := stageInputSecondBitMarkedHandoffTape
            ([] : Word Bool) stage } =
      config 200 [some true, some true, none, some false]
        ((stageNatBits stage).map some) := by
  unfold stageInputSecondBitMarkedHandoffTape
  unfold stageInputSecondBitMarkedTape
  rw [stageInputSecondBitTail_nil]
  cases stage <;>
  simp [StageInputMarkedScannerDescription, stageNatBits,
    MachineDescription.encodeNat,
    MachineDescription.encodeCodeWordAsInput,
    MachineDescription.encodeCodeSymbolAsInput,
    config, tapeAtCells,
    keep, keepMove, writeMove, scanLeftToSentinelRestart,
    scanLeftToSentinelHalt,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem run_start_nil
    (stage : Nat) :
    StageInputMarkedScannerDescription.runConfig (30 + 8 * stage)
        { state := StageInputMarkedScannerDescription.start
          tape := stageInputSecondBitMarkedHandoffTape
            ([] : Word Bool) stage } =
      { state := StageInputMarkedScannerDescription.halt
        tape :=
          stageInputSecondBitMarkedCheckedHandoffTape
            ([] : Word Bool) stage } := by
  let pre : Word Bool := [true, true]
  let bitsToLeft : Word Bool :=
    (List.append pre (stageNatBits stage)).reverse
  rw [show 30 + 8 * stage =
      18 + ((4 * stage + 5) + (bitsToLeft.length + 1)) by
    simp [bitsToLeft, pre, stageNatBits_length]
    omega]
  rw [MachineDescription.runConfig_add]
  rw [run_start_nil_to_state200]
  rw [MachineDescription.runConfig_add]
  change
    StageInputMarkedScannerDescription.runConfig
        (bitsToLeft.length + 1)
        (StageInputMarkedScannerDescription.runConfig (4 * stage + 5)
          (config 200
            (List.append (pre.reverse.map some)
              (none :: [some false]))
            ((stageNatBits stage).map some))) =
      { state := StageInputMarkedScannerDescription.halt
        tape :=
          stageInputSecondBitMarkedCheckedHandoffTape
            ([] : Word Bool) stage }
  rw [run_state200_stageNat_end]
  rw [MachineDescription.runConfig_add]
  rw [run_state220_bits_to_boundary]
  rw [run_state220_none]
  subst bitsToLeft
  subst pre
  unfold stageInputSecondBitMarkedCheckedHandoffTape
  unfold stageInputSecondBitMarkedCheckedTape
  rw [stageInputSecondBitTail_nil]
  simp [StageInputMarkedScannerDescription, config, tapeAtCells,
    Tape.move, Tape.moveRight]

theorem stageInputMarkedScannerDescription_spec :
    StageInputMarkedScannerSpec StageInputMarkedScannerDescription := by
  constructor
  · exact stageInputMarkedScannerDescription_subroutineReady
  constructor
  · intro w stage
    refine
      ⟨30 + 36 * w.length + 8 * w.length * (w.length + 1) +
        8 * stage, ?_⟩
    induction w generalizing stage with
    | nil =>
        simpa using run_start_nil stage
    | cons b rest ih =>
        sorry
  · intro code Tmark T hmark hscanner
    sorry

end StageInputMarkedScanner

export StageInputMarkedScanner
  (StageInputMarkedScannerDescription
   stageInputMarkedScannerDescription_subroutineReady
   stageInputMarkedScannerDescription_spec)

end DovetailInitialLayoutInitializer
end Computability
end FoC
