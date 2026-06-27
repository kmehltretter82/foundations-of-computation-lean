import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.StageInputValidator

set_option doc.verso true

/-!
# Stage-input marked scanner

This module builds the middle scanner used by the stage-input recognizer.  The
preceding marker subroutine has erased the second input bit; the scanner checks
the remaining stage-input payload, restores any marked cells to the ordinary
encoded form, appends the trailing blank used by the checked handoff, and halts
with the head still in the handoff position.

The proof is intentionally organized around machine phases.  The finite
transition table is concrete, but the exported facts are stated in terms of the
encoded payload views, so later initializer modules can avoid expanding the
table.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace DovetailInitialLayoutInitializer
namespace StageInputMarkedScanner

/-!
**Transition combinators.**  These small constructors keep the concrete table
for {lit}`StageInputMarkedScannerDescription` readable.  The scanner has two
left-scan patterns: one returns to the current length marker and restarts at
state {lit}`100`, while the final one halts after finding the checked boundary.
-/

def keep (source : Nat) (read : Bool) (target : Nat) :
    TransitionDescription :=
  transition source (some read) (some read)
    Direction.right target

def keepMove (source : Nat) (read : Option Bool)
    (move : Direction) (target : Nat) :
    TransitionDescription :=
  transition source read read move target

def writeMove (source : Nat) (read write : Option Bool)
    (move : Direction) (target : Nat) :
    TransitionDescription :=
  transition source read write move target

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

/-!
**Encoding views.**  The scanner works over the second-bit-marked suffix of a
stage input.  The definitions below name the pieces that appear repeatedly in
the tape shape: encoded ticks, the {name}`MachineCodeSymbol.done` delimiter,
encoded stage numbers, ordinary payload cells, and the temporary marked payload
cells used while scanning.
-/

def tickBits : Word Bool :=
  encodeCodeSymbolAsInput MachineCodeSymbol.tick

def doneBits : Word Bool :=
  encodeCodeSymbolAsInput MachineCodeSymbol.done

def stageNatBits (stage : Nat) : Word Bool :=
  encodeCodeWordAsInput
    (encodeNat stage)

def cellBits (b : Bool) : Word Bool :=
  encodeCodeSymbolAsInput
    (if b then MachineCodeSymbol.one else MachineCodeSymbol.zero)

def markedCellBits (b : Bool) : Word Bool :=
  if b then
    [true, true, true, false]
  else
    [true, true, false, true]

def cellsBits (w : Word Bool) : Word Bool :=
  encodeCodeWordAsInput
    (encodeCellsAppend (w.map some) [])

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
      encodeCodeWordAsInput
          (List.append [MachineCodeSymbol.zero]
            (encodeCellsAppend
              (List.map some rest) [])) = _
    rw [encodeCodeWordAsInput_append]
    rfl
  · change
      encodeCodeWordAsInput
          (List.append [MachineCodeSymbol.one]
            (encodeCellsAppend
              (List.map some rest) [])) = _
    rw [encodeCodeWordAsInput_append]
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

theorem markedCellsBits_append_single
    (w : Word Bool) (b : Bool) :
    markedCellsBits (List.append w [b]) =
      List.append (markedCellsBits w) (markedCellBits b) := by
  simpa [markedCellsBits] using
    markedCellsBits_append w [b]

theorem markedCellsBits_append_single_map
    (w : Word Bool) (b : Bool) :
    (markedCellsBits (List.append w [b])).map some =
      List.append ((markedCellsBits w).map some)
        ((markedCellBits b).map some) := by
  simpa [List.map_append] using
    congrArg (List.map some) (markedCellsBits_append_single w b)

theorem cellBits_length (b : Bool) :
    (cellBits b).length = 4 := by
  cases b <;> rfl

theorem markedCellBits_length (b : Bool) :
    (markedCellBits b).length = 4 := by
  cases b <;> rfl

theorem markedCellsBits_length
    (w : Word Bool) :
    (markedCellsBits w).length = 4 * w.length := by
  induction w with
  | nil =>
      rfl
  | cons _ rest ih =>
      simp [markedCellsBits, markedCellBits_length, ih]
      omega

theorem stageInputSecondBitTail_nil
    (stage : Nat) :
    stageInputSecondBitTail ([] : Word Bool) stage =
      true :: true :: stageNatBits stage := by
  unfold stageInputSecondBitTail stageInputBits
  simp [PairedRecognizerDovetailStageInputCode,
    DovetailLayout.stageInputCode,
    DovetailLayout.stageInputCodeAppend,
    encodeBoolWordAppend,
    encodeCellListAppend,
    encodeCellsAppend,
    encodeNatAppend,
    encodeNat,
    encodeCodeWordAsInput,
    encodeCodeSymbolAsInput,
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
    DovetailLayout.stageInputCode,
    DovetailLayout.stageInputCodeAppend,
    encodeBoolWordAppend,
    encodeCellListAppend,
    encodeNatAppend,
    encodeNat,
    encodeCellAppend,
    encodeCell,
    encodeCellsAppend,
    encodeCodeSymbolAsInput,
    stageNatBits, cellBits, cellsBits]
  · rw [show
        encodeCellsAppend (List.map some rest)
            (encodeNat stage) =
          List.append
            (encodeCellsAppend
              (List.map some rest) [])
            (encodeNat stage) by
        simpa using
          (encodeCellsAppend_append (List.map some rest)
            ([] : Word MachineCodeSymbol)
            (encodeNat stage))]
    change true :: false ::
        encodeCodeWordAsInput
          (List.append (encodeNat rest.length)
            (List.append [MachineCodeSymbol.zero]
              (List.append
                (encodeCellsAppend
                  (List.map some rest) [])
                (encodeNat stage)))) = _
    rw [encodeCodeWordAsInput_append]
    rw [encodeCodeWordAsInput_append]
    rw [encodeCodeWordAsInput_append]
    simp [encodeCodeWordAsInput,
      encodeCodeSymbolAsInput]
  · rw [show
        encodeCellsAppend (List.map some rest)
            (encodeNat stage) =
          List.append
            (encodeCellsAppend
              (List.map some rest) [])
            (encodeNat stage) by
        simpa using
          (encodeCellsAppend_append (List.map some rest)
            ([] : Word MachineCodeSymbol)
            (encodeNat stage))]
    change true :: false ::
        encodeCodeWordAsInput
          (List.append (encodeNat rest.length)
            (List.append [MachineCodeSymbol.one]
              (List.append
                (encodeCellsAppend
                  (List.map some rest) [])
                (encodeNat stage)))) = _
    rw [encodeCodeWordAsInput_append]
    rw [encodeCodeWordAsInput_append]
    rw [encodeCodeWordAsInput_append]
    simp [encodeCodeWordAsInput,
      encodeCodeSymbolAsInput]

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

/-!
The final stage-number scan starts by consuming the two leading false bits of
the encoded natural.  Naming that shape keeps the state {lit}`150` finishing
lemmas independent of the recursive definition of {name}`stageNatBits`.
-/

theorem stageNatBits_false_false_tail
    (stage : Nat) :
    exists tail : Word Bool,
      stageNatBits stage = false :: false :: tail := by
  cases stage with
  | zero =>
      exact ⟨[true, true], rfl⟩
  | succ stage =>
      exact ⟨true :: false :: stageNatBits stage, by
        simp [stageNatBits_succ]⟩

/-!
**Concrete scanner table.**  The states are grouped by phase:
state {lit}`100` scans the length prefix and marks the next tick, state
{lit}`120` skips the remaining length prefix, state {lit}`130` marks the
current payload cell, state {lit}`140` scans back to the marked length
sentinel, state {lit}`150` restores marked payload cells during the finish
pass, and states {lit}`180`, {lit}`200`, and {lit}`220` append and verify the
final checked blank.
-/

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
  refine ⟨by native_decide, by native_decide, by native_decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := StageInputMarkedScannerDescription.transitions)
      (stateCount := StageInputMarkedScannerDescription.stateCount)
      (by native_decide)
  · exact transition_deterministic_of_all
      (l := StageInputMarkedScannerDescription.transitions)
      (by native_decide)

theorem stageInputMarkedScannerDescription_haltTransitionFree :
    StageInputMarkedScannerDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := StageInputMarkedScannerDescription.transitions)
    (state := StageInputMarkedScannerDescription.halt)
    (by native_decide)

theorem stageInputMarkedScannerDescription_subroutineReady :
    StageInputMarkedScannerDescription.SubroutineReady :=
  ⟨stageInputMarkedScannerDescription_wellFormed,
    stageInputMarkedScannerDescription_haltTransitionFree⟩

/-!
**Length-marker and finish helpers.**  These are the phase-local facts that
keep the remaining forward proof manageable.  State {lit}`100` either consumes
an unmarked tick and moves to state {lit}`120`, or recognizes the
{name}`MachineCodeSymbol.done` delimiter and enters the finish pass.  State
{lit}`150` restores marked payload cells to the ordinary
{name}`cellBits` encoding before crossing the first two bits of the stage
number and handing control to the left scan.
-/

def markedTickRev : List (Option Bool) :=
  [none, some true, some false, some false]

theorem run_state100_tick
    (left tail : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig 4
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

theorem run_state100_done
    (left tail : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig 4
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

theorem run_state150_markedCell
    (b : Bool) (left right : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig 4
        (config 150 left
          (List.append ((markedCellBits b).map some) right)) =
      config 150
        (List.append ((cellBits b).reverse.map some) left)
        right := by
  cases b <;> cases right <;>
  simp [StageInputMarkedScannerDescription, markedCellBits,
    cellBits,
    config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition,
    encodeCodeSymbolAsInput,
    Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem run_state150_markedCells
    (processed : Word Bool)
    (left right : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig
        (4 * processed.length)
        (config 150 left
          (List.append ((markedCellsBits processed).map some)
            right)) =
      config 150
        (List.append ((cellsBits processed).reverse.map some)
          left)
        right := by
  induction processed generalizing left with
  | nil =>
      rfl
  | cons b rest ih =>
      rw [show 4 * (b :: rest).length =
          4 + 4 * rest.length by simp; omega]
      rw [runConfig_add]
      rw [show
          List.append ((markedCellsBits (b :: rest)).map some)
              right =
            List.append ((markedCellBits b).map some)
              (List.append ((markedCellsBits rest).map some)
                right) by
          simp [markedCellsBits, List.map_append, List.append_assoc]]
      rw [run_state150_markedCell]
      rw [ih]
      simp [List.reverse_append, List.map_append,
        List.append_assoc]

theorem run_state150_to_state160
    (left tail : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig 2
        (config 150 left (some false :: some false :: tail)) =
      config 160 left (some false :: none :: tail) := by
  cases tail <;>
  simp [StageInputMarkedScannerDescription,
    config, tapeAtCells, keep, keepMove, writeMove,
    scanLeftToSentinelRestart, scanLeftToSentinelHalt,
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem run_state150_stageNat_to_state160
    (stage : Nat) (left : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig 2
        (config 150 left ((stageNatBits stage).map some)) =
      config 160 left
        (some false :: none ::
          ((stageNatBits stage).drop 2).map some) := by
  rcases stageNatBits_false_false_tail stage with ⟨tail, htail⟩
  rw [htail]
  simpa using run_state150_to_state160 left (tail.map some)

theorem run_state150_markedCells_to_state160
    (processed : Word Bool) (stage : Nat)
    (left : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig
        (4 * processed.length + 2)
        (config 150 left
          (List.append ((markedCellsBits processed).map some)
            ((stageNatBits stage).map some))) =
      config 160
        (List.append ((cellsBits processed).reverse.map some) left)
        (some false :: none ::
          ((stageNatBits stage).drop 2).map some) := by
  rw [runConfig_add]
  rw [run_state150_markedCells]
  rw [run_state150_stageNat_to_state160]

/-!
**Append and boundary scans.**  After the finish pass has restored the payload,
state {lit}`180` moves right to the blank where the checked separator is
written.  States {lit}`200` and {lit}`220` then rescan the final stage number
and move left to the boundary that should become the halted head position.
-/

theorem run_state180_some
    (b : Bool) (left right : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig 1
        (config 180 left (some b :: right)) =
      config 180 (some b :: left) right := by
  cases b <;> cases right <;>
  simp [StageInputMarkedScannerDescription, config, tapeAtCells,
    keep, keepMove, writeMove, scanLeftToSentinelRestart,
    scanLeftToSentinelHalt,
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition, Tape.read, Tape.write,
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
      rw [runConfig_add]
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
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition, Tape.read, Tape.write,
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
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition, encodeCodeSymbolAsInput,
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
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition, encodeCodeSymbolAsInput,
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
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition,
    encodeCodeSymbolAsInput,
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
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition,
    encodeCodeSymbolAsInput,
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
      rw [runConfig_add]
      rw [show
          List.append ((stageNatBits (n + 1)).map some) right =
            List.append (tickBits.map some)
              (List.append ((stageNatBits n).map some) right) by
          simp [stageNatBits_succ, tickBits,
            encodeCodeSymbolAsInput]]
      rw [run_state120_tick]
      rw [ih]
      simp [stageNatBits_succ, tickBits,
        encodeCodeSymbolAsInput,
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
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition,
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
      rw [runConfig_add]
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
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition,
    encodeCodeSymbolAsInput,
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
        runConfig, stepConfig,
        lookupTransition, Matches,
        transition,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons b rest ih =>
      rw [show (b :: rest).length + 4 =
          1 + (rest.length + 4) by
        simp
        omega]
      rw [runConfig_add]
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
          runConfig, stepConfig,
          lookupTransition, Matches,
          transition,
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
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition, Tape.read, Tape.write,
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
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition, Tape.read, Tape.write,
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
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition, Tape.read, Tape.write,
    Tape.move, Tape.moveRight]

def state220ScanConfig
    (bitsToLeft : Word Bool) (boundary : Option Bool)
    (leftTail right : List (Option Bool)) :
    Configuration :=
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
      rw [runConfig_add]
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
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition,
    encodeCodeSymbolAsInput,
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
      rw [runConfig_add]
      rw [show
          (stageNatBits (stage + 1)).map some =
            List.append (tickBits.map some)
              ((stageNatBits stage).map some) by
          simp [stageNatBits_succ, tickBits,
            encodeCodeSymbolAsInput]]
      rw [run_state200_tick]
      have h := ih (List.append pre tickBits)
      simpa [stageNatBits_succ, tickBits,
        encodeCodeSymbolAsInput,
        List.reverse_append, List.map_append, List.append_assoc] using h

/-!
**Entry configurations.**  The two public forward runners split on the payload
length.  The empty payload reaches the final append phase directly, while a
nonempty payload first enters state {lit}`120` after marking the current length
tick.
-/

theorem run_start_cons_to_state120
    (b : Bool) (rest : Word Bool) (stage : Nat) :
    StageInputMarkedScannerDescription.runConfig 6
        { state := StageInputMarkedScannerDescription.start
          tape :=
            stageInputSecondBitMarkedHandoffTape
              (b :: rest) stage } =
      config 120 [none, some true, none, some false]
        (List.append ((stageNatBits rest.length).map some)
          (List.append ((cellBits b).map some)
            (List.append ((cellsBits rest).map some)
              ((stageNatBits stage).map some)))) := by
  unfold stageInputSecondBitMarkedHandoffTape
  unfold stageInputSecondBitMarkedTape
  rw [stageInputSecondBitTail_cons]
  change
    StageInputMarkedScannerDescription.runConfig 6
        { state := StageInputMarkedScannerDescription.start
          tape :=
            Tape.move Direction.right
              (tapeAtCells [some false]
                (none ::
                  List.map some
                    (true :: false ::
                      List.append (stageNatBits rest.length)
                        (List.append (cellBits b)
                          (List.append (cellsBits rest)
                            (stageNatBits stage)))))) } =
      config 120 [none, some true, none, some false]
        (List.append ((stageNatBits rest.length).map some)
          (List.append ((cellBits b).map some)
            (List.append ((cellsBits rest).map some)
              ((stageNatBits stage).map some))))
  cases b
  · simp [StageInputMarkedScannerDescription,
      config, tapeAtCells,
      keep, keepMove, writeMove, scanLeftToSentinelRestart,
      scanLeftToSentinelHalt,
      runConfig, stepConfig,
      lookupTransition, Matches,
      transition, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft, Tape.moveRight]
    generalize
        List.map some (stageNatBits rest.length) ++
          (List.map some (cellBits false) ++
            (List.map some (cellsBits rest) ++
              List.map some (stageNatBits stage))) = cells
    cases cells <;> rfl
  · simp [StageInputMarkedScannerDescription,
      config, tapeAtCells,
      keep, keepMove, writeMove, scanLeftToSentinelRestart,
      scanLeftToSentinelHalt,
      runConfig, stepConfig,
      lookupTransition, Matches,
      transition, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft, Tape.moveRight]
    generalize
        List.map some (stageNatBits rest.length) ++
          (List.map some (cellBits true) ++
            (List.map some (cellsBits rest) ++
              List.map some (stageNatBits stage))) = cells
    cases cells <;> rfl

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
    encodeNat,
    encodeCodeWordAsInput,
    encodeCodeSymbolAsInput,
    config, tapeAtCells,
    keep, keepMove, writeMove, scanLeftToSentinelRestart,
    scanLeftToSentinelHalt,
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition, Tape.read, Tape.write,
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
  rw [runConfig_add]
  rw [run_start_nil_to_state200]
  rw [runConfig_add]
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
  rw [runConfig_add]
  rw [run_state220_bits_to_boundary]
  rw [run_state220_none]
  subst bitsToLeft
  subst pre
  unfold stageInputSecondBitMarkedCheckedHandoffTape
  unfold stageInputSecondBitMarkedCheckedTape
  rw [stageInputSecondBitTail_nil]
  simp [StageInputMarkedScannerDescription, config, tapeAtCells,
    Tape.move, Tape.moveRight]

/-!
**Forward proof split.**  The exported specification only needs an existential
run length, so the nonempty case is split around named phase contracts instead
of carrying one large arithmetic expression.  The first remaining obligation is
the marking loop from state {lit}`120` to the beginning of the finish pass; the
second is the finish pass from that intermediate configuration to the checked
handoff tape.
-/

def markedStartConfig (w : Word Bool) (stage : Nat) :
    Configuration :=
  { state := StageInputMarkedScannerDescription.start
    tape := stageInputSecondBitMarkedHandoffTape w stage }

def checkedHaltConfig (w : Word Bool) (stage : Nat) :
    Configuration :=
  { state := StageInputMarkedScannerDescription.halt
    tape := stageInputSecondBitMarkedCheckedHandoffTape w stage }

def state120AfterStartConfig
    (b : Bool) (rest : Word Bool) (stage : Nat) :
    Configuration :=
  config 120 [none, some true, none, some false]
    (List.append ((stageNatBits rest.length).map some)
      (List.append ((cellBits b).map some)
        (List.append ((cellsBits rest).map some)
          ((stageNatBits stage).map some))))

/-!
**Finish boundary views.**  The marking loop ends at state {lit}`150` with the
payload rewritten as marked cells and with the already-scanned length/delimiter
prefix on the left.  The exact left prefix is part of
{lit}`finishStartConfig`, so later phase lemmas no longer hide the handoff
behind an arbitrary existential configuration.
-/

def finishLengthPrefixRev : Nat -> List (Option Bool)
  | 0 => [some false, some true, none, some false]
  | n + 1 =>
      List.append (tickBits.reverse.map some)
        (finishLengthPrefixRev n)

def finishStartLeft (w : Word Bool) : List (Option Bool) :=
  List.append (doneBits.reverse.map some)
    (finishLengthPrefixRev (w.length - 1))

def finishStartConfig (w : Word Bool) (stage : Nat) :
    Configuration :=
  config 150 (finishStartLeft w)
    (List.append ((markedCellsBits w).map some)
      ((stageNatBits stage).map some))

def activeLengthPrefixTail : Nat -> List (Option Bool)
  | 0 => [none, some false]
  | n + 1 =>
      List.append [some false, some false]
        (finishLengthPrefixRev n)

def activeLengthPrefixRev (n : Nat) : List (Option Bool) :=
  none :: some true :: activeLengthPrefixTail n

theorem activeLengthPrefixRev_zero :
    activeLengthPrefixRev 0 =
      [none, some true, none, some false] := by
  rfl

theorem activeLengthPrefixRev_succ (n : Nat) :
    activeLengthPrefixRev (n + 1) =
      List.append markedTickRev (finishLengthPrefixRev n) := by
  rfl

theorem activeLengthPrefixRestored (n : Nat) :
    some false :: some true :: activeLengthPrefixTail n =
      finishLengthPrefixRev n := by
  cases n with
  | zero =>
      rfl
  | succ n =>
      rfl

def markingState120
    (processed : Word Bool) (b : Bool) (rest : Word Bool)
    (stage : Nat) : Configuration :=
  config 120 (activeLengthPrefixRev processed.length)
    (List.append ((stageNatBits rest.length).map some)
      (List.append ((markedCellsBits processed).map some)
        (List.append ((cellBits b).map some)
          (List.append ((cellsBits rest).map some)
            ((stageNatBits stage).map some)))))

def state100AfterMarked
    (processed : Word Bool) (b : Bool) (rest : Word Bool)
    (stage : Nat) : Configuration :=
  config 100 (finishLengthPrefixRev processed.length)
    (List.append ((stageNatBits rest.length).map some)
      (List.append ((markedCellsBits processed).map some)
        (List.append ((markedCellBits b).map some)
          (List.append ((cellsBits rest).map some)
            ((stageNatBits stage).map some)))))

def markingReturnScanRev
    (processed : Word Bool) (rest : Word Bool) : Word Bool :=
  List.append [true, true]
    (List.append (markedCellsBits processed).reverse
      (stageNatBits rest.length).reverse)

theorem run_mark_current_to_state100
    (processed : Word Bool) (b : Bool) (rest : Word Bool)
    (stage : Nat) :
    exists steps : Nat,
      StageInputMarkedScannerDescription.runConfig steps
          (markingState120 processed b rest stage) =
        state100AfterMarked processed b rest stage := by
  let scanRev := markingReturnScanRev processed rest
  refine
    ⟨(4 * rest.length + 4) +
        (4 * processed.length + (6 + (scanRev.length + 4))), ?_⟩
  rw [runConfig_add]
  unfold markingState120
  rw [run_state120_stageNat]
  rw [runConfig_add]
  rw [run_state130_markedCells]
  rw [runConfig_add]
  rw [run_state130_currentCell]
  have hreturn :=
    run_state140_returnToLengthMarker scanRev b
      (activeLengthPrefixTail processed.length)
      (some (!b) ::
        List.append ((cellsBits rest).map some)
          ((stageNatBits stage).map some))
  cases b <;>
  simpa [state100AfterMarked, scanRev, markingReturnScanRev,
    activeLengthPrefixRev, activeLengthPrefixRestored,
    markedCellBits, List.map_append, List.reverse_append,
    List.append_assoc] using hreturn

theorem run_marking_loop_from_state120
    (processed : Word Bool) (b : Bool) (rest : Word Bool)
    (stage : Nat) :
    exists steps : Nat,
      StageInputMarkedScannerDescription.runConfig steps
          (markingState120 processed b rest stage) =
        finishStartConfig (List.append processed (b :: rest)) stage := by
  induction rest generalizing processed b with
  | nil =>
      rcases run_mark_current_to_state100 processed b [] stage with
        ⟨markSteps, hmark⟩
      refine ⟨markSteps + 4, ?_⟩
      rw [runConfig_add]
      rw [hmark]
      unfold state100AfterMarked
      change
        StageInputMarkedScannerDescription.runConfig 4
            (config 100 (finishLengthPrefixRev processed.length)
              (List.append (doneBits.map some)
                (List.append ((markedCellsBits processed).map some)
                  (List.append ((markedCellBits b).map some)
                    ((stageNatBits stage).map some))))) =
          finishStartConfig (List.append processed [b]) stage
      rw [run_state100_done]
      unfold finishStartConfig finishStartLeft
      rw [markedCellsBits_append_single_map]
      simp [List.length_append, List.append_assoc]
  | cons next rest ih =>
      rcases run_mark_current_to_state100 processed b
          (next :: rest) stage with
        ⟨markSteps, hmark⟩
      rcases ih (List.append processed [b]) next with
        ⟨recSteps, hrec⟩
      refine ⟨markSteps + 4 + recSteps, ?_⟩
      rw [show markSteps + 4 + recSteps =
          markSteps + (4 + recSteps) by omega]
      rw [runConfig_add]
      rw [hmark]
      rw [runConfig_add]
      unfold state100AfterMarked
      rw [show
          (stageNatBits (next :: rest).length).map some =
            List.append (tickBits.map some)
              ((stageNatBits rest.length).map some) by
        simp [stageNatBits_succ, tickBits,
          encodeCodeSymbolAsInput]]
      change
        StageInputMarkedScannerDescription.runConfig recSteps
            (StageInputMarkedScannerDescription.runConfig 4
              (config 100 (finishLengthPrefixRev processed.length)
                (List.append (tickBits.map some)
                  (List.append ((stageNatBits rest.length).map some)
                    (List.append ((markedCellsBits processed).map some)
                      (List.append ((markedCellBits b).map some)
                        (List.append
                          ((cellsBits (next :: rest)).map some)
                          ((stageNatBits stage).map some)))))))) =
          finishStartConfig
            (List.append processed (b :: next :: rest)) stage
      rw [run_state100_tick]
      unfold markingState120 at hrec
      rw [markedCellsBits_append_single_map] at hrec
      simpa [activeLengthPrefixRev_succ, cellsBits_cons,
        List.length_append, List.map_append, List.append_assoc] using hrec

def finishLengthPrefixScanBits : Nat -> Word Bool
  | 0 => [false, true]
  | n + 1 =>
      List.append tickBits.reverse
        (finishLengthPrefixScanBits n)

def finishScanBits (w : Word Bool) : Word Bool :=
  false :: List.append (cellsBits w).reverse
    (List.append doneBits.reverse
      (finishLengthPrefixScanBits (w.length - 1)))

def stageInputSecondBitTailPrefix : Word Bool -> Word Bool
  | [] => [true, true]
  | b :: rest =>
      true :: false ::
        List.append (stageNatBits rest.length)
          (List.append (cellBits b) (cellsBits rest))

theorem finishLengthPrefixRev_eq_scanBits (n : Nat) :
    finishLengthPrefixRev n =
      List.append ((finishLengthPrefixScanBits n).map some)
        [none, some false] := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [finishLengthPrefixRev, finishLengthPrefixScanBits, ih,
        List.map_append, List.append_assoc]

def repeatedTickBits : Nat -> Word Bool
  | 0 => []
  | n + 1 => List.append (repeatedTickBits n) tickBits

theorem repeatedTickBits_append_tick_comm (n : Nat) :
    List.append (repeatedTickBits n) tickBits =
      List.append tickBits (repeatedTickBits n) := by
  induction n with
  | zero =>
      simp [repeatedTickBits]
  | succ n ih =>
      simp [repeatedTickBits, List.append_assoc]
      calc
        List.append (repeatedTickBits n)
            (List.append tickBits tickBits) =
          List.append (List.append (repeatedTickBits n) tickBits)
            tickBits := by
              simp [List.append_assoc]
        _ =
          List.append (List.append tickBits (repeatedTickBits n))
            tickBits := by
              rw [ih]
        _ =
          List.append tickBits
            (List.append (repeatedTickBits n) tickBits) := by
              simp [List.append_assoc]

theorem stageNatBits_eq_repeatedTickBits_doneBits (n : Nat) :
    stageNatBits n =
      List.append (repeatedTickBits n) doneBits := by
  induction n with
  | zero =>
      simp [repeatedTickBits, doneBits, stageNatBits_zero,
        encodeCodeSymbolAsInput]
  | succ n ih =>
      rw [stageNatBits_succ, ih]
      change
        List.append tickBits
            (List.append (repeatedTickBits n) doneBits) =
          List.append (repeatedTickBits (n + 1)) doneBits
      simp [repeatedTickBits, List.append_assoc]
      calc
        List.append tickBits
            (List.append (repeatedTickBits n) doneBits) =
          List.append (List.append tickBits (repeatedTickBits n))
            doneBits := by
              simp [List.append_assoc]
        _ =
          List.append (List.append (repeatedTickBits n) tickBits)
            doneBits := by
              rw [← repeatedTickBits_append_tick_comm n]
        _ =
          List.append (repeatedTickBits n)
            (List.append tickBits doneBits) := by
              simp [List.append_assoc]

theorem finishLengthPrefixScanBits_reverse_repeatedTickBits
    (n : Nat) :
    (finishLengthPrefixScanBits n).reverse =
      List.append [true, false] (repeatedTickBits n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [finishLengthPrefixScanBits, repeatedTickBits,
        tickBits, encodeCodeSymbolAsInput,
        ih, List.append_assoc]

theorem finishLengthPrefixScanBits_reverse_doneBits (n : Nat) :
    List.append (finishLengthPrefixScanBits n).reverse doneBits =
      List.append [true, false] (stageNatBits n) := by
  rw [finishLengthPrefixScanBits_reverse_repeatedTickBits]
  rw [stageNatBits_eq_repeatedTickBits_doneBits]
  rfl

theorem finishScanBits_reverse_nonempty
    (b : Bool) (rest : Word Bool) :
    (finishScanBits (b :: rest)).reverse =
      List.append (stageInputSecondBitTailPrefix (b :: rest))
        [false] := by
  cases b
  · simpa [finishScanBits, stageInputSecondBitTailPrefix,
      cellsBits_cons, cellBits, List.reverse_append,
      List.append_assoc] using
      congrArg
        (fun bits =>
          List.append bits
            (List.append
              (encodeCodeSymbolAsInput
                MachineCodeSymbol.zero)
              (List.append (cellsBits rest) [false])))
        (finishLengthPrefixScanBits_reverse_doneBits rest.length)
  · simpa [finishScanBits, stageInputSecondBitTailPrefix,
      cellsBits_cons, cellBits, List.reverse_append,
      List.append_assoc] using
      congrArg
        (fun bits =>
          List.append bits
            (List.append
              (encodeCodeSymbolAsInput
                MachineCodeSymbol.one)
              (List.append (cellsBits rest) [false])))
        (finishLengthPrefixScanBits_reverse_doneBits rest.length)

def state160ScanConfig
    (bitsToRight : Word Bool) (boundary : Option Bool)
    (leftTail right : List (Option Bool)) :
    Configuration :=
  match bitsToRight with
  | [] => config 160 leftTail (boundary :: right)
  | b :: rest =>
      config 160 (List.append (rest.map some) (boundary :: leftTail))
        (some b :: right)

theorem run_state160_some_cons
    (b : Bool) (cell : Option Bool)
    (left right : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig 1
        (config 160 (cell :: left) (some b :: right)) =
      config 160 left (cell :: some b :: right) := by
  cases b <;> cases cell <;> cases right <;>
  simp [StageInputMarkedScannerDescription, config, tapeAtCells,
    keep, keepMove, writeMove, scanLeftToSentinelRestart,
    scanLeftToSentinelHalt,
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft]

theorem run_state160_bits_to_boundary
    (bitsToRight : Word Bool) (boundary : Option Bool)
    (leftTail right : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig bitsToRight.length
        (state160ScanConfig bitsToRight boundary leftTail right) =
      config 160 leftTail
        (boundary ::
          List.append (bitsToRight.reverse.map some) right) := by
  induction bitsToRight generalizing boundary leftTail right with
  | nil =>
      rfl
  | cons b rest ih =>
      rw [show (b :: rest).length = 1 + rest.length by
        simp
        omega]
      rw [runConfig_add]
      cases rest with
      | nil =>
          change
            StageInputMarkedScannerDescription.runConfig 0
                (StageInputMarkedScannerDescription.runConfig 1
                  (config 160 (boundary :: leftTail)
                    (some b :: right))) =
              config 160 leftTail (boundary :: some b :: right)
          rw [run_state160_some_cons]
          rfl
      | cons b' rest =>
          change
            StageInputMarkedScannerDescription.runConfig
                (b' :: rest).length
                (StageInputMarkedScannerDescription.runConfig 1
                  (config 160
                    (some b' ::
                      List.append (rest.map some)
                        (boundary :: leftTail))
                    (some b :: right))) =
              config 160 leftTail
                (boundary ::
                  List.append
                    ((b :: b' :: rest).reverse.map some)
                    right)
          rw [run_state160_some_cons]
          have h := ih boundary leftTail (some b :: right)
          simp [state160ScanConfig] at h
          simpa [List.map_append, List.append_assoc] using h

theorem run_state160_none_to_state161
    (cell : Option Bool) (left right : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig 1
        (config 160 (cell :: left) (none :: right)) =
      config 161 left (cell :: none :: right) := by
  cases cell <;> cases right <;>
  simp [StageInputMarkedScannerDescription, config, tapeAtCells,
    keep, keepMove, writeMove, scanLeftToSentinelRestart,
    scanLeftToSentinelHalt,
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft]

theorem run_state161_false_to_state170
    (right : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig 1
        (config 161 [] (some false :: right)) =
      config 170 [some false] right := by
  cases right <;>
  simp [StageInputMarkedScannerDescription, config, tapeAtCells,
    keep, keepMove, writeMove, scanLeftToSentinelRestart,
    scanLeftToSentinelHalt,
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition, Tape.read, Tape.write,
    Tape.move, Tape.moveRight]

theorem run_state170_none_to_state180
    (right : List (Option Bool)) :
    StageInputMarkedScannerDescription.runConfig 1
        (config 170 [some false] (none :: right)) =
      config 180 [none, some false] right := by
  cases right <;>
  simp [StageInputMarkedScannerDescription, config, tapeAtCells,
    keep, keepMove, writeMove, scanLeftToSentinelRestart,
    scanLeftToSentinelHalt,
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition, Tape.read, Tape.write,
    Tape.move, Tape.moveRight]

def state160AfterRestoreConfig (w : Word Bool) (stage : Nat) :
    Configuration :=
  config 160
    (List.append ((cellsBits w).reverse.map some)
      (finishStartLeft w))
    (some false :: none :: ((stageNatBits stage).drop 2).map some)

theorem stageInputSecondBitTail_eq_prefix_stageNat
    (w : Word Bool) (stage : Nat) :
    stageInputSecondBitTail w stage =
      List.append (stageInputSecondBitTailPrefix w)
        (stageNatBits stage) := by
  cases w with
  | nil =>
      simp [stageInputSecondBitTailPrefix,
        stageInputSecondBitTail_nil]
  | cons b rest =>
      simp [stageInputSecondBitTailPrefix,
        stageInputSecondBitTail_cons, List.append_assoc]

def markedStageNatBits (stage : Nat) : List (Option Bool) :=
  some false :: none :: ((stageNatBits stage).drop 2).map some

def appendBlankStartConfig (w : Word Bool) (stage : Nat) :
    Configuration :=
  config 180 [none, some false]
    (List.append ((stageInputSecondBitTailPrefix w).map some)
      (markedStageNatBits stage))

def AppendBlankStart
    (w : Word Bool) (stage : Nat)
    (cfg : Configuration) : Prop :=
  cfg = appendBlankStartConfig w stage

def checkedBoundaryScanConfig (w : Word Bool) (stage : Nat) :
    Configuration :=
  state220ScanConfig
    (stageInputSecondBitTail w stage).reverse
    none [some false] [none]

def CheckedBoundaryScanStart
    (w : Word Bool) (stage : Nat)
    (cfg : Configuration) : Prop :=
  cfg = checkedBoundaryScanConfig w stage

theorem run_state120_marking_loop
    (b : Bool) (rest : Word Bool) (stage : Nat) :
    exists steps : Nat,
      StageInputMarkedScannerDescription.runConfig steps
          (state120AfterStartConfig b rest stage) =
        finishStartConfig (b :: rest) stage := by
  rcases run_marking_loop_from_state120
      ([] : Word Bool) b rest stage with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [state120AfterStartConfig, markingState120,
    activeLengthPrefixRev_zero] using hsteps

theorem run_start_cons_marking_loop
    (b : Bool) (rest : Word Bool) (stage : Nat) :
    exists steps : Nat,
      StageInputMarkedScannerDescription.runConfig steps
          (markedStartConfig (b :: rest) stage) =
        finishStartConfig (b :: rest) stage := by
  rcases run_state120_marking_loop b rest stage with
    ⟨steps, hloop⟩
  refine ⟨6 + steps, ?_⟩
  rw [runConfig_add]
  change
    StageInputMarkedScannerDescription.runConfig steps
        (StageInputMarkedScannerDescription.runConfig 6
          { state := StageInputMarkedScannerDescription.start
            tape :=
              stageInputSecondBitMarkedHandoffTape
                (b :: rest) stage }) =
      finishStartConfig (b :: rest) stage
  rw [run_start_cons_to_state120]
  exact hloop

theorem run_finish_restore_cells
    (w : Word Bool) (stage : Nat) :
    exists steps : Nat,
      StageInputMarkedScannerDescription.runConfig steps
          (finishStartConfig w stage) =
        state160AfterRestoreConfig w stage := by
  refine ⟨4 * w.length + 2, ?_⟩
  simpa [finishStartConfig, state160AfterRestoreConfig] using
    run_state150_markedCells_to_state160 w stage (finishStartLeft w)

theorem run_finish_scan_left_to_append
    (b : Bool) (rest : Word Bool) (stage : Nat) :
    exists steps : Nat,
    exists cfg : Configuration,
      StageInputMarkedScannerDescription.runConfig steps
          (state160AfterRestoreConfig (b :: rest) stage) = cfg ∧
        AppendBlankStart (b :: rest) stage cfg := by
  let bits := finishScanBits (b :: rest)
  let scanRight :=
    none :: ((stageNatBits stage).drop 2).map some
  have hstart :
      state160AfterRestoreConfig (b :: rest) stage =
        state160ScanConfig bits none [some false] scanRight := by
    cases b <;>
    simp [bits, scanRight, finishScanBits, state160AfterRestoreConfig,
      finishStartLeft, finishLengthPrefixRev_eq_scanBits,
      state160ScanConfig, cellsBits_cons,
      cellBits, List.map_append,
      List.reverse_append, List.append_assoc]
  refine ⟨bits.length + 3, appendBlankStartConfig (b :: rest) stage,
    ?_, rfl⟩
  rw [show bits.length + 3 = bits.length + (1 + (1 + 1)) by
    omega]
  rw [runConfig_add]
  rw [hstart]
  rw [run_state160_bits_to_boundary]
  rw [runConfig_add]
  rw [run_state160_none_to_state161]
  rw [runConfig_add]
  rw [run_state161_false_to_state170]
  rw [run_state170_none_to_state180]
  simp [appendBlankStartConfig, markedStageNatBits, bits, scanRight,
    finishScanBits_reverse_nonempty, List.map_append, List.append_assoc]

theorem run_finish_append_blank
    {w : Word Bool} {stage : Nat}
    {cfg : Configuration}
    (hcfg : AppendBlankStart w stage cfg) :
    exists steps : Nat,
    exists cfg' : Configuration,
      StageInputMarkedScannerDescription.runConfig steps cfg = cfg' ∧
        CheckedBoundaryScanStart w stage cfg' := by
  let tailPrefix := stageInputSecondBitTailPrefix w
  refine ⟨tailPrefix.length + 2 + (4 * stage + 5),
    checkedBoundaryScanConfig w stage, ?_, rfl⟩
  rw [hcfg]
  rw [show
      tailPrefix.length + 2 + (4 * stage + 5) =
        tailPrefix.length + (1 + (1 + (4 * stage + 5))) by
    omega]
  rw [runConfig_add]
  change
    StageInputMarkedScannerDescription.runConfig
        (1 + (1 + (4 * stage + 5)))
        (StageInputMarkedScannerDescription.runConfig tailPrefix.length
          (appendBlankStartConfig w stage)) =
      checkedBoundaryScanConfig w stage
  unfold appendBlankStartConfig markedStageNatBits
  change
    StageInputMarkedScannerDescription.runConfig
        (1 + (1 + (4 * stage + 5)))
        (StageInputMarkedScannerDescription.runConfig tailPrefix.length
          (config 180 [none, some false]
            (List.append (tailPrefix.map some)
              (some false :: none ::
                ((stageNatBits stage).drop 2).map some)))) =
      checkedBoundaryScanConfig w stage
  rw [run_state180_bits]
  rw [runConfig_add]
  rw [run_state180_some]
  rw [runConfig_add]
  rw [run_state180_none_cons]
  have hstageBits :
      some false :: some false ::
          ((stageNatBits stage).drop 2).map some =
        (stageNatBits stage).map some := by
    rcases stageNatBits_false_false_tail stage with ⟨tail, htail⟩
    rw [htail]
    rfl
  rw [hstageBits]
  change
    StageInputMarkedScannerDescription.runConfig (4 * stage + 5)
        (config 200
          (List.append (tailPrefix.reverse.map some)
            (none :: [some false]))
          ((stageNatBits stage).map some)) =
      checkedBoundaryScanConfig w stage
  rw [run_state200_stageNat_end]
  simp [checkedBoundaryScanConfig,
    stageInputSecondBitTail_eq_prefix_stageNat, tailPrefix]

theorem run_finish_boundary_to_halt
    {w : Word Bool} {stage : Nat}
    {cfg : Configuration}
    (hcfg : CheckedBoundaryScanStart w stage cfg) :
    exists steps : Nat,
      StageInputMarkedScannerDescription.runConfig steps cfg =
        checkedHaltConfig w stage := by
  refine ⟨(stageInputSecondBitTail w stage).length + 1, ?_⟩
  rw [hcfg]
  rw [show
      (stageInputSecondBitTail w stage).length + 1 =
        (stageInputSecondBitTail w stage).reverse.length + 1 by
    simp]
  rw [runConfig_add]
  change
    StageInputMarkedScannerDescription.runConfig 1
        (StageInputMarkedScannerDescription.runConfig
          (stageInputSecondBitTail w stage).reverse.length
          (state220ScanConfig
            (stageInputSecondBitTail w stage).reverse
            none [some false] [none])) =
      checkedHaltConfig w stage
  rw [run_state220_bits_to_boundary]
  rw [run_state220_none]
  simp [StageInputMarkedScannerDescription, checkedHaltConfig,
    stageInputSecondBitMarkedCheckedHandoffTape,
    stageInputSecondBitMarkedCheckedTape, config, tapeAtCells,
    Tape.move, Tape.moveRight]
  generalize
      List.map some (stageInputSecondBitTail w stage) ++ [none] =
    cells
  cases cells <;> rfl

theorem run_forward_finish
    (b : Bool) (rest : Word Bool) (stage : Nat) :
    exists steps : Nat,
      StageInputMarkedScannerDescription.runConfig steps
          (finishStartConfig (b :: rest) stage) =
        checkedHaltConfig (b :: rest) stage := by
  rcases run_finish_restore_cells (b :: rest) stage with
    ⟨restoreSteps, hrestore⟩
  rcases run_finish_scan_left_to_append b rest stage with
    ⟨scanSteps, appendCfg, hscan, happend⟩
  rcases run_finish_append_blank happend with
    ⟨appendSteps, boundaryCfg, hblank, hboundary⟩
  rcases run_finish_boundary_to_halt hboundary with
    ⟨boundarySteps, hhalt⟩
  refine
    ⟨restoreSteps + scanSteps + appendSteps + boundarySteps, ?_⟩
  rw [show
      restoreSteps + scanSteps + appendSteps + boundarySteps =
        restoreSteps + (scanSteps + (appendSteps + boundarySteps)) by
    omega]
  rw [runConfig_add]
  rw [hrestore]
  rw [runConfig_add]
  rw [hscan]
  rw [runConfig_add]
  rw [hblank]
  exact hhalt

theorem run_start_forward_cons
    (b : Bool) (rest : Word Bool) (stage : Nat) :
    exists steps : Nat,
      StageInputMarkedScannerDescription.runConfig steps
          (markedStartConfig (b :: rest) stage) =
        checkedHaltConfig (b :: rest) stage := by
  rcases run_start_cons_marking_loop b rest stage with
    ⟨markSteps, hmark⟩
  rcases run_forward_finish b rest stage with
    ⟨finishSteps, hfinish⟩
  refine ⟨markSteps + finishSteps, ?_⟩
  rw [runConfig_add]
  rw [hmark]
  exact hfinish

theorem run_start_forward
    (w : Word Bool) (stage : Nat) :
    exists steps : Nat,
      StageInputMarkedScannerDescription.runConfig steps
          (markedStartConfig w stage) =
        checkedHaltConfig w stage := by
  cases w with
  | nil =>
      exact ⟨30 + 8 * stage, by
        simpa [markedStartConfig, checkedHaltConfig] using
          run_start_nil stage⟩
  | cons b rest =>
      exact run_start_forward_cons b rest stage


end StageInputMarkedScanner
end DovetailInitialLayoutInitializer
end Computability
end FoC
