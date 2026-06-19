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

/-!
**Encoding views.**  The scanner works over the second-bit-marked suffix of a
stage input.  The definitions below name the pieces that appear repeatedly in
the tape shape: encoded ticks, the {name}`MachineCodeSymbol.done` delimiter,
encoded stage numbers, ordinary payload cells, and the temporary marked payload
cells used while scanning.
-/

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
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition,
    MachineDescription.encodeCodeSymbolAsInput,
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
      rw [MachineDescription.runConfig_add]
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
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition,
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
  rw [MachineDescription.runConfig_add]
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
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write,
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
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write,
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

/-!
**Forward proof split.**  The exported specification only needs an existential
run length, so the nonempty case is split around named phase contracts instead
of carrying one large arithmetic expression.  The first remaining obligation is
the marking loop from state {lit}`120` to the beginning of the finish pass; the
second is the finish pass from that intermediate configuration to the checked
handoff tape.
-/

def markedStartConfig (w : Word Bool) (stage : Nat) :
    MachineDescription.Configuration :=
  { state := StageInputMarkedScannerDescription.start
    tape := stageInputSecondBitMarkedHandoffTape w stage }

def checkedHaltConfig (w : Word Bool) (stage : Nat) :
    MachineDescription.Configuration :=
  { state := StageInputMarkedScannerDescription.halt
    tape := stageInputSecondBitMarkedCheckedHandoffTape w stage }

def state120AfterStartConfig
    (b : Bool) (rest : Word Bool) (stage : Nat) :
    MachineDescription.Configuration :=
  config 120 [none, some true, none, some false]
    (List.append ((stageNatBits rest.length).map some)
      (List.append ((cellBits b).map some)
        (List.append ((cellsBits rest).map some)
          ((stageNatBits stage).map some))))

def ForwardFinishStart
    (w : Word Bool) (stage : Nat)
    (cfg : MachineDescription.Configuration) : Prop :=
  exists left : List (Option Bool),
    cfg =
      config 150 left
        (List.append ((markedCellsBits w).map some)
          ((stageNatBits stage).map some))

theorem run_state120_marking_loop
    (b : Bool) (rest : Word Bool) (stage : Nat) :
    exists steps : Nat,
    exists cfg : MachineDescription.Configuration,
      StageInputMarkedScannerDescription.runConfig steps
          (state120AfterStartConfig b rest stage) = cfg ∧
        ForwardFinishStart (b :: rest) stage cfg := by
  sorry

theorem run_start_cons_marking_loop
    (b : Bool) (rest : Word Bool) (stage : Nat) :
    exists steps : Nat,
    exists cfg : MachineDescription.Configuration,
      StageInputMarkedScannerDescription.runConfig steps
          (markedStartConfig (b :: rest) stage) = cfg ∧
        ForwardFinishStart (b :: rest) stage cfg := by
  rcases run_state120_marking_loop b rest stage with
    ⟨steps, cfg, hloop, hfinishStart⟩
  refine ⟨6 + steps, cfg, ?_, hfinishStart⟩
  rw [MachineDescription.runConfig_add]
  change
    StageInputMarkedScannerDescription.runConfig steps
        (StageInputMarkedScannerDescription.runConfig 6
          { state := StageInputMarkedScannerDescription.start
            tape :=
              stageInputSecondBitMarkedHandoffTape
                (b :: rest) stage }) = cfg
  rw [run_start_cons_to_state120]
  exact hloop

theorem run_forward_finish
    {w : Word Bool} {stage : Nat}
    {cfg : MachineDescription.Configuration}
    (hfinishStart : ForwardFinishStart w stage cfg) :
    exists steps : Nat,
      StageInputMarkedScannerDescription.runConfig steps cfg =
        checkedHaltConfig w stage := by
  sorry

theorem run_start_forward_cons
    (b : Bool) (rest : Word Bool) (stage : Nat) :
    exists steps : Nat,
      StageInputMarkedScannerDescription.runConfig steps
          (markedStartConfig (b :: rest) stage) =
        checkedHaltConfig (b :: rest) stage := by
  rcases run_start_cons_marking_loop b rest stage with
    ⟨markSteps, cfg, hmark, hfinishStart⟩
  rcases run_forward_finish hfinishStart with
    ⟨finishSteps, hfinish⟩
  refine ⟨markSteps + finishSteps, ?_⟩
  rw [MachineDescription.runConfig_add]
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

/-!
**Closed proof split.**  The closed direction begins with the separate marker
subroutine, whose inversion theorem exposes an arbitrary second-bit tail.  The
scanner-specific closed obligation is therefore stated against such a tail; a
separate encoding lemma turns the accepted tail back into the canonical
stage-input code.
-/

def markedTailStartConfig (tail : Word Bool) :
    MachineDescription.Configuration :=
  { state := StageInputMarkedScannerDescription.start
    tape :=
      Tape.move Direction.right
        (tapeAtCells [some false] (none :: tail.map some)) }

theorem scanner_marked_tail_inv
    {tail : Word Bool} {T : Tape Bool}
    (hscanner :
      exists steps : Nat,
        StageInputMarkedScannerDescription.runConfig steps
            (markedTailStartConfig tail) =
          { state := StageInputMarkedScannerDescription.halt
            tape := T }) :
    exists w : Word Bool,
    exists stage : Nat,
      tail = stageInputSecondBitTail w stage ∧
        T = stageInputSecondBitMarkedCheckedHandoffTape w stage := by
  sorry

theorem stageInputBits_code_inv
    {code : Word MachineCodeSymbol} {w : Word Bool}
    {stage : Nat}
    (hbits :
      MachineDescription.encodeCodeWordAsInput code =
        stageInputBits w stage) :
    code = PairedRecognizerDovetailStageInputCode w stage := by
  sorry

theorem stageInputMarkedScannerDescription_closed
    (code : Word MachineCodeSymbol) (Tmark T : Tape Bool)
    (hmark :
      MarkStageInputSecondBitDescription.HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) Tmark)
    (hscanner :
      exists steps : Nat,
        StageInputMarkedScannerDescription.runConfig steps
            { state := StageInputMarkedScannerDescription.start
              tape := Tape.move Direction.right Tmark } =
          { state := StageInputMarkedScannerDescription.halt
            tape := T }) :
    exists w : Word Bool,
    exists stage : Nat,
      code = PairedRecognizerDovetailStageInputCode w stage ∧
        T = stageInputSecondBitMarkedCheckedHandoffTape w stage := by
  rcases markStageInputSecondBitDescription_haltsWithTape_inv hmark with
    ⟨tail, hbits, hTmark⟩
  have hscannerTail :
      exists steps : Nat,
        StageInputMarkedScannerDescription.runConfig steps
            (markedTailStartConfig tail) =
          { state := StageInputMarkedScannerDescription.halt
            tape := T } := by
    rcases hscanner with ⟨steps, hsteps⟩
    refine ⟨steps, ?_⟩
    simpa [markedTailStartConfig, hTmark] using hsteps
  rcases scanner_marked_tail_inv hscannerTail with
    ⟨w, stage, htail, hT⟩
  refine ⟨w, stage, ?_, hT⟩
  apply stageInputBits_code_inv
  rw [stageInputBits_eq_false_false_tail w stage]
  rw [hbits, htail]

/-!
The exported construction theorem packages the subroutine readiness, forward
run, and closed-run inversion required by {name}`StageInputMarkedScannerSpec`.
At this point the theorem itself is only glue; every remaining proof obligation
has a phase-specific name.
-/

theorem stageInputMarkedScannerDescription_spec :
    StageInputMarkedScannerSpec StageInputMarkedScannerDescription := by
  constructor
  · exact stageInputMarkedScannerDescription_subroutineReady
  constructor
  · intro w stage
    simpa [markedStartConfig, checkedHaltConfig] using
      run_start_forward w stage
  · intro code Tmark T hmark hscanner
    exact
      stageInputMarkedScannerDescription_closed
        code Tmark T hmark hscanner

end StageInputMarkedScanner

export StageInputMarkedScanner
  (StageInputMarkedScannerDescription
   stageInputMarkedScannerDescription_subroutineReady
   stageInputMarkedScannerDescription_spec)

end DovetailInitialLayoutInitializer
end Computability
end FoC
