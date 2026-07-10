import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Structured

set_option doc.verso true

/-!
# Structured logical-tape primitive machines

This module provides the first small verified programs over
{module}`FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Structured`.
The primitives are intentionally tiny, concrete transition tables with exact
run lemmas.  Later construction leaves can compose these structured programs
before investing in a one-tape lowering proof.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace Primitives

/-!
## Tape and configuration helpers
-/

/-- One logical tape at a given structured-machine state. -/
def oneTapeConfig (state : Nat) (T : Tape Bool) : Configuration :=
  Configuration.oneTape state T

/-- Two logical tapes at a given structured-machine state. -/
def twoTapeConfig (state : Nat) (T U : Tape Bool) : Configuration where
  state := state
  tapes := [T, U]

/-- A raw word beginning at the head with an explicit left context. -/
def rawWordTape (left : List (Option Bool)) :
    Word Bool -> Tape Bool
  | [] =>
      { left := left
        head := none
        right := [] }
  | bit :: rest =>
      { left := left
        head := some bit
        right := rest.map some }

/-- The tape obtained after scanning a raw word to its right blank. -/
def afterRawWordTape
    (left : List (Option Bool)) (w : Word Bool) : Tape Bool :=
  { left := (w.map some).reverse ++ left
    head := none
    right := [] }

theorem rawWordTape_nil (left : List (Option Bool)) :
    rawWordTape left [] =
      { left := left, head := none, right := [] } :=
  rfl

theorem rawWordTape_cons
    (left : List (Option Bool)) (bit : Bool) (rest : Word Bool) :
    rawWordTape left (bit :: rest) =
      { left := left, head := some bit, right := rest.map some } :=
  rfl

theorem rawWordTape_input (w : Word Bool) :
    rawWordTape [] w = Tape.input w := by
  cases w <;> rfl

theorem afterRawWordTape_nil (left : List (Option Bool)) :
    afterRawWordTape left [] = rawWordTape left [] := by
  rfl

theorem afterRawWordTape_cons
    (left : List (Option Bool)) (bit : Bool) (rest : Word Bool) :
    afterRawWordTape left (bit :: rest) =
      afterRawWordTape (some bit :: left) rest := by
  simp [afterRawWordTape, List.append_assoc]

private def stayAction : TapeAction where
  write? := none
  move := HeadMove.stay

private def moveAction (move : HeadMove) : TapeAction where
  write? := none
  move := move

private def writeAction (cell : Option Bool) : TapeAction where
  write? := some cell
  move := HeadMove.stay

private def writeMoveRightAction (cell : Option Bool) : TapeAction where
  write? := some cell
  move := HeadMove.right

private def moveRightAction : TapeAction where
  write? := none
  move := HeadMove.right

/-!
## One-step move and write primitives
-/

/-- Move the single logical tape once and halt. -/
def moveOnceDescription (move : HeadMove) : Description where
  tapeCount := 1
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ { source := 0
        reads := [none]
        actions := [moveAction move]
        target := 1 }
    , { source := 0
        reads := [some false]
        actions := [moveAction move]
        target := 1 }
    , { source := 0
        reads := [some true]
        actions := [moveAction move]
        target := 1 } ]

theorem moveOnceDescription_lookup
    (move : HeadMove) (T : Tape Bool) :
    (moveOnceDescription move).lookupTransition
        (oneTapeConfig 0 T) =
      some
        { source := 0
          reads := [Tape.read T]
          actions := [moveAction move]
          target := 1 } := by
  cases T with
  | mk left head right =>
      cases head with
      | none =>
          simp [moveOnceDescription, oneTapeConfig,
            Description.lookupTransition, Description.Matches, Tape.read]
      | some bit =>
          cases bit <;>
            simp [moveOnceDescription, oneTapeConfig,
              Description.lookupTransition, Description.Matches, Tape.read]

theorem moveOnceDescription_run
    (move : HeadMove) (T : Tape Bool) :
    (moveOnceDescription move).runConfig 1
        (oneTapeConfig 0 T) =
      oneTapeConfig 1 (move.apply T) := by
  cases T with
  | mk left head right =>
      cases move <;>
        cases head with
        | none =>
            simp [moveOnceDescription, oneTapeConfig, Description.runConfig,
              Description.stepConfig, Description.lookupTransition,
              Description.Matches, Tape.read, Tape.move, Tape.moveLeft,
              Tape.moveRight,
              TapeAction.apply, moveAction, HeadMove.apply]
        | some bit =>
            cases bit <;>
              simp [moveOnceDescription, oneTapeConfig, Description.runConfig,
                Description.stepConfig, Description.lookupTransition,
                Description.Matches, Tape.read, Tape.move, Tape.moveLeft,
                Tape.moveRight,
                TapeAction.apply, moveAction, HeadMove.apply]

/-- Write one cell on the single logical tape and halt. -/
def writeOnceDescription (cell : Option Bool) : Description where
  tapeCount := 1
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ { source := 0
        reads := [none]
        actions := [writeAction cell]
        target := 1 }
    , { source := 0
        reads := [some false]
        actions := [writeAction cell]
        target := 1 }
    , { source := 0
        reads := [some true]
        actions := [writeAction cell]
        target := 1 } ]

theorem writeOnceDescription_lookup
    (cell : Option Bool) (T : Tape Bool) :
    (writeOnceDescription cell).lookupTransition
        (oneTapeConfig 0 T) =
      some
        { source := 0
          reads := [Tape.read T]
          actions := [writeAction cell]
          target := 1 } := by
  cases T with
  | mk left head right =>
      cases head with
      | none =>
          simp [writeOnceDescription, oneTapeConfig,
            Description.lookupTransition, Description.Matches, Tape.read]
      | some bit =>
          cases bit <;>
            simp [writeOnceDescription, oneTapeConfig,
              Description.lookupTransition, Description.Matches, Tape.read]

theorem writeOnceDescription_run
    (cell : Option Bool) (T : Tape Bool) :
    (writeOnceDescription cell).runConfig 1
        (oneTapeConfig 0 T) =
      oneTapeConfig 1 (Tape.write cell T) := by
  cases T with
  | mk left head right =>
      cases head with
      | none =>
          simp [writeOnceDescription, oneTapeConfig, Description.runConfig,
            Description.stepConfig, Description.lookupTransition,
            Description.Matches, Tape.read, Tape.write, TapeAction.apply,
            writeAction, HeadMove.apply]
      | some bit =>
          cases bit <;>
            simp [writeOnceDescription, oneTapeConfig, Description.runConfig,
              Description.stepConfig, Description.lookupTransition,
              Description.Matches, Tape.read, Tape.write, TapeAction.apply,
              writeAction, HeadMove.apply]

/-!
## Scan-to-blank and append primitives
-/

/-- Scan right over raw Boolean cells and halt on the first blank. -/
def scanRightToBlankDescription : Description where
  tapeCount := 1
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ { source := 0
        reads := [some false]
        actions := [moveRightAction]
        target := 0 }
    , { source := 0
        reads := [some true]
        actions := [moveRightAction]
        target := 0 }
    , { source := 0
        reads := [none]
        actions := [stayAction]
        target := 1 } ]

theorem scanRightToBlankDescription_lookup_bit
    (left : List (Option Bool)) (bit : Bool) (rest : Word Bool) :
    scanRightToBlankDescription.lookupTransition
        (oneTapeConfig 0 (rawWordTape left (bit :: rest))) =
      some
        { source := 0
          reads := [some bit]
          actions := [moveRightAction]
          target := 0 } := by
  cases bit <;>
    simp [scanRightToBlankDescription, oneTapeConfig, rawWordTape,
      Description.lookupTransition, Description.Matches, Tape.read]

theorem scanRightToBlankDescription_lookup_blank
    (left : List (Option Bool)) :
    scanRightToBlankDescription.lookupTransition
        (oneTapeConfig 0 (rawWordTape left [])) =
      some
        { source := 0
          reads := [none]
          actions := [stayAction]
          target := 1 } := by
  simp [scanRightToBlankDescription, oneTapeConfig, rawWordTape,
    Description.lookupTransition, Description.Matches, Tape.read]

theorem scanRightToBlankDescription_run_one_bit
    (left : List (Option Bool)) (bit : Bool) (rest : Word Bool) :
    scanRightToBlankDescription.runConfig 1
        (oneTapeConfig 0 (rawWordTape left (bit :: rest))) =
      oneTapeConfig 0 (rawWordTape (some bit :: left) rest) := by
  cases bit <;>
    cases rest <;>
    simp [scanRightToBlankDescription, oneTapeConfig, rawWordTape,
      Description.runConfig, Description.stepConfig,
      Description.lookupTransition, Description.Matches, Tape.read,
      Tape.move, Tape.moveRight,
      TapeAction.apply, moveRightAction, HeadMove.apply]

theorem scanRightToBlankDescription_run_blank
    (left : List (Option Bool)) :
    scanRightToBlankDescription.runConfig 1
        (oneTapeConfig 0 (rawWordTape left [])) =
      oneTapeConfig 1 (rawWordTape left []) := by
  simp [scanRightToBlankDescription, oneTapeConfig, rawWordTape,
    Description.runConfig, Description.stepConfig,
    Description.lookupTransition, Description.Matches, Tape.read,
    TapeAction.apply, stayAction, HeadMove.apply]

theorem scanRightToBlankDescription_run_rawWordTape
    (left : List (Option Bool)) (w : Word Bool) :
    scanRightToBlankDescription.runConfig (w.length + 1)
        (oneTapeConfig 0 (rawWordTape left w)) =
      oneTapeConfig 1 (afterRawWordTape left w) := by
  induction w generalizing left with
  | nil =>
      simpa [afterRawWordTape] using!
        scanRightToBlankDescription_run_blank left
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 = 1 + (rest.length + 1) by
        simp [Nat.add_comm, Nat.add_left_comm]]
      rw [Description.runConfig_add]
      rw [scanRightToBlankDescription_run_one_bit]
      simpa [afterRawWordTape_cons] using ih (some bit :: left)

theorem scanRightToBlankDescription_run_input (w : Word Bool) :
    scanRightToBlankDescription.runConfig (w.length + 1)
        (oneTapeConfig 0 (Tape.input w)) =
      oneTapeConfig 1 (afterRawWordTape [] w) := by
  simpa [rawWordTape_input] using
    scanRightToBlankDescription_run_rawWordTape [] w

/-- Scan right over raw Boolean cells, write a bit at the blank, and halt. -/
def appendBitAtRightBlankDescription (bit : Bool) : Description where
  tapeCount := 1
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ { source := 0
        reads := [some false]
        actions := [moveRightAction]
        target := 0 }
    , { source := 0
        reads := [some true]
        actions := [moveRightAction]
        target := 0 }
    , { source := 0
        reads := [none]
        actions := [writeAction (some bit)]
        target := 1 } ]

def appendBitTargetTape
    (left : List (Option Bool)) (w : Word Bool) (bit : Bool) :
    Tape Bool :=
  { left := (w.map some).reverse ++ left
    head := some bit
    right := [] }

theorem appendBitAtRightBlankDescription_lookup_bit
    (sentinel : Bool) (left : List (Option Bool))
    (bit : Bool) (rest : Word Bool) :
    (appendBitAtRightBlankDescription sentinel).lookupTransition
        (oneTapeConfig 0 (rawWordTape left (bit :: rest))) =
      some
        { source := 0
          reads := [some bit]
          actions := [moveRightAction]
          target := 0 } := by
  cases bit <;>
    simp [appendBitAtRightBlankDescription, oneTapeConfig, rawWordTape,
      Description.lookupTransition, Description.Matches, Tape.read]

theorem appendBitAtRightBlankDescription_lookup_blank
    (sentinel : Bool) (left : List (Option Bool)) :
    (appendBitAtRightBlankDescription sentinel).lookupTransition
        (oneTapeConfig 0 (rawWordTape left [])) =
      some
        { source := 0
          reads := [none]
          actions := [writeAction (some sentinel)]
          target := 1 } := by
  simp [appendBitAtRightBlankDescription, oneTapeConfig, rawWordTape,
    Description.lookupTransition, Description.Matches, Tape.read]

theorem appendBitAtRightBlankDescription_run_one_bit
    (sentinel : Bool) (left : List (Option Bool))
    (bit : Bool) (rest : Word Bool) :
    (appendBitAtRightBlankDescription sentinel).runConfig 1
        (oneTapeConfig 0 (rawWordTape left (bit :: rest))) =
      oneTapeConfig 0 (rawWordTape (some bit :: left) rest) := by
  cases bit <;>
    cases rest <;>
    simp [appendBitAtRightBlankDescription, oneTapeConfig, rawWordTape,
      Description.runConfig, Description.stepConfig,
      Description.lookupTransition, Description.Matches, Tape.read,
      Tape.move, Tape.moveRight,
      TapeAction.apply, moveRightAction, HeadMove.apply]

theorem appendBitAtRightBlankDescription_run_blank
    (sentinel : Bool) (left : List (Option Bool)) :
    (appendBitAtRightBlankDescription sentinel).runConfig 1
        (oneTapeConfig 0 (rawWordTape left [])) =
      oneTapeConfig 1
        { left := left
          head := some sentinel
          right := [] } := by
  simp [appendBitAtRightBlankDescription, oneTapeConfig, rawWordTape,
    Description.runConfig, Description.stepConfig,
    Description.lookupTransition, Description.Matches, Tape.read, Tape.write,
    TapeAction.apply, writeAction, HeadMove.apply]

theorem appendBitAtRightBlankDescription_run_rawWordTape
    (sentinel : Bool) (left : List (Option Bool)) (w : Word Bool) :
    (appendBitAtRightBlankDescription sentinel).runConfig (w.length + 1)
        (oneTapeConfig 0 (rawWordTape left w)) =
      oneTapeConfig 1 (appendBitTargetTape left w sentinel) := by
  induction w generalizing left with
  | nil =>
      simpa [appendBitTargetTape] using
        appendBitAtRightBlankDescription_run_blank sentinel left
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 = 1 + (rest.length + 1) by
        simp [Nat.add_comm, Nat.add_left_comm]]
      rw [Description.runConfig_add]
      rw [appendBitAtRightBlankDescription_run_one_bit]
      simpa [appendBitTargetTape, List.append_assoc] using
        ih (some bit :: left)

theorem appendBitAtRightBlankDescription_run_input
    (sentinel : Bool) (w : Word Bool) :
    (appendBitAtRightBlankDescription sentinel).runConfig (w.length + 1)
        (oneTapeConfig 0 (Tape.input w)) =
      oneTapeConfig 1 (appendBitTargetTape [] w sentinel) := by
  simpa [rawWordTape_input] using
    appendBitAtRightBlankDescription_run_rawWordTape sentinel [] w

/-!
## Copy-until-blank primitive
-/

/-- Copy source bits from tape 0 to tape 1 until tape 0 reaches a blank. -/
def copyUntilBlankDescription : Description where
  tapeCount := 2
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ { source := 0
        reads := [some false, none]
        actions := [moveRightAction, writeMoveRightAction (some false)]
        target := 0 }
    , { source := 0
        reads := [some false, some false]
        actions := [moveRightAction, writeMoveRightAction (some false)]
        target := 0 }
    , { source := 0
        reads := [some false, some true]
        actions := [moveRightAction, writeMoveRightAction (some false)]
        target := 0 }
    , { source := 0
        reads := [some true, none]
        actions := [moveRightAction, writeMoveRightAction (some true)]
        target := 0 }
    , { source := 0
        reads := [some true, some false]
        actions := [moveRightAction, writeMoveRightAction (some true)]
        target := 0 }
    , { source := 0
        reads := [some true, some true]
        actions := [moveRightAction, writeMoveRightAction (some true)]
        target := 0 }
    , { source := 0
        reads := [none, none]
        actions := [stayAction, stayAction]
        target := 1 }
    , { source := 0
        reads := [none, some false]
        actions := [stayAction, stayAction]
        target := 1 }
    , { source := 0
        reads := [none, some true]
        actions := [stayAction, stayAction]
        target := 1 } ]

theorem copyUntilBlankDescription_lookup_bit
    (sourceLeft destLeft : List (Option Bool))
    (bit : Bool) (rest : Word Bool) :
    copyUntilBlankDescription.lookupTransition
        (twoTapeConfig 0
          (rawWordTape sourceLeft (bit :: rest))
          (rawWordTape destLeft [])) =
      some
        { source := 0
          reads := [some bit, none]
          actions := [moveRightAction, writeMoveRightAction (some bit)]
          target := 0 } := by
  cases bit <;>
    simp [copyUntilBlankDescription, twoTapeConfig, rawWordTape,
      Description.lookupTransition, Description.Matches, Tape.read]

theorem copyUntilBlankDescription_lookup_blank
    (sourceLeft destLeft : List (Option Bool)) :
    copyUntilBlankDescription.lookupTransition
        (twoTapeConfig 0
          (rawWordTape sourceLeft [])
          (rawWordTape destLeft [])) =
      some
        { source := 0
          reads := [none, none]
          actions := [stayAction, stayAction]
          target := 1 } := by
  simp [copyUntilBlankDescription, twoTapeConfig, rawWordTape,
    Description.lookupTransition, Description.Matches, Tape.read]

theorem copyUntilBlankDescription_run_one_bit
    (sourceLeft destLeft : List (Option Bool))
    (bit : Bool) (rest : Word Bool) :
    copyUntilBlankDescription.runConfig 1
        (twoTapeConfig 0
          (rawWordTape sourceLeft (bit :: rest))
          (rawWordTape destLeft [])) =
      twoTapeConfig 0
        (rawWordTape (some bit :: sourceLeft) rest)
        (rawWordTape (some bit :: destLeft) []) := by
  cases bit <;>
    cases rest <;>
    simp [copyUntilBlankDescription, twoTapeConfig, rawWordTape,
      Description.runConfig, Description.stepConfig,
      Description.lookupTransition, Description.Matches, Tape.read,
      Tape.move, Tape.moveRight, Tape.write,
      TapeAction.apply, moveRightAction, writeMoveRightAction, HeadMove.apply]

theorem copyUntilBlankDescription_run_blank
    (sourceLeft destLeft : List (Option Bool)) :
    copyUntilBlankDescription.runConfig 1
        (twoTapeConfig 0
          (rawWordTape sourceLeft [])
          (rawWordTape destLeft [])) =
      twoTapeConfig 1
        (rawWordTape sourceLeft [])
        (rawWordTape destLeft []) := by
  simp [copyUntilBlankDescription, twoTapeConfig, rawWordTape,
    Description.runConfig, Description.stepConfig,
    Description.lookupTransition, Description.Matches, Tape.read,
    TapeAction.apply, stayAction, HeadMove.apply]

theorem copyUntilBlankDescription_run_rawWordTape
    (sourceLeft destLeft : List (Option Bool)) (w : Word Bool) :
    copyUntilBlankDescription.runConfig (w.length + 1)
        (twoTapeConfig 0
          (rawWordTape sourceLeft w)
          (rawWordTape destLeft [])) =
      twoTapeConfig 1
        (afterRawWordTape sourceLeft w)
        (afterRawWordTape destLeft w) := by
  induction w generalizing sourceLeft destLeft with
  | nil =>
      simpa [afterRawWordTape] using!
        copyUntilBlankDescription_run_blank sourceLeft destLeft
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 = 1 + (rest.length + 1) by
        simp [Nat.add_comm, Nat.add_left_comm]]
      rw [Description.runConfig_add]
      rw [copyUntilBlankDescription_run_one_bit]
      simpa [afterRawWordTape_cons] using
        ih (some bit :: sourceLeft) (some bit :: destLeft)

theorem copyUntilBlankDescription_run_input
    (w : Word Bool) :
    copyUntilBlankDescription.runConfig (w.length + 1)
        (twoTapeConfig 0 (Tape.input w) Tape.blank) =
      twoTapeConfig 1
        (afterRawWordTape [] w)
        (afterRawWordTape [] w) := by
  cases w with
  | nil =>
      simpa [rawWordTape_input, rawWordTape, Tape.blank, Tape.input] using
        copyUntilBlankDescription_run_rawWordTape [] [] ([] : Word Bool)
  | cons bit rest =>
      simpa [rawWordTape_input, rawWordTape, Tape.blank, Tape.input] using
        copyUntilBlankDescription_run_rawWordTape [] [] (bit :: rest)

/-!
## Smoke examples
-/

private theorem moveOnceDescription_example :
    (moveOnceDescription HeadMove.right).runConfig 1
        (oneTapeConfig 0 (Tape.input [false, true])) =
      oneTapeConfig 1
        { left := [some false]
          head := some true
          right := [] } := by
  decide

private theorem writeOnceDescription_example :
    (writeOnceDescription (some true)).runConfig 1
        (oneTapeConfig 0 (Tape.input [false])) =
      oneTapeConfig 1 (Tape.input [true]) := by
  decide

private theorem scanRightToBlankDescription_example :
    scanRightToBlankDescription.runConfig 4
        (oneTapeConfig 0 (Tape.input [true, false, true])) =
      oneTapeConfig 1
        { left := [some true, some false, some true]
          head := none
          right := [] } := by
  decide

private theorem appendBitAtRightBlankDescription_example :
    (appendBitAtRightBlankDescription false).runConfig 3
        (oneTapeConfig 0 (Tape.input [true, true])) =
      oneTapeConfig 1
        { left := [some true, some true]
          head := some false
          right := [] } := by
  decide

private theorem copyUntilBlankDescription_example :
    copyUntilBlankDescription.runConfig 3
        (twoTapeConfig 0 (Tape.input [false, true]) Tape.blank) =
      twoTapeConfig 1
        { left := [some true, some false]
          head := none
          right := [] }
        { left := [some true, some false]
          head := none
          right := [] } := by
  decide

end Primitives
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
