import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawEncoder.RawBoundaryRightEdgeEmitter.PrependFixedFourBits

set_option doc.verso true

/-!
# Raw-boundary fixed chunk prepender with a blank sentinel

This module contains the delimiter-preserving variant of the fixed four-bit
prepender.  It prepends one fixed code chunk immediately to the left of the
already-emitted suffix, keeps the right boundary blank, and halts back on that
blank boundary.  This is the small primitive needed by raw-boundary designs
that remember the live tail bit in finite control and restore it only after all
chunks have been emitted.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open EncRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf

namespace CommonGround
namespace FiniteTransducers
namespace CountWindowRawSourceEncoder
namespace RawBoundaryRightEdgeEmitter

def prependFixedFourBitsLeftOfBlankSentinelDescription
    (b0 b1 b2 b3 : Bool) : MachineDescription where
  stateCount := 8
  start := 0
  halt := 7
  transitions :=
    [ transition 0 none none Direction.left 1
    , transition 1 (some false) (some false) Direction.left 1
    , transition 1 (some true) (some true) Direction.left 1
    , transition 1 none (some b3) Direction.left 2
    , transition 2 none (some b2) Direction.left 3
    , transition 3 none (some b1) Direction.left 4
    , transition 4 none (some b0) Direction.right 5
    , transition 5 (some false) (some false) Direction.right 5
    , transition 5 (some true) (some true) Direction.right 5
    , transition 5 none none Direction.left 6
    , transition 6 (some false) (some false) Direction.right 7
    , transition 6 (some true) (some true) Direction.right 7 ]

theorem prependFixedFourBitsLeftOfBlankSentinelDescription_wellFormed
    (b0 b1 b2 b3 : Bool) :
    (prependFixedFourBitsLeftOfBlankSentinelDescription
      b0 b1 b2 b3).WellFormed := by
  refine
    ⟨by simp [prependFixedFourBitsLeftOfBlankSentinelDescription],
      by simp [prependFixedFourBitsLeftOfBlankSentinelDescription],
      by simp [prependFixedFourBitsLeftOfBlankSentinelDescription], ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := (prependFixedFourBitsLeftOfBlankSentinelDescription
        b0 b1 b2 b3).transitions)
      (stateCount := (prependFixedFourBitsLeftOfBlankSentinelDescription
        b0 b1 b2 b3).stateCount)
      (by cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide)
  · exact transition_deterministic_of_all
      (l := (prependFixedFourBitsLeftOfBlankSentinelDescription
        b0 b1 b2 b3).transitions)
      (by cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide)

theorem prependFixedFourBitsLeftOfBlankSentinelDescription_haltTransitionFree
    (b0 b1 b2 b3 : Bool) :
    (prependFixedFourBitsLeftOfBlankSentinelDescription
      b0 b1 b2 b3).HaltTransitionFree := by
  exact transition_notFrom_of_all
    (l := (prependFixedFourBitsLeftOfBlankSentinelDescription
      b0 b1 b2 b3).transitions)
    (state := (prependFixedFourBitsLeftOfBlankSentinelDescription
      b0 b1 b2 b3).halt)
    (by cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide)

theorem prependFixedFourBitsLeftOfBlankSentinelDescription_subroutineReady
    (b0 b1 b2 b3 : Bool) :
    (prependFixedFourBitsLeftOfBlankSentinelDescription
      b0 b1 b2 b3).SubroutineReady :=
  ⟨prependFixedFourBitsLeftOfBlankSentinelDescription_wellFormed
      b0 b1 b2 b3,
    prependFixedFourBitsLeftOfBlankSentinelDescription_haltTransitionFree
      b0 b1 b2 b3⟩

private theorem prependFixedFourBitsLeftOfBlankSentinelDescription_step_start
    (b0 b1 b2 b3 : Bool) (emitted : Word Bool)
    (tail : List (Option Bool)) :
    (prependFixedFourBitsLeftOfBlankSentinelDescription b0 b1 b2 b3).runConfig
        1
        { state := (prependFixedFourBitsLeftOfBlankSentinelDescription
            b0 b1 b2 b3).start
          tape := tapeAtCells (emitted.reverse.map some)
            (none :: tail) } =
      { state := 1
        tape := prependFixedFourBitsLeftScanTape emitted.reverse
          (none :: tail) } := by
  cases hrev : emitted.reverse with
  | nil =>
      simp [prependFixedFourBitsLeftOfBlankSentinelDescription,
        prependFixedFourBitsLeftScanTape, runConfig, stepConfig,
        lookupTransition, Matches, transition, Tape.read, Tape.write,
        Tape.move, Tape.moveLeft, tapeAtCells]
  | cons bit rest =>
      cases bit <;>
        simp [prependFixedFourBitsLeftOfBlankSentinelDescription,
          prependFixedFourBitsLeftScanTape, runConfig, stepConfig,
          lookupTransition, Matches, transition, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft, tapeAtCells]

private theorem prependFixedFourBitsLeftOfBlankSentinelDescription_step_scanLeft
    (b0 b1 b2 b3 bit : Bool) (rest : Word Bool)
    (right : List (Option Bool)) :
    (prependFixedFourBitsLeftOfBlankSentinelDescription b0 b1 b2 b3).runConfig
        1
        { state := 1
          tape := prependFixedFourBitsLeftScanTape (bit :: rest) right } =
      { state := 1
        tape := prependFixedFourBitsLeftScanTape rest
          (some bit :: right) } := by
  cases bit <;>
    cases rest <;>
    simp [prependFixedFourBitsLeftOfBlankSentinelDescription,
      prependFixedFourBitsLeftScanTape, runConfig, stepConfig,
      lookupTransition, Matches, transition, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft, tapeAtCells]

private theorem prependFixedFourBitsLeftOfBlankSentinelDescription_run_scanLeft
    (b0 b1 b2 b3 : Bool) (remainingRev : Word Bool)
    (right : List (Option Bool)) :
    (prependFixedFourBitsLeftOfBlankSentinelDescription b0 b1 b2 b3).runConfig
        remainingRev.length
        { state := 1
          tape := prependFixedFourBitsLeftScanTape remainingRev right } =
      { state := 1
        tape := tapeAtCells []
          (none :: List.append (remainingRev.reverse.map some) right) } := by
  induction remainingRev generalizing right with
  | nil =>
      simp [prependFixedFourBitsLeftScanTape, runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        lia]
      rw [runConfig_add]
      rw [prependFixedFourBitsLeftOfBlankSentinelDescription_step_scanLeft]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: right)

private theorem prependFixedFourBitsLeftOfBlankSentinelDescription_run_write
    (b0 b1 b2 b3 : Bool) (right : List (Option Bool)) :
    (prependFixedFourBitsLeftOfBlankSentinelDescription b0 b1 b2 b3).runConfig
        4
        { state := 1
          tape := tapeAtCells [] (none :: right) } =
      { state := 5
        tape := tapeAtCells [some b0]
          (some b1 :: some b2 :: some b3 :: right) } := by
  simp [prependFixedFourBitsLeftOfBlankSentinelDescription, runConfig,
    stepConfig, lookupTransition, Matches, transition, Tape.read,
    Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells]

private theorem prependFixedFourBitsLeftOfBlankSentinelDescription_step_scanRight
    (b0 b1 b2 b3 bit : Bool) (left right : List (Option Bool)) :
    (prependFixedFourBitsLeftOfBlankSentinelDescription b0 b1 b2 b3).runConfig
        1
        { state := 5
          tape := tapeAtCells left (some bit :: right) } =
      { state := 5
        tape := tapeAtCells (some bit :: left) right } := by
  cases bit <;>
    cases right <;>
      simp [prependFixedFourBitsLeftOfBlankSentinelDescription, runConfig,
        stepConfig, lookupTransition, Matches, transition, Tape.read,
        Tape.write, Tape.move, Tape.moveRight, tapeAtCells]

private theorem prependFixedFourBitsLeftOfBlankSentinelDescription_run_scanRight
    (b0 b1 b2 b3 : Bool) (bits : Word Bool)
    (left right : List (Option Bool)) :
    (prependFixedFourBitsLeftOfBlankSentinelDescription b0 b1 b2 b3).runConfig
        bits.length
        { state := 5
          tape := tapeAtCells left
            (List.append (bits.map some) right) } =
      { state := 5
        tape := tapeAtCells
          (List.append (bits.reverse.map some) left) right } := by
  induction bits generalizing left with
  | nil =>
      simp [runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        lia]
      rw [runConfig_add]
      change
        (prependFixedFourBitsLeftOfBlankSentinelDescription
            b0 b1 b2 b3).runConfig
            rest.length
            ((prependFixedFourBitsLeftOfBlankSentinelDescription
                b0 b1 b2 b3).runConfig 1
              { state := 5
                tape := tapeAtCells left
                  (some bit :: List.append (rest.map some) right) }) =
          { state := 5
            tape := tapeAtCells
              (List.append ((bit :: rest).reverse.map some) left) right }
      rw [prependFixedFourBitsLeftOfBlankSentinelDescription_step_scanRight]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: left)

private theorem prependFixedFourBitsLeftOfBlankSentinelDescription_run_restore
    (b0 b1 b2 b3 cell : Bool)
    (leftRevTail tail : List (Option Bool)) :
    (prependFixedFourBitsLeftOfBlankSentinelDescription b0 b1 b2 b3).runConfig
        2
        { state := 5
          tape := tapeAtCells (some cell :: leftRevTail) (none :: tail) } =
      { state := (prependFixedFourBitsLeftOfBlankSentinelDescription
          b0 b1 b2 b3).halt
        tape := tapeAtCells (some cell :: leftRevTail) (none :: tail) } := by
  cases cell <;>
    simp [prependFixedFourBitsLeftOfBlankSentinelDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells]

private theorem
    prependFixedFourBitsLeftOfBlankSentinelDescription_run_restore_bits
    (b0 b1 b2 b3 : Bool) (bits : Word Bool)
    (tail : List (Option Bool)) :
    (prependFixedFourBitsLeftOfBlankSentinelDescription b0 b1 b2 b3).runConfig
        2
        { state := 5
          tape := tapeAtCells
            (List.append (bits.map some)
              [some b3, some b2, some b1, some b0])
            (none :: tail) } =
      { state := (prependFixedFourBitsLeftOfBlankSentinelDescription
          b0 b1 b2 b3).halt
        tape := tapeAtCells
          (List.append (bits.map some)
            [some b3, some b2, some b1, some b0])
          (none :: tail) } := by
  cases bits with
  | nil =>
      simpa [List.append_assoc] using
        prependFixedFourBitsLeftOfBlankSentinelDescription_run_restore
          b0 b1 b2 b3 b3 [some b2, some b1, some b0] tail
  | cons bit rest =>
      simpa [List.append_assoc] using
        prependFixedFourBitsLeftOfBlankSentinelDescription_run_restore
          b0 b1 b2 b3 bit
          (List.append (rest.map some)
            [some b3, some b2, some b1, some b0])
          tail

theorem prependFixedFourBitsLeftOfBlankSentinelDescription_run
    (b0 b1 b2 b3 : Bool) (emitted : Word Bool)
    (tail : List (Option Bool)) :
    (prependFixedFourBitsLeftOfBlankSentinelDescription b0 b1 b2 b3).runConfig
        (2 * emitted.length + 10)
        { state := (prependFixedFourBitsLeftOfBlankSentinelDescription
            b0 b1 b2 b3).start
          tape := tapeAtCells (emitted.reverse.map some)
            (none :: tail) } =
      { state := (prependFixedFourBitsLeftOfBlankSentinelDescription
          b0 b1 b2 b3).halt
        tape := tapeAtCells
          (List.append (emitted.reverse.map some)
            [some b3, some b2, some b1, some b0])
          (none :: tail) } := by
  rw [show 2 * emitted.length + 10 =
      1 + (emitted.reverse.length + (4 +
        ((List.append [b1, b2, b3] emitted).length + 2))) by
    simp [List.length_reverse]
    lia]
  rw [runConfig_add]
  rw [prependFixedFourBitsLeftOfBlankSentinelDescription_step_start]
  rw [runConfig_add]
  rw [prependFixedFourBitsLeftOfBlankSentinelDescription_run_scanLeft]
  simp [List.reverse_reverse]
  rw [runConfig_add]
  rw [prependFixedFourBitsLeftOfBlankSentinelDescription_run_write]
  rw [runConfig_add]
  rw [show emitted.length + 1 + 1 + 1 =
      (List.append [b1, b2, b3] emitted).length by
    simp]
  rw [show some b1 :: some b2 :: some b3 ::
        (List.map some emitted ++ none :: tail) =
      List.append ((List.append [b1, b2, b3] emitted).map some)
        (none :: tail) by
    simp]
  rw [prependFixedFourBitsLeftOfBlankSentinelDescription_run_scanRight]
  rw [show
      List.append
          (List.map some (List.append [b1, b2, b3] emitted).reverse)
          [some b0] =
        List.append (emitted.reverse.map some)
          [some b3, some b2, some b1, some b0] by
    simp [List.map_reverse, List.append_assoc]]
  rw [prependFixedFourBitsLeftOfBlankSentinelDescription_run_restore_bits]
  simp [List.map_reverse]

theorem prependFixedFourBitsLeftOfBlankSentinelDescription_haltsFrom
    (b0 b1 b2 b3 : Bool) (emitted : Word Bool)
    (tail : List (Option Bool)) :
    (prependFixedFourBitsLeftOfBlankSentinelDescription
      b0 b1 b2 b3).HaltsFromTape
      (tapeAtCells (emitted.reverse.map some) (none :: tail))
      (tapeAtCells
        (List.append (emitted.reverse.map some)
          [some b3, some b2, some b1, some b0])
        (none :: tail)) := by
  refine ⟨2 * emitted.length + 10, ?_⟩
  constructor <;>
    rw [prependFixedFourBitsLeftOfBlankSentinelDescription_run]

theorem prependFixedFourBitsLeftOfBlankSentinelDescription_haltsFrom_chunk
    (b0 b1 b2 b3 : Bool) (emitted : Word Bool)
    (tail : List (Option Bool)) :
    (prependFixedFourBitsLeftOfBlankSentinelDescription
      b0 b1 b2 b3).HaltsFromTape
      (tapeAtCells (emitted.reverse.map some) (none :: tail))
      (tapeAtCells
        (List.append (emitted.reverse.map some)
          (([b0, b1, b2, b3] : Word Bool).reverse.map some))
        (none :: tail)) := by
  simpa using
    prependFixedFourBitsLeftOfBlankSentinelDescription_haltsFrom
      b0 b1 b2 b3 emitted tail

theorem prependFixedFourBitsLeftOfBlankSentinelDescription_haltsFrom_prepend
    (b0 b1 b2 b3 : Bool) (emitted : Word Bool)
    (tail : List (Option Bool)) :
    (prependFixedFourBitsLeftOfBlankSentinelDescription
      b0 b1 b2 b3).HaltsFromTape
      (tapeAtCells (emitted.reverse.map some) (none :: tail))
      (tapeAtCells
        ((List.append ([b0, b1, b2, b3] : Word Bool) emitted).reverse.map
          some)
        (none :: tail)) := by
  simpa [List.reverse_append, List.map_append] using
    prependFixedFourBitsLeftOfBlankSentinelDescription_haltsFrom_chunk
      b0 b1 b2 b3 emitted tail

theorem prependFixedFourBitsLeftOfBlankSentinelDescription_target_moveLeftRight
    (b0 b1 b2 b3 : Bool) (emitted : Word Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tapeAtCells
            ((List.append ([b0, b1, b2, b3] : Word Bool)
              emitted).reverse.map some)
            (none :: tail))) =
      tapeAtCells
        ((List.append ([b0, b1, b2, b3] : Word Bool)
          emitted).reverse.map some)
        (none :: tail) := by
  simpa [List.reverse_append, List.map_append, List.append_assoc] using
    tapeAtCells_move_right_move_left_append_cons
      (emitted.reverse.map some)
      [some b2, some b1, some b0]
      (none :: tail)
      (some b3)

def prependHeaderChunkLeftOfBlankSentinelDescription : MachineDescription :=
  prependFixedFourBitsLeftOfBlankSentinelDescription false false false false

theorem prependHeaderChunkLeftOfBlankSentinelDescription_subroutineReady :
    prependHeaderChunkLeftOfBlankSentinelDescription.SubroutineReady :=
  prependFixedFourBitsLeftOfBlankSentinelDescription_subroutineReady
    false false false false

theorem prependHeaderChunkLeftOfBlankSentinelDescription_haltsFrom_prepend
    (emitted : Word Bool) (tail : List (Option Bool)) :
    prependHeaderChunkLeftOfBlankSentinelDescription.HaltsFromTape
      (tapeAtCells (emitted.reverse.map some) (none :: tail))
      (tapeAtCells
        ((List.append ([false, false, false, false] : Word Bool)
          emitted).reverse.map some)
        (none :: tail)) :=
  prependFixedFourBitsLeftOfBlankSentinelDescription_haltsFrom_prepend
    false false false false emitted tail

def prependLengthTickChunkLeftOfBlankSentinelDescription :
    MachineDescription :=
  prependFixedFourBitsLeftOfBlankSentinelDescription false false true false

theorem prependLengthTickChunkLeftOfBlankSentinelDescription_subroutineReady :
    prependLengthTickChunkLeftOfBlankSentinelDescription.SubroutineReady :=
  prependFixedFourBitsLeftOfBlankSentinelDescription_subroutineReady
    false false true false

theorem prependLengthTickChunkLeftOfBlankSentinelDescription_haltsFrom_prepend
    (emitted : Word Bool) (tail : List (Option Bool)) :
    prependLengthTickChunkLeftOfBlankSentinelDescription.HaltsFromTape
      (tapeAtCells (emitted.reverse.map some) (none :: tail))
      (tapeAtCells
        ((List.append ([false, false, true, false] : Word Bool)
          emitted).reverse.map some)
        (none :: tail)) :=
  prependFixedFourBitsLeftOfBlankSentinelDescription_haltsFrom_prepend
    false false true false emitted tail

def prependLengthDoneChunkLeftOfBlankSentinelDescription :
    MachineDescription :=
  prependFixedFourBitsLeftOfBlankSentinelDescription false false true true

theorem prependLengthDoneChunkLeftOfBlankSentinelDescription_subroutineReady :
    prependLengthDoneChunkLeftOfBlankSentinelDescription.SubroutineReady :=
  prependFixedFourBitsLeftOfBlankSentinelDescription_subroutineReady
    false false true true

theorem prependLengthDoneChunkLeftOfBlankSentinelDescription_haltsFrom_prepend
    (emitted : Word Bool) (tail : List (Option Bool)) :
    prependLengthDoneChunkLeftOfBlankSentinelDescription.HaltsFromTape
      (tapeAtCells (emitted.reverse.map some) (none :: tail))
      (tapeAtCells
        ((List.append ([false, false, true, true] : Word Bool)
          emitted).reverse.map some)
        (none :: tail)) :=
  prependFixedFourBitsLeftOfBlankSentinelDescription_haltsFrom_prepend
    false false true true emitted tail

def prependCellZeroChunkLeftOfBlankSentinelDescription :
    MachineDescription :=
  prependFixedFourBitsLeftOfBlankSentinelDescription false true false true

theorem prependCellZeroChunkLeftOfBlankSentinelDescription_subroutineReady :
    prependCellZeroChunkLeftOfBlankSentinelDescription.SubroutineReady :=
  prependFixedFourBitsLeftOfBlankSentinelDescription_subroutineReady
    false true false true

theorem prependCellZeroChunkLeftOfBlankSentinelDescription_haltsFrom_prepend
    (emitted : Word Bool) (tail : List (Option Bool)) :
    prependCellZeroChunkLeftOfBlankSentinelDescription.HaltsFromTape
      (tapeAtCells (emitted.reverse.map some) (none :: tail))
      (tapeAtCells
        ((List.append preservingCellPassZeroBits emitted).reverse.map some)
        (none :: tail)) := by
  simpa [preservingCellPassZeroBits] using
    prependFixedFourBitsLeftOfBlankSentinelDescription_haltsFrom_prepend
      false true false true emitted tail

def prependCellOneChunkLeftOfBlankSentinelDescription :
    MachineDescription :=
  prependFixedFourBitsLeftOfBlankSentinelDescription false true true false

theorem prependCellOneChunkLeftOfBlankSentinelDescription_subroutineReady :
    prependCellOneChunkLeftOfBlankSentinelDescription.SubroutineReady :=
  prependFixedFourBitsLeftOfBlankSentinelDescription_subroutineReady
    false true true false

theorem prependCellOneChunkLeftOfBlankSentinelDescription_haltsFrom_prepend
    (emitted : Word Bool) (tail : List (Option Bool)) :
    prependCellOneChunkLeftOfBlankSentinelDescription.HaltsFromTape
      (tapeAtCells (emitted.reverse.map some) (none :: tail))
      (tapeAtCells
        ((List.append preservingCellPassOneBits emitted).reverse.map some)
        (none :: tail)) := by
  simpa [preservingCellPassOneBits] using
    prependFixedFourBitsLeftOfBlankSentinelDescription_haltsFrom_prepend
      false true true false emitted tail

def prependCellChunkLeftOfBlankSentinelDescription
    (bit : Bool) : MachineDescription :=
  if bit then prependCellOneChunkLeftOfBlankSentinelDescription
  else prependCellZeroChunkLeftOfBlankSentinelDescription

theorem prependCellChunkLeftOfBlankSentinelDescription_subroutineReady
    (bit : Bool) :
    (prependCellChunkLeftOfBlankSentinelDescription bit).SubroutineReady := by
  cases bit
  · simpa [prependCellChunkLeftOfBlankSentinelDescription] using
      prependCellZeroChunkLeftOfBlankSentinelDescription_subroutineReady
  · simpa [prependCellChunkLeftOfBlankSentinelDescription] using
      prependCellOneChunkLeftOfBlankSentinelDescription_subroutineReady

theorem prependCellChunkLeftOfBlankSentinelDescription_haltsFrom_prepend
    (bit : Bool) (emitted : Word Bool)
    (tail : List (Option Bool)) :
    (prependCellChunkLeftOfBlankSentinelDescription bit).HaltsFromTape
      (tapeAtCells (emitted.reverse.map some) (none :: tail))
      (tapeAtCells
        ((List.append (preservingCellPassCellBits [bit]) emitted).reverse.map
          some)
        (none :: tail)) := by
  cases bit
  · simpa [prependCellChunkLeftOfBlankSentinelDescription,
      preservingCellPassCellBits, preservingCellPassZeroBits] using
      prependCellZeroChunkLeftOfBlankSentinelDescription_haltsFrom_prepend
        emitted tail
  · simpa [prependCellChunkLeftOfBlankSentinelDescription,
      preservingCellPassCellBits, preservingCellPassOneBits] using
      prependCellOneChunkLeftOfBlankSentinelDescription_haltsFrom_prepend
        emitted tail

theorem prependCellChunkLeftOfBlankSentinelDescription_target_moveLeftRight
    (bit : Bool) (emitted : Word Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tapeAtCells
            ((List.append (preservingCellPassCellBits [bit])
              emitted).reverse.map some)
            (none :: tail))) =
      tapeAtCells
        ((List.append (preservingCellPassCellBits [bit])
          emitted).reverse.map some)
        (none :: tail) := by
  cases bit
  · simpa [preservingCellPassCellBits, preservingCellPassZeroBits] using
      prependFixedFourBitsLeftOfBlankSentinelDescription_target_moveLeftRight
        false true false true emitted tail
  · simpa [preservingCellPassCellBits, preservingCellPassOneBits] using
      prependFixedFourBitsLeftOfBlankSentinelDescription_target_moveLeftRight
        false true true false emitted tail

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
