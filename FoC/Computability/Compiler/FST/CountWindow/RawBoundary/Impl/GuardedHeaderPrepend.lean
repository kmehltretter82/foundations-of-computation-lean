import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.LengthCursorLoop
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.EndpointSupport

set_option doc.verso true

/-!
# Raw-boundary guarded header prepender

This module provides the header-and-guard writer for the two-pass uniform
right-edge emitter.  Starting on the separator blank with the emitted
length-and-cell block immediately to its left, the machine scans left across
the block to the far-left anchor, writes the header chunk leftward, writes the
guard cell one further left, bounces one more cell left and back to
materialize the explicit blank the block-migration entry demands, then returns
right across the block and halts back on the separator.

The scan-left phase absorbs an optional leftover anchor blank at the far left
of the block (the length-cursor loop leaves one exactly when the raw layout is
empty): the anchor cell is overwritten by the first header bit, so the halt
tape is exact and identical with or without the anchor residue.
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

def rawBoundaryGuardedHeaderPrependHalt : Nat := 0

def rawBoundaryGuardedHeaderPrependStart : Nat := 1

def rawBoundaryGuardedHeaderPrependScanLeft : Nat := 2

def rawBoundaryGuardedHeaderPrependHeaderWrite2 : Nat := 3

def rawBoundaryGuardedHeaderPrependHeaderWrite1 : Nat := 4

def rawBoundaryGuardedHeaderPrependHeaderWrite0 : Nat := 5

def rawBoundaryGuardedHeaderPrependGuardWrite : Nat := 6

def rawBoundaryGuardedHeaderPrependGuardBounce : Nat := 7

def rawBoundaryGuardedHeaderPrependReturn : Nat := 8

def rawBoundaryGuardedHeaderPrependHaltBounce : Nat := 9

def rawBoundaryGuardedHeaderPrependDescription : MachineDescription where
  stateCount := 10
  start := rawBoundaryGuardedHeaderPrependStart
  halt := rawBoundaryGuardedHeaderPrependHalt
  transitions :=
    [ transition rawBoundaryGuardedHeaderPrependStart
        none none Direction.left rawBoundaryGuardedHeaderPrependScanLeft
    , transition rawBoundaryGuardedHeaderPrependScanLeft
        (some false) (some false) Direction.left
        rawBoundaryGuardedHeaderPrependScanLeft
    , transition rawBoundaryGuardedHeaderPrependScanLeft
        (some true) (some true) Direction.left
        rawBoundaryGuardedHeaderPrependScanLeft
    , transition rawBoundaryGuardedHeaderPrependScanLeft
        none (some false) Direction.left
        rawBoundaryGuardedHeaderPrependHeaderWrite2
    , transition rawBoundaryGuardedHeaderPrependHeaderWrite2
        none (some false) Direction.left
        rawBoundaryGuardedHeaderPrependHeaderWrite1
    , transition rawBoundaryGuardedHeaderPrependHeaderWrite1
        none (some false) Direction.left
        rawBoundaryGuardedHeaderPrependHeaderWrite0
    , transition rawBoundaryGuardedHeaderPrependHeaderWrite0
        none (some false) Direction.left
        rawBoundaryGuardedHeaderPrependGuardWrite
    , transition rawBoundaryGuardedHeaderPrependGuardWrite
        none (some true) Direction.left
        rawBoundaryGuardedHeaderPrependGuardBounce
    , transition rawBoundaryGuardedHeaderPrependGuardBounce
        none none Direction.right
        rawBoundaryGuardedHeaderPrependReturn
    , transition rawBoundaryGuardedHeaderPrependReturn
        (some false) (some false) Direction.right
        rawBoundaryGuardedHeaderPrependReturn
    , transition rawBoundaryGuardedHeaderPrependReturn
        (some true) (some true) Direction.right
        rawBoundaryGuardedHeaderPrependReturn
    , transition rawBoundaryGuardedHeaderPrependReturn
        none none Direction.left
        rawBoundaryGuardedHeaderPrependHaltBounce
    , transition rawBoundaryGuardedHeaderPrependHaltBounce
        (some false) (some false) Direction.right
        rawBoundaryGuardedHeaderPrependHalt
    , transition rawBoundaryGuardedHeaderPrependHaltBounce
        (some true) (some true) Direction.right
        rawBoundaryGuardedHeaderPrependHalt ]

theorem rawBoundaryGuardedHeaderPrependDescription_wellFormed :
    rawBoundaryGuardedHeaderPrependDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := rawBoundaryGuardedHeaderPrependDescription.transitions)
      (stateCount := rawBoundaryGuardedHeaderPrependDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := rawBoundaryGuardedHeaderPrependDescription.transitions)
      (by decide)

theorem rawBoundaryGuardedHeaderPrependDescription_haltTransitionFree :
    rawBoundaryGuardedHeaderPrependDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := rawBoundaryGuardedHeaderPrependDescription.transitions)
    (state := rawBoundaryGuardedHeaderPrependDescription.halt)
    (by decide)

theorem rawBoundaryGuardedHeaderPrependDescription_subroutineReady :
    rawBoundaryGuardedHeaderPrependDescription.SubroutineReady :=
  ⟨rawBoundaryGuardedHeaderPrependDescription_wellFormed,
    rawBoundaryGuardedHeaderPrependDescription_haltTransitionFree⟩

attribute [local simp]
  rawBoundaryGuardedHeaderPrependDescription
  rawBoundaryGuardedHeaderPrependHalt
  rawBoundaryGuardedHeaderPrependStart
  rawBoundaryGuardedHeaderPrependScanLeft
  rawBoundaryGuardedHeaderPrependHeaderWrite2
  rawBoundaryGuardedHeaderPrependHeaderWrite1
  rawBoundaryGuardedHeaderPrependHeaderWrite0
  rawBoundaryGuardedHeaderPrependGuardWrite
  rawBoundaryGuardedHeaderPrependGuardBounce
  rawBoundaryGuardedHeaderPrependReturn
  rawBoundaryGuardedHeaderPrependHaltBounce

/--
Scan view of the leftward pass: the block cells still to be crossed are held
reversed in the first argument, with the optional leftover anchor blank kept
at the far left.  Once the scan pops the anchor cell (explicit or implicit),
both anchor cases collapse to the same configuration.
-/
private def rawBoundaryGuardedHeaderScanTape
    (anchor : Bool) : Word Bool -> List (Option Bool) -> Tape Bool
  | [], right => tapeAtCells [] (none :: right)
  | bit :: rest, right =>
      tapeAtCells
        (List.append (rest.map some)
          (if anchor then [none] else []))
        (some bit :: right)

private theorem rawBoundaryGuardedHeaderPrependDescription_step_scanLeft_bit
    (anchor bit : Bool) (rest : Word Bool) (right : List (Option Bool)) :
    rawBoundaryGuardedHeaderPrependDescription.runConfig 1
        { state := rawBoundaryGuardedHeaderPrependScanLeft
          tape := rawBoundaryGuardedHeaderScanTape anchor (bit :: rest) right } =
      { state := rawBoundaryGuardedHeaderPrependScanLeft
        tape :=
          rawBoundaryGuardedHeaderScanTape anchor rest (some bit :: right) } := by
  cases anchor <;> cases bit <;> cases rest <;> cases right <;>
    simp [rawBoundaryGuardedHeaderScanTape, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft]

private theorem rawBoundaryGuardedHeaderPrependDescription_run_scanLeft
    (anchor : Bool) (remainingRev : Word Bool)
    (right : List (Option Bool)) :
    rawBoundaryGuardedHeaderPrependDescription.runConfig
        remainingRev.length
        { state := rawBoundaryGuardedHeaderPrependScanLeft
          tape := rawBoundaryGuardedHeaderScanTape anchor remainingRev right } =
      { state := rawBoundaryGuardedHeaderPrependScanLeft
        tape :=
          tapeAtCells []
            (none ::
              List.append (remainingRev.reverse.map some) right) } := by
  induction remainingRev generalizing right with
  | nil =>
      simp [rawBoundaryGuardedHeaderScanTape, runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      rw [rawBoundaryGuardedHeaderPrependDescription_step_scanLeft_bit]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: right)

private theorem rawBoundaryGuardedHeaderPrependDescription_run_start_scanLeft
    (anchor : Bool) (block : Word Bool) (right : List (Option Bool)) :
    rawBoundaryGuardedHeaderPrependDescription.runConfig 1
        { state := rawBoundaryGuardedHeaderPrependStart
          tape :=
            tapeAtCells
              (List.append (block.reverse.map some)
                (if anchor then [none] else []))
              (none :: right) } =
      { state := rawBoundaryGuardedHeaderPrependScanLeft
        tape :=
          rawBoundaryGuardedHeaderScanTape anchor block.reverse
            (none :: right) } := by
  cases hrev : block.reverse with
  | nil =>
      cases anchor <;>
        simp [rawBoundaryGuardedHeaderScanTape, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells, Tape.read,
          Tape.write, Tape.move, Tape.moveLeft]
  | cons bit rest =>
      cases anchor <;> cases bit <;>
        simp [rawBoundaryGuardedHeaderScanTape, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells, Tape.read,
          Tape.write, Tape.move, Tape.moveLeft]

private theorem rawBoundaryGuardedHeaderPrependDescription_run_writeBlock
    (right : List (Option Bool)) :
    rawBoundaryGuardedHeaderPrependDescription.runConfig 6
        { state := rawBoundaryGuardedHeaderPrependScanLeft
          tape := tapeAtCells [] (none :: right) } =
      { state := rawBoundaryGuardedHeaderPrependReturn
        tape :=
          tapeAtCells [none]
            (some true :: some false :: some false :: some false ::
              some false :: right) } := by
  cases right <;>
    simp [runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      Tape.moveRight]

private theorem rawBoundaryGuardedHeaderPrependDescription_step_return_bit
    (bit : Bool) (left right : List (Option Bool)) :
    rawBoundaryGuardedHeaderPrependDescription.runConfig 1
        { state := rawBoundaryGuardedHeaderPrependReturn
          tape := tapeAtCells left (some bit :: right) } =
      { state := rawBoundaryGuardedHeaderPrependReturn
        tape := tapeAtCells (some bit :: left) right } := by
  cases bit <;> cases right <;>
    simp [runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem rawBoundaryGuardedHeaderPrependDescription_run_return_scanRight
    (bits : Word Bool) (left right : List (Option Bool)) :
    rawBoundaryGuardedHeaderPrependDescription.runConfig bits.length
        { state := rawBoundaryGuardedHeaderPrependReturn
          tape := tapeAtCells left
            (List.append (bits.map some) right) } =
      { state := rawBoundaryGuardedHeaderPrependReturn
        tape :=
          tapeAtCells (List.append (bits.reverse.map some) left)
            right } := by
  induction bits generalizing left with
  | nil =>
      simp [runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      change
        rawBoundaryGuardedHeaderPrependDescription.runConfig rest.length
            (rawBoundaryGuardedHeaderPrependDescription.runConfig 1
              { state := rawBoundaryGuardedHeaderPrependReturn
                tape := tapeAtCells left
                  (some bit ::
                    List.append (rest.map some) right) }) =
          { state := rawBoundaryGuardedHeaderPrependReturn
            tape :=
              tapeAtCells
                (List.append ((bit :: rest).reverse.map some) left)
                right }
      rw [rawBoundaryGuardedHeaderPrependDescription_step_return_bit]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: left)

private theorem rawBoundaryGuardedHeaderPrependDescription_run_return_halt
    (bit : Bool) (left right : List (Option Bool)) :
    rawBoundaryGuardedHeaderPrependDescription.runConfig 2
        { state := rawBoundaryGuardedHeaderPrependReturn
          tape := tapeAtCells (some bit :: left) (none :: right) } =
      { state := rawBoundaryGuardedHeaderPrependHalt
        tape := tapeAtCells (some bit :: left) (none :: right) } := by
  cases bit <;> cases left <;> cases right <;>
    simp [runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      Tape.moveRight]

private theorem rawBoundaryGuardedHeaderPrependDescription_run_return_halt_append
    (xs : Word Bool) (g : Bool) (leftRest right : List (Option Bool)) :
    rawBoundaryGuardedHeaderPrependDescription.runConfig 2
        { state := rawBoundaryGuardedHeaderPrependReturn
          tape :=
            tapeAtCells (List.append (xs.map some) (some g :: leftRest))
              (none :: right) } =
      { state := rawBoundaryGuardedHeaderPrependHalt
        tape :=
          tapeAtCells (List.append (xs.map some) (some g :: leftRest))
            (none :: right) } := by
  cases xs with
  | nil =>
      simpa using
        rawBoundaryGuardedHeaderPrependDescription_run_return_halt
          g leftRest right
  | cons b bs =>
      simpa [List.cons_append] using
        rawBoundaryGuardedHeaderPrependDescription_run_return_halt
          b (List.append (bs.map some) (some g :: leftRest)) right

private theorem rawBoundaryGuardedHeaderPrependDescription_run_full
    (anchor : Bool) (block : Word Bool) (blankTail : Nat)
    (right : List (Option Bool)) :
    rawBoundaryGuardedHeaderPrependDescription.runConfig
        (2 * block.length + 14)
        { state := rawBoundaryGuardedHeaderPrependStart
          tape :=
            tapeAtCells
              (List.append (block.reverse.map some)
                (if anchor then [none] else []))
              (none ::
                List.append
                  (List.replicate (blankTail + 1) (none : Option Bool))
                  right) } =
      { state := rawBoundaryGuardedHeaderPrependHalt
        tape :=
          tapeAtCells
            (List.append (block.reverse.map some)
              [some false, some false, some false, some false, some true,
                none])
            (none ::
              List.append
                (List.replicate (blankTail + 1) (none : Option Bool))
                right) } := by
  rw [show 2 * block.length + 14 =
      1 + (block.length + (6 + ((5 + block.length) + 2))) by
    lia]
  rw [MachineDescription.runConfig_add]
  rw [rawBoundaryGuardedHeaderPrependDescription_run_start_scanLeft]
  rw [show block.length = block.reverse.length by
    simp]
  rw [MachineDescription.runConfig_add]
  rw [rawBoundaryGuardedHeaderPrependDescription_run_scanLeft]
  simp only [List.reverse_reverse]
  rw [MachineDescription.runConfig_add]
  rw [rawBoundaryGuardedHeaderPrependDescription_run_writeBlock]
  rw [MachineDescription.runConfig_add]
  rw [show 5 + block.reverse.length =
      (List.append [true, false, false, false, false] block).length by
    simp
    lia]
  rw [show
      (some true :: some false :: some false :: some false :: some false ::
          List.append (block.map some)
            (none ::
              List.append
                (List.replicate (blankTail + 1) (none : Option Bool))
                right)) =
        List.append
          ((List.append [true, false, false, false, false] block).map some)
          (none ::
            List.append
              (List.replicate (blankTail + 1) (none : Option Bool))
              right) by
    simp]
  rw [rawBoundaryGuardedHeaderPrependDescription_run_return_scanRight]
  rw [show
      (List.append
          ((List.append [true, false, false, false, false]
            block).reverse.map some)
          [none]) =
        List.append (block.reverse.map some)
          [some false, some false, some false, some false, some true,
            none] by
    simp [List.map_append, List.append_assoc]]
  exact
    rawBoundaryGuardedHeaderPrependDescription_run_return_halt_append
      block.reverse false
      [some false, some false, some false, some true, none]
      (List.append
        (List.replicate (blankTail + 1) (none : Option Bool))
        right)

/--
Folding equality for the halt tape's left cells: writing the header chunk and
guard immediately left of the emitted length-and-cell block yields exactly the
reversed encoded layout block followed by the guard cell and the bounce blank.
-/
theorem rawBoundaryGuardedHeaderPrependLeftCells_eq
    (layout : Word Bool) :
    List.append ((encodedLayoutBits layout).reverse.map some)
        ([some true, none] : List (Option Bool)) =
      List.append
        ((rawBoundaryLengthCursorOutputBits layout).reverse.map some)
        [some false, some false, some false, some false, some true,
          none] := by
  rw [encodedLayoutBits_eq_header_length_cells]
  simp [rawBoundaryLengthCursorOutputBits, encodeCodeSymbolAsInput,
    List.reverse_append, List.map_append, List.append_assoc]

/--
Entry-to-exit theorem, anchored form.  From the separator blank with the
emitted length-and-cell block left of it — optionally still carrying the
leftover anchor blank at the block's far left — the machine halts back on the
separator with the guarded encoded-layout block on the left.  The halt tape is
exact and does not depend on the anchor residue: the anchor cell is
overwritten by the first header bit.
-/
theorem rawBoundaryGuardedHeaderPrependDescription_haltsFrom_separator_anchored
    (anchor : Bool) (layout : Word Bool) (blankTail : Nat)
    (right : List (Option Bool)) :
    rawBoundaryGuardedHeaderPrependDescription.HaltsFromTape
      (tapeAtCells
        (List.append
          ((rawBoundaryLengthCursorOutputBits layout).reverse.map some)
          (if anchor then [none] else []))
        (none ::
          List.append
            (List.replicate (blankTail + 1) (none : Option Bool))
            right))
      (tapeAtCells
        (List.append ((encodedLayoutBits layout).reverse.map some)
          [some true, none])
        (none ::
          List.append
            (List.replicate (blankTail + 1) (none : Option Bool))
            right)) := by
  refine
    ⟨2 * (rawBoundaryLengthCursorOutputBits layout).length + 14, ?_⟩
  rw [rawBoundaryGuardedHeaderPrependLeftCells_eq]
  show
    (rawBoundaryGuardedHeaderPrependDescription.runConfig
        (2 * (rawBoundaryLengthCursorOutputBits layout).length + 14)
        { state := rawBoundaryGuardedHeaderPrependStart
          tape :=
            tapeAtCells
              (List.append
                ((rawBoundaryLengthCursorOutputBits layout).reverse.map
                  some)
                (if anchor then [none] else []))
              (none ::
                List.append
                  (List.replicate (blankTail + 1) (none : Option Bool))
                  right) }).state =
        rawBoundaryGuardedHeaderPrependHalt ∧
      (rawBoundaryGuardedHeaderPrependDescription.runConfig
        (2 * (rawBoundaryLengthCursorOutputBits layout).length + 14)
        { state := rawBoundaryGuardedHeaderPrependStart
          tape :=
            tapeAtCells
              (List.append
                ((rawBoundaryLengthCursorOutputBits layout).reverse.map
                  some)
                (if anchor then [none] else []))
              (none ::
                List.append
                  (List.replicate (blankTail + 1) (none : Option Bool))
                  right) }).tape =
        tapeAtCells
          (List.append
            ((rawBoundaryLengthCursorOutputBits layout).reverse.map some)
            [some false, some false, some false, some false, some true,
              none])
          (none ::
            List.append
              (List.replicate (blankTail + 1) (none : Option Bool))
              right)
  rw [rawBoundaryGuardedHeaderPrependDescription_run_full anchor
    (rawBoundaryLengthCursorOutputBits layout) blankTail right]
  exact ⟨rfl, rfl⟩

/--
Entry-to-exit theorem, separator form (anchor-free entry).  This is the seam
statement consumed by the uniform-emitter assembly: from the length-cursor
loop's separator tape holding its output block, the machine halts back on the
separator with left cells exactly the reversed encoded layout block, the guard
cell, and the materialized bounce blank the block-migration entry demands.
-/
theorem rawBoundaryGuardedHeaderPrependDescription_haltsFrom_separator
    (layout : Word Bool) (blankTail : Nat)
    (right : List (Option Bool)) :
    rawBoundaryGuardedHeaderPrependDescription.HaltsFromTape
      (rawBoundaryLengthCursorSeparatorTape
        (rawBoundaryLengthCursorOutputBits layout) blankTail right)
      (tapeAtCells
        (List.append ((encodedLayoutBits layout).reverse.map some)
          [some true, none])
        (none ::
          List.append
            (List.replicate (blankTail + 1) (none : Option Bool))
            right)) := by
  have h :=
    rawBoundaryGuardedHeaderPrependDescription_haltsFrom_separator_anchored
      false layout blankTail right
  simpa [rawBoundaryLengthCursorSeparatorTape] using h

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
