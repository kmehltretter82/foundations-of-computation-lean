import FoC.Computability.Compiler.Core.TransitionTableChecks
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.EmitPulledRawBit

set_option doc.verso true

/-!
# Raw-boundary chunk expansion loop

This module starts the uniform replacement for the old bounded raw-boundary
cell-suffix routes.  The loop keeps the head at the blank separator immediately
left of the unconsumed raw layout prefix.  Each iteration scans to the first
blank after the remaining raw bits, erases the rightmost bit, walks back left
over the separator and the already-emitted chunk block, then prepends the
corresponding four-bit cell chunk in the unbounded blank area to the left.
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

def rawBoundaryChunkExpandLoopHalt : Nat := 0

def rawBoundaryChunkExpandLoopStart : Nat := 1

def rawBoundaryChunkExpandLoopScan : Nat := 2

def rawBoundaryChunkExpandLoopScanRest : Nat := 3

def rawBoundaryChunkExpandLoopEraseRightmost : Nat := 4

def rawBoundaryChunkExpandLoopCarryFalse : Nat := 5

def rawBoundaryChunkExpandLoopAnchorFalse : Nat := 6

def rawBoundaryChunkExpandLoopWriteFalse2 : Nat := 7

def rawBoundaryChunkExpandLoopWriteFalse1 : Nat := 8

def rawBoundaryChunkExpandLoopWriteFalse0 : Nat := 9

def rawBoundaryChunkExpandLoopCarryTrue : Nat := 10

def rawBoundaryChunkExpandLoopAnchorTrue : Nat := 11

def rawBoundaryChunkExpandLoopWriteTrue2 : Nat := 12

def rawBoundaryChunkExpandLoopWriteTrue1 : Nat := 13

def rawBoundaryChunkExpandLoopWriteTrue0 : Nat := 14

def rawBoundaryChunkExpandLoopReturn : Nat := 15

def rawBoundaryChunkExpandLoopDescription : MachineDescription where
  stateCount := 16
  start := rawBoundaryChunkExpandLoopStart
  halt := rawBoundaryChunkExpandLoopHalt
  transitions :=
    [ transition rawBoundaryChunkExpandLoopStart
        none none Direction.right rawBoundaryChunkExpandLoopScan
    , transition rawBoundaryChunkExpandLoopScan
        none none Direction.left rawBoundaryChunkExpandLoopHalt
    , transition rawBoundaryChunkExpandLoopScan
        (some false) (some false) Direction.right
        rawBoundaryChunkExpandLoopScanRest
    , transition rawBoundaryChunkExpandLoopScan
        (some true) (some true) Direction.right
        rawBoundaryChunkExpandLoopScanRest
    , transition rawBoundaryChunkExpandLoopScanRest
        (some false) (some false) Direction.right
        rawBoundaryChunkExpandLoopScanRest
    , transition rawBoundaryChunkExpandLoopScanRest
        (some true) (some true) Direction.right
        rawBoundaryChunkExpandLoopScanRest
    , transition rawBoundaryChunkExpandLoopScanRest
        none none Direction.left rawBoundaryChunkExpandLoopEraseRightmost
    , transition rawBoundaryChunkExpandLoopEraseRightmost
        (some false) none Direction.left
        rawBoundaryChunkExpandLoopCarryFalse
    , transition rawBoundaryChunkExpandLoopEraseRightmost
        (some true) none Direction.left
        rawBoundaryChunkExpandLoopCarryTrue
    , transition rawBoundaryChunkExpandLoopCarryFalse
        (some false) (some false) Direction.left
        rawBoundaryChunkExpandLoopCarryFalse
    , transition rawBoundaryChunkExpandLoopCarryFalse
        (some true) (some true) Direction.left
        rawBoundaryChunkExpandLoopCarryFalse
    , transition rawBoundaryChunkExpandLoopCarryFalse
        none none Direction.left rawBoundaryChunkExpandLoopAnchorFalse
    , transition rawBoundaryChunkExpandLoopAnchorFalse
        (some false) (some false) Direction.left
        rawBoundaryChunkExpandLoopAnchorFalse
    , transition rawBoundaryChunkExpandLoopAnchorFalse
        (some true) (some true) Direction.left
        rawBoundaryChunkExpandLoopAnchorFalse
    , transition rawBoundaryChunkExpandLoopAnchorFalse
        none (some true) Direction.left
        rawBoundaryChunkExpandLoopWriteFalse2
    , transition rawBoundaryChunkExpandLoopWriteFalse2
        none (some false) Direction.left
        rawBoundaryChunkExpandLoopWriteFalse1
    , transition rawBoundaryChunkExpandLoopWriteFalse1
        none (some true) Direction.left
        rawBoundaryChunkExpandLoopWriteFalse0
    , transition rawBoundaryChunkExpandLoopWriteFalse0
        none (some false) Direction.right
        rawBoundaryChunkExpandLoopReturn
    , transition rawBoundaryChunkExpandLoopCarryTrue
        (some false) (some false) Direction.left
        rawBoundaryChunkExpandLoopCarryTrue
    , transition rawBoundaryChunkExpandLoopCarryTrue
        (some true) (some true) Direction.left
        rawBoundaryChunkExpandLoopCarryTrue
    , transition rawBoundaryChunkExpandLoopCarryTrue
        none none Direction.left rawBoundaryChunkExpandLoopAnchorTrue
    , transition rawBoundaryChunkExpandLoopAnchorTrue
        (some false) (some false) Direction.left
        rawBoundaryChunkExpandLoopAnchorTrue
    , transition rawBoundaryChunkExpandLoopAnchorTrue
        (some true) (some true) Direction.left
        rawBoundaryChunkExpandLoopAnchorTrue
    , transition rawBoundaryChunkExpandLoopAnchorTrue
        none (some false) Direction.left
        rawBoundaryChunkExpandLoopWriteTrue2
    , transition rawBoundaryChunkExpandLoopWriteTrue2
        none (some true) Direction.left
        rawBoundaryChunkExpandLoopWriteTrue1
    , transition rawBoundaryChunkExpandLoopWriteTrue1
        none (some true) Direction.left
        rawBoundaryChunkExpandLoopWriteTrue0
    , transition rawBoundaryChunkExpandLoopWriteTrue0
        none (some false) Direction.right
        rawBoundaryChunkExpandLoopReturn
    , transition rawBoundaryChunkExpandLoopReturn
        (some false) (some false) Direction.right
        rawBoundaryChunkExpandLoopReturn
    , transition rawBoundaryChunkExpandLoopReturn
        (some true) (some true) Direction.right
        rawBoundaryChunkExpandLoopReturn
    , transition rawBoundaryChunkExpandLoopReturn
        none none Direction.right rawBoundaryChunkExpandLoopScan ]

theorem rawBoundaryChunkExpandLoopDescription_wellFormed :
    rawBoundaryChunkExpandLoopDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := rawBoundaryChunkExpandLoopDescription.transitions)
      (stateCount := rawBoundaryChunkExpandLoopDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := rawBoundaryChunkExpandLoopDescription.transitions)
      (by decide)

theorem rawBoundaryChunkExpandLoopDescription_haltTransitionFree :
    rawBoundaryChunkExpandLoopDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := rawBoundaryChunkExpandLoopDescription.transitions)
    (state := rawBoundaryChunkExpandLoopDescription.halt)
    (by decide)

theorem rawBoundaryChunkExpandLoopDescription_subroutineReady :
    rawBoundaryChunkExpandLoopDescription.SubroutineReady :=
  ⟨rawBoundaryChunkExpandLoopDescription_wellFormed,
    rawBoundaryChunkExpandLoopDescription_haltTransitionFree⟩

def rawBoundaryChunkExpandCellBits (bit : Bool) : Word Bool :=
  pulledRawBitCellChunkBits bit

/--
Head-on-separator loop view.  The emitted chunk block lies immediately to the
left of the separator.  The unconsumed raw bits lie to its right, followed by
at least one blank and then the untouched live suffix.
-/
def rawBoundaryChunkExpandSeparatorTape
    (emitted remaining : Word Bool) (blankTail : Nat)
    (right : List (Option Bool)) : Tape Bool :=
  tapeAtCells (emitted.reverse.map some)
    (none ::
      List.append (remaining.map some)
        (List.append
          (List.replicate (blankTail + 1) (none : Option Bool))
          right))

/--
Internal scan view, one cell to the right of the separator.  State
{name}`rawBoundaryChunkExpandLoopScan` uses this view between iterations.
-/
def rawBoundaryChunkExpandScanTape
    (emitted remaining : Word Bool) (blankTail : Nat)
    (right : List (Option Bool)) : Tape Bool :=
  tapeAtCells (none :: emitted.reverse.map some)
    (List.append (remaining.map some)
      (List.append
        (List.replicate (blankTail + 1) (none : Option Bool))
        right))

theorem rawBoundaryChunkExpandLoopDescription_run_start
    (emitted remaining : Word Bool) (blankTail : Nat)
    (right : List (Option Bool)) :
    rawBoundaryChunkExpandLoopDescription.runConfig 1
        { state := rawBoundaryChunkExpandLoopStart
          tape :=
            rawBoundaryChunkExpandSeparatorTape
              emitted remaining blankTail right } =
      { state := rawBoundaryChunkExpandLoopScan
        tape :=
          rawBoundaryChunkExpandScanTape
            emitted remaining blankTail right } := by
  cases remaining with
  | nil =>
      simp [rawBoundaryChunkExpandLoopDescription,
        rawBoundaryChunkExpandLoopHalt,
        rawBoundaryChunkExpandLoopStart,
        rawBoundaryChunkExpandLoopScan,
        rawBoundaryChunkExpandLoopScanRest,
        rawBoundaryChunkExpandLoopEraseRightmost,
        rawBoundaryChunkExpandLoopCarryFalse,
        rawBoundaryChunkExpandLoopAnchorFalse,
        rawBoundaryChunkExpandLoopWriteFalse2,
        rawBoundaryChunkExpandLoopWriteFalse1,
        rawBoundaryChunkExpandLoopWriteFalse0,
        rawBoundaryChunkExpandLoopCarryTrue,
        rawBoundaryChunkExpandLoopAnchorTrue,
        rawBoundaryChunkExpandLoopWriteTrue2,
        rawBoundaryChunkExpandLoopWriteTrue1,
        rawBoundaryChunkExpandLoopWriteTrue0,
        rawBoundaryChunkExpandLoopReturn,
        rawBoundaryChunkExpandSeparatorTape,
        rawBoundaryChunkExpandScanTape, runConfig, stepConfig,
        lookupTransition, Matches, transition, tapeAtCells, Tape.read,
        Tape.write, Tape.move, Tape.moveRight, List.replicate_succ]
  | cons bit rest =>
      cases bit <;>
        simp [rawBoundaryChunkExpandLoopDescription,
          rawBoundaryChunkExpandLoopHalt,
          rawBoundaryChunkExpandLoopStart,
          rawBoundaryChunkExpandLoopScan,
          rawBoundaryChunkExpandLoopScanRest,
          rawBoundaryChunkExpandLoopEraseRightmost,
          rawBoundaryChunkExpandLoopCarryFalse,
          rawBoundaryChunkExpandLoopAnchorFalse,
          rawBoundaryChunkExpandLoopWriteFalse2,
          rawBoundaryChunkExpandLoopWriteFalse1,
          rawBoundaryChunkExpandLoopWriteFalse0,
          rawBoundaryChunkExpandLoopCarryTrue,
          rawBoundaryChunkExpandLoopAnchorTrue,
          rawBoundaryChunkExpandLoopWriteTrue2,
          rawBoundaryChunkExpandLoopWriteTrue1,
          rawBoundaryChunkExpandLoopWriteTrue0,
          rawBoundaryChunkExpandLoopReturn,
          rawBoundaryChunkExpandSeparatorTape,
          rawBoundaryChunkExpandScanTape, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells, Tape.read,
          Tape.write, Tape.move, Tape.moveRight]

theorem rawBoundaryChunkExpandLoopDescription_run_done
    (emitted : Word Bool) (blankTail : Nat)
    (right : List (Option Bool)) :
    rawBoundaryChunkExpandLoopDescription.runConfig 1
        { state := rawBoundaryChunkExpandLoopScan
          tape :=
            rawBoundaryChunkExpandScanTape
              emitted [] blankTail right } =
      { state := rawBoundaryChunkExpandLoopHalt
        tape :=
          rawBoundaryChunkExpandSeparatorTape
            emitted [] blankTail right } := by
  simp [rawBoundaryChunkExpandLoopDescription,
    rawBoundaryChunkExpandLoopHalt,
    rawBoundaryChunkExpandLoopStart,
    rawBoundaryChunkExpandLoopScan,
    rawBoundaryChunkExpandLoopScanRest,
    rawBoundaryChunkExpandLoopEraseRightmost,
    rawBoundaryChunkExpandLoopCarryFalse,
    rawBoundaryChunkExpandLoopAnchorFalse,
    rawBoundaryChunkExpandLoopWriteFalse2,
    rawBoundaryChunkExpandLoopWriteFalse1,
    rawBoundaryChunkExpandLoopWriteFalse0,
    rawBoundaryChunkExpandLoopCarryTrue,
    rawBoundaryChunkExpandLoopAnchorTrue,
    rawBoundaryChunkExpandLoopWriteTrue2,
    rawBoundaryChunkExpandLoopWriteTrue1,
    rawBoundaryChunkExpandLoopWriteTrue0,
    rawBoundaryChunkExpandLoopReturn,
    rawBoundaryChunkExpandSeparatorTape,
    rawBoundaryChunkExpandScanTape, runConfig, stepConfig,
    lookupTransition, Matches, transition, tapeAtCells, Tape.read,
    Tape.write, Tape.move, Tape.moveLeft, List.replicate_succ]

private def rawBoundaryChunkExpandScanRestTape
    (left : List (Option Bool)) : Word Bool -> Nat ->
      List (Option Bool) -> Tape Bool
  | [], blankTail, right =>
      tapeAtCells left
        (none ::
          List.append
            (List.replicate blankTail (none : Option Bool))
            right)
  | bit :: rest, blankTail, right =>
      tapeAtCells left
        (some bit ::
          List.append (rest.map some)
            (List.append
              (List.replicate (blankTail + 1) (none : Option Bool))
              right))

private theorem rawBoundaryChunkExpandLoopDescription_step_scanRest_bit
    (left : List (Option Bool)) (bit : Bool) (rest : Word Bool)
    (blankTail : Nat) (right : List (Option Bool)) :
    rawBoundaryChunkExpandLoopDescription.runConfig 1
        { state := rawBoundaryChunkExpandLoopScanRest
          tape := rawBoundaryChunkExpandScanRestTape left (bit :: rest) blankTail right } =
      { state := rawBoundaryChunkExpandLoopScanRest
        tape := rawBoundaryChunkExpandScanRestTape (some bit :: left) rest blankTail right } := by
  cases bit
  · cases rest with
    | nil =>
        simp [rawBoundaryChunkExpandScanRestTape, rawBoundaryChunkExpandLoopDescription,
          rawBoundaryChunkExpandLoopHalt,
          rawBoundaryChunkExpandLoopStart,
          rawBoundaryChunkExpandLoopScan,
          rawBoundaryChunkExpandLoopScanRest,
          rawBoundaryChunkExpandLoopEraseRightmost,
          rawBoundaryChunkExpandLoopCarryFalse,
          rawBoundaryChunkExpandLoopAnchorFalse,
          rawBoundaryChunkExpandLoopWriteFalse2,
          rawBoundaryChunkExpandLoopWriteFalse1,
          rawBoundaryChunkExpandLoopWriteFalse0,
          rawBoundaryChunkExpandLoopCarryTrue,
          rawBoundaryChunkExpandLoopAnchorTrue,
          rawBoundaryChunkExpandLoopWriteTrue2,
          rawBoundaryChunkExpandLoopWriteTrue1,
          rawBoundaryChunkExpandLoopWriteTrue0,
          rawBoundaryChunkExpandLoopReturn,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight,
          List.replicate_succ]
    | cons next more =>
        cases next <;>
          simp [rawBoundaryChunkExpandScanRestTape, rawBoundaryChunkExpandLoopDescription,
            rawBoundaryChunkExpandLoopHalt,
            rawBoundaryChunkExpandLoopStart,
            rawBoundaryChunkExpandLoopScan,
            rawBoundaryChunkExpandLoopScanRest,
            rawBoundaryChunkExpandLoopEraseRightmost,
            rawBoundaryChunkExpandLoopCarryFalse,
            rawBoundaryChunkExpandLoopAnchorFalse,
            rawBoundaryChunkExpandLoopWriteFalse2,
            rawBoundaryChunkExpandLoopWriteFalse1,
            rawBoundaryChunkExpandLoopWriteFalse0,
            rawBoundaryChunkExpandLoopCarryTrue,
            rawBoundaryChunkExpandLoopAnchorTrue,
            rawBoundaryChunkExpandLoopWriteTrue2,
            rawBoundaryChunkExpandLoopWriteTrue1,
            rawBoundaryChunkExpandLoopWriteTrue0,
            rawBoundaryChunkExpandLoopReturn,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]
  · cases rest with
    | nil =>
        simp [rawBoundaryChunkExpandScanRestTape, rawBoundaryChunkExpandLoopDescription,
          rawBoundaryChunkExpandLoopHalt,
          rawBoundaryChunkExpandLoopStart,
          rawBoundaryChunkExpandLoopScan,
          rawBoundaryChunkExpandLoopScanRest,
          rawBoundaryChunkExpandLoopEraseRightmost,
          rawBoundaryChunkExpandLoopCarryFalse,
          rawBoundaryChunkExpandLoopAnchorFalse,
          rawBoundaryChunkExpandLoopWriteFalse2,
          rawBoundaryChunkExpandLoopWriteFalse1,
          rawBoundaryChunkExpandLoopWriteFalse0,
          rawBoundaryChunkExpandLoopCarryTrue,
          rawBoundaryChunkExpandLoopAnchorTrue,
          rawBoundaryChunkExpandLoopWriteTrue2,
          rawBoundaryChunkExpandLoopWriteTrue1,
          rawBoundaryChunkExpandLoopWriteTrue0,
          rawBoundaryChunkExpandLoopReturn,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight,
          List.replicate_succ]
    | cons next more =>
        cases next <;>
          simp [rawBoundaryChunkExpandScanRestTape, rawBoundaryChunkExpandLoopDescription,
            rawBoundaryChunkExpandLoopHalt,
            rawBoundaryChunkExpandLoopStart,
            rawBoundaryChunkExpandLoopScan,
            rawBoundaryChunkExpandLoopScanRest,
            rawBoundaryChunkExpandLoopEraseRightmost,
            rawBoundaryChunkExpandLoopCarryFalse,
            rawBoundaryChunkExpandLoopAnchorFalse,
            rawBoundaryChunkExpandLoopWriteFalse2,
            rawBoundaryChunkExpandLoopWriteFalse1,
            rawBoundaryChunkExpandLoopWriteFalse0,
            rawBoundaryChunkExpandLoopCarryTrue,
            rawBoundaryChunkExpandLoopAnchorTrue,
            rawBoundaryChunkExpandLoopWriteTrue2,
            rawBoundaryChunkExpandLoopWriteTrue1,
            rawBoundaryChunkExpandLoopWriteTrue0,
            rawBoundaryChunkExpandLoopReturn,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem rawBoundaryChunkExpandLoopDescription_run_scanRest_to_rightmost
    (left : List (Option Bool)) (pref : Word Bool)
    (rawBit : Bool) (blankTail : Nat)
    (right : List (Option Bool)) :
    rawBoundaryChunkExpandLoopDescription.runConfig (pref.length + 2)
        { state := rawBoundaryChunkExpandLoopScanRest
          tape :=
            rawBoundaryChunkExpandScanRestTape left (List.append pref [rawBit])
              blankTail right } =
      { state := rawBoundaryChunkExpandLoopEraseRightmost
        tape :=
          tapeAtCells
            (List.append (pref.reverse.map some) left)
            (some rawBit ::
              List.append
                (List.replicate (blankTail + 1) (none : Option Bool))
                right) } := by
  induction pref generalizing left with
  | nil =>
      cases rawBit <;>
        simp [rawBoundaryChunkExpandScanRestTape, rawBoundaryChunkExpandLoopDescription,
          rawBoundaryChunkExpandLoopHalt,
          rawBoundaryChunkExpandLoopStart,
          rawBoundaryChunkExpandLoopScan,
          rawBoundaryChunkExpandLoopScanRest,
          rawBoundaryChunkExpandLoopEraseRightmost,
          rawBoundaryChunkExpandLoopCarryFalse,
          rawBoundaryChunkExpandLoopAnchorFalse,
          rawBoundaryChunkExpandLoopWriteFalse2,
          rawBoundaryChunkExpandLoopWriteFalse1,
          rawBoundaryChunkExpandLoopWriteFalse0,
          rawBoundaryChunkExpandLoopCarryTrue,
          rawBoundaryChunkExpandLoopAnchorTrue,
          rawBoundaryChunkExpandLoopWriteTrue2,
          rawBoundaryChunkExpandLoopWriteTrue1,
          rawBoundaryChunkExpandLoopWriteTrue0,
          rawBoundaryChunkExpandLoopReturn,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          Tape.moveRight, List.replicate_succ]
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 2 =
          1 + (rest.length + 2) by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      rw [show List.append (bit :: rest) [rawBit] =
          bit :: List.append rest [rawBit] by rfl]
      rw [rawBoundaryChunkExpandLoopDescription_step_scanRest_bit]
      cases bit
      · simpa [List.append_assoc] using ih (some false :: left)
      · simpa [List.append_assoc] using ih (some true :: left)

private theorem rawBoundaryChunkExpandLoopDescription_step_scan_bit
    (emitted : Word Bool) (bit : Bool) (rest : Word Bool)
    (blankTail : Nat) (right : List (Option Bool)) :
    rawBoundaryChunkExpandLoopDescription.runConfig 1
        { state := rawBoundaryChunkExpandLoopScan
          tape :=
            rawBoundaryChunkExpandScanTape
              emitted (bit :: rest) blankTail right } =
      { state := rawBoundaryChunkExpandLoopScanRest
        tape :=
          rawBoundaryChunkExpandScanRestTape
            (some bit :: none :: emitted.reverse.map some)
            rest blankTail right } := by
  cases bit
  · cases rest with
    | nil =>
        simp [rawBoundaryChunkExpandScanRestTape, rawBoundaryChunkExpandScanTape,
          rawBoundaryChunkExpandLoopDescription,
          rawBoundaryChunkExpandLoopHalt,
          rawBoundaryChunkExpandLoopStart,
          rawBoundaryChunkExpandLoopScan,
          rawBoundaryChunkExpandLoopScanRest,
          rawBoundaryChunkExpandLoopEraseRightmost,
          rawBoundaryChunkExpandLoopCarryFalse,
          rawBoundaryChunkExpandLoopAnchorFalse,
          rawBoundaryChunkExpandLoopWriteFalse2,
          rawBoundaryChunkExpandLoopWriteFalse1,
          rawBoundaryChunkExpandLoopWriteFalse0,
          rawBoundaryChunkExpandLoopCarryTrue,
          rawBoundaryChunkExpandLoopAnchorTrue,
          rawBoundaryChunkExpandLoopWriteTrue2,
          rawBoundaryChunkExpandLoopWriteTrue1,
          rawBoundaryChunkExpandLoopWriteTrue0,
          rawBoundaryChunkExpandLoopReturn,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight,
          List.replicate_succ]
    | cons next more =>
        cases next <;>
          simp [rawBoundaryChunkExpandScanRestTape, rawBoundaryChunkExpandScanTape,
            rawBoundaryChunkExpandLoopDescription,
            rawBoundaryChunkExpandLoopHalt,
            rawBoundaryChunkExpandLoopStart,
            rawBoundaryChunkExpandLoopScan,
            rawBoundaryChunkExpandLoopScanRest,
            rawBoundaryChunkExpandLoopEraseRightmost,
            rawBoundaryChunkExpandLoopCarryFalse,
            rawBoundaryChunkExpandLoopAnchorFalse,
            rawBoundaryChunkExpandLoopWriteFalse2,
            rawBoundaryChunkExpandLoopWriteFalse1,
            rawBoundaryChunkExpandLoopWriteFalse0,
            rawBoundaryChunkExpandLoopCarryTrue,
            rawBoundaryChunkExpandLoopAnchorTrue,
            rawBoundaryChunkExpandLoopWriteTrue2,
            rawBoundaryChunkExpandLoopWriteTrue1,
            rawBoundaryChunkExpandLoopWriteTrue0,
            rawBoundaryChunkExpandLoopReturn,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]
  · cases rest with
    | nil =>
        simp [rawBoundaryChunkExpandScanRestTape, rawBoundaryChunkExpandScanTape,
          rawBoundaryChunkExpandLoopDescription,
          rawBoundaryChunkExpandLoopHalt,
          rawBoundaryChunkExpandLoopStart,
          rawBoundaryChunkExpandLoopScan,
          rawBoundaryChunkExpandLoopScanRest,
          rawBoundaryChunkExpandLoopEraseRightmost,
          rawBoundaryChunkExpandLoopCarryFalse,
          rawBoundaryChunkExpandLoopAnchorFalse,
          rawBoundaryChunkExpandLoopWriteFalse2,
          rawBoundaryChunkExpandLoopWriteFalse1,
          rawBoundaryChunkExpandLoopWriteFalse0,
          rawBoundaryChunkExpandLoopCarryTrue,
          rawBoundaryChunkExpandLoopAnchorTrue,
          rawBoundaryChunkExpandLoopWriteTrue2,
          rawBoundaryChunkExpandLoopWriteTrue1,
          rawBoundaryChunkExpandLoopWriteTrue0,
          rawBoundaryChunkExpandLoopReturn,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight,
          List.replicate_succ]
    | cons next more =>
        cases next <;>
          simp [rawBoundaryChunkExpandScanRestTape, rawBoundaryChunkExpandScanTape,
            rawBoundaryChunkExpandLoopDescription,
            rawBoundaryChunkExpandLoopHalt,
            rawBoundaryChunkExpandLoopStart,
            rawBoundaryChunkExpandLoopScan,
            rawBoundaryChunkExpandLoopScanRest,
            rawBoundaryChunkExpandLoopEraseRightmost,
            rawBoundaryChunkExpandLoopCarryFalse,
            rawBoundaryChunkExpandLoopAnchorFalse,
            rawBoundaryChunkExpandLoopWriteFalse2,
            rawBoundaryChunkExpandLoopWriteFalse1,
            rawBoundaryChunkExpandLoopWriteFalse0,
            rawBoundaryChunkExpandLoopCarryTrue,
            rawBoundaryChunkExpandLoopAnchorTrue,
            rawBoundaryChunkExpandLoopWriteTrue2,
            rawBoundaryChunkExpandLoopWriteTrue1,
            rawBoundaryChunkExpandLoopWriteTrue0,
            rawBoundaryChunkExpandLoopReturn,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem rawBoundaryChunkExpandLoopDescription_run_scan_to_rightmost
    (emitted pref : Word Bool) (rawBit : Bool) (blankTail : Nat)
    (right : List (Option Bool)) :
    rawBoundaryChunkExpandLoopDescription.runConfig (pref.length + 2)
        { state := rawBoundaryChunkExpandLoopScan
          tape :=
            rawBoundaryChunkExpandScanTape
              emitted (List.append pref [rawBit]) blankTail right } =
      { state := rawBoundaryChunkExpandLoopEraseRightmost
        tape :=
          tapeAtCells
            (List.append (pref.reverse.map some)
              (none :: emitted.reverse.map some))
            (some rawBit ::
              List.append
                (List.replicate (blankTail + 1) (none : Option Bool))
                right) } := by
  cases pref with
  | nil =>
      rw [show ([] : Word Bool).length + 2 = 1 + 1 by rfl]
      rw [MachineDescription.runConfig_add]
      rw [show List.append ([] : Word Bool) [rawBit] =
          rawBit :: [] by rfl]
      rw [rawBoundaryChunkExpandLoopDescription_step_scan_bit]
      cases rawBit <;>
        simp [rawBoundaryChunkExpandScanRestTape, rawBoundaryChunkExpandLoopDescription,
          rawBoundaryChunkExpandLoopHalt,
          rawBoundaryChunkExpandLoopStart,
          rawBoundaryChunkExpandLoopScan,
          rawBoundaryChunkExpandLoopScanRest,
          rawBoundaryChunkExpandLoopEraseRightmost,
          rawBoundaryChunkExpandLoopCarryFalse,
          rawBoundaryChunkExpandLoopAnchorFalse,
          rawBoundaryChunkExpandLoopWriteFalse2,
          rawBoundaryChunkExpandLoopWriteFalse1,
          rawBoundaryChunkExpandLoopWriteFalse0,
          rawBoundaryChunkExpandLoopCarryTrue,
          rawBoundaryChunkExpandLoopAnchorTrue,
          rawBoundaryChunkExpandLoopWriteTrue2,
          rawBoundaryChunkExpandLoopWriteTrue1,
          rawBoundaryChunkExpandLoopWriteTrue0,
          rawBoundaryChunkExpandLoopReturn,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          List.replicate_succ]
  | cons bit rest =>
      rw [show (bit :: rest).length + 2 =
          1 + (rest.length + 2) by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      rw [show List.append (bit :: rest) [rawBit] =
          bit :: List.append rest [rawBit] by rfl]
      rw [rawBoundaryChunkExpandLoopDescription_step_scan_bit]
      rw [rawBoundaryChunkExpandLoopDescription_run_scanRest_to_rightmost]
      cases bit
      · simp [List.reverse_cons, List.map_append, List.append_assoc]
      · simp [List.reverse_cons, List.map_append, List.append_assoc]

private def rawBoundaryChunkExpandCarryState (rawBit : Bool) : Nat :=
  if rawBit then rawBoundaryChunkExpandLoopCarryTrue
  else rawBoundaryChunkExpandLoopCarryFalse

private def rawBoundaryChunkExpandAnchorState (rawBit : Bool) : Nat :=
  if rawBit then rawBoundaryChunkExpandLoopAnchorTrue
  else rawBoundaryChunkExpandLoopAnchorFalse

private def rawBoundaryChunkExpandCarryTape
    (emitted : Word Bool) : Word Bool -> List (Option Bool) -> Tape Bool
  | [], right =>
      tapeAtCells (emitted.reverse.map some) (none :: right)
  | bit :: rest, right =>
      tapeAtCells
        (List.append (rest.map some)
          (none :: emitted.reverse.map some))
        (some bit :: right)

private def rawBoundaryChunkExpandAnchorTape : Word Bool -> List (Option Bool) -> Tape Bool
  | [], right => tapeAtCells [] (none :: right)
  | bit :: rest, right => tapeAtCells (rest.map some) (some bit :: right)

private theorem rawBoundaryChunkExpandLoopDescription_step_eraseRightmost
    (emitted pref : Word Bool) (rawBit : Bool) (blankTail : Nat)
    (right : List (Option Bool)) :
    rawBoundaryChunkExpandLoopDescription.runConfig 1
        { state := rawBoundaryChunkExpandLoopEraseRightmost
          tape :=
            tapeAtCells
              (List.append (pref.reverse.map some)
                (none :: emitted.reverse.map some))
              (some rawBit ::
                List.append
                  (List.replicate (blankTail + 1) (none : Option Bool))
                  right) } =
      { state := rawBoundaryChunkExpandCarryState rawBit
        tape :=
          rawBoundaryChunkExpandCarryTape emitted pref.reverse
            (none ::
              List.append
                (List.replicate (blankTail + 1) (none : Option Bool))
                right) } := by
  cases rawBit <;> cases hrev : pref.reverse with
  | nil =>
      simp [rawBoundaryChunkExpandCarryState, rawBoundaryChunkExpandCarryTape,
        rawBoundaryChunkExpandLoopDescription,
        rawBoundaryChunkExpandLoopHalt,
        rawBoundaryChunkExpandLoopStart,
        rawBoundaryChunkExpandLoopScan,
        rawBoundaryChunkExpandLoopScanRest,
        rawBoundaryChunkExpandLoopEraseRightmost,
        rawBoundaryChunkExpandLoopCarryFalse,
        rawBoundaryChunkExpandLoopAnchorFalse,
        rawBoundaryChunkExpandLoopWriteFalse2,
        rawBoundaryChunkExpandLoopWriteFalse1,
        rawBoundaryChunkExpandLoopWriteFalse0,
        rawBoundaryChunkExpandLoopCarryTrue,
        rawBoundaryChunkExpandLoopAnchorTrue,
        rawBoundaryChunkExpandLoopWriteTrue2,
        rawBoundaryChunkExpandLoopWriteTrue1,
        rawBoundaryChunkExpandLoopWriteTrue0,
        rawBoundaryChunkExpandLoopReturn,
        runConfig, stepConfig, lookupTransition, Matches, transition,
        tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
  | cons bit rest =>
      cases bit <;>
        simp [rawBoundaryChunkExpandCarryState, rawBoundaryChunkExpandCarryTape,
          rawBoundaryChunkExpandLoopDescription,
          rawBoundaryChunkExpandLoopHalt,
          rawBoundaryChunkExpandLoopStart,
          rawBoundaryChunkExpandLoopScan,
          rawBoundaryChunkExpandLoopScanRest,
          rawBoundaryChunkExpandLoopEraseRightmost,
          rawBoundaryChunkExpandLoopCarryFalse,
          rawBoundaryChunkExpandLoopAnchorFalse,
          rawBoundaryChunkExpandLoopWriteFalse2,
          rawBoundaryChunkExpandLoopWriteFalse1,
          rawBoundaryChunkExpandLoopWriteFalse0,
          rawBoundaryChunkExpandLoopCarryTrue,
          rawBoundaryChunkExpandLoopAnchorTrue,
          rawBoundaryChunkExpandLoopWriteTrue2,
          rawBoundaryChunkExpandLoopWriteTrue1,
          rawBoundaryChunkExpandLoopWriteTrue0,
          rawBoundaryChunkExpandLoopReturn,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft]

private theorem rawBoundaryChunkExpandLoopDescription_step_carry_bit
    (emitted : Word Bool) (rawBit bit : Bool) (rest : Word Bool)
    (right : List (Option Bool)) :
    rawBoundaryChunkExpandLoopDescription.runConfig 1
        { state := rawBoundaryChunkExpandCarryState rawBit
          tape := rawBoundaryChunkExpandCarryTape emitted (bit :: rest) right } =
      { state := rawBoundaryChunkExpandCarryState rawBit
        tape := rawBoundaryChunkExpandCarryTape emitted rest (some bit :: right) } := by
  cases rawBit <;> cases bit <;> cases rest <;>
    simp [rawBoundaryChunkExpandCarryState, rawBoundaryChunkExpandCarryTape,
      rawBoundaryChunkExpandLoopDescription,
      rawBoundaryChunkExpandLoopHalt,
      rawBoundaryChunkExpandLoopStart,
      rawBoundaryChunkExpandLoopScan,
      rawBoundaryChunkExpandLoopScanRest,
      rawBoundaryChunkExpandLoopEraseRightmost,
      rawBoundaryChunkExpandLoopCarryFalse,
      rawBoundaryChunkExpandLoopAnchorFalse,
      rawBoundaryChunkExpandLoopWriteFalse2,
      rawBoundaryChunkExpandLoopWriteFalse1,
      rawBoundaryChunkExpandLoopWriteFalse0,
      rawBoundaryChunkExpandLoopCarryTrue,
      rawBoundaryChunkExpandLoopAnchorTrue,
      rawBoundaryChunkExpandLoopWriteTrue2,
      rawBoundaryChunkExpandLoopWriteTrue1,
      rawBoundaryChunkExpandLoopWriteTrue0,
      rawBoundaryChunkExpandLoopReturn,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft]

private theorem rawBoundaryChunkExpandLoopDescription_step_carry_separator
    (emitted : Word Bool) (rawBit : Bool)
    (right : List (Option Bool)) :
    rawBoundaryChunkExpandLoopDescription.runConfig 1
        { state := rawBoundaryChunkExpandCarryState rawBit
          tape := rawBoundaryChunkExpandCarryTape emitted [] right } =
      { state := rawBoundaryChunkExpandAnchorState rawBit
        tape := rawBoundaryChunkExpandAnchorTape emitted.reverse (none :: right) } := by
  cases rawBit <;> cases hrev : emitted.reverse with
  | nil =>
      simp [rawBoundaryChunkExpandCarryState, rawBoundaryChunkExpandAnchorState, rawBoundaryChunkExpandCarryTape,
        rawBoundaryChunkExpandAnchorTape, rawBoundaryChunkExpandLoopDescription,
        rawBoundaryChunkExpandLoopHalt,
        rawBoundaryChunkExpandLoopStart,
        rawBoundaryChunkExpandLoopScan,
        rawBoundaryChunkExpandLoopScanRest,
        rawBoundaryChunkExpandLoopEraseRightmost,
        rawBoundaryChunkExpandLoopCarryFalse,
        rawBoundaryChunkExpandLoopAnchorFalse,
        rawBoundaryChunkExpandLoopWriteFalse2,
        rawBoundaryChunkExpandLoopWriteFalse1,
        rawBoundaryChunkExpandLoopWriteFalse0,
        rawBoundaryChunkExpandLoopCarryTrue,
        rawBoundaryChunkExpandLoopAnchorTrue,
        rawBoundaryChunkExpandLoopWriteTrue2,
        rawBoundaryChunkExpandLoopWriteTrue1,
        rawBoundaryChunkExpandLoopWriteTrue0,
        rawBoundaryChunkExpandLoopReturn,
        runConfig, stepConfig, lookupTransition, Matches, transition,
        tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
        hrev]
  | cons bit rest =>
      cases bit <;>
        simp [rawBoundaryChunkExpandCarryState, rawBoundaryChunkExpandAnchorState, rawBoundaryChunkExpandCarryTape,
          rawBoundaryChunkExpandAnchorTape, rawBoundaryChunkExpandLoopDescription,
          rawBoundaryChunkExpandLoopHalt,
          rawBoundaryChunkExpandLoopStart,
          rawBoundaryChunkExpandLoopScan,
          rawBoundaryChunkExpandLoopScanRest,
          rawBoundaryChunkExpandLoopEraseRightmost,
          rawBoundaryChunkExpandLoopCarryFalse,
          rawBoundaryChunkExpandLoopAnchorFalse,
          rawBoundaryChunkExpandLoopWriteFalse2,
          rawBoundaryChunkExpandLoopWriteFalse1,
          rawBoundaryChunkExpandLoopWriteFalse0,
          rawBoundaryChunkExpandLoopCarryTrue,
          rawBoundaryChunkExpandLoopAnchorTrue,
          rawBoundaryChunkExpandLoopWriteTrue2,
          rawBoundaryChunkExpandLoopWriteTrue1,
          rawBoundaryChunkExpandLoopWriteTrue0,
          rawBoundaryChunkExpandLoopReturn,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          hrev]

private theorem rawBoundaryChunkExpandLoopDescription_run_carry_to_anchor
    (emitted remainingRev : Word Bool) (rawBit : Bool)
    (right : List (Option Bool)) :
    rawBoundaryChunkExpandLoopDescription.runConfig
        (remainingRev.length + 1)
        { state := rawBoundaryChunkExpandCarryState rawBit
          tape := rawBoundaryChunkExpandCarryTape emitted remainingRev right } =
      { state := rawBoundaryChunkExpandAnchorState rawBit
        tape :=
          rawBoundaryChunkExpandAnchorTape emitted.reverse
            (none ::
              List.append (remainingRev.reverse.map some) right) } := by
  induction remainingRev generalizing right with
  | nil =>
      simpa using rawBoundaryChunkExpandLoopDescription_step_carry_separator emitted rawBit right
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 =
          1 + (rest.length + 1) by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      rw [rawBoundaryChunkExpandLoopDescription_step_carry_bit]
      rw [ih (some bit :: right)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

private theorem rawBoundaryChunkExpandLoopDescription_step_anchor_bit
    (rawBit bit : Bool) (rest : Word Bool)
    (right : List (Option Bool)) :
    rawBoundaryChunkExpandLoopDescription.runConfig 1
        { state := rawBoundaryChunkExpandAnchorState rawBit
          tape := rawBoundaryChunkExpandAnchorTape (bit :: rest) right } =
      { state := rawBoundaryChunkExpandAnchorState rawBit
        tape := rawBoundaryChunkExpandAnchorTape rest (some bit :: right) } := by
  cases rawBit <;> cases bit <;> cases rest <;>
    simp [rawBoundaryChunkExpandAnchorState, rawBoundaryChunkExpandAnchorTape,
      rawBoundaryChunkExpandLoopDescription,
      rawBoundaryChunkExpandLoopHalt,
      rawBoundaryChunkExpandLoopStart,
      rawBoundaryChunkExpandLoopScan,
      rawBoundaryChunkExpandLoopScanRest,
      rawBoundaryChunkExpandLoopEraseRightmost,
      rawBoundaryChunkExpandLoopCarryFalse,
      rawBoundaryChunkExpandLoopAnchorFalse,
      rawBoundaryChunkExpandLoopWriteFalse2,
      rawBoundaryChunkExpandLoopWriteFalse1,
      rawBoundaryChunkExpandLoopWriteFalse0,
      rawBoundaryChunkExpandLoopCarryTrue,
      rawBoundaryChunkExpandLoopAnchorTrue,
      rawBoundaryChunkExpandLoopWriteTrue2,
      rawBoundaryChunkExpandLoopWriteTrue1,
      rawBoundaryChunkExpandLoopWriteTrue0,
      rawBoundaryChunkExpandLoopReturn,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft]

private theorem rawBoundaryChunkExpandLoopDescription_run_anchor_scan_left
    (remainingRev : Word Bool) (rawBit : Bool)
    (right : List (Option Bool)) :
    rawBoundaryChunkExpandLoopDescription.runConfig
        remainingRev.length
        { state := rawBoundaryChunkExpandAnchorState rawBit
          tape := rawBoundaryChunkExpandAnchorTape remainingRev right } =
      { state := rawBoundaryChunkExpandAnchorState rawBit
        tape :=
          tapeAtCells []
            (none ::
              List.append (remainingRev.reverse.map some) right) } := by
  induction remainingRev generalizing right with
  | nil =>
      simp [rawBoundaryChunkExpandAnchorTape, runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      rw [rawBoundaryChunkExpandLoopDescription_step_anchor_bit]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: right)

private theorem rawBoundaryChunkExpandLoopDescription_run_anchor_write_false
    (right : List (Option Bool)) :
    rawBoundaryChunkExpandLoopDescription.runConfig 4
        { state := rawBoundaryChunkExpandLoopAnchorFalse
          tape := tapeAtCells [] (none :: right) } =
      { state := rawBoundaryChunkExpandLoopReturn
        tape := tapeAtCells [some false]
          (some true :: some false :: some true :: right) } := by
  simp [rawBoundaryChunkExpandLoopDescription,
    rawBoundaryChunkExpandLoopHalt,
    rawBoundaryChunkExpandLoopStart,
    rawBoundaryChunkExpandLoopScan,
    rawBoundaryChunkExpandLoopScanRest,
    rawBoundaryChunkExpandLoopEraseRightmost,
    rawBoundaryChunkExpandLoopCarryFalse,
    rawBoundaryChunkExpandLoopAnchorFalse,
    rawBoundaryChunkExpandLoopWriteFalse2,
    rawBoundaryChunkExpandLoopWriteFalse1,
    rawBoundaryChunkExpandLoopWriteFalse0,
    rawBoundaryChunkExpandLoopCarryTrue,
    rawBoundaryChunkExpandLoopAnchorTrue,
    rawBoundaryChunkExpandLoopWriteTrue2,
    rawBoundaryChunkExpandLoopWriteTrue1,
    rawBoundaryChunkExpandLoopWriteTrue0,
    rawBoundaryChunkExpandLoopReturn,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight]

private theorem rawBoundaryChunkExpandLoopDescription_run_anchor_write_true
    (right : List (Option Bool)) :
    rawBoundaryChunkExpandLoopDescription.runConfig 4
        { state := rawBoundaryChunkExpandLoopAnchorTrue
          tape := tapeAtCells [] (none :: right) } =
      { state := rawBoundaryChunkExpandLoopReturn
        tape := tapeAtCells [some false]
          (some true :: some true :: some false :: right) } := by
  simp [rawBoundaryChunkExpandLoopDescription,
    rawBoundaryChunkExpandLoopHalt,
    rawBoundaryChunkExpandLoopStart,
    rawBoundaryChunkExpandLoopScan,
    rawBoundaryChunkExpandLoopScanRest,
    rawBoundaryChunkExpandLoopEraseRightmost,
    rawBoundaryChunkExpandLoopCarryFalse,
    rawBoundaryChunkExpandLoopAnchorFalse,
    rawBoundaryChunkExpandLoopWriteFalse2,
    rawBoundaryChunkExpandLoopWriteFalse1,
    rawBoundaryChunkExpandLoopWriteFalse0,
    rawBoundaryChunkExpandLoopCarryTrue,
    rawBoundaryChunkExpandLoopAnchorTrue,
    rawBoundaryChunkExpandLoopWriteTrue2,
    rawBoundaryChunkExpandLoopWriteTrue1,
    rawBoundaryChunkExpandLoopWriteTrue0,
    rawBoundaryChunkExpandLoopReturn,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight]

private theorem rawBoundaryChunkExpandLoopDescription_step_return_bit
    (bit : Bool) (left right : List (Option Bool)) :
    rawBoundaryChunkExpandLoopDescription.runConfig 1
        { state := rawBoundaryChunkExpandLoopReturn
          tape := tapeAtCells left (some bit :: right) } =
      { state := rawBoundaryChunkExpandLoopReturn
        tape := tapeAtCells (some bit :: left) right } := by
  cases bit <;> cases right <;>
    simp [rawBoundaryChunkExpandLoopDescription,
      rawBoundaryChunkExpandLoopHalt,
      rawBoundaryChunkExpandLoopStart,
      rawBoundaryChunkExpandLoopScan,
      rawBoundaryChunkExpandLoopScanRest,
      rawBoundaryChunkExpandLoopEraseRightmost,
      rawBoundaryChunkExpandLoopCarryFalse,
      rawBoundaryChunkExpandLoopAnchorFalse,
      rawBoundaryChunkExpandLoopWriteFalse2,
      rawBoundaryChunkExpandLoopWriteFalse1,
      rawBoundaryChunkExpandLoopWriteFalse0,
      rawBoundaryChunkExpandLoopCarryTrue,
      rawBoundaryChunkExpandLoopAnchorTrue,
      rawBoundaryChunkExpandLoopWriteTrue2,
      rawBoundaryChunkExpandLoopWriteTrue1,
      rawBoundaryChunkExpandLoopWriteTrue0,
      rawBoundaryChunkExpandLoopReturn,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem rawBoundaryChunkExpandLoopDescription_run_return_scan_right
    (bits : Word Bool) (left right : List (Option Bool)) :
    rawBoundaryChunkExpandLoopDescription.runConfig bits.length
        { state := rawBoundaryChunkExpandLoopReturn
          tape := tapeAtCells left
            (List.append (bits.map some) right) } =
      { state := rawBoundaryChunkExpandLoopReturn
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
        rawBoundaryChunkExpandLoopDescription.runConfig rest.length
            (rawBoundaryChunkExpandLoopDescription.runConfig 1
              { state := rawBoundaryChunkExpandLoopReturn
                tape := tapeAtCells left
                  (some bit ::
                    List.append (rest.map some) right) }) =
          { state := rawBoundaryChunkExpandLoopReturn
            tape :=
              tapeAtCells
                (List.append ((bit :: rest).reverse.map some) left)
                right }
      rw [rawBoundaryChunkExpandLoopDescription_step_return_bit]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: left)

private theorem rawBoundaryChunkExpandLoopDescription_step_return_separator
    (left right : List (Option Bool)) :
    rawBoundaryChunkExpandLoopDescription.runConfig 1
        { state := rawBoundaryChunkExpandLoopReturn
          tape := tapeAtCells left (none :: right) } =
      { state := rawBoundaryChunkExpandLoopScan
        tape := tapeAtCells (none :: left) right } := by
  cases right <;>
    simp [rawBoundaryChunkExpandLoopDescription,
      rawBoundaryChunkExpandLoopHalt,
      rawBoundaryChunkExpandLoopStart,
      rawBoundaryChunkExpandLoopScan,
      rawBoundaryChunkExpandLoopScanRest,
      rawBoundaryChunkExpandLoopEraseRightmost,
      rawBoundaryChunkExpandLoopCarryFalse,
      rawBoundaryChunkExpandLoopAnchorFalse,
      rawBoundaryChunkExpandLoopWriteFalse2,
      rawBoundaryChunkExpandLoopWriteFalse1,
      rawBoundaryChunkExpandLoopWriteFalse0,
      rawBoundaryChunkExpandLoopCarryTrue,
      rawBoundaryChunkExpandLoopAnchorTrue,
      rawBoundaryChunkExpandLoopWriteTrue2,
      rawBoundaryChunkExpandLoopWriteTrue1,
      rawBoundaryChunkExpandLoopWriteTrue0,
      rawBoundaryChunkExpandLoopReturn,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem rawBoundaryChunkExpandLoopDescription_run_anchor_write_return_false
    (emitted pref : Word Bool) (blankTail : Nat)
    (right : List (Option Bool)) :
    rawBoundaryChunkExpandLoopDescription.runConfig
        (2 * emitted.length + 8)
        { state := rawBoundaryChunkExpandLoopAnchorFalse
          tape :=
            rawBoundaryChunkExpandAnchorTape emitted.reverse
              (none ::
                List.append (pref.map some)
                  (none ::
                    List.append
                      (List.replicate (blankTail + 1)
                        (none : Option Bool))
                      right)) } =
      { state := rawBoundaryChunkExpandLoopScan
        tape :=
          rawBoundaryChunkExpandScanTape
            (List.append (rawBoundaryChunkExpandCellBits false) emitted)
            pref (blankTail + 1) right } := by
  rw [show 2 * emitted.length + 8 =
      emitted.reverse.length +
        (4 + ((List.append [true, false, true] emitted).length + 1)) by
    simp [List.length_reverse]
    lia]
  rw [MachineDescription.runConfig_add]
  change
    rawBoundaryChunkExpandLoopDescription.runConfig
        (4 + ((List.append [true, false, true] emitted).length + 1))
        (rawBoundaryChunkExpandLoopDescription.runConfig
          emitted.reverse.length
          { state := rawBoundaryChunkExpandAnchorState false
            tape :=
              rawBoundaryChunkExpandAnchorTape emitted.reverse
                (none ::
                  List.append (pref.map some)
                    (none ::
                      List.append
                        (List.replicate (blankTail + 1)
                          (none : Option Bool))
                        right)) }) =
      { state := rawBoundaryChunkExpandLoopScan
        tape :=
          rawBoundaryChunkExpandScanTape
            (List.append (rawBoundaryChunkExpandCellBits false) emitted)
            pref (blankTail + 1) right }
  rw [rawBoundaryChunkExpandLoopDescription_run_anchor_scan_left]
  simp [List.reverse_reverse, rawBoundaryChunkExpandAnchorState]
  rw [MachineDescription.runConfig_add]
  rw [rawBoundaryChunkExpandLoopDescription_run_anchor_write_false]
  rw [MachineDescription.runConfig_add]
  rw [show emitted.length + 1 + 1 + 1 =
      (List.append [true, false, true] emitted).length by
    simp]
  rw [show some true :: some false :: some true ::
        (List.map some emitted ++
          none ::
            (List.map some pref ++
              none ::
                (List.replicate (blankTail + 1) none ++ right))) =
      List.append
        ((List.append [true, false, true] emitted).map some)
        (none ::
          (List.map some pref ++
            none ::
              (List.replicate (blankTail + 1) none ++ right))) by
    simp]
  rw [rawBoundaryChunkExpandLoopDescription_run_return_scan_right]
  rw [rawBoundaryChunkExpandLoopDescription_step_return_separator]
  simp [rawBoundaryChunkExpandScanTape, rawBoundaryChunkExpandCellBits,
    pulledRawBitCellChunkBits, preservingCellPassZeroBits,
    List.map_reverse, List.map_append, List.append_assoc,
    List.replicate_succ]

private theorem rawBoundaryChunkExpandLoopDescription_run_anchor_write_return_true
    (emitted pref : Word Bool) (blankTail : Nat)
    (right : List (Option Bool)) :
    rawBoundaryChunkExpandLoopDescription.runConfig
        (2 * emitted.length + 8)
        { state := rawBoundaryChunkExpandLoopAnchorTrue
          tape :=
            rawBoundaryChunkExpandAnchorTape emitted.reverse
              (none ::
                List.append (pref.map some)
                  (none ::
                    List.append
                      (List.replicate (blankTail + 1)
                        (none : Option Bool))
                      right)) } =
      { state := rawBoundaryChunkExpandLoopScan
        tape :=
          rawBoundaryChunkExpandScanTape
            (List.append (rawBoundaryChunkExpandCellBits true) emitted)
            pref (blankTail + 1) right } := by
  rw [show 2 * emitted.length + 8 =
      emitted.reverse.length +
        (4 + ((List.append [true, true, false] emitted).length + 1)) by
    simp [List.length_reverse]
    lia]
  rw [MachineDescription.runConfig_add]
  change
    rawBoundaryChunkExpandLoopDescription.runConfig
        (4 + ((List.append [true, true, false] emitted).length + 1))
        (rawBoundaryChunkExpandLoopDescription.runConfig
          emitted.reverse.length
          { state := rawBoundaryChunkExpandAnchorState true
            tape :=
              rawBoundaryChunkExpandAnchorTape emitted.reverse
                (none ::
                  List.append (pref.map some)
                    (none ::
                      List.append
                        (List.replicate (blankTail + 1)
                          (none : Option Bool))
                        right)) }) =
      { state := rawBoundaryChunkExpandLoopScan
        tape :=
          rawBoundaryChunkExpandScanTape
            (List.append (rawBoundaryChunkExpandCellBits true) emitted)
            pref (blankTail + 1) right }
  rw [rawBoundaryChunkExpandLoopDescription_run_anchor_scan_left]
  simp [List.reverse_reverse, rawBoundaryChunkExpandAnchorState]
  rw [MachineDescription.runConfig_add]
  rw [rawBoundaryChunkExpandLoopDescription_run_anchor_write_true]
  rw [MachineDescription.runConfig_add]
  rw [show emitted.length + 1 + 1 + 1 =
      (List.append [true, true, false] emitted).length by
    simp]
  rw [show some true :: some true :: some false ::
        (List.map some emitted ++
          none ::
            (List.map some pref ++
              none ::
                (List.replicate (blankTail + 1) none ++ right))) =
      List.append
        ((List.append [true, true, false] emitted).map some)
        (none ::
          (List.map some pref ++
            none ::
              (List.replicate (blankTail + 1) none ++ right))) by
    simp]
  rw [rawBoundaryChunkExpandLoopDescription_run_return_scan_right]
  rw [rawBoundaryChunkExpandLoopDescription_step_return_separator]
  simp [rawBoundaryChunkExpandScanTape, rawBoundaryChunkExpandCellBits,
    pulledRawBitCellChunkBits, preservingCellPassOneBits,
    List.map_reverse, List.map_append, List.append_assoc,
    List.replicate_succ]

private theorem rawBoundaryChunkExpandLoopDescription_run_anchor_write_return
    (emitted pref : Word Bool) (rawBit : Bool) (blankTail : Nat)
    (right : List (Option Bool)) :
    rawBoundaryChunkExpandLoopDescription.runConfig
        (2 * emitted.length + 8)
        { state := rawBoundaryChunkExpandAnchorState rawBit
          tape :=
            rawBoundaryChunkExpandAnchorTape emitted.reverse
              (none ::
                List.append (pref.map some)
                  (none ::
                    List.append
                      (List.replicate (blankTail + 1)
                        (none : Option Bool))
                      right)) } =
      { state := rawBoundaryChunkExpandLoopScan
        tape :=
          rawBoundaryChunkExpandScanTape
            (List.append (rawBoundaryChunkExpandCellBits rawBit) emitted)
            pref (blankTail + 1) right } := by
  cases rawBit
  · simpa [rawBoundaryChunkExpandAnchorState] using
      rawBoundaryChunkExpandLoopDescription_run_anchor_write_return_false emitted pref blankTail right
  · simpa [rawBoundaryChunkExpandAnchorState] using
      rawBoundaryChunkExpandLoopDescription_run_anchor_write_return_true emitted pref blankTail right

theorem rawBoundaryChunkExpandLoopDescription_run_scan_cons_obligation
    (emitted pref : Word Bool) (rawBit : Bool) (blankTail : Nat)
    (right : List (Option Bool)) :
    exists steps : Nat,
      rawBoundaryChunkExpandLoopDescription.runConfig steps
          { state := rawBoundaryChunkExpandLoopScan
            tape :=
              rawBoundaryChunkExpandScanTape
                emitted (List.append pref [rawBit]) blankTail right } =
        { state := rawBoundaryChunkExpandLoopScan
          tape :=
            rawBoundaryChunkExpandScanTape
              (List.append (rawBoundaryChunkExpandCellBits rawBit) emitted)
              pref (blankTail + 1) right } := by
  refine ⟨2 * pref.length + 2 * emitted.length + 12, ?_⟩
  rw [show 2 * pref.length + 2 * emitted.length + 12 =
      (pref.length + 2) +
        (1 + ((pref.reverse.length + 1) +
          (2 * emitted.length + 8))) by
    simp [List.length_reverse]
    lia]
  rw [MachineDescription.runConfig_add]
  rw [rawBoundaryChunkExpandLoopDescription_run_scan_to_rightmost]
  rw [MachineDescription.runConfig_add]
  rw [rawBoundaryChunkExpandLoopDescription_step_eraseRightmost]
  rw [MachineDescription.runConfig_add]
  rw [rawBoundaryChunkExpandLoopDescription_run_carry_to_anchor]
  rw [show
      none ::
          List.append (pref.reverse.reverse.map some)
            (none ::
              List.append
                (List.replicate (blankTail + 1) (none : Option Bool))
                right) =
        none ::
          List.append (pref.map some)
            (none ::
              List.append
                (List.replicate (blankTail + 1) (none : Option Bool))
                right) by
    simp]
  rw [rawBoundaryChunkExpandLoopDescription_run_anchor_write_return]

private theorem rawBoundaryChunkExpandCellBits_append_singleton
    (pref : Word Bool) (rawBit : Bool) :
    preservingCellPassCellBits (List.append pref [rawBit]) =
      List.append (preservingCellPassCellBits pref)
        (rawBoundaryChunkExpandCellBits rawBit) := by
  induction pref with
  | nil =>
      cases rawBit <;>
        simp [rawBoundaryChunkExpandCellBits,
          pulledRawBitCellChunkBits, preservingCellPassCellBits,
          preservingCellPassZeroBits, preservingCellPassOneBits]
  | cons bit rest ih =>
      cases bit <;> cases rawBit
      all_goals
        simp [rawBoundaryChunkExpandCellBits,
          pulledRawBitCellChunkBits, preservingCellPassCellBits,
          preservingCellPassZeroBits, preservingCellPassOneBits] at ih ⊢
        rw [ih]

private theorem rawBoundaryChunkExpandLoopDescription_run_scan_halts
    (layout emitted : Word Bool) (blankTail : Nat)
    (right : List (Option Bool)) :
    exists steps : Nat,
      rawBoundaryChunkExpandLoopDescription.runConfig steps
          { state := rawBoundaryChunkExpandLoopScan
            tape :=
              rawBoundaryChunkExpandScanTape
                emitted layout blankTail right } =
        { state := rawBoundaryChunkExpandLoopHalt
          tape :=
            rawBoundaryChunkExpandSeparatorTape
              (List.append (preservingCellPassCellBits layout) emitted)
              [] (blankTail + layout.length) right } := by
  let motive : Nat -> Prop :=
    fun n =>
      forall (layout emitted : Word Bool) (blankTail : Nat)
        (right : List (Option Bool)),
        layout.length = n ->
          exists steps : Nat,
            rawBoundaryChunkExpandLoopDescription.runConfig steps
                { state := rawBoundaryChunkExpandLoopScan
                  tape :=
                    rawBoundaryChunkExpandScanTape
                      emitted layout blankTail right } =
              { state := rawBoundaryChunkExpandLoopHalt
                tape :=
                  rawBoundaryChunkExpandSeparatorTape
                    (List.append (preservingCellPassCellBits layout)
                      emitted)
                    [] (blankTail + layout.length) right }
  have hmain : motive layout.length := by
    induction layout.length using Nat.strongRecOn with
    | ind n ih =>
        intro current emitted blankTail right hlen
        cases current with
        | nil =>
            refine ⟨1, ?_⟩
            simpa [preservingCellPassCellBits] using
              rawBoundaryChunkExpandLoopDescription_run_done
                emitted blankTail right
        | cons head rest =>
            rcases
                FoC.Computability.list_exists_append_singleton_of_ne_nil
                  (head :: rest) (by simp) with
              ⟨pref, rawBit, hcurrent⟩
            rw [hcurrent] at hlen ⊢
            have hpref_len :
                pref.length < n := by
              simp [List.length_append] at hlen
              lia
            rcases
                rawBoundaryChunkExpandLoopDescription_run_scan_cons_obligation
                  emitted pref rawBit blankTail right with
              ⟨stepCount, hstep⟩
            have hrec :
                exists recSteps : Nat,
                  rawBoundaryChunkExpandLoopDescription.runConfig recSteps
                      { state := rawBoundaryChunkExpandLoopScan
                        tape :=
                          rawBoundaryChunkExpandScanTape
                            (List.append
                              (rawBoundaryChunkExpandCellBits rawBit)
                              emitted)
                            pref (blankTail + 1) right } =
                    { state := rawBoundaryChunkExpandLoopHalt
                      tape :=
                        rawBoundaryChunkExpandSeparatorTape
                          (List.append
                            (preservingCellPassCellBits pref)
                            (List.append
                              (rawBoundaryChunkExpandCellBits rawBit)
                              emitted))
                          [] (blankTail + 1 + pref.length) right } := by
              have hcall :=
                ih pref.length hpref_len pref
                  (List.append (rawBoundaryChunkExpandCellBits rawBit)
                    emitted)
                  (blankTail + 1) right rfl
              simpa [Nat.add_assoc] using hcall
            rcases hrec with ⟨recSteps, hrecRun⟩
            refine ⟨stepCount + recSteps, ?_⟩
            rw [MachineDescription.runConfig_add]
            rw [hstep]
            rw [hrecRun]
            have hbits :
                List.append
                    (preservingCellPassCellBits pref)
                    (List.append
                      (rawBoundaryChunkExpandCellBits rawBit) emitted) =
                  List.append
                    (preservingCellPassCellBits
                      (List.append pref [rawBit]))
                    emitted := by
              rw [rawBoundaryChunkExpandCellBits_append_singleton]
              simp [List.append_assoc]
            have hblank :
                blankTail + 1 + pref.length =
                  blankTail + (List.append pref [rawBit]).length := by
              simp [List.length_append]
              lia
            rw [hbits, hblank]
  exact hmain layout emitted blankTail right rfl

theorem rawBoundaryChunkExpandLoopDescription_haltsFrom_separator_obligation
    (layout emitted : Word Bool) (blankTail : Nat)
    (right : List (Option Bool)) :
    rawBoundaryChunkExpandLoopDescription.HaltsFromTape
      (rawBoundaryChunkExpandSeparatorTape
        emitted layout blankTail right)
      (rawBoundaryChunkExpandSeparatorTape
        (List.append (preservingCellPassCellBits layout) emitted)
        [] (blankTail + layout.length) right) := by
  rcases
      rawBoundaryChunkExpandLoopDescription_run_scan_halts
        layout emitted blankTail right with
    ⟨scanSteps, hscan⟩
  refine ⟨1 + scanSteps, ?_⟩
  dsimp [MachineDescription.HaltsFromTapeIn]
  rw [MachineDescription.runConfig_add]
  simpa [rawBoundaryChunkExpandLoopDescription,
    rawBoundaryChunkExpandLoopStart,
    rawBoundaryChunkExpandLoopHalt] using
    (show
      (rawBoundaryChunkExpandLoopDescription.runConfig scanSteps
          (rawBoundaryChunkExpandLoopDescription.runConfig 1
            { state := rawBoundaryChunkExpandLoopStart
              tape :=
                rawBoundaryChunkExpandSeparatorTape
                  emitted layout blankTail right })).state =
            rawBoundaryChunkExpandLoopHalt ∧
          (rawBoundaryChunkExpandLoopDescription.runConfig scanSteps
            (rawBoundaryChunkExpandLoopDescription.runConfig 1
              { state := rawBoundaryChunkExpandLoopStart
                tape :=
                  rawBoundaryChunkExpandSeparatorTape
                    emitted layout blankTail right })).tape =
            rawBoundaryChunkExpandSeparatorTape
              (List.append (preservingCellPassCellBits layout) emitted) []
              (blankTail + layout.length) right by
      rw [rawBoundaryChunkExpandLoopDescription_run_start]
      rw [hscan]
      constructor <;> rfl)

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
