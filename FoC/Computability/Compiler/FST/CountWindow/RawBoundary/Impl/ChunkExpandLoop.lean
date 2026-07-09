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
  sorry

theorem rawBoundaryChunkExpandLoopDescription_haltsFrom_separator_obligation
    (layout emitted : Word Bool) (blankTail : Nat)
    (right : List (Option Bool)) :
    rawBoundaryChunkExpandLoopDescription.HaltsFromTape
      (rawBoundaryChunkExpandSeparatorTape
        emitted layout blankTail right)
      (rawBoundaryChunkExpandSeparatorTape
        (List.append (preservingCellPassCellBits layout) emitted)
        [] (blankTail + layout.length) right) := by
  sorry

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
