import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.ChunkExpandLoop
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.EndpointSupport

set_option doc.verso true

/-!
# Raw-boundary source-boundary entry glue

This module provides the three-state entry machine for the uniform raw-boundary
right-edge emitter.  Started on the boundary blank of the raw-boundary source
tape, it scans left across the raw layout bits to the left blank sentinel and
bounces one cell right, halting on the first raw bit (or back on the boundary
blank when the layout is empty).  A subsequent {lit}`Direction.left` subroutine
handoff then lands exactly on the chunk-expansion loop entry separator tape.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace CountWindowRawSourceEncoder
namespace RawBoundaryRightEdgeEmitter

def rawBoundarySourceBoundaryEntryHalt : Nat := 0

def rawBoundarySourceBoundaryEntryStart : Nat := 1

def rawBoundarySourceBoundaryEntryScanLeft : Nat := 2

def rawBoundarySourceBoundaryEntryDescription : MachineDescription where
  stateCount := 3
  start := rawBoundarySourceBoundaryEntryStart
  halt := rawBoundarySourceBoundaryEntryHalt
  transitions :=
    [ transition rawBoundarySourceBoundaryEntryStart
        none none Direction.left rawBoundarySourceBoundaryEntryScanLeft
    , transition rawBoundarySourceBoundaryEntryScanLeft
        (some false) (some false) Direction.left
        rawBoundarySourceBoundaryEntryScanLeft
    , transition rawBoundarySourceBoundaryEntryScanLeft
        (some true) (some true) Direction.left
        rawBoundarySourceBoundaryEntryScanLeft
    , transition rawBoundarySourceBoundaryEntryScanLeft
        none none Direction.right rawBoundarySourceBoundaryEntryHalt ]

theorem rawBoundarySourceBoundaryEntryDescription_wellFormed :
    rawBoundarySourceBoundaryEntryDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := rawBoundarySourceBoundaryEntryDescription.transitions)
      (stateCount := rawBoundarySourceBoundaryEntryDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := rawBoundarySourceBoundaryEntryDescription.transitions)
      (by decide)

theorem rawBoundarySourceBoundaryEntryDescription_haltTransitionFree :
    rawBoundarySourceBoundaryEntryDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := rawBoundarySourceBoundaryEntryDescription.transitions)
    (state := rawBoundarySourceBoundaryEntryDescription.halt)
    (by decide)

theorem rawBoundarySourceBoundaryEntryDescription_subroutineReady :
    rawBoundarySourceBoundaryEntryDescription.SubroutineReady :=
  ⟨rawBoundarySourceBoundaryEntryDescription_wellFormed,
    rawBoundarySourceBoundaryEntryDescription_haltTransitionFree⟩

/--
Halt view of the entry machine.  The blank sentinel is the sole explicit cell
left of the head; the head sits on the first raw layout bit, or on the original
boundary blank when the layout is empty.
-/
def rawBoundarySourceBoundaryEntryExitTape
    (skipped count : Word Bool) (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells [none]
    (List.append ((List.append skipped count).map some)
      (none ::
        none ::
        none ::
        List.append
          (List.replicate count.length (none : Option Bool))
          tail))

attribute [local simp]
  rawBoundarySourceBoundaryEntryDescription
  rawBoundarySourceBoundaryEntryHalt
  rawBoundarySourceBoundaryEntryStart
  rawBoundarySourceBoundaryEntryScanLeft

/--
Scan view between iterations.  The first argument lists the raw bits still to
be crossed, innermost (head) first; the head is on the first of them, or on the
blank sentinel when none remain.
-/
private def rawBoundarySourceBoundaryEntryScanTape :
    Word Bool -> List (Option Bool) -> Tape Bool
  | [], right => tapeAtCells [] (none :: right)
  | bit :: rest, right =>
      tapeAtCells (List.append (rest.map some) [none]) (some bit :: right)

private theorem rawBoundarySourceBoundaryEntryDescription_step_start
    (bitsRev : Word Bool) (right : List (Option Bool)) :
    rawBoundarySourceBoundaryEntryDescription.runConfig 1
        { state := rawBoundarySourceBoundaryEntryStart
          tape :=
            tapeAtCells (List.append (bitsRev.map some) [none])
              (none :: right) } =
      { state := rawBoundarySourceBoundaryEntryScanLeft
        tape :=
          rawBoundarySourceBoundaryEntryScanTape bitsRev
            (none :: right) } := by
  cases bitsRev with
  | nil =>
      simp [rawBoundarySourceBoundaryEntryScanTape, runConfig, stepConfig,
        lookupTransition, Matches, transition, tapeAtCells, Tape.read,
        Tape.write, Tape.move, Tape.moveLeft]
  | cons bit rest =>
      cases bit <;>
        simp [rawBoundarySourceBoundaryEntryScanTape, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells, Tape.read,
          Tape.write, Tape.move, Tape.moveLeft]

private theorem rawBoundarySourceBoundaryEntryDescription_step_scanLeft_bit
    (bit : Bool) (rest : Word Bool) (right : List (Option Bool)) :
    rawBoundarySourceBoundaryEntryDescription.runConfig 1
        { state := rawBoundarySourceBoundaryEntryScanLeft
          tape :=
            rawBoundarySourceBoundaryEntryScanTape (bit :: rest) right } =
      { state := rawBoundarySourceBoundaryEntryScanLeft
        tape :=
          rawBoundarySourceBoundaryEntryScanTape rest
            (some bit :: right) } := by
  cases bit <;> cases rest <;> cases right <;>
    simp [rawBoundarySourceBoundaryEntryScanTape, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft]

private theorem rawBoundarySourceBoundaryEntryDescription_run_scanLeft
    (remainingRev : Word Bool) (right : List (Option Bool)) :
    rawBoundarySourceBoundaryEntryDescription.runConfig
        remainingRev.length
        { state := rawBoundarySourceBoundaryEntryScanLeft
          tape :=
            rawBoundarySourceBoundaryEntryScanTape remainingRev right } =
      { state := rawBoundarySourceBoundaryEntryScanLeft
        tape :=
          tapeAtCells []
            (none ::
              List.append (remainingRev.reverse.map some) right) } := by
  induction remainingRev generalizing right with
  | nil =>
      simp [rawBoundarySourceBoundaryEntryScanTape, runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      rw [rawBoundarySourceBoundaryEntryDescription_step_scanLeft_bit]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: right)

private theorem rawBoundarySourceBoundaryEntryDescription_step_scanLeft_sentinel
    (right : List (Option Bool)) :
    rawBoundarySourceBoundaryEntryDescription.runConfig 1
        { state := rawBoundarySourceBoundaryEntryScanLeft
          tape := tapeAtCells [] (none :: right) } =
      { state := rawBoundarySourceBoundaryEntryHalt
        tape := tapeAtCells [none] right } := by
  cases right <;>
    simp [runConfig, stepConfig, lookupTransition, Matches, transition,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem rawBoundarySourceBoundaryEntryDescription_run_full
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    rawBoundarySourceBoundaryEntryDescription.runConfig
        (1 + ((List.append skipped count).reverse.length + 1))
        { state := rawBoundarySourceBoundaryEntryStart
          tape := sourceTape skipped count tail } =
      { state := rawBoundarySourceBoundaryEntryHalt
        tape :=
          rawBoundarySourceBoundaryEntryExitTape skipped count tail } := by
  rw [show sourceTape skipped count tail =
      tapeAtCells
        (List.append
          (((List.append skipped count).reverse).map some) [none])
        (none ::
          (none ::
            none ::
            List.append
              (List.replicate count.length (none : Option Bool))
              tail)) from rfl]
  rw [MachineDescription.runConfig_add]
  rw [rawBoundarySourceBoundaryEntryDescription_step_start]
  rw [MachineDescription.runConfig_add]
  rw [rawBoundarySourceBoundaryEntryDescription_run_scanLeft]
  rw [rawBoundarySourceBoundaryEntryDescription_step_scanLeft_sentinel]
  simp [rawBoundarySourceBoundaryEntryExitTape]

/--
Start-to-halt statement for the entry glue: from the boundary blank of the
source tape the machine halts exactly on
{name}`rawBoundarySourceBoundaryEntryExitTape`.
-/
theorem rawBoundarySourceBoundaryEntryDescription_haltsFrom_sourceTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    rawBoundarySourceBoundaryEntryDescription.HaltsFromTape
      (sourceTape skipped count tail)
      (rawBoundarySourceBoundaryEntryExitTape skipped count tail) := by
  refine ⟨1 + ((List.append skipped count).reverse.length + 1), ?_⟩
  show
    (rawBoundarySourceBoundaryEntryDescription.runConfig
        (1 + ((List.append skipped count).reverse.length + 1))
        { state := rawBoundarySourceBoundaryEntryStart
          tape := sourceTape skipped count tail }).state =
      rawBoundarySourceBoundaryEntryHalt ∧
    (rawBoundarySourceBoundaryEntryDescription.runConfig
        (1 + ((List.append skipped count).reverse.length + 1))
        { state := rawBoundarySourceBoundaryEntryStart
          tape := sourceTape skipped count tail }).tape =
      rawBoundarySourceBoundaryEntryExitTape skipped count tail
  rw [rawBoundarySourceBoundaryEntryDescription_run_full]
  exact ⟨rfl, rfl⟩

private theorem rawBoundarySourceBoundaryEntry_replicate_reshape
    (n : Nat) :
    List.replicate (n + 2 + 1) (none : Option Bool) =
      none :: none :: none :: List.replicate n (none : Option Bool) := by
  rw [show n + 2 + 1 = n + 1 + 1 + 1 by lia]
  simp [List.replicate_succ]

private theorem rawBoundarySourceBoundaryEntry_move_left_general
    (bits : Word Bool) (blanks : Nat) (suffix : List (Option Bool)) :
    Tape.move Direction.left
        (tapeAtCells [none]
          (List.append (bits.map some)
            (none ::
              none ::
              none ::
              List.append
                (List.replicate blanks (none : Option Bool))
                suffix))) =
      tapeAtCells []
        (none ::
          List.append (bits.map some)
            (List.append
              (List.replicate (blanks + 2 + 1) (none : Option Bool))
              suffix)) := by
  cases bits with
  | nil =>
      simp [tapeAtCells, Tape.move, Tape.moveLeft,
        rawBoundarySourceBoundaryEntry_replicate_reshape]
  | cons bit rest =>
      simp [tapeAtCells, Tape.move, Tape.moveLeft,
        rawBoundarySourceBoundaryEntry_replicate_reshape]

/--
Seam bridge for the {lit}`Direction.left` subroutine handoff.  One left move
from the entry exit tape lands exactly on the chunk-expansion loop entry with
the whole raw layout unconsumed, blank tail {lit}`count.length + 2`, and the
untouched live suffix {lit}`some tailFirst :: tail`.
-/
theorem rawBoundarySourceBoundaryEntryExitTape_move_left
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.left
        (rawBoundarySourceBoundaryEntryExitTape skipped count
          (some tailFirst :: tail)) =
      rawBoundaryChunkExpandSeparatorTape []
        (List.append skipped count) (count.length + 2)
        (some tailFirst :: tail) := by
  have h :=
    rawBoundarySourceBoundaryEntry_move_left_general
      (List.append skipped count) count.length (some tailFirst :: tail)
  simpa [rawBoundarySourceBoundaryEntryExitTape,
    rawBoundaryChunkExpandSeparatorTape] using h

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
