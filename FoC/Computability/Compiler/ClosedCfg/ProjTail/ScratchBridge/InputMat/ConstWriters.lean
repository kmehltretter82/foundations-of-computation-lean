import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.Shapes

set_option doc.verso true

/-!
# Count-window input materializer constant writers

The constant middle-segment writer for the count-window structured input
materializer.  The guarded-blank scratch tape of the three-tape target is a
fixed eight-cell code block; this module provides the straight-line finite
machine that appends that block plus its trailing separator blank at the
current head position, moving right, together with its exact run lemmas.

Two entry shapes are proved: writing at the true right edge of the tape
(empty right stack) and writing over an explicit run of nine blank cells with
an arbitrary preserved suffix.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

open CanonicalLayouts.DovetailLayoutScanner

namespace InputMat

/--
Straight-line writer for the constant guarded-blank middle segment.  Starting
on a blank cell it writes the eight segment cells left to right, steps over
the following separator blank, and halts on the cell after the separator.
-/
def guardedBlankSegmentWriterDescription : MachineDescription where
  stateCount := 10
  start := 0
  halt := 9
  transitions :=
    [ transition 0 none (some false) Direction.right 1
    , transition 1 none (some false) Direction.right 2
    , transition 2 none (some true) Direction.right 3
    , transition 3 none (some true) Direction.right 4
    , transition 4 none (some false) Direction.right 5
    , transition 5 none (some false) Direction.right 6
    , transition 6 none (some false) Direction.right 7
    , transition 7 none (some false) Direction.right 8
    , transition 8 none none Direction.right 9 ]

theorem guardedBlankSegmentWriterDescription_wellFormed :
    guardedBlankSegmentWriterDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := guardedBlankSegmentWriterDescription.transitions)
      (stateCount := guardedBlankSegmentWriterDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := guardedBlankSegmentWriterDescription.transitions)
      (by decide)

theorem guardedBlankSegmentWriterDescription_haltTransitionFree :
    guardedBlankSegmentWriterDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := guardedBlankSegmentWriterDescription.transitions)
    (state := guardedBlankSegmentWriterDescription.halt)
    (by decide)

theorem guardedBlankSegmentWriterDescription_subroutineReady :
    guardedBlankSegmentWriterDescription.SubroutineReady :=
  ⟨guardedBlankSegmentWriterDescription_wellFormed,
    guardedBlankSegmentWriterDescription_haltTransitionFree⟩

/--
Right-edge run: from the blank head cell at the true right edge of the tape,
the writer emits the guarded-blank segment followed by its separator blank and
halts on the fresh blank right of the separator.
-/
theorem guardedBlankSegmentWriterDescription_run_rightEdge
    (leftRev : List (Option Bool)) :
    guardedBlankSegmentWriterDescription.runConfig 9
        { state := guardedBlankSegmentWriterDescription.start
          tape := tapeAtCells leftRev [] } =
      { state := guardedBlankSegmentWriterDescription.halt
        tape :=
          tapeAtCells
            (none ::
              List.append guardedBlankSegmentCells.reverse leftRev)
            [] } := by
  simp [guardedBlankSegmentWriterDescription, guardedBlankSegmentCells,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    Tape.read, Tape.write, Tape.move, Tape.moveRight, tapeAtCells]

/--
Blank-run run: from the first cell of an explicit nine-blank run, the writer
emits the guarded-blank segment followed by its separator blank and halts on
the first preserved suffix cell.
-/
theorem guardedBlankSegmentWriterDescription_run_blankRun
    (leftRev rest : List (Option Bool)) :
    guardedBlankSegmentWriterDescription.runConfig 9
        { state := guardedBlankSegmentWriterDescription.start
          tape :=
            tapeAtCells leftRev
              (List.append (List.replicate 9 (none : Option Bool)) rest) } =
      { state := guardedBlankSegmentWriterDescription.halt
        tape :=
          tapeAtCells
            (none ::
              List.append guardedBlankSegmentCells.reverse leftRev)
            rest } := by
  cases rest with
  | nil =>
      simp [guardedBlankSegmentWriterDescription, guardedBlankSegmentCells,
        runConfig, stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.write, Tape.move, Tape.moveRight, tapeAtCells,
        List.replicate]
  | cons cell restTail =>
      simp [guardedBlankSegmentWriterDescription, guardedBlankSegmentCells,
        runConfig, stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.write, Tape.move, Tape.moveRight, tapeAtCells,
        List.replicate]

theorem guardedBlankSegmentWriterDescription_haltsFromTape_rightEdge
    (leftRev : List (Option Bool)) :
    guardedBlankSegmentWriterDescription.HaltsFromTape
      (tapeAtCells leftRev [])
      (tapeAtCells
        (none :: List.append guardedBlankSegmentCells.reverse leftRev)
        []) := by
  refine ⟨9, ?_⟩
  constructor
  · rw [guardedBlankSegmentWriterDescription_run_rightEdge]
  · rw [guardedBlankSegmentWriterDescription_run_rightEdge]

theorem guardedBlankSegmentWriterDescription_haltsFromTape_blankRun
    (leftRev rest : List (Option Bool)) :
    guardedBlankSegmentWriterDescription.HaltsFromTape
      (tapeAtCells leftRev
        (List.append (List.replicate 9 (none : Option Bool)) rest))
      (tapeAtCells
        (none :: List.append guardedBlankSegmentCells.reverse leftRev)
        rest) := by
  refine ⟨9, ?_⟩
  constructor
  · rw [guardedBlankSegmentWriterDescription_run_blankRun]
  · rw [guardedBlankSegmentWriterDescription_run_blankRun]

end InputMat

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
