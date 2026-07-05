import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.ThreeTapeHelpers
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.ThreeTapeTactic
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.TailedThreeTapeDebug

set_option doc.verso true

/-!
# Raw three-tape tail insertion

This module provides a small lowerer-facing three-logical-tape component for
raw bit layouts with an explicit cursor boundary.  The source tape starts at the
boundary after an already-emitted prefix, its right side contains a live tail
followed by a blank separator and an insert payload, scratch contains the same
insert payload, and work starts blank.  The component rewrites the source
payload order from {lit}`prefix ++ tail ++ insert` to
{lit}`prefix ++ insert ++ tail`.

The contract intentionally keeps the prefix/tail boundary explicit.  Without
that cursor or a delimiter before the tail, the raw layout is ambiguous for the
live-tail joiner target.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering
namespace ThreeTape

namespace RawTailInsertion

def copyTail : Nat := 0
def rewindTailEntry : Nat := 1
def rewindTailLoop : Nat := 2
def rewindScratchEntry : Nat := 3
def rewindScratchLoop : Nat := 4
def writeInsert : Nat := 5
def restoreTail : Nat := 6
def halt : Nat := 7

def stateCount : Nat := 8

/-- Source tape for the explicit-boundary raw tail insertion contract. -/
def sourceTape
    (pref tail insert : Word Bool) : Tape Bool :=
  tapeAtCells (pref.reverse.map some)
    (List.append (tail.map some)
      (none :: List.append (insert.map some) [none]))

/-- Source tape after the tail has been erased in place. -/
def erasedTailSourceTape
    (pref tail insert : Word Bool) : Tape Bool :=
  tapeAtCells
    (List.append (List.replicate tail.length (none : Option Bool))
      (pref.reverse.map some))
    (none :: List.append (insert.map some) [none])

/--
Source tape at the insertion boundary after the erased tail cells have been
rewound.  The head is on the first erased tail cell.
-/
def insertionBoundarySourceTape
    (pref tail insert : Word Bool) : Tape Bool :=
  tapeAtCells (pref.reverse.map some)
    (List.append (List.replicate tail.length (none : Option Bool))
      (none :: List.append (insert.map some) [none]))

/-- Source tape after writing {lit}`insert` and restoring {lit}`tail`, parked past tail. -/
def restoredSourceTape
    (pref tail insert : Word Bool) : Tape Bool :=
  tapeAtCells
    (none ::
      List.append (List.append (tail.reverse.map some) (insert.reverse.map some))
        (pref.reverse.map some))
    [none]

def scratchTape (insert : Word Bool) : Tape Bool :=
  outputFromBits insert

def workTape (tail : Word Bool) : Tape Bool :=
  outputFromBits tail

def finalScratchTape (insert : Word Bool) : Tape Bool :=
  tapeAtCells
    (List.append (insert.reverse.map some) [none])
    [none]

def finalWorkTape (tail : Word Bool) : Tape Bool :=
  tapeAtCells
    (List.replicate (tail.length + 1) (none : Option Bool))
    [none]

def initialConfig
    (pref tail insert : Word Bool) : Configuration :=
  config copyTail
    (sourceTape pref tail insert)
    (scratchTape insert)
    (outputFromBits [])

def finalConfig
    (pref tail insert : Word Bool) : Configuration :=
  config halt
    (restoredSourceTape pref tail insert)
    (finalScratchTape insert)
    (finalWorkTape tail)

def rowsForSourceRead
    (source : Nat) (sourceRead : Option Bool)
    (action0 action1 action2 : TapeAction)
    (target : Nat) : List Transition :=
  allReads2
    (fun read1 read2 =>
      row source sourceRead read1 read2
        action0 action1 action2 target)

def rowsForScratchRead
    (source : Nat) (scratchRead : Option Bool)
    (action0 action1 action2 : TapeAction)
    (target : Nat) : List Transition :=
  allReads2
    (fun read0 read2 =>
      row source read0 scratchRead read2
        action0 action1 action2 target)

def rowsForWorkRead
    (source : Nat) (workRead : Option Bool)
    (action0 action1 action2 : TapeAction)
    (target : Nat) : List Transition :=
  allReads2
    (fun read0 read1 =>
      row source read0 read1 workRead
        action0 action1 action2 target)

def rows : List Transition :=
  [ rowsForSourceRead copyTail (some false)
      eraseR keepS (writeBitR false) copyTail
  , rowsForSourceRead copyTail (some true)
      eraseR keepS (writeBitR true) copyTail
  , rowsForSourceRead copyTail none
      keepS keepS keepS rewindTailEntry
  , allReadRows3 rewindTailEntry rewindTailLoop
      keepL keepS keepL
  , rowsForWorkRead rewindTailLoop (some false)
      keepL keepS keepL rewindTailLoop
  , rowsForWorkRead rewindTailLoop (some true)
      keepL keepS keepL rewindTailLoop
  , rowsForWorkRead rewindTailLoop none
      keepR keepS keepR rewindScratchEntry
  , allReadRows3 rewindScratchEntry rewindScratchLoop
      keepS keepL keepS
  , rowsForScratchRead rewindScratchLoop (some false)
      keepS keepL keepS rewindScratchLoop
  , rowsForScratchRead rewindScratchLoop (some true)
      keepS keepL keepS rewindScratchLoop
  , rowsForScratchRead rewindScratchLoop none
      keepS keepR keepS writeInsert
  , rowsForScratchRead writeInsert (some false)
      (writeBitR false) keepR keepS writeInsert
  , rowsForScratchRead writeInsert (some true)
      (writeBitR true) keepR keepS writeInsert
  , rowsForScratchRead writeInsert none
      keepS keepS keepS restoreTail
  , rowsForWorkRead restoreTail (some false)
      (writeBitR false) keepS eraseR restoreTail
  , rowsForWorkRead restoreTail (some true)
      (writeBitR true) keepS eraseR restoreTail
  , rowsForWorkRead restoreTail none
      eraseR keepS keepS halt ].flatten

def description : Description :=
  ThreeTape.description stateCount copyTail halt rows

theorem rowsForSourceRead_supportsReadWriteRow3
    (source : Nat) (sourceRead : Option Bool)
    (action0 action1 action2 : TapeAction)
    (target : Nat) :
    forall row' : Transition,
      row' ∈ rowsForSourceRead
          source sourceRead action0 action1 action2 target ->
        supportsReadWriteRow3 row' = true := by
  intro row' hrow
  simp [rowsForSourceRead, allReads2] at hrow
  rcases hrow with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact row_supportsReadWriteRow3 _ _ _ _ _ _ _ _

theorem rowsForScratchRead_supportsReadWriteRow3
    (source : Nat) (scratchRead : Option Bool)
    (action0 action1 action2 : TapeAction)
    (target : Nat) :
    forall row' : Transition,
      row' ∈ rowsForScratchRead
          source scratchRead action0 action1 action2 target ->
        supportsReadWriteRow3 row' = true := by
  intro row' hrow
  simp [rowsForScratchRead, allReads2] at hrow
  rcases hrow with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact row_supportsReadWriteRow3 _ _ _ _ _ _ _ _

theorem rowsForWorkRead_supportsReadWriteRow3
    (source : Nat) (workRead : Option Bool)
    (action0 action1 action2 : TapeAction)
    (target : Nat) :
    forall row' : Transition,
      row' ∈ rowsForWorkRead
          source workRead action0 action1 action2 target ->
        supportsReadWriteRow3 row' = true := by
  intro row' hrow
  simp [rowsForWorkRead, allReads2] at hrow
  rcases hrow with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact row_supportsReadWriteRow3 _ _ _ _ _ _ _ _

theorem rows_supportsReadWriteRow3 :
    forall row' : Transition,
      row' ∈ rows ->
        supportsReadWriteRow3 row' = true := by
  intro row' hrow
  simp [rows] at hrow
  rcases hrow with
    hrow | hrow | hrow | hrow | hrow | hrow | hrow | hrow |
    hrow | hrow | hrow | hrow | hrow | hrow | hrow | hrow
  · exact rowsForSourceRead_supportsReadWriteRow3
      copyTail (some false) eraseR keepS (writeBitR false)
      copyTail row' hrow
  · exact rowsForSourceRead_supportsReadWriteRow3
      copyTail (some true) eraseR keepS (writeBitR true)
      copyTail row' hrow
  · exact rowsForSourceRead_supportsReadWriteRow3
      copyTail none keepS keepS keepS rewindTailEntry row' hrow
  · exact allReadRows3_supportsReadWriteRow3
      rewindTailEntry rewindTailLoop keepL keepS keepL row' hrow
  · exact rowsForWorkRead_supportsReadWriteRow3
      rewindTailLoop (some false) keepL keepS keepL rewindTailLoop row' hrow
  · exact rowsForWorkRead_supportsReadWriteRow3
      rewindTailLoop (some true) keepL keepS keepL rewindTailLoop row' hrow
  · exact rowsForWorkRead_supportsReadWriteRow3
      rewindTailLoop none keepR keepS keepR rewindScratchEntry row' hrow
  · exact allReadRows3_supportsReadWriteRow3
      rewindScratchEntry rewindScratchLoop keepS keepL keepS row' hrow
  · exact rowsForScratchRead_supportsReadWriteRow3
      rewindScratchLoop (some false) keepS keepL keepS rewindScratchLoop
      row' hrow
  · exact rowsForScratchRead_supportsReadWriteRow3
      rewindScratchLoop (some true) keepS keepL keepS rewindScratchLoop
      row' hrow
  · exact rowsForScratchRead_supportsReadWriteRow3
      rewindScratchLoop none keepS keepR keepS writeInsert row' hrow
  · exact rowsForScratchRead_supportsReadWriteRow3
      writeInsert (some false) (writeBitR false) keepR keepS writeInsert
      row' hrow
  · exact rowsForScratchRead_supportsReadWriteRow3
      writeInsert (some true) (writeBitR true) keepR keepS writeInsert
      row' hrow
  · exact rowsForScratchRead_supportsReadWriteRow3
      writeInsert none keepS keepS keepS restoreTail row' hrow
  · exact rowsForWorkRead_supportsReadWriteRow3
      restoreTail (some false) (writeBitR false) keepS eraseR restoreTail
      row' hrow
  · rcases hrow with hrow | hrow
    · exact rowsForWorkRead_supportsReadWriteRow3
        restoreTail (some true) (writeBitR true) keepS eraseR restoreTail
        row' hrow
    · exact rowsForWorkRead_supportsReadWriteRow3
        restoreTail none eraseR keepS keepS halt row' hrow

theorem description_supported :
    SupportsReadWriteRows3 description :=
  ThreeTape.description_supported stateCount copyTail halt rows
    rows_supportsReadWriteRow3

theorem description_supportsReadWriteRows3 :
    supportsReadWriteRows3 description = true :=
  supportsReadWriteRows3_eq_true_of_supported description_supported

def runFuel (tail insert : Word Bool) : Nat :=
  3 * tail.length + 2 * insert.length + 7

theorem replicate_none_append_cons_none
    (n : Nat) (baseLeft : List (Option Bool)) :
    List.replicate n (none : Option Bool) ++ none :: baseLeft =
      none :: (List.replicate n (none : Option Bool) ++ baseLeft) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

theorem copyTail_step_bit
    (baseLeft : List (Option Bool)) (bit : Bool)
    (remaining insert copied : Word Bool) :
    description.runConfig 1
        (config copyTail
          (tapeAtCells baseLeft
            (some bit :: List.append (remaining.map some)
              (none :: List.append (insert.map some) [none])))
          (scratchTape insert)
          (outputFromBits copied)) =
      config copyTail
        (tapeAtCells (none :: baseLeft)
          (List.append (remaining.map some)
            (none :: List.append (insert.map some) [none])))
        (scratchTape insert)
        (outputFromBits (List.append copied [bit])) := by
  cases bit <;>
    simp [description, ThreeTape.description, rows, rowsForSourceRead,
      rowsForScratchRead, rowsForWorkRead, allReads2, allReadRows3,
      allReads3, Structured.Description.runConfig,
      Structured.Description.stepConfig,
      Structured.Description.lookupTransition,
      config, row, eraseR, writeBitR, keepS,
      Tape.read, tapeAtCells, outputFromBits]
  all_goals
    cases h :
      List.map some remaining ++
        none :: (List.map some insert ++ [none]) <;> rfl

theorem copyTail_step_blank
    (baseLeft : List (Option Bool)) (insert copied : Word Bool) :
    description.runConfig 1
        (config copyTail
          (tapeAtCells baseLeft
            (none :: List.append (insert.map some) [none]))
          (scratchTape insert)
          (outputFromBits copied)) =
      config rewindTailEntry
        (tapeAtCells baseLeft
          (none :: List.append (insert.map some) [none]))
        (scratchTape insert)
        (outputFromBits copied) := by
  simp [description, ThreeTape.description, rows, rowsForSourceRead,
    rowsForScratchRead, rowsForWorkRead, allReads2, allReadRows3,
    allReads3, Structured.Description.runConfig,
    Structured.Description.stepConfig,
    Structured.Description.lookupTransition,
    Structured.Description.Matches, List.find?,
    config, row, keepS, Structured.TapeAction.apply,
    Structured.TapeAction.stay, Structured.HeadMove.apply,
    Tape.read, tapeAtCells, outputFromBits, scratchTape]

theorem copyTail_run_loop
    (remaining copied insert : Word Bool)
    (baseLeft : List (Option Bool)) :
    description.runConfig (remaining.length + 1)
        (config copyTail
          (tapeAtCells baseLeft
            (List.append (remaining.map some)
              (none :: List.append (insert.map some) [none])))
          (scratchTape insert)
          (outputFromBits copied)) =
      config rewindTailEntry
        (tapeAtCells
          (List.append
            (List.replicate remaining.length (none : Option Bool))
            baseLeft)
          (none :: List.append (insert.map some) [none]))
        (scratchTape insert)
        (outputFromBits (List.append copied remaining)) := by
  induction remaining generalizing baseLeft copied with
  | nil =>
      simpa using copyTail_step_blank baseLeft insert copied
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 = 1 + (rest.length + 1) by
        simp [Nat.add_comm, Nat.add_left_comm]]
      rw [Structured.Description.runConfig_add]
      rw [show
        List.append (List.map some (bit :: rest))
            (none :: List.append (insert.map some) [none]) =
          some bit :: List.append (List.map some rest)
            (none :: List.append (insert.map some) [none]) by
        rfl]
      rw [copyTail_step_bit]
      rw [ih (List.append copied [bit]) (none :: baseLeft)]
      simp [List.append_assoc, replicate_none_append_cons_none,
        List.replicate_succ]

theorem copyTail_run
    (pref tail insert : Word Bool) :
    description.runConfig (tail.length + 1)
        (initialConfig pref tail insert) =
      config rewindTailEntry
        (erasedTailSourceTape pref tail insert)
        (scratchTape insert)
        (outputFromBits tail) := by
  simpa [initialConfig, sourceTape, erasedTailSourceTape] using
    copyTail_run_loop tail [] insert (pref.reverse.map some)

theorem restoredSourceTape_normalizedOutput
    (pref tail insert : Word Bool) :
    Tape.normalizedOutput (restoredSourceTape pref tail insert) =
      List.append pref (List.append insert tail) := by
  simp [restoredSourceTape, tapeAtCells_normalizedOutput,
    List.filterMap_append, List.map_reverse,
    List.append_assoc, Function.comp_def]

theorem finalConfig_source_normalizedOutput
    (pref tail insert : Word Bool) :
    Tape.normalizedOutput
        (Description.tapeAt (finalConfig pref tail insert).tapes 0) =
      List.append pref (List.append insert tail) := by
  simpa [finalConfig] using
    restoredSourceTape_normalizedOutput pref tail insert

theorem finalConfig_work_normalizedOutput
    (pref tail insert : Word Bool) :
    Tape.normalizedOutput
        (Description.tapeAt (finalConfig pref tail insert).tapes 2) =
      [] := by
  change
    Tape.normalizedOutput
        (tapeAtCells
          (List.replicate (tail.length + 1) (none : Option Bool))
          [none]) = []
  simp [tapeAtCells_normalizedOutput]

def debugSamplePrefix : Word Bool := [true, false]
def debugSampleTail : Word Bool := [false, true, true]
def debugSampleInsert : Word Bool := [true, true, false]

def debugSampleInitial : Configuration :=
  initialConfig debugSamplePrefix debugSampleTail debugSampleInsert

def debugSampleExpected : TailedSourceExpectation where
  expectedState? := some halt
  expectedSourceHeadRightBits? := some []
  expectedScratchExact? := some (finalScratchTape debugSampleInsert)
  expectedWorkExact? := some (finalWorkTape debugSampleTail)

def debugSampleFinalReport (fuel : Nat) : String :=
  debugFinalTailedReport description fuel debugSampleInitial
    debugSampleExpected

theorem debugSample_run :
    description.runConfig
        (runFuel debugSampleTail debugSampleInsert)
        debugSampleInitial =
      finalConfig debugSamplePrefix debugSampleTail debugSampleInsert := by
  decide

theorem debugSampleFinal_normalizedOutput_contract :
    Tape.normalizedOutput
        (Description.tapeAt
          (finalConfig debugSamplePrefix debugSampleTail debugSampleInsert).tapes
          0) =
      List.append debugSamplePrefix
        (List.append debugSampleInsert debugSampleTail) := by
  change
    Tape.normalizedOutput
        (Description.tapeAt
          (finalConfig debugSamplePrefix debugSampleTail debugSampleInsert).tapes
          0) =
      List.append debugSamplePrefix
        (List.append debugSampleInsert debugSampleTail)
  decide

end RawTailInsertion

end ThreeTape
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
