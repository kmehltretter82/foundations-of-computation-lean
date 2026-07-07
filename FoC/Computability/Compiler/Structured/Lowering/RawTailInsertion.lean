import FoC.Computability.Compiler.Structured.Lowering.ThreeTapeHelpers
import FoC.Computability.Compiler.Structured.Lowering.ThreeTapeTactic
import FoC.Computability.Compiler.Structured.Lowering.TailedThreeTapeDebug

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

def copyTailHandoffConfig
    (pref tail insert : Word Bool) : Configuration :=
  config rewindTailEntry
    (erasedTailSourceTape pref tail insert)
    (scratchTape insert)
    (outputFromBits tail)

def CopyTailSpec (D : Description) : Prop :=
  SupportsReadWriteRows3 D ∧
    forall (pref tail insert : Word Bool),
      D.runConfig (tail.length + 1)
          (initialConfig pref tail insert) =
        copyTailHandoffConfig pref tail insert

theorem CopyTailSpec.supported
    {D : Description} (hD : CopyTailSpec D) :
    SupportsReadWriteRows3 D :=
  hD.left

theorem CopyTailSpec.run
    {D : Description} (hD : CopyTailSpec D)
    (pref tail insert : Word Bool) :
    D.runConfig (tail.length + 1)
        (initialConfig pref tail insert) =
      copyTailHandoffConfig pref tail insert :=
  hD.right pref tail insert

theorem description_copyTailSpec :
    CopyTailSpec description := by
  refine ⟨description_supported, ?_⟩
  intro pref tail insert
  simpa [copyTailHandoffConfig] using
    copyTail_run pref tail insert

def rewindTailRightCells
    (processed insert : Word Bool) : List (Option Bool) :=
  List.append (List.replicate processed.length (none : Option Bool))
    (none :: List.append (insert.map some) [none])

def rewindTailLoopSourceTapeFromLeft
    (leftBoundary : List (Option Bool))
    (remainingRev processed insert : Word Bool) : Tape Bool :=
  match remainingRev with
  | [] =>
      match leftBoundary with
      | [] =>
          tapeAtCells []
            (none :: rewindTailRightCells processed insert)
      | cell :: rest =>
          tapeAtCells rest
            (cell :: rewindTailRightCells processed insert)
  | _ :: rest =>
      tapeAtCells
        (List.append
          (List.replicate rest.length (none : Option Bool))
          leftBoundary)
        (none :: rewindTailRightCells processed insert)

def rewindTailLoopWorkTape
    (remainingRev processed : Word Bool) : Tape Bool :=
  match remainingRev with
  | [] =>
      tapeAtCells []
        (none :: List.append (processed.map some) [none])
  | bit :: rest =>
      tapeAtCells (rest.map some)
        (some bit :: List.append (processed.map some) [none])

def rewindTailHandoffSourceTapeFromLeft
    (leftBoundary : List (Option Bool))
    (tail insert : Word Bool) : Tape Bool :=
  tapeAtCells
    (match leftBoundary with
    | [] => [none]
    | _ => leftBoundary)
    (rewindTailRightCells tail insert)

def rewindTailHandoffWorkTape
    (tail : Word Bool) : Tape Bool :=
  tapeAtCells [none]
    (List.append (tail.map some) [none])

def rewindTailHandoffSourceTape
    (pref tail insert : Word Bool) : Tape Bool :=
  rewindTailHandoffSourceTapeFromLeft
    (pref.reverse.map some) tail insert

def rewindTailHandoffConfig
    (pref tail insert : Word Bool) : Configuration :=
  config rewindScratchEntry
    (rewindTailHandoffSourceTape pref tail insert)
    (scratchTape insert)
    (rewindTailHandoffWorkTape tail)

def rewindScratchLoopScratchTape
    (remainingRev processed : Word Bool) : Tape Bool :=
  match remainingRev with
  | [] =>
      tapeAtCells []
        (none :: List.append (processed.map some) [none])
  | bit :: rest =>
      tapeAtCells (rest.map some)
        (some bit :: List.append (processed.map some) [none])

def writeInsertScratchTape
    (insert : Word Bool) : Tape Bool :=
  tapeAtCells [none]
    (List.append (insert.map some) [none])

def rewindScratchHandoffConfig
    (pref tail insert : Word Bool) : Configuration :=
  config writeInsert
    (rewindTailHandoffSourceTape pref tail insert)
    (writeInsertScratchTape insert)
    (rewindTailHandoffWorkTape tail)

def writeInsertSourceTapeFromLeft
    (leftBoundary : List (Option Bool))
    (written : Word Bool)
    (rightCells : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (written.reverse.map some)
      (match leftBoundary with
      | [] => [none]
      | _ => leftBoundary))
    rightCells

def writeInsertLoopScratchTape
    (written remaining : Word Bool) : Tape Bool :=
  tapeAtCells
    (List.append (written.reverse.map some) [none])
    (List.append (remaining.map some) [none])

def writeInsertHandoffRightCells
    (tail insert : Word Bool) : List (Option Bool) :=
  (rewindTailRightCells tail insert).drop insert.length

def writeInsertHandoffSourceTapeFromLeft
    (leftBoundary : List (Option Bool))
    (tail insert : Word Bool) : Tape Bool :=
  writeInsertSourceTapeFromLeft leftBoundary insert
    (writeInsertHandoffRightCells tail insert)

def writeInsertHandoffSourceTape
    (pref tail insert : Word Bool) : Tape Bool :=
  writeInsertHandoffSourceTapeFromLeft
    (pref.reverse.map some) tail insert

def writeInsertHandoffConfig
    (pref tail insert : Word Bool) : Configuration :=
  config restoreTail
    (writeInsertHandoffSourceTape pref tail insert)
    (finalScratchTape insert)
    (rewindTailHandoffWorkTape tail)

def restoreTailLoopSourceTapeFromLeft
    (leftBoundary : List (Option Bool))
    (insert restored : Word Bool)
    (rightCells : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (restored.reverse.map some)
      (List.append (insert.reverse.map some)
        (match leftBoundary with
        | [] => [none]
        | _ => leftBoundary)))
    rightCells

def restoreTailLoopWorkTape
    (remaining restored : Word Bool) : Tape Bool :=
  tapeAtCells
    (List.replicate (restored.length + 1) (none : Option Bool))
    (List.append (remaining.map some) [none])

def restoreTailCleanupCell
    (insert : Word Bool) : Option Bool :=
  match insert.reverse with
  | [] => none
  | bit :: _ => some bit

def restoreTailHandoffSourceTapeFromLeft
    (leftBoundary : List (Option Bool))
    (tail insert : Word Bool) : Tape Bool :=
  tapeAtCells
    (none ::
      List.append (tail.reverse.map some)
        (List.append (insert.reverse.map some)
          (match leftBoundary with
          | [] => [none]
          | _ => leftBoundary)))
    [none]

def restoreTailHandoffSourceTape
    (pref tail insert : Word Bool) : Tape Bool :=
  restoreTailHandoffSourceTapeFromLeft
    (pref.reverse.map some) tail insert

def restoreTailHandoffConfig
    (pref tail insert : Word Bool) : Configuration :=
  config halt
    (restoreTailHandoffSourceTape pref tail insert)
    (finalScratchTape insert)
    (finalWorkTape tail)

theorem description_lookup_rewindTailEntry
    (source scratch work : Tape Bool) :
    description.lookupTransition
        (config rewindTailEntry source scratch work) =
      some
        (row rewindTailEntry
          (Tape.read source) (Tape.read scratch) (Tape.read work)
          keepL keepS keepL rewindTailLoop) := by
  cases h0 : Tape.read source <;> (try cases ‹Bool›) <;>
    cases h1 : Tape.read scratch <;> (try cases ‹Bool›) <;>
      cases h2 : Tape.read work <;> (try cases ‹Bool›) <;>
        simp (config := {decide := true}) [description,
          ThreeTape.description, rows,
          rowsForSourceRead, rowsForScratchRead, rowsForWorkRead,
          allReads2, allReadRows3, allReads3,
          Structured.Description.lookupTransition, config, row,
          keepL, keepS, h0, h1, h2]

theorem description_lookup_rewindTailLoop_bit
    (source scratch work : Tape Bool) (bit : Bool)
    (hwork : Tape.read work = some bit) :
    description.lookupTransition
        (config rewindTailLoop source scratch work) =
      some
        (row rewindTailLoop
          (Tape.read source) (Tape.read scratch) (some bit)
          keepL keepS keepL rewindTailLoop) := by
  cases bit <;>
    cases h0 : Tape.read source <;> (try cases ‹Bool›) <;>
      cases h1 : Tape.read scratch <;> (try cases ‹Bool›) <;>
        simp (config := {decide := true}) [description,
          ThreeTape.description, rows,
          rowsForSourceRead, rowsForScratchRead, rowsForWorkRead,
          allReads2, allReadRows3, allReads3,
          Structured.Description.lookupTransition, config, row,
          keepL, keepS, h0, h1, hwork]

theorem description_lookup_rewindTailLoop_blank
    (source scratch work : Tape Bool)
    (hwork : Tape.read work = none) :
    description.lookupTransition
        (config rewindTailLoop source scratch work) =
      some
        (row rewindTailLoop
          (Tape.read source) (Tape.read scratch) none
          keepR keepS keepR rewindScratchEntry) := by
  cases h0 : Tape.read source <;> (try cases ‹Bool›) <;>
    cases h1 : Tape.read scratch <;> (try cases ‹Bool›) <;>
      simp (config := {decide := true}) [description,
        ThreeTape.description, rows,
        rowsForSourceRead, rowsForScratchRead, rowsForWorkRead,
        allReads2, allReadRows3, allReads3,
        Structured.Description.lookupTransition, config, row,
        keepL, keepR, keepS, h0, h1, hwork]

theorem description_lookup_rewindScratchEntry
    (source scratch work : Tape Bool) :
    description.lookupTransition
        (config rewindScratchEntry source scratch work) =
      some
        (row rewindScratchEntry
          (Tape.read source) (Tape.read scratch) (Tape.read work)
          keepS keepL keepS rewindScratchLoop) := by
  cases h0 : Tape.read source <;> (try cases ‹Bool›) <;>
    cases h1 : Tape.read scratch <;> (try cases ‹Bool›) <;>
      cases h2 : Tape.read work <;> (try cases ‹Bool›) <;>
        simp (config := {decide := true}) [description,
          ThreeTape.description, rows,
          rowsForSourceRead, rowsForScratchRead, rowsForWorkRead,
          allReads2, allReadRows3, allReads3,
          Structured.Description.lookupTransition, config, row,
          keepL, keepS, h0, h1, h2]

theorem description_lookup_rewindScratchLoop_bit
    (source scratch work : Tape Bool) (bit : Bool)
    (hscratch : Tape.read scratch = some bit) :
    description.lookupTransition
        (config rewindScratchLoop source scratch work) =
      some
        (row rewindScratchLoop
          (Tape.read source) (some bit) (Tape.read work)
          keepS keepL keepS rewindScratchLoop) := by
  cases bit <;>
    cases h0 : Tape.read source <;> (try cases ‹Bool›) <;>
      cases h2 : Tape.read work <;> (try cases ‹Bool›) <;>
        simp (config := {decide := true}) [description,
          ThreeTape.description, rows,
          rowsForSourceRead, rowsForScratchRead, rowsForWorkRead,
          allReads2, allReadRows3, allReads3,
          Structured.Description.lookupTransition, config, row,
          keepL, keepS, h0, hscratch, h2]

theorem description_lookup_rewindScratchLoop_blank
    (source scratch work : Tape Bool)
    (hscratch : Tape.read scratch = none) :
    description.lookupTransition
        (config rewindScratchLoop source scratch work) =
      some
        (row rewindScratchLoop
          (Tape.read source) none (Tape.read work)
          keepS keepR keepS writeInsert) := by
  cases h0 : Tape.read source <;> (try cases ‹Bool›) <;>
    cases h2 : Tape.read work <;> (try cases ‹Bool›) <;>
      simp (config := {decide := true}) [description,
        ThreeTape.description, rows,
        rowsForSourceRead, rowsForScratchRead, rowsForWorkRead,
        allReads2, allReadRows3, allReads3,
        Structured.Description.lookupTransition, config, row,
        keepL, keepR, keepS, h0, hscratch, h2]

theorem description_lookup_writeInsert_bit
    (source scratch work : Tape Bool) (bit : Bool)
    (hscratch : Tape.read scratch = some bit) :
    description.lookupTransition
        (config writeInsert source scratch work) =
      some
        (row writeInsert
          (Tape.read source) (some bit) (Tape.read work)
          (writeBitR bit) keepR keepS writeInsert) := by
  cases bit <;>
    cases h0 : Tape.read source <;> (try cases ‹Bool›) <;>
      cases h2 : Tape.read work <;> (try cases ‹Bool›) <;>
        simp (config := {decide := true}) [description,
          ThreeTape.description, rows,
          rowsForSourceRead, rowsForScratchRead, rowsForWorkRead,
          allReads2, allReadRows3, allReads3,
          Structured.Description.lookupTransition, config, row,
          keepR, keepS, writeBitR, writeR, h0, hscratch, h2]

theorem description_lookup_writeInsert_blank
    (source scratch work : Tape Bool)
    (hscratch : Tape.read scratch = none) :
    description.lookupTransition
        (config writeInsert source scratch work) =
      some
        (row writeInsert
          (Tape.read source) none (Tape.read work)
          keepS keepS keepS restoreTail) := by
  cases h0 : Tape.read source <;> (try cases ‹Bool›) <;>
    cases h2 : Tape.read work <;> (try cases ‹Bool›) <;>
      simp (config := {decide := true}) [description,
        ThreeTape.description, rows,
        rowsForSourceRead, rowsForScratchRead, rowsForWorkRead,
        allReads2, allReadRows3, allReads3,
        Structured.Description.lookupTransition, config, row,
        keepR, keepS, writeBitR, writeR, h0, hscratch, h2]

theorem description_lookup_restoreTail_bit
    (source scratch work : Tape Bool) (bit : Bool)
    (hwork : Tape.read work = some bit) :
    description.lookupTransition
        (config restoreTail source scratch work) =
      some
        (row restoreTail
          (Tape.read source) (Tape.read scratch) (some bit)
          (writeBitR bit) keepS eraseR restoreTail) := by
  cases bit <;>
    cases h0 : Tape.read source <;> (try cases ‹Bool›) <;>
      cases h1 : Tape.read scratch <;> (try cases ‹Bool›) <;>
        simp (config := {decide := true}) [description,
          ThreeTape.description, rows,
          rowsForSourceRead, rowsForScratchRead, rowsForWorkRead,
          allReads2, allReadRows3, allReads3,
          Structured.Description.lookupTransition, config, row,
          keepS, eraseR, writeBitR, writeR, h0, h1, hwork]

theorem description_lookup_restoreTail_blank
    (source scratch work : Tape Bool)
    (hwork : Tape.read work = none) :
    description.lookupTransition
        (config restoreTail source scratch work) =
      some
        (row restoreTail
          (Tape.read source) (Tape.read scratch) none
          eraseR keepS keepS halt) := by
  cases h0 : Tape.read source <;> (try cases ‹Bool›) <;>
    cases h1 : Tape.read scratch <;> (try cases ‹Bool›) <;>
      simp (config := {decide := true}) [description,
        ThreeTape.description, rows,
        rowsForSourceRead, rowsForScratchRead, rowsForWorkRead,
        allReads2, allReadRows3, allReads3,
        Structured.Description.lookupTransition, config, row,
        keepS, eraseR, writeBitR, writeR, h0, h1, hwork]

theorem rewindTail_entry_step
    (pref tail insert : Word Bool) :
    description.runConfig 1
        (copyTailHandoffConfig pref tail insert) =
      config rewindTailLoop
        (rewindTailLoopSourceTapeFromLeft
          (pref.reverse.map some) tail.reverse [] insert)
        (scratchTape insert)
        (rewindTailLoopWorkTape tail.reverse []) := by
  simp only [copyTailHandoffConfig]
  rw [Structured.Description.runConfig]
  rw [Structured.Description.stepConfig]
  rw [description_lookup_rewindTailEntry]
  unfold description
  three_tape_step [erasedTailSourceTape,
    rewindTailLoopSourceTapeFromLeft, rewindTailLoopWorkTape,
    rewindTailRightCells, scratchTape, outputFromBits]
  all_goals
    cases htail : tail.reverse with
    | nil =>
        have hnil : tail = [] := by
          have hlen : tail.length = 0 := by
            have hlen := congrArg List.length htail
            simpa [List.length_reverse] using hlen
          exact List.eq_nil_of_length_eq_zero hlen
        subst tail
        cases (List.map some pref).reverse <;>
          constructor <;> rfl
    | cons bit rest =>
        have hlen : tail.length = rest.length + 1 := by
          have hlen := congrArg List.length htail
          simpa [List.length_reverse] using hlen
        have hmap :
            (tail.map some).reverse = some bit :: rest.map some := by
          calc
            (tail.map some).reverse = tail.reverse.map some := by
              simp
            _ = some bit :: rest.map some := by
              rw [htail]
              rfl
        cases bit <;> simp [hlen, hmap, List.replicate_succ]

theorem rewindTail_loop_step_bit
    (leftBoundary : List (Option Bool)) (bit : Bool)
    (rest processed insert : Word Bool) :
    description.runConfig 1
        (config rewindTailLoop
          (rewindTailLoopSourceTapeFromLeft
            leftBoundary (bit :: rest) processed insert)
          (scratchTape insert)
          (rewindTailLoopWorkTape (bit :: rest) processed)) =
      config rewindTailLoop
        (rewindTailLoopSourceTapeFromLeft
          leftBoundary rest (bit :: processed) insert)
        (scratchTape insert)
        (rewindTailLoopWorkTape rest (bit :: processed)) := by
  rw [Structured.Description.runConfig]
  rw [Structured.Description.stepConfig]
  rw [description_lookup_rewindTailLoop_bit _ _ _ bit (by rfl)]
  unfold description
  three_tape_step [rewindTailLoopSourceTapeFromLeft,
    rewindTailLoopWorkTape, rewindTailRightCells, scratchTape]
  all_goals
    cases rest with
    | nil =>
        cases leftBoundary <;> simp [List.replicate_succ]
    | cons next rest =>
        cases next <;> simp [List.replicate_succ]

theorem rewindTail_loop_step_blank
    (leftBoundary : List (Option Bool))
    (processed insert : Word Bool) :
    description.runConfig 1
        (config rewindTailLoop
          (rewindTailLoopSourceTapeFromLeft
            leftBoundary [] processed insert)
          (scratchTape insert)
          (rewindTailLoopWorkTape [] processed)) =
      config rewindScratchEntry
        (rewindTailHandoffSourceTapeFromLeft
          leftBoundary processed insert)
        (scratchTape insert)
        (rewindTailHandoffWorkTape processed) := by
  rw [Structured.Description.runConfig]
  rw [Structured.Description.stepConfig]
  rw [description_lookup_rewindTailLoop_blank _ _ _ (by rfl)]
  unfold description
  three_tape_step [rewindTailLoopSourceTapeFromLeft,
    rewindTailLoopWorkTape, rewindTailHandoffSourceTapeFromLeft,
    rewindTailHandoffWorkTape, rewindTailRightCells, scratchTape]
  all_goals
    cases leftBoundary <;>
      constructor
    · cases hright :
          List.replicate (List.length processed) (none : Option Bool) ++
            none :: (List.map some insert ++ [none]) <;>
        rfl
    · cases hwork : List.map some processed ++ [none] <;> rfl
    · cases hright :
          List.replicate (List.length processed) (none : Option Bool) ++
            none :: (List.map some insert ++ [none]) <;>
        rfl
    · cases hwork : List.map some processed ++ [none] <;> rfl

theorem rewindTail_loop_run
    (remainingRev processed insert : Word Bool)
    (leftBoundary : List (Option Bool)) :
    description.runConfig (remainingRev.length + 1)
        (config rewindTailLoop
          (rewindTailLoopSourceTapeFromLeft
            leftBoundary remainingRev processed insert)
          (scratchTape insert)
          (rewindTailLoopWorkTape remainingRev processed)) =
      config rewindScratchEntry
        (rewindTailHandoffSourceTapeFromLeft
          leftBoundary (List.append remainingRev.reverse processed)
          insert)
        (scratchTape insert)
        (rewindTailHandoffWorkTape
          (List.append remainingRev.reverse processed)) := by
  induction remainingRev generalizing processed with
  | nil =>
      simpa using
        rewindTail_loop_step_blank
          leftBoundary processed insert
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 = 1 + (rest.length + 1) by
        simp [Nat.add_comm, Nat.add_left_comm]]
      rw [Structured.Description.runConfig_add]
      rw [rewindTail_loop_step_bit]
      rw [ih (bit :: processed)]
      simp [List.reverse_cons, List.append_assoc]

theorem rewindTail_run
    (pref tail insert : Word Bool) :
    description.runConfig (tail.length + 2)
        (copyTailHandoffConfig pref tail insert) =
      rewindTailHandoffConfig pref tail insert := by
  rw [show tail.length + 2 = 1 + (tail.reverse.length + 1) by
    simp [Nat.add_left_comm]]
  rw [Structured.Description.runConfig_add]
  rw [rewindTail_entry_step]
  rw [rewindTail_loop_run]
  simp [rewindTailHandoffConfig, rewindTailHandoffSourceTape,
    rewindTailHandoffWorkTape]

def RewindTailSpec (D : Description) : Prop :=
  SupportsReadWriteRows3 D ∧
    forall (pref tail insert : Word Bool),
      D.runConfig (tail.length + 2)
          (copyTailHandoffConfig pref tail insert) =
        rewindTailHandoffConfig pref tail insert

theorem RewindTailSpec.supported
    {D : Description} (hD : RewindTailSpec D) :
    SupportsReadWriteRows3 D :=
  hD.left

theorem RewindTailSpec.run
    {D : Description} (hD : RewindTailSpec D)
    (pref tail insert : Word Bool) :
    D.runConfig (tail.length + 2)
        (copyTailHandoffConfig pref tail insert) =
      rewindTailHandoffConfig pref tail insert :=
  hD.right pref tail insert

theorem description_rewindTailSpec :
    RewindTailSpec description := by
  refine ⟨description_supported, ?_⟩
  intro pref tail insert
  exact rewindTail_run pref tail insert

def CopyRewindTailSpec (D : Description) : Prop :=
  CopyTailSpec D ∧ RewindTailSpec D ∧
    forall (pref tail insert : Word Bool),
      D.runConfig (2 * tail.length + 3)
          (initialConfig pref tail insert) =
        rewindTailHandoffConfig pref tail insert

theorem CopyRewindTailSpec.copyTail
    {D : Description} (hD : CopyRewindTailSpec D) :
    CopyTailSpec D :=
  hD.left

theorem CopyRewindTailSpec.rewindTail
    {D : Description} (hD : CopyRewindTailSpec D) :
    RewindTailSpec D :=
  hD.right.left

theorem CopyRewindTailSpec.run
    {D : Description} (hD : CopyRewindTailSpec D)
    (pref tail insert : Word Bool) :
    D.runConfig (2 * tail.length + 3)
        (initialConfig pref tail insert) =
      rewindTailHandoffConfig pref tail insert :=
  hD.right.right pref tail insert

theorem description_copyRewindTailSpec :
    CopyRewindTailSpec description := by
  refine ⟨description_copyTailSpec, description_rewindTailSpec, ?_⟩
  intro pref tail insert
  rw [show 2 * tail.length + 3 =
      (tail.length + 1) + (tail.length + 2) by
    lia]
  rw [Structured.Description.runConfig_add]
  rw [CopyTailSpec.run description_copyTailSpec]
  exact RewindTailSpec.run description_rewindTailSpec pref tail insert

theorem rewindScratch_entry_step
    (pref tail insert : Word Bool) :
    description.runConfig 1
        (rewindTailHandoffConfig pref tail insert) =
      config rewindScratchLoop
        (rewindTailHandoffSourceTape pref tail insert)
        (rewindScratchLoopScratchTape insert.reverse [])
        (rewindTailHandoffWorkTape tail) := by
  simp only [rewindTailHandoffConfig]
  rw [Structured.Description.runConfig]
  rw [Structured.Description.stepConfig]
  rw [description_lookup_rewindScratchEntry]
  unfold description
  three_tape_step [rewindScratchLoopScratchTape, scratchTape,
    outputFromBits]
  all_goals
    cases hinsert : insert.reverse with
    | nil =>
        have hnil : insert = [] := by
          have hlen : insert.length = 0 := by
            have hlen := congrArg List.length hinsert
            simpa [List.length_reverse] using hlen
          exact List.eq_nil_of_length_eq_zero hlen
        subst insert
        constructor <;> rfl
    | cons bit rest =>
        have hmap :
            (insert.map some).reverse = some bit :: rest.map some := by
          calc
            (insert.map some).reverse = insert.reverse.map some := by
              simp
            _ = some bit :: rest.map some := by
              rw [hinsert]
              rfl
        cases bit <;> simp [hmap]

theorem rewindScratch_loop_step_bit
    (source work : Tape Bool) (bit : Bool)
    (rest processed : Word Bool) :
    description.runConfig 1
        (config rewindScratchLoop source
          (rewindScratchLoopScratchTape (bit :: rest) processed)
          work) =
      config rewindScratchLoop source
        (rewindScratchLoopScratchTape rest (bit :: processed))
        work := by
  rw [Structured.Description.runConfig]
  rw [Structured.Description.stepConfig]
  rw [description_lookup_rewindScratchLoop_bit _ _ _ bit (by rfl)]
  unfold description
  three_tape_step [rewindScratchLoopScratchTape]
  all_goals
    cases rest with
    | nil =>
        simp
    | cons next rest =>
        cases next <;> simp

theorem rewindScratch_loop_step_blank
    (source work : Tape Bool) (processed : Word Bool) :
    description.runConfig 1
        (config rewindScratchLoop source
          (rewindScratchLoopScratchTape [] processed)
          work) =
      config writeInsert source
        (writeInsertScratchTape processed)
        work := by
  rw [Structured.Description.runConfig]
  rw [Structured.Description.stepConfig]
  rw [description_lookup_rewindScratchLoop_blank _ _ _ (by rfl)]
  unfold description
  three_tape_step [rewindScratchLoopScratchTape,
    writeInsertScratchTape]
  all_goals
    cases processed <;> constructor <;> rfl

theorem rewindScratch_loop_run
    (remainingRev processed : Word Bool)
    (source work : Tape Bool) :
    description.runConfig (remainingRev.length + 1)
        (config rewindScratchLoop source
          (rewindScratchLoopScratchTape remainingRev processed)
          work) =
      config writeInsert source
        (writeInsertScratchTape
          (List.append remainingRev.reverse processed))
        work := by
  induction remainingRev generalizing processed with
  | nil =>
      simpa using
        rewindScratch_loop_step_blank source work processed
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 = 1 + (rest.length + 1) by
        simp [Nat.add_comm, Nat.add_left_comm]]
      rw [Structured.Description.runConfig_add]
      rw [rewindScratch_loop_step_bit]
      rw [ih (bit :: processed)]
      simp [List.reverse_cons, List.append_assoc]

theorem rewindScratch_run
    (pref tail insert : Word Bool) :
    description.runConfig (insert.length + 2)
        (rewindTailHandoffConfig pref tail insert) =
      rewindScratchHandoffConfig pref tail insert := by
  rw [show insert.length + 2 = 1 + (insert.reverse.length + 1) by
    simp [Nat.add_left_comm]]
  rw [Structured.Description.runConfig_add]
  rw [rewindScratch_entry_step]
  rw [rewindScratch_loop_run]
  simp [rewindScratchHandoffConfig]

def RewindScratchSpec (D : Description) : Prop :=
  SupportsReadWriteRows3 D ∧
    forall (pref tail insert : Word Bool),
      D.runConfig (insert.length + 2)
          (rewindTailHandoffConfig pref tail insert) =
        rewindScratchHandoffConfig pref tail insert

theorem RewindScratchSpec.supported
    {D : Description} (hD : RewindScratchSpec D) :
    SupportsReadWriteRows3 D :=
  hD.left

theorem RewindScratchSpec.run
    {D : Description} (hD : RewindScratchSpec D)
    (pref tail insert : Word Bool) :
    D.runConfig (insert.length + 2)
        (rewindTailHandoffConfig pref tail insert) =
      rewindScratchHandoffConfig pref tail insert :=
  hD.right pref tail insert

theorem description_rewindScratchSpec :
    RewindScratchSpec description := by
  refine ⟨description_supported, ?_⟩
  intro pref tail insert
  exact rewindScratch_run pref tail insert

def CopyRewindScratchSpec (D : Description) : Prop :=
  CopyRewindTailSpec D ∧ RewindScratchSpec D ∧
    forall (pref tail insert : Word Bool),
      D.runConfig (2 * tail.length + insert.length + 5)
          (initialConfig pref tail insert) =
        rewindScratchHandoffConfig pref tail insert

theorem CopyRewindScratchSpec.copyRewindTail
    {D : Description} (hD : CopyRewindScratchSpec D) :
    CopyRewindTailSpec D :=
  hD.left

theorem CopyRewindScratchSpec.rewindScratch
    {D : Description} (hD : CopyRewindScratchSpec D) :
    RewindScratchSpec D :=
  hD.right.left

theorem CopyRewindScratchSpec.run
    {D : Description} (hD : CopyRewindScratchSpec D)
    (pref tail insert : Word Bool) :
    D.runConfig (2 * tail.length + insert.length + 5)
        (initialConfig pref tail insert) =
      rewindScratchHandoffConfig pref tail insert :=
  hD.right.right pref tail insert

theorem description_copyRewindScratchSpec :
    CopyRewindScratchSpec description := by
  refine ⟨description_copyRewindTailSpec,
    description_rewindScratchSpec, ?_⟩
  intro pref tail insert
  rw [show 2 * tail.length + insert.length + 5 =
      (2 * tail.length + 3) + (insert.length + 2) by
    lia]
  rw [Structured.Description.runConfig_add]
  rw [CopyRewindTailSpec.run description_copyRewindTailSpec]
  exact RewindScratchSpec.run
    description_rewindScratchSpec pref tail insert

theorem writeInsert_step_bit
    (leftBoundary : List (Option Bool)) (written remaining : Word Bool)
    (sourceCell : Option Bool) (rightCells : List (Option Bool))
    (work : Tape Bool) (bit : Bool) :
    description.runConfig 1
        (config writeInsert
          (writeInsertSourceTapeFromLeft leftBoundary written
            (sourceCell :: rightCells))
          (writeInsertLoopScratchTape written (bit :: remaining))
          work) =
      config writeInsert
        (writeInsertSourceTapeFromLeft leftBoundary
          (List.append written [bit]) rightCells)
        (writeInsertLoopScratchTape
          (List.append written [bit]) remaining)
        work := by
  rw [Structured.Description.runConfig]
  rw [Structured.Description.stepConfig]
  rw [description_lookup_writeInsert_bit _ _ _ bit (by rfl)]
  unfold description
  three_tape_step [writeInsertSourceTapeFromLeft,
    writeInsertLoopScratchTape]
  all_goals
    cases sourceCell <;>
      cases remaining <;>
        cases rightCells <;>
          simp

theorem writeInsert_step_blank
    (source work : Tape Bool) (insert : Word Bool) :
    description.runConfig 1
        (config writeInsert source
          (writeInsertLoopScratchTape insert [])
          work) =
      config restoreTail source
        (finalScratchTape insert)
        work := by
  rw [Structured.Description.runConfig]
  rw [Structured.Description.stepConfig]
  rw [description_lookup_writeInsert_blank _ _ _ (by rfl)]
  unfold description
  three_tape_step [writeInsertLoopScratchTape,
    finalScratchTape]

theorem writeInsert_loop_run
    (remaining written : Word Bool)
    (leftBoundary : List (Option Bool))
    (overwritten suffix : List (Option Bool))
    (work : Tape Bool)
    (hlen : overwritten.length = remaining.length) :
    description.runConfig (remaining.length + 1)
        (config writeInsert
          (writeInsertSourceTapeFromLeft leftBoundary written
            (List.append overwritten suffix))
          (writeInsertLoopScratchTape written remaining)
          work) =
      config restoreTail
        (writeInsertSourceTapeFromLeft leftBoundary
          (List.append written remaining) suffix)
        (finalScratchTape (List.append written remaining))
        work := by
  induction remaining generalizing written overwritten with
  | nil =>
      have hoverwritten : overwritten = [] :=
        List.eq_nil_of_length_eq_zero hlen
      subst overwritten
      simpa using
        writeInsert_step_blank
          (writeInsertSourceTapeFromLeft leftBoundary written suffix)
          work written
  | cons bit rest ih =>
      cases overwritten with
      | nil =>
          simp at hlen
      | cons sourceCell overwrittenRest =>
          have hlenRest : overwrittenRest.length = rest.length := by
            exact Nat.succ.inj hlen
          rw [show (bit :: rest).length + 1 =
              1 + (rest.length + 1) by
            simp [Nat.add_comm, Nat.add_left_comm]]
          rw [show
            List.append (sourceCell :: overwrittenRest) suffix =
              sourceCell :: List.append overwrittenRest suffix by
            rfl]
          rw [Structured.Description.runConfig_add]
          rw [writeInsert_step_bit]
          rw [ih (List.append written [bit])
            overwrittenRest hlenRest]
          simp [List.append_assoc]

theorem writeInsert_overwriteCells_length
    (tail insert : Word Bool) :
    ((rewindTailRightCells tail insert).take insert.length).length =
      insert.length := by
  rw [List.length_take]
  have hle :
      insert.length <= (rewindTailRightCells tail insert).length := by
    simp [rewindTailRightCells]
    lia
  exact Nat.min_eq_left hle

theorem writeInsert_run
    (pref tail insert : Word Bool) :
    description.runConfig (insert.length + 1)
        (rewindScratchHandoffConfig pref tail insert) =
      writeInsertHandoffConfig pref tail insert := by
  let cells := rewindTailRightCells tail insert
  have hrun :=
    writeInsert_loop_run insert []
      (pref.reverse.map some)
      (cells.take insert.length)
      (cells.drop insert.length)
      (rewindTailHandoffWorkTape tail)
      (by
        simpa [cells] using
          writeInsert_overwriteCells_length tail insert)
  simpa [rewindScratchHandoffConfig, rewindTailHandoffSourceTape,
    rewindTailHandoffSourceTapeFromLeft, writeInsertHandoffConfig,
    writeInsertHandoffSourceTape, writeInsertHandoffSourceTapeFromLeft,
    writeInsertHandoffRightCells, writeInsertSourceTapeFromLeft,
    writeInsertScratchTape, writeInsertLoopScratchTape, cells,
    List.take_append_drop] using hrun

def WriteInsertSpec (D : Description) : Prop :=
  SupportsReadWriteRows3 D ∧
    forall (pref tail insert : Word Bool),
      D.runConfig (insert.length + 1)
          (rewindScratchHandoffConfig pref tail insert) =
        writeInsertHandoffConfig pref tail insert

theorem WriteInsertSpec.supported
    {D : Description} (hD : WriteInsertSpec D) :
    SupportsReadWriteRows3 D :=
  hD.left

theorem WriteInsertSpec.run
    {D : Description} (hD : WriteInsertSpec D)
    (pref tail insert : Word Bool) :
    D.runConfig (insert.length + 1)
        (rewindScratchHandoffConfig pref tail insert) =
      writeInsertHandoffConfig pref tail insert :=
  hD.right pref tail insert

theorem description_writeInsertSpec :
    WriteInsertSpec description := by
  refine ⟨description_supported, ?_⟩
  intro pref tail insert
  exact writeInsert_run pref tail insert

def CopyRewindScratchWriteInsertSpec (D : Description) : Prop :=
  CopyRewindScratchSpec D ∧ WriteInsertSpec D ∧
    forall (pref tail insert : Word Bool),
      D.runConfig (2 * tail.length + 2 * insert.length + 6)
          (initialConfig pref tail insert) =
        writeInsertHandoffConfig pref tail insert

theorem CopyRewindScratchWriteInsertSpec.copyRewindScratch
    {D : Description} (hD : CopyRewindScratchWriteInsertSpec D) :
    CopyRewindScratchSpec D :=
  hD.left

theorem CopyRewindScratchWriteInsertSpec.writeInsert
    {D : Description} (hD : CopyRewindScratchWriteInsertSpec D) :
    WriteInsertSpec D :=
  hD.right.left

theorem CopyRewindScratchWriteInsertSpec.run
    {D : Description} (hD : CopyRewindScratchWriteInsertSpec D)
    (pref tail insert : Word Bool) :
    D.runConfig (2 * tail.length + 2 * insert.length + 6)
        (initialConfig pref tail insert) =
      writeInsertHandoffConfig pref tail insert :=
  hD.right.right pref tail insert

theorem description_copyRewindScratchWriteInsertSpec :
    CopyRewindScratchWriteInsertSpec description := by
  refine ⟨description_copyRewindScratchSpec,
    description_writeInsertSpec, ?_⟩
  intro pref tail insert
  rw [show 2 * tail.length + 2 * insert.length + 6 =
      (2 * tail.length + insert.length + 5) +
        (insert.length + 1) by
    lia]
  rw [Structured.Description.runConfig_add]
  rw [CopyRewindScratchSpec.run description_copyRewindScratchSpec]
  exact WriteInsertSpec.run description_writeInsertSpec
    pref tail insert

theorem restoreTail_step_bit
    (leftBoundary : List (Option Bool)) (insert restored remaining : Word Bool)
    (sourceCell : Option Bool) (rightCells : List (Option Bool))
    (scratch : Tape Bool) (bit : Bool) :
    description.runConfig 1
        (config restoreTail
          (restoreTailLoopSourceTapeFromLeft
            leftBoundary insert restored (sourceCell :: rightCells))
          scratch
          (restoreTailLoopWorkTape (bit :: remaining) restored)) =
      config restoreTail
        (restoreTailLoopSourceTapeFromLeft
          leftBoundary insert (List.append restored [bit]) rightCells)
        scratch
        (restoreTailLoopWorkTape remaining
          (List.append restored [bit])) := by
  rw [Structured.Description.runConfig]
  rw [Structured.Description.stepConfig]
  rw [description_lookup_restoreTail_bit _ _ _ bit (by rfl)]
  unfold description
  three_tape_step [restoreTailLoopSourceTapeFromLeft,
    restoreTailLoopWorkTape]
  all_goals
    cases sourceCell <;>
      cases remaining <;>
        cases rightCells <;>
          simp [List.replicate_succ]

theorem restoreTail_step_blank
    (leftBoundary : List (Option Bool))
    (insert tail : Word Bool)
    (cleanupCell : Option Bool)
    (scratch : Tape Bool) :
    description.runConfig 1
        (config restoreTail
          (restoreTailLoopSourceTapeFromLeft
            leftBoundary insert tail (cleanupCell :: [none]))
          scratch
          (restoreTailLoopWorkTape [] tail)) =
      config halt
        (restoreTailHandoffSourceTapeFromLeft
          leftBoundary tail insert)
        scratch
        (finalWorkTape tail) := by
  rw [Structured.Description.runConfig]
  rw [Structured.Description.stepConfig]
  rw [description_lookup_restoreTail_blank _ _ _ (by rfl)]
  unfold description
  three_tape_step [restoreTailLoopSourceTapeFromLeft,
    restoreTailLoopWorkTape, restoreTailHandoffSourceTapeFromLeft,
    finalWorkTape]
  all_goals
    cases cleanupCell <;> constructor <;> rfl

theorem restoreTail_loop_run
    (remaining restored insert : Word Bool)
    (leftBoundary : List (Option Bool))
    (overwritten : List (Option Bool))
    (cleanupCell : Option Bool)
    (scratch : Tape Bool)
    (hlen : overwritten.length = remaining.length) :
    description.runConfig (remaining.length + 1)
        (config restoreTail
          (restoreTailLoopSourceTapeFromLeft leftBoundary insert restored
            (List.append overwritten (cleanupCell :: [none])))
          scratch
          (restoreTailLoopWorkTape remaining restored)) =
      config halt
        (restoreTailHandoffSourceTapeFromLeft
          leftBoundary (List.append restored remaining) insert)
        scratch
        (finalWorkTape (List.append restored remaining)) := by
  induction remaining generalizing restored overwritten with
  | nil =>
      have hoverwritten : overwritten = [] :=
        List.eq_nil_of_length_eq_zero hlen
      subst overwritten
      simpa using
        restoreTail_step_blank
          leftBoundary insert restored cleanupCell scratch
  | cons bit rest ih =>
      cases overwritten with
      | nil =>
          simp at hlen
      | cons sourceCell overwrittenRest =>
          have hlenRest : overwrittenRest.length = rest.length := by
            exact Nat.succ.inj hlen
          rw [show (bit :: rest).length + 1 =
              1 + (rest.length + 1) by
            simp [Nat.add_comm, Nat.add_left_comm]]
          rw [show
            List.append (sourceCell :: overwrittenRest)
                (cleanupCell :: [none]) =
              sourceCell ::
                List.append overwrittenRest (cleanupCell :: [none]) by
            rfl]
          rw [Structured.Description.runConfig_add]
          rw [restoreTail_step_bit]
          rw [ih (List.append restored [bit])
            overwrittenRest hlenRest]
          simp [List.append_assoc]

theorem restoreTail_overwriteCells_length
    (tail insert : Word Bool) :
    ((writeInsertHandoffRightCells tail insert).take tail.length).length =
      tail.length := by
  rw [List.length_take]
  have hle :
      tail.length <= (writeInsertHandoffRightCells tail insert).length := by
    simp [writeInsertHandoffRightCells, rewindTailRightCells]
    lia
  exact Nat.min_eq_left hle

theorem writeInsertHandoffRightCells_afterTail
    (tail insert : Word Bool) :
    (writeInsertHandoffRightCells tail insert).drop tail.length =
      restoreTailCleanupCell insert :: [none] := by
  cases hinsert : insert.reverse with
  | nil =>
      have hnil : insert = [] := by
        have hlen : insert.length = 0 := by
          have hlen := congrArg List.length hinsert
          simpa [List.length_reverse] using hlen
        exact List.eq_nil_of_length_eq_zero hlen
      subst insert
      simp [writeInsertHandoffRightCells, rewindTailRightCells,
        restoreTailCleanupCell]
  | cons bit rest =>
      have hmap :
          (insert.map some).reverse = some bit :: rest.map some := by
        calc
          (insert.map some).reverse = insert.reverse.map some := by
            simp
          _ = some bit :: rest.map some := by
            rw [hinsert]
            rfl
      have hlen : insert.length = rest.length + 1 := by
        have hlen := congrArg List.length hinsert
        simpa [List.length_reverse] using hlen
      have hmapForward :
          insert.map some =
            List.append (rest.reverse.map some) [some bit] := by
        have hrev := congrArg List.reverse hmap
        simpa [List.reverse_cons, List.map_reverse] using hrev
      rw [writeInsertHandoffRightCells]
      rw [List.drop_drop]
      rw [Nat.add_comm insert.length tail.length]
      simp [rewindTailRightCells, restoreTailCleanupCell, hinsert,
        hlen, hmapForward, List.drop_append, List.drop_replicate]

theorem restoreTail_run
    (pref tail insert : Word Bool) :
    description.runConfig (tail.length + 1)
        (writeInsertHandoffConfig pref tail insert) =
      restoreTailHandoffConfig pref tail insert := by
  let cells := writeInsertHandoffRightCells tail insert
  have hrun :=
    restoreTail_loop_run tail [] insert
      (pref.reverse.map some)
      (cells.take tail.length)
      (restoreTailCleanupCell insert)
      (finalScratchTape insert)
      (by
        simpa [cells] using
          restoreTail_overwriteCells_length tail insert)
  have hsplit :
      List.append (cells.take tail.length)
          (restoreTailCleanupCell insert :: [none]) =
        cells := by
    rw [← writeInsertHandoffRightCells_afterTail tail insert]
    exact List.take_append_drop tail.length cells
  rw [hsplit] at hrun
  simpa [writeInsertHandoffConfig, writeInsertHandoffSourceTape,
    writeInsertHandoffSourceTapeFromLeft, writeInsertSourceTapeFromLeft,
    restoreTailHandoffConfig, restoreTailHandoffSourceTape,
    restoreTailHandoffSourceTapeFromLeft, restoreTailLoopSourceTapeFromLeft,
    restoreTailLoopWorkTape, rewindTailHandoffWorkTape, cells,
    List.take_append_drop,
    writeInsertHandoffRightCells_afterTail tail insert] using hrun

def RestoreTailSpec (D : Description) : Prop :=
  SupportsReadWriteRows3 D ∧
    forall (pref tail insert : Word Bool),
      D.runConfig (tail.length + 1)
          (writeInsertHandoffConfig pref tail insert) =
        restoreTailHandoffConfig pref tail insert

theorem RestoreTailSpec.supported
    {D : Description} (hD : RestoreTailSpec D) :
    SupportsReadWriteRows3 D :=
  hD.left

theorem RestoreTailSpec.run
    {D : Description} (hD : RestoreTailSpec D)
    (pref tail insert : Word Bool) :
    D.runConfig (tail.length + 1)
        (writeInsertHandoffConfig pref tail insert) =
      restoreTailHandoffConfig pref tail insert :=
  hD.right pref tail insert

theorem description_restoreTailSpec :
    RestoreTailSpec description := by
  refine ⟨description_supported, ?_⟩
  intro pref tail insert
  exact restoreTail_run pref tail insert

def FullSpec (D : Description) : Prop :=
  CopyRewindScratchWriteInsertSpec D ∧ RestoreTailSpec D ∧
    forall (pref tail insert : Word Bool),
      D.runConfig (runFuel tail insert)
          (initialConfig pref tail insert) =
        restoreTailHandoffConfig pref tail insert

theorem FullSpec.copyRewindScratchWriteInsert
    {D : Description} (hD : FullSpec D) :
    CopyRewindScratchWriteInsertSpec D :=
  hD.left

theorem FullSpec.restoreTail
    {D : Description} (hD : FullSpec D) :
    RestoreTailSpec D :=
  hD.right.left

theorem FullSpec.run
    {D : Description} (hD : FullSpec D)
    (pref tail insert : Word Bool) :
    D.runConfig (runFuel tail insert)
        (initialConfig pref tail insert) =
      restoreTailHandoffConfig pref tail insert :=
  hD.right.right pref tail insert

theorem description_fullSpec :
    FullSpec description := by
  refine ⟨description_copyRewindScratchWriteInsertSpec,
    description_restoreTailSpec, ?_⟩
  intro pref tail insert
  rw [show runFuel tail insert =
      (2 * tail.length + 2 * insert.length + 6) +
        (tail.length + 1) by
    simp [runFuel]
    lia]
  rw [Structured.Description.runConfig_add]
  rw [CopyRewindScratchWriteInsertSpec.run
    description_copyRewindScratchWriteInsertSpec]
  exact RestoreTailSpec.run description_restoreTailSpec
    pref tail insert

theorem rewindTailHandoffSourceTapeFromLeft_normalizedOutput
    (leftBoundary : List (Option Bool)) (tail insert : Word Bool) :
    Tape.normalizedOutput
        (rewindTailHandoffSourceTapeFromLeft
          leftBoundary tail insert) =
      List.append
        (leftBoundary.reverse.filterMap (fun cell => cell))
        insert := by
  cases leftBoundary with
  | nil =>
      simp [rewindTailHandoffSourceTapeFromLeft,
        rewindTailRightCells, tapeAtCells_normalizedOutput,
        List.filterMap_append, Function.comp_def]
  | cons cell rest =>
      cases cell <;>
      simp [rewindTailHandoffSourceTapeFromLeft,
        rewindTailRightCells, tapeAtCells_normalizedOutput,
        List.filterMap_append, Function.comp_def, List.append_assoc]

theorem rewindTailHandoffSourceTape_normalizedOutput
    (pref tail insert : Word Bool) :
    Tape.normalizedOutput
        (rewindTailHandoffSourceTape pref tail insert) =
      List.append pref insert := by
  rw [rewindTailHandoffSourceTape,
    rewindTailHandoffSourceTapeFromLeft_normalizedOutput]
  simp [List.filterMap_map, Function.comp_def]

theorem rewindTailHandoffWorkTape_normalizedOutput
    (tail : Word Bool) :
    Tape.normalizedOutput (rewindTailHandoffWorkTape tail) = tail := by
  simp [rewindTailHandoffWorkTape, tapeAtCells_normalizedOutput,
    List.filterMap_append, Function.comp_def]

theorem rewindTailHandoffConfig_source_normalizedOutput
    (pref tail insert : Word Bool) :
    Tape.normalizedOutput
        (Description.tapeAt
          (rewindTailHandoffConfig pref tail insert).tapes 0) =
      List.append pref insert := by
  simpa [rewindTailHandoffConfig] using
    rewindTailHandoffSourceTape_normalizedOutput pref tail insert

theorem rewindTailHandoffConfig_scratch_normalizedOutput
    (pref tail insert : Word Bool) :
    Tape.normalizedOutput
        (Description.tapeAt
          (rewindTailHandoffConfig pref tail insert).tapes 1) =
      insert := by
  simpa [rewindTailHandoffConfig, scratchTape] using
    outputFromBits_normalizedOutput insert

theorem rewindTailHandoffConfig_work_normalizedOutput
    (pref tail insert : Word Bool) :
    Tape.normalizedOutput
        (Description.tapeAt
          (rewindTailHandoffConfig pref tail insert).tapes 2) =
      tail := by
  simpa [rewindTailHandoffConfig] using
    rewindTailHandoffWorkTape_normalizedOutput tail

theorem writeInsertScratchTape_normalizedOutput
    (insert : Word Bool) :
    Tape.normalizedOutput (writeInsertScratchTape insert) = insert := by
  simp [writeInsertScratchTape, tapeAtCells_normalizedOutput,
    List.filterMap_append, Function.comp_def]

theorem rewindScratchHandoffConfig_source_normalizedOutput
    (pref tail insert : Word Bool) :
    Tape.normalizedOutput
        (Description.tapeAt
          (rewindScratchHandoffConfig pref tail insert).tapes 0) =
      List.append pref insert := by
  simpa [rewindScratchHandoffConfig] using
    rewindTailHandoffSourceTape_normalizedOutput pref tail insert

theorem rewindScratchHandoffConfig_scratch_normalizedOutput
    (pref tail insert : Word Bool) :
    Tape.normalizedOutput
        (Description.tapeAt
          (rewindScratchHandoffConfig pref tail insert).tapes 1) =
      insert := by
  simpa [rewindScratchHandoffConfig] using
    writeInsertScratchTape_normalizedOutput insert

theorem rewindScratchHandoffConfig_work_normalizedOutput
    (pref tail insert : Word Bool) :
    Tape.normalizedOutput
        (Description.tapeAt
          (rewindScratchHandoffConfig pref tail insert).tapes 2) =
      tail := by
  simpa [rewindScratchHandoffConfig] using
    rewindTailHandoffWorkTape_normalizedOutput tail

theorem writeInsertSourceTapeFromLeft_normalizedOutput
    (leftBoundary : List (Option Bool))
    (written : Word Bool)
    (rightCells : List (Option Bool)) :
    Tape.normalizedOutput
        (writeInsertSourceTapeFromLeft
          leftBoundary written rightCells) =
      List.append
        (leftBoundary.reverse.filterMap (fun cell => cell))
        (List.append written
          (rightCells.filterMap (fun cell => cell))) := by
  cases leftBoundary with
  | nil =>
      simp [writeInsertSourceTapeFromLeft,
        tapeAtCells_normalizedOutput,
        List.filterMap_append, Function.comp_def]
  | cons cell rest =>
      cases cell <;>
      simp [writeInsertSourceTapeFromLeft,
        tapeAtCells_normalizedOutput,
        List.filterMap_append, Function.comp_def]

theorem writeInsertHandoffSourceTapeFromLeft_normalizedOutput
    (leftBoundary : List (Option Bool))
    (tail insert : Word Bool) :
    Tape.normalizedOutput
        (writeInsertHandoffSourceTapeFromLeft
          leftBoundary tail insert) =
      List.append
        (leftBoundary.reverse.filterMap (fun cell => cell))
        (List.append insert
          ((writeInsertHandoffRightCells tail insert).filterMap
            (fun cell => cell))) := by
  rw [writeInsertHandoffSourceTapeFromLeft,
    writeInsertSourceTapeFromLeft_normalizedOutput]

theorem writeInsertHandoffSourceTape_normalizedOutput
    (pref tail insert : Word Bool) :
    Tape.normalizedOutput
        (writeInsertHandoffSourceTape pref tail insert) =
      List.append pref
        (List.append insert
          ((writeInsertHandoffRightCells tail insert).filterMap
            (fun cell => cell))) := by
  rw [writeInsertHandoffSourceTape,
    writeInsertHandoffSourceTapeFromLeft_normalizedOutput]
  simp [List.filterMap_map, Function.comp_def]

theorem writeInsertHandoffConfig_source_normalizedOutput
    (pref tail insert : Word Bool) :
    Tape.normalizedOutput
        (Description.tapeAt
          (writeInsertHandoffConfig pref tail insert).tapes 0) =
      List.append pref
        (List.append insert
          ((writeInsertHandoffRightCells tail insert).filterMap
            (fun cell => cell))) := by
  simpa [writeInsertHandoffConfig] using
    writeInsertHandoffSourceTape_normalizedOutput pref tail insert

theorem writeInsertHandoffConfig_scratch_normalizedOutput
    (pref tail insert : Word Bool) :
    Tape.normalizedOutput
        (Description.tapeAt
          (writeInsertHandoffConfig pref tail insert).tapes 1) =
      insert := by
  change Tape.normalizedOutput (finalScratchTape insert) = insert
  simp [finalScratchTape, tapeAtCells_normalizedOutput,
    List.filterMap_append, List.map_reverse, Function.comp_def]

theorem writeInsertHandoffConfig_work_normalizedOutput
    (pref tail insert : Word Bool) :
    Tape.normalizedOutput
        (Description.tapeAt
          (writeInsertHandoffConfig pref tail insert).tapes 2) =
      tail := by
  simpa [writeInsertHandoffConfig] using
    rewindTailHandoffWorkTape_normalizedOutput tail

theorem restoreTailHandoffSourceTapeFromLeft_normalizedOutput
    (leftBoundary : List (Option Bool))
    (tail insert : Word Bool) :
    Tape.normalizedOutput
        (restoreTailHandoffSourceTapeFromLeft
          leftBoundary tail insert) =
      List.append
        (leftBoundary.reverse.filterMap (fun cell => cell))
        (List.append insert tail) := by
  cases leftBoundary with
  | nil =>
      simp [restoreTailHandoffSourceTapeFromLeft,
        tapeAtCells_normalizedOutput,
        List.filterMap_append, Function.comp_def,
        List.append_assoc]
  | cons cell rest =>
      cases cell <;>
      simp [restoreTailHandoffSourceTapeFromLeft,
        tapeAtCells_normalizedOutput,
        List.filterMap_append, Function.comp_def,
        List.append_assoc]

theorem restoreTailHandoffSourceTape_normalizedOutput
    (pref tail insert : Word Bool) :
    Tape.normalizedOutput
        (restoreTailHandoffSourceTape pref tail insert) =
      List.append pref (List.append insert tail) := by
  rw [restoreTailHandoffSourceTape,
    restoreTailHandoffSourceTapeFromLeft_normalizedOutput]
  simp [List.filterMap_map, Function.comp_def]

theorem finalWorkTape_normalizedOutput
    (tail : Word Bool) :
    Tape.normalizedOutput (finalWorkTape tail) = [] := by
  simp [finalWorkTape, tapeAtCells_normalizedOutput]

theorem restoreTailHandoffConfig_source_normalizedOutput
    (pref tail insert : Word Bool) :
    Tape.normalizedOutput
        (Description.tapeAt
          (restoreTailHandoffConfig pref tail insert).tapes 0) =
      List.append pref (List.append insert tail) := by
  simpa [restoreTailHandoffConfig] using
    restoreTailHandoffSourceTape_normalizedOutput pref tail insert

theorem restoreTailHandoffConfig_scratch_normalizedOutput
    (pref tail insert : Word Bool) :
    Tape.normalizedOutput
        (Description.tapeAt
          (restoreTailHandoffConfig pref tail insert).tapes 1) =
      insert := by
  change Tape.normalizedOutput (finalScratchTape insert) = insert
  simp [finalScratchTape, tapeAtCells_normalizedOutput,
    List.filterMap_append, List.map_reverse, Function.comp_def]

theorem restoreTailHandoffConfig_work_normalizedOutput
    (pref tail insert : Word Bool) :
    Tape.normalizedOutput
        (Description.tapeAt
          (restoreTailHandoffConfig pref tail insert).tapes 2) =
      [] := by
  simpa [restoreTailHandoffConfig] using
    finalWorkTape_normalizedOutput tail

theorem sourceTape_normalizedOutput
    (pref tail insert : Word Bool) :
    Tape.normalizedOutput (sourceTape pref tail insert) =
      List.append pref (List.append tail insert) := by
  simp [sourceTape, tapeAtCells_normalizedOutput,
    List.filterMap_append, List.map_reverse, Function.comp_def]

theorem erasedTailSourceTape_normalizedOutput
    (pref tail insert : Word Bool) :
    Tape.normalizedOutput (erasedTailSourceTape pref tail insert) =
      List.append pref insert := by
  simp [erasedTailSourceTape, tapeAtCells_normalizedOutput,
    List.filterMap_append, List.map_reverse, List.append_assoc,
    Function.comp_def]

theorem insertionBoundarySourceTape_normalizedOutput
    (pref tail insert : Word Bool) :
    Tape.normalizedOutput (insertionBoundarySourceTape pref tail insert) =
      List.append pref insert := by
  simp [insertionBoundarySourceTape, tapeAtCells_normalizedOutput,
    List.filterMap_append, List.map_reverse, Function.comp_def]

theorem scratchTape_normalizedOutput
    (insert : Word Bool) :
    Tape.normalizedOutput (scratchTape insert) = insert :=
  outputFromBits_normalizedOutput insert

theorem workTape_normalizedOutput
    (tail : Word Bool) :
    Tape.normalizedOutput (workTape tail) = tail :=
  outputFromBits_normalizedOutput tail

theorem finalScratchTape_normalizedOutput
    (insert : Word Bool) :
    Tape.normalizedOutput (finalScratchTape insert) = insert := by
  simp [finalScratchTape, tapeAtCells_normalizedOutput,
    List.filterMap_append, List.map_reverse, Function.comp_def]

theorem initialConfig_source_normalizedOutput
    (pref tail insert : Word Bool) :
    Tape.normalizedOutput
        (Description.tapeAt (initialConfig pref tail insert).tapes 0) =
      List.append pref (List.append tail insert) := by
  simpa [initialConfig] using
    sourceTape_normalizedOutput pref tail insert

theorem initialConfig_scratch_normalizedOutput
    (pref tail insert : Word Bool) :
    Tape.normalizedOutput
        (Description.tapeAt (initialConfig pref tail insert).tapes 1) =
      insert := by
  simpa [initialConfig] using
    scratchTape_normalizedOutput insert

theorem initialConfig_work_normalizedOutput
    (pref tail insert : Word Bool) :
    Tape.normalizedOutput
        (Description.tapeAt (initialConfig pref tail insert).tapes 2) =
      [] := by
  change Tape.normalizedOutput (outputFromBits []) = []
  exact outputFromBits_normalizedOutput []

theorem copyTailHandoffConfig_source_normalizedOutput
    (pref tail insert : Word Bool) :
    Tape.normalizedOutput
        (Description.tapeAt
          (copyTailHandoffConfig pref tail insert).tapes 0) =
      List.append pref insert := by
  simpa [copyTailHandoffConfig] using
    erasedTailSourceTape_normalizedOutput pref tail insert

theorem copyTailHandoffConfig_scratch_normalizedOutput
    (pref tail insert : Word Bool) :
    Tape.normalizedOutput
        (Description.tapeAt
          (copyTailHandoffConfig pref tail insert).tapes 1) =
      insert := by
  simpa [copyTailHandoffConfig] using
    scratchTape_normalizedOutput insert

theorem copyTailHandoffConfig_work_normalizedOutput
    (pref tail insert : Word Bool) :
    Tape.normalizedOutput
        (Description.tapeAt
          (copyTailHandoffConfig pref tail insert).tapes 2) =
      tail := by
  simpa [copyTailHandoffConfig] using
    outputFromBits_normalizedOutput tail

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
