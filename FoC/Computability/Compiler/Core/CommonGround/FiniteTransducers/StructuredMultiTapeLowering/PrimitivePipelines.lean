import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.CursorPipelines

set_option doc.verso true

/-!
# Structured primitive pipelines

This module wraps composed cursor pipelines as guarded physical primitive
contracts at canonical encoded block boundaries.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

private theorem atTapeSeparator_zero_eq
    {logical : List (Tape Bool)} {physical : Tape Bool}
    (hseparator : AtTapeSeparator logical 0 physical) :
    physical = encodedStructuredTapes logical := by
  rcases hseparator with ⟨_hle, hphysical⟩
  simpa [encodedStructuredTapes, tapeAtEncodedSplit,
    encodedPrefixBeforeTape, encodedSuffixFromTape] using hphysical

private theorem guardedAtExistingTapeSeparator_zero
    {logical : List (Tape Bool)}
    (hlogical : 0 < logical.length) :
    AtExistingTapeSeparator (guardLogicalTapes logical) 0
      (encodedGuardedStructuredTapes logical) := by
  cases logical with
  | nil =>
      simp at hlogical
  | cons T rest =>
      constructor
      · exact atTapeSeparator_zero_self
          (guardLogicalTapes (T :: rest))
      · simp [guardLogicalTapes]

private theorem atExistingTapeSeparator_zero_of_atHasGuardCells
    {logical : List (Tape Bool)}
    (hguards : LogicalTapeAtHasGuardCells logical 0) :
    AtExistingTapeSeparator logical 0
      (encodedStructuredTapes logical) := by
  rcases hguards with ⟨T, rest, hdrop, _hguard⟩
  constructor
  · exact atTapeSeparator_zero_self logical
  · exact ⟨T, rest, hdrop⟩

private theorem atExistingTapeSeparator_zero_of_atHasGuardCells_one
    {logical : List (Tape Bool)}
    (hguards : LogicalTapeAtHasGuardCells logical 1) :
    AtExistingTapeSeparator logical 0
      (encodedStructuredTapes logical) := by
  rcases hguards with ⟨U, rest, hdrop, _hguard⟩
  cases logical with
  | nil =>
      simp at hdrop
  | cons T tail =>
      exact
        ⟨atTapeSeparator_zero_self (T :: tail),
          ⟨T, tail, rfl⟩⟩

private theorem atExistingTapeSeparator_zero_of_atHasGuardCells_two
    {logical : List (Tape Bool)}
    (hguards : LogicalTapeAtHasGuardCells logical 2) :
    AtExistingTapeSeparator logical 0
      (encodedStructuredTapes logical) := by
  rcases hguards with ⟨V, rest, hdrop, _hguard⟩
  cases logical with
  | nil =>
      simp at hdrop
  | cons T tail =>
      exact
        ⟨atTapeSeparator_zero_self (T :: tail),
          ⟨T, tail, rfl⟩⟩

private theorem guardedDropOne_exists_of_one_lt
    {logical : List (Tape Bool)}
    (hlogical : 1 < logical.length) :
    exists T : Tape Bool, exists rest : List (Tape Bool),
      (guardLogicalTapes logical).drop 1 = T :: rest := by
  cases logical with
  | nil =>
      simp at hlogical
  | cons T rest =>
      cases rest with
      | nil =>
          simp at hlogical
      | cons U tail =>
          exact ⟨guardLogicalTape U, guardLogicalTapes tail, rfl⟩

private theorem guardedHasAtLeastThreeTapes_of_two_lt
    {logical : List (Tape Bool)}
    (hlogical : 2 < logical.length) :
    HasAtLeastThreeTapes (guardLogicalTapes logical) := by
  cases logical with
  | nil =>
      simp at hlogical
  | cons T rest =>
      cases rest with
      | nil =>
          simp at hlogical
      | cons U rest =>
          cases rest with
          | nil =>
              simp at hlogical
          | cons V tail =>
              exact
                ⟨guardLogicalTape T, guardLogicalTape U,
                  guardLogicalTape V, guardLogicalTapes tail, rfl⟩

private theorem guardedWriteHeadCell_zero_apply
    (cell : Option Bool) (logical : List (Tape Bool)) :
    (PhysicalPrimitive.writeHeadCell 0 cell).apply
        (guardLogicalTapes logical) =
      guardLogicalTapes
        ((PhysicalPrimitive.writeHeadCell 0 cell).apply logical) := by
  cases logical with
  | nil =>
      rfl
  | cons T rest =>
      simp [PhysicalPrimitive.apply, guardLogicalTapes,
        Description.tapeAt, guardLogicalTape_write]

private theorem guardedWriteHeadCell_one_apply
    (cell : Option Bool) (logical : List (Tape Bool)) :
    (PhysicalPrimitive.writeHeadCell 1 cell).apply
        (guardLogicalTapes logical) =
      guardLogicalTapes
        ((PhysicalPrimitive.writeHeadCell 1 cell).apply logical) := by
  cases logical with
  | nil =>
      rfl
  | cons T rest =>
      cases rest with
      | nil =>
          simp [PhysicalPrimitive.apply, guardLogicalTapes,
            Description.tapeAt]
      | cons U tail =>
          simp [PhysicalPrimitive.apply, guardLogicalTapes,
            Description.tapeAt, guardLogicalTape_write]

private theorem guardedWriteHeadCell_two_apply
    (cell : Option Bool) (logical : List (Tape Bool)) :
    (PhysicalPrimitive.writeHeadCell 2 cell).apply
        (guardLogicalTapes logical) =
      guardLogicalTapes
        ((PhysicalPrimitive.writeHeadCell 2 cell).apply logical) := by
  cases logical with
  | nil =>
      rfl
  | cons T rest =>
      cases rest with
      | nil =>
          simp [PhysicalPrimitive.apply, guardLogicalTapes,
            Description.tapeAt]
      | cons U rest =>
          cases rest with
          | nil =>
              simp [PhysicalPrimitive.apply, guardLogicalTapes,
                Description.tapeAt]
          | cons V tail =>
              simp [PhysicalPrimitive.apply, guardLogicalTapes,
                Description.tapeAt, guardLogicalTape_write]

/--
Guarded physical read-check primitive for tape 0.

This is the first non-noop primitive built from composed cursor pipelines.  It
checks the encoded guarded tape-0 head cell and returns to the canonical block
start.
-/
def readHeadCell0Description
    (expected : Option Bool) : MachineDescription :=
  cursorReadHeadCellAndReturnToSeparatorDescription expected

theorem readHeadCell0Description_physicalPrimitiveGuardedContract
    (expected : Option Bool) :
    PhysicalPrimitiveGuardedContract
      (PhysicalPrimitive.readHeadCell 0 expected)
      (readHeadCell0Description expected) where
  subroutineReady :=
    (cursorReadHeadCellAndReturnToSeparatorDescription_contract
      0 expected).subroutineReady
  realizes := by
    intro logical henabled
    rcases henabled with ⟨hlength, hread⟩
    have hsource :
        AtExistingTapeSeparator (guardLogicalTapes logical) 0
          (encodedGuardedStructuredTapes logical) ∧
          Tape.read
              (Description.tapeAt (guardLogicalTapes logical) 0) =
            expected := by
      constructor
      · exact guardedAtExistingTapeSeparator_zero hlength
      · simpa [tapeAt_guardLogicalTapes_read] using hread
    rcases
        (cursorReadHeadCellAndReturnToSeparatorDescription_contract
          0 expected).realizes
          (guardLogicalTapes logical)
          (encodedGuardedStructuredTapes logical)
          hsource with
      ⟨Tout, hhalts, hseparator⟩
    have hTout : Tout = encodedGuardedStructuredTapes logical :=
      atTapeSeparator_zero_eq hseparator
    simpa [readHeadCell0Description, PhysicalPrimitive.apply, hTout]
      using hhalts

theorem readHeadCell0Description_physicalPrimitiveGuardedContractEquiv
    (expected : Option Bool) :
    PhysicalPrimitiveGuardedContractEquiv
      (PhysicalPrimitive.readHeadCell 0 expected)
      (readHeadCell0Description expected) :=
  (readHeadCell0Description_physicalPrimitiveGuardedContract
    expected).toEquiv

/--
Guarded physical write primitive for tape 0.

The composed cursor pipeline overwrites the guarded tape-0 head-cell code and
returns to the canonical block start.  The endpoint is exact because
{name}`guardLogicalTape_write` commutes guarding with the logical write.
-/
def writeHeadCell0Description
    (cell : Option Bool) : MachineDescription :=
  cursorWriteHeadCellAndReturnToSeparatorDescription cell

theorem writeHeadCell0Description_physicalPrimitiveGuardedContract
    (cell : Option Bool) :
    PhysicalPrimitiveGuardedContract
      (PhysicalPrimitive.writeHeadCell 0 cell)
      (writeHeadCell0Description cell) where
  subroutineReady :=
    (cursorWriteHeadCellAndReturnToSeparatorDescription_contract
      0 cell).subroutineReady
  realizes := by
    intro logical henabled
    have hsource :
        AtExistingTapeSeparator (guardLogicalTapes logical) 0
          (encodedGuardedStructuredTapes logical) :=
      guardedAtExistingTapeSeparator_zero henabled
    rcases
        (cursorWriteHeadCellAndReturnToSeparatorDescription_contract
          0 cell).realizes
          (guardLogicalTapes logical)
          (encodedGuardedStructuredTapes logical)
          hsource with
      ⟨Tout, hhalts, hseparator⟩
    have hTout :
        Tout =
          encodedStructuredTapes
            ((PhysicalPrimitive.writeHeadCell 0 cell).apply
              (guardLogicalTapes logical)) :=
      atTapeSeparator_zero_eq hseparator
    have hguard :
        encodedStructuredTapes
            ((PhysicalPrimitive.writeHeadCell 0 cell).apply
              (guardLogicalTapes logical)) =
          encodedGuardedStructuredTapes
            ((PhysicalPrimitive.writeHeadCell 0 cell).apply
              logical) := by
      simp [encodedGuardedStructuredTapes,
        guardedWriteHeadCell_zero_apply]
    simpa [writeHeadCell0Description, hTout, hguard]
      using hhalts

theorem writeHeadCell0Description_physicalPrimitiveGuardedContractEquiv
    (cell : Option Bool) :
    PhysicalPrimitiveGuardedContractEquiv
      (PhysicalPrimitive.writeHeadCell 0 cell)
      (writeHeadCell0Description cell) :=
  (writeHeadCell0Description_physicalPrimitiveGuardedContract cell).toEquiv

/--
Guarded physical stay-move primitive for tape 0.

Structured stay does not move the logical head, so the physical implementation
is the block-start no-op.
-/
def moveHead0StayDescription : MachineDescription :=
  cursorNoopDescription

theorem moveHead0StayDescription_physicalPrimitiveGuardedContract :
    PhysicalPrimitiveGuardedContract
      (PhysicalPrimitive.moveHead 0 HeadMove.stay)
      moveHead0StayDescription where
  subroutineReady := cursorNoopDescription_subroutineReady
  realizes := by
    intro logical henabled
    cases logical with
    | nil =>
        simp at henabled
    | cons T rest =>
        simpa [moveHead0StayDescription, PhysicalPrimitive.apply,
          Description.tapeAt, HeadMove.apply] using
          cursorNoopDescription_haltsFromTape
            (encodedGuardedStructuredTapes (T :: rest))

theorem moveHead0StayDescription_physicalPrimitiveGuardedContractEquiv :
    PhysicalPrimitiveGuardedContractEquiv
      (PhysicalPrimitive.moveHead 0 HeadMove.stay)
      moveHead0StayDescription :=
  moveHead0StayDescription_physicalPrimitiveGuardedContract.toEquiv

/--
Guarded local left-move primitive for tape 0.

The machine performs the real marker swap and returns to block start, but its
endpoint is the encoded consumed-guard tape list.  The contract therefore uses
{name}`PhysicalPrimitiveGuardedLogicalEquivContract` rather than pretending the
raw one-tape output is equivalent to the canonical re-guarded encoding.
-/
def moveHead0LeftLocalDescription : MachineDescription :=
  cursorMoveHeadLeftLocalAndReturnToSeparatorDescription

theorem moveHead0LeftLocalDescription_physicalPrimitiveGuardedLogicalEquivContract :
    PhysicalPrimitiveGuardedLogicalEquivContract
      (PhysicalPrimitive.moveHead 0 HeadMove.left)
      moveHead0LeftLocalDescription where
  subroutineReady :=
    (cursorMoveHeadLeftLocalAndReturnToSeparatorDescription_contract_guarded
      0).subroutineReady
  realizes := by
    intro logical henabled
    have hsource :
        AtExistingTapeSeparator (guardLogicalTapes logical) 0
          (encodedGuardedStructuredTapes logical) :=
      guardedAtExistingTapeSeparator_zero henabled
    rcases
        (cursorMoveHeadLeftLocalAndReturnToSeparatorDescription_contract_guarded
          0).realizes logical
          (encodedGuardedStructuredTapes logical) hsource with
      ⟨Tout, hhalts, hseparator⟩
    let actual :=
      (PhysicalPrimitive.moveHead 0 HeadMove.left).apply
        (guardLogicalTapes logical)
    refine ⟨actual, ?_, ?_⟩
    · exact
        PhysicalPrimitive.apply_guardLogicalTapes_equiv
          (PhysicalPrimitive.moveHead 0 HeadMove.left) logical
    · have hTout : Tout = encodedStructuredTapes actual :=
        atTapeSeparator_zero_eq hseparator
      simpa [moveHead0LeftLocalDescription, actual, hTout]
        using hhalts

theorem moveHead0LeftLocalDescription_haltsFromEncodedStructuredTapes_of_guardCells
    (logical : List (Tape Bool))
    (hguards : LogicalTapeAtHasGuardCells logical 0) :
    moveHead0LeftLocalDescription.HaltsFromTape
      (encodedStructuredTapes logical)
      (encodedStructuredTapes
        ((PhysicalPrimitive.moveHead 0 HeadMove.left).apply logical)) := by
  rcases
      (cursorMoveHeadLeftLocalAndReturnToSeparatorDescription_contract_withGuardCells
        0).realizes logical (encodedStructuredTapes logical)
        ⟨hguards, atExistingTapeSeparator_zero_of_atHasGuardCells hguards⟩
    with ⟨Tout, hhalts, hseparator⟩
  have hTout :
      Tout =
        encodedStructuredTapes
          ((PhysicalPrimitive.moveHead 0 HeadMove.left).apply logical) :=
    atTapeSeparator_zero_eq hseparator
  simpa [moveHead0LeftLocalDescription, hTout] using hhalts

/--
Guarded local right-move primitive for tape 0.

This mirrors {name}`moveHead0LeftLocalDescription` and exposes the same
consumed-guard endpoint relation.
-/
def moveHead0RightLocalDescription : MachineDescription :=
  cursorMoveHeadRightLocalAndReturnToSeparatorDescription

theorem moveHead0RightLocalDescription_physicalPrimitiveGuardedLogicalEquivContract :
    PhysicalPrimitiveGuardedLogicalEquivContract
      (PhysicalPrimitive.moveHead 0 HeadMove.right)
      moveHead0RightLocalDescription where
  subroutineReady :=
    (cursorMoveHeadRightLocalAndReturnToSeparatorDescription_contract_guarded
      0).subroutineReady
  realizes := by
    intro logical henabled
    have hsource :
        AtExistingTapeSeparator (guardLogicalTapes logical) 0
          (encodedGuardedStructuredTapes logical) :=
      guardedAtExistingTapeSeparator_zero henabled
    rcases
        (cursorMoveHeadRightLocalAndReturnToSeparatorDescription_contract_guarded
          0).realizes logical
          (encodedGuardedStructuredTapes logical) hsource with
      ⟨Tout, hhalts, hseparator⟩
    let actual :=
      (PhysicalPrimitive.moveHead 0 HeadMove.right).apply
        (guardLogicalTapes logical)
    refine ⟨actual, ?_, ?_⟩
    · exact
        PhysicalPrimitive.apply_guardLogicalTapes_equiv
          (PhysicalPrimitive.moveHead 0 HeadMove.right) logical
    · have hTout : Tout = encodedStructuredTapes actual :=
        atTapeSeparator_zero_eq hseparator
      simpa [moveHead0RightLocalDescription, actual, hTout]
        using hhalts

theorem moveHead0RightLocalDescription_haltsFromEncodedStructuredTapes_of_guardCells
    (logical : List (Tape Bool))
    (hguards : LogicalTapeAtHasGuardCells logical 0) :
    moveHead0RightLocalDescription.HaltsFromTape
      (encodedStructuredTapes logical)
      (encodedStructuredTapes
        ((PhysicalPrimitive.moveHead 0 HeadMove.right).apply logical)) := by
  rcases
      (cursorMoveHeadRightLocalAndReturnToSeparatorDescription_contract_withGuardCells
        0).realizes logical (encodedStructuredTapes logical)
        ⟨hguards, atExistingTapeSeparator_zero_of_atHasGuardCells hguards⟩
    with ⟨Tout, hhalts, hseparator⟩
  have hTout :
      Tout =
        encodedStructuredTapes
          ((PhysicalPrimitive.moveHead 0 HeadMove.right).apply logical) :=
    atTapeSeparator_zero_eq hseparator
  simpa [moveHead0RightLocalDescription, hTout] using hhalts

/--
Guarded local left-move primitive for tape 1.

As with tape 0, the endpoint physically encodes the consumed-guard tape list
and is related to the represented target by pointwise logical tape equivalence.
-/
def moveHead1LeftLocalDescription : MachineDescription :=
  cursorTape1MoveHeadLeftLocalAndReturnToBlockStartDescription

theorem moveHead1LeftLocalDescription_physicalPrimitiveGuardedLogicalEquivContract :
    PhysicalPrimitiveGuardedLogicalEquivContract
      (PhysicalPrimitive.moveHead 1 HeadMove.left)
      moveHead1LeftLocalDescription where
  subroutineReady :=
    cursorTape1MoveHeadLeftLocalAndReturnToBlockStartDescription_contract_guarded
      |>.subroutineReady
  realizes := by
    intro logical henabled
    have hzero : 0 < logical.length :=
      Nat.lt_trans (by decide : 0 < 1) henabled
    have hsource :
        AtExistingTapeSeparator (guardLogicalTapes logical) 0
            (encodedGuardedStructuredTapes logical) ∧
          (exists T : Tape Bool, exists rest : List (Tape Bool),
            (guardLogicalTapes logical).drop 1 = T :: rest) := by
      exact
        ⟨guardedAtExistingTapeSeparator_zero hzero,
          guardedDropOne_exists_of_one_lt henabled⟩
    rcases
        cursorTape1MoveHeadLeftLocalAndReturnToBlockStartDescription_contract_guarded
          |>.realizes logical
            (encodedGuardedStructuredTapes logical) hsource with
      ⟨Tout, hhalts, hseparator⟩
    let actual :=
      (PhysicalPrimitive.moveHead 1 HeadMove.left).apply
        (guardLogicalTapes logical)
    refine ⟨actual, ?_, ?_⟩
    · exact
        PhysicalPrimitive.apply_guardLogicalTapes_equiv
          (PhysicalPrimitive.moveHead 1 HeadMove.left) logical
    · have hTout : Tout = encodedStructuredTapes actual :=
        atTapeSeparator_zero_eq hseparator
      simpa [moveHead1LeftLocalDescription, actual, hTout]
        using hhalts

theorem moveHead1LeftLocalDescription_haltsFromEncodedStructuredTapes_of_guardCells
    (logical : List (Tape Bool))
    (hguards : LogicalTapeAtHasGuardCells logical 1) :
    moveHead1LeftLocalDescription.HaltsFromTape
      (encodedStructuredTapes logical)
      (encodedStructuredTapes
        ((PhysicalPrimitive.moveHead 1 HeadMove.left).apply logical)) := by
  rcases
      cursorTape1MoveHeadLeftLocalAndReturnToBlockStartDescription_contract_withGuardCells
        |>.realizes logical (encodedStructuredTapes logical)
          ⟨hguards,
            atExistingTapeSeparator_zero_of_atHasGuardCells_one
              hguards⟩
    with ⟨Tout, hhalts, hseparator⟩
  have hTout :
      Tout =
        encodedStructuredTapes
          ((PhysicalPrimitive.moveHead 1 HeadMove.left).apply logical) :=
    atTapeSeparator_zero_eq hseparator
  simpa [moveHead1LeftLocalDescription, hTout] using hhalts

/--
Guarded local right-move primitive for tape 1.
-/
def moveHead1RightLocalDescription : MachineDescription :=
  cursorTape1MoveHeadRightLocalAndReturnToBlockStartDescription

theorem moveHead1RightLocalDescription_physicalPrimitiveGuardedLogicalEquivContract :
    PhysicalPrimitiveGuardedLogicalEquivContract
      (PhysicalPrimitive.moveHead 1 HeadMove.right)
      moveHead1RightLocalDescription where
  subroutineReady :=
    cursorTape1MoveHeadRightLocalAndReturnToBlockStartDescription_contract_guarded
      |>.subroutineReady
  realizes := by
    intro logical henabled
    have hzero : 0 < logical.length :=
      Nat.lt_trans (by decide : 0 < 1) henabled
    have hsource :
        AtExistingTapeSeparator (guardLogicalTapes logical) 0
            (encodedGuardedStructuredTapes logical) ∧
          (exists T : Tape Bool, exists rest : List (Tape Bool),
            (guardLogicalTapes logical).drop 1 = T :: rest) := by
      exact
        ⟨guardedAtExistingTapeSeparator_zero hzero,
          guardedDropOne_exists_of_one_lt henabled⟩
    rcases
        cursorTape1MoveHeadRightLocalAndReturnToBlockStartDescription_contract_guarded
          |>.realizes logical
            (encodedGuardedStructuredTapes logical) hsource with
      ⟨Tout, hhalts, hseparator⟩
    let actual :=
      (PhysicalPrimitive.moveHead 1 HeadMove.right).apply
        (guardLogicalTapes logical)
    refine ⟨actual, ?_, ?_⟩
    · exact
        PhysicalPrimitive.apply_guardLogicalTapes_equiv
          (PhysicalPrimitive.moveHead 1 HeadMove.right) logical
    · have hTout : Tout = encodedStructuredTapes actual :=
        atTapeSeparator_zero_eq hseparator
      simpa [moveHead1RightLocalDescription, actual, hTout]
        using hhalts

theorem moveHead1RightLocalDescription_haltsFromEncodedStructuredTapes_of_guardCells
    (logical : List (Tape Bool))
    (hguards : LogicalTapeAtHasGuardCells logical 1) :
    moveHead1RightLocalDescription.HaltsFromTape
      (encodedStructuredTapes logical)
      (encodedStructuredTapes
        ((PhysicalPrimitive.moveHead 1 HeadMove.right).apply logical)) := by
  rcases
      cursorTape1MoveHeadRightLocalAndReturnToBlockStartDescription_contract_withGuardCells
        |>.realizes logical (encodedStructuredTapes logical)
          ⟨hguards,
            atExistingTapeSeparator_zero_of_atHasGuardCells_one
              hguards⟩
    with ⟨Tout, hhalts, hseparator⟩
  have hTout :
      Tout =
        encodedStructuredTapes
          ((PhysicalPrimitive.moveHead 1 HeadMove.right).apply logical) :=
    atTapeSeparator_zero_eq hseparator
  simpa [moveHead1RightLocalDescription, hTout] using hhalts

/--
Guarded local left-move primitive for tape 2.

The physical pipeline seeks to tape 2, performs the local marker swap, returns
through tape 1, and halts at the canonical block-start separator.
-/
def moveHead2LeftLocalDescription : MachineDescription :=
  cursorTape2MoveHeadLeftLocalAndReturnToBlockStartDescription

theorem moveHead2LeftLocalDescription_physicalPrimitiveGuardedLogicalEquivContract :
    PhysicalPrimitiveGuardedLogicalEquivContract
      (PhysicalPrimitive.moveHead 2 HeadMove.left)
      moveHead2LeftLocalDescription where
  subroutineReady :=
    cursorTape2MoveHeadLeftLocalAndReturnToBlockStartDescription_contract_guarded
      |>.subroutineReady
  realizes := by
    intro logical henabled
    have hzero : 0 < logical.length :=
      Nat.lt_trans (by decide : 0 < 2) henabled
    have hsource :
        AtExistingTapeSeparator (guardLogicalTapes logical) 0
            (encodedGuardedStructuredTapes logical) ∧
          HasAtLeastThreeTapes (guardLogicalTapes logical) := by
      exact
        ⟨guardedAtExistingTapeSeparator_zero hzero,
          guardedHasAtLeastThreeTapes_of_two_lt henabled⟩
    rcases
        cursorTape2MoveHeadLeftLocalAndReturnToBlockStartDescription_contract_guarded
          |>.realizes logical
            (encodedGuardedStructuredTapes logical) hsource with
      ⟨Tout, hhalts, hseparator⟩
    let actual :=
      (PhysicalPrimitive.moveHead 2 HeadMove.left).apply
        (guardLogicalTapes logical)
    refine ⟨actual, ?_, ?_⟩
    · exact
        PhysicalPrimitive.apply_guardLogicalTapes_equiv
          (PhysicalPrimitive.moveHead 2 HeadMove.left) logical
    · have hTout : Tout = encodedStructuredTapes actual :=
        atTapeSeparator_zero_eq hseparator
      simpa [moveHead2LeftLocalDescription, actual, hTout]
        using hhalts

theorem moveHead2LeftLocalDescription_haltsFromEncodedStructuredTapes_of_guardCells
    (logical : List (Tape Bool))
    (hguards : LogicalTapeAtHasGuardCells logical 2) :
    moveHead2LeftLocalDescription.HaltsFromTape
      (encodedStructuredTapes logical)
      (encodedStructuredTapes
        ((PhysicalPrimitive.moveHead 2 HeadMove.left).apply logical)) := by
  rcases
      cursorTape2MoveHeadLeftLocalAndReturnToBlockStartDescription_contract_withGuardCells
        |>.realizes logical (encodedStructuredTapes logical)
          ⟨hguards,
            atExistingTapeSeparator_zero_of_atHasGuardCells_two
              hguards⟩
    with ⟨Tout, hhalts, hseparator⟩
  have hTout :
      Tout =
        encodedStructuredTapes
          ((PhysicalPrimitive.moveHead 2 HeadMove.left).apply logical) :=
    atTapeSeparator_zero_eq hseparator
  simpa [moveHead2LeftLocalDescription, hTout] using hhalts

/--
Guarded local right-move primitive for tape 2.
-/
def moveHead2RightLocalDescription : MachineDescription :=
  cursorTape2MoveHeadRightLocalAndReturnToBlockStartDescription

theorem moveHead2RightLocalDescription_physicalPrimitiveGuardedLogicalEquivContract :
    PhysicalPrimitiveGuardedLogicalEquivContract
      (PhysicalPrimitive.moveHead 2 HeadMove.right)
      moveHead2RightLocalDescription where
  subroutineReady :=
    cursorTape2MoveHeadRightLocalAndReturnToBlockStartDescription_contract_guarded
      |>.subroutineReady
  realizes := by
    intro logical henabled
    have hzero : 0 < logical.length :=
      Nat.lt_trans (by decide : 0 < 2) henabled
    have hsource :
        AtExistingTapeSeparator (guardLogicalTapes logical) 0
            (encodedGuardedStructuredTapes logical) ∧
          HasAtLeastThreeTapes (guardLogicalTapes logical) := by
      exact
        ⟨guardedAtExistingTapeSeparator_zero hzero,
          guardedHasAtLeastThreeTapes_of_two_lt henabled⟩
    rcases
        cursorTape2MoveHeadRightLocalAndReturnToBlockStartDescription_contract_guarded
          |>.realizes logical
            (encodedGuardedStructuredTapes logical) hsource with
      ⟨Tout, hhalts, hseparator⟩
    let actual :=
      (PhysicalPrimitive.moveHead 2 HeadMove.right).apply
        (guardLogicalTapes logical)
    refine ⟨actual, ?_, ?_⟩
    · exact
        PhysicalPrimitive.apply_guardLogicalTapes_equiv
          (PhysicalPrimitive.moveHead 2 HeadMove.right) logical
    · have hTout : Tout = encodedStructuredTapes actual :=
        atTapeSeparator_zero_eq hseparator
      simpa [moveHead2RightLocalDescription, actual, hTout]
        using hhalts

theorem moveHead2RightLocalDescription_haltsFromEncodedStructuredTapes_of_guardCells
    (logical : List (Tape Bool))
    (hguards : LogicalTapeAtHasGuardCells logical 2) :
    moveHead2RightLocalDescription.HaltsFromTape
      (encodedStructuredTapes logical)
      (encodedStructuredTapes
        ((PhysicalPrimitive.moveHead 2 HeadMove.right).apply logical)) := by
  rcases
      cursorTape2MoveHeadRightLocalAndReturnToBlockStartDescription_contract_withGuardCells
        |>.realizes logical (encodedStructuredTapes logical)
          ⟨hguards,
            atExistingTapeSeparator_zero_of_atHasGuardCells_two
              hguards⟩
    with ⟨Tout, hhalts, hseparator⟩
  have hTout :
      Tout =
        encodedStructuredTapes
          ((PhysicalPrimitive.moveHead 2 HeadMove.right).apply logical) :=
    atTapeSeparator_zero_eq hseparator
  simpa [moveHead2RightLocalDescription, hTout] using hhalts

private theorem actionPrimitivesAt_zero_enabled
    {logical : List (Tape Bool)}
    {write? : Option (Option Bool)} {move : HeadMove}
    (henabled :
      physicalPrimitiveSequenceEnabled
        (actionPrimitivesAt 0 { write? := write?, move := move })
        logical) :
    0 < logical.length := by
  cases write? <;>
    simpa [actionPrimitivesAt, writePrimitivesForAction]
      using henabled.left

private theorem encodedGuardedStructuredTapes_bounce_zero
    (logical : List (Tape Bool))
    (hlength : 0 < logical.length) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (encodedGuardedStructuredTapes logical)) =
      encodedGuardedStructuredTapes logical :=
  atExistingTapeSeparator_moveLeft_moveRight
    (guardedAtExistingTapeSeparator_zero hlength)

/--
Tape-0 action fragment for a local left move, with an optional write first.

This covers the non-stay action shape at the logical-equivalence endpoint.  It
does not yet export the canonical guarded endpoint required by the existing row
bridge.
-/
def action0LeftLocalDescription
    (write? : Option (Option Bool)) : MachineDescription :=
  match write? with
  | none => moveHead0LeftLocalDescription
  | some cell =>
      canonicalPrimitiveSeqDescription
        (writeHeadCell0Description cell)
        moveHead0LeftLocalDescription

theorem action0LeftLocalDescription_physicalPrimitiveSequenceGuardedLogicalEquivContract
    (write? : Option (Option Bool)) :
    PhysicalPrimitiveSequenceGuardedLogicalEquivContract
      (actionPrimitivesAt 0 { write? := write?, move := HeadMove.left })
      (action0LeftLocalDescription write?) := by
  constructor
  · cases write? with
    | none =>
        exact
          moveHead0LeftLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
            |>.subroutineReady
    | some cell =>
        exact
          canonicalPrimitiveSeqDescription_subroutineReady
            (writeHeadCell0Description_physicalPrimitiveGuardedContract
              cell |>.subroutineReady)
            (moveHead0LeftLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
              |>.subroutineReady)
  · intro logical henabled
    have hlength : 0 < logical.length :=
      actionPrimitivesAt_zero_enabled henabled
    cases write? with
    | none =>
        rcases
            moveHead0LeftLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
              |>.realizes logical hlength with
          ⟨actual, hactual, hhalts⟩
        refine ⟨actual, ?_, ?_⟩
        · simpa [actionPrimitivesAt, writePrimitivesForAction,
            PhysicalPrimitive.apply] using hactual
        · simpa [action0LeftLocalDescription] using hhalts
    | some cell =>
        let written :=
          (PhysicalPrimitive.writeHeadCell 0 cell).apply logical
        have hwrite :=
          (writeHeadCell0Description_physicalPrimitiveGuardedContract
            cell).realizes logical hlength
        have hlengthWritten : 0 < written.length := by
          simpa [written, PhysicalPrimitive.apply] using hlength
        rcases
            moveHead0LeftLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
              |>.realizes written hlengthWritten with
          ⟨actual, hactual, hmoveHalts⟩
        refine ⟨actual, ?_, ?_⟩
        · simpa [actionPrimitivesAt, writePrimitivesForAction,
            written, PhysicalPrimitive.apply] using hactual
        · have hbounce :=
            encodedGuardedStructuredTapes_bounce_zero
              written hlengthWritten
          have hmoveFromBounce :
              moveHead0LeftLocalDescription.HaltsFromTape
                (Tape.move Direction.left
                  (Tape.move Direction.right
                    (encodedGuardedStructuredTapes written)))
                (encodedStructuredTapes actual) := by
            rw [hbounce]
            exact hmoveHalts
          simpa [action0LeftLocalDescription, written] using
            canonicalPrimitiveSeqDescription_haltsFromTape_of_haltsFromTape
              (writeHeadCell0Description_physicalPrimitiveGuardedContract
                cell |>.subroutineReady)
              (moveHead0LeftLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
                |>.subroutineReady)
              hwrite hmoveFromBounce

/--
Tape-0 action fragment for a local right move, with an optional write first.
-/
def action0RightLocalDescription
    (write? : Option (Option Bool)) : MachineDescription :=
  match write? with
  | none => moveHead0RightLocalDescription
  | some cell =>
      canonicalPrimitiveSeqDescription
        (writeHeadCell0Description cell)
        moveHead0RightLocalDescription

theorem action0RightLocalDescription_physicalPrimitiveSequenceGuardedLogicalEquivContract
    (write? : Option (Option Bool)) :
    PhysicalPrimitiveSequenceGuardedLogicalEquivContract
      (actionPrimitivesAt 0 { write? := write?, move := HeadMove.right })
      (action0RightLocalDescription write?) := by
  constructor
  · cases write? with
    | none =>
        exact
          moveHead0RightLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
            |>.subroutineReady
    | some cell =>
        exact
          canonicalPrimitiveSeqDescription_subroutineReady
            (writeHeadCell0Description_physicalPrimitiveGuardedContract
              cell |>.subroutineReady)
            (moveHead0RightLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
              |>.subroutineReady)
  · intro logical henabled
    have hlength : 0 < logical.length :=
      actionPrimitivesAt_zero_enabled henabled
    cases write? with
    | none =>
        rcases
            moveHead0RightLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
              |>.realizes logical hlength with
          ⟨actual, hactual, hhalts⟩
        refine ⟨actual, ?_, ?_⟩
        · simpa [actionPrimitivesAt, writePrimitivesForAction,
            PhysicalPrimitive.apply] using hactual
        · simpa [action0RightLocalDescription] using hhalts
    | some cell =>
        let written :=
          (PhysicalPrimitive.writeHeadCell 0 cell).apply logical
        have hwrite :=
          (writeHeadCell0Description_physicalPrimitiveGuardedContract
            cell).realizes logical hlength
        have hlengthWritten : 0 < written.length := by
          simpa [written, PhysicalPrimitive.apply] using hlength
        rcases
            moveHead0RightLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
              |>.realizes written hlengthWritten with
          ⟨actual, hactual, hmoveHalts⟩
        refine ⟨actual, ?_, ?_⟩
        · simpa [actionPrimitivesAt, writePrimitivesForAction,
            written, PhysicalPrimitive.apply] using hactual
        · have hbounce :=
            encodedGuardedStructuredTapes_bounce_zero
              written hlengthWritten
          have hmoveFromBounce :
              moveHead0RightLocalDescription.HaltsFromTape
                (Tape.move Direction.left
                  (Tape.move Direction.right
                    (encodedGuardedStructuredTapes written)))
                (encodedStructuredTapes actual) := by
            rw [hbounce]
            exact hmoveHalts
          simpa [action0RightLocalDescription, written] using
            canonicalPrimitiveSeqDescription_haltsFromTape_of_haltsFromTape
              (writeHeadCell0Description_physicalPrimitiveGuardedContract
                cell |>.subroutineReady)
              (moveHead0RightLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
                |>.subroutineReady)
              hwrite hmoveFromBounce

/--
Complete guarded tape-0 read-check sequence:
seek tape 0, verify the expected head cell, then return to block start.
-/
def readCheck0Description
    (expected : Option Bool) : MachineDescription :=
  canonicalPrimitiveSeqDescription
    (canonicalPrimitiveSeqDescription
      seekTape0Description
      (readHeadCell0Description expected))
    returnBlockStartNoopDescription

theorem readCheck0Description_physicalPrimitiveSequenceGuardedContractEquiv
    (expected : Option Bool) :
    PhysicalPrimitiveSequenceGuardedContractEquiv
      (readCheckPrimitivesAt 0 expected)
      (readCheck0Description expected) := by
  have hseek :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        [PhysicalPrimitive.seekTape 0] seekTape0Description :=
    seekTape0Description_physicalPrimitiveGuardedContract.toSequenceEquiv
  have hread :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        [PhysicalPrimitive.readHeadCell 0 expected]
        (readHeadCell0Description expected) :=
    (readHeadCell0Description_physicalPrimitiveGuardedContract
      expected).toSequenceEquiv
  have hreturn :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        [PhysicalPrimitive.returnToBlockStart]
        returnBlockStartNoopDescription :=
    returnBlockStartNoopDescription_physicalPrimitiveGuardedContract
      |>.toSequenceEquiv
  have hfirst :=
    physicalPrimitiveSequenceGuardedContractEquiv_append
      hseek hread
  have hall :=
    physicalPrimitiveSequenceGuardedContractEquiv_append
      hfirst hreturn
  simpa [readCheck0Description, readCheckPrimitivesAt]
    using hall

/--
Complete guarded tape-1 read-check sequence:
seek tape 1, verify the expected head cell, then return to block start.

Unlike tape 0, this is a whole-pipeline contract: the intermediate tape-1
separator is not a canonical endpoint for standalone primitive contracts.
-/
def readCheck1Description
    (expected : Option Bool) : MachineDescription :=
  cursorTape1ReadHeadCellAndReturnToBlockStartDescription expected

private theorem readCheckPrimitivesAt_one_enabled
    {logical : List (Tape Bool)} {expected : Option Bool}
    (henabled :
      physicalPrimitiveSequenceEnabled
        (readCheckPrimitivesAt 1 expected) logical) :
    1 < logical.length ∧
      Tape.read (Description.tapeAt logical 1) = expected := by
  simpa [readCheckPrimitivesAt, PhysicalPrimitive.apply] using henabled

theorem readCheck1Description_physicalPrimitiveSequenceGuardedContractEquiv
    (expected : Option Bool) :
    PhysicalPrimitiveSequenceGuardedContractEquiv
      (readCheckPrimitivesAt 1 expected)
      (readCheck1Description expected) := by
  constructor
  · exact
      (cursorTape1ReadHeadCellAndReturnToBlockStartDescription_contract
        expected).subroutineReady
  ·
    intro logical henabled
    rcases readCheckPrimitivesAt_one_enabled henabled with
      ⟨hlength, hread⟩
    have hzero : 0 < logical.length :=
      Nat.lt_trans (by decide : 0 < 1) hlength
    have hsource :
        AtExistingTapeSeparator (guardLogicalTapes logical) 0
            (encodedGuardedStructuredTapes logical) ∧
          (exists T : Tape Bool, exists rest : List (Tape Bool),
            (guardLogicalTapes logical).drop 1 = T :: rest) ∧
          Tape.read
              (Description.tapeAt (guardLogicalTapes logical) 1) =
            expected := by
      exact
        ⟨guardedAtExistingTapeSeparator_zero hzero,
          guardedDropOne_exists_of_one_lt hlength,
          by simpa [tapeAt_guardLogicalTapes_read] using hread⟩
    rcases
        (cursorTape1ReadHeadCellAndReturnToBlockStartDescription_contract
          expected).realizes
          (guardLogicalTapes logical)
          (encodedGuardedStructuredTapes logical)
          hsource with
      ⟨Tout, hhalts, hseparator⟩
    have hTout : Tout = encodedGuardedStructuredTapes logical :=
      atTapeSeparator_zero_eq hseparator
    exact
      MachineDescription.HaltsFromTape.toEquiv
        (by
          simpa [readCheck1Description, hTout, readCheckPrimitivesAt]
            using hhalts)

/--
Complete guarded tape-2 read-check sequence:
seek tape 2, verify the expected head cell, then return to block start.
-/
def readCheck2Description
    (expected : Option Bool) : MachineDescription :=
  cursorTape2ReadHeadCellAndReturnToBlockStartDescription expected

private theorem readCheckPrimitivesAt_two_enabled
    {logical : List (Tape Bool)} {expected : Option Bool}
    (henabled :
      physicalPrimitiveSequenceEnabled
        (readCheckPrimitivesAt 2 expected) logical) :
    2 < logical.length ∧
      Tape.read (Description.tapeAt logical 2) = expected := by
  simpa [readCheckPrimitivesAt, PhysicalPrimitive.apply] using henabled

theorem readCheck2Description_physicalPrimitiveSequenceGuardedContractEquiv
    (expected : Option Bool) :
    PhysicalPrimitiveSequenceGuardedContractEquiv
      (readCheckPrimitivesAt 2 expected)
      (readCheck2Description expected) := by
  constructor
  · exact
      (cursorTape2ReadHeadCellAndReturnToBlockStartDescription_contract
        expected).subroutineReady
  ·
    intro logical henabled
    rcases readCheckPrimitivesAt_two_enabled henabled with
      ⟨hlength, hread⟩
    have hzero : 0 < logical.length :=
      Nat.lt_trans (by decide : 0 < 2) hlength
    have hsource :
        AtExistingTapeSeparator (guardLogicalTapes logical) 0
            (encodedGuardedStructuredTapes logical) ∧
          HasAtLeastThreeTapes (guardLogicalTapes logical) ∧
          Tape.read
              (Description.tapeAt (guardLogicalTapes logical) 2) =
            expected := by
      exact
        ⟨guardedAtExistingTapeSeparator_zero hzero,
          guardedHasAtLeastThreeTapes_of_two_lt hlength,
          by simpa [tapeAt_guardLogicalTapes_read] using hread⟩
    rcases
        (cursorTape2ReadHeadCellAndReturnToBlockStartDescription_contract
          expected).realizes
          (guardLogicalTapes logical)
          (encodedGuardedStructuredTapes logical)
          hsource with
      ⟨Tout, hhalts, hseparator⟩
    have hTout : Tout = encodedGuardedStructuredTapes logical :=
      atTapeSeparator_zero_eq hseparator
    exact
      MachineDescription.HaltsFromTape.toEquiv
        (by
          simpa [readCheck2Description, hTout, readCheckPrimitivesAt]
            using hhalts)

/--
Complete guarded tape-0 stay-action sequence.

The optional write is applied at the encoded tape-0 head cell, then the
structured {lit}`stay` move and block-start return are both physical no-ops.  The
contract is stated as an equivalence contract so it composes with the guarded
row-lowering path even when neighbouring pieces use stay-compiled handoffs.
-/
def action0StayDescription
    (write? : Option (Option Bool)) : MachineDescription :=
  match write? with
  | none =>
      canonicalPrimitiveSeqDescription
        (canonicalPrimitiveSeqDescription
          seekTape0Description
          moveHead0StayDescription)
        returnBlockStartNoopDescription
  | some cell =>
      canonicalPrimitiveSeqDescription
        (canonicalPrimitiveSeqDescription
          (canonicalPrimitiveSeqDescription
            seekTape0Description
            (writeHeadCell0Description cell))
          moveHead0StayDescription)
        returnBlockStartNoopDescription

theorem action0StayDescription_physicalPrimitiveSequenceGuardedContractEquiv
    (write? : Option (Option Bool)) :
    PhysicalPrimitiveSequenceGuardedContractEquiv
      (actionPrimitivesAt 0 { write? := write?, move := HeadMove.stay })
      (action0StayDescription write?) := by
  have hseek :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        [PhysicalPrimitive.seekTape 0] seekTape0Description :=
    seekTape0Description_physicalPrimitiveGuardedContract.toSequenceEquiv
  have hmove :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        [PhysicalPrimitive.moveHead 0 HeadMove.stay]
        moveHead0StayDescription :=
    moveHead0StayDescription_physicalPrimitiveGuardedContract
      |>.toSequenceEquiv
  have hreturn :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        [PhysicalPrimitive.returnToBlockStart]
        returnBlockStartNoopDescription :=
    returnBlockStartNoopDescription_physicalPrimitiveGuardedContract
      |>.toSequenceEquiv
  cases write? with
  | none =>
      have hfirst :=
        physicalPrimitiveSequenceGuardedContractEquiv_append
          hseek hmove
      have hall :=
        physicalPrimitiveSequenceGuardedContractEquiv_append
          hfirst hreturn
      simpa [action0StayDescription, actionPrimitivesAt,
        writePrimitivesForAction] using hall
  | some cell =>
      have hwrite :
          PhysicalPrimitiveSequenceGuardedContractEquiv
            [PhysicalPrimitive.writeHeadCell 0 cell]
            (writeHeadCell0Description cell) :=
        (writeHeadCell0Description_physicalPrimitiveGuardedContract cell)
          |>.toSequenceEquiv
      have hfirst :=
        physicalPrimitiveSequenceGuardedContractEquiv_append
          hseek hwrite
      have hsecond :=
        physicalPrimitiveSequenceGuardedContractEquiv_append
          hfirst hmove
      have hall :=
        physicalPrimitiveSequenceGuardedContractEquiv_append
          hsecond hreturn
      simpa [action0StayDescription, actionPrimitivesAt,
        writePrimitivesForAction] using hall

/--
Complete guarded tape-1 stay-action sequence.

This is a whole-pipeline contract for tape 1: it seeks to tape 1, optionally
writes the selected head cell, performs the structured {lit}`stay` action, and
returns to the canonical block start.
-/
def action1StayDescription
    (write? : Option (Option Bool)) : MachineDescription :=
  match write? with
  | none => cursorTape1NoopAndReturnToBlockStartDescription
  | some cell =>
      cursorTape1WriteHeadCellAndReturnToBlockStartDescription cell

private theorem actionPrimitivesAt_one_stay_enabled
    {logical : List (Tape Bool)} {write? : Option (Option Bool)}
    (henabled :
      physicalPrimitiveSequenceEnabled
        (actionPrimitivesAt 1
          { write? := write?, move := HeadMove.stay }) logical) :
    1 < logical.length := by
  cases write? with
  | none =>
      simp [actionPrimitivesAt, writePrimitivesForAction,
        PhysicalPrimitive.apply] at henabled
      exact henabled
  | some cell =>
      simp [actionPrimitivesAt, writePrimitivesForAction,
        PhysicalPrimitive.apply] at henabled
      exact henabled

private theorem applyPhysicalPrimitiveSequence_actionPrimitivesAt_one_stay
    (write? : Option (Option Bool))
    {logical : List (Tape Bool)}
    (hlength : 1 < logical.length) :
    applyPhysicalPrimitiveSequence
        (actionPrimitivesAt 1
          { write? := write?, move := HeadMove.stay }) logical =
      match write? with
      | none => logical
      | some cell =>
          (PhysicalPrimitive.writeHeadCell 1 cell).apply logical := by
  cases logical with
  | nil =>
      simp at hlength
  | cons T rest =>
      cases rest with
      | nil =>
          simp at hlength
      | cons U tail =>
          cases write? with
          | none =>
              simp [actionPrimitivesAt, writePrimitivesForAction,
                PhysicalPrimitive.apply, Description.tapeAt,
                HeadMove.apply]
          | some cell =>
              simp [actionPrimitivesAt, writePrimitivesForAction,
                PhysicalPrimitive.apply, Description.tapeAt,
                HeadMove.apply]

theorem action1StayDescription_physicalPrimitiveSequenceGuardedContractEquiv
    (write? : Option (Option Bool)) :
    PhysicalPrimitiveSequenceGuardedContractEquiv
      (actionPrimitivesAt 1 { write? := write?, move := HeadMove.stay })
      (action1StayDescription write?) := by
  constructor
  · cases write? with
    | none =>
        exact
          cursorTape1NoopAndReturnToBlockStartDescription_contract
            |>.subroutineReady
    | some cell =>
        exact
          (cursorTape1WriteHeadCellAndReturnToBlockStartDescription_contract
            cell).subroutineReady
  · intro logical henabled
    have hlength : 1 < logical.length :=
      actionPrimitivesAt_one_stay_enabled henabled
    have hzero : 0 < logical.length :=
      Nat.lt_trans (by decide : 0 < 1) hlength
    have hsource :
        AtExistingTapeSeparator (guardLogicalTapes logical) 0
            (encodedGuardedStructuredTapes logical) ∧
          (exists T : Tape Bool, exists rest : List (Tape Bool),
            (guardLogicalTapes logical).drop 1 = T :: rest) := by
      exact
        ⟨guardedAtExistingTapeSeparator_zero hzero,
          guardedDropOne_exists_of_one_lt hlength⟩
    cases write? with
    | none =>
        rcases
            cursorTape1NoopAndReturnToBlockStartDescription_contract.realizes
              (guardLogicalTapes logical)
              (encodedGuardedStructuredTapes logical)
              hsource with
          ⟨Tout, hhalts, hseparator⟩
        have hTout : Tout = encodedGuardedStructuredTapes logical :=
          atTapeSeparator_zero_eq hseparator
        have hseq :=
          applyPhysicalPrimitiveSequence_actionPrimitivesAt_one_stay
            (none : Option (Option Bool)) hlength
        exact
          MachineDescription.HaltsFromTape.toEquiv
            (by
              rw [hseq]
              simpa [action1StayDescription, hTout] using hhalts)
    | some cell =>
        rcases
            (cursorTape1WriteHeadCellAndReturnToBlockStartDescription_contract
              cell).realizes
              (guardLogicalTapes logical)
              (encodedGuardedStructuredTapes logical)
              hsource with
          ⟨Tout, hhalts, hseparator⟩
        have hTout :
            Tout =
              encodedStructuredTapes
                ((PhysicalPrimitive.writeHeadCell 1 cell).apply
                  (guardLogicalTapes logical)) :=
          atTapeSeparator_zero_eq hseparator
        have hguard :
            encodedStructuredTapes
                ((PhysicalPrimitive.writeHeadCell 1 cell).apply
                  (guardLogicalTapes logical)) =
              encodedGuardedStructuredTapes
                ((PhysicalPrimitive.writeHeadCell 1 cell).apply
                  logical) := by
          simp [encodedGuardedStructuredTapes,
            guardedWriteHeadCell_one_apply]
        have hseq :=
          applyPhysicalPrimitiveSequence_actionPrimitivesAt_one_stay
            (some cell) hlength
        exact
          MachineDescription.HaltsFromTape.toEquiv
            (by
              rw [hseq]
              simpa [action1StayDescription, hTout, hguard]
                using hhalts)

private theorem actionPrimitivesAt_one_enabled
    {logical : List (Tape Bool)}
    {write? : Option (Option Bool)} {move : HeadMove}
    (henabled :
      physicalPrimitiveSequenceEnabled
        (actionPrimitivesAt 1 { write? := write?, move := move })
        logical) :
    1 < logical.length := by
  cases write? <;>
    simpa [actionPrimitivesAt, writePrimitivesForAction]
      using henabled.left

/--
Tape-1 action fragment for a local left move, with an optional write first.

The write phase is the whole tape-1 pipeline, so the intermediate tape-1
separator stays internal.  The final endpoint uses the logical-equivalence
contract because the local move consumes a represented guard cell.
-/
def action1LeftLocalDescription
    (write? : Option (Option Bool)) : MachineDescription :=
  match write? with
  | none => moveHead1LeftLocalDescription
  | some cell =>
      canonicalPrimitiveSeqDescription
        (cursorTape1WriteHeadCellAndReturnToBlockStartDescription cell)
        moveHead1LeftLocalDescription

theorem action1LeftLocalDescription_physicalPrimitiveSequenceGuardedLogicalEquivContract
    (write? : Option (Option Bool)) :
    PhysicalPrimitiveSequenceGuardedLogicalEquivContract
      (actionPrimitivesAt 1 { write? := write?, move := HeadMove.left })
      (action1LeftLocalDescription write?) := by
  constructor
  · cases write? with
    | none =>
        exact
          moveHead1LeftLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
            |>.subroutineReady
    | some cell =>
        exact
          canonicalPrimitiveSeqDescription_subroutineReady
            ((cursorTape1WriteHeadCellAndReturnToBlockStartDescription_contract
              cell).subroutineReady)
            (moveHead1LeftLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
              |>.subroutineReady)
  · intro logical henabled
    have hlength : 1 < logical.length :=
      actionPrimitivesAt_one_enabled henabled
    have hzero : 0 < logical.length :=
      Nat.lt_trans (by decide : 0 < 1) hlength
    have hsource :
        AtExistingTapeSeparator (guardLogicalTapes logical) 0
            (encodedGuardedStructuredTapes logical) ∧
          (exists T : Tape Bool, exists rest : List (Tape Bool),
            (guardLogicalTapes logical).drop 1 = T :: rest) := by
      exact
        ⟨guardedAtExistingTapeSeparator_zero hzero,
          guardedDropOne_exists_of_one_lt hlength⟩
    cases write? with
    | none =>
        rcases
            moveHead1LeftLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
              |>.realizes logical hlength with
          ⟨actual, hactual, hhalts⟩
        refine ⟨actual, ?_, ?_⟩
        · simpa [actionPrimitivesAt, writePrimitivesForAction,
            PhysicalPrimitive.apply] using hactual
        · simpa [action1LeftLocalDescription] using hhalts
    | some cell =>
        let written :=
          (PhysicalPrimitive.writeHeadCell 1 cell).apply logical
        rcases
            (cursorTape1WriteHeadCellAndReturnToBlockStartDescription_contract
              cell).realizes
              (guardLogicalTapes logical)
              (encodedGuardedStructuredTapes logical)
              hsource with
          ⟨Twrite, hwriteRaw, hwriteSeparator⟩
        have hwriteTout :
            Twrite =
              encodedStructuredTapes
                ((PhysicalPrimitive.writeHeadCell 1 cell).apply
                  (guardLogicalTapes logical)) :=
          atTapeSeparator_zero_eq hwriteSeparator
        have hguard :
            encodedStructuredTapes
                ((PhysicalPrimitive.writeHeadCell 1 cell).apply
                  (guardLogicalTapes logical)) =
              encodedGuardedStructuredTapes written := by
          simp [written, encodedGuardedStructuredTapes,
            guardedWriteHeadCell_one_apply]
        have hwrite :
            (cursorTape1WriteHeadCellAndReturnToBlockStartDescription
              cell).HaltsFromTape
              (encodedGuardedStructuredTapes logical)
              (encodedGuardedStructuredTapes written) := by
          simpa [hwriteTout, hguard] using hwriteRaw
        have hlengthWritten : 1 < written.length := by
          simpa [written, PhysicalPrimitive.apply] using hlength
        rcases
            moveHead1LeftLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
              |>.realizes written hlengthWritten with
          ⟨actual, hactual, hmoveHalts⟩
        refine ⟨actual, ?_, ?_⟩
        · simpa [actionPrimitivesAt, writePrimitivesForAction,
            written, PhysicalPrimitive.apply] using hactual
        · have hzeroWritten : 0 < written.length :=
            Nat.lt_trans (by decide : 0 < 1) hlengthWritten
          have hbounce :=
            encodedGuardedStructuredTapes_bounce_zero
              written hzeroWritten
          have hmoveFromBounce :
              moveHead1LeftLocalDescription.HaltsFromTape
                (Tape.move Direction.left
                  (Tape.move Direction.right
                    (encodedGuardedStructuredTapes written)))
                (encodedStructuredTapes actual) := by
            rw [hbounce]
            exact hmoveHalts
          simpa [action1LeftLocalDescription, written] using
            canonicalPrimitiveSeqDescription_haltsFromTape_of_haltsFromTape
              ((cursorTape1WriteHeadCellAndReturnToBlockStartDescription_contract
                cell).subroutineReady)
              (moveHead1LeftLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
                |>.subroutineReady)
              hwrite hmoveFromBounce

/--
Tape-1 action fragment for a local right move, with an optional write first.
-/
def action1RightLocalDescription
    (write? : Option (Option Bool)) : MachineDescription :=
  match write? with
  | none => moveHead1RightLocalDescription
  | some cell =>
      canonicalPrimitiveSeqDescription
        (cursorTape1WriteHeadCellAndReturnToBlockStartDescription cell)
        moveHead1RightLocalDescription

theorem action1RightLocalDescription_physicalPrimitiveSequenceGuardedLogicalEquivContract
    (write? : Option (Option Bool)) :
    PhysicalPrimitiveSequenceGuardedLogicalEquivContract
      (actionPrimitivesAt 1 { write? := write?, move := HeadMove.right })
      (action1RightLocalDescription write?) := by
  constructor
  · cases write? with
    | none =>
        exact
          moveHead1RightLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
            |>.subroutineReady
    | some cell =>
        exact
          canonicalPrimitiveSeqDescription_subroutineReady
            ((cursorTape1WriteHeadCellAndReturnToBlockStartDescription_contract
              cell).subroutineReady)
            (moveHead1RightLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
              |>.subroutineReady)
  · intro logical henabled
    have hlength : 1 < logical.length :=
      actionPrimitivesAt_one_enabled henabled
    have hzero : 0 < logical.length :=
      Nat.lt_trans (by decide : 0 < 1) hlength
    have hsource :
        AtExistingTapeSeparator (guardLogicalTapes logical) 0
            (encodedGuardedStructuredTapes logical) ∧
          (exists T : Tape Bool, exists rest : List (Tape Bool),
            (guardLogicalTapes logical).drop 1 = T :: rest) := by
      exact
        ⟨guardedAtExistingTapeSeparator_zero hzero,
          guardedDropOne_exists_of_one_lt hlength⟩
    cases write? with
    | none =>
        rcases
            moveHead1RightLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
              |>.realizes logical hlength with
          ⟨actual, hactual, hhalts⟩
        refine ⟨actual, ?_, ?_⟩
        · simpa [actionPrimitivesAt, writePrimitivesForAction,
            PhysicalPrimitive.apply] using hactual
        · simpa [action1RightLocalDescription] using hhalts
    | some cell =>
        let written :=
          (PhysicalPrimitive.writeHeadCell 1 cell).apply logical
        rcases
            (cursorTape1WriteHeadCellAndReturnToBlockStartDescription_contract
              cell).realizes
              (guardLogicalTapes logical)
              (encodedGuardedStructuredTapes logical)
              hsource with
          ⟨Twrite, hwriteRaw, hwriteSeparator⟩
        have hwriteTout :
            Twrite =
              encodedStructuredTapes
                ((PhysicalPrimitive.writeHeadCell 1 cell).apply
                  (guardLogicalTapes logical)) :=
          atTapeSeparator_zero_eq hwriteSeparator
        have hguard :
            encodedStructuredTapes
                ((PhysicalPrimitive.writeHeadCell 1 cell).apply
                  (guardLogicalTapes logical)) =
              encodedGuardedStructuredTapes written := by
          simp [written, encodedGuardedStructuredTapes,
            guardedWriteHeadCell_one_apply]
        have hwrite :
            (cursorTape1WriteHeadCellAndReturnToBlockStartDescription
              cell).HaltsFromTape
              (encodedGuardedStructuredTapes logical)
              (encodedGuardedStructuredTapes written) := by
          simpa [hwriteTout, hguard] using hwriteRaw
        have hlengthWritten : 1 < written.length := by
          simpa [written, PhysicalPrimitive.apply] using hlength
        rcases
            moveHead1RightLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
              |>.realizes written hlengthWritten with
          ⟨actual, hactual, hmoveHalts⟩
        refine ⟨actual, ?_, ?_⟩
        · simpa [actionPrimitivesAt, writePrimitivesForAction,
            written, PhysicalPrimitive.apply] using hactual
        · have hzeroWritten : 0 < written.length :=
            Nat.lt_trans (by decide : 0 < 1) hlengthWritten
          have hbounce :=
            encodedGuardedStructuredTapes_bounce_zero
              written hzeroWritten
          have hmoveFromBounce :
              moveHead1RightLocalDescription.HaltsFromTape
                (Tape.move Direction.left
                  (Tape.move Direction.right
                    (encodedGuardedStructuredTapes written)))
                (encodedStructuredTapes actual) := by
            rw [hbounce]
            exact hmoveHalts
          simpa [action1RightLocalDescription, written] using
            canonicalPrimitiveSeqDescription_haltsFromTape_of_haltsFromTape
              ((cursorTape1WriteHeadCellAndReturnToBlockStartDescription_contract
                cell).subroutineReady)
              (moveHead1RightLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
                |>.subroutineReady)
              hwrite hmoveFromBounce

/--
Complete guarded tape-2 stay-action sequence.

This is a whole-pipeline contract for tape 2: it seeks to tape 2, optionally
writes the selected head cell, performs the structured {lit}`stay` action, and
returns through tape 1 to the canonical block start.
-/
def action2StayDescription
    (write? : Option (Option Bool)) : MachineDescription :=
  match write? with
  | none => cursorTape2NoopAndReturnToBlockStartDescription
  | some cell =>
      cursorTape2WriteHeadCellAndReturnToBlockStartDescription cell

private theorem actionPrimitivesAt_two_stay_enabled
    {logical : List (Tape Bool)} {write? : Option (Option Bool)}
    (henabled :
      physicalPrimitiveSequenceEnabled
        (actionPrimitivesAt 2
          { write? := write?, move := HeadMove.stay }) logical) :
    2 < logical.length := by
  cases write? with
  | none =>
      simp [actionPrimitivesAt, writePrimitivesForAction,
        PhysicalPrimitive.apply] at henabled
      exact henabled
  | some cell =>
      simp [actionPrimitivesAt, writePrimitivesForAction,
        PhysicalPrimitive.apply] at henabled
      exact henabled

private theorem applyPhysicalPrimitiveSequence_actionPrimitivesAt_two_stay
    (write? : Option (Option Bool))
    {logical : List (Tape Bool)}
    (hlength : 2 < logical.length) :
    applyPhysicalPrimitiveSequence
        (actionPrimitivesAt 2
          { write? := write?, move := HeadMove.stay }) logical =
      match write? with
      | none => logical
      | some cell =>
          (PhysicalPrimitive.writeHeadCell 2 cell).apply logical := by
  cases logical with
  | nil =>
      simp at hlength
  | cons T rest =>
      cases rest with
      | nil =>
          simp at hlength
      | cons U rest =>
          cases rest with
          | nil =>
              simp at hlength
          | cons V tail =>
              cases write? with
              | none =>
                  simp [actionPrimitivesAt, writePrimitivesForAction,
                    PhysicalPrimitive.apply, Description.tapeAt,
                    HeadMove.apply]
              | some cell =>
                  simp [actionPrimitivesAt, writePrimitivesForAction,
                    PhysicalPrimitive.apply, Description.tapeAt,
                    HeadMove.apply]

theorem action2StayDescription_physicalPrimitiveSequenceGuardedContractEquiv
    (write? : Option (Option Bool)) :
    PhysicalPrimitiveSequenceGuardedContractEquiv
      (actionPrimitivesAt 2 { write? := write?, move := HeadMove.stay })
      (action2StayDescription write?) := by
  constructor
  · cases write? with
    | none =>
        exact
          cursorTape2NoopAndReturnToBlockStartDescription_contract
            |>.subroutineReady
    | some cell =>
        exact
          (cursorTape2WriteHeadCellAndReturnToBlockStartDescription_contract
            cell).subroutineReady
  · intro logical henabled
    have hlength : 2 < logical.length :=
      actionPrimitivesAt_two_stay_enabled henabled
    have hzero : 0 < logical.length :=
      Nat.lt_trans (by decide : 0 < 2) hlength
    have hsource :
        AtExistingTapeSeparator (guardLogicalTapes logical) 0
            (encodedGuardedStructuredTapes logical) ∧
          HasAtLeastThreeTapes (guardLogicalTapes logical) := by
      exact
        ⟨guardedAtExistingTapeSeparator_zero hzero,
          guardedHasAtLeastThreeTapes_of_two_lt hlength⟩
    cases write? with
    | none =>
        rcases
            cursorTape2NoopAndReturnToBlockStartDescription_contract.realizes
              (guardLogicalTapes logical)
              (encodedGuardedStructuredTapes logical)
              hsource with
          ⟨Tout, hhalts, hseparator⟩
        have hTout : Tout = encodedGuardedStructuredTapes logical :=
          atTapeSeparator_zero_eq hseparator
        have hseq :=
          applyPhysicalPrimitiveSequence_actionPrimitivesAt_two_stay
            (none : Option (Option Bool)) hlength
        exact
          MachineDescription.HaltsFromTape.toEquiv
            (by
              rw [hseq]
              simpa [action2StayDescription, hTout] using hhalts)
    | some cell =>
        rcases
            (cursorTape2WriteHeadCellAndReturnToBlockStartDescription_contract
              cell).realizes
              (guardLogicalTapes logical)
              (encodedGuardedStructuredTapes logical)
              hsource with
          ⟨Tout, hhalts, hseparator⟩
        have hTout :
            Tout =
              encodedStructuredTapes
                ((PhysicalPrimitive.writeHeadCell 2 cell).apply
                  (guardLogicalTapes logical)) :=
          atTapeSeparator_zero_eq hseparator
        have hguard :
            encodedStructuredTapes
                ((PhysicalPrimitive.writeHeadCell 2 cell).apply
                  (guardLogicalTapes logical)) =
              encodedGuardedStructuredTapes
                ((PhysicalPrimitive.writeHeadCell 2 cell).apply
                  logical) := by
          simp [encodedGuardedStructuredTapes,
            guardedWriteHeadCell_two_apply]
        have hseq :=
          applyPhysicalPrimitiveSequence_actionPrimitivesAt_two_stay
            (some cell) hlength
        exact
          MachineDescription.HaltsFromTape.toEquiv
            (by
              rw [hseq]
              simpa [action2StayDescription, hTout, hguard]
                using hhalts)

private theorem actionPrimitivesAt_two_enabled
    {logical : List (Tape Bool)}
    {write? : Option (Option Bool)} {move : HeadMove}
    (henabled :
      physicalPrimitiveSequenceEnabled
        (actionPrimitivesAt 2 { write? := write?, move := move })
        logical) :
    2 < logical.length := by
  cases write? <;>
    simpa [actionPrimitivesAt, writePrimitivesForAction]
      using henabled.left

/--
Tape-2 action fragment for a local left move, with an optional write first.

The write and move phases are whole tape-2 pipelines that return through tape
1 to block start.  The final endpoint is stated through pointwise logical tape
equivalence because the move consumes a represented guard cell.
-/
def action2LeftLocalDescription
    (write? : Option (Option Bool)) : MachineDescription :=
  match write? with
  | none => moveHead2LeftLocalDescription
  | some cell =>
      canonicalPrimitiveSeqDescription
        (cursorTape2WriteHeadCellAndReturnToBlockStartDescription cell)
        moveHead2LeftLocalDescription

theorem action2LeftLocalDescription_physicalPrimitiveSequenceGuardedLogicalEquivContract
    (write? : Option (Option Bool)) :
    PhysicalPrimitiveSequenceGuardedLogicalEquivContract
      (actionPrimitivesAt 2 { write? := write?, move := HeadMove.left })
      (action2LeftLocalDescription write?) := by
  constructor
  · cases write? with
    | none =>
        exact
          moveHead2LeftLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
            |>.subroutineReady
    | some cell =>
        exact
          canonicalPrimitiveSeqDescription_subroutineReady
            ((cursorTape2WriteHeadCellAndReturnToBlockStartDescription_contract
              cell).subroutineReady)
            (moveHead2LeftLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
              |>.subroutineReady)
  · intro logical henabled
    have hlength : 2 < logical.length :=
      actionPrimitivesAt_two_enabled henabled
    have hzero : 0 < logical.length :=
      Nat.lt_trans (by decide : 0 < 2) hlength
    have hsource :
        AtExistingTapeSeparator (guardLogicalTapes logical) 0
            (encodedGuardedStructuredTapes logical) ∧
          HasAtLeastThreeTapes (guardLogicalTapes logical) := by
      exact
        ⟨guardedAtExistingTapeSeparator_zero hzero,
          guardedHasAtLeastThreeTapes_of_two_lt hlength⟩
    cases write? with
    | none =>
        rcases
            moveHead2LeftLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
              |>.realizes logical hlength with
          ⟨actual, hactual, hhalts⟩
        refine ⟨actual, ?_, ?_⟩
        · simpa [actionPrimitivesAt, writePrimitivesForAction,
            PhysicalPrimitive.apply] using hactual
        · simpa [action2LeftLocalDescription] using hhalts
    | some cell =>
        let written :=
          (PhysicalPrimitive.writeHeadCell 2 cell).apply logical
        rcases
            (cursorTape2WriteHeadCellAndReturnToBlockStartDescription_contract
              cell).realizes
              (guardLogicalTapes logical)
              (encodedGuardedStructuredTapes logical)
              hsource with
          ⟨Twrite, hwriteRaw, hwriteSeparator⟩
        have hwriteTout :
            Twrite =
              encodedStructuredTapes
                ((PhysicalPrimitive.writeHeadCell 2 cell).apply
                  (guardLogicalTapes logical)) :=
          atTapeSeparator_zero_eq hwriteSeparator
        have hguard :
            encodedStructuredTapes
                ((PhysicalPrimitive.writeHeadCell 2 cell).apply
                  (guardLogicalTapes logical)) =
              encodedGuardedStructuredTapes written := by
          simp [written, encodedGuardedStructuredTapes,
            guardedWriteHeadCell_two_apply]
        have hwrite :
            (cursorTape2WriteHeadCellAndReturnToBlockStartDescription
              cell).HaltsFromTape
              (encodedGuardedStructuredTapes logical)
              (encodedGuardedStructuredTapes written) := by
          simpa [hwriteTout, hguard] using hwriteRaw
        have hlengthWritten : 2 < written.length := by
          simpa [written, PhysicalPrimitive.apply] using hlength
        rcases
            moveHead2LeftLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
              |>.realizes written hlengthWritten with
          ⟨actual, hactual, hmoveHalts⟩
        refine ⟨actual, ?_, ?_⟩
        · simpa [actionPrimitivesAt, writePrimitivesForAction,
            written, PhysicalPrimitive.apply] using hactual
        · have hzeroWritten : 0 < written.length :=
            Nat.lt_trans (by decide : 0 < 2) hlengthWritten
          have hbounce :=
            encodedGuardedStructuredTapes_bounce_zero
              written hzeroWritten
          have hmoveFromBounce :
              moveHead2LeftLocalDescription.HaltsFromTape
                (Tape.move Direction.left
                  (Tape.move Direction.right
                    (encodedGuardedStructuredTapes written)))
                (encodedStructuredTapes actual) := by
            rw [hbounce]
            exact hmoveHalts
          simpa [action2LeftLocalDescription, written] using
            canonicalPrimitiveSeqDescription_haltsFromTape_of_haltsFromTape
              ((cursorTape2WriteHeadCellAndReturnToBlockStartDescription_contract
                cell).subroutineReady)
              (moveHead2LeftLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
                |>.subroutineReady)
              hwrite hmoveFromBounce

/--
Tape-2 action fragment for a local right move, with an optional write first.
-/
def action2RightLocalDescription
    (write? : Option (Option Bool)) : MachineDescription :=
  match write? with
  | none => moveHead2RightLocalDescription
  | some cell =>
      canonicalPrimitiveSeqDescription
        (cursorTape2WriteHeadCellAndReturnToBlockStartDescription cell)
        moveHead2RightLocalDescription

theorem action2RightLocalDescription_physicalPrimitiveSequenceGuardedLogicalEquivContract
    (write? : Option (Option Bool)) :
    PhysicalPrimitiveSequenceGuardedLogicalEquivContract
      (actionPrimitivesAt 2 { write? := write?, move := HeadMove.right })
      (action2RightLocalDescription write?) := by
  constructor
  · cases write? with
    | none =>
        exact
          moveHead2RightLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
            |>.subroutineReady
    | some cell =>
        exact
          canonicalPrimitiveSeqDescription_subroutineReady
            ((cursorTape2WriteHeadCellAndReturnToBlockStartDescription_contract
              cell).subroutineReady)
            (moveHead2RightLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
              |>.subroutineReady)
  · intro logical henabled
    have hlength : 2 < logical.length :=
      actionPrimitivesAt_two_enabled henabled
    have hzero : 0 < logical.length :=
      Nat.lt_trans (by decide : 0 < 2) hlength
    have hsource :
        AtExistingTapeSeparator (guardLogicalTapes logical) 0
            (encodedGuardedStructuredTapes logical) ∧
          HasAtLeastThreeTapes (guardLogicalTapes logical) := by
      exact
        ⟨guardedAtExistingTapeSeparator_zero hzero,
          guardedHasAtLeastThreeTapes_of_two_lt hlength⟩
    cases write? with
    | none =>
        rcases
            moveHead2RightLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
              |>.realizes logical hlength with
          ⟨actual, hactual, hhalts⟩
        refine ⟨actual, ?_, ?_⟩
        · simpa [actionPrimitivesAt, writePrimitivesForAction,
            PhysicalPrimitive.apply] using hactual
        · simpa [action2RightLocalDescription] using hhalts
    | some cell =>
        let written :=
          (PhysicalPrimitive.writeHeadCell 2 cell).apply logical
        rcases
            (cursorTape2WriteHeadCellAndReturnToBlockStartDescription_contract
              cell).realizes
              (guardLogicalTapes logical)
              (encodedGuardedStructuredTapes logical)
              hsource with
          ⟨Twrite, hwriteRaw, hwriteSeparator⟩
        have hwriteTout :
            Twrite =
              encodedStructuredTapes
                ((PhysicalPrimitive.writeHeadCell 2 cell).apply
                  (guardLogicalTapes logical)) :=
          atTapeSeparator_zero_eq hwriteSeparator
        have hguard :
            encodedStructuredTapes
                ((PhysicalPrimitive.writeHeadCell 2 cell).apply
                  (guardLogicalTapes logical)) =
              encodedGuardedStructuredTapes written := by
          simp [written, encodedGuardedStructuredTapes,
            guardedWriteHeadCell_two_apply]
        have hwrite :
            (cursorTape2WriteHeadCellAndReturnToBlockStartDescription
              cell).HaltsFromTape
              (encodedGuardedStructuredTapes logical)
              (encodedGuardedStructuredTapes written) := by
          simpa [hwriteTout, hguard] using hwriteRaw
        have hlengthWritten : 2 < written.length := by
          simpa [written, PhysicalPrimitive.apply] using hlength
        rcases
            moveHead2RightLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
              |>.realizes written hlengthWritten with
          ⟨actual, hactual, hmoveHalts⟩
        refine ⟨actual, ?_, ?_⟩
        · simpa [actionPrimitivesAt, writePrimitivesForAction,
            written, PhysicalPrimitive.apply] using hactual
        · have hzeroWritten : 0 < written.length :=
            Nat.lt_trans (by decide : 0 < 2) hlengthWritten
          have hbounce :=
            encodedGuardedStructuredTapes_bounce_zero
              written hzeroWritten
          have hmoveFromBounce :
              moveHead2RightLocalDescription.HaltsFromTape
                (Tape.move Direction.left
                  (Tape.move Direction.right
                    (encodedGuardedStructuredTapes written)))
                (encodedStructuredTapes actual) := by
            rw [hbounce]
            exact hmoveHalts
          simpa [action2RightLocalDescription, written] using
            canonicalPrimitiveSeqDescription_haltsFromTape_of_haltsFromTape
              ((cursorTape2WriteHeadCellAndReturnToBlockStartDescription_contract
                cell).subroutineReady)
              (moveHead2RightLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
                |>.subroutineReady)
              hwrite hmoveFromBounce

/--
Guarded tape-0 row fragment: check the expected read, then apply an optional
write with a structured {lit}`stay` move.

This is not a full three-tape row lowerer yet, but it is the first reusable
piece that combines the read-check phase and the action phase through the
guarded {name}`MachineDescription.HaltsFromTapeEquiv` sequence contract.
-/
def tape0ReadStayActionDescription
    (expected : Option Bool) (write? : Option (Option Bool)) :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    (readCheck0Description expected)
    (action0StayDescription write?)

theorem tape0ReadStayActionDescription_physicalPrimitiveSequenceGuardedContractEquiv
    (expected : Option Bool) (write? : Option (Option Bool)) :
    PhysicalPrimitiveSequenceGuardedContractEquiv
      (readCheckPrimitivesAt 0 expected ++
        actionPrimitivesAt 0 { write? := write?, move := HeadMove.stay })
      (tape0ReadStayActionDescription expected write?) :=
  physicalPrimitiveSequenceGuardedContractEquiv_append
    (readCheck0Description_physicalPrimitiveSequenceGuardedContractEquiv
      expected)
    (action0StayDescription_physicalPrimitiveSequenceGuardedContractEquiv
      write?)

/--
Guarded tape-1 row fragment: check the expected read, then apply an optional
write with a structured {lit}`stay` move.

This fragment uses whole-pipeline tape-1 contracts on both sides, so the
intermediate tape-1 separator remains internal to the implementation.
-/
def tape1ReadStayActionDescription
    (expected : Option Bool) (write? : Option (Option Bool)) :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    (readCheck1Description expected)
    (action1StayDescription write?)

theorem tape1ReadStayActionDescription_physicalPrimitiveSequenceGuardedContractEquiv
    (expected : Option Bool) (write? : Option (Option Bool)) :
    PhysicalPrimitiveSequenceGuardedContractEquiv
      (readCheckPrimitivesAt 1 expected ++
        actionPrimitivesAt 1 { write? := write?, move := HeadMove.stay })
      (tape1ReadStayActionDescription expected write?) :=
  physicalPrimitiveSequenceGuardedContractEquiv_append
    (readCheck1Description_physicalPrimitiveSequenceGuardedContractEquiv
      expected)
    (action1StayDescription_physicalPrimitiveSequenceGuardedContractEquiv
      write?)

/--
Guarded tape-2 row fragment: check the expected read, then apply an optional
write with a structured {lit}`stay` move.

This fragment returns through tape 1 after each tape-2 phase, keeping the
tape-2 separator an internal cursor position.
-/
def tape2ReadStayActionDescription
    (expected : Option Bool) (write? : Option (Option Bool)) :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    (readCheck2Description expected)
    (action2StayDescription write?)

theorem tape2ReadStayActionDescription_physicalPrimitiveSequenceGuardedContractEquiv
    (expected : Option Bool) (write? : Option (Option Bool)) :
    PhysicalPrimitiveSequenceGuardedContractEquiv
      (readCheckPrimitivesAt 2 expected ++
        actionPrimitivesAt 2 { write? := write?, move := HeadMove.stay })
      (tape2ReadStayActionDescription expected write?) :=
  physicalPrimitiveSequenceGuardedContractEquiv_append
    (readCheck2Description_physicalPrimitiveSequenceGuardedContractEquiv
      expected)
    (action2StayDescription_physicalPrimitiveSequenceGuardedContractEquiv
      write?)

/--
Tape-2 action fragment for an arbitrary local move.

This wrapper lets the row compiler treat {lit}`stay`, {lit}`left`, and
{lit}`right` uniformly at the final action position.  The exported contract is
the logical-equivalence variant because the left/right cases consume guard
slack.
-/
def action2LocalMoveDescription
    (write? : Option (Option Bool)) (move : HeadMove) :
    MachineDescription :=
  match move with
  | HeadMove.stay => action2StayDescription write?
  | HeadMove.left => action2LeftLocalDescription write?
  | HeadMove.right => action2RightLocalDescription write?

theorem action2LocalMoveDescription_physicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
    (write? : Option (Option Bool)) (move : HeadMove) :
    PhysicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
      (actionPrimitivesAt 2 { write? := write?, move := move })
      (action2LocalMoveDescription write? move) := by
  cases move with
  | stay =>
      simpa [action2LocalMoveDescription] using
        (action2StayDescription_physicalPrimitiveSequenceGuardedContractEquiv
          write?).toLogicalEquiv
  | left =>
      simpa [action2LocalMoveDescription] using
        (action2LeftLocalDescription_physicalPrimitiveSequenceGuardedLogicalEquivContract
          write?).toEquiv
  | right =>
      simpa [action2LocalMoveDescription] using
        (action2RightLocalDescription_physicalPrimitiveSequenceGuardedLogicalEquivContract
          write?).toEquiv

/--
Tape-1 action fragment for an arbitrary local move.

Like the tape-2 wrapper, this exports the logical-equivalence endpoint because
left/right moves consume represented guard slack.
-/
def action1LocalMoveDescription
    (write? : Option (Option Bool)) (move : HeadMove) :
    MachineDescription :=
  match move with
  | HeadMove.stay => action1StayDescription write?
  | HeadMove.left => action1LeftLocalDescription write?
  | HeadMove.right => action1RightLocalDescription write?

theorem action1LocalMoveDescription_physicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
    (write? : Option (Option Bool)) (move : HeadMove) :
    PhysicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
      (actionPrimitivesAt 1 { write? := write?, move := move })
      (action1LocalMoveDescription write? move) := by
  cases move with
  | stay =>
      simpa [action1LocalMoveDescription] using
        (action1StayDescription_physicalPrimitiveSequenceGuardedContractEquiv
          write?).toLogicalEquiv
  | left =>
      simpa [action1LocalMoveDescription] using
        (action1LeftLocalDescription_physicalPrimitiveSequenceGuardedLogicalEquivContract
          write?).toEquiv
  | right =>
      simpa [action1LocalMoveDescription] using
        (action1RightLocalDescription_physicalPrimitiveSequenceGuardedLogicalEquivContract
          write?).toEquiv

/--
Tape-0 action fragment for an arbitrary local move.
-/
def action0LocalMoveDescription
    (write? : Option (Option Bool)) (move : HeadMove) :
    MachineDescription :=
  match move with
  | HeadMove.stay => action0StayDescription write?
  | HeadMove.left => action0LeftLocalDescription write?
  | HeadMove.right => action0RightLocalDescription write?

theorem action0LocalMoveDescription_physicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
    (write? : Option (Option Bool)) (move : HeadMove) :
    PhysicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
      (actionPrimitivesAt 0 { write? := write?, move := move })
      (action0LocalMoveDescription write? move) := by
  cases move with
  | stay =>
      simpa [action0LocalMoveDescription] using
        (action0StayDescription_physicalPrimitiveSequenceGuardedContractEquiv
          write?).toLogicalEquiv
  | left =>
      simpa [action0LocalMoveDescription] using
        (action0LeftLocalDescription_physicalPrimitiveSequenceGuardedLogicalEquivContract
          write?).toEquiv
  | right =>
      simpa [action0LocalMoveDescription] using
        (action0RightLocalDescription_physicalPrimitiveSequenceGuardedLogicalEquivContract
          write?).toEquiv

/--
Full guarded three-tape row fragment for rows whose actions all use
structured {lit}`stay`.

The sequence order matches {name}`transitionPrimitiveSequence3`: all three
read checks run first, then the three optional-write stay actions run.
-/
def readWriteStayRow3Description
    (read0 read1 read2 : Option Bool)
    (write0? write1? write2? : Option (Option Bool)) :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    (canonicalPrimitiveSeqDescription
      (canonicalPrimitiveSeqDescription
        (canonicalPrimitiveSeqDescription
          (canonicalPrimitiveSeqDescription
            (readCheck0Description read0)
            (readCheck1Description read1))
          (readCheck2Description read2))
        (action0StayDescription write0?))
      (action1StayDescription write1?))
    (action2StayDescription write2?)

theorem readWriteStayRow3Description_physicalPrimitiveSequenceGuardedContractEquiv
    (read0 read1 read2 : Option Bool)
    (write0? write1? write2? : Option (Option Bool)) :
    PhysicalPrimitiveSequenceGuardedContractEquiv
      (transitionPrimitiveSequence3 read0 read1 read2
        { write? := write0?, move := HeadMove.stay }
        { write? := write1?, move := HeadMove.stay }
        { write? := write2?, move := HeadMove.stay })
      (readWriteStayRow3Description read0 read1 read2
        write0? write1? write2?) := by
  have hread0 :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        (readCheckPrimitivesAt 0 read0)
        (readCheck0Description read0) :=
    readCheck0Description_physicalPrimitiveSequenceGuardedContractEquiv
      read0
  have hread1 :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        (readCheckPrimitivesAt 1 read1)
        (readCheck1Description read1) :=
    readCheck1Description_physicalPrimitiveSequenceGuardedContractEquiv
      read1
  have hread2 :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        (readCheckPrimitivesAt 2 read2)
        (readCheck2Description read2) :=
    readCheck2Description_physicalPrimitiveSequenceGuardedContractEquiv
      read2
  have haction0 :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        (actionPrimitivesAt 0
          { write? := write0?, move := HeadMove.stay })
        (action0StayDescription write0?) :=
    action0StayDescription_physicalPrimitiveSequenceGuardedContractEquiv
      write0?
  have haction1 :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        (actionPrimitivesAt 1
          { write? := write1?, move := HeadMove.stay })
        (action1StayDescription write1?) :=
    action1StayDescription_physicalPrimitiveSequenceGuardedContractEquiv
      write1?
  have haction2 :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        (actionPrimitivesAt 2
          { write? := write2?, move := HeadMove.stay })
        (action2StayDescription write2?) :=
    action2StayDescription_physicalPrimitiveSequenceGuardedContractEquiv
      write2?
  have h01 :=
    physicalPrimitiveSequenceGuardedContractEquiv_append
      hread0 hread1
  have h012 :=
    physicalPrimitiveSequenceGuardedContractEquiv_append
      h01 hread2
  have h012a0 :=
    physicalPrimitiveSequenceGuardedContractEquiv_append
      h012 haction0
  have h012a01 :=
    physicalPrimitiveSequenceGuardedContractEquiv_append
      h012a0 haction1
  have hall :=
    physicalPrimitiveSequenceGuardedContractEquiv_append
      h012a01 haction2
  simpa [readWriteStayRow3Description, transitionPrimitiveSequence3,
    List.append_assoc] using hall

/--
Full guarded three-tape row fragment where tape 0 and tape 1 stay, and tape 2
is the final local action.

The final tape-2 action may move left or right, so the row exports the
logical-equivalence endpoint contract rather than a canonical guarded endpoint.
-/
def readWriteStayStayMove2Row3Description
    (read0 read1 read2 : Option Bool)
    (write0? write1? write2? : Option (Option Bool))
    (move2 : HeadMove) :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    (canonicalPrimitiveSeqDescription
      (canonicalPrimitiveSeqDescription
        (canonicalPrimitiveSeqDescription
          (canonicalPrimitiveSeqDescription
            (readCheck0Description read0)
            (readCheck1Description read1))
          (readCheck2Description read2))
        (action0StayDescription write0?))
      (action1StayDescription write1?))
    (action2LocalMoveDescription write2? move2)

theorem readWriteStayStayMove2Row3Description_physicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
    (read0 read1 read2 : Option Bool)
    (write0? write1? write2? : Option (Option Bool))
    (move2 : HeadMove) :
    PhysicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
      (transitionPrimitiveSequence3 read0 read1 read2
        { write? := write0?, move := HeadMove.stay }
        { write? := write1?, move := HeadMove.stay }
        { write? := write2?, move := move2 })
      (readWriteStayStayMove2Row3Description read0 read1 read2
        write0? write1? write2? move2) := by
  have hread0 :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        (readCheckPrimitivesAt 0 read0)
        (readCheck0Description read0) :=
    readCheck0Description_physicalPrimitiveSequenceGuardedContractEquiv
      read0
  have hread1 :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        (readCheckPrimitivesAt 1 read1)
        (readCheck1Description read1) :=
    readCheck1Description_physicalPrimitiveSequenceGuardedContractEquiv
      read1
  have hread2 :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        (readCheckPrimitivesAt 2 read2)
        (readCheck2Description read2) :=
    readCheck2Description_physicalPrimitiveSequenceGuardedContractEquiv
      read2
  have haction0 :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        (actionPrimitivesAt 0
          { write? := write0?, move := HeadMove.stay })
        (action0StayDescription write0?) :=
    action0StayDescription_physicalPrimitiveSequenceGuardedContractEquiv
      write0?
  have haction1 :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        (actionPrimitivesAt 1
          { write? := write1?, move := HeadMove.stay })
        (action1StayDescription write1?) :=
    action1StayDescription_physicalPrimitiveSequenceGuardedContractEquiv
      write1?
  have haction2 :
      PhysicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
        (actionPrimitivesAt 2
          { write? := write2?, move := move2 })
        (action2LocalMoveDescription write2? move2) :=
    action2LocalMoveDescription_physicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
      write2? move2
  have h01 :=
    physicalPrimitiveSequenceGuardedContractEquiv_append
      hread0 hread1
  have h012 :=
    physicalPrimitiveSequenceGuardedContractEquiv_append
      h01 hread2
  have h012a0 :=
    physicalPrimitiveSequenceGuardedContractEquiv_append
      h012 haction0
  have h012a01 :=
    physicalPrimitiveSequenceGuardedContractEquiv_append
      h012a0 haction1
  have hall :=
    physicalPrimitiveSequenceGuardedContractEquiv_append_logicalEquiv
      h012a01 haction2
  simpa [readWriteStayStayMove2Row3Description,
    transitionPrimitiveSequence3, List.append_assoc] using hall

/--
Full guarded three-tape row fragment where tape 0 and tape 2 stay, and tape 1
is scheduled as the final local action.

The action order is proof-relevant: tape-2's stay action is run before the
guard-consuming tape-1 action, so the final endpoint can use the one-way
logical-equivalence boundary.
-/
def readWriteStayMove1StayRow3Description
    (read0 read1 read2 : Option Bool)
    (write0? write1? write2? : Option (Option Bool))
    (move1 : HeadMove) :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    (canonicalPrimitiveSeqDescription
      (canonicalPrimitiveSeqDescription
        (canonicalPrimitiveSeqDescription
          (canonicalPrimitiveSeqDescription
            (readCheck0Description read0)
            (readCheck1Description read1))
          (readCheck2Description read2))
        (action0StayDescription write0?))
      (action2StayDescription write2?))
    (action1LocalMoveDescription write1? move1)

theorem readWriteStayMove1StayRow3Description_physicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
    (read0 read1 read2 : Option Bool)
    (write0? write1? write2? : Option (Option Bool))
    (move1 : HeadMove) :
    PhysicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
      (transitionPrimitiveSequence3Action1Last read0 read1 read2
        { write? := write0?, move := HeadMove.stay }
        { write? := write1?, move := move1 }
        { write? := write2?, move := HeadMove.stay })
      (readWriteStayMove1StayRow3Description read0 read1 read2
        write0? write1? write2? move1) := by
  have hread0 :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        (readCheckPrimitivesAt 0 read0)
        (readCheck0Description read0) :=
    readCheck0Description_physicalPrimitiveSequenceGuardedContractEquiv
      read0
  have hread1 :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        (readCheckPrimitivesAt 1 read1)
        (readCheck1Description read1) :=
    readCheck1Description_physicalPrimitiveSequenceGuardedContractEquiv
      read1
  have hread2 :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        (readCheckPrimitivesAt 2 read2)
        (readCheck2Description read2) :=
    readCheck2Description_physicalPrimitiveSequenceGuardedContractEquiv
      read2
  have haction0 :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        (actionPrimitivesAt 0
          { write? := write0?, move := HeadMove.stay })
        (action0StayDescription write0?) :=
    action0StayDescription_physicalPrimitiveSequenceGuardedContractEquiv
      write0?
  have haction2 :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        (actionPrimitivesAt 2
          { write? := write2?, move := HeadMove.stay })
        (action2StayDescription write2?) :=
    action2StayDescription_physicalPrimitiveSequenceGuardedContractEquiv
      write2?
  have haction1 :
      PhysicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
        (actionPrimitivesAt 1
          { write? := write1?, move := move1 })
        (action1LocalMoveDescription write1? move1) :=
    action1LocalMoveDescription_physicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
      write1? move1
  have h01 :=
    physicalPrimitiveSequenceGuardedContractEquiv_append
      hread0 hread1
  have h012 :=
    physicalPrimitiveSequenceGuardedContractEquiv_append
      h01 hread2
  have h012a0 :=
    physicalPrimitiveSequenceGuardedContractEquiv_append
      h012 haction0
  have h012a02 :=
    physicalPrimitiveSequenceGuardedContractEquiv_append
      h012a0 haction2
  have hall :=
    physicalPrimitiveSequenceGuardedContractEquiv_append_logicalEquiv
      h012a02 haction1
  simpa [readWriteStayMove1StayRow3Description,
    transitionPrimitiveSequence3Action1Last, List.append_assoc] using hall

/--
Full guarded three-tape row fragment where tape 1 and tape 2 stay, and tape 0
is scheduled as the final local action.
-/
def readWriteMove0StayStayRow3Description
    (read0 read1 read2 : Option Bool)
    (write0? write1? write2? : Option (Option Bool))
    (move0 : HeadMove) :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    (canonicalPrimitiveSeqDescription
      (canonicalPrimitiveSeqDescription
        (canonicalPrimitiveSeqDescription
          (canonicalPrimitiveSeqDescription
            (readCheck0Description read0)
            (readCheck1Description read1))
          (readCheck2Description read2))
        (action1StayDescription write1?))
      (action2StayDescription write2?))
    (action0LocalMoveDescription write0? move0)

theorem readWriteMove0StayStayRow3Description_physicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
    (read0 read1 read2 : Option Bool)
    (write0? write1? write2? : Option (Option Bool))
    (move0 : HeadMove) :
    PhysicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
      (transitionPrimitiveSequence3Action0Last read0 read1 read2
        { write? := write0?, move := move0 }
        { write? := write1?, move := HeadMove.stay }
        { write? := write2?, move := HeadMove.stay })
      (readWriteMove0StayStayRow3Description read0 read1 read2
        write0? write1? write2? move0) := by
  have hread0 :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        (readCheckPrimitivesAt 0 read0)
        (readCheck0Description read0) :=
    readCheck0Description_physicalPrimitiveSequenceGuardedContractEquiv
      read0
  have hread1 :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        (readCheckPrimitivesAt 1 read1)
        (readCheck1Description read1) :=
    readCheck1Description_physicalPrimitiveSequenceGuardedContractEquiv
      read1
  have hread2 :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        (readCheckPrimitivesAt 2 read2)
        (readCheck2Description read2) :=
    readCheck2Description_physicalPrimitiveSequenceGuardedContractEquiv
      read2
  have haction1 :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        (actionPrimitivesAt 1
          { write? := write1?, move := HeadMove.stay })
        (action1StayDescription write1?) :=
    action1StayDescription_physicalPrimitiveSequenceGuardedContractEquiv
      write1?
  have haction2 :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        (actionPrimitivesAt 2
          { write? := write2?, move := HeadMove.stay })
        (action2StayDescription write2?) :=
    action2StayDescription_physicalPrimitiveSequenceGuardedContractEquiv
      write2?
  have haction0 :
      PhysicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
        (actionPrimitivesAt 0
          { write? := write0?, move := move0 })
        (action0LocalMoveDescription write0? move0) :=
    action0LocalMoveDescription_physicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
      write0? move0
  have h01 :=
    physicalPrimitiveSequenceGuardedContractEquiv_append
      hread0 hread1
  have h012 :=
    physicalPrimitiveSequenceGuardedContractEquiv_append
      h01 hread2
  have h012a1 :=
    physicalPrimitiveSequenceGuardedContractEquiv_append
      h012 haction1
  have h012a12 :=
    physicalPrimitiveSequenceGuardedContractEquiv_append
      h012a1 haction2
  have hall :=
    physicalPrimitiveSequenceGuardedContractEquiv_append_logicalEquiv
      h012a12 haction0
  simpa [readWriteMove0StayStayRow3Description,
    transitionPrimitiveSequence3Action0Last, List.append_assoc] using hall

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
