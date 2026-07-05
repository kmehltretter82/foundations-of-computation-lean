import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.PrimitivePipelines

set_option doc.verso true

/-!
# Chainable action slack

This module exposes exact action-level contracts for layouts that already carry
selected-tape guard slack.  These contracts are the bridge from isolated local
head moves to row compilers that can schedule multiple moving tapes without a
guard-refresh normalizer between actions.
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

private theorem atExistingTapeSeparator_zero_of_atHasGuardCells
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    (hguards : LogicalTapeAtHasGuardCells logical tapeIndex) :
    AtExistingTapeSeparator logical 0
      (encodedStructuredTapes logical) := by
  rcases hguards with ⟨T, rest, hdrop, _hguard⟩
  cases logical with
  | nil =>
      simp at hdrop
  | cons U tail =>
      exact
        ⟨atTapeSeparator_zero_self (U :: tail),
          ⟨U, tail, rfl⟩⟩

private theorem drop_exists_of_atHasGuardCells
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    (hguards : LogicalTapeAtHasGuardCells logical tapeIndex) :
    exists T : Tape Bool, exists rest : List (Tape Bool),
      logical.drop tapeIndex = T :: rest := by
  rcases hguards with ⟨T, rest, hdrop, _hguard⟩
  exact ⟨T, rest, hdrop⟩

private theorem encodedStructuredTapes_bounce_zero_of_atHasGuardCells
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    (hguards : LogicalTapeAtHasGuardCells logical tapeIndex) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (encodedStructuredTapes logical)) =
      encodedStructuredTapes logical :=
  atExistingTapeSeparator_moveLeft_moveRight
    (atExistingTapeSeparator_zero_of_atHasGuardCells hguards)

private theorem cursorNoopDescription_haltsFromEncodedStructuredTapes_bounce_of_atHasGuardCells
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    (hguards : LogicalTapeAtHasGuardCells logical tapeIndex) :
    cursorNoopDescription.HaltsFromTape
      (Tape.move Direction.left
        (Tape.move Direction.right
          (encodedStructuredTapes logical)))
      (encodedStructuredTapes logical) := by
  rw [encodedStructuredTapes_bounce_zero_of_atHasGuardCells hguards]
  exact cursorNoopDescription_haltsFromTape
    (encodedStructuredTapes logical)

private theorem logicalTapeHasGuardCells_write
    (cell : Option Bool) {T : Tape Bool}
    (hguard : LogicalTapeHasGuardCells T) :
    LogicalTapeHasGuardCells (Tape.write cell T) := by
  exact
    ⟨by
      simpa [LogicalTapeHasLeftGuard, Tape.write] using hguard.left,
    by
      simpa [LogicalTapeHasRightGuard, Tape.write] using hguard.right⟩

private theorem logicalTapeAtHasGuardCells_writeHeadCell_same
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    (cell : Option Bool)
    (hguards : LogicalTapeAtHasGuardCells logical tapeIndex) :
    LogicalTapeAtHasGuardCells
      ((PhysicalPrimitive.writeHeadCell tapeIndex cell).apply logical)
      tapeIndex := by
  rcases hguards with ⟨T, rest, hdrop, hguard⟩
  refine
    ⟨Tape.write cell T, rest, ?_,
      logicalTapeHasGuardCells_write cell hguard⟩
  have htapeAt : Description.tapeAt logical tapeIndex = T :=
    description_tapeAt_eq_of_drop_eq_cons hdrop
  simp [PhysicalPrimitive.apply, htapeAt,
    replaceTapeAt_drop_eq_of_drop_eq_cons hdrop]

private theorem replaceTapeAt_eq_self_of_drop_eq_cons
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {T : Tape Bool} {rest : List (Tape Bool)}
    (hdrop : logical.drop tapeIndex = T :: rest) :
    replaceTapeAt tapeIndex T logical = logical := by
  induction tapeIndex generalizing logical with
  | zero =>
      cases logical with
      | nil =>
          simp at hdrop
      | cons U tail =>
          simp at hdrop
          rcases hdrop with ⟨rfl, rfl⟩
          rfl
  | succ tapeIndex ih =>
      cases logical with
      | nil =>
          simp at hdrop
      | cons U tail =>
          simp at hdrop
          simp [replaceTapeAt, ih hdrop]

private theorem replaceTapeAt_tapeAt_eq_self_of_atHasGuardCells
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    (hguards : LogicalTapeAtHasGuardCells logical tapeIndex) :
    replaceTapeAt tapeIndex
        (Description.tapeAt logical tapeIndex) logical =
      logical := by
  rcases hguards with ⟨T, rest, hdrop, _hguard⟩
  rw [description_tapeAt_eq_of_drop_eq_cons hdrop]
  exact replaceTapeAt_eq_self_of_drop_eq_cons hdrop

private theorem hasAtLeastThreeTapes_of_atHasGuardCells_two
    {logical : List (Tape Bool)}
    (hguards : LogicalTapeAtHasGuardCells logical 2) :
    HasAtLeastThreeTapes logical := by
  rcases hguards with ⟨V, rest, hdrop, _hguard⟩
  cases logical with
  | nil =>
      simp at hdrop
  | cons T tail =>
      cases tail with
      | nil =>
          simp at hdrop
      | cons U tail =>
          cases tail with
          | nil =>
              simp at hdrop
          | cons V' rest' =>
              exact ⟨T, U, V', rest', rfl⟩

private theorem list_eq_three_of_length_eq_three
    {α : Type u} {xs : List α}
    (h : xs.length = 3) :
    exists a : α, exists b : α, exists c : α,
      xs = [a, b, c] := by
  cases xs with
  | nil =>
      simp at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp at h
      | cons b rest =>
          cases rest with
          | nil =>
              simp at h
          | cons c rest =>
              cases rest with
              | nil =>
                  exact ⟨a, b, c, rfl⟩
              | cons _d _rest =>
                  simp at h

private theorem writeHeadCell0Description_haltsFromEncodedStructuredTapes_of_guardCells
    (cell : Option Bool) (logical : List (Tape Bool))
    (hguards : LogicalTapeAtHasGuardCells logical 0) :
    (writeHeadCell0Description cell).HaltsFromTape
      (encodedStructuredTapes logical)
      (encodedStructuredTapes
        ((PhysicalPrimitive.writeHeadCell 0 cell).apply logical)) := by
  rcases
      (cursorWriteHeadCellAndReturnToSeparatorDescription_contract
        0 cell).realizes logical (encodedStructuredTapes logical)
        (atExistingTapeSeparator_zero_of_atHasGuardCells hguards) with
    ⟨Tout, hhalts, hseparator⟩
  have hTout :
      Tout =
        encodedStructuredTapes
          ((PhysicalPrimitive.writeHeadCell 0 cell).apply logical) :=
    atTapeSeparator_zero_eq hseparator
  simpa [writeHeadCell0Description, hTout] using hhalts

private theorem cursorTape1WriteHeadCellAndReturnToBlockStartDescription_haltsFromEncodedStructuredTapes_of_guardCells
    (cell : Option Bool) (logical : List (Tape Bool))
    (hguards : LogicalTapeAtHasGuardCells logical 1) :
    (cursorTape1WriteHeadCellAndReturnToBlockStartDescription
      cell).HaltsFromTape
      (encodedStructuredTapes logical)
      (encodedStructuredTapes
        ((PhysicalPrimitive.writeHeadCell 1 cell).apply logical)) := by
  rcases
      (cursorTape1WriteHeadCellAndReturnToBlockStartDescription_contract
        cell).realizes logical (encodedStructuredTapes logical)
        ⟨atExistingTapeSeparator_zero_of_atHasGuardCells hguards,
          drop_exists_of_atHasGuardCells hguards⟩ with
    ⟨Tout, hhalts, hseparator⟩
  have hTout :
      Tout =
        encodedStructuredTapes
          ((PhysicalPrimitive.writeHeadCell 1 cell).apply logical) :=
    atTapeSeparator_zero_eq hseparator
  simpa [hTout] using hhalts

private theorem cursorTape2WriteHeadCellAndReturnToBlockStartDescription_haltsFromEncodedStructuredTapes_of_guardCells
    (cell : Option Bool) (logical : List (Tape Bool))
    (hguards : LogicalTapeAtHasGuardCells logical 2) :
    (cursorTape2WriteHeadCellAndReturnToBlockStartDescription
      cell).HaltsFromTape
      (encodedStructuredTapes logical)
      (encodedStructuredTapes
        ((PhysicalPrimitive.writeHeadCell 2 cell).apply logical)) := by
  rcases
      (cursorTape2WriteHeadCellAndReturnToBlockStartDescription_contract
        cell).realizes logical (encodedStructuredTapes logical)
        ⟨atExistingTapeSeparator_zero_of_atHasGuardCells hguards,
          hasAtLeastThreeTapes_of_atHasGuardCells_two hguards⟩ with
    ⟨Tout, hhalts, hseparator⟩
  have hTout :
      Tout =
        encodedStructuredTapes
          ((PhysicalPrimitive.writeHeadCell 2 cell).apply logical) :=
    atTapeSeparator_zero_eq hseparator
  simpa [hTout] using hhalts

theorem action0StayDescription_haltsFromEncodedStructuredTapes_of_guardCells
    (write? : Option (Option Bool)) (logical : List (Tape Bool))
    (hguards : LogicalTapeAtHasGuardCells logical 0) :
    (action0StayDescription write?).HaltsFromTape
      (encodedStructuredTapes logical)
      (encodedStructuredTapes
        (applyPhysicalPrimitiveSequence
          (actionPrimitivesAt 0
            { write? := write?, move := HeadMove.stay })
          logical)) := by
  cases write? with
  | none =>
      have hseek :
          seekTape0Description.HaltsFromTape
            (encodedStructuredTapes logical)
            (encodedStructuredTapes logical) :=
        cursorNoopDescription_haltsFromTape
          (encodedStructuredTapes logical)
      have hmove :
          moveHead0StayDescription.HaltsFromTape
            (Tape.move Direction.left
              (Tape.move Direction.right
                (encodedStructuredTapes logical)))
            (encodedStructuredTapes logical) := by
        simpa [moveHead0StayDescription] using
          cursorNoopDescription_haltsFromEncodedStructuredTapes_bounce_of_atHasGuardCells
            hguards
      have hfirst :
          (canonicalPrimitiveSeqDescription
            seekTape0Description
            moveHead0StayDescription).HaltsFromTape
            (encodedStructuredTapes logical)
            (encodedStructuredTapes logical) :=
        canonicalPrimitiveSeqDescription_haltsFromTape_of_haltsFromTape
          cursorNoopDescription_subroutineReady
          cursorNoopDescription_subroutineReady
          hseek hmove
      have hreturn :
          returnBlockStartNoopDescription.HaltsFromTape
            (Tape.move Direction.left
              (Tape.move Direction.right
                (encodedStructuredTapes logical)))
            (encodedStructuredTapes logical) := by
        simpa [returnBlockStartNoopDescription] using
          cursorNoopDescription_haltsFromEncodedStructuredTapes_bounce_of_atHasGuardCells
            hguards
      have htarget :
          applyPhysicalPrimitiveSequence
              (actionPrimitivesAt 0
                { write? := (none : Option (Option Bool)),
                  move := HeadMove.stay })
              logical =
            logical := by
        simpa [actionPrimitivesAt, writePrimitivesForAction,
          PhysicalPrimitive.apply, HeadMove.apply] using
          replaceTapeAt_tapeAt_eq_self_of_atHasGuardCells hguards
      rw [htarget]
      simpa [action0StayDescription] using
        canonicalPrimitiveSeqDescription_haltsFromTape_of_haltsFromTape
          (canonicalPrimitiveSeqDescription_subroutineReady
            cursorNoopDescription_subroutineReady
            cursorNoopDescription_subroutineReady)
          cursorNoopDescription_subroutineReady
          hfirst hreturn
  | some cell =>
      let written :=
        (PhysicalPrimitive.writeHeadCell 0 cell).apply logical
      have hseek :
          seekTape0Description.HaltsFromTape
            (encodedStructuredTapes logical)
            (encodedStructuredTapes logical) :=
        cursorNoopDescription_haltsFromTape
          (encodedStructuredTapes logical)
      have hwriteRaw :
          (writeHeadCell0Description cell).HaltsFromTape
            (encodedStructuredTapes logical)
            (encodedStructuredTapes written) := by
        simpa [written] using
          writeHeadCell0Description_haltsFromEncodedStructuredTapes_of_guardCells
            cell logical hguards
      have hwrite :
          (writeHeadCell0Description cell).HaltsFromTape
            (Tape.move Direction.left
              (Tape.move Direction.right
                (encodedStructuredTapes logical)))
            (encodedStructuredTapes written) := by
        rw [encodedStructuredTapes_bounce_zero_of_atHasGuardCells
          hguards]
        exact hwriteRaw
      have hfirst :
          (canonicalPrimitiveSeqDescription
            seekTape0Description
            (writeHeadCell0Description cell)).HaltsFromTape
            (encodedStructuredTapes logical)
            (encodedStructuredTapes written) :=
        canonicalPrimitiveSeqDescription_haltsFromTape_of_haltsFromTape
          cursorNoopDescription_subroutineReady
          (writeHeadCell0Description_physicalPrimitiveGuardedContract
            cell |>.subroutineReady)
          hseek hwrite
      have hguardsWritten :
          LogicalTapeAtHasGuardCells written 0 := by
        simpa [written] using
          logicalTapeAtHasGuardCells_writeHeadCell_same cell hguards
      have hmove :
          moveHead0StayDescription.HaltsFromTape
            (Tape.move Direction.left
              (Tape.move Direction.right
                (encodedStructuredTapes written)))
            (encodedStructuredTapes written) := by
        simpa [moveHead0StayDescription] using
          cursorNoopDescription_haltsFromEncodedStructuredTapes_bounce_of_atHasGuardCells
            hguardsWritten
      have hsecond :
          (canonicalPrimitiveSeqDescription
            (canonicalPrimitiveSeqDescription
              seekTape0Description
              (writeHeadCell0Description cell))
            moveHead0StayDescription).HaltsFromTape
            (encodedStructuredTapes logical)
            (encodedStructuredTapes written) :=
        canonicalPrimitiveSeqDescription_haltsFromTape_of_haltsFromTape
          (canonicalPrimitiveSeqDescription_subroutineReady
            cursorNoopDescription_subroutineReady
            (writeHeadCell0Description_physicalPrimitiveGuardedContract
              cell |>.subroutineReady))
          cursorNoopDescription_subroutineReady
          hfirst hmove
      have hreturn :
          returnBlockStartNoopDescription.HaltsFromTape
            (Tape.move Direction.left
              (Tape.move Direction.right
                (encodedStructuredTapes written)))
            (encodedStructuredTapes written) := by
        simpa [returnBlockStartNoopDescription] using
          cursorNoopDescription_haltsFromEncodedStructuredTapes_bounce_of_atHasGuardCells
            hguardsWritten
      have htarget :
          applyPhysicalPrimitiveSequence
              (actionPrimitivesAt 0
                { write? := some cell, move := HeadMove.stay })
              logical =
            written := by
        simpa [actionPrimitivesAt, writePrimitivesForAction,
          written, PhysicalPrimitive.apply, HeadMove.apply] using
          replaceTapeAt_tapeAt_eq_self_of_atHasGuardCells
            hguardsWritten
      rw [htarget]
      simpa [action0StayDescription] using
        canonicalPrimitiveSeqDescription_haltsFromTape_of_haltsFromTape
          (canonicalPrimitiveSeqDescription_subroutineReady
            (canonicalPrimitiveSeqDescription_subroutineReady
              cursorNoopDescription_subroutineReady
              (writeHeadCell0Description_physicalPrimitiveGuardedContract
                cell |>.subroutineReady))
            cursorNoopDescription_subroutineReady)
          cursorNoopDescription_subroutineReady
          hsecond hreturn

theorem action1StayDescription_haltsFromEncodedStructuredTapes_of_guardCells
    (write? : Option (Option Bool)) (logical : List (Tape Bool))
    (hguards : LogicalTapeAtHasGuardCells logical 1) :
    (action1StayDescription write?).HaltsFromTape
      (encodedStructuredTapes logical)
      (encodedStructuredTapes
        (applyPhysicalPrimitiveSequence
          (actionPrimitivesAt 1
            { write? := write?, move := HeadMove.stay })
          logical)) := by
  cases write? with
  | none =>
      rcases
          cursorTape1NoopAndReturnToBlockStartDescription_contract.realizes
            logical (encodedStructuredTapes logical)
            ⟨atExistingTapeSeparator_zero_of_atHasGuardCells hguards,
              drop_exists_of_atHasGuardCells hguards⟩ with
        ⟨Tout, hhalts, hseparator⟩
      have hTout : Tout = encodedStructuredTapes logical :=
        atTapeSeparator_zero_eq hseparator
      have htarget :
          applyPhysicalPrimitiveSequence
              (actionPrimitivesAt 1
                { write? := (none : Option (Option Bool)),
                  move := HeadMove.stay })
              logical =
            logical := by
        simpa [actionPrimitivesAt, writePrimitivesForAction,
          PhysicalPrimitive.apply, HeadMove.apply] using
          replaceTapeAt_tapeAt_eq_self_of_atHasGuardCells hguards
      rw [htarget]
      simpa [action1StayDescription, hTout] using hhalts
  | some cell =>
      have hwrite :=
        cursorTape1WriteHeadCellAndReturnToBlockStartDescription_haltsFromEncodedStructuredTapes_of_guardCells
          cell logical hguards
      let written :=
        (PhysicalPrimitive.writeHeadCell 1 cell).apply logical
      have hguardsWritten :
          LogicalTapeAtHasGuardCells written 1 := by
        simpa [written] using
          logicalTapeAtHasGuardCells_writeHeadCell_same cell hguards
      have htarget :
          applyPhysicalPrimitiveSequence
              (actionPrimitivesAt 1
                { write? := some cell, move := HeadMove.stay })
              logical =
            written := by
        simpa [actionPrimitivesAt, writePrimitivesForAction,
          written, PhysicalPrimitive.apply, HeadMove.apply] using
          replaceTapeAt_tapeAt_eq_self_of_atHasGuardCells
            hguardsWritten
      rw [htarget]
      simpa [action1StayDescription, written] using hwrite

theorem action2StayDescription_haltsFromEncodedStructuredTapes_of_guardCells
    (write? : Option (Option Bool)) (logical : List (Tape Bool))
    (hguards : LogicalTapeAtHasGuardCells logical 2) :
    (action2StayDescription write?).HaltsFromTape
      (encodedStructuredTapes logical)
      (encodedStructuredTapes
        (applyPhysicalPrimitiveSequence
          (actionPrimitivesAt 2
            { write? := write?, move := HeadMove.stay })
          logical)) := by
  cases write? with
  | none =>
      rcases
          cursorTape2NoopAndReturnToBlockStartDescription_contract.realizes
            logical (encodedStructuredTapes logical)
            ⟨atExistingTapeSeparator_zero_of_atHasGuardCells hguards,
              hasAtLeastThreeTapes_of_atHasGuardCells_two hguards⟩ with
        ⟨Tout, hhalts, hseparator⟩
      have hTout : Tout = encodedStructuredTapes logical :=
        atTapeSeparator_zero_eq hseparator
      have htarget :
          applyPhysicalPrimitiveSequence
              (actionPrimitivesAt 2
                { write? := (none : Option (Option Bool)),
                  move := HeadMove.stay })
              logical =
            logical := by
        simpa [actionPrimitivesAt, writePrimitivesForAction,
          PhysicalPrimitive.apply, HeadMove.apply] using
          replaceTapeAt_tapeAt_eq_self_of_atHasGuardCells hguards
      rw [htarget]
      simpa [action2StayDescription, hTout] using hhalts
  | some cell =>
      have hwrite :=
        cursorTape2WriteHeadCellAndReturnToBlockStartDescription_haltsFromEncodedStructuredTapes_of_guardCells
          cell logical hguards
      let written :=
        (PhysicalPrimitive.writeHeadCell 2 cell).apply logical
      have hguardsWritten :
          LogicalTapeAtHasGuardCells written 2 := by
        simpa [written] using
          logicalTapeAtHasGuardCells_writeHeadCell_same cell hguards
      have htarget :
          applyPhysicalPrimitiveSequence
              (actionPrimitivesAt 2
                { write? := some cell, move := HeadMove.stay })
              logical =
            written := by
        simpa [actionPrimitivesAt, writePrimitivesForAction,
          written, PhysicalPrimitive.apply, HeadMove.apply] using
          replaceTapeAt_tapeAt_eq_self_of_atHasGuardCells
            hguardsWritten
      rw [htarget]
      simpa [action2StayDescription, written] using hwrite

theorem action0LeftLocalDescription_haltsFromEncodedStructuredTapes_of_guardCells
    (write? : Option (Option Bool)) (logical : List (Tape Bool))
    (hguards : LogicalTapeAtHasGuardCells logical 0) :
    (action0LeftLocalDescription write?).HaltsFromTape
      (encodedStructuredTapes logical)
      (encodedStructuredTapes
        (applyPhysicalPrimitiveSequence
          (actionPrimitivesAt 0
            { write? := write?, move := HeadMove.left })
          logical)) := by
  cases write? with
  | none =>
      have hmove :=
        moveHead0LeftLocalDescription_haltsFromEncodedStructuredTapes_of_guardCells
          logical hguards
      simpa [action0LeftLocalDescription, actionPrimitivesAt,
        writePrimitivesForAction, PhysicalPrimitive.apply]
        using hmove
  | some cell =>
      let written :=
        (PhysicalPrimitive.writeHeadCell 0 cell).apply logical
      have hwrite :
          (writeHeadCell0Description cell).HaltsFromTape
            (encodedStructuredTapes logical)
            (encodedStructuredTapes written) := by
        simpa [written] using
          writeHeadCell0Description_haltsFromEncodedStructuredTapes_of_guardCells
            cell logical hguards
      have hguardsWritten :
          LogicalTapeAtHasGuardCells written 0 := by
        simpa [written] using
          logicalTapeAtHasGuardCells_writeHeadCell_same cell hguards
      have hmove :
          moveHead0LeftLocalDescription.HaltsFromTape
            (encodedStructuredTapes written)
            (encodedStructuredTapes
              ((PhysicalPrimitive.moveHead 0 HeadMove.left).apply
                written)) :=
        moveHead0LeftLocalDescription_haltsFromEncodedStructuredTapes_of_guardCells
          written hguardsWritten
      have hbounce :=
        encodedStructuredTapes_bounce_zero_of_atHasGuardCells
          hguardsWritten
      have hmoveFromBounce :
          moveHead0LeftLocalDescription.HaltsFromTape
            (Tape.move Direction.left
              (Tape.move Direction.right
                (encodedStructuredTapes written)))
            (encodedStructuredTapes
              ((PhysicalPrimitive.moveHead 0 HeadMove.left).apply
                written)) := by
        rw [hbounce]
        exact hmove
      simpa [action0LeftLocalDescription, actionPrimitivesAt,
        writePrimitivesForAction, written, PhysicalPrimitive.apply]
        using
          canonicalPrimitiveSeqDescription_haltsFromTape_of_haltsFromTape
            (writeHeadCell0Description_physicalPrimitiveGuardedContract
              cell |>.subroutineReady)
            (moveHead0LeftLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
              |>.subroutineReady)
            hwrite hmoveFromBounce

theorem action0RightLocalDescription_haltsFromEncodedStructuredTapes_of_guardCells
    (write? : Option (Option Bool)) (logical : List (Tape Bool))
    (hguards : LogicalTapeAtHasGuardCells logical 0) :
    (action0RightLocalDescription write?).HaltsFromTape
      (encodedStructuredTapes logical)
      (encodedStructuredTapes
        (applyPhysicalPrimitiveSequence
          (actionPrimitivesAt 0
            { write? := write?, move := HeadMove.right })
          logical)) := by
  cases write? with
  | none =>
      have hmove :=
        moveHead0RightLocalDescription_haltsFromEncodedStructuredTapes_of_guardCells
          logical hguards
      simpa [action0RightLocalDescription, actionPrimitivesAt,
        writePrimitivesForAction, PhysicalPrimitive.apply]
        using hmove
  | some cell =>
      let written :=
        (PhysicalPrimitive.writeHeadCell 0 cell).apply logical
      have hwrite :
          (writeHeadCell0Description cell).HaltsFromTape
            (encodedStructuredTapes logical)
            (encodedStructuredTapes written) := by
        simpa [written] using
          writeHeadCell0Description_haltsFromEncodedStructuredTapes_of_guardCells
            cell logical hguards
      have hguardsWritten :
          LogicalTapeAtHasGuardCells written 0 := by
        simpa [written] using
          logicalTapeAtHasGuardCells_writeHeadCell_same cell hguards
      have hmove :
          moveHead0RightLocalDescription.HaltsFromTape
            (encodedStructuredTapes written)
            (encodedStructuredTapes
              ((PhysicalPrimitive.moveHead 0 HeadMove.right).apply
                written)) :=
        moveHead0RightLocalDescription_haltsFromEncodedStructuredTapes_of_guardCells
          written hguardsWritten
      have hbounce :=
        encodedStructuredTapes_bounce_zero_of_atHasGuardCells
          hguardsWritten
      have hmoveFromBounce :
          moveHead0RightLocalDescription.HaltsFromTape
            (Tape.move Direction.left
              (Tape.move Direction.right
                (encodedStructuredTapes written)))
            (encodedStructuredTapes
              ((PhysicalPrimitive.moveHead 0 HeadMove.right).apply
                written)) := by
        rw [hbounce]
        exact hmove
      simpa [action0RightLocalDescription, actionPrimitivesAt,
        writePrimitivesForAction, written, PhysicalPrimitive.apply]
        using
          canonicalPrimitiveSeqDescription_haltsFromTape_of_haltsFromTape
            (writeHeadCell0Description_physicalPrimitiveGuardedContract
              cell |>.subroutineReady)
            (moveHead0RightLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
              |>.subroutineReady)
            hwrite hmoveFromBounce

theorem action1LeftLocalDescription_haltsFromEncodedStructuredTapes_of_guardCells
    (write? : Option (Option Bool)) (logical : List (Tape Bool))
    (hguards : LogicalTapeAtHasGuardCells logical 1) :
    (action1LeftLocalDescription write?).HaltsFromTape
      (encodedStructuredTapes logical)
      (encodedStructuredTapes
        (applyPhysicalPrimitiveSequence
          (actionPrimitivesAt 1
            { write? := write?, move := HeadMove.left })
          logical)) := by
  cases write? with
  | none =>
      have hmove :=
        moveHead1LeftLocalDescription_haltsFromEncodedStructuredTapes_of_guardCells
          logical hguards
      simpa [action1LeftLocalDescription, actionPrimitivesAt,
        writePrimitivesForAction, PhysicalPrimitive.apply]
        using hmove
  | some cell =>
      let written :=
        (PhysicalPrimitive.writeHeadCell 1 cell).apply logical
      have hwrite :
          (cursorTape1WriteHeadCellAndReturnToBlockStartDescription
            cell).HaltsFromTape
            (encodedStructuredTapes logical)
            (encodedStructuredTapes written) := by
        simpa [written] using
          cursorTape1WriteHeadCellAndReturnToBlockStartDescription_haltsFromEncodedStructuredTapes_of_guardCells
            cell logical hguards
      have hguardsWritten :
          LogicalTapeAtHasGuardCells written 1 := by
        simpa [written] using
          logicalTapeAtHasGuardCells_writeHeadCell_same cell hguards
      have hmove :
          moveHead1LeftLocalDescription.HaltsFromTape
            (encodedStructuredTapes written)
            (encodedStructuredTapes
              ((PhysicalPrimitive.moveHead 1 HeadMove.left).apply
                written)) :=
        moveHead1LeftLocalDescription_haltsFromEncodedStructuredTapes_of_guardCells
          written hguardsWritten
      have hbounce :=
        encodedStructuredTapes_bounce_zero_of_atHasGuardCells
          hguardsWritten
      have hmoveFromBounce :
          moveHead1LeftLocalDescription.HaltsFromTape
            (Tape.move Direction.left
              (Tape.move Direction.right
                (encodedStructuredTapes written)))
            (encodedStructuredTapes
              ((PhysicalPrimitive.moveHead 1 HeadMove.left).apply
                written)) := by
        rw [hbounce]
        exact hmove
      simpa [action1LeftLocalDescription, actionPrimitivesAt,
        writePrimitivesForAction, written, PhysicalPrimitive.apply]
        using
          canonicalPrimitiveSeqDescription_haltsFromTape_of_haltsFromTape
            ((cursorTape1WriteHeadCellAndReturnToBlockStartDescription_contract
              cell).subroutineReady)
            (moveHead1LeftLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
              |>.subroutineReady)
            hwrite hmoveFromBounce

theorem action1RightLocalDescription_haltsFromEncodedStructuredTapes_of_guardCells
    (write? : Option (Option Bool)) (logical : List (Tape Bool))
    (hguards : LogicalTapeAtHasGuardCells logical 1) :
    (action1RightLocalDescription write?).HaltsFromTape
      (encodedStructuredTapes logical)
      (encodedStructuredTapes
        (applyPhysicalPrimitiveSequence
          (actionPrimitivesAt 1
            { write? := write?, move := HeadMove.right })
          logical)) := by
  cases write? with
  | none =>
      have hmove :=
        moveHead1RightLocalDescription_haltsFromEncodedStructuredTapes_of_guardCells
          logical hguards
      simpa [action1RightLocalDescription, actionPrimitivesAt,
        writePrimitivesForAction, PhysicalPrimitive.apply]
        using hmove
  | some cell =>
      let written :=
        (PhysicalPrimitive.writeHeadCell 1 cell).apply logical
      have hwrite :
          (cursorTape1WriteHeadCellAndReturnToBlockStartDescription
            cell).HaltsFromTape
            (encodedStructuredTapes logical)
            (encodedStructuredTapes written) := by
        simpa [written] using
          cursorTape1WriteHeadCellAndReturnToBlockStartDescription_haltsFromEncodedStructuredTapes_of_guardCells
            cell logical hguards
      have hguardsWritten :
          LogicalTapeAtHasGuardCells written 1 := by
        simpa [written] using
          logicalTapeAtHasGuardCells_writeHeadCell_same cell hguards
      have hmove :
          moveHead1RightLocalDescription.HaltsFromTape
            (encodedStructuredTapes written)
            (encodedStructuredTapes
              ((PhysicalPrimitive.moveHead 1 HeadMove.right).apply
                written)) :=
        moveHead1RightLocalDescription_haltsFromEncodedStructuredTapes_of_guardCells
          written hguardsWritten
      have hbounce :=
        encodedStructuredTapes_bounce_zero_of_atHasGuardCells
          hguardsWritten
      have hmoveFromBounce :
          moveHead1RightLocalDescription.HaltsFromTape
            (Tape.move Direction.left
              (Tape.move Direction.right
                (encodedStructuredTapes written)))
            (encodedStructuredTapes
              ((PhysicalPrimitive.moveHead 1 HeadMove.right).apply
                written)) := by
        rw [hbounce]
        exact hmove
      simpa [action1RightLocalDescription, actionPrimitivesAt,
        writePrimitivesForAction, written, PhysicalPrimitive.apply]
        using
          canonicalPrimitiveSeqDescription_haltsFromTape_of_haltsFromTape
            ((cursorTape1WriteHeadCellAndReturnToBlockStartDescription_contract
              cell).subroutineReady)
            (moveHead1RightLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
              |>.subroutineReady)
            hwrite hmoveFromBounce

theorem action2LeftLocalDescription_haltsFromEncodedStructuredTapes_of_guardCells
    (write? : Option (Option Bool)) (logical : List (Tape Bool))
    (hguards : LogicalTapeAtHasGuardCells logical 2) :
    (action2LeftLocalDescription write?).HaltsFromTape
      (encodedStructuredTapes logical)
      (encodedStructuredTapes
        (applyPhysicalPrimitiveSequence
          (actionPrimitivesAt 2
            { write? := write?, move := HeadMove.left })
          logical)) := by
  cases write? with
  | none =>
      have hmove :=
        moveHead2LeftLocalDescription_haltsFromEncodedStructuredTapes_of_guardCells
          logical hguards
      simpa [action2LeftLocalDescription, actionPrimitivesAt,
        writePrimitivesForAction, PhysicalPrimitive.apply]
        using hmove
  | some cell =>
      let written :=
        (PhysicalPrimitive.writeHeadCell 2 cell).apply logical
      have hwrite :
          (cursorTape2WriteHeadCellAndReturnToBlockStartDescription
            cell).HaltsFromTape
            (encodedStructuredTapes logical)
            (encodedStructuredTapes written) := by
        simpa [written] using
          cursorTape2WriteHeadCellAndReturnToBlockStartDescription_haltsFromEncodedStructuredTapes_of_guardCells
            cell logical hguards
      have hguardsWritten :
          LogicalTapeAtHasGuardCells written 2 := by
        simpa [written] using
          logicalTapeAtHasGuardCells_writeHeadCell_same cell hguards
      have hmove :
          moveHead2LeftLocalDescription.HaltsFromTape
            (encodedStructuredTapes written)
            (encodedStructuredTapes
              ((PhysicalPrimitive.moveHead 2 HeadMove.left).apply
                written)) :=
        moveHead2LeftLocalDescription_haltsFromEncodedStructuredTapes_of_guardCells
          written hguardsWritten
      have hbounce :=
        encodedStructuredTapes_bounce_zero_of_atHasGuardCells
          hguardsWritten
      have hmoveFromBounce :
          moveHead2LeftLocalDescription.HaltsFromTape
            (Tape.move Direction.left
              (Tape.move Direction.right
                (encodedStructuredTapes written)))
            (encodedStructuredTapes
              ((PhysicalPrimitive.moveHead 2 HeadMove.left).apply
                written)) := by
        rw [hbounce]
        exact hmove
      simpa [action2LeftLocalDescription, actionPrimitivesAt,
        writePrimitivesForAction, written, PhysicalPrimitive.apply]
        using
          canonicalPrimitiveSeqDescription_haltsFromTape_of_haltsFromTape
            ((cursorTape2WriteHeadCellAndReturnToBlockStartDescription_contract
              cell).subroutineReady)
            (moveHead2LeftLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
              |>.subroutineReady)
            hwrite hmoveFromBounce

theorem action2RightLocalDescription_haltsFromEncodedStructuredTapes_of_guardCells
    (write? : Option (Option Bool)) (logical : List (Tape Bool))
    (hguards : LogicalTapeAtHasGuardCells logical 2) :
    (action2RightLocalDescription write?).HaltsFromTape
      (encodedStructuredTapes logical)
      (encodedStructuredTapes
        (applyPhysicalPrimitiveSequence
          (actionPrimitivesAt 2
            { write? := write?, move := HeadMove.right })
          logical)) := by
  cases write? with
  | none =>
      have hmove :=
        moveHead2RightLocalDescription_haltsFromEncodedStructuredTapes_of_guardCells
          logical hguards
      simpa [action2RightLocalDescription, actionPrimitivesAt,
        writePrimitivesForAction, PhysicalPrimitive.apply]
        using hmove
  | some cell =>
      let written :=
        (PhysicalPrimitive.writeHeadCell 2 cell).apply logical
      have hwrite :
          (cursorTape2WriteHeadCellAndReturnToBlockStartDescription
            cell).HaltsFromTape
            (encodedStructuredTapes logical)
            (encodedStructuredTapes written) := by
        simpa [written] using
          cursorTape2WriteHeadCellAndReturnToBlockStartDescription_haltsFromEncodedStructuredTapes_of_guardCells
            cell logical hguards
      have hguardsWritten :
          LogicalTapeAtHasGuardCells written 2 := by
        simpa [written] using
          logicalTapeAtHasGuardCells_writeHeadCell_same cell hguards
      have hmove :
          moveHead2RightLocalDescription.HaltsFromTape
            (encodedStructuredTapes written)
            (encodedStructuredTapes
              ((PhysicalPrimitive.moveHead 2 HeadMove.right).apply
                written)) :=
        moveHead2RightLocalDescription_haltsFromEncodedStructuredTapes_of_guardCells
          written hguardsWritten
      have hbounce :=
        encodedStructuredTapes_bounce_zero_of_atHasGuardCells
          hguardsWritten
      have hmoveFromBounce :
          moveHead2RightLocalDescription.HaltsFromTape
            (Tape.move Direction.left
              (Tape.move Direction.right
                (encodedStructuredTapes written)))
            (encodedStructuredTapes
              ((PhysicalPrimitive.moveHead 2 HeadMove.right).apply
                written)) := by
        rw [hbounce]
        exact hmove
      simpa [action2RightLocalDescription, actionPrimitivesAt,
        writePrimitivesForAction, written, PhysicalPrimitive.apply]
        using
          canonicalPrimitiveSeqDescription_haltsFromTape_of_haltsFromTape
            ((cursorTape2WriteHeadCellAndReturnToBlockStartDescription_contract
              cell).subroutineReady)
            (moveHead2RightLocalDescription_physicalPrimitiveGuardedLogicalEquivContract
              |>.subroutineReady)
            hwrite hmoveFromBounce

theorem action0LocalMoveDescription_haltsFromEncodedStructuredTapes_of_guardCells
    (write? : Option (Option Bool)) (move : HeadMove)
    (logical : List (Tape Bool))
    (hguards : LogicalTapeAtHasGuardCells logical 0) :
    (action0LocalMoveDescription write? move).HaltsFromTape
      (encodedStructuredTapes logical)
      (encodedStructuredTapes
        (applyPhysicalPrimitiveSequence
          (actionPrimitivesAt 0
            { write? := write?, move := move })
          logical)) := by
  cases move with
  | stay =>
      simpa [action0LocalMoveDescription] using
        action0StayDescription_haltsFromEncodedStructuredTapes_of_guardCells
          write? logical hguards
  | left =>
      simpa [action0LocalMoveDescription] using
        action0LeftLocalDescription_haltsFromEncodedStructuredTapes_of_guardCells
          write? logical hguards
  | right =>
      simpa [action0LocalMoveDescription] using
        action0RightLocalDescription_haltsFromEncodedStructuredTapes_of_guardCells
          write? logical hguards

theorem action1LocalMoveDescription_haltsFromEncodedStructuredTapes_of_guardCells
    (write? : Option (Option Bool)) (move : HeadMove)
    (logical : List (Tape Bool))
    (hguards : LogicalTapeAtHasGuardCells logical 1) :
    (action1LocalMoveDescription write? move).HaltsFromTape
      (encodedStructuredTapes logical)
      (encodedStructuredTapes
        (applyPhysicalPrimitiveSequence
          (actionPrimitivesAt 1
            { write? := write?, move := move })
          logical)) := by
  cases move with
  | stay =>
      simpa [action1LocalMoveDescription] using
        action1StayDescription_haltsFromEncodedStructuredTapes_of_guardCells
          write? logical hguards
  | left =>
      simpa [action1LocalMoveDescription] using
        action1LeftLocalDescription_haltsFromEncodedStructuredTapes_of_guardCells
          write? logical hguards
  | right =>
      simpa [action1LocalMoveDescription] using
        action1RightLocalDescription_haltsFromEncodedStructuredTapes_of_guardCells
          write? logical hguards

theorem action2LocalMoveDescription_haltsFromEncodedStructuredTapes_of_guardCells
    (write? : Option (Option Bool)) (move : HeadMove)
    (logical : List (Tape Bool))
    (hguards : LogicalTapeAtHasGuardCells logical 2) :
    (action2LocalMoveDescription write? move).HaltsFromTape
      (encodedStructuredTapes logical)
      (encodedStructuredTapes
        (applyPhysicalPrimitiveSequence
          (actionPrimitivesAt 2
            { write? := write?, move := move })
          logical)) := by
  cases move with
  | stay =>
      simpa [action2LocalMoveDescription] using
        action2StayDescription_haltsFromEncodedStructuredTapes_of_guardCells
          write? logical hguards
  | left =>
      simpa [action2LocalMoveDescription] using
        action2LeftLocalDescription_haltsFromEncodedStructuredTapes_of_guardCells
          write? logical hguards
  | right =>
      simpa [action2LocalMoveDescription] using
        action2RightLocalDescription_haltsFromEncodedStructuredTapes_of_guardCells
          write? logical hguards

/--
Three-tape read-check fragment used by the slack row path.
-/
def readCheckRow3Description
    (read0 read1 read2 : Option Bool) : MachineDescription :=
  canonicalPrimitiveSeqDescription
    (canonicalPrimitiveSeqDescription
      (readCheck0Description read0)
      (readCheck1Description read1))
    (readCheck2Description read2)

theorem readCheckRow3Description_physicalPrimitiveSequenceGuardedContractEquiv
    (read0 read1 read2 : Option Bool) :
    PhysicalPrimitiveSequenceGuardedContractEquiv
      (readCheckPrimitivesAt 0 read0 ++
        readCheckPrimitivesAt 1 read1 ++
          readCheckPrimitivesAt 2 read2)
      (readCheckRow3Description read0 read1 read2) := by
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
  have h01 :=
    physicalPrimitiveSequenceGuardedContractEquiv_append
      hread0 hread1
  have hall :=
    physicalPrimitiveSequenceGuardedContractEquiv_append
      h01 hread2
  simpa [readCheckRow3Description, List.append_assoc] using hall

/--
Action-only three-tape fragment for the chainable slack route.

The machine assumes that all read checks have already succeeded and only
performs the three tape actions in tape order.  Its theorem below is exact over
an already slack-encoded logical tape list.
-/
def actionSlackRow3Description
    (write0? : Option (Option Bool)) (move0 : HeadMove)
    (write1? : Option (Option Bool)) (move1 : HeadMove)
    (write2? : Option (Option Bool)) (move2 : HeadMove) :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    (canonicalPrimitiveSeqDescription
      (action0LocalMoveDescription write0? move0)
      (action1LocalMoveDescription write1? move1))
    (action2LocalMoveDescription write2? move2)

theorem actionSlackRow3Description_subroutineReady
    (write0? : Option (Option Bool)) (move0 : HeadMove)
    (write1? : Option (Option Bool)) (move1 : HeadMove)
    (write2? : Option (Option Bool)) (move2 : HeadMove) :
    (actionSlackRow3Description
      write0? move0 write1? move1 write2? move2).SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    (canonicalPrimitiveSeqDescription_subroutineReady
      (action0LocalMoveDescription_physicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
        write0? move0 |>.subroutineReady)
      (action1LocalMoveDescription_physicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
        write1? move1 |>.subroutineReady))
    (action2LocalMoveDescription_physicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
      write2? move2 |>.subroutineReady)

theorem actionSlackRow3Description_haltsFromEncodedStructuredTapes_of_guardCells
    (write0? : Option (Option Bool)) (move0 : HeadMove)
    (write1? : Option (Option Bool)) (move1 : HeadMove)
    (write2? : Option (Option Bool)) (move2 : HeadMove)
    (logical : List (Tape Bool))
    (hguards0 : LogicalTapeAtHasGuardCells logical 0)
    (hguards1 :
      LogicalTapeAtHasGuardCells
        (applyPhysicalPrimitiveSequence
          (actionPrimitivesAt 0
            { write? := write0?, move := move0 })
          logical)
        1)
    (hguards2 :
      LogicalTapeAtHasGuardCells
        (applyPhysicalPrimitiveSequence
          (actionPrimitivesAt 1
            { write? := write1?, move := move1 })
          (applyPhysicalPrimitiveSequence
            (actionPrimitivesAt 0
              { write? := write0?, move := move0 })
            logical))
        2) :
    (actionSlackRow3Description
      write0? move0 write1? move1 write2? move2).HaltsFromTape
      (encodedStructuredTapes logical)
      (encodedStructuredTapes
        (applyPhysicalPrimitiveSequence
          (actionPrimitivesAt 0
            { write? := write0?, move := move0 } ++
            actionPrimitivesAt 1
              { write? := write1?, move := move1 } ++
            actionPrimitivesAt 2
              { write? := write2?, move := move2 })
          logical)) := by
  let action0 :=
    actionPrimitivesAt 0 { write? := write0?, move := move0 }
  let action1 :=
    actionPrimitivesAt 1 { write? := write1?, move := move1 }
  let action2 :=
    actionPrimitivesAt 2 { write? := write2?, move := move2 }
  let logical1 := applyPhysicalPrimitiveSequence action0 logical
  let logical2 := applyPhysicalPrimitiveSequence action1 logical1
  let logical3 := applyPhysicalPrimitiveSequence action2 logical2
  have haction0 :
      (action0LocalMoveDescription write0? move0).HaltsFromTape
        (encodedStructuredTapes logical)
        (encodedStructuredTapes logical1) := by
    simpa [logical1, action0] using
      action0LocalMoveDescription_haltsFromEncodedStructuredTapes_of_guardCells
        write0? move0 logical hguards0
  have hguards1' : LogicalTapeAtHasGuardCells logical1 1 := by
    simpa [logical1, action0] using hguards1
  have haction1 :
      (action1LocalMoveDescription write1? move1).HaltsFromTape
        (Tape.move Direction.left
          (Tape.move Direction.right
            (encodedStructuredTapes logical1)))
        (encodedStructuredTapes logical2) := by
    rw [encodedStructuredTapes_bounce_zero_of_atHasGuardCells
      hguards1']
    simpa [logical2, action1] using
      action1LocalMoveDescription_haltsFromEncodedStructuredTapes_of_guardCells
        write1? move1 logical1 hguards1'
  have hfirst :
      (canonicalPrimitiveSeqDescription
        (action0LocalMoveDescription write0? move0)
        (action1LocalMoveDescription write1? move1)).HaltsFromTape
        (encodedStructuredTapes logical)
        (encodedStructuredTapes logical2) :=
    canonicalPrimitiveSeqDescription_haltsFromTape_of_haltsFromTape
      (action0LocalMoveDescription_physicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
        write0? move0 |>.subroutineReady)
      (action1LocalMoveDescription_physicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
        write1? move1 |>.subroutineReady)
      haction0 haction1
  have hguards2' : LogicalTapeAtHasGuardCells logical2 2 := by
    simpa [logical1, logical2, action0, action1] using hguards2
  have haction2 :
      (action2LocalMoveDescription write2? move2).HaltsFromTape
        (Tape.move Direction.left
          (Tape.move Direction.right
            (encodedStructuredTapes logical2)))
        (encodedStructuredTapes logical3) := by
    rw [encodedStructuredTapes_bounce_zero_of_atHasGuardCells
      hguards2']
    simpa [logical3, action2] using
      action2LocalMoveDescription_haltsFromEncodedStructuredTapes_of_guardCells
        write2? move2 logical2 hguards2'
  have htarget :
      applyPhysicalPrimitiveSequence
          (actionPrimitivesAt 0
            { write? := write0?, move := move0 } ++
            actionPrimitivesAt 1
              { write? := write1?, move := move1 } ++
            actionPrimitivesAt 2
              { write? := write2?, move := move2 })
          logical =
        logical3 := by
    simp [logical1, logical2, logical3, action0, action1, action2,
      applyPhysicalPrimitiveSequence_append]
  rw [htarget]
  simpa [actionSlackRow3Description] using
    canonicalPrimitiveSeqDescription_haltsFromTape_of_haltsFromTape
      (canonicalPrimitiveSeqDescription_subroutineReady
        (action0LocalMoveDescription_physicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
          write0? move0 |>.subroutineReady)
        (action1LocalMoveDescription_physicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
          write1? move1 |>.subroutineReady))
      (action2LocalMoveDescription_physicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
        write2? move2 |>.subroutineReady)
      hfirst haction2

theorem actionSlackRow3Description_haltsFromEncodedStructuredThreeTapes_of_guardCells
    (write0? : Option (Option Bool)) (move0 : HeadMove)
    (write1? : Option (Option Bool)) (move1 : HeadMove)
    (write2? : Option (Option Bool)) (move2 : HeadMove)
    (T U V : Tape Bool)
    (hT : LogicalTapeHasGuardCells T)
    (hU : LogicalTapeHasGuardCells U)
    (hV : LogicalTapeHasGuardCells V) :
    (actionSlackRow3Description
      write0? move0 write1? move1 write2? move2).HaltsFromTape
      (encodedStructuredTapes [T, U, V])
      (encodedStructuredTapes
        [({ write? := write0?, move := move0 } : TapeAction).apply T,
          ({ write? := write1?, move := move1 } : TapeAction).apply U,
          ({ write? := write2?, move := move2 } : TapeAction).apply V]) := by
  let action0 : TapeAction := { write? := write0?, move := move0 }
  let action1 : TapeAction := { write? := write1?, move := move1 }
  let action2 : TapeAction := { write? := write2?, move := move2 }
  have hguards0 : LogicalTapeAtHasGuardCells [T, U, V] 0 :=
    ⟨T, [U, V], rfl, hT⟩
  have hguards1 :
      LogicalTapeAtHasGuardCells
        (applyPhysicalPrimitiveSequence
          (actionPrimitivesAt 0 action0) [T, U, V]) 1 := by
    rw [applyPhysicalPrimitiveSequence_actionPrimitivesAt_zero_three]
    exact ⟨U, [V], rfl, hU⟩
  have hguards2 :
      LogicalTapeAtHasGuardCells
        (applyPhysicalPrimitiveSequence
          (actionPrimitivesAt 1 action1)
          (applyPhysicalPrimitiveSequence
            (actionPrimitivesAt 0 action0) [T, U, V])) 2 := by
    rw [applyPhysicalPrimitiveSequence_actionPrimitivesAt_zero_three]
    rw [applyPhysicalPrimitiveSequence_actionPrimitivesAt_one_three]
    exact ⟨V, [], rfl, hV⟩
  have hrun :=
    actionSlackRow3Description_haltsFromEncodedStructuredTapes_of_guardCells
      write0? move0 write1? move1 write2? move2
      [T, U, V] hguards0
      (by simpa [action0] using hguards1)
      (by simpa [action0, action1] using hguards2)
  simpa [action0, action1, action2,
    applyPhysicalPrimitiveSequence_append,
    applyPhysicalPrimitiveSequence_actionPrimitivesAt_zero_three,
    applyPhysicalPrimitiveSequence_actionPrimitivesAt_one_three,
    applyPhysicalPrimitiveSequence_actionPrimitivesAt_two_three]
    using hrun

theorem actionSlackRow3Description_haltsFromEncodedGuardedStructuredThreeTapes
    (write0? : Option (Option Bool)) (move0 : HeadMove)
    (write1? : Option (Option Bool)) (move1 : HeadMove)
    (write2? : Option (Option Bool)) (move2 : HeadMove)
    (T U V : Tape Bool) :
    (actionSlackRow3Description
      write0? move0 write1? move1 write2? move2).HaltsFromTape
      (encodedGuardedStructuredTapes [T, U, V])
      (encodedStructuredTapes
        [({ write? := write0?, move := move0 } : TapeAction).apply
            (guardLogicalTape T),
          ({ write? := write1?, move := move1 } : TapeAction).apply
            (guardLogicalTape U),
          ({ write? := write2?, move := move2 } : TapeAction).apply
            (guardLogicalTape V)]) := by
  simpa [encodedGuardedStructuredTapes, guardLogicalTapes] using
    actionSlackRow3Description_haltsFromEncodedStructuredThreeTapes_of_guardCells
      write0? move0 write1? move1 write2? move2
      (guardLogicalTape T) (guardLogicalTape U) (guardLogicalTape V)
      (guardLogicalTape_hasGuardCells T)
      (guardLogicalTape_hasGuardCells U)
      (guardLogicalTape_hasGuardCells V)

/--
Full three-tape read/action fragment for the slack row path.

This composes the canonical guarded read checks with the action-only slack row.
The result is an equivalence run because the read phase uses the existing
guarded equivalence contracts, while the action phase is exact from the
canonical guarded endpoint.
-/
def readActionSlackRow3Description
    (read0 read1 read2 : Option Bool)
    (write0? : Option (Option Bool)) (move0 : HeadMove)
    (write1? : Option (Option Bool)) (move1 : HeadMove)
    (write2? : Option (Option Bool)) (move2 : HeadMove) :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    (readCheckRow3Description read0 read1 read2)
    (actionSlackRow3Description
      write0? move0 write1? move1 write2? move2)

theorem readActionSlackRow3Description_haltsFromEncodedGuardedStructuredThreeTapes
    (read0 read1 read2 : Option Bool)
    (write0? : Option (Option Bool)) (move0 : HeadMove)
    (write1? : Option (Option Bool)) (move1 : HeadMove)
    (write2? : Option (Option Bool)) (move2 : HeadMove)
    (T U V : Tape Bool)
    (hread0 : Tape.read T = read0)
    (hread1 : Tape.read U = read1)
    (hread2 : Tape.read V = read2) :
    (readActionSlackRow3Description read0 read1 read2
      write0? move0 write1? move1 write2? move2).HaltsFromTapeEquiv
      (encodedGuardedStructuredTapes [T, U, V])
      (encodedStructuredTapes
        [({ write? := write0?, move := move0 } : TapeAction).apply
            (guardLogicalTape T),
          ({ write? := write1?, move := move1 } : TapeAction).apply
            (guardLogicalTape U),
          ({ write? := write2?, move := move2 } : TapeAction).apply
            (guardLogicalTape V)]) := by
  let action0 : TapeAction := { write? := write0?, move := move0 }
  let action1 : TapeAction := { write? := write1?, move := move1 }
  let action2 : TapeAction := { write? := write2?, move := move2 }
  have hreadEnabled :
      physicalPrimitiveSequenceEnabled
        (readCheckPrimitivesAt 0 read0 ++
          readCheckPrimitivesAt 1 read1 ++
            readCheckPrimitivesAt 2 read2)
        [T, U, V] := by
    simp [readCheckPrimitivesAt, PhysicalPrimitive.apply,
      Description.tapeAt, hread0, hread1, hread2]
  have hreadRunRaw :=
    (readCheckRow3Description_physicalPrimitiveSequenceGuardedContractEquiv
      read0 read1 read2).realizes [T, U, V] hreadEnabled
  have hreadRun :
      (readCheckRow3Description read0 read1 read2).HaltsFromTapeEquiv
        (encodedGuardedStructuredTapes [T, U, V])
        (encodedGuardedStructuredTapes [T, U, V]) := by
    simpa [readCheckRow3Description, readCheckPrimitivesAt,
      applyPhysicalPrimitiveSequence_append] using hreadRunRaw
  have hactionRun :
      (actionSlackRow3Description
        write0? move0 write1? move1 write2? move2).HaltsFromTape
        (encodedGuardedStructuredTapes [T, U, V])
        (encodedStructuredTapes
          [action0.apply (guardLogicalTape T),
            action1.apply (guardLogicalTape U),
            action2.apply (guardLogicalTape V)]) := by
    simpa [action0, action1, action2] using
      actionSlackRow3Description_haltsFromEncodedGuardedStructuredThreeTapes
        write0? move0 write1? move1 write2? move2 T U V
  simpa [readActionSlackRow3Description, action0, action1, action2] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      (readCheckRow3Description_physicalPrimitiveSequenceGuardedContractEquiv
        read0 read1 read2 |>.subroutineReady)
      (actionSlackRow3Description_subroutineReady
        write0? move0 write1? move1 write2? move2)
      hreadRun
      (MachineDescription.HaltsFromTape.toEquiv hactionRun)

theorem readActionSlackRow3Description_lowersGuardedTransitionLogicalEquiv
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (read0 read1 read2 : Option Bool)
    (write0? : Option (Option Bool)) (move0 : HeadMove)
    (write1? : Option (Option Bool)) (move1 : HeadMove)
    (write2? : Option (Option Bool)) (move2 : HeadMove)
    (hreads : t.reads = [read0, read1, read2])
    (hactions :
      t.actions =
        [ { write? := write0?, move := move0 }
        , { write? := write1?, move := move1 }
        , { write? := write2?, move := move2 } ]) :
    LowersGuardedTransitionLogicalEquiv D t
      (readActionSlackRow3Description read0 read1 read2
        write0? move0 write1? move1 write2? move2) where
  subroutineReady :=
    canonicalPrimitiveSeqDescription_subroutineReady
      (readCheckRow3Description_physicalPrimitiveSequenceGuardedContractEquiv
        read0 read1 read2 |>.subroutineReady)
      (actionSlackRow3Description_subroutineReady
        write0? move0 write1? move1 write2? move2)
  realizes := by
    intro c hc _hsource hcurrentReads
    have hlen : c.tapes.length = 3 := by
      simpa [hD] using hc
    rcases list_eq_three_of_length_eq_three hlen with
      ⟨T, U, V, htapes⟩
    cases c with
    | mk state tapes =>
        simp at htapes
        cases htapes
        let action0 : TapeAction := { write? := write0?, move := move0 }
        let action1 : TapeAction := { write? := write1?, move := move1 }
        let action2 : TapeAction := { write? := write2?, move := move2 }
        have hreadsEq :
            [read0, read1, read2] =
              [Tape.read T, Tape.read U, Tape.read V] := by
          simpa [hreads, hD] using hcurrentReads
        have hreadsComponents :
            read0 = Tape.read T ∧
              read1 = Tape.read U ∧
                read2 = Tape.read V := by
          simpa using hreadsEq
        rcases hreadsComponents with ⟨hread0', hread1', hread2'⟩
        have hread0 : Tape.read T = read0 := hread0'.symm
        have hread1 : Tape.read U = read1 := hread1'.symm
        have hread2 : Tape.read V = read2 := hread2'.symm
        have hrun :=
          readActionSlackRow3Description_haltsFromEncodedGuardedStructuredThreeTapes
            read0 read1 read2
            write0? move0 write1? move1 write2? move2
            T U V hread0 hread1 hread2
        let actual : List (Tape Bool) :=
          [action0.apply (guardLogicalTape T),
            action1.apply (guardLogicalTape U),
            action2.apply (guardLogicalTape V)]
        have htarget :
            D.applyActions
                [action0, action1, action2] [T, U, V] =
              [action0.apply T, action1.apply U, action2.apply V] :=
          Description.applyActions_three D hD
            action0 action1 action2 T U V
        have hequiv :
            LogicalTapeListEquiv actual
              (D.applyActions t.actions [T, U, V]) := by
          rw [hactions, htarget]
          exact
            ⟨Tape.Equiv.trans
                (guardLogicalTape_action_equiv action0 T)
                (guardLogicalTape_equiv (action0.apply T)),
              ⟨Tape.Equiv.trans
                  (guardLogicalTape_action_equiv action1 U)
                  (guardLogicalTape_equiv (action1.apply U)),
                ⟨Tape.Equiv.trans
                    (guardLogicalTape_action_equiv action2 V)
                    (guardLogicalTape_equiv (action2.apply V)),
                  trivial⟩⟩⟩
        refine
          ⟨encodedStructuredTapes actual,
            ⟨actual, hequiv, rfl⟩, ?_⟩
        simpa [readActionSlackRow3Description, action0, action1,
          action2, actual] using hrun

theorem readActionSlackRow3Description_lowersGuardedTransitionGuardSlack
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (read0 read1 read2 : Option Bool)
    (write0? : Option (Option Bool)) (move0 : HeadMove)
    (write1? : Option (Option Bool)) (move1 : HeadMove)
    (write2? : Option (Option Bool)) (move2 : HeadMove)
    (hreads : t.reads = [read0, read1, read2])
    (hactions :
      t.actions =
        [ { write? := write0?, move := move0 }
        , { write? := write1?, move := move1 }
        , { write? := write2?, move := move2 } ]) :
    LowersGuardedTransitionGuardSlack D t
      (readActionSlackRow3Description read0 read1 read2
        write0? move0 write1? move1 write2? move2) where
  subroutineReady :=
    canonicalPrimitiveSeqDescription_subroutineReady
      (readCheckRow3Description_physicalPrimitiveSequenceGuardedContractEquiv
        read0 read1 read2 |>.subroutineReady)
      (actionSlackRow3Description_subroutineReady
        write0? move0 write1? move1 write2? move2)
  realizes := by
    intro c hc _hsource hcurrentReads
    have hlen : c.tapes.length = 3 := by
      simpa [hD] using hc
    rcases list_eq_three_of_length_eq_three hlen with
      ⟨T, U, V, htapes⟩
    cases c with
    | mk state tapes =>
        simp at htapes
        cases htapes
        let action0 : TapeAction := { write? := write0?, move := move0 }
        let action1 : TapeAction := { write? := write1?, move := move1 }
        let action2 : TapeAction := { write? := write2?, move := move2 }
        have hreadsEq :
            [read0, read1, read2] =
              [Tape.read T, Tape.read U, Tape.read V] := by
          simpa [hreads, hD] using hcurrentReads
        have hreadsComponents :
            read0 = Tape.read T ∧
              read1 = Tape.read U ∧
                read2 = Tape.read V := by
          simpa using hreadsEq
        rcases hreadsComponents with ⟨hread0', hread1', hread2'⟩
        have hread0 : Tape.read T = read0 := hread0'.symm
        have hread1 : Tape.read U = read1 := hread1'.symm
        have hread2 : Tape.read V = read2 := hread2'.symm
        have hrun :=
          readActionSlackRow3Description_haltsFromEncodedGuardedStructuredThreeTapes
            read0 read1 read2
            write0? move0 write1? move1 write2? move2
            T U V hread0 hread1 hread2
        let actual : List (Tape Bool) :=
          [action0.apply (guardLogicalTape T),
            action1.apply (guardLogicalTape U),
            action2.apply (guardLogicalTape V)]
        have hsourceApply :
            applyPhysicalPrimitiveSequence
                (transitionPrimitiveSequenceOfRow3 t) [T, U, V] =
              D.applyActions t.actions [T, U, V] := by
          rw [applyPhysicalPrimitiveSequence_transitionPrimitiveSequenceOfRow3
            t read0 read1 read2 action0 action1 action2 T U V
            hreads hactions]
          rw [hactions]
          exact (Description.applyActions_three D hD
            action0 action1 action2 T U V).symm
        have hguardApply :
            applyPhysicalPrimitiveSequence
                (transitionPrimitiveSequenceOfRow3 t)
                (guardLogicalTapes [T, U, V]) =
              actual := by
          change
            applyPhysicalPrimitiveSequence
                (transitionPrimitiveSequenceOfRow3 t)
                [guardLogicalTape T, guardLogicalTape U,
                  guardLogicalTape V] =
              actual
          simpa [actual] using
            applyPhysicalPrimitiveSequence_transitionPrimitiveSequenceOfRow3
              t read0 read1 read2 action0 action1 action2
              (guardLogicalTape T) (guardLogicalTape U)
              (guardLogicalTape V) hreads hactions
        have hendpoint :
            PhysicalPrimitiveSequenceGuardSlackEndpoint
              (transitionPrimitiveSequenceOfRow3 t)
              [T, U, V]
              (D.applyActions t.actions [T, U, V])
              (encodedStructuredTapes actual) := by
          exact ⟨hsourceApply.symm, by
            rw [hguardApply]⟩
        refine
          ⟨encodedStructuredTapes actual, hendpoint, ?_⟩
        simpa [readActionSlackRow3Description, action0, action1,
          action2, actual] using hrun

def readActionSlackRow3DescriptionWithGuardSlackRefresh
    (read0 read1 read2 : Option Bool)
    (write0? : Option (Option Bool)) (move0 : HeadMove)
    (write1? : Option (Option Bool)) (move1 : HeadMove)
    (write2? : Option (Option Bool)) (move2 : HeadMove)
    (refresh : MachineDescription) : MachineDescription :=
  guardedLogicalEquivThenRefreshDescription
    (readActionSlackRow3Description read0 read1 read2
      write0? move0 write1? move1 write2? move2)
    refresh

theorem readActionSlackRow3DescriptionWithGuardSlackRefresh_lowersGuardedTransitionEquiv
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (read0 read1 read2 : Option Bool)
    (write0? : Option (Option Bool)) (move0 : HeadMove)
    (write1? : Option (Option Bool)) (move1 : HeadMove)
    (write2? : Option (Option Bool)) (move2 : HeadMove)
    (hreads : t.reads = [read0, read1, read2])
    (hactions :
      t.actions =
        [ { write? := write0?, move := move0 }
        , { write? := write1?, move := move1 }
        , { write? := write2?, move := move2 } ])
    {refresh : MachineDescription}
    (hrefresh : GuardSlackRefreshContract refresh) :
    LowersGuardedTransitionEquiv D t
      (readActionSlackRow3DescriptionWithGuardSlackRefresh
        read0 read1 read2
        write0? move0 write1? move1 write2? move2 refresh) := by
  simpa [readActionSlackRow3DescriptionWithGuardSlackRefresh] using
    lowersGuardedTransitionGuardSlack_thenRefresh
      (readActionSlackRow3Description_lowersGuardedTransitionGuardSlack
        D t hD read0 read1 read2
        write0? move0 write1? move1 write2? move2
        hreads hactions)
      hrefresh

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
