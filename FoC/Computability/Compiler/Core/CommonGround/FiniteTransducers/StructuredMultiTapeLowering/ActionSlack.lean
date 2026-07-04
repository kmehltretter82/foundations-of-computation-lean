import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.PrimitivePipelines

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

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
