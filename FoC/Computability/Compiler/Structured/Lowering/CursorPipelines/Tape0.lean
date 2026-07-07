import FoC.Computability.Compiler.Structured.Lowering.CursorComposition
import FoC.Computability.Compiler.Structured.Lowering.CursorHead

set_option doc.verso true

/-!
# Structured cursor pipelines

This module starts assembling concrete cursor routines into reusable physical
pipeline fragments.  These are still cursor-level contracts; guarded primitive
contracts will wrap them at canonical block boundaries.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

/--
Move right from a selected tape separator and scan to that tape's head marker.
-/
def cursorEnterAndScanToHeadMarkerDescription :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    (cursorMoveOnceDescription Direction.right)
    cursorScanToHeadMarkerDescription

theorem cursorEnterAndScanToHeadMarkerDescription_contract
    (tapeIndex : Nat) :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator logical tapeIndex physical)
      (fun logical physical =>
        AtTapeHeadMarker logical tapeIndex physical)
      cursorEnterAndScanToHeadMarkerDescription :=
  cursorRoutineContract_canonicalSeq_self
    (cursorMoveRightDescription_contract_separator_to_segmentEntry
      tapeIndex)
    (cursorScanToHeadMarkerDescription_contract tapeIndex)
    (by
      intro logical physical hentry
      exact atTapeSegmentEntry_moveLeft_moveRight hentry)

/--
Move right from a selected tape separator, scan to the head marker, and move
onto the encoded head-cell code.
-/
def cursorEnterAndMoveToHeadCellDescription :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    cursorEnterAndScanToHeadMarkerDescription
    cursorMoveHeadMarkerToCellDescription

theorem cursorEnterAndMoveToHeadCellDescription_contract
    (tapeIndex : Nat) :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator logical tapeIndex physical)
      (fun logical physical =>
        AtTapeHeadCellCode logical tapeIndex physical)
      cursorEnterAndMoveToHeadCellDescription :=
  cursorRoutineContract_canonicalSeq_self
    (cursorEnterAndScanToHeadMarkerDescription_contract tapeIndex)
    (cursorMoveHeadMarkerToCellDescription_contract tapeIndex)
    (by
      intro logical physical hmarker
      exact atTapeHeadMarker_moveLeft_moveRight hmarker)

theorem cursorEnterAndMoveToHeadCellDescription_contract_withRead
    (tapeIndex : Nat) (expected : Option Bool) :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator logical tapeIndex physical ∧
          Tape.read (Description.tapeAt logical tapeIndex) = expected)
      (fun logical physical =>
        AtTapeHeadCellCodeWithRead logical tapeIndex expected physical)
      cursorEnterAndMoveToHeadCellDescription where
  subroutineReady :=
    (cursorEnterAndMoveToHeadCellDescription_contract tapeIndex).subroutineReady
  realizes := by
    intro logical Tin hsource
    rcases hsource with ⟨hseparator, hread⟩
    rcases
        (cursorEnterAndMoveToHeadCellDescription_contract
          tapeIndex).realizes logical Tin hseparator with
      ⟨Tout, hhalts, hcell⟩
    exact
      ⟨Tout, hhalts,
        atTapeHeadCellCode_to_withRead hcell hread⟩

/--
Move from a selected tape separator to the encoded head cell and verify the
expected logical read.
-/
def cursorEnterReadHeadCellDescription
    (expected : Option Bool) : MachineDescription :=
  canonicalPrimitiveSeqDescription
    cursorEnterAndMoveToHeadCellDescription
    (readHeadCellCodeDescription expected)

theorem cursorEnterReadHeadCellDescription_contract
    (tapeIndex : Nat) (expected : Option Bool) :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator logical tapeIndex physical ∧
          Tape.read (Description.tapeAt logical tapeIndex) = expected)
      (fun logical physical =>
        AtTapeHeadCellCode logical tapeIndex physical)
      (cursorEnterReadHeadCellDescription expected) :=
  cursorRoutineContract_canonicalSeq_self
    (cursorEnterAndMoveToHeadCellDescription_contract_withRead
      tapeIndex expected)
    (readHeadCellCodeDescription_contract tapeIndex expected)
    (by
      intro logical physical hcell
      exact atTapeHeadCellCodeWithRead_moveLeft_moveRight hcell)

/--
Verify the expected logical read from a selected separator and return to that
separator.
-/
def cursorReadHeadCellAndReturnToSeparatorDescription
    (expected : Option Bool) : MachineDescription :=
  canonicalPrimitiveSeqDescription
    (cursorEnterReadHeadCellDescription expected)
    returnToOpeningSeparatorDescription

theorem cursorReadHeadCellAndReturnToSeparatorDescription_contract
    (tapeIndex : Nat) (expected : Option Bool) :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator logical tapeIndex physical ∧
          Tape.read (Description.tapeAt logical tapeIndex) = expected)
      (fun logical physical =>
        AtTapeSeparator logical tapeIndex physical)
      (cursorReadHeadCellAndReturnToSeparatorDescription expected) :=
  cursorRoutineContract_canonicalSeq_self
    (cursorEnterReadHeadCellDescription_contract tapeIndex expected)
    (returnToOpeningSeparatorDescription_contract_headCell tapeIndex)
    (by
      intro logical physical hcell
      exact atTapeHeadCellCode_moveLeft_moveRight hcell)

/--
Move from a selected tape separator to the encoded head cell and overwrite its
logical value.
-/
def cursorEnterWriteHeadCellDescription
    (cell : Option Bool) : MachineDescription :=
  canonicalPrimitiveSeqDescription
    cursorEnterAndMoveToHeadCellDescription
    (writeHeadCellCodeDescription cell)

theorem cursorEnterWriteHeadCellDescription_contract
    (tapeIndex : Nat) (cell : Option Bool) :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator logical tapeIndex physical)
      (fun logical physical =>
        AtTapeHeadCellCode
          ((PhysicalPrimitive.writeHeadCell tapeIndex cell).apply
            logical)
          tapeIndex physical)
      (cursorEnterWriteHeadCellDescription cell) :=
  cursorRoutineContract_canonicalSeq_self
    (cursorEnterAndMoveToHeadCellDescription_contract tapeIndex)
    (writeHeadCellCodeDescription_contract tapeIndex cell)
    (by
      intro logical physical hcell
      exact atTapeHeadCellCode_moveLeft_moveRight hcell)

/--
Overwrite the selected tape head cell and return to the selected separator.
-/
def cursorWriteHeadCellAndReturnToSeparatorDescription
    (cell : Option Bool) : MachineDescription :=
  canonicalPrimitiveSeqDescription
    (cursorEnterWriteHeadCellDescription cell)
    returnToOpeningSeparatorDescription

theorem cursorWriteHeadCellAndReturnToSeparatorDescription_contract
    (tapeIndex : Nat) (cell : Option Bool) :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator logical tapeIndex physical)
      (fun logical physical =>
        AtTapeSeparator
          ((PhysicalPrimitive.writeHeadCell tapeIndex cell).apply
            logical)
          tapeIndex physical)
      (cursorWriteHeadCellAndReturnToSeparatorDescription cell) := by
  have hreturn :
      CursorRoutineContract
        (fun logical physical =>
          AtTapeHeadCellCode
            ((PhysicalPrimitive.writeHeadCell tapeIndex cell).apply
              logical)
            tapeIndex physical)
        (fun logical physical =>
          AtTapeSeparator
            ((PhysicalPrimitive.writeHeadCell tapeIndex cell).apply
              logical)
            tapeIndex physical)
        returnToOpeningSeparatorDescription := by
    exact
      { subroutineReady :=
          (returnToOpeningSeparatorDescription_contract_headCell
            tapeIndex).subroutineReady
        realizes := by
          intro logical Tin hsource
          exact
            (returnToOpeningSeparatorDescription_contract_headCell
              tapeIndex).realizes
              ((PhysicalPrimitive.writeHeadCell tapeIndex cell).apply
                logical)
              Tin hsource }
  exact
    cursorRoutineContract_canonicalSeq_self
      (cursorEnterWriteHeadCellDescription_contract tapeIndex cell)
      hreturn
      (by
        intro logical physical hcell
        exact atTapeHeadCellCode_moveLeft_moveRight hcell)

/--
Enter a guarded tape segment and move the selected logical head one cell left.

The endpoint is intentionally stated over
{lit}`(PhysicalPrimitive.moveHead ...).apply (guardLogicalTapes logical)`.
This is the consumed-guard layout produced by the local marker swap.  It is not
the canonical re-guarded endpoint yet.
-/
def cursorEnterMoveHeadLeftLocalDescription :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    cursorEnterAndMoveToHeadCellDescription
    moveHeadLeftLocalDescription

theorem cursorEnterMoveHeadLeftLocalDescription_contract_guarded
    (tapeIndex : Nat) :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator (guardLogicalTapes logical)
          tapeIndex physical)
      (fun logical physical =>
        AtTapeHeadCellCode
          ((PhysicalPrimitive.moveHead tapeIndex HeadMove.left).apply
            (guardLogicalTapes logical))
          tapeIndex physical)
      cursorEnterMoveHeadLeftLocalDescription := by
  have henter :
      CursorRoutineContract
        (fun logical physical =>
          AtExistingTapeSeparator (guardLogicalTapes logical)
            tapeIndex physical)
        (fun logical physical =>
          AtTapeHeadCellCode (guardLogicalTapes logical)
            tapeIndex physical)
        cursorEnterAndMoveToHeadCellDescription := by
    exact
      { subroutineReady :=
          (cursorEnterAndMoveToHeadCellDescription_contract
            tapeIndex).subroutineReady
        realizes := by
          intro logical Tin hsource
          exact
            (cursorEnterAndMoveToHeadCellDescription_contract
              tapeIndex).realizes
              (guardLogicalTapes logical) Tin hsource }
  have hmove :
      CursorRoutineContract
        (fun logical physical =>
          AtTapeHeadCellCodeWithLeftNeighbor
            (guardLogicalTapes logical) tapeIndex physical)
        (fun logical physical =>
          AtTapeHeadCellCode
            ((PhysicalPrimitive.moveHead tapeIndex HeadMove.left).apply
              (guardLogicalTapes logical))
            tapeIndex physical)
        moveHeadLeftLocalDescription := by
    exact
      { subroutineReady :=
          (moveHeadLeftLocalDescription_contract
            tapeIndex).subroutineReady
        realizes := by
          intro logical Tin hsource
          exact
            (moveHeadLeftLocalDescription_contract
              tapeIndex).realizes
              (guardLogicalTapes logical) Tin hsource }
  exact
    cursorRoutineContract_canonicalSeq henter hmove
      (by
        intro logical physical hcell
        rw [atTapeHeadCellCode_moveLeft_moveRight hcell]
        exact guardedAtTapeHeadCellCode_to_leftNeighbor hcell)

theorem cursorEnterMoveHeadLeftLocalDescription_contract_withGuardCells
    (tapeIndex : Nat) :
    CursorRoutineContract
      (fun logical physical =>
        LogicalTapeAtHasGuardCells logical tapeIndex ∧
          AtExistingTapeSeparator logical tapeIndex physical)
      (fun logical physical =>
        AtTapeHeadCellCode
          ((PhysicalPrimitive.moveHead tapeIndex HeadMove.left).apply
            logical)
          tapeIndex physical)
      cursorEnterMoveHeadLeftLocalDescription := by
  have henter :
      CursorRoutineContract
        (fun logical physical =>
          LogicalTapeAtHasGuardCells logical tapeIndex ∧
            AtExistingTapeSeparator logical tapeIndex physical)
        (fun logical physical =>
          LogicalTapeAtHasGuardCells logical tapeIndex ∧
            AtTapeHeadCellCode logical tapeIndex physical)
        cursorEnterAndMoveToHeadCellDescription := by
    exact
      { subroutineReady :=
          (cursorEnterAndMoveToHeadCellDescription_contract
            tapeIndex).subroutineReady
        realizes := by
          intro logical Tin hsource
          rcases hsource with ⟨hguards, hseparator⟩
          rcases
              (cursorEnterAndMoveToHeadCellDescription_contract
                tapeIndex).realizes logical Tin hseparator with
            ⟨Tout, hhalts, hcell⟩
          exact ⟨Tout, hhalts, hguards, hcell⟩ }
  have hmove :
      CursorRoutineContract
        (fun logical physical =>
          AtTapeHeadCellCodeWithLeftNeighbor logical tapeIndex physical)
        (fun logical physical =>
          AtTapeHeadCellCode
            ((PhysicalPrimitive.moveHead tapeIndex HeadMove.left).apply
              logical)
            tapeIndex physical)
        moveHeadLeftLocalDescription :=
    moveHeadLeftLocalDescription_contract tapeIndex
  exact
    cursorRoutineContract_canonicalSeq henter hmove
      (by
        intro logical physical hcell
        rw [atTapeHeadCellCode_moveLeft_moveRight hcell.right]
        exact
          atTapeHeadCellCode_to_leftNeighbor_of_guardCells
            hcell.left hcell.right)

/--
Enter a guarded tape segment and move the selected logical head one cell right.

As for {name}`cursorEnterMoveHeadLeftLocalDescription`, this exposes the
consumed-guard layout.  A later guard-refresh routine must convert that layout
back to the canonical guarded endpoint used by row contracts.
-/
def cursorEnterMoveHeadRightLocalDescription :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    cursorEnterAndMoveToHeadCellDescription
    moveHeadRightLocalDescription

theorem cursorEnterMoveHeadRightLocalDescription_contract_guarded
    (tapeIndex : Nat) :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator (guardLogicalTapes logical)
          tapeIndex physical)
      (fun logical physical =>
        AtTapeHeadCellCode
          ((PhysicalPrimitive.moveHead tapeIndex HeadMove.right).apply
            (guardLogicalTapes logical))
          tapeIndex physical)
      cursorEnterMoveHeadRightLocalDescription := by
  have henter :
      CursorRoutineContract
        (fun logical physical =>
          AtExistingTapeSeparator (guardLogicalTapes logical)
            tapeIndex physical)
        (fun logical physical =>
          AtTapeHeadCellCode (guardLogicalTapes logical)
            tapeIndex physical)
        cursorEnterAndMoveToHeadCellDescription := by
    exact
      { subroutineReady :=
          (cursorEnterAndMoveToHeadCellDescription_contract
            tapeIndex).subroutineReady
        realizes := by
          intro logical Tin hsource
          exact
            (cursorEnterAndMoveToHeadCellDescription_contract
              tapeIndex).realizes
              (guardLogicalTapes logical) Tin hsource }
  have hmove :
      CursorRoutineContract
        (fun logical physical =>
          AtTapeHeadCellCodeWithRightNeighbor
            (guardLogicalTapes logical) tapeIndex physical)
        (fun logical physical =>
          AtTapeHeadCellCode
            ((PhysicalPrimitive.moveHead tapeIndex HeadMove.right).apply
              (guardLogicalTapes logical))
            tapeIndex physical)
        moveHeadRightLocalDescription := by
    exact
      { subroutineReady :=
          (moveHeadRightLocalDescription_contract
            tapeIndex).subroutineReady
        realizes := by
          intro logical Tin hsource
          exact
            (moveHeadRightLocalDescription_contract
              tapeIndex).realizes
              (guardLogicalTapes logical) Tin hsource }
  exact
    cursorRoutineContract_canonicalSeq henter hmove
      (by
        intro logical physical hcell
        rw [atTapeHeadCellCode_moveLeft_moveRight hcell]
        exact guardedAtTapeHeadCellCode_to_rightNeighbor hcell)

theorem cursorEnterMoveHeadRightLocalDescription_contract_withGuardCells
    (tapeIndex : Nat) :
    CursorRoutineContract
      (fun logical physical =>
        LogicalTapeAtHasGuardCells logical tapeIndex ∧
          AtExistingTapeSeparator logical tapeIndex physical)
      (fun logical physical =>
        AtTapeHeadCellCode
          ((PhysicalPrimitive.moveHead tapeIndex HeadMove.right).apply
            logical)
          tapeIndex physical)
      cursorEnterMoveHeadRightLocalDescription := by
  have henter :
      CursorRoutineContract
        (fun logical physical =>
          LogicalTapeAtHasGuardCells logical tapeIndex ∧
            AtExistingTapeSeparator logical tapeIndex physical)
        (fun logical physical =>
          LogicalTapeAtHasGuardCells logical tapeIndex ∧
            AtTapeHeadCellCode logical tapeIndex physical)
        cursorEnterAndMoveToHeadCellDescription := by
    exact
      { subroutineReady :=
          (cursorEnterAndMoveToHeadCellDescription_contract
            tapeIndex).subroutineReady
        realizes := by
          intro logical Tin hsource
          rcases hsource with ⟨hguards, hseparator⟩
          rcases
              (cursorEnterAndMoveToHeadCellDescription_contract
                tapeIndex).realizes logical Tin hseparator with
            ⟨Tout, hhalts, hcell⟩
          exact ⟨Tout, hhalts, hguards, hcell⟩ }
  have hmove :
      CursorRoutineContract
        (fun logical physical =>
          AtTapeHeadCellCodeWithRightNeighbor logical tapeIndex physical)
        (fun logical physical =>
          AtTapeHeadCellCode
            ((PhysicalPrimitive.moveHead tapeIndex HeadMove.right).apply
              logical)
            tapeIndex physical)
        moveHeadRightLocalDescription :=
    moveHeadRightLocalDescription_contract tapeIndex
  exact
    cursorRoutineContract_canonicalSeq henter hmove
      (by
        intro logical physical hcell
        rw [atTapeHeadCellCode_moveLeft_moveRight hcell.right]
        exact
          atTapeHeadCellCode_to_rightNeighbor_of_guardCells
            hcell.left hcell.right)

/--
Guarded local left move followed by a return to the selected tape separator.

This gives the primitive layer a reusable executable cursor fragment for the
non-refresh part of a left-moving structured action.
-/
def cursorMoveHeadLeftLocalAndReturnToSeparatorDescription :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    cursorEnterMoveHeadLeftLocalDescription
    returnToOpeningSeparatorDescription

theorem cursorMoveHeadLeftLocalAndReturnToSeparatorDescription_contract_guarded
    (tapeIndex : Nat) :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator (guardLogicalTapes logical)
          tapeIndex physical)
      (fun logical physical =>
        AtTapeSeparator
          ((PhysicalPrimitive.moveHead tapeIndex HeadMove.left).apply
            (guardLogicalTapes logical))
          tapeIndex physical)
      cursorMoveHeadLeftLocalAndReturnToSeparatorDescription := by
  have hreturn :
      CursorRoutineContract
        (fun logical physical =>
          AtTapeHeadCellCode
            ((PhysicalPrimitive.moveHead tapeIndex HeadMove.left).apply
              (guardLogicalTapes logical))
            tapeIndex physical)
        (fun logical physical =>
          AtTapeSeparator
            ((PhysicalPrimitive.moveHead tapeIndex HeadMove.left).apply
              (guardLogicalTapes logical))
            tapeIndex physical)
        returnToOpeningSeparatorDescription := by
    exact
      { subroutineReady :=
          (returnToOpeningSeparatorDescription_contract_headCell
            tapeIndex).subroutineReady
        realizes := by
          intro logical Tin hsource
          exact
            (returnToOpeningSeparatorDescription_contract_headCell
              tapeIndex).realizes
              ((PhysicalPrimitive.moveHead tapeIndex HeadMove.left).apply
                (guardLogicalTapes logical))
              Tin hsource }
  exact
    cursorRoutineContract_canonicalSeq_self
      (cursorEnterMoveHeadLeftLocalDescription_contract_guarded
        tapeIndex)
      hreturn
      (by
        intro logical physical hcell
        exact atTapeHeadCellCode_moveLeft_moveRight hcell)

theorem cursorMoveHeadLeftLocalAndReturnToSeparatorDescription_contract_withGuardCells
    (tapeIndex : Nat) :
    CursorRoutineContract
      (fun logical physical =>
        LogicalTapeAtHasGuardCells logical tapeIndex ∧
          AtExistingTapeSeparator logical tapeIndex physical)
      (fun logical physical =>
        AtTapeSeparator
          ((PhysicalPrimitive.moveHead tapeIndex HeadMove.left).apply
            logical)
          tapeIndex physical)
      cursorMoveHeadLeftLocalAndReturnToSeparatorDescription := by
  have hreturn :
      CursorRoutineContract
        (fun logical physical =>
          AtTapeHeadCellCode
            ((PhysicalPrimitive.moveHead tapeIndex HeadMove.left).apply
              logical)
            tapeIndex physical)
        (fun logical physical =>
          AtTapeSeparator
            ((PhysicalPrimitive.moveHead tapeIndex HeadMove.left).apply
              logical)
            tapeIndex physical)
        returnToOpeningSeparatorDescription := by
    exact
      { subroutineReady :=
          (returnToOpeningSeparatorDescription_contract_headCell
            tapeIndex).subroutineReady
        realizes := by
          intro logical Tin hsource
          exact
            (returnToOpeningSeparatorDescription_contract_headCell
              tapeIndex).realizes
              ((PhysicalPrimitive.moveHead tapeIndex HeadMove.left).apply
                logical)
              Tin hsource }
  exact
    cursorRoutineContract_canonicalSeq_self
      (cursorEnterMoveHeadLeftLocalDescription_contract_withGuardCells
        tapeIndex)
      hreturn
      (by
        intro logical physical hcell
        exact atTapeHeadCellCode_moveLeft_moveRight hcell)

/--
Guarded local right move followed by a return to the selected tape separator.

This mirrors {name}`cursorMoveHeadLeftLocalAndReturnToSeparatorDescription` for
right-moving structured actions.
-/
def cursorMoveHeadRightLocalAndReturnToSeparatorDescription :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    cursorEnterMoveHeadRightLocalDescription
    returnToOpeningSeparatorDescription

theorem cursorMoveHeadRightLocalAndReturnToSeparatorDescription_contract_guarded
    (tapeIndex : Nat) :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator (guardLogicalTapes logical)
          tapeIndex physical)
      (fun logical physical =>
        AtTapeSeparator
          ((PhysicalPrimitive.moveHead tapeIndex HeadMove.right).apply
            (guardLogicalTapes logical))
          tapeIndex physical)
      cursorMoveHeadRightLocalAndReturnToSeparatorDescription := by
  have hreturn :
      CursorRoutineContract
        (fun logical physical =>
          AtTapeHeadCellCode
            ((PhysicalPrimitive.moveHead tapeIndex HeadMove.right).apply
              (guardLogicalTapes logical))
            tapeIndex physical)
        (fun logical physical =>
          AtTapeSeparator
            ((PhysicalPrimitive.moveHead tapeIndex HeadMove.right).apply
              (guardLogicalTapes logical))
            tapeIndex physical)
        returnToOpeningSeparatorDescription := by
    exact
      { subroutineReady :=
          (returnToOpeningSeparatorDescription_contract_headCell
            tapeIndex).subroutineReady
        realizes := by
          intro logical Tin hsource
          exact
            (returnToOpeningSeparatorDescription_contract_headCell
              tapeIndex).realizes
              ((PhysicalPrimitive.moveHead tapeIndex HeadMove.right).apply
                (guardLogicalTapes logical))
              Tin hsource }
  exact
    cursorRoutineContract_canonicalSeq_self
      (cursorEnterMoveHeadRightLocalDescription_contract_guarded
        tapeIndex)
      hreturn
      (by
        intro logical physical hcell
        exact atTapeHeadCellCode_moveLeft_moveRight hcell)

theorem cursorMoveHeadRightLocalAndReturnToSeparatorDescription_contract_withGuardCells
    (tapeIndex : Nat) :
    CursorRoutineContract
      (fun logical physical =>
        LogicalTapeAtHasGuardCells logical tapeIndex ∧
          AtExistingTapeSeparator logical tapeIndex physical)
      (fun logical physical =>
        AtTapeSeparator
          ((PhysicalPrimitive.moveHead tapeIndex HeadMove.right).apply
            logical)
          tapeIndex physical)
      cursorMoveHeadRightLocalAndReturnToSeparatorDescription := by
  have hreturn :
      CursorRoutineContract
        (fun logical physical =>
          AtTapeHeadCellCode
            ((PhysicalPrimitive.moveHead tapeIndex HeadMove.right).apply
              logical)
            tapeIndex physical)
        (fun logical physical =>
          AtTapeSeparator
            ((PhysicalPrimitive.moveHead tapeIndex HeadMove.right).apply
              logical)
            tapeIndex physical)
        returnToOpeningSeparatorDescription := by
    exact
      { subroutineReady :=
          (returnToOpeningSeparatorDescription_contract_headCell
            tapeIndex).subroutineReady
        realizes := by
          intro logical Tin hsource
          exact
            (returnToOpeningSeparatorDescription_contract_headCell
              tapeIndex).realizes
              ((PhysicalPrimitive.moveHead tapeIndex HeadMove.right).apply
                logical)
              Tin hsource }
  exact
    cursorRoutineContract_canonicalSeq_self
      (cursorEnterMoveHeadRightLocalDescription_contract_withGuardCells
        tapeIndex)
      hreturn
      (by
        intro logical physical hcell
        exact atTapeHeadCellCode_moveLeft_moveRight hcell)

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
