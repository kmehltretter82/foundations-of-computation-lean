import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.CursorComposition
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.CursorHead

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

/--
Return from the separator before tape 1 to the canonical block-start
separator.

The routine first moves left onto the last encoded bit of tape 0, then uses the
opening-separator scanner to return to the beginning of that segment.
-/
def returnFromTape1SeparatorToBlockStartDescription :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    (cursorMoveOnceDescription Direction.left)
    returnToOpeningSeparatorDescription

private theorem list_cons_exists_append_singleton
    {α : Type u} (head : α) (tail : List α) :
    exists init : List α, exists last : α,
      head :: tail = List.append init [last] := by
  induction tail generalizing head with
  | nil =>
      exact ⟨[], head, rfl⟩
  | cons next rest ih =>
      rcases ih next with ⟨init, last, hinit⟩
      exact ⟨head :: init, last, by simp [hinit]⟩

private theorem logicalTapeBits_exists_append_singleton
    (T : Tape Bool) :
    exists init : Word Bool, exists last : Bool,
      logicalTapeBits T = List.append init [last] := by
  rcases logicalTapeBits_exists_cons T with
    ⟨head, tail, hbits⟩
  rcases list_cons_exists_append_singleton head tail with
    ⟨init, last, hinit⟩
  exact ⟨init, last, by rw [hbits, hinit]⟩

private theorem atTapeSeparator_one_eq
    (T : Tape Bool) (rest : List (Tape Bool)) :
    tapeAtEncodedSplit
        (encodedPrefixBeforeTape (T :: rest) 1)
        (encodedSuffixFromTape (T :: rest) 1) =
      tapeAtEncodedSplit
        (tapeSeparatorCells ++ logicalTapeCode T)
        (encodedStructuredTapeCells rest) := by
  simp [tapeAtEncodedSplit, encodedPrefixBeforeTape,
    encodedSuffixFromTape, encodedStructuredTapeCellsPrefix]

private theorem take_succ_eq_take_append_of_drop_eq_cons_local
    {α : Type u} {xs : List α} {index : Nat}
    {head : α} {tail : List α}
    (hdrop : xs.drop index = head :: tail) :
    xs.take (index + 1) = xs.take index ++ [head] := by
  induction index generalizing xs with
  | zero =>
      cases xs with
      | nil =>
          simp at hdrop
      | cons x rest =>
          simp at hdrop
          rcases hdrop with ⟨rfl, rfl⟩
          rfl
  | succ index ih =>
      cases xs with
      | nil =>
          simp at hdrop
      | cons x rest =>
          simp at hdrop
          have htail :
              rest.take (index + 1) =
                rest.take index ++ [head] :=
            ih hdrop
          simpa [List.take_succ_cons, List.append_assoc] using
            congrArg (fun cells => x :: cells) htail

private theorem drop_succ_eq_tail_of_drop_eq_cons_local
    {α : Type u} {xs : List α} {index : Nat}
    {head : α} {tail : List α}
    (hdrop : xs.drop index = head :: tail) :
    xs.drop (index + 1) = tail := by
  induction index generalizing xs with
  | zero =>
      cases xs with
      | nil =>
          simp at hdrop
      | cons x rest =>
          simp at hdrop
          rcases hdrop with ⟨rfl, rfl⟩
          rfl
  | succ index ih =>
      cases xs with
      | nil =>
          simp at hdrop
      | cons x rest =>
          simp at hdrop
          exact ih hdrop

theorem returnFromTape1SeparatorToBlockStartDescription_contract :
    CursorRoutineContract
      (fun logical physical =>
        AtTapeSeparator logical 1 physical)
      (fun logical physical =>
        AtTapeSeparator logical 0 physical)
      returnFromTape1SeparatorToBlockStartDescription where
  subroutineReady :=
    canonicalPrimitiveSeqDescription_subroutineReady
      (cursorMoveOnceDescription_subroutineReady Direction.left)
      returnToOpeningSeparatorDescription_subroutineReady
  realizes := by
    intro logical Tin hseparator
    rcases hseparator with ⟨hle, hTin⟩
    cases logical with
    | nil =>
        simp at hle
    | cons T rest =>
        rcases logicalTapeBits_exists_append_singleton T with
          ⟨init, last, hbits⟩
        rcases encodedStructuredTapeCells_startsWith_separator rest with
          ⟨suffix, hsuffix⟩
        let Tmid :=
          tapeAtCells ((init.map some).reverse ++ tapeSeparatorCells)
            (some last :: encodedStructuredTapeCells rest)
        exists encodedStructuredTapes (T :: rest)
        constructor
        · have hmove :
              (cursorMoveOnceDescription Direction.left).HaltsFromTape
                Tin Tmid := by
            rw [hTin]
            have htarget :
                Tape.move Direction.left
                    (tapeAtEncodedSplit
                      (encodedPrefixBeforeTape (T :: rest) 1)
                      (encodedSuffixFromTape (T :: rest) 1)) =
                  Tmid := by
              rw [atTapeSeparator_one_eq T rest]
              simp [Tmid, tapeAtEncodedSplit, tapeAtCells,
                Tape.move, Tape.moveLeft,
                logicalTapeCode_eq_map_some T, hbits, hsuffix,
                tapeSeparatorCells,
                List.map_append, List.reverse_append]
            simpa [htarget] using
              cursorMoveOnceDescription_haltsFromTape
                Direction.left
                (tapeAtEncodedSplit
                  (encodedPrefixBeforeTape (T :: rest) 1)
                  (encodedSuffixFromTape (T :: rest) 1))
          have hbounce :
              Tape.move Direction.left (Tape.move Direction.right Tmid) =
                Tmid := by
            simpa [Tmid, hsuffix] using
              tapeAtCells_move_left_move_right_cons_cons
                ((init.map some).reverse ++ tapeSeparatorCells)
                (some last) none suffix
          have hreturn :
              returnToOpeningSeparatorDescription.HaltsFromTape
                (Tape.move Direction.left
                  (Tape.move Direction.right Tmid))
                (encodedStructuredTapes (T :: rest)) := by
            rw [hbounce]
            have hscan :=
              returnToOpeningSeparatorDescription_haltsFromTape
                init.reverse last [] (encodedStructuredTapeCells rest)
            simpa [Tmid, encodedStructuredTapes,
              logicalTapeCode_eq_map_some T, hbits, tapeSeparatorCells,
              List.map_append, List.map_reverse, List.reverse_reverse,
              List.append_assoc] using hscan
          exact
            canonicalPrimitiveSeqDescription_haltsFromTape_of_haltsFromTape
              (cursorMoveOnceDescription_subroutineReady Direction.left)
              returnToOpeningSeparatorDescription_subroutineReady
              hmove hreturn
        · exact atTapeSeparator_zero_self (T :: rest)

private theorem returnFromTape1SeparatorToBlockStartDescription_contract_existing_map
    (f : List (Tape Bool) -> List (Tape Bool)) :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator (f logical) 1 physical)
      (fun logical physical =>
        AtTapeSeparator (f logical) 0 physical)
      returnFromTape1SeparatorToBlockStartDescription := by
  exact
    { subroutineReady :=
        returnFromTape1SeparatorToBlockStartDescription_contract
          |>.subroutineReady
      realizes := by
        intro logical Tin hexisting
        exact
          returnFromTape1SeparatorToBlockStartDescription_contract
            |>.realizes (f logical) Tin hexisting.left }

/--
Same physical routine as
{name}`returnFromTape1SeparatorToBlockStartDescription`, stated at an arbitrary
segment boundary.  Starting at the separator after tape {lit}`tapeIndex`, it moves
left over that encoded segment and halts on the segment's opening separator.
-/
def returnFromNextSeparatorToCurrentSeparatorDescription :
    MachineDescription :=
  returnFromTape1SeparatorToBlockStartDescription

theorem returnFromNextSeparatorToCurrentSeparatorDescription_contract
    (tapeIndex : Nat) :
    CursorRoutineContract
      (fun logical physical =>
        AtTapeSeparator logical (tapeIndex + 1) physical ∧
          exists T : Tape Bool, exists rest : List (Tape Bool),
            logical.drop tapeIndex = T :: rest)
      (fun logical physical =>
        AtTapeSeparator logical tapeIndex physical)
      returnFromNextSeparatorToCurrentSeparatorDescription where
  subroutineReady := by
    simpa [returnFromNextSeparatorToCurrentSeparatorDescription] using
      (returnFromTape1SeparatorToBlockStartDescription_contract
        |>.subroutineReady)
  realizes := by
    intro logical Tin hsource
    rcases hsource with ⟨hseparator, T, rest, hdrop⟩
    rcases hseparator with ⟨hle, hTin⟩
    rcases logicalTapeBits_exists_append_singleton T with
      ⟨init, last, hbits⟩
    rcases encodedStructuredTapeCells_startsWith_separator rest with
      ⟨suffix, hsuffix⟩
    let pfx := encodedPrefixBeforeTape logical tapeIndex
    let Tmid :=
      tapeAtCells
        ((init.map some).reverse ++ tapeSeparatorCells ++ pfx.reverse)
        (some last :: encodedStructuredTapeCells rest)
    let Tout :=
      tapeAtEncodedSplit
        (encodedPrefixBeforeTape logical tapeIndex)
        (encodedSuffixFromTape logical tapeIndex)
    exists Tout
    constructor
    · have htake :
          logical.take (tapeIndex + 1) =
            logical.take tapeIndex ++ [T] :=
        take_succ_eq_take_append_of_drop_eq_cons_local hdrop
      have hdropSucc :
          logical.drop (tapeIndex + 1) = rest :=
        drop_succ_eq_tail_of_drop_eq_cons_local hdrop
      have hmove :
          (cursorMoveOnceDescription Direction.left).HaltsFromTape
            Tin Tmid := by
        rw [hTin]
        have htarget :
            Tape.move Direction.left
                (tapeAtEncodedSplit
                  (encodedPrefixBeforeTape logical (tapeIndex + 1))
                  (encodedSuffixFromTape logical (tapeIndex + 1))) =
              Tmid := by
          simp [Tmid, pfx, tapeAtEncodedSplit, tapeAtCells,
            encodedPrefixBeforeTape, encodedSuffixFromTape, htake,
            hdropSucc, Tape.move, Tape.moveLeft,
            logicalTapeCode_eq_map_some T, hbits, hsuffix,
            tapeSeparatorCells, List.map_append, List.reverse_append,
            List.append_assoc]
        simpa [htarget] using
          cursorMoveOnceDescription_haltsFromTape
            Direction.left
            (tapeAtEncodedSplit
              (encodedPrefixBeforeTape logical (tapeIndex + 1))
              (encodedSuffixFromTape logical (tapeIndex + 1)))
      have hbounce :
          Tape.move Direction.left (Tape.move Direction.right Tmid) =
            Tmid := by
        simpa [Tmid, hsuffix, List.append_assoc] using
          tapeAtCells_move_left_move_right_cons_cons
            ((init.map some).reverse ++
              tapeSeparatorCells ++ pfx.reverse)
            (some last) none suffix
      have hreturn :
          returnToOpeningSeparatorDescription.HaltsFromTape
            (Tape.move Direction.left
              (Tape.move Direction.right Tmid))
            Tout := by
        rw [hbounce]
        have hscan :=
          returnToOpeningSeparatorDescription_haltsFromTape
            init.reverse last pfx.reverse
            (encodedStructuredTapeCells rest)
        simpa [Tout, Tmid, pfx, tapeAtEncodedSplit,
          encodedSuffixFromTape, hdrop,
          logicalTapeCode_eq_map_some T, hbits, tapeSeparatorCells,
          List.map_append, List.map_reverse, List.reverse_reverse,
          List.append_assoc] using hscan
      simpa [returnFromNextSeparatorToCurrentSeparatorDescription]
        using
          canonicalPrimitiveSeqDescription_haltsFromTape_of_haltsFromTape
            (cursorMoveOnceDescription_subroutineReady Direction.left)
            returnToOpeningSeparatorDescription_subroutineReady
            hmove hreturn
    · constructor
      · exact Nat.le_trans (Nat.le_succ tapeIndex) hle
      · rfl

/--
Seek from block start to tape 1, verify the expected head cell, and return to
the tape-1 separator.
-/
def cursorTape1ReadHeadCellAndReturnToSeparatorDescription
    (expected : Option Bool) : MachineDescription :=
  canonicalPrimitiveSeqDescription
    seekTape1Description
    (cursorReadHeadCellAndReturnToSeparatorDescription expected)

theorem cursorTape1ReadHeadCellAndReturnToSeparatorDescription_contract
    (expected : Option Bool) :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator logical 0 physical ∧
          (exists T : Tape Bool, exists rest : List (Tape Bool),
            logical.drop 1 = T :: rest) ∧
          Tape.read (Description.tapeAt logical 1) = expected)
      (fun logical physical =>
        AtExistingTapeSeparator logical 1 physical)
      (cursorTape1ReadHeadCellAndReturnToSeparatorDescription
        expected) := by
  let source := fun logical physical =>
    AtExistingTapeSeparator logical 0 physical ∧
      (exists T : Tape Bool, exists rest : List (Tape Bool),
        logical.drop 1 = T :: rest) ∧
      Tape.read (Description.tapeAt logical 1) = expected
  let middle := fun logical physical =>
    AtExistingTapeSeparator logical 1 physical ∧
      Tape.read (Description.tapeAt logical 1) = expected
  have hseek :
      CursorRoutineContract source middle seekTape1Description := by
    exact
      { subroutineReady := seekTape1Description_contract.subroutineReady
        realizes := by
          intro logical Tin hsource
          rcases hsource with ⟨hstart, hexists, hread⟩
          rcases seekTape1Description_contract.realizes
              logical Tin hstart with
            ⟨Tout, hhalts, hseparator⟩
          exact ⟨Tout, hhalts, ⟨⟨hseparator, hexists⟩, hread⟩⟩ }
  have hreadContract :
      CursorRoutineContract middle
        (fun logical physical =>
          AtExistingTapeSeparator logical 1 physical)
        (cursorReadHeadCellAndReturnToSeparatorDescription
          expected) := by
    exact
      { subroutineReady :=
          (cursorReadHeadCellAndReturnToSeparatorDescription_contract
            1 expected).subroutineReady
        realizes := by
          intro logical Tin hmiddle
          rcases hmiddle with ⟨hexisting, hread⟩
          rcases
              (cursorReadHeadCellAndReturnToSeparatorDescription_contract
                1 expected).realizes logical Tin
                ⟨hexisting, hread⟩ with
            ⟨Tout, hhalts, hseparator⟩
          exact ⟨Tout, hhalts, ⟨hseparator, hexisting.right⟩⟩ }
  exact
    cursorRoutineContract_canonicalSeq_self
      hseek hreadContract
      (by
        intro logical physical hmiddle
        exact atExistingTapeSeparator_moveLeft_moveRight hmiddle.left)

/--
Seek from block start to tape 1, verify the expected head cell, and return all
the way to the canonical block-start separator.
-/
def cursorTape1ReadHeadCellAndReturnToBlockStartDescription
    (expected : Option Bool) : MachineDescription :=
  canonicalPrimitiveSeqDescription
    (cursorTape1ReadHeadCellAndReturnToSeparatorDescription expected)
    returnFromTape1SeparatorToBlockStartDescription

theorem cursorTape1ReadHeadCellAndReturnToBlockStartDescription_contract
    (expected : Option Bool) :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator logical 0 physical ∧
          (exists T : Tape Bool, exists rest : List (Tape Bool),
            logical.drop 1 = T :: rest) ∧
          Tape.read (Description.tapeAt logical 1) = expected)
      (fun logical physical =>
        AtTapeSeparator logical 0 physical)
      (cursorTape1ReadHeadCellAndReturnToBlockStartDescription
        expected) :=
  cursorRoutineContract_canonicalSeq
    (cursorTape1ReadHeadCellAndReturnToSeparatorDescription_contract
      expected)
    returnFromTape1SeparatorToBlockStartDescription_contract
    (by
      intro logical physical hexisting
      rw [atExistingTapeSeparator_moveLeft_moveRight hexisting]
      exact hexisting.left)

def HasAtLeastThreeTapes
    (logical : List (Tape Bool)) : Prop :=
  exists T : Tape Bool, exists U : Tape Bool,
  exists V : Tape Bool, exists rest : List (Tape Bool),
    logical = T :: U :: V :: rest

private theorem hasAtLeastThreeTapes_drop_one
    {logical : List (Tape Bool)}
    (hshape : HasAtLeastThreeTapes logical) :
    exists T : Tape Bool, exists rest : List (Tape Bool),
      logical.drop 1 = T :: rest := by
  rcases hshape with ⟨T, U, V, rest, hlogical⟩
  subst hlogical
  exact ⟨U, V :: rest, rfl⟩

private theorem hasAtLeastThreeTapes_drop_two
    {logical : List (Tape Bool)}
    (hshape : HasAtLeastThreeTapes logical) :
    exists T : Tape Bool, exists rest : List (Tape Bool),
      logical.drop 2 = T :: rest := by
  rcases hshape with ⟨T, U, V, rest, hlogical⟩
  subst hlogical
  exact ⟨V, rest, rfl⟩

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

private theorem seekTape2Description_contract_existing :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator logical 0 physical ∧
          HasAtLeastThreeTapes logical)
      (fun logical physical =>
        AtExistingTapeSeparator logical 2 physical ∧
          HasAtLeastThreeTapes logical)
      seekTape2Description := by
  exact
    { subroutineReady := seekTape2Description_contract.subroutineReady
      realizes := by
        intro logical Tin hsource
        rcases hsource with ⟨hstart, hshape⟩
        rcases hshape with ⟨T, U, V, rest, hlogical⟩
        rcases seekTape2Description_contract.realizes
            logical Tin
            ⟨T, U, V :: rest, hlogical, hstart.left⟩ with
          ⟨Tout, hhalts, hseparator⟩
        have hshape' : HasAtLeastThreeTapes logical :=
          ⟨T, U, V, rest, hlogical⟩
        exact
          ⟨Tout, hhalts,
            ⟨⟨hseparator,
                hasAtLeastThreeTapes_drop_two hshape'⟩,
              hshape'⟩⟩ }

private theorem returnFromTape2SeparatorToTape1Description_contract_existing_map
    (f : List (Tape Bool) -> List (Tape Bool)) :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator (f logical) 2 physical ∧
          HasAtLeastThreeTapes (f logical))
      (fun logical physical =>
        AtExistingTapeSeparator (f logical) 1 physical)
      returnFromNextSeparatorToCurrentSeparatorDescription := by
  exact
    { subroutineReady :=
        (returnFromNextSeparatorToCurrentSeparatorDescription_contract
          1).subroutineReady
      realizes := by
        intro logical Tin hsource
        rcases hsource with ⟨hexisting, hshape⟩
        rcases
            (returnFromNextSeparatorToCurrentSeparatorDescription_contract
              1).realizes (f logical) Tin
              ⟨hexisting.left,
                hasAtLeastThreeTapes_drop_one hshape⟩ with
          ⟨Tout, hhalts, hseparator⟩
        exact
          ⟨Tout, hhalts,
            ⟨hseparator, hasAtLeastThreeTapes_drop_one hshape⟩⟩ }

private theorem seekTape2Description_contract_existing_map
    (f : List (Tape Bool) -> List (Tape Bool)) :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator (f logical) 0 physical ∧
          HasAtLeastThreeTapes (f logical))
      (fun logical physical =>
        AtExistingTapeSeparator (f logical) 2 physical ∧
          HasAtLeastThreeTapes (f logical))
      seekTape2Description := by
  exact
    { subroutineReady := seekTape2Description_contract.subroutineReady
      realizes := by
        intro logical Tin hsource
        rcases hsource with ⟨hstart, hshape⟩
        rcases hshape with ⟨T, U, V, rest, hlogical⟩
        rcases seekTape2Description_contract.realizes
            (f logical) Tin
            ⟨T, U, V :: rest, hlogical, hstart.left⟩ with
          ⟨Tout, hhalts, hseparator⟩
        have hshape' : HasAtLeastThreeTapes (f logical) :=
          ⟨T, U, V, rest, hlogical⟩
        exact
          ⟨Tout, hhalts,
            ⟨⟨hseparator,
                hasAtLeastThreeTapes_drop_two hshape'⟩,
              hshape'⟩⟩ }

private theorem seekTape2Description_contract_guardCells :
    CursorRoutineContract
      (fun logical physical =>
        LogicalTapeAtHasGuardCells logical 2 ∧
          AtExistingTapeSeparator logical 0 physical)
      (fun logical physical =>
        LogicalTapeAtHasGuardCells logical 2 ∧
          AtExistingTapeSeparator logical 2 physical ∧
          HasAtLeastThreeTapes logical)
      seekTape2Description := by
  exact
    { subroutineReady := seekTape2Description_contract.subroutineReady
      realizes := by
        intro logical Tin hsource
        rcases hsource with ⟨hguards, hstart⟩
        have hshape : HasAtLeastThreeTapes logical :=
          hasAtLeastThreeTapes_of_atHasGuardCells_two hguards
        rcases hshape with ⟨T, U, V, rest, hlogical⟩
        rcases seekTape2Description_contract.realizes
            logical Tin
            ⟨T, U, V :: rest, hlogical, hstart.left⟩ with
          ⟨Tout, hhalts, hseparator⟩
        have hshape' : HasAtLeastThreeTapes logical :=
          ⟨T, U, V, rest, hlogical⟩
        exact
          ⟨Tout, hhalts,
            ⟨hguards,
              ⟨⟨hseparator,
                  hasAtLeastThreeTapes_drop_two hshape'⟩,
                hshape'⟩⟩⟩ }

/--
Seek from block start to tape 2, verify the expected head cell, and return to
the tape-2 separator.
-/
def cursorTape2ReadHeadCellAndReturnToSeparatorDescription
    (expected : Option Bool) : MachineDescription :=
  canonicalPrimitiveSeqDescription
    seekTape2Description
    (cursorReadHeadCellAndReturnToSeparatorDescription expected)

theorem cursorTape2ReadHeadCellAndReturnToSeparatorDescription_contract
    (expected : Option Bool) :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator logical 0 physical ∧
          HasAtLeastThreeTapes logical ∧
          Tape.read (Description.tapeAt logical 2) = expected)
      (fun logical physical =>
        AtExistingTapeSeparator logical 2 physical ∧
          HasAtLeastThreeTapes logical)
      (cursorTape2ReadHeadCellAndReturnToSeparatorDescription
        expected) := by
  let source := fun logical physical =>
    AtExistingTapeSeparator logical 0 physical ∧
      HasAtLeastThreeTapes logical ∧
      Tape.read (Description.tapeAt logical 2) = expected
  let middle := fun logical physical =>
    AtExistingTapeSeparator logical 2 physical ∧
      HasAtLeastThreeTapes logical ∧
      Tape.read (Description.tapeAt logical 2) = expected
  have hseek :
      CursorRoutineContract source middle seekTape2Description := by
    exact
      { subroutineReady :=
          seekTape2Description_contract_existing.subroutineReady
        realizes := by
          intro logical Tin hsource
          rcases hsource with ⟨hstart, hshape, hread⟩
          rcases
              seekTape2Description_contract_existing.realizes
                logical Tin ⟨hstart, hshape⟩ with
            ⟨Tout, hhalts, hseparator⟩
          exact ⟨Tout, hhalts, ⟨hseparator.1, hseparator.2, hread⟩⟩ }
  have hreadContract :
      CursorRoutineContract middle
        (fun logical physical =>
          AtExistingTapeSeparator logical 2 physical ∧
            HasAtLeastThreeTapes logical)
        (cursorReadHeadCellAndReturnToSeparatorDescription
          expected) := by
    exact
      { subroutineReady :=
          (cursorReadHeadCellAndReturnToSeparatorDescription_contract
            2 expected).subroutineReady
        realizes := by
          intro logical Tin hmiddle
          rcases hmiddle with ⟨hexisting, hshape, hread⟩
          rcases
              (cursorReadHeadCellAndReturnToSeparatorDescription_contract
                2 expected).realizes logical Tin
                ⟨hexisting, hread⟩ with
            ⟨Tout, hhalts, hseparator⟩
          exact
            ⟨Tout, hhalts,
              ⟨⟨hseparator, hexisting.right⟩, hshape⟩⟩ }
  exact
    cursorRoutineContract_canonicalSeq_self
      hseek hreadContract
      (by
        intro logical physical hmiddle
        exact atExistingTapeSeparator_moveLeft_moveRight hmiddle.left)

/--
Seek from block start to tape 2, verify the expected head cell, and return to
the tape-1 separator.
-/
def cursorTape2ReadHeadCellAndReturnToTape1SeparatorDescription
    (expected : Option Bool) : MachineDescription :=
  canonicalPrimitiveSeqDescription
    (cursorTape2ReadHeadCellAndReturnToSeparatorDescription expected)
    returnFromNextSeparatorToCurrentSeparatorDescription

theorem cursorTape2ReadHeadCellAndReturnToTape1SeparatorDescription_contract
    (expected : Option Bool) :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator logical 0 physical ∧
          HasAtLeastThreeTapes logical ∧
          Tape.read (Description.tapeAt logical 2) = expected)
      (fun logical physical =>
        AtExistingTapeSeparator logical 1 physical)
      (cursorTape2ReadHeadCellAndReturnToTape1SeparatorDescription
        expected) := by
  let hreturn :=
    returnFromTape2SeparatorToTape1Description_contract_existing_map id
  exact
    cursorRoutineContract_canonicalSeq_self
      (cursorTape2ReadHeadCellAndReturnToSeparatorDescription_contract
        expected)
      hreturn
      (by
        intro logical physical hmiddle
        exact atExistingTapeSeparator_moveLeft_moveRight hmiddle.left)

/--
Seek from block start to tape 2, verify the expected head cell, and return all
the way to the canonical block-start separator.
-/
def cursorTape2ReadHeadCellAndReturnToBlockStartDescription
    (expected : Option Bool) : MachineDescription :=
  canonicalPrimitiveSeqDescription
    (cursorTape2ReadHeadCellAndReturnToTape1SeparatorDescription
      expected)
    returnFromTape1SeparatorToBlockStartDescription

theorem cursorTape2ReadHeadCellAndReturnToBlockStartDescription_contract
    (expected : Option Bool) :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator logical 0 physical ∧
          HasAtLeastThreeTapes logical ∧
          Tape.read (Description.tapeAt logical 2) = expected)
      (fun logical physical =>
        AtTapeSeparator logical 0 physical)
      (cursorTape2ReadHeadCellAndReturnToBlockStartDescription
        expected) :=
  cursorRoutineContract_canonicalSeq
    (cursorTape2ReadHeadCellAndReturnToTape1SeparatorDescription_contract
      expected)
    returnFromTape1SeparatorToBlockStartDescription_contract
    (by
      intro logical physical hexisting
      rw [atExistingTapeSeparator_moveLeft_moveRight hexisting]
      exact hexisting.left)

/--
Seek from block start to tape 2 and return to block start without inspecting or
mutating the selected tape.
-/
def cursorTape2NoopAndReturnToBlockStartDescription :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    (canonicalPrimitiveSeqDescription
      seekTape2Description
      returnFromNextSeparatorToCurrentSeparatorDescription)
    returnFromTape1SeparatorToBlockStartDescription

theorem cursorTape2NoopAndReturnToBlockStartDescription_contract :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator logical 0 physical ∧
          HasAtLeastThreeTapes logical)
      (fun logical physical =>
        AtTapeSeparator logical 0 physical)
      cursorTape2NoopAndReturnToBlockStartDescription := by
  have hseek :
      CursorRoutineContract
        (fun logical physical =>
          AtExistingTapeSeparator logical 0 physical ∧
            HasAtLeastThreeTapes logical)
        (fun logical physical =>
          AtExistingTapeSeparator logical 2 physical ∧
            HasAtLeastThreeTapes logical)
        seekTape2Description :=
    seekTape2Description_contract_existing
  have hreturnOne :
      CursorRoutineContract
        (fun logical physical =>
          AtExistingTapeSeparator logical 2 physical ∧
            HasAtLeastThreeTapes logical)
      (fun logical physical =>
        AtExistingTapeSeparator logical 1 physical)
        returnFromNextSeparatorToCurrentSeparatorDescription := by
    exact
      returnFromTape2SeparatorToTape1Description_contract_existing_map id
  have hfirst :
      CursorRoutineContract
        (fun logical physical =>
          AtExistingTapeSeparator logical 0 physical ∧
            HasAtLeastThreeTapes logical)
        (fun logical physical =>
          AtExistingTapeSeparator logical 1 physical)
        (canonicalPrimitiveSeqDescription
          seekTape2Description
          returnFromNextSeparatorToCurrentSeparatorDescription) :=
    cursorRoutineContract_canonicalSeq_self
      hseek hreturnOne
      (by
        intro logical physical hmiddle
        exact atExistingTapeSeparator_moveLeft_moveRight hmiddle.left)
  exact
    cursorRoutineContract_canonicalSeq
      hfirst
      returnFromTape1SeparatorToBlockStartDescription_contract
      (by
        intro logical physical hexisting
        rw [atExistingTapeSeparator_moveLeft_moveRight hexisting]
        exact hexisting.left)

private theorem writeHeadCell_two_apply_hasAtLeastThreeTapes
    (cell : Option Bool) {logical : List (Tape Bool)}
    (hshape : HasAtLeastThreeTapes logical) :
    HasAtLeastThreeTapes
      ((PhysicalPrimitive.writeHeadCell 2 cell).apply logical) := by
  rcases hshape with ⟨T, U, V, rest, hlogical⟩
  subst hlogical
  exact
    ⟨T, U, Tape.write cell V, rest, by
      simp [PhysicalPrimitive.apply, Description.tapeAt]⟩

private theorem moveHead_two_apply_hasAtLeastThreeTapes
    (move : HeadMove) {logical : List (Tape Bool)}
    (hshape : HasAtLeastThreeTapes logical) :
    HasAtLeastThreeTapes
      ((PhysicalPrimitive.moveHead 2 move).apply logical) := by
  rcases hshape with ⟨T, U, V, rest, hlogical⟩
  subst hlogical
  exact
    ⟨T, U, move.apply V, rest, by
      cases move <;>
        simp [PhysicalPrimitive.apply, Description.tapeAt,
          HeadMove.apply]⟩

/--
Seek from block start to tape 2, write the selected head cell, and return to
the tape-2 separator.
-/
def cursorTape2WriteHeadCellAndReturnToSeparatorDescription
    (cell : Option Bool) : MachineDescription :=
  canonicalPrimitiveSeqDescription
    seekTape2Description
    (cursorWriteHeadCellAndReturnToSeparatorDescription cell)

theorem cursorTape2WriteHeadCellAndReturnToSeparatorDescription_contract
    (cell : Option Bool) :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator logical 0 physical ∧
          HasAtLeastThreeTapes logical)
      (fun logical physical =>
        AtExistingTapeSeparator
          ((PhysicalPrimitive.writeHeadCell 2 cell).apply logical)
          2 physical ∧
          HasAtLeastThreeTapes
            ((PhysicalPrimitive.writeHeadCell 2 cell).apply logical))
      (cursorTape2WriteHeadCellAndReturnToSeparatorDescription
        cell) := by
  have hseek :
      CursorRoutineContract
        (fun logical physical =>
          AtExistingTapeSeparator logical 0 physical ∧
            HasAtLeastThreeTapes logical)
        (fun logical physical =>
          AtExistingTapeSeparator logical 2 physical ∧
            HasAtLeastThreeTapes logical)
        seekTape2Description :=
    seekTape2Description_contract_existing
  have hwrite :
      CursorRoutineContract
        (fun logical physical =>
          AtExistingTapeSeparator logical 2 physical ∧
            HasAtLeastThreeTapes logical)
        (fun logical physical =>
          AtExistingTapeSeparator
            ((PhysicalPrimitive.writeHeadCell 2 cell).apply logical)
            2 physical ∧
            HasAtLeastThreeTapes
              ((PhysicalPrimitive.writeHeadCell 2 cell).apply logical))
        (cursorWriteHeadCellAndReturnToSeparatorDescription
          cell) := by
    exact
      { subroutineReady :=
          (cursorWriteHeadCellAndReturnToSeparatorDescription_contract
            2 cell).subroutineReady
        realizes := by
          intro logical Tin hsource
          rcases hsource with ⟨hexisting, hshape⟩
          rcases
              (cursorWriteHeadCellAndReturnToSeparatorDescription_contract
                2 cell).realizes logical Tin hexisting with
            ⟨Tout, hhalts, hseparator⟩
          have hshape' :
              HasAtLeastThreeTapes
                ((PhysicalPrimitive.writeHeadCell 2 cell).apply
                  logical) :=
            writeHeadCell_two_apply_hasAtLeastThreeTapes cell hshape
          exact
            ⟨Tout, hhalts,
              ⟨⟨hseparator,
                  hasAtLeastThreeTapes_drop_two hshape'⟩,
                hshape'⟩⟩ }
  exact
    cursorRoutineContract_canonicalSeq_self
      hseek hwrite
      (by
        intro logical physical hmiddle
        exact atExistingTapeSeparator_moveLeft_moveRight hmiddle.left)

/--
Seek from block start to tape 2, write the selected head cell, and return to
the tape-1 separator.
-/
def cursorTape2WriteHeadCellAndReturnToTape1SeparatorDescription
    (cell : Option Bool) : MachineDescription :=
  canonicalPrimitiveSeqDescription
    (cursorTape2WriteHeadCellAndReturnToSeparatorDescription cell)
    returnFromNextSeparatorToCurrentSeparatorDescription

theorem cursorTape2WriteHeadCellAndReturnToTape1SeparatorDescription_contract
    (cell : Option Bool) :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator logical 0 physical ∧
          HasAtLeastThreeTapes logical)
      (fun logical physical =>
        AtExistingTapeSeparator
          ((PhysicalPrimitive.writeHeadCell 2 cell).apply logical)
          1 physical)
      (cursorTape2WriteHeadCellAndReturnToTape1SeparatorDescription
        cell) := by
  let hreturn :=
    returnFromTape2SeparatorToTape1Description_contract_existing_map
      (fun logical =>
        (PhysicalPrimitive.writeHeadCell 2 cell).apply logical)
  exact
    cursorRoutineContract_canonicalSeq_self
      (cursorTape2WriteHeadCellAndReturnToSeparatorDescription_contract
        cell)
      hreturn
      (by
        intro logical physical hmiddle
        exact atExistingTapeSeparator_moveLeft_moveRight hmiddle.left)

/--
Seek from block start to tape 2, write the selected head cell, and return all
the way to the canonical block-start separator.
-/
def cursorTape2WriteHeadCellAndReturnToBlockStartDescription
    (cell : Option Bool) : MachineDescription :=
  canonicalPrimitiveSeqDescription
    (cursorTape2WriteHeadCellAndReturnToTape1SeparatorDescription
      cell)
    returnFromTape1SeparatorToBlockStartDescription

theorem cursorTape2WriteHeadCellAndReturnToBlockStartDescription_contract
    (cell : Option Bool) :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator logical 0 physical ∧
          HasAtLeastThreeTapes logical)
      (fun logical physical =>
        AtTapeSeparator
          ((PhysicalPrimitive.writeHeadCell 2 cell).apply logical)
          0 physical)
      (cursorTape2WriteHeadCellAndReturnToBlockStartDescription
        cell) := by
  have hreturn :
      CursorRoutineContract
        (fun logical physical =>
          AtExistingTapeSeparator
            ((PhysicalPrimitive.writeHeadCell 2 cell).apply logical)
            1 physical)
        (fun logical physical =>
          AtTapeSeparator
            ((PhysicalPrimitive.writeHeadCell 2 cell).apply logical)
            0 physical)
        returnFromTape1SeparatorToBlockStartDescription :=
    returnFromTape1SeparatorToBlockStartDescription_contract_existing_map
      (fun logical =>
        (PhysicalPrimitive.writeHeadCell 2 cell).apply logical)
  exact
    cursorRoutineContract_canonicalSeq_self
      (cursorTape2WriteHeadCellAndReturnToTape1SeparatorDescription_contract
        cell)
      hreturn
      (by
        intro logical physical hexisting
        exact atExistingTapeSeparator_moveLeft_moveRight hexisting)

/--
Seek from block start to tape 2, move its head one cell left locally, and
return to the tape-2 separator.
-/
def cursorTape2MoveHeadLeftLocalAndReturnToSeparatorDescription :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    seekTape2Description
    cursorMoveHeadLeftLocalAndReturnToSeparatorDescription

theorem cursorTape2MoveHeadLeftLocalAndReturnToSeparatorDescription_contract_guarded :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator (guardLogicalTapes logical) 0 physical ∧
          HasAtLeastThreeTapes (guardLogicalTapes logical))
      (fun logical physical =>
        AtExistingTapeSeparator
          ((PhysicalPrimitive.moveHead 2 HeadMove.left).apply
            (guardLogicalTapes logical))
          2 physical ∧
          HasAtLeastThreeTapes
            ((PhysicalPrimitive.moveHead 2 HeadMove.left).apply
              (guardLogicalTapes logical)))
      cursorTape2MoveHeadLeftLocalAndReturnToSeparatorDescription := by
  have hseek :
      CursorRoutineContract
        (fun logical physical =>
          AtExistingTapeSeparator (guardLogicalTapes logical) 0 physical ∧
            HasAtLeastThreeTapes (guardLogicalTapes logical))
        (fun logical physical =>
          AtExistingTapeSeparator (guardLogicalTapes logical) 2 physical ∧
            HasAtLeastThreeTapes (guardLogicalTapes logical))
        seekTape2Description :=
    seekTape2Description_contract_existing_map guardLogicalTapes
  have hmove :
      CursorRoutineContract
        (fun logical physical =>
          AtExistingTapeSeparator (guardLogicalTapes logical) 2 physical ∧
            HasAtLeastThreeTapes (guardLogicalTapes logical))
        (fun logical physical =>
          AtExistingTapeSeparator
            ((PhysicalPrimitive.moveHead 2 HeadMove.left).apply
              (guardLogicalTapes logical))
            2 physical ∧
            HasAtLeastThreeTapes
              ((PhysicalPrimitive.moveHead 2 HeadMove.left).apply
                (guardLogicalTapes logical)))
        cursorMoveHeadLeftLocalAndReturnToSeparatorDescription := by
    exact
      { subroutineReady :=
          (cursorMoveHeadLeftLocalAndReturnToSeparatorDescription_contract_guarded
            2).subroutineReady
        realizes := by
          intro logical Tin hsource
          rcases hsource with ⟨hexisting, hshape⟩
          rcases
              (cursorMoveHeadLeftLocalAndReturnToSeparatorDescription_contract_guarded
                2).realizes logical Tin hexisting with
            ⟨Tout, hhalts, hseparator⟩
          have hshape' :
              HasAtLeastThreeTapes
                ((PhysicalPrimitive.moveHead 2 HeadMove.left).apply
                  (guardLogicalTapes logical)) :=
            moveHead_two_apply_hasAtLeastThreeTapes
              HeadMove.left hshape
          exact
            ⟨Tout, hhalts,
              ⟨⟨hseparator,
                  hasAtLeastThreeTapes_drop_two hshape'⟩,
                hshape'⟩⟩ }
  exact
    cursorRoutineContract_canonicalSeq_self
      hseek hmove
      (by
        intro logical physical hmiddle
        exact atExistingTapeSeparator_moveLeft_moveRight hmiddle.left)

theorem cursorTape2MoveHeadLeftLocalAndReturnToSeparatorDescription_contract_withGuardCells :
    CursorRoutineContract
      (fun logical physical =>
        LogicalTapeAtHasGuardCells logical 2 ∧
          AtExistingTapeSeparator logical 0 physical)
      (fun logical physical =>
        AtExistingTapeSeparator
          ((PhysicalPrimitive.moveHead 2 HeadMove.left).apply logical)
          2 physical ∧
          HasAtLeastThreeTapes
            ((PhysicalPrimitive.moveHead 2 HeadMove.left).apply logical))
      cursorTape2MoveHeadLeftLocalAndReturnToSeparatorDescription := by
  have hseek :
      CursorRoutineContract
        (fun logical physical =>
          LogicalTapeAtHasGuardCells logical 2 ∧
            AtExistingTapeSeparator logical 0 physical)
        (fun logical physical =>
          LogicalTapeAtHasGuardCells logical 2 ∧
            AtExistingTapeSeparator logical 2 physical ∧
            HasAtLeastThreeTapes logical)
        seekTape2Description :=
    seekTape2Description_contract_guardCells
  have hmove :
      CursorRoutineContract
        (fun logical physical =>
          LogicalTapeAtHasGuardCells logical 2 ∧
            AtExistingTapeSeparator logical 2 physical ∧
            HasAtLeastThreeTapes logical)
        (fun logical physical =>
          AtExistingTapeSeparator
            ((PhysicalPrimitive.moveHead 2 HeadMove.left).apply logical)
            2 physical ∧
            HasAtLeastThreeTapes
              ((PhysicalPrimitive.moveHead 2 HeadMove.left).apply logical))
        cursorMoveHeadLeftLocalAndReturnToSeparatorDescription := by
    exact
      { subroutineReady :=
          (cursorMoveHeadLeftLocalAndReturnToSeparatorDescription_contract_withGuardCells
            2).subroutineReady
        realizes := by
          intro logical Tin hsource
          rcases hsource with ⟨hguards, hexisting, hshape⟩
          rcases
              (cursorMoveHeadLeftLocalAndReturnToSeparatorDescription_contract_withGuardCells
                2).realizes logical Tin ⟨hguards, hexisting⟩ with
            ⟨Tout, hhalts, hseparator⟩
          have hshape' :
              HasAtLeastThreeTapes
                ((PhysicalPrimitive.moveHead 2 HeadMove.left).apply
                  logical) :=
            moveHead_two_apply_hasAtLeastThreeTapes
              HeadMove.left hshape
          exact
            ⟨Tout, hhalts,
              ⟨⟨hseparator,
                  hasAtLeastThreeTapes_drop_two hshape'⟩,
                hshape'⟩⟩ }
  exact
    cursorRoutineContract_canonicalSeq_self
      hseek hmove
      (by
        intro logical physical hmiddle
        exact atExistingTapeSeparator_moveLeft_moveRight hmiddle.right.left)

/--
Seek from block start to tape 2, move its head one cell left locally, and
return to the tape-1 separator.
-/
def cursorTape2MoveHeadLeftLocalAndReturnToTape1SeparatorDescription :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    cursorTape2MoveHeadLeftLocalAndReturnToSeparatorDescription
    returnFromNextSeparatorToCurrentSeparatorDescription

theorem cursorTape2MoveHeadLeftLocalAndReturnToTape1SeparatorDescription_contract_guarded :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator (guardLogicalTapes logical) 0 physical ∧
          HasAtLeastThreeTapes (guardLogicalTapes logical))
      (fun logical physical =>
        AtExistingTapeSeparator
          ((PhysicalPrimitive.moveHead 2 HeadMove.left).apply
            (guardLogicalTapes logical))
          1 physical)
      cursorTape2MoveHeadLeftLocalAndReturnToTape1SeparatorDescription := by
  let hreturn :=
    returnFromTape2SeparatorToTape1Description_contract_existing_map
      (fun logical =>
        (PhysicalPrimitive.moveHead 2 HeadMove.left).apply
          (guardLogicalTapes logical))
  exact
    cursorRoutineContract_canonicalSeq_self
      cursorTape2MoveHeadLeftLocalAndReturnToSeparatorDescription_contract_guarded
      hreturn
      (by
        intro logical physical hmiddle
        exact atExistingTapeSeparator_moveLeft_moveRight hmiddle.left)

theorem cursorTape2MoveHeadLeftLocalAndReturnToTape1SeparatorDescription_contract_withGuardCells :
    CursorRoutineContract
      (fun logical physical =>
        LogicalTapeAtHasGuardCells logical 2 ∧
          AtExistingTapeSeparator logical 0 physical)
      (fun logical physical =>
        AtExistingTapeSeparator
          ((PhysicalPrimitive.moveHead 2 HeadMove.left).apply logical)
          1 physical)
      cursorTape2MoveHeadLeftLocalAndReturnToTape1SeparatorDescription := by
  let hreturn :=
    returnFromTape2SeparatorToTape1Description_contract_existing_map
      (fun logical =>
        (PhysicalPrimitive.moveHead 2 HeadMove.left).apply logical)
  exact
    cursorRoutineContract_canonicalSeq_self
      cursorTape2MoveHeadLeftLocalAndReturnToSeparatorDescription_contract_withGuardCells
      hreturn
      (by
        intro logical physical hmiddle
        exact atExistingTapeSeparator_moveLeft_moveRight hmiddle.left)

/--
Seek from block start to tape 2, move its head one cell left locally, and
return all the way to the canonical block-start separator.
-/
def cursorTape2MoveHeadLeftLocalAndReturnToBlockStartDescription :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    cursorTape2MoveHeadLeftLocalAndReturnToTape1SeparatorDescription
    returnFromTape1SeparatorToBlockStartDescription

theorem cursorTape2MoveHeadLeftLocalAndReturnToBlockStartDescription_contract_guarded :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator (guardLogicalTapes logical) 0 physical ∧
          HasAtLeastThreeTapes (guardLogicalTapes logical))
      (fun logical physical =>
        AtTapeSeparator
          ((PhysicalPrimitive.moveHead 2 HeadMove.left).apply
            (guardLogicalTapes logical))
          0 physical)
      cursorTape2MoveHeadLeftLocalAndReturnToBlockStartDescription := by
  have hreturn :
      CursorRoutineContract
        (fun logical physical =>
          AtExistingTapeSeparator
            ((PhysicalPrimitive.moveHead 2 HeadMove.left).apply
              (guardLogicalTapes logical))
            1 physical)
        (fun logical physical =>
          AtTapeSeparator
            ((PhysicalPrimitive.moveHead 2 HeadMove.left).apply
              (guardLogicalTapes logical))
            0 physical)
        returnFromTape1SeparatorToBlockStartDescription :=
    returnFromTape1SeparatorToBlockStartDescription_contract_existing_map
      (fun logical =>
        (PhysicalPrimitive.moveHead 2 HeadMove.left).apply
          (guardLogicalTapes logical))
  exact
    cursorRoutineContract_canonicalSeq_self
      cursorTape2MoveHeadLeftLocalAndReturnToTape1SeparatorDescription_contract_guarded
      hreturn
      (by
        intro logical physical hexisting
        exact atExistingTapeSeparator_moveLeft_moveRight hexisting)

theorem cursorTape2MoveHeadLeftLocalAndReturnToBlockStartDescription_contract_withGuardCells :
    CursorRoutineContract
      (fun logical physical =>
        LogicalTapeAtHasGuardCells logical 2 ∧
          AtExistingTapeSeparator logical 0 physical)
      (fun logical physical =>
        AtTapeSeparator
          ((PhysicalPrimitive.moveHead 2 HeadMove.left).apply logical)
          0 physical)
      cursorTape2MoveHeadLeftLocalAndReturnToBlockStartDescription := by
  have hreturn :
      CursorRoutineContract
        (fun logical physical =>
          AtExistingTapeSeparator
            ((PhysicalPrimitive.moveHead 2 HeadMove.left).apply logical)
            1 physical)
        (fun logical physical =>
          AtTapeSeparator
            ((PhysicalPrimitive.moveHead 2 HeadMove.left).apply logical)
            0 physical)
        returnFromTape1SeparatorToBlockStartDescription :=
    returnFromTape1SeparatorToBlockStartDescription_contract_existing_map
      (fun logical =>
        (PhysicalPrimitive.moveHead 2 HeadMove.left).apply logical)
  exact
    cursorRoutineContract_canonicalSeq_self
      cursorTape2MoveHeadLeftLocalAndReturnToTape1SeparatorDescription_contract_withGuardCells
      hreturn
      (by
        intro logical physical hexisting
        exact atExistingTapeSeparator_moveLeft_moveRight hexisting)

/--
Seek from block start to tape 2, move its head one cell right locally, and
return to the tape-2 separator.
-/
def cursorTape2MoveHeadRightLocalAndReturnToSeparatorDescription :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    seekTape2Description
    cursorMoveHeadRightLocalAndReturnToSeparatorDescription

theorem cursorTape2MoveHeadRightLocalAndReturnToSeparatorDescription_contract_guarded :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator (guardLogicalTapes logical) 0 physical ∧
          HasAtLeastThreeTapes (guardLogicalTapes logical))
      (fun logical physical =>
        AtExistingTapeSeparator
          ((PhysicalPrimitive.moveHead 2 HeadMove.right).apply
            (guardLogicalTapes logical))
          2 physical ∧
          HasAtLeastThreeTapes
            ((PhysicalPrimitive.moveHead 2 HeadMove.right).apply
              (guardLogicalTapes logical)))
      cursorTape2MoveHeadRightLocalAndReturnToSeparatorDescription := by
  have hseek :
      CursorRoutineContract
        (fun logical physical =>
          AtExistingTapeSeparator (guardLogicalTapes logical) 0 physical ∧
            HasAtLeastThreeTapes (guardLogicalTapes logical))
        (fun logical physical =>
          AtExistingTapeSeparator (guardLogicalTapes logical) 2 physical ∧
            HasAtLeastThreeTapes (guardLogicalTapes logical))
        seekTape2Description :=
    seekTape2Description_contract_existing_map guardLogicalTapes
  have hmove :
      CursorRoutineContract
        (fun logical physical =>
          AtExistingTapeSeparator (guardLogicalTapes logical) 2 physical ∧
            HasAtLeastThreeTapes (guardLogicalTapes logical))
        (fun logical physical =>
          AtExistingTapeSeparator
            ((PhysicalPrimitive.moveHead 2 HeadMove.right).apply
              (guardLogicalTapes logical))
            2 physical ∧
            HasAtLeastThreeTapes
              ((PhysicalPrimitive.moveHead 2 HeadMove.right).apply
                (guardLogicalTapes logical)))
        cursorMoveHeadRightLocalAndReturnToSeparatorDescription := by
    exact
      { subroutineReady :=
          (cursorMoveHeadRightLocalAndReturnToSeparatorDescription_contract_guarded
            2).subroutineReady
        realizes := by
          intro logical Tin hsource
          rcases hsource with ⟨hexisting, hshape⟩
          rcases
              (cursorMoveHeadRightLocalAndReturnToSeparatorDescription_contract_guarded
                2).realizes logical Tin hexisting with
            ⟨Tout, hhalts, hseparator⟩
          have hshape' :
              HasAtLeastThreeTapes
                ((PhysicalPrimitive.moveHead 2 HeadMove.right).apply
                  (guardLogicalTapes logical)) :=
            moveHead_two_apply_hasAtLeastThreeTapes
              HeadMove.right hshape
          exact
            ⟨Tout, hhalts,
              ⟨⟨hseparator,
                  hasAtLeastThreeTapes_drop_two hshape'⟩,
                hshape'⟩⟩ }
  exact
    cursorRoutineContract_canonicalSeq_self
      hseek hmove
      (by
        intro logical physical hmiddle
        exact atExistingTapeSeparator_moveLeft_moveRight hmiddle.left)

theorem cursorTape2MoveHeadRightLocalAndReturnToSeparatorDescription_contract_withGuardCells :
    CursorRoutineContract
      (fun logical physical =>
        LogicalTapeAtHasGuardCells logical 2 ∧
          AtExistingTapeSeparator logical 0 physical)
      (fun logical physical =>
        AtExistingTapeSeparator
          ((PhysicalPrimitive.moveHead 2 HeadMove.right).apply logical)
          2 physical ∧
          HasAtLeastThreeTapes
            ((PhysicalPrimitive.moveHead 2 HeadMove.right).apply logical))
      cursorTape2MoveHeadRightLocalAndReturnToSeparatorDescription := by
  have hseek :
      CursorRoutineContract
        (fun logical physical =>
          LogicalTapeAtHasGuardCells logical 2 ∧
            AtExistingTapeSeparator logical 0 physical)
        (fun logical physical =>
          LogicalTapeAtHasGuardCells logical 2 ∧
            AtExistingTapeSeparator logical 2 physical ∧
            HasAtLeastThreeTapes logical)
        seekTape2Description :=
    seekTape2Description_contract_guardCells
  have hmove :
      CursorRoutineContract
        (fun logical physical =>
          LogicalTapeAtHasGuardCells logical 2 ∧
            AtExistingTapeSeparator logical 2 physical ∧
            HasAtLeastThreeTapes logical)
        (fun logical physical =>
          AtExistingTapeSeparator
            ((PhysicalPrimitive.moveHead 2 HeadMove.right).apply logical)
            2 physical ∧
            HasAtLeastThreeTapes
              ((PhysicalPrimitive.moveHead 2 HeadMove.right).apply logical))
        cursorMoveHeadRightLocalAndReturnToSeparatorDescription := by
    exact
      { subroutineReady :=
          (cursorMoveHeadRightLocalAndReturnToSeparatorDescription_contract_withGuardCells
            2).subroutineReady
        realizes := by
          intro logical Tin hsource
          rcases hsource with ⟨hguards, hexisting, hshape⟩
          rcases
              (cursorMoveHeadRightLocalAndReturnToSeparatorDescription_contract_withGuardCells
                2).realizes logical Tin ⟨hguards, hexisting⟩ with
            ⟨Tout, hhalts, hseparator⟩
          have hshape' :
              HasAtLeastThreeTapes
                ((PhysicalPrimitive.moveHead 2 HeadMove.right).apply
                  logical) :=
            moveHead_two_apply_hasAtLeastThreeTapes
              HeadMove.right hshape
          exact
            ⟨Tout, hhalts,
              ⟨⟨hseparator,
                  hasAtLeastThreeTapes_drop_two hshape'⟩,
                hshape'⟩⟩ }
  exact
    cursorRoutineContract_canonicalSeq_self
      hseek hmove
      (by
        intro logical physical hmiddle
        exact atExistingTapeSeparator_moveLeft_moveRight hmiddle.right.left)

/--
Seek from block start to tape 2, move its head one cell right locally, and
return to the tape-1 separator.
-/
def cursorTape2MoveHeadRightLocalAndReturnToTape1SeparatorDescription :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    cursorTape2MoveHeadRightLocalAndReturnToSeparatorDescription
    returnFromNextSeparatorToCurrentSeparatorDescription

theorem cursorTape2MoveHeadRightLocalAndReturnToTape1SeparatorDescription_contract_guarded :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator (guardLogicalTapes logical) 0 physical ∧
          HasAtLeastThreeTapes (guardLogicalTapes logical))
      (fun logical physical =>
        AtExistingTapeSeparator
          ((PhysicalPrimitive.moveHead 2 HeadMove.right).apply
            (guardLogicalTapes logical))
          1 physical)
      cursorTape2MoveHeadRightLocalAndReturnToTape1SeparatorDescription := by
  let hreturn :=
    returnFromTape2SeparatorToTape1Description_contract_existing_map
      (fun logical =>
        (PhysicalPrimitive.moveHead 2 HeadMove.right).apply
          (guardLogicalTapes logical))
  exact
    cursorRoutineContract_canonicalSeq_self
      cursorTape2MoveHeadRightLocalAndReturnToSeparatorDescription_contract_guarded
      hreturn
      (by
        intro logical physical hmiddle
        exact atExistingTapeSeparator_moveLeft_moveRight hmiddle.left)

theorem cursorTape2MoveHeadRightLocalAndReturnToTape1SeparatorDescription_contract_withGuardCells :
    CursorRoutineContract
      (fun logical physical =>
        LogicalTapeAtHasGuardCells logical 2 ∧
          AtExistingTapeSeparator logical 0 physical)
      (fun logical physical =>
        AtExistingTapeSeparator
          ((PhysicalPrimitive.moveHead 2 HeadMove.right).apply logical)
          1 physical)
      cursorTape2MoveHeadRightLocalAndReturnToTape1SeparatorDescription := by
  let hreturn :=
    returnFromTape2SeparatorToTape1Description_contract_existing_map
      (fun logical =>
        (PhysicalPrimitive.moveHead 2 HeadMove.right).apply logical)
  exact
    cursorRoutineContract_canonicalSeq_self
      cursorTape2MoveHeadRightLocalAndReturnToSeparatorDescription_contract_withGuardCells
      hreturn
      (by
        intro logical physical hmiddle
        exact atExistingTapeSeparator_moveLeft_moveRight hmiddle.left)

/--
Seek from block start to tape 2, move its head one cell right locally, and
return all the way to the canonical block-start separator.
-/
def cursorTape2MoveHeadRightLocalAndReturnToBlockStartDescription :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    cursorTape2MoveHeadRightLocalAndReturnToTape1SeparatorDescription
    returnFromTape1SeparatorToBlockStartDescription

theorem cursorTape2MoveHeadRightLocalAndReturnToBlockStartDescription_contract_guarded :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator (guardLogicalTapes logical) 0 physical ∧
          HasAtLeastThreeTapes (guardLogicalTapes logical))
      (fun logical physical =>
        AtTapeSeparator
          ((PhysicalPrimitive.moveHead 2 HeadMove.right).apply
            (guardLogicalTapes logical))
          0 physical)
      cursorTape2MoveHeadRightLocalAndReturnToBlockStartDescription := by
  have hreturn :
      CursorRoutineContract
        (fun logical physical =>
          AtExistingTapeSeparator
            ((PhysicalPrimitive.moveHead 2 HeadMove.right).apply
              (guardLogicalTapes logical))
            1 physical)
        (fun logical physical =>
          AtTapeSeparator
            ((PhysicalPrimitive.moveHead 2 HeadMove.right).apply
              (guardLogicalTapes logical))
            0 physical)
        returnFromTape1SeparatorToBlockStartDescription :=
    returnFromTape1SeparatorToBlockStartDescription_contract_existing_map
      (fun logical =>
        (PhysicalPrimitive.moveHead 2 HeadMove.right).apply
          (guardLogicalTapes logical))
  exact
    cursorRoutineContract_canonicalSeq_self
      cursorTape2MoveHeadRightLocalAndReturnToTape1SeparatorDescription_contract_guarded
      hreturn
      (by
        intro logical physical hexisting
        exact atExistingTapeSeparator_moveLeft_moveRight hexisting)

theorem cursorTape2MoveHeadRightLocalAndReturnToBlockStartDescription_contract_withGuardCells :
    CursorRoutineContract
      (fun logical physical =>
        LogicalTapeAtHasGuardCells logical 2 ∧
          AtExistingTapeSeparator logical 0 physical)
      (fun logical physical =>
        AtTapeSeparator
          ((PhysicalPrimitive.moveHead 2 HeadMove.right).apply logical)
          0 physical)
      cursorTape2MoveHeadRightLocalAndReturnToBlockStartDescription := by
  have hreturn :
      CursorRoutineContract
        (fun logical physical =>
          AtExistingTapeSeparator
            ((PhysicalPrimitive.moveHead 2 HeadMove.right).apply logical)
            1 physical)
        (fun logical physical =>
          AtTapeSeparator
            ((PhysicalPrimitive.moveHead 2 HeadMove.right).apply logical)
            0 physical)
        returnFromTape1SeparatorToBlockStartDescription :=
    returnFromTape1SeparatorToBlockStartDescription_contract_existing_map
      (fun logical =>
        (PhysicalPrimitive.moveHead 2 HeadMove.right).apply logical)
  exact
    cursorRoutineContract_canonicalSeq_self
      cursorTape2MoveHeadRightLocalAndReturnToTape1SeparatorDescription_contract_withGuardCells
      hreturn
      (by
        intro logical physical hexisting
        exact atExistingTapeSeparator_moveLeft_moveRight hexisting)

private theorem seekTape1Description_contract_existing_map
    (f : List (Tape Bool) -> List (Tape Bool)) :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator (f logical) 0 physical ∧
          (exists T : Tape Bool, exists rest : List (Tape Bool),
            (f logical).drop 1 = T :: rest))
      (fun logical physical =>
        AtExistingTapeSeparator (f logical) 1 physical)
      seekTape1Description := by
  exact
    { subroutineReady := seekTape1Description_contract.subroutineReady
      realizes := by
        intro logical Tin hsource
        rcases hsource with ⟨hstart, hexists⟩
        rcases seekTape1Description_contract.realizes
            (f logical) Tin hstart with
          ⟨Tout, hhalts, hseparator⟩
        exact ⟨Tout, hhalts, ⟨hseparator, hexists⟩⟩ }

private theorem seekTape1Description_contract_guardCells :
    CursorRoutineContract
      (fun logical physical =>
        LogicalTapeAtHasGuardCells logical 1 ∧
          AtExistingTapeSeparator logical 0 physical)
      (fun logical physical =>
        LogicalTapeAtHasGuardCells logical 1 ∧
          AtExistingTapeSeparator logical 1 physical)
      seekTape1Description := by
  exact
    { subroutineReady := seekTape1Description_contract.subroutineReady
      realizes := by
        intro logical Tin hsource
        rcases hsource with ⟨hguards, hstart⟩
        rcases hguards with ⟨T, rest, hdrop, hguard⟩
        rcases seekTape1Description_contract.realizes
            logical Tin hstart with
          ⟨Tout, hhalts, hseparator⟩
        exact
          ⟨Tout, hhalts,
            ⟨⟨T, rest, hdrop, hguard⟩,
              ⟨hseparator, ⟨T, rest, hdrop⟩⟩⟩⟩ }

/--
Seek from block start to tape 1 and return to block start without inspecting or
mutating the selected tape.
-/
def cursorTape1NoopAndReturnToBlockStartDescription :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    seekTape1Description
    returnFromTape1SeparatorToBlockStartDescription

theorem cursorTape1NoopAndReturnToBlockStartDescription_contract :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator logical 0 physical ∧
          (exists T : Tape Bool, exists rest : List (Tape Bool),
            logical.drop 1 = T :: rest))
      (fun logical physical =>
        AtTapeSeparator logical 0 physical)
      cursorTape1NoopAndReturnToBlockStartDescription := by
  have hseek :
      CursorRoutineContract
        (fun logical physical =>
          AtExistingTapeSeparator logical 0 physical ∧
            (exists T : Tape Bool, exists rest : List (Tape Bool),
              logical.drop 1 = T :: rest))
        (fun logical physical =>
          AtExistingTapeSeparator logical 1 physical)
        seekTape1Description :=
    seekTape1Description_contract_existing_map id
  have hreturn :
      CursorRoutineContract
        (fun logical physical =>
          AtExistingTapeSeparator logical 1 physical)
        (fun logical physical =>
          AtTapeSeparator logical 0 physical)
        returnFromTape1SeparatorToBlockStartDescription :=
    returnFromTape1SeparatorToBlockStartDescription_contract_existing_map id
  exact
    cursorRoutineContract_canonicalSeq_self
      hseek hreturn
      (by
        intro logical physical hexisting
        exact atExistingTapeSeparator_moveLeft_moveRight hexisting)

private theorem writeHeadCell_one_apply_drop_exists
    (cell : Option Bool) {logical : List (Tape Bool)}
    (hexists :
      exists T : Tape Bool, exists rest : List (Tape Bool),
        logical.drop 1 = T :: rest) :
    exists T : Tape Bool, exists rest : List (Tape Bool),
      ((PhysicalPrimitive.writeHeadCell 1 cell).apply logical).drop 1 =
        T :: rest := by
  cases logical with
  | nil =>
      simp at hexists
  | cons T rest =>
      cases rest with
      | nil =>
          simp at hexists
      | cons U tail =>
          exact
            ⟨Tape.write cell U, tail, by
              simp [PhysicalPrimitive.apply, Description.tapeAt]⟩

private theorem moveHead_one_apply_drop_exists
    (move : HeadMove) {logical : List (Tape Bool)}
    (hexists :
      exists T : Tape Bool, exists rest : List (Tape Bool),
        logical.drop 1 = T :: rest) :
    exists T : Tape Bool, exists rest : List (Tape Bool),
      ((PhysicalPrimitive.moveHead 1 move).apply logical).drop 1 =
        T :: rest := by
  cases logical with
  | nil =>
      simp at hexists
  | cons T rest =>
      cases rest with
      | nil =>
          simp at hexists
      | cons U tail =>
          exact
            ⟨move.apply U, tail, by
              cases move <;>
                simp [PhysicalPrimitive.apply, Description.tapeAt,
                  HeadMove.apply]⟩

/--
Seek from block start to tape 1, write the selected head cell, and return to
the tape-1 separator.
-/
def cursorTape1WriteHeadCellAndReturnToSeparatorDescription
    (cell : Option Bool) : MachineDescription :=
  canonicalPrimitiveSeqDescription
    seekTape1Description
    (cursorWriteHeadCellAndReturnToSeparatorDescription cell)

theorem cursorTape1WriteHeadCellAndReturnToSeparatorDescription_contract
    (cell : Option Bool) :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator logical 0 physical ∧
          (exists T : Tape Bool, exists rest : List (Tape Bool),
            logical.drop 1 = T :: rest))
      (fun logical physical =>
        AtExistingTapeSeparator
          ((PhysicalPrimitive.writeHeadCell 1 cell).apply logical)
          1 physical)
      (cursorTape1WriteHeadCellAndReturnToSeparatorDescription
        cell) := by
  have hseek :
      CursorRoutineContract
        (fun logical physical =>
          AtExistingTapeSeparator logical 0 physical ∧
            (exists T : Tape Bool, exists rest : List (Tape Bool),
              logical.drop 1 = T :: rest))
        (fun logical physical =>
          AtExistingTapeSeparator logical 1 physical)
        seekTape1Description :=
    seekTape1Description_contract_existing_map id
  have hwrite :
      CursorRoutineContract
        (fun logical physical =>
          AtExistingTapeSeparator logical 1 physical)
        (fun logical physical =>
          AtExistingTapeSeparator
            ((PhysicalPrimitive.writeHeadCell 1 cell).apply logical)
            1 physical)
        (cursorWriteHeadCellAndReturnToSeparatorDescription
          cell) := by
    exact
      { subroutineReady :=
          (cursorWriteHeadCellAndReturnToSeparatorDescription_contract
            1 cell).subroutineReady
        realizes := by
          intro logical Tin hexisting
          rcases
              (cursorWriteHeadCellAndReturnToSeparatorDescription_contract
                1 cell).realizes logical Tin hexisting with
            ⟨Tout, hhalts, hseparator⟩
          exact
            ⟨Tout, hhalts,
              ⟨hseparator,
                writeHeadCell_one_apply_drop_exists cell
                  hexisting.right⟩⟩ }
  exact
    cursorRoutineContract_canonicalSeq_self
      hseek hwrite
      (by
        intro logical physical hexisting
        exact atExistingTapeSeparator_moveLeft_moveRight hexisting)

/--
Seek from block start to tape 1, write the selected head cell, and return all
the way to the canonical block-start separator.
-/
def cursorTape1WriteHeadCellAndReturnToBlockStartDescription
    (cell : Option Bool) : MachineDescription :=
  canonicalPrimitiveSeqDescription
    (cursorTape1WriteHeadCellAndReturnToSeparatorDescription cell)
    returnFromTape1SeparatorToBlockStartDescription

theorem cursorTape1WriteHeadCellAndReturnToBlockStartDescription_contract
    (cell : Option Bool) :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator logical 0 physical ∧
          (exists T : Tape Bool, exists rest : List (Tape Bool),
            logical.drop 1 = T :: rest))
      (fun logical physical =>
        AtTapeSeparator
          ((PhysicalPrimitive.writeHeadCell 1 cell).apply logical)
          0 physical)
      (cursorTape1WriteHeadCellAndReturnToBlockStartDescription
        cell) := by
  have hreturn :
      CursorRoutineContract
        (fun logical physical =>
          AtExistingTapeSeparator
            ((PhysicalPrimitive.writeHeadCell 1 cell).apply logical)
            1 physical)
        (fun logical physical =>
          AtTapeSeparator
            ((PhysicalPrimitive.writeHeadCell 1 cell).apply logical)
            0 physical)
        returnFromTape1SeparatorToBlockStartDescription :=
    returnFromTape1SeparatorToBlockStartDescription_contract_existing_map
      (fun logical =>
        (PhysicalPrimitive.writeHeadCell 1 cell).apply logical)
  exact
    cursorRoutineContract_canonicalSeq_self
      (cursorTape1WriteHeadCellAndReturnToSeparatorDescription_contract
        cell)
      hreturn
      (by
        intro logical physical hexisting
        exact atExistingTapeSeparator_moveLeft_moveRight hexisting)

/--
Seek from block start to tape 1, move its head one cell left locally, and
return to the tape-1 separator.
-/
def cursorTape1MoveHeadLeftLocalAndReturnToSeparatorDescription :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    seekTape1Description
    cursorMoveHeadLeftLocalAndReturnToSeparatorDescription

theorem cursorTape1MoveHeadLeftLocalAndReturnToSeparatorDescription_contract_guarded :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator (guardLogicalTapes logical) 0 physical ∧
          (exists T : Tape Bool, exists rest : List (Tape Bool),
            (guardLogicalTapes logical).drop 1 = T :: rest))
      (fun logical physical =>
        AtExistingTapeSeparator
          ((PhysicalPrimitive.moveHead 1 HeadMove.left).apply
            (guardLogicalTapes logical))
          1 physical)
      cursorTape1MoveHeadLeftLocalAndReturnToSeparatorDescription := by
  have hseek :
      CursorRoutineContract
        (fun logical physical =>
          AtExistingTapeSeparator (guardLogicalTapes logical) 0 physical ∧
            (exists T : Tape Bool, exists rest : List (Tape Bool),
              (guardLogicalTapes logical).drop 1 = T :: rest))
        (fun logical physical =>
          AtExistingTapeSeparator (guardLogicalTapes logical) 1 physical)
        seekTape1Description :=
    seekTape1Description_contract_existing_map guardLogicalTapes
  have hmove :
      CursorRoutineContract
        (fun logical physical =>
          AtExistingTapeSeparator (guardLogicalTapes logical) 1 physical)
        (fun logical physical =>
          AtExistingTapeSeparator
            ((PhysicalPrimitive.moveHead 1 HeadMove.left).apply
              (guardLogicalTapes logical))
            1 physical)
        cursorMoveHeadLeftLocalAndReturnToSeparatorDescription := by
    exact
      { subroutineReady :=
          (cursorMoveHeadLeftLocalAndReturnToSeparatorDescription_contract_guarded
            1).subroutineReady
        realizes := by
          intro logical Tin hexisting
          rcases
              (cursorMoveHeadLeftLocalAndReturnToSeparatorDescription_contract_guarded
                1).realizes logical Tin hexisting with
            ⟨Tout, hhalts, hseparator⟩
          exact
            ⟨Tout, hhalts,
              ⟨hseparator,
                moveHead_one_apply_drop_exists HeadMove.left
                  hexisting.right⟩⟩ }
  exact
    cursorRoutineContract_canonicalSeq_self
      hseek hmove
      (by
        intro logical physical hexisting
        exact atExistingTapeSeparator_moveLeft_moveRight hexisting)

theorem cursorTape1MoveHeadLeftLocalAndReturnToSeparatorDescription_contract_withGuardCells :
    CursorRoutineContract
      (fun logical physical =>
        LogicalTapeAtHasGuardCells logical 1 ∧
          AtExistingTapeSeparator logical 0 physical)
      (fun logical physical =>
        AtExistingTapeSeparator
          ((PhysicalPrimitive.moveHead 1 HeadMove.left).apply logical)
          1 physical)
      cursorTape1MoveHeadLeftLocalAndReturnToSeparatorDescription := by
  have hseek :
      CursorRoutineContract
        (fun logical physical =>
          LogicalTapeAtHasGuardCells logical 1 ∧
            AtExistingTapeSeparator logical 0 physical)
        (fun logical physical =>
          LogicalTapeAtHasGuardCells logical 1 ∧
            AtExistingTapeSeparator logical 1 physical)
        seekTape1Description :=
    seekTape1Description_contract_guardCells
  have hmove :
      CursorRoutineContract
        (fun logical physical =>
          LogicalTapeAtHasGuardCells logical 1 ∧
            AtExistingTapeSeparator logical 1 physical)
        (fun logical physical =>
          AtExistingTapeSeparator
            ((PhysicalPrimitive.moveHead 1 HeadMove.left).apply logical)
            1 physical)
        cursorMoveHeadLeftLocalAndReturnToSeparatorDescription := by
    exact
      { subroutineReady :=
          (cursorMoveHeadLeftLocalAndReturnToSeparatorDescription_contract_withGuardCells
            1).subroutineReady
        realizes := by
          intro logical Tin hsource
          rcases hsource with ⟨hguards, hexisting⟩
          rcases
              (cursorMoveHeadLeftLocalAndReturnToSeparatorDescription_contract_withGuardCells
                1).realizes logical Tin ⟨hguards, hexisting⟩ with
            ⟨Tout, hhalts, hseparator⟩
          exact
            ⟨Tout, hhalts,
              ⟨hseparator,
                moveHead_one_apply_drop_exists HeadMove.left
                  hexisting.right⟩⟩ }
  exact
    cursorRoutineContract_canonicalSeq_self
      hseek hmove
      (by
        intro logical physical hmiddle
        exact atExistingTapeSeparator_moveLeft_moveRight hmiddle.right)

/--
Seek from block start to tape 1, move its head one cell left locally, and
return all the way to the canonical block-start separator.
-/
def cursorTape1MoveHeadLeftLocalAndReturnToBlockStartDescription :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    cursorTape1MoveHeadLeftLocalAndReturnToSeparatorDescription
    returnFromTape1SeparatorToBlockStartDescription

theorem cursorTape1MoveHeadLeftLocalAndReturnToBlockStartDescription_contract_guarded :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator (guardLogicalTapes logical) 0 physical ∧
          (exists T : Tape Bool, exists rest : List (Tape Bool),
            (guardLogicalTapes logical).drop 1 = T :: rest))
      (fun logical physical =>
        AtTapeSeparator
          ((PhysicalPrimitive.moveHead 1 HeadMove.left).apply
            (guardLogicalTapes logical))
          0 physical)
      cursorTape1MoveHeadLeftLocalAndReturnToBlockStartDescription := by
  have hreturn :
      CursorRoutineContract
        (fun logical physical =>
          AtExistingTapeSeparator
            ((PhysicalPrimitive.moveHead 1 HeadMove.left).apply
              (guardLogicalTapes logical))
            1 physical)
        (fun logical physical =>
          AtTapeSeparator
            ((PhysicalPrimitive.moveHead 1 HeadMove.left).apply
              (guardLogicalTapes logical))
            0 physical)
        returnFromTape1SeparatorToBlockStartDescription :=
    returnFromTape1SeparatorToBlockStartDescription_contract_existing_map
      (fun logical =>
        (PhysicalPrimitive.moveHead 1 HeadMove.left).apply
          (guardLogicalTapes logical))
  exact
    cursorRoutineContract_canonicalSeq_self
      cursorTape1MoveHeadLeftLocalAndReturnToSeparatorDescription_contract_guarded
      hreturn
      (by
        intro logical physical hexisting
        exact atExistingTapeSeparator_moveLeft_moveRight hexisting)

theorem cursorTape1MoveHeadLeftLocalAndReturnToBlockStartDescription_contract_withGuardCells :
    CursorRoutineContract
      (fun logical physical =>
        LogicalTapeAtHasGuardCells logical 1 ∧
          AtExistingTapeSeparator logical 0 physical)
      (fun logical physical =>
        AtTapeSeparator
          ((PhysicalPrimitive.moveHead 1 HeadMove.left).apply logical)
          0 physical)
      cursorTape1MoveHeadLeftLocalAndReturnToBlockStartDescription := by
  have hreturn :
      CursorRoutineContract
        (fun logical physical =>
          AtExistingTapeSeparator
            ((PhysicalPrimitive.moveHead 1 HeadMove.left).apply logical)
            1 physical)
        (fun logical physical =>
          AtTapeSeparator
            ((PhysicalPrimitive.moveHead 1 HeadMove.left).apply logical)
            0 physical)
        returnFromTape1SeparatorToBlockStartDescription :=
    returnFromTape1SeparatorToBlockStartDescription_contract_existing_map
      (fun logical =>
        (PhysicalPrimitive.moveHead 1 HeadMove.left).apply logical)
  exact
    cursorRoutineContract_canonicalSeq_self
      cursorTape1MoveHeadLeftLocalAndReturnToSeparatorDescription_contract_withGuardCells
      hreturn
      (by
        intro logical physical hexisting
        exact atExistingTapeSeparator_moveLeft_moveRight hexisting)

/--
Seek from block start to tape 1, move its head one cell right locally, and
return to the tape-1 separator.
-/
def cursorTape1MoveHeadRightLocalAndReturnToSeparatorDescription :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    seekTape1Description
    cursorMoveHeadRightLocalAndReturnToSeparatorDescription

theorem cursorTape1MoveHeadRightLocalAndReturnToSeparatorDescription_contract_guarded :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator (guardLogicalTapes logical) 0 physical ∧
          (exists T : Tape Bool, exists rest : List (Tape Bool),
            (guardLogicalTapes logical).drop 1 = T :: rest))
      (fun logical physical =>
        AtExistingTapeSeparator
          ((PhysicalPrimitive.moveHead 1 HeadMove.right).apply
            (guardLogicalTapes logical))
          1 physical)
      cursorTape1MoveHeadRightLocalAndReturnToSeparatorDescription := by
  have hseek :
      CursorRoutineContract
        (fun logical physical =>
          AtExistingTapeSeparator (guardLogicalTapes logical) 0 physical ∧
            (exists T : Tape Bool, exists rest : List (Tape Bool),
              (guardLogicalTapes logical).drop 1 = T :: rest))
        (fun logical physical =>
          AtExistingTapeSeparator (guardLogicalTapes logical) 1 physical)
        seekTape1Description :=
    seekTape1Description_contract_existing_map guardLogicalTapes
  have hmove :
      CursorRoutineContract
        (fun logical physical =>
          AtExistingTapeSeparator (guardLogicalTapes logical) 1 physical)
        (fun logical physical =>
          AtExistingTapeSeparator
            ((PhysicalPrimitive.moveHead 1 HeadMove.right).apply
              (guardLogicalTapes logical))
            1 physical)
        cursorMoveHeadRightLocalAndReturnToSeparatorDescription := by
    exact
      { subroutineReady :=
          (cursorMoveHeadRightLocalAndReturnToSeparatorDescription_contract_guarded
            1).subroutineReady
        realizes := by
          intro logical Tin hexisting
          rcases
              (cursorMoveHeadRightLocalAndReturnToSeparatorDescription_contract_guarded
                1).realizes logical Tin hexisting with
            ⟨Tout, hhalts, hseparator⟩
          exact
            ⟨Tout, hhalts,
              ⟨hseparator,
                moveHead_one_apply_drop_exists HeadMove.right
                  hexisting.right⟩⟩ }
  exact
    cursorRoutineContract_canonicalSeq_self
      hseek hmove
      (by
        intro logical physical hexisting
        exact atExistingTapeSeparator_moveLeft_moveRight hexisting)

theorem cursorTape1MoveHeadRightLocalAndReturnToSeparatorDescription_contract_withGuardCells :
    CursorRoutineContract
      (fun logical physical =>
        LogicalTapeAtHasGuardCells logical 1 ∧
          AtExistingTapeSeparator logical 0 physical)
      (fun logical physical =>
        AtExistingTapeSeparator
          ((PhysicalPrimitive.moveHead 1 HeadMove.right).apply logical)
          1 physical)
      cursorTape1MoveHeadRightLocalAndReturnToSeparatorDescription := by
  have hseek :
      CursorRoutineContract
        (fun logical physical =>
          LogicalTapeAtHasGuardCells logical 1 ∧
            AtExistingTapeSeparator logical 0 physical)
        (fun logical physical =>
          LogicalTapeAtHasGuardCells logical 1 ∧
            AtExistingTapeSeparator logical 1 physical)
        seekTape1Description :=
    seekTape1Description_contract_guardCells
  have hmove :
      CursorRoutineContract
        (fun logical physical =>
          LogicalTapeAtHasGuardCells logical 1 ∧
            AtExistingTapeSeparator logical 1 physical)
        (fun logical physical =>
          AtExistingTapeSeparator
            ((PhysicalPrimitive.moveHead 1 HeadMove.right).apply logical)
            1 physical)
        cursorMoveHeadRightLocalAndReturnToSeparatorDescription := by
    exact
      { subroutineReady :=
          (cursorMoveHeadRightLocalAndReturnToSeparatorDescription_contract_withGuardCells
            1).subroutineReady
        realizes := by
          intro logical Tin hsource
          rcases hsource with ⟨hguards, hexisting⟩
          rcases
              (cursorMoveHeadRightLocalAndReturnToSeparatorDescription_contract_withGuardCells
                1).realizes logical Tin ⟨hguards, hexisting⟩ with
            ⟨Tout, hhalts, hseparator⟩
          exact
            ⟨Tout, hhalts,
              ⟨hseparator,
                moveHead_one_apply_drop_exists HeadMove.right
                  hexisting.right⟩⟩ }
  exact
    cursorRoutineContract_canonicalSeq_self
      hseek hmove
      (by
        intro logical physical hmiddle
        exact atExistingTapeSeparator_moveLeft_moveRight hmiddle.right)

/--
Seek from block start to tape 1, move its head one cell right locally, and
return all the way to the canonical block-start separator.
-/
def cursorTape1MoveHeadRightLocalAndReturnToBlockStartDescription :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    cursorTape1MoveHeadRightLocalAndReturnToSeparatorDescription
    returnFromTape1SeparatorToBlockStartDescription

theorem cursorTape1MoveHeadRightLocalAndReturnToBlockStartDescription_contract_guarded :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator (guardLogicalTapes logical) 0 physical ∧
          (exists T : Tape Bool, exists rest : List (Tape Bool),
            (guardLogicalTapes logical).drop 1 = T :: rest))
      (fun logical physical =>
        AtTapeSeparator
          ((PhysicalPrimitive.moveHead 1 HeadMove.right).apply
            (guardLogicalTapes logical))
          0 physical)
      cursorTape1MoveHeadRightLocalAndReturnToBlockStartDescription := by
  have hreturn :
      CursorRoutineContract
        (fun logical physical =>
          AtExistingTapeSeparator
            ((PhysicalPrimitive.moveHead 1 HeadMove.right).apply
              (guardLogicalTapes logical))
            1 physical)
        (fun logical physical =>
          AtTapeSeparator
            ((PhysicalPrimitive.moveHead 1 HeadMove.right).apply
              (guardLogicalTapes logical))
            0 physical)
        returnFromTape1SeparatorToBlockStartDescription :=
    returnFromTape1SeparatorToBlockStartDescription_contract_existing_map
      (fun logical =>
        (PhysicalPrimitive.moveHead 1 HeadMove.right).apply
          (guardLogicalTapes logical))
  exact
    cursorRoutineContract_canonicalSeq_self
      cursorTape1MoveHeadRightLocalAndReturnToSeparatorDescription_contract_guarded
      hreturn
      (by
        intro logical physical hexisting
        exact atExistingTapeSeparator_moveLeft_moveRight hexisting)

theorem cursorTape1MoveHeadRightLocalAndReturnToBlockStartDescription_contract_withGuardCells :
    CursorRoutineContract
      (fun logical physical =>
        LogicalTapeAtHasGuardCells logical 1 ∧
          AtExistingTapeSeparator logical 0 physical)
      (fun logical physical =>
        AtTapeSeparator
          ((PhysicalPrimitive.moveHead 1 HeadMove.right).apply logical)
          0 physical)
      cursorTape1MoveHeadRightLocalAndReturnToBlockStartDescription := by
  have hreturn :
      CursorRoutineContract
        (fun logical physical =>
          AtExistingTapeSeparator
            ((PhysicalPrimitive.moveHead 1 HeadMove.right).apply logical)
            1 physical)
        (fun logical physical =>
          AtTapeSeparator
            ((PhysicalPrimitive.moveHead 1 HeadMove.right).apply logical)
            0 physical)
        returnFromTape1SeparatorToBlockStartDescription :=
    returnFromTape1SeparatorToBlockStartDescription_contract_existing_map
      (fun logical =>
        (PhysicalPrimitive.moveHead 1 HeadMove.right).apply logical)
  exact
    cursorRoutineContract_canonicalSeq_self
      cursorTape1MoveHeadRightLocalAndReturnToSeparatorDescription_contract_withGuardCells
      hreturn
      (by
        intro logical physical hexisting
        exact atExistingTapeSeparator_moveLeft_moveRight hexisting)

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
