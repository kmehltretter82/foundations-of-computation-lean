import FoC.Computability.Compiler.Structured.Lowering.CursorPipelines.Tape2AndTape1Read

set_option doc.verso true

/-!
# Cursor tape-1 write and move pipelines

Tape-1 no-op, write, and local head-move cursor pipelines.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

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
