import FoC.Computability.Compiler.Structured.Lowering.Composition
import FoC.Computability.Compiler.Structured.Lowering.CursorBasic
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.TapeLemmas

set_option doc.verso true

/-!
# Structured cursor composition

This module composes cursor-level routines.  Cursor contracts expose internal
physical positions, so composition must explicitly account for the standard
right/left handoff bounce inserted by
{name (full := FoC.Computability.CommonGround.FiniteTransducers.Structured.MultiTapeLowering.canonicalPrimitiveSeqDescription)}`canonicalPrimitiveSeqDescription`.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

private theorem logicalTapeCode_exists_cons_cons
    (T : Tape Bool) :
    exists first : Option Bool, exists second : Option Bool,
    exists tail : List (Option Bool),
      logicalTapeCode T = first :: second :: tail := by
  cases hleft : T.left.reverse with
  | nil =>
      refine ⟨some true, some true,
        List.append (logicalCellCode T.head)
          (logicalCellListCode T.right), ?_⟩
      simp only [logicalTapeCode, hleft, logicalCellListCode_nil,
        headMarkerCells]
      rfl
  | cons cell cells =>
      let suffix :=
        List.append (logicalCellListCode cells)
          (List.append headMarkerCells
            (List.append (logicalCellCode T.head)
              (logicalCellListCode T.right)))
      cases cell with
      | none =>
          refine ⟨some false, some false, suffix, ?_⟩
          simp only [logicalTapeCode, hleft, logicalCellListCode_cons,
            logicalCellCode_none, suffix]
          rfl
      | some bit =>
          cases bit
          · refine ⟨some false, some true, suffix, ?_⟩
            simp only [logicalTapeCode, hleft, logicalCellListCode_cons,
              logicalCellCode_some_false, suffix]
            rfl
          · refine ⟨some true, some false, suffix, ?_⟩
            simp only [logicalTapeCode, hleft, logicalCellListCode_cons,
              logicalCellCode_some_true, suffix]
            rfl

private theorem logicalCellCode_exists_cons_cons
    (cell : Option Bool) :
    exists first : Option Bool, exists second : Option Bool,
    exists tail : List (Option Bool),
      logicalCellCode cell = first :: second :: tail := by
  cases cell with
  | none =>
      exact ⟨some false, some false, [], rfl⟩
  | some bit =>
      cases bit
      · exact ⟨some false, some true, [], rfl⟩
      · exact ⟨some true, some false, [], rfl⟩

theorem atTapeSegmentEntry_moveLeft_moveRight
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {physical : Tape Bool}
    (hentry : AtTapeSegmentEntry logical tapeIndex physical) :
    Tape.move Direction.left (Tape.move Direction.right physical) =
      physical := by
  rcases hentry with ⟨T, rest, _hdrop, hphysical⟩
  rcases logicalTapeCode_exists_cons_cons T with
    ⟨first, second, tail, hcode⟩
  have hmove :=
    tapeAtCells_move_left_move_right_cons_cons
      (left :=
        (List.append
          (encodedPrefixBeforeTape logical tapeIndex)
          tapeSeparatorCells).reverse)
      (head := first)
      (next := second)
      (right := List.append tail
        (encodedStructuredTapeCells rest))
  simpa only [hphysical, tapeAtEncodedSplit, hcode,
    List.append_assoc, List.reverse_append]
    using hmove

theorem atExistingTapeSeparator_moveLeft_moveRight
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {physical : Tape Bool}
    (hseparator : AtExistingTapeSeparator logical tapeIndex physical) :
    Tape.move Direction.left (Tape.move Direction.right physical) =
      physical := by
  rcases hseparator with ⟨hposition, T, rest, hdrop⟩
  rcases hposition with ⟨_hle, hphysical⟩
  rcases logicalTapeBits_exists_cons T with ⟨bit, bits, hbits⟩
  have hmove :=
    tapeAtCells_move_left_move_right_cons_cons
      ((encodedPrefixBeforeTape logical tapeIndex).reverse)
      none (some bit)
      (List.append (bits.map some)
        (encodedStructuredTapeCells rest))
  simpa [hphysical, tapeAtEncodedSplit, encodedSuffixFromTape,
    hdrop, encodedStructuredTapeCells, logicalTapeCode_eq_map_some T,
    hbits, tapeSeparatorCells, List.map_append, List.append_assoc]
    using hmove

theorem atTapeHeadMarker_moveLeft_moveRight
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {physical : Tape Bool}
    (hmarker : AtTapeHeadMarker logical tapeIndex physical) :
    Tape.move Direction.left (Tape.move Direction.right physical) =
      physical := by
  rcases hmarker with ⟨T, rest, _hdrop, hphysical⟩
  have hmove :=
    tapeAtCells_move_left_move_right_cons_cons
      (left :=
        (List.append
          (encodedPrefixBeforeTape logical tapeIndex)
          (List.append tapeSeparatorCells
            (logicalCellListCode T.left.reverse))).reverse)
      (head := some true)
      (next := some true)
      (right :=
        List.append (logicalCellCode T.head)
          (List.append (logicalCellListCode T.right)
            (encodedStructuredTapeCells rest)))
  simpa [hphysical, tapeAtEncodedSplit, headMarkerCells,
    List.append_assoc] using hmove

theorem atTapeHeadCellCode_moveLeft_moveRight
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {physical : Tape Bool}
    (hcell : AtTapeHeadCellCode logical tapeIndex physical) :
    Tape.move Direction.left (Tape.move Direction.right physical) =
      physical := by
  rcases hcell with ⟨T, rest, _hdrop, hphysical⟩
  cases hhead : T.head with
  | none =>
      have hmove :=
        tapeAtCells_move_left_move_right_cons_cons
          (left :=
            (List.append
              (encodedPrefixBeforeTape logical tapeIndex)
              (List.append tapeSeparatorCells
                (List.append (logicalCellListCode T.left.reverse)
                  headMarkerCells))).reverse)
          (head := some false)
          (next := some false)
          (right :=
            List.append (logicalCellListCode T.right)
              (encodedStructuredTapeCells rest))
      simpa [hphysical, tapeAtEncodedSplit, hhead, logicalCellCode,
        logicalCellBits, List.append_assoc] using hmove
  | some bit =>
      cases bit
      · have hmove :=
          tapeAtCells_move_left_move_right_cons_cons
            (left :=
              (List.append
                (encodedPrefixBeforeTape logical tapeIndex)
                (List.append tapeSeparatorCells
                  (List.append (logicalCellListCode T.left.reverse)
                    headMarkerCells))).reverse)
            (head := some false)
            (next := some true)
            (right :=
              List.append (logicalCellListCode T.right)
                (encodedStructuredTapeCells rest))
        simpa [hphysical, tapeAtEncodedSplit, hhead, logicalCellCode,
          logicalCellBits, List.append_assoc] using hmove
      · have hmove :=
          tapeAtCells_move_left_move_right_cons_cons
            (left :=
              (List.append
                (encodedPrefixBeforeTape logical tapeIndex)
                (List.append tapeSeparatorCells
                  (List.append (logicalCellListCode T.left.reverse)
                    headMarkerCells))).reverse)
            (head := some true)
            (next := some false)
            (right :=
              List.append (logicalCellListCode T.right)
                (encodedStructuredTapeCells rest))
        simpa [hphysical, tapeAtEncodedSplit, hhead, logicalCellCode,
          logicalCellBits, List.append_assoc] using hmove

theorem atTapeHeadCellCodeWithRead_moveLeft_moveRight
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {expected : Option Bool} {physical : Tape Bool}
    (hcell : AtTapeHeadCellCodeWithRead logical tapeIndex expected
      physical) :
    Tape.move Direction.left (Tape.move Direction.right physical) =
      physical := by
  rcases hcell with ⟨T, rest, hdrop, _hread, hphysical⟩
  exact atTapeHeadCellCode_moveLeft_moveRight
    ⟨T, rest, hdrop, hphysical⟩

theorem atTapeHeadCellCode_to_withRead
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {expected : Option Bool} {physical : Tape Bool}
    (hcell : AtTapeHeadCellCode logical tapeIndex physical)
    (hread :
      Tape.read (Description.tapeAt logical tapeIndex) = expected) :
    AtTapeHeadCellCodeWithRead logical tapeIndex expected physical := by
  rcases hcell with ⟨T, rest, hdrop, hphysical⟩
  have htapeAt : Description.tapeAt logical tapeIndex = T :=
    description_tapeAt_eq_of_drop_eq_cons hdrop
  exact ⟨T, rest, hdrop, by simpa [htapeAt] using hread, hphysical⟩

/--
Compose two cursor routines through the canonical right/left handoff.

The bridge hypothesis is deliberately explicit: some cursor predicates are
stable under the handoff because the physical tape has a real cell to the right,
while others need a dedicated layout lemma.  Keeping that proof at each call
site prevents this low-level theorem from hiding tape-shape obligations.
-/
theorem cursorRoutineContract_canonicalSeq
    {source middle bouncedMiddle target :
      List (Tape Bool) -> Tape Bool -> Prop}
    {A B : MachineDescription}
    (hA : CursorRoutineContract source middle A)
    (hB : CursorRoutineContract bouncedMiddle target B)
    (hbridge :
      forall logical : List (Tape Bool),
      forall T : Tape Bool,
        middle logical T ->
          bouncedMiddle logical
            (Tape.move Direction.left (Tape.move Direction.right T))) :
    CursorRoutineContract source target
      (canonicalPrimitiveSeqDescription A B) where
  subroutineReady :=
    canonicalPrimitiveSeqDescription_subroutineReady
      hA.subroutineReady hB.subroutineReady
  realizes := by
    intro logical Tin hsource
    rcases hA.realizes logical Tin hsource with
      ⟨Tmid, hAhalts, hmiddle⟩
    rcases hB.realizes logical
        (Tape.move Direction.left (Tape.move Direction.right Tmid))
        (hbridge logical Tmid hmiddle) with
      ⟨Tout, hBhalts, htarget⟩
    exact
      ⟨Tout,
        canonicalPrimitiveSeqDescription_haltsFromTape_of_haltsFromTape
          hA.subroutineReady hB.subroutineReady hAhalts hBhalts,
        htarget⟩

/--
Compose two cursor routines when the canonical handoff returns exactly to the
same cursor shape.
-/
theorem cursorRoutineContract_canonicalSeq_self
    {source middle target :
      List (Tape Bool) -> Tape Bool -> Prop}
    {A B : MachineDescription}
    (hA : CursorRoutineContract source middle A)
    (hB : CursorRoutineContract middle target B)
    (hmove :
      forall logical : List (Tape Bool),
      forall T : Tape Bool,
        middle logical T ->
          Tape.move Direction.left (Tape.move Direction.right T) = T) :
    CursorRoutineContract source target
      (canonicalPrimitiveSeqDescription A B) :=
  cursorRoutineContract_canonicalSeq
    hA hB
    (by
      intro logical T hmiddle
      rw [hmove logical T hmiddle]
      exact hmiddle)

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
