import FoC.Computability.Compiler.ClosedCfg.ProjTail.StructuredPrefixEraserShape

set_option doc.verso true

/-!
# Pair-parity guarded two-tape structured prefix eraser

This module provides the concrete finite machine that erases the two guarded
structured logical-tape fields in front of the selected decoder footprint.

The machine works from the right tape end.  It first writes a two-cell marker
over the two trailing blanks, then scans leftward through the footprint with a
two-state parity walk.  Inside the footprint every decoder pair is
{lit}`(none, cell)`, so odd offsets from the footprint end are always blank;
the first nonblank cell read at an odd offset is the last cell of the second
guarded field.  Both fields are erased leftward, then the head returns
rightward.  During the return scan the only adjacent nonblank pair on the tape
is the marker, so reading a nonblank immediately after a nonblank finds the
right tape end again; the machine erases the marker and halts.
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

/--
Pair-parity eraser for the guarded two-tape structured prefix.

States: {lit}`0` mark end cell, {lit}`1` mark the cell before it,
{lit}`2`/{lit}`3` leftward parity scan over the footprint pairs,
{lit}`4` erase the second guarded field, {lit}`5`/{lit}`6` cross the field
separator and erase the first guarded field, {lit}`7`/{lit}`8` rightward
return scan, {lit}`9` erase the first marker cell, {lit}`10` halt.
-/
def pairParityEraserDescription : MachineDescription where
  stateCount := 11
  start := 0
  halt := 10
  transitions :=
    [ transition 0 none (some true) Direction.left 1
    , transition 1 none (some true) Direction.left 2
    , transition 2 none none Direction.left 3
    , transition 2 (some false) (some false) Direction.left 3
    , transition 2 (some true) (some true) Direction.left 3
    , transition 3 none none Direction.left 2
    , transition 3 (some false) none Direction.left 4
    , transition 3 (some true) none Direction.left 4
    , transition 4 (some false) none Direction.left 4
    , transition 4 (some true) none Direction.left 4
    , transition 4 none none Direction.left 5
    , transition 5 (some false) none Direction.left 6
    , transition 5 (some true) none Direction.left 6
    , transition 6 (some false) none Direction.left 6
    , transition 6 (some true) none Direction.left 6
    , transition 6 none none Direction.right 7
    , transition 7 none none Direction.right 7
    , transition 7 (some false) (some false) Direction.right 8
    , transition 7 (some true) (some true) Direction.right 8
    , transition 8 none none Direction.right 7
    , transition 8 (some true) none Direction.left 9
    , transition 9 (some true) none Direction.right 10 ]

theorem pairParityEraserDescription_wellFormed :
    pairParityEraserDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := pairParityEraserDescription.transitions)
      (stateCount := pairParityEraserDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := pairParityEraserDescription.transitions)
      (by decide)

theorem pairParityEraserDescription_haltTransitionFree :
    pairParityEraserDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := pairParityEraserDescription.transitions)
    (state := pairParityEraserDescription.halt)
    (by decide)

theorem pairParityEraserDescription_subroutineReady :
    pairParityEraserDescription.SubroutineReady :=
  ⟨pairParityEraserDescription_wellFormed,
    pairParityEraserDescription_haltTransitionFree⟩

/-!
## Pair-list helpers

The decoder footprint is a flattened list of two-cell pairs whose left cell is
always blank.  The helpers below expose that pair structure in both reading
directions, plus the final-cell tracker used by the rightward return scan.
-/

/-- Flatten pair cells left to right: each source cell becomes
{lit}`[none, cell]`. -/
def pairParityEraserPairFlatten :
    List (Option Bool) -> List (Option Bool)
  | [] => []
  | cell :: rest => none :: cell :: pairParityEraserPairFlatten rest

/-- Flatten pair cells right to left: each source cell becomes
{lit}`[cell, none]`. -/
def pairParityEraserPairFlattenRev :
    List (Option Bool) -> List (Option Bool)
  | [] => []
  | cell :: rest => cell :: none :: pairParityEraserPairFlattenRev rest

/-- Last cell of a pair list, with an explicit default for the empty list. -/
def pairParityEraserLastCell :
    List (Option Bool) -> Option Bool -> Option Bool
  | [], cell => cell
  | next :: rest, _ => pairParityEraserLastCell rest next

/-- Return-scan state after passing a cell: blank keeps {lit}`7`, nonblank
sets {lit}`8`. -/
def pairParityEraserScanState : Option Bool -> Nat
  | none => 7
  | some _ => 8

theorem pairParityEraserPairFlatten_append
    (a b : List (Option Bool)) :
    pairParityEraserPairFlatten (a ++ b) =
      pairParityEraserPairFlatten a ++ pairParityEraserPairFlatten b := by
  induction a with
  | nil => rfl
  | cons cell rest ih =>
      simp [pairParityEraserPairFlatten, ih]

theorem pairParityEraserPairFlattenRev_append
    (a b : List (Option Bool)) :
    pairParityEraserPairFlattenRev (a ++ b) =
      pairParityEraserPairFlattenRev a ++
        pairParityEraserPairFlattenRev b := by
  induction a with
  | nil => rfl
  | cons cell rest ih =>
      simp [pairParityEraserPairFlattenRev, ih]

theorem pairParityEraserPairFlatten_reverse
    (cells : List (Option Bool)) :
    (pairParityEraserPairFlatten cells).reverse =
      pairParityEraserPairFlattenRev cells.reverse := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
      simp [pairParityEraserPairFlatten, List.reverse_cons, ih,
        pairParityEraserPairFlattenRev_append,
        pairParityEraserPairFlattenRev]

theorem pairParityEraserLastCell_append_none
    (cells : List (Option Bool)) (cell : Option Bool) :
    pairParityEraserLastCell (cells ++ [none]) cell = none := by
  induction cells generalizing cell with
  | nil => rfl
  | cons next rest ih =>
      simpa [pairParityEraserLastCell] using ih next

theorem pairParityEraserCellCells_eq_pair
    (cell : Option Bool) :
    selectedSegmentLogicalTapeDecoderCellCells cell = [none, cell] := by
  cases cell with
  | none => rfl
  | some bit => cases bit <;> rfl

theorem pairParityEraserCellCells_flatten_eq_pairFlatten
    (cells : List (Option Bool)) :
    (cells.map selectedSegmentLogicalTapeDecoderCellCells).flatten =
      pairParityEraserPairFlatten cells := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
      simp [pairParityEraserCellCells_eq_pair, ih,
        pairParityEraserPairFlatten]

/-- The decoder footprint is the pair flattening of three guard blanks plus
the payload cells. -/
theorem pairParityEraserFootprint_eq_pairFlatten
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintCells bits padding =
      pairParityEraserPairFlatten
        (none :: none :: none ::
          selectedSegmentLogicalTapeDecoderPayloadCells bits padding) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintCells_eq_fromPayload]
  rw [selectedSegmentLogicalTapeDecoderFootprintCellsFromPayload]
  rw [pairParityEraserCellCells_flatten_eq_pairFlatten]
  rw [selectedSegmentLogicalTapeDecoderGuardPrefixCells_cells]
  rfl

/-!
## Blank-block and trailing-blank helpers
-/

theorem pairParityEraserReplicate_none_cons
    (n : Nat) (xs : List (Option Bool)) :
    (none : Option Bool) ::
        (List.replicate n (none : Option Bool) ++ xs) =
      List.replicate (n + 1) (none : Option Bool) ++ xs := by
  simp [List.replicate_succ]

theorem pairParityEraserReplicate_none_append
    (a b : Nat) (xs : List (Option Bool)) :
    List.replicate a (none : Option Bool) ++
        (List.replicate b (none : Option Bool) ++ xs) =
      List.replicate (a + b) (none : Option Bool) ++ xs := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [show a + 1 + b = (a + b) + 1 by lia]
      simp only [List.replicate_succ, List.cons_append]
      rw [ih]

theorem pairParityEraserReplicate_none_middle
    (n : Nat) (xs : List (Option Bool)) :
    List.replicate n (none : Option Bool) ++ ((none : Option Bool) :: xs) =
      List.replicate (n + 1) (none : Option Bool) ++ xs := by
  induction n with
  | zero =>
      simp [List.replicate_succ]
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append]
      rw [ih]
      simp [List.replicate_succ]

theorem pairParityEraserDropTrailingNone_replicate
    (n : Nat) :
    Tape.dropTrailingNone
        (List.replicate n (none : Option Bool)) = [] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [List.replicate_succ, Tape.dropTrailingNone, ih]

theorem pairParityEraserDropTrailingNone_append_replicate
    (xs : List (Option Bool)) (n : Nat) :
    Tape.dropTrailingNone
        (xs ++ List.replicate n (none : Option Bool)) =
      Tape.dropTrailingNone xs := by
  induction xs with
  | nil =>
      simpa using pairParityEraserDropTrailingNone_replicate n
  | cons x xs ih =>
      rw [List.cons_append]
      rw [Tape.dropTrailingNone_cons, Tape.dropTrailingNone_cons]
      rw [ih]

theorem pairParityEraserDropTrailingNone_cons_blanks
    (xs : List (Option Bool)) (n : Nat) :
    Tape.dropTrailingNone
        ((none : Option Bool) ::
          (xs ++ List.replicate n (none : Option Bool))) =
      Tape.dropTrailingNone ((none : Option Bool) :: xs) := by
  simpa using
    pairParityEraserDropTrailingNone_append_replicate (none :: xs) n

/-!
## Endpoint tape shapes

The eraser endpoints are exposed as explicit tape records: the head rests on
the blank right end, the right context is empty, and the left context lists
the footprint and (for the source) the two guarded fields, nearest first.
-/

theorem pairParityEraserTape_eq_of_fields
    {T : Tape Bool} {l : List (Option Bool)} {h : Option Bool}
    {r : List (Option Bool)}
    (hl : T.left = l) (hh : T.head = h) (hr : T.right = r) :
    T = { left := l, head := h, right := r } := by
  cases T
  cases hl
  cases hh
  cases hr
  rfl

theorem pairParityEraserSourceTape_shape
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    guardedTwoTapeStructuredPrefixEraserSourceTape T0 T1 bits padding =
      { left := none ::
          ((selectedSegmentLogicalTapeDecoderDensifierFootprintCells
              bits padding).reverse ++
            (none ::
              (guardedTwoTapeStructuredPrefixCells T0 T1).reverse)),
        head := none,
        right := [] } := by
  refine pairParityEraserTape_eq_of_fields ?_ ?_ ?_
  · rw [guardedTwoTapeStructuredPrefixEraserSourceTape]
    rw [selectedSegmentLogicalTapeDecoderTargetTape_left]
    simp [selectedSegmentLogicalTapeDecoderStart,
      selectedSegmentLogicalTapeDecoder_cells_guard_rightEdgeScanSourceTapeFromLeft_eq_footprint]
  · rw [guardedTwoTapeStructuredPrefixEraserSourceTape]
    rw [selectedSegmentLogicalTapeDecoderTargetTape_head]
  · rw [guardedTwoTapeStructuredPrefixEraserSourceTape]
    rw [selectedSegmentLogicalTapeDecoderTargetTape_right]

theorem pairParityEraserTargetTape_shape
    (bits : Word Bool) (padding : List (Option Bool)) :
    guardedTwoTapeStructuredPrefixEraserTargetTape bits padding =
      { left := none ::
          ((selectedSegmentLogicalTapeDecoderDensifierFootprintCells
              bits padding).reverse ++ [none]),
        head := none,
        right := [] } := by
  rw [guardedTwoTapeStructuredPrefixEraserTargetTape]
  rw [selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload]
  rw [selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload]
  rw [← selectedSegmentLogicalTapeDecoderFootprintCells_eq_fromPayload]
  rw [rightEndCompactionSourceTape]
  simp [tapeAtCells, List.reverse_append]

theorem pairParityEraserPrefixCells_reverse
    (T0 T1 : Tape Bool) :
    (guardedTwoTapeStructuredPrefixCells T0 T1).reverse =
      (logicalTapeBits (guardLogicalTape T1)).reverse.map some ++
        (none ::
          ((logicalTapeBits (guardLogicalTape T0)).reverse.map some ++
            [none])) := by
  rw [guardedTwoTapeStructuredPrefixCells_expanded]
  simp [tapeSeparatorCells, logicalTapeCode_eq_map_some,
    List.reverse_append, List.map_reverse, List.append_assoc]

theorem pairParityEraserExists_two_cons
    {α : Type} (l : List α) (h : 2 ≤ l.length) :
    exists a b rest, l = a :: b :: rest := by
  cases l with
  | nil =>
      simp at h
  | cons a l' =>
      cases l' with
      | nil =>
          simp at h
      | cons b rest =>
          exact ⟨a, b, rest, rfl⟩

theorem pairParityEraserGuardedBits_two_le
    (T : Tape Bool) :
    2 ≤ (logicalTapeBits (guardLogicalTape T)).length := by
  rw [logicalTapeBits_length_guardedShape]
  lia


/-!
## Phase run lemmas

Each lemma is an exact {name}`MachineDescription.runConfig` equation for one
machine phase; the loop phases induct on the list they consume, generalizing
the tape contexts they accumulate.
-/

/-- Phase 1: write the two-cell end marker and land on the footprint end. -/
theorem pairParityEraser_run_mark
    (x : Option Bool) (rest : List (Option Bool)) :
    pairParityEraserDescription.runConfig 2
        { state := 0
          tape :=
            { left := none :: x :: rest
              head := none
              right := [] } } =
      { state := 2
        tape :=
          { left := rest
            head := x
            right := [some true, some true] } } := by
  simp [pairParityEraserDescription, runConfig, stepConfig,
    lookupTransition, Matches, transition, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft]

/-- Phase 2: leftward parity scan over reversed footprint pairs.  The scan
preserves every cell it passes and ends reading the cell after the block. -/
theorem pairParityEraser_run_scan
    (rev : List (Option Bool)) (c e : Option Bool)
    (leftRest right : List (Option Bool)) :
    pairParityEraserDescription.runConfig (2 * rev.length + 2)
        { state := 2
          tape :=
            { left := none ::
                (pairParityEraserPairFlattenRev rev ++ (e :: leftRest))
              head := c
              right := right } } =
      { state := 2
        tape :=
          { left := leftRest
            head := e
            right := (pairParityEraserPairFlattenRev rev).reverse ++
              (none :: c :: right) } } := by
  induction rev generalizing c right with
  | nil =>
      cases c with
      | none =>
          simp [pairParityEraserPairFlattenRev, pairParityEraserDescription,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      | some bit =>
          cases bit <;>
            simp [pairParityEraserPairFlattenRev,
              pairParityEraserDescription, runConfig, stepConfig,
              lookupTransition, Matches, transition, Tape.read, Tape.write,
              Tape.move, Tape.moveLeft]
  | cons d rest ih =>
      rw [show 2 * (d :: rest).length + 2 = 2 + (2 * rest.length + 2) by
        simp
        lia]
      rw [runConfig_add]
      have hstep :
          pairParityEraserDescription.runConfig 2
              { state := 2
                tape :=
                  { left := none ::
                      (pairParityEraserPairFlattenRev (d :: rest) ++
                        (e :: leftRest))
                    head := c
                    right := right } } =
            { state := 2
              tape :=
                { left := none ::
                    (pairParityEraserPairFlattenRev rest ++ (e :: leftRest))
                  head := d
                  right := none :: c :: right } } := by
        cases c with
        | none =>
            simp [pairParityEraserPairFlattenRev,
              pairParityEraserDescription, runConfig, stepConfig,
              lookupTransition, Matches, transition, Tape.read, Tape.write,
              Tape.move, Tape.moveLeft]
        | some bit =>
            cases bit <;>
              simp [pairParityEraserPairFlattenRev,
                pairParityEraserDescription, runConfig, stepConfig,
                lookupTransition, Matches, transition, Tape.read, Tape.write,
                Tape.move, Tape.moveLeft]
      rw [hstep]
      simpa [pairParityEraserPairFlattenRev, List.append_assoc] using
        ih d (none :: c :: right)

/-- Phase 3 entry: consume the separator and the last cell of the second
guarded field. -/
theorem pairParityEraser_run_enterErase
    (t u : Bool) (Q right : List (Option Bool)) :
    pairParityEraserDescription.runConfig 2
        { state := 2
          tape :=
            { left := some t :: some u :: Q
              head := none
              right := right } } =
      { state := 4
        tape :=
          { left := Q
            head := some u
            right := none :: none :: right } } := by
  cases t <;>
    simp [pairParityEraserDescription, runConfig, stepConfig,
      lookupTransition, Matches, transition, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft]

/-- Phase 3 loop: erase the rest of the second guarded field, then cross the
field separator. -/
theorem pairParityEraser_run_erase4
    (w : List Bool) (current : Bool) (e : Option Bool)
    (leftRest right : List (Option Bool)) :
    pairParityEraserDescription.runConfig (w.length + 2)
        { state := 4
          tape :=
            { left := w.map some ++ (none :: e :: leftRest)
              head := some current
              right := right } } =
      { state := 5
        tape :=
          { left := leftRest
            head := e
            right := List.replicate (w.length + 2) (none : Option Bool) ++
              right } } := by
  induction w generalizing current right with
  | nil =>
      cases current <;>
        simp [pairParityEraserDescription, runConfig, stepConfig,
          lookupTransition, Matches, transition, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft, List.replicate_succ]
  | cons u urest ih =>
      rw [show (u :: urest).length + 2 = 1 + (urest.length + 2) by
        simp
        lia]
      rw [runConfig_add]
      have hstep :
          pairParityEraserDescription.runConfig 1
              { state := 4
                tape :=
                  { left := (u :: urest).map some ++
                      (none :: e :: leftRest)
                    head := some current
                    right := right } } =
            { state := 4
              tape :=
                { left := urest.map some ++ (none :: e :: leftRest)
                  head := some u
                  right := none :: right } } := by
        cases current <;>
          simp [pairParityEraserDescription, runConfig, stepConfig,
            lookupTransition, Matches, transition, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
      rw [hstep]
      simpa [pairParityEraserReplicate_none_middle, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using ih u (none :: right)

/-- Phase 4 entry: erase the last cell of the first guarded field. -/
theorem pairParityEraser_run_gap
    (s v : Bool) (Q right : List (Option Bool)) :
    pairParityEraserDescription.runConfig 1
        { state := 5
          tape :=
            { left := some v :: Q
              head := some s
              right := right } } =
      { state := 6
        tape :=
          { left := Q
            head := some v
            right := none :: right } } := by
  cases s <;>
    simp [pairParityEraserDescription, runConfig, stepConfig,
      lookupTransition, Matches, transition, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft]

/-- Phase 4 loop: erase the rest of the first guarded field down to the left
boundary blank, then turn right. -/
theorem pairParityEraser_run_erase6
    (w : List Bool) (current : Bool) (right : List (Option Bool)) :
    pairParityEraserDescription.runConfig (w.length + 2)
        { state := 6
          tape :=
            { left := w.map some ++ [none]
              head := some current
              right := right } } =
      { state := 7
        tape :=
          { left := [none]
            head := none
            right := List.replicate w.length (none : Option Bool) ++
              right } } := by
  induction w generalizing current right with
  | nil =>
      cases current <;>
        simp [pairParityEraserDescription, runConfig, stepConfig,
          lookupTransition, Matches, transition, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons u urest ih =>
      rw [show (u :: urest).length + 2 = 1 + (urest.length + 2) by
        simp
        lia]
      rw [runConfig_add]
      have hstep :
          pairParityEraserDescription.runConfig 1
              { state := 6
                tape :=
                  { left := (u :: urest).map some ++ [none]
                    head := some current
                    right := right } } =
            { state := 6
              tape :=
                { left := urest.map some ++ [none]
                  head := some u
                  right := none :: right } } := by
        cases current <;>
          simp [pairParityEraserDescription, runConfig, stepConfig,
            lookupTransition, Matches, transition, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
      rw [hstep]
      simpa [pairParityEraserReplicate_none_middle, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using ih u (none :: right)

/-- Phase 5: skip rightward over an exact block of blanks. -/
theorem pairParityEraser_run_skip7
    (n : Nat) (left : List (Option Bool)) (r : Option Bool)
    (rs : List (Option Bool)) :
    pairParityEraserDescription.runConfig (n + 1)
        { state := 7
          tape :=
            { left := left
              head := none
              right := List.replicate n (none : Option Bool) ++
                (r :: rs) } } =
      { state := 7
        tape :=
          { left := List.replicate (n + 1) (none : Option Bool) ++ left
            head := r
            right := rs } } := by
  induction n generalizing left with
  | zero =>
      simp [pairParityEraserDescription, runConfig, stepConfig,
        lookupTransition, Matches, transition, Tape.read, Tape.write,
        Tape.move, Tape.moveRight, List.replicate_succ]
  | succ n ih =>
      rw [show n + 1 + 1 = 1 + (n + 1) by lia]
      rw [runConfig_add]
      have hstep :
          pairParityEraserDescription.runConfig 1
              { state := 7
                tape :=
                  { left := left
                    head := none
                    right := List.replicate (n + 1) (none : Option Bool) ++
                      (r :: rs) } } =
            { state := 7
              tape :=
                { left := none :: left
                  head := none
                  right := List.replicate n (none : Option Bool) ++
                    (r :: rs) } } := by
        simp [pairParityEraserDescription, runConfig, stepConfig,
          lookupTransition, Matches, transition, Tape.read, Tape.write,
          Tape.move, Tape.moveRight, List.replicate_succ]
      rw [hstep]
      simpa [pairParityEraserReplicate_none_middle, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using ih (none :: left)

/-- Phase 6: rightward return scan over footprint pairs.  Every pair starts
with a blank cell, so the scan state entering a pair may be {lit}`7` or
{lit}`8`; it leaves the pair in the state recording the pair value. -/
theorem pairParityEraser_run_ret
    (cells : List (Option Bool)) (h c : Option Bool)
    (left : List (Option Bool)) (r : Option Bool)
    (rs : List (Option Bool)) :
    pairParityEraserDescription.runConfig (2 * cells.length + 2)
        { state := pairParityEraserScanState h
          tape :=
            { left := left
              head := none
              right := (c :: pairParityEraserPairFlatten cells) ++
                (r :: rs) } } =
      { state :=
          pairParityEraserScanState (pairParityEraserLastCell cells c)
        tape :=
          { left :=
              (pairParityEraserPairFlatten (c :: cells)).reverse ++ left
            head := r
            right := rs } } := by
  induction cells generalizing h c left with
  | nil =>
      cases h with
      | none =>
          cases c with
          | none =>
              simp [pairParityEraserScanState, pairParityEraserLastCell,
                pairParityEraserPairFlatten, pairParityEraserDescription,
                runConfig, stepConfig, lookupTransition, Matches, transition,
                Tape.read, Tape.write, Tape.move, Tape.moveRight]
          | some bit =>
              cases bit <;>
                simp [pairParityEraserScanState, pairParityEraserLastCell,
                  pairParityEraserPairFlatten, pairParityEraserDescription,
                  runConfig, stepConfig, lookupTransition, Matches,
                  transition, Tape.read, Tape.write, Tape.move,
                  Tape.moveRight]
      | some hb =>
          cases c with
          | none =>
              simp [pairParityEraserScanState, pairParityEraserLastCell,
                pairParityEraserPairFlatten, pairParityEraserDescription,
                runConfig, stepConfig, lookupTransition, Matches, transition,
                Tape.read, Tape.write, Tape.move, Tape.moveRight]
          | some bit =>
              cases bit <;>
                simp [pairParityEraserScanState, pairParityEraserLastCell,
                  pairParityEraserPairFlatten, pairParityEraserDescription,
                  runConfig, stepConfig, lookupTransition, Matches,
                  transition, Tape.read, Tape.write, Tape.move,
                  Tape.moveRight]
  | cons d rest ih =>
      rw [show 2 * (d :: rest).length + 2 = 2 + (2 * rest.length + 2) by
        simp
        lia]
      rw [runConfig_add]
      have hstep :
          pairParityEraserDescription.runConfig 2
              { state := pairParityEraserScanState h
                tape :=
                  { left := left
                    head := none
                    right := (c ::
                        pairParityEraserPairFlatten (d :: rest)) ++
                      (r :: rs) } } =
            { state := pairParityEraserScanState c
              tape :=
                { left := c :: none :: left
                  head := none
                  right := (d :: pairParityEraserPairFlatten rest) ++
                    (r :: rs) } } := by
        cases h with
        | none =>
            cases c with
            | none =>
                simp [pairParityEraserScanState, pairParityEraserPairFlatten,
                  pairParityEraserDescription, runConfig, stepConfig,
                  lookupTransition, Matches, transition, Tape.read,
                  Tape.write, Tape.move, Tape.moveRight]
            | some bit =>
                cases bit <;>
                  simp [pairParityEraserScanState,
                    pairParityEraserPairFlatten, pairParityEraserDescription,
                    runConfig, stepConfig, lookupTransition, Matches,
                    transition, Tape.read, Tape.write, Tape.move,
                    Tape.moveRight]
        | some hb =>
            cases c with
            | none =>
                simp [pairParityEraserScanState, pairParityEraserPairFlatten,
                  pairParityEraserDescription, runConfig, stepConfig,
                  lookupTransition, Matches, transition, Tape.read,
                  Tape.write, Tape.move, Tape.moveRight]
            | some bit =>
                cases bit <;>
                  simp [pairParityEraserScanState,
                    pairParityEraserPairFlatten, pairParityEraserDescription,
                    runConfig, stepConfig, lookupTransition, Matches,
                    transition, Tape.read, Tape.write, Tape.move,
                    Tape.moveRight]
      rw [hstep]
      simpa [pairParityEraserPairFlatten, pairParityEraserLastCell,
        List.append_assoc] using ih c d (c :: none :: left)

/-- Phase 7: recognize the adjacent marker pair, erase it, and halt on the
blank right end. -/
theorem pairParityEraser_run_finish
    (left : List (Option Bool)) :
    pairParityEraserDescription.runConfig 3
        { state := 7
          tape :=
            { left := left
              head := some true
              right := [some true] } } =
      { state := 10
        tape :=
          { left := none :: left
            head := none
            right := [] } } := by
  simp [pairParityEraserDescription, runConfig, stepConfig,
    lookupTransition, Matches, transition, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft, Tape.moveRight]

/-- Phase 6 with the literal entry state.  The return scan is always entered
from the blank-skip state {lit}`7`. -/
theorem pairParityEraser_run_ret7
    (cells : List (Option Bool)) (c : Option Bool)
    (left : List (Option Bool)) (r : Option Bool)
    (rs : List (Option Bool)) :
    pairParityEraserDescription.runConfig (2 * cells.length + 2)
        { state := 7
          tape :=
            { left := left
              head := none
              right := (c :: pairParityEraserPairFlatten cells) ++
                (r :: rs) } } =
      { state :=
          pairParityEraserScanState (pairParityEraserLastCell cells c)
        tape :=
          { left :=
              (pairParityEraserPairFlatten (c :: cells)).reverse ++ left
            head := r
            right := rs } } :=
  pairParityEraser_run_ret cells none c left r rs

/-!
## Full run assembly
-/

/--
Complete halting run over the generic endpoint geometry.

The pair list argument is the footprint pair list after its leading guard
blank; it always ends with the payload boundary blank, which the second list
argument witnesses.  The four booleans and two words are the reversed bit
words of the two guarded fields, split into their first two cells.
-/
theorem pairParityEraser_run_full
    (J1 zs : List (Option Bool))
    (hJ1 : J1 = zs ++ [none])
    (t u s v : Bool) (w1 w0 : List Bool) :
    pairParityEraserDescription.HaltsFromTape
      { left := none ::
          ((pairParityEraserPairFlatten (none :: J1)).reverse ++
            (none :: (some t :: some u :: (w1.map some ++
              (none :: (some s :: some v :: (w0.map some ++ [none])))))))
        head := none
        right := [] }
      { left := none ::
          ((pairParityEraserPairFlatten (none :: J1)).reverse ++
            (List.replicate (w0.length + w1.length + 6)
              (none : Option Bool) ++ [none]))
        head := none
        right := [] } := by
  have hFR : (pairParityEraserPairFlatten (none :: J1)).reverse =
      none :: none ::
        pairParityEraserPairFlattenRev (zs.reverse ++ [none]) := by
    rw [pairParityEraserPairFlatten_reverse, hJ1]
    simp [pairParityEraserPairFlattenRev,
      pairParityEraserPairFlattenRev_append, List.reverse_append]
  have hF : pairParityEraserPairFlatten (none :: J1) =
      (pairParityEraserPairFlattenRev (zs.reverse ++ [none])).reverse ++
        [none, none] := by
    have h := congrArg List.reverse hFR
    simpa [List.reverse_reverse, List.reverse_cons, List.append_assoc]
      using h
  have hstep1 :
      (pairParityEraserPairFlattenRev (zs.reverse ++ [none])).reverse ++
          (none :: none :: [some true, some true]) =
        none :: ((none :: pairParityEraserPairFlatten J1) ++
          [some true, some true]) := by
    have h2 : (none : Option Bool) ::
        ((none :: pairParityEraserPairFlatten J1) ++
          [some true, some true]) =
        pairParityEraserPairFlatten (none :: J1) ++
          [some true, some true] := by
      simp [pairParityEraserPairFlatten]
    rw [h2, hF]
    simp [List.append_assoc]
  have hblanks :
      List.replicate w0.length (none : Option Bool) ++
          (none :: (List.replicate (w1.length + 2) (none : Option Bool) ++
            (none :: none ::
              ((pairParityEraserPairFlattenRev
                  (zs.reverse ++ [none])).reverse ++
                (none :: none :: [some true, some true]))))) =
        List.replicate (w0.length + w1.length + 5) (none : Option Bool) ++
          (none :: ((none :: pairParityEraserPairFlatten J1) ++
            [some true, some true])) := by
    rw [hstep1]
    rw [show ((none : Option Bool) :: none ::
        (none :: ((none :: pairParityEraserPairFlatten J1) ++
          [some true, some true]))) =
      List.replicate 2 (none : Option Bool) ++
        (none :: ((none :: pairParityEraserPairFlatten J1) ++
          [some true, some true])) from rfl]
    rw [pairParityEraserReplicate_none_append (w1.length + 2) 2]
    rw [pairParityEraserReplicate_none_cons (w1.length + 2 + 2)]
    rw [pairParityEraserReplicate_none_append w0.length
      (w1.length + 2 + 2 + 1)]
    rw [show w0.length + (w1.length + 2 + 2 + 1) =
      w0.length + w1.length + 5 by lia]
  have hlast : pairParityEraserLastCell J1 none = none := by
    rw [hJ1]
    exact pairParityEraserLastCell_append_none zs none
  have hrun : pairParityEraserDescription.runConfig
      (2 + ((2 * (zs.reverse ++ [none]).length + 2) + (2 +
        ((w1.length + 2) + (1 + ((w0.length + 2) +
          ((w0.length + w1.length + 5 + 1) +
            ((2 * J1.length + 2) + 3))))))))
      { state := 0
        tape :=
          { left := none :: none :: none ::
              (pairParityEraserPairFlattenRev (zs.reverse ++ [none]) ++
                (none :: (some t :: some u :: (w1.map some ++
                  (none :: (some s :: some v ::
                    (w0.map some ++ [none])))))))
            head := none
            right := [] } } =
    { state := 10
      tape :=
        { left := none ::
            ((pairParityEraserPairFlatten (none :: J1)).reverse ++
              (List.replicate (w0.length + w1.length + 6)
                (none : Option Bool) ++ [none]))
          head := none
          right := [] } } := by
    rw [runConfig_add, pairParityEraser_run_mark]
    rw [runConfig_add, pairParityEraser_run_scan]
    rw [runConfig_add, pairParityEraser_run_enterErase]
    rw [runConfig_add, pairParityEraser_run_erase4]
    rw [runConfig_add, pairParityEraser_run_gap]
    rw [runConfig_add, pairParityEraser_run_erase6]
    rw [hblanks]
    rw [runConfig_add, pairParityEraser_run_skip7]
    rw [runConfig_add, pairParityEraser_run_ret7]
    rw [hlast]
    rw [show pairParityEraserScanState none = 7 from rfl]
    rw [pairParityEraser_run_finish]
  have hsrc :
      ({ left := none ::
           ((pairParityEraserPairFlatten (none :: J1)).reverse ++
             (none :: (some t :: some u :: (w1.map some ++
               (none :: (some s :: some v :: (w0.map some ++ [none])))))))
         head := none
         right := [] } : Tape Bool) =
        { left := none :: none :: none ::
            (pairParityEraserPairFlattenRev (zs.reverse ++ [none]) ++
              (none :: (some t :: some u :: (w1.map some ++
                (none :: (some s :: some v :: (w0.map some ++ [none])))))))
          head := none
          right := [] } := by
    rw [hFR]
    simp only [List.cons_append]
  refine ⟨2 + ((2 * (zs.reverse ++ [none]).length + 2) + (2 +
    ((w1.length + 2) + (1 + ((w0.length + 2) +
      ((w0.length + w1.length + 5 + 1) +
        ((2 * J1.length + 2) + 3))))))), ?_, ?_⟩
  · rw [show pairParityEraserDescription.start = 0 from rfl, hsrc]
    exact congrArg Configuration.state hrun
  · rw [show pairParityEraserDescription.start = 0 from rfl, hsrc]
    exact congrArg Configuration.tape hrun

/-!
## Public specification
-/

/-- The pair-parity eraser satisfies the reusable guarded two-tape
structured-prefix eraser contract. -/
theorem pairParityEraserDescription_spec :
    GuardedTwoTapeStructuredPrefixEraserSpec pairParityEraserDescription := by
  refine ⟨pairParityEraserDescription_subroutineReady, ?_⟩
  intro T0 T1 bits padding
  obtain ⟨t, u, w1, hw1⟩ :=
    pairParityEraserExists_two_cons
      (logicalTapeBits (guardLogicalTape T1)).reverse
      (by
        rw [List.length_reverse]
        exact pairParityEraserGuardedBits_two_le T1)
  obtain ⟨s, v, w0, hw0⟩ :=
    pairParityEraserExists_two_cons
      (logicalTapeBits (guardLogicalTape T0)).reverse
      (by
        rw [List.length_reverse]
        exact pairParityEraserGuardedBits_two_le T0)
  have hJ1 : (none :: none ::
      selectedSegmentLogicalTapeDecoderPayloadCells bits padding :
        List (Option Bool)) =
      (none :: none :: (bits.map some ++ (none :: padding))) ++ [none] := by
    simp [selectedSegmentLogicalTapeDecoderPayloadCells, List.append_assoc]
  have hrun :=
    pairParityEraser_run_full
      (none :: none ::
        selectedSegmentLogicalTapeDecoderPayloadCells bits padding)
      (none :: none :: (bits.map some ++ (none :: padding)))
      hJ1 t u s v w1 w0
  have hsource :
      guardedTwoTapeStructuredPrefixEraserSourceTape T0 T1 bits padding =
        { left := none ::
            ((pairParityEraserPairFlatten (none :: none :: none ::
                selectedSegmentLogicalTapeDecoderPayloadCells
                  bits padding)).reverse ++
              (none :: (some t :: some u :: (w1.map some ++
                (none :: (some s :: some v :: (w0.map some ++ [none])))))))
          head := none
          right := [] } := by
    rw [pairParityEraserSourceTape_shape]
    rw [pairParityEraserFootprint_eq_pairFlatten]
    rw [pairParityEraserPrefixCells_reverse]
    rw [hw1, hw0]
    simp only [List.map_cons, List.cons_append]
  rw [hsource]
  refine ⟨_, hrun, ?_⟩
  rw [pairParityEraserTargetTape_shape]
  rw [pairParityEraserFootprint_eq_pairFlatten]
  refine ⟨?_, rfl, rfl⟩
  show Tape.dropTrailingNone (none ::
      ((pairParityEraserPairFlatten (none :: none :: none ::
          selectedSegmentLogicalTapeDecoderPayloadCells
            bits padding)).reverse ++
        (List.replicate (w0.length + w1.length + 6)
          (none : Option Bool) ++ [none]))) =
    Tape.dropTrailingNone (none ::
      ((pairParityEraserPairFlatten (none :: none :: none ::
          selectedSegmentLogicalTapeDecoderPayloadCells
            bits padding)).reverse ++ [none]))
  rw [pairParityEraserReplicate_none_middle (w0.length + w1.length + 6)
    ([] : List (Option Bool))]
  simp only [List.append_nil]
  rw [pairParityEraserDropTrailingNone_cons_blanks]
  rw [show ([none] : List (Option Bool)) =
    List.replicate 1 (none : Option Bool) from rfl]
  rw [pairParityEraserDropTrailingNone_cons_blanks]

/-- Split pad-symbol case form of the eraser contract, as consumed by the
frontier construction leaf. -/
theorem pairParityEraserDescription_splitPadSymbolCaseSpec :
    GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec
      pairParityEraserDescription :=
  guardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec_of_spec
    pairParityEraserDescription_spec

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
