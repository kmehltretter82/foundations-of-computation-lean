import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Basic
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Structured

set_option doc.verso true

/-!
# Structured multi-tape lowering layout

This module starts the multi-logical-tape lowering path for
{module}`FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Structured`.
It intentionally stops at the physical encoding and invariant layer.  Later
modules can add primitive seek/update routines and simulation theorems without
changing the contract vocabulary introduced here.

The target is still the ordinary one-tape
{name (full := FoC.Computability.MachineDescription)}`MachineDescription`
model.  Structured
{name (full := FoC.Computability.CommonGround.FiniteTransducers.Structured.HeadMove.stay)}`HeadMove.stay`
is represented by leaving the encoded logical head marker on the same physical
logical cell; the physical one-tape machine may still move while performing
that simulation.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

/-!
## Physical cell encoding
-/

/--
Two physical Boolean cells encode one logical tape cell.

The physical blank cell is deliberately not used inside a logical cell code:
blank physical cells are reserved for separators between encoded logical tape
segments.
-/
def logicalCellCode : Option Bool -> List (Option Bool)
  | none => [some false, some false]
  | some false => [some false, some true]
  | some true => [some true, some false]

/-- Marker immediately before the encoded logical head cell. -/
def headMarkerCells : List (Option Bool) :=
  [some true, some true]

/-- Physical blank separator between logical tape segments. -/
def tapeSeparatorCells : List (Option Bool) :=
  [none]

/-- Encode a finite list of logical cells. -/
def logicalCellListCode : List (Option Bool) -> List (Option Bool)
  | [] => []
  | cell :: rest =>
      List.append (logicalCellCode cell) (logicalCellListCode rest)

/--
Encode one logical tape segment.

The segment is written in logical left-to-right order:
the reversed left stack, then a head marker, then the head cell, then the right
stack.  Segment separators are added by
{lit}`encodedStructuredTapeCells`, not by this definition.
-/
def logicalTapeCode (T : Tape Bool) : List (Option Bool) :=
  List.append (logicalCellListCode T.left.reverse)
    (List.append headMarkerCells
      (List.append (logicalCellCode T.head)
        (logicalCellListCode T.right)))

/--
Encode a list of logical tapes with a separator before every tape and one final
separator after the last tape.

The canonical physical head starts on the first separator.
-/
def encodedStructuredTapeCells :
    List (Tape Bool) -> List (Option Bool)
  | [] => tapeSeparatorCells
  | T :: rest =>
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode T)
          (encodedStructuredTapeCells rest))

/--
Canonical one-tape representation of the logical tape list.  The physical head
is on the left boundary separator of the encoded multi-tape block.
-/
def encodedStructuredTapes
    (logical : List (Tape Bool)) : Tape Bool :=
  tapeAtCells [] (encodedStructuredTapeCells logical)

@[simp] theorem logicalCellCode_none :
    logicalCellCode (none : Option Bool) = [some false, some false] := by
  rfl

@[simp] theorem logicalCellCode_some_false :
    logicalCellCode (some false) = [some false, some true] := by
  rfl

@[simp] theorem logicalCellCode_some_true :
    logicalCellCode (some true) = [some true, some false] := by
  rfl

@[simp] theorem logicalCellCode_length
    (cell : Option Bool) :
    (logicalCellCode cell).length = 2 := by
  cases cell with
  | none => rfl
  | some bit =>
      cases bit <;> rfl

@[simp] theorem logicalCellListCode_nil :
    logicalCellListCode [] = [] := by
  rfl

@[simp] theorem logicalCellListCode_cons
    (cell : Option Bool) (rest : List (Option Bool)) :
    logicalCellListCode (cell :: rest) =
      List.append (logicalCellCode cell) (logicalCellListCode rest) := by
  rfl

@[simp] theorem logicalCellListCode_append
    (left right : List (Option Bool)) :
    logicalCellListCode (left ++ right) =
      List.append (logicalCellListCode left)
        (logicalCellListCode right) := by
  induction left with
  | nil =>
      rfl
  | cons cell rest ih =>
      simp [logicalCellListCode, ih, List.append_assoc]

@[simp] theorem encodedStructuredTapeCells_nil :
    encodedStructuredTapeCells [] = tapeSeparatorCells := by
  rfl

@[simp] theorem encodedStructuredTapeCells_cons
    (T : Tape Bool) (rest : List (Tape Bool)) :
    encodedStructuredTapeCells (T :: rest) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode T)
          (encodedStructuredTapeCells rest)) := by
  rfl

@[simp] theorem encodedStructuredTapes_read
    (logical : List (Tape Bool)) :
    Tape.read (encodedStructuredTapes logical) = none := by
  cases logical with
  | nil => rfl
  | cons T rest => rfl

/-!
## Codec and guard facts
-/

/--
Token view of the physical encoding.  This is used for codec reasoning before
primitive machines start scanning raw physical cells.
-/
inductive PhysicalToken where
  | separator : PhysicalToken
  | headMarker : PhysicalToken
  | logicalCell (cell : Option Bool) : PhysicalToken
deriving Repr, DecidableEq

namespace PhysicalToken

def code : PhysicalToken -> List (Option Bool)
  | separator => tapeSeparatorCells
  | headMarker => headMarkerCells
  | logicalCell cell => logicalCellCode cell

@[simp] theorem code_separator :
    code separator = tapeSeparatorCells := by
  rfl

@[simp] theorem code_headMarker :
    code headMarker = headMarkerCells := by
  rfl

@[simp] theorem code_cell (cell : Option Bool) :
    code (logicalCell cell) = logicalCellCode cell := by
  rfl

end PhysicalToken

def physicalTokenListCode :
    List PhysicalToken -> List (Option Bool)
  | [] => []
  | token :: rest =>
      List.append token.code (physicalTokenListCode rest)

def logicalCellListTokens
    (cells : List (Option Bool)) : List PhysicalToken :=
  cells.map PhysicalToken.logicalCell

def logicalTapeTokens (T : Tape Bool) : List PhysicalToken :=
  List.append (logicalCellListTokens T.left.reverse)
    (PhysicalToken.headMarker ::
      PhysicalToken.logicalCell T.head ::
        logicalCellListTokens T.right)

def encodedStructuredTapeTokens :
    List (Tape Bool) -> List PhysicalToken
  | [] => [PhysicalToken.separator]
  | T :: rest =>
      PhysicalToken.separator ::
        List.append (logicalTapeTokens T)
          (encodedStructuredTapeTokens rest)

@[simp] theorem physicalTokenListCode_nil :
    physicalTokenListCode [] = [] := by
  rfl

@[simp] theorem physicalTokenListCode_cons
    (token : PhysicalToken) (rest : List PhysicalToken) :
    physicalTokenListCode (token :: rest) =
      List.append token.code (physicalTokenListCode rest) := by
  rfl

@[simp] theorem physicalTokenListCode_append
    (xs ys : List PhysicalToken) :
    physicalTokenListCode (List.append xs ys) =
      List.append (physicalTokenListCode xs)
        (physicalTokenListCode ys) := by
  induction xs with
  | nil =>
      rfl
  | cons token rest ih =>
      change
        List.append token.code
            (physicalTokenListCode (List.append rest ys)) =
          List.append
            (List.append token.code (physicalTokenListCode rest))
            (physicalTokenListCode ys)
      rw [ih]
      exact (List.append_assoc token.code
        (physicalTokenListCode rest) (physicalTokenListCode ys)).symm

@[simp] theorem physicalTokenListCode_logicalCellListTokens
    (cells : List (Option Bool)) :
    physicalTokenListCode (logicalCellListTokens cells) =
      logicalCellListCode cells := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      change
        List.append (logicalCellCode cell)
            (physicalTokenListCode (logicalCellListTokens rest)) =
          List.append (logicalCellCode cell)
            (logicalCellListCode rest)
      rw [ih]

@[simp] theorem physicalTokenListCode_logicalTapeTokens
    (T : Tape Bool) :
    physicalTokenListCode (logicalTapeTokens T) =
      logicalTapeCode T := by
  change
    physicalTokenListCode
        (List.append (logicalCellListTokens T.left.reverse)
          (PhysicalToken.headMarker ::
            PhysicalToken.logicalCell T.head ::
              logicalCellListTokens T.right)) =
      List.append (logicalCellListCode T.left.reverse)
        (List.append headMarkerCells
          (List.append (logicalCellCode T.head)
            (logicalCellListCode T.right)))
  calc
    physicalTokenListCode
        (List.append (logicalCellListTokens T.left.reverse)
          (PhysicalToken.headMarker ::
            PhysicalToken.logicalCell T.head ::
              logicalCellListTokens T.right))
        = List.append
            (physicalTokenListCode
              (logicalCellListTokens T.left.reverse))
            (physicalTokenListCode
              (PhysicalToken.headMarker ::
                PhysicalToken.logicalCell T.head ::
                  logicalCellListTokens T.right)) :=
          physicalTokenListCode_append
            (logicalCellListTokens T.left.reverse)
            (PhysicalToken.headMarker ::
              PhysicalToken.logicalCell T.head ::
                logicalCellListTokens T.right)
    _ = List.append (logicalCellListCode T.left.reverse)
        (List.append headMarkerCells
          (List.append (logicalCellCode T.head)
            (logicalCellListCode T.right))) := by
      simp [physicalTokenListCode,
        physicalTokenListCode_logicalCellListTokens]

@[simp] theorem physicalTokenListCode_encodedStructuredTapeTokens
    (logical : List (Tape Bool)) :
    physicalTokenListCode (encodedStructuredTapeTokens logical) =
      encodedStructuredTapeCells logical := by
  induction logical with
  | nil =>
      rfl
  | cons T rest ih =>
      change
        List.append tapeSeparatorCells
          (physicalTokenListCode
            (List.append (logicalTapeTokens T)
              (encodedStructuredTapeTokens rest))) =
        List.append tapeSeparatorCells
          (List.append (logicalTapeCode T)
            (encodedStructuredTapeCells rest))
      congr 1
      calc
        physicalTokenListCode
            (List.append (logicalTapeTokens T)
              (encodedStructuredTapeTokens rest))
            = List.append
                (physicalTokenListCode (logicalTapeTokens T))
                (physicalTokenListCode
                  (encodedStructuredTapeTokens rest)) :=
              physicalTokenListCode_append (logicalTapeTokens T)
                (encodedStructuredTapeTokens rest)
        _ = List.append (logicalTapeCode T)
            (encodedStructuredTapeCells rest) := by
          rw [physicalTokenListCode_logicalTapeTokens, ih]

theorem logicalCellCode_injective :
    Function.Injective logicalCellCode := by
  intro a b h
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some bit =>
          cases bit <;> simp [logicalCellCode] at h
  | some abit =>
      cases abit <;>
        cases b with
        | none =>
            simp [logicalCellCode] at h
        | some bbit =>
            cases bbit <;> simp [logicalCellCode] at h <;> rfl

theorem logicalCellCode_ne_headMarkerCells
    (cell : Option Bool) :
    logicalCellCode cell ≠ headMarkerCells := by
  cases cell with
  | none =>
      simp [logicalCellCode, headMarkerCells]
  | some bit =>
      cases bit <;> simp [logicalCellCode, headMarkerCells]

theorem headMarkerCells_ne_logicalCellCode
    (cell : Option Bool) :
    headMarkerCells ≠ logicalCellCode cell := by
  exact (logicalCellCode_ne_headMarkerCells cell).symm

theorem logicalCellCode_ne_tapeSeparatorCells
    (cell : Option Bool) :
    logicalCellCode cell ≠ tapeSeparatorCells := by
  cases cell with
  | none =>
      simp [logicalCellCode, tapeSeparatorCells]
  | some bit =>
      cases bit <;> simp [logicalCellCode, tapeSeparatorCells]

theorem tapeSeparatorCells_ne_logicalCellCode
    (cell : Option Bool) :
    tapeSeparatorCells ≠ logicalCellCode cell := by
  exact (logicalCellCode_ne_tapeSeparatorCells cell).symm

theorem headMarkerCells_ne_tapeSeparatorCells :
    headMarkerCells ≠ tapeSeparatorCells := by
  simp [headMarkerCells, tapeSeparatorCells]

theorem tapeSeparatorCells_ne_headMarkerCells :
    tapeSeparatorCells ≠ headMarkerCells := by
  exact headMarkerCells_ne_tapeSeparatorCells.symm

@[simp] theorem headMarkerCells_length :
    headMarkerCells.length = 2 := by
  rfl

@[simp] theorem tapeSeparatorCells_length :
    tapeSeparatorCells.length = 1 := by
  rfl

@[simp] theorem logicalCellListCode_length
    (cells : List (Option Bool)) :
    (logicalCellListCode cells).length = 2 * cells.length := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      simp [logicalCellListCode, ih, Nat.mul_add, Nat.add_comm]

theorem encodedStructuredTapeCells_startsWith_separator
    (logical : List (Tape Bool)) :
    exists rest : List (Option Bool),
      encodedStructuredTapeCells logical =
        List.append tapeSeparatorCells rest := by
  cases logical with
  | nil =>
      exact ⟨[], rfl⟩
  | cons T rest =>
      exact ⟨List.append (logicalTapeCode T)
        (encodedStructuredTapeCells rest), rfl⟩

/--
The canonical token view of one logical tape has one distinguished head-marker
token between the encoded left context and the head cell.
-/
theorem logicalTapeTokens_headMarker_split
    (T : Tape Bool) :
    logicalTapeTokens T =
      List.append (logicalCellListTokens T.left.reverse)
        [PhysicalToken.headMarker] ++
        (PhysicalToken.logicalCell T.head ::
          logicalCellListTokens T.right) := by
  simp [logicalTapeTokens, List.append_assoc]

/-- Raw Boolean payload for one encoded logical cell. -/
def logicalCellBits : Option Bool -> Word Bool
  | none => [false, false]
  | some false => [false, true]
  | some true => [true, false]

/-- Raw Boolean payload for a list of encoded logical cells. -/
def logicalCellListBits :
    List (Option Bool) -> Word Bool
  | [] => []
  | cell :: rest =>
      List.append (logicalCellBits cell)
        (logicalCellListBits rest)

@[simp] theorem logicalCellListBits_append
    (left right : List (Option Bool)) :
    logicalCellListBits (left ++ right) =
      List.append (logicalCellListBits left)
        (logicalCellListBits right) := by
  induction left with
  | nil =>
      rfl
  | cons cell rest ih =>
      simp [logicalCellListBits, ih, List.append_assoc]

/-- Raw Boolean payload for one encoded logical tape segment. -/
def logicalTapeBits (T : Tape Bool) : Word Bool :=
  List.append (logicalCellListBits T.left.reverse)
    (List.append [true, true]
      (List.append (logicalCellBits T.head)
        (logicalCellListBits T.right)))

@[simp] theorem logicalCellCode_eq_map_some
    (cell : Option Bool) :
    logicalCellCode cell = (logicalCellBits cell).map some := by
  cases cell with
  | none => rfl
  | some bit =>
      cases bit <;> rfl

@[simp] theorem logicalCellListCode_eq_map_some
    (cells : List (Option Bool)) :
    logicalCellListCode cells =
      (logicalCellListBits cells).map some := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      simp [logicalCellListCode, logicalCellListBits, ih,
        List.map_append]

theorem logicalTapeCode_eq_map_some
    (T : Tape Bool) :
    logicalTapeCode T = (logicalTapeBits T).map some := by
  simp [logicalTapeCode, logicalTapeBits, headMarkerCells]

theorem logicalTapeBits_exists_cons
    (T : Tape Bool) :
    exists bit : Bool, exists rest : Word Bool,
      logicalTapeBits T = bit :: rest := by
  unfold logicalTapeBits
  cases hleft : logicalCellListBits T.left.reverse with
  | nil =>
      exists true
      exists true ::
        List.append (logicalCellBits T.head)
          (logicalCellListBits T.right)
  | cons bit bits =>
      exists bit
      exists List.append bits
        (List.append [true, true]
          (List.append (logicalCellBits T.head)
            (logicalCellListBits T.right)))

theorem logicalCellBits_exists_cons
    (cell : Option Bool) :
    exists bit : Bool, exists rest : Word Bool,
      logicalCellBits cell = bit :: rest := by
  cases cell with
  | none =>
      exact ⟨false, [false], rfl⟩
  | some bit =>
      cases bit
      · exact ⟨false, [true], rfl⟩
      · exact ⟨true, [false], rfl⟩

/--
Left guard condition for a logical tape.  It records that moving the logical
head left can consume an already represented cell rather than forcing a
physical segment expansion.
-/
def LogicalTapeHasLeftGuard (T : Tape Bool) : Prop :=
  T.left ≠ []

/--
Right guard condition for a logical tape.  It records that moving the logical
head right can consume an already represented cell rather than forcing a
physical segment expansion.
-/
def LogicalTapeHasRightGuard (T : Tape Bool) : Prop :=
  T.right ≠ []

def LogicalTapeHasGuardCells (T : Tape Bool) : Prop :=
  LogicalTapeHasLeftGuard T ∧ LogicalTapeHasRightGuard T

theorem tapeAction_apply_preserves_left_guard_of_stay
    (action : TapeAction) (T : Tape Bool)
    (hmove : action.move = HeadMove.stay)
    (hguard : LogicalTapeHasLeftGuard T) :
    LogicalTapeHasLeftGuard (action.apply T) := by
  cases action with
  | mk write? move =>
      cases hmove
      cases write? <;> exact hguard

theorem tapeAction_apply_preserves_right_guard_of_stay
    (action : TapeAction) (T : Tape Bool)
    (hmove : action.move = HeadMove.stay)
    (hguard : LogicalTapeHasRightGuard T) :
    LogicalTapeHasRightGuard (action.apply T) := by
  cases action with
  | mk write? move =>
      cases hmove
      cases write? <;> exact hguard

theorem tapeAction_apply_preserves_guards_of_stay
    (action : TapeAction) (T : Tape Bool)
    (hmove : action.move = HeadMove.stay)
    (hguard : LogicalTapeHasGuardCells T) :
    LogicalTapeHasGuardCells (action.apply T) := by
  exact
    ⟨tapeAction_apply_preserves_left_guard_of_stay
        action T hmove hguard.left,
      tapeAction_apply_preserves_right_guard_of_stay
        action T hmove hguard.right⟩

/-!
## Cursor and phase invariants
-/

/-- Encoded cells for complete tape segments, without the final separator. -/
def encodedStructuredTapeCellsPrefix :
    List (Tape Bool) -> List (Option Bool)
  | [] => []
  | T :: rest =>
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode T)
          (encodedStructuredTapeCellsPrefix rest))

@[simp] theorem encodedStructuredTapeCellsPrefix_nil :
    encodedStructuredTapeCellsPrefix [] = [] := by
  rfl

@[simp] theorem encodedStructuredTapeCellsPrefix_cons
    (T : Tape Bool) (rest : List (Tape Bool)) :
    encodedStructuredTapeCellsPrefix (T :: rest) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode T)
          (encodedStructuredTapeCellsPrefix rest)) := by
  rfl

theorem encodedStructuredTapeCells_eq_prefix_append_separator
    (logical : List (Tape Bool)) :
    encodedStructuredTapeCells logical =
      List.append (encodedStructuredTapeCellsPrefix logical)
        tapeSeparatorCells := by
  induction logical with
  | nil =>
      rfl
  | cons T rest ih =>
      simp [encodedStructuredTapeCells,
        encodedStructuredTapeCellsPrefix, ih, List.append_assoc]

@[simp] theorem encodedStructuredTapeCellsPrefix_append
    (left right : List (Tape Bool)) :
    encodedStructuredTapeCellsPrefix (left ++ right) =
      List.append (encodedStructuredTapeCellsPrefix left)
        (encodedStructuredTapeCellsPrefix right) := by
  induction left with
  | nil =>
      rfl
  | cons T rest ih =>
      simp [encodedStructuredTapeCellsPrefix, ih, List.append_assoc]

theorem encodedStructuredTapeCellsPrefix_append_singleton
    (left : List (Tape Bool)) (T : Tape Bool) :
    encodedStructuredTapeCellsPrefix (left ++ [T]) =
      List.append
        (List.append (encodedStructuredTapeCellsPrefix left)
          tapeSeparatorCells)
        (logicalTapeCode T) := by
  simp [encodedStructuredTapeCellsPrefix, List.append_assoc]

def tapeAtEncodedSplit
    (left right : List (Option Bool)) : Tape Bool :=
  tapeAtCells left.reverse right

def encodedPrefixBeforeTape
    (logical : List (Tape Bool)) (tapeIndex : Nat) :
    List (Option Bool) :=
  encodedStructuredTapeCellsPrefix (logical.take tapeIndex)

def encodedSuffixFromTape
    (logical : List (Tape Bool)) (tapeIndex : Nat) :
    List (Option Bool) :=
  encodedStructuredTapeCells (logical.drop tapeIndex)

def AtTapeSeparator
    (logical : List (Tape Bool)) (tapeIndex : Nat)
    (physical : Tape Bool) : Prop :=
  tapeIndex ≤ logical.length ∧
    physical =
      tapeAtEncodedSplit
        (encodedPrefixBeforeTape logical tapeIndex)
        (encodedSuffixFromTape logical tapeIndex)

def AtEncodedBlockStart
    (logical : List (Tape Bool)) (physical : Tape Bool) : Prop :=
  AtTapeSeparator logical 0 physical

def AtTapeHeadMarker
    (logical : List (Tape Bool)) (tapeIndex : Nat)
    (physical : Tape Bool) : Prop :=
  exists T : Tape Bool, exists rest : List (Tape Bool),
    logical.drop tapeIndex = T :: rest ∧
      physical =
        tapeAtEncodedSplit
          (List.append
            (encodedPrefixBeforeTape logical tapeIndex)
            (List.append tapeSeparatorCells
              (logicalCellListCode T.left.reverse)))
          (List.append headMarkerCells
            (List.append (logicalCellCode T.head)
              (List.append (logicalCellListCode T.right)
                (encodedStructuredTapeCells rest))))

def AtTapeHeadCellCode
    (logical : List (Tape Bool)) (tapeIndex : Nat)
    (physical : Tape Bool) : Prop :=
  exists T : Tape Bool, exists rest : List (Tape Bool),
    logical.drop tapeIndex = T :: rest ∧
      physical =
        tapeAtEncodedSplit
          (List.append
            (encodedPrefixBeforeTape logical tapeIndex)
            (List.append tapeSeparatorCells
              (List.append (logicalCellListCode T.left.reverse)
                headMarkerCells)))
          (List.append (logicalCellCode T.head)
            (List.append (logicalCellListCode T.right)
              (encodedStructuredTapeCells rest)))

def AtTapeSegmentEnd
    (logical : List (Tape Bool)) (tapeIndex : Nat)
    (physical : Tape Bool) : Prop :=
  exists T : Tape Bool, exists rest : List (Tape Bool),
    logical.drop tapeIndex = T :: rest ∧
      physical =
        tapeAtEncodedSplit
          (List.append
            (encodedPrefixBeforeTape logical tapeIndex)
            (List.append tapeSeparatorCells
              (logicalTapeCode T)))
          (encodedStructuredTapeCells rest)

theorem atEncodedBlockStart_self
    (logical : List (Tape Bool)) :
    AtEncodedBlockStart logical
      (encodedStructuredTapes logical) := by
  exact ⟨Nat.zero_le logical.length, rfl⟩

theorem atTapeSeparator_zero_self
    (logical : List (Tape Bool)) :
    AtTapeSeparator logical 0
      (encodedStructuredTapes logical) := by
  exact atEncodedBlockStart_self logical

/-!
## Layout invariants
-/

/--
Exact representation invariant for logical tapes encoded on one physical tape.

This is intentionally an equality wrapper rather than a parser.  Primitive
lowering routines can later replace goals about the physical tape with this
single invariant and then unfold the concrete layout only locally.
-/
def StructuredEncodedTapes
    (logical : List (Tape Bool)) (physical : Tape Bool) : Prop :=
  physical = encodedStructuredTapes logical

/--
Exact representation invariant for a structured configuration.

The finite-control state remains the structured state at this layer.  A later
lowered one-tape machine may map structured states to larger physical control
states; {lit}`StructuredEncodedPhysicalConfig` below factors that mapping out.
-/
def StructuredEncodedConfig
    (D : Description) (c : Configuration)
    (physical : Tape Bool) : Prop :=
  c.state < D.stateCount ∧
    c.tapes.length = D.tapeCount ∧
    StructuredEncodedTapes c.tapes physical

/--
Representation invariant for an ordinary one-tape machine configuration whose
finite-control state is supplied by a caller-provided state map.
-/
def StructuredEncodedPhysicalConfig
    (stateMap : Nat -> Nat) (D : Description)
    (c : Configuration)
    (physical : MachineDescription.Configuration) : Prop :=
  physical.state = stateMap c.state ∧
    StructuredEncodedConfig D c physical.tape

theorem structuredEncodedTapes_self
    (logical : List (Tape Bool)) :
    StructuredEncodedTapes logical
      (encodedStructuredTapes logical) := by
  rfl

theorem structuredEncodedConfig_self
    (D : Description) (c : Configuration)
    (hstate : c.state < D.stateCount)
    (htapes : c.tapes.length = D.tapeCount) :
    StructuredEncodedConfig D c
      (encodedStructuredTapes c.tapes) := by
  exact ⟨hstate, htapes, structuredEncodedTapes_self c.tapes⟩

theorem structuredEncodedConfig_tape_eq
    {D : Description} {c : Configuration} {physical : Tape Bool}
    (h : StructuredEncodedConfig D c physical) :
    physical = encodedStructuredTapes c.tapes :=
  h.right.right

theorem structuredEncodedConfig_tapes_length
    {D : Description} {c : Configuration} {physical : Tape Bool}
    (h : StructuredEncodedConfig D c physical) :
    c.tapes.length = D.tapeCount :=
  h.right.left

theorem structuredEncodedConfig_state_lt
    {D : Description} {c : Configuration} {physical : Tape Bool}
    (h : StructuredEncodedConfig D c physical) :
    c.state < D.stateCount :=
  h.left

theorem structuredEncodedPhysicalConfig_self
    (stateMap : Nat -> Nat) (D : Description)
    (c : Configuration)
    (hstate : c.state < D.stateCount)
    (htapes : c.tapes.length = D.tapeCount) :
    StructuredEncodedPhysicalConfig stateMap D c
      { state := stateMap c.state
        tape := encodedStructuredTapes c.tapes } := by
  exact
    ⟨rfl, structuredEncodedConfig_self D c hstate htapes⟩

theorem structuredEncodedPhysicalConfig_state_eq
    {stateMap : Nat -> Nat} {D : Description}
    {c : Configuration}
    {physical : MachineDescription.Configuration}
    (h : StructuredEncodedPhysicalConfig stateMap D c physical) :
    physical.state = stateMap c.state :=
  h.left

theorem structuredEncodedPhysicalConfig_tape_eq
    {stateMap : Nat -> Nat} {D : Description}
    {c : Configuration}
    {physical : MachineDescription.Configuration}
    (h : StructuredEncodedPhysicalConfig stateMap D c physical) :
    physical.tape = encodedStructuredTapes c.tapes :=
  structuredEncodedConfig_tape_eq h.right

/-!
## Three-tape wrapper
-/

def structured3Config
    (state : Nat) (T U V : Tape Bool) : Configuration where
  state := state
  tapes := [T, U, V]

def encodedStructured3Tapes
    (T U V : Tape Bool) : Tape Bool :=
  encodedStructuredTapes [T, U, V]

def StructuredEncoded3Tapes
    (T U V : Tape Bool) (physical : Tape Bool) : Prop :=
  StructuredEncodedTapes [T, U, V] physical

def StructuredEncoded3Config
    (D : Description) (state : Nat)
    (T U V : Tape Bool) (physical : Tape Bool) : Prop :=
  StructuredEncodedConfig D (structured3Config state T U V)
    physical

def StructuredEncoded3PhysicalConfig
    (stateMap : Nat -> Nat) (D : Description) (state : Nat)
    (T U V : Tape Bool)
    (physical : MachineDescription.Configuration) : Prop :=
  StructuredEncodedPhysicalConfig stateMap D
    (structured3Config state T U V) physical

@[simp] theorem structured3Config_state
    (state : Nat) (T U V : Tape Bool) :
    (structured3Config state T U V).state = state := by
  rfl

@[simp] theorem structured3Config_tapes
    (state : Nat) (T U V : Tape Bool) :
    (structured3Config state T U V).tapes = [T, U, V] := by
  rfl

@[simp] theorem encodedStructured3Tapes_read
    (T U V : Tape Bool) :
    Tape.read (encodedStructured3Tapes T U V) = none := by
  rfl

theorem structuredEncoded3Tapes_self
    (T U V : Tape Bool) :
    StructuredEncoded3Tapes T U V
      (encodedStructured3Tapes T U V) := by
  exact structuredEncodedTapes_self [T, U, V]

theorem structuredEncoded3Config_self
    (D : Description) (state : Nat) (T U V : Tape Bool)
    (hstate : state < D.stateCount)
    (htapes : D.tapeCount = 3) :
    StructuredEncoded3Config D state T U V
      (encodedStructured3Tapes T U V) := by
  refine structuredEncodedConfig_self D
    (structured3Config state T U V) hstate ?_
  simpa [structured3Config] using htapes.symm

theorem structuredEncoded3Config_tapeCount
    {D : Description} {state : Nat} {T U V : Tape Bool}
    {physical : Tape Bool}
    (h : StructuredEncoded3Config D state T U V physical) :
    D.tapeCount = 3 := by
  have htapes := structuredEncodedConfig_tapes_length h
  simpa [structured3Config] using htapes.symm

theorem structuredEncoded3PhysicalConfig_self
    (stateMap : Nat -> Nat) (D : Description)
    (state : Nat) (T U V : Tape Bool)
    (hstate : state < D.stateCount)
    (htapes : D.tapeCount = 3) :
    StructuredEncoded3PhysicalConfig stateMap D state T U V
      { state := stateMap state
        tape := encodedStructured3Tapes T U V } := by
  refine structuredEncodedPhysicalConfig_self stateMap D
    (structured3Config state T U V) hstate ?_
  simpa [structured3Config] using htapes.symm

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
