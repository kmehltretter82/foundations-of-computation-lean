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

/-!
## Primitive physical routines
-/

/--
Replace the logical tape at an index, leaving out-of-range indices unchanged.

The primitive contracts below use this pure operation to state the logical
effect that a physical one-tape routine must realize on the encoded layout.
-/
def replaceTapeAt
    (index : Nat) (replacement : Tape Bool) :
    List (Tape Bool) -> List (Tape Bool)
  | [] => []
  | T :: rest =>
      match index with
      | 0 => replacement :: rest
      | index + 1 => T :: replaceTapeAt index replacement rest

@[simp] theorem replaceTapeAt_nil
    (index : Nat) (replacement : Tape Bool) :
    replaceTapeAt index replacement [] = [] := by
  cases index <;> rfl

@[simp] theorem replaceTapeAt_zero_cons
    (replacement T : Tape Bool) (rest : List (Tape Bool)) :
    replaceTapeAt 0 replacement (T :: rest) = replacement :: rest := by
  rfl

@[simp] theorem replaceTapeAt_succ_cons
    (index : Nat) (replacement T : Tape Bool)
    (rest : List (Tape Bool)) :
    replaceTapeAt (index + 1) replacement (T :: rest) =
      T :: replaceTapeAt index replacement rest := by
  rfl

@[simp] theorem replaceTapeAt_length
    (index : Nat) (replacement : Tape Bool)
    (logical : List (Tape Bool)) :
    (replaceTapeAt index replacement logical).length = logical.length := by
  induction index generalizing logical with
  | zero =>
      cases logical <;> rfl
  | succ index ih =>
      cases logical with
      | nil => rfl
      | cons T rest =>
          simp [replaceTapeAt, ih]

/--
One logical primitive that a physical one-tape routine can implement.

The constructors are intentionally layout-level operations, not ordinary
structured-machine transitions.  For example, {lit}`seekTape` and
{lit}`returnToBlockStart` change the physical cursor but leave the represented
logical tapes unchanged.
-/
inductive PhysicalPrimitive where
  | seekTape (index : Nat)
  | readHeadCell (index : Nat) (expected : Option Bool)
  | writeHeadCell (index : Nat) (cell : Option Bool)
  | moveHead (index : Nat) (move : HeadMove)
  | returnToBlockStart
deriving Repr, DecidableEq

namespace PhysicalPrimitive

/-- Logical endpoint effect of a primitive routine. -/
def apply :
    PhysicalPrimitive -> List (Tape Bool) -> List (Tape Bool)
  | seekTape _index, logical => logical
  | readHeadCell _index _expected, logical => logical
  | writeHeadCell index cell, logical =>
      replaceTapeAt index
        (Tape.write cell (Description.tapeAt logical index))
        logical
  | moveHead index move, logical =>
      replaceTapeAt index
        (move.apply (Description.tapeAt logical index))
        logical
  | returnToBlockStart, logical => logical

/--
Precondition for a primitive.  Read checks are partial: a physical checker is
only required to reach the normal endpoint when the encoded logical head cell
matches the expected read.
-/
def enabled :
    PhysicalPrimitive -> List (Tape Bool) -> Prop
  | readHeadCell index expected, logical =>
      Tape.read (Description.tapeAt logical index) = expected
  | _, _ => True

@[simp] theorem apply_seekTape
    (index : Nat) (logical : List (Tape Bool)) :
    apply (seekTape index) logical = logical := by
  rfl

@[simp] theorem apply_readHeadCell
    (index : Nat) (expected : Option Bool)
    (logical : List (Tape Bool)) :
    apply (readHeadCell index expected) logical = logical := by
  rfl

@[simp] theorem apply_returnToBlockStart
    (logical : List (Tape Bool)) :
    apply returnToBlockStart logical = logical := by
  rfl

@[simp] theorem enabled_seekTape
    (index : Nat) (logical : List (Tape Bool)) :
    enabled (seekTape index) logical := by
  trivial

@[simp] theorem enabled_writeHeadCell
    (index : Nat) (cell : Option Bool)
    (logical : List (Tape Bool)) :
    enabled (writeHeadCell index cell) logical := by
  trivial

@[simp] theorem enabled_moveHead
    (index : Nat) (move : HeadMove)
    (logical : List (Tape Bool)) :
    enabled (moveHead index move) logical := by
  trivial

@[simp] theorem enabled_returnToBlockStart
    (logical : List (Tape Bool)) :
    enabled returnToBlockStart logical := by
  trivial

end PhysicalPrimitive

/-- Apply a sequence of physical primitive endpoint effects. -/
def applyPhysicalPrimitiveSequence :
    List PhysicalPrimitive -> List (Tape Bool) -> List (Tape Bool)
  | [], logical => logical
  | primitive :: rest, logical =>
      applyPhysicalPrimitiveSequence rest
        (primitive.apply logical)

/-- Sequential precondition for a primitive list. -/
def physicalPrimitiveSequenceEnabled :
    List PhysicalPrimitive -> List (Tape Bool) -> Prop
  | [], _logical => True
  | primitive :: rest, logical =>
      primitive.enabled logical ∧
        physicalPrimitiveSequenceEnabled rest
          (primitive.apply logical)

@[simp] theorem applyPhysicalPrimitiveSequence_nil
    (logical : List (Tape Bool)) :
    applyPhysicalPrimitiveSequence [] logical = logical := by
  rfl

@[simp] theorem applyPhysicalPrimitiveSequence_cons
    (primitive : PhysicalPrimitive) (rest : List PhysicalPrimitive)
    (logical : List (Tape Bool)) :
    applyPhysicalPrimitiveSequence (primitive :: rest) logical =
      applyPhysicalPrimitiveSequence rest (primitive.apply logical) := by
  rfl

@[simp] theorem physicalPrimitiveSequenceEnabled_nil
    (logical : List (Tape Bool)) :
    physicalPrimitiveSequenceEnabled [] logical := by
  trivial

theorem applyPhysicalPrimitiveSequence_append
    (first second : List PhysicalPrimitive)
    (logical : List (Tape Bool)) :
    applyPhysicalPrimitiveSequence (first ++ second) logical =
      applyPhysicalPrimitiveSequence second
        (applyPhysicalPrimitiveSequence first logical) := by
  induction first generalizing logical with
  | nil =>
      rfl
  | cons primitive rest ih =>
      simp [applyPhysicalPrimitiveSequence, ih]

/--
Contract for one concrete physical primitive machine.

The machine starts and ends at the canonical encoded block boundary.  Internal
head movement is hidden by the contract; only the represented logical tapes are
observable.
-/
structure PhysicalPrimitiveContract
    (primitive : PhysicalPrimitive)
    (machine : MachineDescription) : Prop where
  subroutineReady : machine.SubroutineReady
  realizes :
    forall logical : List (Tape Bool),
      primitive.enabled logical ->
        machine.HaltsFromTape
          (encodedStructuredTapes logical)
          (encodedStructuredTapes (primitive.apply logical))

/-- Contract for a compiled sequence of physical primitives. -/
structure PhysicalPrimitiveSequenceContract
    (primitives : List PhysicalPrimitive)
    (machine : MachineDescription) : Prop where
  subroutineReady : machine.SubroutineReady
  realizes :
    forall logical : List (Tape Bool),
      physicalPrimitiveSequenceEnabled primitives logical ->
        machine.HaltsFromTape
          (encodedStructuredTapes logical)
          (encodedStructuredTapes
            (applyPhysicalPrimitiveSequence primitives logical))

def readCheckPrimitivesAt
    (index : Nat) (expected : Option Bool) :
    List PhysicalPrimitive :=
  [ PhysicalPrimitive.seekTape index
  , PhysicalPrimitive.readHeadCell index expected
  , PhysicalPrimitive.returnToBlockStart ]

def writePrimitivesForAction
    (index : Nat) (action : TapeAction) :
    List PhysicalPrimitive :=
  match action.write? with
  | none => []
  | some cell => [PhysicalPrimitive.writeHeadCell index cell]

def actionPrimitivesAt
    (index : Nat) (action : TapeAction) :
    List PhysicalPrimitive :=
  [PhysicalPrimitive.seekTape index] ++
    writePrimitivesForAction index action ++
      [ PhysicalPrimitive.moveHead index action.move
      , PhysicalPrimitive.returnToBlockStart ]

@[simp] theorem applyPhysicalPrimitiveSequence_readCheckPrimitivesAt
    (index : Nat) (expected : Option Bool)
    (logical : List (Tape Bool)) :
    applyPhysicalPrimitiveSequence
        (readCheckPrimitivesAt index expected) logical =
      logical := by
  rfl

theorem applyPhysicalPrimitiveSequence_actionPrimitivesAt_zero_three
    (action : TapeAction) (T U V : Tape Bool) :
    applyPhysicalPrimitiveSequence
        (actionPrimitivesAt 0 action) [T, U, V] =
      [action.apply T, U, V] := by
  cases action with
  | mk write? move =>
      cases write? with
      | none =>
          cases move <;> rfl
      | some cell =>
          cases move <;> rfl

theorem applyPhysicalPrimitiveSequence_actionPrimitivesAt_one_three
    (action : TapeAction) (T U V : Tape Bool) :
    applyPhysicalPrimitiveSequence
        (actionPrimitivesAt 1 action) [T, U, V] =
      [T, action.apply U, V] := by
  cases action with
  | mk write? move =>
      cases write? with
      | none =>
          cases move <;> rfl
      | some cell =>
          cases move <;> rfl

theorem applyPhysicalPrimitiveSequence_actionPrimitivesAt_two_three
    (action : TapeAction) (T U V : Tape Bool) :
    applyPhysicalPrimitiveSequence
        (actionPrimitivesAt 2 action) [T, U, V] =
      [T, U, action.apply V] := by
  cases action with
  | mk write? move =>
      cases write? with
      | none =>
          cases move <;> rfl
      | some cell =>
          cases move <;> rfl

def transitionPrimitiveSequence3
    (read0 read1 read2 : Option Bool)
    (action0 action1 action2 : TapeAction) :
    List PhysicalPrimitive :=
  readCheckPrimitivesAt 0 read0 ++
    readCheckPrimitivesAt 1 read1 ++
      readCheckPrimitivesAt 2 read2 ++
        actionPrimitivesAt 0 action0 ++
          actionPrimitivesAt 1 action1 ++
            actionPrimitivesAt 2 action2

theorem applyPhysicalPrimitiveSequence_transitionPrimitiveSequence3
    (read0 read1 read2 : Option Bool)
    (action0 action1 action2 : TapeAction)
    (T U V : Tape Bool) :
    applyPhysicalPrimitiveSequence
        (transitionPrimitiveSequence3 read0 read1 read2
          action0 action1 action2) [T, U, V] =
      [action0.apply T, action1.apply U, action2.apply V] := by
  simp [transitionPrimitiveSequence3,
    applyPhysicalPrimitiveSequence_append,
    applyPhysicalPrimitiveSequence_actionPrimitivesAt_zero_three,
    applyPhysicalPrimitiveSequence_actionPrimitivesAt_one_three,
    applyPhysicalPrimitiveSequence_actionPrimitivesAt_two_three]

def transitionPrimitiveSequenceOfRow3
    (t : Transition) : List PhysicalPrimitive :=
  match t.reads, t.actions with
  | [read0, read1, read2], [action0, action1, action2] =>
      transitionPrimitiveSequence3 read0 read1 read2
        action0 action1 action2
  | _, _ => []

theorem applyPhysicalPrimitiveSequence_transitionPrimitiveSequenceOfRow3
    (t : Transition)
    (read0 read1 read2 : Option Bool)
    (action0 action1 action2 : TapeAction)
    (T U V : Tape Bool)
    (hreads : t.reads = [read0, read1, read2])
    (hactions : t.actions = [action0, action1, action2]) :
    applyPhysicalPrimitiveSequence
        (transitionPrimitiveSequenceOfRow3 t) [T, U, V] =
      [action0.apply T, action1.apply U, action2.apply V] := by
  cases t with
  | mk source reads actions target =>
      simp [transitionPrimitiveSequenceOfRow3] at hreads hactions ⊢
      cases hreads
      cases hactions
      exact
        applyPhysicalPrimitiveSequence_transitionPrimitiveSequence3
          read0 read1 read2 action0 action1 action2 T U V

/-!
## One-transition lowering contract
-/

/--
Contract for the physical machine that lowers one structured transition row.

This is the first milestone-8 bridge.  It does not yet build the physical
transition table; instead it states exactly what such a table must do from the
canonical encoded boundary when the row's source state and read tuple match.
-/
structure LowersTransition
    (D : Description) (t : Transition)
    (machine : MachineDescription) : Prop where
  subroutineReady : machine.SubroutineReady
  realizes :
    forall c : Configuration,
      c.tapes.length = D.tapeCount ->
      t.source = c.state ->
        t.reads = D.currentReads c ->
          machine.HaltsFromTape
            (encodedStructuredTapes c.tapes)
            (encodedStructuredTapes
              (D.applyActions t.actions c.tapes))

def structuredTransitionTarget
    (D : Description) (t : Transition)
    (c : Configuration) : Configuration where
  state := t.target
  tapes := D.applyActions t.actions c.tapes

theorem stepConfig_eq_some_of_lookupTransition
    {D : Description} {c : Configuration} {t : Transition}
    (hlookup : D.lookupTransition c = some t) :
    D.stepConfig c = some (structuredTransitionTarget D t c) := by
  simp [Description.stepConfig, structuredTransitionTarget, hlookup]

theorem lowersTransition_realizes_lookup
    {D : Description} {t : Transition}
    {machine : MachineDescription} {c : Configuration}
    (h : LowersTransition D t machine)
    (hc : c.tapes.length = D.tapeCount)
    (hlookup : D.lookupTransition c = some t) :
    machine.HaltsFromTape
      (encodedStructuredTapes c.tapes)
      (encodedStructuredTapes
        (D.applyActions t.actions c.tapes)) := by
  have hmatch := Description.lookupTransition_match hlookup
  exact h.realizes c hc hmatch.left hmatch.right

theorem lowersTransition_realizes_structured_step
    {D : Description} {t : Transition}
    {machine : MachineDescription} {c next : Configuration}
    (h : LowersTransition D t machine)
    (hc : c.tapes.length = D.tapeCount)
    (hlookup : D.lookupTransition c = some t)
    (hnext : next = structuredTransitionTarget D t c) :
    D.stepConfig c = some next ∧
      machine.HaltsFromTape
        (encodedStructuredTapes c.tapes)
        (encodedStructuredTapes next.tapes) := by
  constructor
  · rw [hnext]
    exact stepConfig_eq_some_of_lookupTransition hlookup
  · rw [hnext]
    exact lowersTransition_realizes_lookup h hc hlookup

/-!
## Cursor-level physical routines
-/

/--
Cursor position immediately after the separator that opens a logical tape
segment.  This is the first executable cursor boundary after
{name}`AtTapeSeparator`: a one-tape machine can move right from a separator
into the segment, then later scan for the head marker or next separator.
-/
def AtTapeSegmentEntry
    (logical : List (Tape Bool)) (tapeIndex : Nat)
    (physical : Tape Bool) : Prop :=
  exists T : Tape Bool, exists rest : List (Tape Bool),
    logical.drop tapeIndex = T :: rest ∧
      physical =
        tapeAtEncodedSplit
          (List.append
            (encodedPrefixBeforeTape logical tapeIndex)
            tapeSeparatorCells)
          (List.append (logicalTapeCode T)
            (encodedStructuredTapeCells rest))

/--
Cursor position on the separator immediately after a logical tape segment.

This is intentionally stated with the same {lit}`drop tapeIndex = T :: rest`
witness as {name}`AtTapeSegmentEntry`; a later bridge can identify this with
{lit}`AtTapeSeparator logical (tapeIndex + 1)`.
-/
def AtTapeSegmentExit
    (logical : List (Tape Bool)) (tapeIndex : Nat)
    (physical : Tape Bool) : Prop :=
  exists T : Tape Bool, exists rest : List (Tape Bool),
    logical.drop tapeIndex = T :: rest ∧
      physical =
        tapeAtEncodedSplit
          (List.append
            (List.append
              (encodedPrefixBeforeTape logical tapeIndex)
              tapeSeparatorCells)
            (logicalTapeCode T))
          (encodedStructuredTapeCells rest)

/-- A separator cursor whose selected tape segment exists. -/
def AtExistingTapeSeparator
    (logical : List (Tape Bool)) (tapeIndex : Nat)
    (physical : Tape Bool) : Prop :=
  AtTapeSeparator logical tapeIndex physical ∧
    exists T : Tape Bool, exists rest : List (Tape Bool),
      logical.drop tapeIndex = T :: rest

def AtTapeHeadCellCodeWithRead
    (logical : List (Tape Bool)) (tapeIndex : Nat)
    (expected : Option Bool) (physical : Tape Bool) : Prop :=
  exists T : Tape Bool, exists rest : List (Tape Bool),
    logical.drop tapeIndex = T :: rest ∧
      Tape.read T = expected ∧
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

private theorem replaceTapeAt_take_eq
    (logical : List (Tape Bool)) (tapeIndex : Nat)
    (replacement : Tape Bool) :
    (replaceTapeAt tapeIndex replacement logical).take tapeIndex =
      logical.take tapeIndex := by
  induction tapeIndex generalizing logical with
  | zero =>
      cases logical <;> rfl
  | succ tapeIndex ih =>
      cases logical with
      | nil => rfl
      | cons T rest =>
          simp [replaceTapeAt, ih]

private theorem replaceTapeAt_drop_eq_of_drop_eq_cons
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {T replacement : Tape Bool} {rest : List (Tape Bool)}
    (hdrop : logical.drop tapeIndex = T :: rest) :
    (replaceTapeAt tapeIndex replacement logical).drop tapeIndex =
      replacement :: rest := by
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
          exact ih hdrop

private theorem encodedPrefixBeforeTape_replaceTapeAt_eq
    (logical : List (Tape Bool)) (tapeIndex : Nat)
    (replacement : Tape Bool) :
    encodedPrefixBeforeTape
        (replaceTapeAt tapeIndex replacement logical) tapeIndex =
      encodedPrefixBeforeTape logical tapeIndex := by
  simp [encodedPrefixBeforeTape, replaceTapeAt_take_eq]

private theorem list_getD_eq_of_drop_eq_cons
    {α : Type u} {xs : List α} {index : Nat}
    {head fallback : α} {tail : List α}
    (hdrop : xs.drop index = head :: tail) :
    xs.getD index fallback = head := by
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

private theorem description_tapeAt_eq_of_drop_eq_cons
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {T : Tape Bool} {rest : List (Tape Bool)}
    (hdrop : logical.drop tapeIndex = T :: rest) :
    Description.tapeAt logical tapeIndex = T := by
  exact list_getD_eq_of_drop_eq_cons
    (fallback := Tape.blank) hdrop

private theorem take_succ_eq_take_append_of_drop_eq_cons
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

private theorem drop_succ_eq_tail_of_drop_eq_cons
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

private theorem succ_le_length_of_drop_eq_cons
    {α : Type u} {xs : List α} {index : Nat}
    {head : α} {tail : List α}
    (hdrop : xs.drop index = head :: tail) :
    index + 1 ≤ xs.length := by
  induction index generalizing xs with
  | zero =>
      cases xs with
      | nil =>
          simp at hdrop
      | cons x rest =>
          simp
  | succ index ih =>
      cases xs with
      | nil =>
          simp at hdrop
      | cons x rest =>
          simp at hdrop
          have hrest : index + 1 ≤ rest.length :=
            ih hdrop
          simpa [Nat.add_assoc, Nat.succ_eq_add_one] using
            Nat.succ_le_succ hrest

theorem atTapeSegmentExit_to_atTapeSeparator_succ
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {physical : Tape Bool}
    (h : AtTapeSegmentExit logical tapeIndex physical) :
    AtTapeSeparator logical (tapeIndex + 1) physical := by
  rcases h with ⟨T, rest, hdrop, hphysical⟩
  constructor
  · exact succ_le_length_of_drop_eq_cons hdrop
  · rw [hphysical]
    have htake :
        logical.take (tapeIndex + 1) =
          logical.take tapeIndex ++ [T] :=
      take_succ_eq_take_append_of_drop_eq_cons hdrop
    have hdropSucc :
        logical.drop (tapeIndex + 1) = rest :=
      drop_succ_eq_tail_of_drop_eq_cons hdrop
    simp [tapeAtEncodedSplit,
      encodedPrefixBeforeTape, encodedSuffixFromTape, htake, hdropSucc,
      List.append_assoc]

/--
Contract for a concrete cursor routine.

Unlike {name}`PhysicalPrimitiveContract`, this does not force the routine to
start and end at the canonical block boundary.  It is the lower-level shape
needed by real physical seek/scan routines.
-/
structure CursorRoutineContract
    (source target : List (Tape Bool) -> Tape Bool -> Prop)
    (machine : MachineDescription) : Prop where
  subroutineReady : machine.SubroutineReady
  realizes :
    forall logical : List (Tape Bool),
    forall Tin : Tape Bool,
      source logical Tin ->
        exists Tout : Tape Bool,
          machine.HaltsFromTape Tin Tout ∧ target logical Tout

/--
Concrete zero-step cursor machine.

This is useful for already-at-boundary routines, notably the fixed
{lit}`seekTape 0` case from the canonical encoded block start.
-/
def cursorNoopDescription : MachineDescription where
  stateCount := 1
  start := 0
  halt := 0
  transitions := []

theorem cursorNoopDescription_wellFormed :
    cursorNoopDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · intro t ht
    simp [cursorNoopDescription] at ht
  · intro t _u ht _hu _hkey
    simp [cursorNoopDescription] at ht

theorem cursorNoopDescription_haltTransitionFree :
    cursorNoopDescription.HaltTransitionFree := by
  intro t ht
  simp [cursorNoopDescription] at ht

theorem cursorNoopDescription_subroutineReady :
    cursorNoopDescription.SubroutineReady :=
  ⟨cursorNoopDescription_wellFormed,
    cursorNoopDescription_haltTransitionFree⟩

theorem cursorNoopDescription_haltsFromTape
    (T : Tape Bool) :
    cursorNoopDescription.HaltsFromTape T T := by
  refine ⟨0, ?_⟩
  constructor <;> rfl

theorem cursorNoopDescription_contract
    (P : List (Tape Bool) -> Tape Bool -> Prop) :
    CursorRoutineContract P P cursorNoopDescription where
  subroutineReady := cursorNoopDescription_subroutineReady
  realizes := by
    intro logical Tin hsource
    exact ⟨Tin, cursorNoopDescription_haltsFromTape Tin, hsource⟩

/-- The concrete fixed-index seek routine for tape 0 at block start. -/
def seekTape0Description : MachineDescription :=
  cursorNoopDescription

theorem seekTape0Description_physicalPrimitiveContract :
    PhysicalPrimitiveContract (PhysicalPrimitive.seekTape 0)
      seekTape0Description where
  subroutineReady := cursorNoopDescription_subroutineReady
  realizes := by
    intro logical _henabled
    exact cursorNoopDescription_haltsFromTape
      (encodedStructuredTapes logical)

/-- Return-to-block-start is also a no-op once the caller is already there. -/
def returnBlockStartNoopDescription : MachineDescription :=
  cursorNoopDescription

theorem returnBlockStartNoopDescription_physicalPrimitiveContract :
    PhysicalPrimitiveContract PhysicalPrimitive.returnToBlockStart
      returnBlockStartNoopDescription where
  subroutineReady := cursorNoopDescription_subroutineReady
  realizes := by
    intro logical _henabled
    exact cursorNoopDescription_haltsFromTape
      (encodedStructuredTapes logical)

/-!
## Concrete row machines
-/

/--
Concrete row machine for a three-tape row whose actions are all
{name}`TapeAction.stay`.

The row read tuple is handled by the {name}`LowersTransition` precondition:
this machine is only used after structured lookup has already established that
the row is the active row.  Therefore the physical implementation is the
zero-step no-op machine.
-/
def stayRow3Description (_t : Transition) : MachineDescription :=
  cursorNoopDescription

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

theorem applyActions_three_stay
    (D : Description) (hD : D.tapeCount = 3)
    (T U V : Tape Bool) :
    D.applyActions
        [TapeAction.stay, TapeAction.stay, TapeAction.stay]
        [T, U, V] =
      [T, U, V] := by
  rw [Description.applyActions_three D hD]
  simp [TapeAction.stay, TapeAction.apply, HeadMove.apply]

theorem stayRow3Description_lowersTransition
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (hactions :
      t.actions =
        [TapeAction.stay, TapeAction.stay, TapeAction.stay]) :
    LowersTransition D t (stayRow3Description t) where
  subroutineReady := cursorNoopDescription_subroutineReady
  realizes := by
    intro c hc _hsource _hreads
    have hlen : c.tapes.length = 3 := by
      simpa [hD] using hc
    rcases list_eq_three_of_length_eq_three hlen with
      ⟨T, U, V, htapes⟩
    cases c with
    | mk state tapes =>
        simp at htapes
        cases htapes
        change
          cursorNoopDescription.HaltsFromTape
            (encodedStructuredTapes [T, U, V])
            (encodedStructuredTapes
              (D.applyActions t.actions [T, U, V]))
        rw [hactions, applyActions_three_stay D hD T U V]
        exact cursorNoopDescription_haltsFromTape
          (encodedStructuredTapes [T, U, V])

/-- Preserve the current physical cell and move once. -/
def cursorMoveOnceDescription (move : Direction) :
    MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ { source := 0
        read := none
        write := none
        move := move
        target := 1 }
    , { source := 0
        read := some false
        write := some false
        move := move
        target := 1 }
    , { source := 0
        read := some true
        write := some true
        move := move
        target := 1 } ]

theorem cursorMoveOnceDescription_wellFormed
    (move : Direction) :
    (cursorMoveOnceDescription move).WellFormed := by
  cases move
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := (cursorMoveOnceDescription Direction.left).transitions)
      (stateCount := (cursorMoveOnceDescription Direction.left).stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := (cursorMoveOnceDescription Direction.left).transitions)
      (by decide)
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := (cursorMoveOnceDescription Direction.right).transitions)
      (stateCount := (cursorMoveOnceDescription Direction.right).stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := (cursorMoveOnceDescription Direction.right).transitions)
      (by decide)

theorem cursorMoveOnceDescription_haltTransitionFree
    (move : Direction) :
    (cursorMoveOnceDescription move).HaltTransitionFree :=
  transition_notFrom_of_all
    (l := (cursorMoveOnceDescription move).transitions)
    (state := (cursorMoveOnceDescription move).halt)
    (by cases move <;> decide)

theorem cursorMoveOnceDescription_subroutineReady
    (move : Direction) :
    (cursorMoveOnceDescription move).SubroutineReady :=
  ⟨cursorMoveOnceDescription_wellFormed move,
    cursorMoveOnceDescription_haltTransitionFree move⟩

theorem cursorMoveOnceDescription_run
    (move : Direction) (T : Tape Bool) :
    (cursorMoveOnceDescription move).runConfig 1
        { state := (cursorMoveOnceDescription move).start
          tape := T } =
      { state := (cursorMoveOnceDescription move).halt
        tape := Tape.move move T } := by
  cases move <;>
    cases T with
    | mk left head right =>
        cases head with
        | none =>
            simp [cursorMoveOnceDescription, MachineDescription.runConfig,
              MachineDescription.stepConfig,
              MachineDescription.lookupTransition,
              MachineDescription.Matches, Tape.read, Tape.write]
        | some bit =>
            cases bit <;>
              simp [cursorMoveOnceDescription,
                MachineDescription.runConfig,
                MachineDescription.stepConfig,
                MachineDescription.lookupTransition,
                MachineDescription.Matches, Tape.read, Tape.write]

theorem cursorMoveOnceDescription_haltsFromTape
    (move : Direction) (T : Tape Bool) :
    (cursorMoveOnceDescription move).HaltsFromTape T
      (Tape.move move T) := by
  refine ⟨1, ?_⟩
  constructor <;>
    rw [cursorMoveOnceDescription_run]

/--
Scan right over the nonblank encoded cells of one logical tape segment, then
bounce left/right so the final halted head is exactly on the next separator.
-/
def cursorScanToNextSeparatorDescription : MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ { source := 0
        read := some false
        write := some false
        move := Direction.right
        target := 0 }
    , { source := 0
        read := some true
        write := some true
        move := Direction.right
        target := 0 }
    , { source := 0
        read := none
        write := none
        move := Direction.left
        target := 1 }
    , { source := 1
        read := some false
        write := some false
        move := Direction.right
        target := 2 }
    , { source := 1
        read := some true
        write := some true
        move := Direction.right
        target := 2 } ]

theorem cursorScanToNextSeparatorDescription_wellFormed :
    cursorScanToNextSeparatorDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := cursorScanToNextSeparatorDescription.transitions)
      (stateCount := cursorScanToNextSeparatorDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := cursorScanToNextSeparatorDescription.transitions)
      (by decide)

theorem cursorScanToNextSeparatorDescription_haltTransitionFree :
    cursorScanToNextSeparatorDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := cursorScanToNextSeparatorDescription.transitions)
    (state := cursorScanToNextSeparatorDescription.halt)
    (by decide)

theorem cursorScanToNextSeparatorDescription_subroutineReady :
    cursorScanToNextSeparatorDescription.SubroutineReady :=
  ⟨cursorScanToNextSeparatorDescription_wellFormed,
    cursorScanToNextSeparatorDescription_haltTransitionFree⟩

private theorem cursorScanToNextSeparatorDescription_step_bit
    (left right : List (Option Bool)) (bit : Bool) :
    cursorScanToNextSeparatorDescription.runConfig 1
        { state := cursorScanToNextSeparatorDescription.start
          tape := tapeAtCells left (some bit :: right) } =
      { state := cursorScanToNextSeparatorDescription.start
        tape := tapeAtCells (some bit :: left) right } := by
  cases bit <;> cases right <;>
    simp [cursorScanToNextSeparatorDescription,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem cursorScanToNextSeparatorDescription_run_scan
    (bits : Word Bool) (left suffix : List (Option Bool)) :
    cursorScanToNextSeparatorDescription.runConfig bits.length
        { state := cursorScanToNextSeparatorDescription.start
          tape :=
            tapeAtCells left
              (List.append (bits.map some) (none :: suffix)) } =
      { state := cursorScanToNextSeparatorDescription.start
        tape :=
          tapeAtCells
            (List.append (bits.reverse.map some) left)
            (none :: suffix) } := by
  induction bits generalizing left with
  | nil =>
      simp [MachineDescription.runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp [Nat.add_comm]]
      rw [MachineDescription.runConfig_add]
      change
        cursorScanToNextSeparatorDescription.runConfig rest.length
            (cursorScanToNextSeparatorDescription.runConfig 1
              { state := cursorScanToNextSeparatorDescription.start
                tape :=
                  tapeAtCells left
                    (some bit ::
                      List.append (rest.map some) (none :: suffix)) }) =
          { state := cursorScanToNextSeparatorDescription.start
            tape :=
              tapeAtCells
                (List.append ((bit :: rest).reverse.map some) left)
                (none :: suffix) }
      rw [cursorScanToNextSeparatorDescription_step_bit left
        (List.append (rest.map some) (none :: suffix)) bit]
      simpa [List.reverse_cons, List.map_append,
        List.append_assoc] using ih (some bit :: left)

private theorem reverse_map_some_append_exists_cons
    (bit : Bool) (rest : Word Bool)
    (left : List (Option Bool)) :
    exists head : Bool, exists tail : List (Option Bool),
      List.append ((bit :: rest).reverse.map some) left =
        some head :: tail := by
  induction rest generalizing bit left with
  | nil =>
      exact ⟨bit, left, rfl⟩
  | cons next rest ih =>
      simpa [List.reverse_cons, List.map_append,
        List.append_assoc] using ih next (some bit :: left)

private theorem cursorScanToNextSeparatorDescription_run_finish
    (bit : Bool) (left suffix : List (Option Bool)) :
    cursorScanToNextSeparatorDescription.runConfig 2
        { state := cursorScanToNextSeparatorDescription.start
          tape := tapeAtCells (some bit :: left) (none :: suffix) } =
      { state := cursorScanToNextSeparatorDescription.halt
        tape := tapeAtCells (some bit :: left) (none :: suffix) } := by
  cases bit <;> cases left <;> cases suffix <;>
    simp [cursorScanToNextSeparatorDescription,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      Tape.moveRight]

theorem cursorScanToNextSeparatorDescription_run_to_next
    (bit : Bool) (rest : Word Bool)
    (left suffix : List (Option Bool)) :
    cursorScanToNextSeparatorDescription.runConfig
        ((bit :: rest).length + 2)
        { state := cursorScanToNextSeparatorDescription.start
          tape :=
            tapeAtCells left
              (List.append ((bit :: rest).map some)
                (none :: suffix)) } =
      { state := cursorScanToNextSeparatorDescription.halt
        tape :=
          tapeAtCells
            (List.append ((bit :: rest).reverse.map some) left)
            (none :: suffix) } := by
  rw [MachineDescription.runConfig_add]
  rw [cursorScanToNextSeparatorDescription_run_scan]
  rcases reverse_map_some_append_exists_cons bit rest left with
    ⟨head, tail, hleft⟩
  rw [hleft]
  exact cursorScanToNextSeparatorDescription_run_finish head tail suffix

theorem cursorScanToNextSeparatorDescription_haltsFromTape
    (bit : Bool) (rest : Word Bool)
    (left suffix : List (Option Bool)) :
    cursorScanToNextSeparatorDescription.HaltsFromTape
      (tapeAtCells left
        (List.append ((bit :: rest).map some) (none :: suffix)))
      (tapeAtCells
        (List.append ((bit :: rest).reverse.map some) left)
        (none :: suffix)) := by
  refine ⟨(bit :: rest).length + 2, ?_⟩
  constructor <;>
    rw [cursorScanToNextSeparatorDescription_run_to_next]

theorem cursorScanToNextSeparatorDescription_contract_segmentEntry_to_exit
    (tapeIndex : Nat) :
    CursorRoutineContract
      (fun logical physical =>
        AtTapeSegmentEntry logical tapeIndex physical)
      (fun logical physical =>
        AtTapeSegmentExit logical tapeIndex physical)
      cursorScanToNextSeparatorDescription where
  subroutineReady :=
    cursorScanToNextSeparatorDescription_subroutineReady
  realizes := by
    intro logical Tin hentry
    rcases hentry with ⟨T, rest, hdrop, hTin⟩
    rcases logicalTapeBits_exists_cons T with ⟨bit, bits, hbits⟩
    rcases encodedStructuredTapeCells_startsWith_separator rest with
      ⟨suffix, hsuffix⟩
    let Tout :=
      tapeAtEncodedSplit
        (List.append
          (List.append
            (encodedPrefixBeforeTape logical tapeIndex)
            tapeSeparatorCells)
          (logicalTapeCode T))
        (encodedStructuredTapeCells rest)
    exists Tout
    constructor
    · rw [hTin]
      have hrun :=
        cursorScanToNextSeparatorDescription_haltsFromTape bit bits
          (List.append
            (encodedPrefixBeforeTape logical tapeIndex)
            tapeSeparatorCells).reverse
          suffix
      simpa [Tout, tapeAtEncodedSplit, logicalTapeCode_eq_map_some T,
        hbits, hsuffix, tapeSeparatorCells, List.reverse_append,
        List.map_reverse, List.append_assoc] using hrun
    · exact ⟨T, rest, hdrop, rfl⟩

/--
Seek from the separator before an existing segment to the separator immediately
after that segment.
-/
def cursorSeekNextSeparatorDescription : MachineDescription where
  stateCount := 4
  start := 0
  halt := 3
  transitions :=
    [ { source := 0
        read := none
        write := none
        move := Direction.right
        target := 1 }
    , { source := 1
        read := some false
        write := some false
        move := Direction.right
        target := 1 }
    , { source := 1
        read := some true
        write := some true
        move := Direction.right
        target := 1 }
    , { source := 1
        read := none
        write := none
        move := Direction.left
        target := 2 }
    , { source := 2
        read := some false
        write := some false
        move := Direction.right
        target := 3 }
    , { source := 2
        read := some true
        write := some true
        move := Direction.right
        target := 3 } ]

theorem cursorSeekNextSeparatorDescription_wellFormed :
    cursorSeekNextSeparatorDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := cursorSeekNextSeparatorDescription.transitions)
      (stateCount := cursorSeekNextSeparatorDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := cursorSeekNextSeparatorDescription.transitions)
      (by decide)

theorem cursorSeekNextSeparatorDescription_haltTransitionFree :
    cursorSeekNextSeparatorDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := cursorSeekNextSeparatorDescription.transitions)
    (state := cursorSeekNextSeparatorDescription.halt)
    (by decide)

theorem cursorSeekNextSeparatorDescription_subroutineReady :
    cursorSeekNextSeparatorDescription.SubroutineReady :=
  ⟨cursorSeekNextSeparatorDescription_wellFormed,
    cursorSeekNextSeparatorDescription_haltTransitionFree⟩

private theorem cursorSeekNextSeparatorDescription_step_entry
    (left right : List (Option Bool)) :
    cursorSeekNextSeparatorDescription.runConfig 1
        { state := cursorSeekNextSeparatorDescription.start
          tape := tapeAtCells left (none :: right) } =
      { state := 1
        tape := tapeAtCells (none :: left) right } := by
  cases right <;>
    simp [cursorSeekNextSeparatorDescription,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem cursorSeekNextSeparatorDescription_step_bit
    (left right : List (Option Bool)) (bit : Bool) :
    cursorSeekNextSeparatorDescription.runConfig 1
        { state := 1
          tape := tapeAtCells left (some bit :: right) } =
      { state := 1
        tape := tapeAtCells (some bit :: left) right } := by
  cases bit <;> cases right <;>
    simp [cursorSeekNextSeparatorDescription,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem cursorSeekNextSeparatorDescription_run_scan
    (bits : Word Bool) (left suffix : List (Option Bool)) :
    cursorSeekNextSeparatorDescription.runConfig bits.length
        { state := 1
          tape :=
            tapeAtCells left
              (List.append (bits.map some) (none :: suffix)) } =
      { state := 1
        tape :=
          tapeAtCells
            (List.append (bits.reverse.map some) left)
            (none :: suffix) } := by
  induction bits generalizing left with
  | nil =>
      simp [MachineDescription.runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp [Nat.add_comm]]
      rw [MachineDescription.runConfig_add]
      change
        cursorSeekNextSeparatorDescription.runConfig rest.length
            (cursorSeekNextSeparatorDescription.runConfig 1
              { state := 1
                tape :=
                  tapeAtCells left
                    (some bit ::
                      List.append (rest.map some) (none :: suffix)) }) =
          { state := 1
            tape :=
              tapeAtCells
                (List.append ((bit :: rest).reverse.map some) left)
                (none :: suffix) }
      rw [cursorSeekNextSeparatorDescription_step_bit left
        (List.append (rest.map some) (none :: suffix)) bit]
      simpa [List.reverse_cons, List.map_append,
        List.append_assoc] using ih (some bit :: left)

private theorem cursorSeekNextSeparatorDescription_run_finish
    (bit : Bool) (left suffix : List (Option Bool)) :
    cursorSeekNextSeparatorDescription.runConfig 2
        { state := 1
          tape := tapeAtCells (some bit :: left) (none :: suffix) } =
      { state := cursorSeekNextSeparatorDescription.halt
        tape := tapeAtCells (some bit :: left) (none :: suffix) } := by
  cases bit <;> cases left <;> cases suffix <;>
    simp [cursorSeekNextSeparatorDescription,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      Tape.moveRight]

theorem cursorSeekNextSeparatorDescription_run_to_next
    (bit : Bool) (rest : Word Bool)
    (left suffix : List (Option Bool)) :
    cursorSeekNextSeparatorDescription.runConfig
        ((bit :: rest).length + 3)
        { state := cursorSeekNextSeparatorDescription.start
          tape :=
            tapeAtCells left
              (none ::
                List.append ((bit :: rest).map some)
                  (none :: suffix)) } =
      { state := cursorSeekNextSeparatorDescription.halt
        tape :=
          tapeAtCells
            (List.append ((bit :: rest).reverse.map some)
              (none :: left))
            (none :: suffix) } := by
  rw [show (bit :: rest).length + 3 =
      1 + ((bit :: rest).length + 2) by
    simp [Nat.add_assoc, Nat.add_left_comm]]
  rw [MachineDescription.runConfig_add]
  rw [cursorSeekNextSeparatorDescription_step_entry]
  rw [MachineDescription.runConfig_add]
  rw [cursorSeekNextSeparatorDescription_run_scan]
  rcases reverse_map_some_append_exists_cons bit rest (none :: left) with
    ⟨head, tail, hleft⟩
  rw [hleft]
  exact cursorSeekNextSeparatorDescription_run_finish head tail suffix

theorem cursorSeekNextSeparatorDescription_haltsFromTape
    (bit : Bool) (rest : Word Bool)
    (left suffix : List (Option Bool)) :
    cursorSeekNextSeparatorDescription.HaltsFromTape
      (tapeAtCells left
        (none ::
          List.append ((bit :: rest).map some) (none :: suffix)))
      (tapeAtCells
        (List.append ((bit :: rest).reverse.map some) (none :: left))
        (none :: suffix)) := by
  refine ⟨(bit :: rest).length + 3, ?_⟩
  constructor <;>
    rw [cursorSeekNextSeparatorDescription_run_to_next]

theorem cursorSeekNextSeparatorDescription_contract
    (tapeIndex : Nat) :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator logical tapeIndex physical)
      (fun logical physical =>
        AtTapeSeparator logical (tapeIndex + 1) physical)
      cursorSeekNextSeparatorDescription where
  subroutineReady :=
    cursorSeekNextSeparatorDescription_subroutineReady
  realizes := by
    intro logical Tin hsource
    rcases hsource with ⟨hseparator, T, rest, hdrop⟩
    rcases logicalTapeBits_exists_cons T with ⟨bit, bits, hbits⟩
    rcases encodedStructuredTapeCells_startsWith_separator rest with
      ⟨suffix, hsuffix⟩
    let Tout :=
      tapeAtEncodedSplit
        (List.append
          (List.append
            (encodedPrefixBeforeTape logical tapeIndex)
            tapeSeparatorCells)
          (logicalTapeCode T))
        (encodedStructuredTapeCells rest)
    exists Tout
    constructor
    · rcases hseparator with ⟨_hle, hTin⟩
      rw [hTin]
      have hrun :=
        cursorSeekNextSeparatorDescription_haltsFromTape bit bits
          (encodedPrefixBeforeTape logical tapeIndex).reverse suffix
      simpa [Tout, tapeAtEncodedSplit, encodedSuffixFromTape, hdrop,
        logicalTapeCode_eq_map_some T, hbits, hsuffix,
        tapeSeparatorCells, List.reverse_append, List.map_reverse,
        List.append_assoc] using hrun
    · exact atTapeSegmentExit_to_atTapeSeparator_succ
        ⟨T, rest, hdrop, rfl⟩

/-- Fixed seek from the canonical block start to tape 1. -/
def seekTape1Description : MachineDescription :=
  cursorSeekNextSeparatorDescription

theorem seekTape1Description_contract :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator logical 0 physical)
      (fun logical physical =>
        AtTapeSeparator logical 1 physical)
      seekTape1Description :=
  cursorSeekNextSeparatorDescription_contract 0

/--
Fixed seek from the canonical block start to tape 2.

This is a concrete two-segment scanner.  It is intentionally separate from the
single-segment scanner because this layer still has no verified subroutine
composition operator for {name}`MachineDescription`.
-/
def seekTape2Description : MachineDescription where
  stateCount := 5
  start := 0
  halt := 4
  transitions :=
    [ { source := 0
        read := none
        write := none
        move := Direction.right
        target := 1 }
    , { source := 1
        read := some false
        write := some false
        move := Direction.right
        target := 1 }
    , { source := 1
        read := some true
        write := some true
        move := Direction.right
        target := 1 }
    , { source := 1
        read := none
        write := none
        move := Direction.right
        target := 2 }
    , { source := 2
        read := some false
        write := some false
        move := Direction.right
        target := 2 }
    , { source := 2
        read := some true
        write := some true
        move := Direction.right
        target := 2 }
    , { source := 2
        read := none
        write := none
        move := Direction.left
        target := 3 }
    , { source := 3
        read := some false
        write := some false
        move := Direction.right
        target := 4 }
    , { source := 3
        read := some true
        write := some true
        move := Direction.right
        target := 4 } ]

theorem seekTape2Description_wellFormed :
    seekTape2Description.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := seekTape2Description.transitions)
      (stateCount := seekTape2Description.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := seekTape2Description.transitions)
      (by decide)

theorem seekTape2Description_haltTransitionFree :
    seekTape2Description.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := seekTape2Description.transitions)
    (state := seekTape2Description.halt)
    (by decide)

theorem seekTape2Description_subroutineReady :
    seekTape2Description.SubroutineReady :=
  ⟨seekTape2Description_wellFormed,
    seekTape2Description_haltTransitionFree⟩

private theorem seekTape2Description_step_entry
    (left right : List (Option Bool)) :
    seekTape2Description.runConfig 1
        { state := seekTape2Description.start
          tape := tapeAtCells left (none :: right) } =
      { state := 1
        tape := tapeAtCells (none :: left) right } := by
  cases right <;>
    simp [seekTape2Description,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem seekTape2Description_step_bit_first
    (left right : List (Option Bool)) (bit : Bool) :
    seekTape2Description.runConfig 1
        { state := 1
          tape := tapeAtCells left (some bit :: right) } =
      { state := 1
        tape := tapeAtCells (some bit :: left) right } := by
  cases bit <;> cases right <;>
    simp [seekTape2Description,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem seekTape2Description_run_scan_first
    (bits : Word Bool) (left suffix : List (Option Bool)) :
    seekTape2Description.runConfig bits.length
        { state := 1
          tape :=
            tapeAtCells left
              (List.append (bits.map some) (none :: suffix)) } =
      { state := 1
        tape :=
          tapeAtCells
            (List.append (bits.reverse.map some) left)
            (none :: suffix) } := by
  induction bits generalizing left with
  | nil =>
      simp [MachineDescription.runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp [Nat.add_comm]]
      rw [MachineDescription.runConfig_add]
      change
        seekTape2Description.runConfig rest.length
            (seekTape2Description.runConfig 1
              { state := 1
                tape :=
                  tapeAtCells left
                    (some bit ::
                      List.append (rest.map some) (none :: suffix)) }) =
          { state := 1
            tape :=
              tapeAtCells
                (List.append ((bit :: rest).reverse.map some) left)
                (none :: suffix) }
      rw [seekTape2Description_step_bit_first left
        (List.append (rest.map some) (none :: suffix)) bit]
      simpa [List.reverse_cons, List.map_append,
        List.append_assoc] using ih (some bit :: left)

private theorem seekTape2Description_step_between
    (left right : List (Option Bool)) :
    seekTape2Description.runConfig 1
        { state := 1
          tape := tapeAtCells left (none :: right) } =
      { state := 2
        tape := tapeAtCells (none :: left) right } := by
  cases right <;>
    simp [seekTape2Description,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem seekTape2Description_step_bit_second
    (left right : List (Option Bool)) (bit : Bool) :
    seekTape2Description.runConfig 1
        { state := 2
          tape := tapeAtCells left (some bit :: right) } =
      { state := 2
        tape := tapeAtCells (some bit :: left) right } := by
  cases bit <;> cases right <;>
    simp [seekTape2Description,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem seekTape2Description_run_scan_second
    (bits : Word Bool) (left suffix : List (Option Bool)) :
    seekTape2Description.runConfig bits.length
        { state := 2
          tape :=
            tapeAtCells left
              (List.append (bits.map some) (none :: suffix)) } =
      { state := 2
        tape :=
          tapeAtCells
            (List.append (bits.reverse.map some) left)
            (none :: suffix) } := by
  induction bits generalizing left with
  | nil =>
      simp [MachineDescription.runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp [Nat.add_comm]]
      rw [MachineDescription.runConfig_add]
      change
        seekTape2Description.runConfig rest.length
            (seekTape2Description.runConfig 1
              { state := 2
                tape :=
                  tapeAtCells left
                    (some bit ::
                      List.append (rest.map some) (none :: suffix)) }) =
          { state := 2
            tape :=
              tapeAtCells
                (List.append ((bit :: rest).reverse.map some) left)
                (none :: suffix) }
      rw [seekTape2Description_step_bit_second left
        (List.append (rest.map some) (none :: suffix)) bit]
      simpa [List.reverse_cons, List.map_append,
        List.append_assoc] using ih (some bit :: left)

private theorem seekTape2Description_run_finish
    (bit : Bool) (left suffix : List (Option Bool)) :
    seekTape2Description.runConfig 2
        { state := 2
          tape := tapeAtCells (some bit :: left) (none :: suffix) } =
      { state := seekTape2Description.halt
        tape := tapeAtCells (some bit :: left) (none :: suffix) } := by
  cases bit <;> cases left <;> cases suffix <;>
    simp [seekTape2Description,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      Tape.moveRight]

theorem seekTape2Description_run_to_second
    (firstBit : Bool) (firstRest : Word Bool)
    (secondBit : Bool) (secondRest : Word Bool)
    (left suffix : List (Option Bool)) :
    seekTape2Description.runConfig
        (1 + ((firstBit :: firstRest).length +
          (1 + ((secondBit :: secondRest).length + 2))))
        { state := seekTape2Description.start
          tape :=
            tapeAtCells left
              (none ::
                List.append ((firstBit :: firstRest).map some)
                  (none ::
                    List.append ((secondBit :: secondRest).map some)
                      (none :: suffix))) } =
      { state := seekTape2Description.halt
        tape :=
          tapeAtCells
            (List.append ((secondBit :: secondRest).reverse.map some)
              (none ::
                List.append ((firstBit :: firstRest).reverse.map some)
                  (none :: left)))
            (none :: suffix) } := by
  rw [MachineDescription.runConfig_add]
  rw [seekTape2Description_step_entry]
  rw [MachineDescription.runConfig_add]
  rw [seekTape2Description_run_scan_first]
  rw [MachineDescription.runConfig_add]
  rw [seekTape2Description_step_between]
  rw [MachineDescription.runConfig_add]
  rw [seekTape2Description_run_scan_second]
  rcases reverse_map_some_append_exists_cons secondBit secondRest
      (none ::
        List.append ((firstBit :: firstRest).reverse.map some)
          (none :: left)) with
    ⟨head, tail, hleft⟩
  rw [hleft]
  exact seekTape2Description_run_finish head tail suffix

theorem seekTape2Description_haltsFromTape
    (firstBit : Bool) (firstRest : Word Bool)
    (secondBit : Bool) (secondRest : Word Bool)
    (left suffix : List (Option Bool)) :
    seekTape2Description.HaltsFromTape
      (tapeAtCells left
        (none ::
          List.append ((firstBit :: firstRest).map some)
            (none ::
              List.append ((secondBit :: secondRest).map some)
                (none :: suffix))))
      (tapeAtCells
        (List.append ((secondBit :: secondRest).reverse.map some)
          (none ::
            List.append ((firstBit :: firstRest).reverse.map some)
              (none :: left)))
        (none :: suffix)) := by
  refine
    ⟨1 + ((firstBit :: firstRest).length +
      (1 + ((secondBit :: secondRest).length + 2))), ?_⟩
  constructor <;>
    rw [seekTape2Description_run_to_second]

theorem seekTape2Description_contract_three :
    CursorRoutineContract
      (fun logical physical =>
        exists T : Tape Bool, exists U : Tape Bool,
        exists V : Tape Bool,
          logical = [T, U, V] ∧ AtEncodedBlockStart logical physical)
      (fun logical physical =>
        AtTapeSeparator logical 2 physical)
      seekTape2Description where
  subroutineReady := seekTape2Description_subroutineReady
  realizes := by
    intro logical Tin hsource
    rcases hsource with ⟨T, U, V, hlogical, hstart⟩
    subst hlogical
    rcases logicalTapeBits_exists_cons T with
      ⟨firstBit, firstRest, hfirstBits⟩
    rcases logicalTapeBits_exists_cons U with
      ⟨secondBit, secondRest, hsecondBits⟩
    rcases encodedStructuredTapeCells_startsWith_separator [V] with
      ⟨suffix, hsuffix⟩
    let Tout :=
      tapeAtEncodedSplit
        (List.append
          (List.append
            (List.append tapeSeparatorCells (logicalTapeCode T))
            tapeSeparatorCells)
          (logicalTapeCode U))
        (encodedStructuredTapeCells [V])
    exists Tout
    constructor
    · rcases hstart with ⟨_hle, hTin⟩
      rw [hTin]
      have hrun :=
        seekTape2Description_haltsFromTape
          firstBit firstRest secondBit secondRest [] suffix
      simpa [Tout, tapeAtEncodedSplit, encodedPrefixBeforeTape,
        encodedSuffixFromTape, logicalTapeCode_eq_map_some T,
        logicalTapeCode_eq_map_some U, hfirstBits, hsecondBits,
        hsuffix, tapeSeparatorCells, List.reverse_append,
        List.map_reverse, List.append_assoc] using hrun
    · refine ⟨?_, ?_⟩
      · change 2 ≤ 3
        decide
      simp [Tout, tapeAtEncodedSplit, encodedPrefixBeforeTape,
        encodedSuffixFromTape, List.append_assoc]

/--
Moving right once from an existing tape separator enters that tape segment.
This is the first concrete cursor-to-cursor routine used by later seek
machines.
-/
theorem cursorMoveRightDescription_contract_separator_to_segmentEntry
    (tapeIndex : Nat) :
    CursorRoutineContract
      (fun logical physical =>
        AtExistingTapeSeparator logical tapeIndex physical)
      (fun logical physical =>
        AtTapeSegmentEntry logical tapeIndex physical)
      (cursorMoveOnceDescription Direction.right) where
  subroutineReady :=
    cursorMoveOnceDescription_subroutineReady Direction.right
  realizes := by
    intro logical Tin hsource
    rcases hsource with ⟨hseparator, T, rest, hdrop⟩
    exists Tape.move Direction.right Tin
    constructor
    · exact cursorMoveOnceDescription_haltsFromTape Direction.right Tin
    · rcases hseparator with ⟨_hle, hTin⟩
      refine ⟨T, rest, hdrop, ?_⟩
      rw [hTin]
      have hmove :
          Tape.move Direction.right
            (tapeAtCells
              (encodedPrefixBeforeTape logical tapeIndex).reverse
              (none ::
                List.append (logicalTapeCode T)
                  (encodedStructuredTapeCells rest))) =
            tapeAtCells
              (none ::
                (encodedPrefixBeforeTape logical tapeIndex).reverse)
              (List.append (logicalTapeCode T)
                (encodedStructuredTapeCells rest)) := by
        cases hcells :
            List.append (logicalTapeCode T)
              (encodedStructuredTapeCells rest) <;>
          rfl
      simpa [tapeAtEncodedSplit, encodedSuffixFromTape, hdrop,
        tapeSeparatorCells, List.reverse_append] using hmove

/--
Scan right through encoded logical cells until the two-cell head marker is
found.  The machine halts back on the first marker cell.
-/
def cursorScanToHeadMarkerDescription : MachineDescription where
  stateCount := 4
  start := 0
  halt := 3
  transitions :=
    [ { source := 0
        read := some false
        write := some false
        move := Direction.right
        target := 1 }
    , { source := 0
        read := some true
        write := some true
        move := Direction.right
        target := 2 }
    , { source := 1
        read := some false
        write := some false
        move := Direction.right
        target := 0 }
    , { source := 1
        read := some true
        write := some true
        move := Direction.right
        target := 0 }
    , { source := 2
        read := some false
        write := some false
        move := Direction.right
        target := 0 }
    , { source := 2
        read := some true
        write := some true
        move := Direction.left
        target := 3 } ]

theorem cursorScanToHeadMarkerDescription_wellFormed :
    cursorScanToHeadMarkerDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := cursorScanToHeadMarkerDescription.transitions)
      (stateCount := cursorScanToHeadMarkerDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := cursorScanToHeadMarkerDescription.transitions)
      (by decide)

theorem cursorScanToHeadMarkerDescription_haltTransitionFree :
    cursorScanToHeadMarkerDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := cursorScanToHeadMarkerDescription.transitions)
    (state := cursorScanToHeadMarkerDescription.halt)
    (by decide)

theorem cursorScanToHeadMarkerDescription_subroutineReady :
    cursorScanToHeadMarkerDescription.SubroutineReady :=
  ⟨cursorScanToHeadMarkerDescription_wellFormed,
    cursorScanToHeadMarkerDescription_haltTransitionFree⟩

private theorem cursorScanToHeadMarkerDescription_run_cell
    (cell : Option Bool) (left suffix : List (Option Bool)) :
    cursorScanToHeadMarkerDescription.runConfig 2
        { state := cursorScanToHeadMarkerDescription.start
          tape :=
            tapeAtCells left
              (List.append (logicalCellCode cell) suffix) } =
      { state := cursorScanToHeadMarkerDescription.start
        tape :=
          tapeAtCells
            (List.append (logicalCellCode cell).reverse left)
            suffix } := by
  cases cell with
  | none =>
      cases suffix <;>
        simp [cursorScanToHeadMarkerDescription,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition,
          MachineDescription.Matches, logicalCellCode,
          tapeAtCells, Tape.read, Tape.write, Tape.move,
          Tape.moveRight]
  | some bit =>
      cases bit <;> cases suffix <;>
        simp [cursorScanToHeadMarkerDescription,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition,
          MachineDescription.Matches, logicalCellCode,
          tapeAtCells, Tape.read, Tape.write, Tape.move,
          Tape.moveRight]

private theorem cursorScanToHeadMarkerDescription_run_cell_assoc
    (cell : Option Bool) (left middle suffix : List (Option Bool)) :
    cursorScanToHeadMarkerDescription.runConfig 2
        { state := cursorScanToHeadMarkerDescription.start
          tape :=
            tapeAtCells left
              (List.append
                (List.append (logicalCellCode cell) middle)
                suffix) } =
      { state := cursorScanToHeadMarkerDescription.start
        tape :=
          tapeAtCells
            (List.append (logicalCellCode cell).reverse left)
            (List.append middle suffix) } := by
  simpa [List.append_assoc] using
    cursorScanToHeadMarkerDescription_run_cell cell left
      (List.append middle suffix)

private theorem cursorScanToHeadMarkerDescription_run_cells
    (cells : List (Option Bool))
    (left suffix : List (Option Bool)) :
    cursorScanToHeadMarkerDescription.runConfig (2 * cells.length)
        { state := cursorScanToHeadMarkerDescription.start
          tape :=
            tapeAtCells left
              (List.append (logicalCellListCode cells)
                (List.append headMarkerCells suffix)) } =
      { state := cursorScanToHeadMarkerDescription.start
        tape :=
          tapeAtCells
            (List.append (logicalCellListCode cells).reverse left)
            (List.append headMarkerCells suffix) } := by
  induction cells generalizing left with
  | nil =>
      simp [MachineDescription.runConfig, logicalCellListCode]
  | cons cell rest ih =>
      rw [show 2 * (cell :: rest).length =
          2 + 2 * rest.length by
        simp [Nat.mul_add, Nat.add_comm]]
      rw [MachineDescription.runConfig_add]
      simp only [logicalCellListCode_cons]
      rw [cursorScanToHeadMarkerDescription_run_cell_assoc]
      simpa [List.reverse_append, List.append_assoc] using
          ih (List.append (logicalCellCode cell).reverse left)

private theorem cursorScanToHeadMarkerDescription_run_marker
    (left suffix : List (Option Bool)) :
    cursorScanToHeadMarkerDescription.runConfig 2
        { state := cursorScanToHeadMarkerDescription.start
          tape :=
            tapeAtCells left
              (List.append headMarkerCells suffix) } =
      { state := cursorScanToHeadMarkerDescription.halt
        tape :=
          tapeAtCells left
            (List.append headMarkerCells suffix) } := by
  cases suffix <;>
    simp [cursorScanToHeadMarkerDescription,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      headMarkerCells, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft, Tape.moveRight]

theorem cursorScanToHeadMarkerDescription_run_to_marker
    (cells : List (Option Bool))
    (left suffix : List (Option Bool)) :
    cursorScanToHeadMarkerDescription.runConfig
        (2 * cells.length + 2)
        { state := cursorScanToHeadMarkerDescription.start
          tape :=
            tapeAtCells left
              (List.append (logicalCellListCode cells)
                (List.append headMarkerCells suffix)) } =
      { state := cursorScanToHeadMarkerDescription.halt
        tape :=
          tapeAtCells
            (List.append (logicalCellListCode cells).reverse left)
            (List.append headMarkerCells suffix) } := by
  rw [MachineDescription.runConfig_add]
  rw [cursorScanToHeadMarkerDescription_run_cells]
  rw [cursorScanToHeadMarkerDescription_run_marker]

theorem cursorScanToHeadMarkerDescription_haltsFromTape
    (cells : List (Option Bool))
    (left suffix : List (Option Bool)) :
    cursorScanToHeadMarkerDescription.HaltsFromTape
      (tapeAtCells left
        (List.append (logicalCellListCode cells)
          (List.append headMarkerCells suffix)))
      (tapeAtCells
        (List.append (logicalCellListCode cells).reverse left)
        (List.append headMarkerCells suffix)) := by
  refine ⟨2 * cells.length + 2, ?_⟩
  constructor <;>
    rw [cursorScanToHeadMarkerDescription_run_to_marker]

theorem cursorScanToHeadMarkerDescription_contract
    (tapeIndex : Nat) :
    CursorRoutineContract
      (fun logical physical =>
        AtTapeSegmentEntry logical tapeIndex physical)
      (fun logical physical =>
        AtTapeHeadMarker logical tapeIndex physical)
      cursorScanToHeadMarkerDescription where
  subroutineReady :=
    cursorScanToHeadMarkerDescription_subroutineReady
  realizes := by
    intro logical Tin hentry
    rcases hentry with ⟨T, rest, hdrop, hTin⟩
    let suffix :=
      List.append (logicalCellCode T.head)
        (List.append (logicalCellListCode T.right)
          (encodedStructuredTapeCells rest))
    let Tout :=
      tapeAtEncodedSplit
        (List.append
          (encodedPrefixBeforeTape logical tapeIndex)
          (List.append tapeSeparatorCells
            (logicalCellListCode T.left.reverse)))
        (List.append headMarkerCells suffix)
    exists Tout
    constructor
    · rw [hTin]
      have hrun :=
        cursorScanToHeadMarkerDescription_haltsFromTape
          T.left.reverse
          (List.append
            (encodedPrefixBeforeTape logical tapeIndex)
            tapeSeparatorCells).reverse
          suffix
      simpa [Tout, suffix, tapeAtEncodedSplit, logicalTapeCode,
        List.reverse_append, List.append_assoc] using hrun
    · exact ⟨T, rest, hdrop, rfl⟩

/-- Move from the first head-marker cell to the first encoded head-cell bit. -/
def cursorMoveHeadMarkerToCellDescription : MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ { source := 0
        read := some true
        write := some true
        move := Direction.right
        target := 1 }
    , { source := 1
        read := some true
        write := some true
        move := Direction.right
        target := 2 } ]

theorem cursorMoveHeadMarkerToCellDescription_wellFormed :
    cursorMoveHeadMarkerToCellDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := cursorMoveHeadMarkerToCellDescription.transitions)
      (stateCount := cursorMoveHeadMarkerToCellDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := cursorMoveHeadMarkerToCellDescription.transitions)
      (by decide)

theorem cursorMoveHeadMarkerToCellDescription_haltTransitionFree :
    cursorMoveHeadMarkerToCellDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := cursorMoveHeadMarkerToCellDescription.transitions)
    (state := cursorMoveHeadMarkerToCellDescription.halt)
    (by decide)

theorem cursorMoveHeadMarkerToCellDescription_subroutineReady :
    cursorMoveHeadMarkerToCellDescription.SubroutineReady :=
  ⟨cursorMoveHeadMarkerToCellDescription_wellFormed,
    cursorMoveHeadMarkerToCellDescription_haltTransitionFree⟩

theorem cursorMoveHeadMarkerToCellDescription_run
    (left suffix : List (Option Bool)) :
    cursorMoveHeadMarkerToCellDescription.runConfig 2
        { state := cursorMoveHeadMarkerToCellDescription.start
          tape :=
            tapeAtCells left
              (List.append headMarkerCells suffix) } =
      { state := cursorMoveHeadMarkerToCellDescription.halt
        tape :=
          tapeAtCells (List.append headMarkerCells.reverse left)
            suffix } := by
  cases suffix <;>
    simp [cursorMoveHeadMarkerToCellDescription,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      headMarkerCells, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveRight]

theorem cursorMoveHeadMarkerToCellDescription_haltsFromTape
    (left suffix : List (Option Bool)) :
    cursorMoveHeadMarkerToCellDescription.HaltsFromTape
      (tapeAtCells left (List.append headMarkerCells suffix))
      (tapeAtCells (List.append headMarkerCells.reverse left)
        suffix) := by
  refine ⟨2, ?_⟩
  constructor <;>
    rw [cursorMoveHeadMarkerToCellDescription_run]

theorem cursorMoveHeadMarkerToCellDescription_contract
    (tapeIndex : Nat) :
    CursorRoutineContract
      (fun logical physical =>
        AtTapeHeadMarker logical tapeIndex physical)
      (fun logical physical =>
        AtTapeHeadCellCode logical tapeIndex physical)
      cursorMoveHeadMarkerToCellDescription where
  subroutineReady :=
    cursorMoveHeadMarkerToCellDescription_subroutineReady
  realizes := by
    intro logical Tin hmarker
    rcases hmarker with ⟨T, rest, hdrop, hTin⟩
    let suffix :=
      List.append (logicalCellCode T.head)
        (List.append (logicalCellListCode T.right)
          (encodedStructuredTapeCells rest))
    let Tout :=
      tapeAtEncodedSplit
        (List.append
          (encodedPrefixBeforeTape logical tapeIndex)
          (List.append tapeSeparatorCells
            (List.append (logicalCellListCode T.left.reverse)
              headMarkerCells)))
        suffix
    exists Tout
    constructor
    · rw [hTin]
      have hrun :=
        cursorMoveHeadMarkerToCellDescription_haltsFromTape
          (List.append
            (encodedPrefixBeforeTape logical tapeIndex)
            (List.append tapeSeparatorCells
              (logicalCellListCode T.left.reverse))).reverse
          suffix
      simpa [Tout, suffix, tapeAtEncodedSplit,
        List.reverse_append, List.append_assoc] using hrun
    · exact ⟨T, rest, hdrop, rfl⟩

def logicalCellCodeFirstPhysical
    (cell : Option Bool) : Option Bool :=
  match cell with
  | none => some false
  | some false => some false
  | some true => some true

def logicalCellCodeSecondPhysical
    (cell : Option Bool) : Option Bool :=
  match cell with
  | none => some false
  | some false => some true
  | some true => some false

theorem logicalCellCode_eq_pair
    (cell : Option Bool) :
    logicalCellCode cell =
      [logicalCellCodeFirstPhysical cell,
        logicalCellCodeSecondPhysical cell] := by
  cases cell with
  | none => rfl
  | some bit =>
      cases bit <;> rfl

/--
Check that the encoded head-cell code equals the expected logical cell and
halt back on the first bit of that code.
-/
def readHeadCellCodeDescription
    (expected : Option Bool) : MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ { source := 0
        read := logicalCellCodeFirstPhysical expected
        write := logicalCellCodeFirstPhysical expected
        move := Direction.right
        target := 1 }
    , { source := 1
        read := logicalCellCodeSecondPhysical expected
        write := logicalCellCodeSecondPhysical expected
        move := Direction.left
        target := 2 } ]

theorem readHeadCellCodeDescription_wellFormed
    (expected : Option Bool) :
    (readHeadCellCodeDescription expected).WellFormed := by
  cases expected with
  | none =>
      refine ⟨by decide, by decide, by decide, ?_, ?_⟩
      · exact transition_wellFormed_of_all
          (l := (readHeadCellCodeDescription none).transitions)
          (stateCount := (readHeadCellCodeDescription none).stateCount)
          (by decide)
      · exact transition_deterministic_of_all
          (l := (readHeadCellCodeDescription none).transitions)
          (by decide)
  | some bit =>
      cases bit
      · refine ⟨by decide, by decide, by decide, ?_, ?_⟩
        · exact transition_wellFormed_of_all
            (l := (readHeadCellCodeDescription (some false)).transitions)
            (stateCount :=
              (readHeadCellCodeDescription (some false)).stateCount)
            (by decide)
        · exact transition_deterministic_of_all
            (l := (readHeadCellCodeDescription (some false)).transitions)
            (by decide)
      · refine ⟨by decide, by decide, by decide, ?_, ?_⟩
        · exact transition_wellFormed_of_all
            (l := (readHeadCellCodeDescription (some true)).transitions)
            (stateCount :=
              (readHeadCellCodeDescription (some true)).stateCount)
            (by decide)
        · exact transition_deterministic_of_all
            (l := (readHeadCellCodeDescription (some true)).transitions)
            (by decide)

theorem readHeadCellCodeDescription_haltTransitionFree
    (expected : Option Bool) :
    (readHeadCellCodeDescription expected).HaltTransitionFree := by
  cases expected with
  | none =>
      exact transition_notFrom_of_all
        (l := (readHeadCellCodeDescription none).transitions)
        (state := (readHeadCellCodeDescription none).halt)
        (by decide)
  | some bit =>
      cases bit
      · exact transition_notFrom_of_all
          (l := (readHeadCellCodeDescription (some false)).transitions)
          (state := (readHeadCellCodeDescription (some false)).halt)
          (by decide)
      · exact transition_notFrom_of_all
          (l := (readHeadCellCodeDescription (some true)).transitions)
          (state := (readHeadCellCodeDescription (some true)).halt)
          (by decide)

theorem readHeadCellCodeDescription_subroutineReady
    (expected : Option Bool) :
    (readHeadCellCodeDescription expected).SubroutineReady :=
  ⟨readHeadCellCodeDescription_wellFormed expected,
    readHeadCellCodeDescription_haltTransitionFree expected⟩

theorem readHeadCellCodeDescription_run
    (expected : Option Bool)
    (left suffix : List (Option Bool)) :
    (readHeadCellCodeDescription expected).runConfig 2
        { state := (readHeadCellCodeDescription expected).start
          tape :=
            tapeAtCells left
              (List.append (logicalCellCode expected) suffix) } =
      { state := (readHeadCellCodeDescription expected).halt
        tape :=
          tapeAtCells left
            (List.append (logicalCellCode expected) suffix) } := by
  cases expected with
  | none =>
      cases suffix <;>
        simp [readHeadCellCodeDescription, logicalCellCode,
          logicalCellCodeFirstPhysical,
          logicalCellCodeSecondPhysical,
          MachineDescription.runConfig,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition,
          MachineDescription.Matches, tapeAtCells, Tape.read,
          Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  | some bit =>
      cases bit <;> cases suffix <;>
        simp [readHeadCellCodeDescription, logicalCellCode,
          logicalCellCodeFirstPhysical,
          logicalCellCodeSecondPhysical,
          MachineDescription.runConfig,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition,
          MachineDescription.Matches, tapeAtCells, Tape.read,
          Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem readHeadCellCodeDescription_haltsFromTape
    (expected : Option Bool)
    (left suffix : List (Option Bool)) :
    (readHeadCellCodeDescription expected).HaltsFromTape
      (tapeAtCells left
        (List.append (logicalCellCode expected) suffix))
      (tapeAtCells left
        (List.append (logicalCellCode expected) suffix)) := by
  refine ⟨2, ?_⟩
  constructor <;>
    rw [readHeadCellCodeDescription_run]

theorem readHeadCellCodeDescription_contract
    (tapeIndex : Nat) (expected : Option Bool) :
    CursorRoutineContract
      (fun logical physical =>
        AtTapeHeadCellCodeWithRead logical tapeIndex expected physical)
      (fun logical physical =>
        AtTapeHeadCellCode logical tapeIndex physical)
      (readHeadCellCodeDescription expected) where
  subroutineReady :=
    readHeadCellCodeDescription_subroutineReady expected
  realizes := by
    intro logical Tin hsource
    rcases hsource with ⟨T, rest, hdrop, hread, hTin⟩
    let suffix :=
      List.append (logicalCellListCode T.right)
        (encodedStructuredTapeCells rest)
    let Tout :=
      tapeAtEncodedSplit
        (List.append
          (encodedPrefixBeforeTape logical tapeIndex)
          (List.append tapeSeparatorCells
            (List.append (logicalCellListCode T.left.reverse)
              headMarkerCells)))
        (List.append (logicalCellCode T.head) suffix)
    exists Tout
    constructor
    · have hhead : T.head = expected := hread
      rw [hTin, hhead]
      have hrun :=
        readHeadCellCodeDescription_haltsFromTape expected
          (List.append
            (encodedPrefixBeforeTape logical tapeIndex)
            (List.append tapeSeparatorCells
              (List.append (logicalCellListCode T.left.reverse)
                headMarkerCells))).reverse
          suffix
      simpa [Tout, suffix, tapeAtEncodedSplit, hhead,
        List.reverse_append, List.append_assoc] using hrun
    · exact ⟨T, rest, hdrop, rfl⟩

/--
Overwrite the encoded two-bit head-cell code and halt back on its first bit.
The physical cursor location is preserved; the represented logical tape head
cell changes.
-/
def writeHeadCellCodeDescription
    (cell : Option Bool) : MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ { source := 0
        read := none
        write := logicalCellCodeFirstPhysical cell
        move := Direction.right
        target := 1 }
    , { source := 0
        read := some false
        write := logicalCellCodeFirstPhysical cell
        move := Direction.right
        target := 1 }
    , { source := 0
        read := some true
        write := logicalCellCodeFirstPhysical cell
        move := Direction.right
        target := 1 }
    , { source := 1
        read := none
        write := logicalCellCodeSecondPhysical cell
        move := Direction.left
        target := 2 }
    , { source := 1
        read := some false
        write := logicalCellCodeSecondPhysical cell
        move := Direction.left
        target := 2 }
    , { source := 1
        read := some true
        write := logicalCellCodeSecondPhysical cell
        move := Direction.left
        target := 2 } ]

theorem writeHeadCellCodeDescription_wellFormed
    (cell : Option Bool) :
    (writeHeadCellCodeDescription cell).WellFormed := by
  cases cell with
  | none =>
      refine ⟨by decide, by decide, by decide, ?_, ?_⟩
      · exact transition_wellFormed_of_all
          (l := (writeHeadCellCodeDescription none).transitions)
          (stateCount := (writeHeadCellCodeDescription none).stateCount)
          (by decide)
      · exact transition_deterministic_of_all
          (l := (writeHeadCellCodeDescription none).transitions)
          (by decide)
  | some bit =>
      cases bit
      · refine ⟨by decide, by decide, by decide, ?_, ?_⟩
        · exact transition_wellFormed_of_all
            (l := (writeHeadCellCodeDescription (some false)).transitions)
            (stateCount :=
              (writeHeadCellCodeDescription (some false)).stateCount)
            (by decide)
        · exact transition_deterministic_of_all
            (l := (writeHeadCellCodeDescription (some false)).transitions)
            (by decide)
      · refine ⟨by decide, by decide, by decide, ?_, ?_⟩
        · exact transition_wellFormed_of_all
            (l := (writeHeadCellCodeDescription (some true)).transitions)
            (stateCount :=
              (writeHeadCellCodeDescription (some true)).stateCount)
            (by decide)
        · exact transition_deterministic_of_all
            (l := (writeHeadCellCodeDescription (some true)).transitions)
            (by decide)

theorem writeHeadCellCodeDescription_haltTransitionFree
    (cell : Option Bool) :
    (writeHeadCellCodeDescription cell).HaltTransitionFree := by
  cases cell with
  | none =>
      exact transition_notFrom_of_all
        (l := (writeHeadCellCodeDescription none).transitions)
        (state := (writeHeadCellCodeDescription none).halt)
        (by decide)
  | some bit =>
      cases bit
      · exact transition_notFrom_of_all
          (l := (writeHeadCellCodeDescription (some false)).transitions)
          (state := (writeHeadCellCodeDescription (some false)).halt)
          (by decide)
      · exact transition_notFrom_of_all
          (l := (writeHeadCellCodeDescription (some true)).transitions)
          (state := (writeHeadCellCodeDescription (some true)).halt)
          (by decide)

theorem writeHeadCellCodeDescription_subroutineReady
    (cell : Option Bool) :
    (writeHeadCellCodeDescription cell).SubroutineReady :=
  ⟨writeHeadCellCodeDescription_wellFormed cell,
    writeHeadCellCodeDescription_haltTransitionFree cell⟩

theorem writeHeadCellCodeDescription_run
    (oldCell newCell : Option Bool)
    (left suffix : List (Option Bool)) :
    (writeHeadCellCodeDescription newCell).runConfig 2
        { state := (writeHeadCellCodeDescription newCell).start
          tape :=
            tapeAtCells left
              (List.append (logicalCellCode oldCell) suffix) } =
      { state := (writeHeadCellCodeDescription newCell).halt
        tape :=
          tapeAtCells left
            (List.append (logicalCellCode newCell) suffix) } := by
  cases oldCell with
  | none =>
      cases newCell with
      | none =>
          cases suffix <;>
            simp [writeHeadCellCodeDescription, logicalCellCode,
              logicalCellCodeFirstPhysical,
              logicalCellCodeSecondPhysical,
              MachineDescription.runConfig,
              MachineDescription.stepConfig,
              MachineDescription.lookupTransition,
              MachineDescription.Matches, tapeAtCells, Tape.read,
              Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
      | some newBit =>
          cases newBit <;> cases suffix <;>
            simp [writeHeadCellCodeDescription, logicalCellCode,
              logicalCellCodeFirstPhysical,
              logicalCellCodeSecondPhysical,
              MachineDescription.runConfig,
              MachineDescription.stepConfig,
              MachineDescription.lookupTransition,
              MachineDescription.Matches, tapeAtCells, Tape.read,
              Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  | some oldBit =>
      cases oldBit <;>
        cases newCell with
        | none =>
            cases suffix <;>
              simp [writeHeadCellCodeDescription, logicalCellCode,
                logicalCellCodeFirstPhysical,
                logicalCellCodeSecondPhysical,
                MachineDescription.runConfig,
                MachineDescription.stepConfig,
                MachineDescription.lookupTransition,
                MachineDescription.Matches, tapeAtCells, Tape.read,
                Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
        | some newBit =>
            cases newBit <;> cases suffix <;>
              simp [writeHeadCellCodeDescription, logicalCellCode,
                logicalCellCodeFirstPhysical,
                logicalCellCodeSecondPhysical,
                MachineDescription.runConfig,
                MachineDescription.stepConfig,
                MachineDescription.lookupTransition,
                MachineDescription.Matches, tapeAtCells, Tape.read,
                Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem writeHeadCellCodeDescription_haltsFromTape
    (oldCell newCell : Option Bool)
    (left suffix : List (Option Bool)) :
    (writeHeadCellCodeDescription newCell).HaltsFromTape
      (tapeAtCells left
        (List.append (logicalCellCode oldCell) suffix))
      (tapeAtCells left
        (List.append (logicalCellCode newCell) suffix)) := by
  refine ⟨2, ?_⟩
  constructor <;>
    rw [writeHeadCellCodeDescription_run]

theorem writeHeadCellCodeDescription_contract
    (tapeIndex : Nat) (cell : Option Bool) :
    CursorRoutineContract
      (fun logical physical =>
        AtTapeHeadCellCode logical tapeIndex physical)
      (fun logical physical =>
        AtTapeHeadCellCode
          ((PhysicalPrimitive.writeHeadCell tapeIndex cell).apply logical)
          tapeIndex physical)
      (writeHeadCellCodeDescription cell) where
  subroutineReady :=
    writeHeadCellCodeDescription_subroutineReady cell
  realizes := by
    intro logical Tin hsource
    rcases hsource with ⟨T, rest, hdrop, hTin⟩
    let suffix :=
      List.append (logicalCellListCode T.right)
        (encodedStructuredTapeCells rest)
    let Tout :=
      tapeAtEncodedSplit
        (List.append
          (encodedPrefixBeforeTape logical tapeIndex)
          (List.append tapeSeparatorCells
            (List.append (logicalCellListCode T.left.reverse)
              headMarkerCells)))
        (List.append (logicalCellCode cell) suffix)
    exists Tout
    constructor
    · rw [hTin]
      have hrun :=
        writeHeadCellCodeDescription_haltsFromTape
          T.head cell
          (List.append
            (encodedPrefixBeforeTape logical tapeIndex)
            (List.append tapeSeparatorCells
              (List.append (logicalCellListCode T.left.reverse)
                headMarkerCells))).reverse
          suffix
      simpa [Tout, suffix, tapeAtEncodedSplit,
        List.reverse_append, List.append_assoc] using hrun
    · have htapeAt :
          Description.tapeAt logical tapeIndex = T :=
        description_tapeAt_eq_of_drop_eq_cons hdrop
      refine ⟨Tape.write cell T, rest, ?_, ?_⟩
      · simpa [PhysicalPrimitive.apply, htapeAt] using
          replaceTapeAt_drop_eq_of_drop_eq_cons
            (replacement := Tape.write cell T) hdrop
      · simp [Tout, suffix, tapeAtEncodedSplit,
          PhysicalPrimitive.apply, htapeAt,
          encodedPrefixBeforeTape_replaceTapeAt_eq, Tape.write,
          List.append_assoc]

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
