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

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
