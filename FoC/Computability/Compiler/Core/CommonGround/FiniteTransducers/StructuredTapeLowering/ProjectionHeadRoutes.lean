import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredInputMaterializer
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTableChecks
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.ConcreteRefresh
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.Composition
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.Projection
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.ThreeTapeHelpers
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.ThreeTapeTactic

set_option doc.verso true

/-!
# Structured selected-head projection routes

The base projection module proves the selected singleton decoder route: the
selected logical tape is the last encoded structured tape segment, so the
generated bit scanner halts on the blank separator immediately after that
segment.

This module records the matching selected-head route.  The selected logical
tape may have additional encoded structured segments to its right.  The
scanner proof is still the same generated finite-control scanner, but its
target carries a padding tail made from the remaining structured block.  A
cleanup machine over this padded target is therefore enough to build the full
selected-head decoder spec, and from there the tape
0/1/2 segment normalizers and projectors.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

/-!
## Padded selected-head scanner target

The scanner starts one cell to the right of the selected segment separator.
For a singleton selected segment, the scanner consumes the encoded logical tape
and sees the final separator blank.  For a selected head, the same separator is
followed by the remaining encoded structured segments.  The definitions below
name the tail after that separator so later routes can avoid unfolding the
whole structured encoding.
-/

/--
Cells that remain to the right of the first separator in an encoded structured
block.

For the empty block this is empty: the block itself is just the separator.
For a nonempty block it is the selected tape code followed by the rest of the
encoded structured block.
-/
def selectedSegmentLogicalTapeDecoderRestPadding :
    List (Tape Bool) -> List (Option Bool)
  | [] => []
  | T :: rest =>
      List.append (logicalTapeCode T) (encodedStructuredTapeCells rest)

/-- The empty structured rest contributes no padding after its separator. -/
theorem selectedSegmentLogicalTapeDecoderRestPadding_nil :
    selectedSegmentLogicalTapeDecoderRestPadding [] = [] := by
  rfl

/--
The nonempty structured rest contributes the next tape code plus the remaining
structured block after its opening separator.
-/
theorem selectedSegmentLogicalTapeDecoderRestPadding_cons
    (T : Tape Bool) (rest : List (Tape Bool)) :
    selectedSegmentLogicalTapeDecoderRestPadding (T :: rest) =
      List.append (logicalTapeCode T) (encodedStructuredTapeCells rest) := by
  rfl

/--
Every encoded structured block starts with the separator blank, and
{name}`selectedSegmentLogicalTapeDecoderRestPadding` names the remaining tail.
-/
theorem encodedStructuredTapeCells_eq_none_cons_restPadding
    (rest : List (Tape Bool)) :
    encodedStructuredTapeCells rest =
      none :: selectedSegmentLogicalTapeDecoderRestPadding rest := by
  cases rest with
  | nil =>
      rfl
  | cons T rest =>
      rfl

/--
Equivalent append-shaped view of the rest block, useful when a later proof is
already stated in terms of {name}`tapeSeparatorCells`.
-/
theorem encodedStructuredTapeCells_eq_separator_append_restPadding
    (rest : List (Tape Bool)) :
    encodedStructuredTapeCells rest =
      List.append tapeSeparatorCells
        (selectedSegmentLogicalTapeDecoderRestPadding rest) := by
  rw [encodedStructuredTapeCells_eq_none_cons_restPadding]
  rfl

/-- The rest padding for a singleton specialization is empty. -/
theorem selectedSegmentLogicalTapeDecoderRestPadding_singleton :
    selectedSegmentLogicalTapeDecoderRestPadding [] = [] := by
  rfl

/--
Target tape produced by the selected-segment scanner when the selected segment
has an encoded structured suffix to its right.

The generated scanner preserves the right-hand suffix as padding; only the
selected logical tape code is decoded into optional output cells.
-/
def selectedSegmentLogicalTapeDecoderHeadTargetTape
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) : Tape Bool :=
  FSTStatefulOptionAppendTargetTapeFromLeftWithPadding
    selectedSegmentLogicalTapeDecoderNext
    selectedSegmentLogicalTapeDecoderEmit
    selectedSegmentLogicalTapeDecoderStart
    (logicalTapeBits (guardLogicalTape target))
    (none :: encodedPrefix.reverse)
    (selectedSegmentLogicalTapeDecoderRestPadding rest)

/-- The selected-head target is definitionally the singleton target when no rest remains. -/
theorem selectedSegmentLogicalTapeDecoderHeadTargetTape_nil
    (target : Tape Bool) (encodedPrefix : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderHeadTargetTape
        target [] encodedPrefix =
      selectedSegmentLogicalTapeDecoderTargetTape target encodedPrefix := by
  simp [selectedSegmentLogicalTapeDecoderHeadTargetTape,
    selectedSegmentLogicalTapeDecoderTargetTape,
    selectedSegmentLogicalTapeDecoderRestPadding,
    FSTStatefulOptionAppendTargetTapeFromLeftWithPadding,
    FSTStatefulOptionAppendTargetTapeFromLeft,
    statefulOptionAppendWriteTargetTapeAtBlank,
    tapeAtCells]

/--
Left stack of the padded selected-head scanner target.

It is the same left stack as the singleton scanner target: the separator just
crossed, the reversed physical decoder footprint, and the encoded prefix.
-/
theorem selectedSegmentLogicalTapeDecoderHeadTargetTape_left
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderHeadTargetTape
        target rest encodedPrefix).left =
      none ::
        List.append
          (statefulOptionCellsFrom selectedSegmentLogicalTapeDecoderNext
            selectedSegmentLogicalTapeDecoderEmit
            selectedSegmentLogicalTapeDecoderStart
            (logicalTapeBits (guardLogicalTape target))).reverse
          (none :: encodedPrefix.reverse) := by
  rw [selectedSegmentLogicalTapeDecoderHeadTargetTape,
    FSTStatefulOptionAppendTargetTapeFromLeftWithPadding]
  cases selectedSegmentLogicalTapeDecoderRestPadding rest <;> rfl

/-- Source shape after moving right from the selected segment separator. -/
theorem selectedSegmentLogicalTapeDecoderHead_source_after_move
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    Tape.move Direction.right
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells (guardLogicalTape target :: rest))) =
      tapeAtCells (none :: encodedPrefix.reverse)
        (List.append
          ((logicalTapeBits (guardLogicalTape target)).map some)
          (none :: selectedSegmentLogicalTapeDecoderRestPadding rest)) := by
  simp [tapeAtEncodedSplit, encodedStructuredTapeCells,
    tapeSeparatorCells, logicalTapeCode_eq_map_some, Tape.move,
    Tape.moveRight, tapeAtCells]
  rw [encodedStructuredTapeCells_eq_none_cons_restPadding rest]
  cases (List.map some (logicalTapeBits (guardLogicalTape target)) ++
      none :: selectedSegmentLogicalTapeDecoderRestPadding rest) <;> rfl

/--
The generated selected-segment scanner works unchanged for a selected head:
the remaining structured block is just padding after the separator blank.
-/
theorem selectedSegmentLogicalTapeDecoderDescription_haltsFrom_selectedHeadPayload
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDescription.HaltsFromTape
      (Tape.move Direction.right
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells (guardLogicalTape target :: rest))))
      (selectedSegmentLogicalTapeDecoderHeadTargetTape
        target rest encodedPrefix) := by
  rw [selectedSegmentLogicalTapeDecoderHead_source_after_move]
  change
    (generatedStatefulOptionAppendDescription
        selectedSegmentLogicalTapeDecoderStateCount
        selectedSegmentLogicalTapeDecoderStart
        selectedSegmentLogicalTapeDecoderNext
        selectedSegmentLogicalTapeDecoderEmit
        []).HaltsFromTape
      (tapeAtCells (none :: encodedPrefix.reverse)
        (List.append
          ((logicalTapeBits (guardLogicalTape target)).map some)
          (none :: selectedSegmentLogicalTapeDecoderRestPadding rest)))
      (selectedSegmentLogicalTapeDecoderHeadTargetTape
        target rest encodedPrefix)
  exact
    generatedStatefulOptionAppendDescription_haltsFrom_tapeAtCells_nil_withPadding
      selectedSegmentLogicalTapeDecoderStateCount
      selectedSegmentLogicalTapeDecoderStart
      selectedSegmentLogicalTapeDecoderNext
      selectedSegmentLogicalTapeDecoderEmit
      (logicalTapeBits (guardLogicalTape target))
      (none :: encodedPrefix.reverse)
      (selectedSegmentLogicalTapeDecoderRestPadding rest)
      selectedSegmentLogicalTapeDecoderStart_lt
      selectedSegmentLogicalTapeDecoderNext_lt

/-!
## Cleanup contracts

The scanner target still contains blanks from skipped physical code bits and
the untouched encoded suffix.  A cleanup machine for this padded target is the
right reusable premise for tape 0 and tape 1 projection.  The older singleton
cleanup is exactly the specialization where the structured suffix is empty.
-/

def selectedSegmentLogicalTapeDecoderPaddedCleanupLeftStack
    (target : Tape Bool) (encodedPrefix : List (Option Bool)) :
    List (Option Bool) :=
  none ::
    List.append
      (statefulOptionCellsFrom selectedSegmentLogicalTapeDecoderNext
        selectedSegmentLogicalTapeDecoderEmit
        selectedSegmentLogicalTapeDecoderStart
        (logicalTapeBits (guardLogicalTape target))).reverse
      (none :: encodedPrefix.reverse)

def selectedSegmentLogicalTapeDecoderCellShapeCleanupSourceTape
    (logical : Tape Bool) (padding : List (Option Bool))
    (encodedPrefix : List (Option Bool)) : Tape Bool :=
  FSTStatefulOptionAppendTargetTapeFromLeftWithPadding
    selectedSegmentLogicalTapeDecoderNext
    selectedSegmentLogicalTapeDecoderEmit
    selectedSegmentLogicalTapeDecoderStart
    (logicalTapeBits logical)
    (none :: encodedPrefix.reverse)
    padding

def selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
    (target : Tape Bool) (padding : List (Option Bool))
    (encodedPrefix : List (Option Bool)) : Tape Bool :=
  selectedSegmentLogicalTapeDecoderCellShapeCleanupSourceTape
    (guardLogicalTape target) padding encodedPrefix

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape_eq_cellShape
    (target : Tape Bool) (padding : List (Option Bool))
    (encodedPrefix : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
        target padding encodedPrefix =
      selectedSegmentLogicalTapeDecoderCellShapeCleanupSourceTape
        (guardLogicalTape target) padding encodedPrefix := by
  rfl

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape_eq_tapeAtCells
    (target : Tape Bool) (padding : List (Option Bool))
    (encodedPrefix : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
        target padding encodedPrefix =
      tapeAtCells
        (selectedSegmentLogicalTapeDecoderPaddedCleanupLeftStack
          target encodedPrefix)
        padding := by
  rfl

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape_left
    (target : Tape Bool) (padding : List (Option Bool))
    (encodedPrefix : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
        target padding encodedPrefix).left =
      selectedSegmentLogicalTapeDecoderPaddedCleanupLeftStack
        target encodedPrefix := by
  rw [selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape_eq_tapeAtCells]
  cases padding <;> rfl

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape_head_nil
    (target : Tape Bool) (encodedPrefix : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
        target [] encodedPrefix).head = none := by
  rfl

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape_head_cons
    (target : Tape Bool) (pad : Option Bool)
    (padding encodedPrefix : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
        target (pad :: padding) encodedPrefix).head = pad := by
  rfl

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape_right_nil
    (target : Tape Bool) (encodedPrefix : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
        target [] encodedPrefix).right = [] := by
  rfl

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape_right_cons
    (target : Tape Bool) (pad : Option Bool)
    (padding encodedPrefix : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
        target (pad :: padding) encodedPrefix).right = padding := by
  rfl

theorem selectedSegmentLogicalTapeDecoderCellCells_flatten_filterMap
    (cells : List (Option Bool)) :
    ((cells.map selectedSegmentLogicalTapeDecoderCellCells).flatten).filterMap
        (fun cell => cell) =
      cells.filterMap (fun cell => cell) := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      cases cell with
      | none =>
          simpa [selectedSegmentLogicalTapeDecoderCellCells] using ih
      | some bit =>
          cases bit <;>
            simp [selectedSegmentLogicalTapeDecoderCellCells,
              ih]

theorem selectedSegmentLogicalTapeDecoderCellCells_filterMap_flatten
    (cells : List (Option Bool)) :
    (cells.map
        ((List.filterMap fun cell => cell) ∘
          selectedSegmentLogicalTapeDecoderCellCells)).flatten =
      cells.filterMap (fun cell => cell) := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      cases cell with
      | none =>
          simpa [selectedSegmentLogicalTapeDecoderCellCells] using ih
      | some bit =>
          cases bit <;>
            simpa [selectedSegmentLogicalTapeDecoderCellCells,
              List.filterMap_append] using ih

theorem selectedSegmentLogicalTapeDecoderCellCells_filterMap_flatten_reverse
    (cells : List (Option Bool)) :
    (cells.map
        ((List.filterMap fun cell => cell) ∘
          selectedSegmentLogicalTapeDecoderCellCells)).reverse.flatten =
      (cells.filterMap (fun cell => cell)).reverse := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      cases cell with
      | none =>
          simpa [selectedSegmentLogicalTapeDecoderCellCells] using ih
      | some bit =>
          cases bit <;>
            simp [selectedSegmentLogicalTapeDecoderCellCells,
              ih]

theorem selectedSegmentLogicalTapeDecoder_cells_filterMap_logicalTapeBits_zero
    (target : Tape Bool) :
    (statefulOptionCellsFrom selectedSegmentLogicalTapeDecoderNext
        selectedSegmentLogicalTapeDecoderEmit 0
        (logicalTapeBits target)).filterMap (fun cell => cell) =
      Tape.normalizedOutput target := by
  cases target with
  | mk left head right =>
      rw [selectedSegmentLogicalTapeDecoder_cells_logicalTapeBits_zero]
      cases head with
      | none =>
          simp [selectedSegmentLogicalTapeDecoderCellCells,
            Tape.normalizedOutput, Tape.cells, List.filterMap_append]
          rw [
            selectedSegmentLogicalTapeDecoderCellCells_filterMap_flatten_reverse,
            selectedSegmentLogicalTapeDecoderCellCells_filterMap_flatten]
      | some bit =>
          cases bit
          · simp [selectedSegmentLogicalTapeDecoderCellCells,
              Tape.normalizedOutput, Tape.cells, List.filterMap_append]
            rw [
              selectedSegmentLogicalTapeDecoderCellCells_filterMap_flatten_reverse,
              selectedSegmentLogicalTapeDecoderCellCells_filterMap_flatten]
          · simp [selectedSegmentLogicalTapeDecoderCellCells,
              Tape.normalizedOutput, Tape.cells, List.filterMap_append]
            rw [
              selectedSegmentLogicalTapeDecoderCellCells_filterMap_flatten_reverse,
              selectedSegmentLogicalTapeDecoderCellCells_filterMap_flatten]

theorem selectedSegmentLogicalTapeDecoder_cells_filterMap_guardLogicalTapeBits_zero
    (target : Tape Bool) :
    (statefulOptionCellsFrom selectedSegmentLogicalTapeDecoderNext
        selectedSegmentLogicalTapeDecoderEmit 0
        (logicalTapeBits (guardLogicalTape target))).filterMap
          (fun cell => cell) =
      Tape.normalizedOutput target := by
  rw [selectedSegmentLogicalTapeDecoder_cells_filterMap_logicalTapeBits_zero]
  exact Tape.Equiv.normalizedOutput_eq (guardLogicalTape_equiv target)

theorem selectedSegmentLogicalTapeDecoder_cells_filterMap_guardLogicalTapeBits_start
    (target : Tape Bool) :
    (statefulOptionCellsFrom selectedSegmentLogicalTapeDecoderNext
        selectedSegmentLogicalTapeDecoderEmit
        selectedSegmentLogicalTapeDecoderStart
        (logicalTapeBits (guardLogicalTape target))).filterMap
          (fun cell => cell) =
      Tape.normalizedOutput target := by
  simpa [selectedSegmentLogicalTapeDecoderStart] using
    selectedSegmentLogicalTapeDecoder_cells_filterMap_guardLogicalTapeBits_zero
      target

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape_cells_nil
    (target : Tape Bool) (encodedPrefix : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
          target [] encodedPrefix) =
      List.append encodedPrefix
        (none ::
          List.append
            (statefulOptionCellsFrom selectedSegmentLogicalTapeDecoderNext
              selectedSegmentLogicalTapeDecoderEmit
              selectedSegmentLogicalTapeDecoderStart
              (logicalTapeBits (guardLogicalTape target)))
            [none, none]) := by
  simp [selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape,
    selectedSegmentLogicalTapeDecoderCellShapeCleanupSourceTape,
    FSTStatefulOptionAppendTargetTapeFromLeftWithPadding,
    tapeAtCells, Tape.cells, List.reverse_append,
    selectedSegmentLogicalTapeDecoderStart, List.append_assoc]

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape_cells_cons
    (target : Tape Bool) (pad : Option Bool)
    (padding encodedPrefix : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
          target (pad :: padding) encodedPrefix) =
      List.append encodedPrefix
        (none ::
          List.append
            (statefulOptionCellsFrom selectedSegmentLogicalTapeDecoderNext
              selectedSegmentLogicalTapeDecoderEmit
              selectedSegmentLogicalTapeDecoderStart
              (logicalTapeBits (guardLogicalTape target)))
            (none :: pad :: padding)) := by
  simp [selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape,
    selectedSegmentLogicalTapeDecoderCellShapeCleanupSourceTape,
    FSTStatefulOptionAppendTargetTapeFromLeftWithPadding,
    tapeAtCells, Tape.cells, List.reverse_append,
    selectedSegmentLogicalTapeDecoderStart, List.append_assoc]

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape_normalizedOutput_nil
    (target : Tape Bool) (encodedPrefix : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
          target [] encodedPrefix) =
      List.append (encodedPrefix.filterMap (fun cell => cell))
        (Tape.normalizedOutput target) := by
  rw [Tape.normalizedOutput]
  rw [selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape_cells_nil]
  simp [List.filterMap_append,
    selectedSegmentLogicalTapeDecoder_cells_filterMap_guardLogicalTapeBits_start]

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape_normalizedOutput_cons
    (target : Tape Bool) (pad : Option Bool)
    (padding encodedPrefix : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
          target (pad :: padding) encodedPrefix) =
      List.append (encodedPrefix.filterMap (fun cell => cell))
        (List.append (Tape.normalizedOutput target)
          ((pad :: padding).filterMap (fun cell => cell))) := by
  rw [Tape.normalizedOutput]
  rw [selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape_cells_cons]
  simp [List.filterMap_append,
    selectedSegmentLogicalTapeDecoder_cells_filterMap_guardLogicalTapeBits_start]

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape_normalizedOutput
    (target : Tape Bool) (padding encodedPrefix : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
          target padding encodedPrefix) =
      List.append (encodedPrefix.filterMap (fun cell => cell))
        (List.append (Tape.normalizedOutput target)
          (padding.filterMap (fun cell => cell))) := by
  cases padding with
  | nil =>
      simpa using
        selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape_normalizedOutput_nil
          target encodedPrefix
  | cons pad padding =>
      simpa using
        selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape_normalizedOutput_cons
          target pad padding encodedPrefix

theorem selectedSegmentLogicalTapeDecoderHeadTargetTape_eq_paddedCleanupSourceTape
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderHeadTargetTape
        target rest encodedPrefix =
      selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
        target
        (selectedSegmentLogicalTapeDecoderRestPadding rest)
        encodedPrefix := by
  rfl

theorem selectedSegmentLogicalTapeDecoderHeadTargetTape_normalizedOutput
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderHeadTargetTape
          target rest encodedPrefix) =
      List.append (encodedPrefix.filterMap (fun cell => cell))
        (List.append (Tape.normalizedOutput target)
          ((selectedSegmentLogicalTapeDecoderRestPadding rest).filterMap
            (fun cell => cell))) := by
  simpa [
    selectedSegmentLogicalTapeDecoderHeadTargetTape_eq_paddedCleanupSourceTape] using
    selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape_normalizedOutput
      target (selectedSegmentLogicalTapeDecoderRestPadding rest)
      encodedPrefix

def SelectedSegmentLogicalTapeDecoderGuardedCellShapeCleanupSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (padding : List (Option Bool))
      (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderCellShapeCleanupSourceTape
          (guardLogicalTape target) padding encodedPrefix)
        (guardLogicalTape target)

def SelectedSegmentLogicalTapeDecoderGuardedCellShapeCleanupConstruction : Prop :=
  exists cleanup : MachineDescription,
    SelectedSegmentLogicalTapeDecoderGuardedCellShapeCleanupSpec cleanup

/--
Raw selected-head source used by the three-tape decoder bridge.

Unlike the post-FST cleanup source, this tape still contains the raw
{lit}`[true, true]` head marker inside the selected logical-tape segment.
-/
def selectedSegmentLogicalTapeDecoderRawHeadSourceTape
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) : Tape Bool :=
  tapeAtEncodedSplit encodedPrefix
    (encodedStructuredTapeCells (guardLogicalTape target :: rest))

/-- Structured three-tape input for the raw selected-head decoder backend. -/
def selectedSegmentLogicalTapeDecoderRawHeadStructuredInputTape
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) : Tape Bool :=
  encodedGuardedStructured3Tapes
    (selectedSegmentLogicalTapeDecoderRawHeadSourceTape
      target rest encodedPrefix)
    Tape.blank
    Tape.blank

/-- Index family for materializing raw selected-head decoder inputs. -/
abbrev SelectedSegmentLogicalTapeDecoderRawHeadIngressIndex : Type :=
  Tape Bool × (List (Tape Bool) × List (Option Bool))

/-- Source family for the generic structured input materializer ingress. -/
def selectedSegmentLogicalTapeDecoderRawHeadIngressMaterializerSource
    (input : SelectedSegmentLogicalTapeDecoderRawHeadIngressIndex) :
    Tape Bool :=
  selectedSegmentLogicalTapeDecoderRawHeadSourceTape
    input.1 input.2.1 input.2.2

/-- Tape-2 output-buffer family for the generic structured input materializer ingress. -/
def selectedSegmentLogicalTapeDecoderRawHeadIngressMaterializerOutput
    (_input : SelectedSegmentLogicalTapeDecoderRawHeadIngressIndex) :
    Tape Bool :=
  Tape.blank

/-- Structured three-tape output for the raw selected-head decoder backend. -/
def selectedSegmentLogicalTapeDecoderRawHeadFinalSourceTape
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) : Tape Bool :=
  let guarded := guardLogicalTape target
  tapeAtEncodedSplit
    (List.append encodedPrefix
      (List.append tapeSeparatorCells
        (logicalCellListCode guarded.left.reverse)))
    (List.append headMarkerCells
      (List.append (logicalCellCode guarded.head)
        (List.append (logicalCellListCode guarded.right)
          (encodedStructuredTapeCells rest))))

def selectedSegmentLogicalTapeDecoderRawHeadOutputTape
    (target : Tape Bool) : Tape Bool :=
  { left := List.append target.left [none]
    head := target.head
    right := List.append target.right [none, none] }

theorem selectedSegmentLogicalTapeDecoderRawHeadOutputTape_equiv
    (target : Tape Bool) :
    Tape.Equiv
      (selectedSegmentLogicalTapeDecoderRawHeadOutputTape target)
      target := by
  constructor
  · simp [selectedSegmentLogicalTapeDecoderRawHeadOutputTape,
      dropTrailingNone_append_none]
  constructor
  · rfl
  · simp [selectedSegmentLogicalTapeDecoderRawHeadOutputTape]
    change
      Tape.dropTrailingNone (target.right ++ ([none] ++ [none])) =
        Tape.dropTrailingNone target.right
    rw [← List.append_assoc]
    rw [dropTrailingNone_append_none, dropTrailingNone_append_none]

/--
Structured three-tape output for the raw selected-head decoder backend.

Tape 0 is allowed to stop at the selected head marker.  Forcing it to become
blank would incorrectly require erasing arbitrary source prefix cells.  The
egress bridge projects tape 2, so preserving a precise tape-0 scan position is
the useful exact endpoint.
-/
def selectedSegmentLogicalTapeDecoderRawHeadStructuredOutputTape
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) : Tape Bool :=
  encodedGuardedStructured3Tapes
    (selectedSegmentLogicalTapeDecoderRawHeadFinalSourceTape
      target rest encodedPrefix)
    Tape.blank
    (selectedSegmentLogicalTapeDecoderRawHeadOutputTape target)

/--
Ingress bridge from the old raw selected-head one-tape endpoint into the
structured three-tape decoder input.
-/
def SelectedSegmentLogicalTapeDecoderRawHeadIngressBridgeSpec
    (ingress : MachineDescription) : Prop :=
  ingress.SubroutineReady ∧
    forall (target : Tape Bool) (rest : List (Tape Bool))
      (encodedPrefix : List (Option Bool)),
      ingress.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderRawHeadSourceTape
          target rest encodedPrefix)
        (selectedSegmentLogicalTapeDecoderRawHeadStructuredInputTape
          target rest encodedPrefix)

/-- Existence wrapper for the raw selected-head decoder ingress bridge. -/
def SelectedSegmentLogicalTapeDecoderRawHeadIngressBridgeConstruction :
    Prop :=
  exists ingress : MachineDescription,
    SelectedSegmentLogicalTapeDecoderRawHeadIngressBridgeSpec ingress

theorem selectedSegmentLogicalTapeDecoderRawHeadIngressBridgeSpec_of_structured3InputMaterializerSpec
    {materializer : MachineDescription}
    (hmaterializer :
      Structured3InputMaterializerSpec
        selectedSegmentLogicalTapeDecoderRawHeadIngressMaterializerSource
        selectedSegmentLogicalTapeDecoderRawHeadIngressMaterializerOutput
        materializer) :
    SelectedSegmentLogicalTapeDecoderRawHeadIngressBridgeSpec
      materializer := by
  constructor
  · exact hmaterializer.left
  · intro target rest encodedPrefix
    have hrun :=
      hmaterializer.right (target, (rest, encodedPrefix))
    simpa [
      selectedSegmentLogicalTapeDecoderRawHeadIngressMaterializerSource,
      selectedSegmentLogicalTapeDecoderRawHeadIngressMaterializerOutput,
      selectedSegmentLogicalTapeDecoderRawHeadSourceTape,
      selectedSegmentLogicalTapeDecoderRawHeadStructuredInputTape,
      structured3InputMaterializerTargetTape] using hrun

theorem selectedSegmentLogicalTapeDecoderRawHeadIngressBridgeConstruction_of_structured3InputMaterializerConstruction
    (hmaterializer :
      Structured3InputMaterializerConstruction
        selectedSegmentLogicalTapeDecoderRawHeadIngressMaterializerSource
        selectedSegmentLogicalTapeDecoderRawHeadIngressMaterializerOutput) :
    SelectedSegmentLogicalTapeDecoderRawHeadIngressBridgeConstruction := by
  rcases hmaterializer with ⟨materializer, hmaterializerSpec⟩
  exact
    ⟨materializer,
      selectedSegmentLogicalTapeDecoderRawHeadIngressBridgeSpec_of_structured3InputMaterializerSpec
        hmaterializerSpec⟩

/--
Structured three-tape normalizer for raw selected-head segments.

This is the main algorithmic leaf: tape 0 carries the raw selected-head segment
with its head marker still present, tape 1 is workspace, and tape 2 receives a
guarded representative of the selected target tape.
-/
def SelectedSegmentLogicalTapeDecoderRawHeadThreeTapeNormalizerSpec
    (normalizer : MachineDescription) : Prop :=
  normalizer.SubroutineReady ∧
    forall (target : Tape Bool) (rest : List (Tape Bool))
      (encodedPrefix : List (Option Bool)),
      normalizer.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderRawHeadStructuredInputTape
          target rest encodedPrefix)
        (selectedSegmentLogicalTapeDecoderRawHeadStructuredOutputTape
          target rest encodedPrefix)

/-- Existence wrapper for the raw selected-head three-tape normalizer. -/
def SelectedSegmentLogicalTapeDecoderRawHeadThreeTapeNormalizerConstruction :
    Prop :=
  exists normalizer : MachineDescription,
    SelectedSegmentLogicalTapeDecoderRawHeadThreeTapeNormalizerSpec normalizer

/-- Egress bridge from the structured raw selected-head output to the old target. -/
def SelectedSegmentLogicalTapeDecoderRawHeadEgressBridgeSpec
    (egress : MachineDescription) : Prop :=
  egress.SubroutineReady ∧
    forall (target : Tape Bool) (rest : List (Tape Bool))
      (encodedPrefix : List (Option Bool)),
      egress.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderRawHeadStructuredOutputTape
          target rest encodedPrefix)
        target

/-- Existence wrapper for the raw selected-head egress bridge. -/
def SelectedSegmentLogicalTapeDecoderRawHeadEgressBridgeConstruction :
    Prop :=
  exists egress : MachineDescription,
    SelectedSegmentLogicalTapeDecoderRawHeadEgressBridgeSpec egress

theorem selectedSegmentLogicalTapeDecoderRawHeadEgressBridgeSpec_of_tape2ProjectorSpec
    {projector : MachineDescription}
    (hprojector : StructuredTape2ProjectorSpec projector) :
    SelectedSegmentLogicalTapeDecoderRawHeadEgressBridgeSpec projector := by
  constructor
  · exact hprojector.left
  · intro target rest encodedPrefix
    rcases
        hprojector.right
          (selectedSegmentLogicalTapeDecoderRawHeadFinalSourceTape
            target rest encodedPrefix)
          Tape.blank
          (selectedSegmentLogicalTapeDecoderRawHeadOutputTape target) with
      ⟨actual, hhalts, hequiv⟩
    exact
      ⟨actual, by
        simpa [
          selectedSegmentLogicalTapeDecoderRawHeadStructuredOutputTape] using
          hhalts,
        Tape.Equiv.trans hequiv
          (selectedSegmentLogicalTapeDecoderRawHeadOutputTape_equiv
            target)⟩

theorem selectedSegmentLogicalTapeDecoderRawHeadEgressBridgeConstruction_of_tape2ProjectorConstruction
    (hprojector : StructuredTape2ProjectorConstruction) :
    SelectedSegmentLogicalTapeDecoderRawHeadEgressBridgeConstruction := by
  rcases hprojector with ⟨projector, hprojectorSpec⟩
  exact
    ⟨projector,
      selectedSegmentLogicalTapeDecoderRawHeadEgressBridgeSpec_of_tape2ProjectorSpec
        hprojectorSpec⟩

/-- Bundled existence wrapper for the raw selected-head endpoint bridge. -/
def SelectedSegmentLogicalTapeDecoderRawHeadThreeTapeBridgeConstruction :
    Prop :=
  exists ingress normalizer egress : MachineDescription,
    SelectedSegmentLogicalTapeDecoderRawHeadIngressBridgeSpec ingress ∧
    SelectedSegmentLogicalTapeDecoderRawHeadThreeTapeNormalizerSpec normalizer ∧
    SelectedSegmentLogicalTapeDecoderRawHeadEgressBridgeSpec egress

/-- Description assembled from raw ingress, structured normalizer, and egress. -/
def selectedSegmentLogicalTapeDecoderRawHeadThreeTapeBridgeDescription
    (ingress normalizer egress : MachineDescription) :
    MachineDescription :=
  structured3EndpointBridgeDescription
    ingress normalizer egress

theorem selectedSegmentLogicalTapeDecoderRawHeadThreeTapeBridgeDescription_spec
    {ingress normalizer egress : MachineDescription}
    (hingress :
      SelectedSegmentLogicalTapeDecoderRawHeadIngressBridgeSpec ingress)
    (hnormalizer :
      SelectedSegmentLogicalTapeDecoderRawHeadThreeTapeNormalizerSpec
        normalizer)
    (hegress :
      SelectedSegmentLogicalTapeDecoderRawHeadEgressBridgeSpec egress) :
    StructuredSelectedHeadSegmentDecoderSpec
      (selectedSegmentLogicalTapeDecoderRawHeadThreeTapeBridgeDescription
        ingress normalizer egress) := by
  constructor
  · exact
      structured3EndpointBridgeDescription_subroutineReady
        hingress.left hnormalizer.left hegress.left
  · intro target rest encodedPrefix
    simpa [
      selectedSegmentLogicalTapeDecoderRawHeadThreeTapeBridgeDescription,
      selectedSegmentLogicalTapeDecoderRawHeadSourceTape] using
      structured3EndpointBridgeDescription_haltsFromTapeEquiv
        hingress.left hnormalizer.left hegress.left
        (hingress.right target rest encodedPrefix)
        (hnormalizer.right target rest encodedPrefix)
        (hegress.right target rest encodedPrefix)

theorem structuredSelectedHeadSegmentDecoderConstruction_of_rawHeadThreeTapeBridgeConstruction
    (hbridge :
      SelectedSegmentLogicalTapeDecoderRawHeadThreeTapeBridgeConstruction) :
    StructuredSelectedHeadSegmentDecoderConstruction := by
  rcases hbridge with
    ⟨ingress, normalizer, egress, hingress, hnormalizer, hegress⟩
  exact
    ⟨selectedSegmentLogicalTapeDecoderRawHeadThreeTapeBridgeDescription
        ingress normalizer egress,
      selectedSegmentLogicalTapeDecoderRawHeadThreeTapeBridgeDescription_spec
        hingress hnormalizer hegress⟩

namespace SelectedSegmentLogicalTapeDecoderRawHeadNormalizer

def startState : Nat := 0

def haltState : Nat := 99

/--
Lowerer-facing row table for the raw selected-head normalizer.

The machine starts with tape 0 on the selected segment separator.  It copies
decoded cells before the raw {lit}`[true, true]` marker to tape 2's left side,
skips the marker, copies the head/right cells to tape 2, then scans tape 0
backwards to the marker while rewinding tape 2 to the decoded head cell.
Tape 1 is deliberately unused so the endpoint can keep it exactly blank.
-/
def rows : List Transition :=
  [ ThreeTape.row 0 none none none
      ThreeTape.keepR ThreeTape.keepS ThreeTape.keepS 1

  , ThreeTape.row 1 (some false) none none
      ThreeTape.keepR ThreeTape.keepS ThreeTape.keepS 2
  , ThreeTape.row 1 (some true) none none
      ThreeTape.keepR ThreeTape.keepS ThreeTape.keepS 3
  , ThreeTape.row 2 (some false) none none
      ThreeTape.keepR ThreeTape.keepS ThreeTape.keepR 1
  , ThreeTape.row 2 (some true) none none
      ThreeTape.keepR ThreeTape.keepS (ThreeTape.writeR (some false)) 1
  , ThreeTape.row 3 (some false) none none
      ThreeTape.keepR ThreeTape.keepS (ThreeTape.writeR (some true)) 1
  , ThreeTape.row 3 (some true) none none
      ThreeTape.keepR ThreeTape.keepS ThreeTape.keepS 4

  , ThreeTape.row 4 none none none
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepS 10
  , ThreeTape.row 4 (some false) none none
      ThreeTape.keepR ThreeTape.keepS ThreeTape.keepS 5
  , ThreeTape.row 4 (some true) none none
      ThreeTape.keepR ThreeTape.keepS ThreeTape.keepS 6
  , ThreeTape.row 5 (some false) none none
      ThreeTape.keepR ThreeTape.keepS ThreeTape.keepR 4
  , ThreeTape.row 5 (some true) none none
      ThreeTape.keepR ThreeTape.keepS (ThreeTape.writeR (some false)) 4
  , ThreeTape.row 6 (some false) none none
      ThreeTape.keepR ThreeTape.keepS (ThreeTape.writeR (some true)) 4

  , ThreeTape.row 10 (some false) none none
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepL 12
  , ThreeTape.row 10 (some false) none (some false)
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepL 12
  , ThreeTape.row 10 (some false) none (some true)
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepL 12
  , ThreeTape.row 10 (some true) none none
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepS 11
  , ThreeTape.row 10 (some true) none (some false)
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepS 11
  , ThreeTape.row 10 (some true) none (some true)
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepS 11
  , ThreeTape.row 11 (some false) none none
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepL 10
  , ThreeTape.row 11 (some false) none (some false)
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepL 10
  , ThreeTape.row 11 (some false) none (some true)
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepL 10
  , ThreeTape.row 11 (some true) none none
      ThreeTape.keepS ThreeTape.keepS ThreeTape.keepS haltState
  , ThreeTape.row 11 (some true) none (some false)
      ThreeTape.keepS ThreeTape.keepS ThreeTape.keepS haltState
  , ThreeTape.row 11 (some true) none (some true)
      ThreeTape.keepS ThreeTape.keepS ThreeTape.keepS haltState
  , ThreeTape.row 12 (some false) none none
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepS 10
  , ThreeTape.row 12 (some false) none (some false)
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepS 10
  , ThreeTape.row 12 (some false) none (some true)
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepS 10
  , ThreeTape.row 12 (some true) none none
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepS 10
  , ThreeTape.row 12 (some true) none (some false)
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepS 10
  , ThreeTape.row 12 (some true) none (some true)
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepS 10 ]

def description : Description :=
  ThreeTape.description 100 startState haltState rows

theorem description_wellFormed :
    description.WellFormed :=
  structuredDescription_wellFormed_of_bool description (by decide)

theorem description_haltTransitionFree :
    description.HaltTransitionFree :=
  structuredDescription_haltTransitionFree_of_bool description (by decide)

theorem description_supportsReadWriteRows3 :
    SupportsReadWriteRows3 description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

def loweredDescription : MachineDescription :=
  lowerStructured3Description description

theorem loweredDescription_subroutineReady :
    loweredDescription.SubroutineReady := by
  simpa [loweredDescription] using
    lowerStructured3Description_subroutineReady
      description_wellFormed
      description_supportsReadWriteRows3

def initialConfig
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) : Configuration :=
  ThreeTape.config startState
    (selectedSegmentLogicalTapeDecoderRawHeadSourceTape
      target rest encodedPrefix)
    Tape.blank
    Tape.blank

def finalConfig
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) : Configuration :=
  ThreeTape.config haltState
    (selectedSegmentLogicalTapeDecoderRawHeadFinalSourceTape
      target rest encodedPrefix)
    Tape.blank
    (selectedSegmentLogicalTapeDecoderRawHeadOutputTape target)

def targetCells (target : Tape Bool) : List (Option Bool) :=
  let guarded := guardLogicalTape target
  List.append guarded.left.reverse
    (guarded.head :: guarded.right)

def rightEdgeOutputTape (target : Tape Bool) : Tape Bool :=
  tapeAtCells (targetCells target).reverse []

def afterLeftCopyConfig
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) : Configuration :=
  let guarded := guardLogicalTape target
  ThreeTape.config 4
    (tapeAtEncodedSplit
      (List.append encodedPrefix
        (List.append tapeSeparatorCells
          (List.append (logicalCellListCode guarded.left.reverse)
            headMarkerCells)))
      (List.append (logicalCellCode guarded.head)
        (List.append (logicalCellListCode guarded.right)
          (encodedStructuredTapeCells rest))))
    Tape.blank
    (tapeAtCells guarded.left [])

def afterRightCopyConfig
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) : Configuration :=
  let guarded := guardLogicalTape target
  ThreeTape.config 4
    (tapeAtEncodedSplit
      (List.append encodedPrefix
        (List.append tapeSeparatorCells
          (logicalTapeCode guarded)))
      (encodedStructuredTapeCells rest))
    Tape.blank
    (rightEdgeOutputTape target)

def rewindStartConfig
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) : Configuration :=
  let guarded := guardLogicalTape target
  ThreeTape.config 10
    (ThreeTape.keepL.apply
      (tapeAtEncodedSplit
        (List.append encodedPrefix
          (List.append tapeSeparatorCells
            (logicalTapeCode guarded)))
        (encodedStructuredTapeCells rest)))
    Tape.blank
    (rightEdgeOutputTape target)

def rewindMarkerSecondConfig
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) : Configuration :=
  let guarded := guardLogicalTape target
  ThreeTape.config 10
    (tapeAtEncodedSplit
      (List.append
        (List.append encodedPrefix
          (List.append tapeSeparatorCells
            (logicalCellListCode guarded.left.reverse)))
        [some true])
      (List.append [some true]
        (List.append (logicalCellCode guarded.head)
          (List.append (logicalCellListCode guarded.right)
            (encodedStructuredTapeCells rest)))))
    Tape.blank
        (selectedSegmentLogicalTapeDecoderRawHeadOutputTape target)

private def rewindOutputCurrentCells
    (cells : List (Option Bool)) : List (Option Bool) :=
  match cells with
  | [] => [none]
  | _ => cells

@[simp] private theorem rewindOutputCurrentCells_cons
    (cell : Option Bool) (tail : List (Option Bool)) :
    rewindOutputCurrentCells (cell :: tail) = cell :: tail := by
  rfl

@[simp] private theorem rewindOutputCurrentCells_logicalCellListCode_singleton_append
    (cell : Option Bool) (tail : List (Option Bool)) :
    rewindOutputCurrentCells
        (List.append (logicalCellListCode [cell]) tail) =
      List.append (logicalCellListCode [cell]) tail := by
  cases cell with
  | none =>
      simp [rewindOutputCurrentCells, logicalCellListCode, logicalCellCode]
  | some bit =>
      cases bit <;>
        simp [rewindOutputCurrentCells, logicalCellListCode,
          logicalCellCode]

@[simp] private theorem rewindOutputCurrentCells_logicalCellListBits_singleton_append
    (cell : Option Bool) (tail : List (Option Bool)) :
    rewindOutputCurrentCells
        (List.append (List.map some (logicalCellListBits [cell])) tail) =
      List.append (List.map some (logicalCellListBits [cell])) tail := by
  cases cell with
  | none =>
      simp [rewindOutputCurrentCells, logicalCellListBits,
        logicalCellBits]
  | some bit =>
      cases bit <;>
        simp [rewindOutputCurrentCells, logicalCellListBits,
          logicalCellBits]

@[simp] private theorem rewindOutputCurrentCells_encodedStructuredTapeCells
    (rest : List (Tape Bool)) :
    rewindOutputCurrentCells (encodedStructuredTapeCells rest) =
      encodedStructuredTapeCells rest := by
  cases rest with
  | nil =>
      simp [rewindOutputCurrentCells, encodedStructuredTapeCells,
        tapeSeparatorCells]
  | cons T rest =>
      simp [rewindOutputCurrentCells, encodedStructuredTapeCells,
        tapeSeparatorCells]

private def rewindCellStackConfig
    (baseLeft stack sourceRight outputLeft outputRight :
      List (Option Bool)) : Configuration :=
  ThreeTape.config 10
    (ThreeTape.keepL.apply
      (tapeAtCells
        (List.append (logicalCellListCode stack.reverse).reverse baseLeft)
        sourceRight))
    Tape.blank
    (tapeAtCells (List.append stack outputLeft) outputRight)

private def rewindCellStackDoneConfig
    (baseLeft stack sourceRight outputLeft outputRight :
      List (Option Bool)) : Configuration :=
  ThreeTape.config 10
    (ThreeTape.keepL.apply
      (tapeAtCells baseLeft
        (List.append (logicalCellListCode stack.reverse)
          (rewindOutputCurrentCells sourceRight))))
    Tape.blank
    (tapeAtCells outputLeft
      (List.append stack.reverse (rewindOutputCurrentCells outputRight)))

private theorem description_rewinds_cellStack_step_nilSource
    (baseLeft stack outputLeft outputRight :
      List (Option Bool)) (cell : Option Bool) :
    description.runConfig 2
        (rewindCellStackConfig baseLeft (cell :: stack)
          [] outputLeft outputRight) =
      rewindCellStackConfig baseLeft stack
        (List.append (logicalCellListCode [cell])
          (rewindOutputCurrentCells []))
        outputLeft
        (cell :: rewindOutputCurrentCells outputRight) := by
  cases cell with
  | none =>
      cases outputRight with
      | nil =>
          three_tape_step [
            description, rows, rewindCellStackConfig,
            rewindOutputCurrentCells, logicalCellCode,
            logicalCellListCode, logicalCellListBits, logicalCellBits,
            tapeAtCells]
      | cons outHead outTail =>
          cases outHead with
          | none =>
              three_tape_step [
                description, rows, rewindCellStackConfig,
                rewindOutputCurrentCells, logicalCellCode,
                logicalCellListCode, logicalCellListBits,
                logicalCellBits,
                tapeAtCells]
          | some outBit =>
              cases outBit <;>
                three_tape_step [
                  description, rows, rewindCellStackConfig,
                  rewindOutputCurrentCells, logicalCellCode,
                  logicalCellListCode, logicalCellListBits,
                  logicalCellBits,
                  tapeAtCells]
  | some bit =>
      cases bit <;>
        cases outputRight with
        | nil =>
            three_tape_step [
              description, rows, rewindCellStackConfig,
              rewindOutputCurrentCells, logicalCellCode,
              logicalCellListCode, logicalCellListBits, logicalCellBits,
              tapeAtCells]
        | cons outHead outTail =>
            cases outHead with
            | none =>
                three_tape_step [
                  description, rows, rewindCellStackConfig,
                  rewindOutputCurrentCells, logicalCellCode,
                  logicalCellListCode, logicalCellListBits,
                  logicalCellBits,
                  tapeAtCells]
            | some outBit =>
                cases outBit <;>
                  three_tape_step [
                    description, rows, rewindCellStackConfig,
                    rewindOutputCurrentCells, logicalCellCode,
                    logicalCellListCode, logicalCellListBits,
                    logicalCellBits,
                    tapeAtCells]

private theorem description_rewinds_cellStack_step_sourceHeadNone
    (baseLeft stack sourceTail outputLeft outputRight :
      List (Option Bool)) (cell : Option Bool) :
    description.runConfig 2
        (rewindCellStackConfig baseLeft (cell :: stack)
          (none :: sourceTail) outputLeft outputRight) =
      rewindCellStackConfig baseLeft stack
        (List.append (logicalCellListCode [cell])
          (rewindOutputCurrentCells (none :: sourceTail)))
        outputLeft
        (cell :: rewindOutputCurrentCells outputRight) := by
  cases cell with
  | none =>
      cases outputRight with
      | nil =>
          three_tape_step [
            description, rows, rewindCellStackConfig,
            rewindOutputCurrentCells, logicalCellCode,
            logicalCellListCode, logicalCellListBits,
            logicalCellBits,
            tapeAtCells]
      | cons outHead outTail =>
          cases outHead with
          | none =>
              three_tape_step [
                description, rows, rewindCellStackConfig,
                rewindOutputCurrentCells, logicalCellCode,
                logicalCellListCode, logicalCellListBits,
                logicalCellBits,
                tapeAtCells]
          | some outBit =>
              cases outBit <;>
                three_tape_step [
                  description, rows, rewindCellStackConfig,
                  rewindOutputCurrentCells, logicalCellCode,
                  logicalCellListCode, logicalCellListBits,
                  logicalCellBits,
                  tapeAtCells]
  | some bit =>
      cases bit <;>
        cases outputRight with
        | nil =>
            three_tape_step [
              description, rows, rewindCellStackConfig,
              rewindOutputCurrentCells, logicalCellCode,
              logicalCellListCode, logicalCellListBits,
              logicalCellBits,
              tapeAtCells]
        | cons outHead outTail =>
            cases outHead with
            | none =>
                three_tape_step [
                  description, rows, rewindCellStackConfig,
                  rewindOutputCurrentCells, logicalCellCode,
                  logicalCellListCode, logicalCellListBits,
                  logicalCellBits,
                  tapeAtCells]
            | some outBit =>
                cases outBit <;>
                  three_tape_step [
                    description, rows, rewindCellStackConfig,
                    rewindOutputCurrentCells, logicalCellCode,
                    logicalCellListCode, logicalCellListBits,
                    logicalCellBits,
                    tapeAtCells]

private theorem description_rewinds_cellStack_step_sourceHeadSome
    (baseLeft stack sourceTail outputLeft outputRight :
      List (Option Bool)) (sourceBit : Bool) (cell : Option Bool) :
    description.runConfig 2
        (rewindCellStackConfig baseLeft (cell :: stack)
          (some sourceBit :: sourceTail) outputLeft outputRight) =
      rewindCellStackConfig baseLeft stack
        (List.append (logicalCellListCode [cell])
          (rewindOutputCurrentCells (some sourceBit :: sourceTail)))
        outputLeft
        (cell :: rewindOutputCurrentCells outputRight) := by
  cases sourceBit <;>
    cases cell with
    | none =>
        cases outputRight with
        | nil =>
            three_tape_step [
              description, rows, rewindCellStackConfig,
              rewindOutputCurrentCells, logicalCellCode,
              logicalCellListCode, logicalCellListBits,
              logicalCellBits,
              tapeAtCells]
        | cons outHead outTail =>
            cases outHead with
            | none =>
                three_tape_step [
                  description, rows, rewindCellStackConfig,
                  rewindOutputCurrentCells, logicalCellCode,
                  logicalCellListCode, logicalCellListBits,
                  logicalCellBits,
                  tapeAtCells]
            | some outBit =>
                cases outBit <;>
                  three_tape_step [
                    description, rows, rewindCellStackConfig,
                    rewindOutputCurrentCells, logicalCellCode,
                    logicalCellListCode, logicalCellListBits,
                    logicalCellBits,
                    tapeAtCells]
    | some bit =>
        cases bit <;>
          cases outputRight with
          | nil =>
              three_tape_step [
                description, rows, rewindCellStackConfig,
                rewindOutputCurrentCells, logicalCellCode,
                logicalCellListCode, logicalCellListBits,
                logicalCellBits,
                tapeAtCells]
          | cons outHead outTail =>
              cases outHead with
              | none =>
                  three_tape_step [
                    description, rows, rewindCellStackConfig,
                    rewindOutputCurrentCells, logicalCellCode,
                    logicalCellListCode, logicalCellListBits,
                    logicalCellBits,
                    tapeAtCells]
              | some outBit =>
                  cases outBit <;>
                    three_tape_step [
                      description, rows, rewindCellStackConfig,
                      rewindOutputCurrentCells, logicalCellCode,
                      logicalCellListCode, logicalCellListBits,
                      logicalCellBits,
                      tapeAtCells]

private theorem description_rewinds_cellStack_step
    (baseLeft stack sourceRight outputLeft outputRight :
      List (Option Bool)) (cell : Option Bool) :
    description.runConfig 2
        (rewindCellStackConfig baseLeft (cell :: stack)
          sourceRight outputLeft outputRight) =
      rewindCellStackConfig baseLeft stack
        (List.append (logicalCellListCode [cell])
          (rewindOutputCurrentCells sourceRight))
        outputLeft
        (cell :: rewindOutputCurrentCells outputRight) := by
  cases sourceRight with
  | nil =>
      exact description_rewinds_cellStack_step_nilSource
        baseLeft stack outputLeft outputRight cell
  | cons sourceHead sourceTail =>
      cases sourceHead with
      | none =>
          exact description_rewinds_cellStack_step_sourceHeadNone
            baseLeft stack sourceTail outputLeft outputRight cell
      | some sourceBit =>
          exact description_rewinds_cellStack_step_sourceHeadSome
            baseLeft stack sourceTail outputLeft outputRight sourceBit cell

private theorem description_rewinds_cellStackConfig
    (baseLeft stack sourceRight outputLeft outputRight :
      List (Option Bool)) :
    description.runConfig (2 * stack.length)
      (rewindCellStackConfig
        baseLeft stack sourceRight outputLeft outputRight) =
      rewindCellStackDoneConfig
        baseLeft stack sourceRight outputLeft outputRight := by
  induction stack generalizing sourceRight outputRight with
  | nil =>
      cases sourceRight <;> cases outputRight <;>
        simp [rewindCellStackConfig, rewindCellStackDoneConfig,
          rewindOutputCurrentCells, logicalCellListBits,
          Structured.Description.runConfig, tapeAtCells]
  | cons cell stack ih =>
      rw [show 2 * (cell :: stack).length =
        2 + 2 * stack.length by
        simp
        lia]
      rw [Description.runConfig_add]
      rw [description_rewinds_cellStack_step]
      rw [ih (List.append (logicalCellListCode [cell])
          (rewindOutputCurrentCells sourceRight))
        (cell :: rewindOutputCurrentCells outputRight)]
      change
        ThreeTape.config 10
          (ThreeTape.keepL.apply
            (tapeAtCells baseLeft
              (List.append (logicalCellListCode stack.reverse)
                (rewindOutputCurrentCells
                  (List.append (logicalCellListCode [cell])
                    (rewindOutputCurrentCells sourceRight))))))
          Tape.blank
          (tapeAtCells outputLeft
            (List.append stack.reverse
              (rewindOutputCurrentCells
                (cell :: rewindOutputCurrentCells outputRight)))) = _
      rw [rewindOutputCurrentCells_logicalCellListCode_singleton_append]
      simp [rewindCellStackDoneConfig, List.reverse_cons, List.append_assoc]

private def leftCopyConfig
    (baseLeft processed remaining suffix :
      List (Option Bool)) : Configuration :=
  ThreeTape.config 1
    (tapeAtEncodedSplit
      (List.append baseLeft (logicalCellListCode processed))
      (List.append (logicalCellListCode remaining)
        (List.append headMarkerCells suffix)))
    Tape.blank
    (tapeAtCells processed.reverse [])

private theorem description_enters_leftCopyConfig
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    description.runConfig 1
        (initialConfig target rest encodedPrefix) =
      leftCopyConfig
        (List.append encodedPrefix tapeSeparatorCells)
        []
        (guardLogicalTape target).left.reverse
        (List.append (logicalCellCode (guardLogicalTape target).head)
          (List.append (logicalCellListCode (guardLogicalTape target).right)
            (encodedStructuredTapeCells rest))) := by
  cases target with
  | mk left head right =>
      cases head with
      | none =>
          three_tape_step [
            description, rows, initialConfig, leftCopyConfig,
            selectedSegmentLogicalTapeDecoderRawHeadSourceTape,
            guardLogicalTape, logicalTapeCode, logicalCellListCode,
            logicalCellCode, logicalCellListBits, logicalCellBits,
            encodedStructuredTapeCells, tapeAtEncodedSplit,
            tapeSeparatorCells, headMarkerCells, startState, haltState,
            List.map_append, List.append_assoc]
      | some bit =>
          cases bit <;>
            three_tape_step [
              description, rows, initialConfig, leftCopyConfig,
              selectedSegmentLogicalTapeDecoderRawHeadSourceTape,
              guardLogicalTape, logicalTapeCode, logicalCellListCode,
              logicalCellCode, logicalCellListBits, logicalCellBits,
              encodedStructuredTapeCells, tapeAtEncodedSplit,
              tapeSeparatorCells, headMarkerCells, startState, haltState,
              List.map_append, List.append_assoc]

private theorem description_leftCopy_cell
    (baseLeft processed remaining suffix : List (Option Bool))
    (cell : Option Bool) :
    description.runConfig 2
        (leftCopyConfig baseLeft processed (cell :: remaining) suffix) =
      leftCopyConfig baseLeft (List.append processed [cell])
        remaining suffix := by
  cases cell with
  | none =>
      three_tape_step [
        description, rows, leftCopyConfig, logicalCellListCode,
        logicalCellCode, logicalCellListBits, logicalCellBits,
        tapeAtEncodedSplit, tapeAtCells, List.map_append,
        List.reverse_append, List.append_assoc]
      cases
          (List.map some (logicalCellListBits remaining) ++
            (headMarkerCells ++ suffix)) <;>
        rfl
  | some bit =>
      cases bit <;>
        three_tape_step [
          description, rows, leftCopyConfig, logicalCellListCode,
          logicalCellCode, logicalCellListBits, logicalCellBits,
          tapeAtEncodedSplit, tapeAtCells, List.map_append,
          List.reverse_append, List.append_assoc]
      all_goals
        cases
            (List.map some (logicalCellListBits remaining) ++
              (headMarkerCells ++ suffix)) <;>
          rfl

private theorem description_leftCopy_cells
    (baseLeft processed remaining suffix : List (Option Bool)) :
    description.runConfig (2 * remaining.length)
        (leftCopyConfig baseLeft processed remaining suffix) =
      leftCopyConfig baseLeft (List.append processed remaining)
        [] suffix := by
  induction remaining generalizing processed with
  | nil =>
      simp [leftCopyConfig, Structured.Description.runConfig]
  | cons cell remaining ih =>
      rw [show 2 * (cell :: remaining).length =
        2 + 2 * remaining.length by
        simp
        lia]
      rw [Description.runConfig_add]
      rw [description_leftCopy_cell]
      rw [ih (List.append processed [cell])]
      simp [List.append_assoc]

private theorem description_leftCopy_headMarker
    (baseLeft processed suffix : List (Option Bool)) :
    description.runConfig 2
        (leftCopyConfig baseLeft processed [] suffix) =
      ThreeTape.config 4
        (tapeAtEncodedSplit
          (List.append
            (List.append baseLeft (logicalCellListCode processed))
            headMarkerCells)
          suffix)
        Tape.blank
        (tapeAtCells processed.reverse []) := by
  cases suffix with
  | nil =>
      three_tape_step [
        description, rows, leftCopyConfig, logicalCellListCode,
        logicalCellCode, tapeAtEncodedSplit, tapeAtCells,
        headMarkerCells, List.reverse_append, List.append_assoc]
  | cons sourceHead sourceTail =>
      cases sourceHead with
      | none =>
          three_tape_step [
            description, rows, leftCopyConfig, logicalCellListCode,
            logicalCellCode, tapeAtEncodedSplit, tapeAtCells,
            headMarkerCells, List.reverse_append, List.append_assoc]
      | some sourceBit =>
          cases sourceBit <;>
            three_tape_step [
              description, rows, leftCopyConfig, logicalCellListCode,
              logicalCellCode, tapeAtEncodedSplit, tapeAtCells,
              headMarkerCells, List.reverse_append, List.append_assoc]

theorem description_reaches_afterLeftCopyConfig
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    exists steps : Nat,
      description.runConfig steps
        (initialConfig target rest encodedPrefix) =
        afterLeftCopyConfig target rest encodedPrefix := by
  let guarded : Tape Bool := guardLogicalTape target
  let baseLeft : List (Option Bool) :=
    List.append encodedPrefix tapeSeparatorCells
  let suffix : List (Option Bool) :=
    List.append (logicalCellCode guarded.head)
      (List.append (logicalCellListCode guarded.right)
        (encodedStructuredTapeCells rest))
  refine ⟨1 + (2 * guarded.left.reverse.length + 2), ?_⟩
  rw [Description.runConfig_add]
  rw [description_enters_leftCopyConfig]
  change
    description.runConfig (2 * guarded.left.reverse.length + 2)
        (leftCopyConfig baseLeft [] guarded.left.reverse suffix) =
      afterLeftCopyConfig target rest encodedPrefix
  rw [Description.runConfig_add]
  rw [description_leftCopy_cells]
  rw [description_leftCopy_headMarker]
  simp [guarded, baseLeft, suffix, afterLeftCopyConfig, tapeAtEncodedSplit,
    List.append_assoc]

private def rightCopyConfig
    (baseLeft outputBaseLeft processed remaining suffix :
      List (Option Bool)) : Configuration :=
  ThreeTape.config 4
    (tapeAtEncodedSplit
      (List.append baseLeft (logicalCellListCode processed))
      (List.append (logicalCellListCode remaining) suffix))
    Tape.blank
    (tapeAtCells (List.append processed.reverse outputBaseLeft) [])

private theorem description_rightCopy_cell
    (baseLeft outputBaseLeft processed remaining suffix :
      List (Option Bool)) (cell : Option Bool) :
    description.runConfig 2
        (rightCopyConfig baseLeft outputBaseLeft processed
          (cell :: remaining) suffix) =
      rightCopyConfig baseLeft outputBaseLeft
        (List.append processed [cell]) remaining suffix := by
  cases cell with
  | none =>
      three_tape_step [
        description, rows, rightCopyConfig, logicalCellListCode,
        logicalCellCode, logicalCellListBits, logicalCellBits,
        tapeAtEncodedSplit, tapeAtCells, List.map_append,
        List.reverse_append, List.append_assoc]
      cases
          (List.map some (logicalCellListBits remaining) ++ suffix) <;>
        rfl
  | some bit =>
      cases bit <;>
        three_tape_step [
          description, rows, rightCopyConfig, logicalCellListCode,
          logicalCellCode, logicalCellListBits, logicalCellBits,
          tapeAtEncodedSplit, tapeAtCells, List.map_append,
          List.reverse_append, List.append_assoc]
      all_goals
        cases
            (List.map some (logicalCellListBits remaining) ++ suffix) <;>
          rfl

private theorem description_rightCopy_cells
    (baseLeft outputBaseLeft processed remaining suffix :
      List (Option Bool)) :
    description.runConfig (2 * remaining.length)
        (rightCopyConfig baseLeft outputBaseLeft processed
          remaining suffix) =
      rightCopyConfig baseLeft outputBaseLeft
        (List.append processed remaining) [] suffix := by
  induction remaining generalizing processed with
  | nil =>
      simp [rightCopyConfig, Structured.Description.runConfig]
  | cons cell remaining ih =>
      rw [show 2 * (cell :: remaining).length =
        2 + 2 * remaining.length by
        simp
        lia]
      rw [Description.runConfig_add]
      rw [description_rightCopy_cell]
      rw [ih (List.append processed [cell])]
      simp [List.append_assoc]

theorem description_reaches_afterRightCopyConfig
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    exists steps : Nat,
      description.runConfig steps
        (afterLeftCopyConfig target rest encodedPrefix) =
        afterRightCopyConfig target rest encodedPrefix := by
  let guarded : Tape Bool := guardLogicalTape target
  let baseLeft : List (Option Bool) :=
    List.append encodedPrefix
      (List.append tapeSeparatorCells
        (List.append (logicalCellListCode guarded.left.reverse)
          headMarkerCells))
  let cells : List (Option Bool) :=
    guarded.head :: guarded.right
  let suffix : List (Option Bool) := encodedStructuredTapeCells rest
  refine ⟨2 * cells.length, ?_⟩
  have h :=
    description_rightCopy_cells baseLeft guarded.left [] cells suffix
  simpa [guarded, baseLeft, cells, suffix, rightCopyConfig,
    afterLeftCopyConfig, afterRightCopyConfig, rightEdgeOutputTape,
    targetCells, logicalTapeCode, logicalCellListCode,
    logicalCellListBits, tapeAtEncodedSplit, List.map_append,
    List.reverse_append, List.append_assoc] using h

theorem description_enters_rewind
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    description.runConfig 1
      (afterRightCopyConfig target rest encodedPrefix) =
      rewindStartConfig target rest encodedPrefix := by
  cases target with
  | mk left head right =>
      cases rest with
      | nil =>
          three_tape_step [
            description, rows, afterRightCopyConfig, rewindStartConfig,
            rightEdgeOutputTape, targetCells, guardLogicalTape,
            logicalTapeCode, encodedStructuredTapeCells, tapeAtEncodedSplit,
            tapeSeparatorCells]
      | cons next rest =>
          three_tape_step [
            description, rows, afterRightCopyConfig, rewindStartConfig,
            rightEdgeOutputTape, targetCells, guardLogicalTape,
            logicalTapeCode, encodedStructuredTapeCells, tapeAtEncodedSplit,
            tapeSeparatorCells]

theorem description_rewinds_to_markerSecondConfig
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    exists steps : Nat,
      description.runConfig steps
        (rewindStartConfig target rest encodedPrefix) =
        rewindMarkerSecondConfig target rest encodedPrefix := by
  cases target with
  | mk left head right =>
      let guarded : Tape Bool :=
        guardLogicalTape { left := left, head := head, right := right }
      let stack : List (Option Bool) :=
        (guarded.head :: guarded.right).reverse
      let baseLeft : List (Option Bool) :=
        List.append [some true, some true]
          (List.append encodedPrefix
            (List.append tapeSeparatorCells
              (logicalCellListCode guarded.left.reverse))).reverse
      refine ⟨2 * stack.length, ?_⟩
      have h :=
        description_rewinds_cellStackConfig
          baseLeft stack (encodedStructuredTapeCells rest)
          guarded.left []
      cases rest with
      | nil =>
          cases head with
          | none =>
              simpa [guarded, stack, baseLeft, rewindStartConfig,
                rewindMarkerSecondConfig, rewindCellStackConfig,
                rewindCellStackDoneConfig,
                selectedSegmentLogicalTapeDecoderRawHeadOutputTape,
                rightEdgeOutputTape, targetCells, guardLogicalTape,
                logicalTapeCode, tapeAtEncodedSplit, tapeSeparatorCells,
                headMarkerCells, rewindOutputCurrentCells,
                logicalCellListBits, logicalCellBits, List.map_append,
                ThreeTape.keepL, Structured.TapeAction.apply,
                Structured.HeadMove.apply,
                Tape.move, Tape.moveLeft, tapeAtCells,
                List.reverse_append, List.append_assoc] using h
          | some bit =>
              cases bit <;>
                simpa [guarded, stack, baseLeft, rewindStartConfig,
                  rewindMarkerSecondConfig, rewindCellStackConfig,
                  rewindCellStackDoneConfig,
                  selectedSegmentLogicalTapeDecoderRawHeadOutputTape,
                  rightEdgeOutputTape, targetCells, guardLogicalTape,
                  logicalTapeCode, tapeAtEncodedSplit, tapeSeparatorCells,
                  headMarkerCells, rewindOutputCurrentCells,
                  logicalCellListBits, logicalCellBits, List.map_append,
                  ThreeTape.keepL, Structured.TapeAction.apply,
                  Structured.HeadMove.apply,
                  Tape.move, Tape.moveLeft, tapeAtCells,
                  List.reverse_append, List.append_assoc] using h
      | cons next restTail =>
          cases head with
          | none =>
              simpa [guarded, stack, baseLeft, rewindStartConfig,
                rewindMarkerSecondConfig, rewindCellStackConfig,
                rewindCellStackDoneConfig,
                selectedSegmentLogicalTapeDecoderRawHeadOutputTape,
                rightEdgeOutputTape, targetCells, guardLogicalTape,
                logicalTapeCode, tapeAtEncodedSplit, tapeSeparatorCells,
                headMarkerCells, rewindOutputCurrentCells,
                logicalCellListBits, logicalCellBits, List.map_append,
                ThreeTape.keepL, Structured.TapeAction.apply,
                Structured.HeadMove.apply,
                Tape.move, Tape.moveLeft, tapeAtCells,
                List.reverse_append, List.append_assoc] using h
          | some bit =>
              cases bit <;>
                simpa [guarded, stack, baseLeft, rewindStartConfig,
                  rewindMarkerSecondConfig, rewindCellStackConfig,
                  rewindCellStackDoneConfig,
                  selectedSegmentLogicalTapeDecoderRawHeadOutputTape,
                  rightEdgeOutputTape, targetCells, guardLogicalTape,
                  logicalTapeCode, tapeAtEncodedSplit, tapeSeparatorCells,
                  headMarkerCells, rewindOutputCurrentCells,
                  logicalCellListBits, logicalCellBits, List.map_append,
                  ThreeTape.keepL, Structured.TapeAction.apply,
                  Structured.HeadMove.apply,
                  Tape.move, Tape.moveLeft, tapeAtCells,
                  List.reverse_append, List.append_assoc] using h

theorem description_rewinds_markerSecond_to_finalConfig
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    description.runConfig 2
      (rewindMarkerSecondConfig target rest encodedPrefix) =
      finalConfig target rest encodedPrefix := by
  cases target with
  | mk left head right =>
      cases head with
      | none =>
          three_tape_step [
            description, rows, rewindMarkerSecondConfig, finalConfig,
            selectedSegmentLogicalTapeDecoderRawHeadOutputTape,
            selectedSegmentLogicalTapeDecoderRawHeadFinalSourceTape,
            guardLogicalTape, logicalCellListCode, logicalCellCode,
            encodedStructuredTapeCells, tapeAtEncodedSplit,
            tapeSeparatorCells, headMarkerCells]
      | some bit =>
          cases bit <;>
            three_tape_step [
              description, rows, rewindMarkerSecondConfig, finalConfig,
              selectedSegmentLogicalTapeDecoderRawHeadOutputTape,
              selectedSegmentLogicalTapeDecoderRawHeadFinalSourceTape,
              guardLogicalTape, logicalCellListCode, logicalCellCode,
              encodedStructuredTapeCells, tapeAtEncodedSplit,
              tapeSeparatorCells, headMarkerCells]

theorem description_rewinds_to_finalConfig
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    exists steps : Nat,
      description.runConfig steps
        (rewindStartConfig target rest encodedPrefix) =
        finalConfig target rest encodedPrefix := by
  rcases description_rewinds_to_markerSecondConfig target rest encodedPrefix with
    ⟨steps, hsteps⟩
  refine ⟨steps + 2, ?_⟩
  rw [Description.runConfig_add]
  rw [hsteps]
  exact description_rewinds_markerSecond_to_finalConfig
    target rest encodedPrefix

theorem description_reaches_finalConfig
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    exists steps : Nat,
      description.runConfig steps
        (afterRightCopyConfig target rest encodedPrefix) =
        finalConfig target rest encodedPrefix := by
  rcases description_rewinds_to_finalConfig target rest encodedPrefix with
    ⟨steps, hsteps⟩
  refine ⟨1 + steps, ?_⟩
  rw [Description.runConfig_add]
  rw [description_enters_rewind target rest encodedPrefix]
  exact hsteps

theorem description_haltsWithTapes
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    description.HaltsWithTapes
      (initialConfig target rest encodedPrefix)
      (finalConfig target rest encodedPrefix).tapes := by
  rcases
    description_reaches_afterLeftCopyConfig target rest encodedPrefix with
    ⟨leftSteps, hleft⟩
  rcases
    description_reaches_afterRightCopyConfig target rest encodedPrefix with
    ⟨rightSteps, hright⟩
  rcases
    description_reaches_finalConfig target rest encodedPrefix with
    ⟨rewindSteps, hrewind⟩
  refine ⟨(leftSteps + rightSteps) + rewindSteps, ?_⟩
  simpa [finalConfig] using
    ThreeTape.runConfig_chain3 hleft hright hrewind

theorem loweredDescription_haltsFromTapeEquiv
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    loweredDescription.HaltsFromTapeEquiv
      (selectedSegmentLogicalTapeDecoderRawHeadStructuredInputTape
        target rest encodedPrefix)
      (selectedSegmentLogicalTapeDecoderRawHeadStructuredOutputTape
        target rest encodedPrefix) := by
  simpa [
    loweredDescription,
    initialConfig,
    finalConfig,
    selectedSegmentLogicalTapeDecoderRawHeadStructuredInputTape,
    selectedSegmentLogicalTapeDecoderRawHeadStructuredOutputTape,
    encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      description_wellFormed
      description_haltTransitionFree
      description_supportsReadWriteRows3
      (c := initialConfig target rest encodedPrefix)
      (tapes := (finalConfig target rest encodedPrefix).tapes)
      (by rfl)
      (by rfl)
      (description_haltsWithTapes target rest encodedPrefix)

theorem loweredDescription_spec :
    SelectedSegmentLogicalTapeDecoderRawHeadThreeTapeNormalizerSpec
      loweredDescription := by
  constructor
  · exact loweredDescription_subroutineReady
  · intro target rest encodedPrefix
    exact loweredDescription_haltsFromTapeEquiv target rest encodedPrefix

theorem construction :
    SelectedSegmentLogicalTapeDecoderRawHeadThreeTapeNormalizerConstruction :=
  ⟨loweredDescription, loweredDescription_spec⟩

end SelectedSegmentLogicalTapeDecoderRawHeadNormalizer

def SelectedSegmentLogicalTapeDecoderPaddedCleanupSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (padding : List (Option Bool))
      (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
          target padding encodedPrefix)
        target

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupSpec_of_guardedCellShapeSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderGuardedCellShapeCleanupSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderPaddedCleanupSpec cleanup := by
  rcases hcleanup with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro target padding encodedPrefix
  rcases hrun target padding encodedPrefix with
    ⟨actual, hhalts, hequiv⟩
  exact
    ⟨actual, hhalts,
      Tape.Equiv.trans hequiv (guardLogicalTape_equiv target)⟩

def SelectedSegmentLogicalTapeDecoderPaddedCleanupConstruction : Prop :=
  exists cleanup : MachineDescription,
    SelectedSegmentLogicalTapeDecoderPaddedCleanupSpec cleanup

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupConstruction_of_guardedCellShape
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderGuardedCellShapeCleanupConstruction) :
    SelectedSegmentLogicalTapeDecoderPaddedCleanupConstruction := by
  rcases hcleanup with ⟨cleanup, hspec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderPaddedCleanupSpec_of_guardedCellShapeSpec
        hspec⟩

def SelectedSegmentLogicalTapeDecoderPaddedCleanupNilPaddingSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
          target [] encodedPrefix)
        target

def SelectedSegmentLogicalTapeDecoderPaddedCleanupConsPaddingSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (pad : Option Bool)
      (padding encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
          target (pad :: padding) encodedPrefix)
        target

def SelectedSegmentLogicalTapeDecoderPaddedCleanupSplitSpec
    (cleanup : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderPaddedCleanupNilPaddingSpec cleanup ∧
    SelectedSegmentLogicalTapeDecoderPaddedCleanupConsPaddingSpec cleanup

def SelectedSegmentLogicalTapeDecoderPaddedCleanupSplitConstruction : Prop :=
  exists cleanup : MachineDescription,
    SelectedSegmentLogicalTapeDecoderPaddedCleanupSplitSpec cleanup

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupSplitSpec_of_spec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedCleanupSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderPaddedCleanupSplitSpec cleanup := by
  rcases hcleanup with ⟨hready, hrun⟩
  constructor
  · exact
      ⟨hready, fun target encodedPrefix =>
        hrun target [] encodedPrefix⟩
  · exact
      ⟨hready, fun target pad padding encodedPrefix =>
        hrun target (pad :: padding) encodedPrefix⟩

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupSpec_of_splitSpec
    {cleanup : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderPaddedCleanupSplitSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderPaddedCleanupSpec cleanup := by
  rcases hsplit with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilRun⟩
  rcases hcons with ⟨_hreadyCons, hconsRun⟩
  refine ⟨hready, ?_⟩
  intro target padding encodedPrefix
  cases padding with
  | nil =>
      exact hnilRun target encodedPrefix
  | cons pad padding =>
      exact hconsRun target pad padding encodedPrefix

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupConstruction_of_split
    (hsplit :
      SelectedSegmentLogicalTapeDecoderPaddedCleanupSplitConstruction) :
    SelectedSegmentLogicalTapeDecoderPaddedCleanupConstruction := by
  rcases hsplit with ⟨cleanup, hsplitSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderPaddedCleanupSpec_of_splitSpec
        hsplitSpec⟩

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupSplitConstruction_of_construction
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedCleanupConstruction) :
    SelectedSegmentLogicalTapeDecoderPaddedCleanupSplitConstruction := by
  rcases hcleanup with ⟨cleanup, hspec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderPaddedCleanupSplitSpec_of_spec
        hspec⟩

/-!
## Exact padded cleanup

The equivalence-facing padded cleanup above is enough for normalized-output
projection, but exact endpoint projectors need the cleanup phase to start from
the canonical sequence handoff tape and halt on the literal target tape.  The
selected-head exact route below is just the specialization where the padding is
the encoded rest block after the selected logical tape.
-/

def SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (padding : List (Option Bool))
      (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape
          (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
            target padding encodedPrefix))
        target

def SelectedSegmentLogicalTapeDecoderPaddedExactCleanupClosedSpec
    (cleanup : MachineDescription) : Prop :=
  forall (target : Tape Bool) (padding : List (Option Bool))
      (encodedPrefix : List (Option Bool)),
    ExactClosedFromTape cleanup
      (canonicalPrimitiveSeqHandoffTape
        (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
          target padding encodedPrefix))
      target

/--
Exact cleanup for a padded scanner target.

This is the reusable exact boundary below the selected-head route.  The
selected-head exact cleanup specializes {lit}`padding` to
{name}`selectedSegmentLogicalTapeDecoderRestPadding`.
-/
structure SelectedSegmentLogicalTapeDecoderPaddedExactCleanupSpec
    (cleanup : MachineDescription) : Prop where
  subroutineReady : cleanup.SubroutineReady
  forward :
    forall (target : Tape Bool) (padding : List (Option Bool))
      (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape
          (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
            target padding encodedPrefix))
        target
  closed :
    forall (target : Tape Bool) (padding : List (Option Bool))
      (encodedPrefix : List (Option Bool)),
      ExactClosedFromTape cleanup
        (canonicalPrimitiveSeqHandoffTape
          (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
            target padding encodedPrefix))
        target

def SelectedSegmentLogicalTapeDecoderPaddedExactCleanupConstruction :
    Prop :=
  exists cleanup : MachineDescription,
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupSpec cleanup

namespace SelectedSegmentLogicalTapeDecoderPaddedExactCleanupSpec

theorem toCleanupSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderPaddedCleanupSpec cleanup := by
  constructor
  · exact hcleanup.subroutineReady
  · intro target padding encodedPrefix
    exact
      HaltsFromTapeEquiv_of_input_equiv
        (D := cleanup)
        (Tin :=
          canonicalPrimitiveSeqHandoffTape
            (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
              target padding encodedPrefix))
        (Tin' :=
          selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
            target padding encodedPrefix)
        (Tout := target)
        (canonicalPrimitiveSeqHandoffTape_equiv
          (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
            target padding encodedPrefix))
        (hcleanup.forward target padding encodedPrefix)

theorem forwardSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSpec
      cleanup :=
  ⟨hcleanup.subroutineReady, hcleanup.forward⟩

theorem closedSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupClosedSpec
      cleanup :=
  hcleanup.closed

end SelectedSegmentLogicalTapeDecoderPaddedExactCleanupSpec

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupConstruction_of_exact
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupConstruction) :
    SelectedSegmentLogicalTapeDecoderPaddedCleanupConstruction := by
  rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
  exact ⟨cleanup, hcleanupSpec.toCleanupSpec⟩

def SelectedSegmentLogicalTapeDecoderPaddedExactCleanupNilPaddingSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape
          (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
            target [] encodedPrefix))
        target

def SelectedSegmentLogicalTapeDecoderPaddedExactCleanupConsPaddingSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (pad : Option Bool)
      (padding encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape
          (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
            target (pad :: padding) encodedPrefix))
        target

def SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitSpec
    (cleanup : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderPaddedExactCleanupNilPaddingSpec cleanup ∧
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupConsPaddingSpec cleanup

def SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitConstruction :
    Prop :=
  exists cleanup : MachineDescription,
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitSpec cleanup

theorem selectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitSpec_of_spec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitSpec
      cleanup := by
  rcases hcleanup with ⟨hready, hrun⟩
  constructor
  · exact
      ⟨hready, fun target encodedPrefix =>
        hrun target [] encodedPrefix⟩
  · exact
      ⟨hready, fun target pad padding encodedPrefix =>
        hrun target (pad :: padding) encodedPrefix⟩

theorem selectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSpec_of_splitSpec
    {cleanup : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitSpec
        cleanup) :
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSpec
      cleanup := by
  rcases hsplit with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilRun⟩
  rcases hcons with ⟨_hreadyCons, hconsRun⟩
  refine ⟨hready, ?_⟩
  intro target padding encodedPrefix
  cases padding with
  | nil =>
      exact hnilRun target encodedPrefix
  | cons pad padding =>
      exact hconsRun target pad padding encodedPrefix

theorem selectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardConstruction_of_split
    (hsplit :
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitConstruction) :
    exists cleanup : MachineDescription,
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSpec
        cleanup := by
  rcases hsplit with ⟨cleanup, hsplitSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSpec_of_splitSpec
        hsplitSpec⟩

theorem selectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitConstruction_of_cleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupConstruction) :
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitConstruction := by
  rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitSpec_of_spec
        hcleanupSpec.forwardSpec⟩

theorem selectedSegmentLogicalTapeDecoderPaddedExactCleanupSpec_of_forwardSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupSpec cleanup where
  subroutineReady := hcleanup.left
  forward := hcleanup.right
  closed := by
    intro target padding encodedPrefix
    exact
      exactClosedFromTape_of_haltsFromTape_of_subroutineReady
        hcleanup.left
        (hcleanup.right target padding encodedPrefix)

theorem selectedSegmentLogicalTapeDecoderPaddedExactCleanupConstruction_of_forward
    (hcleanup :
      exists cleanup : MachineDescription,
        SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSpec
          cleanup) :
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupConstruction := by
  rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderPaddedExactCleanupSpec_of_forwardSpec
        hcleanupSpec⟩

theorem selectedSegmentLogicalTapeDecoderPaddedExactCleanupConstruction_of_forwardSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitConstruction) :
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupConstruction :=
  selectedSegmentLogicalTapeDecoderPaddedExactCleanupConstruction_of_forward
    (selectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardConstruction_of_split
      hsplit)

theorem selectedSegmentLogicalTapeDecoderPaddedExactCleanupConstruction_iff_forwardSplit :
    SelectedSegmentLogicalTapeDecoderPaddedExactCleanupConstruction <->
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitConstruction := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitConstruction_of_cleanup
  · exact
      selectedSegmentLogicalTapeDecoderPaddedExactCleanupConstruction_of_forwardSplit

/-- Cleanup needed after the padded selected-head bit decoder. -/
def SelectedSegmentLogicalTapeDecoderHeadCleanupSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (rest : List (Tape Bool))
      (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderHeadTargetTape
          target rest encodedPrefix)
        target

/-- Existence wrapper for the padded selected-head cleanup phase. -/
def SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction : Prop :=
  exists cleanup : MachineDescription,
    SelectedSegmentLogicalTapeDecoderHeadCleanupSpec cleanup

/--
Exact cleanup for a padded selected-head scanner target.

The input is the canonical primitive-sequence handoff tape for the scanner
target, because this cleanup runs as the right-hand component of
{lit}`selectedSegmentLogicalTapeDecoderHeadPipelineDescription`.
-/
def SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (rest : List (Tape Bool))
      (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape
          (selectedSegmentLogicalTapeDecoderHeadTargetTape
            target rest encodedPrefix))
        target

/--
Closed exact cleanup for padded selected-head scanner targets.
-/
def SelectedSegmentLogicalTapeDecoderHeadExactCleanupClosedSpec
    (cleanup : MachineDescription) : Prop :=
  forall (target : Tape Bool) (rest : List (Tape Bool))
      (encodedPrefix : List (Option Bool)),
    ExactClosedFromTape cleanup
      (canonicalPrimitiveSeqHandoffTape
        (selectedSegmentLogicalTapeDecoderHeadTargetTape
          target rest encodedPrefix))
      target

/--
Exact cleanup boundary for selected-head projection.

This is the construction target needed by literal endpoint projectors; the
older cleanup route below remains the equivalence-facing compatibility layer.
-/
structure SelectedSegmentLogicalTapeDecoderHeadExactCleanupSpec
    (cleanup : MachineDescription) : Prop where
  subroutineReady : cleanup.SubroutineReady
  forward :
    forall (target : Tape Bool) (rest : List (Tape Bool))
      (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape
          (selectedSegmentLogicalTapeDecoderHeadTargetTape
            target rest encodedPrefix))
        target
  closed :
    forall (target : Tape Bool) (rest : List (Tape Bool))
      (encodedPrefix : List (Option Bool)),
      ExactClosedFromTape cleanup
        (canonicalPrimitiveSeqHandoffTape
          (selectedSegmentLogicalTapeDecoderHeadTargetTape
            target rest encodedPrefix))
        target

/-- Existence wrapper for the exact selected-head cleanup route. -/
def SelectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction :
    Prop :=
  exists cleanup : MachineDescription,
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupSpec cleanup

namespace SelectedSegmentLogicalTapeDecoderHeadExactCleanupSpec

/-- Exact selected-head cleanup implies the older equivalence cleanup route. -/
theorem toCleanupSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderHeadCleanupSpec cleanup := by
  constructor
  · exact hcleanup.subroutineReady
  · intro target rest encodedPrefix
    exact
      HaltsFromTapeEquiv_of_input_equiv
        (D := cleanup)
        (Tin :=
          canonicalPrimitiveSeqHandoffTape
            (selectedSegmentLogicalTapeDecoderHeadTargetTape
              target rest encodedPrefix))
        (Tin' :=
          selectedSegmentLogicalTapeDecoderHeadTargetTape
            target rest encodedPrefix)
        (Tout := target)
        (canonicalPrimitiveSeqHandoffTape_equiv
          (selectedSegmentLogicalTapeDecoderHeadTargetTape
            target rest encodedPrefix))
        (hcleanup.forward target rest encodedPrefix)

/-- Forward-only view of an exact selected-head cleanup. -/
theorem forwardSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSpec
      cleanup := by
  exact ⟨hcleanup.subroutineReady, hcleanup.forward⟩

/-- Closed-only view of an exact selected-head cleanup. -/
theorem closedSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupClosedSpec
      cleanup :=
  hcleanup.closed

end SelectedSegmentLogicalTapeDecoderHeadExactCleanupSpec

/--
Construction-level adapter from exact selected-head cleanup to the existing
equivalence cleanup construction.
-/
theorem selectedSegmentLogicalTapeDecoderHeadCleanupConstruction_of_exact
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction) :
    SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction := by
  rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
  exact
    ⟨cleanup,
      hcleanupSpec.toCleanupSpec⟩

/--
Exact cleanup branch where there is no encoded structured suffix after the
selected segment.
-/
def SelectedSegmentLogicalTapeDecoderHeadExactCleanupNilRestSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape
          (selectedSegmentLogicalTapeDecoderHeadTargetTape
            target [] encodedPrefix))
        target

/--
Exact cleanup branch where the selected segment is followed by at least one
encoded structured tape.
-/
def SelectedSegmentLogicalTapeDecoderHeadExactCleanupConsRestSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target next : Tape Bool) (rest : List (Tape Bool))
      (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape
          (selectedSegmentLogicalTapeDecoderHeadTargetTape
            target (next :: rest) encodedPrefix))
        target

/-- Branch split for exact selected-head cleanup forward behavior. -/
def SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitSpec
    (cleanup : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderHeadExactCleanupNilRestSpec cleanup ∧
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupConsRestSpec cleanup

/-- Construction wrapper for the exact forward branch split. -/
def SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction :
    Prop :=
  exists cleanup : MachineDescription,
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitSpec cleanup

/-- Split exact cleanup forward behavior into nil-rest and cons-rest branches. -/
theorem selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitSpec_of_spec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitSpec
      cleanup := by
  constructor
  · constructor
    · exact hcleanup.left
    · intro target encodedPrefix
      exact hcleanup.right target [] encodedPrefix
  · constructor
    · exact hcleanup.left
    · intro target next rest encodedPrefix
      exact hcleanup.right target (next :: rest) encodedPrefix

/-- Reassemble exact cleanup forward behavior from branch cases. -/
theorem selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSpec_of_splitSpec
    {cleanup : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitSpec
        cleanup) :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSpec
      cleanup := by
  rcases hsplit with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilRun⟩
  rcases hcons with ⟨_hreadyCons, hconsRun⟩
  refine ⟨hready, ?_⟩
  intro target rest encodedPrefix
  cases rest with
  | nil =>
      exact hnilRun target encodedPrefix
  | cons next rest =>
      exact hconsRun target next rest encodedPrefix

/-- Construction-level split adapter from exact cleanup forward behavior. -/
theorem selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction_of_cleanup
    (hcleanup :
      exists cleanup : MachineDescription,
        SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSpec
          cleanup) :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction := by
  rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitSpec_of_spec
        hcleanupSpec⟩

/-- Construction-level exact cleanup forward behavior from branch cases. -/
theorem selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardConstruction_of_split
    (hsplit :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction) :
    exists cleanup : MachineDescription,
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSpec
        cleanup := by
  rcases hsplit with ⟨cleanup, hsplitSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSpec_of_splitSpec
        hsplitSpec⟩

/--
Forward exact selected-head cleanup already gives exact closedness.

The cleanup machine is subroutine-ready, so finite-control execution from the
same input tape is deterministic.  Any public halt from one of these cleanup
inputs therefore has the same literal target as the forward run.
-/
theorem selectedSegmentLogicalTapeDecoderHeadExactCleanupSpec_of_forwardSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupSpec cleanup where
  subroutineReady := hcleanup.left
  forward := hcleanup.right
  closed := by
    intro target rest encodedPrefix
    exact
      exactClosedFromTape_of_haltsFromTape_of_subroutineReady
        hcleanup.left
        (hcleanup.right target rest encodedPrefix)

/--
Construction-level exact selected-head cleanup from forward exact cleanup.
-/
theorem selectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction_of_forward
    (hcleanup :
      exists cleanup : MachineDescription,
        SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSpec
          cleanup) :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction := by
  rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderHeadExactCleanupSpec_of_forwardSpec
        hcleanupSpec⟩

/--
Construction-level exact selected-head cleanup from the forward branch split.
-/
theorem selectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction_of_forwardSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction) :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction :=
  selectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction_of_forward
    (selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardConstruction_of_split
      hsplit)

/--
The forward split and full exact selected-head cleanup constructions are
equivalent construction targets.
-/
theorem selectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction_iff_forwardSplit :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction <->
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction := by
  constructor
  · intro hcleanup
    rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
    exact
      ⟨cleanup,
        selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitSpec_of_spec
          hcleanupSpec.forwardSpec⟩
  · exact
      selectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction_of_forwardSplit

theorem selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitSpec_of_paddedExactCleanupForwardSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSpec
        cleanup) :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitSpec
      cleanup := by
  rcases hcleanup with ⟨hready, hrun⟩
  constructor
  · constructor
    · exact hready
    · intro target encodedPrefix
      simpa [
        selectedSegmentLogicalTapeDecoderHeadTargetTape_eq_paddedCleanupSourceTape] using
        hrun target
          (selectedSegmentLogicalTapeDecoderRestPadding [])
          encodedPrefix
  · constructor
    · exact hready
    · intro target next rest encodedPrefix
      simpa [
        selectedSegmentLogicalTapeDecoderHeadTargetTape_eq_paddedCleanupSourceTape] using
        hrun target
          (selectedSegmentLogicalTapeDecoderRestPadding (next :: rest))
          encodedPrefix

theorem selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction_of_paddedExactCleanupForward
    (hcleanup :
      exists cleanup : MachineDescription,
        SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSpec
          cleanup) :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction := by
  rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitSpec_of_paddedExactCleanupForwardSpec
        hcleanupSpec⟩

theorem selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction_of_paddedExactCleanupForwardSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitConstruction) :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction :=
  selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction_of_paddedExactCleanupForward
    (selectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardConstruction_of_split
      hsplit)

theorem selectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction_of_paddedExactCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedExactCleanupConstruction) :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction :=
  selectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction_of_forwardSplit
    (selectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction_of_paddedExactCleanupForwardSplit
      (selectedSegmentLogicalTapeDecoderPaddedExactCleanupForwardSplitConstruction_of_cleanup
        hcleanup))

/--
Literal selected-head decoder behavior.

This is stronger than {name}`StructuredSelectedHeadSegmentDecoderSpec`: it
requires exact final tape equality, and its closed side records that any halt
from the selected-head source has that literal target.
-/
structure StructuredSelectedHeadSegmentDecoderExactSpec
    (decoder : MachineDescription) : Prop where
  subroutineReady : decoder.SubroutineReady
  forward :
    forall (target : Tape Bool) (rest : List (Tape Bool))
      (encodedPrefix : List (Option Bool)),
      decoder.HaltsFromTape
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells (guardLogicalTape target :: rest)))
        target
  closed :
    forall (target : Tape Bool) (rest : List (Tape Bool))
      (encodedPrefix : List (Option Bool)),
      ExactClosedFromTape decoder
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells (guardLogicalTape target :: rest)))
        target

/-- Existence wrapper for literal selected-head decoder behavior. -/
def StructuredSelectedHeadSegmentDecoderExactConstruction : Prop :=
  exists decoder : MachineDescription,
    StructuredSelectedHeadSegmentDecoderExactSpec decoder

namespace StructuredSelectedHeadSegmentDecoderExactSpec

/-- Literal selected-head decoding implies the existing equivalence route. -/
theorem toSpec
    {decoder : MachineDescription}
    (hdecoder :
      StructuredSelectedHeadSegmentDecoderExactSpec decoder) :
    StructuredSelectedHeadSegmentDecoderSpec decoder := by
  constructor
  · exact hdecoder.subroutineReady
  · intro target rest encodedPrefix
    exact (hdecoder.forward target rest encodedPrefix).toEquiv

end StructuredSelectedHeadSegmentDecoderExactSpec

/--
Construction-level adapter from literal selected-head decoding to the existing
equivalence selected-head decoder construction.
-/
theorem structuredSelectedHeadSegmentDecoderConstruction_of_exact
    (hdecoder :
      StructuredSelectedHeadSegmentDecoderExactConstruction) :
    StructuredSelectedHeadSegmentDecoderConstruction := by
  rcases hdecoder with ⟨decoder, hdecoderSpec⟩
  exact
    ⟨decoder,
      hdecoderSpec.toSpec⟩

/--
Literal tape-2 segment normalizer behavior at an already-selected segment.
-/
structure StructuredTape2ExactSegmentNormalizerSpec
    (normalizer : MachineDescription) : Prop where
  subroutineReady : normalizer.SubroutineReady
  forward :
    forall (T0 T1 T2 : Tape Bool) (physical : Tape Bool),
      AtTapeSeparator (guardLogicalTapes [T0, T1, T2]) 2 physical ->
        normalizer.HaltsFromTape physical T2
  closed :
    forall (T0 T1 T2 : Tape Bool) (physical : Tape Bool),
      AtTapeSeparator (guardLogicalTapes [T0, T1, T2]) 2 physical ->
        ExactClosedFromTape normalizer physical T2

/-- Existence wrapper for literal tape-2 segment normalization. -/
def StructuredTape2ExactSegmentNormalizerConstruction : Prop :=
  exists normalizer : MachineDescription,
    StructuredTape2ExactSegmentNormalizerSpec normalizer

namespace StructuredTape2ExactSegmentNormalizerSpec

/-- Literal tape-2 segment normalization implies the equivalence normalizer. -/
theorem toSegmentNormalizerSpec
    {normalizer : MachineDescription}
    (hnormalizer :
      StructuredTape2ExactSegmentNormalizerSpec normalizer) :
    StructuredTape2SegmentNormalizerSpec normalizer := by
  constructor
  · exact hnormalizer.subroutineReady
  · intro T0 T1 T2 physical hseparator
    exact (hnormalizer.forward T0 T1 T2 physical hseparator).toEquiv

end StructuredTape2ExactSegmentNormalizerSpec

/--
Construction-level adapter from literal tape-2 segment normalization to the
existing equivalence segment-normalizer construction.
-/
theorem structuredTape2SegmentNormalizerConstruction_of_exact
    (hnormalizer :
      StructuredTape2ExactSegmentNormalizerConstruction) :
    StructuredTape2SegmentNormalizerConstruction := by
  rcases hnormalizer with ⟨normalizer, hnormalizerSpec⟩
  exact
    ⟨normalizer,
      hnormalizerSpec.toSegmentNormalizerSpec⟩

/--
Literal selected-head decoding gives literal tape-2 segment normalization.
-/
theorem structuredTape2ExactSegmentNormalizerConstruction_of_exactHeadDecoder
    (hdecoder :
      StructuredSelectedHeadSegmentDecoderExactConstruction) :
    StructuredTape2ExactSegmentNormalizerConstruction := by
  rcases hdecoder with ⟨decoder, hdecoderSpec⟩
  refine ⟨decoder, ?_⟩
  constructor
  · exact hdecoderSpec.subroutineReady
  · intro T0 T1 T2 physical hseparator
    rcases hseparator with ⟨_hindex, hphysical⟩
    rw [hphysical]
    simpa [encodedSuffixFromTape, guardLogicalTapes] using
      hdecoderSpec.forward T2 []
        (encodedPrefixBeforeTape (guardLogicalTapes [T0, T1, T2]) 2)
  · intro T0 T1 T2 physical hseparator
    rcases hseparator with ⟨_hindex, hphysical⟩
    intro T hhalt
    exact
      hdecoderSpec.closed T2 []
        (encodedPrefixBeforeTape (guardLogicalTapes [T0, T1, T2]) 2)
        T
        (by
          rw [hphysical] at hhalt
          simpa [encodedSuffixFromTape, guardLogicalTapes] using hhalt)

/--
The endpoint handoff bounce is exact on the canonical guarded three-tape
encoding. The encoded block starts with a separator and has a nonempty right
side, so moving right and then left restores the same physical tape literally.
-/
theorem canonicalPrimitiveSeqHandoffTape_encodedGuardedStructured3Tapes
    (T0 T1 T2 : Tape Bool) :
    canonicalPrimitiveSeqHandoffTape
        (encodedGuardedStructured3Tapes T0 T1 T2) =
      encodedGuardedStructured3Tapes T0 T1 T2 := by
  simp [canonicalPrimitiveSeqHandoffTape,
    encodedGuardedStructured3Tapes, encodedGuardedStructuredTapes,
    encodedStructuredTapes, encodedStructuredTapeCells, guardLogicalTapes,
    guardLogicalTape, tapeAtCells, tapeSeparatorCells, logicalTapeCode,
    logicalCellListBits, logicalCellBits, logicalCellCode, headMarkerCells,
    Tape.move, Tape.moveLeft, Tape.moveRight]

/--
The projector-internal handoff bounce is exact at the selected tape-2
separator of a guarded three-tape block.
-/
theorem canonicalPrimitiveSeqHandoffTape_eq_self_of_atTape2Separator
    {T0 T1 T2 physical : Tape Bool}
    (hseparator :
      AtTapeSeparator (guardLogicalTapes [T0, T1, T2]) 2 physical) :
    canonicalPrimitiveSeqHandoffTape physical = physical := by
  rcases hseparator with ⟨_hindex, hphysical⟩
  rw [hphysical]
  simp [canonicalPrimitiveSeqHandoffTape, tapeAtEncodedSplit,
    encodedSuffixFromTape, guardLogicalTapes, guardLogicalTape,
    encodedStructuredTapeCells, tapeAtCells, tapeSeparatorCells,
    logicalTapeCode, logicalCellListBits, logicalCellBits, logicalCellCode,
    headMarkerCells, Tape.move, Tape.moveLeft, Tape.moveRight]

/--
Exact segment-normalizer behavior as a right-hand component of the canonical
tape-2 projector sequence.

The normalizer input is the canonical sequence handoff tape for the separator,
not merely the separator tape itself. This is the exact contract needed by
{name}`canonicalPrimitiveSeqDescription_exactClosedFromTape`.
-/
structure StructuredTape2ExactHandoffSegmentNormalizerSpec
    (normalizer : MachineDescription) : Prop where
  subroutineReady : normalizer.SubroutineReady
  forward :
    forall (T0 T1 T2 : Tape Bool) (physical : Tape Bool),
      AtTapeSeparator (guardLogicalTapes [T0, T1, T2]) 2 physical ->
        normalizer.HaltsFromTape
          (canonicalPrimitiveSeqHandoffTape physical)
          T2
  closed :
    forall (T0 T1 T2 : Tape Bool) (physical : Tape Bool),
      AtTapeSeparator (guardLogicalTapes [T0, T1, T2]) 2 physical ->
        ExactClosedFromTape normalizer
          (canonicalPrimitiveSeqHandoffTape physical)
          T2

/-- Existence wrapper for the exact handoff-facing tape-2 normalizer. -/
def StructuredTape2ExactHandoffSegmentNormalizerConstruction : Prop :=
  exists normalizer : MachineDescription,
    StructuredTape2ExactHandoffSegmentNormalizerSpec normalizer

namespace StructuredTape2ExactHandoffSegmentNormalizerSpec

/--
The handoff-facing exact normalizer still implies the existing equivalence
segment-normalizer contract.
-/
theorem toSegmentNormalizerSpec
    {normalizer : MachineDescription}
    (hnormalizer :
      StructuredTape2ExactHandoffSegmentNormalizerSpec normalizer) :
    StructuredTape2SegmentNormalizerSpec normalizer := by
  constructor
  · exact hnormalizer.subroutineReady
  · intro T0 T1 T2 physical hseparator
    exact
      HaltsFromTapeEquiv_of_input_equiv
        (D := normalizer)
        (Tin := canonicalPrimitiveSeqHandoffTape physical)
        (Tin' := physical)
        (Tout := T2)
        (canonicalPrimitiveSeqHandoffTape_equiv physical)
        (hnormalizer.forward T0 T1 T2 physical hseparator)

end StructuredTape2ExactHandoffSegmentNormalizerSpec

/--
At the concrete tape-2 separator shape, a direct exact normalizer can be used
as the right-hand component of the canonical projector sequence.
-/
theorem structuredTape2ExactHandoffSegmentNormalizerSpec_of_exact
    {normalizer : MachineDescription}
    (hnormalizer :
      StructuredTape2ExactSegmentNormalizerSpec normalizer) :
    StructuredTape2ExactHandoffSegmentNormalizerSpec normalizer := by
  constructor
  · exact hnormalizer.subroutineReady
  · intro T0 T1 T2 physical hseparator
    rw [canonicalPrimitiveSeqHandoffTape_eq_self_of_atTape2Separator
      hseparator]
    exact hnormalizer.forward T0 T1 T2 physical hseparator
  · intro T0 T1 T2 physical hseparator
    intro T hhalt
    exact
      hnormalizer.closed T0 T1 T2 physical hseparator T
        (by
          simpa [canonicalPrimitiveSeqHandoffTape_eq_self_of_atTape2Separator
            hseparator] using hhalt)

/--
Construction-level adapter from direct exact tape-2 segment normalization to
the handoff-facing exact segment-normalizer contract.
-/
theorem structuredTape2ExactHandoffSegmentNormalizerConstruction_of_exact
    (hnormalizer :
      StructuredTape2ExactSegmentNormalizerConstruction) :
    StructuredTape2ExactHandoffSegmentNormalizerConstruction := by
  rcases hnormalizer with ⟨normalizer, hnormalizerSpec⟩
  exact
    ⟨normalizer,
      structuredTape2ExactHandoffSegmentNormalizerSpec_of_exact
        hnormalizerSpec⟩

/--
Exact selected-head decoding supplies the handoff-facing tape-2 segment
normalizer needed by the exact projector route.
-/
theorem structuredTape2ExactHandoffSegmentNormalizerConstruction_of_exactHeadDecoder
    (hdecoder :
      StructuredSelectedHeadSegmentDecoderExactConstruction) :
    StructuredTape2ExactHandoffSegmentNormalizerConstruction :=
  structuredTape2ExactHandoffSegmentNormalizerConstruction_of_exact
    (structuredTape2ExactSegmentNormalizerConstruction_of_exactHeadDecoder
      hdecoder)

/--
Exact run of the tape-2 seeker from the endpoint-bounced guarded three-tape
encoding.
-/
theorem seekTape2Description_haltsFrom_endpointHandoff
    (T0 T1 T2 : Tape Bool) :
    exists physical : Tape Bool,
      seekTape2Description.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape
          (encodedGuardedStructured3Tapes T0 T1 T2))
        physical ∧
        AtTapeSeparator (guardLogicalTapes [T0, T1, T2]) 2 physical := by
  have hsource :
      exists A : Tape Bool, exists B : Tape Bool, exists C : Tape Bool,
        guardLogicalTapes [T0, T1, T2] = [A, B, C] ∧
          AtEncodedBlockStart (guardLogicalTapes [T0, T1, T2])
            (encodedGuardedStructured3Tapes T0 T1 T2) := by
    refine
      ⟨guardLogicalTape T0, guardLogicalTape T1,
        guardLogicalTape T2, ?_, ?_⟩
    · simp [guardLogicalTapes]
    · exact atEncodedBlockStart_self (guardLogicalTapes [T0, T1, T2])
  rcases
      seekTape2Description_contract_three.realizes
        (guardLogicalTapes [T0, T1, T2])
        (encodedGuardedStructured3Tapes T0 T1 T2)
        hsource with
    ⟨physical, hseek, hseparator⟩
  refine ⟨physical, ?_, hseparator⟩
  simpa [canonicalPrimitiveSeqHandoffTape_encodedGuardedStructured3Tapes]
    using hseek

/--
Exact tape-2 projector contract for endpoint use.

The input is the endpoint handoff tape because the projector is itself the
right-hand component of the three-part endpoint wrapper.
-/
structure StructuredTape2ExactProjectorSpec
    (projector : MachineDescription) : Prop where
  subroutineReady : projector.SubroutineReady
  forward :
    forall T0 T1 T2 : Tape Bool,
      projector.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape
          (encodedGuardedStructured3Tapes T0 T1 T2))
        T2
  closed :
    forall T0 T1 T2 : Tape Bool,
      ExactClosedFromTape projector
        (canonicalPrimitiveSeqHandoffTape
          (encodedGuardedStructured3Tapes T0 T1 T2))
        T2

/-- Existence wrapper for {name}`StructuredTape2ExactProjectorSpec`. -/
def StructuredTape2ExactProjectorConstruction : Prop :=
  exists projector : MachineDescription,
    StructuredTape2ExactProjectorSpec projector

namespace StructuredTape2ExactProjectorSpec

/-- Exact tape-2 projection implies the existing equivalence projector route. -/
theorem toProjectorSpec
    {projector : MachineDescription}
    (hprojector :
      StructuredTape2ExactProjectorSpec projector) :
    StructuredTape2ProjectorSpec projector := by
  constructor
  · exact hprojector.subroutineReady
  · intro T0 T1 T2
    have hforward := hprojector.forward T0 T1 T2
    rw [canonicalPrimitiveSeqHandoffTape_encodedGuardedStructured3Tapes]
      at hforward
    exact hforward.toEquiv

end StructuredTape2ExactProjectorSpec

/--
Lift a handoff-facing exact tape-2 segment normalizer through the tape-2
seeker to obtain the endpoint-facing exact tape-2 projector.
-/
theorem structuredTape2ExactProjectorSpec_of_handoffSegmentNormalizerSpec
    {normalizer : MachineDescription}
    (hnormalizer :
      StructuredTape2ExactHandoffSegmentNormalizerSpec normalizer) :
    StructuredTape2ExactProjectorSpec
      (structuredTape2ProjectorDescription normalizer) := by
  constructor
  · exact
      structuredTape2ProjectorDescription_subroutineReady
        hnormalizer.subroutineReady
  · intro T0 T1 T2
    rcases seekTape2Description_haltsFrom_endpointHandoff T0 T1 T2 with
      ⟨physical, hseek, hseparator⟩
    exact
      canonicalPrimitiveSeqDescription_haltsFromTape_exact
        seekTape2Description_subroutineReady
        hnormalizer.subroutineReady
        hseek
        (hnormalizer.forward T0 T1 T2 physical hseparator)
  · intro T0 T1 T2
    rcases seekTape2Description_haltsFrom_endpointHandoff T0 T1 T2 with
      ⟨physical, hseek, hseparator⟩
    exact
      canonicalPrimitiveSeqDescription_exactClosedFromTape
        seekTape2Description_subroutineReady
        hnormalizer.subroutineReady
        (by
          intro T hhalt
          exact
            MachineDescription.haltsFromTape_functional_of_haltTransitionFree
              seekTape2Description_subroutineReady.right hhalt hseek)
        (hnormalizer.closed T0 T1 T2 physical hseparator)

/--
Construction-level exact tape-2 projector from a handoff-facing exact segment
normalizer.
-/
theorem structuredTape2ExactProjectorConstruction_of_handoffSegmentNormalizerConstruction
    (hnormalizer :
      StructuredTape2ExactHandoffSegmentNormalizerConstruction) :
    StructuredTape2ExactProjectorConstruction := by
  rcases hnormalizer with ⟨normalizer, hnormalizerSpec⟩
  exact
    ⟨structuredTape2ProjectorDescription normalizer,
      structuredTape2ExactProjectorSpec_of_handoffSegmentNormalizerSpec
        hnormalizerSpec⟩

/--
Construction-level exact tape-2 projector from a direct exact segment
normalizer.
-/
theorem structuredTape2ExactProjectorConstruction_of_exactSegmentNormalizerConstruction
    (hnormalizer :
      StructuredTape2ExactSegmentNormalizerConstruction) :
    StructuredTape2ExactProjectorConstruction :=
  structuredTape2ExactProjectorConstruction_of_handoffSegmentNormalizerConstruction
    (structuredTape2ExactHandoffSegmentNormalizerConstruction_of_exact
      hnormalizer)

/--
Exact selected-head decoding supplies the endpoint-facing exact tape-2
projector.
-/
theorem structuredTape2ExactProjectorConstruction_of_exactHeadDecoder
    (hdecoder :
      StructuredSelectedHeadSegmentDecoderExactConstruction) :
    StructuredTape2ExactProjectorConstruction :=
  structuredTape2ExactProjectorConstruction_of_exactSegmentNormalizerConstruction
    (structuredTape2ExactSegmentNormalizerConstruction_of_exactHeadDecoder
      hdecoder)

/--
Construction-level adapter from the exact tape-2 projector to the existing
equivalence projector route.
-/
theorem structuredTape2ProjectorConstruction_of_exact
    (hprojector :
      StructuredTape2ExactProjectorConstruction) :
    StructuredTape2ProjectorConstruction := by
  rcases hprojector with ⟨projector, hprojectorSpec⟩
  exact ⟨projector, hprojectorSpec.toProjectorSpec⟩

theorem selectedSegmentLogicalTapeDecoderHeadCleanupSpec_of_paddedCleanupSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedCleanupSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderHeadCleanupSpec cleanup := by
  rcases hcleanup with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro target rest encodedPrefix
  simpa [
    selectedSegmentLogicalTapeDecoderHeadTargetTape_eq_paddedCleanupSourceTape] using
    hrun target (selectedSegmentLogicalTapeDecoderRestPadding rest)
      encodedPrefix

theorem selectedSegmentLogicalTapeDecoderHeadCleanupConstruction_of_paddedCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedCleanupConstruction) :
    SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction := by
  rcases hcleanup with ⟨cleanup, hspec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderHeadCleanupSpec_of_paddedCleanupSpec
        hspec⟩

/-- Singleton cleanup follows from padded selected-head cleanup. -/
theorem selectedSegmentLogicalTapeDecoderCleanupSpec_of_headCleanupSpec
    {cleanup : MachineDescription}
    (hcleanup : SelectedSegmentLogicalTapeDecoderHeadCleanupSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderCleanupSpec cleanup := by
  constructor
  · exact hcleanup.left
  · intro target encodedPrefix
    simpa [selectedSegmentLogicalTapeDecoderHeadTargetTape_nil] using
      hcleanup.right target [] encodedPrefix

/-- Construction-level singleton cleanup adapter. -/
theorem selectedSegmentLogicalTapeDecoderCleanupConstruction_of_headCleanup
    (hcleanup : SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    SelectedSegmentLogicalTapeDecoderCleanupConstruction := by
  rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderCleanupSpec_of_headCleanupSpec
        hcleanupSpec⟩

/--
The converse is intentionally absent.  Singleton cleanup does not know how to
discard or preserve arbitrary encoded structured suffixes after the selected
segment.
-/
def SelectedSegmentLogicalTapeDecoderHeadCleanupNilRestSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderHeadTargetTape
          target [] encodedPrefix)
        target

/--
Cleanup branch where the selected segment is followed by at least one encoded
structured tape.
-/
def SelectedSegmentLogicalTapeDecoderHeadCleanupConsRestSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target next : Tape Bool) (rest : List (Tape Bool))
      (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderHeadTargetTape
          target (next :: rest) encodedPrefix)
        target

/-- Branch split for padded selected-head cleanup. -/
def SelectedSegmentLogicalTapeDecoderHeadCleanupSplitSpec
    (cleanup : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderHeadCleanupNilRestSpec cleanup ∧
    SelectedSegmentLogicalTapeDecoderHeadCleanupConsRestSpec cleanup

/-- Construction wrapper for the branch-split cleanup view. -/
def SelectedSegmentLogicalTapeDecoderHeadCleanupSplitConstruction : Prop :=
  exists cleanup : MachineDescription,
    SelectedSegmentLogicalTapeDecoderHeadCleanupSplitSpec cleanup

/-- Split padded selected-head cleanup into nil-rest and cons-rest branches. -/
theorem selectedSegmentLogicalTapeDecoderHeadCleanupSplitSpec_of_spec
    {cleanup : MachineDescription}
    (hcleanup : SelectedSegmentLogicalTapeDecoderHeadCleanupSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderHeadCleanupSplitSpec cleanup := by
  constructor
  · constructor
    · exact hcleanup.left
    · intro target encodedPrefix
      exact hcleanup.right target [] encodedPrefix
  · constructor
    · exact hcleanup.left
    · intro target next rest encodedPrefix
      exact hcleanup.right target (next :: rest) encodedPrefix

/-- Reassemble padded selected-head cleanup from nil-rest and cons-rest branches. -/
theorem selectedSegmentLogicalTapeDecoderHeadCleanupSpec_of_splitSpec
    {cleanup : MachineDescription}
    (hsplit : SelectedSegmentLogicalTapeDecoderHeadCleanupSplitSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderHeadCleanupSpec cleanup := by
  rcases hsplit with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilRun⟩
  rcases hcons with ⟨_hreadyCons, hconsRun⟩
  refine ⟨hready, ?_⟩
  intro target rest encodedPrefix
  cases rest with
  | nil =>
      exact hnilRun target encodedPrefix
  | cons next rest =>
      exact hconsRun target next rest encodedPrefix

/-- Construction-level split adapter from the full cleanup view. -/
theorem selectedSegmentLogicalTapeDecoderHeadCleanupSplitConstruction_of_cleanup
    (hcleanup : SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    SelectedSegmentLogicalTapeDecoderHeadCleanupSplitConstruction := by
  rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderHeadCleanupSplitSpec_of_spec
        hcleanupSpec⟩

/-- Construction-level full cleanup adapter from the branch-split view. -/
theorem selectedSegmentLogicalTapeDecoderHeadCleanupConstruction_of_split
    (hsplit : SelectedSegmentLogicalTapeDecoderHeadCleanupSplitConstruction) :
    SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction := by
  rcases hsplit with ⟨cleanup, hsplitSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderHeadCleanupSpec_of_splitSpec
        hsplitSpec⟩

/-- Full cleanup and branch-split cleanup are equivalent route boundaries. -/
theorem selectedSegmentLogicalTapeDecoderHeadCleanupConstruction_iff_split :
    SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction ↔
      SelectedSegmentLogicalTapeDecoderHeadCleanupSplitConstruction := by
  constructor
  · exact selectedSegmentLogicalTapeDecoderHeadCleanupSplitConstruction_of_cleanup
  · exact selectedSegmentLogicalTapeDecoderHeadCleanupConstruction_of_split

/-!
## Pipeline route

The physical machine assembled here is the same three-phase pipeline as the
singleton decoder: move right from the separator, run the generated scanner,
then run the cleanup.  The only difference is the scanner target used by the
cleanup specification.
-/

/-- Alias for the selected-head pipeline assembled from the cleanup phase. -/
def selectedSegmentLogicalTapeDecoderHeadPipelineDescription
    (cleanup : MachineDescription) : MachineDescription :=
  selectedSegmentLogicalTapeDecoderPipelineDescription cleanup

/-- Subroutine readiness for the padded selected-head decoder pipeline. -/
theorem selectedSegmentLogicalTapeDecoderHeadPipelineDescription_subroutineReady
    {cleanup : MachineDescription}
    (hcleanup : cleanup.SubroutineReady) :
    (selectedSegmentLogicalTapeDecoderHeadPipelineDescription
      cleanup).SubroutineReady := by
  exact
    selectedSegmentLogicalTapeDecoderPipelineDescription_subroutineReady
      hcleanup

/--
The move-right and generated-scanner phases turn the selected-head source into
the padded scanner target expected by
{name}`SelectedSegmentLogicalTapeDecoderHeadCleanupSpec`.
-/
theorem selectedSegmentLogicalTapeDecoderHeadPipelineSpec_of_cleanupSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupSpec cleanup) :
    StructuredSelectedHeadSegmentDecoderSpec
      (selectedSegmentLogicalTapeDecoderHeadPipelineDescription
        cleanup) := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderHeadPipelineDescription_subroutineReady
        hcleanup.left
  · intro target rest encodedPrefix
    have hmove :
        (cursorMoveOnceDescription Direction.right).HaltsFromTapeEquiv
          (tapeAtEncodedSplit encodedPrefix
            (encodedStructuredTapeCells (guardLogicalTape target :: rest)))
          (Tape.move Direction.right
            (tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells
                (guardLogicalTape target :: rest)))) :=
      (cursorMoveOnceDescription_haltsFromTape Direction.right
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells
            (guardLogicalTape target :: rest)))).toEquiv
    have hscan :
        selectedSegmentLogicalTapeDecoderDescription.HaltsFromTapeEquiv
          (Tape.move Direction.right
            (tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells
                (guardLogicalTape target :: rest))))
          (selectedSegmentLogicalTapeDecoderHeadTargetTape
            target rest encodedPrefix) :=
      (selectedSegmentLogicalTapeDecoderDescription_haltsFrom_selectedHeadPayload
        target rest encodedPrefix).toEquiv
    have hpipelineScan :
        (canonicalPrimitiveSeqDescription
          (cursorMoveOnceDescription Direction.right)
          selectedSegmentLogicalTapeDecoderDescription).HaltsFromTapeEquiv
            (tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells
                (guardLogicalTape target :: rest)))
            (selectedSegmentLogicalTapeDecoderHeadTargetTape
              target rest encodedPrefix) :=
      canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        (cursorMoveOnceDescription_subroutineReady Direction.right)
        selectedSegmentLogicalTapeDecoderDescription_subroutineReady
        hmove
        hscan
    exact
      canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        (canonicalPrimitiveSeqDescription_subroutineReady
          (cursorMoveOnceDescription_subroutineReady Direction.right)
          selectedSegmentLogicalTapeDecoderDescription_subroutineReady)
        hcleanup.left
        hpipelineScan
        (hcleanup.right target rest encodedPrefix)

/--
The canonical sequence handoff after moving right from a selected-head
separator is literally the same tape.

After crossing the separator, the physical head is on the first encoded guard
cell of the selected logical tape, and that encoded guard cell has a second
physical bit to its right.
-/
theorem canonicalPrimitiveSeqHandoffTape_selectedHeadAfterMove
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    canonicalPrimitiveSeqHandoffTape
        (Tape.move Direction.right
          (tapeAtEncodedSplit encodedPrefix
            (encodedStructuredTapeCells
              (guardLogicalTape target :: rest)))) =
      Tape.move Direction.right
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells
            (guardLogicalTape target :: rest))) := by
  simp [canonicalPrimitiveSeqHandoffTape, tapeAtEncodedSplit,
    encodedStructuredTapeCells, guardLogicalTape, tapeAtCells,
    tapeSeparatorCells, logicalTapeCode, logicalCellListBits,
    logicalCellBits, logicalCellCode, headMarkerCells, Tape.move,
    Tape.moveLeft, Tape.moveRight]

/--
Exact selected-head decoder pipeline from an exact cleanup phase.

This is the literal-tape version of
{name}`selectedSegmentLogicalTapeDecoderHeadPipelineSpec_of_cleanupSpec`.
The closed side uses deterministic exact halting for the generated move and
scanner phases, then delegates the final target shape to the exact cleanup
contract.
-/
theorem selectedSegmentLogicalTapeDecoderHeadPipelineExactSpec_of_exactCleanupSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupSpec cleanup) :
    StructuredSelectedHeadSegmentDecoderExactSpec
      (selectedSegmentLogicalTapeDecoderHeadPipelineDescription
        cleanup) := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderHeadPipelineDescription_subroutineReady
        hcleanup.subroutineReady
  · intro target rest encodedPrefix
    let source :=
      tapeAtEncodedSplit encodedPrefix
        (encodedStructuredTapeCells (guardLogicalTape target :: rest))
    let moved := Tape.move Direction.right source
    let scanned :=
      selectedSegmentLogicalTapeDecoderHeadTargetTape
        target rest encodedPrefix
    have hmove :
        (cursorMoveOnceDescription Direction.right).HaltsFromTape
          source moved := by
      exact cursorMoveOnceDescription_haltsFromTape Direction.right source
    have hscanMoved :
        selectedSegmentLogicalTapeDecoderDescription.HaltsFromTape
          moved scanned := by
      simpa [source, moved, scanned] using
        selectedSegmentLogicalTapeDecoderDescription_haltsFrom_selectedHeadPayload
          target rest encodedPrefix
    have hmoved :
        canonicalPrimitiveSeqHandoffTape moved = moved := by
      simpa [source, moved] using
        canonicalPrimitiveSeqHandoffTape_selectedHeadAfterMove
          target rest encodedPrefix
    have hscan :
        selectedSegmentLogicalTapeDecoderDescription.HaltsFromTape
          (canonicalPrimitiveSeqHandoffTape moved)
          scanned := by
      rw [hmoved]
      exact hscanMoved
    have hpipelineScan :
        (canonicalPrimitiveSeqDescription
          (cursorMoveOnceDescription Direction.right)
          selectedSegmentLogicalTapeDecoderDescription).HaltsFromTape
            source scanned :=
      canonicalPrimitiveSeqDescription_haltsFromTape_exact
        (cursorMoveOnceDescription_subroutineReady Direction.right)
        selectedSegmentLogicalTapeDecoderDescription_subroutineReady
        hmove hscan
    have hpipeline :
        (selectedSegmentLogicalTapeDecoderHeadPipelineDescription
          cleanup).HaltsFromTape source target :=
      by
        simpa [selectedSegmentLogicalTapeDecoderHeadPipelineDescription,
          selectedSegmentLogicalTapeDecoderPipelineDescription, source,
          scanned] using
          canonicalPrimitiveSeqDescription_haltsFromTape_exact
            (canonicalPrimitiveSeqDescription_subroutineReady
              (cursorMoveOnceDescription_subroutineReady Direction.right)
              selectedSegmentLogicalTapeDecoderDescription_subroutineReady)
            hcleanup.subroutineReady
            hpipelineScan
            (hcleanup.forward target rest encodedPrefix)
    simpa [source] using hpipeline
  · intro target rest encodedPrefix
    let source :=
      tapeAtEncodedSplit encodedPrefix
        (encodedStructuredTapeCells (guardLogicalTape target :: rest))
    let moved := Tape.move Direction.right source
    let scanned :=
      selectedSegmentLogicalTapeDecoderHeadTargetTape
        target rest encodedPrefix
    have hmove :
        (cursorMoveOnceDescription Direction.right).HaltsFromTape
          source moved := by
      exact cursorMoveOnceDescription_haltsFromTape Direction.right source
    have hscanMoved :
        selectedSegmentLogicalTapeDecoderDescription.HaltsFromTape
          moved scanned := by
      simpa [source, moved, scanned] using
        selectedSegmentLogicalTapeDecoderDescription_haltsFrom_selectedHeadPayload
          target rest encodedPrefix
    have hmoved :
        canonicalPrimitiveSeqHandoffTape moved = moved := by
      simpa [source, moved] using
        canonicalPrimitiveSeqHandoffTape_selectedHeadAfterMove
          target rest encodedPrefix
    have hscan :
        selectedSegmentLogicalTapeDecoderDescription.HaltsFromTape
          (canonicalPrimitiveSeqHandoffTape moved)
          scanned := by
      rw [hmoved]
      exact hscanMoved
    have hpipelineScanClosed :
        ExactClosedFromTape
          (canonicalPrimitiveSeqDescription
            (cursorMoveOnceDescription Direction.right)
            selectedSegmentLogicalTapeDecoderDescription)
          source scanned :=
      canonicalPrimitiveSeqDescription_exactClosedFromTape
        (cursorMoveOnceDescription_subroutineReady Direction.right)
        selectedSegmentLogicalTapeDecoderDescription_subroutineReady
        (by
          intro T hhalt
          exact
            MachineDescription.haltsFromTape_functional_of_haltTransitionFree
              (cursorMoveOnceDescription_subroutineReady
                Direction.right).right hhalt hmove)
        (by
          intro T hhalt
          exact
            MachineDescription.haltsFromTape_functional_of_haltTransitionFree
              selectedSegmentLogicalTapeDecoderDescription_subroutineReady.right
              hhalt hscan)
    have hpipelineClosed :
        ExactClosedFromTape
          (selectedSegmentLogicalTapeDecoderHeadPipelineDescription
            cleanup)
          source target :=
      by
        simpa [selectedSegmentLogicalTapeDecoderHeadPipelineDescription,
          selectedSegmentLogicalTapeDecoderPipelineDescription, source,
          scanned] using
          canonicalPrimitiveSeqDescription_exactClosedFromTape
            (canonicalPrimitiveSeqDescription_subroutineReady
              (cursorMoveOnceDescription_subroutineReady Direction.right)
              selectedSegmentLogicalTapeDecoderDescription_subroutineReady)
            hcleanup.subroutineReady
            hpipelineScanClosed
            (hcleanup.closed target rest encodedPrefix)
    simpa [source] using hpipelineClosed

/-- Build an exact selected-head decoder from an exact cleanup phase. -/
theorem structuredSelectedHeadSegmentDecoderExactConstruction_of_exactHeadCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction) :
    StructuredSelectedHeadSegmentDecoderExactConstruction := by
  rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
  exact
    ⟨selectedSegmentLogicalTapeDecoderHeadPipelineDescription cleanup,
      selectedSegmentLogicalTapeDecoderHeadPipelineExactSpec_of_exactCleanupSpec
        hcleanupSpec⟩

/-- Exact tape-2 projector from exact selected-head cleanup. -/
theorem structuredTape2ExactProjectorConstruction_of_exactHeadCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction) :
    StructuredTape2ExactProjectorConstruction :=
  structuredTape2ExactProjectorConstruction_of_exactHeadDecoder
    (structuredSelectedHeadSegmentDecoderExactConstruction_of_exactHeadCleanup
      hcleanup)

/-- Equivalence tape-2 projector from exact selected-head cleanup. -/
theorem structuredTape2ProjectorConstruction_of_exactHeadCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction) :
    StructuredTape2ProjectorConstruction :=
  structuredTape2ProjectorConstruction_of_exact
    (structuredTape2ExactProjectorConstruction_of_exactHeadCleanup hcleanup)

/-- Exact selected-head decoder from forward-split exact cleanup. -/
theorem structuredSelectedHeadSegmentDecoderExactConstruction_of_exactHeadCleanupForwardSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction) :
    StructuredSelectedHeadSegmentDecoderExactConstruction :=
  structuredSelectedHeadSegmentDecoderExactConstruction_of_exactHeadCleanup
    (selectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction_of_forwardSplit
      hsplit)

/-- Exact tape-2 projector from forward-split exact cleanup. -/
theorem structuredTape2ExactProjectorConstruction_of_exactHeadCleanupForwardSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction) :
    StructuredTape2ExactProjectorConstruction :=
  structuredTape2ExactProjectorConstruction_of_exactHeadCleanup
    (selectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction_of_forwardSplit
      hsplit)

/-- Equivalence tape-2 projector from forward-split exact cleanup. -/
theorem structuredTape2ProjectorConstruction_of_exactHeadCleanupForwardSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction) :
    StructuredTape2ProjectorConstruction :=
  structuredTape2ProjectorConstruction_of_exact
    (structuredTape2ExactProjectorConstruction_of_exactHeadCleanupForwardSplit
      hsplit)

/--
Bundle of exact selected-head consequences from one forward-split cleanup
construction.

The split premise is the finite-table shape expected for the real cleanup:
empty rest and nonempty rest are independent finite-control branches.  The
closed exact facts are derived by functionality once the forward branch runs
are available.
-/
structure StructuredSelectedHeadExactDecoderRouteConstruction : Prop where
  exactCleanupForwardSplit :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction
  exactCleanup :
    SelectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction
  exactHeadDecoder :
    StructuredSelectedHeadSegmentDecoderExactConstruction
  headDecoder :
    StructuredSelectedHeadSegmentDecoderConstruction
  exactTape2Projector :
    StructuredTape2ExactProjectorConstruction
  tape2Projector :
    StructuredTape2ProjectorConstruction

/-- Build the exact selected-head route bundle from forward-split cleanup. -/
theorem structuredSelectedHeadExactDecoderRouteConstruction_of_forwardSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupForwardSplitConstruction) :
    StructuredSelectedHeadExactDecoderRouteConstruction := by
  let hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction :=
    selectedSegmentLogicalTapeDecoderHeadExactCleanupConstruction_of_forwardSplit
      hsplit
  let hexactHead :
      StructuredSelectedHeadSegmentDecoderExactConstruction :=
    structuredSelectedHeadSegmentDecoderExactConstruction_of_exactHeadCleanup
      hcleanup
  let hhead :
      StructuredSelectedHeadSegmentDecoderConstruction :=
    structuredSelectedHeadSegmentDecoderConstruction_of_exact
      hexactHead
  let hexactProjector :
      StructuredTape2ExactProjectorConstruction :=
    structuredTape2ExactProjectorConstruction_of_exactHeadDecoder
      hexactHead
  let hprojector :
      StructuredTape2ProjectorConstruction :=
    structuredTape2ProjectorConstruction_of_exact
      hexactProjector
  exact
    { exactCleanupForwardSplit := hsplit
      exactCleanup := hcleanup
      exactHeadDecoder := hexactHead
      headDecoder := hhead
      exactTape2Projector := hexactProjector
      tape2Projector := hprojector }

/-- Build a selected-head decoder from a padded selected-head cleanup. -/
theorem structuredSelectedHeadSegmentDecoderConstruction_of_headCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    StructuredSelectedHeadSegmentDecoderConstruction := by
  rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
  exact
    ⟨selectedSegmentLogicalTapeDecoderHeadPipelineDescription cleanup,
      selectedSegmentLogicalTapeDecoderHeadPipelineSpec_of_cleanupSpec
        hcleanupSpec⟩

/-- The selected-head cleanup route also supplies the selected singleton decoder. -/
theorem structuredSelectedSingletonSegmentDecoderConstruction_of_headCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    StructuredSelectedSingletonSegmentDecoderConstruction :=
  structuredSelectedSingletonSegmentDecoderConstruction_of_headDecoder
    (structuredSelectedHeadSegmentDecoderConstruction_of_headCleanup hcleanup)

/-!
## Output route

Many downstream routes only need the normalized public word recovered from the
selected logical tape.  The output route is weaker than the exact
{name}`MachineDescription.HaltsFromTapeEquiv` route but follows immediately
from it.
-/

/-- Normalized-output view of a selected-head decoder. -/
def StructuredSelectedHeadSegmentDecoderOutputSpec
    (decoder : MachineDescription) : Prop :=
  decoder.SubroutineReady ∧
    forall (target : Tape Bool) (rest : List (Tape Bool))
      (encodedPrefix : List (Option Bool)),
      decoder.HaltsFromTapeWithOutput
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells (guardLogicalTape target :: rest)))
        (Tape.normalizedOutput target)

/-- Existence wrapper for the selected-head output route. -/
def StructuredSelectedHeadSegmentDecoderOutputConstruction : Prop :=
  exists decoder : MachineDescription,
    StructuredSelectedHeadSegmentDecoderOutputSpec decoder

/-- Exact selected-head decoding implies the normalized-output route. -/
theorem structuredSelectedHeadSegmentDecoderOutputSpec_of_spec
    {decoder : MachineDescription}
    (hdecoder : StructuredSelectedHeadSegmentDecoderSpec decoder) :
    StructuredSelectedHeadSegmentDecoderOutputSpec decoder := by
  constructor
  · exact hdecoder.left
  · intro target rest encodedPrefix
    exact
      MachineDescription.haltsFromTapeWithOutput_of_haltsFromTapeEquiv
        (hdecoder.right target rest encodedPrefix)

/-- Construction-level exact-to-output adapter for selected-head decoders. -/
theorem structuredSelectedHeadSegmentDecoderOutputConstruction_of_exact
    (hdecoder : StructuredSelectedHeadSegmentDecoderConstruction) :
    StructuredSelectedHeadSegmentDecoderOutputConstruction := by
  rcases hdecoder with ⟨decoder, hdecoderSpec⟩
  exact
    ⟨decoder,
      structuredSelectedHeadSegmentDecoderOutputSpec_of_spec
        hdecoderSpec⟩

/-- Build the selected-head output route directly from padded cleanup. -/
theorem structuredSelectedHeadSegmentDecoderOutputConstruction_of_headCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    StructuredSelectedHeadSegmentDecoderOutputConstruction :=
  structuredSelectedHeadSegmentDecoderOutputConstruction_of_exact
    (structuredSelectedHeadSegmentDecoderConstruction_of_headCleanup
      hcleanup)

/-!
## Projector consequences

Once a selected-head decoder exists, the generic projection module already
knows how to turn it into the tape 0, tape 1, and tape 2 segment normalizers.
This section packages those consequences so downstream code can depend on one
route bundle rather than rebuilding the same adapters.
-/

/-- Tape-0 segment normalizer from padded selected-head cleanup. -/
theorem structuredTape0SegmentNormalizerConstruction_of_headCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    StructuredTape0SegmentNormalizerConstruction :=
  structuredTape0SegmentNormalizerConstruction_of_selectedHeadDecoder
    (structuredSelectedHeadSegmentDecoderConstruction_of_headCleanup
      hcleanup)

/-- Tape-1 segment normalizer from padded selected-head cleanup. -/
theorem structuredTape1SegmentNormalizerConstruction_of_headCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    StructuredTape1SegmentNormalizerConstruction :=
  structuredTape1SegmentNormalizerConstruction_of_selectedHeadDecoder
    (structuredSelectedHeadSegmentDecoderConstruction_of_headCleanup
      hcleanup)

/-- Tape-2 segment normalizer from padded selected-head cleanup. -/
theorem structuredTape2SegmentNormalizerConstruction_of_headCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    StructuredTape2SegmentNormalizerConstruction :=
  structuredTape2SegmentNormalizerConstruction_of_selectedHeadDecoder
    (structuredSelectedHeadSegmentDecoderConstruction_of_headCleanup
      hcleanup)

/-- Tape-0 projector from padded selected-head cleanup. -/
theorem structuredTape0ProjectorConstruction_of_headCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    StructuredTape0ProjectorConstruction :=
  structuredTape0ProjectorConstruction_of_segmentNormalizerConstruction
    (structuredTape0SegmentNormalizerConstruction_of_headCleanup
      hcleanup)

/-- Tape-1 projector from padded selected-head cleanup. -/
theorem structuredTape1ProjectorConstruction_of_headCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    StructuredTape1ProjectorConstruction :=
  structuredTape1ProjectorConstruction_of_segmentNormalizerConstruction
    (structuredTape1SegmentNormalizerConstruction_of_headCleanup
      hcleanup)

/-- Tape-2 projector from padded selected-head cleanup. -/
theorem structuredTape2ProjectorConstruction_of_headCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    StructuredTape2ProjectorConstruction :=
  structuredTape2ProjectorConstruction_of_segmentNormalizerConstruction
    (structuredTape2SegmentNormalizerConstruction_of_headCleanup
      hcleanup)

/-- Tape-2 projector from branch-split padded selected-head cleanup. -/
theorem structuredTape2ProjectorConstruction_of_headCleanupSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderHeadCleanupSplitConstruction) :
    StructuredTape2ProjectorConstruction :=
  structuredTape2ProjectorConstruction_of_headCleanup
    (selectedSegmentLogicalTapeDecoderHeadCleanupConstruction_of_split
      hsplit)

/--
Bundle of selected-head decoder consequences from one padded cleanup premise.

The fields are deliberately redundant.  Later bridge modules commonly need a
specific projection of this route; making each consequence a field avoids
re-deriving local lets through large endpoint proofs.
-/
structure StructuredSelectedHeadDecoderRouteConstruction : Prop where
  headCleanup :
    SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction
  singletonCleanup :
    SelectedSegmentLogicalTapeDecoderCleanupConstruction
  headDecoder :
    StructuredSelectedHeadSegmentDecoderConstruction
  singletonDecoder :
    StructuredSelectedSingletonSegmentDecoderConstruction
  headOutput :
    StructuredSelectedHeadSegmentDecoderOutputConstruction
  tape0SegmentNormalizer :
    StructuredTape0SegmentNormalizerConstruction
  tape1SegmentNormalizer :
    StructuredTape1SegmentNormalizerConstruction
  tape2SegmentNormalizer :
    StructuredTape2SegmentNormalizerConstruction
  tape0Projector :
    StructuredTape0ProjectorConstruction
  tape1Projector :
    StructuredTape1ProjectorConstruction
  tape2Projector :
    StructuredTape2ProjectorConstruction

/-- Build the selected-head route bundle from the padded cleanup premise. -/
theorem structuredSelectedHeadDecoderRouteConstruction_of_headCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    StructuredSelectedHeadDecoderRouteConstruction := by
  let hhead :
      StructuredSelectedHeadSegmentDecoderConstruction :=
    structuredSelectedHeadSegmentDecoderConstruction_of_headCleanup
      hcleanup
  let hsingletonCleanup :
      SelectedSegmentLogicalTapeDecoderCleanupConstruction :=
    selectedSegmentLogicalTapeDecoderCleanupConstruction_of_headCleanup
      hcleanup
  let hsingleton :
      StructuredSelectedSingletonSegmentDecoderConstruction :=
    structuredSelectedSingletonSegmentDecoderConstruction_of_headDecoder
      hhead
  let houtput :
      StructuredSelectedHeadSegmentDecoderOutputConstruction :=
    structuredSelectedHeadSegmentDecoderOutputConstruction_of_exact
      hhead
  let htape0 :
      StructuredTape0SegmentNormalizerConstruction :=
    structuredTape0SegmentNormalizerConstruction_of_selectedHeadDecoder
      hhead
  let htape1 :
      StructuredTape1SegmentNormalizerConstruction :=
    structuredTape1SegmentNormalizerConstruction_of_selectedHeadDecoder
      hhead
  let htape2 :
      StructuredTape2SegmentNormalizerConstruction :=
    structuredTape2SegmentNormalizerConstruction_of_selectedHeadDecoder
      hhead
  let hproject0 :
      StructuredTape0ProjectorConstruction :=
    structuredTape0ProjectorConstruction_of_segmentNormalizerConstruction
      htape0
  let hproject1 :
      StructuredTape1ProjectorConstruction :=
    structuredTape1ProjectorConstruction_of_segmentNormalizerConstruction
      htape1
  let hproject2 :
      StructuredTape2ProjectorConstruction :=
    structuredTape2ProjectorConstruction_of_segmentNormalizerConstruction
      htape2
  exact
    { headCleanup := hcleanup
      singletonCleanup := hsingletonCleanup
      headDecoder := hhead
      singletonDecoder := hsingleton
      headOutput := houtput
      tape0SegmentNormalizer := htape0
      tape1SegmentNormalizer := htape1
      tape2SegmentNormalizer := htape2
      tape0Projector := hproject0
      tape1Projector := hproject1
      tape2Projector := hproject2 }

/--
Build the selected-head route bundle from branch-split cleanup.

This keeps downstream users at the split boundary when the real finite-machine
cleanup naturally separates the empty-rest and nonempty-rest cases.
-/
theorem structuredSelectedHeadDecoderRouteConstruction_of_headCleanupSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderHeadCleanupSplitConstruction) :
    StructuredSelectedHeadDecoderRouteConstruction :=
  structuredSelectedHeadDecoderRouteConstruction_of_headCleanup
    (selectedSegmentLogicalTapeDecoderHeadCleanupConstruction_of_split
      hsplit)

/-!
## Bundle projections

These small projection lemmas keep downstream modules independent from the
internal field names if the route bundle is expanded later.
-/

theorem selectedHeadRoute_headCleanup
    (hroute : StructuredSelectedHeadDecoderRouteConstruction) :
    SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction :=
  hroute.headCleanup

theorem selectedHeadRoute_singletonCleanup
    (hroute : StructuredSelectedHeadDecoderRouteConstruction) :
    SelectedSegmentLogicalTapeDecoderCleanupConstruction :=
  hroute.singletonCleanup

theorem selectedHeadRoute_headDecoder
    (hroute : StructuredSelectedHeadDecoderRouteConstruction) :
    StructuredSelectedHeadSegmentDecoderConstruction :=
  hroute.headDecoder

theorem selectedHeadRoute_singletonDecoder
    (hroute : StructuredSelectedHeadDecoderRouteConstruction) :
    StructuredSelectedSingletonSegmentDecoderConstruction :=
  hroute.singletonDecoder

theorem selectedHeadRoute_headOutput
    (hroute : StructuredSelectedHeadDecoderRouteConstruction) :
    StructuredSelectedHeadSegmentDecoderOutputConstruction :=
  hroute.headOutput

theorem selectedHeadRoute_tape0SegmentNormalizer
    (hroute : StructuredSelectedHeadDecoderRouteConstruction) :
    StructuredTape0SegmentNormalizerConstruction :=
  hroute.tape0SegmentNormalizer

theorem selectedHeadRoute_tape1SegmentNormalizer
    (hroute : StructuredSelectedHeadDecoderRouteConstruction) :
    StructuredTape1SegmentNormalizerConstruction :=
  hroute.tape1SegmentNormalizer

theorem selectedHeadRoute_tape2SegmentNormalizer
    (hroute : StructuredSelectedHeadDecoderRouteConstruction) :
    StructuredTape2SegmentNormalizerConstruction :=
  hroute.tape2SegmentNormalizer

theorem selectedHeadRoute_tape0Projector
    (hroute : StructuredSelectedHeadDecoderRouteConstruction) :
    StructuredTape0ProjectorConstruction :=
  hroute.tape0Projector

theorem selectedHeadRoute_tape1Projector
    (hroute : StructuredSelectedHeadDecoderRouteConstruction) :
    StructuredTape1ProjectorConstruction :=
  hroute.tape1Projector

theorem selectedHeadRoute_tape2Projector
    (hroute : StructuredSelectedHeadDecoderRouteConstruction) :
    StructuredTape2ProjectorConstruction :=
  hroute.tape2Projector

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
