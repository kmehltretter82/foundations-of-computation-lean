import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredInputMaterializer
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTableChecks
import FoC.Computability.Compiler.Structured.Lowering.ConcreteRefresh
import FoC.Computability.Compiler.Structured.Lowering.Composition
import FoC.Computability.Compiler.Structured.Lowering.Projection
import FoC.Computability.Compiler.Structured.Lowering.ThreeTapeHelpers
import FoC.Computability.Compiler.Structured.Lowering.ThreeTapeTactic

set_option doc.verso true

/-!
# Historical selected-head projection route contracts

The base projection module proves the selected singleton decoder route: the
selected logical tape is the last encoded structured tape segment, so the
generated bit scanner halts on the blank separator immediately after that
segment.

This module records the matching selected-head route shapes.  The selected
logical tape may have additional encoded structured segments to its right, so
the scanner target carries a padding tail made from the remaining structured
block.  These declarations remain useful as conditional adapters and as the
source of the tracked #17 counterexample.  They do not provide a live cleanup
construction: the scanner erases the logical head marker, and
{lit}`ContractGuardrails.lean` refutes recovery of arbitrary targets.  The
live tape-2 projector starts directly from the marker-preserving canonical
guarded three-tape encoding.
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

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape_handoff_nil
    (target : Tape Bool) (encodedPrefix : List (Option Bool)) :
    canonicalPrimitiveSeqHandoffTape
        (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
          target [] encodedPrefix) =
      tapeAtCells
        (selectedSegmentLogicalTapeDecoderPaddedCleanupLeftStack
          target encodedPrefix)
        [none, none] := by
  simp [canonicalPrimitiveSeqHandoffTape,
    selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape_eq_tapeAtCells,
    tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape_handoff_singleton
    (target : Tape Bool) (pad : Option Bool)
    (encodedPrefix : List (Option Bool)) :
    canonicalPrimitiveSeqHandoffTape
        (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
          target [pad] encodedPrefix) =
      tapeAtCells
        (selectedSegmentLogicalTapeDecoderPaddedCleanupLeftStack
          target encodedPrefix)
        [pad, none] := by
  simp [canonicalPrimitiveSeqHandoffTape,
    selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape_eq_tapeAtCells,
    tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape_handoff_cons_cons
    (target : Tape Bool) (pad next : Option Bool)
    (padding encodedPrefix : List (Option Bool)) :
    canonicalPrimitiveSeqHandoffTape
        (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
          target (pad :: next :: padding) encodedPrefix) =
      selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
        target (pad :: next :: padding) encodedPrefix := by
  simp [canonicalPrimitiveSeqHandoffTape,
    selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape_eq_tapeAtCells,
    tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

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

/-- Named target family for the raw selected-head materializer ingress. -/
def selectedSegmentLogicalTapeDecoderRawHeadIngressMaterializerTarget
    (input : SelectedSegmentLogicalTapeDecoderRawHeadIngressIndex) :
    Tape Bool :=
  selectedSegmentLogicalTapeDecoderRawHeadStructuredInputTape
    input.1 input.2.1 input.2.2

theorem selectedSegmentLogicalTapeDecoderRawHeadStructuredInputTape_eq_materializerTarget
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderRawHeadStructuredInputTape
        target rest encodedPrefix =
      structured3InputMaterializerTargetTape
        (selectedSegmentLogicalTapeDecoderRawHeadSourceTape
          target rest encodedPrefix)
        Tape.blank := by
  rfl

theorem selectedSegmentLogicalTapeDecoderRawHeadIngressMaterializerTarget_eq
    (input : SelectedSegmentLogicalTapeDecoderRawHeadIngressIndex) :
    selectedSegmentLogicalTapeDecoderRawHeadIngressMaterializerTarget input =
      structured3InputMaterializerTargetTape
        (selectedSegmentLogicalTapeDecoderRawHeadIngressMaterializerSource
          input)
        (selectedSegmentLogicalTapeDecoderRawHeadIngressMaterializerOutput
          input) := by
  cases input with
  | mk target restAndPrefix =>
      cases restAndPrefix with
      | mk rest encodedPrefix =>
          rfl

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

theorem selectedSegmentLogicalTapeDecoderRawHeadIngressBridgeSpec_of_targetFamilySpec
    {materializer : MachineDescription}
    (hmaterializer :
      Structured3InputTargetFamilySpec
        selectedSegmentLogicalTapeDecoderRawHeadIngressMaterializerSource
        selectedSegmentLogicalTapeDecoderRawHeadIngressMaterializerTarget
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
      selectedSegmentLogicalTapeDecoderRawHeadIngressMaterializerTarget,
      selectedSegmentLogicalTapeDecoderRawHeadSourceTape] using hrun

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

theorem selectedSegmentLogicalTapeDecoderRawHeadIngressBridgeConstruction_of_targetFamilyConstruction
    (hmaterializer :
      Structured3InputTargetFamilyConstruction
        selectedSegmentLogicalTapeDecoderRawHeadIngressMaterializerSource
        selectedSegmentLogicalTapeDecoderRawHeadIngressMaterializerTarget) :
    SelectedSegmentLogicalTapeDecoderRawHeadIngressBridgeConstruction := by
  rcases hmaterializer with ⟨materializer, hmaterializerSpec⟩
  exact
    ⟨materializer,
      selectedSegmentLogicalTapeDecoderRawHeadIngressBridgeSpec_of_targetFamilySpec
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

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
