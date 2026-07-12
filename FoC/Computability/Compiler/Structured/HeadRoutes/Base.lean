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

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
