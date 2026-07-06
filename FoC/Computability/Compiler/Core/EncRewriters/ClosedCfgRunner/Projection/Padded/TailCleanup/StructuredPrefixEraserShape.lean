import FoC.Computability.Compiler.DescriptionExecution
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.BoundaryEraser
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.SelectedFootprintCompactionShape

set_option doc.verso true

/-!
# Guarded structured-prefix eraser shape

This module isolates the reusable endpoint view for deleting the two guarded
structured logical-tape fields that precede the selected logical-tape decoder
footprint.  The concrete handoff module adapts these generic contracts back to
the selected-segment theorem names.
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

/-- Encoded two-tape structured prefix consumed by the eraser handoff. -/
def guardedTwoTapeStructuredPrefixCells
    (T0 T1 : Tape Bool) : List (Option Bool) :=
  encodedStructuredTapeCellsPrefix
    [guardLogicalTape T0, guardLogicalTape T1]

/-- Source tape for the generic guarded two-tape prefix eraser. -/
def guardedTwoTapeStructuredPrefixEraserSourceTape
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) : Tape Bool :=
  selectedSegmentLogicalTapeDecoderTargetTape
    (rightEdgeScanSourceTapeFromLeft [none] bits padding)
    (guardedTwoTapeStructuredPrefixCells T0 T1)

/-- Target tape for the generic guarded two-tape prefix eraser. -/
def guardedTwoTapeStructuredPrefixEraserTargetTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape Bool :=
  selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
    (selectedSegmentLogicalTapeDecoderPayloadCells bits padding)

theorem guardedTwoTapeStructuredPrefixCells_eq
    (T0 T1 : Tape Bool) :
    guardedTwoTapeStructuredPrefixCells T0 T1 =
      encodedStructuredTapeCellsPrefix
        [guardLogicalTape T0, guardLogicalTape T1] := by
  rfl

theorem guardedTwoTapeStructuredPrefixCells_expanded
    (T0 T1 : Tape Bool) :
    guardedTwoTapeStructuredPrefixCells T0 T1 =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape T0))
          (List.append tapeSeparatorCells
            (logicalTapeCode (guardLogicalTape T1)))) := by
  simp [guardedTwoTapeStructuredPrefixCells,
    encodedStructuredTapeCellsPrefix]

theorem guardedTwoTapeStructuredPrefixCells_filterMap
    (T0 T1 : Tape Bool) :
    (guardedTwoTapeStructuredPrefixCells T0 T1).filterMap
        (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (logicalTapeBits (guardLogicalTape T1)) := by
  simp [guardedTwoTapeStructuredPrefixCells,
    encodedStructuredTapeCellsPrefix, tapeSeparatorCells,
    logicalTapeCode_eq_map_some, List.filterMap_append,
    Function.comp_def]

theorem logicalCellBits_length_guardedShape
    (cell : Option Bool) :
    (logicalCellBits cell).length = 2 := by
  cases cell with
  | none =>
      rfl
  | some bit =>
      cases bit <;> rfl

theorem logicalCellListBits_length_guardedShape
    (cells : List (Option Bool)) :
    (logicalCellListBits cells).length = 2 * cells.length := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      simp [logicalCellListBits, logicalCellBits_length_guardedShape,
        ih]
      lia

theorem logicalTapeBits_length_guardedShape
    (T : Tape Bool) :
    (logicalTapeBits T).length =
      2 * T.left.length + 2 * T.right.length + 4 := by
  simp [logicalTapeBits, logicalCellListBits_length_guardedShape,
    logicalCellBits_length_guardedShape]
  lia

theorem logicalTapeCode_length_guardedShape
    (T : Tape Bool) :
    (logicalTapeCode T).length =
      2 * T.left.length + 2 * T.right.length + 4 := by
  rw [logicalTapeCode_eq_map_some]
  simp [logicalTapeBits_length_guardedShape]

theorem logicalTapeCode_guardLogicalTape_length_guardedShape
    (T : Tape Bool) :
    (logicalTapeCode (guardLogicalTape T)).length =
      2 * T.left.length + 2 * T.right.length + 8 := by
  simp [guardLogicalTape, logicalTapeCode_length_guardedShape]
  lia

theorem guardedTwoTapeStructuredPrefixCells_length
    (T0 T1 : Tape Bool) :
    (guardedTwoTapeStructuredPrefixCells T0 T1).length =
      2 * T0.left.length + 2 * T0.right.length +
        (2 * T1.left.length + 2 * T1.right.length) + 18 := by
  rw [guardedTwoTapeStructuredPrefixCells_expanded]
  simp [logicalTapeCode_guardLogicalTape_length_guardedShape]
  lia

theorem guardedTwoTapeStructuredPrefixEraserSourceTape_cells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        (guardedTwoTapeStructuredPrefixCells T0 T1)
        bits padding := by
  exact
    selectedSegmentLogicalTapeDecoderTargetTape_cells_rightEdgeScanSourceTapeFromLeft_eq_densifierSource
      (guardedTwoTapeStructuredPrefixCells T0 T1) bits padding

theorem guardedTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    guardedTwoTapeStructuredPrefixEraserTargetTape bits padding =
      selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        bits padding := by
  rw [guardedTwoTapeStructuredPrefixEraserTargetTape]
  rw [selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape]
  rw [selectedSegmentLogicalTapeDecoderFootprintSourceTape_eq_fromPayload]

theorem guardedTwoTapeStructuredPrefixEraserTargetTape_cells
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.cells
        (guardedTwoTapeStructuredPrefixEraserTargetTape
          bits padding) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        [] bits padding := by
  rw [guardedTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape]
  exact selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells
    bits padding

theorem guardedTwoTapeStructuredPrefixEraserTargetTape_cells_eq_fromPayload
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.cells
        (guardedTwoTapeStructuredPrefixEraserTargetTape
          bits padding) =
      Tape.cells
        (selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
          (selectedSegmentLogicalTapeDecoderPayloadCells bits padding)) := by
  rfl

theorem selectedSegmentLogicalTapeDecoderDensifierSourceCells_eq_prefix_append_nil_guardedShape
    (encodedPrefix : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierSourceCells
        encodedPrefix bits padding =
      List.append encodedPrefix
        (selectedSegmentLogicalTapeDecoderDensifierSourceCells
          [] bits padding) := by
  simp [selectedSegmentLogicalTapeDecoderDensifierSourceCells]

theorem guardedTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding) =
      List.append (guardedTwoTapeStructuredPrefixCells T0 T1)
        (Tape.cells
          (guardedTwoTapeStructuredPrefixEraserTargetTape
            bits padding)) := by
  rw [guardedTwoTapeStructuredPrefixEraserSourceTape_cells,
    guardedTwoTapeStructuredPrefixEraserTargetTape_cells]
  exact
    selectedSegmentLogicalTapeDecoderDensifierSourceCells_eq_prefix_append_nil_guardedShape
      (guardedTwoTapeStructuredPrefixCells T0 T1)
      bits padding

theorem guardedTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_targetTape_cells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape T0))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode (guardLogicalTape T1))
              (Tape.cells
                (guardedTwoTapeStructuredPrefixEraserTargetTape
                  bits padding))))) := by
  rw [
    guardedTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells,
    guardedTwoTapeStructuredPrefixCells_expanded]
  simp [List.append_assoc]

theorem guardedTwoTapeStructuredPrefixEraserSourceTape_cells_eq_boundaryFields_append_target
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding) =
      none ::
        List.append
          ((logicalTapeBits (guardLogicalTape T0)).map some)
          (none ::
            List.append
              ((logicalTapeBits (guardLogicalTape T1)).map some)
              (Tape.cells
                (guardedTwoTapeStructuredPrefixEraserTargetTape
                  bits padding))) := by
  rw [
    guardedTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_targetTape_cells]
  simp [tapeSeparatorCells, logicalTapeCode_eq_map_some]

theorem guardedTwoTapeStructuredPrefixEraserSourceTape_cells_eq_boundaryFields_append_footprint
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding) =
      none ::
        List.append
          ((logicalTapeBits (guardLogicalTape T0)).map some)
          (none ::
            List.append
              ((logicalTapeBits (guardLogicalTape T1)).map some)
              (none ::
                List.append
                  (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
                    bits padding)
                  [none, none])) := by
  rw [
    guardedTwoTapeStructuredPrefixEraserSourceTape_cells_eq_boundaryFields_append_target,
    guardedTwoTapeStructuredPrefixEraserTargetTape,
    selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload_cells_eq]
  rw [← selectedSegmentLogicalTapeDecoderFootprintLeftCells_eq_fromPayload]
  simp [selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells,
    List.append_assoc]

theorem guardedTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding) =
      List.append
        ((guardedTwoTapeStructuredPrefixCells T0 T1).filterMap
          (fun cell => cell))
        (List.append bits (padding.filterMap (fun cell => cell))) := by
  rw [guardedTwoTapeStructuredPrefixEraserSourceTape]
  rw [selectedSegmentLogicalTapeDecoderTargetTape_normalizedOutput]
  rw [rightEdgeScanSourceTapeFromLeft_singleBlank_normalizedOutput]

theorem guardedTwoTapeStructuredPrefixEraserTargetTape_normalizedOutput
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixEraserTargetTape bits padding) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [guardedTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape]
  exact selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_normalizedOutput
    bits padding

theorem guardedTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput_eq_guardedBits_append_target
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (Tape.normalizedOutput
            (guardedTwoTapeStructuredPrefixEraserTargetTape
              bits padding))) := by
  rw [guardedTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput,
    guardedTwoTapeStructuredPrefixEraserTargetTape_normalizedOutput,
    guardedTwoTapeStructuredPrefixCells_filterMap]
  simp [List.append_assoc]

theorem guardedTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (Tape.cells
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding)).filterMap (fun cell => cell) =
      List.append
        ((guardedTwoTapeStructuredPrefixCells T0 T1).filterMap
          (fun cell => cell))
        (List.append bits (padding.filterMap (fun cell => cell))) := by
  rw [guardedTwoTapeStructuredPrefixEraserSourceTape_cells]
  exact
    selectedSegmentLogicalTapeDecoderDensifierSourceCells_filterMap
      (guardedTwoTapeStructuredPrefixCells T0 T1) bits padding

theorem guardedTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (Tape.cells
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding)).filterMap (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (List.append bits (padding.filterMap (fun cell => cell)))) := by
  rw [guardedTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap,
    guardedTwoTapeStructuredPrefixCells_filterMap]
  simp [List.append_assoc]

theorem guardedTwoTapeStructuredPrefixEraserTargetTape_cells_filterMap
    (bits : Word Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (guardedTwoTapeStructuredPrefixEraserTargetTape
          bits padding)).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [guardedTwoTapeStructuredPrefixEraserTargetTape_cells]
  simpa using
    selectedSegmentLogicalTapeDecoderDensifierSourceCells_filterMap
      [] bits padding

theorem guardedTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_append_target
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (Tape.cells
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding)).filterMap (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          ((Tape.cells
            (guardedTwoTapeStructuredPrefixEraserTargetTape
              bits padding)).filterMap (fun cell => cell))) := by
  rw [guardedTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits,
    guardedTwoTapeStructuredPrefixEraserTargetTape_cells_filterMap]

def guardedTwoTapeStructuredPrefixSecondFieldEraserBaseLeft
    (T0 : Tape Bool) : List (Option Bool) :=
  List.append ((logicalTapeBits (guardLogicalTape T0)).reverse.map some)
    [none]

def guardedTwoTapeStructuredPrefixSecondFieldEraserSuffixTail
    (bits : Word Bool) (padding : List (Option Bool)) :
    List (Option Bool) :=
  List.append
    (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
      bits padding)
    [none, none]

def guardedTwoTapeStructuredPrefixFirstFieldEraserSuffixTail
    (T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) : List (Option Bool) :=
  List.append
    (List.replicate
      (logicalTapeBits (guardLogicalTape T1)).length
      (none : Option Bool))
    (none ::
      guardedTwoTapeStructuredPrefixSecondFieldEraserSuffixTail
        bits padding)

def guardedTwoTapeStructuredPrefixErasedFootprintLeftCells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) : List (Option Bool) :=
  none ::
    List.append
      (List.replicate
        (logicalTapeBits (guardLogicalTape T0)).length
        (none : Option Bool))
      (none ::
        List.append
          (List.replicate
            (logicalTapeBits (guardLogicalTape T1)).length
            (none : Option Bool))
          (none ::
            List.append
              (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
                bits padding)
              [none]))

theorem guardedTwoTapeStructuredPrefixEraserSourceTape_cells_eq_secondFieldBoundaryEraserSourceTape_cells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding) =
      Tape.cells
        (leftBoundaryEraserSourceTape
          (guardedTwoTapeStructuredPrefixSecondFieldEraserBaseLeft T0)
          (logicalTapeBits (guardLogicalTape T1))
          none
          (guardedTwoTapeStructuredPrefixSecondFieldEraserSuffixTail
            bits padding)) := by
  rw [
    guardedTwoTapeStructuredPrefixEraserSourceTape_cells_eq_boundaryFields_append_footprint,
    leftBoundaryEraserSourceTape_cells]
  simp [
    guardedTwoTapeStructuredPrefixSecondFieldEraserBaseLeft,
    guardedTwoTapeStructuredPrefixSecondFieldEraserSuffixTail,
    List.reverse_append, List.map_reverse]

theorem guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserTargetTape_cells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (leftBoundaryEraserTargetTape
          (guardedTwoTapeStructuredPrefixSecondFieldEraserBaseLeft T0)
          (logicalTapeBits (guardLogicalTape T1))
          none
          (guardedTwoTapeStructuredPrefixSecondFieldEraserSuffixTail
            bits padding)) =
      none ::
        List.append
          ((logicalTapeBits (guardLogicalTape T0)).map some)
          (none ::
            List.append
              (List.replicate
                (logicalTapeBits (guardLogicalTape T1)).length
                (none : Option Bool))
              (none ::
                List.append
                  (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
                    bits padding)
                  [none, none])) := by
  rw [leftBoundaryEraserTargetTape_cells]
  simp [
    guardedTwoTapeStructuredPrefixSecondFieldEraserBaseLeft,
    guardedTwoTapeStructuredPrefixSecondFieldEraserSuffixTail,
    List.reverse_append, List.map_reverse]

theorem guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserTargetTape_cells_filterMap
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (Tape.cells
        (leftBoundaryEraserTargetTape
          (guardedTwoTapeStructuredPrefixSecondFieldEraserBaseLeft T0)
          (logicalTapeBits (guardLogicalTape T1))
          none
          (guardedTwoTapeStructuredPrefixSecondFieldEraserSuffixTail
            bits padding))).filterMap (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append bits (padding.filterMap (fun cell => cell))) := by
  rw [
    guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserTargetTape_cells]
  simp [selectedSegmentLogicalTapeDecoderDensifierFootprintCells_filterMap,
    List.filterMap_append, Function.comp_def]

theorem guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserTargetTape_cells_eq_firstFieldBoundaryEraserSourceTape_cells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (leftBoundaryEraserTargetTape
          (guardedTwoTapeStructuredPrefixSecondFieldEraserBaseLeft T0)
          (logicalTapeBits (guardLogicalTape T1))
          none
          (guardedTwoTapeStructuredPrefixSecondFieldEraserSuffixTail
            bits padding)) =
      Tape.cells
        (leftBoundaryEraserSourceTape
          []
          (logicalTapeBits (guardLogicalTape T0))
          none
          (guardedTwoTapeStructuredPrefixFirstFieldEraserSuffixTail
            T1 bits padding)) := by
  rw [
    guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserTargetTape_cells,
    leftBoundaryEraserSourceTape_cells]
  simp [
    guardedTwoTapeStructuredPrefixFirstFieldEraserSuffixTail,
    guardedTwoTapeStructuredPrefixSecondFieldEraserSuffixTail]

theorem guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape_cells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (leftBoundaryEraserTargetTape
          []
          (logicalTapeBits (guardLogicalTape T0))
          none
          (guardedTwoTapeStructuredPrefixFirstFieldEraserSuffixTail
            T1 bits padding)) =
      none ::
        List.append
          (List.replicate
            (logicalTapeBits (guardLogicalTape T0)).length
            (none : Option Bool))
          (none ::
            List.append
              (List.replicate
                (logicalTapeBits (guardLogicalTape T1)).length
                (none : Option Bool))
              (none ::
                List.append
                  (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
                    bits padding)
                  [none, none])) := by
  rw [leftBoundaryEraserTargetTape_cells]
  simp [
    guardedTwoTapeStructuredPrefixFirstFieldEraserSuffixTail,
    guardedTwoTapeStructuredPrefixSecondFieldEraserSuffixTail]

theorem guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape_cells_eq_erasedFootprintVisibleCells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (leftBoundaryEraserTargetTape
          []
          (logicalTapeBits (guardLogicalTape T0))
          none
          (guardedTwoTapeStructuredPrefixFirstFieldEraserSuffixTail
            T1 bits padding)) =
      rightEndCompactionVisibleCells
        (guardedTwoTapeStructuredPrefixErasedFootprintLeftCells
          T0 T1 bits padding) := by
  rw [
    guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape_cells]
  simp [
    guardedTwoTapeStructuredPrefixErasedFootprintLeftCells,
    rightEndCompactionVisibleCells, List.append_assoc]

theorem guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape_cells_filterMap
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (Tape.cells
        (leftBoundaryEraserTargetTape
          []
          (logicalTapeBits (guardLogicalTape T0))
          none
          (guardedTwoTapeStructuredPrefixFirstFieldEraserSuffixTail
            T1 bits padding))).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [
    guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape_cells]
  simp [selectedSegmentLogicalTapeDecoderDensifierFootprintCells_filterMap,
    List.filterMap_append]

theorem guardedTwoTapeStructuredPrefixErasedFootprintLeftCells_filterMap
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (guardedTwoTapeStructuredPrefixErasedFootprintLeftCells
        T0 T1 bits padding).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  simp [
    guardedTwoTapeStructuredPrefixErasedFootprintLeftCells,
    selectedSegmentLogicalTapeDecoderDensifierFootprintCells_filterMap,
    List.filterMap_append]

theorem guardedTwoTapeStructuredPrefixErasedFootprintVisibleCells_filterMap
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (rightEndCompactionVisibleCells
        (guardedTwoTapeStructuredPrefixErasedFootprintLeftCells
          T0 T1 bits padding)).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  simp [rightEndCompactionVisibleCells,
    guardedTwoTapeStructuredPrefixErasedFootprintLeftCells_filterMap,
    List.filterMap_append]

theorem guardedTwoTapeStructuredPrefixEraserTargetTape_cells_length
    (bits : Word Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (guardedTwoTapeStructuredPrefixEraserTargetTape
          bits padding)).length =
      13 + 2 * bits.length + 2 * padding.length := by
  rw [guardedTwoTapeStructuredPrefixEraserTargetTape]
  rw [selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload_cells_eq]
  rw [List.append_eq]
  rw [List.length_append]
  rw [selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload_length]
  rw [selectedSegmentLogicalTapeDecoderPayloadCells_length]
  simp
  lia

theorem guardedTwoTapeStructuredPrefixEraserSourceTape_cells_length
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (Tape.cells
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding)).length =
      2 * T0.left.length + 2 * T0.right.length +
        (2 * T1.left.length + 2 * T1.right.length) +
        (31 + 2 * bits.length + 2 * padding.length) := by
  rw [guardedTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells]
  rw [List.append_eq]
  rw [List.length_append]
  rw [guardedTwoTapeStructuredPrefixCells_length]
  rw [guardedTwoTapeStructuredPrefixEraserTargetTape_cells_length]
  lia

/--
Reusable contract for the finite eraser that deletes the two guarded
structured logical-tape fields before the selected decoder footprint.
-/
def GuardedTwoTapeStructuredPrefixEraserSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    forall (T0 T1 : Tape Bool) (bits : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding)
        (guardedTwoTapeStructuredPrefixEraserTargetTape
          bits padding)

def GuardedTwoTapeStructuredPrefixEraserConstruction : Prop :=
  exists eraser : MachineDescription,
    GuardedTwoTapeStructuredPrefixEraserSpec eraser

def GuardedTwoTapeStructuredPrefixEraserNilPadSymbolCaseSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall T0 T1 : Tape Bool,
      eraser.HaltsFromTapeEquiv
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] [])
        (guardedTwoTapeStructuredPrefixEraserTargetTape [] [])) ∧
    (forall (T0 T1 : Tape Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (none :: padding))
        (guardedTwoTapeStructuredPrefixEraserTargetTape
          [] (none :: padding))) ∧
    forall (T0 T1 : Tape Bool) (padBit : Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (some padBit :: padding))
        (guardedTwoTapeStructuredPrefixEraserTargetTape
          [] (some padBit :: padding))

def GuardedTwoTapeStructuredPrefixEraserConsPadSymbolCaseSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool),
      eraser.HaltsFromTapeEquiv
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) [])
        (guardedTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) [])) ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (none :: padding))
        (guardedTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) (none :: padding))) ∧
    forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (some padBit :: padding))
        (guardedTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) (some padBit :: padding))

def GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec
    (eraser : MachineDescription) : Prop :=
  GuardedTwoTapeStructuredPrefixEraserNilPadSymbolCaseSpec eraser ∧
    GuardedTwoTapeStructuredPrefixEraserConsPadSymbolCaseSpec eraser

def GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction :
    Prop :=
  exists eraser : MachineDescription,
    GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec eraser

theorem guardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec_of_spec
    {eraser : MachineDescription}
    (h :
      GuardedTwoTapeStructuredPrefixEraserSpec eraser) :
    GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec eraser := by
  rcases h with ⟨hready, hrun⟩
  refine ⟨?_, ?_⟩
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro T0 T1
      exact hrun T0 T1 [] []
    · intro T0 T1 padding
      exact hrun T0 T1 [] (none :: padding)
    · intro T0 T1 padBit padding
      exact hrun T0 T1 [] (some padBit :: padding)
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro T0 T1 bit rest
      exact hrun T0 T1 (bit :: rest) []
    · intro T0 T1 bit rest padding
      exact hrun T0 T1 (bit :: rest) (none :: padding)
    · intro T0 T1 bit rest padBit padding
      exact hrun T0 T1 (bit :: rest) (some padBit :: padding)

theorem guardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction_of_construction
    (h :
      GuardedTwoTapeStructuredPrefixEraserConstruction) :
    GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction := by
  rcases h with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      guardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec_of_spec
        hspec⟩

theorem guardedTwoTapeStructuredPrefixEraserSpec_of_splitPadSymbolCaseSpec
    {eraser : MachineDescription}
    (h :
      GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec
        eraser) :
    GuardedTwoTapeStructuredPrefixEraserSpec eraser := by
  rcases h with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  refine ⟨hready, ?_⟩
  intro T0 T1 bits padding
  cases bits with
  | nil =>
      cases padding with
      | nil =>
          exact hnilNil T0 T1
      | cons pad padding =>
          cases pad with
          | none =>
              exact hnilNone T0 T1 padding
          | some padBit =>
              exact hnilSome T0 T1 padBit padding
  | cons bit rest =>
      cases padding with
      | nil =>
          exact hconsNil T0 T1 bit rest
      | cons pad padding =>
          cases pad with
          | none =>
              exact hconsNone T0 T1 bit rest padding
          | some padBit =>
              exact hconsSome T0 T1 bit rest padBit padding

theorem guardedTwoTapeStructuredPrefixEraserConstruction_of_splitPadSymbolCases
    (h :
      GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction) :
    GuardedTwoTapeStructuredPrefixEraserConstruction := by
  rcases h with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      guardedTwoTapeStructuredPrefixEraserSpec_of_splitPadSymbolCaseSpec
        hspec⟩

theorem guardedTwoTapeStructuredPrefixEraserSpec_iff_splitPadSymbolCaseSpec
    (eraser : MachineDescription) :
    GuardedTwoTapeStructuredPrefixEraserSpec eraser ↔
      GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec
        eraser := by
  constructor
  · exact guardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec_of_spec
  · exact guardedTwoTapeStructuredPrefixEraserSpec_of_splitPadSymbolCaseSpec

theorem guardedTwoTapeStructuredPrefixEraserConstruction_iff_splitPadSymbolCaseConstruction :
    GuardedTwoTapeStructuredPrefixEraserConstruction ↔
      GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction := by
  constructor
  · exact guardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction_of_construction
  · exact guardedTwoTapeStructuredPrefixEraserConstruction_of_splitPadSymbolCases

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
