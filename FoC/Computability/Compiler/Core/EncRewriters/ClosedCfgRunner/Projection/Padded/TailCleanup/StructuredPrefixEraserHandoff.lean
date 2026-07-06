import FoC.Computability.Compiler.DescriptionExecution
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.BoundaryEraser
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.SelectedFootprintCompaction
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.StructuredPrefixEraserShape

set_option doc.verso true

/-!
# Structured prefix eraser handoff

This module contains the selected logical-tape decoder handoff that erases the
two guarded structured logical tapes before the selected footprint compactor
runs.  Count-window-specific instantiations remain in
the threaded count-window bridge module.
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

def selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) : Tape Bool :=
  selectedSegmentLogicalTapeDecoderTargetTape
    (rightEdgeScanSourceTapeFromLeft [none] bits padding)
    (encodedStructuredTapeCellsPrefix
      [guardLogicalTape T0, guardLogicalTape T1])

def selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
    (bits : Word Bool) (padding : List (Option Bool)) : Tape Bool :=
  selectedSegmentLogicalTapeDecoderTargetTape
    (rightEdgeScanSourceTapeFromLeft [none] bits padding)
    []

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        (encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1])
        bits padding := by
  exact
    selectedSegmentLogicalTapeDecoderTargetTape_cells_rightEdgeScanSourceTapeFromLeft_eq_densifierSource
      (encodedStructuredTapeCellsPrefix
        [guardLogicalTape T0, guardLogicalTape T1])
      bits padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_cells
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          bits padding) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        [] bits padding := by
  exact
    selectedSegmentLogicalTapeDecoderTargetTape_cells_rightEdgeScanSourceTapeFromLeft_eq_densifierSource
      [] bits padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
        bits padding =
      selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        bits padding := by
  rfl

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_rightEndCompactionSourceTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
        bits padding =
      rightEndCompactionSourceTape
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          bits padding) := by
  rw [
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape,
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape]

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_eq_guardedTwoTapeStructuredPrefixEraserSourceTape
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
        T0 T1 bits padding =
      guardedTwoTapeStructuredPrefixEraserSourceTape
        T0 T1 bits padding := by
  rfl

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_guardedTwoTapeStructuredPrefixEraserTargetTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
        bits padding =
      guardedTwoTapeStructuredPrefixEraserTargetTape
        bits padding := by
  rw [
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape,
    guardedTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape]

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding) =
      List.append
        ((encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1]).filterMap
            (fun cell => cell))
        (List.append bits (padding.filterMap (fun cell => cell))) := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape]
  rw [selectedSegmentLogicalTapeDecoderTargetTape_normalizedOutput]
  rw [rightEdgeScanSourceTapeFromLeft_singleBlank_normalizedOutput]

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_normalizedOutput
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          bits padding) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape]
  rw [selectedSegmentLogicalTapeDecoderTargetTape_normalizedOutput]
  rw [rightEdgeScanSourceTapeFromLeft_singleBlank_normalizedOutput]
  simp

theorem encodedStructuredTapeCellsPrefix_two_guarded_filterMap
    (T0 T1 : Tape Bool) :
    (encodedStructuredTapeCellsPrefix
        [guardLogicalTape T0, guardLogicalTape T1]).filterMap
        (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (logicalTapeBits (guardLogicalTape T1)) := by
  simp [encodedStructuredTapeCellsPrefix, tapeSeparatorCells,
    logicalTapeCode_eq_map_some,
    List.filterMap_append, Function.comp_def]

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput_eq_guardedBits_append_targetTape_normalizedOutput
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (Tape.normalizedOutput
            (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
              bits padding))) := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput,
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_normalizedOutput]
  rw [encodedStructuredTapeCellsPrefix_two_guarded_filterMap]
  simp [List.append_assoc]

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding)).filterMap (fun cell => cell) =
      List.append
        ((encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1]).filterMap
            (fun cell => cell))
        (List.append bits (padding.filterMap (fun cell => cell))) := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells]
  exact
    selectedSegmentLogicalTapeDecoderDensifierSourceCells_filterMap
      (encodedStructuredTapeCellsPrefix
        [guardLogicalTape T0, guardLogicalTape T1])
      bits padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding)).filterMap (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (List.append bits (padding.filterMap (fun cell => cell)))) := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap,
    encodedStructuredTapeCellsPrefix_two_guarded_filterMap]
  simp [List.append_assoc]

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_cells_filterMap
    (bits : Word Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          bits padding)).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_cells]
  simpa using
    selectedSegmentLogicalTapeDecoderDensifierSourceCells_filterMap
      [] bits padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_append_targetTape_cells_filterMap
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding)).filterMap (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          ((Tape.cells
            (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
              bits padding)).filterMap (fun cell => cell))) := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits,
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_cells_filterMap]

theorem selectedSegmentLogicalTapeDecoderDensifierSourceCells_eq_prefix_append_nil
    (encodedPrefix : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierSourceCells
        encodedPrefix bits padding =
      List.append encodedPrefix
        (selectedSegmentLogicalTapeDecoderDensifierSourceCells
          [] bits padding) := by
  simp [selectedSegmentLogicalTapeDecoderDensifierSourceCells]

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding) =
      List.append
        (encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1])
        (Tape.cells
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            bits padding)) := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells,
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_cells]
  exact
    selectedSegmentLogicalTapeDecoderDensifierSourceCells_eq_prefix_append_nil
      (encodedStructuredTapeCellsPrefix
        [guardLogicalTape T0, guardLogicalTape T1])
      bits padding

theorem encodedStructuredTapeCellsPrefix_two_guarded_eq
    (T0 T1 : Tape Bool) :
    encodedStructuredTapeCellsPrefix
        [guardLogicalTape T0, guardLogicalTape T1] =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape T0))
          (List.append tapeSeparatorCells
            (logicalTapeCode (guardLogicalTape T1)))) := by
  simp [encodedStructuredTapeCellsPrefix]

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_targetTape_cells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape T0))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode (guardLogicalTape T1))
              (Tape.cells
                (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
                  bits padding))))) := by
  rw [
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells,
    encodedStructuredTapeCellsPrefix_two_guarded_eq]
  simp [List.append_assoc]

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_footprintSourceTape_cells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding) =
      List.append
        (encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1])
        (Tape.cells
          (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
            bits padding)) := by
  rw [
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells,
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape]

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_footprintSourceTape_cells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape T0))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode (guardLogicalTape T1))
              (Tape.cells
                (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
                  bits padding))))) := by
  rw [
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_targetTape_cells,
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape]

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_footprintCells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape T0))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode (guardLogicalTape T1))
              (none ::
                List.append
                  (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
                    bits padding)
                  [none, none])))) := by
  rw [
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_footprintSourceTape_cells,
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint]

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_boundaryFields_append_footprintCells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
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
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_footprintCells]
  simp [tapeSeparatorCells, logicalTapeCode_eq_map_some]

def selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixSecondFieldEraserBaseLeft
    (T0 : Tape Bool) : List (Option Bool) :=
  List.append ((logicalTapeBits (guardLogicalTape T0)).reverse.map some)
    [none]

def selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixSecondFieldEraserSuffixTail
    (bits : Word Bool) (padding : List (Option Bool)) :
    List (Option Bool) :=
  List.append
    (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
      bits padding)
    [none, none]

def selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixFirstFieldEraserSuffixTail
    (T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) : List (Option Bool) :=
  List.append
    (List.replicate
      (logicalTapeBits (guardLogicalTape T1)).length
      (none : Option Bool))
    (none ::
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixSecondFieldEraserSuffixTail
        bits padding)

def selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixErasedFootprintLeftCells
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

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_secondFieldBoundaryEraserSourceTape_cells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding) =
      Tape.cells
        (leftBoundaryEraserSourceTape
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixSecondFieldEraserBaseLeft
            T0)
          (logicalTapeBits (guardLogicalTape T1))
          none
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixSecondFieldEraserSuffixTail
            bits padding)) := by
  rw [
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_boundaryFields_append_footprintCells,
    leftBoundaryEraserSourceTape_cells]
  simp [
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixSecondFieldEraserBaseLeft,
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixSecondFieldEraserSuffixTail,
    List.reverse_append, List.map_reverse]

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixSecondFieldBoundaryEraserTargetTape_cells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (leftBoundaryEraserTargetTape
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixSecondFieldEraserBaseLeft
            T0)
          (logicalTapeBits (guardLogicalTape T1))
          none
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixSecondFieldEraserSuffixTail
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
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixSecondFieldEraserBaseLeft,
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixSecondFieldEraserSuffixTail,
    List.reverse_append, List.map_reverse]

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixSecondFieldBoundaryEraserTargetTape_cells_filterMap
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (Tape.cells
        (leftBoundaryEraserTargetTape
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixSecondFieldEraserBaseLeft
            T0)
          (logicalTapeBits (guardLogicalTape T1))
          none
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixSecondFieldEraserSuffixTail
            bits padding))).filterMap (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append bits (padding.filterMap (fun cell => cell))) := by
  rw [
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixSecondFieldBoundaryEraserTargetTape_cells]
  simp [selectedSegmentLogicalTapeDecoderDensifierFootprintCells_filterMap,
    List.filterMap_append, Function.comp_def]

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixSecondFieldBoundaryEraserTargetTape_cells_eq_firstFieldBoundaryEraserSourceTape_cells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (leftBoundaryEraserTargetTape
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixSecondFieldEraserBaseLeft
            T0)
          (logicalTapeBits (guardLogicalTape T1))
          none
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixSecondFieldEraserSuffixTail
            bits padding)) =
      Tape.cells
        (leftBoundaryEraserSourceTape
          []
          (logicalTapeBits (guardLogicalTape T0))
          none
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixFirstFieldEraserSuffixTail
            T1 bits padding)) := by
  rw [
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixSecondFieldBoundaryEraserTargetTape_cells,
    leftBoundaryEraserSourceTape_cells]
  simp [
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixFirstFieldEraserSuffixTail,
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixSecondFieldEraserSuffixTail]

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape_cells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (leftBoundaryEraserTargetTape
          []
          (logicalTapeBits (guardLogicalTape T0))
          none
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixFirstFieldEraserSuffixTail
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
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixFirstFieldEraserSuffixTail,
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixSecondFieldEraserSuffixTail]

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape_cells_eq_erasedFootprintVisibleCells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (leftBoundaryEraserTargetTape
          []
          (logicalTapeBits (guardLogicalTape T0))
          none
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixFirstFieldEraserSuffixTail
            T1 bits padding)) =
      rightEndCompactionVisibleCells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixErasedFootprintLeftCells
          T0 T1 bits padding) := by
  rw [
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape_cells]
  simp [
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixErasedFootprintLeftCells,
    rightEndCompactionVisibleCells, List.append_assoc]

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape_cells_filterMap
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (Tape.cells
        (leftBoundaryEraserTargetTape
          []
          (logicalTapeBits (guardLogicalTape T0))
          none
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixFirstFieldEraserSuffixTail
            T1 bits padding))).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape_cells]
  simp [selectedSegmentLogicalTapeDecoderDensifierFootprintCells_filterMap,
    List.filterMap_append]

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixErasedFootprintLeftCells_filterMap
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixErasedFootprintLeftCells
        T0 T1 bits padding).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  simp [
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixErasedFootprintLeftCells,
    selectedSegmentLogicalTapeDecoderDensifierFootprintCells_filterMap,
    List.filterMap_append]

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixErasedFootprintVisibleCells_filterMap
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (rightEndCompactionVisibleCells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixErasedFootprintLeftCells
          T0 T1 bits padding)).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  simp [rightEndCompactionVisibleCells,
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixErasedFootprintLeftCells_filterMap,
    List.filterMap_append]

theorem logicalCellCode_length
    (cell : Option Bool) :
    (logicalCellCode cell).length = 2 := by
  cases cell with
  | none =>
      rfl
  | some bit =>
      cases bit <;> rfl

theorem logicalCellBits_length
    (cell : Option Bool) :
    (logicalCellBits cell).length = 2 := by
  cases cell with
  | none =>
      rfl
  | some bit =>
      cases bit <;> rfl

theorem logicalCellListBits_length
    (cells : List (Option Bool)) :
    (logicalCellListBits cells).length = 2 * cells.length := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      simp [logicalCellListBits, logicalCellBits_length, ih]
      lia

theorem logicalCellListCode_length
    (cells : List (Option Bool)) :
    (logicalCellListCode cells).length = 2 * cells.length := by
  rw [logicalCellListCode_eq_map_some]
  simp [logicalCellListBits_length]

theorem logicalTapeBits_length
    (T : Tape Bool) :
    (logicalTapeBits T).length =
      2 * T.left.length + 2 * T.right.length + 4 := by
  simp [logicalTapeBits, logicalCellListBits_length,
    logicalCellBits_length]
  lia

theorem logicalTapeCode_length
    (T : Tape Bool) :
    (logicalTapeCode T).length =
      2 * T.left.length + 2 * T.right.length + 4 := by
  rw [logicalTapeCode_eq_map_some]
  simp [logicalTapeBits_length]

theorem logicalTapeCode_guardLogicalTape_length
    (T : Tape Bool) :
    (logicalTapeCode (guardLogicalTape T)).length =
      2 * T.left.length + 2 * T.right.length + 8 := by
  simp [guardLogicalTape, logicalTapeCode_length]
  lia

theorem encodedStructuredTapeCellsPrefix_two_guarded_length
    (T0 T1 : Tape Bool) :
    (encodedStructuredTapeCellsPrefix
        [guardLogicalTape T0, guardLogicalTape T1]).length =
      2 * T0.left.length + 2 * T0.right.length +
        (2 * T1.left.length + 2 * T1.right.length) + 18 := by
  rw [encodedStructuredTapeCellsPrefix_two_guarded_eq]
  simp [logicalTapeCode_guardLogicalTape_length]
  lia

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_cells_length
    (bits : Word Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          bits padding)).length =
      13 + 2 * bits.length + 2 * padding.length := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_cells]
  simp [selectedSegmentLogicalTapeDecoderDensifierSourceCells,
    selectedSegmentLogicalTapeDecoderDensifierFootprintCells_length]
  lia

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_length
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding)).length =
      2 * T0.left.length + 2 * T0.right.length +
        (2 * T1.left.length + 2 * T1.right.length) +
          (31 + 2 * bits.length + 2 * padding.length) := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells]
  simp [logicalTapeCode_guardLogicalTape_length,
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_cells_length]
  lia

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    forall (T0 T1 : Tape Bool) (bits : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding)
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          bits padding)

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction :
    Prop :=
  exists eraser : MachineDescription,
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSpec eraser

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall (T0 T1 : Tape Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] padding)
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          [] padding)) ∧
    forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) padding)
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) padding)

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseConstruction :
    Prop :=
  exists eraser : MachineDescription,
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseSpec
      eraser

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall T0 T1 : Tape Bool,
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] [])
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          [] [])) ∧
    (forall (T0 T1 : Tape Bool) (pad : Option Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (pad :: padding))
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          [] (pad :: padding))) ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) [])
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) [])) ∧
    forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (pad : Option Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (pad :: padding))
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) (pad :: padding))

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseConstruction :
    Prop :=
  exists eraser : MachineDescription,
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseSpec
      eraser

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall T0 T1 : Tape Bool,
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] [])
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          [] [])) ∧
    (forall (T0 T1 : Tape Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (none :: padding))
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          [] (none :: padding))) ∧
    (forall (T0 T1 : Tape Bool) (padBit : Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          [] (some padBit :: padding))) ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) [])
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) [])) ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (none :: padding))
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) (none :: padding))) ∧
    forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseConstruction :
    Prop :=
  exists eraser : MachineDescription,
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseSpec
      eraser

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserNilPadSymbolCaseSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall T0 T1 : Tape Bool,
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] [])
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          [] [])) ∧
    (forall (T0 T1 : Tape Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (none :: padding))
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          [] (none :: padding))) ∧
    forall (T0 T1 : Tape Bool) (padBit : Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          [] (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConsPadSymbolCaseSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) [])
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) [])) ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (none :: padding))
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) (none :: padding))) ∧
    forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec
    (eraser : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserNilPadSymbolCaseSpec
      eraser ∧
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConsPadSymbolCaseSpec
      eraser

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction :
    Prop :=
  exists eraser : MachineDescription,
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec
      eraser

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffNilPadSymbolCaseSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall T0 T1 : Tape Bool,
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] [])
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] [])) ∧
    (forall (T0 T1 : Tape Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (none :: padding))
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (none :: padding))) ∧
    forall (T0 T1 : Tape Bool) (padBit : Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConsPadSymbolCaseSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) [])
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) [])) ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (none :: padding))
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (none :: padding))) ∧
    forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec
    (eraser : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffNilPadSymbolCaseSpec
      eraser ∧
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConsPadSymbolCaseSpec
      eraser

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction :
    Prop :=
  exists eraser : MachineDescription,
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec
      eraser

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffNilPadSymbolCaseSpec_of_guardedPrefixEraserSpec
    {eraser : MachineDescription}
    (hguard :
      GuardedTwoTapeStructuredPrefixEraserNilPadSymbolCaseSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffNilPadSymbolCaseSpec
      eraser := by
  rcases hguard with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  refine ⟨hready, ?_, ?_, ?_⟩
  · intro T0 T1
    simpa [
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_eq_guardedTwoTapeStructuredPrefixEraserSourceTape,
      guardedTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
      hnilNil T0 T1
  · intro T0 T1 padding
    simpa [
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_eq_guardedTwoTapeStructuredPrefixEraserSourceTape,
      guardedTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
      hnilNone T0 T1 padding
  · intro T0 T1 padBit padding
    simpa [
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_eq_guardedTwoTapeStructuredPrefixEraserSourceTape,
      guardedTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
      hnilSome T0 T1 padBit padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConsPadSymbolCaseSpec_of_guardedPrefixEraserSpec
    {eraser : MachineDescription}
    (hguard :
      GuardedTwoTapeStructuredPrefixEraserConsPadSymbolCaseSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConsPadSymbolCaseSpec
      eraser := by
  rcases hguard with ⟨hready, hconsNil, hconsNone, hconsSome⟩
  refine ⟨hready, ?_, ?_, ?_⟩
  · intro T0 T1 bit rest
    simpa [
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_eq_guardedTwoTapeStructuredPrefixEraserSourceTape,
      guardedTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
      hconsNil T0 T1 bit rest
  · intro T0 T1 bit rest padding
    simpa [
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_eq_guardedTwoTapeStructuredPrefixEraserSourceTape,
      guardedTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
      hconsNone T0 T1 bit rest padding
  · intro T0 T1 bit rest padBit padding
    simpa [
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_eq_guardedTwoTapeStructuredPrefixEraserSourceTape,
      guardedTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
      hconsSome T0 T1 bit rest padBit padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec_of_guardedPrefixEraserSpec
    {eraser : MachineDescription}
    (hguard :
      GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec
      eraser := by
  rcases hguard with ⟨hnil, hcons⟩
  exact
    ⟨selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffNilPadSymbolCaseSpec_of_guardedPrefixEraserSpec
        hnil,
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConsPadSymbolCaseSpec_of_guardedPrefixEraserSpec
        hcons⟩

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction_of_guardedPrefixEraser
    (hguard :
      GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction := by
  rcases hguard with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec_of_guardedPrefixEraserSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseConstruction_of_split
    (hsplit :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseConstruction := by
  rcases hsplit with ⟨eraser, hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  exact
    ⟨eraser, hready, hnilNil, hnilNone, hnilSome,
      hconsNil, hconsNone, hconsSome⟩

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseConstruction_of_padSymbolCases
    (hcases :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseConstruction := by
  rcases hcases with
    ⟨eraser, hready, hnilNil, hnilNone, hnilSome, hconsNil,
      hconsNone, hconsSome⟩
  refine ⟨eraser, hready, hnilNil, ?_, hconsNil, ?_⟩
  · intro T0 T1 pad padding
    cases pad with
    | none =>
        exact hnilNone T0 T1 padding
    | some padBit =>
        exact hnilSome T0 T1 padBit padding
  · intro T0 T1 bit rest pad padding
    cases pad with
    | none =>
        exact hconsNone T0 T1 bit rest padding
    | some padBit =>
        exact hconsSome T0 T1 bit rest padBit padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction_of_footprintHandoff
    (hhandoff :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction := by
  rcases hhandoff with ⟨eraser, hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  refine ⟨eraser, ?_, ?_⟩
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro T0 T1
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
        hnilNil T0 T1
    · intro T0 T1 padding
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
        hnilNone T0 T1 padding
    · intro T0 T1 padBit padding
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
        hnilSome T0 T1 padBit padding
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro T0 T1 bit rest
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
        hconsNil T0 T1 bit rest
    · intro T0 T1 bit rest padding
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
        hconsNone T0 T1 bit rest padding
    · intro T0 T1 bit rest padBit padding
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
        hconsSome T0 T1 bit rest padBit padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction_of_split
    (hsplit :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction := by
  rcases hsplit with ⟨eraser, hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  refine ⟨eraser, ?_, ?_⟩
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro T0 T1
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
        hnilNil T0 T1
    · intro T0 T1 padding
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
        hnilNone T0 T1 padding
    · intro T0 T1 padBit padding
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
        hnilSome T0 T1 padBit padding
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro T0 T1 bit rest
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
        hconsNil T0 T1 bit rest
    · intro T0 T1 bit rest padding
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
        hconsNone T0 T1 bit rest padding
    · intro T0 T1 bit rest padBit padding
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
        hconsSome T0 T1 bit rest padBit padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction_of_cases
    (hcases :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction := by
  rcases hcases with ⟨eraser, hready, hnil, hcons⟩
  refine ⟨eraser, hready, ?_⟩
  intro T0 T1 bits padding
  cases bits with
  | nil =>
      exact hnil T0 T1 padding
  | cons bit rest =>
      exact hcons T0 T1 bit rest padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseConstruction_of_bitPaddingCases
    (hcases :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseConstruction := by
  rcases hcases with
    ⟨eraser, hready, hnilNil, hnilCons, hconsNil,
      hconsCons⟩
  refine ⟨eraser, hready, ?_, ?_⟩
  · intro T0 T1 padding
    cases padding with
    | nil =>
        exact hnilNil T0 T1
    | cons pad padding =>
        exact hnilCons T0 T1 pad padding
  · intro T0 T1 bit rest padding
    cases padding with
    | nil =>
        exact hconsNil T0 T1 bit rest
    | cons pad padding =>
        exact hconsCons T0 T1 bit rest pad padding

/--
Reusable structured-prefix eraser handoff contract.

A single eraser removes the two guarded structured logical tapes that precede
the selected logical-tape decoder footprint, for every selected payload and
padding shape.  The nil/cons and padding-specific contracts above are views of
this one machine contract.
-/
def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    forall (T0 T1 : Tape Bool) (bits : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding)
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          bits padding)

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction :
    Prop :=
  exists eraser : MachineDescription,
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec
      eraser

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec_of_guardedPrefixEraserSpec
    {eraser : MachineDescription}
    (hguard :
      GuardedTwoTapeStructuredPrefixEraserSpec eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec
      eraser := by
  rcases hguard with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro T0 T1 bits padding
  simpa [
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_eq_guardedTwoTapeStructuredPrefixEraserSourceTape,
    guardedTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
    hrun T0 T1 bits padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction_of_guardedPrefixEraser
    (hguard :
      GuardedTwoTapeStructuredPrefixEraserConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction := by
  rcases hguard with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec_of_guardedPrefixEraserSpec
        hspec⟩

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    forall (T0 T1 : Tape Bool) (bits : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding)
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            bits padding))

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputConstruction :
    Prop :=
  exists eraser : MachineDescription,
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputSpec
      eraser

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseOutputSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall (T0 T1 : Tape Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] padding)
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            [] padding))) ∧
    forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) padding)
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            (bit :: rest) padding))

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseOutputConstruction :
    Prop :=
  exists eraser : MachineDescription,
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseOutputSpec
      eraser

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseOutputSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall T0 T1 : Tape Bool,
      eraser.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] [])
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            [] []))) ∧
    (forall (T0 T1 : Tape Bool) (pad : Option Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (pad :: padding))
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            [] (pad :: padding)))) ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool),
      eraser.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) [])
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            (bit :: rest) []))) ∧
    forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (pad : Option Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (pad :: padding))
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            (bit :: rest) (pad :: padding)))

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseOutputConstruction :
    Prop :=
  exists eraser : MachineDescription,
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseOutputSpec
      eraser

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseOutputSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall T0 T1 : Tape Bool,
      eraser.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] [])
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            [] []))) ∧
    (forall (T0 T1 : Tape Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (none :: padding))
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            [] (none :: padding)))) ∧
    (forall (T0 T1 : Tape Bool) (padBit : Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (some padBit :: padding))
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            [] (some padBit :: padding)))) ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool),
      eraser.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) [])
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            (bit :: rest) []))) ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (none :: padding))
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            (bit :: rest) (none :: padding)))) ∧
    forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (some padBit :: padding))
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            (bit :: rest) (some padBit :: padding)))

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseOutputConstruction :
    Prop :=
  exists eraser : MachineDescription,
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseOutputSpec
      eraser

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseOutputSpec_of_outputSpec
    {eraser : MachineDescription}
    (heraser :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseOutputSpec
      eraser := by
  rcases heraser with ⟨hready, hrun⟩
  refine ⟨hready, ?_, ?_⟩
  · intro T0 T1 padding
    exact hrun T0 T1 [] padding
  · intro T0 T1 bit rest padding
    exact hrun T0 T1 (bit :: rest) padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseOutputConstruction_of_output
    (heraser :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseOutputConstruction := by
  rcases heraser with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseOutputSpec_of_outputSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputSpec_of_caseOutputSpec
    {eraser : MachineDescription}
    (hcases :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseOutputSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputSpec
      eraser := by
  rcases hcases with ⟨hready, hnil, hcons⟩
  refine ⟨hready, ?_⟩
  intro T0 T1 bits padding
  cases bits with
  | nil =>
      exact hnil T0 T1 padding
  | cons bit rest =>
      exact hcons T0 T1 bit rest padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputConstruction_of_caseOutput
    (hcases :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseOutputConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputConstruction := by
  rcases hcases with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputSpec_of_caseOutputSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseOutputSpec_of_bitPaddingCaseOutputSpec
    {eraser : MachineDescription}
    (hcases :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseOutputSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseOutputSpec
      eraser := by
  rcases hcases with
    ⟨hready, hnilNil, hnilCons, hconsNil, hconsCons⟩
  refine ⟨hready, ?_, ?_⟩
  · intro T0 T1 padding
    cases padding with
    | nil =>
        exact hnilNil T0 T1
    | cons pad padding =>
        exact hnilCons T0 T1 pad padding
  · intro T0 T1 bit rest padding
    cases padding with
    | nil =>
        exact hconsNil T0 T1 bit rest
    | cons pad padding =>
        exact hconsCons T0 T1 bit rest pad padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseOutputConstruction_of_bitPaddingCasesOutput
    (hcases :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseOutputConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseOutputConstruction := by
  rcases hcases with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseOutputSpec_of_bitPaddingCaseOutputSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseOutputSpec_of_padSymbolCaseOutputSpec
    {eraser : MachineDescription}
    (hcases :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseOutputSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseOutputSpec
      eraser := by
  rcases hcases with
    ⟨hready, hnilNil, hnilNone, hnilSome, hconsNil,
      hconsNone, hconsSome⟩
  refine ⟨hready, hnilNil, ?_, hconsNil, ?_⟩
  · intro T0 T1 pad padding
    cases pad with
    | none =>
        exact hnilNone T0 T1 padding
    | some padBit =>
        exact hnilSome T0 T1 padBit padding
  · intro T0 T1 bit rest pad padding
    cases pad with
    | none =>
        exact hconsNone T0 T1 bit rest padding
    | some padBit =>
        exact hconsSome T0 T1 bit rest padBit padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseOutputConstruction_of_padSymbolCasesOutput
    (hcases :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseOutputConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseOutputConstruction := by
  rcases hcases with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseOutputSpec_of_padSymbolCaseOutputSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseOutputConstruction_of_padSymbolCasesOutput
    (hcases :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseOutputConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseOutputConstruction :=
  selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseOutputConstruction_of_bitPaddingCasesOutput
    (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseOutputConstruction_of_padSymbolCasesOutput
      hcases)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputConstruction_of_padSymbolCasesOutput
    (hcases :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseOutputConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputConstruction :=
  selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputConstruction_of_caseOutput
    (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseOutputConstruction_of_padSymbolCasesOutput
      hcases)

/--
Normalized-output version of the structured-prefix footprint handoff.
This is the endpoint needed by callers that only consume the decoded selected
payload and padding, not the exact physical cursor left by the eraser.
-/
def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    forall (T0 T1 : Tape Bool) (bits : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding)
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
            bits padding))

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputConstruction :
    Prop :=
  exists eraser : MachineDescription,
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputSpec
      eraser

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputSpec_of_exact
    {eraser : MachineDescription}
    (heraser :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputSpec
      eraser := by
  rcases heraser with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro T0 T1 bits padding
  rcases hrun T0 T1 bits padding with ⟨actual, hhalt, hequiv⟩
  have houtput :=
    MachineDescription.haltsFromTapeWithOutput_of_haltsFromTape hhalt
  rw [Tape.Equiv.normalizedOutput_eq hequiv] at houtput
  exact houtput

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputConstruction_of_exact
    (heraser :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputConstruction := by
  rcases heraser with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputSpec_of_exact
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputSpec_of_exact
    {eraser : MachineDescription}
    (hhandoff :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputSpec
      eraser := by
  rcases hhandoff with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro T0 T1 bits padding
  rcases hrun T0 T1 bits padding with ⟨actual, hhalt, hequiv⟩
  have houtput :=
    MachineDescription.haltsFromTapeWithOutput_of_haltsFromTape hhalt
  rw [Tape.Equiv.normalizedOutput_eq hequiv] at houtput
  exact houtput

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputConstruction_of_exact
    (hhandoff :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputConstruction := by
  rcases hhandoff with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputSpec_of_exact
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputSpec_of_eraserOutputSpec
    {eraser : MachineDescription}
    (heraser :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputSpec
      eraser := by
  rcases heraser with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro T0 T1 bits padding
  simpa [
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
    hrun T0 T1 bits padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputConstruction_of_eraserOutput
    (heraser :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputConstruction := by
  rcases heraser with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputSpec_of_eraserOutputSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputSpec_of_footprintHandoffOutputSpec
    {eraser : MachineDescription}
    (hhandoff :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputSpec
      eraser := by
  rcases hhandoff with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro T0 T1 bits padding
  simpa [
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
    hrun T0 T1 bits padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputConstruction_of_footprintHandoffOutput
    (hhandoff :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputConstruction := by
  rcases hhandoff with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputSpec_of_footprintHandoffOutputSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputSpec_iff_footprintHandoffOutputSpec
    (eraser : MachineDescription) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputSpec
        eraser ↔
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputSpec
        eraser := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputSpec_of_eraserOutputSpec
  · exact
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputSpec_of_footprintHandoffOutputSpec

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputConstruction_iff_footprintHandoffOutputConstruction :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputConstruction ↔
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputConstruction := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputConstruction_of_eraserOutput
  · exact
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserOutputConstruction_of_footprintHandoffOutput

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffNilPadSymbolCaseOutputSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall T0 T1 : Tape Bool,
      eraser.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] [])
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
            [] []))) ∧
    (forall (T0 T1 : Tape Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (none :: padding))
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
            [] (none :: padding)))) ∧
    forall (T0 T1 : Tape Bool) (padBit : Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (some padBit :: padding))
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
            [] (some padBit :: padding)))

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConsPadSymbolCaseOutputSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool),
      eraser.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) [])
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
            (bit :: rest) []))) ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (none :: padding))
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
            (bit :: rest) (none :: padding)))) ∧
    forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (some padBit :: padding))
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
            (bit :: rest) (some padBit :: padding)))

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseOutputSpec
    (eraser : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffNilPadSymbolCaseOutputSpec
      eraser ∧
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConsPadSymbolCaseOutputSpec
      eraser

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseOutputConstruction :
    Prop :=
  exists eraser : MachineDescription,
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseOutputSpec
      eraser

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseOutputSpec_of_handoffOutputSpec
    {eraser : MachineDescription}
    (hhandoff :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseOutputSpec
      eraser := by
  rcases hhandoff with ⟨hready, hrun⟩
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

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseOutputConstruction_of_handoffOutput
    (hhandoff :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseOutputConstruction := by
  rcases hhandoff with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseOutputSpec_of_handoffOutputSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputSpec_of_splitPadSymbolCaseOutputSpec
    {eraser : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseOutputSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputSpec
      eraser := by
  rcases hsplit with ⟨hnil, hcons⟩
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

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputConstruction_of_splitPadSymbolCaseOutput
    (hsplit :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseOutputConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputConstruction := by
  rcases hsplit with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputSpec_of_splitPadSymbolCaseOutputSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputSpec_iff_splitPadSymbolCaseOutputSpec
    (eraser : MachineDescription) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputSpec
        eraser ↔
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseOutputSpec
        eraser := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseOutputSpec_of_handoffOutputSpec
  · exact
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputSpec_of_splitPadSymbolCaseOutputSpec

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputConstruction_iff_splitPadSymbolCaseOutputConstruction :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputConstruction ↔
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseOutputConstruction := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseOutputConstruction_of_handoffOutput
  · exact
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffOutputConstruction_of_splitPadSymbolCaseOutput

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseOutputSpec_of_exact
    {eraser : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseOutputSpec
      eraser := by
  rcases hsplit with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  have toOutput :
      forall {Tin Tout : Tape Bool},
        eraser.HaltsFromTapeEquiv Tin Tout ->
          eraser.HaltsFromTapeWithOutput Tin
            (Tape.normalizedOutput Tout) := by
    intro Tin Tout hhaltEquiv
    rcases hhaltEquiv with ⟨actual, hhalt, hequiv⟩
    have houtput :=
      MachineDescription.haltsFromTapeWithOutput_of_haltsFromTape hhalt
    rw [Tape.Equiv.normalizedOutput_eq hequiv] at houtput
    exact houtput
  refine ⟨?_, ?_⟩
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro T0 T1
      exact toOutput (hnilNil T0 T1)
    · intro T0 T1 padding
      exact toOutput (hnilNone T0 T1 padding)
    · intro T0 T1 padBit padding
      exact toOutput (hnilSome T0 T1 padBit padding)
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro T0 T1 bit rest
      exact toOutput (hconsNil T0 T1 bit rest)
    · intro T0 T1 bit rest padding
      exact toOutput (hconsNone T0 T1 bit rest padding)
    · intro T0 T1 bit rest padBit padding
      exact toOutput (hconsSome T0 T1 bit rest padBit padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseOutputConstruction_of_exact
    (hsplit :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseOutputConstruction := by
  rcases hsplit with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseOutputSpec_of_exact
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec_of_handoffSpec
    {eraser : MachineDescription}
    (hhandoff :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec
      eraser := by
  rcases hhandoff with ⟨hready, hrun⟩
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

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction_of_handoff
    (hhandoff :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction := by
  rcases hhandoff with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec_of_handoffSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction_of_footprintHandoff
    (hhandoff :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction := by
  rcases hhandoff with ⟨eraser, hready, hrun⟩
  refine ⟨eraser, hready, ?_⟩
  intro T0 T1 bits padding
  simpa [
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
    hrun T0 T1 bits padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec_of_eraserSpec
    {eraser : MachineDescription}
    (heraser :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec
      eraser := by
  rcases heraser with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro T0 T1 bits padding
  simpa [
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
    hrun T0 T1 bits padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction_of_eraser
    (heraser :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction := by
  rcases heraser with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec_of_eraserSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec_iff_eraserSpec
    (eraser : MachineDescription) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec
        eraser ↔
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSpec
        eraser := by
  constructor
  · intro hhandoff
    rcases hhandoff with ⟨hready, hrun⟩
    refine ⟨hready, ?_⟩
    intro T0 T1 bits padding
    simpa [
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
      hrun T0 T1 bits padding
  · exact
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec_of_eraserSpec

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction_iff_eraserConstruction :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction ↔
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction_of_footprintHandoff
  · exact
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction_of_eraser

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec_of_splitPadSymbolCaseSpec
    {eraser : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec
      eraser := by
  rcases hsplit with ⟨hnil, hcons⟩
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

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction_of_splitPadSymbolCases
    (hsplit :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction := by
  rcases hsplit with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec_of_splitPadSymbolCaseSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec_iff_splitPadSymbolCaseSpec
    (eraser : MachineDescription) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec
        eraser ↔
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec
        eraser := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec_of_handoffSpec
  · exact
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec_of_splitPadSymbolCaseSpec

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction_iff_splitPadSymbolCaseConstruction :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction ↔
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction_of_handoff
  · exact
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction_of_splitPadSymbolCases

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction_core :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction := by
  -- Remaining finite-machine leaf: delete the concrete two-tape guarded
  -- structured prefix for each nil/cons payload and padding-symbol branch.
  sorry

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction_core :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction_of_splitPadSymbolCases
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction_core

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction_core :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction_of_footprintHandoff
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction_core

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseConstruction_core :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseConstruction := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseConstruction_of_split
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction_core

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseConstruction_core :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseConstruction := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseConstruction_of_padSymbolCases
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseConstruction_core

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseConstruction_core :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseConstruction := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseConstruction_of_bitPaddingCases
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseConstruction_core

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction_core :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction_of_footprintHandoff
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction_core

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters
end Computability
end FoC
