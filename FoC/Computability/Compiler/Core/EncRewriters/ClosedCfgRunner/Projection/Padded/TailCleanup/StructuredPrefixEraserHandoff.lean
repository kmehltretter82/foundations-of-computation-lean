import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.SelectedFootprintCompaction

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

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape_nil_nil :
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
        [] [] =
      selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] [] := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape
      [] []

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape_nil_none
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
        [] (none :: padding) =
      selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] (none :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape
      [] (none :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape_nil_some
    (padBit : Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
        [] (some padBit :: padding) =
      selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] (some padBit :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape
      [] (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape_cons_nil
    (bit : Bool) (rest : Word Bool) :
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
        (bit :: rest) [] =
      selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        (bit :: rest) [] := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape
      (bit :: rest) []

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape_cons_none
    (bit : Bool) (rest : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
        (bit :: rest) (none :: padding) =
      selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        (bit :: rest) (none :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape
      (bit :: rest) (none :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape_cons_some
    (bit : Bool) (rest : Word Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
        (bit :: rest) (some padBit :: padding) =
      selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        (bit :: rest) (some padBit :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape
      (bit :: rest) (some padBit :: padding)

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

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput_eq_guardedBits_append_targetTape_normalizedOutput_nil_nil
    (T0 T1 : Tape Bool) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] []) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (Tape.normalizedOutput
            (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
              [] []))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput_eq_guardedBits_append_targetTape_normalizedOutput
      T0 T1 [] []

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput_eq_guardedBits_append_targetTape_normalizedOutput_nil_none
    (T0 T1 : Tape Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (none :: padding)) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (Tape.normalizedOutput
            (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
              [] (none :: padding)))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput_eq_guardedBits_append_targetTape_normalizedOutput
      T0 T1 [] (none :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput_eq_guardedBits_append_targetTape_normalizedOutput_nil_some
    (T0 T1 : Tape Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (some padBit :: padding)) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (Tape.normalizedOutput
            (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
              [] (some padBit :: padding)))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput_eq_guardedBits_append_targetTape_normalizedOutput
      T0 T1 [] (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput_eq_guardedBits_append_targetTape_normalizedOutput_cons_nil
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) []) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (Tape.normalizedOutput
            (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
              (bit :: rest) []))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput_eq_guardedBits_append_targetTape_normalizedOutput
      T0 T1 (bit :: rest) []

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput_eq_guardedBits_append_targetTape_normalizedOutput_cons_none
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (none :: padding)) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (Tape.normalizedOutput
            (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
              (bit :: rest) (none :: padding)))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput_eq_guardedBits_append_targetTape_normalizedOutput
      T0 T1 (bit :: rest) (none :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput_eq_guardedBits_append_targetTape_normalizedOutput_cons_some
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
    (padBit : Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (some padBit :: padding)) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (Tape.normalizedOutput
            (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
              (bit :: rest) (some padBit :: padding)))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput_eq_guardedBits_append_targetTape_normalizedOutput
      T0 T1 (bit :: rest) (some padBit :: padding)

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

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_nil_nil
    (T0 T1 : Tape Bool) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] [])).filterMap (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (logicalTapeBits (guardLogicalTape T1)) := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits]
  simp

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_nil_none
    (T0 T1 : Tape Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (none :: padding))).filterMap (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (padding.filterMap (fun cell => cell))) := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits]
  simp

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_nil_some
    (T0 T1 : Tape Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (some padBit :: padding))).filterMap
        (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (padBit :: padding.filterMap (fun cell => cell))) := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits]
  simp

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_cons_nil
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) [])).filterMap (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (bit :: rest)) := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits]
  simp

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_cons_none
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (none :: padding))).filterMap
        (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (List.append (bit :: rest)
            (padding.filterMap (fun cell => cell)))) := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits]
  simp

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_cons_some
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
    (padBit : Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (some padBit :: padding))).filterMap
        (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (List.append (bit :: rest)
            (padBit :: padding.filterMap (fun cell => cell)))) := by
  rw [selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits]
  simp

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

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_append_targetTape_cells_filterMap_nil_nil
    (T0 T1 : Tape Bool) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] [])).filterMap (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          ((Tape.cells
            (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
              [] [])).filterMap (fun cell => cell))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_append_targetTape_cells_filterMap
      T0 T1 [] []

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_append_targetTape_cells_filterMap_nil_none
    (T0 T1 : Tape Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (none :: padding))).filterMap (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          ((Tape.cells
            (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
              [] (none :: padding))).filterMap (fun cell => cell))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_append_targetTape_cells_filterMap
      T0 T1 [] (none :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_append_targetTape_cells_filterMap_nil_some
    (T0 T1 : Tape Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (some padBit :: padding))).filterMap
        (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          ((Tape.cells
            (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
              [] (some padBit :: padding))).filterMap
              (fun cell => cell))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_append_targetTape_cells_filterMap
      T0 T1 [] (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_append_targetTape_cells_filterMap_cons_nil
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) [])).filterMap (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          ((Tape.cells
            (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
              (bit :: rest) [])).filterMap (fun cell => cell))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_append_targetTape_cells_filterMap
      T0 T1 (bit :: rest) []

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_append_targetTape_cells_filterMap_cons_none
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (none :: padding))).filterMap
        (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          ((Tape.cells
            (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
              (bit :: rest) (none :: padding))).filterMap
              (fun cell => cell))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_append_targetTape_cells_filterMap
      T0 T1 (bit :: rest) (none :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_append_targetTape_cells_filterMap_cons_some
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
    (padBit : Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (some padBit :: padding))).filterMap
        (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          ((Tape.cells
            (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
              (bit :: rest) (some padBit :: padding))).filterMap
              (fun cell => cell))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits_append_targetTape_cells_filterMap
      T0 T1 (bit :: rest) (some padBit :: padding)

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

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_targetTape_cells_nil_nil
    (T0 T1 : Tape Bool) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] []) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape T0))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode (guardLogicalTape T1))
              (Tape.cells
                (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
                  [] []))))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_targetTape_cells
      T0 T1 [] []

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_targetTape_cells_nil_none
    (T0 T1 : Tape Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (none :: padding)) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape T0))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode (guardLogicalTape T1))
              (Tape.cells
                (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
                  [] (none :: padding)))))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_targetTape_cells
      T0 T1 [] (none :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_targetTape_cells_nil_some
    (T0 T1 : Tape Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (some padBit :: padding)) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape T0))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode (guardLogicalTape T1))
              (Tape.cells
                (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
                  [] (some padBit :: padding)))))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_targetTape_cells
      T0 T1 [] (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_targetTape_cells_cons_nil
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) []) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape T0))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode (guardLogicalTape T1))
              (Tape.cells
                (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
                  (bit :: rest) []))))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_targetTape_cells
      T0 T1 (bit :: rest) []

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_targetTape_cells_cons_none
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (none :: padding)) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape T0))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode (guardLogicalTape T1))
              (Tape.cells
                (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
                  (bit :: rest) (none :: padding)))))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_targetTape_cells
      T0 T1 (bit :: rest) (none :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_targetTape_cells_cons_some
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
    (padBit : Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (some padBit :: padding)) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape T0))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode (guardLogicalTape T1))
              (Tape.cells
                (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
                  (bit :: rest) (some padBit :: padding)))))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_targetTape_cells
      T0 T1 (bit :: rest) (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells_nil_nil
    (T0 T1 : Tape Bool) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] []) =
      List.append
        (encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1])
        (Tape.cells
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            [] [])) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells
      T0 T1 [] []

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells_nil_cons
    (T0 T1 : Tape Bool) (pad : Option Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (pad :: padding)) =
      List.append
        (encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1])
        (Tape.cells
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            [] (pad :: padding))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells
      T0 T1 [] (pad :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells_nil_none
    (T0 T1 : Tape Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (none :: padding)) =
      List.append
        (encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1])
        (Tape.cells
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            [] (none :: padding))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells_nil_cons
      T0 T1 none padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells_nil_some
    (T0 T1 : Tape Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (some padBit :: padding)) =
      List.append
        (encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1])
        (Tape.cells
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            [] (some padBit :: padding))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells_nil_cons
      T0 T1 (some padBit) padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells_cons_nil
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) []) =
      List.append
        (encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1])
        (Tape.cells
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            (bit :: rest) [])) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells
      T0 T1 (bit :: rest) []

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells_cons_cons
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
    (pad : Option Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (pad :: padding)) =
      List.append
        (encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1])
        (Tape.cells
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            (bit :: rest) (pad :: padding))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells
      T0 T1 (bit :: rest) (pad :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells_cons_none
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (none :: padding)) =
      List.append
        (encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1])
        (Tape.cells
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            (bit :: rest) (none :: padding))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells_cons_cons
      T0 T1 bit rest none padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells_cons_some
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
    (padBit : Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (some padBit :: padding)) =
      List.append
        (encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1])
        (Tape.cells
          (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
            (bit :: rest) (some padBit :: padding))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_targetTape_cells_cons_cons
      T0 T1 bit rest (some padBit) padding

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

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_footprintSourceTape_cells_nil_nil
    (T0 T1 : Tape Bool) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] []) =
      List.append
        (encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1])
        (Tape.cells
          (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
            [] [])) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_footprintSourceTape_cells
      T0 T1 [] []

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_footprintSourceTape_cells_nil_none
    (T0 T1 : Tape Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (none :: padding)) =
      List.append
        (encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1])
        (Tape.cells
          (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
            [] (none :: padding))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_footprintSourceTape_cells
      T0 T1 [] (none :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_footprintSourceTape_cells_nil_some
    (T0 T1 : Tape Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (some padBit :: padding)) =
      List.append
        (encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1])
        (Tape.cells
          (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
            [] (some padBit :: padding))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_footprintSourceTape_cells
      T0 T1 [] (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_footprintSourceTape_cells_cons_nil
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) []) =
      List.append
        (encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1])
        (Tape.cells
          (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
            (bit :: rest) [])) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_footprintSourceTape_cells
      T0 T1 (bit :: rest) []

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_footprintSourceTape_cells_cons_none
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (none :: padding)) =
      List.append
        (encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1])
        (Tape.cells
          (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
            (bit :: rest) (none :: padding))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_footprintSourceTape_cells
      T0 T1 (bit :: rest) (none :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_footprintSourceTape_cells_cons_some
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
    (padBit : Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (some padBit :: padding)) =
      List.append
        (encodedStructuredTapeCellsPrefix
          [guardLogicalTape T0, guardLogicalTape T1])
        (Tape.cells
          (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
            (bit :: rest) (some padBit :: padding))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_prefix_append_footprintSourceTape_cells
      T0 T1 (bit :: rest) (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_footprintSourceTape_cells_nil_nil
    (T0 T1 : Tape Bool) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] []) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape T0))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode (guardLogicalTape T1))
              (Tape.cells
                (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
                  [] []))))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_footprintSourceTape_cells
      T0 T1 [] []

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_footprintSourceTape_cells_nil_none
    (T0 T1 : Tape Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (none :: padding)) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape T0))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode (guardLogicalTape T1))
              (Tape.cells
                (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
                  [] (none :: padding)))))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_footprintSourceTape_cells
      T0 T1 [] (none :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_footprintSourceTape_cells_nil_some
    (T0 T1 : Tape Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (some padBit :: padding)) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape T0))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode (guardLogicalTape T1))
              (Tape.cells
                (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
                  [] (some padBit :: padding)))))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_footprintSourceTape_cells
      T0 T1 [] (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_footprintSourceTape_cells_cons_nil
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) []) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape T0))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode (guardLogicalTape T1))
              (Tape.cells
                (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
                  (bit :: rest) []))))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_footprintSourceTape_cells
      T0 T1 (bit :: rest) []

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_footprintSourceTape_cells_cons_none
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (none :: padding)) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape T0))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode (guardLogicalTape T1))
              (Tape.cells
                (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
                  (bit :: rest) (none :: padding)))))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_footprintSourceTape_cells
      T0 T1 (bit :: rest) (none :: padding)

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_footprintSourceTape_cells_cons_some
    (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
    (padBit : Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (some padBit :: padding)) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape T0))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode (guardLogicalTape T1))
              (Tape.cells
                (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
                  (bit :: rest) (some padBit :: padding)))))) := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_cells_eq_expandedPrefix_append_footprintSourceTape_cells
      T0 T1 (bit :: rest) (some padBit :: padding)

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
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape_nil_nil] using
        hnilNil T0 T1
    · intro T0 T1 padding
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape_nil_none] using
        hnilNone T0 T1 padding
    · intro T0 T1 padBit padding
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape_nil_some] using
        hnilSome T0 T1 padBit padding
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro T0 T1 bit rest
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape_cons_nil] using
        hconsNil T0 T1 bit rest
    · intro T0 T1 bit rest padding
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape_cons_none] using
        hconsNone T0 T1 bit rest padding
    · intro T0 T1 bit rest padBit padding
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape_cons_some] using
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
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape_nil_nil] using
        hnilNil T0 T1
    · intro T0 T1 padding
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape_nil_none] using
        hnilNone T0 T1 padding
    · intro T0 T1 padBit padding
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape_nil_some] using
        hnilSome T0 T1 padBit padding
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro T0 T1 bit rest
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape_cons_nil] using
        hconsNil T0 T1 bit rest
    · intro T0 T1 bit rest padding
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape_cons_none] using
        hconsNone T0 T1 bit rest padding
    · intro T0 T1 bit rest padBit padding
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape_cons_some] using
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

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction_of_handoff
    (hhandoff :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction := by
  rcases hhandoff with ⟨eraser, hready, hrun⟩
  refine ⟨eraser, ?_, ?_⟩
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

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction_core :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction := by
  sorry

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction_core :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction := by
  exact
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction_of_handoff
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction_core

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
