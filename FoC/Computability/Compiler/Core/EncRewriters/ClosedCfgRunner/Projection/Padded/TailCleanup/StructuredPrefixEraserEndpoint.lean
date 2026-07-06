import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.StructuredPrefixEraserShape

set_option doc.verso true

/-!
# Guarded structured-prefix eraser endpoint views

This module records exact parking facts for the generic two-tape structured
prefix eraser isolated in the structured-prefix shape module.  The shape
module already exposes the visible cells and output-level contracts.  The
lemmas here make the endpoint positions explicit: the decoder output is parked
at the right edge, while the reusable boundary eraser helpers are parked at
the field-local separators.
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

/-- The right-edge left stack of the generic structured-prefix source. -/
def guardedTwoTapeStructuredPrefixEraserSourceRightEdgeLeftStack
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) : List (Option Bool) :=
  none ::
    List.append
      (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
        bits padding).reverse
      (none :: (guardedTwoTapeStructuredPrefixCells T0 T1).reverse)

/-- The right-edge left stack of the generic structured-prefix target. -/
def guardedTwoTapeStructuredPrefixEraserTargetRightEdgeLeftStack
    (bits : Word Bool) (padding : List (Option Bool)) :
    List (Option Bool) :=
  none ::
    List.append
      (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
        bits padding).reverse
      [none]

/-- Right-edge parked source tape, as an explicit {name}`tapeAtCells` shape. -/
def guardedTwoTapeStructuredPrefixEraserSourceRightEdgeTape
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (guardedTwoTapeStructuredPrefixEraserSourceRightEdgeLeftStack
      T0 T1 bits padding)
    []

/-- Right-edge parked target tape, as an explicit {name}`tapeAtCells` shape. -/
def guardedTwoTapeStructuredPrefixEraserTargetRightEdgeTape
    (bits : Word Bool) (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (guardedTwoTapeStructuredPrefixEraserTargetRightEdgeLeftStack
      bits padding)
    []

theorem guardedTwoTapeStructuredPrefixEraserSourceTape_left
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (guardedTwoTapeStructuredPrefixEraserSourceTape
        T0 T1 bits padding).left =
      guardedTwoTapeStructuredPrefixEraserSourceRightEdgeLeftStack
        T0 T1 bits padding := by
  simp [guardedTwoTapeStructuredPrefixEraserSourceTape,
    guardedTwoTapeStructuredPrefixEraserSourceRightEdgeLeftStack,
    selectedSegmentLogicalTapeDecoderTargetTape_left,
    selectedSegmentLogicalTapeDecoderStart,
    selectedSegmentLogicalTapeDecoder_cells_guard_rightEdgeScanSourceTapeFromLeft_eq_footprint]

theorem guardedTwoTapeStructuredPrefixEraserSourceTape_head
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (guardedTwoTapeStructuredPrefixEraserSourceTape
        T0 T1 bits padding).head = none := by
  rfl

theorem guardedTwoTapeStructuredPrefixEraserSourceTape_right
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (guardedTwoTapeStructuredPrefixEraserSourceTape
        T0 T1 bits padding).right = [] := by
  rfl

theorem guardedTwoTapeStructuredPrefixEraserSourceTape_eq_rightEdgeTape
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    guardedTwoTapeStructuredPrefixEraserSourceTape
        T0 T1 bits padding =
      guardedTwoTapeStructuredPrefixEraserSourceRightEdgeTape
        T0 T1 bits padding := by
  cases hsource :
      guardedTwoTapeStructuredPrefixEraserSourceTape
        T0 T1 bits padding with
  | mk left head right =>
      have hleft :
          left =
            guardedTwoTapeStructuredPrefixEraserSourceRightEdgeLeftStack
              T0 T1 bits padding := by
        simpa [hsource] using
          guardedTwoTapeStructuredPrefixEraserSourceTape_left
            T0 T1 bits padding
      have hhead : head = none := by
        simpa [hsource] using
          guardedTwoTapeStructuredPrefixEraserSourceTape_head
            T0 T1 bits padding
      have hright : right = [] := by
        simpa [hsource] using
          guardedTwoTapeStructuredPrefixEraserSourceTape_right
            T0 T1 bits padding
      subst left
      subst head
      subst right
      simp [guardedTwoTapeStructuredPrefixEraserSourceRightEdgeTape,
        tapeAtCells]

theorem guardedTwoTapeStructuredPrefixEraserTargetTape_left
    (bits : Word Bool) (padding : List (Option Bool)) :
    (guardedTwoTapeStructuredPrefixEraserTargetTape
        bits padding).left =
      guardedTwoTapeStructuredPrefixEraserTargetRightEdgeLeftStack
        bits padding := by
  rw [guardedTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape]
  simp [selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape,
    guardedTwoTapeStructuredPrefixEraserTargetRightEdgeLeftStack,
    selectedSegmentLogicalTapeDecoderTargetTape_left,
    selectedSegmentLogicalTapeDecoderStart,
    selectedSegmentLogicalTapeDecoder_cells_guard_rightEdgeScanSourceTapeFromLeft_eq_footprint]

theorem guardedTwoTapeStructuredPrefixEraserTargetTape_head
    (bits : Word Bool) (padding : List (Option Bool)) :
    (guardedTwoTapeStructuredPrefixEraserTargetTape
        bits padding).head = none := by
  rfl

theorem guardedTwoTapeStructuredPrefixEraserTargetTape_right
    (bits : Word Bool) (padding : List (Option Bool)) :
    (guardedTwoTapeStructuredPrefixEraserTargetTape
        bits padding).right = [] := by
  rfl

theorem guardedTwoTapeStructuredPrefixEraserTargetTape_eq_rightEdgeTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    guardedTwoTapeStructuredPrefixEraserTargetTape bits padding =
      guardedTwoTapeStructuredPrefixEraserTargetRightEdgeTape
        bits padding := by
  cases htarget :
      guardedTwoTapeStructuredPrefixEraserTargetTape
        bits padding with
  | mk left head right =>
      have hleft :
          left =
            guardedTwoTapeStructuredPrefixEraserTargetRightEdgeLeftStack
              bits padding := by
        simpa [htarget] using
          guardedTwoTapeStructuredPrefixEraserTargetTape_left
            bits padding
      have hhead : head = none := by
        simpa [htarget] using
          guardedTwoTapeStructuredPrefixEraserTargetTape_head
            bits padding
      have hright : right = [] := by
        simpa [htarget] using
          guardedTwoTapeStructuredPrefixEraserTargetTape_right
            bits padding
      subst left
      subst head
      subst right
      simp [guardedTwoTapeStructuredPrefixEraserTargetRightEdgeTape,
        tapeAtCells]

theorem guardedTwoTapeStructuredPrefixEraserSourceRightEdgeLeftStack_reverse
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (guardedTwoTapeStructuredPrefixEraserSourceRightEdgeLeftStack
        T0 T1 bits padding).reverse =
      List.append (guardedTwoTapeStructuredPrefixCells T0 T1)
        (none ::
          List.append
            (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
              bits padding)
            [none]) := by
  simp [guardedTwoTapeStructuredPrefixEraserSourceRightEdgeLeftStack,
    List.reverse_append, List.append_assoc]

theorem guardedTwoTapeStructuredPrefixEraserTargetRightEdgeLeftStack_reverse
    (bits : Word Bool) (padding : List (Option Bool)) :
    (guardedTwoTapeStructuredPrefixEraserTargetRightEdgeLeftStack
        bits padding).reverse =
      none ::
        List.append
          (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
            bits padding)
          [none] := by
  simp [guardedTwoTapeStructuredPrefixEraserTargetRightEdgeLeftStack,
    List.reverse_append]

theorem guardedTwoTapeStructuredPrefixEraserSourceRightEdgeTape_cells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (guardedTwoTapeStructuredPrefixEraserSourceRightEdgeTape
          T0 T1 bits padding) =
      List.append (guardedTwoTapeStructuredPrefixCells T0 T1)
        (none ::
          List.append
            (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
              bits padding)
            [none, none]) := by
  simp [guardedTwoTapeStructuredPrefixEraserSourceRightEdgeTape,
    tapeAtCells, Tape.cells,
    guardedTwoTapeStructuredPrefixEraserSourceRightEdgeLeftStack_reverse,
    List.append_assoc]

theorem guardedTwoTapeStructuredPrefixEraserTargetRightEdgeTape_cells
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.cells
        (guardedTwoTapeStructuredPrefixEraserTargetRightEdgeTape
          bits padding) =
      none ::
        List.append
          (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
            bits padding)
          [none, none] := by
  simp [guardedTwoTapeStructuredPrefixEraserTargetRightEdgeTape,
    tapeAtCells, Tape.cells,
    guardedTwoTapeStructuredPrefixEraserTargetRightEdgeLeftStack_reverse,
    List.append_assoc]

theorem guardedTwoTapeStructuredPrefixEraserSourceTape_cells_via_rightEdgeTape
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding) =
      Tape.cells
        (guardedTwoTapeStructuredPrefixEraserSourceRightEdgeTape
          T0 T1 bits padding) := by
  rw [guardedTwoTapeStructuredPrefixEraserSourceTape_eq_rightEdgeTape]

theorem guardedTwoTapeStructuredPrefixEraserTargetTape_cells_via_rightEdgeTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.cells
        (guardedTwoTapeStructuredPrefixEraserTargetTape
          bits padding) =
      Tape.cells
        (guardedTwoTapeStructuredPrefixEraserTargetRightEdgeTape
          bits padding) := by
  rw [guardedTwoTapeStructuredPrefixEraserTargetTape_eq_rightEdgeTape]

/-- Exact source of the second field-local boundary eraser. -/
def guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserSourceTape
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) : Tape Bool :=
  leftBoundaryEraserSourceTape
    (guardedTwoTapeStructuredPrefixSecondFieldEraserBaseLeft T0)
    (logicalTapeBits (guardLogicalTape T1))
    none
    (guardedTwoTapeStructuredPrefixSecondFieldEraserSuffixTail
      bits padding)

/-- Exact target of the second field-local boundary eraser. -/
def guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserTargetTape
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) : Tape Bool :=
  leftBoundaryEraserTargetTape
    (guardedTwoTapeStructuredPrefixSecondFieldEraserBaseLeft T0)
    (logicalTapeBits (guardLogicalTape T1))
    none
    (guardedTwoTapeStructuredPrefixSecondFieldEraserSuffixTail
      bits padding)

/-- Exact source of the first field-local boundary eraser. -/
def guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSourceTape
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) : Tape Bool :=
  leftBoundaryEraserSourceTape
    []
    (logicalTapeBits (guardLogicalTape T0))
    none
    (guardedTwoTapeStructuredPrefixFirstFieldEraserSuffixTail
      T1 bits padding)

/-- Exact target of the first field-local boundary eraser. -/
def guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) : Tape Bool :=
  leftBoundaryEraserTargetTape
    []
    (logicalTapeBits (guardLogicalTape T0))
    none
    (guardedTwoTapeStructuredPrefixFirstFieldEraserSuffixTail
      T1 bits padding)

theorem guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserSourceTape_cells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserSourceTape
          T0 T1 bits padding) =
      Tape.cells
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding) := by
  exact
    (guardedTwoTapeStructuredPrefixEraserSourceTape_cells_eq_secondFieldBoundaryEraserSourceTape_cells
      T0 T1 bits padding).symm

theorem guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserTargetTape_cells_eq
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserTargetTape
          T0 T1 bits padding) =
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
  exact
    guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserTargetTape_cells
      T0 T1 bits padding

theorem guardedTwoTapeStructuredPrefixSecondFieldTarget_cells_eq_firstFieldSource_cells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserTargetTape
          T0 T1 bits padding) =
      Tape.cells
        (guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSourceTape
          T0 T1 bits padding) := by
  exact
    guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserTargetTape_cells_eq_firstFieldBoundaryEraserSourceTape_cells
      T0 T1 bits padding

theorem guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSourceTape_cells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSourceTape
          T0 T1 bits padding) =
      Tape.cells
        (guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserTargetTape
          T0 T1 bits padding) := by
  exact
    (guardedTwoTapeStructuredPrefixSecondFieldTarget_cells_eq_firstFieldSource_cells
      T0 T1 bits padding).symm

theorem guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape_cells_eq
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape
          T0 T1 bits padding) =
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
  exact
    guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape_cells
      T0 T1 bits padding

theorem guardedTwoTapeStructuredPrefixFirstFieldTarget_cells_eq_erasedVisible
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape
          T0 T1 bits padding) =
      rightEndCompactionVisibleCells
        (guardedTwoTapeStructuredPrefixErasedFootprintLeftCells
          T0 T1 bits padding) := by
  exact
    guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape_cells_eq_erasedFootprintVisibleCells
      T0 T1 bits padding

theorem guardedTwoTapeStructuredPrefixSecondFieldBoundarySource_filterMap
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (Tape.cells
        (guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserSourceTape
          T0 T1 bits padding)).filterMap (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (List.append bits (padding.filterMap (fun cell => cell)))) := by
  rw [guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserSourceTape_cells]
  exact
    guardedTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits
      T0 T1 bits padding

theorem guardedTwoTapeStructuredPrefixSecondFieldBoundaryTarget_filterMap
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (Tape.cells
        (guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserTargetTape
          T0 T1 bits padding)).filterMap (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append bits (padding.filterMap (fun cell => cell))) := by
  exact
    guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserTargetTape_cells_filterMap
      T0 T1 bits padding

theorem guardedTwoTapeStructuredPrefixFirstFieldBoundarySource_filterMap
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (Tape.cells
        (guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSourceTape
          T0 T1 bits padding)).filterMap (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append bits (padding.filterMap (fun cell => cell))) := by
  rw [guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSourceTape_cells]
  exact
    guardedTwoTapeStructuredPrefixSecondFieldBoundaryTarget_filterMap
      T0 T1 bits padding

theorem guardedTwoTapeStructuredPrefixFirstFieldBoundaryTarget_filterMap
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (Tape.cells
        (guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape
          T0 T1 bits padding)).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  exact
    guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape_cells_filterMap
      T0 T1 bits padding

theorem guardedTwoTapeStructuredPrefixSecondFieldBoundarySource_normalizedOutput
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserSourceTape
          T0 T1 bits padding) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (List.append bits (padding.filterMap (fun cell => cell)))) := by
  rw [Tape.normalizedOutput, guardedTwoTapeStructuredPrefixSecondFieldBoundarySource_filterMap]

theorem guardedTwoTapeStructuredPrefixSecondFieldBoundaryTarget_normalizedOutput
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserTargetTape
          T0 T1 bits padding) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append bits (padding.filterMap (fun cell => cell))) := by
  rw [Tape.normalizedOutput, guardedTwoTapeStructuredPrefixSecondFieldBoundaryTarget_filterMap]

theorem guardedTwoTapeStructuredPrefixFirstFieldBoundarySource_normalizedOutput
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSourceTape
          T0 T1 bits padding) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append bits (padding.filterMap (fun cell => cell))) := by
  rw [Tape.normalizedOutput, guardedTwoTapeStructuredPrefixFirstFieldBoundarySource_filterMap]

theorem guardedTwoTapeStructuredPrefixFirstFieldBoundaryTarget_normalizedOutput
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape
          T0 T1 bits padding) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [Tape.normalizedOutput, guardedTwoTapeStructuredPrefixFirstFieldBoundaryTarget_filterMap]

theorem guardedTwoTapeStructuredPrefixSecondBoundaryEraserOutput_progress
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserSourceTape
          T0 T1 bits padding) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (Tape.normalizedOutput
            (guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape
              T0 T1 bits padding))) := by
  rw [
    guardedTwoTapeStructuredPrefixSecondFieldBoundarySource_normalizedOutput,
    guardedTwoTapeStructuredPrefixFirstFieldBoundaryTarget_normalizedOutput]

theorem guardedTwoTapeStructuredPrefixSecondBoundaryTarget_eq_firstBoundarySource_output
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserTargetTape
          T0 T1 bits padding) =
      Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSourceTape
          T0 T1 bits padding) := by
  rw [
    guardedTwoTapeStructuredPrefixSecondFieldBoundaryTarget_normalizedOutput,
    guardedTwoTapeStructuredPrefixFirstFieldBoundarySource_normalizedOutput]

theorem guardedTwoTapeStructuredPrefixFirstBoundaryEraserOutput_progress
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSourceTape
          T0 T1 bits padding) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (Tape.normalizedOutput
          (guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape
            T0 T1 bits padding)) := by
  rw [
    guardedTwoTapeStructuredPrefixFirstFieldBoundarySource_normalizedOutput,
    guardedTwoTapeStructuredPrefixFirstFieldBoundaryTarget_normalizedOutput]

theorem guardedTwoTapeStructuredPrefixBoundaryEraserOutput_progress
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserSourceTape
          T0 T1 bits padding) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (Tape.normalizedOutput
            (guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape
              T0 T1 bits padding))) := by
  rw [
    guardedTwoTapeStructuredPrefixSecondFieldBoundarySource_normalizedOutput,
    guardedTwoTapeStructuredPrefixFirstFieldBoundaryTarget_normalizedOutput]

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
