import FoC.Computability.Compiler.ClosedCfg.ProjTail.SelectedFootprintCompactionShape

set_option doc.verso true

/-!
# Selected decoder footprint compactor endpoint views

The footprint shape module exposes the payload-level source and target for the
remaining generic compactor primitive.  This module records the exact tape
parking facts behind those shapes: the source is a right-end compaction source
parked on the blank after the encoded footprint, and the target is the
right-edge rewind source parked on the blank after the compacted payload.
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

/-- Left stack for the generic footprint source, parameterized by payload. -/
def selectedSegmentLogicalTapeDecoderFootprintSourceLeftStackFromPayload
    (payload : List (Option Bool)) : List (Option Bool) :=
  (selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload
    payload).reverse

/-- Explicit right-end source tape for the generic footprint compactor. -/
def selectedSegmentLogicalTapeDecoderFootprintSourceRightEndTapeFromPayload
    (payload : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (selectedSegmentLogicalTapeDecoderFootprintSourceLeftStackFromPayload
      payload)
    [none]

/-- Left stack for the compacted payload target. -/
def selectedSegmentLogicalTapeDecoderFootprintTargetLeftStack
    (bits : Word Bool) : List (Option Bool) :=
  bits.reverse.map some

/-- Explicit right-edge target tape for the generic footprint compactor. -/
def selectedSegmentLogicalTapeDecoderFootprintTargetRightEdgeTape
    (bits : Word Bool) (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (selectedSegmentLogicalTapeDecoderFootprintTargetLeftStack bits)
    (none :: padding)

theorem selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload_eq_rightEndTape
    (payload : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
        payload =
      selectedSegmentLogicalTapeDecoderFootprintSourceRightEndTapeFromPayload
        payload := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload_left
    (payload : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
        payload).left =
      selectedSegmentLogicalTapeDecoderFootprintSourceLeftStackFromPayload
        payload := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload_head
    (payload : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
        payload).head = none := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload_right
    (payload : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
        payload).right = [] := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintSourceRightEndTape_cells
    (payload : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderFootprintSourceRightEndTapeFromPayload
          payload) =
      List.append
        (selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload
          payload)
        [none] := by
  simp [
    selectedSegmentLogicalTapeDecoderFootprintSourceRightEndTapeFromPayload,
    selectedSegmentLogicalTapeDecoderFootprintSourceLeftStackFromPayload,
    tapeAtCells, Tape.cells]

theorem selectedSegmentLogicalTapeDecoderFootprintSourceLeftStack_reverse
    (payload : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintSourceLeftStackFromPayload
        payload).reverse =
      selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload
        payload := by
  simp [selectedSegmentLogicalTapeDecoderFootprintSourceLeftStackFromPayload]

theorem selectedSegmentLogicalTapeDecoderFootprintSourceLeftStack_filterMap
    (payload : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintSourceLeftStackFromPayload
        payload).filterMap (fun cell => cell) =
      (payload.filterMap (fun cell => cell)).reverse := by
  rw [selectedSegmentLogicalTapeDecoderFootprintSourceLeftStackFromPayload]
  rw [Tape.filterMap_reverse]
  rw [selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload_filterMap]

theorem selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload_cells_via_rightEnd
    (payload : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
          payload) =
      Tape.cells
        (selectedSegmentLogicalTapeDecoderFootprintSourceRightEndTapeFromPayload
          payload) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload_eq_rightEndTape]

theorem selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload_eq_rightEdgeTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
        bits padding =
      selectedSegmentLogicalTapeDecoderFootprintTargetRightEdgeTape
        bits padding := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload_left
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
        bits padding).left =
      selectedSegmentLogicalTapeDecoderFootprintTargetLeftStack bits := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload_head
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
        bits padding).head = none := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload_right
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
        bits padding).right = padding := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintTargetRightEdgeTape_cells
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderFootprintTargetRightEdgeTape
          bits padding) =
      selectedSegmentLogicalTapeDecoderFootprintTargetCells
        bits padding := by
  simp [
    selectedSegmentLogicalTapeDecoderFootprintTargetRightEdgeTape,
    selectedSegmentLogicalTapeDecoderFootprintTargetLeftStack,
    selectedSegmentLogicalTapeDecoderFootprintTargetCells,
    tapeAtCells, Tape.cells, List.map_reverse]

theorem selectedSegmentLogicalTapeDecoderFootprintTargetLeftStack_reverse
    (bits : Word Bool) :
    (selectedSegmentLogicalTapeDecoderFootprintTargetLeftStack
        bits).reverse =
      bits.map some := by
  simp [selectedSegmentLogicalTapeDecoderFootprintTargetLeftStack,
    List.map_reverse]

theorem selectedSegmentLogicalTapeDecoderFootprintTargetLeftStack_filterMap
    (bits : Word Bool) :
    (selectedSegmentLogicalTapeDecoderFootprintTargetLeftStack
        bits).filterMap (fun cell => cell) =
      bits.reverse := by
  induction bits with
  | nil =>
      rfl
  | cons bit rest ih =>
      simp [selectedSegmentLogicalTapeDecoderFootprintTargetLeftStack,
        List.map_reverse, Function.comp_def]

theorem selectedSegmentLogicalTapeDecoderFootprintTargetTape_cells_via_rightEdge
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
          bits padding) =
      Tape.cells
        (selectedSegmentLogicalTapeDecoderFootprintTargetRightEdgeTape
          bits padding) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload_eq_rightEdgeTape]

/-- Source tape specialized to the canonical decoded payload family. -/
def selectedSegmentLogicalTapeDecoderFootprintSourceTape
    (bits : Word Bool) (padding : List (Option Bool)) : Tape Bool :=
  selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
    (selectedSegmentLogicalTapeDecoderPayloadCells bits padding)

/-- Source left stack specialized to the canonical decoded payload family. -/
def selectedSegmentLogicalTapeDecoderFootprintSourceLeftStack
    (bits : Word Bool) (padding : List (Option Bool)) :
    List (Option Bool) :=
  selectedSegmentLogicalTapeDecoderFootprintSourceLeftStackFromPayload
    (selectedSegmentLogicalTapeDecoderPayloadCells bits padding)

theorem selectedSegmentLogicalTapeDecoderFootprintSourceTape_eq
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintSourceTape
        bits padding =
      selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
        (selectedSegmentLogicalTapeDecoderPayloadCells bits padding) := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintSourceTape_left
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintSourceTape
        bits padding).left =
      selectedSegmentLogicalTapeDecoderFootprintSourceLeftStack
        bits padding := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintSourceTape_head
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintSourceTape
        bits padding).head = none := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintSourceTape_right
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintSourceTape
        bits padding).right = [] := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintSourceTape_cells
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderFootprintSourceTape
          bits padding) =
      List.append
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          bits padding)
        [none] := by
  rw [selectedSegmentLogicalTapeDecoderFootprintSourceTape]
  rw [selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload_cells_eq]
  rw [← selectedSegmentLogicalTapeDecoderFootprintLeftCells_eq_fromPayload]

theorem selectedSegmentLogicalTapeDecoderFootprintSourceTape_cells_filterMap
    (bits : Word Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderFootprintSourceTape
          bits padding)).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintSourceTape]
  rw [selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload_cells_filterMap]
  rw [selectedSegmentLogicalTapeDecoderPayloadCells_filterMap]

theorem selectedSegmentLogicalTapeDecoderFootprintSourceTape_normalizedOutput
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderFootprintSourceTape
          bits padding) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [Tape.normalizedOutput,
    selectedSegmentLogicalTapeDecoderFootprintSourceTape_cells_filterMap]

theorem selectedSegmentLogicalTapeDecoderFootprintTargetTape_normalizedOutput_via_endpoint
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
          bits padding) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  exact
    selectedSegmentLogicalTapeDecoderFootprintTargetFromPayload_normalizedOutput
      bits padding

theorem selectedSegmentLogicalTapeDecoderFootprintSourceTarget_normalizedOutput_eq
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderFootprintSourceTape
          bits padding) =
      Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
          bits padding) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintSourceTape_normalizedOutput,
    selectedSegmentLogicalTapeDecoderFootprintTargetTape_normalizedOutput_via_endpoint]

theorem selectedSegmentLogicalTapeDecoderFootprintSourceLeftStack_reverse_eq
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintSourceLeftStack
        bits padding).reverse =
      selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
        bits padding := by
  rw [selectedSegmentLogicalTapeDecoderFootprintSourceLeftStack]
  rw [selectedSegmentLogicalTapeDecoderFootprintSourceLeftStack_reverse]
  rw [← selectedSegmentLogicalTapeDecoderFootprintLeftCells_eq_fromPayload]

theorem selectedSegmentLogicalTapeDecoderFootprintSourceLeftStack_filterMap_eq
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintSourceLeftStack
        bits padding).filterMap (fun cell => cell) =
      (List.append bits
        (padding.filterMap (fun cell => cell))).reverse := by
  rw [selectedSegmentLogicalTapeDecoderFootprintSourceLeftStack]
  rw [selectedSegmentLogicalTapeDecoderFootprintSourceLeftStack_filterMap]
  rw [selectedSegmentLogicalTapeDecoderPayloadCells_filterMap]

theorem selectedSegmentLogicalTapeDecoderFootprintSourceTape_eq_rightEndCompactionSource
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintSourceTape
        bits padding =
      rightEndCompactionSourceTape
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          bits padding) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintSourceTape]
  exact
    (selectedSegmentLogicalTapeDecoderFootprintSourceTape_eq_fromPayload
      bits padding).symm

theorem selectedSegmentLogicalTapeDecoderFootprintTargetTape_eq_rightEdgeRewindSource
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
        bits padding =
      rightEdgeRewindSourceTape bits padding := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintSourceTape_nil_nil :
    selectedSegmentLogicalTapeDecoderFootprintSourceTape [] [] =
      selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
        [none, none] := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintSourceTape_nil_none
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintSourceTape
        [] (none :: padding) =
      selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
        (none :: none :: List.append padding [none]) := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintSourceTape_nil_some
    (padBit : Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintSourceTape
        [] (some padBit :: padding) =
      selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
        (none :: some padBit :: List.append padding [none]) := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintSourceTape_cons_nil
    (bit : Bool) (rest : Word Bool) :
    selectedSegmentLogicalTapeDecoderFootprintSourceTape
        (bit :: rest) [] =
      selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
        (some bit :: List.append (rest.map some) [none, none]) := by
  simp [selectedSegmentLogicalTapeDecoderFootprintSourceTape,
    selectedSegmentLogicalTapeDecoderPayloadCells_cons_nil]

theorem selectedSegmentLogicalTapeDecoderFootprintSourceTape_cons_none
    (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintSourceTape
        (bit :: rest) (none :: padding) =
      selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
        (some bit ::
          List.append (rest.map some)
            (none :: none :: List.append padding [none])) := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintSourceTape_cons_some
    (bit : Bool) (rest : Word Bool)
    (padBit : Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintSourceTape
        (bit :: rest) (some padBit :: padding) =
      selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
        (some bit ::
          List.append (rest.map some)
            (none :: some padBit :: List.append padding [none])) := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintTargetTape_nil_nil :
    selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
        [] [] =
      selectedSegmentLogicalTapeDecoderFootprintTargetRightEdgeTape
        [] [] := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintTargetTape_nil_none
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
        [] (none :: padding) =
      selectedSegmentLogicalTapeDecoderFootprintTargetRightEdgeTape
        [] (none :: padding) := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintTargetTape_nil_some
    (padBit : Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
        [] (some padBit :: padding) =
      selectedSegmentLogicalTapeDecoderFootprintTargetRightEdgeTape
        [] (some padBit :: padding) := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintTargetTape_cons_nil
    (bit : Bool) (rest : Word Bool) :
    selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
        (bit :: rest) [] =
      selectedSegmentLogicalTapeDecoderFootprintTargetRightEdgeTape
        (bit :: rest) [] := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintTargetTape_cons_none
    (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
        (bit :: rest) (none :: padding) =
      selectedSegmentLogicalTapeDecoderFootprintTargetRightEdgeTape
        (bit :: rest) (none :: padding) := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintTargetTape_cons_some
    (bit : Bool) (rest : Word Bool)
    (padBit : Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
        (bit :: rest) (some padBit :: padding) =
      selectedSegmentLogicalTapeDecoderFootprintTargetRightEdgeTape
        (bit :: rest) (some padBit :: padding) := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintSourceLeftStack_nil_nil :
    selectedSegmentLogicalTapeDecoderFootprintSourceLeftStack [] [] =
      selectedSegmentLogicalTapeDecoderFootprintSourceLeftStackFromPayload
        [none, none] := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintSourceLeftStack_nil_none
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintSourceLeftStack
        [] (none :: padding) =
      selectedSegmentLogicalTapeDecoderFootprintSourceLeftStackFromPayload
        (none :: none :: List.append padding [none]) := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintSourceLeftStack_nil_some
    (padBit : Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintSourceLeftStack
        [] (some padBit :: padding) =
      selectedSegmentLogicalTapeDecoderFootprintSourceLeftStackFromPayload
        (none :: some padBit :: List.append padding [none]) := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintSourceLeftStack_cons_nil
    (bit : Bool) (rest : Word Bool) :
    selectedSegmentLogicalTapeDecoderFootprintSourceLeftStack
        (bit :: rest) [] =
      selectedSegmentLogicalTapeDecoderFootprintSourceLeftStackFromPayload
        (some bit :: List.append (rest.map some) [none, none]) := by
  simp [selectedSegmentLogicalTapeDecoderFootprintSourceLeftStack,
    selectedSegmentLogicalTapeDecoderPayloadCells_cons_nil]

theorem selectedSegmentLogicalTapeDecoderFootprintSourceLeftStack_cons_none
    (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintSourceLeftStack
        (bit :: rest) (none :: padding) =
      selectedSegmentLogicalTapeDecoderFootprintSourceLeftStackFromPayload
        (some bit ::
          List.append (rest.map some)
            (none :: none :: List.append padding [none])) := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintSourceLeftStack_cons_some
    (bit : Bool) (rest : Word Bool)
    (padBit : Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintSourceLeftStack
        (bit :: rest) (some padBit :: padding) =
      selectedSegmentLogicalTapeDecoderFootprintSourceLeftStackFromPayload
        (some bit ::
          List.append (rest.map some)
            (none :: some padBit :: List.append padding [none])) := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintSourceBranch_normalizedOutputs
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderFootprintSourceTape
          bits padding) =
      Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
          bits padding) := by
  exact
    selectedSegmentLogicalTapeDecoderFootprintSourceTarget_normalizedOutput_eq
      bits padding

theorem selectedSegmentLogicalTapeDecoderFootprintSourceTarget_cells_filterMap_eq
    (bits : Word Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderFootprintSourceTape
          bits padding)).filterMap (fun cell => cell) =
      (Tape.cells
        (selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
          bits padding)).filterMap (fun cell => cell) := by
  rw [
    selectedSegmentLogicalTapeDecoderFootprintSourceTape_cells_filterMap,
    selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload_cells_filterMap]

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
