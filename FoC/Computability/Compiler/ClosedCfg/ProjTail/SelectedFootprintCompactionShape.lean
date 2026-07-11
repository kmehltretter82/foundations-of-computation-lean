import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge

set_option doc.verso true

/-!
# Selected logical-tape decoder footprint shape

This module isolates the pure source and target shapes behind selected
logical-tape decoder footprint compaction.  The finite-machine leaf is not
proved here; the point is to expose the branch-independent payload view that a
generic compactor should consume.
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

/-- Fixed blank prefix emitted before the selected decoder payload cells. -/
def selectedSegmentLogicalTapeDecoderGuardPrefixCells :
    List (Option Bool) :=
  List.append
    (selectedSegmentLogicalTapeDecoderCellCells (none : Option Bool))
    (List.append
      (selectedSegmentLogicalTapeDecoderCellCells (none : Option Bool))
      [none, none])

/--
Payload logical cells that should remain after footprint compaction.

The final trailing {lit}`none` is the right boundary consumed by the stateful
decoder.  The exact target tape omits it up to the ordinary right-edge tape
boundary.
-/
def selectedSegmentLogicalTapeDecoderPayloadCells
    (bits : Word Bool) (padding : List (Option Bool)) :
    List (Option Bool) :=
  List.append (bits.map some)
    (none :: List.append padding [none])

/-- The selected decoder footprint as fixed guard cells plus encoded payload. -/
def selectedSegmentLogicalTapeDecoderFootprintCellsFromPayload
    (payload : List (Option Bool)) : List (Option Bool) :=
  List.append selectedSegmentLogicalTapeDecoderGuardPrefixCells
    (payload.map selectedSegmentLogicalTapeDecoderCellCells).flatten

/-- Left cells for the right-end source shape of the generic footprint view. -/
def selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload
    (payload : List (Option Bool)) : List (Option Bool) :=
  none ::
    List.append
      (selectedSegmentLogicalTapeDecoderFootprintCellsFromPayload payload)
      [none]

/-- Right-end compaction source tape for the generic footprint view. -/
def selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
    (payload : List (Option Bool)) : Tape Bool :=
  rightEndCompactionSourceTape
    (selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload
      payload)

/-- Concrete exact target cells before placing the head at the separator. -/
def selectedSegmentLogicalTapeDecoderFootprintTargetCells
    (bits : Word Bool) (padding : List (Option Bool)) :
    List (Option Bool) :=
  List.append (bits.map some) (none :: padding)

/-- Exact target tape for the payload view. -/
def selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape Bool :=
  rightEdgeRewindSourceTape bits padding

theorem selectedSegmentLogicalTapeDecoderGuardPrefixCells_eq :
    selectedSegmentLogicalTapeDecoderGuardPrefixCells =
      List.append
        (selectedSegmentLogicalTapeDecoderCellCells (none : Option Bool))
        (List.append
          (selectedSegmentLogicalTapeDecoderCellCells
            (none : Option Bool))
          [none, none]) := by
  rfl

theorem selectedSegmentLogicalTapeDecoderGuardPrefixCells_cells :
    selectedSegmentLogicalTapeDecoderGuardPrefixCells =
      [none, none, none, none, none, none] := by
  rfl

theorem selectedSegmentLogicalTapeDecoderGuardPrefixCells_length :
    selectedSegmentLogicalTapeDecoderGuardPrefixCells.length = 6 := by
  rfl

theorem selectedSegmentLogicalTapeDecoderGuardPrefixCells_filterMap :
    selectedSegmentLogicalTapeDecoderGuardPrefixCells.filterMap
        (fun cell => cell) =
      [] := by
  rfl

theorem selectedSegmentLogicalTapeDecoderCellCells_length_shape
    (cell : Option Bool) :
    (selectedSegmentLogicalTapeDecoderCellCells cell).length = 2 := by
  cases cell with
  | none =>
      rfl
  | some bit =>
      cases bit <;> rfl

theorem selectedSegmentLogicalTapeDecoderCellCells_flatten_length_shape
    (cells : List (Option Bool)) :
    ((cells.map selectedSegmentLogicalTapeDecoderCellCells).flatten).length =
      2 * cells.length := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      simp [selectedSegmentLogicalTapeDecoderCellCells_length_shape, ih]
      lia

theorem selectedSegmentLogicalTapeDecoderPayloadCells_nil
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderPayloadCells [] padding =
      none :: List.append padding [none] := by
  rfl

theorem selectedSegmentLogicalTapeDecoderPayloadCells_cons
    (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderPayloadCells
        (bit :: rest) padding =
      some bit ::
        List.append (rest.map some)
          (none :: List.append padding [none]) := by
  rfl

theorem selectedSegmentLogicalTapeDecoderPayloadCells_nil_nil :
    selectedSegmentLogicalTapeDecoderPayloadCells [] [] =
      [none, none] := by
  rfl

theorem selectedSegmentLogicalTapeDecoderPayloadCells_nil_none
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderPayloadCells
        [] (none :: padding) =
      none :: none :: List.append padding [none] := by
  rfl

theorem selectedSegmentLogicalTapeDecoderPayloadCells_nil_some
    (padBit : Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderPayloadCells
        [] (some padBit :: padding) =
      none :: some padBit :: List.append padding [none] := by
  rfl

theorem selectedSegmentLogicalTapeDecoderPayloadCells_cons_nil
    (bit : Bool) (rest : Word Bool) :
    selectedSegmentLogicalTapeDecoderPayloadCells
        (bit :: rest) [] =
      some bit :: List.append (rest.map some) [none, none] := by
  simp [selectedSegmentLogicalTapeDecoderPayloadCells]

theorem selectedSegmentLogicalTapeDecoderPayloadCells_cons_none
    (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderPayloadCells
        (bit :: rest) (none :: padding) =
      some bit ::
        List.append (rest.map some)
          (none :: none :: List.append padding [none]) := by
  rfl

theorem selectedSegmentLogicalTapeDecoderPayloadCells_cons_some
    (bit : Bool) (rest : Word Bool)
    (padBit : Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderPayloadCells
        (bit :: rest) (some padBit :: padding) =
      some bit ::
        List.append (rest.map some)
          (none :: some padBit :: List.append padding [none]) := by
  rfl

theorem selectedSegmentLogicalTapeDecoderPayloadCells_filterMap
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderPayloadCells
        bits padding).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  simp [selectedSegmentLogicalTapeDecoderPayloadCells,
    List.filterMap_append, Function.comp_def]

theorem selectedSegmentLogicalTapeDecoderPayloadCells_length
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderPayloadCells
        bits padding).length =
      bits.length + padding.length + 2 := by
  simp [selectedSegmentLogicalTapeDecoderPayloadCells]
  lia

theorem selectedSegmentLogicalTapeDecoderPayloadCells_last_boundary
    (bits : Word Bool) (padding : List (Option Bool)) :
    exists pref : List (Option Bool),
      selectedSegmentLogicalTapeDecoderPayloadCells bits padding =
        List.append pref [none] := by
  refine
    ⟨List.append (bits.map some) (none :: padding), ?_⟩
  simp [selectedSegmentLogicalTapeDecoderPayloadCells, List.append_assoc]

theorem selectedSegmentLogicalTapeDecoderPayloadCells_targetCells_append_boundary
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderPayloadCells bits padding =
      List.append
        (selectedSegmentLogicalTapeDecoderFootprintTargetCells
          bits padding)
        [none] := by
  simp [selectedSegmentLogicalTapeDecoderPayloadCells,
    selectedSegmentLogicalTapeDecoderFootprintTargetCells,
    List.append_assoc]

theorem selectedSegmentLogicalTapeDecoderFootprintTargetCells_filterMap
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintTargetCells
        bits padding).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  simp [selectedSegmentLogicalTapeDecoderFootprintTargetCells,
    List.filterMap_append, Function.comp_def]

theorem selectedSegmentLogicalTapeDecoderFootprintTargetCells_length
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintTargetCells
        bits padding).length =
      bits.length + padding.length + 1 := by
  simp [selectedSegmentLogicalTapeDecoderFootprintTargetCells]
  lia

theorem selectedSegmentLogicalTapeDecoderFootprintTargetCells_nil
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintTargetCells [] padding =
      none :: padding := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintTargetCells_cons
    (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintTargetCells
        (bit :: rest) padding =
      some bit ::
        List.append (rest.map some) (none :: padding) := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintCellsFromPayload_filterMap
    (payload : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintCellsFromPayload
        payload).filterMap (fun cell => cell) =
      payload.filterMap (fun cell => cell) := by
  simpa [selectedSegmentLogicalTapeDecoderFootprintCellsFromPayload,
    selectedSegmentLogicalTapeDecoderGuardPrefixCells_filterMap,
    List.filterMap_append] using
    selectedSegmentLogicalTapeDecoderCellCells_flatten_filterMap payload

theorem selectedSegmentLogicalTapeDecoderFootprintCellsFromPayload_length
    (payload : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintCellsFromPayload
        payload).length =
      6 + 2 * payload.length := by
  rw [selectedSegmentLogicalTapeDecoderFootprintCellsFromPayload]
  rw [List.append_eq]
  rw [List.length_append]
  rw [selectedSegmentLogicalTapeDecoderGuardPrefixCells_length]
  rw [selectedSegmentLogicalTapeDecoderCellCells_flatten_length_shape]

theorem selectedSegmentLogicalTapeDecoderFootprintCellsFromPayload_nil :
    selectedSegmentLogicalTapeDecoderFootprintCellsFromPayload [] =
      selectedSegmentLogicalTapeDecoderGuardPrefixCells := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintCellsFromPayload_cons
    (cell : Option Bool) (payload : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintCellsFromPayload
        (cell :: payload) =
      List.append selectedSegmentLogicalTapeDecoderGuardPrefixCells
        (List.append
          (selectedSegmentLogicalTapeDecoderCellCells cell)
          (payload.map
            selectedSegmentLogicalTapeDecoderCellCells).flatten) := by
  simp [selectedSegmentLogicalTapeDecoderFootprintCellsFromPayload]

theorem selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload_filterMap
    (payload : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload
        payload).filterMap (fun cell => cell) =
      payload.filterMap (fun cell => cell) := by
  simp [selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload,
    selectedSegmentLogicalTapeDecoderFootprintCellsFromPayload_filterMap,
    List.filterMap_append]

theorem selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload_length
    (payload : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload
        payload).length =
      8 + 2 * payload.length := by
  simp [selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload,
    selectedSegmentLogicalTapeDecoderFootprintCellsFromPayload_length]
  lia

theorem selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload_eq
    (payload : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload
        payload =
      none ::
        List.append
          (List.append selectedSegmentLogicalTapeDecoderGuardPrefixCells
            (payload.map
              selectedSegmentLogicalTapeDecoderCellCells).flatten)
          [none] := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintCells_eq_fromPayload
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintCells
        bits padding =
      selectedSegmentLogicalTapeDecoderFootprintCellsFromPayload
        (selectedSegmentLogicalTapeDecoderPayloadCells bits padding) := by
  cases bits with
  | nil =>
      simp [selectedSegmentLogicalTapeDecoderDensifierFootprintCells,
        selectedSegmentLogicalTapeDecoderFootprintCellsFromPayload,
        selectedSegmentLogicalTapeDecoderGuardPrefixCells,
        selectedSegmentLogicalTapeDecoderPayloadCells,
        List.append_assoc]
  | cons bit rest =>
      simp [selectedSegmentLogicalTapeDecoderDensifierFootprintCells,
        selectedSegmentLogicalTapeDecoderFootprintCellsFromPayload,
        selectedSegmentLogicalTapeDecoderGuardPrefixCells,
        selectedSegmentLogicalTapeDecoderPayloadCells,
        List.append_assoc]

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintCells_length
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
      bits padding).length =
      10 + 2 * bits.length + 2 * padding.length := by
  rw [selectedSegmentLogicalTapeDecoderFootprintCells_eq_fromPayload,
    selectedSegmentLogicalTapeDecoderFootprintCellsFromPayload_length,
    selectedSegmentLogicalTapeDecoderPayloadCells_length]
  lia

theorem selectedSegmentLogicalTapeDecoderFootprintCells_eq_guardPrefix_payload
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintCells
        bits padding =
      List.append selectedSegmentLogicalTapeDecoderGuardPrefixCells
        ((selectedSegmentLogicalTapeDecoderPayloadCells
          bits padding).map
            selectedSegmentLogicalTapeDecoderCellCells).flatten := by
  rw [selectedSegmentLogicalTapeDecoderFootprintCells_eq_fromPayload]
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintLeftCells_eq_fromPayload
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
        bits padding =
      selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload
        (selectedSegmentLogicalTapeDecoderPayloadCells bits padding) := by
  simp [selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells,
    selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload,
    selectedSegmentLogicalTapeDecoderFootprintCells_eq_fromPayload]

theorem selectedSegmentLogicalTapeDecoderFootprintLeftCells_eq_guardPrefix_payload
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
        bits padding =
      none ::
        List.append
          (List.append selectedSegmentLogicalTapeDecoderGuardPrefixCells
            ((selectedSegmentLogicalTapeDecoderPayloadCells
              bits padding).map
                selectedSegmentLogicalTapeDecoderCellCells).flatten)
          [none] := by
  rw [selectedSegmentLogicalTapeDecoderFootprintLeftCells_eq_fromPayload]
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintLeftCells_filterMap_via_payload
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
        bits padding).filterMap (fun cell => cell) =
      (selectedSegmentLogicalTapeDecoderPayloadCells
        bits padding).filterMap (fun cell => cell) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintLeftCells_eq_fromPayload]
  exact
    selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload_filterMap
      (selectedSegmentLogicalTapeDecoderPayloadCells bits padding)

theorem selectedSegmentLogicalTapeDecoderFootprintLeftCells_filterMap_eq_target
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
        bits padding).filterMap (fun cell => cell) =
      (selectedSegmentLogicalTapeDecoderFootprintTargetCells
        bits padding).filterMap (fun cell => cell) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintLeftCells_filterMap_via_payload,
    selectedSegmentLogicalTapeDecoderPayloadCells_filterMap,
    selectedSegmentLogicalTapeDecoderFootprintTargetCells_filterMap]

theorem selectedSegmentLogicalTapeDecoderFootprintSourceTape_eq_fromPayload
    (bits : Word Bool) (padding : List (Option Bool)) :
    rightEndCompactionSourceTape
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          bits padding) =
      selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
        (selectedSegmentLogicalTapeDecoderPayloadCells bits padding) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintLeftCells_eq_fromPayload]
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload_cells
    (payload : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
          payload) =
      rightEndCompactionVisibleCells
        (selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload
          payload) := by
  exact rightEndCompactionSourceTape_cells
    (selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload
      payload)

theorem selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload_cells_eq
    (payload : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
          payload) =
      List.append
        (selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload
          payload)
        [none] := by
  rw [selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload_cells]
  rfl

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          bits padding) =
      none ::
        List.append
          (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
            bits padding)
          [none, none] := by
  rw [selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells]
  simp [selectedSegmentLogicalTapeDecoderDensifierSourceCells]

theorem selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload_cells_filterMap
    (payload : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
          payload)).filterMap (fun cell => cell) =
      payload.filterMap (fun cell => cell) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload_cells_eq]
  simp [selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload_filterMap,
    List.filterMap_append]

theorem selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload_eq
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
        bits padding =
      rightEdgeRewindSourceTape bits padding := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload_cells
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
          bits padding) =
      selectedSegmentLogicalTapeDecoderFootprintTargetCells
        bits padding := by
  rw [selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload]
  rw [rightEdgeRewindSourceTape_cells]
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload_cells_filterMap
    (bits : Word Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
          bits padding)).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload_cells]
  exact
    selectedSegmentLogicalTapeDecoderFootprintTargetCells_filterMap
      bits padding

theorem selectedSegmentLogicalTapeDecoderFootprintPayload_filterMap_eq_target
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderPayloadCells
        bits padding).filterMap (fun cell => cell) =
      (Tape.cells
        (selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
          bits padding)).filterMap (fun cell => cell) := by
  rw [selectedSegmentLogicalTapeDecoderPayloadCells_filterMap,
    selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload_cells_filterMap]

theorem selectedSegmentLogicalTapeDecoderFootprintSourceFromPayload_filterMap_eq_target
    (bits : Word Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
          (selectedSegmentLogicalTapeDecoderPayloadCells
            bits padding))).filterMap (fun cell => cell) =
      (Tape.cells
        (selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
          bits padding)).filterMap (fun cell => cell) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload_cells_filterMap,
    selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload_cells_filterMap,
    selectedSegmentLogicalTapeDecoderPayloadCells_filterMap]

theorem selectedSegmentLogicalTapeDecoderFootprintSourceFromPayload_normalizedOutput
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
          (selectedSegmentLogicalTapeDecoderPayloadCells
            bits padding)) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [Tape.normalizedOutput]
  rw [selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload_cells_filterMap]
  rw [selectedSegmentLogicalTapeDecoderPayloadCells_filterMap]

theorem selectedSegmentLogicalTapeDecoderFootprintTargetFromPayload_normalizedOutput
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
          bits padding) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload]
  exact rightEdgeRewindSourceTape_normalizedOutput bits padding

theorem selectedSegmentLogicalTapeDecoderFootprintSourceFromPayload_normalizedOutput_eq_target
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
          (selectedSegmentLogicalTapeDecoderPayloadCells
            bits padding)) =
      Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
          bits padding) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintSourceFromPayload_normalizedOutput,
    selectedSegmentLogicalTapeDecoderFootprintTargetFromPayload_normalizedOutput]

theorem selectedSegmentLogicalTapeDecoderFootprintLeftCells_nil_nil_eq_fromPayload :
    selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
        [] [] =
      selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload
        [none, none] := by
  simpa [selectedSegmentLogicalTapeDecoderPayloadCells_nil_nil] using
    selectedSegmentLogicalTapeDecoderFootprintLeftCells_eq_fromPayload
      [] []

theorem selectedSegmentLogicalTapeDecoderFootprintLeftCells_nil_none_eq_fromPayload
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
        [] (none :: padding) =
      selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload
        (none :: none :: List.append padding [none]) := by
  simpa [selectedSegmentLogicalTapeDecoderPayloadCells_nil_none] using
    selectedSegmentLogicalTapeDecoderFootprintLeftCells_eq_fromPayload
      [] (none :: padding)

theorem selectedSegmentLogicalTapeDecoderFootprintLeftCells_nil_some_eq_fromPayload
    (padBit : Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
        [] (some padBit :: padding) =
      selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload
        (none :: some padBit :: List.append padding [none]) := by
  simpa [selectedSegmentLogicalTapeDecoderPayloadCells_nil_some] using
    selectedSegmentLogicalTapeDecoderFootprintLeftCells_eq_fromPayload
      [] (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderFootprintLeftCells_cons_nil_eq_fromPayload
    (bit : Bool) (rest : Word Bool) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
        (bit :: rest) [] =
      selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload
        (some bit :: List.append (rest.map some) [none, none]) := by
  simpa [selectedSegmentLogicalTapeDecoderPayloadCells_cons_nil] using
    selectedSegmentLogicalTapeDecoderFootprintLeftCells_eq_fromPayload
      (bit :: rest) []

theorem selectedSegmentLogicalTapeDecoderFootprintLeftCells_cons_none_eq_fromPayload
    (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
        (bit :: rest) (none :: padding) =
      selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload
        (some bit ::
          List.append (rest.map some)
            (none :: none :: List.append padding [none])) := by
  simpa [selectedSegmentLogicalTapeDecoderPayloadCells_cons_none] using
    selectedSegmentLogicalTapeDecoderFootprintLeftCells_eq_fromPayload
      (bit :: rest) (none :: padding)

theorem selectedSegmentLogicalTapeDecoderFootprintLeftCells_cons_some_eq_fromPayload
    (bit : Bool) (rest : Word Bool)
    (padBit : Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
        (bit :: rest) (some padBit :: padding) =
      selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload
        (some bit ::
          List.append (rest.map some)
            (none :: some padBit :: List.append padding [none])) := by
  simpa [selectedSegmentLogicalTapeDecoderPayloadCells_cons_some] using
    selectedSegmentLogicalTapeDecoderFootprintLeftCells_eq_fromPayload
      (bit :: rest) (some padBit :: padding)

/--
Reusable interface for the finite compactor still missing below the selected
cleanup stack.  It states the exact selected decoder footprint in the generic
payload form and keeps the public target as a right-edge rewind source.
-/
def GuardedLogicalTapeDecoderFootprintCompactorSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    forall (bits : Word Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
          (selectedSegmentLogicalTapeDecoderPayloadCells bits padding))
        (selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
          bits padding)

def GuardedLogicalTapeDecoderFootprintCompactorConstruction :
    Prop :=
  exists compactor : MachineDescription,
    GuardedLogicalTapeDecoderFootprintCompactorSpec compactor

def GuardedLogicalTapeDecoderFootprintCompactorNilSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    compactor.HaltsFromTapeEquiv
      (selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
        (selectedSegmentLogicalTapeDecoderPayloadCells [] []))
      (selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
        [] []) ∧
    (forall padding : List (Option Bool),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
          (selectedSegmentLogicalTapeDecoderPayloadCells
            [] (none :: padding)))
        (selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
          [] (none :: padding))) ∧
    forall (padBit : Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
          (selectedSegmentLogicalTapeDecoderPayloadCells
            [] (some padBit :: padding)))
        (selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
          [] (some padBit :: padding))

def GuardedLogicalTapeDecoderFootprintCompactorConsSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    (forall (bit : Bool) (rest : Word Bool),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
          (selectedSegmentLogicalTapeDecoderPayloadCells
            (bit :: rest) []))
        (selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
          (bit :: rest) [])) ∧
    (forall (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
          (selectedSegmentLogicalTapeDecoderPayloadCells
            (bit :: rest) (none :: padding)))
        (selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
          (bit :: rest) (none :: padding))) ∧
    forall (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
          (selectedSegmentLogicalTapeDecoderPayloadCells
            (bit :: rest) (some padBit :: padding)))
        (selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
          (bit :: rest) (some padBit :: padding))

def GuardedLogicalTapeDecoderFootprintCompactorSplitSpec
    (compactor : MachineDescription) : Prop :=
  GuardedLogicalTapeDecoderFootprintCompactorNilSpec compactor ∧
    GuardedLogicalTapeDecoderFootprintCompactorConsSpec compactor

def GuardedLogicalTapeDecoderFootprintCompactorSplitConstruction :
    Prop :=
  exists compactor : MachineDescription,
    GuardedLogicalTapeDecoderFootprintCompactorSplitSpec compactor

theorem guardedLogicalTapeDecoderFootprintCompactorSplitSpec_of_spec
    {compactor : MachineDescription}
    (h :
      GuardedLogicalTapeDecoderFootprintCompactorSpec compactor) :
    GuardedLogicalTapeDecoderFootprintCompactorSplitSpec compactor := by
  rcases h with ⟨hready, hrun⟩
  refine ⟨?_, ?_⟩
  · refine ⟨hready, ?_, ?_, ?_⟩
    · exact hrun [] []
    · intro padding
      exact hrun [] (none :: padding)
    · intro padBit padding
      exact hrun [] (some padBit :: padding)
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro bit rest
      exact hrun (bit :: rest) []
    · intro bit rest padding
      exact hrun (bit :: rest) (none :: padding)
    · intro bit rest padBit padding
      exact hrun (bit :: rest) (some padBit :: padding)

theorem guardedLogicalTapeDecoderFootprintCompactorSplitConstruction_of_construction
    (h :
      GuardedLogicalTapeDecoderFootprintCompactorConstruction) :
    GuardedLogicalTapeDecoderFootprintCompactorSplitConstruction := by
  rcases h with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      guardedLogicalTapeDecoderFootprintCompactorSplitSpec_of_spec
        hspec⟩

theorem guardedLogicalTapeDecoderFootprintCompactorSpec_of_splitSpec
    {compactor : MachineDescription}
    (h :
      GuardedLogicalTapeDecoderFootprintCompactorSplitSpec compactor) :
    GuardedLogicalTapeDecoderFootprintCompactorSpec compactor := by
  rcases h with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  cases bits with
  | nil =>
      cases padding with
      | nil =>
          exact hnilNil
      | cons pad padding =>
          cases pad with
          | none =>
              exact hnilNone padding
          | some padBit =>
              exact hnilSome padBit padding
  | cons bit rest =>
      cases padding with
      | nil =>
          exact hconsNil bit rest
      | cons pad padding =>
          cases pad with
          | none =>
              exact hconsNone bit rest padding
          | some padBit =>
              exact hconsSome bit rest padBit padding

theorem guardedLogicalTapeDecoderFootprintCompactorConstruction_of_split
    (h :
      GuardedLogicalTapeDecoderFootprintCompactorSplitConstruction) :
    GuardedLogicalTapeDecoderFootprintCompactorConstruction := by
  rcases h with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      guardedLogicalTapeDecoderFootprintCompactorSpec_of_splitSpec
        hspec⟩

theorem guardedLogicalTapeDecoderFootprintCompactorSpec_iff_splitSpec
    (compactor : MachineDescription) :
    GuardedLogicalTapeDecoderFootprintCompactorSpec compactor ↔
      GuardedLogicalTapeDecoderFootprintCompactorSplitSpec
        compactor := by
  constructor
  · exact guardedLogicalTapeDecoderFootprintCompactorSplitSpec_of_spec
  · exact guardedLogicalTapeDecoderFootprintCompactorSpec_of_splitSpec

theorem guardedLogicalTapeDecoderFootprintCompactorConstruction_iff_splitConstruction :
    GuardedLogicalTapeDecoderFootprintCompactorConstruction ↔
      GuardedLogicalTapeDecoderFootprintCompactorSplitConstruction := by
  constructor
  · exact guardedLogicalTapeDecoderFootprintCompactorSplitConstruction_of_construction
  · exact guardedLogicalTapeDecoderFootprintCompactorConstruction_of_split

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
