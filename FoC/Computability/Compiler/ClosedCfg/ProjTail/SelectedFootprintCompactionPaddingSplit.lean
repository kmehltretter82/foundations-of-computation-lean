import FoC.Computability.Compiler.ClosedCfg.ProjTail.SelectedFootprintCompactionEndpoint

set_option doc.verso true

/-!
# Padding-aware selected footprint compaction split

The selected-footprint compactor is not a plain "delete every blank" right-end
compactor.  Its exact target keeps the padding tail to the right of the
separator blank.  This module names that split explicitly: selected bits,
separator, preserved padding, and the trailing source boundary are separate
pieces, with adapters back to the guarded compactor contract.
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

/-! ## Logical payload pieces -/

/-- Logical selected bits kept by the footprint compactor. -/
def selectedSegmentLogicalTapeDecoderFootprintPaddingSplitBitCells
    (bits : Word Bool) : List (Option Bool) :=
  bits.map some

/-- The separator between decoded selected bits and right-side padding. -/
def selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSeparatorCells :
    List (Option Bool) :=
  [none]

/-- Logical padding cells preserved to the right of the separator. -/
def selectedSegmentLogicalTapeDecoderFootprintPaddingSplitPaddingCells
    (padding : List (Option Bool)) : List (Option Bool) :=
  padding

/-- The trailing source boundary consumed by the compactor. -/
def selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTrailingBoundaryCells :
    List (Option Bool) :=
  [none]

/--
Logical payload cells that remain visible in the exact target.  This is the
selected bits, followed by the separator, followed by the preserved padding.
-/
def selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells
    (bits : Word Bool) (padding : List (Option Bool)) :
    List (Option Bool) :=
  List.append
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitBitCells bits)
    (List.append
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSeparatorCells
      (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitPaddingCells
        padding))

/--
Logical payload cells encoded in the source footprint.  This has the exact
target payload plus the trailing source boundary.
-/
def selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells
    (bits : Word Bool) (padding : List (Option Bool)) :
    List (Option Bool) :=
  List.append
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells
      bits padding)
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTrailingBoundaryCells

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitBitCells_nil :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitBitCells [] =
      [] := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitBitCells_cons
    (bit : Bool) (rest : Word Bool) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitBitCells
        (bit :: rest) =
      some bit ::
        selectedSegmentLogicalTapeDecoderFootprintPaddingSplitBitCells
          rest := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitBitCells_length
    (bits : Word Bool) :
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitBitCells
        bits).length =
      bits.length := by
  simp [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitBitCells]

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitBitCells_filterMap
    (bits : Word Bool) :
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitBitCells
        bits).filterMap (fun cell => cell) =
      bits := by
  simp [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitBitCells,
    Function.comp_def]

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSeparatorCells_eq :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSeparatorCells =
      [none] := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSeparatorCells_length :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSeparatorCells.length =
      1 := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSeparatorCells_filterMap :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSeparatorCells.filterMap
        (fun cell => cell) =
      [] := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitPaddingCells_eq
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitPaddingCells
        padding =
      padding := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitPaddingCells_nil :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitPaddingCells [] =
      [] := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitPaddingCells_cons
    (pad : Option Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitPaddingCells
        (pad :: padding) =
      pad ::
        selectedSegmentLogicalTapeDecoderFootprintPaddingSplitPaddingCells
          padding := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitPaddingCells_length
    (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitPaddingCells
        padding).length =
      padding.length := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitPaddingCells_filterMap
    (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitPaddingCells
        padding).filterMap (fun cell => cell) =
      padding.filterMap (fun cell => cell) := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTrailingBoundaryCells_eq :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTrailingBoundaryCells =
      [none] := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTrailingBoundaryCells_length :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTrailingBoundaryCells.length =
      1 := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTrailingBoundaryCells_filterMap :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTrailingBoundaryCells.filterMap
        (fun cell => cell) =
      [] := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells_eq
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells
        bits padding =
      selectedSegmentLogicalTapeDecoderFootprintTargetCells
        bits padding := by
  simp [
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitBitCells,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSeparatorCells,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitPaddingCells,
    selectedSegmentLogicalTapeDecoderFootprintTargetCells]

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells_eq
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells
        bits padding =
      selectedSegmentLogicalTapeDecoderPayloadCells
        bits padding := by
  simp [
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells_eq,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTrailingBoundaryCells,
    selectedSegmentLogicalTapeDecoderPayloadCells_targetCells_append_boundary]

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells_eq_target_append_boundary
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells
        bits padding =
      List.append
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells
          bits padding)
        [none] := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells_nil
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells
        [] padding =
      none :: padding := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells_eq]
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells_cons
    (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells
        (bit :: rest) padding =
      some bit ::
        List.append (rest.map some) (none :: padding) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells_eq]
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells_nil_nil :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells
        [] [] =
      [none] := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells_nil_none
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells
        [] (none :: padding) =
      none :: none :: padding := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells_nil_some
    (padBit : Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells
        [] (some padBit :: padding) =
      none :: some padBit :: padding := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells_cons_nil
    (bit : Bool) (rest : Word Bool) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells
        (bit :: rest) [] =
      some bit :: List.append (rest.map some) [none] := by
  simp [
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells_eq,
    selectedSegmentLogicalTapeDecoderFootprintTargetCells]

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells_cons_none
    (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells
        (bit :: rest) (none :: padding) =
      some bit ::
        List.append (rest.map some) (none :: none :: padding) := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells_cons_some
    (bit : Bool) (rest : Word Bool)
    (padBit : Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells
        (bit :: rest) (some padBit :: padding) =
      some bit ::
        List.append (rest.map some) (none :: some padBit :: padding) := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells_nil_nil :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells
        [] [] =
      [none, none] := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells_eq]
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells_nil_none
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells
        [] (none :: padding) =
      none :: none :: List.append padding [none] := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells_eq]
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells_nil_some
    (padBit : Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells
        [] (some padBit :: padding) =
      none :: some padBit :: List.append padding [none] := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells_eq]
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells_cons_nil
    (bit : Bool) (rest : Word Bool) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells
        (bit :: rest) [] =
      some bit :: List.append (rest.map some) [none, none] := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells_eq]
  simp [selectedSegmentLogicalTapeDecoderPayloadCells]

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells_cons_none
    (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells
        (bit :: rest) (none :: padding) =
      some bit ::
        List.append (rest.map some)
          (none :: none :: List.append padding [none]) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells_eq]
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells_cons_some
    (bit : Bool) (rest : Word Bool)
    (padBit : Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells
        (bit :: rest) (some padBit :: padding) =
      some bit ::
        List.append (rest.map some)
          (none :: some padBit :: List.append padding [none]) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells_eq]
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells_filterMap
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells
        bits padding).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells_eq]
  exact
    selectedSegmentLogicalTapeDecoderFootprintTargetCells_filterMap
      bits padding

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells_filterMap
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells
        bits padding).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells_eq]
  exact
    selectedSegmentLogicalTapeDecoderPayloadCells_filterMap bits padding

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells_length
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells
        bits padding).length =
      bits.length + padding.length + 1 := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells_eq]
  exact
    selectedSegmentLogicalTapeDecoderFootprintTargetCells_length
      bits padding

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells_length
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells
        bits padding).length =
      bits.length + padding.length + 2 := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells_eq]
  exact
    selectedSegmentLogicalTapeDecoderPayloadCells_length bits padding

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayload_filterMap_eq_target
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells
        bits padding).filterMap (fun cell => cell) =
      (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells
        bits padding).filterMap (fun cell => cell) := by
  rw [
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells_filterMap,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells_filterMap]

/-! ## Encoded footprint pieces -/

/-- Encoded selected-bit logical cells. -/
def selectedSegmentLogicalTapeDecoderFootprintPaddingSplitEncodedBitCells
    (bits : Word Bool) : List (Option Bool) :=
  ((selectedSegmentLogicalTapeDecoderFootprintPaddingSplitBitCells
    bits).map selectedSegmentLogicalTapeDecoderCellCells).flatten

/-- Encoded separator logical cell. -/
def selectedSegmentLogicalTapeDecoderFootprintPaddingSplitEncodedSeparatorCells :
    List (Option Bool) :=
  (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSeparatorCells.map
    selectedSegmentLogicalTapeDecoderCellCells).flatten

/-- Encoded preserved-padding logical cells. -/
def selectedSegmentLogicalTapeDecoderFootprintPaddingSplitEncodedPaddingCells
    (padding : List (Option Bool)) : List (Option Bool) :=
  ((selectedSegmentLogicalTapeDecoderFootprintPaddingSplitPaddingCells
    padding).map selectedSegmentLogicalTapeDecoderCellCells).flatten

/-- Encoded trailing source boundary logical cell. -/
def selectedSegmentLogicalTapeDecoderFootprintPaddingSplitEncodedTrailingBoundaryCells :
    List (Option Bool) :=
  (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTrailingBoundaryCells.map
    selectedSegmentLogicalTapeDecoderCellCells).flatten

/-- Encoded target payload: selected bits, separator, and preserved padding. -/
def selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetEncodedCells
    (bits : Word Bool) (padding : List (Option Bool)) :
    List (Option Bool) :=
  List.append
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitEncodedBitCells
      bits)
    (List.append
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitEncodedSeparatorCells
      (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitEncodedPaddingCells
        padding))

/--
Encoded source payload: target encoded payload plus the trailing source
boundary.
-/
def selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceEncodedCells
    (bits : Word Bool) (padding : List (Option Bool)) :
    List (Option Bool) :=
  List.append
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetEncodedCells
      bits padding)
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitEncodedTrailingBoundaryCells

/-- Full encoded footprint cells after the fixed guard prefix. -/
def selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCells
    (bits : Word Bool) (padding : List (Option Bool)) :
    List (Option Bool) :=
  List.append selectedSegmentLogicalTapeDecoderGuardPrefixCells
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceEncodedCells
      bits padding)

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitEncodedSeparatorCells_eq :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitEncodedSeparatorCells =
      selectedSegmentLogicalTapeDecoderCellCells (none : Option Bool) := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitEncodedTrailingBoundaryCells_eq :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitEncodedTrailingBoundaryCells =
      selectedSegmentLogicalTapeDecoderCellCells (none : Option Bool) := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitEncodedBitCells_length
    (bits : Word Bool) :
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitEncodedBitCells
        bits).length =
      2 * bits.length := by
  simpa [
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitEncodedBitCells,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitBitCells] using
    selectedSegmentLogicalTapeDecoderCellCells_flatten_length_shape
      (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitBitCells
        bits)

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitEncodedPaddingCells_length
    (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitEncodedPaddingCells
        padding).length =
      2 * padding.length := by
  simpa [
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitEncodedPaddingCells,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitPaddingCells] using
    selectedSegmentLogicalTapeDecoderCellCells_flatten_length_shape
      padding

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitEncodedSeparatorCells_length :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitEncodedSeparatorCells.length =
      2 := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitEncodedTrailingBoundaryCells_length :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitEncodedTrailingBoundaryCells.length =
      2 := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetEncodedCells_eq_map_target
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetEncodedCells
        bits padding =
      ((selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells
        bits padding).map selectedSegmentLogicalTapeDecoderCellCells).flatten := by
  simp [
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetEncodedCells,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitEncodedBitCells,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitEncodedSeparatorCells,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitEncodedPaddingCells,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitBitCells,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSeparatorCells,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitPaddingCells,
    List.map_append, List.flatten_append]

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceEncodedCells_eq_map_source
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceEncodedCells
        bits padding =
      ((selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells
        bits padding).map selectedSegmentLogicalTapeDecoderCellCells).flatten := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells_eq_target_append_boundary]
  simp [
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceEncodedCells,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetEncodedCells_eq_map_target,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitEncodedTrailingBoundaryCells,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTrailingBoundaryCells,
    List.map_append, List.flatten_append]

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetEncodedCells_length
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetEncodedCells
        bits padding).length =
      2 * (bits.length + padding.length + 1) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetEncodedCells_eq_map_target]
  rw [selectedSegmentLogicalTapeDecoderCellCells_flatten_length_shape]
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells_length]

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceEncodedCells_length
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceEncodedCells
        bits padding).length =
      2 * (bits.length + padding.length + 2) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceEncodedCells_eq_map_source]
  rw [selectedSegmentLogicalTapeDecoderCellCells_flatten_length_shape]
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells_length]

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCells_eq_footprintCells
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCells
        bits padding =
      selectedSegmentLogicalTapeDecoderDensifierFootprintCells
        bits padding := by
  rw [selectedSegmentLogicalTapeDecoderFootprintCells_eq_guardPrefix_payload]
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCells]
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceEncodedCells_eq_map_source]
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells_eq]

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCells_filterMap
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCells
        bits padding).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCells_eq_footprintCells]
  rw [selectedSegmentLogicalTapeDecoderFootprintCells_eq_fromPayload]
  rw [selectedSegmentLogicalTapeDecoderFootprintCellsFromPayload_filterMap]
  rw [selectedSegmentLogicalTapeDecoderPayloadCells_filterMap]

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCells_length
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCells
        bits padding).length =
      10 + 2 * bits.length + 2 * padding.length := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCells_eq_footprintCells]
  rw [selectedSegmentLogicalTapeDecoderFootprintCells_eq_fromPayload]
  rw [selectedSegmentLogicalTapeDecoderFootprintCellsFromPayload_length]
  rw [selectedSegmentLogicalTapeDecoderPayloadCells_length]
  lia

/-! ## Source and target tapes through the padding split -/

/-- Source left cells in the padding-aware split. -/
def selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceLeftCells
    (bits : Word Bool) (padding : List (Option Bool)) :
    List (Option Bool) :=
  none ::
    List.append
      (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCells
        bits padding)
      [none]

/-- Right-end source tape in the padding-aware split. -/
def selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
    (bits : Word Bool) (padding : List (Option Bool)) : Tape Bool :=
  rightEndCompactionSourceTape
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceLeftCells
      bits padding)

/-- Exact target tape in the padding-aware split. -/
def selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
    (bits : Word Bool) (padding : List (Option Bool)) : Tape Bool :=
  rightEdgeRewindSourceTape bits padding

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceLeftCells_eq
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceLeftCells
        bits padding =
      selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
        bits padding := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceLeftCells]
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCells_eq_footprintCells]
  rw [selectedSegmentLogicalTapeDecoderFootprintLeftCells_eq_fromPayload]
  rw [selectedSegmentLogicalTapeDecoderFootprintCells_eq_fromPayload]
  rw [selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload_eq]
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape_eq_sourceTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
        bits padding =
      selectedSegmentLogicalTapeDecoderFootprintSourceTape
        bits padding := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape]
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceLeftCells_eq]
  rw [selectedSegmentLogicalTapeDecoderFootprintSourceTape_eq_rightEndCompactionSource]

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape_eq_fromPayload
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
        bits padding =
      selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
        (selectedSegmentLogicalTapeDecoderPayloadCells bits padding) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape_eq_sourceTape]
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape_eq_fromPayload
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
        bits padding =
      selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
        bits padding := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape_eq_rightEdgeRewind
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
        bits padding =
      rightEdgeRewindSourceTape bits padding := by
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape_cells
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
          bits padding) =
      List.append
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceLeftCells
          bits padding)
        [none] := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape]
  exact rightEndCompactionSourceTape_cells
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceLeftCells
      bits padding)

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape_cells
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
          bits padding) =
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells
        bits padding := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape]
  rw [rightEdgeRewindSourceTape_cells]
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells_eq]
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape_cells_filterMap
    (bits : Word Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
          bits padding)).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape_eq_sourceTape]
  exact
    selectedSegmentLogicalTapeDecoderFootprintSourceTape_cells_filterMap
      bits padding

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape_cells_filterMap
    (bits : Word Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
          bits padding)).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape_cells]
  exact
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells_filterMap
      bits padding

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTarget_cells_filterMap_eq
    (bits : Word Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
          bits padding)).filterMap (fun cell => cell) =
      (Tape.cells
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
          bits padding)).filterMap (fun cell => cell) := by
  rw [
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape_cells_filterMap,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape_cells_filterMap]

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape_normalizedOutput
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
          bits padding) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [Tape.normalizedOutput]
  exact
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape_cells_filterMap
      bits padding

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape_normalizedOutput
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
          bits padding) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [Tape.normalizedOutput]
  exact
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape_cells_filterMap
      bits padding

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTarget_normalizedOutput_eq
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
          bits padding) =
      Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
          bits padding) := by
  rw [
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape_normalizedOutput,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape_normalizedOutput]

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape_nil_nil :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
        [] [] =
      selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
        [none, none] := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape_eq_fromPayload]
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape_nil_none
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
        [] (none :: padding) =
      selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
        (none :: none :: List.append padding [none]) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape_eq_fromPayload]
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape_nil_some
    (padBit : Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
        [] (some padBit :: padding) =
      selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
        (none :: some padBit :: List.append padding [none]) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape_eq_fromPayload]
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape_cons_nil
    (bit : Bool) (rest : Word Bool) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
        (bit :: rest) [] =
      selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
        (some bit :: List.append (rest.map some) [none, none]) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape_eq_fromPayload]
  simp [selectedSegmentLogicalTapeDecoderPayloadCells]

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape_cons_none
    (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
        (bit :: rest) (none :: padding) =
      selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
        (some bit ::
          List.append (rest.map some)
            (none :: none :: List.append padding [none])) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape_eq_fromPayload]
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape_cons_some
    (bit : Bool) (rest : Word Bool)
    (padBit : Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
        (bit :: rest) (some padBit :: padding) =
      selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
        (some bit ::
          List.append (rest.map some)
            (none :: some padBit :: List.append padding [none])) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape_eq_fromPayload]
  rfl

/-! ## Padding-split compactor contracts -/

/--
Same machine obligation as the guarded footprint compactor, but stated through
the explicit padding-aware source and target tapes above.
-/
def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    forall (bits : Word Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
          bits padding)
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
          bits padding)

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorConstruction :
    Prop :=
  exists compactor : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSpec
      compactor

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorNilSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    compactor.HaltsFromTapeEquiv
      (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
        [] [])
      (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
        [] []) ∧
    (forall padding : List (Option Bool),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
          [] (none :: padding))
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
          [] (none :: padding))) ∧
    forall (padBit : Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
          [] (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
          [] (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorConsSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    (forall (bit : Bool) (rest : Word Bool),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
          (bit :: rest) [])
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
          (bit :: rest) [])) ∧
    (forall (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
          (bit :: rest) (none :: padding))
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
          (bit :: rest) (none :: padding))) ∧
    forall (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
          (bit :: rest) (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
          (bit :: rest) (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitSpec
    (compactor : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorNilSpec
      compactor ∧
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorConsSpec
      compactor

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitConstruction :
    Prop :=
  exists compactor : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitSpec
      compactor

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSpec_of_guardedSpec
    {compactor : MachineDescription}
    (h :
      GuardedLogicalTapeDecoderFootprintCompactorSpec compactor) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSpec
      compactor := by
  rcases h with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  rw [
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape_eq_fromPayload,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape_eq_fromPayload]
  exact hrun bits padding

theorem guardedLogicalTapeDecoderFootprintCompactorSpec_of_paddingSplitSpec
    {compactor : MachineDescription}
    (h :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSpec
        compactor) :
    GuardedLogicalTapeDecoderFootprintCompactorSpec compactor := by
  rcases h with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  rw [← selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape_eq_fromPayload,
    ← selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape_eq_fromPayload]
  exact hrun bits padding

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorConstruction_of_guarded
    (h :
      GuardedLogicalTapeDecoderFootprintCompactorConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorConstruction := by
  rcases h with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSpec_of_guardedSpec
        hspec⟩

theorem guardedLogicalTapeDecoderFootprintCompactorConstruction_of_paddingSplit
    (h :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorConstruction) :
    GuardedLogicalTapeDecoderFootprintCompactorConstruction := by
  rcases h with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      guardedLogicalTapeDecoderFootprintCompactorSpec_of_paddingSplitSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSpec_iff_guardedSpec
    (compactor : MachineDescription) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSpec
        compactor ↔
      GuardedLogicalTapeDecoderFootprintCompactorSpec compactor := by
  constructor
  · exact guardedLogicalTapeDecoderFootprintCompactorSpec_of_paddingSplitSpec
  · exact selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSpec_of_guardedSpec

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorConstruction_iff_guardedConstruction :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorConstruction ↔
      GuardedLogicalTapeDecoderFootprintCompactorConstruction := by
  constructor
  · exact guardedLogicalTapeDecoderFootprintCompactorConstruction_of_paddingSplit
  · exact selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorConstruction_of_guarded

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitSpec_of_spec
    {compactor : MachineDescription}
    (h :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSpec
        compactor) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitSpec
      compactor := by
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

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSpec_of_splitSpec
    {compactor : MachineDescription}
    (h :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitSpec
        compactor) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSpec
      compactor := by
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

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitConstruction_of_construction
    (h :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitConstruction := by
  rcases h with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitSpec_of_spec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorConstruction_of_split
    (h :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorConstruction := by
  rcases h with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSpec_of_splitSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSpec_iff_splitSpec
    (compactor : MachineDescription) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSpec
        compactor ↔
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitSpec
        compactor := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitSpec_of_spec
  · exact
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSpec_of_splitSpec

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorConstruction_iff_splitConstruction :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorConstruction ↔
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitConstruction := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitConstruction_of_construction
  · exact
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorConstruction_of_split

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
