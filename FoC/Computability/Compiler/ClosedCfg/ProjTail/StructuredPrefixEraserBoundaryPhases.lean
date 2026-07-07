import FoC.Computability.Compiler.ClosedCfg.ProjTail.StructuredPrefixEraserEndpoint

set_option doc.verso true

/-!
# Boundary phases for the guarded two-tape structured-prefix eraser

The structured-prefix eraser endpoint view exposes the right-edge source and
the two field-local boundary eraser sources.  This module factors the next
bottom-up proof obligations into explicit phase contracts:

* the existing left-boundary eraser deletes the second guarded field;
* the same finite machine deletes the first guarded field;
* the remaining gaps are positioning and compaction bridges between endpoints.

No new machine assumption is introduced here.  The exact boundary eraser
phases are proved from the existing left-boundary eraser description; the
positioning contracts are named so later composition work has a precise target.
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

/-! ## Field and footprint cell views -/

/-- Logical bits of the first guarded structured-tape field. -/
def guardedTwoTapeStructuredPrefixFirstFieldBits
    (T0 : Tape Bool) : Word Bool :=
  logicalTapeBits (guardLogicalTape T0)

/-- Logical bits of the second guarded structured-tape field. -/
def guardedTwoTapeStructuredPrefixSecondFieldBits
    (T1 : Tape Bool) : Word Bool :=
  logicalTapeBits (guardLogicalTape T1)

/-- Encoded cells of the first guarded structured-tape field. -/
def guardedTwoTapeStructuredPrefixFirstFieldEncodedCells
    (T0 : Tape Bool) : List (Option Bool) :=
  (guardedTwoTapeStructuredPrefixFirstFieldBits T0).map some

/-- Encoded cells of the second guarded structured-tape field. -/
def guardedTwoTapeStructuredPrefixSecondFieldEncodedCells
    (T1 : Tape Bool) : List (Option Bool) :=
  (guardedTwoTapeStructuredPrefixSecondFieldBits T1).map some

/-- Blank cells left after erasing the first guarded field. -/
def guardedTwoTapeStructuredPrefixFirstFieldErasedCells
    (T0 : Tape Bool) : List (Option Bool) :=
  List.replicate
    (guardedTwoTapeStructuredPrefixFirstFieldBits T0).length
    (none : Option Bool)

/-- Blank cells left after erasing the second guarded field. -/
def guardedTwoTapeStructuredPrefixSecondFieldErasedCells
    (T1 : Tape Bool) : List (Option Bool) :=
  List.replicate
    (guardedTwoTapeStructuredPrefixSecondFieldBits T1).length
    (none : Option Bool)

/--
The decoder footprint tail following the two structured fields in the source.
It starts with the separator immediately before the selected decoder footprint.
-/
def guardedTwoTapeStructuredPrefixFootprintVisibleTail
    (bits : Word Bool) (padding : List (Option Bool)) :
    List (Option Bool) :=
  none ::
    List.append
      (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
        bits padding)
      [none, none]

/-- Visible cells before any field erasure. -/
def guardedTwoTapeStructuredPrefixBoundarySourceCells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) : List (Option Bool) :=
  none ::
    List.append
      (guardedTwoTapeStructuredPrefixFirstFieldEncodedCells T0)
      (none ::
        List.append
          (guardedTwoTapeStructuredPrefixSecondFieldEncodedCells T1)
          (guardedTwoTapeStructuredPrefixFootprintVisibleTail
            bits padding))

/-- Visible cells after the second guarded field has been erased. -/
def guardedTwoTapeStructuredPrefixAfterSecondBoundaryCells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) : List (Option Bool) :=
  none ::
    List.append
      (guardedTwoTapeStructuredPrefixFirstFieldEncodedCells T0)
      (none ::
        List.append
          (guardedTwoTapeStructuredPrefixSecondFieldErasedCells T1)
          (guardedTwoTapeStructuredPrefixFootprintVisibleTail
            bits padding))

/-- Visible cells after both guarded fields have been erased. -/
def guardedTwoTapeStructuredPrefixAfterFirstBoundaryCells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) : List (Option Bool) :=
  none ::
    List.append
      (guardedTwoTapeStructuredPrefixFirstFieldErasedCells T0)
      (none ::
        List.append
          (guardedTwoTapeStructuredPrefixSecondFieldErasedCells T1)
          (guardedTwoTapeStructuredPrefixFootprintVisibleTail
            bits padding))

theorem guardedTwoTapeStructuredPrefixFirstFieldBits_eq
    (T0 : Tape Bool) :
    guardedTwoTapeStructuredPrefixFirstFieldBits T0 =
      logicalTapeBits (guardLogicalTape T0) := by
  rfl

theorem guardedTwoTapeStructuredPrefixSecondFieldBits_eq
    (T1 : Tape Bool) :
    guardedTwoTapeStructuredPrefixSecondFieldBits T1 =
      logicalTapeBits (guardLogicalTape T1) := by
  rfl

theorem guardedTwoTapeStructuredPrefixFirstFieldEncodedCells_eq
    (T0 : Tape Bool) :
    guardedTwoTapeStructuredPrefixFirstFieldEncodedCells T0 =
      (logicalTapeBits (guardLogicalTape T0)).map some := by
  rfl

theorem guardedTwoTapeStructuredPrefixSecondFieldEncodedCells_eq
    (T1 : Tape Bool) :
    guardedTwoTapeStructuredPrefixSecondFieldEncodedCells T1 =
      (logicalTapeBits (guardLogicalTape T1)).map some := by
  rfl

theorem logicalTapeBits_guardLogicalTape_length_boundaryPhase
    (T : Tape Bool) :
    (logicalTapeBits (guardLogicalTape T)).length =
      2 * T.left.length + 2 * T.right.length + 8 := by
  rw [logicalTapeBits_length_guardedShape]
  simp [guardLogicalTape]
  lia

theorem guardedTwoTapeStructuredPrefixFirstFieldBits_length_shape
    (T0 : Tape Bool) :
    (guardedTwoTapeStructuredPrefixFirstFieldBits T0).length =
      2 * T0.left.length + 2 * T0.right.length + 8 := by
  rw [guardedTwoTapeStructuredPrefixFirstFieldBits]
  rw [logicalTapeBits_length_guardedShape]
  simp [guardLogicalTape]
  lia

theorem guardedTwoTapeStructuredPrefixSecondFieldBits_length_shape
    (T1 : Tape Bool) :
    (guardedTwoTapeStructuredPrefixSecondFieldBits T1).length =
      2 * T1.left.length + 2 * T1.right.length + 8 := by
  rw [guardedTwoTapeStructuredPrefixSecondFieldBits]
  rw [logicalTapeBits_length_guardedShape]
  simp [guardLogicalTape]
  lia

theorem guardedTwoTapeStructuredPrefixFirstFieldEncodedCells_length
    (T0 : Tape Bool) :
    (guardedTwoTapeStructuredPrefixFirstFieldEncodedCells T0).length =
      (logicalTapeBits (guardLogicalTape T0)).length := by
  simp [guardedTwoTapeStructuredPrefixFirstFieldEncodedCells,
    guardedTwoTapeStructuredPrefixFirstFieldBits]

theorem guardedTwoTapeStructuredPrefixSecondFieldEncodedCells_length
    (T1 : Tape Bool) :
    (guardedTwoTapeStructuredPrefixSecondFieldEncodedCells T1).length =
      (logicalTapeBits (guardLogicalTape T1)).length := by
  simp [guardedTwoTapeStructuredPrefixSecondFieldEncodedCells,
    guardedTwoTapeStructuredPrefixSecondFieldBits]

theorem guardedTwoTapeStructuredPrefixFirstFieldErasedCells_length
    (T0 : Tape Bool) :
    (guardedTwoTapeStructuredPrefixFirstFieldErasedCells T0).length =
      (logicalTapeBits (guardLogicalTape T0)).length := by
  simp [guardedTwoTapeStructuredPrefixFirstFieldErasedCells,
    guardedTwoTapeStructuredPrefixFirstFieldBits]

theorem guardedTwoTapeStructuredPrefixSecondFieldErasedCells_length
    (T1 : Tape Bool) :
    (guardedTwoTapeStructuredPrefixSecondFieldErasedCells T1).length =
      (logicalTapeBits (guardLogicalTape T1)).length := by
  simp [guardedTwoTapeStructuredPrefixSecondFieldErasedCells,
    guardedTwoTapeStructuredPrefixSecondFieldBits]

theorem guardedTwoTapeStructuredPrefixFirstFieldEncodedCells_filterMap
    (T0 : Tape Bool) :
    (guardedTwoTapeStructuredPrefixFirstFieldEncodedCells T0).filterMap
        (fun cell => cell) =
      logicalTapeBits (guardLogicalTape T0) := by
  simp [guardedTwoTapeStructuredPrefixFirstFieldEncodedCells,
    guardedTwoTapeStructuredPrefixFirstFieldBits,
    Function.comp_def]

theorem guardedTwoTapeStructuredPrefixSecondFieldEncodedCells_filterMap
    (T1 : Tape Bool) :
    (guardedTwoTapeStructuredPrefixSecondFieldEncodedCells T1).filterMap
        (fun cell => cell) =
      logicalTapeBits (guardLogicalTape T1) := by
  simp [guardedTwoTapeStructuredPrefixSecondFieldEncodedCells,
    guardedTwoTapeStructuredPrefixSecondFieldBits,
    Function.comp_def]

theorem guardedTwoTapeStructuredPrefixFirstFieldErasedCells_filterMap
    (T0 : Tape Bool) :
    (guardedTwoTapeStructuredPrefixFirstFieldErasedCells T0).filterMap
        (fun cell => cell) =
      [] := by
  simp [guardedTwoTapeStructuredPrefixFirstFieldErasedCells]

theorem guardedTwoTapeStructuredPrefixSecondFieldErasedCells_filterMap
    (T1 : Tape Bool) :
    (guardedTwoTapeStructuredPrefixSecondFieldErasedCells T1).filterMap
        (fun cell => cell) =
      [] := by
  simp [guardedTwoTapeStructuredPrefixSecondFieldErasedCells]

theorem guardedTwoTapeStructuredPrefixFootprintVisibleTail_eq
    (bits : Word Bool) (padding : List (Option Bool)) :
    guardedTwoTapeStructuredPrefixFootprintVisibleTail bits padding =
      none ::
        List.append
          (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
            bits padding)
          [none, none] := by
  rfl

theorem guardedTwoTapeStructuredPrefixFootprintVisibleTail_filterMap
    (bits : Word Bool) (padding : List (Option Bool)) :
    (guardedTwoTapeStructuredPrefixFootprintVisibleTail
        bits padding).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  simp [guardedTwoTapeStructuredPrefixFootprintVisibleTail,
    selectedSegmentLogicalTapeDecoderDensifierFootprintCells_filterMap,
    List.filterMap_append]

theorem guardedTwoTapeStructuredPrefixFootprintVisibleTail_length
    (bits : Word Bool) (padding : List (Option Bool)) :
    (guardedTwoTapeStructuredPrefixFootprintVisibleTail
        bits padding).length =
      13 + 2 * bits.length + 2 * padding.length := by
  have hfoot :
      (selectedSegmentLogicalTapeDecoderFootprintCellsFromPayload
          (selectedSegmentLogicalTapeDecoderPayloadCells
            bits padding)).length =
        6 + 2 *
          (selectedSegmentLogicalTapeDecoderPayloadCells
            bits padding).length :=
    selectedSegmentLogicalTapeDecoderFootprintCellsFromPayload_length
      (selectedSegmentLogicalTapeDecoderPayloadCells bits padding)
  have hpayload :
      (selectedSegmentLogicalTapeDecoderPayloadCells
          bits padding).length =
        bits.length + padding.length + 2 :=
    selectedSegmentLogicalTapeDecoderPayloadCells_length bits padding
  simp [guardedTwoTapeStructuredPrefixFootprintVisibleTail,
    selectedSegmentLogicalTapeDecoderFootprintCells_eq_fromPayload,
    hfoot, hpayload]
  lia

theorem guardedTwoTapeStructuredPrefixBoundarySourceCells_eq_sourceTape_cells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    guardedTwoTapeStructuredPrefixBoundarySourceCells
        T0 T1 bits padding =
      Tape.cells
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding) := by
  rw [guardedTwoTapeStructuredPrefixEraserSourceTape_cells_eq_boundaryFields_append_footprint]
  simp [guardedTwoTapeStructuredPrefixBoundarySourceCells,
    guardedTwoTapeStructuredPrefixFirstFieldEncodedCells,
    guardedTwoTapeStructuredPrefixFirstFieldBits,
    guardedTwoTapeStructuredPrefixSecondFieldEncodedCells,
    guardedTwoTapeStructuredPrefixSecondFieldBits,
    guardedTwoTapeStructuredPrefixFootprintVisibleTail]

theorem guardedTwoTapeStructuredPrefixBoundarySourceCells_filterMap
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (guardedTwoTapeStructuredPrefixBoundarySourceCells
        T0 T1 bits padding).filterMap (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (List.append bits (padding.filterMap (fun cell => cell)))) := by
  rw [guardedTwoTapeStructuredPrefixBoundarySourceCells_eq_sourceTape_cells]
  exact
    guardedTwoTapeStructuredPrefixEraserSourceTape_cells_filterMap_eq_guardedBits
      T0 T1 bits padding

theorem guardedTwoTapeStructuredPrefixBoundarySourceCells_length
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (guardedTwoTapeStructuredPrefixBoundarySourceCells
        T0 T1 bits padding).length =
      2 * T0.left.length + 2 * T0.right.length +
        (2 * T1.left.length + 2 * T1.right.length) +
        (31 + 2 * bits.length + 2 * padding.length) := by
  rw [guardedTwoTapeStructuredPrefixBoundarySourceCells_eq_sourceTape_cells]
  exact guardedTwoTapeStructuredPrefixEraserSourceTape_cells_length
    T0 T1 bits padding

theorem guardedTwoTapeStructuredPrefixAfterSecondBoundaryCells_eq_secondTarget_cells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    guardedTwoTapeStructuredPrefixAfterSecondBoundaryCells
        T0 T1 bits padding =
      Tape.cells
        (guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserTargetTape
          T0 T1 bits padding) := by
  rw [guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserTargetTape_cells_eq]
  simp [guardedTwoTapeStructuredPrefixAfterSecondBoundaryCells,
    guardedTwoTapeStructuredPrefixFirstFieldEncodedCells,
    guardedTwoTapeStructuredPrefixFirstFieldBits,
    guardedTwoTapeStructuredPrefixSecondFieldErasedCells,
    guardedTwoTapeStructuredPrefixSecondFieldBits,
    guardedTwoTapeStructuredPrefixFootprintVisibleTail]

theorem guardedTwoTapeStructuredPrefixAfterSecondBoundaryCells_eq_firstSource_cells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    guardedTwoTapeStructuredPrefixAfterSecondBoundaryCells
        T0 T1 bits padding =
      Tape.cells
        (guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSourceTape
          T0 T1 bits padding) := by
  rw [guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSourceTape_cells]
  exact
    guardedTwoTapeStructuredPrefixAfterSecondBoundaryCells_eq_secondTarget_cells
      T0 T1 bits padding

theorem guardedTwoTapeStructuredPrefixAfterSecondBoundaryCells_filterMap
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (guardedTwoTapeStructuredPrefixAfterSecondBoundaryCells
        T0 T1 bits padding).filterMap (fun cell => cell) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append bits (padding.filterMap (fun cell => cell))) := by
  rw [guardedTwoTapeStructuredPrefixAfterSecondBoundaryCells_eq_secondTarget_cells]
  exact
    guardedTwoTapeStructuredPrefixSecondFieldBoundaryTarget_filterMap
      T0 T1 bits padding

theorem guardedTwoTapeStructuredPrefixAfterSecondBoundaryCells_length
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (guardedTwoTapeStructuredPrefixAfterSecondBoundaryCells
        T0 T1 bits padding).length =
      2 * T0.left.length + 2 * T0.right.length +
        (2 * T1.left.length + 2 * T1.right.length) +
        (31 + 2 * bits.length + 2 * padding.length) := by
  simp [guardedTwoTapeStructuredPrefixAfterSecondBoundaryCells,
    guardedTwoTapeStructuredPrefixFirstFieldEncodedCells_length,
    guardedTwoTapeStructuredPrefixSecondFieldErasedCells_length,
    guardedTwoTapeStructuredPrefixFootprintVisibleTail_length,
    logicalTapeBits_guardLogicalTape_length_boundaryPhase]
  lia

theorem guardedTwoTapeStructuredPrefixAfterFirstBoundaryCells_eq_firstTarget_cells
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    guardedTwoTapeStructuredPrefixAfterFirstBoundaryCells
        T0 T1 bits padding =
      Tape.cells
        (guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape
          T0 T1 bits padding) := by
  rw [guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape_cells_eq]
  simp [guardedTwoTapeStructuredPrefixAfterFirstBoundaryCells,
    guardedTwoTapeStructuredPrefixFirstFieldErasedCells,
    guardedTwoTapeStructuredPrefixFirstFieldBits,
    guardedTwoTapeStructuredPrefixSecondFieldErasedCells,
    guardedTwoTapeStructuredPrefixSecondFieldBits,
    guardedTwoTapeStructuredPrefixFootprintVisibleTail]

theorem guardedTwoTapeStructuredPrefixAfterFirstBoundaryCells_filterMap
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (guardedTwoTapeStructuredPrefixAfterFirstBoundaryCells
        T0 T1 bits padding).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [guardedTwoTapeStructuredPrefixAfterFirstBoundaryCells_eq_firstTarget_cells]
  exact
    guardedTwoTapeStructuredPrefixFirstFieldBoundaryTarget_filterMap
      T0 T1 bits padding

theorem guardedTwoTapeStructuredPrefixAfterFirstBoundaryCells_length
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    (guardedTwoTapeStructuredPrefixAfterFirstBoundaryCells
        T0 T1 bits padding).length =
      2 * T0.left.length + 2 * T0.right.length +
        (2 * T1.left.length + 2 * T1.right.length) +
        (31 + 2 * bits.length + 2 * padding.length) := by
  simp [guardedTwoTapeStructuredPrefixAfterFirstBoundaryCells,
    guardedTwoTapeStructuredPrefixFirstFieldErasedCells_length,
    guardedTwoTapeStructuredPrefixSecondFieldErasedCells_length,
    guardedTwoTapeStructuredPrefixFootprintVisibleTail_length,
    logicalTapeBits_guardLogicalTape_length_boundaryPhase]
  lia

/-! ## Exact boundary eraser phases -/

def GuardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    forall (T0 T1 : Tape Bool) (bits : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTape
        (guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserSourceTape
          T0 T1 bits padding)
        (guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserTargetTape
          T0 T1 bits padding)

def GuardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserConstruction :
    Prop :=
  exists eraser : MachineDescription,
    GuardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserSpec eraser

def GuardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    forall (T0 T1 : Tape Bool) (bits : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTape
        (guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSourceTape
          T0 T1 bits padding)
        (guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape
          T0 T1 bits padding)

def GuardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserConstruction :
    Prop :=
  exists eraser : MachineDescription,
    GuardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSpec eraser

def GuardedTwoTapeStructuredPrefixBoundaryEraserPairSpec
    (eraser : MachineDescription) : Prop :=
  GuardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserSpec eraser ∧
    GuardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSpec eraser

def GuardedTwoTapeStructuredPrefixBoundaryEraserPairConstruction :
    Prop :=
  exists eraser : MachineDescription,
    GuardedTwoTapeStructuredPrefixBoundaryEraserPairSpec eraser

theorem guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserSpec_core :
    GuardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserSpec
      leftBoundaryEraserDescription := by
  refine ⟨leftBoundaryEraserDescription_subroutineReady, ?_⟩
  intro T0 T1 bits padding
  exact
    leftBoundaryEraserDescription_haltsFromTape
      (guardedTwoTapeStructuredPrefixSecondFieldEraserBaseLeft T0)
      (logicalTapeBits (guardLogicalTape T1))
      none
      (guardedTwoTapeStructuredPrefixSecondFieldEraserSuffixTail
        bits padding)

theorem guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserConstruction_core :
    GuardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserConstruction :=
  ⟨leftBoundaryEraserDescription,
    guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserSpec_core⟩

theorem guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSpec_core :
    GuardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSpec
      leftBoundaryEraserDescription := by
  refine ⟨leftBoundaryEraserDescription_subroutineReady, ?_⟩
  intro T0 T1 bits padding
  exact
    leftBoundaryEraserDescription_haltsFromTape
      []
      (logicalTapeBits (guardLogicalTape T0))
      none
      (guardedTwoTapeStructuredPrefixFirstFieldEraserSuffixTail
        T1 bits padding)

theorem guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserConstruction_core :
    GuardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserConstruction :=
  ⟨leftBoundaryEraserDescription,
    guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSpec_core⟩

theorem guardedTwoTapeStructuredPrefixBoundaryEraserPairSpec_core :
    GuardedTwoTapeStructuredPrefixBoundaryEraserPairSpec
      leftBoundaryEraserDescription :=
  ⟨guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserSpec_core,
    guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSpec_core⟩

theorem guardedTwoTapeStructuredPrefixBoundaryEraserPairConstruction_core :
    GuardedTwoTapeStructuredPrefixBoundaryEraserPairConstruction :=
  ⟨leftBoundaryEraserDescription,
    guardedTwoTapeStructuredPrefixBoundaryEraserPairSpec_core⟩

/-! ## Equivalence and output views of the exact boundary phases -/

def GuardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserEquivSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    forall (T0 T1 : Tape Bool) (bits : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserSourceTape
          T0 T1 bits padding)
        (guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserTargetTape
          T0 T1 bits padding)

def GuardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserEquivSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    forall (T0 T1 : Tape Bool) (bits : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSourceTape
          T0 T1 bits padding)
        (guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape
          T0 T1 bits padding)

def GuardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserOutputSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    forall (T0 T1 : Tape Bool) (bits : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeWithOutput
        (guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserSourceTape
          T0 T1 bits padding)
        (Tape.normalizedOutput
          (guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserTargetTape
            T0 T1 bits padding))

def GuardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserOutputSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    forall (T0 T1 : Tape Bool) (bits : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeWithOutput
        (guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSourceTape
          T0 T1 bits padding)
        (Tape.normalizedOutput
          (guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape
            T0 T1 bits padding))

theorem guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserEquivSpec_of_exact
    {eraser : MachineDescription}
    (h :
      GuardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserSpec eraser) :
    GuardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserEquivSpec
      eraser := by
  rcases h with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro T0 T1 bits padding
  exact
    MachineDescription.HaltsFromTape.toEquiv
      (hrun T0 T1 bits padding)

theorem guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserEquivSpec_of_exact
    {eraser : MachineDescription}
    (h :
      GuardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSpec eraser) :
    GuardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserEquivSpec
      eraser := by
  rcases h with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro T0 T1 bits padding
  exact
    MachineDescription.HaltsFromTape.toEquiv
      (hrun T0 T1 bits padding)

theorem guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserOutputSpec_of_exact
    {eraser : MachineDescription}
    (h :
      GuardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserSpec eraser) :
    GuardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserOutputSpec
      eraser := by
  rcases h with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro T0 T1 bits padding
  exact
    MachineDescription.haltsFromTapeWithOutput_of_haltsFromTape
      (hrun T0 T1 bits padding)

theorem guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserOutputSpec_of_exact
    {eraser : MachineDescription}
    (h :
      GuardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSpec eraser) :
    GuardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserOutputSpec
      eraser := by
  rcases h with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro T0 T1 bits padding
  exact
    MachineDescription.haltsFromTapeWithOutput_of_haltsFromTape
      (hrun T0 T1 bits padding)

theorem guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserEquivSpec_core :
    GuardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserEquivSpec
      leftBoundaryEraserDescription :=
  guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserEquivSpec_of_exact
    guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserSpec_core

theorem guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserEquivSpec_core :
    GuardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserEquivSpec
      leftBoundaryEraserDescription :=
  guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserEquivSpec_of_exact
    guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSpec_core

theorem guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserOutputSpec_core :
    GuardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserOutputSpec
      leftBoundaryEraserDescription :=
  guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserOutputSpec_of_exact
    guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserSpec_core

theorem guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserOutputSpec_core :
    GuardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserOutputSpec
      leftBoundaryEraserDescription :=
  guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserOutputSpec_of_exact
    guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSpec_core

/-! ## Named positioning gaps -/

def GuardedTwoTapeStructuredPrefixInitialPositionerSpec
    (positioner : MachineDescription) : Prop :=
  positioner.SubroutineReady ∧
    forall (T0 T1 : Tape Bool) (bits : Word Bool)
      (padding : List (Option Bool)),
      positioner.HaltsFromTape
        (guardedTwoTapeStructuredPrefixEraserSourceRightEdgeTape
          T0 T1 bits padding)
        (guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserSourceTape
          T0 T1 bits padding)

def GuardedTwoTapeStructuredPrefixInitialPositionerConstruction :
    Prop :=
  exists positioner : MachineDescription,
    GuardedTwoTapeStructuredPrefixInitialPositionerSpec positioner

def GuardedTwoTapeStructuredPrefixBetweenFieldsPositionerSpec
    (positioner : MachineDescription) : Prop :=
  positioner.SubroutineReady ∧
    forall (T0 T1 : Tape Bool) (bits : Word Bool)
      (padding : List (Option Bool)),
      positioner.HaltsFromTape
        (guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserTargetTape
          T0 T1 bits padding)
        (guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSourceTape
          T0 T1 bits padding)

def GuardedTwoTapeStructuredPrefixBetweenFieldsPositionerConstruction :
    Prop :=
  exists positioner : MachineDescription,
    GuardedTwoTapeStructuredPrefixBetweenFieldsPositionerSpec positioner

def GuardedTwoTapeStructuredPrefixErasedPrefixCompactorSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    forall (T0 T1 : Tape Bool) (bits : Word Bool)
      (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape
          T0 T1 bits padding)
        (guardedTwoTapeStructuredPrefixEraserTargetRightEdgeTape
          bits padding)

def GuardedTwoTapeStructuredPrefixErasedPrefixCompactorConstruction :
    Prop :=
  exists compactor : MachineDescription,
    GuardedTwoTapeStructuredPrefixErasedPrefixCompactorSpec compactor

def GuardedTwoTapeStructuredPrefixInitialPositionerOutputSpec
    (positioner : MachineDescription) : Prop :=
  positioner.SubroutineReady ∧
    forall (T0 T1 : Tape Bool) (bits : Word Bool)
      (padding : List (Option Bool)),
      positioner.HaltsFromTapeWithOutput
        (guardedTwoTapeStructuredPrefixEraserSourceRightEdgeTape
          T0 T1 bits padding)
        (Tape.normalizedOutput
          (guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserSourceTape
            T0 T1 bits padding))

def GuardedTwoTapeStructuredPrefixBetweenFieldsPositionerOutputSpec
    (positioner : MachineDescription) : Prop :=
  positioner.SubroutineReady ∧
    forall (T0 T1 : Tape Bool) (bits : Word Bool)
      (padding : List (Option Bool)),
      positioner.HaltsFromTapeWithOutput
        (guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserTargetTape
          T0 T1 bits padding)
        (Tape.normalizedOutput
          (guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSourceTape
            T0 T1 bits padding))

def GuardedTwoTapeStructuredPrefixErasedPrefixCompactorOutputSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    forall (T0 T1 : Tape Bool) (bits : Word Bool)
      (padding : List (Option Bool)),
      compactor.HaltsFromTapeWithOutput
        (guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape
          T0 T1 bits padding)
        (Tape.normalizedOutput
          (guardedTwoTapeStructuredPrefixEraserTargetRightEdgeTape
            bits padding))

theorem guardedTwoTapeStructuredPrefixInitialPositionerOutputSpec_of_exact
    {positioner : MachineDescription}
    (h :
      GuardedTwoTapeStructuredPrefixInitialPositionerSpec positioner) :
    GuardedTwoTapeStructuredPrefixInitialPositionerOutputSpec
      positioner := by
  rcases h with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro T0 T1 bits padding
  exact
    MachineDescription.haltsFromTapeWithOutput_of_haltsFromTape
      (hrun T0 T1 bits padding)

theorem guardedTwoTapeStructuredPrefixBetweenFieldsPositionerOutputSpec_of_exact
    {positioner : MachineDescription}
    (h :
      GuardedTwoTapeStructuredPrefixBetweenFieldsPositionerSpec positioner) :
    GuardedTwoTapeStructuredPrefixBetweenFieldsPositionerOutputSpec
      positioner := by
  rcases h with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro T0 T1 bits padding
  exact
    MachineDescription.haltsFromTapeWithOutput_of_haltsFromTape
      (hrun T0 T1 bits padding)

theorem guardedTwoTapeStructuredPrefixErasedPrefixCompactorOutputSpec_of_exact
    {compactor : MachineDescription}
    (h :
      GuardedTwoTapeStructuredPrefixErasedPrefixCompactorSpec compactor) :
    GuardedTwoTapeStructuredPrefixErasedPrefixCompactorOutputSpec
      compactor := by
  rcases h with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro T0 T1 bits padding
  exact
    MachineDescription.haltsFromTapeWithOutput_of_haltsFromTapeEquiv
      (hrun T0 T1 bits padding)

theorem guardedTwoTapeStructuredPrefixInitialPositionerSourceTarget_normalizedOutput_eq
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixEraserSourceRightEdgeTape
          T0 T1 bits padding) =
      Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserSourceTape
          T0 T1 bits padding) := by
  rw [← guardedTwoTapeStructuredPrefixEraserSourceTape_eq_rightEdgeTape]
  rw [Tape.normalizedOutput]
  rw [Tape.normalizedOutput]
  rw [guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserSourceTape_cells]

theorem guardedTwoTapeStructuredPrefixBetweenFieldsPositionerSourceTarget_normalizedOutput_eq
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserTargetTape
          T0 T1 bits padding) =
      Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSourceTape
          T0 T1 bits padding) := by
  exact
    guardedTwoTapeStructuredPrefixSecondBoundaryTarget_eq_firstBoundarySource_output
      T0 T1 bits padding

theorem guardedTwoTapeStructuredPrefixErasedPrefixCompactorSourceTarget_normalizedOutput_eq
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape
          T0 T1 bits padding) =
      Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixEraserTargetRightEdgeTape
          bits padding) := by
  rw [guardedTwoTapeStructuredPrefixFirstFieldBoundaryTarget_normalizedOutput]
  rw [← guardedTwoTapeStructuredPrefixEraserTargetTape_eq_rightEdgeTape]
  rw [guardedTwoTapeStructuredPrefixEraserTargetTape_normalizedOutput]

theorem guardedTwoTapeStructuredPrefixInitialPositionerOutputTarget_eq_source
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserSourceTape
          T0 T1 bits padding) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (List.append bits (padding.filterMap (fun cell => cell)))) := by
  exact
    guardedTwoTapeStructuredPrefixSecondFieldBoundarySource_normalizedOutput
      T0 T1 bits padding

theorem guardedTwoTapeStructuredPrefixBetweenFieldsPositionerOutputTarget_eq_source
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSourceTape
          T0 T1 bits padding) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append bits (padding.filterMap (fun cell => cell))) := by
  exact
    guardedTwoTapeStructuredPrefixFirstFieldBoundarySource_normalizedOutput
      T0 T1 bits padding

theorem guardedTwoTapeStructuredPrefixErasedPrefixCompactorOutputTarget_eq_footprint
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixEraserTargetRightEdgeTape
          bits padding) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [← guardedTwoTapeStructuredPrefixEraserTargetTape_eq_rightEdgeTape]
  exact guardedTwoTapeStructuredPrefixEraserTargetTape_normalizedOutput
    bits padding

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
