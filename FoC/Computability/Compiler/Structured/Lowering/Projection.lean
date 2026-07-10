import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StatefulOptionAppendGenerated
import FoC.Computability.Compiler.Structured.Lowering.CursorSeek

set_option doc.verso true

/-!
# Structured tape projection contracts

This module records reusable finite-machine contracts for projecting logical
tapes out of the guarded structured one-tape encoding.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

/--
Finite-machine contract for extracting logical tape 0 from a guarded
three-logical-tape encoding.

The target is stated up to {name}`Tape.Equiv` so an implementation may preserve
or introduce harmless guard blanks around the extracted logical tape.
-/
def StructuredTape0ProjectorSpec
    (projector : MachineDescription) : Prop :=
  projector.SubroutineReady ∧
    forall T0 T1 T2 : Tape Bool,
      projector.HaltsFromTapeEquiv
        (encodedGuardedStructured3Tapes T0 T1 T2)
        T0

/-- Existence wrapper for {name}`StructuredTape0ProjectorSpec`. -/
def StructuredTape0ProjectorConstruction : Prop :=
  exists projector : MachineDescription,
    StructuredTape0ProjectorSpec projector

/--
Normalizer contract for the physical tape-0 segment when the cursor is at the
opening separator.
-/
def StructuredTape0SegmentNormalizerSpec
    (normalizer : MachineDescription) : Prop :=
  normalizer.SubroutineReady ∧
    forall (T0 T1 T2 : Tape Bool) (physical : Tape Bool),
      AtTapeSeparator (guardLogicalTapes [T0, T1, T2]) 0 physical ->
        normalizer.HaltsFromTapeEquiv physical T0

/-- Existence wrapper for {name}`StructuredTape0SegmentNormalizerSpec`. -/
def StructuredTape0SegmentNormalizerConstruction : Prop :=
  exists normalizer : MachineDescription,
    StructuredTape0SegmentNormalizerSpec normalizer

/-- Tape-0 projection starts already at the first segment separator. -/
def structuredTape0ProjectorDescription
    (normalizer : MachineDescription) : MachineDescription :=
  normalizer

theorem structuredTape0ProjectorDescription_subroutineReady
    {normalizer : MachineDescription}
    (hnormalizer : normalizer.SubroutineReady) :
    (structuredTape0ProjectorDescription normalizer).SubroutineReady :=
  hnormalizer

theorem structuredTape0ProjectorSpec_of_segmentNormalizerSpec
    {normalizer : MachineDescription}
    (hnormalizer : StructuredTape0SegmentNormalizerSpec normalizer) :
    StructuredTape0ProjectorSpec
      (structuredTape0ProjectorDescription normalizer) := by
  constructor
  · exact
      structuredTape0ProjectorDescription_subroutineReady
        hnormalizer.left
  · intro T0 T1 T2
    exact
      hnormalizer.right T0 T1 T2
        (encodedGuardedStructured3Tapes T0 T1 T2)
        (by
          simpa [encodedGuardedStructured3Tapes] using!
            atEncodedBlockStart_self (guardLogicalTapes [T0, T1, T2]))

theorem structuredTape0ProjectorConstruction_of_segmentNormalizerConstruction
    (hnormalizer : StructuredTape0SegmentNormalizerConstruction) :
    StructuredTape0ProjectorConstruction := by
  rcases hnormalizer with ⟨normalizer, hnormalizerSpec⟩
  exact
    ⟨structuredTape0ProjectorDescription normalizer,
      structuredTape0ProjectorSpec_of_segmentNormalizerSpec
        hnormalizerSpec⟩

/--
Finite-machine contract for extracting logical tape 1 from a guarded
three-logical-tape encoding.

The target is stated up to {name}`Tape.Equiv` so an implementation may preserve
or introduce harmless guard blanks around the extracted logical tape.
-/
def StructuredTape1ProjectorSpec
    (projector : MachineDescription) : Prop :=
  projector.SubroutineReady ∧
    forall T0 T1 T2 : Tape Bool,
      projector.HaltsFromTapeEquiv
        (encodedGuardedStructured3Tapes T0 T1 T2)
        T1

/-- Existence wrapper for {name}`StructuredTape1ProjectorSpec`. -/
def StructuredTape1ProjectorConstruction : Prop :=
  exists projector : MachineDescription,
    StructuredTape1ProjectorSpec projector

/--
Normalizer contract for the physical tape-1 segment after the cursor has
already reached its opening separator.
-/
def StructuredTape1SegmentNormalizerSpec
    (normalizer : MachineDescription) : Prop :=
  normalizer.SubroutineReady ∧
    forall (T0 T1 T2 : Tape Bool) (physical : Tape Bool),
      AtTapeSeparator (guardLogicalTapes [T0, T1, T2]) 1 physical ->
        normalizer.HaltsFromTapeEquiv physical T1

/-- Existence wrapper for {name}`StructuredTape1SegmentNormalizerSpec`. -/
def StructuredTape1SegmentNormalizerConstruction : Prop :=
  exists normalizer : MachineDescription,
    StructuredTape1SegmentNormalizerSpec normalizer

/--
The canonical projector assembled from the proven tape-1 seeker and a segment
normalizer.
-/
def structuredTape1ProjectorDescription
    (normalizer : MachineDescription) : MachineDescription :=
  canonicalPrimitiveSeqDescription seekTape1Description normalizer

theorem structuredTape1ProjectorDescription_subroutineReady
    {normalizer : MachineDescription}
    (hnormalizer : normalizer.SubroutineReady) :
    (structuredTape1ProjectorDescription normalizer).SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    seekTape1Description_contract.subroutineReady hnormalizer

theorem structuredTape1ProjectorSpec_of_segmentNormalizerSpec
    {normalizer : MachineDescription}
    (hnormalizer : StructuredTape1SegmentNormalizerSpec normalizer) :
    StructuredTape1ProjectorSpec
      (structuredTape1ProjectorDescription normalizer) := by
  constructor
  · exact
      structuredTape1ProjectorDescription_subroutineReady
        hnormalizer.left
  · intro T0 T1 T2
    have hsource :
        AtExistingTapeSeparator (guardLogicalTapes [T0, T1, T2]) 0
          (encodedGuardedStructured3Tapes T0 T1 T2) := by
      constructor
      · simpa [encodedGuardedStructured3Tapes] using!
          atEncodedBlockStart_self (guardLogicalTapes [T0, T1, T2])
      · refine
          ⟨guardLogicalTape T0,
            [guardLogicalTape T1, guardLogicalTape T2], ?_⟩
        simp [guardLogicalTapes]
    rcases
        seekTape1Description_contract.realizes
          (guardLogicalTapes [T0, T1, T2])
          (encodedGuardedStructured3Tapes T0 T1 T2)
          hsource with
      ⟨Tmid, hseek, hseparator⟩
    exact
      canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        seekTape1Description_contract.subroutineReady
        hnormalizer.left
        hseek.toEquiv
        (hnormalizer.right T0 T1 T2 Tmid hseparator)

theorem structuredTape1ProjectorConstruction_of_segmentNormalizerConstruction
    (hnormalizer : StructuredTape1SegmentNormalizerConstruction) :
    StructuredTape1ProjectorConstruction := by
  rcases hnormalizer with ⟨normalizer, hnormalizerSpec⟩
  exact
    ⟨structuredTape1ProjectorDescription normalizer,
      structuredTape1ProjectorSpec_of_segmentNormalizerSpec
        hnormalizerSpec⟩

/--
Finite-machine contract for extracting logical tape 2 from a guarded
three-logical-tape encoding.

The target is stated up to {name}`Tape.Equiv` so an implementation may preserve
or introduce harmless guard blanks around the extracted logical tape.
-/
def StructuredTape2ProjectorSpec
    (projector : MachineDescription) : Prop :=
  projector.SubroutineReady ∧
    forall T0 T1 T2 : Tape Bool,
      projector.HaltsFromTapeEquiv
        (encodedGuardedStructured3Tapes T0 T1 T2)
        T2

/-- Existence wrapper for {name}`StructuredTape2ProjectorSpec`. -/
def StructuredTape2ProjectorConstruction : Prop :=
  exists projector : MachineDescription,
    StructuredTape2ProjectorSpec projector

/--
Normalizer contract for the physical tape-2 segment after the cursor has
already reached its opening separator.

The source uses the guarded encoding because lowered structured machines carry
one represented blank guard on both sides of each logical tape.  The target is
the original unguarded logical tape, up to {name}`Tape.Equiv`.
-/
def StructuredTape2SegmentNormalizerSpec
    (normalizer : MachineDescription) : Prop :=
  normalizer.SubroutineReady ∧
    forall (T0 T1 T2 : Tape Bool) (physical : Tape Bool),
      AtTapeSeparator (guardLogicalTapes [T0, T1, T2]) 2 physical ->
        normalizer.HaltsFromTapeEquiv physical T2

/-- Existence wrapper for {name}`StructuredTape2SegmentNormalizerSpec`. -/
def StructuredTape2SegmentNormalizerConstruction : Prop :=
  exists normalizer : MachineDescription,
    StructuredTape2SegmentNormalizerSpec normalizer

/--
Decoder for a canonical selected singleton structured segment.

The cursor is at the selected segment separator, any encoded prefix to the left
is ignored by the contract, and the selected guarded singleton segment is
decoded back to the original plain logical tape.  Guard-refresh machines only
restore this canonical input shape; they do not perform this decoding step.
-/
def StructuredSelectedSingletonSegmentDecoderSpec
    (decoder : MachineDescription) : Prop :=
  decoder.SubroutineReady ∧
    forall (target : Tape Bool) (encodedPrefix : List (Option Bool)),
      decoder.HaltsFromTapeEquiv
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells [guardLogicalTape target]))
        target

/--
Existence wrapper for
{name}`StructuredSelectedSingletonSegmentDecoderSpec`.
-/
def StructuredSelectedSingletonSegmentDecoderConstruction : Prop :=
  exists decoder : MachineDescription,
    StructuredSelectedSingletonSegmentDecoderSpec decoder

/--
Finite-control scanner state count for decoding {name}`logicalTapeBits`.

State {lit}`0` expects the first bit of a two-bit logical cell code, state
{lit}`1` remembers that the first bit was {lit}`false`, and state {lit}`2`
remembers that the first bit was {lit}`true`.
-/
def selectedSegmentLogicalTapeDecoderStateCount : Nat := 3

def selectedSegmentLogicalTapeDecoderStart : Nat := 0

def selectedSegmentLogicalTapeDecoderNext : Nat -> Bool -> Nat
  | 0, false => 1
  | 0, true => 2
  | _, _ => 0

def selectedSegmentLogicalTapeDecoderEmit : Nat -> Bool -> Option Bool
  | 1, true => some false
  | 2, false => some true
  | _, _ => none

def selectedSegmentLogicalTapeDecoderCellCells :
    Option Bool -> List (Option Bool)
  | none => [none, none]
  | some bit => [none, some bit]

theorem selectedSegmentLogicalTapeDecoderStart_lt :
    selectedSegmentLogicalTapeDecoderStart <
      selectedSegmentLogicalTapeDecoderStateCount := by
  decide

theorem selectedSegmentLogicalTapeDecoderNext_lt :
    forall state bit,
      state < selectedSegmentLogicalTapeDecoderStateCount ->
        selectedSegmentLogicalTapeDecoderNext state bit <
          selectedSegmentLogicalTapeDecoderStateCount := by
  intro state bit hstate
  cases state with
  | zero =>
      cases bit <;> decide
  | succ state =>
      cases state with
      | zero =>
          cases bit <;> decide
      | succ state =>
          cases state with
          | zero =>
              cases bit <;> decide
          | succ state =>
              simp [selectedSegmentLogicalTapeDecoderStateCount] at hstate
              lia

theorem selectedSegmentLogicalTapeDecoder_after_logicalCellBits_zero
    (cell : Option Bool) :
    statefulOptionAfter selectedSegmentLogicalTapeDecoderNext 0
      (logicalCellBits cell) = 0 := by
  cases cell with
  | none =>
      rfl
  | some bit =>
      cases bit <;> rfl

theorem selectedSegmentLogicalTapeDecoder_output_logicalCellBits_zero
    (cell : Option Bool) :
    statefulOptionOutputFrom selectedSegmentLogicalTapeDecoderNext
        selectedSegmentLogicalTapeDecoderEmit 0 (logicalCellBits cell) =
      match cell with
      | none => []
      | some bit => [bit] := by
  cases cell with
  | none =>
      rfl
  | some bit =>
      cases bit <;> rfl

theorem selectedSegmentLogicalTapeDecoder_cells_logicalCellBits_zero
    (cell : Option Bool) :
    statefulOptionCellsFrom selectedSegmentLogicalTapeDecoderNext
        selectedSegmentLogicalTapeDecoderEmit 0 (logicalCellBits cell) =
      selectedSegmentLogicalTapeDecoderCellCells cell := by
  cases cell with
  | none =>
      rfl
  | some bit =>
      cases bit <;> rfl

theorem selectedSegmentLogicalTapeDecoder_after_logicalCellListBits_zero
    (cells : List (Option Bool)) :
    statefulOptionAfter selectedSegmentLogicalTapeDecoderNext 0
      (logicalCellListBits cells) = 0 := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      cases cell with
      | none =>
          simpa [logicalCellListBits, logicalCellBits,
            statefulOptionAfter,
            selectedSegmentLogicalTapeDecoderNext] using ih
      | some bit =>
          cases bit <;>
            simpa [logicalCellListBits, logicalCellBits,
              statefulOptionAfter,
              selectedSegmentLogicalTapeDecoderNext] using ih

theorem selectedSegmentLogicalTapeDecoder_output_logicalCellListBits_zero
    (cells : List (Option Bool)) :
    statefulOptionOutputFrom selectedSegmentLogicalTapeDecoderNext
        selectedSegmentLogicalTapeDecoderEmit 0
        (logicalCellListBits cells) =
      cells.filterMap (fun cell => cell) := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      rw [logicalCellListBits]
      rw [statefulOptionOutputFrom_append]
      rw [selectedSegmentLogicalTapeDecoder_output_logicalCellBits_zero]
      rw [selectedSegmentLogicalTapeDecoder_after_logicalCellBits_zero]
      rw [ih]
      cases cell <;> rfl

theorem selectedSegmentLogicalTapeDecoder_cells_logicalCellListBits_zero
    (cells : List (Option Bool)) :
    statefulOptionCellsFrom selectedSegmentLogicalTapeDecoderNext
        selectedSegmentLogicalTapeDecoderEmit 0
        (logicalCellListBits cells) =
      (cells.map selectedSegmentLogicalTapeDecoderCellCells).flatten := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      rw [logicalCellListBits]
      rw [statefulOptionCellsFrom_append]
      rw [selectedSegmentLogicalTapeDecoder_cells_logicalCellBits_zero]
      rw [selectedSegmentLogicalTapeDecoder_after_logicalCellBits_zero]
      rw [ih]
      cases cell <;> rfl

theorem selectedSegmentLogicalTapeDecoder_after_headMarker_zero :
    statefulOptionAfter selectedSegmentLogicalTapeDecoderNext 0
      [true, true] = 0 := by
  rfl

theorem selectedSegmentLogicalTapeDecoder_output_headMarker_zero :
    statefulOptionOutputFrom selectedSegmentLogicalTapeDecoderNext
        selectedSegmentLogicalTapeDecoderEmit 0 [true, true] = [] := by
  rfl

theorem selectedSegmentLogicalTapeDecoder_cells_headMarker_zero :
    statefulOptionCellsFrom selectedSegmentLogicalTapeDecoderNext
        selectedSegmentLogicalTapeDecoderEmit 0 [true, true] =
      [none, none] := by
  rfl

theorem selectedSegmentLogicalTapeDecoder_cells_logicalTapeBits_zero
    (T : Tape Bool) :
    statefulOptionCellsFrom selectedSegmentLogicalTapeDecoderNext
        selectedSegmentLogicalTapeDecoderEmit 0 (logicalTapeBits T) =
      List.append
        ((T.left.reverse.map
          selectedSegmentLogicalTapeDecoderCellCells).flatten)
        (List.append [none, none]
          (List.append
            (selectedSegmentLogicalTapeDecoderCellCells T.head)
            ((T.right.map
              selectedSegmentLogicalTapeDecoderCellCells).flatten))) := by
  cases T with
  | mk left head right =>
      rw [logicalTapeBits]
      rw [statefulOptionCellsFrom_append]
      rw [selectedSegmentLogicalTapeDecoder_cells_logicalCellListBits_zero]
      rw [selectedSegmentLogicalTapeDecoder_after_logicalCellListBits_zero]
      rw [statefulOptionCellsFrom_append]
      rw [selectedSegmentLogicalTapeDecoder_cells_headMarker_zero]
      rw [selectedSegmentLogicalTapeDecoder_after_headMarker_zero]
      rw [statefulOptionCellsFrom_append]
      rw [selectedSegmentLogicalTapeDecoder_cells_logicalCellBits_zero]
      rw [selectedSegmentLogicalTapeDecoder_after_logicalCellBits_zero]
      rw [selectedSegmentLogicalTapeDecoder_cells_logicalCellListBits_zero]

theorem selectedSegmentLogicalTapeDecoder_output_logicalTapeBits_zero
    (T : Tape Bool) :
    statefulOptionOutputFrom selectedSegmentLogicalTapeDecoderNext
        selectedSegmentLogicalTapeDecoderEmit 0 (logicalTapeBits T) =
      Tape.normalizedOutput T := by
  cases T with
  | mk left head right =>
      rw [logicalTapeBits]
      rw [statefulOptionOutputFrom_append]
      rw [selectedSegmentLogicalTapeDecoder_output_logicalCellListBits_zero]
      rw [selectedSegmentLogicalTapeDecoder_after_logicalCellListBits_zero]
      rw [statefulOptionOutputFrom_append]
      rw [selectedSegmentLogicalTapeDecoder_output_headMarker_zero]
      rw [selectedSegmentLogicalTapeDecoder_after_headMarker_zero]
      rw [statefulOptionOutputFrom_append]
      rw [selectedSegmentLogicalTapeDecoder_output_logicalCellBits_zero]
      rw [selectedSegmentLogicalTapeDecoder_after_logicalCellBits_zero]
      rw [selectedSegmentLogicalTapeDecoder_output_logicalCellListBits_zero]
      cases head with
      | none =>
          simp [Tape.normalizedOutput, Tape.cells,
            List.filterMap_append]
      | some bit =>
          cases bit <;>
            simp [Tape.normalizedOutput, Tape.cells,
              List.filterMap_append]

/-- Generated finite-control decoder for the selected structured segment. -/
def selectedSegmentLogicalTapeDecoderDescription : MachineDescription :=
  generatedStatefulOptionAppendDescription
    selectedSegmentLogicalTapeDecoderStateCount
    selectedSegmentLogicalTapeDecoderStart
    selectedSegmentLogicalTapeDecoderNext
    selectedSegmentLogicalTapeDecoderEmit
    []

/-- Exact target shape produced by the selected-segment bit decoder. -/
def selectedSegmentLogicalTapeDecoderTargetTape
    (target : Tape Bool) (encodedPrefix : List (Option Bool)) :
    Tape Bool :=
  FSTStatefulOptionAppendTargetTapeFromLeft
    selectedSegmentLogicalTapeDecoderNext
    selectedSegmentLogicalTapeDecoderEmit
    selectedSegmentLogicalTapeDecoderStart
    (logicalTapeBits (guardLogicalTape target))
    []
    (none :: encodedPrefix.reverse)

theorem selectedSegmentLogicalTapeDecoderTargetTape_left
    (target : Tape Bool) (encodedPrefix : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderTargetTape
        target encodedPrefix).left =
      none ::
        List.append
          (statefulOptionCellsFrom selectedSegmentLogicalTapeDecoderNext
            selectedSegmentLogicalTapeDecoderEmit
            selectedSegmentLogicalTapeDecoderStart
            (logicalTapeBits (guardLogicalTape target))).reverse
          (none :: encodedPrefix.reverse) := by
  rfl

theorem selectedSegmentLogicalTapeDecoderTargetTape_head
    (target : Tape Bool) (encodedPrefix : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderTargetTape
        target encodedPrefix).head = none := by
  rfl

theorem selectedSegmentLogicalTapeDecoderTargetTape_right
    (target : Tape Bool) (encodedPrefix : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderTargetTape
        target encodedPrefix).right = [] := by
  rfl

theorem selectedSegmentLogicalTapeDecoderDescription_subroutineReady :
    selectedSegmentLogicalTapeDecoderDescription.SubroutineReady := by
  exact
    generatedStatefulOptionAppendDescription_subroutineReady
      selectedSegmentLogicalTapeDecoderStateCount
      selectedSegmentLogicalTapeDecoderStart
      selectedSegmentLogicalTapeDecoderNext
      selectedSegmentLogicalTapeDecoderEmit
      []
      selectedSegmentLogicalTapeDecoderStart_lt
      selectedSegmentLogicalTapeDecoderNext_lt

theorem selectedSegmentLogicalTapeDecoder_output_guardLogicalTapeBits_zero
    (T : Tape Bool) :
    statefulOptionOutputFrom selectedSegmentLogicalTapeDecoderNext
        selectedSegmentLogicalTapeDecoderEmit 0
        (logicalTapeBits (guardLogicalTape T)) =
      Tape.normalizedOutput T := by
  rw [selectedSegmentLogicalTapeDecoder_output_logicalTapeBits_zero]
  exact Tape.Equiv.normalizedOutput_eq (guardLogicalTape_equiv T)

theorem selectedSegmentLogicalTapeDecoderDescription_haltsFrom_selectedSingletonPayload
    (target : Tape Bool) (encodedPrefix : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDescription.HaltsFromTape
      (Tape.move Direction.right
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells [guardLogicalTape target])))
      (selectedSegmentLogicalTapeDecoderTargetTape
        target encodedPrefix) := by
  have hsource :
      Tape.move Direction.right
          (tapeAtEncodedSplit encodedPrefix
            (encodedStructuredTapeCells [guardLogicalTape target])) =
        tapeAtCells (none :: encodedPrefix.reverse)
          (List.append
            ((logicalTapeBits (guardLogicalTape target)).map some)
            [none]) := by
    simp [tapeAtEncodedSplit, encodedStructuredTapeCells,
      tapeSeparatorCells, logicalTapeCode_eq_map_some, Tape.move,
      Tape.moveRight, tapeAtCells]
    cases (List.map some (logicalTapeBits (guardLogicalTape target)) ++
      [none]) <;> rfl
  rw [hsource]
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
          [none]))
      (selectedSegmentLogicalTapeDecoderTargetTape
        target encodedPrefix)
  exact
    generatedStatefulOptionAppendDescription_haltsFrom_tapeAtCells
      selectedSegmentLogicalTapeDecoderStateCount
      selectedSegmentLogicalTapeDecoderStart
      selectedSegmentLogicalTapeDecoderNext
      selectedSegmentLogicalTapeDecoderEmit
      []
      (logicalTapeBits (guardLogicalTape target))
      (none :: encodedPrefix.reverse)
      selectedSegmentLogicalTapeDecoderStart_lt
      selectedSegmentLogicalTapeDecoderNext_lt

theorem selectedSegmentLogicalTapeDecoderTargetTape_normalizedOutput
    (target : Tape Bool) (encodedPrefix : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderTargetTape
          target encodedPrefix) =
      List.append (encodedPrefix.filterMap (fun cell => cell))
        (Tape.normalizedOutput target) := by
  rw [selectedSegmentLogicalTapeDecoderTargetTape,
    FSTStatefulOptionAppendTargetTapeFromLeft_normalizedOutput]
  simp [selectedSegmentLogicalTapeDecoderStart,
    selectedSegmentLogicalTapeDecoder_output_guardLogicalTapeBits_zero,
    List.filterMap_append]

/--
Exact visible-cell shape left by the selected-segment bit decoder.

The stale structured prefix is still present to the left of a separator blank;
the decoded selected segment is represented by optional output cells; and the
machine halts at the right blank after the scanned segment.
-/
theorem selectedSegmentLogicalTapeDecoderTargetTape_cells
    (target : Tape Bool) (encodedPrefix : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderTargetTape
          target encodedPrefix) =
      List.append encodedPrefix
        (none ::
          List.append
            (statefulOptionCellsFrom selectedSegmentLogicalTapeDecoderNext
              selectedSegmentLogicalTapeDecoderEmit
              selectedSegmentLogicalTapeDecoderStart
              (logicalTapeBits (guardLogicalTape target)))
            [none, none]) := by
  rw [selectedSegmentLogicalTapeDecoderTargetTape,
    FSTStatefulOptionAppendTargetTapeFromLeft_cells]
  simp [selectedSegmentLogicalTapeDecoderStart, List.append_assoc]

/--
Cleanup needed after the selected-segment bit decoder.

The decoder target still carries the old encoded structured prefix to the left
and contains blanks for skipped physical code bits.  This contract isolates the
remaining normalizer from the already-proved selected-segment seek and scan.
-/
def SelectedSegmentLogicalTapeDecoderCleanupSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTargetTape
          target encodedPrefix)
        target

/-- Existence wrapper for the selected-segment decoder cleanup phase. -/
def SelectedSegmentLogicalTapeDecoderCleanupConstruction : Prop :=
  exists cleanup : MachineDescription,
    SelectedSegmentLogicalTapeDecoderCleanupSpec cleanup

/-- Full selected-singleton decoder assembled from move-right, scan, cleanup. -/
def selectedSegmentLogicalTapeDecoderPipelineDescription
    (cleanup : MachineDescription) : MachineDescription :=
  canonicalPrimitiveSeqDescription
    (canonicalPrimitiveSeqDescription
      (cursorMoveOnceDescription Direction.right)
      selectedSegmentLogicalTapeDecoderDescription)
    cleanup

theorem selectedSegmentLogicalTapeDecoderPipelineDescription_subroutineReady
    {cleanup : MachineDescription}
    (hcleanup : cleanup.SubroutineReady) :
    (selectedSegmentLogicalTapeDecoderPipelineDescription
      cleanup).SubroutineReady := by
  exact
    canonicalPrimitiveSeqDescription_subroutineReady
      (canonicalPrimitiveSeqDescription_subroutineReady
        (cursorMoveOnceDescription_subroutineReady Direction.right)
        selectedSegmentLogicalTapeDecoderDescription_subroutineReady)
      hcleanup

theorem selectedSegmentLogicalTapeDecoderPipelineSpec_of_cleanupSpec
    {cleanup : MachineDescription}
    (hcleanup : SelectedSegmentLogicalTapeDecoderCleanupSpec cleanup) :
    StructuredSelectedSingletonSegmentDecoderSpec
      (selectedSegmentLogicalTapeDecoderPipelineDescription
        cleanup) := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderPipelineDescription_subroutineReady
        hcleanup.left
  · intro target encodedPrefix
    have hmove :
        (cursorMoveOnceDescription Direction.right).HaltsFromTapeEquiv
          (tapeAtEncodedSplit encodedPrefix
            (encodedStructuredTapeCells [guardLogicalTape target]))
          (Tape.move Direction.right
            (tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells [guardLogicalTape target]))) :=
      (cursorMoveOnceDescription_haltsFromTape Direction.right
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells [guardLogicalTape target]))).toEquiv
    have hscan :
        selectedSegmentLogicalTapeDecoderDescription.HaltsFromTapeEquiv
          (Tape.move Direction.right
            (tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells [guardLogicalTape target])))
          (selectedSegmentLogicalTapeDecoderTargetTape
            target encodedPrefix) :=
      (selectedSegmentLogicalTapeDecoderDescription_haltsFrom_selectedSingletonPayload
        target encodedPrefix).toEquiv
    have hpipelineScan :
        (canonicalPrimitiveSeqDescription
          (cursorMoveOnceDescription Direction.right)
          selectedSegmentLogicalTapeDecoderDescription).HaltsFromTapeEquiv
            (tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells [guardLogicalTape target]))
            (selectedSegmentLogicalTapeDecoderTargetTape
              target encodedPrefix) :=
      canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        (cursorMoveOnceDescription_subroutineReady Direction.right)
        selectedSegmentLogicalTapeDecoderDescription_subroutineReady
        hmove
        hscan
    exact
      canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        (canonicalPrimitiveSeqDescription_subroutineReady
          (cursorMoveOnceDescription_subroutineReady Direction.right)
          selectedSegmentLogicalTapeDecoderDescription_subroutineReady)
        hcleanup.left
        hpipelineScan
        (hcleanup.right target encodedPrefix)

/--
Decoder for a canonical selected structured segment that may have trailing
encoded structured segments to its right.

This is the stronger projector boundary needed for tape 0 and tape 1.  The
final-singleton decoder below is the tape-2 specialization where
{lit}`rest = []`.
-/
def StructuredSelectedHeadSegmentDecoderSpec
    (decoder : MachineDescription) : Prop :=
  decoder.SubroutineReady ∧
    forall (target : Tape Bool) (rest : List (Tape Bool))
      (encodedPrefix : List (Option Bool)),
      decoder.HaltsFromTapeEquiv
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells (guardLogicalTape target :: rest)))
        target

/--
Existence wrapper for
{name}`StructuredSelectedHeadSegmentDecoderSpec`.
-/
def StructuredSelectedHeadSegmentDecoderConstruction : Prop :=
  exists decoder : MachineDescription,
    StructuredSelectedHeadSegmentDecoderSpec decoder

theorem structuredSelectedSingletonSegmentDecoderConstruction_of_headDecoder
    (hdecoder :
      StructuredSelectedHeadSegmentDecoderConstruction) :
    StructuredSelectedSingletonSegmentDecoderConstruction := by
  rcases hdecoder with ⟨decoder, hdecoderReady, hdecoderRun⟩
  refine ⟨decoder, hdecoderReady, ?_⟩
  intro target encodedPrefix
  simpa using hdecoderRun target [] encodedPrefix

theorem structuredTape0SegmentNormalizerConstruction_of_selectedHeadDecoder
    (hdecoder :
      StructuredSelectedHeadSegmentDecoderConstruction) :
    StructuredTape0SegmentNormalizerConstruction := by
  rcases hdecoder with ⟨decoder, hdecoderReady, hdecoderRun⟩
  refine ⟨decoder, hdecoderReady, ?_⟩
  intro T0 T1 T2 physical hseparator
  rcases hseparator with ⟨_hindex, hphysical⟩
  rw [hphysical]
  simpa [encodedSuffixFromTape, guardLogicalTapes] using
    hdecoderRun T0 [guardLogicalTape T1, guardLogicalTape T2]
      (encodedPrefixBeforeTape (guardLogicalTapes [T0, T1, T2]) 0)

theorem structuredTape1SegmentNormalizerConstruction_of_selectedHeadDecoder
    (hdecoder :
      StructuredSelectedHeadSegmentDecoderConstruction) :
    StructuredTape1SegmentNormalizerConstruction := by
  rcases hdecoder with ⟨decoder, hdecoderReady, hdecoderRun⟩
  refine ⟨decoder, hdecoderReady, ?_⟩
  intro T0 T1 T2 physical hseparator
  rcases hseparator with ⟨_hindex, hphysical⟩
  rw [hphysical]
  simpa [encodedSuffixFromTape, guardLogicalTapes] using
    hdecoderRun T1 [guardLogicalTape T2]
      (encodedPrefixBeforeTape (guardLogicalTapes [T0, T1, T2]) 1)

theorem structuredTape2SegmentNormalizerConstruction_of_selectedHeadDecoder
    (hdecoder :
      StructuredSelectedHeadSegmentDecoderConstruction) :
    StructuredTape2SegmentNormalizerConstruction := by
  rcases hdecoder with ⟨decoder, hdecoderReady, hdecoderRun⟩
  refine ⟨decoder, hdecoderReady, ?_⟩
  intro T0 T1 T2 physical hseparator
  rcases hseparator with ⟨_hindex, hphysical⟩
  rw [hphysical]
  simpa [encodedSuffixFromTape, guardLogicalTapes] using
    hdecoderRun T2 []
      (encodedPrefixBeforeTape (guardLogicalTapes [T0, T1, T2]) 2)

/--
Generic extractor for a selected singleton structured segment.

This is currently the same boundary as
{name}`StructuredSelectedSingletonSegmentDecoderSpec`: the selected segment is
already canonical, so the remaining operation is decoding the structured
physical code to the plain logical tape.
-/
def StructuredSelectedSingletonSegmentExtractorSpec
    (extractor : MachineDescription) : Prop :=
  StructuredSelectedSingletonSegmentDecoderSpec extractor

/--
Existence wrapper for
{name}`StructuredSelectedSingletonSegmentExtractorSpec`.
-/
def StructuredSelectedSingletonSegmentExtractorConstruction : Prop :=
  exists extractor : MachineDescription,
    StructuredSelectedSingletonSegmentExtractorSpec extractor

theorem structuredSelectedSingletonSegmentExtractorConstruction_of_decoder
    (hdecoder :
      StructuredSelectedSingletonSegmentDecoderConstruction) :
    StructuredSelectedSingletonSegmentExtractorConstruction :=
  hdecoder

theorem structuredTape2SegmentNormalizerConstruction_of_selectedSingletonExtractor
    (hextractor :
      StructuredSelectedSingletonSegmentExtractorConstruction) :
    StructuredTape2SegmentNormalizerConstruction := by
  rcases hextractor with ⟨extractor, hextractorReady, hextractorRun⟩
  refine ⟨extractor, hextractorReady, ?_⟩
  intro T0 T1 T2 physical hseparator
  rcases hseparator with ⟨_hindex, hphysical⟩
  rw [hphysical]
  simpa [encodedSuffixFromTape, guardLogicalTapes] using
    hextractorRun T2
      (encodedPrefixBeforeTape (guardLogicalTapes [T0, T1, T2]) 2)

theorem structuredSelectedSingletonSegmentDecoderConstruction_of_cleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderCleanupConstruction) :
    StructuredSelectedSingletonSegmentDecoderConstruction := by
  rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
  exact
    ⟨selectedSegmentLogicalTapeDecoderPipelineDescription cleanup,
      selectedSegmentLogicalTapeDecoderPipelineSpec_of_cleanupSpec
        hcleanupSpec⟩

/--
The canonical projector assembled from the proven tape-2 seeker and a segment
normalizer.
-/
def structuredTape2ProjectorDescription
    (normalizer : MachineDescription) : MachineDescription :=
  canonicalPrimitiveSeqDescription seekTape2Description normalizer

theorem structuredTape2ProjectorDescription_subroutineReady
    {normalizer : MachineDescription}
    (hnormalizer : normalizer.SubroutineReady) :
    (structuredTape2ProjectorDescription normalizer).SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    seekTape2Description_subroutineReady hnormalizer

theorem structuredTape2ProjectorSpec_of_segmentNormalizerSpec
    {normalizer : MachineDescription}
    (hnormalizer : StructuredTape2SegmentNormalizerSpec normalizer) :
    StructuredTape2ProjectorSpec
      (structuredTape2ProjectorDescription normalizer) := by
  constructor
  · exact
      structuredTape2ProjectorDescription_subroutineReady
        hnormalizer.left
  · intro T0 T1 T2
    have hsource :
        exists A : Tape Bool, exists B : Tape Bool, exists C : Tape Bool,
          guardLogicalTapes [T0, T1, T2] = [A, B, C] ∧
            AtEncodedBlockStart (guardLogicalTapes [T0, T1, T2])
              (encodedGuardedStructured3Tapes T0 T1 T2) := by
      refine
        ⟨guardLogicalTape T0, guardLogicalTape T1,
          guardLogicalTape T2, ?_, ?_⟩
      · simp [guardLogicalTapes]
      · exact atEncodedBlockStart_self (guardLogicalTapes [T0, T1, T2])
    rcases
        seekTape2Description_contract_three.realizes
          (guardLogicalTapes [T0, T1, T2])
          (encodedGuardedStructured3Tapes T0 T1 T2)
          hsource with
      ⟨Tmid, hseek, hseparator⟩
    exact
      canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        seekTape2Description_subroutineReady
        hnormalizer.left
        hseek.toEquiv
        (hnormalizer.right T0 T1 T2 Tmid hseparator)

theorem structuredTape2ProjectorConstruction_of_segmentNormalizerConstruction
    (hnormalizer : StructuredTape2SegmentNormalizerConstruction) :
    StructuredTape2ProjectorConstruction := by
  rcases hnormalizer with ⟨normalizer, hnormalizerSpec⟩
  exact
    ⟨structuredTape2ProjectorDescription normalizer,
      structuredTape2ProjectorSpec_of_segmentNormalizerSpec
        hnormalizerSpec⟩

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
