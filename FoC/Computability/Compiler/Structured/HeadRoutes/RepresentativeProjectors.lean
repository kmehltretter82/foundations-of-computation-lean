import FoC.Computability.Compiler.Structured.HeadRoutes.Pipeline
import FoC.Computability.Compiler.Structured.HeadRoutes.RepresentativeCleanup

set_option doc.verso true

/-!
# Representative selected-head projector contracts

Representative cleanup gives exact behavior to a canonical padded output tape.
This module lifts that shape through the selected-head decoder and names the
parallel representative contracts for tape-2 projection.  Public adapters stay
equivalence-facing.
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
Representative exact output for the selected-head decoder.
-/
def structuredSelectedHeadSegmentDecoderRepresentativeOutputTape
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) : Tape Bool :=
  selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape
    target
    (selectedSegmentLogicalTapeDecoderRestPadding rest)
    encodedPrefix

theorem structuredSelectedHeadSegmentDecoderRepresentativeOutputTape_equiv
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    Tape.Equiv
      (structuredSelectedHeadSegmentDecoderRepresentativeOutputTape
        target rest encodedPrefix)
      target := by
  simpa [structuredSelectedHeadSegmentDecoderRepresentativeOutputTape] using
    selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape_equiv
      target
      (selectedSegmentLogicalTapeDecoderRestPadding rest)
      encodedPrefix

private theorem statefulOptionCellsFrom_length
    (next : Nat -> Bool -> Nat) (emit : Nat -> Bool -> Option Bool)
    (state : Nat) (input : Word Bool) :
    (statefulOptionCellsFrom next emit state input).length = input.length := by
  induction input generalizing state with
  | nil => rfl
  | cons bit rest ih =>
      simp [statefulOptionCellsFrom, ih]

private theorem selectedSegmentLogicalTapeDecoderSource_contextLength_le_handoff
    (target : Tape Bool) (padding encodedPrefix : List (Option Bool)) :
    Tape.contextLength
        (tapeAtEncodedSplit encodedPrefix
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode (guardLogicalTape target))
              (none :: padding)))) <=
      Tape.contextLength
        (canonicalPrimitiveSeqHandoffTape
          (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
            target padding encodedPrefix)) := by
  cases padding with
  | nil =>
      simp [tapeAtEncodedSplit, tapeSeparatorCells,
        logicalTapeCode_eq_map_some,
        selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape,
        selectedSegmentLogicalTapeDecoderCellShapeCleanupSourceTape,
        FSTStatefulOptionAppendTargetTapeFromLeftWithPadding,
        canonicalPrimitiveSeqHandoffTape,
        tapeAtCells, Tape.contextLength, Tape.move,
        Tape.moveLeft, Tape.moveRight,
        statefulOptionCellsFrom_length]
      lia
  | cons pad padding =>
      cases padding with
      | nil =>
          simp [tapeAtEncodedSplit, tapeSeparatorCells,
            logicalTapeCode_eq_map_some,
            selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape,
            selectedSegmentLogicalTapeDecoderCellShapeCleanupSourceTape,
            FSTStatefulOptionAppendTargetTapeFromLeftWithPadding,
            canonicalPrimitiveSeqHandoffTape,
            tapeAtCells, Tape.contextLength, Tape.move,
            Tape.moveLeft, Tape.moveRight,
            statefulOptionCellsFrom_length]
          lia
      | cons next padding =>
          simp [tapeAtEncodedSplit, tapeSeparatorCells,
            logicalTapeCode_eq_map_some,
            selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape,
            selectedSegmentLogicalTapeDecoderCellShapeCleanupSourceTape,
            FSTStatefulOptionAppendTargetTapeFromLeftWithPadding,
            canonicalPrimitiveSeqHandoffTape,
            tapeAtCells, Tape.contextLength, Tape.move,
            Tape.moveLeft, Tape.moveRight,
            statefulOptionCellsFrom_length]
          lia

/--
Context-length guard for the selected-head representative output.

The proof is part of the representative cleanup closure work; it should be
proved before concrete transition-table closure starts.
-/
theorem structuredSelectedHeadSegmentDecoderRepresentativeOutputTape_contextLength_ge_source
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    Tape.contextLength
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells (guardLogicalTape target :: rest))) <=
      Tape.contextLength
        (structuredSelectedHeadSegmentDecoderRepresentativeOutputTape
          target rest encodedPrefix) := by
  have hsource :
      Tape.contextLength
          (tapeAtEncodedSplit encodedPrefix
            (encodedStructuredTapeCells (guardLogicalTape target :: rest))) <=
        Tape.contextLength
          (canonicalPrimitiveSeqHandoffTape
            (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
              target (selectedSegmentLogicalTapeDecoderRestPadding rest)
              encodedPrefix)) := by
    change Tape.contextLength
        (tapeAtEncodedSplit encodedPrefix
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode (guardLogicalTape target))
              (encodedStructuredTapeCells rest)))) <= _
    rw [encodedStructuredTapeCells_eq_none_cons_restPadding rest]
    simpa [tapeSeparatorCells] using
      selectedSegmentLogicalTapeDecoderSource_contextLength_le_handoff
        target (selectedSegmentLogicalTapeDecoderRestPadding rest)
        encodedPrefix
  have hhandoff :
      Tape.contextLength
          (canonicalPrimitiveSeqHandoffTape
            (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
              target (selectedSegmentLogicalTapeDecoderRestPadding rest)
              encodedPrefix)) <=
        Tape.contextLength
          (selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape
            target (selectedSegmentLogicalTapeDecoderRestPadding rest)
            encodedPrefix) :=
    selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape_contextLength_ge_handoff
      target (selectedSegmentLogicalTapeDecoderRestPadding rest) encodedPrefix
  exact Nat.le_trans hsource (by
    simpa [structuredSelectedHeadSegmentDecoderRepresentativeOutputTape] using
      hhandoff)

/--
Exact selected-head decoder behavior to a representative output tape.
-/
structure StructuredSelectedHeadSegmentDecoderRepresentativeSpec
    (decoder : MachineDescription) : Prop where
  subroutineReady : decoder.SubroutineReady
  forward :
    forall (target : Tape Bool) (rest : List (Tape Bool))
      (encodedPrefix : List (Option Bool)),
      decoder.HaltsFromTape
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells (guardLogicalTape target :: rest)))
        (structuredSelectedHeadSegmentDecoderRepresentativeOutputTape
          target rest encodedPrefix)
  closedRepresentative :
    forall (target : Tape Bool) (rest : List (Tape Bool))
      (encodedPrefix : List (Option Bool)),
      ExactClosedFromTape decoder
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells (guardLogicalTape target :: rest)))
        (structuredSelectedHeadSegmentDecoderRepresentativeOutputTape
          target rest encodedPrefix)
  outputEquiv :
    forall (target : Tape Bool) (rest : List (Tape Bool))
      (encodedPrefix : List (Option Bool)),
      Tape.Equiv
        (structuredSelectedHeadSegmentDecoderRepresentativeOutputTape
          target rest encodedPrefix)
        target

def StructuredSelectedHeadSegmentDecoderRepresentativeConstruction :
    Prop :=
  exists decoder : MachineDescription,
    StructuredSelectedHeadSegmentDecoderRepresentativeSpec decoder

namespace StructuredSelectedHeadSegmentDecoderRepresentativeSpec

theorem toSpec
    {decoder : MachineDescription}
    (hdecoder :
      StructuredSelectedHeadSegmentDecoderRepresentativeSpec decoder) :
    StructuredSelectedHeadSegmentDecoderSpec decoder := by
  constructor
  · exact hdecoder.subroutineReady
  · intro target rest encodedPrefix
    exact
      ⟨structuredSelectedHeadSegmentDecoderRepresentativeOutputTape
          target rest encodedPrefix,
        hdecoder.forward target rest encodedPrefix,
        hdecoder.outputEquiv target rest encodedPrefix⟩

end StructuredSelectedHeadSegmentDecoderRepresentativeSpec

theorem structuredSelectedHeadSegmentDecoderConstruction_of_representative
    (hdecoder :
      StructuredSelectedHeadSegmentDecoderRepresentativeConstruction) :
    StructuredSelectedHeadSegmentDecoderConstruction := by
  rcases hdecoder with ⟨decoder, hdecoderSpec⟩
  exact ⟨decoder, hdecoderSpec.toSpec⟩

theorem selectedSegmentLogicalTapeDecoderHeadPipeline_haltsFrom_representativeCleanupSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupSpec
        cleanup)
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderHeadPipelineDescription
      cleanup).HaltsFromTape
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells (guardLogicalTape target :: rest)))
        (structuredSelectedHeadSegmentDecoderRepresentativeOutputTape
          target rest encodedPrefix) := by
  let source :=
    tapeAtEncodedSplit encodedPrefix
      (encodedStructuredTapeCells (guardLogicalTape target :: rest))
  let moved := Tape.move Direction.right source
  let scanned :=
    selectedSegmentLogicalTapeDecoderHeadTargetTape
      target rest encodedPrefix
  let output :=
    structuredSelectedHeadSegmentDecoderRepresentativeOutputTape
      target rest encodedPrefix
  have hmove :
      (cursorMoveOnceDescription Direction.right).HaltsFromTape
        source moved := by
    exact cursorMoveOnceDescription_haltsFromTape Direction.right source
  have hscanMoved :
      selectedSegmentLogicalTapeDecoderDescription.HaltsFromTape
        moved scanned := by
    simpa [source, moved, scanned] using
      selectedSegmentLogicalTapeDecoderDescription_haltsFrom_selectedHeadPayload
        target rest encodedPrefix
  have hmoved :
      canonicalPrimitiveSeqHandoffTape moved = moved := by
    simpa [source, moved] using
      canonicalPrimitiveSeqHandoffTape_selectedHeadAfterMove
        target rest encodedPrefix
  have hscan :
      selectedSegmentLogicalTapeDecoderDescription.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape moved)
        scanned := by
    rw [hmoved]
    exact hscanMoved
  have hpipelineScan :
      (canonicalPrimitiveSeqDescription
        (cursorMoveOnceDescription Direction.right)
        selectedSegmentLogicalTapeDecoderDescription).HaltsFromTape
          source scanned :=
    canonicalPrimitiveSeqDescription_haltsFromTape_exact
      (cursorMoveOnceDescription_subroutineReady Direction.right)
      selectedSegmentLogicalTapeDecoderDescription_subroutineReady
      hmove hscan
  have hcleanupRun :
      cleanup.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape scanned)
        output := by
    simpa [scanned, output,
      structuredSelectedHeadSegmentDecoderRepresentativeOutputTape,
      selectedSegmentLogicalTapeDecoderHeadTargetTape_eq_paddedCleanupSourceTape] using
      hcleanup.forward target
        (selectedSegmentLogicalTapeDecoderRestPadding rest)
        encodedPrefix
  simpa [
    selectedSegmentLogicalTapeDecoderHeadPipelineDescription,
    selectedSegmentLogicalTapeDecoderPipelineDescription,
    source, scanned, output] using
    canonicalPrimitiveSeqDescription_haltsFromTape_exact
      (canonicalPrimitiveSeqDescription_subroutineReady
        (cursorMoveOnceDescription_subroutineReady Direction.right)
        selectedSegmentLogicalTapeDecoderDescription_subroutineReady)
      hcleanup.subroutineReady
      hpipelineScan
      hcleanupRun

theorem structuredSelectedHeadSegmentDecoderRepresentativeSpec_of_representativeCleanupSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupSpec
        cleanup) :
    StructuredSelectedHeadSegmentDecoderRepresentativeSpec
      (selectedSegmentLogicalTapeDecoderHeadPipelineDescription cleanup) where
  subroutineReady :=
    selectedSegmentLogicalTapeDecoderHeadPipelineDescription_subroutineReady
      hcleanup.subroutineReady
  forward :=
    selectedSegmentLogicalTapeDecoderHeadPipeline_haltsFrom_representativeCleanupSpec
      hcleanup
  closedRepresentative := by
    intro target rest encodedPrefix
    exact
      exactClosedFromTape_of_haltsFromTape_of_subroutineReady
        (selectedSegmentLogicalTapeDecoderHeadPipelineDescription_subroutineReady
          hcleanup.subroutineReady)
        (selectedSegmentLogicalTapeDecoderHeadPipeline_haltsFrom_representativeCleanupSpec
          hcleanup target rest encodedPrefix)
  outputEquiv :=
    structuredSelectedHeadSegmentDecoderRepresentativeOutputTape_equiv

theorem structuredSelectedHeadSegmentDecoderRepresentativeConstruction_of_representativeCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupConstruction) :
    StructuredSelectedHeadSegmentDecoderRepresentativeConstruction := by
  rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
  exact
    ⟨selectedSegmentLogicalTapeDecoderHeadPipelineDescription cleanup,
      structuredSelectedHeadSegmentDecoderRepresentativeSpec_of_representativeCleanupSpec
        hcleanupSpec⟩

/--
Representative output for tape-2 segment normalization at an already selected
separator.
-/
def structuredTape2RepresentativeSegmentOutputTape
    (T0 T1 T2 _physical : Tape Bool) : Tape Bool :=
  structuredSelectedHeadSegmentDecoderRepresentativeOutputTape
    T2 []
    (encodedPrefixBeforeTape (guardLogicalTapes [T0, T1, T2]) 2)

theorem structuredTape2RepresentativeSegmentOutputTape_equiv
    (T0 T1 T2 physical : Tape Bool) :
    Tape.Equiv
      (structuredTape2RepresentativeSegmentOutputTape T0 T1 T2 physical)
      T2 := by
  simpa [structuredTape2RepresentativeSegmentOutputTape] using
    structuredSelectedHeadSegmentDecoderRepresentativeOutputTape_equiv
      T2 []
      (encodedPrefixBeforeTape (guardLogicalTapes [T0, T1, T2]) 2)

theorem structuredTape2RepresentativeSegmentOutputTape_contextLength_ge_source
    (T0 T1 T2 physical : Tape Bool)
    (hseparator :
      AtTapeSeparator (guardLogicalTapes [T0, T1, T2]) 2 physical) :
    Tape.contextLength physical <=
      Tape.contextLength
        (structuredTape2RepresentativeSegmentOutputTape
          T0 T1 T2 physical) := by
  rw [hseparator.2]
  simpa [structuredTape2RepresentativeSegmentOutputTape,
    encodedSuffixFromTape] using
    structuredSelectedHeadSegmentDecoderRepresentativeOutputTape_contextLength_ge_source
      T2 [] (encodedPrefixBeforeTape (guardLogicalTapes [T0, T1, T2]) 2)

structure StructuredTape2RepresentativeSegmentNormalizerSpec
    (normalizer : MachineDescription) : Prop where
  subroutineReady : normalizer.SubroutineReady
  forward :
    forall (T0 T1 T2 physical : Tape Bool),
      AtTapeSeparator (guardLogicalTapes [T0, T1, T2]) 2 physical ->
        normalizer.HaltsFromTape physical
          (structuredTape2RepresentativeSegmentOutputTape
            T0 T1 T2 physical)
  closedRepresentative :
    forall (T0 T1 T2 physical : Tape Bool),
      AtTapeSeparator (guardLogicalTapes [T0, T1, T2]) 2 physical ->
        ExactClosedFromTape normalizer physical
          (structuredTape2RepresentativeSegmentOutputTape
            T0 T1 T2 physical)
  outputEquiv :
    forall (T0 T1 T2 physical : Tape Bool),
      AtTapeSeparator (guardLogicalTapes [T0, T1, T2]) 2 physical ->
        Tape.Equiv
          (structuredTape2RepresentativeSegmentOutputTape
            T0 T1 T2 physical)
          T2

def StructuredTape2RepresentativeSegmentNormalizerConstruction :
    Prop :=
  exists normalizer : MachineDescription,
    StructuredTape2RepresentativeSegmentNormalizerSpec normalizer

namespace StructuredTape2RepresentativeSegmentNormalizerSpec

theorem toSegmentNormalizerSpec
    {normalizer : MachineDescription}
    (hnormalizer :
      StructuredTape2RepresentativeSegmentNormalizerSpec normalizer) :
    StructuredTape2SegmentNormalizerSpec normalizer := by
  constructor
  · exact hnormalizer.subroutineReady
  · intro T0 T1 T2 physical hseparator
    exact
      ⟨structuredTape2RepresentativeSegmentOutputTape
          T0 T1 T2 physical,
        hnormalizer.forward T0 T1 T2 physical hseparator,
        hnormalizer.outputEquiv T0 T1 T2 physical hseparator⟩

end StructuredTape2RepresentativeSegmentNormalizerSpec

theorem structuredTape2SegmentNormalizerConstruction_of_representative
    (hnormalizer :
      StructuredTape2RepresentativeSegmentNormalizerConstruction) :
    StructuredTape2SegmentNormalizerConstruction := by
  rcases hnormalizer with ⟨normalizer, hnormalizerSpec⟩
  exact ⟨normalizer, hnormalizerSpec.toSegmentNormalizerSpec⟩

theorem structuredTape2RepresentativeSegmentNormalizerConstruction_of_selectedHeadRepresentativeDecoder
    (hdecoder :
      StructuredSelectedHeadSegmentDecoderRepresentativeConstruction) :
    StructuredTape2RepresentativeSegmentNormalizerConstruction := by
  rcases hdecoder with ⟨decoder, hdecoderSpec⟩
  refine ⟨decoder, ?_⟩
  constructor
  · exact hdecoderSpec.subroutineReady
  · intro T0 T1 T2 physical hseparator
    rcases hseparator with ⟨_hindex, hphysical⟩
    rw [hphysical]
    simpa [encodedSuffixFromTape, guardLogicalTapes,
      structuredTape2RepresentativeSegmentOutputTape] using
      hdecoderSpec.forward T2 []
        (encodedPrefixBeforeTape (guardLogicalTapes [T0, T1, T2]) 2)
  · intro T0 T1 T2 physical hseparator
    exact
      exactClosedFromTape_of_haltsFromTape_of_subroutineReady
        hdecoderSpec.subroutineReady
        (by
          rcases hseparator with ⟨_hindex, hphysical⟩
          rw [hphysical]
          simpa [encodedSuffixFromTape, guardLogicalTapes,
            structuredTape2RepresentativeSegmentOutputTape] using
            hdecoderSpec.forward T2 []
              (encodedPrefixBeforeTape
                (guardLogicalTapes [T0, T1, T2]) 2))
  · intro T0 T1 T2 physical hseparator
    exact
      structuredTape2RepresentativeSegmentOutputTape_equiv
        T0 T1 T2 physical

/-- Representative output for the public tape-2 projector. -/
def structuredTape2RepresentativeProjectorOutputTape
    (T0 T1 T2 : Tape Bool) : Tape Bool :=
  structuredSelectedHeadSegmentDecoderRepresentativeOutputTape
    T2 []
    (encodedPrefixBeforeTape (guardLogicalTapes [T0, T1, T2]) 2)

theorem structuredTape2RepresentativeProjectorOutputTape_equiv
    (T0 T1 T2 : Tape Bool) :
    Tape.Equiv
      (structuredTape2RepresentativeProjectorOutputTape T0 T1 T2)
      T2 := by
  simpa [structuredTape2RepresentativeProjectorOutputTape] using
    structuredSelectedHeadSegmentDecoderRepresentativeOutputTape_equiv
      T2 []
      (encodedPrefixBeforeTape (guardLogicalTapes [T0, T1, T2]) 2)

structure StructuredTape2RepresentativeProjectorSpec
    (projector : MachineDescription) : Prop where
  subroutineReady : projector.SubroutineReady
  forward :
    forall T0 T1 T2 : Tape Bool,
      projector.HaltsFromTape
        (encodedGuardedStructured3Tapes T0 T1 T2)
        (structuredTape2RepresentativeProjectorOutputTape T0 T1 T2)
  closedRepresentative :
    forall T0 T1 T2 : Tape Bool,
      ExactClosedFromTape projector
        (encodedGuardedStructured3Tapes T0 T1 T2)
        (structuredTape2RepresentativeProjectorOutputTape T0 T1 T2)
  outputEquiv :
    forall T0 T1 T2 : Tape Bool,
      Tape.Equiv
        (structuredTape2RepresentativeProjectorOutputTape T0 T1 T2)
        T2

def StructuredTape2RepresentativeProjectorConstruction : Prop :=
  exists projector : MachineDescription,
    StructuredTape2RepresentativeProjectorSpec projector

namespace StructuredTape2RepresentativeProjectorSpec

theorem toProjectorSpec
    {projector : MachineDescription}
    (hprojector :
      StructuredTape2RepresentativeProjectorSpec projector) :
    StructuredTape2ProjectorSpec projector := by
  constructor
  · exact hprojector.subroutineReady
  · intro T0 T1 T2
    exact
      ⟨structuredTape2RepresentativeProjectorOutputTape T0 T1 T2,
        hprojector.forward T0 T1 T2,
        hprojector.outputEquiv T0 T1 T2⟩

end StructuredTape2RepresentativeProjectorSpec

theorem structuredTape2ProjectorConstruction_of_representative
    (hprojector :
      StructuredTape2RepresentativeProjectorConstruction) :
    StructuredTape2ProjectorConstruction := by
  rcases hprojector with ⟨projector, hprojectorSpec⟩
  exact ⟨projector, hprojectorSpec.toProjectorSpec⟩

theorem selectedSegmentLogicalTapeDecoderHeadCleanupConstruction_of_representative
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupConstruction) :
    SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction :=
  selectedSegmentLogicalTapeDecoderHeadCleanupConstruction_of_paddedCleanup
    (selectedSegmentLogicalTapeDecoderPaddedCleanupConstruction_of_representative
      hcleanup)

theorem structuredSelectedHeadDecoderRouteConstruction_of_representativeCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupConstruction) :
    StructuredSelectedHeadDecoderRouteConstruction :=
  structuredSelectedHeadDecoderRouteConstruction_of_headCleanup
    (selectedSegmentLogicalTapeDecoderHeadCleanupConstruction_of_representative
      hcleanup)

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
