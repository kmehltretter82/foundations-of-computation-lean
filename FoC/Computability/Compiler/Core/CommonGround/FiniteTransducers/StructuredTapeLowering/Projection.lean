import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.CursorSeek

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
          simpa [encodedGuardedStructured3Tapes] using
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
      · simpa [encodedGuardedStructured3Tapes] using
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
Generic extractor for a selected singleton structured segment.

The cursor is at the selected segment separator, any encoded prefix to the left
is ignored by the contract, and the selected guarded singleton segment is
projected back to the original plain logical tape.
-/
def StructuredSelectedSingletonSegmentExtractorSpec
    (extractor : MachineDescription) : Prop :=
  extractor.SubroutineReady ∧
    forall (target : Tape Bool) (encodedPrefix : List (Option Bool)),
      extractor.HaltsFromTapeEquiv
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells [guardLogicalTape target]))
        target

/--
Existence wrapper for
{name}`StructuredSelectedSingletonSegmentExtractorSpec`.
-/
def StructuredSelectedSingletonSegmentExtractorConstruction : Prop :=
  exists extractor : MachineDescription,
    StructuredSelectedSingletonSegmentExtractorSpec extractor

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

theorem structuredSelectedSingletonSegmentExtractorConstruction_core :
    StructuredSelectedSingletonSegmentExtractorConstruction := by
  sorry

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
