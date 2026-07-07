import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.ProjectionHeadRoutes.ExactCleanup

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

/--
Legacy literal selected-head decoder behavior.

This is stronger than {name}`StructuredSelectedHeadSegmentDecoderSpec` and is
over-strong for arbitrary public targets.  Public endpoint code should use the
representative/equivalence-facing selected-head route instead of depending on
this as a construction target.
-/
structure StructuredSelectedHeadSegmentDecoderExactSpec
    (decoder : MachineDescription) : Prop where
  subroutineReady : decoder.SubroutineReady
  forward :
    forall (target : Tape Bool) (rest : List (Tape Bool))
      (encodedPrefix : List (Option Bool)),
      decoder.HaltsFromTape
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells (guardLogicalTape target :: rest)))
        target
  closed :
    forall (target : Tape Bool) (rest : List (Tape Bool))
      (encodedPrefix : List (Option Bool)),
      ExactClosedFromTape decoder
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells (guardLogicalTape target :: rest)))
        target

/-- Existence wrapper for literal selected-head decoder behavior. -/
def StructuredSelectedHeadSegmentDecoderExactConstruction : Prop :=
  exists decoder : MachineDescription,
    StructuredSelectedHeadSegmentDecoderExactSpec decoder

namespace StructuredSelectedHeadSegmentDecoderExactSpec

/-- Literal selected-head decoding implies the existing equivalence route. -/
theorem toSpec
    {decoder : MachineDescription}
    (hdecoder :
      StructuredSelectedHeadSegmentDecoderExactSpec decoder) :
    StructuredSelectedHeadSegmentDecoderSpec decoder := by
  constructor
  · exact hdecoder.subroutineReady
  · intro target rest encodedPrefix
    exact (hdecoder.forward target rest encodedPrefix).toEquiv

end StructuredSelectedHeadSegmentDecoderExactSpec

/--
Construction-level adapter from literal selected-head decoding to the existing
equivalence selected-head decoder construction.
-/
theorem structuredSelectedHeadSegmentDecoderConstruction_of_exact
    (hdecoder :
      StructuredSelectedHeadSegmentDecoderExactConstruction) :
    StructuredSelectedHeadSegmentDecoderConstruction := by
  rcases hdecoder with ⟨decoder, hdecoderSpec⟩
  exact
    ⟨decoder,
      hdecoderSpec.toSpec⟩

/--
Legacy literal tape-2 segment normalizer behavior at an already-selected
segment.
-/
structure StructuredTape2ExactSegmentNormalizerSpec
    (normalizer : MachineDescription) : Prop where
  subroutineReady : normalizer.SubroutineReady
  forward :
    forall (T0 T1 T2 : Tape Bool) (physical : Tape Bool),
      AtTapeSeparator (guardLogicalTapes [T0, T1, T2]) 2 physical ->
        normalizer.HaltsFromTape physical T2
  closed :
    forall (T0 T1 T2 : Tape Bool) (physical : Tape Bool),
      AtTapeSeparator (guardLogicalTapes [T0, T1, T2]) 2 physical ->
        ExactClosedFromTape normalizer physical T2

/-- Existence wrapper for literal tape-2 segment normalization. -/
def StructuredTape2ExactSegmentNormalizerConstruction : Prop :=
  exists normalizer : MachineDescription,
    StructuredTape2ExactSegmentNormalizerSpec normalizer

namespace StructuredTape2ExactSegmentNormalizerSpec

/-- Literal tape-2 segment normalization implies the equivalence normalizer. -/
theorem toSegmentNormalizerSpec
    {normalizer : MachineDescription}
    (hnormalizer :
      StructuredTape2ExactSegmentNormalizerSpec normalizer) :
    StructuredTape2SegmentNormalizerSpec normalizer := by
  constructor
  · exact hnormalizer.subroutineReady
  · intro T0 T1 T2 physical hseparator
    exact (hnormalizer.forward T0 T1 T2 physical hseparator).toEquiv

end StructuredTape2ExactSegmentNormalizerSpec

/--
Construction-level adapter from literal tape-2 segment normalization to the
existing equivalence segment-normalizer construction.
-/
theorem structuredTape2SegmentNormalizerConstruction_of_exact
    (hnormalizer :
      StructuredTape2ExactSegmentNormalizerConstruction) :
    StructuredTape2SegmentNormalizerConstruction := by
  rcases hnormalizer with ⟨normalizer, hnormalizerSpec⟩
  exact
    ⟨normalizer,
      hnormalizerSpec.toSegmentNormalizerSpec⟩

/--
Literal selected-head decoding gives literal tape-2 segment normalization.
-/
theorem structuredTape2ExactSegmentNormalizerConstruction_of_exactHeadDecoder
    (hdecoder :
      StructuredSelectedHeadSegmentDecoderExactConstruction) :
    StructuredTape2ExactSegmentNormalizerConstruction := by
  rcases hdecoder with ⟨decoder, hdecoderSpec⟩
  refine ⟨decoder, ?_⟩
  constructor
  · exact hdecoderSpec.subroutineReady
  · intro T0 T1 T2 physical hseparator
    rcases hseparator with ⟨_hindex, hphysical⟩
    rw [hphysical]
    simpa [encodedSuffixFromTape, guardLogicalTapes] using
      hdecoderSpec.forward T2 []
        (encodedPrefixBeforeTape (guardLogicalTapes [T0, T1, T2]) 2)
  · intro T0 T1 T2 physical hseparator
    rcases hseparator with ⟨_hindex, hphysical⟩
    intro T hhalt
    exact
      hdecoderSpec.closed T2 []
        (encodedPrefixBeforeTape (guardLogicalTapes [T0, T1, T2]) 2)
        T
        (by
          rw [hphysical] at hhalt
          simpa [encodedSuffixFromTape, guardLogicalTapes] using hhalt)

/--
The endpoint handoff bounce is exact on the canonical guarded three-tape
encoding. The encoded block starts with a separator and has a nonempty right
side, so moving right and then left restores the same physical tape literally.
-/
theorem canonicalPrimitiveSeqHandoffTape_encodedGuardedStructured3Tapes
    (T0 T1 T2 : Tape Bool) :
    canonicalPrimitiveSeqHandoffTape
        (encodedGuardedStructured3Tapes T0 T1 T2) =
      encodedGuardedStructured3Tapes T0 T1 T2 := by
  simp [canonicalPrimitiveSeqHandoffTape,
    encodedGuardedStructured3Tapes, encodedGuardedStructuredTapes,
    encodedStructuredTapes, encodedStructuredTapeCells, guardLogicalTapes,
    guardLogicalTape, tapeAtCells, tapeSeparatorCells, logicalTapeCode,
    logicalCellListBits, logicalCellBits, logicalCellCode, headMarkerCells,
    Tape.move, Tape.moveLeft, Tape.moveRight]

/--
The projector-internal handoff bounce is exact at the selected tape-2
separator of a guarded three-tape block.
-/
theorem canonicalPrimitiveSeqHandoffTape_eq_self_of_atTape2Separator
    {T0 T1 T2 physical : Tape Bool}
    (hseparator :
      AtTapeSeparator (guardLogicalTapes [T0, T1, T2]) 2 physical) :
    canonicalPrimitiveSeqHandoffTape physical = physical := by
  rcases hseparator with ⟨_hindex, hphysical⟩
  rw [hphysical]
  simp [canonicalPrimitiveSeqHandoffTape, tapeAtEncodedSplit,
    encodedSuffixFromTape, guardLogicalTapes, guardLogicalTape,
    encodedStructuredTapeCells, tapeAtCells, tapeSeparatorCells,
    logicalTapeCode, logicalCellListBits, logicalCellBits, logicalCellCode,
    headMarkerCells, Tape.move, Tape.moveLeft, Tape.moveRight]

/--
Exact segment-normalizer behavior as a right-hand component of the canonical
tape-2 projector sequence.

The normalizer input is the canonical sequence handoff tape for the separator,
not merely the separator tape itself. This is the exact contract needed by
{name}`canonicalPrimitiveSeqDescription_exactClosedFromTape`.
-/
structure StructuredTape2ExactHandoffSegmentNormalizerSpec
    (normalizer : MachineDescription) : Prop where
  subroutineReady : normalizer.SubroutineReady
  forward :
    forall (T0 T1 T2 : Tape Bool) (physical : Tape Bool),
      AtTapeSeparator (guardLogicalTapes [T0, T1, T2]) 2 physical ->
        normalizer.HaltsFromTape
          (canonicalPrimitiveSeqHandoffTape physical)
          T2
  closed :
    forall (T0 T1 T2 : Tape Bool) (physical : Tape Bool),
      AtTapeSeparator (guardLogicalTapes [T0, T1, T2]) 2 physical ->
        ExactClosedFromTape normalizer
          (canonicalPrimitiveSeqHandoffTape physical)
          T2

/-- Existence wrapper for the exact handoff-facing tape-2 normalizer. -/
def StructuredTape2ExactHandoffSegmentNormalizerConstruction : Prop :=
  exists normalizer : MachineDescription,
    StructuredTape2ExactHandoffSegmentNormalizerSpec normalizer

namespace StructuredTape2ExactHandoffSegmentNormalizerSpec

/--
The handoff-facing exact normalizer still implies the existing equivalence
segment-normalizer contract.
-/
theorem toSegmentNormalizerSpec
    {normalizer : MachineDescription}
    (hnormalizer :
      StructuredTape2ExactHandoffSegmentNormalizerSpec normalizer) :
    StructuredTape2SegmentNormalizerSpec normalizer := by
  constructor
  · exact hnormalizer.subroutineReady
  · intro T0 T1 T2 physical hseparator
    exact
      HaltsFromTapeEquiv_of_input_equiv
        (D := normalizer)
        (Tin := canonicalPrimitiveSeqHandoffTape physical)
        (Tin' := physical)
        (Tout := T2)
        (canonicalPrimitiveSeqHandoffTape_equiv physical)
        (hnormalizer.forward T0 T1 T2 physical hseparator)

end StructuredTape2ExactHandoffSegmentNormalizerSpec

/--
At the concrete tape-2 separator shape, a direct exact normalizer can be used
as the right-hand component of the canonical projector sequence.
-/
theorem structuredTape2ExactHandoffSegmentNormalizerSpec_of_exact
    {normalizer : MachineDescription}
    (hnormalizer :
      StructuredTape2ExactSegmentNormalizerSpec normalizer) :
    StructuredTape2ExactHandoffSegmentNormalizerSpec normalizer := by
  constructor
  · exact hnormalizer.subroutineReady
  · intro T0 T1 T2 physical hseparator
    rw [canonicalPrimitiveSeqHandoffTape_eq_self_of_atTape2Separator
      hseparator]
    exact hnormalizer.forward T0 T1 T2 physical hseparator
  · intro T0 T1 T2 physical hseparator
    intro T hhalt
    exact
      hnormalizer.closed T0 T1 T2 physical hseparator T
        (by
          simpa [canonicalPrimitiveSeqHandoffTape_eq_self_of_atTape2Separator
            hseparator] using hhalt)

/--
Construction-level adapter from direct exact tape-2 segment normalization to
the handoff-facing exact segment-normalizer contract.
-/
theorem structuredTape2ExactHandoffSegmentNormalizerConstruction_of_exact
    (hnormalizer :
      StructuredTape2ExactSegmentNormalizerConstruction) :
    StructuredTape2ExactHandoffSegmentNormalizerConstruction := by
  rcases hnormalizer with ⟨normalizer, hnormalizerSpec⟩
  exact
    ⟨normalizer,
      structuredTape2ExactHandoffSegmentNormalizerSpec_of_exact
        hnormalizerSpec⟩

/--
Exact selected-head decoding supplies the handoff-facing tape-2 segment
normalizer needed by the exact projector route.
-/
theorem structuredTape2ExactHandoffSegmentNormalizerConstruction_of_exactHeadDecoder
    (hdecoder :
      StructuredSelectedHeadSegmentDecoderExactConstruction) :
    StructuredTape2ExactHandoffSegmentNormalizerConstruction :=
  structuredTape2ExactHandoffSegmentNormalizerConstruction_of_exact
    (structuredTape2ExactSegmentNormalizerConstruction_of_exactHeadDecoder
      hdecoder)

/--
Exact run of the tape-2 seeker from the endpoint-bounced guarded three-tape
encoding.
-/
theorem seekTape2Description_haltsFrom_endpointHandoff
    (T0 T1 T2 : Tape Bool) :
    exists physical : Tape Bool,
      seekTape2Description.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape
          (encodedGuardedStructured3Tapes T0 T1 T2))
        physical ∧
        AtTapeSeparator (guardLogicalTapes [T0, T1, T2]) 2 physical := by
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
    ⟨physical, hseek, hseparator⟩
  refine ⟨physical, ?_, hseparator⟩
  simpa [canonicalPrimitiveSeqHandoffTape_encodedGuardedStructured3Tapes]
    using hseek

/--
Legacy exact tape-2 projector contract.

The input is the endpoint handoff tape because the projector is itself the
right-hand component of the three-part endpoint wrapper.  This literal target
shape is over-strong for the public selected-head route; endpoint code should
use {name}`StructuredTape2ProjectorSpec` or representative wrappers.
-/
structure StructuredTape2ExactProjectorSpec
    (projector : MachineDescription) : Prop where
  subroutineReady : projector.SubroutineReady
  forward :
    forall T0 T1 T2 : Tape Bool,
      projector.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape
          (encodedGuardedStructured3Tapes T0 T1 T2))
        T2
  closed :
    forall T0 T1 T2 : Tape Bool,
      ExactClosedFromTape projector
        (canonicalPrimitiveSeqHandoffTape
          (encodedGuardedStructured3Tapes T0 T1 T2))
        T2

/-- Existence wrapper for {name}`StructuredTape2ExactProjectorSpec`. -/
def StructuredTape2ExactProjectorConstruction : Prop :=
  exists projector : MachineDescription,
    StructuredTape2ExactProjectorSpec projector

namespace StructuredTape2ExactProjectorSpec

/-- Exact tape-2 projection implies the existing equivalence projector route. -/
theorem toProjectorSpec
    {projector : MachineDescription}
    (hprojector :
      StructuredTape2ExactProjectorSpec projector) :
    StructuredTape2ProjectorSpec projector := by
  constructor
  · exact hprojector.subroutineReady
  · intro T0 T1 T2
    have hforward := hprojector.forward T0 T1 T2
    rw [canonicalPrimitiveSeqHandoffTape_encodedGuardedStructured3Tapes]
      at hforward
    exact hforward.toEquiv

end StructuredTape2ExactProjectorSpec

/--
Lift a handoff-facing exact tape-2 segment normalizer through the tape-2
seeker to obtain the endpoint-facing exact tape-2 projector.
-/
theorem structuredTape2ExactProjectorSpec_of_handoffSegmentNormalizerSpec
    {normalizer : MachineDescription}
    (hnormalizer :
      StructuredTape2ExactHandoffSegmentNormalizerSpec normalizer) :
    StructuredTape2ExactProjectorSpec
      (structuredTape2ProjectorDescription normalizer) := by
  constructor
  · exact
      structuredTape2ProjectorDescription_subroutineReady
        hnormalizer.subroutineReady
  · intro T0 T1 T2
    rcases seekTape2Description_haltsFrom_endpointHandoff T0 T1 T2 with
      ⟨physical, hseek, hseparator⟩
    exact
      canonicalPrimitiveSeqDescription_haltsFromTape_exact
        seekTape2Description_subroutineReady
        hnormalizer.subroutineReady
        hseek
        (hnormalizer.forward T0 T1 T2 physical hseparator)
  · intro T0 T1 T2
    rcases seekTape2Description_haltsFrom_endpointHandoff T0 T1 T2 with
      ⟨physical, hseek, hseparator⟩
    exact
      canonicalPrimitiveSeqDescription_exactClosedFromTape
        seekTape2Description_subroutineReady
        hnormalizer.subroutineReady
        (by
          intro T hhalt
          exact
            MachineDescription.haltsFromTape_functional_of_haltTransitionFree
              seekTape2Description_subroutineReady.right hhalt hseek)
        (hnormalizer.closed T0 T1 T2 physical hseparator)

/--
Construction-level exact tape-2 projector from a handoff-facing exact segment
normalizer.
-/
theorem structuredTape2ExactProjectorConstruction_of_handoffSegmentNormalizerConstruction
    (hnormalizer :
      StructuredTape2ExactHandoffSegmentNormalizerConstruction) :
    StructuredTape2ExactProjectorConstruction := by
  rcases hnormalizer with ⟨normalizer, hnormalizerSpec⟩
  exact
    ⟨structuredTape2ProjectorDescription normalizer,
      structuredTape2ExactProjectorSpec_of_handoffSegmentNormalizerSpec
        hnormalizerSpec⟩

/--
Construction-level exact tape-2 projector from a direct exact segment
normalizer.
-/
theorem structuredTape2ExactProjectorConstruction_of_exactSegmentNormalizerConstruction
    (hnormalizer :
      StructuredTape2ExactSegmentNormalizerConstruction) :
    StructuredTape2ExactProjectorConstruction :=
  structuredTape2ExactProjectorConstruction_of_handoffSegmentNormalizerConstruction
    (structuredTape2ExactHandoffSegmentNormalizerConstruction_of_exact
      hnormalizer)

/--
Exact selected-head decoding supplies the endpoint-facing exact tape-2
projector.
-/
theorem structuredTape2ExactProjectorConstruction_of_exactHeadDecoder
    (hdecoder :
      StructuredSelectedHeadSegmentDecoderExactConstruction) :
    StructuredTape2ExactProjectorConstruction :=
  structuredTape2ExactProjectorConstruction_of_exactSegmentNormalizerConstruction
    (structuredTape2ExactSegmentNormalizerConstruction_of_exactHeadDecoder
      hdecoder)

/--
Construction-level adapter from the exact tape-2 projector to the existing
equivalence projector route.
-/
theorem structuredTape2ProjectorConstruction_of_exact
    (hprojector :
      StructuredTape2ExactProjectorConstruction) :
    StructuredTape2ProjectorConstruction := by
  rcases hprojector with ⟨projector, hprojectorSpec⟩
  exact ⟨projector, hprojectorSpec.toProjectorSpec⟩

theorem selectedSegmentLogicalTapeDecoderHeadCleanupSpec_of_paddedCleanupSpec
    {cleanup : MachineDescription}
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedCleanupSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderHeadCleanupSpec cleanup := by
  rcases hcleanup with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro target rest encodedPrefix
  simpa [
    selectedSegmentLogicalTapeDecoderHeadTargetTape_eq_paddedCleanupSourceTape] using
    hrun target (selectedSegmentLogicalTapeDecoderRestPadding rest)
      encodedPrefix

theorem selectedSegmentLogicalTapeDecoderHeadCleanupConstruction_of_paddedCleanup
    (hcleanup :
      SelectedSegmentLogicalTapeDecoderPaddedCleanupConstruction) :
    SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction := by
  rcases hcleanup with ⟨cleanup, hspec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderHeadCleanupSpec_of_paddedCleanupSpec
        hspec⟩

/-- Singleton cleanup follows from padded selected-head cleanup. -/
theorem selectedSegmentLogicalTapeDecoderCleanupSpec_of_headCleanupSpec
    {cleanup : MachineDescription}
    (hcleanup : SelectedSegmentLogicalTapeDecoderHeadCleanupSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderCleanupSpec cleanup := by
  constructor
  · exact hcleanup.left
  · intro target encodedPrefix
    simpa [selectedSegmentLogicalTapeDecoderHeadTargetTape_nil] using
      hcleanup.right target [] encodedPrefix

/-- Construction-level singleton cleanup adapter. -/
theorem selectedSegmentLogicalTapeDecoderCleanupConstruction_of_headCleanup
    (hcleanup : SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    SelectedSegmentLogicalTapeDecoderCleanupConstruction := by
  rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderCleanupSpec_of_headCleanupSpec
        hcleanupSpec⟩

/--
The converse is intentionally absent.  Singleton cleanup does not know how to
discard or preserve arbitrary encoded structured suffixes after the selected
segment.
-/
def SelectedSegmentLogicalTapeDecoderHeadCleanupNilRestSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderHeadTargetTape
          target [] encodedPrefix)
        target

/--
Cleanup branch where the selected segment is followed by at least one encoded
structured tape.
-/
def SelectedSegmentLogicalTapeDecoderHeadCleanupConsRestSpec
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target next : Tape Bool) (rest : List (Tape Bool))
      (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderHeadTargetTape
          target (next :: rest) encodedPrefix)
        target

/-- Branch split for padded selected-head cleanup. -/
def SelectedSegmentLogicalTapeDecoderHeadCleanupSplitSpec
    (cleanup : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderHeadCleanupNilRestSpec cleanup ∧
    SelectedSegmentLogicalTapeDecoderHeadCleanupConsRestSpec cleanup

/-- Construction wrapper for the branch-split cleanup view. -/
def SelectedSegmentLogicalTapeDecoderHeadCleanupSplitConstruction : Prop :=
  exists cleanup : MachineDescription,
    SelectedSegmentLogicalTapeDecoderHeadCleanupSplitSpec cleanup

/-- Split padded selected-head cleanup into nil-rest and cons-rest branches. -/
theorem selectedSegmentLogicalTapeDecoderHeadCleanupSplitSpec_of_spec
    {cleanup : MachineDescription}
    (hcleanup : SelectedSegmentLogicalTapeDecoderHeadCleanupSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderHeadCleanupSplitSpec cleanup := by
  constructor
  · constructor
    · exact hcleanup.left
    · intro target encodedPrefix
      exact hcleanup.right target [] encodedPrefix
  · constructor
    · exact hcleanup.left
    · intro target next rest encodedPrefix
      exact hcleanup.right target (next :: rest) encodedPrefix

/-- Reassemble padded selected-head cleanup from nil-rest and cons-rest branches. -/
theorem selectedSegmentLogicalTapeDecoderHeadCleanupSpec_of_splitSpec
    {cleanup : MachineDescription}
    (hsplit : SelectedSegmentLogicalTapeDecoderHeadCleanupSplitSpec cleanup) :
    SelectedSegmentLogicalTapeDecoderHeadCleanupSpec cleanup := by
  rcases hsplit with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilRun⟩
  rcases hcons with ⟨_hreadyCons, hconsRun⟩
  refine ⟨hready, ?_⟩
  intro target rest encodedPrefix
  cases rest with
  | nil =>
      exact hnilRun target encodedPrefix
  | cons next rest =>
      exact hconsRun target next rest encodedPrefix

/-- Construction-level split adapter from the full cleanup view. -/
theorem selectedSegmentLogicalTapeDecoderHeadCleanupSplitConstruction_of_cleanup
    (hcleanup : SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction) :
    SelectedSegmentLogicalTapeDecoderHeadCleanupSplitConstruction := by
  rcases hcleanup with ⟨cleanup, hcleanupSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderHeadCleanupSplitSpec_of_spec
        hcleanupSpec⟩

/-- Construction-level full cleanup adapter from the branch-split view. -/
theorem selectedSegmentLogicalTapeDecoderHeadCleanupConstruction_of_split
    (hsplit : SelectedSegmentLogicalTapeDecoderHeadCleanupSplitConstruction) :
    SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction := by
  rcases hsplit with ⟨cleanup, hsplitSpec⟩
  exact
    ⟨cleanup,
      selectedSegmentLogicalTapeDecoderHeadCleanupSpec_of_splitSpec
        hsplitSpec⟩

/-- Full cleanup and branch-split cleanup are equivalent route boundaries. -/
theorem selectedSegmentLogicalTapeDecoderHeadCleanupConstruction_iff_split :
    SelectedSegmentLogicalTapeDecoderHeadCleanupConstruction ↔
      SelectedSegmentLogicalTapeDecoderHeadCleanupSplitConstruction := by
  constructor
  · exact selectedSegmentLogicalTapeDecoderHeadCleanupSplitConstruction_of_cleanup
  · exact selectedSegmentLogicalTapeDecoderHeadCleanupConstruction_of_split


end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
