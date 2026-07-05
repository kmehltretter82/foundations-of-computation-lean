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
