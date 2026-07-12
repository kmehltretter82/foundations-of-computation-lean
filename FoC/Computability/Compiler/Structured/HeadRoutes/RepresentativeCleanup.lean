import FoC.Computability.Compiler.Structured.HeadRoutes.ExactCleanup

set_option doc.verso true

/-!
# Retired representative-cleanup guardrail contract

This module keeps only the exact representative shapes needed for the kernel-checked
source-collision guardrail.  The unused padding lattice and projector routes were deleted after
the marker-preserving #17 projector closed.
-/

namespace FoC
namespace Computability

open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

def selectedSegmentLogicalTapeDecoderPaddedCleanupOutputPaddingLength
    (target : Tape Bool) (padding : List (Option Bool)) (encodedPrefix : List (Option Bool)) : Nat :=
  Tape.contextLength
    (canonicalPrimitiveSeqHandoffTape (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
      target padding encodedPrefix))

def selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape
    (target : Tape Bool) (padding : List (Option Bool)) (encodedPrefix : List (Option Bool)) : Tape Bool :=
  { left := target.left
    head := target.head
    right :=
      target.right ++ List.replicate
        (selectedSegmentLogicalTapeDecoderPaddedCleanupOutputPaddingLength
          target padding encodedPrefix) (none : Option Bool) }

def SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupNilPaddingSpec (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall (target : Tape Bool) (encodedPrefix : List (Option Bool)),
      cleanup.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
          target [] encodedPrefix))
        (selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape target [] encodedPrefix)

def SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitSpec (cleanup : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupNilPaddingSpec
      cleanup ∧
    (cleanup.SubroutineReady ∧
      forall (target : Tape Bool) (pad : Option Bool)
        (padding encodedPrefix : List (Option Bool)),
        cleanup.HaltsFromTape
          (canonicalPrimitiveSeqHandoffTape (selectedSegmentLogicalTapeDecoderPaddedCleanupSourceTape
            target (pad :: padding) encodedPrefix))
          (selectedSegmentLogicalTapeDecoderPaddedCleanupOutputTape
            target (pad :: padding) encodedPrefix))

def SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitConstruction :
    Prop :=
  exists cleanup, SelectedSegmentLogicalTapeDecoderPaddedRepresentativeCleanupForwardSplitSpec cleanup

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
