import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.IndexedMaterializer.AcceptRewind

set_option doc.verso true

/-!
Composition of the accepting finite-machine phases into the public branch contract.
-/

namespace FoC
namespace Computability

open Languages MachineDescription CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup
namespace InputMat
namespace Route

open CanonicalLayouts.DovetailLayoutScanner MarkerAwareCommon AcceptBranch AcceptFinish AcceptInternalMarker
open AcceptMarkedLive AcceptReconstructPrefix AcceptDelimiter AcceptT0Allocator AcceptFinalTail
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat.DirectTokenDriver

theorem rewoundSourceTape0_eq_publicSource
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput true) :
    rewoundSourceTape0 input.L =
      countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
        true input := by
  rw [countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource]
  unfold rewoundSourceTape0 acceptRightPadding
    Tape0RewindPadded.targetTape acceptBits
    boolWordRawBitsDecoderSourceTape
  rw [sourcePadding_accept_eq_acceptConfig_length input]
  rfl

def acceptCommonDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription acceptPositionDescription
    MarkerAwareCommon.description
theorem acceptCommonDescription_ready :
    acceptCommonDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    acceptPositionDescription_subroutineReady
    MarkerAwareCommon.description_ready

def acceptPairRewindDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription AcceptBranch.pairDescription
    AcceptBranch.rewindDescription

theorem acceptPairRewindDescription_ready :
    acceptPairRewindDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    AcceptBranch.pairDescription_ready
    AcceptBranch.rewindDescription_ready
def acceptPrefixDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription acceptCommonDescription
    acceptPairRewindDescription

theorem acceptPrefixDescription_ready :
    acceptPrefixDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    acceptCommonDescription_ready acceptPairRewindDescription_ready

def acceptMarkLiveDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription markEraseGapDescription
    markedLiveDescription
theorem acceptMarkLiveDescription_ready :
    acceptMarkLiveDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    markEraseGapDescription_ready markedLiveDescription_ready

def acceptMoveRewindDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription moveTape2LeftFiveDescription
    (canonicalPrimitiveSeqDescription
      Tape2Rewinder.loweredDescription
      moveTape2LeftOneDescription)

theorem acceptMoveRewindDescription_ready :
    acceptMoveRewindDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    moveTape2LeftFiveDescription_ready
    (canonicalPrimitiveSeqDescription_subroutineReady
      Tape2Rewinder.loweredDescription_subroutineReady
      moveTape2LeftOneDescription_ready)
def acceptInternalDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription MarkerScanLowered.loweredDescription
    moveRightOneDescription

theorem acceptInternalDescription_ready :
    acceptInternalDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    MarkerScanLowered.loweredDescription_ready
    moveRightOneDescription_ready

def acceptDriverDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription Lowered.rewindDescription
    loweredPrefixDriverDescription
theorem acceptDriverDescription_ready :
    acceptDriverDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    Lowered.rewindDescription_ready
    loweredPrefixDriverDescription_subroutineReady

def acceptReconstructDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    (canonicalPrimitiveSeqDescription acceptMoveRewindDescription
      acceptInternalDescription)
    acceptDriverDescription

theorem acceptReconstructDescription_ready :
    acceptReconstructDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    (canonicalPrimitiveSeqDescription_subroutineReady
      acceptMoveRewindDescription_ready acceptInternalDescription_ready)
    acceptDriverDescription_ready
def acceptAllocateDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription loweredDelimiterDescription
    (canonicalPrimitiveSeqDescription loweredRightEdgeDescription
      BlankSpanAllocator.loweredDescription)

theorem acceptAllocateDescription_ready :
    acceptAllocateDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    loweredDelimiterDescription_ready
    (canonicalPrimitiveSeqDescription_subroutineReady
      loweredRightEdgeDescription_ready
      BlankSpanAllocator.loweredDescription_ready)

def acceptFinalizeDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription loweredTape0RewindDescription
    (canonicalPrimitiveSeqDescription MarkerScanLowered.loweredDescription
      moveRightOneDescription)
theorem acceptFinalizeDescription_ready :
    acceptFinalizeDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    loweredTape0RewindDescription_ready
    (canonicalPrimitiveSeqDescription_subroutineReady
      MarkerScanLowered.loweredDescription_ready
      moveRightOneDescription_ready)

def acceptTailDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription acceptAllocateDescription
    acceptFinalizeDescription

theorem acceptTailDescription_ready :
    acceptTailDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    acceptAllocateDescription_ready acceptFinalizeDescription_ready
def acceptDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    (canonicalPrimitiveSeqDescription acceptPrefixDescription
      acceptMarkLiveDescription)
    (canonicalPrimitiveSeqDescription acceptReconstructDescription
      acceptTailDescription)

theorem acceptDescription_ready : acceptDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    (canonicalPrimitiveSeqDescription_subroutineReady
      acceptPrefixDescription_ready acceptMarkLiveDescription_ready)
    (canonicalPrimitiveSeqDescription_subroutineReady
      acceptReconstructDescription_ready acceptTailDescription_ready)

theorem acceptCommonDescription_realizes
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput true) :
    acceptCommonDescription.HaltsFromTapeEquiv
      (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
        true input)
      (encodedGuardedStructured3Tapes
        (commonEndpointTape0 true input.L) Tape.blank
        (afterStageTape2 (acceptOutputRest input.L) input.L)) := by
  simpa [acceptCommonDescription] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      acceptPositionDescription_subroutineReady
      MarkerAwareCommon.description_ready
      (acceptPositionDescription_realizes input)
      (MarkerAwareCommon.realizes true
        (acceptOutputRest input.L) input.L)
theorem acceptPairRewindDescription_realizes (L : DovetailLayout) :
    acceptPairRewindDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (commonEndpointTape0 true L) Tape.blank
        (afterStageTape2 (acceptOutputRest L) L))
      (encodedGuardedStructured3Tapes
        (afterPairTape0 L) Tape.blank (afterRewindTape2 L)) := by
  simpa [acceptPairRewindDescription] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      AcceptBranch.pairDescription_ready
      AcceptBranch.rewindDescription_ready
      (pairAtCommon_realizes L) (rewindAtPair_realizes L)

theorem acceptPrefixDescription_realizes
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput true) :
    acceptPrefixDescription.HaltsFromTapeEquiv
      (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
        true input)
      (encodedGuardedStructured3Tapes
        (afterPairTape0 input.L) Tape.blank (afterRewindTape2 input.L)) := by
  simpa [acceptPrefixDescription] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      acceptCommonDescription_ready acceptPairRewindDescription_ready
      (acceptCommonDescription_realizes input)
      (acceptPairRewindDescription_realizes input.L)

theorem acceptMarkLiveDescription_realizes (L : DovetailLayout) :
    acceptMarkLiveDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (afterPairTape0 L) Tape.blank (afterRewindTape2 L))
      (encodedGuardedStructured3Tapes
        (afterLiveCopyTape0 L) Tape.blank (markedExactOutputEndTape2 L)) := by
  simpa [acceptMarkLiveDescription] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      markEraseGapDescription_ready markedLiveDescription_ready
      (markEraseGapDescription_realizes L) (markedLiveDescription_realizes L)
theorem acceptMoveRewindDescription_realizes (L : DovetailLayout) :
    acceptMoveRewindDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (afterLiveCopyTape0 L) Tape.blank (markedExactOutputEndTape2 L))
      (encodedGuardedStructured3Tapes
        (afterLiveCopyTape0 L) Tape.blank (internalScanSourceTape2 L)) := by
  have htail := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    Tape2Rewinder.loweredDescription_subroutineReady
    moveTape2LeftOneDescription_ready
    (livePaddedRewind_realizes L)
    (moveTape2LeftOneDescription_realizes
      (afterLiveCopyTape0 L) (liveRewindTargetTape2 L))
  have hall := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    moveTape2LeftFiveDescription_ready
    (canonicalPrimitiveSeqDescription_subroutineReady
      Tape2Rewinder.loweredDescription_subroutineReady
      moveTape2LeftOneDescription_ready)
    (moveTape2LeftFiveDescription_realizes L) htail
  simpa [acceptMoveRewindDescription, internalScanSourceTape2] using hall

theorem acceptInternalDescription_realizes (L : DovetailLayout) :
    acceptInternalDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (afterLiveCopyTape0 L) Tape.blank (internalScanSourceTape2 L))
      (encodedGuardedStructured3Tapes
        (afterLiveCopyTape0 L) Tape.blank (postInternalRightTape2 L)) := by
  simpa [acceptInternalDescription] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      MarkerScanLowered.loweredDescription_ready moveRightOneDescription_ready
      (internalMarkerScan_realizes L) (moveRightAfterInternal_realizes L)

theorem acceptDriverDescription_realizes (L : DovetailLayout) :
    acceptDriverDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (afterLiveCopyTape0 L) Tape.blank (postInternalRightTape2 L))
      (encodedGuardedStructured3Tapes
        (afterDriverTape0 true L) Tape.blank
        (afterReconstructionDriverTape2 L)) := by
  simpa [acceptDriverDescription] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      Lowered.rewindDescription_ready
      loweredPrefixDriverDescription_subroutineReady
      (rewindT0ForDriver_realizes L) (reconstructionDriver_realizes L)
theorem acceptReconstructDescription_realizes (L : DovetailLayout) :
    acceptReconstructDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (afterLiveCopyTape0 L) Tape.blank (markedExactOutputEndTape2 L))
      (encodedGuardedStructured3Tapes
        (afterDriverTape0 true L) Tape.blank
        (afterReconstructionDriverTape2 L)) := by
  have hfirst := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    acceptMoveRewindDescription_ready acceptInternalDescription_ready
    (acceptMoveRewindDescription_realizes L)
    (acceptInternalDescription_realizes L)
  simpa [acceptReconstructDescription] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      (canonicalPrimitiveSeqDescription_subroutineReady
        acceptMoveRewindDescription_ready acceptInternalDescription_ready)
      acceptDriverDescription_ready hfirst
      (acceptDriverDescription_realizes L)

theorem acceptAllocateDescription_realizes (L : DovetailLayout) :
    acceptAllocateDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (afterDriverTape0 true L) Tape.blank
        (afterReconstructionDriverTape2 L))
      (encodedGuardedStructured3Tapes
        (afterAllocatorTape0 L) Tape.blank (afterAllocatorTape2 L)) := by
  have hdelimiter := delimiter_realizes L
  rw [← afterReconstructionDriverTape2_eq_delimiterSource] at hdelimiter
  have htail := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    loweredRightEdgeDescription_ready
    BlankSpanAllocator.loweredDescription_ready
    (rightEdge_realizes L) (allocator_realizes L)
  simpa [acceptAllocateDescription] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      loweredDelimiterDescription_ready
      (canonicalPrimitiveSeqDescription_subroutineReady
        loweredRightEdgeDescription_ready
        BlankSpanAllocator.loweredDescription_ready)
      hdelimiter htail

theorem acceptFinalizeDescription_realizes (L : DovetailLayout) :
    acceptFinalizeDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (afterAllocatorTape0 L) Tape.blank (afterAllocatorTape2 L))
      (encodedGuardedStructured3Tapes
        (rewoundSourceTape0 L) Tape.blank (finalOutputTape2 L)) := by
  have hscan := outerMarkerScan_realizes L
  rw [← afterAllocatorTape2_eq_outerMarkerSource] at hscan
  have htail := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    MarkerScanLowered.loweredDescription_ready moveRightOneDescription_ready
    hscan (moveRightAfterOuter_realizes L)
  simpa [acceptFinalizeDescription] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      loweredTape0RewindDescription_ready
      (canonicalPrimitiveSeqDescription_subroutineReady
        MarkerScanLowered.loweredDescription_ready moveRightOneDescription_ready)
      (tape0Rewind_realizes L) htail
theorem acceptTailDescription_realizes (L : DovetailLayout) :
    acceptTailDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (afterDriverTape0 true L) Tape.blank
        (afterReconstructionDriverTape2 L))
      (encodedGuardedStructured3Tapes
        (rewoundSourceTape0 L) Tape.blank (finalOutputTape2 L)) := by
  simpa [acceptTailDescription] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      acceptAllocateDescription_ready acceptFinalizeDescription_ready
      (acceptAllocateDescription_realizes L)
      (acceptFinalizeDescription_realizes L)

theorem acceptDescription_realizes
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput true) :
    acceptDescription.HaltsFromTapeEquiv
      (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
        true input)
      (structured3InputMaterializerTargetTape
        (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
          true input)
        (countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputTape
          true input)) := by
  have hleft := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    acceptPrefixDescription_ready acceptMarkLiveDescription_ready
    (acceptPrefixDescription_realizes input)
    (acceptMarkLiveDescription_realizes input.L)
  have hright := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    acceptReconstructDescription_ready acceptTailDescription_ready
    (acceptReconstructDescription_realizes input.L)
    (acceptTailDescription_realizes input.L)
  have hall := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    (canonicalPrimitiveSeqDescription_subroutineReady
      acceptPrefixDescription_ready acceptMarkLiveDescription_ready)
    (canonicalPrimitiveSeqDescription_subroutineReady
      acceptReconstructDescription_ready acceptTailDescription_ready)
    hleft hright
  rw [finalOutputTape2_eq_publicTarget,
    rewoundSourceTape0_eq_publicSource input] at hall
  simpa [acceptDescription, structured3InputMaterializerTargetTape,
    countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputTape]
    using hall

end Route
end InputMat
end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
