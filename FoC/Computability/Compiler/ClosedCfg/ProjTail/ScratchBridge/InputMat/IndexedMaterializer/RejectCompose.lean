import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.IndexedMaterializer.RejectReturn

set_option doc.verso true

/-!
Composition of the rejecting phases into the indexed public construction.
-/

set_option linter.unusedSimpArgs false

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace FoC
namespace Computability

open Languages MachineDescription CommonGround.FiniteTransducers CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup
namespace InputMat
namespace Route
namespace RejectComposition

open CanonicalLayouts.DovetailLayoutScanner CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat.DirectTokenDriver
open MarkerAwareCommon AcceptBranch RejectContinuation RejectLive RejectTape2Tail RejectBranchShapes RejectGapShapes
open AcceptFinish AcceptReconstructPrefix AcceptT0Allocator RejectTape0Padding

/-! Public source through the halting stage locator. -/

theorem locatedConfigTape0_eq_pairPositionTape0 (L : DovetailLayout) :
    locatedConfigTape0 false L = pairPositionTape0 L := by
  have hbits :
      Route.prefixThroughStageBits L =
        RejectBranchShapes.prefixThroughStageBits L := by
    rcases cellListFieldBits_cons_false (L.input.map some) [] with
      ⟨inputTail, hinput⟩
    have hword : boolWordFieldBits L.input [] = false :: inputTail := hinput
    have hwordTail : (boolWordFieldBits L.input []).tail = inputTail := by
      simp [hword]
    simp [Route.prefixThroughStageBits,
      RejectBranchShapes.prefixThroughStageBits,
      RejectBranchShapes.inputStageBits,
      RejectBranchShapes.stageBits, hword, hwordTail,
      List.append_assoc]
  have hprefix :
      AcceptConfigCopy.wrappedBits (Route.prefixThroughStageBits L) =
        List.append
          (List.append (wrappedKind .transition) (wrappedRawBit false))
          (AcceptConfigCopy.wrappedBits
            (RejectBranchShapes.inputStageBits L)) := by
    rw [hbits, RejectBranchShapes.prefixThroughStageBits,
      Route.wrappedBits_append,
      Route.wrappedBits_transitionPrefixBits]
    rfl
  unfold locatedConfigTape0 pairPositionTape0 commonEndpointLeft
  rw [hprefix, route_configHitBits_eq_pairSourceBits]
  simp [List.reverse_append, List.map_append, List.append_assoc]

def rejectLocateDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription rejectPositionDescription
    MarkerAwareCommon.armLocateStageDescription
theorem rejectLocateDescription_ready :
    rejectLocateDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    rejectPositionDescription_subroutineReady
    MarkerAwareCommon.armLocateStageDescription_ready

theorem rejectLocateDescription_realizes
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        false) :
    rejectLocateDescription.HaltsFromTapeEquiv
      (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
        false input)
      (encodedGuardedStructured3Tapes
        (pairPositionTape0 input.L) Tape.blank
        (afterStageTape2 (rejectOutputRest input.L) input.L)) := by
  have h := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    rejectPositionDescription_subroutineReady
    MarkerAwareCommon.armLocateStageDescription_ready
    (rejectPositionDescription_realizes input)
    (MarkerAwareCommon.armLocateStageDescription_realizes false
      (rejectOutputRest input.L) input.L)
  simpa [rejectLocateDescription, locatedConfigTape0_eq_pairPositionTape0]
    using h

/-! Copy the reject-sized pair and land at the marked continuation. -/

theorem rejectPairDescription_realizes (L : DovetailLayout) :
    AcceptBranch.pairDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (pairPositionTape0 L) Tape.blank
        (afterStageTape2 (rejectOutputRest L) L))
      (encodedGuardedStructured3Tapes
        (rejectAfterPairTape0 L) Tape.blank (rejectAfterPairTape2 L)) := by
  have h := AcceptBranch.pairDescription_realizes
    (pairSourceBits L) (RejectBranchShapes.rejectBits L)
    (List.append
      ((AcceptConfigCopy.wrappedBits
        (RejectBranchShapes.inputStageBits L)).reverse.map some)
      (MarkerAwareCommon.commonEndpointLeft L))
    (List.append
      ((RejectBranchShapes.stageBits L).reverse.map some)
      (MarkerAwareCommon.counterBaseLeft L))
    (MarkerAwareCommon.rawBoundaryRest false L)
    (Nat.le_of_lt (rejectBits_length_lt_pairSourceBits_length L))
  simpa [pairPositionTape0, rejectAfterPairTape0, rejectAfterPairTape2,
    pairEndLeft0, remainingPairBits, afterStageTape2, rejectOutputRest,
    RejectBranchShapes.stageBits, RejectBranchShapes.rejectBits,
    PairStream.counterTape, scanTape, List.append_assoc] using h
def rejectInitialDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription rejectLocateDescription
    AcceptBranch.pairDescription

theorem rejectInitialDescription_ready :
  rejectInitialDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    rejectLocateDescription_ready AcceptBranch.pairDescription_ready

theorem rejectInitialDescription_realizes
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        false) :
    rejectInitialDescription.HaltsFromTapeEquiv
      (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
        false input)
      (encodedGuardedStructured3Tapes
        (rejectAfterPairTape0 input.L) Tape.blank
        (rejectAfterPairTape2 input.L)) := by
  simpa [rejectInitialDescription] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      rejectLocateDescription_ready AcceptBranch.pairDescription_ready
      (rejectLocateDescription_realizes input)
      (rejectPairDescription_realizes input.L)

/-! Pair endpoint through the transferred output marker. -/
def rejectGapPrefixDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription gapMarkerDescription
    (canonicalPrimitiveSeqDescription
      AcceptBranch.rewindDescription
      primaryRewindOptionsDescription)

theorem rejectGapPrefixDescription_ready :
    rejectGapPrefixDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    gapMarkerDescription_ready
    (canonicalPrimitiveSeqDescription_subroutineReady
      AcceptBranch.rewindDescription_ready
      primaryRewindOptionsDescription_ready)

theorem rejectGapPrefixDescription_realizes (L : DovetailLayout) :
    rejectGapPrefixDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rejectAfterPairTape0 L) Tape.blank (rejectAfterPairTape2 L))
      (encodedGuardedStructured3Tapes
        (primaryRewoundGapTape0 L) Tape.blank (rejectRewoundTape2 L)) := by
  have htail := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    AcceptBranch.rewindDescription_ready
    primaryRewindOptionsDescription_ready
    (rejectTape2Rewind_realizes L)
    (primaryRewindOptionsDescription_realizes L)
  simpa [rejectGapPrefixDescription] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      gapMarkerDescription_ready
      (canonicalPrimitiveSeqDescription_subroutineReady
        AcceptBranch.rewindDescription_ready
        primaryRewindOptionsDescription_ready)
      (gapMarkerDescription_realizes L) htail
def rejectTransferDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription armAdvanceDataDescription
    rejectGapDescription

theorem rejectTransferDescription_ready :
    rejectTransferDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    armAdvanceDataDescription_ready rejectGapDescription_ready

theorem rejectTransferDescription_realizes (L : DovetailLayout) :
    rejectTransferDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (primaryRewoundGapTape0 L) Tape.blank (rejectRewoundTape2 L))
      (encodedGuardedStructured3Tapes
        (afterMarkedEraseTape0 L) Tape.blank (rejectMarkerTargetTape2 L)) := by
  simpa [rejectTransferDescription] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      armAdvanceDataDescription_ready rejectGapDescription_ready
      (armAdvanceDataDescription_realizes L)
      (rejectGapDescription_realizes L)
def rejectToMarkerDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription rejectGapPrefixDescription
    rejectTransferDescription

theorem rejectToMarkerDescription_ready :
    rejectToMarkerDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    rejectGapPrefixDescription_ready rejectTransferDescription_ready

theorem rejectToMarkerDescription_realizes (L : DovetailLayout) :
    rejectToMarkerDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rejectAfterPairTape0 L) Tape.blank (rejectAfterPairTape2 L))
      (encodedGuardedStructured3Tapes
        (afterMarkedEraseTape0 L) Tape.blank (rejectMarkerTargetTape2 L)) := by
  simpa [rejectToMarkerDescription] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      rejectGapPrefixDescription_ready rejectTransferDescription_ready
      (rejectGapPrefixDescription_realizes L)
      (rejectTransferDescription_realizes L)

/-! Transferred marker through the exact public tape-2 output. -/
def rejectLiveCleanupDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription rejectLiveDescription
    rejectCleanupDescription

theorem rejectLiveCleanupDescription_ready :
    rejectLiveCleanupDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    rejectLiveDescription_ready rejectCleanupDescription_ready

def rejectOutputTailDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription moveTape2RightEightDescription
    (canonicalPrimitiveSeqDescription rejectLiveCleanupDescription
      rejectTape2TailDescription)
theorem rejectOutputTailDescription_ready :
    rejectOutputTailDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    moveTape2RightEightDescription_ready
    (canonicalPrimitiveSeqDescription_subroutineReady
      rejectLiveCleanupDescription_ready rejectTape2TailDescription_ready)

theorem rejectOutputTailDescription_realizes (L : DovetailLayout) :
    rejectOutputTailDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (afterMarkedEraseTape0 L) Tape.blank (rejectMarkerTargetTape2 L))
      (encodedGuardedStructured3Tapes
        (rejectAfterLiveCopyTape0 L) Tape.blank
        (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
          (ParsedLayoutBits L).length
          (postFieldDecodedPrefixScanPadding false L))) := by
  have hlive := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    rejectLiveCleanupDescription_ready rejectTape2TailDescription_ready
    (rejectLiveCleanup_realizes L)
    (rejectTape2TailDescription_realizes L)
  have h := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    moveTape2RightEightDescription_ready
    (canonicalPrimitiveSeqDescription_subroutineReady
      rejectLiveCleanupDescription_ready rejectTape2TailDescription_ready)
    (moveTape2RightEight_at_reject_gap_realizes L) hlive
  rw [rejectFinalOutputTape2_eq_publicTarget] at h
  simpa [rejectOutputTailDescription, rejectLiveCleanupDescription] using h

def rejectCoreDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription rejectInitialDescription
    (canonicalPrimitiveSeqDescription rejectToMarkerDescription
      rejectOutputTailDescription)
theorem rejectCoreDescription_ready :
    rejectCoreDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    rejectInitialDescription_ready
    (canonicalPrimitiveSeqDescription_subroutineReady
      rejectToMarkerDescription_ready rejectOutputTailDescription_ready)

theorem rejectCoreDescription_realizes
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        false) :
    rejectCoreDescription.HaltsFromTapeEquiv
      (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
        false input)
      (encodedGuardedStructured3Tapes
        (rejectAfterLiveCopyTape0 input.L) Tape.blank
        (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
          (ParsedLayoutBits input.L).length
          (postFieldDecodedPrefixScanPadding false input.L))) := by
  have htail := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    rejectToMarkerDescription_ready rejectOutputTailDescription_ready
    (rejectToMarkerDescription_realizes input.L)
    (rejectOutputTailDescription_realizes input.L)
  simpa [rejectCoreDescription] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      rejectInitialDescription_ready
      (canonicalPrimitiveSeqDescription_subroutineReady
        rejectToMarkerDescription_ready rejectOutputTailDescription_ready)
      (rejectInitialDescription_realizes input) htail

/-! Restore the primary tape for the raw padded finalizer. -/

theorem rejectAfterLiveCopyTape0_eq_rejectAtBoundaryTape0
    (L : DovetailLayout) :
    rejectAfterLiveCopyTape0 L = rejectAtBoundaryTape0 L := by
  unfold rejectAfterLiveCopyTape0 rejectAtBoundaryTape0
    rejectRemainingLiveBits rejectAfterFirstStageLeft
    afterFirstStageLeft postPrefixLeft
  have hraw := RejectLive.rawBoundaryRest_reject_eq_false_false_drop L
  cases hstage : L.stage with
  | zero =>
      simp [remainingLiveBits, hstage, configHitBits,
        wrappedBits_parsedLayoutBits,
        Components.wrappedNatTokens,
        List.reverse_append, List.map_append, List.append_assoc]
      apply congrArg (scanTape _)
      exact hraw.symm
  | succ stage =>
      have hsplit :
          AcceptConfigCopy.wrappedBits
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  stage)
                (configHitBits L)) =
            List.append (Components.wrappedNatTokens stage)
              (AcceptConfigCopy.wrappedBits (configHitBits L)) := by
        rw [wrappedBits_append, wrappedBits_stageNatBits]
      let base : List (Option Bool) :=
        List.append
          (List.append ((wrappedKind .tick).reverse.map some)
            ((Components.wrappedCellTokens L.input).reverse.map some))
          (List.append
            (List.append
              ((Components.wrappedNatTokens L.input.length).reverse.map some)
              ((wrappedKind .transition).reverse.map some))
            (none :: primaryMarkerBaseLeft L))
      have hleft :
          List.append
              ((AcceptConfigCopy.wrappedBits
                (List.append
                  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                    stage)
                  (configHitBits L))).reverse.map some)
              base =
            List.append
              ((AcceptConfigCopy.wrappedBits (configHitBits L)).reverse.map some)
              (List.append
                ((Components.wrappedNatTokens stage).reverse.map some) base) := by
        have hrev :
            (AcceptConfigCopy.wrappedBits
                (List.append
                  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                    stage)
                  (configHitBits L))).reverse.map some =
              List.append
                ((AcceptConfigCopy.wrappedBits (configHitBits L)).reverse.map some)
                ((Components.wrappedNatTokens stage).reverse.map some) := by
          calc
            _ = (List.append (Components.wrappedNatTokens stage)
                  (AcceptConfigCopy.wrappedBits (configHitBits L))).reverse.map some :=
                congrArg
                  (fun xs => (xs.reverse.map some : List (Option Bool))) hsplit
            _ = _ := reverse_map_some_append
              (Components.wrappedNatTokens stage)
              (AcceptConfigCopy.wrappedBits (configHitBits L))
        rw [hrev]
        exact List.append_assoc _ _ _
      simp only [remainingLiveBits, hstage, List.reverse_append,
        List.map_append, List.append_assoc, reverse_map_some_append]
      rw [hleft]
      rw [wrappedBits_parsedLayoutBits, hstage]
      have hnat :
          Components.wrappedNatTokens (stage + 1) =
            List.append (wrappedKind .tick)
              (Components.wrappedNatTokens stage) := by
        rfl
      rw [hnat]
      simp only [List.reverse_append,
        List.map_append, List.append_assoc, reverse_map_some_append]
      rw [append_seven_regroup]
      apply congrArg (scanTape _)
      exact hraw.symm
theorem rejectRewoundParsed_eq_postPosition (L : DovetailLayout) :
    rewoundParsedTape0 false L = postPositionTape0 false L := by
  unfold rewoundParsedTape0
  exact (postPositionTape0_eq_unmarked_shape false L).symm

theorem rejectRewindT0ForDriver_realizes
    (L : DovetailLayout) (T2 : Tape Bool) :
    MarkerAwareCommon.Lowered.rewindDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rejectAfterLiveCopyTape0 L) Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (postPositionTape0 false L) Tape.blank T2) := by
  rw [rejectAfterLiveCopyTape0_eq_rejectAtBoundaryTape0]
  have h := rejectRewindFull_realizes L T2
  rw [rejectRewoundParsed_eq_postPosition] at h
  exact h

namespace OutputMarkerOptions

open OutputOriginMarker

syntax "output_marker_options_step" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| output_marker_options_step [$lemmas,*]) =>
      `(tactic|
        three_tape_step [OutputOriginMarker.description,
          OutputOriginMarker.rows, OutputOriginMarker.rowsForRead,
          OutputOriginMarker.rowsForTape2Read,
          OutputOriginMarker.start, OutputOriginMarker.mark,
          OutputOriginMarker.halt, allReads3, allReads2, allReadCells,
          List.find?, tapeAtCells, $lemmas,*])

theorem run
    (T0 T1 : Tape Bool) (right : List (Option Bool)) :
    OutputOriginMarker.description.runConfig 2
        (config OutputOriginMarker.start T0 T1
          (tapeAtCells [none] right)) =
      config OutputOriginMarker.halt T0 T1
        (tapeAtCells [some true] right) := by
  cases h0 : T0.head with
  | none =>
      cases h1 : T1.head with
      | none =>
          cases right with
          | nil => output_marker_options_step [h0, h1]
          | cons cell right => cases cell with
            | none => output_marker_options_step [h0, h1]
            | some bit => cases bit <;> output_marker_options_step [h0, h1]
      | some bit1 => cases bit1 <;>
          cases right with
          | nil => output_marker_options_step [h0, h1]
          | cons cell right => cases cell with
            | none => output_marker_options_step [h0, h1]
            | some bit => cases bit <;> output_marker_options_step [h0, h1]
  | some bit0 => cases bit0 <;>
      cases h1 : T1.head with
      | none =>
          cases right with
          | nil => output_marker_options_step [h0, h1]
          | cons cell right => cases cell with
            | none => output_marker_options_step [h0, h1]
            | some bit => cases bit <;> output_marker_options_step [h0, h1]
      | some bit1 => cases bit1 <;>
          cases right with
          | nil => output_marker_options_step [h0, h1]
          | cons cell right => cases cell with
            | none => output_marker_options_step [h0, h1]
            | some bit => cases bit <;> output_marker_options_step [h0, h1]

end OutputMarkerOptions
theorem outputOriginMarkerDescription_realizes_options
    (T0 : Tape Bool) (right : List (Option Bool)) :
    outputOriginMarkerDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes T0 Tape.blank
        (tapeAtCells [none] right))
      (encodedGuardedStructured3Tapes T0 Tape.blank
        (tapeAtCells [some true] right)) := by
  simpa [outputOriginMarkerDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      outputOriginMarker_ready.left outputOriginMarker_ready.right
      outputOriginMarker_supports
      (c := config OutputOriginMarker.start T0 Tape.blank
        (tapeAtCells [none] right))
      (tapes := [T0, Tape.blank, tapeAtCells [some true] right])
      rfl rfl ⟨2, OutputMarkerOptions.run T0 Tape.blank right⟩

def rejectFinalLiveRight (L : DovetailLayout) : List (Option Bool) :=
  List.append ((rejectKeptPrefixBits L).map some)
    (List.append (List.replicate 4 none)
      (List.append
        ((RejectBranchShapes.rejectHitBits L).map some)
        [none, none]))

def rejectFinalOutputRight (L : DovetailLayout) : List (Option Bool) :=
  List.append
    (List.replicate
      ((ParsedLayoutBits L).length + markerOffset L + 8)
      (none : Option Bool))
    (rejectFinalLiveRight L)
def rejectMarkedFinalOutputTape2 (L : DovetailLayout) : Tape Bool :=
  tapeAtCells [some true] (rejectFinalOutputRight L)

theorem rejectFinalOutputTape2_eq_options_shape (L : DovetailLayout) :
    rejectFinalOutputTape2 L =
      tapeAtCells [none] (rejectFinalOutputRight L) := by
  exact rejectFinalOutputTape2_shape L

theorem rejectMarkFinalOutput_realizes (L : DovetailLayout) :
    outputOriginMarkerDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rejectAfterLiveCopyTape0 L) Tape.blank (rejectFinalOutputTape2 L))
      (encodedGuardedStructured3Tapes
        (rejectAfterLiveCopyTape0 L) Tape.blank
        (rejectMarkedFinalOutputTape2 L)) := by
  rw [rejectFinalOutputTape2_eq_options_shape]
  exact outputOriginMarkerDescription_realizes_options
    (rejectAfterLiveCopyTape0 L) (rejectFinalOutputRight L)
def rejectRewindDriverDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    MarkerAwareCommon.Lowered.rewindDescription
    loweredPrefixDriverDescription

theorem rejectRewindDriverDescription_ready :
    rejectRewindDriverDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    MarkerAwareCommon.Lowered.rewindDescription_ready
    loweredPrefixDriverDescription_subroutineReady

theorem rejectRewindDriverDescription_realizes (L : DovetailLayout) :
    rejectRewindDriverDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rejectAfterLiveCopyTape0 L) Tape.blank
        (rejectMarkedFinalOutputTape2 L))
      (encodedGuardedStructured3Tapes
        (afterDriverTape0 false L) Tape.blank
        (Components.eraseRight (driverPrefixBits L).length
          (rejectMarkedFinalOutputTape2 L))) := by
  simpa [rejectRewindDriverDescription] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      MarkerAwareCommon.Lowered.rewindDescription_ready
      loweredPrefixDriverDescription_subroutineReady
      (rejectRewindT0ForDriver_realizes L (rejectMarkedFinalOutputTape2 L))
      (loweredPrefixDriverDescription_realizes_with_tape false L
        (rejectMarkedFinalOutputTape2 L))
def rejectPostDriverRight (L : DovetailLayout) : List (Option Bool) :=
  List.append
    (List.replicate
      ((ParsedLayoutBits L).length +
        (RejectBranchShapes.rejectBits L).length + 7)
      (none : Option Bool))
    (rejectFinalLiveRight L)

theorem rejectFinalOutputRight_eq_driver_split (L : DovetailLayout) :
    rejectFinalOutputRight L =
      List.append
        (List.replicate (driverPrefixBits L).length
          (none : Option Bool))
        (none :: rejectPostDriverRight L) := by
  have hcount :
      (ParsedLayoutBits L).length + markerOffset L + 8 =
        (driverPrefixBits L).length +
          (1 + ((ParsedLayoutBits L).length +
            (RejectBranchShapes.rejectBits L).length + 7)) := by
    rw [AcceptDelimiter.driverPrefixBits_eq_inputStageBits]
    change
      (ParsedLayoutBits L).length + markerOffset L + 8 =
        (RejectBranchShapes.inputStageBits L).length +
          (1 + ((ParsedLayoutBits L).length +
            (RejectBranchShapes.rejectBits L).length + 7))
    simp [markerOffset]
    lia
  unfold rejectFinalOutputRight rejectPostDriverRight
  rw [hcount]
  generalize hn : (driverPrefixBits L).length = n
  generalize hq :
    (ParsedLayoutBits L).length +
      (RejectBranchShapes.rejectBits L).length + 7 = q
  calc
    List.append (List.replicate (n + (1 + q)) none)
          (rejectFinalLiveRight L) =
        List.append
          (List.append (List.replicate n none)
            (List.replicate (1 + q) none))
          (rejectFinalLiveRight L) := by
      exact congrArg (fun xs => List.append xs (rejectFinalLiveRight L))
        (AcceptFinish.replicate_none_append_replicate n (1 + q)).symm
    _ = List.append (List.replicate n none)
          (none :: List.append (List.replicate q none)
            (rejectFinalLiveRight L)) := by
      rw [show 1 + q = q + 1 by lia, List.replicate_succ]
      simp [List.append_assoc]

def rejectAfterDriverMarkerTape2 (L : DovetailLayout) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate (driverPrefixBits L).length (none : Option Bool))
      [some true])
    (none :: rejectPostDriverRight L)
theorem eraseDriverMarkedOutput_eq_afterDriverMarker (L : DovetailLayout) :
    Components.eraseRight (driverPrefixBits L).length
        (rejectMarkedFinalOutputTape2 L) =
      rejectAfterDriverMarkerTape2 L := by
  unfold rejectMarkedFinalOutputTape2 rejectAfterDriverMarkerTape2
  rw [rejectFinalOutputRight_eq_driver_split]
  exact AcceptDelimiter.eraseRight_replicate_none_prefix
    (driverPrefixBits L).length [some true]
    (none :: rejectPostDriverRight L)

def rejectMarkerReturnTargetTape2 (L : DovetailLayout) : Tape Bool :=
  tapeAtCells []
    (none ::
      List.append
        (List.replicate ((driverPrefixBits L).length + 1)
          (none : Option Bool))
        (rejectPostDriverRight L))

theorem rejectMarkerScanReturn_realizes
    (T0 : Tape Bool) (L : DovetailLayout) :
    MarkerScanLowered.loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes T0 Tape.blank
        (rejectAfterDriverMarkerTape2 L))
      (encodedGuardedStructured3Tapes T0 Tape.blank
        (rejectMarkerReturnTargetTape2 L)) := by
  simpa [rejectAfterDriverMarkerTape2, rejectMarkerReturnTargetTape2] using
    MarkerScanLowered.loweredDescription_realizes
      (driverPrefixBits L).length T0 ([] : List (Option Bool))
      (rejectPostDriverRight L)
theorem rejectMarkerReturn_moveRight_eq_final (L : DovetailLayout) :
    keepR.apply (rejectMarkerReturnTargetTape2 L) =
      rejectFinalOutputTape2 L := by
  have hrep :
      List.append
          (List.replicate ((driverPrefixBits L).length + 1)
            (none : Option Bool))
          (rejectPostDriverRight L) =
        List.append
          (List.replicate (driverPrefixBits L).length none)
          (none :: rejectPostDriverRight L) := by
    simpa using
      (list_replicate_add_append (none : Option Bool)
        (driverPrefixBits L).length 1 (rejectPostDriverRight L))
  rw [rejectFinalOutputTape2_eq_options_shape,
    rejectFinalOutputRight_eq_driver_split]
  unfold rejectMarkerReturnTargetTape2
  change
    tapeAtCells [none]
        (List.append
          (List.replicate ((driverPrefixBits L).length + 1) none)
          (rejectPostDriverRight L)) =
      tapeAtCells [none]
        (List.append
          (List.replicate (driverPrefixBits L).length none)
          (none :: rejectPostDriverRight L))
  rw [hrep]

def rejectOutputReturnDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription MarkerScanLowered.loweredDescription
    moveRightOneDescription

theorem rejectOutputReturnDescription_ready :
    rejectOutputReturnDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    MarkerScanLowered.loweredDescription_ready moveRightOneDescription_ready
theorem rejectOutputReturnDescription_realizes
    (T0 : Tape Bool) (L : DovetailLayout) :
    rejectOutputReturnDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes T0 Tape.blank
        (rejectAfterDriverMarkerTape2 L))
      (encodedGuardedStructured3Tapes T0 Tape.blank
        (rejectFinalOutputTape2 L)) := by
  have hr := moveRightOneDescription_realizes T0
    (rejectMarkerReturnTargetTape2 L)
  rw [rejectMarkerReturn_moveRight_eq_final] at hr
  simpa [rejectOutputReturnDescription] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      MarkerScanLowered.loweredDescription_ready moveRightOneDescription_ready
      (rejectMarkerScanReturn_realizes T0 L) hr

theorem rejectCoreDescription_realizes_finalOutput
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        false) :
    rejectCoreDescription.HaltsFromTapeEquiv
      (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
        false input)
      (encodedGuardedStructured3Tapes
        (rejectAfterLiveCopyTape0 input.L) Tape.blank
        (rejectFinalOutputTape2 input.L)) := by
  have h := rejectCoreDescription_realizes input
  rw [← rejectFinalOutputTape2_eq_publicTarget] at h
  exact h

def rejectDriverEdgeDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription outputOriginMarkerDescription
    (canonicalPrimitiveSeqDescription rejectRewindDriverDescription
      loweredRightEdgeDescription)
theorem rejectDriverEdgeDescription_ready :
    rejectDriverEdgeDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    outputOriginMarkerDescription_subroutineReady
    (canonicalPrimitiveSeqDescription_subroutineReady
      rejectRewindDriverDescription_ready loweredRightEdgeDescription_ready)

theorem rejectDriverEdgeDescription_realizes (L : DovetailLayout) :
    rejectDriverEdgeDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rejectAfterLiveCopyTape0 L) Tape.blank (rejectFinalOutputTape2 L))
      (encodedGuardedStructured3Tapes
        (rightEdgeTape0 L) Tape.blank (rejectAfterDriverMarkerTape2 L)) := by
  have hd := rejectRewindDriverDescription_realizes L
  rw [eraseDriverMarkedOutput_eq_afterDriverMarker] at hd
  have hdr := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    rejectRewindDriverDescription_ready loweredRightEdgeDescription_ready hd
    (rightEdgeDescription_realizes L (rejectAfterDriverMarkerTape2 L))
  simpa [rejectDriverEdgeDescription] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      outputOriginMarkerDescription_subroutineReady
      (canonicalPrimitiveSeqDescription_subroutineReady
        rejectRewindDriverDescription_ready loweredRightEdgeDescription_ready)
      (rejectMarkFinalOutput_realizes L) hdr

def rejectEdgeRestoredOutputDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription rejectDriverEdgeDescription
    rejectOutputReturnDescription
theorem rejectEdgeRestoredOutputDescription_ready :
    rejectEdgeRestoredOutputDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    rejectDriverEdgeDescription_ready rejectOutputReturnDescription_ready

theorem rejectEdgeRestoredOutputDescription_realizes (L : DovetailLayout) :
    rejectEdgeRestoredOutputDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rejectAfterLiveCopyTape0 L) Tape.blank (rejectFinalOutputTape2 L))
      (encodedGuardedStructured3Tapes
        (rightEdgeTape0 L) Tape.blank (rejectFinalOutputTape2 L)) := by
  simpa [rejectEdgeRestoredOutputDescription] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      rejectDriverEdgeDescription_ready rejectOutputReturnDescription_ready
      (rejectDriverEdgeDescription_realizes L)
      (rejectOutputReturnDescription_realizes (rightEdgeTape0 L) L)

def rejectPrePaddingDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription rejectCoreDescription
    rejectEdgeRestoredOutputDescription
theorem rejectPrePaddingDescription_ready :
    rejectPrePaddingDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    rejectCoreDescription_ready rejectEdgeRestoredOutputDescription_ready

theorem rejectPrePaddingDescription_realizes
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        false) :
    rejectPrePaddingDescription.HaltsFromTapeEquiv
      (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
        false input)
      (encodedGuardedStructured3Tapes
        (rightEdgeTape0 input.L) Tape.blank
        (rejectFinalOutputTape2 input.L)) := by
  simpa [rejectPrePaddingDescription] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      rejectCoreDescription_ready rejectEdgeRestoredOutputDescription_ready
      (rejectCoreDescription_realizes_finalOutput input)
      (rejectEdgeRestoredOutputDescription_realizes input.L)

end RejectComposition
end Route
end InputMat
end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC


namespace FoC
namespace Computability

open Languages MachineDescription CommonGround.FiniteTransducers CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup
namespace InputMat
namespace Route
namespace RejectTape0Padding
namespace RejectNewComposition

open CanonicalLayouts.DovetailLayoutScanner RejectComposition AfterAcceptCountRuns

def prePaddingLocateDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription rejectPrePaddingDescription
    LocateAccept.loweredDescription
theorem prePaddingLocateDescription_ready :
    prePaddingLocateDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    rejectPrePaddingDescription_ready LocateAccept.loweredDescription_ready

theorem prePaddingLocateDescription_realizes
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        false) :
    prePaddingLocateDescription.HaltsFromTapeEquiv
      (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
        false input)
      (encodedGuardedStructured3Tapes
        (rightEdgeTape0 input.L) Tape.blank (afterLocateTape2 input.L)) := by
  simpa [prePaddingLocateDescription] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      rejectPrePaddingDescription_ready LocateAccept.loweredDescription_ready
      (rejectPrePaddingDescription_realizes input)
      (locateAcceptDescription_realizes input.L)
  done

def prePaddingAcceptScanDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription prePaddingLocateDescription
    AcceptScannerLift.description
theorem prePaddingAcceptScanDescription_ready :
    prePaddingAcceptScanDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    prePaddingLocateDescription_ready AcceptScannerLift.ready

theorem prePaddingAcceptScanDescription_realizes
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        false) :
    prePaddingAcceptScanDescription.HaltsFromTapeEquiv
      (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
        false input)
      (encodedGuardedStructured3Tapes
        (rightEdgeTape0 input.L) Tape.blank
        (afterAcceptScanTape2 input.L)) := by
  simpa [prePaddingAcceptScanDescription] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      prePaddingLocateDescription_ready AcceptScannerLift.ready
      (prePaddingLocateDescription_realizes input)
      (acceptScannerDescription_realizes input.L)
  done

def prePaddingAcceptCountDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription prePaddingAcceptScanDescription
    AfterAcceptCountRuns.loweredDescription
theorem prePaddingAcceptCountDescription_ready :
    prePaddingAcceptCountDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    prePaddingAcceptScanDescription_ready
    AfterAcceptCountRuns.loweredDescription_ready

theorem prePaddingAcceptCountDescription_realizes
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        false) :
    prePaddingAcceptCountDescription.HaltsFromTapeEquiv
      (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
        false input)
      (encodedGuardedStructured3Tapes
        (afterAcceptCountTape0 input.L) Tape.blank
        (afterAcceptCountTape2 input.L)) := by
  simpa [prePaddingAcceptCountDescription] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      prePaddingAcceptScanDescription_ready
      AfterAcceptCountRuns.loweredDescription_ready
      (prePaddingAcceptScanDescription_realizes input)
      (afterAcceptCountDescription_realizes input.L)
  done

def prePaddingGapCopyDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription prePaddingAcceptCountDescription
    GapCopy.loweredDescription
theorem prePaddingGapCopyDescription_ready :
    prePaddingGapCopyDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    prePaddingAcceptCountDescription_ready GapCopy.loweredDescription_ready

theorem prePaddingGapCopyDescription_realizes
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        false) :
    prePaddingGapCopyDescription.HaltsFromTapeEquiv
      (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
        false input)
      (encodedGuardedStructured3Tapes
        (afterGapCopyTape0 input.L) Tape.blank
        (afterGapCopyTape2 input.L)) := by
  simpa [prePaddingGapCopyDescription] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      prePaddingAcceptCountDescription_ready GapCopy.loweredDescription_ready
      (prePaddingAcceptCountDescription_realizes input)
      (gapCopyDescription_realizes input.L)
  done

end RejectNewComposition
end RejectTape0Padding
end Route
end InputMat
end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC


namespace FoC
namespace Computability

open Languages MachineDescription CommonGround.FiniteTransducers CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup
namespace InputMat
namespace Route
namespace RejectTape0Padding
namespace RejectFinalTape0

open CanonicalLayouts.DovetailLayoutScanner AfterAcceptCountRuns GapCopyReturnRuns AcceptFinalTail

def rejectTape0RightPadding (L : DovetailLayout) :
    List (Option Bool) :=
  List.append
    (List.replicate ((countedAcceptBits L).length + 3) none)
    (List.append ((boolFieldBits L.rejectHit []).map some) [none, none])
def rewoundRejectSourceTape0 (L : DovetailLayout) : Tape Bool :=
  Tape0RewindPadded.targetTape [] (sourceWord false L)
    (rejectTape0RightPadding L)

def beforeFinalTape0Rewind (L : DovetailLayout) : Tape Bool :=
  Tape0RewindPadded.sourceTape [] (sourceWord false L)
    (rejectTape0RightPadding L)

theorem finalTape0RewindDescription_realizes
    (L : DovetailLayout) (T2 : Tape Bool) :
    loweredTape0RewindDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (beforeFinalTape0Rewind L) Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (rewoundRejectSourceTape0 L) Tape.blank T2) := by
  exact loweredTape0RewindDescription_realizes
    [] (sourceWord false L) (rejectTape0RightPadding L) T2
  done
theorem rewoundRejectSourceTape0_eq_publicSource
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        false) :
    rewoundRejectSourceTape0 input.L =
      countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
        false input := by
  rw [countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource]
  unfold rewoundRejectSourceTape0 rejectTape0RightPadding
    Tape0RewindPadded.targetTape sourceWord
    boolWordRawBitsDecoderSourceTape
  rw [sourcePadding_reject_eq_acceptConfig_length input]
  simp only [countedAcceptBits,
    selectedProjectionPaddedTailCleanupSelectedHitBits]
  rw [if_neg (by decide : false ≠ true)]
  rfl

end RejectFinalTape0
end RejectTape0Padding
end Route
end InputMat
end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC


namespace FoC
namespace Computability

open Languages MachineDescription CommonGround.FiniteTransducers CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup
namespace InputMat
namespace Route
namespace RejectTape0Padding
namespace RejectMarkerReturn

open CanonicalLayouts.DovetailLayoutScanner GapCopyReturnRuns GapCopyReturnRuns.MarkerReturn RejectRawRewind
open RejectNewComposition RejectFinalTape0 RejectTape2Tail RejectLive RejectBranchShapes
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat.DirectTokenDriver

def markerReturnN0 (L : DovetailLayout) : Nat :=
  (AfterAcceptCountRuns.countedAcceptBits L).length - 1

def markerReturnN2 (L : DovetailLayout) : Nat :=
  (ParsedLayoutBits L).length + markerOffset L + 6
def markerReturnTailBits (L : DovetailLayout) : List Bool :=
  (rewindBits L).tail

def markerReturnRight2 (L : DovetailLayout) : List (Option Bool) :=
  List.append ((markerReturnTailBits L).map some)
    (none :: rewindRightPadding L)

def afterMarkerReturnTape0 (L : DovetailLayout) : Tape Bool :=
  MarkerReturn.targetTape0
    (AfterAcceptCountRuns.rightEdgeBase0 L)
    (markerReturnN0 L) (rewindRightPadding L)
def afterMarkerReturnTape2 (L : DovetailLayout) : Tape Bool :=
  MarkerReturn.targetTape2 [none] (markerReturnN2 L) false
    (markerReturnRight2 L)

theorem afterFixedBackTape0_eq_markerReturnSource (L : DovetailLayout) :
    afterFixedBackTape0 L =
      MarkerReturn.sourceTape0
        (AfterAcceptCountRuns.rightEdgeBase0 L)
        (markerReturnN0 L) (rewindRightPadding L) := by
  rfl

theorem rewindBits_eq_false_cons_tail (L : DovetailLayout) :
    rewindBits L = false :: markerReturnTailBits L := by
  rcases stageNatBits_cons_false L.stage with ⟨stageTail, hstage⟩
  unfold markerReturnTailBits rewindBits
  rw [hstage]
  rfl
theorem afterRawRewindTape2_eq_markerReturnSource (L : DovetailLayout) :
    afterRawRewindTape2 L =
      MarkerReturn.sourceTape2 [none] (markerReturnN2 L) false
        (markerReturnRight2 L) := by
  unfold afterRawRewindTape2 Tape2Rewinder.targetTapeWithContext
    rewindBase2 markerReturnN2 markerReturnRight2
    MarkerReturn.sourceTape2
  rw [rewindBits_eq_false_cons_tail]
  simp [List.replicate_succ, List.append_assoc]

theorem markerReturnDescription_realizes (L : DovetailLayout) :
    MarkerReturn.loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (afterFixedBackTape0 L) Tape.blank (afterRawRewindTape2 L))
      (encodedGuardedStructured3Tapes
        (afterMarkerReturnTape0 L) Tape.blank
        (afterMarkerReturnTape2 L)) := by
  rw [afterFixedBackTape0_eq_markerReturnSource]
  rw [afterRawRewindTape2_eq_markerReturnSource]
  simpa [afterMarkerReturnTape0, afterMarkerReturnTape2] using
    MarkerReturn.loweredDescription_realizes
      (AfterAcceptCountRuns.rightEdgeBase0 L) [none]
      (rewindRightPadding L) (markerReturnRight2 L)
      (markerReturnN0 L) (markerReturnN2 L) false Tape.blank

def prePaddingFixedBackDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription prePaddingGapCopyDescription
    FixedBack.loweredDescription
theorem prePaddingFixedBackDescription_ready :
    prePaddingFixedBackDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    prePaddingGapCopyDescription_ready FixedBack.loweredDescription_ready

theorem prePaddingFixedBackDescription_realizes
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        false) :
    prePaddingFixedBackDescription.HaltsFromTapeEquiv
      (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
        false input)
      (encodedGuardedStructured3Tapes
        (afterFixedBackTape0 input.L) Tape.blank
        (afterFixedBackTape2 input.L)) := by
  simpa [prePaddingFixedBackDescription] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      prePaddingGapCopyDescription_ready FixedBack.loweredDescription_ready
      (prePaddingGapCopyDescription_realizes input)
      (fixedBackDescription_realizes input.L)

def prePaddingRawRewindDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription prePaddingFixedBackDescription
    Tape2Rewinder.loweredDescription
theorem prePaddingRawRewindDescription_ready :
    prePaddingRawRewindDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    prePaddingFixedBackDescription_ready
    Tape2Rewinder.loweredDescription_subroutineReady

theorem prePaddingRawRewindDescription_realizes
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        false) :
    prePaddingRawRewindDescription.HaltsFromTapeEquiv
      (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
        false input)
      (encodedGuardedStructured3Tapes
        (afterFixedBackTape0 input.L) Tape.blank
        (afterRawRewindTape2 input.L)) := by
  simpa [prePaddingRawRewindDescription] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      prePaddingFixedBackDescription_ready
      Tape2Rewinder.loweredDescription_subroutineReady
      (prePaddingFixedBackDescription_realizes input)
      (rawRewindDescription_realizes input.L)

def prePaddingMarkerReturnDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription prePaddingRawRewindDescription
    MarkerReturn.loweredDescription
theorem prePaddingMarkerReturnDescription_ready :
    prePaddingMarkerReturnDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    prePaddingRawRewindDescription_ready
    MarkerReturn.loweredDescription_ready

theorem prePaddingMarkerReturnDescription_realizes
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        false) :
    prePaddingMarkerReturnDescription.HaltsFromTapeEquiv
      (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
        false input)
      (encodedGuardedStructured3Tapes
        (afterMarkerReturnTape0 input.L) Tape.blank
        (afterMarkerReturnTape2 input.L)) := by
  simpa [prePaddingMarkerReturnDescription] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      prePaddingRawRewindDescription_ready MarkerReturn.loweredDescription_ready
      (prePaddingRawRewindDescription_realizes input)
      (markerReturnDescription_realizes input.L)

theorem afterMarkerReturnTape0_eq_beforeFinalTape0Rewind
    (L : DovetailLayout) :
    afterMarkerReturnTape0 L = beforeFinalTape0Rewind L := by
  have hpos := configurationFieldBits_length_pos L.acceptConfig
  have hsub :
      (AfterAcceptCountRuns.countedAcceptBits L).length - 1 + 1 =
        (AfterAcceptCountRuns.countedAcceptBits L).length := by
    have hpos' : 0 <
        (AfterAcceptCountRuns.countedAcceptBits L).length := by
      simpa [AfterAcceptCountRuns.countedAcceptBits] using hpos
    exact Nat.sub_add_cancel (by lia)
  unfold afterMarkerReturnTape0 MarkerReturn.targetTape0 markerReturnN0
    beforeFinalTape0Rewind
    AcceptFinalTail.Tape0RewindPadded.sourceTape
    rejectTape0RightPadding rewindRightPadding
  rw [hsub]
  simp [AfterAcceptCountRuns.rightEdgeBase0,
    list_replicate_add_append, List.append_assoc]
theorem afterMarkerReturnTape2_eq_publicTarget (L : DovetailLayout) :
    afterMarkerReturnTape2 L = rejectFinalOutputTape2 L := by
  rw [rejectFinalOutputTape2_shape]
  have hbits :
      some false :: (markerReturnTailBits L).map some =
        (rewindBits L).map some := by
    exact (congrArg (fun bits : List Bool => bits.map some)
      (rewindBits_eq_false_cons_tail L)).symm
  have hprefix :
      none :: List.replicate (markerReturnN2 L + 1)
          (none : Option Bool) =
        List.replicate
          ((ParsedLayoutBits L).length + markerOffset L + 8) none := by
    rw [← List.replicate_succ]
    unfold markerReturnN2
    congr 1
  have hlive :
      List.append
          (some false :: (markerReturnTailBits L).map some)
          (none :: rewindRightPadding L) =
        List.append ((rejectKeptPrefixBits L).map some)
          (List.append (List.replicate 4 none)
            (List.append
              ((RejectBranchShapes.rejectHitBits L).map some)
              [none, none])) := by
    rw [hbits]
    unfold rewindBits gapCopyData rejectKeptPrefixBits
      rewindRightPadding
    simp [AfterAcceptCountRuns.countedAcceptBits,
      AcceptBranch.acceptBits, AcceptBranch.rejectBits,
      RejectBranchShapes.rejectHitBits,
      List.replicate_succ, List.append_assoc]
  unfold afterMarkerReturnTape2 MarkerReturn.targetTape2
    markerReturnRight2
  change
    tapeAtCells [none]
        (List.append
          (none :: List.replicate (markerReturnN2 L + 1) none)
          (List.append
            (some false :: (markerReturnTailBits L).map some)
            (none :: rewindRightPadding L))) =
      tapeAtCells [none]
        (List.append
          (List.replicate
            ((ParsedLayoutBits L).length + markerOffset L + 8) none)
          (List.append ((rejectKeptPrefixBits L).map some)
            (List.append (List.replicate 4 none)
              (List.append
                ((RejectBranchShapes.rejectHitBits L).map some)
                [none, none]))))
  rw [hprefix, hlive]

def rejectCompletedDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription prePaddingMarkerReturnDescription
    AcceptFinalTail.loweredTape0RewindDescription

theorem rejectCompletedDescription_ready :
    rejectCompletedDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    prePaddingMarkerReturnDescription_ready
    AcceptFinalTail.loweredTape0RewindDescription_ready
theorem rejectCompletedDescription_realizes
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        false) :
    rejectCompletedDescription.HaltsFromTapeEquiv
      (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
        false input)
      (structured3InputMaterializerTargetTape
        (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
          false input)
        (countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputTape
          false input)) := by
  have hfinal := finalTape0RewindDescription_realizes
    input.L (afterMarkerReturnTape2 input.L)
  rw [← afterMarkerReturnTape0_eq_beforeFinalTape0Rewind] at hfinal
  have h := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    prePaddingMarkerReturnDescription_ready
    AcceptFinalTail.loweredTape0RewindDescription_ready
    (prePaddingMarkerReturnDescription_realizes input) hfinal
  rw [rewoundRejectSourceTape0_eq_publicSource input] at h
  rw [afterMarkerReturnTape2_eq_publicTarget,
    rejectFinalOutputTape2_eq_publicTarget] at h
  simpa [rejectCompletedDescription,
    structured3InputMaterializerTargetTape,
    countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputTape]
    using h

end RejectMarkerReturn
end RejectTape0Padding
end Route
end InputMat
end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC

namespace FoC
namespace Computability

open Languages MachineDescription CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup
namespace InputMat
namespace Route
namespace IndexedConstruction

open CanonicalLayouts.DovetailLayoutScanner RejectTape0Padding.RejectMarkerReturn

theorem acceptDescription_spec :
    CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec
      true acceptDescription := by
  exact ⟨acceptDescription_ready, acceptDescription_realizes⟩
  done

theorem acceptDescription_indexedSpec :
    CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec
      true acceptDescription := by
  exact
    countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec_of_boolWordSpec
      acceptDescription_spec
  done
theorem rejectDescription_spec :
    CountWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSpec
      false rejectCompletedDescription := by
  exact ⟨rejectCompletedDescription_ready, rejectCompletedDescription_realizes⟩
  done

theorem rejectDescription_indexedSpec :
    CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec
      false rejectCompletedDescription := by
  exact
    countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerSpec_of_boolWordSpec
      rejectDescription_spec
  done

theorem indexedBoolWordMaterializerConstruction :
    CountWindowPostFieldDecodedPrefixStructuredIndexedBoolWordMaterializerConstruction := by
  intro useAccept
  cases useAccept
  case false =>
    exact ⟨rejectCompletedDescription, rejectDescription_indexedSpec⟩
  case true =>
    exact ⟨acceptDescription, acceptDescription_indexedSpec⟩
  done

end IndexedConstruction
end Route
end InputMat
end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
