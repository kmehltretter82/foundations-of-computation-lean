import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.IndexedMaterializer.RejectBranch

set_option doc.verso true

/-!
Rejecting-route gap erasure and tape-2 tail reconstruction.
-/

set_option linter.unusedSimpArgs false

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace FoC
namespace Computability

open Languages MachineDescription CommonGround.FiniteTransducers

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup
namespace InputMat
namespace Route
namespace RejectGapShapes

open CanonicalLayouts.DovetailLayoutScanner CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat.DirectTokenDriver
open RejectBranchShapes RejectContinuation RejectLive

theorem copiedRejectBits_length_le_markerOffset (L : DovetailLayout) :
    (copiedRejectBits L).length <= markerOffset L := by
  simp [copiedRejectBits, markerOffset, inputStageBits, stageBits]

theorem directScratchBlankDriverBits_reject_length (L : DovetailLayout) :
    (directScratchBlankDriverBits false L).length = markerOffset L + 8 := by
  simp [directScratchBlankDriverBits, markerOffset, inputStageBits,
    stageBits, rejectBits, boolFieldBits_nil_length,
    selectedProjectionPaddedTailCleanupSelectedConfigBits]
  lia
theorem dataBits_take_marker_length (L : DovetailLayout) :
    ((dataBits L).take (markerOffset L)).length = markerOffset L := by
  rw [List.length_take, Nat.min_eq_left
    (Nat.le_of_lt (markerOffset_lt_dataBits_length L))]


def rejectBeforeGapBits (L : DovetailLayout) : List Bool :=
  List.append (inputStageBits L)
    ((pairSourceBits L).take (rejectBits L).length)

theorem dataBits_eq_beforeGap_remaining (L : DovetailLayout) :
    dataBits L =
      List.append (rejectBeforeGapBits L) (remainingPairBits L) := by
  rw [dataBits_eq_inputStage_pairSource]
  simp [rejectBeforeGapBits, remainingPairBits, List.append_assoc,
    List.take_append_drop]
theorem rejectBeforeGapBits_length (L : DovetailLayout) :
    (rejectBeforeGapBits L).length = markerOffset L := by
  simp [rejectBeforeGapBits, markerOffset, List.length_take,
    Nat.min_eq_left
      (Nat.le_of_lt (rejectBits_length_lt_pairSourceBits_length L))]

theorem rejectBeforeGapBits_eq_take_marker (L : DovetailLayout) :
    rejectBeforeGapBits L = (dataBits L).take (markerOffset L) := by
  rw [dataBits_eq_beforeGap_remaining, ← rejectBeforeGapBits_length]
  exact (List.take_left
    (l₁ := rejectBeforeGapBits L) (l₂ := remainingPairBits L)).symm

theorem remainingPair_after_length
    (L : DovetailLayout) (markedBit : Bool) (after : List Bool)
    (hremaining : remainingPairBits L = markedBit :: after) :
    after.length = (acceptBits L).length + 7 := by
  have hlen := congrArg List.length (dataBits_eq_beforeGap_remaining L)
  rw [hremaining] at hlen
  rw [dataBits_length] at hlen
  simp at hlen
  rw [rejectBeforeGapBits_length] at hlen
  unfold markerOffset at hlen
  lia
theorem continuation_beforeGapBits_eq (L : DovetailLayout) :
    RejectContinuation.beforeGapBits L = rejectBeforeGapBits L := by
  rfl

theorem continuation_rejectRewoundTape2_eq (L : DovetailLayout) :
    RejectContinuation.rejectRewoundTape2 L =
      Tape2Rewinder.targetTapeWithContext (commonCounterBaseTail L)
        (copiedRejectBits L) [] := by
  rfl

theorem rawBoundaryRest_reject_eq_false_false_drop (L : DovetailLayout) :
    MarkerAwareCommon.rawBoundaryRest false L =
      false :: false ::
        (MarkerAwareCommon.rawBoundaryRest false L).drop 2 := by
  rcases
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_false_false_tail
        L.stage with
    ⟨tail, htail⟩
  rw [MarkerAwareCommon.rawBoundaryRest,
    false_cons_structuredSuffixTail]
  simp [htail]
theorem rawBoundaryRest_reject_map_eq (L : DovetailLayout) :
    (MarkerAwareCommon.rawBoundaryRest false L).map some =
      some false :: some false ::
        ((MarkerAwareCommon.rawBoundaryRest false L).drop 2).map
          some := by
  have h := congrArg (List.map some)
    (rawBoundaryRest_reject_eq_false_false_drop L)
  simpa using h

def afterMarkedEraseTape0 (L : DovetailLayout) : Tape Bool :=
  match remainingPairBits L with
  | [] => RejectContinuation.dataMarkedTape0 L
  | markedBit :: after =>
      MarkedErase.scanOptionTape
        (List.append
          (List.append
            (List.append
              (MarkedErase.wrappedOptionsWord after).reverse
              (MarkedErase.wrappedOptions markedBit).reverse)
            (MarkedErase.wrappedOptionsWord
              (RejectContinuation.beforeGapBits L)).reverse)
          (MarkerAwareCommon.commonEndpointLeft L))
        (some false :: some false ::
          ((MarkerAwareCommon.rawBoundaryRest false L).drop 2).map
            some)

theorem markedEraseAtData_run
    (L : DovetailLayout) (markedBit : Bool) (after : List Bool)
    (hremaining : remainingPairBits L = markedBit :: after) :
    MarkedErase.description.runConfig
        (MarkedErase.markedFuel
          (RejectContinuation.beforeGapBits L) after)
        (config MarkedErase.loop
          (RejectContinuation.dataMarkedTape0 L) Tape.blank
          (RejectContinuation.rejectRewoundTape2 L)) =
      config MarkedErase.halt (afterMarkedEraseTape0 L) Tape.blank
        (MarkedErase.eraseBits after
          ((writeBitR true).apply
            (MarkedErase.eraseBits
              (RejectContinuation.beforeGapBits L)
              (RejectContinuation.rejectRewoundTape2 L)))) := by
  have hrun := MarkedErase.run
    (RejectContinuation.beforeGapBits L) after markedBit
    (MarkerAwareCommon.commonEndpointLeft L)
    (((MarkerAwareCommon.rawBoundaryRest false L).drop 2).map some)
    (RejectContinuation.rejectRewoundTape2 L)
  have hsource : RejectContinuation.dataMarkedTape0 L =
      MarkedErase.scanOptionTape
        (MarkerAwareCommon.commonEndpointLeft L)
        (List.append
          (MarkedErase.wrappedOptionsWord
            (RejectContinuation.beforeGapBits L))
          (List.append (MarkedErase.markedOptions markedBit)
            (List.append (MarkedErase.wrappedOptionsWord after)
              (some false :: some false ::
                ((MarkerAwareCommon.rawBoundaryRest false L).drop 2).map
                  some)))) := by
    rw [RejectContinuation.dataMarkedTape0, hremaining]
    rw [rawBoundaryRest_reject_map_eq]
    done
  have htarget : afterMarkedEraseTape0 L =
      MarkedErase.scanOptionTape
        (List.append
          (List.append
            (List.append
              (MarkedErase.wrappedOptionsWord after).reverse
              (MarkedErase.wrappedOptions markedBit).reverse)
            (MarkedErase.wrappedOptionsWord
              (RejectContinuation.beforeGapBits L)).reverse)
          (MarkerAwareCommon.commonEndpointLeft L))
        (some false :: some false ::
          ((MarkerAwareCommon.rawBoundaryRest false L).drop 2).map
            some) := by
    rw [afterMarkedEraseTape0, hremaining]
  rw [hsource, htarget]
  exact hrun
theorem eraseRight_step
    (cell : Option Bool) (left right : List (Option Bool)) :
    eraseR.apply (tapeAtCells left (cell :: right)) =
      tapeAtCells (none :: left) right := by
  cases right <;> rfl

theorem eraseRight_tapeAtCells
    (n : Nat) (cells left : List (Option Bool)) :
    Components.eraseRight n
        (tapeAtCells left (List.append cells [none])) =
      tapeAtCells
        (List.append (List.replicate n (none : Option Bool)) left)
        (List.append (cells.drop n) [none]) := by
  induction n generalizing cells left with
  | zero => rfl
  | succ n ih =>
      cases cells with
      | nil =>
          simp only [List.drop]
          rw [Components.eraseRight]
          change Components.eraseRight n
              (tapeAtCells (none :: left) [none]) = _
          have h := ih [] (none :: left)
          rw [List.drop_nil] at h
          have h' :
              Components.eraseRight n
                  (tapeAtCells (none :: left) [none]) =
                tapeAtCells
                  (List.append (List.replicate n (none : Option Bool))
                    (none :: left)) [none] := by
            simpa using h
          rw [h']
          rw [MarkerScanLeft.replicate_none_append_cons]
          rfl
      | cons cell cells =>
          rw [Components.eraseRight]
          change Components.eraseRight n
              (eraseR.apply
                (tapeAtCells left
                  (List.append (cell :: cells) [none]))) = _
          change Components.eraseRight n
              (eraseR.apply
                (tapeAtCells left
                  (cell :: List.append cells [none]))) = _
          rw [eraseRight_step]
          rw [ih]
          rw [MarkerScanLeft.replicate_none_append_cons]
          rfl

theorem eraseBits_eq_eraseRight
    (bits : List Bool) (T : Tape Bool) :
    MarkedErase.eraseBits bits T = Components.eraseRight bits.length T := by
  induction bits generalizing T with
  | nil => rfl
  | cons bit bits ih =>
      simp only [MarkedErase.eraseBits, List.length_cons]
      rw [Components.eraseRight]
      exact ih (eraseR.apply T)
theorem drop_map_some (n : Nat) (bits : List Bool) :
    (bits.map some).drop n = (bits.drop n).map some := by
  induction n generalizing bits with
  | zero => rfl
  | succ n ih =>
      cases bits with
      | nil => rfl
      | cons bit bits => exact ih bits

theorem eraseBefore_rejectRewound_shape
    (L : DovetailLayout) (base2 : List (Option Bool)) :
    MarkedErase.eraseBits ((dataBits L).take (markerOffset L))
        (Tape2Rewinder.targetTapeWithContext base2 (copiedRejectBits L) []) =
      tapeAtCells
        (List.append
          (List.replicate (markerOffset L) (none : Option Bool))
          (none :: base2)) [none] := by
  rw [eraseBits_eq_eraseRight]
  unfold Tape2Rewinder.targetTapeWithContext
  rw [dataBits_take_marker_length]
  rw [eraseRight_tapeAtCells]
  rw [drop_map_some]
  have hdrop : (copiedRejectBits L).drop (markerOffset L) = [] :=
    List.drop_eq_nil_of_le (copiedRejectBits_length_le_markerOffset L)
  rw [hdrop]
  rfl

def gapMarkerBase
    (L : DovetailLayout) (base2 : List (Option Bool)) :
    List (Option Bool) :=
  List.append
    (List.replicate (markerOffset L) (none : Option Bool))
    (none :: base2)
theorem writeBitR_true_blank
    (left : List (Option Bool)) :
    (writeBitR true).apply (tapeAtCells left [none]) =
      tapeAtCells (some true :: left) [none] := by
  rfl

theorem markedEraseOutput_eq_markerScanSource
    (L : DovetailLayout) (base2 : List (Option Bool))
    (after : List Bool) :
    MarkedErase.eraseBits after
        ((writeBitR true).apply
          (MarkedErase.eraseBits
            ((dataBits L).take (markerOffset L))
            (Tape2Rewinder.targetTapeWithContext base2 (copiedRejectBits L) []))) =
      MarkerScanLeft.sourceTape (gapMarkerBase L base2) after.length := by
  rw [eraseBefore_rejectRewound_shape]
  rw [writeBitR_true_blank]
  rw [eraseBits_eq_eraseRight]
  simpa [MarkerScanLeft.sourceTape, gapMarkerBase] using
    (eraseRight_tapeAtCells after.length []
      (some true ::
        List.append
          (List.replicate (markerOffset L) (none : Option Bool))
          (none :: base2)))

theorem markedEraseTape2_eq_markerScanSource
    (L : DovetailLayout) (after : List Bool) :
    MarkedErase.eraseBits after
        ((writeBitR true).apply
          (MarkedErase.eraseBits
            (RejectContinuation.beforeGapBits L)
            (RejectContinuation.rejectRewoundTape2 L))) =
      MarkerScanLeft.sourceTape
        (gapMarkerBase L (commonCounterBaseTail L)) after.length := by
  rw [continuation_beforeGapBits_eq,
    rejectBeforeGapBits_eq_take_marker,
    continuation_rejectRewoundTape2_eq]
  exact markedEraseOutput_eq_markerScanSource L
    (commonCounterBaseTail L) after

theorem markedEraseDescription_realizes_reject
    (L : DovetailLayout) (markedBit : Bool) (after : List Bool)
    (hremaining : remainingPairBits L = markedBit :: after) :
    AcceptInternalMarker.markedEraseDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (RejectContinuation.dataMarkedTape0 L) Tape.blank
        (RejectContinuation.rejectRewoundTape2 L))
      (encodedGuardedStructured3Tapes
        (afterMarkedEraseTape0 L) Tape.blank
        (MarkerScanLeft.sourceTape
          (gapMarkerBase L (commonCounterBaseTail L)) after.length)) := by
  have hrun := markedEraseAtData_run L markedBit after hremaining
  rw [markedEraseTape2_eq_markerScanSource] at hrun
  simpa [AcceptInternalMarker.markedEraseDescription,
    encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      AcceptInternalMarker.markedErase_ready.left
      AcceptInternalMarker.markedErase_ready.right
      AcceptInternalMarker.markedErase_supports
      (c := config MarkedErase.loop
        (RejectContinuation.dataMarkedTape0 L) Tape.blank
        (RejectContinuation.rejectRewoundTape2 L))
      (tapes :=
        [ afterMarkedEraseTape0 L
        , Tape.blank
        , MarkerScanLeft.sourceTape
            (gapMarkerBase L (commonCounterBaseTail L)) after.length ])
      rfl rfl
      ⟨MarkedErase.markedFuel
          (RejectContinuation.beforeGapBits L) after,
        hrun⟩

def markerScanDescription : MachineDescription :=
  lowerStructured3Description MarkerScanLeft.description

theorem markerScan_ready : MarkerScanLeft.description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool MarkerScanLeft.description
    (by decide)
theorem markerScan_supports :
    SupportsReadWriteRows3 MarkerScanLeft.description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

theorem markerScanDescription_ready :
    markerScanDescription.SubroutineReady := by
  simpa [markerScanDescription] using
    lowerStructured3Description_subroutineReady
      markerScan_ready.left markerScan_supports

theorem markerScanDescription_realizes_reject
    (L : DovetailLayout) (after : List Bool) :
    markerScanDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (afterMarkedEraseTape0 L) Tape.blank
        (MarkerScanLeft.sourceTape
          (gapMarkerBase L (commonCounterBaseTail L)) after.length))
      (encodedGuardedStructured3Tapes
        (afterMarkedEraseTape0 L) Tape.blank
        (MarkerScanLeft.targetTape
          (gapMarkerBase L (commonCounterBaseTail L)) after.length)) := by
  have hrun := MarkerScanLeft.run after.length (afterMarkedEraseTape0 L)
    Tape.blank (gapMarkerBase L (commonCounterBaseTail L))
  simpa [markerScanDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      markerScan_ready.left markerScan_ready.right markerScan_supports
      (c := config MarkerScanLeft.enter (afterMarkedEraseTape0 L)
        Tape.blank
        (MarkerScanLeft.sourceTape
          (gapMarkerBase L (commonCounterBaseTail L)) after.length))
      (tapes :=
        [ afterMarkedEraseTape0 L
        , Tape.blank
        , MarkerScanLeft.targetTape
            (gapMarkerBase L (commonCounterBaseTail L)) after.length ])
      rfl rfl ⟨MarkerScanLeft.fuel after.length, hrun⟩
def rejectGapDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    AcceptInternalMarker.markedEraseDescription markerScanDescription

theorem rejectGapDescription_ready : rejectGapDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    AcceptInternalMarker.markedEraseDescription_ready
    markerScanDescription_ready

def rejectMarkerTargetTape2 (L : DovetailLayout) : Tape Bool :=
  match remainingPairBits L with
  | [] => RejectContinuation.rejectRewoundTape2 L
  | _ :: after =>
      MarkerScanLeft.targetTape
        (gapMarkerBase L (commonCounterBaseTail L)) after.length
theorem rejectGapDescription_realizes (L : DovetailLayout) :
    rejectGapDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (RejectContinuation.dataMarkedTape0 L) Tape.blank
        (RejectContinuation.rejectRewoundTape2 L))
      (encodedGuardedStructured3Tapes
        (afterMarkedEraseTape0 L) Tape.blank
        (rejectMarkerTargetTape2 L)) := by
  rcases remainingPairBits_exists_cons L with
    ⟨markedBit, after, hremaining⟩
  have he := markedEraseDescription_realizes_reject
    L markedBit after hremaining
  have hs := markerScanDescription_realizes_reject L after
  have h := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    AcceptInternalMarker.markedEraseDescription_ready
    markerScanDescription_ready he hs
  simpa [rejectGapDescription, rejectMarkerTargetTape2, hremaining] using h

theorem afterMarkedEraseTape0_eq_rejectAtBoundaryTape0
    (L : DovetailLayout) :
    afterMarkedEraseTape0 L = RejectLive.rejectAtBoundaryTape0 L := by
  rcases remainingPairBits_exists_cons L with
    ⟨markedBit, after, hremaining⟩
  rw [afterMarkedEraseTape0, hremaining]
  simp only
  unfold RejectLive.rejectAtBoundaryTape0
  have hright :
      some false :: some false ::
          ((MarkerAwareCommon.rawBoundaryRest false L).drop 2).map
            some =
        (MarkerAwareCommon.rawBoundaryRest false L).map some :=
    (rawBoundaryRest_reject_map_eq L).symm
  have hdata : RejectBranchShapes.dataBits L =
      List.append (RejectContinuation.beforeGapBits L)
        (markedBit :: after) := by
    rw [dataBits_eq_beforeGap_remaining, hremaining,
      continuation_beforeGapBits_eq]
  have hleft :
      List.append
          (List.append
            (List.append
              (MarkedErase.wrappedOptionsWord after).reverse
              (MarkedErase.wrappedOptions markedBit).reverse)
            (MarkedErase.wrappedOptionsWord
              (RejectContinuation.beforeGapBits L)).reverse)
          (MarkerAwareCommon.commonEndpointLeft L) =
        List.append
          ((AcceptConfigCopy.wrappedBits (ParsedLayoutBits L)).reverse.map
            some)
          (none :: MarkerAwareCommon.primaryMarkerBaseLeft L) := by
    unfold MarkedErase.wrappedOptionsWord MarkedErase.wrappedOptions
    rw [MarkerAwareCommon.commonEndpointLeft]
    rw [MarkerAwareCommon.wrappedBits_parsed_eq_header_false_data]
    rw [common_dataBits_eq_dataBits]
    rw [hdata]
    rw [Route.wrappedBits_append]
    simp [AcceptConfigCopy.wrappedBits, AcceptConfigCopy.wrappedBit,
      List.reverse_append, List.map_append, List.append_assoc]
  rw [hleft, hright]
  rfl
  done


end RejectGapShapes
end Route
end InputMat
end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC

set_option maxRecDepth 20000

namespace FoC
namespace Computability

open Languages MachineDescription CommonGround.FiniteTransducers CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup
namespace InputMat
namespace Route
namespace RejectTape2Tail

open CanonicalLayouts.DovetailLayoutScanner CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat.DirectTokenDriver
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat.Tape2Rewinder
open MarkerAwareCommon AcceptBranch AcceptFinish AcceptReconstructPrefix RejectContinuation RejectLive
open RejectBranchShapes RejectGapShapes

/-! Eight-cell advance from the transferred reject marker. -/

def moveTape2RightTwoDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription moveRightOneDescription
    moveRightOneDescription
def moveTape2RightFourDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription moveTape2RightTwoDescription
    moveTape2RightTwoDescription

def moveTape2RightEightDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription moveTape2RightFourDescription
    moveTape2RightFourDescription

theorem moveTape2RightTwoDescription_ready :
    moveTape2RightTwoDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    moveRightOneDescription_ready moveRightOneDescription_ready
theorem moveTape2RightFourDescription_ready :
    moveTape2RightFourDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    moveTape2RightTwoDescription_ready moveTape2RightTwoDescription_ready

theorem moveTape2RightEightDescription_ready :
    moveTape2RightEightDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    moveTape2RightFourDescription_ready moveTape2RightFourDescription_ready

def moveTape2RightTwo (T : Tape Bool) : Tape Bool :=
  keepR.apply (keepR.apply T)
def moveTape2RightFour (T : Tape Bool) : Tape Bool :=
  moveTape2RightTwo (moveTape2RightTwo T)

def moveTape2RightEight (T : Tape Bool) : Tape Bool :=
  moveTape2RightFour (moveTape2RightFour T)

theorem moveTape2RightTwoDescription_realizes
    (T0 T2 : Tape Bool) :
    moveTape2RightTwoDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes T0 Tape.blank T2)
      (encodedGuardedStructured3Tapes T0 Tape.blank
        (moveTape2RightTwo T2)) := by
  simpa [moveTape2RightTwoDescription, moveTape2RightTwo] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      moveRightOneDescription_ready moveRightOneDescription_ready
      (moveRightOneDescription_realizes T0 T2)
      (moveRightOneDescription_realizes T0 (keepR.apply T2))
theorem moveTape2RightFourDescription_realizes
    (T0 T2 : Tape Bool) :
    moveTape2RightFourDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes T0 Tape.blank T2)
      (encodedGuardedStructured3Tapes T0 Tape.blank
        (moveTape2RightFour T2)) := by
  simpa [moveTape2RightFourDescription, moveTape2RightFour] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      moveTape2RightTwoDescription_ready moveTape2RightTwoDescription_ready
      (moveTape2RightTwoDescription_realizes T0 T2)
      (moveTape2RightTwoDescription_realizes T0 (moveTape2RightTwo T2))

theorem moveTape2RightEightDescription_realizes
    (T0 T2 : Tape Bool) :
    moveTape2RightEightDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes T0 Tape.blank T2)
      (encodedGuardedStructured3Tapes T0 Tape.blank
        (moveTape2RightEight T2)) := by
  simpa [moveTape2RightEightDescription, moveTape2RightEight] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      moveTape2RightFourDescription_ready moveTape2RightFourDescription_ready
      (moveTape2RightFourDescription_realizes T0 T2)
      (moveTape2RightFourDescription_realizes T0 (moveTape2RightFour T2))

theorem moveTape2RightEight_blanks
    (left right : List (Option Bool)) :
    moveTape2RightEight
        (tapeAtCells left
          (List.append (List.replicate 8 (none : Option Bool)) right)) =
      tapeAtCells
        (List.append (List.replicate 8 (none : Option Bool)) left) right := by
  cases right <;>
    rfl
def rejectLiveBase (L : DovetailLayout) : List (Option Bool) :=
  List.append (List.replicate 8 (none : Option Bool))
    (gapMarkerBase L (commonCounterBaseTail L))

def rejectLiveStartTape2 (L : DovetailLayout) : Tape Bool :=
  tapeAtCells (rejectLiveBase L)
    (List.replicate ((RejectBranchShapes.acceptBits L).length + 1)
      (none : Option Bool))

theorem rejectMarkerTarget_moveRightEight (L : DovetailLayout) :
    moveTape2RightEight (rejectMarkerTargetTape2 L) =
      rejectLiveStartTape2 L := by
  rcases remainingPairBits_exists_cons L with
    ⟨markedBit, after, hremaining⟩
  have hafter := remainingPair_after_length L markedBit after hremaining
  rw [rejectMarkerTargetTape2, hremaining]
  unfold MarkerScanLeft.targetTape rejectLiveStartTape2
  have hright :
      none ::
          List.append (List.replicate after.length (none : Option Bool))
            [none] =
        List.append (List.replicate 8 (none : Option Bool))
          (List.replicate
            ((RejectBranchShapes.acceptBits L).length + 1) none) := by
    have htail :
        List.append (List.replicate after.length (none : Option Bool))
            [none] =
          List.replicate (after.length + 1) none := by
      rw [show [none] = List.replicate 1 (none : Option Bool) by rfl]
      rw [AcceptFinish.replicate_none_append_replicate]
    rw [htail]
    rw [show none :: List.replicate (after.length + 1)
          (none : Option Bool) =
        List.replicate (after.length + 2) none by
      calc
        none :: List.replicate (after.length + 1) (none : Option Bool) =
            List.replicate ((after.length + 1) + 1) none :=
          (List.replicate_succ
            (n := after.length + 1) (a := (none : Option Bool))).symm
        _ = List.replicate (after.length + 2) none := by congr 1 <;> lia]
    rw [AcceptFinish.replicate_none_append_replicate]
    congr 1
    lia
  change moveTape2RightEight
      (tapeAtCells (gapMarkerBase L (commonCounterBaseTail L))
        (none ::
          List.append (List.replicate after.length (none : Option Bool))
            [none])) = _
  rw [hright, moveTape2RightEight_blanks]
  rfl
theorem moveTape2RightEight_at_reject_gap_realizes (L : DovetailLayout) :
    moveTape2RightEightDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (afterMarkedEraseTape0 L) Tape.blank (rejectMarkerTargetTape2 L))
      (encodedGuardedStructured3Tapes
        (rejectAtBoundaryTape0 L) Tape.blank (rejectLiveStartTape2 L)) := by
  have h := moveTape2RightEightDescription_realizes
    (afterMarkedEraseTape0 L) (rejectMarkerTargetTape2 L)
  rw [rejectMarkerTarget_moveRightEight] at h
  simpa only [afterMarkedEraseTape0_eq_rejectAtBoundaryTape0] using h

/-! Exact live overwrite and accept-hit cleanup. -/

theorem writeWordRight_blank_run_of_lt
    (new : Word Bool) (blankTail : Nat)
    (left : List (Option Bool))
    (h : blankTail < new.length) :
    writeWordRight new
        (tapeAtCells left
          (List.replicate (blankTail + 1) (none : Option Bool))) =
      tapeAtCells (List.append (new.reverse.map some) left) [none] := by
  induction new generalizing blankTail left with
  | nil => simp at h
  | cons bit rest ih =>
      cases blankTail with
      | zero =>
          cases rest with
          | nil => cases bit <;> rfl
          | cons next tail =>
              rw [writeWordRight]
              change writeWordRight (next :: tail)
                  (tapeAtCells (some bit :: left) [none]) = _
              have hrest : 0 < (next :: tail).length := by simp
              simpa [List.reverse_cons, List.map_append,
                List.append_assoc] using
                ih 0 (some bit :: left) hrest
      | succ blankTail =>
          rw [writeWordRight]
          change writeWordRight rest
              (tapeAtCells (some bit :: left)
                (List.replicate (blankTail + 1) none)) = _
          have hrest : blankTail < rest.length := by
            simpa using h
          rw [ih blankTail (some bit :: left) hrest]
          simp [List.reverse_cons, List.map_append, List.append_assoc]

def rejectCopiedLiveTape2 (L : DovetailLayout) : Tape Bool :=
  tapeAtCells
    (List.append ((liveBits L).reverse.map some) (rejectLiveBase L)) [none]
theorem writeLive_at_rejectStart_eq_copied (L : DovetailLayout) :
    writeWordRight (liveBits L) (rejectLiveStartTape2 L) =
      rejectCopiedLiveTape2 L := by
  have hlength :
      (RejectBranchShapes.acceptBits L).length < (liveBits L).length := by
    simp [liveBits, RejectBranchShapes.acceptBits,
      AcceptBranch.acceptBits, AcceptBranch.rejectBits,
      AcceptBranch.acceptHitBits, AcceptBranch.rejectHitBits,
      boolFieldBits_nil_length]
    lia
  simpa [rejectLiveStartTape2, rejectCopiedLiveTape2] using
    writeWordRight_blank_run_of_lt (liveBits L)
      (RejectBranchShapes.acceptBits L).length (rejectLiveBase L)
      hlength

def rejectCleanedTape2 (L : DovetailLayout) : Tape Bool :=
  rejectCleanedLiveEndTape2 (rejectLiveBase L) L

theorem rejectLiveCleanup_realizes (L : DovetailLayout) :
    (canonicalPrimitiveSeqDescription rejectLiveDescription
      rejectCleanupDescription).HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rejectAtBoundaryTape0 L) Tape.blank (rejectLiveStartTape2 L))
      (encodedGuardedStructured3Tapes
        (rejectAfterLiveCopyTape0 L) Tape.blank (rejectCleanedTape2 L)) := by
  have hl := rejectLiveDescription_realizes L (rejectLiveStartTape2 L)
  rw [writeLive_at_rejectStart_eq_copied] at hl
  have hc := rejectCleanupDescription_realizes
    (rejectAfterLiveCopyTape0 L) (rejectCopiedLiveTape2 L)
  have hclean :
      rejectCleanupApply (rejectCopiedLiveTape2 L) =
        rejectCleanedTape2 L := by
    simpa [rejectCopiedLiveTape2, rejectCleanedTape2] using
      rejectCleanup_exact (rejectLiveBase L) L
  rw [hclean] at hc
  simpa [rejectCleanedTape2] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      rejectLiveDescription_ready rejectCleanupDescription_ready hl hc

/-! Rewind the two visible segments around the four-cell blank hole. -/
def rejectHitRewindBase (L : DovetailLayout) : List (Option Bool) :=
  List.append (List.replicate 3 (none : Option Bool))
    (List.append ((rejectKeptPrefixBits L).reverse.map some)
      (rejectLiveBase L))

def rejectHitRewindSourceTape2 (L : DovetailLayout) : Tape Bool :=
  Tape2Rewinder.sourceTapeWithContext
    (rejectHitRewindBase L) (RejectBranchShapes.rejectHitBits L) [none]

def rejectHitRewindTargetTape2 (L : DovetailLayout) : Tape Bool :=
  Tape2Rewinder.targetTapeWithContext
    (rejectHitRewindBase L) (RejectBranchShapes.rejectHitBits L) [none]
theorem cleaned_moveLeftOne_eq_rejectHitSource (L : DovetailLayout) :
    keepL.apply (rejectCleanedTape2 L) = rejectHitRewindSourceTape2 L := by
  simp [rejectCleanedTape2, rejectCleanedLiveEndTape2,
    rejectHitRewindSourceTape2,
    Tape2Rewinder.sourceTapeWithContext, rejectHitRewindBase,
    AcceptBranch.rejectHitBits,
    RejectBranchShapes.rejectHitBits,
    keepL, TapeAction.apply, HeadMove.apply, Tape.move, Tape.moveLeft,
    tapeAtCells, List.append_assoc]

def rejectMoveHitRewindDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription moveTape2LeftOneDescription
    Tape2Rewinder.loweredDescription

theorem rejectMoveHitRewindDescription_ready :
    rejectMoveHitRewindDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    moveTape2LeftOneDescription_ready
    Tape2Rewinder.loweredDescription_subroutineReady
theorem rejectMoveHitRewindDescription_realizes (L : DovetailLayout) :
    rejectMoveHitRewindDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rejectAfterLiveCopyTape0 L) Tape.blank (rejectCleanedTape2 L))
      (encodedGuardedStructured3Tapes
        (rejectAfterLiveCopyTape0 L) Tape.blank
        (rejectHitRewindTargetTape2 L)) := by
  have hm := moveTape2LeftOneDescription_realizes
    (rejectAfterLiveCopyTape0 L) (rejectCleanedTape2 L)
  rw [cleaned_moveLeftOne_eq_rejectHitSource] at hm
  have hr := Tape2Rewinder.loweredDescription_realizes_withContext
    (rejectHitRewindBase L) (RejectBranchShapes.rejectHitBits L)
    [none] (rejectAfterLiveCopyTape0 L) Tape.blank
  simpa [rejectMoveHitRewindDescription, rejectHitRewindSourceTape2,
    rejectHitRewindTargetTape2] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      moveTape2LeftOneDescription_ready
      Tape2Rewinder.loweredDescription_subroutineReady hm hr

def rejectPrefixRewindBase (L : DovetailLayout) : List (Option Bool) :=
  (rejectLiveBase L).tail

def rejectPrefixRightPadding (L : DovetailLayout) :
    List (Option Bool) :=
  List.append (List.replicate 3 (none : Option Bool))
    (List.append ((RejectBranchShapes.rejectHitBits L).map some)
      [none, none])
def rejectPrefixRewindSourceTape2 (L : DovetailLayout) : Tape Bool :=
  Tape2Rewinder.sourceTapeWithContext
    (rejectPrefixRewindBase L) (rejectKeptPrefixBits L)
    (rejectPrefixRightPadding L)

def rejectPrefixRewindTargetTape2 (L : DovetailLayout) : Tape Bool :=
  Tape2Rewinder.targetTapeWithContext
    (rejectPrefixRewindBase L) (rejectKeptPrefixBits L)
    (rejectPrefixRightPadding L)

theorem liveBase_eq_none_cons_tail (L : DovetailLayout) :
    rejectLiveBase L = none :: rejectPrefixRewindBase L := by
  rfl
theorem hitTarget_moveLeftFour_eq_prefixSource (L : DovetailLayout) :
    moveLeftFour (rejectHitRewindTargetTape2 L) =
      rejectPrefixRewindSourceTape2 L := by
  rw [rejectHitRewindTargetTape2,
    Tape2Rewinder.targetTapeWithContext]
  rw [rejectPrefixRewindSourceTape2,
    Tape2Rewinder.sourceTapeWithContext]
  rw [← liveBase_eq_none_cons_tail]
  have hhit : RejectBranchShapes.rejectHitBits L =
      [false, true, L.rejectHit, !L.rejectHit] := by
    cases h : L.rejectHit <;>
      simp [RejectBranchShapes.rejectHitBits, boolFieldBits,
        cellFieldBits, cellCodeBits, encodeCell,
        encodeCodeWordAsInput, encodeCodeSymbolAsInput, h]
  rw [hhit]
  simp [moveLeftFour, rejectHitRewindBase, rejectPrefixRightPadding,
    hhit,
    keepL, TapeAction.apply, HeadMove.apply, Tape.move, Tape.moveLeft,
    tapeAtCells, List.append_assoc]

def rejectMovePrefixRewindDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription moveLeftFourDescription
    Tape2Rewinder.loweredDescription

theorem rejectMovePrefixRewindDescription_ready :
    rejectMovePrefixRewindDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    moveLeftFourDescription_ready
    Tape2Rewinder.loweredDescription_subroutineReady
theorem rejectMovePrefixRewindDescription_realizes (L : DovetailLayout) :
    rejectMovePrefixRewindDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rejectAfterLiveCopyTape0 L) Tape.blank
        (rejectHitRewindTargetTape2 L))
      (encodedGuardedStructured3Tapes
        (rejectAfterLiveCopyTape0 L) Tape.blank
        (rejectPrefixRewindTargetTape2 L)) := by
  have hm := moveLeftFourDescription_realizes
    (rejectAfterLiveCopyTape0 L) (rejectHitRewindTargetTape2 L)
  rw [hitTarget_moveLeftFour_eq_prefixSource] at hm
  have hr := Tape2Rewinder.loweredDescription_realizes_withContext
    (rejectPrefixRewindBase L) (rejectKeptPrefixBits L)
    (rejectPrefixRightPadding L) (rejectAfterLiveCopyTape0 L) Tape.blank
  simpa [rejectMovePrefixRewindDescription, rejectPrefixRewindSourceTape2,
    rejectPrefixRewindTargetTape2] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      moveLeftFourDescription_ready
      Tape2Rewinder.loweredDescription_subroutineReady hm hr

/-! Return across the outer blank prefix to the public output head. -/

def rejectOuterScanRight (L : DovetailLayout) : List (Option Bool) :=
  List.append ((rejectKeptPrefixBits L).map some)
    (none :: rejectPrefixRightPadding L)

def rejectOuterScanSourceTape2 (L : DovetailLayout) : Tape Bool :=
  tapeAtCells (rejectPrefixRewindBase L)
    (none :: rejectOuterScanRight L)
theorem prefixTarget_moveLeftOne_eq_outerScanSource (L : DovetailLayout) :
    keepL.apply (rejectPrefixRewindTargetTape2 L) =
      rejectOuterScanSourceTape2 L := by
  rw [rejectPrefixRewindTargetTape2,
    Tape2Rewinder.targetTapeWithContext]
  rw [rejectOuterScanSourceTape2, rejectOuterScanRight]
  rcases stageNatBits_cons_false L.stage with ⟨stageTail, hstage⟩
  simp [rejectKeptPrefixBits, hstage,
    keepL, TapeAction.apply, HeadMove.apply, Tape.move, Tape.moveLeft,
    tapeAtCells, List.append_assoc]

def rejectOuterScanCount (L : DovetailLayout) : Nat :=
  (ParsedLayoutBits L).length + markerOffset L + 7

theorem rejectPrefixRewindBase_shape (L : DovetailLayout) :
    rejectPrefixRewindBase L =
      List.append
        (List.replicate (rejectOuterScanCount L) (none : Option Bool))
        [some true] := by
  have hpos : 0 < (ParsedLayoutBits L).length := by
    rw [parsedLayoutBits_fieldDecomp]
    simp [transitionPrefixBits_length]
    lia
  have htail : commonCounterBaseTail L =
      AcceptBranch.counterBaseTail L := by rfl
  rw [rejectPrefixRewindBase, rejectLiveBase, gapMarkerBase, htail,
    AcceptFinish.counterBaseTail_eq_marked_replicate]
  change
    List.append (List.replicate 7 (none : Option Bool))
        (List.append (List.replicate (markerOffset L) none)
          (none ::
            List.append
              (List.replicate ((ParsedLayoutBits L).length - 1) none)
              [some true])) = _
  calc
    _ = List.append
          (List.append (List.replicate 7 (none : Option Bool))
            (List.replicate (markerOffset L) none))
          (none ::
            List.append
              (List.replicate ((ParsedLayoutBits L).length - 1) none)
              [some true]) :=
        (List.append_assoc _ _ _).symm
    _ = List.append
          (List.replicate (7 + markerOffset L) (none : Option Bool))
          (none ::
            List.append
              (List.replicate ((ParsedLayoutBits L).length - 1) none)
              [some true]) := by
        rw [AcceptFinish.replicate_none_append_replicate]
    _ = List.append
          (List.replicate
            (7 + markerOffset L + 1 +
              ((ParsedLayoutBits L).length - 1)) none)
          [some true] := by
        rw [AcceptFinish.replicate_none_append_none_marked]
    _ = List.append
          (List.replicate (rejectOuterScanCount L) none) [some true] := by
        unfold rejectOuterScanCount
        congr 2
        lia
def rejectAfterOuterScanTape2 (L : DovetailLayout) : Tape Bool :=
  tapeAtCells []
    (none ::
      List.append
        (List.replicate (rejectOuterScanCount L + 1)
          (none : Option Bool))
        (rejectOuterScanRight L))

theorem rejectOuterMarkerScan_realizes (L : DovetailLayout) :
    MarkerScanLowered.loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rejectAfterLiveCopyTape0 L) Tape.blank
        (rejectOuterScanSourceTape2 L))
      (encodedGuardedStructured3Tapes
        (rejectAfterLiveCopyTape0 L) Tape.blank
        (rejectAfterOuterScanTape2 L)) := by
  rw [rejectOuterScanSourceTape2, rejectPrefixRewindBase_shape]
  simpa [rejectAfterOuterScanTape2] using
    MarkerScanLowered.loweredDescription_realizes
      (rejectOuterScanCount L) (rejectAfterLiveCopyTape0 L)
      ([] : List (Option Bool)) (rejectOuterScanRight L)

def rejectFinalOutputTape2 (L : DovetailLayout) : Tape Bool :=
  keepR.apply (rejectAfterOuterScanTape2 L)
theorem rejectMoveRightAfterOuter_realizes (L : DovetailLayout) :
    moveRightOneDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rejectAfterLiveCopyTape0 L) Tape.blank
        (rejectAfterOuterScanTape2 L))
      (encodedGuardedStructured3Tapes
        (rejectAfterLiveCopyTape0 L) Tape.blank
        (rejectFinalOutputTape2 L)) := by
  exact moveRightOneDescription_realizes
    (rejectAfterLiveCopyTape0 L) (rejectAfterOuterScanTape2 L)

theorem rejectFinalOutputTape2_shape (L : DovetailLayout) :
    rejectFinalOutputTape2 L =
      tapeAtCells [none]
        (List.append
          (List.replicate
            ((ParsedLayoutBits L).length + markerOffset L + 8)
            (none : Option Bool))
          (List.append ((rejectKeptPrefixBits L).map some)
            (List.append (List.replicate 4 none)
              (List.append
                ((RejectBranchShapes.rejectHitBits L).map some)
                [none, none])))) := by
  unfold rejectFinalOutputTape2 rejectAfterOuterScanTape2
    rejectOuterScanCount rejectOuterScanRight rejectPrefixRightPadding
  rw [AcceptFinalTail.keepR_tapeAtCells_nil_none]
  rw [show (ParsedLayoutBits L).length + markerOffset L + 7 + 1 =
      (ParsedLayoutBits L).length + markerOffset L + 8 by lia]
  apply congrArg (tapeAtCells [none])
  apply congrArg
    (List.append
      (List.replicate
        ((ParsedLayoutBits L).length + markerOffset L + 8)
        (none : Option Bool)))
  apply congrArg (List.append ((rejectKeptPrefixBits L).map some))
  let tail : List (Option Bool) :=
    List.append ((RejectBranchShapes.rejectHitBits L).map some)
      [none, none]
  change List.append
      (none :: List.replicate 3 (none : Option Bool)) tail =
    List.append (List.replicate 4 none) tail
  exact congrArg (fun xs => List.append xs tail)
    (show none :: List.replicate 3 (none : Option Bool) =
      List.replicate 4 none by rfl)

theorem rejectPublicTarget_shape (L : DovetailLayout) :
    structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
        (ParsedLayoutBits L).length
        (postFieldDecodedPrefixScanPadding false L) =
      tapeAtCells [none]
        (List.append
          (List.replicate
            ((ParsedLayoutBits L).length + markerOffset L + 8)
            (none : Option Bool))
          (List.append ((rejectKeptPrefixBits L).map some)
            (List.append (List.replicate 4 none)
              (List.append
                ((RejectBranchShapes.rejectHitBits L).map some)
                [none, none])))) := by
  have hblank :
      (selectedProjectionPaddedTailCleanupScratchCountBits false L).length +
          2 = markerOffset L + 8 := by
    rw [← directScratchBlankDriverBits_length false L]
    exact directScratchBlankDriverBits_reject_length L
  have hprefix :
      List.append
          (List.replicate ((ParsedLayoutBits L).length + 1)
            (none : Option Bool))
          (none ::
            List.replicate
              (selectedProjectionPaddedTailCleanupScratchCountBits
                false L).length none) =
        List.replicate
          ((ParsedLayoutBits L).length + markerOffset L + 8) none := by
    rw [show none ::
          List.replicate
            (selectedProjectionPaddedTailCleanupScratchCountBits false L).length
            (none : Option Bool) =
        List.replicate
          ((selectedProjectionPaddedTailCleanupScratchCountBits false L).length +
            1) none by
      rw [List.replicate_succ]]
    rw [AcceptFinish.replicate_none_append_replicate]
    congr 1
    lia
  have hlive :
      List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage).map some)
          (List.append
            ((selectedProjectionPaddedTailCleanupUnselectedConfigBits
              false L).map some)
            (List.append
              ((selectedProjectionPaddedTailCleanupSelectedConfigBits
                false L).map some)
              (List.append (List.replicate 4 (none : Option Bool))
                (List.append
                  ((selectedProjectionPaddedTailCleanupSelectedHitBits
                    false L).map some)
                  [none, none])))) =
        List.append ((rejectKeptPrefixBits L).map some)
          (List.append (List.replicate 4 none)
            (List.append
              ((RejectBranchShapes.rejectHitBits L).map some)
              [none, none])) := by
    simp [rejectKeptPrefixBits,
      RejectBranchShapes.acceptBits,
      RejectBranchShapes.rejectBits,
      RejectBranchShapes.rejectHitBits,
      AcceptBranch.acceptBits,
      AcceptBranch.rejectBits,
      selectedProjectionPaddedTailCleanupUnselectedConfigBits,
      selectedProjectionPaddedTailCleanupSelectedConfigBits,
      selectedProjectionPaddedTailCleanupSelectedHitBits,
      List.map_append, List.append_assoc]
  rw [postFieldDecodedPrefixScanPadding_reject_decomp]
  unfold structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
  let prefixBlanks : List (Option Bool) :=
    List.replicate ((ParsedLayoutBits L).length + 1) none
  let scanBlanks : List (Option Bool) :=
    none ::
      List.replicate
        (selectedProjectionPaddedTailCleanupScratchCountBits false L).length
        none
  let liveTail : List (Option Bool) :=
    List.append
      ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        L.stage).map some)
      (List.append
        ((selectedProjectionPaddedTailCleanupUnselectedConfigBits
          false L).map some)
        (List.append
          ((selectedProjectionPaddedTailCleanupSelectedConfigBits
            false L).map some)
          (List.append (List.replicate 4 none)
            (List.append
              ((selectedProjectionPaddedTailCleanupSelectedHitBits
                false L).map some)
              [none, none]))))
  let finalTail : List (Option Bool) :=
    List.append ((rejectKeptPrefixBits L).map some)
      (List.append (List.replicate 4 none)
        (List.append
          ((RejectBranchShapes.rejectHitBits L).map some)
          [none, none]))
  have hprefix' :
      List.append prefixBlanks scanBlanks =
        List.replicate
          ((ParsedLayoutBits L).length + markerOffset L + 8) none := by
    exact hprefix
  have hlive' : liveTail = finalTail := by
    exact hlive
  change tapeAtCells [none]
      (List.append prefixBlanks (List.append scanBlanks liveTail)) =
    tapeAtCells [none]
      (List.append
        (List.replicate
          ((ParsedLayoutBits L).length + markerOffset L + 8) none)
        finalTail)
  apply congrArg (tapeAtCells [none])
  calc
    List.append prefixBlanks (List.append scanBlanks liveTail) =
        List.append (List.append prefixBlanks scanBlanks) liveTail :=
      (List.append_assoc prefixBlanks scanBlanks liveTail).symm
    _ = List.append
        (List.replicate
          ((ParsedLayoutBits L).length + markerOffset L + 8) none)
        liveTail := by rw [hprefix']
    _ = List.append
        (List.replicate
          ((ParsedLayoutBits L).length + markerOffset L + 8) none)
        finalTail := congrArg _ hlive'
theorem rejectFinalOutputTape2_eq_publicTarget (L : DovetailLayout) :
    rejectFinalOutputTape2 L =
      structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
        (ParsedLayoutBits L).length
        (postFieldDecodedPrefixScanPadding false L) := by
  rw [rejectFinalOutputTape2_shape, rejectPublicTarget_shape]

/-! Composed tape-2 tail. -/

def rejectOuterReturnDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription moveTape2LeftOneDescription
    (canonicalPrimitiveSeqDescription MarkerScanLowered.loweredDescription
      moveRightOneDescription)

theorem rejectOuterReturnDescription_ready :
    rejectOuterReturnDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    moveTape2LeftOneDescription_ready
    (canonicalPrimitiveSeqDescription_subroutineReady
      MarkerScanLowered.loweredDescription_ready
      moveRightOneDescription_ready)
theorem rejectOuterReturnDescription_realizes (L : DovetailLayout) :
    rejectOuterReturnDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rejectAfterLiveCopyTape0 L) Tape.blank
        (rejectPrefixRewindTargetTape2 L))
      (encodedGuardedStructured3Tapes
        (rejectAfterLiveCopyTape0 L) Tape.blank
        (rejectFinalOutputTape2 L)) := by
  have hm := moveTape2LeftOneDescription_realizes
    (rejectAfterLiveCopyTape0 L) (rejectPrefixRewindTargetTape2 L)
  rw [prefixTarget_moveLeftOne_eq_outerScanSource] at hm
  have htail := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    MarkerScanLowered.loweredDescription_ready moveRightOneDescription_ready
    (rejectOuterMarkerScan_realizes L)
    (rejectMoveRightAfterOuter_realizes L)
  simpa [rejectOuterReturnDescription] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      moveTape2LeftOneDescription_ready
      (canonicalPrimitiveSeqDescription_subroutineReady
        MarkerScanLowered.loweredDescription_ready
        moveRightOneDescription_ready) hm htail

def rejectTape2TailDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription rejectMoveHitRewindDescription
    (canonicalPrimitiveSeqDescription rejectMovePrefixRewindDescription
      rejectOuterReturnDescription)

theorem rejectTape2TailDescription_ready :
    rejectTape2TailDescription.SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    rejectMoveHitRewindDescription_ready
    (canonicalPrimitiveSeqDescription_subroutineReady
      rejectMovePrefixRewindDescription_ready
      rejectOuterReturnDescription_ready)
theorem rejectTape2TailDescription_realizes (L : DovetailLayout) :
    rejectTape2TailDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rejectAfterLiveCopyTape0 L) Tape.blank (rejectCleanedTape2 L))
      (encodedGuardedStructured3Tapes
        (rejectAfterLiveCopyTape0 L) Tape.blank
        (rejectFinalOutputTape2 L)) := by
  have htail := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    rejectMovePrefixRewindDescription_ready rejectOuterReturnDescription_ready
    (rejectMovePrefixRewindDescription_realizes L)
    (rejectOuterReturnDescription_realizes L)
  simpa [rejectTape2TailDescription] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      rejectMoveHitRewindDescription_ready
      (canonicalPrimitiveSeqDescription_subroutineReady
        rejectMovePrefixRewindDescription_ready
        rejectOuterReturnDescription_ready)
      (rejectMoveHitRewindDescription_realizes L) htail

end RejectTape2Tail
end Route
end InputMat
end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
