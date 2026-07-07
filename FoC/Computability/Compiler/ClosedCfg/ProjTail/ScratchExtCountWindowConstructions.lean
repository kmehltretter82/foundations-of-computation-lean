import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.GapPayloadLocalCompactor
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawEncoder
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchExtCountWindow
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchExtRawSourceBridge

set_option doc.verso true

/-!
# Post-padding scratch-count window constructions

This module packages the finite-machine construction leaves for the
scratch-count window materializer/restorer.  The tape shapes, specs, and
shared composition lemmas live in
{module}`FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchExtCountWindow`;
the remaining executable construction leaves are kept here to keep that core
module below the large-file threshold.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

open CanonicalLayouts.DovetailLayoutScanner

theorem selectedProjectionPaddedTailCleanupScratchCountWindowPrefixScannerConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowPrefixScannerConstruction := by
  intro useAccept
  exact
    ⟨postPaddingOutputPrefixScannerDescription,
      postPaddingOutputPrefixScannerDescription_subroutineReady,
      fun L =>
        selectedProjectionPaddedTailCleanupOutputPrefixScanner_haltsFrom_baseSourceTapeWithExtraScratch
          useAccept L 0⟩

theorem selectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixStageScannerConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixStageScannerConstruction := by
  intro useAccept
  exact
    ⟨canonicalSeqDescription
        CanonicalLayouts.DovetailStagePrefix.NonemptyNatSuffixScannerDescription
        rightMoveOnceDescription,
      canonicalSeqDescription_subroutineReady
        CanonicalLayouts.DovetailStagePrefix.nonemptyNatSuffixScannerDescription_subroutineReady
        rightMoveOnceDescription_subroutineReady,
      fun L =>
        selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixStageScanner_haltsFrom
          useAccept L 0⟩

theorem selectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixFirstFieldEraserConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixFirstFieldEraserConstruction := by
  exact
    ⟨leftBoundaryBitConfigurationFieldEraseAndPayloadScanDescription,
      leftBoundaryBitConfigurationFieldEraseAndPayloadScanDescription_subroutineReady,
      fun L =>
        selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldEraser_haltsFrom
          L 0⟩

theorem selectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixFirstFieldEraserConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixFirstFieldEraserConstruction := by
  exact
    ⟨leftBoundaryBitConfigurationFieldEraseAndPayloadScanDescription,
      leftBoundaryBitConfigurationFieldEraseAndPayloadScanDescription_subroutineReady,
      fun L =>
        selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldEraser_haltsFrom
          L 0⟩

theorem acceptPostFieldHandoff_rightMoveSource_eq_of_config_and_payload_append_last
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool)
    (hdeleted :
      configurationFieldBits L.acceptConfig [] =
        false :: deletedTail)
    (hpayload :
      selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload
          L =
        List.append pref [leftBit]) :
    Tape.move Direction.right
        (selectedProjectionPaddedTailCleanupScratchCountAcceptAfterFirstFieldEraseTape
          L 0) =
      rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
        (rightBlankLocalGapBaseLeft deletedTail.length
          (selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
            L))
        leftBit pref.reverse 0 [none, none, none, none, none] := by
  have hcons :=
    selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload_cons_false
      L
  have hpayloadCons :
      false ::
          selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayloadRest
            L =
        List.append pref [leftBit] := by
    rw [← hcons, hpayload]
  simpa [selectedProjectionPaddedTailCleanupScratchCountAcceptAfterFirstFieldEraseTape,
    hdeleted] using
      rightBlankGapPayloadScanTargetTape_move_right_eq_localGapSource
        (selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
          L)
        deletedTail.length false leftBit
        (selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayloadRest
          L)
        pref [none, none, none, none, none] hpayloadCons

def postFieldHandoffAfterSentinelGapPadding
    (deletedTail : Word Bool) (rightPadding : List (Option Bool)) :
    List (Option Bool) :=
  match deletedTail, rightPadding with
  | [], _ => rightPadding
  | _ :: _, [] => []
  | _ :: _, _ :: tail =>
      sentinelGapCompactorFinalPadding deletedTail.length 0 tail

def acceptPostFieldHandoffAfterSentinelGapTape
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool) : Tape Bool :=
  leadingBlankLeftShiftTargetTapeWithPadding
    (selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
      L)
    (List.append pref [leftBit])
    (postFieldHandoffAfterSentinelGapPadding deletedTail
      [none, none, none, none, none])

-- Normalize the accept-side compactor target so later restoration work can
-- reason about the surviving prefix/payload bits without tape-position noise.
theorem acceptPostFieldHandoffAfterSentinelGapTape_normalizedOutput
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool) :
    Tape.normalizedOutput
        (acceptPostFieldHandoffAfterSentinelGapTape
          L pref leftBit deletedTail) =
      List.append
        ((selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
          L).reverse.filterMap (fun cell => cell))
        (List.append (List.append pref [leftBit])
          ((postFieldHandoffAfterSentinelGapPadding deletedTail
            [none, none, none, none, none]).filterMap
              (fun cell => cell))) := by
  rw [acceptPostFieldHandoffAfterSentinelGapTape,
    leadingBlankLeftShiftTargetTapeWithPadding_normalizedOutput]

def acceptPostFieldHandoffAfterBoundaryCleanupTape
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool) : Tape Bool :=
  leadingBlankLeftShiftTargetTapeWithPadding []
    (List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
      (List.append pref [leftBit]))
    (none ::
      leadingBlankLeftShiftTargetVisiblePadding
        (postFieldHandoffAfterSentinelGapPadding deletedTail
          [none, none, none, none, none]))

theorem acceptPostFieldHandoffAfterSentinelGapTape_move_left_move_right
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (acceptPostFieldHandoffAfterSentinelGapTape
            L pref leftBit deletedTail)) =
      acceptPostFieldHandoffAfterSentinelGapTape
        L pref leftBit deletedTail := by
  cases deletedTail with
  | nil =>
      simpa [acceptPostFieldHandoffAfterSentinelGapTape,
        postFieldHandoffAfterSentinelGapPadding] using
        leadingBlankLeftShiftTargetTapeWithPadding_move_left_move_right_padding_cons_cons
          (selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
            L)
          (List.append pref [leftBit])
          (none : Option Bool) (none : Option Bool)
          [none, none, none]
  | cons deletedHead deletedRest =>
      simpa [acceptPostFieldHandoffAfterSentinelGapTape,
        postFieldHandoffAfterSentinelGapPadding,
        sentinelGapCompactorFinalPadding,
        sentinelGapCompactorFinalPadding_cons_cons_right,
        List.append_assoc] using
        leadingBlankLeftShiftTargetTapeWithPadding_move_left_move_right_padding_cons_cons
          (selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
            L)
          (List.append pref [leftBit])
          (none : Option Bool) (none : Option Bool)
          (List.append
            (List.replicate deletedRest.length (none : Option Bool))
            [none, none, none, none])

theorem acceptPostFieldHandoffAfterBoundaryCleanupTape_move_left_move_right
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (acceptPostFieldHandoffAfterBoundaryCleanupTape
            L pref leftBit deletedTail)) =
      acceptPostFieldHandoffAfterBoundaryCleanupTape
        L pref leftBit deletedTail := by
  unfold acceptPostFieldHandoffAfterBoundaryCleanupTape
  generalize hpad :
    postFieldHandoffAfterSentinelGapPadding deletedTail
      [none, none, none, none, none] = padding
  cases padding <;>
    simp [leadingBlankLeftShiftTargetVisiblePadding,
      leadingBlankLeftShiftTargetTapeWithPadding, tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]

theorem acceptPostFieldHandoff_sentinelGap_haltsFrom_of_config_and_payload_append_last
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool)
    (hdeleted :
      configurationFieldBits L.acceptConfig [] =
        false :: deletedTail)
    (_hpayload :
      selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload
          L =
        List.append pref [leftBit]) :
    sentinelGapCompactorDescription.HaltsFromTape
      (rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
        (rightBlankLocalGapBaseLeft deletedTail.length
          (selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
            L))
        leftBit pref.reverse 0 [none, none, none, none, none])
      (acceptPostFieldHandoffAfterSentinelGapTape
        L pref leftBit deletedTail) := by
  obtain ⟨basePref, boundaryBit, hprefix⟩ :=
    selectedProjectionPaddedTailCleanupPrefix_append_last L
  have hbase0 :
      selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
          L =
        List.append
          ((selectedProjectionPaddedTailCleanupPrefixBits L).reverse.map some)
          [none] := by
    unfold selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
    change postPaddingOutputPrefixAfterStageBase (ParsedLayoutBits L)
        L.stage [none] =
      List.append
        ((selectedProjectionPaddedTailCleanupPrefixBits L).reverse.map some)
        [none]
    exact postPaddingOutputPrefixAfterStageBase_eq_prefixBits_reverse L
  have hbase :
      selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
          L =
        some boundaryBit :: List.append (basePref.reverse.map some) [none] := by
    rw [hbase0, hprefix]
    simp [List.reverse_append]
  cases deletedTail with
  | nil =>
      simpa [acceptPostFieldHandoffAfterSentinelGapTape,
        postFieldHandoffAfterSentinelGapPadding,
        rightBlankLocalGapBaseLeft, hbase] using
        sentinelGapCompactorDescription_haltsFromTape_final_pass
          (List.append (basePref.reverse.map some) [none])
          boundaryBit leftBit pref.reverse 0
          [none, none, none, none, none]
  | cons deletedHead deletedRest =>
      simpa [acceptPostFieldHandoffAfterSentinelGapTape,
        postFieldHandoffAfterSentinelGapPadding,
        rightBlankLocalGapBaseLeft, hbase] using
        sentinelGapCompactorDescription_haltsFromTape_gapBase_zero_cons_right
          deletedRest.length
          (List.append (basePref.reverse.map some) [none])
          boundaryBit leftBit pref.reverse
          [none, none, none, none]

theorem acceptPostFieldHandoff_boundaryCleanup_haltsFrom_of_config_and_payload_append_last
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool)
    (_hdeleted :
      configurationFieldBits L.acceptConfig [] =
        false :: deletedTail)
    (_hpayload :
      selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload
          L =
        List.append pref [leftBit]) :
    sentinelBoundaryCleanupDescription.HaltsFromTape
      (Tape.move Direction.left
        (Tape.move Direction.right
          (acceptPostFieldHandoffAfterSentinelGapTape
            L pref leftBit deletedTail)))
      (acceptPostFieldHandoffAfterBoundaryCleanupTape
        L pref leftBit deletedTail) := by
  obtain ⟨basePref, boundaryBit, hprefix⟩ :=
    selectedProjectionPaddedTailCleanupPrefix_append_last L
  have hbase0 :
      selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
          L =
        List.append
          ((selectedProjectionPaddedTailCleanupPrefixBits L).reverse.map some)
          [none] := by
    unfold selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
    change postPaddingOutputPrefixAfterStageBase (ParsedLayoutBits L)
        L.stage [none] =
      List.append
        ((selectedProjectionPaddedTailCleanupPrefixBits L).reverse.map some)
        [none]
    exact postPaddingOutputPrefixAfterStageBase_eq_prefixBits_reverse L
  have hbase :
      selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
          L =
        some boundaryBit :: List.append (basePref.reverse.map some) [none] := by
    rw [hbase0, hprefix]
    simp [List.reverse_append]
  have hbits :
      List.append basePref (boundaryBit :: List.append pref [leftBit]) =
        List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
          (List.append pref [leftBit]) := by
    rw [hprefix]
    simp [List.append_assoc]
  rw [acceptPostFieldHandoffAfterSentinelGapTape_move_left_move_right]
  unfold acceptPostFieldHandoffAfterBoundaryCleanupTape
  rw [← hbits]
  simpa [acceptPostFieldHandoffAfterSentinelGapTape,
    postFieldHandoffAfterSentinelGapPadding, hbase] using
    sentinelBoundaryCleanupDescription_haltsFrom_sentinelTarget
      basePref (List.append pref [leftBit]) boundaryBit
      (postFieldHandoffAfterSentinelGapPadding deletedTail
        [none, none, none, none, none])

theorem rejectPostFieldHandoff_rightMoveSource_eq_of_config_and_payload_append_last
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool)
    (hdeleted :
      configurationFieldBits L.acceptConfig [] =
        false :: deletedTail)
    (hpayload :
      selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayload
          L =
        List.append pref [leftBit]) :
    Tape.move Direction.right
        (selectedProjectionPaddedTailCleanupScratchCountRejectAfterFirstFieldEraseTape
          L 0) =
      rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
        (rightBlankLocalGapBaseLeft deletedTail.length
          (selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
            L))
        leftBit pref.reverse 0
        (List.append (List.replicate 3 (none : Option Bool))
          (List.append
            ((selectedProjectionPaddedTailCleanupSelectedHitBits
              false L).map some)
            [none, none])) := by
  have hcons :=
    selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayload_cons_false
      L
  have hpayloadCons :
      false ::
          selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayloadRest
            L =
        List.append pref [leftBit] := by
    rw [← hcons, hpayload]
  simpa [selectedProjectionPaddedTailCleanupScratchCountRejectAfterFirstFieldEraseTape,
    hdeleted, List.append_assoc] using
      rightBlankGapPayloadScanTargetTape_move_right_eq_localGapSource
        (selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
          L)
        deletedTail.length false leftBit
        (selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayloadRest
          L)
        pref
        (List.append (List.replicate 3 (none : Option Bool))
          (List.append
            ((selectedProjectionPaddedTailCleanupSelectedHitBits
              false L).map some)
            [none, none]))
        hpayloadCons

def rejectPostFieldHandoffAfterFirstGapTape
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool) : Tape Bool :=
  leadingBlankLeftShiftTargetTapeWithPadding
    (selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
      L)
    (List.append pref [leftBit])
    (postFieldHandoffAfterSentinelGapPadding deletedTail
      (List.append (List.replicate 3 (none : Option Bool))
        (List.append
          ((selectedProjectionPaddedTailCleanupSelectedHitBits
            false L).map some)
          [none, none])))

-- The reject-side window carries the selected-hit bits in its right padding;
-- this exposes those bits in the normalized output shape.
theorem rejectPostFieldHandoffAfterFirstGapTape_normalizedOutput
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool) :
    Tape.normalizedOutput
        (rejectPostFieldHandoffAfterFirstGapTape
          L pref leftBit deletedTail) =
      List.append
        ((selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
          L).reverse.filterMap (fun cell => cell))
        (List.append (List.append pref [leftBit])
          ((postFieldHandoffAfterSentinelGapPadding deletedTail
            (List.append (List.replicate 3 (none : Option Bool))
              (List.append
                ((selectedProjectionPaddedTailCleanupSelectedHitBits
                  false L).map some)
                [none, none]))).filterMap (fun cell => cell))) := by
  rw [rejectPostFieldHandoffAfterFirstGapTape,
    leadingBlankLeftShiftTargetTapeWithPadding_normalizedOutput]

theorem rejectPostFieldHandoff_firstGap_haltsFrom_of_config_and_payload_append_last
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool)
    (hdeleted :
      configurationFieldBits L.acceptConfig [] =
        false :: deletedTail)
    (_hpayload :
      selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayload
          L =
        List.append pref [leftBit]) :
    sentinelGapCompactorDescription.HaltsFromTape
      (rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
        (rightBlankLocalGapBaseLeft deletedTail.length
          (selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
            L))
        leftBit pref.reverse 0
        (List.append (List.replicate 3 (none : Option Bool))
          (List.append
            ((selectedProjectionPaddedTailCleanupSelectedHitBits
              false L).map some)
            [none, none]))
      )
      (rejectPostFieldHandoffAfterFirstGapTape
        L pref leftBit deletedTail) := by
  obtain ⟨basePref, boundaryBit, hprefix⟩ :=
    selectedProjectionPaddedTailCleanupPrefix_append_last L
  have hbase0 :
      selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
          L =
        List.append
          ((selectedProjectionPaddedTailCleanupPrefixBits L).reverse.map some)
          [none] := by
    unfold selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
    change postPaddingOutputPrefixAfterStageBase (ParsedLayoutBits L)
        L.stage [none] =
      List.append
        ((selectedProjectionPaddedTailCleanupPrefixBits L).reverse.map some)
        [none]
    exact postPaddingOutputPrefixAfterStageBase_eq_prefixBits_reverse L
  have hbase :
      selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
          L =
        some boundaryBit :: List.append (basePref.reverse.map some) [none] := by
    rw [hbase0, hprefix]
    simp [List.reverse_append]
  cases deletedTail with
  | nil =>
      simpa [rejectPostFieldHandoffAfterFirstGapTape,
        postFieldHandoffAfterSentinelGapPadding,
        rightBlankLocalGapBaseLeft, hbase] using
        sentinelGapCompactorDescription_haltsFromTape_final_pass
          (List.append (basePref.reverse.map some) [none])
          boundaryBit leftBit pref.reverse 0
          (List.append (List.replicate 3 (none : Option Bool))
            (List.append
              ((selectedProjectionPaddedTailCleanupSelectedHitBits
                false L).map some)
              [none, none]))
  | cons deletedHead deletedRest =>
      simpa [rejectPostFieldHandoffAfterFirstGapTape,
        postFieldHandoffAfterSentinelGapPadding,
        rightBlankLocalGapBaseLeft, hbase] using
        sentinelGapCompactorDescription_haltsFromTape_gapBase_zero_cons_right
          deletedRest.length
          (List.append (basePref.reverse.map some) [none])
          boundaryBit leftBit pref.reverse
          (List.append (List.replicate 2 (none : Option Bool))
            (List.append
              ((selectedProjectionPaddedTailCleanupSelectedHitBits
                false L).map some)
              [none, none]))

theorem rejectPostFieldHandoffAfterFirstGapTape_move_left_move_right
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (rejectPostFieldHandoffAfterFirstGapTape
            L pref leftBit deletedTail)) =
      rejectPostFieldHandoffAfterFirstGapTape
        L pref leftBit deletedTail := by
  cases deletedTail with
  | nil =>
      simpa [rejectPostFieldHandoffAfterFirstGapTape,
        postFieldHandoffAfterSentinelGapPadding] using
        leadingBlankLeftShiftTargetTapeWithPadding_move_left_move_right_padding_cons_cons
          (selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
            L)
          (List.append pref [leftBit])
          (none : Option Bool) (none : Option Bool)
          (none ::
            List.append
              ((selectedProjectionPaddedTailCleanupSelectedHitBits
                false L).map some)
              [none, none])
  | cons deletedHead deletedRest =>
      simpa [rejectPostFieldHandoffAfterFirstGapTape,
        postFieldHandoffAfterSentinelGapPadding,
        sentinelGapCompactorFinalPadding,
        sentinelGapCompactorFinalPadding_cons_cons_right,
        List.append_assoc] using
        leadingBlankLeftShiftTargetTapeWithPadding_move_left_move_right_padding_cons_cons
          (selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
            L)
          (List.append pref [leftBit])
          (none : Option Bool) (none : Option Bool)
          (List.append
            (List.replicate deletedRest.length (none : Option Bool))
            (none :: none ::
              List.append
                ((selectedProjectionPaddedTailCleanupSelectedHitBits
                  false L).map some)
                [none, none]))

theorem selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase_eq_prefixBits_reverse
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
        L =
      List.append
        ((selectedProjectionPaddedTailCleanupPrefixBits L).reverse.map some)
        [none] := by
  unfold selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
  change postPaddingOutputPrefixAfterStageBase (ParsedLayoutBits L)
      L.stage [none] =
    List.append
      ((selectedProjectionPaddedTailCleanupPrefixBits L).reverse.map some)
      [none]
  exact postPaddingOutputPrefixAfterStageBase_eq_prefixBits_reverse L

def rejectPostFieldHandoffRightPadding
    (L : DovetailLayout) : List (Option Bool) :=
  List.append (List.replicate 3 (none : Option Bool))
    (List.append
      ((selectedProjectionPaddedTailCleanupSelectedHitBits
        false L).map some)
      [none, none])

def rejectPostFieldHandoffPostGapPadding
    (L : DovetailLayout) (deletedTail : Word Bool) :
    List (Option Bool) :=
  postFieldHandoffAfterSentinelGapPadding deletedTail
    (rejectPostFieldHandoffRightPadding L)

def rejectPostFieldHandoffRewindBits
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool) :
    Word Bool :=
  List.append
    (selectedProjectionPaddedTailCleanupPrefixBits L)
    (List.append pref [leftBit])

def rejectPostFieldHandoffRewindPadding
    (L : DovetailLayout) (deletedTail : Word Bool) :
    List (Option Bool) :=
  none ::
    leadingBlankLeftShiftTargetVisiblePadding
      (rejectPostFieldHandoffPostGapPadding L deletedTail)

-- The compacted reject handoff still carries the decoded-prefix scaffold in
-- the after-stage left base.  Two left moves expose that scaffold as the
-- prefix part of the right-edge rewind word; the restoration leaf below must
-- rebuild the exact decoded-prefix source tape from this rewound boundary.
def rejectPostFieldHandoffRewoundTape
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool) : Tape Bool :=
  rightEdgeRewindTargetTapeWithBase
    ([] : List (Option Bool))
    (rejectPostFieldHandoffRewindBits L pref leftBit)
    (rejectPostFieldHandoffRewindPadding L deletedTail)

def rejectPostFieldDecodedPrefixRestorerSourceTape
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool) : Tape Bool :=
  rejectPostFieldHandoffRewoundTape L pref leftBit deletedTail

def RejectPostFieldHandoffRightEdgeRewinderSpec
    (rewinder : MachineDescription) : Prop :=
  rewinder.SubroutineReady ∧
    forall (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
      (deletedTail : Word Bool),
      configurationFieldBits L.acceptConfig [] =
          false :: deletedTail ->
      selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayload
          L =
        List.append pref [leftBit] ->
      rewinder.HaltsFromTape
        (rejectPostFieldHandoffAfterFirstGapTape
          L pref leftBit deletedTail)
        (rejectPostFieldHandoffRewoundTape
          L pref leftBit deletedTail)

def RejectPostFieldHandoffRightEdgeRewinderConstruction : Prop :=
  exists rewinder : MachineDescription,
    RejectPostFieldHandoffRightEdgeRewinderSpec rewinder

def RejectPostFieldDecodedPrefixRestorerSpec
    (normalizer : MachineDescription) : Prop :=
  normalizer.SubroutineReady ∧
    forall (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
      (deletedTail : Word Bool),
      configurationFieldBits L.acceptConfig [] =
          false :: deletedTail ->
      selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayload
          L =
        List.append pref [leftBit] ->
      normalizer.HaltsFromTapeEquiv
        (rejectPostFieldDecodedPrefixRestorerSourceTape
          L pref leftBit deletedTail)
        (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape
          false L 0)

def RejectPostFieldDecodedPrefixRestorerConstruction : Prop :=
  exists normalizer : MachineDescription,
    RejectPostFieldDecodedPrefixRestorerSpec normalizer

def rejectPostFieldHandoffRightEdgeRewindDescription :
    MachineDescription :=
  canonicalSeqDescription leftMoveTwiceDescription
    rightEdgeRewindDescription

theorem rejectPostFieldHandoffRightEdgeRewindDescription_subroutineReady :
    rejectPostFieldHandoffRightEdgeRewindDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    leftMoveTwiceDescription_subroutineReady
    rightEdgeRewindDescription_subroutineReady

theorem rejectPostFieldHandoffAfterFirstGapTape_leftTwice_eq_rightEdgeRewindSource
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool) :
    Tape.move Direction.left
        (Tape.move Direction.left
          (rejectPostFieldHandoffAfterFirstGapTape
            L pref leftBit deletedTail)) =
      rightEdgeRewindSourceTapeWithBase
        ([] : List (Option Bool))
        (rejectPostFieldHandoffRewindBits L pref leftBit)
        (rejectPostFieldHandoffRewindPadding L deletedTail) := by
  rw [rejectPostFieldHandoffAfterFirstGapTape,
    selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase_eq_prefixBits_reverse]
  simpa [rejectPostFieldHandoffRewindBits,
    rejectPostFieldHandoffRewindPadding,
    rejectPostFieldHandoffPostGapPadding,
    rejectPostFieldHandoffRightPadding] using
    leadingBlankLeftShiftTargetTapeWithPadding_leftTwice_eq_rightEdgeRewindSourceWithPrefix
      (selectedProjectionPaddedTailCleanupPrefixBits L)
      (List.append pref [leftBit])
      (postFieldHandoffAfterSentinelGapPadding deletedTail
        (List.append (List.replicate 3 (none : Option Bool))
          (List.append
            ((selectedProjectionPaddedTailCleanupSelectedHitBits
              false L).map some)
            [none, none])))

theorem rejectPostFieldHandoff_rightEdgeRewind_haltsFrom
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool) :
    rejectPostFieldHandoffRightEdgeRewindDescription.HaltsFromTape
      (rejectPostFieldHandoffAfterFirstGapTape
        L pref leftBit deletedTail)
      (rejectPostFieldHandoffRewoundTape
        L pref leftBit deletedTail) := by
  have hsource :=
    rejectPostFieldHandoffAfterFirstGapTape_leftTwice_eq_rightEdgeRewindSource
      L pref leftBit deletedTail
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      leftMoveTwiceDescription_subroutineReady
      rightEdgeRewindDescription_subroutineReady
      (leftMoveTwiceDescription_haltsFromTape
        (rejectPostFieldHandoffAfterFirstGapTape
          L pref leftBit deletedTail))
      (by
        rw [hsource, rejectPostFieldHandoffRewindPadding])
      (by
        simpa [rejectPostFieldHandoffRewoundTape] using
          rightEdgeRewindDescription_haltsFromTapeWithBase
            ([] : List (Option Bool))
            (rejectPostFieldHandoffRewindBits L pref leftBit)
            (rejectPostFieldHandoffRewindPadding L deletedTail))

theorem rejectPostFieldHandoffRightEdgeRewinderConstruction_core :
    RejectPostFieldHandoffRightEdgeRewinderConstruction := by
  exact
    ⟨rejectPostFieldHandoffRightEdgeRewindDescription,
      rejectPostFieldHandoffRightEdgeRewindDescription_subroutineReady,
      fun L pref leftBit deletedTail _hdeleted _hpayload =>
        rejectPostFieldHandoff_rightEdgeRewind_haltsFrom
          L pref leftBit deletedTail⟩

theorem rejectPostFieldHandoffRewoundTape_move_left_move_right
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (rejectPostFieldHandoffRewoundTape
            L pref leftBit deletedTail)) =
      rejectPostFieldHandoffRewoundTape
        L pref leftBit deletedTail := by
  simpa [rejectPostFieldHandoffRewoundTape,
    rejectPostFieldHandoffRewindBits, List.append_assoc] using
    rightEdgeRewindTargetTapeWithBase_move_left_move_right_append_last
      ([] : List (Option Bool))
      (List.append (selectedProjectionPaddedTailCleanupPrefixBits L) pref)
      leftBit
      (rejectPostFieldHandoffRewindPadding L deletedTail)

def RejectPostFieldRemainingGapsSpec
    (normalizer : MachineDescription) : Prop :=
  normalizer.SubroutineReady ∧
    forall (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
      (deletedTail : Word Bool),
      configurationFieldBits L.acceptConfig [] =
          false :: deletedTail ->
      selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayload
          L =
        List.append pref [leftBit] ->
      normalizer.HaltsFromTapeEquiv
        (rejectPostFieldHandoffAfterFirstGapTape
          L pref leftBit deletedTail)
        (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape
          false L 0)

def RejectPostFieldRemainingGapsConstruction : Prop :=
  exists normalizer : MachineDescription,
    RejectPostFieldRemainingGapsSpec normalizer

theorem rejectPostFieldRemainingGapsConstruction_of_rewinderAndRestorer
    (hrewinder : RejectPostFieldHandoffRightEdgeRewinderConstruction)
    (hrestorer : RejectPostFieldDecodedPrefixRestorerConstruction) :
    RejectPostFieldRemainingGapsConstruction := by
  rcases hrewinder with ⟨rewinder, hrewinderSpec⟩
  rcases hrestorer with ⟨restorer, hrestorerSpec⟩
  exact
    ⟨canonicalSeqDescription rewinder restorer,
      by
        constructor
        · exact
            canonicalSeqDescription_subroutineReady
              hrewinderSpec.left hrestorerSpec.left
        · intro L pref leftBit deletedTail hdeleted hpayload
          exact
            canonicalSeqDescription_haltsFromTapeEquiv_of_haltsFromTape
              hrewinderSpec.left
              hrestorerSpec.left
              (hrewinderSpec.right
                L pref leftBit deletedTail hdeleted hpayload)
              (rejectPostFieldHandoffRewoundTape_move_left_move_right
                L pref leftBit deletedTail)
              (hrestorerSpec.right
                L pref leftBit deletedTail hdeleted hpayload)⟩

theorem rejectPostFieldHandoff_remainingGaps_haltsFrom_of_config_and_payload_append_last
    {normalizer : MachineDescription}
    (hnormalizer : RejectPostFieldRemainingGapsSpec normalizer)
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool)
    (hdeleted :
      configurationFieldBits L.acceptConfig [] =
        false :: deletedTail)
    (hpayload :
      selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayload
          L =
        List.append pref [leftBit]) :
    normalizer.HaltsFromTapeEquiv
      (Tape.move Direction.left
        (Tape.move Direction.right
          (rejectPostFieldHandoffAfterFirstGapTape
            L pref leftBit deletedTail)))
      (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape
        false L 0) := by
  rw [
    rejectPostFieldHandoffAfterFirstGapTape_move_left_move_right]
  exact
    hnormalizer.right
      L pref leftBit deletedTail hdeleted hpayload

theorem rejectPostFieldHandoff_localGap_haltsFrom_of_config_and_payload_append_last
    {normalizer : MachineDescription}
    (hnormalizer : RejectPostFieldRemainingGapsSpec normalizer)
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool)
    (hdeleted :
      configurationFieldBits L.acceptConfig [] =
        false :: deletedTail)
    (hpayload :
      selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayload
          L =
        List.append pref [leftBit]) :
    (SeqViaCanonical
      sentinelGapCompactorDescription
      normalizer).HaltsFromTapeEquiv
      (rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
        (rightBlankLocalGapBaseLeft deletedTail.length
          (selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
            L))
        leftBit pref.reverse 0
        (List.append (List.replicate 3 (none : Option Bool))
          (List.append
            ((selectedProjectionPaddedTailCleanupSelectedHitBits
              false L).map some)
            [none, none]))
      )
      (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape
        false L 0) := by
  exact
    SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
      sentinelGapCompactorDescription_subroutineReady
      hnormalizer.left
      (rejectPostFieldHandoff_firstGap_haltsFrom_of_config_and_payload_append_last
        L pref leftBit deletedTail hdeleted hpayload).toEquiv
      (Tape.Equiv.refl _)
      (rejectPostFieldHandoff_remainingGaps_haltsFrom_of_config_and_payload_append_last
        hnormalizer L pref leftBit deletedTail hdeleted hpayload)

theorem rejectPostFieldHandoff_rightMove_haltsFrom_of_payload_append_last
    {normalizer : MachineDescription}
    (hnormalizer : RejectPostFieldRemainingGapsSpec normalizer)
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (hpayload :
      selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayload
          L =
        List.append pref [leftBit]) :
    (SeqViaCanonical
      sentinelGapCompactorDescription
      normalizer).HaltsFromTapeEquiv
      (Tape.move Direction.right
        (selectedProjectionPaddedTailCleanupScratchCountRejectAfterFirstFieldEraseTape
          L 0))
      (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape
        false L 0) := by
  rcases configurationFieldBits_cons_false L.acceptConfig [] with
    ⟨deletedTail, hdeleted⟩
  rw [
    rejectPostFieldHandoff_rightMoveSource_eq_of_config_and_payload_append_last
      L pref leftBit deletedTail hdeleted hpayload]
  exact
    rejectPostFieldHandoff_localGap_haltsFrom_of_config_and_payload_append_last
      hnormalizer L pref leftBit deletedTail hdeleted hpayload

theorem rejectPostFieldHandoff_rightMove_haltsFrom
    {normalizer : MachineDescription}
    (hnormalizer : RejectPostFieldRemainingGapsSpec normalizer)
    (L : DovetailLayout) :
    (SeqViaCanonical
      sentinelGapCompactorDescription
      normalizer).HaltsFromTapeEquiv
      (Tape.move Direction.right
        (selectedProjectionPaddedTailCleanupScratchCountRejectAfterFirstFieldEraseTape
          L 0))
      (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape
        false L 0) := by
  rcases
      selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayload_append_last
        L with
    ⟨pref, leftBit, hpayload⟩
  exact
    rejectPostFieldHandoff_rightMove_haltsFrom_of_payload_append_last
      hnormalizer L pref leftBit hpayload

theorem rejectPostFieldHandoff_haltsFrom
    {normalizer : MachineDescription}
    (hnormalizer : RejectPostFieldRemainingGapsSpec normalizer)
    (L : DovetailLayout) :
    (SeqViaCanonical
      sentinelGapCompactorDescription
      normalizer).HaltsFromTapeEquiv
      (selectedProjectionPaddedTailCleanupScratchCountRejectPostFieldHandoffTape
        L 0)
      (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape
        false L 0) := by
  simpa [selectedProjectionPaddedTailCleanupScratchCountRejectPostFieldHandoffTape]
    using rejectPostFieldHandoff_rightMove_haltsFrom hnormalizer L

def acceptPostFieldHandoffBoundaryCleanupDescription : MachineDescription :=
  SeqViaCanonical sentinelGapCompactorDescription
    sentinelBoundaryCleanupDescription

theorem acceptPostFieldHandoffBoundaryCleanupDescription_subroutineReady :
    acceptPostFieldHandoffBoundaryCleanupDescription.SubroutineReady :=
  SeqViaCanonical_subroutineReady
    sentinelGapCompactorDescription_subroutineReady
    sentinelBoundaryCleanupDescription_subroutineReady

theorem acceptPostFieldHandoff_boundaryCleanupDescription_haltsFrom_of_config_and_payload_append_last
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool)
    (hdeleted :
      configurationFieldBits L.acceptConfig [] =
        false :: deletedTail)
    (hpayload :
      selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload
          L =
        List.append pref [leftBit]) :
    acceptPostFieldHandoffBoundaryCleanupDescription.HaltsFromTape
      (rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
        (rightBlankLocalGapBaseLeft deletedTail.length
          (selectedProjectionPaddedTailCleanupScratchCountAfterStageNormalizerLeftBase
            L))
        leftBit pref.reverse 0 [none, none, none, none, none])
      (acceptPostFieldHandoffAfterBoundaryCleanupTape
        L pref leftBit deletedTail) := by
  exact
    SeqViaCanonical_haltsFromTape_of_haltsFromTape
      sentinelGapCompactorDescription_subroutineReady
      sentinelBoundaryCleanupDescription_subroutineReady
      (acceptPostFieldHandoff_sentinelGap_haltsFrom_of_config_and_payload_append_last
        L pref leftBit deletedTail hdeleted hpayload)
      rfl
      (acceptPostFieldHandoff_boundaryCleanup_haltsFrom_of_config_and_payload_append_last
        L pref leftBit deletedTail hdeleted hpayload)

theorem acceptPostFieldHandoff_boundaryCleanupDescription_rightMove_haltsFrom_of_payload_append_last
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (hpayload :
      selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload
          L =
        List.append pref [leftBit]) :
    acceptPostFieldHandoffBoundaryCleanupDescription.HaltsFromTape
      (Tape.move Direction.right
        (selectedProjectionPaddedTailCleanupScratchCountAcceptAfterFirstFieldEraseTape
          L 0))
      (acceptPostFieldHandoffAfterBoundaryCleanupTape
        L pref leftBit
        (configurationFieldBits L.acceptConfig []).tail) := by
  rcases configurationFieldBits_cons_false L.acceptConfig [] with
    ⟨deletedTail, hdeleted⟩
  rw [
    acceptPostFieldHandoff_rightMoveSource_eq_of_config_and_payload_append_last
      L pref leftBit deletedTail hdeleted hpayload]
  have htail :
      (configurationFieldBits L.acceptConfig []).tail = deletedTail := by
    rw [hdeleted]
    rfl
  rw [htail]
  exact
    acceptPostFieldHandoff_boundaryCleanupDescription_haltsFrom_of_config_and_payload_append_last
      L pref leftBit deletedTail hdeleted hpayload

def AcceptPostFieldBoundaryToDecodedPrefixSpec
    (normalizer : MachineDescription) : Prop :=
  normalizer.SubroutineReady ∧
    forall (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
      (deletedTail : Word Bool),
      configurationFieldBits L.acceptConfig [] =
          false :: deletedTail ->
      selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload
          L =
        List.append pref [leftBit] ->
      normalizer.HaltsFromTapeEquiv
        (acceptPostFieldHandoffAfterBoundaryCleanupTape
          L pref leftBit deletedTail)
        (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape
          true L 0)

def AcceptPostFieldBoundaryToDecodedPrefixConstruction : Prop :=
  exists normalizer : MachineDescription,
    AcceptPostFieldBoundaryToDecodedPrefixSpec normalizer

def acceptPostFieldHandoffAfterBoundaryRepositionTape
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool) : Tape Bool :=
  Tape.move Direction.left
    (Tape.move Direction.left
      (acceptPostFieldHandoffAfterBoundaryCleanupTape
        L pref leftBit deletedTail))

theorem acceptPostFieldHandoff_boundaryReposition_haltsFrom
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool) :
    leftMoveTwiceDescription.HaltsFromTape
      (acceptPostFieldHandoffAfterBoundaryCleanupTape
        L pref leftBit deletedTail)
      (acceptPostFieldHandoffAfterBoundaryRepositionTape
        L pref leftBit deletedTail) := by
  simpa [acceptPostFieldHandoffAfterBoundaryRepositionTape] using
    leftMoveTwiceDescription_haltsFromTape
      (acceptPostFieldHandoffAfterBoundaryCleanupTape
        L pref leftBit deletedTail)

def AcceptPostFieldRepositionToDecodedPrefixSpec
    (normalizer : MachineDescription) : Prop :=
  normalizer.SubroutineReady ∧
    forall (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
      (deletedTail : Word Bool),
      configurationFieldBits L.acceptConfig [] =
          false :: deletedTail ->
      selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload
          L =
        List.append pref [leftBit] ->
      normalizer.HaltsFromTapeEquiv
        (acceptPostFieldHandoffAfterBoundaryRepositionTape
          L pref leftBit deletedTail)
        (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape
          true L 0)

def AcceptPostFieldRepositionToDecodedPrefixConstruction : Prop :=
  exists normalizer : MachineDescription,
    AcceptPostFieldRepositionToDecodedPrefixSpec normalizer

theorem acceptPostFieldHandoffAfterBoundaryRepositionTape_eq_rightEdgeRewindSource
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool) :
    acceptPostFieldHandoffAfterBoundaryRepositionTape
        L pref leftBit deletedTail =
      rightEdgeRewindSourceTape
        (List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
          (List.append pref [leftBit]))
        (none ::
          none ::
          leadingBlankLeftShiftTargetVisiblePadding
            (postFieldHandoffAfterSentinelGapPadding
              deletedTail [none, none, none, none, none])) := by
  simp [acceptPostFieldHandoffAfterBoundaryRepositionTape,
    acceptPostFieldHandoffAfterBoundaryCleanupTape,
    leadingBlankLeftShiftTargetTapeWithPadding_second_left_rewindSource]

def acceptPostFieldHandoffAfterRightEdgeRewindTape
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool) : Tape Bool :=
  rightEdgeRewindTargetTape
    (List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
      (List.append pref [leftBit]))
    (none ::
      none ::
      leadingBlankLeftShiftTargetVisiblePadding
        (postFieldHandoffAfterSentinelGapPadding
          deletedTail [none, none, none, none, none]))

-- After the accept-side right-edge rewind, the visible output is the selected
-- prefix followed by the payload bits that survived sentinel-gap padding.
theorem acceptPostFieldHandoffAfterRightEdgeRewindTape_normalizedOutput
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool) :
    Tape.normalizedOutput
        (acceptPostFieldHandoffAfterRightEdgeRewindTape
          L pref leftBit deletedTail) =
      List.append
        (List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
          (List.append pref [leftBit]))
        ((none ::
          none ::
          leadingBlankLeftShiftTargetVisiblePadding
            (postFieldHandoffAfterSentinelGapPadding
              deletedTail [none, none, none, none, none])).filterMap
                (fun cell => cell)) := by
  rw [acceptPostFieldHandoffAfterRightEdgeRewindTape,
    rightEdgeRewindTargetTape_normalizedOutput]

def AcceptPostFieldRepositionRightEdgeRewinderSpec
    (rewinder : MachineDescription) : Prop :=
  rewinder.SubroutineReady ∧
    forall (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
      (deletedTail : Word Bool),
      configurationFieldBits L.acceptConfig [] =
          false :: deletedTail ->
      selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload
          L =
        List.append pref [leftBit] ->
      rewinder.HaltsFromTape
        (acceptPostFieldHandoffAfterBoundaryRepositionTape
          L pref leftBit deletedTail)
        (acceptPostFieldHandoffAfterRightEdgeRewindTape
          L pref leftBit deletedTail)

def AcceptPostFieldRepositionRightEdgeRewinderConstruction : Prop :=
  exists rewinder : MachineDescription,
    AcceptPostFieldRepositionRightEdgeRewinderSpec rewinder

def AcceptPostFieldRewoundToDecodedPrefixSpec
    (normalizer : MachineDescription) : Prop :=
  normalizer.SubroutineReady ∧
    forall (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
      (deletedTail : Word Bool),
      configurationFieldBits L.acceptConfig [] =
          false :: deletedTail ->
      selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload
          L =
        List.append pref [leftBit] ->
      normalizer.HaltsFromTapeEquiv
        (acceptPostFieldHandoffAfterRightEdgeRewindTape
          L pref leftBit deletedTail)
        (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape
          true L 0)

def AcceptPostFieldRewoundToDecodedPrefixConstruction : Prop :=
  exists normalizer : MachineDescription,
    AcceptPostFieldRewoundToDecodedPrefixSpec normalizer

/--
Branch-independent padding for the decoded-prefix scan source.  The first
blank is the scan stop cell; the replicated blanks cover the counted scratch
window before the branch-specific post-count tail.
-/
def postFieldDecodedPrefixScanPadding
    (useAccept : Bool)
    (L : DovetailLayout) : List (Option Bool) :=
  none ::
    List.append
      (List.replicate
        (selectedProjectionPaddedTailCleanupScratchCountBits
          useAccept L).length
        (none : Option Bool))
      (selectedProjectionPaddedTailCleanupPostCountTailCells
        useAccept L 0)

/--
Common scan-source tape after post-field restoration.  Both accept and reject
branches should eventually reach this shape, then reuse
{name}`rightEdgeScanThenRightMoveDescription`.
-/
def postFieldDecodedPrefixScanSourceTape
    (useAccept : Bool)
    (L : DovetailLayout) : Tape Bool :=
  rightEdgeScanSourceTapeFromLeft [none]
    (ParsedLayoutBits L)
    (postFieldDecodedPrefixScanPadding useAccept L)

theorem postFieldDecodedPrefixScanSourceTape_normalizedOutput
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.normalizedOutput
        (postFieldDecodedPrefixScanSourceTape useAccept L) =
      List.append (ParsedLayoutBits L)
        ((postFieldDecodedPrefixScanPadding useAccept L).filterMap
          (fun cell => cell)) := by
  simp [postFieldDecodedPrefixScanSourceTape,
    rightEdgeScanSourceTapeFromLeft, tapeAtCells_normalizedOutput,
    List.filterMap_append, Function.comp_def]

/--
Expose the skipped/count split inside {name}`ParsedLayoutBits` for the shared
post-field materializer.  This is the cheap shape fact used before the hard
finite-machine restoration leaf.
-/
theorem postFieldDecodedPrefixScanSourceTape_eq_split
    (useAccept : Bool) (L : DovetailLayout) :
    postFieldDecodedPrefixScanSourceTape useAccept L =
      rightEdgeScanSourceTapeFromLeft [none]
        (List.append
          (selectedProjectionPaddedTailCleanupScratchSkippedBits
            useAccept L)
          (selectedProjectionPaddedTailCleanupScratchCountBits
            useAccept L))
        (postFieldDecodedPrefixScanPadding useAccept L) := by
  rw [postFieldDecodedPrefixScanSourceTape,
    selectedProjectionPaddedTailCleanupParsedLayoutBits_eq_skipped_append_count]

/--
The post-field scan source is the raw decoded-prefix source before the final
rewind.  This is the tape shape the branch materializers must rebuild from
their post-field handoff tapes.
-/
theorem postFieldDecodedPrefixScanSourceTape_eq_rawSourceTapeWithPostCountTail
    (useAccept : Bool) (L : DovetailLayout) :
    postFieldDecodedPrefixScanSourceTape useAccept L =
      selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithPostCountTail
        useAccept L 0 := by
  simp [postFieldDecodedPrefixScanSourceTape,
    postFieldDecodedPrefixScanPadding,
    selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithPostCountTail,
    rightEdgeScanSourceTapeFromLeft]

def acceptPostFieldDecodedPrefixScanPadding
    (L : DovetailLayout) : List (Option Bool) :=
  postFieldDecodedPrefixScanPadding true L

/--
Accept-specialized view of {name}`postFieldDecodedPrefixScanSourceTape`,
retained for the older accept-side construction names.
-/
def acceptPostFieldDecodedPrefixScanSourceTape
    (L : DovetailLayout) : Tape Bool :=
  postFieldDecodedPrefixScanSourceTape true L

/--
Select the branch-specific payload that survived the first-field eraser.
The shared materializer proves against this selector, while the old accept and
reject wrappers specialize it to their existing payload names.
-/
def countWindowPostFieldDecodedPrefixMaterializerPayload
    (useAccept : Bool) (L : DovetailLayout) : Word Bool :=
  if useAccept then
    selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload L
  else
    selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayload L

/--
Branch-specific source tape for the shared post-field materializer.  Accept
starts from the right-edge-rewound handoff tape; reject starts from the rewound
handoff exposed by the reject restorer path.
-/
def countWindowPostFieldDecodedPrefixMaterializerSourceTape
    (useAccept : Bool) (L : DovetailLayout) (pref : Word Bool)
    (leftBit : Bool) (deletedTail : Word Bool) : Tape Bool :=
  if useAccept then
    acceptPostFieldHandoffAfterRightEdgeRewindTape
      L pref leftBit deletedTail
  else
    rejectPostFieldDecodedPrefixRestorerSourceTape
      L pref leftBit deletedTail

theorem countWindowPostFieldDecodedPrefixMaterializerPayload_true
    (L : DovetailLayout) :
    countWindowPostFieldDecodedPrefixMaterializerPayload true L =
      selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload
        L := by
  rfl

theorem countWindowPostFieldDecodedPrefixMaterializerPayload_false
    (L : DovetailLayout) :
    countWindowPostFieldDecodedPrefixMaterializerPayload false L =
      selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayload
        L := by
  rfl

theorem countWindowPostFieldDecodedPrefixMaterializerSourceTape_true
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool) :
    countWindowPostFieldDecodedPrefixMaterializerSourceTape
        true L pref leftBit deletedTail =
      acceptPostFieldHandoffAfterRightEdgeRewindTape
        L pref leftBit deletedTail := by
  rfl

theorem countWindowPostFieldDecodedPrefixMaterializerSourceTape_false
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool) :
    countWindowPostFieldDecodedPrefixMaterializerSourceTape
        false L pref leftBit deletedTail =
      rejectPostFieldDecodedPrefixRestorerSourceTape
        L pref leftBit deletedTail := by
  rfl

/--
Finite-machine contract for one branch of the shared post-field materializer.
It rebuilds a tape equivalent to the full decoded {name}`ParsedLayoutBits` scan
source from the branch's post-field right-edge tape.
-/
def CountWindowPostFieldDecodedPrefixScanSourceMaterializerSpec
    (useAccept : Bool)
    (materializer : MachineDescription) : Prop :=
  materializer.SubroutineReady ∧
    forall (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
      (deletedTail : Word Bool),
      configurationFieldBits L.acceptConfig [] =
          false :: deletedTail ->
      countWindowPostFieldDecodedPrefixMaterializerPayload
          useAccept L =
        List.append pref [leftBit] ->
      materializer.HaltsFromTapeEquiv
        (countWindowPostFieldDecodedPrefixMaterializerSourceTape
          useAccept L pref leftBit deletedTail)
        (postFieldDecodedPrefixScanSourceTape useAccept L)

/--
Branch-indexed existence wrapper for
{name}`CountWindowPostFieldDecodedPrefixScanSourceMaterializerSpec`.  The
accept and reject branches may use different finite machines while sharing the
same contract shape.
-/
def CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction :
    Prop :=
  forall useAccept : Bool,
  exists materializer : MachineDescription,
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerSpec
      useAccept materializer

def RejectPostFieldDecodedPrefixScanSourceMaterializerConstruction :
    Prop :=
  exists materializer : MachineDescription,
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerSpec
      false materializer

def AcceptPostFieldDecodedPrefixScanSourceMaterializerConstruction :
    Prop :=
  exists materializer : MachineDescription,
    CountWindowPostFieldDecodedPrefixScanSourceMaterializerSpec
      true materializer

/-
The one-tape materializer contract is kept as a composition boundary up to tape
equivalence, but this module no longer exports an unproved concrete
construction for it.  The proved replacement for the decoded-prefix extractor
is the lowered structured three-tape construction in
{module}`FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge`.
-/

/--
Reject-specialized wrapper contract for the shared post-field materializer.
It keeps the older reject construction boundary while routing through
{name}`postFieldDecodedPrefixScanSourceTape`.
-/
def RejectPostFieldDecodedPrefixScanSourceSpec
    (materializer : MachineDescription) : Prop :=
  materializer.SubroutineReady ∧
    forall (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
      (deletedTail : Word Bool),
      configurationFieldBits L.acceptConfig [] =
          false :: deletedTail ->
      selectedProjectionPaddedTailCleanupScratchCountRejectFirstFieldPayload
          L =
        List.append pref [leftBit] ->
      materializer.HaltsFromTapeEquiv
        (rejectPostFieldDecodedPrefixRestorerSourceTape
          L pref leftBit deletedTail)
        (postFieldDecodedPrefixScanSourceTape false L)

/-- Existence wrapper for {name}`RejectPostFieldDecodedPrefixScanSourceSpec`. -/
def RejectPostFieldDecodedPrefixScanSourceConstruction : Prop :=
  exists materializer : MachineDescription,
    RejectPostFieldDecodedPrefixScanSourceSpec materializer

/--
Accept-specialized wrapper contract for the shared post-field materializer.
This preserves the older accept construction boundary while the implementation
is supplied by the branch-indexed materializer.
-/
def AcceptPostFieldRewoundToDecodedPrefixScanSourceSpec
    (materializer : MachineDescription) : Prop :=
  materializer.SubroutineReady ∧
    forall (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
      (deletedTail : Word Bool),
      configurationFieldBits L.acceptConfig [] =
          false :: deletedTail ->
      selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload
          L =
        List.append pref [leftBit] ->
      materializer.HaltsFromTapeEquiv
        (acceptPostFieldHandoffAfterRightEdgeRewindTape
          L pref leftBit deletedTail)
        (acceptPostFieldDecodedPrefixScanSourceTape L)

/-- Existence wrapper for {name}`AcceptPostFieldRewoundToDecodedPrefixScanSourceSpec`. -/
def AcceptPostFieldRewoundToDecodedPrefixScanSourceConstruction :
    Prop :=
  exists materializer : MachineDescription,
    AcceptPostFieldRewoundToDecodedPrefixScanSourceSpec materializer

/--
Project the reject branch out of the shared count-window post-field
materializer.
-/
theorem rejectPostFieldDecodedPrefixScanSourceConstruction_of_countWindowMaterializer
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction) :
    RejectPostFieldDecodedPrefixScanSourceConstruction := by
  rcases hmaterializer false with ⟨materializer, hmaterializerSpec⟩
  exact
    ⟨materializer,
      hmaterializerSpec.left,
      fun L pref leftBit deletedTail hdeleted hpayload => by
        simpa [
          countWindowPostFieldDecodedPrefixMaterializerPayload_false,
          countWindowPostFieldDecodedPrefixMaterializerSourceTape_false] using
          hmaterializerSpec.right
            L pref leftBit deletedTail hdeleted hpayload⟩

/--
Project the accept branch out of the shared count-window post-field
materializer.
-/
theorem acceptPostFieldRewoundToDecodedPrefixScanSourceConstruction_of_countWindowMaterializer
    (hmaterializer :
      CountWindowPostFieldDecodedPrefixScanSourceMaterializerConstruction) :
    AcceptPostFieldRewoundToDecodedPrefixScanSourceConstruction := by
  rcases hmaterializer true with ⟨materializer, hmaterializerSpec⟩
  exact
    ⟨materializer,
      hmaterializerSpec.left,
      fun L pref leftBit deletedTail hdeleted hpayload => by
        simpa [
          acceptPostFieldDecodedPrefixScanSourceTape,
          countWindowPostFieldDecodedPrefixMaterializerPayload_true,
          countWindowPostFieldDecodedPrefixMaterializerSourceTape_true] using
          hmaterializerSpec.right
            L pref leftBit deletedTail hdeleted hpayload⟩

def AcceptPostFieldDecodedPrefixScanToRewindSpec
    (scanner : MachineDescription) : Prop :=
  scanner.SubroutineReady ∧
    forall L : DovetailLayout,
      scanner.HaltsFromTapeEquiv
        (acceptPostFieldDecodedPrefixScanSourceTape L)
        (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape
          true L 0)

def AcceptPostFieldDecodedPrefixScanToRewindConstruction :
    Prop :=
  exists scanner : MachineDescription,
    AcceptPostFieldDecodedPrefixScanToRewindSpec scanner

def postFieldDecodedPrefixScanToRewindDescription :
    MachineDescription :=
  rightEdgeScanThenRightMoveDescription

theorem postFieldDecodedPrefixScanToRewindDescription_subroutineReady :
    postFieldDecodedPrefixScanToRewindDescription.SubroutineReady :=
  rightEdgeScanThenRightMoveDescription_subroutineReady

theorem postFieldDecodedPrefixScanSourceTape_move_left_move_right
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (postFieldDecodedPrefixScanSourceTape useAccept L)) =
      postFieldDecodedPrefixScanSourceTape useAccept L := by
  simpa [postFieldDecodedPrefixScanSourceTape,
    postFieldDecodedPrefixScanPadding] using
    rightEdgeScanSourceTapeFromLeft_move_left_move_right_padding_cons
      [none] (ParsedLayoutBits L) (none : Option Bool)
      (List.append
        (List.replicate
          (selectedProjectionPaddedTailCleanupScratchCountBits
            useAccept L).length
          (none : Option Bool))
        (selectedProjectionPaddedTailCleanupPostCountTailCells
          useAccept L 0))

theorem postFieldDecodedPrefixScanToRewind_haltsFrom
    (useAccept : Bool) (L : DovetailLayout) :
    postFieldDecodedPrefixScanToRewindDescription.HaltsFromTapeEquiv
      (postFieldDecodedPrefixScanSourceTape useAccept L)
      (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape
        useAccept L 0) := by
  simpa [postFieldDecodedPrefixScanToRewindDescription,
    postFieldDecodedPrefixScanSourceTape,
    postFieldDecodedPrefixScanPadding,
    selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape] using
    rightEdgeScanThenRightMoveDescription_haltsFromTapeEquiv
      (ParsedLayoutBits L)
      (List.append
        (List.replicate
          (selectedProjectionPaddedTailCleanupScratchCountBits
            useAccept L).length
          (none : Option Bool))
        (selectedProjectionPaddedTailCleanupPostCountTailCells
          useAccept L 0))

def acceptPostFieldDecodedPrefixScanToRewindDescription :
    MachineDescription :=
  postFieldDecodedPrefixScanToRewindDescription

theorem acceptPostFieldDecodedPrefixScanToRewindDescription_subroutineReady :
    acceptPostFieldDecodedPrefixScanToRewindDescription.SubroutineReady :=
  postFieldDecodedPrefixScanToRewindDescription_subroutineReady

theorem acceptPostFieldDecodedPrefixScanSourceTape_move_left_move_right
    (L : DovetailLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (acceptPostFieldDecodedPrefixScanSourceTape L)) =
      acceptPostFieldDecodedPrefixScanSourceTape L := by
  simpa [acceptPostFieldDecodedPrefixScanSourceTape] using
    postFieldDecodedPrefixScanSourceTape_move_left_move_right true L

theorem acceptPostFieldDecodedPrefixScanToRewind_haltsFrom
    (L : DovetailLayout) :
    acceptPostFieldDecodedPrefixScanToRewindDescription.HaltsFromTapeEquiv
      (acceptPostFieldDecodedPrefixScanSourceTape L)
      (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape
        true L 0) := by
  simpa [acceptPostFieldDecodedPrefixScanToRewindDescription,
    acceptPostFieldDecodedPrefixScanSourceTape] using
    postFieldDecodedPrefixScanToRewind_haltsFrom true L

theorem acceptPostFieldDecodedPrefixScanToRewindConstruction_core :
    AcceptPostFieldDecodedPrefixScanToRewindConstruction := by
  exact
    ⟨acceptPostFieldDecodedPrefixScanToRewindDescription,
      acceptPostFieldDecodedPrefixScanToRewindDescription_subroutineReady,
      fun L =>
        acceptPostFieldDecodedPrefixScanToRewind_haltsFrom L⟩

theorem rejectPostFieldDecodedPrefixRestorerConstruction_of_scanSource
    (hmaterializer : RejectPostFieldDecodedPrefixScanSourceConstruction) :
    RejectPostFieldDecodedPrefixRestorerConstruction := by
  rcases hmaterializer with ⟨materializer, hmaterializerSpec⟩
  exact
    ⟨canonicalSeqDescription materializer
        postFieldDecodedPrefixScanToRewindDescription,
      by
        constructor
        · exact
            canonicalSeqDescription_subroutineReady
              hmaterializerSpec.left
              postFieldDecodedPrefixScanToRewindDescription_subroutineReady
        · intro L pref leftBit deletedTail hdeleted hpayload
          exact
            canonicalSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv
              hmaterializerSpec.left
              postFieldDecodedPrefixScanToRewindDescription_subroutineReady
              (hmaterializerSpec.right
                L pref leftBit deletedTail hdeleted hpayload)
              (postFieldDecodedPrefixScanSourceTape_move_left_move_right
                false L)
              (postFieldDecodedPrefixScanToRewind_haltsFrom
                false L)⟩

theorem acceptPostFieldHandoff_rightEdgeRewind_haltsFrom
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool) :
    rightEdgeRewindDescription.HaltsFromTape
      (acceptPostFieldHandoffAfterBoundaryRepositionTape
        L pref leftBit deletedTail)
      (acceptPostFieldHandoffAfterRightEdgeRewindTape
        L pref leftBit deletedTail) := by
  rw [acceptPostFieldHandoffAfterBoundaryRepositionTape_eq_rightEdgeRewindSource]
  exact
    rightEdgeRewindDescription_haltsFromTape
      (List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
        (List.append pref [leftBit]))
      (none ::
        none ::
        leadingBlankLeftShiftTargetVisiblePadding
          (postFieldHandoffAfterSentinelGapPadding
            deletedTail [none, none, none, none, none]))

theorem acceptPostFieldRepositionRightEdgeRewinderConstruction_core :
    AcceptPostFieldRepositionRightEdgeRewinderConstruction := by
  exact
    ⟨rightEdgeRewindDescription,
      rightEdgeRewindDescription_subroutineReady,
      fun L pref leftBit deletedTail _hdeleted _hpayload =>
        acceptPostFieldHandoff_rightEdgeRewind_haltsFrom
          L pref leftBit deletedTail⟩

theorem acceptPostFieldHandoffAfterRightEdgeRewindTape_move_left_move_right
    (L : DovetailLayout) (pref : Word Bool) (leftBit : Bool)
    (deletedTail : Word Bool) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (acceptPostFieldHandoffAfterRightEdgeRewindTape
            L pref leftBit deletedTail)) =
      acceptPostFieldHandoffAfterRightEdgeRewindTape
        L pref leftBit deletedTail := by
  cases hbits :
      List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
        (List.append pref [leftBit]) with
  | nil =>
      cases pref <;>
        simp at hbits
  | cons first rest =>
      unfold acceptPostFieldHandoffAfterRightEdgeRewindTape
      rw [hbits]
      exact
        rightEdgeRewindTargetTape_move_left_move_right_cons
          first rest
          (none ::
            none ::
            leadingBlankLeftShiftTargetVisiblePadding
              (postFieldHandoffAfterSentinelGapPadding
                deletedTail [none, none, none, none, none]))

theorem acceptPostFieldRepositionToDecodedPrefixConstruction_of_rewinderAndRestorer
    (hrewinder : AcceptPostFieldRepositionRightEdgeRewinderConstruction)
    (hrestorer : AcceptPostFieldRewoundToDecodedPrefixConstruction) :
    AcceptPostFieldRepositionToDecodedPrefixConstruction := by
  rcases hrewinder with ⟨rewinder, hrewinderSpec⟩
  rcases hrestorer with ⟨restorer, hrestorerSpec⟩
  exact
    ⟨canonicalSeqDescription rewinder restorer,
      by
        constructor
        · exact
            canonicalSeqDescription_subroutineReady
              hrewinderSpec.left hrestorerSpec.left
        · intro L pref leftBit deletedTail hdeleted hpayload
          exact
            canonicalSeqDescription_haltsFromTapeEquiv_of_haltsFromTape
              hrewinderSpec.left
              hrestorerSpec.left
              (hrewinderSpec.right
                L pref leftBit deletedTail hdeleted hpayload)
              (acceptPostFieldHandoffAfterRightEdgeRewindTape_move_left_move_right
                L pref leftBit deletedTail)
              (hrestorerSpec.right
                L pref leftBit deletedTail hdeleted hpayload)⟩

theorem acceptPostFieldBoundaryToDecodedPrefixConstruction_of_reposition
    (hreposition : AcceptPostFieldRepositionToDecodedPrefixConstruction) :
    AcceptPostFieldBoundaryToDecodedPrefixConstruction := by
  rcases hreposition with ⟨normalizer, hnormalizer⟩
  exact
    ⟨SeqViaCanonical leftMoveTwiceDescription normalizer,
      by
        constructor
        · exact
            SeqViaCanonical_subroutineReady
              leftMoveTwiceDescription_subroutineReady
              hnormalizer.left
        · intro L pref leftBit deletedTail hdeleted hpayload
          exact
            SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
              leftMoveTwiceDescription_subroutineReady
              hnormalizer.left
              (acceptPostFieldHandoff_boundaryReposition_haltsFrom
                L pref leftBit deletedTail).toEquiv
              (Tape.Equiv.refl _)
              (hnormalizer.right
                L pref leftBit deletedTail hdeleted hpayload)⟩

theorem acceptPostFieldRewoundToDecodedPrefixConstruction_of_scanSource
    (hmaterializer :
      AcceptPostFieldRewoundToDecodedPrefixScanSourceConstruction)
    (hscanner : AcceptPostFieldDecodedPrefixScanToRewindConstruction) :
    AcceptPostFieldRewoundToDecodedPrefixConstruction := by
  rcases hmaterializer with ⟨materializer, hmaterializerSpec⟩
  rcases hscanner with ⟨scanner, hscannerSpec⟩
  exact
    ⟨canonicalSeqDescription materializer scanner,
      by
        constructor
        · exact
            canonicalSeqDescription_subroutineReady
              hmaterializerSpec.left hscannerSpec.left
        · intro L pref leftBit deletedTail hdeleted hpayload
          exact
            canonicalSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv
              hmaterializerSpec.left
              hscannerSpec.left
              (hmaterializerSpec.right
                L pref leftBit deletedTail hdeleted hpayload)
              (acceptPostFieldDecodedPrefixScanSourceTape_move_left_move_right
                L)
              (hscannerSpec.right L)⟩

theorem acceptPostFieldHandoff_haltsFrom_of_boundaryToDecoded
    {normalizer : MachineDescription}
    (hnormalizer :
      AcceptPostFieldBoundaryToDecodedPrefixSpec normalizer)
    (L : DovetailLayout) :
    (SeqViaCanonical
      acceptPostFieldHandoffBoundaryCleanupDescription
      normalizer).HaltsFromTapeEquiv
      (selectedProjectionPaddedTailCleanupScratchCountAcceptPostFieldHandoffTape
        L 0)
      (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape
        true L 0) := by
  rcases
      selectedProjectionPaddedTailCleanupScratchCountAcceptFirstFieldPayload_append_last
        L with
    ⟨pref, leftBit, hpayload⟩
  rcases configurationFieldBits_cons_false L.acceptConfig [] with
    ⟨deletedTail, hdeleted⟩
  have htail :
      (configurationFieldBits L.acceptConfig []).tail = deletedTail := by
    rw [hdeleted]
    rfl
  have hcleanup :
      acceptPostFieldHandoffBoundaryCleanupDescription.HaltsFromTape
        (selectedProjectionPaddedTailCleanupScratchCountAcceptPostFieldHandoffTape
          L 0)
        (acceptPostFieldHandoffAfterBoundaryCleanupTape
          L pref leftBit deletedTail) := by
    simpa [
      selectedProjectionPaddedTailCleanupScratchCountAcceptPostFieldHandoffTape,
      htail] using
      acceptPostFieldHandoff_boundaryCleanupDescription_rightMove_haltsFrom_of_payload_append_last
        L pref leftBit hpayload
  simpa [selectedProjectionPaddedTailCleanupScratchCountAcceptPostFieldHandoffTape]
    using
      SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
        acceptPostFieldHandoffBoundaryCleanupDescription_subroutineReady
        hnormalizer.left
        hcleanup.toEquiv
        (by
          rw [
            acceptPostFieldHandoffAfterBoundaryCleanupTape_move_left_move_right
              L pref leftBit deletedTail]
          exact Tape.Equiv.refl _)
        (hnormalizer.right L pref leftBit deletedTail hdeleted hpayload)

theorem selectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixPostFieldHandoffCoreConstruction_of_remainingGaps
    (hremaining : RejectPostFieldRemainingGapsConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixPostFieldHandoffCoreConstruction := by
  rcases hremaining with ⟨normalizer, hnormalizer⟩
  exact
    ⟨SeqViaCanonical
        sentinelGapCompactorDescription normalizer,
      SeqViaCanonical_subroutineReady
        sentinelGapCompactorDescription_subroutineReady
        hnormalizer.left,
      fun L => rejectPostFieldHandoff_haltsFrom hnormalizer L⟩

theorem selectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixRewinderConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixRewinderConstruction := by
  intro useAccept
  exact
    ⟨sourceRewindDescription,
      sourceRewindDescription_subroutineReady,
      fun L =>
        sourceRewindDescription_haltsFrom_scratchCountDecodedPrefixRewindSourceTape
          useAccept L 0⟩

theorem selectedProjectionPaddedTailCleanupScratchCountWindowPositionerConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowPositionerConstruction := by
  intro useAccept
  exact
    selectedProjectionPaddedTailCleanupScratchCountWindowPositionerConstruction_of_handoffCore
      (selectedProjectionPaddedTailCleanupScratchCountWindowRawToCounterHandoffCoreConstruction_of_suffixPositioner
        scratchCountSuffixPositionerHandoffConstruction_core)

def SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerOpenConstructions :
    Prop :=
  AcceptPostFieldBoundaryToDecodedPrefixConstruction ∧
  RejectPostFieldRemainingGapsConstruction

theorem selectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixPostFieldHandoffCoreConstruction_of_boundaryToDecoded
    (hboundary : AcceptPostFieldBoundaryToDecodedPrefixConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixPostFieldHandoffCoreConstruction := by
  rcases hboundary with ⟨normalizer, hnormalizer⟩
  exact
    ⟨SeqViaCanonical
        acceptPostFieldHandoffBoundaryCleanupDescription normalizer,
      SeqViaCanonical_subroutineReady
        acceptPostFieldHandoffBoundaryCleanupDescription_subroutineReady
        hnormalizer.left,
      acceptPostFieldHandoff_haltsFrom_of_boundaryToDecoded
        hnormalizer⟩

theorem selectedProjectionPaddedTailCleanupScratchCountWindowDecoderConstruction_of_materializerOpenConstructions
    (hleaves :
      SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerOpenConstructions) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowDecoderConstruction := by
  rcases hleaves with ⟨hacceptBoundary, hrejectRemaining⟩
  let hacceptHandoffCore :
      SelectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixPostFieldHandoffCoreConstruction :=
    selectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixPostFieldHandoffCoreConstruction_of_boundaryToDecoded
      hacceptBoundary
  let hrejectHandoffCore :
      SelectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixPostFieldHandoffCoreConstruction :=
    selectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixPostFieldHandoffCoreConstruction_of_remainingGaps
      hrejectRemaining
  let hacceptPostField :
      SelectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixPostFieldNormalizerConstruction :=
    selectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixPostFieldNormalizerConstruction_of_handoffCore
      hacceptHandoffCore
  let hrejectPostField :
      SelectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixPostFieldNormalizerConstruction :=
    selectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixPostFieldNormalizerConstruction_of_handoffCore
      hrejectHandoffCore
  let hacceptTail :
      SelectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixTailNormalizerConstruction :=
    selectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixTailNormalizerConstruction_of_firstFieldAndPostField
      selectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixFirstFieldEraserConstruction_core
      hacceptPostField
  let hrejectTail :
      SelectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixTailNormalizerConstruction :=
    selectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixTailNormalizerConstruction_of_firstFieldAndPostField
      selectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixFirstFieldEraserConstruction_core
      hrejectPostField
  let htail :
      SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixTailNormalizerConstruction :=
    selectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixTailNormalizerConstruction_of_branches
      hacceptTail hrejectTail
  let hnormalizer :
      SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixNormalizerConstruction :=
    selectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixNormalizerConstruction_of_stageScannerAndTailNormalizer
      selectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixStageScannerConstruction_core
      htail
  let hrestorer :
      SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixRestorerConstruction :=
    selectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixRestorerConstruction_of_normalizerAndRewinder
      hnormalizer
      selectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixRewinderConstruction_core
  exact
    selectedProjectionPaddedTailCleanupScratchCountWindowDecoderConstruction_of_prefixScannerAndDecodedRestorer
      selectedProjectionPaddedTailCleanupScratchCountWindowPrefixScannerConstruction_core
      hrestorer

theorem selectedProjectionPaddedTailCleanupScratchCountWindowPositionerConstruction_of_materializerOpenConstructions
    (hleaves :
      SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerOpenConstructions) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowPositionerConstruction := by
  rcases hleaves with ⟨_hacceptBoundary, _hrejectRemaining⟩
  intro useAccept
  exact
    selectedProjectionPaddedTailCleanupScratchCountWindowPositionerConstruction_of_handoffCore
      (selectedProjectionPaddedTailCleanupScratchCountWindowRawToCounterHandoffCoreConstruction_of_suffixPositioner
        scratchCountSuffixPositionerHandoffConstruction_core)

theorem selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction_of_openConstructions
    (hleaves :
      SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerOpenConstructions) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction :=
  selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction_of_decoderAndPositioner
    (selectedProjectionPaddedTailCleanupScratchCountWindowDecoderConstruction_of_materializerOpenConstructions
      hleaves)
    (selectedProjectionPaddedTailCleanupScratchCountWindowPositionerConstruction_of_materializerOpenConstructions
      hleaves)

theorem scratchCountSuffixRightEdgeScannerConstruction_core :
    ScratchCountSuffixRightEdgeScannerConstruction := by
  exact
    ⟨erasePreservingScanDescription,
      erasePreservingScanDescription_subroutineReady,
      fun pref suffix rightTail _hpos =>
        erasePreservingScanDescription_haltsFrom_scratchCountSuffixRestorerSourceTape
          pref suffix rightTail⟩

theorem scratchCountSuffixRightEdgeLocalCompactorConstruction_core :
    ScratchCountSuffixRightEdgeLocalCompactorConstruction := by
  exact
    ⟨rightBlankLocalGapCompactorDescription,
      rightBlankLocalGapCompactorDescription_subroutineReady,
      fun pref suffix rightTail hpos =>
        rightBlankLocalGapCompactorDescription_haltsFrom_scratchCountSuffixRestorerRightEdgeTape
          pref suffix rightTail hpos⟩

theorem scratchCountSuffixCompactedRightEdgeRewinderConstruction_core :
    ScratchCountSuffixCompactedRightEdgeRewinderConstruction := by
  exact
    ⟨selectedProjectionPaddedTailCleanupSentinelRewindDescription,
      selectedProjectionPaddedTailCleanupSentinelRewindDescription_subroutineReady,
      fun pref suffix rightTail hpos =>
        sentinelRewindDescription_haltsFrom_scratchCountCompactedRightEdgeTape
          pref suffix rightTail hpos⟩

def scratchCountSuffixExtraBlankPadding
    (suffix : Word Bool) (rightTail : List (Option Bool)) :
    List (Option Bool) :=
  none ::
    none ::
    none ::
    List.append
      (List.replicate (suffix.length - 1) (none : Option Bool))
      rightTail

def scratchCountSuffixExtraBlankRightGapTape
    (pref suffix : Word Bool) (rightTail : List (Option Bool)) :
    Tape Bool :=
  rightEdgeRewindSourceTapeWithBase []
    (List.append pref suffix)
    (scratchCountSuffixExtraBlankPadding suffix rightTail)

def ScratchCountSuffixExtraBlankRightGapScannerSpec
    (scanner : MachineDescription) : Prop :=
  scanner.SubroutineReady ∧
    forall (pref suffix : Word Bool)
      (rightTail : List (Option Bool)),
      0 < suffix.length ->
        scanner.HaltsFromTape
          (scratchCountSuffixRestorerExtraBlankRewindTape
            pref suffix rightTail)
          (scratchCountSuffixExtraBlankRightGapTape
            pref suffix rightTail)

def ScratchCountSuffixExtraBlankRightGapScannerConstruction :
    Prop :=
  exists scanner : MachineDescription,
    ScratchCountSuffixExtraBlankRightGapScannerSpec scanner

def ScratchCountSuffixExtraBlankRightGapRestorerSpec
    (restorer : MachineDescription) : Prop :=
  restorer.SubroutineReady ∧
    forall (pref suffix : Word Bool)
      (rightTail : List (Option Bool)),
      0 < suffix.length ->
        restorer.HaltsFromTape
          (scratchCountSuffixExtraBlankRightGapTape
            pref suffix rightTail)
          (scratchCountSuffixRestorerExtraBlankRewindTape
            pref suffix rightTail)

def ScratchCountSuffixExtraBlankRightGapRestorerConstruction :
    Prop :=
  exists restorer : MachineDescription,
    ScratchCountSuffixExtraBlankRightGapRestorerSpec restorer

def scratchCountSuffixExtraBlankLeftBoundaryTape
    (pref suffix : Word Bool) (rightTail : List (Option Bool)) :
    Tape Bool :=
  rightEdgeRewindTargetTapeWithBase []
    (List.append pref suffix)
    (scratchCountSuffixExtraBlankPadding suffix rightTail)

theorem scratchCountSuffixExtraBlankLeftBoundaryTape_eq_extraBlankRewindTape
    (pref suffix : Word Bool) (rightTail : List (Option Bool)) :
    scratchCountSuffixExtraBlankLeftBoundaryTape pref suffix rightTail =
      scratchCountSuffixRestorerExtraBlankRewindTape
        pref suffix rightTail := by
  rfl

def ScratchCountSuffixExtraBlankLeftBoundaryRewinderSpec
    (rewinder : MachineDescription) : Prop :=
  rewinder.SubroutineReady ∧
    forall (pref suffix : Word Bool)
      (rightTail : List (Option Bool)),
      0 < suffix.length ->
        rewinder.HaltsFromTape
          (scratchCountSuffixExtraBlankRightGapTape
            pref suffix rightTail)
          (scratchCountSuffixExtraBlankLeftBoundaryTape
            pref suffix rightTail)

def ScratchCountSuffixExtraBlankLeftBoundaryRewinderConstruction :
    Prop :=
  exists rewinder : MachineDescription,
    ScratchCountSuffixExtraBlankLeftBoundaryRewinderSpec rewinder

def ScratchCountSuffixExtraBlankLeftBoundaryRestorerSpec
    (restorer : MachineDescription) : Prop :=
  restorer.SubroutineReady ∧
    forall (pref suffix : Word Bool)
      (rightTail : List (Option Bool)),
      0 < suffix.length ->
        restorer.HaltsFromTape
          (scratchCountSuffixExtraBlankLeftBoundaryTape
            pref suffix rightTail)
          (scratchCountSuffixRestorerExtraBlankRewindTape
            pref suffix rightTail)

def ScratchCountSuffixExtraBlankLeftBoundaryRestorerConstruction :
    Prop :=
  exists restorer : MachineDescription,
    ScratchCountSuffixExtraBlankLeftBoundaryRestorerSpec restorer

theorem scratchCountSuffixExtraBlankLeftBoundaryTape_move_left_move_right
    (pref suffix : Word Bool) (rightTail : List (Option Bool))
    (hpos : 0 < suffix.length) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (scratchCountSuffixExtraBlankLeftBoundaryTape
            pref suffix rightTail)) =
      scratchCountSuffixExtraBlankLeftBoundaryTape
        pref suffix rightTail := by
  cases pref with
  | nil =>
      cases suffix with
      | nil =>
          simp at hpos
      | cons bit rest =>
          simpa [scratchCountSuffixExtraBlankLeftBoundaryTape,
            scratchCountSuffixExtraBlankPadding] using
            rightEdgeRewindTargetTapeWithBase_move_left_move_right_cons
              ([] : List (Option Bool)) bit rest
              (scratchCountSuffixExtraBlankPadding (bit :: rest)
                rightTail)
  | cons bit prefRest =>
      simpa [scratchCountSuffixExtraBlankLeftBoundaryTape,
        scratchCountSuffixExtraBlankPadding, List.append_assoc] using
        rightEdgeRewindTargetTapeWithBase_move_left_move_right_cons
          ([] : List (Option Bool)) bit (List.append prefRest suffix)
          (scratchCountSuffixExtraBlankPadding suffix rightTail)

theorem scratchCountSuffixExtraBlankLeftBoundaryRewinder_haltsFrom
    (pref suffix : Word Bool) (rightTail : List (Option Bool)) :
    rightEdgeRewindDescription.HaltsFromTape
      (scratchCountSuffixExtraBlankRightGapTape
        pref suffix rightTail)
      (scratchCountSuffixExtraBlankLeftBoundaryTape
        pref suffix rightTail) := by
  simpa [scratchCountSuffixExtraBlankRightGapTape,
    scratchCountSuffixExtraBlankLeftBoundaryTape] using
    rightEdgeRewindDescription_haltsFromTapeWithBase
      ([] : List (Option Bool)) (List.append pref suffix)
      (scratchCountSuffixExtraBlankPadding suffix rightTail)

theorem scratchCountSuffixExtraBlankLeftBoundaryRewinderConstruction_core :
    ScratchCountSuffixExtraBlankLeftBoundaryRewinderConstruction := by
  exact
    ⟨rightEdgeRewindDescription,
      rightEdgeRewindDescription_subroutineReady,
      fun pref suffix rightTail _hpos =>
        scratchCountSuffixExtraBlankLeftBoundaryRewinder_haltsFrom
          pref suffix rightTail⟩

theorem scratchCountSuffixExtraBlankRightGapRestorerConstruction_of_leftBoundaryParts
    (hrewinder : ScratchCountSuffixExtraBlankLeftBoundaryRewinderConstruction)
    (hrestorer : ScratchCountSuffixExtraBlankLeftBoundaryRestorerConstruction) :
    ScratchCountSuffixExtraBlankRightGapRestorerConstruction := by
  rcases hrewinder with ⟨rewinder, hrewinderSpec⟩
  rcases hrestorer with ⟨restorer, hrestorerSpec⟩
  exact
    ⟨canonicalSeqDescription rewinder restorer,
      by
        constructor
        · exact canonicalSeqDescription_subroutineReady
            hrewinderSpec.left hrestorerSpec.left
        · intro pref suffix rightTail hpos
          exact
            canonicalSeqDescription_haltsFromTape_of_haltsFromTape
              hrewinderSpec.left
              hrestorerSpec.left
              (hrewinderSpec.right pref suffix rightTail hpos)
              (scratchCountSuffixExtraBlankLeftBoundaryTape_move_left_move_right
                pref suffix rightTail hpos)
              (hrestorerSpec.right pref suffix rightTail hpos)⟩

theorem scratchCountSuffixExtraBlankRightGapTape_move_left_move_right
    (pref suffix : Word Bool) (rightTail : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (scratchCountSuffixExtraBlankRightGapTape
            pref suffix rightTail)) =
      scratchCountSuffixExtraBlankRightGapTape
        pref suffix rightTail := by
  simpa [scratchCountSuffixExtraBlankRightGapTape,
    scratchCountSuffixExtraBlankPadding] using
    rightEdgeRewindSourceTapeWithBase_move_left_move_right_padding_cons
      ([] : List (Option Bool)) (List.append pref suffix)
      (none : Option Bool)
      (none ::
        none ::
        List.append
          (List.replicate (suffix.length - 1) (none : Option Bool))
          rightTail)

theorem scratchCountSuffixExtraBlankRightGapScanner_haltsFrom
    (pref suffix : Word Bool) (rightTail : List (Option Bool))
    (hpos : 0 < suffix.length) :
    (canonicalSeqDescription rightEdgeScanDescription
      rightMoveOnceDescription).HaltsFromTape
      (scratchCountSuffixRestorerExtraBlankRewindTape
        pref suffix rightTail)
      (scratchCountSuffixExtraBlankRightGapTape
        pref suffix rightTail) := by
  let bits : Word Bool := List.append pref suffix
  let padding : List (Option Bool) :=
    scratchCountSuffixExtraBlankPadding suffix rightTail
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      rightEdgeScanDescription_subroutineReady
      rightMoveOnceDescription_subroutineReady
      (by
        simpa [scratchCountSuffixRestorerExtraBlankRewindTape,
          scratchCountSuffixExtraBlankPadding, bits, padding,
          rightEdgeScanSourceTapeFromLeft, rightEdgeRewindTargetTape]
          using rightEdgeScanDescription_haltsFromTape
            [none] bits padding)
      (by
        simpa [bits, padding] using
          rightEdgeScanTargetTapeFromLeft_move_left_move_right
            [none] bits padding)
      (by
        have htarget :
            Tape.move Direction.right
                (rightEdgeScanTargetTapeFromLeft [none] bits padding) =
              scratchCountSuffixExtraBlankRightGapTape
                pref suffix rightTail := by
          subst bits
          subst padding
          cases hbits : List.append pref suffix with
          | nil =>
              have hsuffix : suffix = [] := by
                cases pref <;> cases suffix <;>
                  simp at hbits ⊢
              simp [hsuffix] at hpos
          | cons bit rest =>
              have hleft :
                  (List.map some suffix).reverse ++
                      ((List.map some pref).reverse ++ [none]) =
                    (List.map some rest).reverse ++
                      [some bit, none] := by
                have h :=
                  congrArg
                    (fun bits : Word Bool =>
                      (bits.reverse.map some) ++ [none])
                    hbits
                simpa [List.reverse_append, List.map_append,
                  List.reverse_cons, List.append_assoc] using h
              cases hstack :
                  (List.map some rest).reverse ++
                    [some bit, none] with
              | nil =>
                  simp at hstack
              | cons cell stack =>
                  simp [scratchCountSuffixExtraBlankRightGapTape,
                    scratchCountSuffixExtraBlankPadding,
                    rightEdgeScanTargetTapeFromLeft,
                    rightEdgeRewindSourceTapeWithBase, tapeAtCells,
                    Tape.move, Tape.moveLeft, Tape.moveRight,
                    hleft, hstack, List.reverse_cons, List.map_append,
                    List.append_assoc]
        simpa [htarget] using
          rightMoveOnceDescription_haltsFromTape
            (rightEdgeScanTargetTapeFromLeft [none] bits padding))

theorem scratchCountSuffixExtraBlankRightGapScannerConstruction_core :
    ScratchCountSuffixExtraBlankRightGapScannerConstruction := by
  exact
    ⟨canonicalSeqDescription rightEdgeScanDescription
      rightMoveOnceDescription,
      canonicalSeqDescription_subroutineReady
        rightEdgeScanDescription_subroutineReady
        rightMoveOnceDescription_subroutineReady,
      fun pref suffix rightTail _hpos =>
        scratchCountSuffixExtraBlankRightGapScanner_haltsFrom
          pref suffix rightTail _hpos⟩

theorem scratchCountSuffixExtraBlankRestorerConstruction_of_rightGapParts
    (hscanner : ScratchCountSuffixExtraBlankRightGapScannerConstruction)
    (hrestorer : ScratchCountSuffixExtraBlankRightGapRestorerConstruction) :
    ScratchCountSuffixExtraBlankRestorerConstruction := by
  rcases hscanner with ⟨scanner, hscannerSpec⟩
  rcases hrestorer with ⟨restorer, hrestorerSpec⟩
  exact
    ⟨canonicalSeqDescription scanner restorer,
      by
        constructor
        · exact canonicalSeqDescription_subroutineReady
            hscannerSpec.left hrestorerSpec.left
        · intro pref suffix rightTail hpos
          exact
            canonicalSeqDescription_haltsFromTape_of_haltsFromTape
              hscannerSpec.left
              hrestorerSpec.left
              (hscannerSpec.right pref suffix rightTail hpos)
              (scratchCountSuffixExtraBlankRightGapTape_move_left_move_right
                pref suffix rightTail)
              (hrestorerSpec.right pref suffix rightTail hpos)⟩

theorem scratchCountSuffixCompactedRightEdgeRestorerConstruction_core :
    ScratchCountSuffixCompactedRightEdgeRestorerConstruction :=
  scratchCountSuffixCompactedRightEdgeRewinderConstruction_core

theorem scratchCountSuffixRightEdgeRestorerConstruction_core :
    ScratchCountSuffixRightEdgeRestorerConstruction :=
  scratchCountSuffixRightEdgeRestorerConstruction_of_localCompactorAndCompactedRestorer
    scratchCountSuffixRightEdgeLocalCompactorConstruction_core
    scratchCountSuffixCompactedRightEdgeRestorerConstruction_core

theorem selectedProjectionPaddedTailCleanupScratchCountWindowSuffixRestorerConstruction_core :
    ScratchCountSuffixRestorerConstruction :=
  scratchCountSuffixRestorerConstruction_of_rightEdgeScannerAndRestorer
    scratchCountSuffixRightEdgeScannerConstruction_core
    scratchCountSuffixRightEdgeRestorerConstruction_core

theorem selectedProjectionPaddedTailCleanupScratchCountWindowRawSourceEncoderConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRawSourceEncoderConstruction :=
  selectedProjectionPaddedTailCleanupScratchCountWindowRawSourceEncoderConstruction_countWindowRawSourceEncoderBridge

theorem selectedProjectionPaddedTailCleanupScratchCountWindowRestorerConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRestorerConstruction :=
  selectedProjectionPaddedTailCleanupScratchCountWindowRestorerConstruction_of_suffixRestorerAndRawSourceEncoder
    selectedProjectionPaddedTailCleanupScratchCountWindowSuffixRestorerConstruction_core
    selectedProjectionPaddedTailCleanupScratchCountWindowRawSourceEncoderConstruction_core

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
