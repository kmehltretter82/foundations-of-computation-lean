import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.GapPayloadLocalCompactor
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawSourceEncoder
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.PostPaddingScratchExtender.CountWindow
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.PostPaddingScratchExtender.CountWindowRawSourceEncoderBridge

set_option doc.verso true

/-!
# Post-padding scratch-count window constructions

This module packages the finite-machine construction leaves for the
scratch-count window materializer/restorer.  The tape shapes, specs, and
shared composition lemmas live in
{module}`FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.PostPaddingScratchExtender.CountWindow`;
the remaining executable construction leaves are kept here to keep that core
module below the large-file threshold.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncodedRewriters
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

theorem leadingBlankLeftShiftTargetTapeWithPadding_leftTwice_eq_rightEdgeRewindSourceWithPrefix
    (baseBits bits : Word Bool) (padding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.left
          (leadingBlankLeftShiftTargetTapeWithPadding
            (List.append (baseBits.reverse.map some) [none])
            bits padding)) =
      rightEdgeRewindSourceTapeWithBase
        ([] : List (Option Bool))
        (List.append baseBits bits)
        (none :: leadingBlankLeftShiftTargetVisiblePadding padding) := by
  cases bits <;> cases baseBits <;> cases padding <;>
    simp [leadingBlankLeftShiftTargetTapeWithPadding,
      rightEdgeRewindSourceTapeWithBase,
      leadingBlankLeftShiftTargetVisiblePadding, tapeAtCells,
      Tape.move, Tape.moveLeft, List.reverse_append,
      List.map_reverse, List.append_assoc]

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

theorem rightEdgeRewindTargetTapeWithBase_move_left_move_right_append_last
    (baseLeft : List (Option Bool)) (pref : Word Bool)
    (last : Bool) (padding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (rightEdgeRewindTargetTapeWithBase
            baseLeft (List.append pref [last]) padding)) =
      rightEdgeRewindTargetTapeWithBase
        baseLeft (List.append pref [last]) padding := by
  cases pref with
  | nil =>
      simpa using
        rightEdgeRewindTargetTapeWithBase_move_left_move_right_cons
          baseLeft last [] padding
  | cons first rest =>
      simpa using
        rightEdgeRewindTargetTapeWithBase_move_left_move_right_cons
          baseLeft first (List.append rest [last]) padding

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

-- This is the remaining finite-machine leaf: it must use the decoded scaffold
-- exposed by the rewound reject handoff to reconstruct the exact
-- `selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape`.
theorem rejectPostFieldDecodedPrefixRestorerConstruction_core :
    RejectPostFieldDecodedPrefixRestorerConstruction := by
  sorry

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

theorem rejectPostFieldHandoff_remainingGapsConstruction_core :
    RejectPostFieldRemainingGapsConstruction :=
  rejectPostFieldRemainingGapsConstruction_of_rewinderAndRestorer
    rejectPostFieldHandoffRightEdgeRewinderConstruction_core
    rejectPostFieldDecodedPrefixRestorerConstruction_core

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

def acceptPostFieldDecodedPrefixScanPadding
    (L : DovetailLayout) : List (Option Bool) :=
  none ::
    List.append
      (List.replicate
        (selectedProjectionPaddedTailCleanupScratchCountBits
          true L).length
        (none : Option Bool))
      (selectedProjectionPaddedTailCleanupPostCountTailCells
        true L 0)

-- Once the accept-side post-field payload has been rebuilt, the final
-- positioning step is just a right-edge scan across the restored
-- `ParsedLayoutBits`, followed by one right move onto the decoded-prefix gap.
def acceptPostFieldDecodedPrefixScanSourceTape
    (L : DovetailLayout) : Tape Bool :=
  rightEdgeScanSourceTapeFromLeft [none]
    (ParsedLayoutBits L)
    (acceptPostFieldDecodedPrefixScanPadding L)

def acceptPostFieldDecodedPrefixScanTargetTape
    (L : DovetailLayout) : Tape Bool :=
  rightEdgeScanTargetTapeFromLeft [none]
    (ParsedLayoutBits L)
    (acceptPostFieldDecodedPrefixScanPadding L)

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
      materializer.HaltsFromTape
        (acceptPostFieldHandoffAfterRightEdgeRewindTape
          L pref leftBit deletedTail)
        (acceptPostFieldDecodedPrefixScanSourceTape L)

def AcceptPostFieldRewoundToDecodedPrefixScanSourceConstruction :
    Prop :=
  exists materializer : MachineDescription,
    AcceptPostFieldRewoundToDecodedPrefixScanSourceSpec materializer

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

def acceptPostFieldDecodedPrefixScanToRewindDescription :
    MachineDescription :=
  canonicalSeqDescription rightEdgeScanDescription
    rightMoveOnceDescription

theorem acceptPostFieldDecodedPrefixScanToRewindDescription_subroutineReady :
    acceptPostFieldDecodedPrefixScanToRewindDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    rightEdgeScanDescription_subroutineReady
    rightMoveOnceDescription_subroutineReady

theorem rightEdgeScanSourceTapeFromLeft_move_left_move_right_padding_cons
    (left : List (Option Bool)) (bits : Word Bool)
    (pad : Option Bool) (padding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (rightEdgeScanSourceTapeFromLeft left bits (pad :: padding))) =
      rightEdgeScanSourceTapeFromLeft left bits (pad :: padding) := by
  cases bits with
  | nil =>
      cases left <;> cases pad <;> cases padding <;>
        simp [rightEdgeScanSourceTapeFromLeft, tapeAtCells,
          Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons current rest =>
      exact
        rightEdgeScanSourceTapeFromLeft_move_left_move_right_cons
          left (pad :: padding) current rest

theorem acceptPostFieldDecodedPrefixScanSourceTape_move_left_move_right
    (L : DovetailLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (acceptPostFieldDecodedPrefixScanSourceTape L)) =
      acceptPostFieldDecodedPrefixScanSourceTape L := by
  simpa [acceptPostFieldDecodedPrefixScanSourceTape,
    acceptPostFieldDecodedPrefixScanPadding] using
    rightEdgeScanSourceTapeFromLeft_move_left_move_right_padding_cons
      [none] (ParsedLayoutBits L) (none : Option Bool)
      (List.append
        (List.replicate
          (selectedProjectionPaddedTailCleanupScratchCountBits
            true L).length
          (none : Option Bool))
        (selectedProjectionPaddedTailCleanupPostCountTailCells
          true L 0))

theorem acceptPostFieldDecodedPrefixScanRightMove_equiv_rewindSource
    (L : DovetailLayout) :
    Tape.Equiv
      (Tape.move Direction.right
        (acceptPostFieldDecodedPrefixScanTargetTape L))
      (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape
        true L 0) := by
  rw [acceptPostFieldDecodedPrefixScanTargetTape]
  have hshape :
      Tape.move Direction.right
          (rightEdgeScanTargetTapeFromLeft [none]
            (ParsedLayoutBits L)
            (acceptPostFieldDecodedPrefixScanPadding L)) =
        tapeAtCells
          (List.append ((ParsedLayoutBits L).reverse.map some) [none])
          (none :: acceptPostFieldDecodedPrefixScanPadding L) := by
    unfold rightEdgeScanTargetTapeFromLeft
    cases hstack :
        List.append ((ParsedLayoutBits L).reverse.map some)
          ([none] : List (Option Bool)) with
    | nil =>
        have hlen := congrArg List.length hstack
        simp at hlen
    | cons cell stack =>
        cases acceptPostFieldDecodedPrefixScanPadding L <;>
          simp [tapeAtCells, Tape.move, Tape.moveLeft,
            Tape.moveRight]
  rw [hshape]
  simp [
    selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape,
    acceptPostFieldDecodedPrefixScanPadding, tapeAtCells, Tape.Equiv,
    FoC.Computability.dropTrailingNone_append_none]

theorem acceptPostFieldDecodedPrefixScanToRewind_haltsFrom
    (L : DovetailLayout) :
    acceptPostFieldDecodedPrefixScanToRewindDescription.HaltsFromTapeEquiv
      (acceptPostFieldDecodedPrefixScanSourceTape L)
      (selectedProjectionPaddedTailCleanupScratchCountDecodedPrefixRewindSourceTape
        true L 0) := by
  exact
    canonicalSeqDescription_haltsFromTapeEquiv_of_haltsFromTape
      rightEdgeScanDescription_subroutineReady
      rightMoveOnceDescription_subroutineReady
      (by
        simpa [acceptPostFieldDecodedPrefixScanSourceTape,
          acceptPostFieldDecodedPrefixScanTargetTape] using
          rightEdgeScanDescription_haltsFromTape
            [none] (ParsedLayoutBits L)
            (acceptPostFieldDecodedPrefixScanPadding L))
      (by
        simpa [acceptPostFieldDecodedPrefixScanTargetTape] using
          rightEdgeScanTargetTapeFromLeft_move_left_move_right
            [none] (ParsedLayoutBits L)
            (acceptPostFieldDecodedPrefixScanPadding L))
      (by
        refine
          ⟨Tape.move Direction.right
              (acceptPostFieldDecodedPrefixScanTargetTape L),
            ?_, ?_⟩
        · exact
            rightMoveOnceDescription_haltsFromTape
              (acceptPostFieldDecodedPrefixScanTargetTape L)
        · exact
            acceptPostFieldDecodedPrefixScanRightMove_equiv_rewindSource
              L)

theorem acceptPostFieldDecodedPrefixScanToRewindConstruction_core :
    AcceptPostFieldDecodedPrefixScanToRewindConstruction := by
  exact
    ⟨acceptPostFieldDecodedPrefixScanToRewindDescription,
      acceptPostFieldDecodedPrefixScanToRewindDescription_subroutineReady,
      fun L =>
        acceptPostFieldDecodedPrefixScanToRewind_haltsFrom L⟩

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

-- This is the accept-side finite-machine leaf that still needs a concrete
-- implementation: it rebuilds the full parsed-layout scan source from the
-- post-field right-edge boundary.
theorem acceptPostFieldRewoundToDecodedPrefixScanSourceConstruction_core :
    AcceptPostFieldRewoundToDecodedPrefixScanSourceConstruction := by
  sorry

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
            canonicalSeqDescription_haltsFromTapeEquiv_of_haltsFromTape
              hmaterializerSpec.left
              hscannerSpec.left
              (hmaterializerSpec.right
                L pref leftBit deletedTail hdeleted hpayload)
              (acceptPostFieldDecodedPrefixScanSourceTape_move_left_move_right
                L)
              (hscannerSpec.right L)⟩

theorem acceptPostFieldRewoundToDecodedPrefixConstruction_core :
    AcceptPostFieldRewoundToDecodedPrefixConstruction :=
  acceptPostFieldRewoundToDecodedPrefixConstruction_of_scanSource
    acceptPostFieldRewoundToDecodedPrefixScanSourceConstruction_core
    acceptPostFieldDecodedPrefixScanToRewindConstruction_core

theorem acceptPostFieldRepositionToDecodedPrefixConstruction_core :
    AcceptPostFieldRepositionToDecodedPrefixConstruction :=
  acceptPostFieldRepositionToDecodedPrefixConstruction_of_rewinderAndRestorer
    acceptPostFieldRepositionRightEdgeRewinderConstruction_core
    acceptPostFieldRewoundToDecodedPrefixConstruction_core

theorem acceptPostFieldBoundaryToDecodedPrefixConstruction_core :
    AcceptPostFieldBoundaryToDecodedPrefixConstruction :=
  acceptPostFieldBoundaryToDecodedPrefixConstruction_of_reposition
    acceptPostFieldRepositionToDecodedPrefixConstruction_core

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

theorem selectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixPostFieldHandoffCoreConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixPostFieldHandoffCoreConstruction := by
  rcases acceptPostFieldBoundaryToDecodedPrefixConstruction_core with
    ⟨normalizer, hnormalizer⟩
  exact
    ⟨SeqViaCanonical
        acceptPostFieldHandoffBoundaryCleanupDescription normalizer,
      SeqViaCanonical_subroutineReady
        acceptPostFieldHandoffBoundaryCleanupDescription_subroutineReady
        hnormalizer.left,
      acceptPostFieldHandoff_haltsFrom_of_boundaryToDecoded
        hnormalizer⟩

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

theorem selectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixPostFieldHandoffCoreConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixPostFieldHandoffCoreConstruction :=
  selectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixPostFieldHandoffCoreConstruction_of_remainingGaps
    rejectPostFieldHandoff_remainingGapsConstruction_core

theorem selectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixPostFieldNormalizerConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixPostFieldNormalizerConstruction :=
  selectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixPostFieldNormalizerConstruction_of_handoffCore
    selectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixPostFieldHandoffCoreConstruction_core

theorem selectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixPostFieldNormalizerConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixPostFieldNormalizerConstruction :=
  selectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixPostFieldNormalizerConstruction_of_handoffCore
    selectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixPostFieldHandoffCoreConstruction_core

theorem selectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixTailNormalizerConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixTailNormalizerConstruction :=
  selectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixTailNormalizerConstruction_of_firstFieldAndPostField
    selectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixFirstFieldEraserConstruction_core
    selectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixPostFieldNormalizerConstruction_core

theorem selectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixTailNormalizerConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixTailNormalizerConstruction :=
  selectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixTailNormalizerConstruction_of_firstFieldAndPostField
    selectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixFirstFieldEraserConstruction_core
    selectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixPostFieldNormalizerConstruction_core

theorem selectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixTailNormalizerConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixTailNormalizerConstruction :=
  selectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixTailNormalizerConstruction_of_branches
    selectedProjectionPaddedTailCleanupScratchCountWindowAcceptDecodedPrefixTailNormalizerConstruction_core
    selectedProjectionPaddedTailCleanupScratchCountWindowRejectDecodedPrefixTailNormalizerConstruction_core

theorem selectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixNormalizerConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixNormalizerConstruction :=
  selectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixNormalizerConstruction_of_stageScannerAndTailNormalizer
    selectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixStageScannerConstruction_core
    selectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixTailNormalizerConstruction_core

theorem selectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixRewinderConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixRewinderConstruction := by
  intro useAccept
  exact
    ⟨sourceRewindDescription,
      sourceRewindDescription_subroutineReady,
      fun L =>
        sourceRewindDescription_haltsFrom_scratchCountDecodedPrefixRewindSourceTape
          useAccept L 0⟩

theorem selectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixRestorerConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixRestorerConstruction :=
  selectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixRestorerConstruction_of_normalizerAndRewinder
    selectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixNormalizerConstruction_core
    selectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixRewinderConstruction_core

theorem selectedProjectionPaddedTailCleanupScratchCountWindowDecoderConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowDecoderConstruction :=
  selectedProjectionPaddedTailCleanupScratchCountWindowDecoderConstruction_of_prefixScannerAndDecodedRestorer
    selectedProjectionPaddedTailCleanupScratchCountWindowPrefixScannerConstruction_core
    selectedProjectionPaddedTailCleanupScratchCountWindowDecodedPrefixRestorerConstruction_core

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

theorem selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerOpenConstructions_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerOpenConstructions :=
  ⟨acceptPostFieldBoundaryToDecodedPrefixConstruction_core,
    rejectPostFieldHandoff_remainingGapsConstruction_core⟩

theorem selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction :=
  selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction_of_openConstructions
    selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerOpenConstructions_core

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

theorem selectedProjectionPaddedTailCleanupPostCountTailCells_zero_append_replicate
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    List.append
        (selectedProjectionPaddedTailCleanupPostCountTailCells
          useAccept L 0)
        (List.replicate extraScratch (none : Option Bool)) =
      selectedProjectionPaddedTailCleanupPostCountTailCells
        useAccept L extraScratch := by
  cases useAccept <;>
    simp [selectedProjectionPaddedTailCleanupPostCountTailCells,
      selectedProjectionPaddedTailCleanupAcceptPostCountTailCells,
      selectedProjectionPaddedTailCleanupRejectPostCountTailCells,
      selectedProjectionPaddedTailCleanupAcceptAfterStageTailCells,
      selectedProjectionPaddedTailCleanupRejectAfterStageTailCells,
      List.append_assoc]

theorem selectedProjectionPaddedTailCleanupScratchCountWindowRawSourceEncoderConstruction_of_countWindowRawSourceEncoder
    (hencoder : CountWindowRawSourceEncoderEquivConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRawSourceEncoderConstruction := by
  rcases hencoder with ⟨encoder, hencoderSpec⟩
  intro useAccept
  exact
    ⟨encoder,
      hencoderSpec.left,
      fun L => by
        have hsplit :
            ParsedLayoutBits L =
              List.append
                (selectedProjectionPaddedTailCleanupScratchSkippedBits
                  useAccept L)
                (selectedProjectionPaddedTailCleanupScratchCountBits
                  useAccept L) :=
          selectedProjectionPaddedTailCleanupParsedLayoutBits_eq_skipped_append_count
            useAccept L
        rcases
            selectedProjectionPaddedTailCleanupPostCountTailCells_cons_false
              useAccept L 0 with
          ⟨postCountTail, hpostCountTail⟩
        have htail :
            List.append
                (some false :: postCountTail)
                (List.replicate
                  (selectedProjectionPaddedTailCleanupScratchCountBits
                    useAccept L).length
                  (none : Option Bool)) =
              selectedProjectionPaddedTailCleanupPostCountTailCells
                useAccept L
                (selectedProjectionPaddedTailCleanupScratchCountBits
                  useAccept L).length := by
          rw [← hpostCountTail]
          exact
            selectedProjectionPaddedTailCleanupPostCountTailCells_zero_append_replicate
              useAccept L
              (selectedProjectionPaddedTailCleanupScratchCountBits
                useAccept L).length
        have hrun :=
          hencoderSpec.right
            (selectedProjectionPaddedTailCleanupScratchSkippedBits
              useAccept L)
            (selectedProjectionPaddedTailCleanupScratchCountBits
              useAccept L)
            false
            postCountTail
        have hsource :
            countWindowRawSourceEncoderSourceTape
                (selectedProjectionPaddedTailCleanupScratchSkippedBits
                  useAccept L)
                (selectedProjectionPaddedTailCleanupScratchCountBits
                  useAccept L)
                (some false :: postCountTail) =
              selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithExtraCountBlank
                useAccept L 0 := by
          simp [selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithExtraCountBlank,
            countWindowRawSourceEncoderSourceTape,
            hsplit, hpostCountTail, List.map_append, List.append_assoc]
        have htarget :
            countWindowRawSourceEncoderTargetTape
                (selectedProjectionPaddedTailCleanupScratchSkippedBits
                  useAccept L)
                (selectedProjectionPaddedTailCleanupScratchCountBits
                  useAccept L)
                (some false :: postCountTail) =
              selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
                useAccept L
                (selectedProjectionPaddedTailCleanupScratchCountBits
                  useAccept L).length := by
          unfold countWindowRawSourceEncoderTargetTape
          rw [htail]
          cases useAccept <;>
            simp [
              selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch_countSplit,
              selectedProjectionPaddedTailCleanupEncodedCountWindowSourceCells,
              selectedProjectionPaddedTailCleanupEncodedHeaderCells,
              selectedProjectionPaddedTailCleanupEncodedLayoutLengthCells,
              selectedProjectionPaddedTailCleanupEncodedScratchSkippedCells,
              selectedProjectionPaddedTailCleanupEncodedScratchCountCells,
              selectedProjectionPaddedTailCleanupPostCountTailCells,
              selectedProjectionPaddedTailCleanupAcceptPostCountTailCells,
              selectedProjectionPaddedTailCleanupRejectPostCountTailCells,
              selectedProjectionPaddedTailCleanupAcceptAfterStageTailCells,
              selectedProjectionPaddedTailCleanupRejectAfterStageTailCells,
              countWindowRawSourceEncoderHeaderCells,
              countWindowRawSourceEncoderLayoutLengthCells,
              countWindowRawSourceEncoderCellFieldCells,
              hsplit]
        rw [← hsource, ← htarget]
        exact hrun⟩

theorem selectedProjectionPaddedTailCleanupScratchCountWindowAcceptRawSourceEncoderConstruction_core :
    exists encoder : MachineDescription,
      SelectedProjectionPaddedTailCleanupScratchCountWindowRawSourceEncoderSpec
        true encoder :=
  selectedProjectionPaddedTailCleanupScratchCountWindowRawSourceEncoderConstruction_countWindowRawSourceEncoderBridge
    true

theorem selectedProjectionPaddedTailCleanupScratchCountWindowRejectRawSourceEncoderConstruction_core :
    exists encoder : MachineDescription,
      SelectedProjectionPaddedTailCleanupScratchCountWindowRawSourceEncoderSpec
        false encoder :=
  selectedProjectionPaddedTailCleanupScratchCountWindowRawSourceEncoderConstruction_countWindowRawSourceEncoderBridge
    false

theorem selectedProjectionPaddedTailCleanupScratchCountWindowRawSourceEncoderConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRawSourceEncoderConstruction := by
  intro useAccept
  cases useAccept
  · exact
      selectedProjectionPaddedTailCleanupScratchCountWindowRejectRawSourceEncoderConstruction_core
  · exact
      selectedProjectionPaddedTailCleanupScratchCountWindowAcceptRawSourceEncoderConstruction_core

theorem selectedProjectionPaddedTailCleanupScratchCountWindowRestorerConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRestorerConstruction :=
  selectedProjectionPaddedTailCleanupScratchCountWindowRestorerConstruction_of_suffixRestorerAndRawSourceEncoder
    selectedProjectionPaddedTailCleanupScratchCountWindowSuffixRestorerConstruction_core
    selectedProjectionPaddedTailCleanupScratchCountWindowRawSourceEncoderConstruction_core

theorem selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction_core :
    SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction :=
  selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction_of_parts
    selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerConstruction_core
    selectedProjectionPaddedTailCleanupScratchCountWindowRestorerConstruction_core

/--
Finite-machine leaf that exposes the selected branch scratch-count window and
uses it to append the branch-specific scratch padding.
-/
theorem selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction := by
  exact
    selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction_of_countWindowMaterializers
      selectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction_core

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchExtenderConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchExtenderConstruction :=
  selectedProjectionPaddedTailCleanupPostPaddingScratchExtenderConstruction_of_countExtenders
    selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction :=
  selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction_of_extenders
    selectedProjectionPaddedTailCleanupPostPaddingScratchExtenderConstruction

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
