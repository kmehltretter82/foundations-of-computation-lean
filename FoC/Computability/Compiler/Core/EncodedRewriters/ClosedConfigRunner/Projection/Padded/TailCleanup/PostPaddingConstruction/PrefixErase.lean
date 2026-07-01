import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.PostPaddingConstruction.Core

set_option doc.verso true

/-!
# Post-padding output-prefix erasure

This module contains the output-prefix scanner handoff lemmas and the accept
prefix eraser used before the final closeout composition.  It imports the
post-padding construction core for the sentinel and compaction bridge facts.
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

theorem postPaddingOutputPrefixStageScannerDescription_rejectSourceBits_handoff_withRight
    (L : DovetailLayout) (rightPadding : List (Option Bool)) :
    exists fieldTail : Word Bool,
      postPaddingOutputPrefixStageScannerDescription.HaltsFromTape
        (tapeAtCells [none]
          (List.append
            ((selectedProjectionPaddedTailCleanupPostPaddingSourceBits
              false L).map some)
            rightPadding))
        (postPaddingOutputPrefixStageScannerTargetTapeWithRight
          (ParsedLayoutBits L) L.stage [none] fieldTail rightPadding) ∧
      Tape.move Direction.right
          (postPaddingOutputPrefixStageScannerTargetTapeWithRight
            (ParsedLayoutBits L) L.stage [none] fieldTail rightPadding) =
        tapeAtCells
          (List.append
            ((selectedProjectionPaddedTailCleanupPrefixBits L).reverse.map
              some)
            [none])
          (List.append
            ((configurationFieldBits L.acceptConfig
              (configurationFieldBits L.rejectConfig
                (boolFieldBits L.rejectHit []))).map some)
            rightPadding) := by
  rcases
      configurationFieldBits_cons_false
        L.acceptConfig
        (configurationFieldBits L.rejectConfig
          (boolFieldBits L.rejectHit [])) with
    ⟨fieldTail, hfieldTail⟩
  refine ⟨fieldTail, ?_, ?_⟩
  · rw [selectedProjectionPaddedTailCleanupPostPaddingSourceBits_false]
    rw [selectedProjectionPaddedTailCleanupPrefixBits]
    rw [SelectedProjectionTailProjector.outputPrefixBits]
    rw [
      configurationFieldBits_append_nil
        L.rejectConfig (boolFieldBits L.rejectHit [])]
    rw [
      configurationFieldBits_append_nil
        L.acceptConfig
        (configurationFieldBits L.rejectConfig
          (boolFieldBits L.rejectHit []))]
    rw [hfieldTail]
    simpa [List.map_append, List.append_assoc] using
      postPaddingOutputPrefixStageScannerDescription_haltsFrom_raw_withRight
        (ParsedLayoutBits L) L.stage [none] fieldTail rightPadding
  · have hmove :=
      postPaddingOutputPrefixStageScannerTarget_move_right_eq_configSource_withRight
        (ParsedLayoutBits L) L.stage [none] fieldTail rightPadding
    rw [postPaddingOutputPrefixAfterStageBase_eq_prefixBits_reverse] at hmove
    rw [hmove, ← hfieldTail]
    simp [DovetailInitialLayoutInitializer.tapeAtCells, tapeAtCells,
      List.map_reverse]
    rfl

theorem postPaddingAcceptConfigRestoredBase_eq_keptPrefix_reverse
    (L : DovetailLayout) :
    configurationRestoredLeftWithBase L.acceptConfig
        (postPaddingOutputPrefixAfterStageBase
          (ParsedLayoutBits L) L.stage [none]) =
      List.append
        ((selectedProjectionPaddedTailCleanupKeptPrefixBits true L).reverse.map
          some)
        [none] := by
  rw [configurationRestoredLeftWithBase_eq_fieldBits_reverse_append]
  rw [postPaddingOutputPrefixAfterStageBase_eq_prefixBits_reverse]
  simp [selectedProjectionPaddedTailCleanupKeptPrefixBits,
    selectedProjectionPaddedTailCleanupSelectedConfigBits,
    List.reverse_append, List.map_append, List.append_assoc]

theorem postPaddingOutputPrefixStageConfigScannerDescription_haltsFrom_acceptSourceBits
    (L : DovetailLayout) :
    exists suffixTail : Word Bool,
      postPaddingOutputPrefixStageConfigScannerDescription.HaltsFromTape
        (tapeAtCells [none]
          ((selectedProjectionPaddedTailCleanupPostPaddingSourceBits
            true L).map some))
        (postPaddingOutputPrefixStageConfigScannerTargetTape
          (ParsedLayoutBits L) L.stage L.acceptConfig [none] suffixTail) := by
  rcases
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_cons_false
        L.rejectConfig
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.acceptHit []) with
    ⟨suffixTail, hsuffix⟩
  refine ⟨suffixTail, ?_⟩
  rw [selectedProjectionPaddedTailCleanupPostPaddingSourceBits_true]
  rw [selectedProjectionPaddedTailCleanupPrefixBits]
  rw [SelectedProjectionTailProjector.outputPrefixBits]
  rw [
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
      L.rejectConfig
      (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
        L.acceptHit [])]
  rw [hsuffix]
  rw [
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
      L.acceptConfig (false :: suffixTail)]
  simpa [List.map_append, List.append_assoc] using
    postPaddingOutputPrefixStageConfigScannerDescription_haltsFrom_raw
      (ParsedLayoutBits L) L.stage L.acceptConfig [none] suffixTail

theorem postPaddingOutputPrefixStageConfigScannerTarget_accept_move_right_eq_unselectedSource
    (L : DovetailLayout) :
    exists suffixTail : Word Bool,
      Tape.move Direction.right
          (postPaddingOutputPrefixStageConfigScannerTargetTape
            (ParsedLayoutBits L) L.stage L.acceptConfig [none]
            suffixTail) =
        tapeAtCells
          (configurationRestoredLeftWithBase L.acceptConfig
            (postPaddingOutputPrefixAfterStageBase
              (ParsedLayoutBits L) L.stage [none]))
          ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.rejectConfig
            (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
              L.acceptHit [])).map some) := by
  rcases
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_cons_false
        L.rejectConfig
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.acceptHit []) with
    ⟨suffixTail, hsuffix⟩
  refine ⟨suffixTail, ?_⟩
  rw [hsuffix]
  exact
    postPaddingOutputPrefixStageConfigScannerTarget_move_right_eq_suffixSource
      (ParsedLayoutBits L) L.stage L.acceptConfig [none] suffixTail

theorem postPaddingOutputPrefixStageConfigScannerDescription_acceptSourceBits_handoff
    (L : DovetailLayout) :
    exists suffixTail : Word Bool,
      postPaddingOutputPrefixStageConfigScannerDescription.HaltsFromTape
        (tapeAtCells [none]
          ((selectedProjectionPaddedTailCleanupPostPaddingSourceBits
            true L).map some))
        (postPaddingOutputPrefixStageConfigScannerTargetTape
          (ParsedLayoutBits L) L.stage L.acceptConfig [none] suffixTail) ∧
      Tape.move Direction.right
          (postPaddingOutputPrefixStageConfigScannerTargetTape
            (ParsedLayoutBits L) L.stage L.acceptConfig [none]
            suffixTail) =
        tapeAtCells
          (List.append
            ((selectedProjectionPaddedTailCleanupKeptPrefixBits
              true L).reverse.map some)
            [none])
          ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.rejectConfig
            (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
              L.acceptHit [])).map some) := by
  rcases
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_cons_false
        L.rejectConfig
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.acceptHit []) with
    ⟨suffixTail, hsuffix⟩
  refine ⟨suffixTail, ?_, ?_⟩
  · rw [selectedProjectionPaddedTailCleanupPostPaddingSourceBits_true]
    rw [selectedProjectionPaddedTailCleanupPrefixBits]
    rw [SelectedProjectionTailProjector.outputPrefixBits]
    rw [
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
        L.rejectConfig
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.acceptHit [])]
    rw [hsuffix]
    rw [
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
        L.acceptConfig (false :: suffixTail)]
    simpa [List.map_append, List.append_assoc] using
      postPaddingOutputPrefixStageConfigScannerDescription_haltsFrom_raw
        (ParsedLayoutBits L) L.stage L.acceptConfig [none] suffixTail
  · rw [hsuffix]
    have hmove :=
      postPaddingOutputPrefixStageConfigScannerTarget_move_right_eq_suffixSource
        (ParsedLayoutBits L) L.stage L.acceptConfig [none] suffixTail
    rw [postPaddingAcceptConfigRestoredBase_eq_keptPrefix_reverse] at hmove
    exact hmove

theorem postPaddingOutputPrefixStageConfigScannerDescription_acceptSourceBits_handoff_splitKeptPrefix
    (L : DovetailLayout) :
    exists scannerTail : Word Bool,
    exists hitTail : Word Bool,
    exists pref : Word Bool,
    exists leftBit : Bool,
      selectedProjectionPaddedTailCleanupKeptPrefixBits true L =
          List.append pref [leftBit] ∧
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.acceptHit [] =
        false :: hitTail ∧
      postPaddingOutputPrefixStageConfigScannerDescription.HaltsFromTape
        (tapeAtCells [none]
          ((selectedProjectionPaddedTailCleanupPostPaddingSourceBits
            true L).map some))
        (postPaddingOutputPrefixStageConfigScannerTargetTape
          (ParsedLayoutBits L) L.stage L.acceptConfig [none]
          scannerTail) ∧
      Tape.move Direction.right
          (postPaddingOutputPrefixStageConfigScannerTargetTape
            (ParsedLayoutBits L) L.stage L.acceptConfig [none]
            scannerTail) =
        tapeAtCells
          (some leftBit ::
            List.append (pref.reverse.map some) [none])
          ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.rejectConfig (false :: hitTail)).map some) := by
  rcases selectedProjectionPaddedTailCleanupKeptPrefix_true_append_last
      L with
    ⟨pref, leftBit, hpref⟩
  rcases
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits_cons_false
        (some L.acceptHit) [] with
    ⟨hitTail, hhitTail⟩
  rcases
      postPaddingOutputPrefixStageConfigScannerDescription_acceptSourceBits_handoff
        L with
    ⟨scannerTail, hscan, hmove⟩
  refine ⟨scannerTail, hitTail, pref, leftBit, hpref, ?_, hscan, ?_⟩
  · simpa [CanonicalLayouts.DovetailLayoutScanner.boolFieldBits] using
      hhitTail
  · rw [hmove, hpref]
    have hhit :
        CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            L.acceptHit [] =
          false :: hitTail := by
      simpa [CanonicalLayouts.DovetailLayoutScanner.boolFieldBits] using
        hhitTail
    rw [hhit]
    simp [List.reverse_append]

theorem postPaddingOutputPrefixStageConfigScannerDescription_acceptSourceBits_handoff_splitKeptPrefix_withRight
    (L : DovetailLayout) (rightPadding : List (Option Bool)) :
    exists scannerTail : Word Bool,
    exists hitTail : Word Bool,
    exists pref : Word Bool,
    exists leftBit : Bool,
      selectedProjectionPaddedTailCleanupKeptPrefixBits true L =
          List.append pref [leftBit] ∧
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.acceptHit [] =
        false :: hitTail ∧
      postPaddingOutputPrefixStageConfigScannerDescription.HaltsFromTape
        (tapeAtCells [none]
          (List.append
            ((selectedProjectionPaddedTailCleanupPostPaddingSourceBits
              true L).map some)
            rightPadding))
        (postPaddingOutputPrefixStageConfigScannerTargetTapeWithRight
          (ParsedLayoutBits L) L.stage L.acceptConfig [none]
          scannerTail rightPadding) ∧
      Tape.move Direction.right
          (postPaddingOutputPrefixStageConfigScannerTargetTapeWithRight
            (ParsedLayoutBits L) L.stage L.acceptConfig [none]
            scannerTail rightPadding) =
        tapeAtCells
          (some leftBit ::
            List.append (pref.reverse.map some) [none])
          (List.append
            ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.rejectConfig (false :: hitTail)).map some)
            rightPadding) := by
  rcases selectedProjectionPaddedTailCleanupKeptPrefix_true_append_last
      L with
    ⟨pref, leftBit, hpref⟩
  rcases
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits_cons_false
        (some L.acceptHit) [] with
    ⟨hitTail, hhitTail⟩
  rcases
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_cons_false
        L.rejectConfig
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.acceptHit []) with
    ⟨scannerTail, hscannerTail⟩
  refine ⟨scannerTail, hitTail, pref, leftBit, hpref, ?_, ?_, ?_⟩
  · simpa [CanonicalLayouts.DovetailLayoutScanner.boolFieldBits] using
      hhitTail
  · rw [selectedProjectionPaddedTailCleanupPostPaddingSourceBits_true]
    rw [selectedProjectionPaddedTailCleanupPrefixBits]
    rw [SelectedProjectionTailProjector.outputPrefixBits]
    rw [
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
        L.rejectConfig
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.acceptHit [])]
    rw [hscannerTail]
    rw [
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
        L.acceptConfig (false :: scannerTail)]
    simpa [List.map_append, List.append_assoc] using
      postPaddingOutputPrefixStageConfigScannerDescription_haltsFrom_raw_withRight
        (ParsedLayoutBits L) L.stage L.acceptConfig [none]
        scannerTail rightPadding
  · have hmove :=
      postPaddingOutputPrefixStageConfigScannerTarget_move_right_eq_suffixSource_withRight
        (ParsedLayoutBits L) L.stage L.acceptConfig [none]
        scannerTail rightPadding
    rw [postPaddingAcceptConfigRestoredBase_eq_keptPrefix_reverse] at hmove
    rw [hmove, hpref]
    have hhit :
        CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            L.acceptHit [] =
          false :: hitTail := by
      simpa [CanonicalLayouts.DovetailLayoutScanner.boolFieldBits] using
        hhitTail
    rw [← hscannerTail]
    rw [hhit]
    simp [DovetailInitialLayoutInitializer.tapeAtCells, tapeAtCells,
      List.reverse_append]
    rfl

def selectedProjectionPaddedTailCleanupAcceptPrefixEraseDescription :
    MachineDescription :=
  seqSubroutine postPaddingOutputPrefixStageConfigScannerDescription
    leftBoundaryBitConfigurationFieldEraseAndPayloadScanDescription
    Direction.right

theorem selectedProjectionPaddedTailCleanupAcceptPrefixEraseDescription_subroutineReady :
    selectedProjectionPaddedTailCleanupAcceptPrefixEraseDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    postPaddingOutputPrefixStageConfigScannerDescription_subroutineReady
    leftBoundaryBitConfigurationFieldEraseAndPayloadScanDescription_subroutineReady

theorem selectedProjectionPaddedTailCleanupAcceptPrefixEraseDescription_haltsFrom_sourceWithRight
    (L : DovetailLayout) (padding : List (Option Bool)) :
    exists hitTail : Word Bool,
    exists pref : Word Bool,
    exists leftBit : Bool,
      selectedProjectionPaddedTailCleanupKeptPrefixBits true L =
          List.append pref [leftBit] ∧
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.acceptHit [] =
        false :: hitTail ∧
      selectedProjectionPaddedTailCleanupAcceptPrefixEraseDescription.HaltsFromTape
        (tapeAtCells [none]
          (List.append
            ((selectedProjectionPaddedTailCleanupPostPaddingSourceBits
              true L).map some)
            (none :: padding)))
        (rightBlankGapPayloadScanTargetTape
          (some leftBit :: List.append (pref.reverse.map some) [none])
          (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.rejectConfig []).length
          false hitTail padding) := by
  rcases
      postPaddingOutputPrefixStageConfigScannerDescription_acceptSourceBits_handoff_splitKeptPrefix_withRight
        L (none :: padding) with
    ⟨scannerTail, hitTail, pref, leftBit, hpref, hhit,
      hscan, hmove⟩
  refine ⟨hitTail, pref, leftBit, hpref, hhit, ?_⟩
  exact
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      postPaddingOutputPrefixStageConfigScannerDescription_subroutineReady
      leftBoundaryBitConfigurationFieldEraseAndPayloadScanDescription_subroutineReady
      hscan
      (by
        simpa [List.append_assoc] using hmove)
      (leftBoundaryBitConfigurationFieldEraseAndPayloadScanDescription_haltsFromTape
        leftBit L.rejectConfig
        (List.append (pref.reverse.map some) [none])
        hitTail padding)

def selectedProjectionPaddedTailCleanupAcceptEraseToRightEndDescription :
    MachineDescription :=
  seqSubroutine
    selectedProjectionPaddedTailCleanupAcceptPrefixEraseDescription
    rightMoveAcrossFiveBlanksDescription
    Direction.right

theorem selectedProjectionPaddedTailCleanupAcceptEraseToRightEndDescription_subroutineReady :
    selectedProjectionPaddedTailCleanupAcceptEraseToRightEndDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    selectedProjectionPaddedTailCleanupAcceptPrefixEraseDescription_subroutineReady
    rightMoveAcrossFiveBlanksDescription_subroutineReady

theorem selectedProjectionPaddedTailCleanupAcceptEraseToRightEndDescription_haltsFrom_sourceWithRight
    (L : DovetailLayout) (rightPadding : List (Option Bool)) :
    selectedProjectionPaddedTailCleanupAcceptEraseToRightEndDescription.HaltsFromTape
      (tapeAtCells [none]
        (List.append
          ((selectedProjectionPaddedTailCleanupPostPaddingSourceBits
            true L).map some)
          (none ::
            List.append (List.replicate 5 (none : Option Bool))
              rightPadding)))
      (rightEndCompactionSourceTapeWithRightPadding
        (selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells L)
        rightPadding) := by
  rcases
      selectedProjectionPaddedTailCleanupAcceptPrefixEraseDescription_haltsFrom_sourceWithRight
        L
        (List.append (List.replicate 5 (none : Option Bool))
          rightPadding) with
    ⟨hitTail, pref, leftBit, hpref, hhit, herase⟩
  let leftCells : List (Option Bool) :=
    List.append
      (some leftBit ::
        List.append (pref.reverse.map some) [none]).reverse
      (List.append
        (List.replicate
          (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.rejectConfig []).length
          (none : Option Bool))
        ((false :: hitTail).map some))
  have hleft :
      List.append leftCells
          (List.replicate 5 (none : Option Bool)) =
        selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells
          L := by
    have hprefMap :
        List.append
            ((selectedProjectionPaddedTailCleanupPrefixBits L).map some)
            ((selectedProjectionPaddedTailCleanupSelectedConfigBits
              true L).map some) =
          List.append (pref.map some) [some leftBit] := by
      have hmap := congrArg (List.map some) hpref
      simpa [selectedProjectionPaddedTailCleanupKeptPrefixBits,
        List.map_append] using hmap
    simp [leftCells,
      selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells,
      selectedProjectionPaddedTailCleanupUnselectedConfigBits,
      selectedProjectionPaddedTailCleanupSelectedHitBits,
      hhit, List.map_append, List.append_assoc]
    simpa [List.append_assoc] using
      congrArg
        (fun xs =>
          List.append xs
            (List.append
              (List.replicate
                (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                  L.rejectConfig []).length
                (none : Option Bool))
              (some false ::
                (List.map some hitTail ++
                  [none, none, none, none, none]))))
        hprefMap.symm
  exact
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      selectedProjectionPaddedTailCleanupAcceptPrefixEraseDescription_subroutineReady
      rightMoveAcrossFiveBlanksDescription_subroutineReady
      herase
      (by
        simpa [leftCells] using
          rightBlankGapPayloadScanTargetTape_move_right_eq_rightEndCompactionSourceTapeWithRightPadding
            (some leftBit ::
              List.append (pref.reverse.map some) [none])
            (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.rejectConfig []).length
            false hitTail
            (List.append (List.replicate 5 (none : Option Bool))
              rightPadding))
      (by
        rw [← hleft]
        simpa [leftCells, List.append_assoc] using
          rightMoveAcrossFiveBlanksDescription_haltsFrom_rightPaddingWithTail
            leftCells rightPadding)

theorem postPaddingOutputPrefixStageConfigScannerDescription_haltsFrom_rejectSourceBits
    (L : DovetailLayout) :
    exists suffixTail : Word Bool,
      postPaddingOutputPrefixStageConfigScannerDescription.HaltsFromTape
        (tapeAtCells [none]
          ((selectedProjectionPaddedTailCleanupPostPaddingSourceBits
            false L).map some))
        (postPaddingOutputPrefixStageConfigScannerTargetTape
          (ParsedLayoutBits L) L.stage L.acceptConfig [none] suffixTail) := by
  rcases
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_cons_false
        L.rejectConfig
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.rejectHit []) with
    ⟨suffixTail, hsuffix⟩
  refine ⟨suffixTail, ?_⟩
  rw [selectedProjectionPaddedTailCleanupPostPaddingSourceBits_false]
  rw [selectedProjectionPaddedTailCleanupPrefixBits]
  rw [SelectedProjectionTailProjector.outputPrefixBits]
  rw [
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
      L.rejectConfig
      (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
        L.rejectHit [])]
  rw [hsuffix]
  rw [
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
      L.acceptConfig (false :: suffixTail)]
  simpa [List.map_append, List.append_assoc] using
    postPaddingOutputPrefixStageConfigScannerDescription_haltsFrom_raw
      (ParsedLayoutBits L) L.stage L.acceptConfig [none] suffixTail

theorem postPaddingOutputPrefixStageConfigScannerTarget_reject_move_right_eq_selectedSource
    (L : DovetailLayout) :
    exists suffixTail : Word Bool,
      Tape.move Direction.right
          (postPaddingOutputPrefixStageConfigScannerTargetTape
            (ParsedLayoutBits L) L.stage L.acceptConfig [none]
            suffixTail) =
        tapeAtCells
          (configurationRestoredLeftWithBase L.acceptConfig
            (postPaddingOutputPrefixAfterStageBase
              (ParsedLayoutBits L) L.stage [none]))
          ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.rejectConfig
            (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
              L.rejectHit [])).map some) := by
  rcases
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_cons_false
        L.rejectConfig
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.rejectHit []) with
    ⟨suffixTail, hsuffix⟩
  refine ⟨suffixTail, ?_⟩
  rw [hsuffix]
  exact
    postPaddingOutputPrefixStageConfigScannerTarget_move_right_eq_suffixSource
      (ParsedLayoutBits L) L.stage L.acceptConfig [none] suffixTail

theorem postPaddingOutputPrefixStageConfigScannerDescription_rejectSourceBits_handoff
    (L : DovetailLayout) :
    exists suffixTail : Word Bool,
      postPaddingOutputPrefixStageConfigScannerDescription.HaltsFromTape
        (tapeAtCells [none]
          ((selectedProjectionPaddedTailCleanupPostPaddingSourceBits
            false L).map some))
        (postPaddingOutputPrefixStageConfigScannerTargetTape
          (ParsedLayoutBits L) L.stage L.acceptConfig [none] suffixTail) ∧
      Tape.move Direction.right
          (postPaddingOutputPrefixStageConfigScannerTargetTape
            (ParsedLayoutBits L) L.stage L.acceptConfig [none]
            suffixTail) =
        tapeAtCells
          (List.append
            ((List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
              (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                false L)).reverse.map some)
            [none])
          ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.rejectConfig
            (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
              L.rejectHit [])).map some) := by
  rcases
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_cons_false
        L.rejectConfig
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.rejectHit []) with
    ⟨suffixTail, hsuffix⟩
  refine ⟨suffixTail, ?_, ?_⟩
  · rw [selectedProjectionPaddedTailCleanupPostPaddingSourceBits_false]
    rw [selectedProjectionPaddedTailCleanupPrefixBits]
    rw [SelectedProjectionTailProjector.outputPrefixBits]
    rw [
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
        L.rejectConfig
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.rejectHit [])]
    rw [hsuffix]
    rw [
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
        L.acceptConfig (false :: suffixTail)]
    simpa [List.map_append, List.append_assoc] using
      postPaddingOutputPrefixStageConfigScannerDescription_haltsFrom_raw
        (ParsedLayoutBits L) L.stage L.acceptConfig [none] suffixTail
  · rw [hsuffix]
    have hmove :=
      postPaddingOutputPrefixStageConfigScannerTarget_move_right_eq_suffixSource
        (ParsedLayoutBits L) L.stage L.acceptConfig [none] suffixTail
    rw [postPaddingAcceptConfigRestoredBase_eq_keptPrefix_reverse] at hmove
    simpa [selectedProjectionPaddedTailCleanupKeptPrefixBits,
      selectedProjectionPaddedTailCleanupSelectedConfigBits,
      selectedProjectionPaddedTailCleanupUnselectedConfigBits,
      List.append_assoc] using hmove

theorem postPaddingOutputPrefixStageConfigScannerDescription_rejectSourceBits_handoff_withRight
    (L : DovetailLayout) (rightPadding : List (Option Bool)) :
    exists suffixTail : Word Bool,
      postPaddingOutputPrefixStageConfigScannerDescription.HaltsFromTape
        (tapeAtCells [none]
          (List.append
            ((selectedProjectionPaddedTailCleanupPostPaddingSourceBits
              false L).map some)
            rightPadding))
        (postPaddingOutputPrefixStageConfigScannerTargetTapeWithRight
          (ParsedLayoutBits L) L.stage L.acceptConfig [none]
          suffixTail rightPadding) ∧
      Tape.move Direction.right
          (postPaddingOutputPrefixStageConfigScannerTargetTapeWithRight
            (ParsedLayoutBits L) L.stage L.acceptConfig [none]
            suffixTail rightPadding) =
        tapeAtCells
          (List.append
            ((List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
              (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                false L)).reverse.map some)
            [none])
          (List.append
            ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.rejectConfig
              (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                L.rejectHit [])).map some)
            rightPadding) := by
  rcases
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_cons_false
        L.rejectConfig
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.rejectHit []) with
    ⟨suffixTail, hsuffix⟩
  refine ⟨suffixTail, ?_, ?_⟩
  · rw [selectedProjectionPaddedTailCleanupPostPaddingSourceBits_false]
    rw [selectedProjectionPaddedTailCleanupPrefixBits]
    rw [SelectedProjectionTailProjector.outputPrefixBits]
    rw [
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
        L.rejectConfig
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.rejectHit [])]
    rw [hsuffix]
    rw [
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
        L.acceptConfig (false :: suffixTail)]
    simpa [List.map_append, List.append_assoc] using
      postPaddingOutputPrefixStageConfigScannerDescription_haltsFrom_raw_withRight
        (ParsedLayoutBits L) L.stage L.acceptConfig [none]
        suffixTail rightPadding
  · have hmove :=
      postPaddingOutputPrefixStageConfigScannerTarget_move_right_eq_suffixSource_withRight
        (ParsedLayoutBits L) L.stage L.acceptConfig [none]
        suffixTail rightPadding
    rw [postPaddingAcceptConfigRestoredBase_eq_keptPrefix_reverse] at hmove
    rw [hmove]
    rw [← hsuffix]
    simp [DovetailInitialLayoutInitializer.tapeAtCells, tapeAtCells,
      selectedProjectionPaddedTailCleanupKeptPrefixBits,
      selectedProjectionPaddedTailCleanupSelectedConfigBits,
      selectedProjectionPaddedTailCleanupUnselectedConfigBits,
      List.map_append, List.append_assoc]
    rfl

end SelectedProjectionPaddedTailCleanup

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
