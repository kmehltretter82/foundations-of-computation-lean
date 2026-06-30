import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.PostPaddingRejectRoute

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncodedRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

open CanonicalLayouts.DovetailLayoutScanner

theorem selectedProjectionPaddedTailCleanupSentinelExtraScratch_pos_true
    (L : DovetailLayout) :
    0 < selectedProjectionPaddedTailCleanupSentinelExtraScratch true L := by
  have hsource :=
    SelectedProjectionTailProjector.sourceFieldBits_length_le_parsedLayoutBits
      L
  have hbools :
      8 <=
        (boolFieldBits L.acceptHit []).length +
          (boolFieldBits L.rejectHit []).length := by
    cases L.acceptHit <;> cases L.rejectHit <;>
      simp [boolFieldBits, cellFieldBits, cellCodeBits,
        encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput]
  have hsplit :
      (SelectedProjectionTailProjector.sourceFieldBits L).length =
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          L.stage).length +
          (configurationFieldBits L.acceptConfig []).length +
          (configurationFieldBits L.rejectConfig []).length +
          (boolFieldBits L.acceptHit []).length +
          (boolFieldBits L.rejectHit []).length := by
    rw [SelectedProjectionTailProjector.sourceFieldBits]
    rw [←
      configurationFieldBits_append_nil L.acceptConfig
        (configurationFieldBits L.rejectConfig
          (boolFieldBits L.acceptHit
            (boolFieldBits L.rejectHit [])))]
    rw [←
      configurationFieldBits_append_nil L.rejectConfig
        (boolFieldBits L.acceptHit
          (boolFieldBits L.rejectHit []))]
    rw [show
        boolFieldBits L.acceptHit (boolFieldBits L.rejectHit []) =
          List.append (boolFieldBits L.acceptHit [])
            (boolFieldBits L.rejectHit []) by
      simpa [boolFieldBits] using
        (cellFieldBits_append_nil (some L.acceptHit)
          (boolFieldBits L.rejectHit [])).symm]
    simp [List.length_append, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]
  have hreject_pos :
      0 < (configurationFieldBits L.rejectConfig []).length := by
    simpa [selectedProjectionPaddedTailCleanupUnselectedConfigBits] using
      selectedProjectionPaddedTailCleanupUnselectedConfigBits_length_pos
        true L
  have hlt :
      selectedProjectionPaddedTailCleanupSentinelBaseScratch true L <
        (SelectedProjectionTailProjector.sourceFieldBits L).length := by
    rw [hsplit]
    simp [selectedProjectionPaddedTailCleanupSentinelBaseScratch,
      selectedProjectionPaddedTailCleanupUnselectedConfigBits]
    omega
  have hbase_lt_parsed :
      selectedProjectionPaddedTailCleanupSentinelBaseScratch true L <
        (ParsedLayoutBits L).length := Nat.lt_of_lt_of_le hlt hsource
  rw [selectedProjectionPaddedTailCleanupSentinelExtraScratch]
  omega

theorem selectedProjectionPaddedTailCleanupSentinelExtraScratch_pos_false
    (L : DovetailLayout) :
    0 < selectedProjectionPaddedTailCleanupSentinelExtraScratch false L := by
  have hsource :=
    SelectedProjectionTailProjector.sourceFieldBits_length_le_parsedLayoutBits
      L
  have hbools :
      8 <=
        (boolFieldBits L.acceptHit []).length +
          (boolFieldBits L.rejectHit []).length := by
    cases L.acceptHit <;> cases L.rejectHit <;>
      simp [boolFieldBits, cellFieldBits, cellCodeBits,
        encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput]
  have hsplit :
      (SelectedProjectionTailProjector.sourceFieldBits L).length =
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          L.stage).length +
          (configurationFieldBits L.acceptConfig []).length +
          (configurationFieldBits L.rejectConfig []).length +
          (boolFieldBits L.acceptHit []).length +
          (boolFieldBits L.rejectHit []).length := by
    rw [SelectedProjectionTailProjector.sourceFieldBits]
    rw [←
      configurationFieldBits_append_nil L.acceptConfig
        (configurationFieldBits L.rejectConfig
          (boolFieldBits L.acceptHit
            (boolFieldBits L.rejectHit [])))]
    rw [←
      configurationFieldBits_append_nil L.rejectConfig
        (boolFieldBits L.acceptHit
          (boolFieldBits L.rejectHit []))]
    rw [show
        boolFieldBits L.acceptHit (boolFieldBits L.rejectHit []) =
          List.append (boolFieldBits L.acceptHit [])
            (boolFieldBits L.rejectHit []) by
      simpa [boolFieldBits] using
        (cellFieldBits_append_nil (some L.acceptHit)
          (boolFieldBits L.rejectHit [])).symm]
    simp [List.length_append, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]
  have haccept_pos :
      0 < (configurationFieldBits L.acceptConfig []).length := by
    simpa [selectedProjectionPaddedTailCleanupUnselectedConfigBits] using
      selectedProjectionPaddedTailCleanupUnselectedConfigBits_length_pos
        false L
  have hlt :
      selectedProjectionPaddedTailCleanupSentinelBaseScratch false L <
        (SelectedProjectionTailProjector.sourceFieldBits L).length := by
    rw [hsplit]
    simp [selectedProjectionPaddedTailCleanupSentinelBaseScratch,
      selectedProjectionPaddedTailCleanupUnselectedConfigBits]
    omega
  have hbase_lt_parsed :
      selectedProjectionPaddedTailCleanupSentinelBaseScratch false L <
        (ParsedLayoutBits L).length := Nat.lt_of_lt_of_le hlt hsource
  rw [selectedProjectionPaddedTailCleanupSentinelExtraScratch]
  omega

def selectedProjectionPaddedTailCleanupAcceptSourceToEquivOutputDescription :
    MachineDescription :=
  canonicalSeqDescription
    selectedProjectionPaddedTailCleanupAcceptEraseToRightEndDescription
    selectedProjectionPaddedTailCleanupFalseMarkerToEquivOutputDescription

theorem selectedProjectionPaddedTailCleanupAcceptSourceToEquivOutputDescription_subroutineReady :
    selectedProjectionPaddedTailCleanupAcceptSourceToEquivOutputDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    selectedProjectionPaddedTailCleanupAcceptEraseToRightEndDescription_subroutineReady
    selectedProjectionPaddedTailCleanupFalseMarkerToEquivOutputDescription_subroutineReady

theorem selectedProjectionPaddedTailCleanupAcceptSourceToEquivOutputDescription_haltsFrom_source
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupAcceptSourceToEquivOutputDescription.HaltsFromTape
      (tapeAtCells [none]
        (List.append
          ((selectedProjectionPaddedTailCleanupPostPaddingSourceBits
            true L).map some)
          (none ::
            List.append (List.replicate 5 (none : Option Bool))
              (List.replicate
                (selectedProjectionPaddedTailCleanupSentinelExtraScratch
                  true L)
                (none : Option Bool)))))
      (SelectedProjectionEquivEmitterPaddedOutputTape true L) := by
  let rightPadding : List (Option Bool) :=
    List.replicate
      (selectedProjectionPaddedTailCleanupSentinelExtraScratch true L)
      (none : Option Bool)
  have herase :=
    selectedProjectionPaddedTailCleanupAcceptEraseToRightEndDescription_haltsFrom_sourceWithRight
      L rightPadding
  have hfinish :=
    selectedProjectionPaddedTailCleanupDeletedAcceptRightEnd_to_equivOutput_withLayoutExtraScratch
      L
  have hbridge :
      Tape.move Direction.left
          (Tape.move Direction.right
            (rightEndCompactionSourceTapeWithRightPadding
              (selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells L)
              rightPadding)) =
        rightEndCompactionSourceTapeWithRightPadding
          (selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells L)
          rightPadding := by
    have hpos :=
      selectedProjectionPaddedTailCleanupSentinelExtraScratch_pos_true L
    cases hextra :
        selectedProjectionPaddedTailCleanupSentinelExtraScratch true L with
    | zero => omega
    | succ extra =>
        simpa [rightPadding, hextra, List.replicate_succ] using
          rightEndCompactionSourceTapeWithRightPadding_move_left_move_right_cons
            (selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells
              L)
            none
            (List.replicate extra (none : Option Bool))
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      selectedProjectionPaddedTailCleanupAcceptEraseToRightEndDescription_subroutineReady
      selectedProjectionPaddedTailCleanupFalseMarkerToEquivOutputDescription_subroutineReady
      herase hbridge hfinish

theorem selectedProjectionPaddedTailCleanupDeletedRejectRightEnd_fixedGap_sentinelCompactor_haltsFrom_bridgePaddingWithRight
    (L : DovetailLayout) (rightPadding : List (Option Bool)) :
    sentinelGapCompactorDescription.HaltsFromTape
      (rightEndCompactionSourceTapeWithRightPadding
        (selectedProjectionPaddedTailCleanupDeletedRejectRightEndLeftCells L)
        (none :: rightPadding))
      (rightEndCompactionSourceTapeWithRightPadding
        (selectedProjectionPaddedTailCleanupDeletedRejectFixedGapClosedLeftCells
          L)
        (List.append (List.replicate 3 (none : Option Bool))
          rightPadding)) := by
  rcases
      selectedProjectionPaddedTailCleanupSelectedConfig_false_append_last
        L with
    ⟨cfgPref, leftBit, hcfg⟩
  rcases
      selectedProjectionPaddedTailCleanupSelectedHit_false_reverse_cons
        L with
    ⟨current, leftRest, hhitRev⟩
  let baseTail : List (Option Bool) :=
    List.append (cfgPref.reverse.map some)
      (List.append
        (List.replicate
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits
            false L).length
          (none : Option Bool))
        (List.append
          ((selectedProjectionPaddedTailCleanupPrefixBits L).reverse.map
            some)
          [none]))
  have hhit : (current :: leftRest).reverse =
      selectedProjectionPaddedTailCleanupSelectedHitBits false L := by
    rw [← hhitRev]
    simp
  have hsource :
      rightEndCompactionSourceTapeWithRightPadding
          (selectedProjectionPaddedTailCleanupDeletedRejectRightEndLeftCells
            L)
          (none :: rightPadding) =
        rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
          (rightBlankLocalGapBaseLeft 3 (some leftBit :: baseTail))
          current leftRest 0 (none :: rightPadding) := by
    simp [rightBlankLocalGapCompactorSourceTapeWithBaseAndRight,
      rightEndCompactionSourceTapeWithRightPadding,
      selectedProjectionPaddedTailCleanupDeletedRejectRightEndLeftCells,
      rightBlankLocalGapBaseLeft, baseTail, hcfg, ← hhit,
      tapeAtCells, List.reverse_append, List.map_reverse,
      List.map_append, List.append_assoc]
  have htarget :
      rightEndCompactionSourceTapeWithRightPadding
          (selectedProjectionPaddedTailCleanupDeletedRejectFixedGapClosedLeftCells
            L)
          (List.append (List.replicate 3 (none : Option Bool))
            rightPadding) =
        leadingBlankLeftShiftTargetTapeWithPadding
          (some leftBit :: baseTail) (current :: leftRest).reverse
          (sentinelGapCompactorFinalPadding 3 0 rightPadding) := by
    simp [rightEndCompactionSourceTapeWithRightPadding,
      selectedProjectionPaddedTailCleanupDeletedRejectFixedGapClosedLeftCells,
      leadingBlankLeftShiftTargetTapeWithPadding, baseTail, hcfg,
      ← hhit, sentinelGapCompactorFinalPadding, tapeAtCells,
      List.reverse_append, List.map_reverse, List.map_append,
      List.append_assoc]
  rw [hsource, htarget]
  simpa using
    sentinelGapCompactorDescription_haltsFromTape_gapBase_zero_cons_right
      2 baseTail leftBit current leftRest rightPadding

def selectedProjectionPaddedTailCleanupDeletedRejectRightEndToEquivOutputDescription :
    MachineDescription :=
  canonicalSeqDescription
    sentinelGapCompactorDescription
    selectedProjectionPaddedTailCleanupFalseMarkerToEquivOutputDescription

theorem selectedProjectionPaddedTailCleanupDeletedRejectRightEndToEquivOutputDescription_subroutineReady :
    selectedProjectionPaddedTailCleanupDeletedRejectRightEndToEquivOutputDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    sentinelGapCompactorDescription_subroutineReady
    selectedProjectionPaddedTailCleanupFalseMarkerToEquivOutputDescription_subroutineReady

theorem selectedProjectionPaddedTailCleanupDeletedRejectRightEndToEquivOutputDescription_haltsFrom
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupDeletedRejectRightEndToEquivOutputDescription.HaltsFromTape
      (rightEndCompactionSourceTapeWithRightPadding
        (selectedProjectionPaddedTailCleanupDeletedRejectRightEndLeftCells L)
        (none ::
          List.replicate
            (selectedProjectionPaddedTailCleanupSentinelExtraScratch
              false L)
            (none : Option Bool)))
      (SelectedProjectionEquivEmitterPaddedOutputTape false L) := by
  let extraPadding : List (Option Bool) :=
    List.replicate
      (selectedProjectionPaddedTailCleanupSentinelExtraScratch false L)
      (none : Option Bool)
  have hgap :=
    selectedProjectionPaddedTailCleanupDeletedRejectRightEnd_fixedGap_sentinelCompactor_haltsFrom_bridgePaddingWithRight
      L extraPadding
  have hfinish :=
    selectedProjectionPaddedTailCleanupDeletedRejectFixedGapClosed_to_equivOutput_withLayoutExtraScratch
      L
  have hbridge :
      Tape.move Direction.left
          (Tape.move Direction.right
            (rightEndCompactionSourceTapeWithRightPadding
              (selectedProjectionPaddedTailCleanupDeletedRejectFixedGapClosedLeftCells
                L)
              (List.append (List.replicate 3 (none : Option Bool))
                extraPadding))) =
        rightEndCompactionSourceTapeWithRightPadding
          (selectedProjectionPaddedTailCleanupDeletedRejectFixedGapClosedLeftCells
            L)
          (List.append (List.replicate 3 (none : Option Bool))
            extraPadding) := by
    simpa [List.replicate_succ, List.append_assoc] using
      rightEndCompactionSourceTapeWithRightPadding_move_left_move_right_cons
        (selectedProjectionPaddedTailCleanupDeletedRejectFixedGapClosedLeftCells
          L)
        none
        (List.append (List.replicate 2 (none : Option Bool))
          extraPadding)
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      sentinelGapCompactorDescription_subroutineReady
      selectedProjectionPaddedTailCleanupFalseMarkerToEquivOutputDescription_subroutineReady
      hgap hbridge hfinish

def selectedProjectionPaddedTailCleanupRejectSourceToEquivOutputDescription :
    MachineDescription :=
  canonicalSeqDescription
    selectedProjectionPaddedTailCleanupRejectEraseToRightEndDescription
    selectedProjectionPaddedTailCleanupDeletedRejectRightEndToEquivOutputDescription

theorem selectedProjectionPaddedTailCleanupRejectSourceToEquivOutputDescription_subroutineReady :
    selectedProjectionPaddedTailCleanupRejectSourceToEquivOutputDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    selectedProjectionPaddedTailCleanupRejectEraseToRightEndDescription_subroutineReady
    selectedProjectionPaddedTailCleanupDeletedRejectRightEndToEquivOutputDescription_subroutineReady

theorem selectedProjectionPaddedTailCleanupRejectSourceToEquivOutputDescription_haltsFrom_source
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupRejectSourceToEquivOutputDescription.HaltsFromTape
      (tapeAtCells [none]
        (List.append
          (List.append
            (List.append
              ((selectedProjectionPaddedTailCleanupPrefixBits L).map some)
              ((configurationFieldBits L.acceptConfig []).map some))
            ((configurationFieldBits L.rejectConfig []).map some))
          (List.append (List.replicate 4 (none : Option Bool))
            (List.append
              ((selectedProjectionPaddedTailCleanupSelectedHitBits
                false L).map some)
              (none :: none ::
                List.replicate
                  (selectedProjectionPaddedTailCleanupSentinelExtraScratch
                    false L)
                  (none : Option Bool))))))
      (SelectedProjectionEquivEmitterPaddedOutputTape false L) := by
  let extraPadding : List (Option Bool) :=
    List.replicate
      (selectedProjectionPaddedTailCleanupSentinelExtraScratch false L)
      (none : Option Bool)
  let rightPadding : List (Option Bool) := none :: extraPadding
  have herase :=
    selectedProjectionPaddedTailCleanupRejectEraseToRightEndDescription_haltsFrom_sourceWithRight
      L rightPadding
  have hfinish :=
    selectedProjectionPaddedTailCleanupDeletedRejectRightEndToEquivOutputDescription_haltsFrom
      L
  have hbridge :
      Tape.move Direction.left
          (Tape.move Direction.right
            (rightEndCompactionSourceTapeWithRightPadding
              (selectedProjectionPaddedTailCleanupDeletedRejectRightEndLeftCells L)
              rightPadding)) =
        rightEndCompactionSourceTapeWithRightPadding
          (selectedProjectionPaddedTailCleanupDeletedRejectRightEndLeftCells L)
          rightPadding := by
    simpa [rightPadding] using
      rightEndCompactionSourceTapeWithRightPadding_move_left_move_right_cons
        (selectedProjectionPaddedTailCleanupDeletedRejectRightEndLeftCells L)
        none extraPadding
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      selectedProjectionPaddedTailCleanupRejectEraseToRightEndDescription_subroutineReady
      selectedProjectionPaddedTailCleanupDeletedRejectRightEndToEquivOutputDescription_subroutineReady
      herase hbridge hfinish

/--
Combined post-padding finite-machine leaf for selected-projection tail cleanup.
The branch wrappers below project this single obligation into the accepting and
rejecting branch contracts.
-/
theorem selectedProjectionPaddedTailCleanupPostPaddingCoreConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingConstruction := by
  sorry

def selectedHitOtherFlagErasedPostEraseFromPostPadding
    (useAccept : Bool) (postPadding : MachineDescription) :
    MachineDescription :=
  if useAccept then
    SeqViaCanonical skipCurrentAndFourBlankPaddingLeftDescription
      postPadding
  else
    SeqViaCanonical skipCurrentAndFourBlankPaddingRightDescription
      postPadding

theorem selectedProjectionPaddedTailCleanupPostEraseSpec_of_postPadding
    {useAccept : Bool} {postPadding : MachineDescription}
    (hpostPadding :
      SelectedProjectionPaddedTailCleanupPostPaddingSpec
        useAccept postPadding) :
    SelectedProjectionPaddedTailCleanupPostEraseSpec useAccept
      (selectedHitOtherFlagErasedPostEraseFromPostPadding
        useAccept postPadding) := by
  cases useAccept
  · constructor
    · simpa [selectedHitOtherFlagErasedPostEraseFromPostPadding] using
        SeqViaCanonical_subroutineReady
          skipCurrentAndFourBlankPaddingRightDescription_subroutineReady
          hpostPadding.left
    · intro L
      exact
        SeqViaCanonical_haltsFromTape_of_haltsFromTape
          skipCurrentAndFourBlankPaddingRightDescription_subroutineReady
          hpostPadding.left
          (skipCurrentAndFourBlankPaddingRightDescription_haltsFrom_rejectHandoff_named
            L)
          (by
            simpa [selectedHitOtherFlagErasedAfterPaddingTape] using
              selectedHitOtherFlagErasedAfterPaddingTape_move_left_move_right
                false L)
          (by
            simpa [selectedHitOtherFlagErasedAfterPaddingTape] using
              hpostPadding.right L)
  · constructor
    · simpa [selectedHitOtherFlagErasedPostEraseFromPostPadding] using
        SeqViaCanonical_subroutineReady
          skipCurrentAndFourBlankPaddingLeftDescription_subroutineReady
          hpostPadding.left
    · intro L
      exact
        SeqViaCanonical_haltsFromTape_of_haltsFromTape
          skipCurrentAndFourBlankPaddingLeftDescription_subroutineReady
          hpostPadding.left
          (skipCurrentAndFourBlankPaddingLeftDescription_haltsFrom_acceptHandoff
            L)
          (by
            simpa [selectedHitOtherFlagErasedAfterPaddingTape] using
              selectedHitOtherFlagErasedAfterPaddingTape_move_left_move_right
                true L)
          (by
            simpa [selectedHitOtherFlagErasedAfterPaddingTape] using
              hpostPadding.right L)

theorem selectedProjectionPaddedTailCleanupPostEraseConstruction_of_postPadding
    (h :
      SelectedProjectionPaddedTailCleanupPostPaddingConstruction) :
    SelectedProjectionPaddedTailCleanupPostEraseConstruction := by
  intro useAccept
  rcases h useAccept with ⟨postPadding, hpostPadding⟩
  exact
    ⟨selectedHitOtherFlagErasedPostEraseFromPostPadding
        useAccept postPadding,
      selectedProjectionPaddedTailCleanupPostEraseSpec_of_postPadding
        hpostPadding⟩

/--
Post-padding finite-machine leaf for selected-projection tail cleanup on the
accepting projection branch.
-/
theorem selectedProjectionPaddedTailCleanupPostPaddingAcceptConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingBranchConstruction true := by
  exact selectedProjectionPaddedTailCleanupPostPaddingCoreConstruction true

/--
Post-padding finite-machine leaf for selected-projection tail cleanup on the
rejecting projection branch.
-/
theorem selectedProjectionPaddedTailCleanupPostPaddingRejectConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingBranchConstruction false := by
  exact selectedProjectionPaddedTailCleanupPostPaddingCoreConstruction false

theorem selectedProjectionPaddedTailCleanupPostPaddingConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingConstruction :=
  selectedProjectionPaddedTailCleanupPostPaddingConstruction_of_branches
    selectedProjectionPaddedTailCleanupPostPaddingAcceptConstruction
    selectedProjectionPaddedTailCleanupPostPaddingRejectConstruction

theorem selectedProjectionPaddedTailCleanupPostEraseConstruction :
    SelectedProjectionPaddedTailCleanupPostEraseConstruction :=
  selectedProjectionPaddedTailCleanupPostEraseConstruction_of_postPadding
    selectedProjectionPaddedTailCleanupPostPaddingConstruction

end SelectedProjectionPaddedTailCleanup

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
