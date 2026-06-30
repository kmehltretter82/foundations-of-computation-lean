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

def selectedProjectionPaddedTailCleanupAcceptLayoutScratchSourceTape
    (L : DovetailLayout) : Tape Bool :=
  tapeAtCells [none]
    (List.append
      ((selectedProjectionPaddedTailCleanupPostPaddingSourceBits
        true L).map some)
      (none ::
        List.append (List.replicate 5 (none : Option Bool))
          (List.replicate
            (selectedProjectionPaddedTailCleanupSentinelExtraScratch
              true L)
            (none : Option Bool))))

def selectedProjectionPaddedTailCleanupRejectLayoutScratchSourceTape
    (L : DovetailLayout) : Tape Bool :=
  tapeAtCells [none]
    (List.append
      (List.append
        (List.append
          ((selectedProjectionPaddedTailCleanupPrefixBits L).map some)
          ((selectedProjectionPaddedTailCleanupUnselectedConfigBits
            false L).map some))
        ((selectedProjectionPaddedTailCleanupSelectedConfigBits
          false L).map some))
      (List.append (List.replicate 4 (none : Option Bool))
        (List.append
          ((selectedProjectionPaddedTailCleanupSelectedHitBits
            false L).map some)
          (none :: none ::
            List.replicate
              (selectedProjectionPaddedTailCleanupSentinelExtraScratch
                false L)
              (none : Option Bool)))))

def selectedProjectionPaddedTailCleanupLayoutScratchSourceTape
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  if useAccept then
    selectedProjectionPaddedTailCleanupAcceptLayoutScratchSourceTape L
  else
    selectedProjectionPaddedTailCleanupRejectLayoutScratchSourceTape L

def selectedProjectionPaddedTailCleanupAcceptBaseSourceTape
    (L : DovetailLayout) : Tape Bool :=
  tapeAtCells [none]
    (List.append
      ((selectedProjectionPaddedTailCleanupPostPaddingSourceBits
        true L).map some)
      (none :: List.replicate 5 (none : Option Bool)))

def selectedProjectionPaddedTailCleanupRejectBaseSourceTape
    (L : DovetailLayout) : Tape Bool :=
  tapeAtCells [none]
    (List.append
      (List.append
        (List.append
          ((selectedProjectionPaddedTailCleanupPrefixBits L).map some)
          ((selectedProjectionPaddedTailCleanupUnselectedConfigBits
            false L).map some))
        ((selectedProjectionPaddedTailCleanupSelectedConfigBits
          false L).map some))
      (List.append (List.replicate 4 (none : Option Bool))
        (List.append
          ((selectedProjectionPaddedTailCleanupSelectedHitBits
            false L).map some)
          (none :: none :: []))))

def selectedProjectionPaddedTailCleanupBaseSourceTape
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  if useAccept then
    selectedProjectionPaddedTailCleanupAcceptBaseSourceTape L
  else
    selectedProjectionPaddedTailCleanupRejectBaseSourceTape L

def selectedProjectionPaddedTailCleanupSourceToEquivOutputDescription
    (useAccept : Bool) : MachineDescription :=
  if useAccept then
    selectedProjectionPaddedTailCleanupAcceptSourceToEquivOutputDescription
  else
    selectedProjectionPaddedTailCleanupRejectSourceToEquivOutputDescription

theorem selectedProjectionPaddedTailCleanupSourceToEquivOutputDescription_subroutineReady
    (useAccept : Bool) :
    (selectedProjectionPaddedTailCleanupSourceToEquivOutputDescription
      useAccept).SubroutineReady := by
  cases useAccept
  · simpa [selectedProjectionPaddedTailCleanupSourceToEquivOutputDescription]
      using
        selectedProjectionPaddedTailCleanupRejectSourceToEquivOutputDescription_subroutineReady
  · simpa [selectedProjectionPaddedTailCleanupSourceToEquivOutputDescription]
      using
        selectedProjectionPaddedTailCleanupAcceptSourceToEquivOutputDescription_subroutineReady

theorem selectedProjectionPaddedTailCleanupSourceToEquivOutputDescription_haltsFrom_layoutScratchSource
    (useAccept : Bool) (L : DovetailLayout) :
    (selectedProjectionPaddedTailCleanupSourceToEquivOutputDescription
      useAccept).HaltsFromTape
      (selectedProjectionPaddedTailCleanupLayoutScratchSourceTape
        useAccept L)
      (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L) := by
  cases useAccept
  · simpa [
      selectedProjectionPaddedTailCleanupSourceToEquivOutputDescription,
      selectedProjectionPaddedTailCleanupLayoutScratchSourceTape,
      selectedProjectionPaddedTailCleanupRejectLayoutScratchSourceTape,
      selectedProjectionPaddedTailCleanupUnselectedConfigBits,
      selectedProjectionPaddedTailCleanupSelectedConfigBits]
      using
        selectedProjectionPaddedTailCleanupRejectSourceToEquivOutputDescription_haltsFrom_source
          L
  · simpa [
      selectedProjectionPaddedTailCleanupSourceToEquivOutputDescription,
      selectedProjectionPaddedTailCleanupLayoutScratchSourceTape,
      selectedProjectionPaddedTailCleanupAcceptLayoutScratchSourceTape]
      using
        selectedProjectionPaddedTailCleanupAcceptSourceToEquivOutputDescription_haltsFrom_source
          L

theorem selectedProjectionPaddedTailCleanupLayoutScratchSourceTape_move_left_move_right
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (selectedProjectionPaddedTailCleanupLayoutScratchSourceTape
            useAccept L)) =
      selectedProjectionPaddedTailCleanupLayoutScratchSourceTape
        useAccept L := by
  cases useAccept
  · simp [
      selectedProjectionPaddedTailCleanupLayoutScratchSourceTape,
      selectedProjectionPaddedTailCleanupRejectLayoutScratchSourceTape,
      selectedProjectionPaddedTailCleanupPrefixBits,
      SelectedProjectionTailProjector.outputPrefixBits,
      encodeCodeSymbolAsInput, tapeAtCells, Tape.move,
      Tape.moveLeft, Tape.moveRight, List.append_assoc]
  · simp [
      selectedProjectionPaddedTailCleanupLayoutScratchSourceTape,
      selectedProjectionPaddedTailCleanupAcceptLayoutScratchSourceTape,
      selectedProjectionPaddedTailCleanupPostPaddingSourceBits,
      selectedProjectionPaddedTailCleanupPrefixBits,
      SelectedProjectionTailProjector.outputPrefixBits,
      encodeCodeSymbolAsInput, tapeAtCells, Tape.move,
      Tape.moveLeft, Tape.moveRight, List.map_append,
      List.append_assoc]

theorem selectedProjectionPaddedTailCleanupBaseSourceTape_move_left_move_right
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (selectedProjectionPaddedTailCleanupBaseSourceTape
            useAccept L)) =
      selectedProjectionPaddedTailCleanupBaseSourceTape
        useAccept L := by
  cases useAccept
  · simp [
      selectedProjectionPaddedTailCleanupBaseSourceTape,
      selectedProjectionPaddedTailCleanupRejectBaseSourceTape,
      selectedProjectionPaddedTailCleanupPrefixBits,
      SelectedProjectionTailProjector.outputPrefixBits,
      encodeCodeSymbolAsInput, tapeAtCells, Tape.move,
      Tape.moveLeft, Tape.moveRight, List.append_assoc]
  · simp [
      selectedProjectionPaddedTailCleanupBaseSourceTape,
      selectedProjectionPaddedTailCleanupAcceptBaseSourceTape,
      selectedProjectionPaddedTailCleanupPostPaddingSourceBits,
      selectedProjectionPaddedTailCleanupPrefixBits,
      SelectedProjectionTailProjector.outputPrefixBits,
      encodeCodeSymbolAsInput, tapeAtCells, Tape.move,
      Tape.moveLeft, Tape.moveRight, List.map_append,
      List.append_assoc]

def leftMoveCurrentAcrossFourBlankGapDescription :
    MachineDescription where
  stateCount := 5
  start := 0
  halt := 4
  transitions :=
    [ transition 0 (some false) (some false) Direction.left 1
    , transition 0 (some true) (some true) Direction.left 1
    , transition 1 none none Direction.left 2
    , transition 2 none none Direction.left 3
    , transition 3 none none Direction.left 4
    ]

theorem leftMoveCurrentAcrossFourBlankGapDescription_wellFormed :
    leftMoveCurrentAcrossFourBlankGapDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := leftMoveCurrentAcrossFourBlankGapDescription.transitions)
      (stateCount :=
        leftMoveCurrentAcrossFourBlankGapDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := leftMoveCurrentAcrossFourBlankGapDescription.transitions)
      (by decide)

theorem leftMoveCurrentAcrossFourBlankGapDescription_haltTransitionFree :
    leftMoveCurrentAcrossFourBlankGapDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := leftMoveCurrentAcrossFourBlankGapDescription.transitions)
    (state := leftMoveCurrentAcrossFourBlankGapDescription.halt)
    (by decide)

theorem leftMoveCurrentAcrossFourBlankGapDescription_subroutineReady :
    leftMoveCurrentAcrossFourBlankGapDescription.SubroutineReady :=
  ⟨leftMoveCurrentAcrossFourBlankGapDescription_wellFormed,
    leftMoveCurrentAcrossFourBlankGapDescription_haltTransitionFree⟩

theorem leftMoveCurrentAcrossFourBlankGapDescription_run
    (current : Bool) (left right : List (Option Bool)) :
    leftMoveCurrentAcrossFourBlankGapDescription.runConfig 4
        { state := leftMoveCurrentAcrossFourBlankGapDescription.start
          tape :=
            tapeAtCells
              (none :: none :: none :: none :: left)
              (some current :: right) } =
      { state := leftMoveCurrentAcrossFourBlankGapDescription.halt
        tape :=
          tapeAtCells left
            (none :: none :: none :: none :: some current :: right) } := by
  cases current <;> cases right <;>
    simp [leftMoveCurrentAcrossFourBlankGapDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem leftMoveCurrentAcrossFourBlankGapDescription_haltsFromTape
    (current : Bool) (left right : List (Option Bool)) :
    leftMoveCurrentAcrossFourBlankGapDescription.HaltsFromTape
      (tapeAtCells
        (none :: none :: none :: none :: left)
        (some current :: right))
      (tapeAtCells left
        (none :: none :: none :: none :: some current :: right)) := by
  refine ⟨4, ?_⟩
  constructor <;>
    rw [leftMoveCurrentAcrossFourBlankGapDescription_run]

def selectedProjectionPaddedTailCleanupRejectRightEndToBaseSourceDescription :
    MachineDescription :=
  canonicalSeqDescription
    (canonicalSeqDescription rightEdgeRewindDescription
      leftMoveCurrentAcrossFourBlankGapDescription)
    rightEdgeRewindDescription

theorem selectedProjectionPaddedTailCleanupRejectRightEndToBaseSourceDescription_subroutineReady :
    selectedProjectionPaddedTailCleanupRejectRightEndToBaseSourceDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    (canonicalSeqDescription_subroutineReady
      rightEdgeRewindDescription_subroutineReady
      leftMoveCurrentAcrossFourBlankGapDescription_subroutineReady)
    rightEdgeRewindDescription_subroutineReady

theorem selectedProjectionPaddedTailCleanupRejectRightEndToBaseSourceDescription_haltsFrom
    (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupRejectRightEndToBaseSourceDescription.HaltsFromTape
      (rightEndCompactionSourceTapeWithRightPadding
        (selectedHitOtherFlagErasedRejectAfterPaddingRightEndLeftCells L)
        [none])
      (selectedProjectionPaddedTailCleanupRejectBaseSourceTape L) := by
  rcases cellFieldBits_cons_false (some L.rejectHit) [] with
    ⟨hitTail, hhitTail⟩
  have hhit :
      selectedProjectionPaddedTailCleanupSelectedHitBits false L =
        false :: hitTail := by
    simpa [selectedProjectionPaddedTailCleanupSelectedHitBits,
      boolFieldBits] using hhitTail
  let baseBits : Word Bool :=
    List.append
      (selectedProjectionPaddedTailCleanupPrefixBits L)
      (List.append
        (selectedProjectionPaddedTailCleanupUnselectedConfigBits false L)
        (selectedProjectionPaddedTailCleanupSelectedConfigBits false L))
  let hitBits : Word Bool := false :: hitTail
  let hitBaseLeft : List (Option Bool) :=
    List.append (List.replicate 3 (none : Option Bool))
      (List.append (baseBits.reverse.map some) [none])
  let finalPadding : List (Option Bool) :=
    List.append (List.replicate 3 (none : Option Bool))
      (List.append (hitBits.map some)
        [none, none])
  have hstart :
      rightEndCompactionSourceTapeWithRightPadding
          (selectedHitOtherFlagErasedRejectAfterPaddingRightEndLeftCells L)
          [none] =
        rightEdgeRewindSourceTapeWithBase hitBaseLeft hitBits [none] := by
    rw [selectedHitOtherFlagErasedRejectAfterPaddingRightEndLeftCells_eq_sourceFields]
    rw [hhit]
    simp [rightEndCompactionSourceTapeWithRightPadding,
      rightEdgeRewindSourceTapeWithBase, hitBaseLeft, hitBits, baseBits,
      selectedProjectionPaddedTailCleanupUnselectedConfigBits,
      selectedProjectionPaddedTailCleanupSelectedConfigBits,
      tapeAtCells, List.reverse_append, List.map_append,
      List.replicate_succ, List.append_assoc]
  have hrewindHit :
      rightEdgeRewindDescription.HaltsFromTape
        (rightEndCompactionSourceTapeWithRightPadding
          (selectedHitOtherFlagErasedRejectAfterPaddingRightEndLeftCells L)
          [none])
        (rightEdgeRewindTargetTapeWithBase hitBaseLeft hitBits [none]) := by
    simpa [hstart] using
      rightEdgeRewindDescription_haltsFromTapeWithBase
        hitBaseLeft hitBits [none]
  have hbridgeHit :
      Tape.move Direction.left
          (Tape.move Direction.right
            (rightEdgeRewindTargetTapeWithBase hitBaseLeft hitBits [none])) =
        rightEdgeRewindTargetTapeWithBase hitBaseLeft hitBits [none] := by
    cases hitTail <;>
      simp [rightEdgeRewindTargetTapeWithBase, hitBits, tapeAtCells,
        Tape.move, Tape.moveLeft, Tape.moveRight]
  have hmoveGap :
      leftMoveCurrentAcrossFourBlankGapDescription.HaltsFromTape
        (rightEdgeRewindTargetTapeWithBase hitBaseLeft hitBits [none])
        (rightEdgeRewindSourceTapeWithBase [] baseBits finalPadding) := by
    simpa [rightEdgeRewindTargetTapeWithBase,
      rightEdgeRewindSourceTapeWithBase, hitBaseLeft, finalPadding,
      hitBits, List.replicate_succ, List.append_assoc] using
      leftMoveCurrentAcrossFourBlankGapDescription_haltsFromTape
        false
        (List.append (baseBits.reverse.map some) [none])
        (List.append (hitTail.map some) [none, none])
  have hfirst :
      (canonicalSeqDescription rightEdgeRewindDescription
        leftMoveCurrentAcrossFourBlankGapDescription).HaltsFromTape
        (rightEndCompactionSourceTapeWithRightPadding
          (selectedHitOtherFlagErasedRejectAfterPaddingRightEndLeftCells L)
          [none])
        (rightEdgeRewindSourceTapeWithBase [] baseBits finalPadding) :=
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      rightEdgeRewindDescription_subroutineReady
      leftMoveCurrentAcrossFourBlankGapDescription_subroutineReady
      hrewindHit hbridgeHit hmoveGap
  have hbridgeBase :
      Tape.move Direction.left
          (Tape.move Direction.right
            (rightEdgeRewindSourceTapeWithBase [] baseBits finalPadding)) =
        rightEdgeRewindSourceTapeWithBase [] baseBits finalPadding := by
    simpa [finalPadding, hitBits, List.append_assoc] using
      rightEdgeRewindSourceTapeWithBase_move_left_move_right_padding_append_cons
        [] baseBits 3 (some false)
        (List.append (hitTail.map some) [none, none])
  have hrewindBase :
      rightEdgeRewindDescription.HaltsFromTape
        (rightEdgeRewindSourceTapeWithBase [] baseBits finalPadding)
        (selectedProjectionPaddedTailCleanupRejectBaseSourceTape L) := by
    have hrewind :=
      rightEdgeRewindDescription_haltsFromTapeWithBase
        [] baseBits finalPadding
    simpa [rightEdgeRewindTargetTapeWithBase,
      selectedProjectionPaddedTailCleanupRejectBaseSourceTape,
      finalPadding, hitBits, baseBits, hhit,
      selectedProjectionPaddedTailCleanupUnselectedConfigBits,
      selectedProjectionPaddedTailCleanupSelectedConfigBits,
      List.replicate_succ, List.append_assoc] using hrewind
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      (canonicalSeqDescription_subroutineReady
        rightEdgeRewindDescription_subroutineReady
        leftMoveCurrentAcrossFourBlankGapDescription_subroutineReady)
      rightEdgeRewindDescription_subroutineReady
      hfirst hbridgeBase hrewindBase

def SelectedProjectionPaddedTailCleanupPostPaddingBaseSourceMaterializerSpec
    (useAccept : Bool) (materializer : MachineDescription) : Prop :=
  materializer.SubroutineReady ∧
    forall L : DovetailLayout,
      materializer.HaltsFromTape
        (selectedHitOtherFlagErasedAfterPaddingTape useAccept L)
        (selectedProjectionPaddedTailCleanupBaseSourceTape useAccept L)

def SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorSpec
    (useAccept : Bool) (allocator : MachineDescription) : Prop :=
  allocator.SubroutineReady ∧
    forall L : DovetailLayout,
      allocator.HaltsFromTape
        (selectedProjectionPaddedTailCleanupBaseSourceTape useAccept L)
        (selectedProjectionPaddedTailCleanupLayoutScratchSourceTape
          useAccept L)

def SelectedProjectionPaddedTailCleanupPostPaddingSourceMaterializerSpec
    (useAccept : Bool) (materializer : MachineDescription) : Prop :=
  materializer.SubroutineReady ∧
    forall L : DovetailLayout,
      materializer.HaltsFromTape
        (selectedHitOtherFlagErasedAfterPaddingTape useAccept L)
        (selectedProjectionPaddedTailCleanupLayoutScratchSourceTape
          useAccept L)

def SelectedProjectionPaddedTailCleanupPostPaddingSourceMaterializerConstruction :
    Prop :=
  forall useAccept : Bool,
    exists materializer : MachineDescription,
      SelectedProjectionPaddedTailCleanupPostPaddingSourceMaterializerSpec
        useAccept materializer

def SelectedProjectionPaddedTailCleanupPostPaddingBaseAndScratchConstruction :
    Prop :=
  (exists rejectMaterializer : MachineDescription,
      SelectedProjectionPaddedTailCleanupPostPaddingBaseSourceMaterializerSpec
        false rejectMaterializer) ∧
    forall useAccept : Bool,
      exists allocator : MachineDescription,
        SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorSpec
          useAccept allocator

theorem selectedProjectionPaddedTailCleanupAcceptBaseSourceMaterializerSpec :
    SelectedProjectionPaddedTailCleanupPostPaddingBaseSourceMaterializerSpec
      true rightEdgeRewindDescription := by
  constructor
  · exact rightEdgeRewindDescription_subroutineReady
  · intro L
    simpa [selectedProjectionPaddedTailCleanupAcceptBaseSourceTape,
      selectedProjectionPaddedTailCleanupBaseSourceTape] using
      rightEdgeRewindDescription_haltsFrom_acceptAfterPadding_tapeAtCells
        L

theorem selectedProjectionPaddedTailCleanupRejectBaseSourceMaterializerSpec :
    SelectedProjectionPaddedTailCleanupPostPaddingBaseSourceMaterializerSpec
      false
      (canonicalSeqDescription
        selectedHitOtherFlagErasedRejectToRightEndDescription
        selectedProjectionPaddedTailCleanupRejectRightEndToBaseSourceDescription) := by
  constructor
  · exact
      canonicalSeqDescription_subroutineReady
        selectedHitOtherFlagErasedRejectToRightEndDescription_subroutineReady
        selectedProjectionPaddedTailCleanupRejectRightEndToBaseSourceDescription_subroutineReady
  · intro L
    exact
      canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        selectedHitOtherFlagErasedRejectToRightEndDescription_subroutineReady
        selectedProjectionPaddedTailCleanupRejectRightEndToBaseSourceDescription_subroutineReady
        (selectedHitOtherFlagErasedRejectToRightEndDescription_haltsFrom_afterPadding
          L)
        (rightEndCompactionSourceTape_move_left_move_right_eq_withRightPadding
          (selectedHitOtherFlagErasedRejectAfterPaddingRightEndLeftCells L))
        (selectedProjectionPaddedTailCleanupRejectRightEndToBaseSourceDescription_haltsFrom
          L)

theorem selectedProjectionPaddedTailCleanupPostPaddingSourceMaterializerSpec_of_baseAndScratch
    {useAccept : Bool}
    {baseMaterializer allocator : MachineDescription}
    (hbase :
      SelectedProjectionPaddedTailCleanupPostPaddingBaseSourceMaterializerSpec
        useAccept baseMaterializer)
    (hallocator :
      SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorSpec
        useAccept allocator) :
    SelectedProjectionPaddedTailCleanupPostPaddingSourceMaterializerSpec
      useAccept (canonicalSeqDescription baseMaterializer allocator) := by
  constructor
  · exact canonicalSeqDescription_subroutineReady hbase.left hallocator.left
  · intro L
    exact
      canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        hbase.left hallocator.left
        (hbase.right L)
        (selectedProjectionPaddedTailCleanupBaseSourceTape_move_left_move_right
          useAccept L)
        (hallocator.right L)

theorem selectedProjectionPaddedTailCleanupPostPaddingSourceMaterializerConstruction_of_baseAndScratch
    (h :
      SelectedProjectionPaddedTailCleanupPostPaddingBaseAndScratchConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingSourceMaterializerConstruction := by
  intro useAccept
  cases useAccept
  · rcases h.left with ⟨rejectMaterializer, hreject⟩
    rcases h.right false with ⟨allocator, hallocator⟩
    exact
      ⟨canonicalSeqDescription rejectMaterializer allocator,
        selectedProjectionPaddedTailCleanupPostPaddingSourceMaterializerSpec_of_baseAndScratch
          hreject hallocator⟩
  · rcases h.right true with ⟨allocator, hallocator⟩
    exact
      ⟨canonicalSeqDescription rightEdgeRewindDescription allocator,
        selectedProjectionPaddedTailCleanupPostPaddingSourceMaterializerSpec_of_baseAndScratch
          selectedProjectionPaddedTailCleanupAcceptBaseSourceMaterializerSpec
          hallocator⟩

theorem selectedProjectionPaddedTailCleanupPostPaddingBranchConstruction_of_sourceMaterializer
    {useAccept : Bool} {materializer : MachineDescription}
    (hmaterializer :
      SelectedProjectionPaddedTailCleanupPostPaddingSourceMaterializerSpec
        useAccept materializer) :
    SelectedProjectionPaddedTailCleanupPostPaddingBranchConstruction
      useAccept := by
  refine
    ⟨canonicalSeqDescription materializer
        (selectedProjectionPaddedTailCleanupSourceToEquivOutputDescription
          useAccept), ?_⟩
  constructor
  · exact
      canonicalSeqDescription_subroutineReady
        hmaterializer.left
        (selectedProjectionPaddedTailCleanupSourceToEquivOutputDescription_subroutineReady
          useAccept)
  · intro L
    exact
      canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        hmaterializer.left
        (selectedProjectionPaddedTailCleanupSourceToEquivOutputDescription_subroutineReady
          useAccept)
        (hmaterializer.right L)
        (selectedProjectionPaddedTailCleanupLayoutScratchSourceTape_move_left_move_right
          useAccept L)
        (selectedProjectionPaddedTailCleanupSourceToEquivOutputDescription_haltsFrom_layoutScratchSource
          useAccept L)

theorem selectedProjectionPaddedTailCleanupPostPaddingConstruction_of_sourceMaterializers
    (hmaterializers :
      SelectedProjectionPaddedTailCleanupPostPaddingSourceMaterializerConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingConstruction := by
  intro useAccept
  rcases hmaterializers useAccept with
    ⟨materializer, hmaterializer⟩
  exact
    selectedProjectionPaddedTailCleanupPostPaddingBranchConstruction_of_sourceMaterializer
      hmaterializer

/--
Combined post-padding finite-machine leaf for selected-projection tail cleanup.
The branch wrappers below project this single obligation into the accepting and
rejecting branch contracts.
-/
theorem selectedProjectionPaddedTailCleanupPostPaddingCoreConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingConstruction := by
  exact
    selectedProjectionPaddedTailCleanupPostPaddingConstruction_of_sourceMaterializers
      (selectedProjectionPaddedTailCleanupPostPaddingSourceMaterializerConstruction_of_baseAndScratch
        (by
          refine
            ⟨⟨canonicalSeqDescription
                selectedHitOtherFlagErasedRejectToRightEndDescription
                selectedProjectionPaddedTailCleanupRejectRightEndToBaseSourceDescription,
              selectedProjectionPaddedTailCleanupRejectBaseSourceMaterializerSpec⟩,
              ?_⟩
          sorry))

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
