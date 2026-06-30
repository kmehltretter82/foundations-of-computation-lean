import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.SentinelGapCompactor
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.PostErase

set_option doc.verso true

/-!
# Framework-backed post-padding cleanup adapters

This module keeps the selected-projection post-padding integration work out of
{module}`FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.PostErase`,
which is already near the repository's large-file threshold.  It instantiates
the reusable sentinel-bounded right-end compactor on the first selected
projection branch.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncodedRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

theorem selectedProjectionPaddedTailCleanupKeptPrefix_true_append_last
    (L : DovetailLayout) :
    exists pref : Word Bool,
    exists leftBit : Bool,
      selectedProjectionPaddedTailCleanupKeptPrefixBits true L =
        List.append pref [leftBit] := by
  rcases
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_cons_false
        L.acceptConfig [] with
    ⟨tail, htail⟩
  cases hrev : tail.reverse with
  | nil =>
      have htailNil : tail = [] := by
        simpa using congrArg List.reverse hrev
      refine ⟨selectedProjectionPaddedTailCleanupPrefixBits L, false, ?_⟩
      rw [selectedProjectionPaddedTailCleanupKeptPrefixBits]
      simp [selectedProjectionPaddedTailCleanupSelectedConfigBits,
        htail, htailNil]
  | cons bit rest =>
      refine
        ⟨List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
          (false :: rest.reverse), bit, ?_⟩
      have htailEq : tail = List.append rest.reverse [bit] := by
        rw [← List.reverse_reverse tail]
        rw [hrev]
        simp
      rw [selectedProjectionPaddedTailCleanupKeptPrefixBits]
      simp [selectedProjectionPaddedTailCleanupSelectedConfigBits,
        htail, htailEq]

theorem selectedProjectionPaddedTailCleanupSelectedHit_true_reverse_cons
    (L : DovetailLayout) :
    exists current : Bool,
    exists leftRest : Word Bool,
      (selectedProjectionPaddedTailCleanupSelectedHitBits true L).reverse =
        current :: leftRest := by
  by_cases h : L.acceptHit
  · refine ⟨false, [true, true, false], ?_⟩
    simp [selectedProjectionPaddedTailCleanupSelectedHitBits,
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
      encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput, h]
  · refine ⟨true, [false, true, false], ?_⟩
    simp [selectedProjectionPaddedTailCleanupSelectedHitBits,
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
      encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput, h]

theorem selectedProjectionPaddedTailCleanupSelectedConfig_false_append_last
    (L : DovetailLayout) :
    exists pref : Word Bool,
    exists leftBit : Bool,
      selectedProjectionPaddedTailCleanupSelectedConfigBits false L =
        List.append pref [leftBit] := by
  rcases
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_cons_false
        L.rejectConfig [] with
    ⟨tail, htail⟩
  cases hrev : tail.reverse with
  | nil =>
      have htailNil : tail = [] := by
        simpa using congrArg List.reverse hrev
      refine ⟨[], false, ?_⟩
      simp [selectedProjectionPaddedTailCleanupSelectedConfigBits,
        htail, htailNil]
  | cons bit rest =>
      refine ⟨false :: rest.reverse, bit, ?_⟩
      have htailEq : tail = List.append rest.reverse [bit] := by
        rw [← List.reverse_reverse tail]
        rw [hrev]
        simp
      simp [selectedProjectionPaddedTailCleanupSelectedConfigBits,
        htail, htailEq]

theorem selectedProjectionPaddedTailCleanupStageBits_append_last
    (stage : Nat) :
    exists pref : Word Bool,
    exists leftBit : Bool,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage =
        List.append pref [leftBit] := by
  rcases SelectedProjectionTailProjector.stageNatBits_cons_cons stage with
    ⟨first, second, rest, hstage⟩
  cases hrev : (second :: rest).reverse with
  | nil =>
      simp at hrev
  | cons bit revRest =>
      refine ⟨first :: revRest.reverse, bit, ?_⟩
      have htail :
          second :: rest = List.append revRest.reverse [bit] := by
        rw [← List.reverse_reverse (second :: rest)]
        rw [hrev]
        simp
      rw [hstage, htail]
      simp

theorem selectedProjectionPaddedTailCleanupPrefix_append_last
    (L : DovetailLayout) :
    exists pref : Word Bool,
    exists leftBit : Bool,
      selectedProjectionPaddedTailCleanupPrefixBits L =
        List.append pref [leftBit] := by
  rcases selectedProjectionPaddedTailCleanupStageBits_append_last
      L.stage with
    ⟨stagePref, leftBit, hstage⟩
  refine
    ⟨List.append (SelectedProjectionTailProjector.outputPrefixBits L)
      stagePref, leftBit, ?_⟩
  rw [selectedProjectionPaddedTailCleanupPrefixBits, hstage]
  simp [List.append_assoc]

theorem selectedProjectionPaddedTailCleanupSelectedHit_false_reverse_cons
    (L : DovetailLayout) :
    exists current : Bool,
    exists leftRest : Word Bool,
      (selectedProjectionPaddedTailCleanupSelectedHitBits false L).reverse =
        current :: leftRest := by
  by_cases h : L.rejectHit
  · refine ⟨false, [true, true, false], ?_⟩
    simp [selectedProjectionPaddedTailCleanupSelectedHitBits,
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
      encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput, h]
  · refine ⟨true, [false, true, false], ?_⟩
    simp [selectedProjectionPaddedTailCleanupSelectedHitBits,
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
      encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput, h]

theorem selectedProjectionPaddedTailCleanupDeletedAcceptRightEnd_sentinelCompactor_haltsFrom
    (L : DovetailLayout) :
    sentinelRightEndGapCompactorDescription.HaltsFromTape
      (rightEndCompactionSourceTape
        (selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells L))
      (leadingBlankLeftShiftTargetTapeWithPadding []
        (selectedProjectionPaddedTailCleanupTargetBits true L)
        (none :: sentinelGapCompactorFinalPadding
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits
            true L).length.pred
          5 [])) := by
  rcases selectedProjectionPaddedTailCleanupKeptPrefix_true_append_last
      L with
    ⟨pref, leftBit, hpref⟩
  rcases selectedProjectionPaddedTailCleanupSelectedHit_true_reverse_cons
      L with
    ⟨current, leftRest, hhitRev⟩
  rcases
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_cons_false
        L.rejectConfig [] with
    ⟨deletedTail, hdeleted⟩
  have hhit : (current :: leftRest).reverse =
      selectedProjectionPaddedTailCleanupSelectedHitBits true L := by
    rw [← hhitRev]
    simp
  have hdeleteLen :
      (selectedProjectionPaddedTailCleanupUnselectedConfigBits true L).length =
        Nat.succ deletedTail.length := by
    simp [selectedProjectionPaddedTailCleanupUnselectedConfigBits,
      hdeleted]
  have htargetBits :
      selectedProjectionPaddedTailCleanupTargetBits true L =
        List.append pref (leftBit :: (current :: leftRest).reverse) := by
    rw [selectedProjectionPaddedTailCleanupTargetBits_eq_kept,
      hpref, selectedProjectionPaddedTailCleanupKeptSuffixBits, hhit]
    simp [List.append_assoc]
  have hsourceCells :
      selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells L =
        rightEndSentinelGapCompactorSourceLeftCells
          (List.append (pref.reverse.map some) [none])
          leftBit current leftRest deletedTail.length 5 := by
    rw [rightEndSentinelGapCompactorSourceLeftCells_eq_split]
    rw [selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells]
    rw [hdeleteLen]
    rw [← hhit]
    rw [← hpref]
    simp [selectedProjectionPaddedTailCleanupKeptPrefixBits,
      List.map_append, List.append_assoc]
  have hrun :=
    sentinelRightEndGapCompactorDescription_haltsFrom_rightEndGapSource
      deletedTail.length pref leftBit current leftRest 3
  rw [hdeleteLen, htargetBits, hsourceCells]
  simpa using hrun

def selectedProjectionPaddedTailCleanupDeletedRejectFixedGapClosedLeftCells
    (L : DovetailLayout) : List (Option Bool) :=
  List.append [none]
    (List.append
      ((selectedProjectionPaddedTailCleanupPrefixBits L).map some)
      (List.append
        (List.replicate
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits
            false L).length
          (none : Option Bool))
        (List.append
          ((List.append
            (selectedProjectionPaddedTailCleanupSelectedConfigBits
              false L)
            (selectedProjectionPaddedTailCleanupSelectedHitBits
              false L)).map some)
          [none, none])))

theorem selectedProjectionPaddedTailCleanupDeletedRejectRightEnd_fixedGap_sentinelCompactor_haltsFrom
    (L : DovetailLayout) :
    sentinelGapCompactorDescription.HaltsFromTape
      (rightEndCompactionSourceTape
        (selectedProjectionPaddedTailCleanupDeletedRejectRightEndLeftCells L))
      (rightEndCompactionSourceTapeWithRightPadding
        (selectedProjectionPaddedTailCleanupDeletedRejectFixedGapClosedLeftCells
          L)
        (List.replicate 3 (none : Option Bool))) := by
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
      rightEndCompactionSourceTape
          (selectedProjectionPaddedTailCleanupDeletedRejectRightEndLeftCells
            L) =
        rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
          (rightBlankLocalGapBaseLeft 3 (some leftBit :: baseTail))
          current leftRest 0 [] := by
    simp [rightBlankLocalGapCompactorSourceTapeWithBaseAndRight,
      rightEndCompactionSourceTape,
      selectedProjectionPaddedTailCleanupDeletedRejectRightEndLeftCells,
      rightBlankLocalGapBaseLeft, baseTail, hcfg, ← hhit,
      tapeAtCells, List.reverse_append, List.map_reverse,
      List.map_append, List.append_assoc]
  have htarget :
      rightEndCompactionSourceTapeWithRightPadding
          (selectedProjectionPaddedTailCleanupDeletedRejectFixedGapClosedLeftCells
            L)
          (List.replicate 3 (none : Option Bool)) =
        leadingBlankLeftShiftTargetTapeWithPadding
          (some leftBit :: baseTail) (current :: leftRest).reverse
          (sentinelGapCompactorFinalPadding 3 0 []) := by
    simp [rightEndCompactionSourceTapeWithRightPadding,
      selectedProjectionPaddedTailCleanupDeletedRejectFixedGapClosedLeftCells,
      leadingBlankLeftShiftTargetTapeWithPadding, baseTail, hcfg,
      ← hhit, sentinelGapCompactorFinalPadding, tapeAtCells,
      List.reverse_append, List.map_reverse, List.map_append,
      List.append_assoc]
  rw [hsource, htarget]
  exact
    sentinelGapCompactorDescription_haltsFromTape_gapBase_zero
      3 baseTail leftBit current leftRest

theorem selectedProjectionPaddedTailCleanupDeletedRejectFixedGapClosed_sentinelCompactor_haltsFrom
    (L : DovetailLayout) :
    sentinelRightEndGapCompactorDescription.HaltsFromTape
      (rightEndCompactionSourceTapeWithRightPadding
        (selectedProjectionPaddedTailCleanupDeletedRejectFixedGapClosedLeftCells
          L)
        (List.replicate 3 (none : Option Bool)))
      (leadingBlankLeftShiftTargetTapeWithPadding []
        (selectedProjectionPaddedTailCleanupTargetBits false L)
        (none :: sentinelGapCompactorFinalPadding
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits
            false L).length.pred
          2 (List.replicate 3 (none : Option Bool)))) := by
  rcases selectedProjectionPaddedTailCleanupPrefix_append_last L with
    ⟨pref, leftBit, hpref⟩
  rcases
      selectedProjectionPaddedTailCleanupSelectedHit_false_reverse_cons
        L with
    ⟨current, hitLeftRest, hhitRev⟩
  rcases
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_cons_false
        L.acceptConfig [] with
    ⟨deletedTail, hdeleted⟩
  let payload : Word Bool :=
    List.append
      (selectedProjectionPaddedTailCleanupSelectedConfigBits false L)
      (selectedProjectionPaddedTailCleanupSelectedHitBits false L)
  let leftRest : Word Bool :=
    List.append hitLeftRest
      (selectedProjectionPaddedTailCleanupSelectedConfigBits false L).reverse
  have hpayload :
      (current :: leftRest).reverse = payload := by
    have hhit :
        hitLeftRest.reverse ++ [current] =
          selectedProjectionPaddedTailCleanupSelectedHitBits false L := by
      rw [←
        List.reverse_reverse
          (selectedProjectionPaddedTailCleanupSelectedHitBits false L)]
      rw [hhitRev]
      simp
    change
      (current ::
          List.append hitLeftRest
            (selectedProjectionPaddedTailCleanupSelectedConfigBits
              false L).reverse).reverse =
        List.append
          (selectedProjectionPaddedTailCleanupSelectedConfigBits false L)
          (selectedProjectionPaddedTailCleanupSelectedHitBits false L)
    rw [List.reverse_cons]
    simp [List.reverse_append, hhit, List.append_assoc]
  have hdeleteLen :
      (selectedProjectionPaddedTailCleanupUnselectedConfigBits
        false L).length =
        Nat.succ deletedTail.length := by
    simp [selectedProjectionPaddedTailCleanupUnselectedConfigBits,
      hdeleted]
  have htargetBits :
      selectedProjectionPaddedTailCleanupTargetBits false L =
        List.append pref (leftBit :: (current :: leftRest).reverse) := by
    rw [selectedProjectionPaddedTailCleanupTargetBits_eq_selectedFields,
      hpref, hpayload]
    simp [payload, List.append_assoc]
  have hsourceCells :
      selectedProjectionPaddedTailCleanupDeletedRejectFixedGapClosedLeftCells
          L =
        rightEndSentinelGapCompactorSourceLeftCells
          (List.append (pref.reverse.map some) [none])
          leftBit current leftRest deletedTail.length 2 := by
    rw [rightEndSentinelGapCompactorSourceLeftCells_eq_split]
    rw [selectedProjectionPaddedTailCleanupDeletedRejectFixedGapClosedLeftCells]
    rw [hdeleteLen, hpayload, ← hpref]
    simp [payload, List.map_append, List.append_assoc]
  have hrun :=
    sentinelRightEndGapCompactorDescription_haltsFrom_rightEndGapSourceWithRightPadding
      deletedTail.length pref leftBit current leftRest 0
      (List.replicate 3 (none : Option Bool))
  rw [hdeleteLen, htargetBits, hsourceCells]
  simpa using hrun

theorem selectedProjectionPaddedTailCleanupDeletedAcceptRightEnd_sentinelCompactor_haltsFrom_withRightPadding
    (L : DovetailLayout) (rightPadding : List (Option Bool)) :
    sentinelRightEndGapCompactorDescription.HaltsFromTape
      (rightEndCompactionSourceTapeWithRightPadding
        (selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells L)
        rightPadding)
      (leadingBlankLeftShiftTargetTapeWithPadding []
        (selectedProjectionPaddedTailCleanupTargetBits true L)
        (none :: sentinelGapCompactorFinalPadding
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits
            true L).length.pred
          5 rightPadding)) := by
  rcases selectedProjectionPaddedTailCleanupKeptPrefix_true_append_last
      L with
    ⟨pref, leftBit, hpref⟩
  rcases selectedProjectionPaddedTailCleanupSelectedHit_true_reverse_cons
      L with
    ⟨current, leftRest, hhitRev⟩
  rcases
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_cons_false
        L.rejectConfig [] with
    ⟨deletedTail, hdeleted⟩
  have hhit : (current :: leftRest).reverse =
      selectedProjectionPaddedTailCleanupSelectedHitBits true L := by
    rw [← hhitRev]
    simp
  have hdeleteLen :
      (selectedProjectionPaddedTailCleanupUnselectedConfigBits true L).length =
        Nat.succ deletedTail.length := by
    simp [selectedProjectionPaddedTailCleanupUnselectedConfigBits,
      hdeleted]
  have htargetBits :
      selectedProjectionPaddedTailCleanupTargetBits true L =
        List.append pref (leftBit :: (current :: leftRest).reverse) := by
    rw [selectedProjectionPaddedTailCleanupTargetBits_eq_kept,
      hpref, selectedProjectionPaddedTailCleanupKeptSuffixBits, hhit]
    simp [List.append_assoc]
  have hsourceCells :
      selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells L =
        rightEndSentinelGapCompactorSourceLeftCells
          (List.append (pref.reverse.map some) [none])
          leftBit current leftRest deletedTail.length 5 := by
    rw [rightEndSentinelGapCompactorSourceLeftCells_eq_split]
    rw [selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells]
    rw [hdeleteLen]
    rw [← hhit]
    rw [← hpref]
    simp [selectedProjectionPaddedTailCleanupKeptPrefixBits,
      List.map_append, List.append_assoc]
  have hrun :=
    sentinelRightEndGapCompactorDescription_haltsFrom_rightEndGapSourceWithRightPadding
      deletedTail.length pref leftBit current leftRest 3 rightPadding
  rw [hdeleteLen, htargetBits, hsourceCells]
  simpa using hrun

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
