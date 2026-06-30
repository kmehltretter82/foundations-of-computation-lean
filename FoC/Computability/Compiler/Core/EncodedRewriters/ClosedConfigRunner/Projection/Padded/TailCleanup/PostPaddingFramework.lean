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
        htail, htailEq, List.append_assoc]

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

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
