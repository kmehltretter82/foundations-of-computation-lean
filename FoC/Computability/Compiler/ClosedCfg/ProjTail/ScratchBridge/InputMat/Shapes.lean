import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMatContracts

set_option doc.verso true

/-!
# Count-window input materializer shapes

Closed-form shape and padding lemmas for the count-window structured input
materializer. This module names
the intermediate tapes, proves the branch padding closed forms, and decomposes
the guarded three-tape target into per-segment cell words for the exact machine
phase specifications.

The numeric closed forms used by the later machine phases are proved below.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

open CanonicalLayouts.DovetailLayoutScanner

namespace InputMat

/-! ## Replicate helpers -/

theorem replicate_none_two_cons (n : Nat) :
    none :: none :: List.replicate n (none : Option Bool) =
      List.replicate (n + 2) (none : Option Bool) := by
  rw [show n + 2 = (n + 1) + 1 from rfl, List.replicate_succ,
    List.replicate_succ]

theorem cons_none_replicate_append
    (k : Nat) (suffix : List (Option Bool)) :
    none ::
        List.append (List.replicate k (none : Option Bool)) suffix =
      List.append (List.replicate (k + 1) (none : Option Bool)) suffix := by
  rw [List.replicate_succ]
  rfl

/-! ## Branch source-padding closed forms

The accept-branch padding is uniformly a blank run of length
{lit}`deletedTail.length + 7`; the reject-branch padding is a blank run of
length {lit}`deletedTail.length + 4` followed by the visible selected-hit cell
code and a final two-blank boundary.  Both closed forms hold for every
deleted tail, including the nil arm, which collapses to the same form.
-/

theorem sourcePadding_accept_closedForm
    (L : DovetailLayout) (deletedTail : Word Bool) :
    countWindowPostFieldDecodedPrefixStructuredSourcePadding
        true L deletedTail =
      List.replicate (deletedTail.length + 7) (none : Option Bool) := by
  cases deletedTail with
  | nil => rfl
  | cons deletedHead deletedRest =>
      have hrep4 :
          ([none, none, none, none] : List (Option Bool)) =
            List.replicate 4 (none : Option Bool) := rfl
      have hgap :
          postFieldHandoffAfterSentinelGapPadding
              (deletedHead :: deletedRest)
              [none, none, none, none, none] =
            none :: none ::
              List.append
                (List.replicate deletedRest.length (none : Option Bool))
                [none, none, none, none] := by
        have h :=
          sentinelGapCompactorFinalPadding_cons_cons_right
            deletedRest.length 0 [none, none, none, none]
        simpa [postFieldHandoffAfterSentinelGapPadding,
          sentinelGapCompactorFinalPadding, List.length_cons,
          Nat.zero_add] using h
      calc
        countWindowPostFieldDecodedPrefixStructuredSourcePadding
            true L (deletedHead :: deletedRest) =
            none :: none ::
              leadingBlankLeftShiftTargetVisiblePadding
                (postFieldHandoffAfterSentinelGapPadding
                  (deletedHead :: deletedRest)
                  [none, none, none, none, none]) := rfl
        _ = none :: none ::
              leadingBlankLeftShiftTargetVisiblePadding
                (none :: none ::
                  List.append
                    (List.replicate deletedRest.length (none : Option Bool))
                    [none, none, none, none]) := by
            rw [hgap]
        _ = none :: none :: none :: none ::
              List.append
                (List.replicate deletedRest.length (none : Option Bool))
                [none, none, none, none] := rfl
        _ = none :: none :: none :: none ::
              List.replicate (deletedRest.length + 4) (none : Option Bool) := by
            rw [hrep4, replicate_none_append_replicate_none]
        _ = none :: none ::
              List.replicate (deletedRest.length + 4 + 2)
                (none : Option Bool) := by
            rw [replicate_none_two_cons]
        _ = List.replicate (deletedRest.length + 4 + 2 + 2)
              (none : Option Bool) := by
            rw [replicate_none_two_cons]
        _ = List.replicate ((deletedHead :: deletedRest).length + 7)
              (none : Option Bool) := by
            rfl

theorem sourcePadding_reject_closedForm
    (L : DovetailLayout) (deletedTail : Word Bool) :
    countWindowPostFieldDecodedPrefixStructuredSourcePadding
        false L deletedTail =
      List.append
        (List.replicate (deletedTail.length + 4) (none : Option Bool))
        (List.append
          ((selectedProjectionPaddedTailCleanupSelectedHitBits
            false L).map some)
          [none, none]) := by
  cases deletedTail with
  | nil =>
      show none ::
          leadingBlankLeftShiftTargetVisiblePadding
            (rejectPostFieldHandoffPostGapPadding L []) = _
      rw [rejectPostFieldHandoffPostGapPadding,
        rejectPostFieldHandoffRightPadding]
      show none :: none :: none :: none ::
          List.append
            ((selectedProjectionPaddedTailCleanupSelectedHitBits
              false L).map some)
            [none, none] = _
      rw [List.length_nil]
      rfl
  | cons deletedHead deletedRest =>
      have hgap :
          postFieldHandoffAfterSentinelGapPadding
              (deletedHead :: deletedRest)
              (rejectPostFieldHandoffRightPadding L) =
            none :: none ::
              List.append
                (List.replicate deletedRest.length (none : Option Bool))
                (none :: none ::
                  List.append
                    ((selectedProjectionPaddedTailCleanupSelectedHitBits
                      false L).map some)
                    [none, none]) := by
        have h :=
          sentinelGapCompactorFinalPadding_cons_cons_right
            deletedRest.length 0
            (none :: none ::
              List.append
                ((selectedProjectionPaddedTailCleanupSelectedHitBits
                  false L).map some)
                [none, none])
        simpa [postFieldHandoffAfterSentinelGapPadding,
          rejectPostFieldHandoffRightPadding,
          sentinelGapCompactorFinalPadding, List.length_cons,
          List.replicate, Nat.zero_add] using h
      calc
        countWindowPostFieldDecodedPrefixStructuredSourcePadding
            false L (deletedHead :: deletedRest) =
            none ::
              leadingBlankLeftShiftTargetVisiblePadding
                (postFieldHandoffAfterSentinelGapPadding
                  (deletedHead :: deletedRest)
                  (rejectPostFieldHandoffRightPadding L)) := rfl
        _ = none ::
              leadingBlankLeftShiftTargetVisiblePadding
                (none :: none ::
                  List.append
                    (List.replicate deletedRest.length (none : Option Bool))
                    (none :: none ::
                      List.append
                        ((selectedProjectionPaddedTailCleanupSelectedHitBits
                          false L).map some)
                        [none, none])) := by
            rw [hgap]
        _ = none :: none :: none ::
              List.append
                (List.replicate deletedRest.length (none : Option Bool))
                (none :: none ::
                  List.append
                    ((selectedProjectionPaddedTailCleanupSelectedHitBits
                      false L).map some)
                    [none, none]) := rfl
        _ = none :: none :: none ::
              List.append
                (List.replicate deletedRest.length (none : Option Bool))
                (List.append (List.replicate 2 (none : Option Bool))
                  (List.append
                    ((selectedProjectionPaddedTailCleanupSelectedHitBits
                      false L).map some)
                    [none, none])) := rfl
        _ = none :: none :: none ::
              List.append
                (List.append
                  (List.replicate deletedRest.length (none : Option Bool))
                  (List.replicate 2 (none : Option Bool)))
                (List.append
                  ((selectedProjectionPaddedTailCleanupSelectedHitBits
                    false L).map some)
                  [none, none]) := by
            exact
              congrArg (fun cells => none :: none :: none :: cells)
                (List.append_assoc
                  (List.replicate deletedRest.length (none : Option Bool))
                  (List.replicate 2 (none : Option Bool))
                  (List.append
                    ((selectedProjectionPaddedTailCleanupSelectedHitBits
                      false L).map some)
                    [none, none])).symm
        _ = none :: none :: none ::
              List.append
                (List.replicate (deletedRest.length + 2) (none : Option Bool))
                (List.append
                  ((selectedProjectionPaddedTailCleanupSelectedHitBits
                    false L).map some)
                  [none, none]) := by
            rw [replicate_none_append_replicate_none]
        _ = none :: none ::
              List.append
                (List.replicate (deletedRest.length + 2 + 1)
                  (none : Option Bool))
                (List.append
                  ((selectedProjectionPaddedTailCleanupSelectedHitBits
                    false L).map some)
                  [none, none]) := by
            rw [cons_none_replicate_append]
        _ = none ::
              List.append
                (List.replicate (deletedRest.length + 2 + 1 + 1)
                  (none : Option Bool))
                (List.append
                  ((selectedProjectionPaddedTailCleanupSelectedHitBits
                    false L).map some)
                  [none, none]) := by
            rw [cons_none_replicate_append]
        _ = List.append
              (List.replicate (deletedRest.length + 2 + 1 + 1 + 1)
                (none : Option Bool))
              (List.append
                ((selectedProjectionPaddedTailCleanupSelectedHitBits
                  false L).map some)
                [none, none]) := by
            rw [cons_none_replicate_append]
        _ = List.append
              (List.replicate ((deletedHead :: deletedRest).length + 4)
                (none : Option Bool))
              (List.append
                ((selectedProjectionPaddedTailCleanupSelectedHitBits
                  false L).map some)
                [none, none]) := by
            rfl

/-! ## Field-width closed forms -/

theorem selectedHitBits_length
    (useAccept : Bool) (L : DovetailLayout) :
    (selectedProjectionPaddedTailCleanupSelectedHitBits
        useAccept L).length = 4 := by
  cases useAccept with
  | false =>
      cases hb : L.rejectHit <;>
        simp [selectedProjectionPaddedTailCleanupSelectedHitBits, hb,
          boolFieldBits, cellFieldBits, cellCodeBits, encodeCell,
          encodeCodeWordAsInput, encodeCodeSymbolAsInput]
  | true =>
      cases hb : L.acceptHit <;>
        simp [selectedProjectionPaddedTailCleanupSelectedHitBits, hb,
          boolFieldBits, cellFieldBits, cellCodeBits, encodeCell,
          encodeCodeWordAsInput, encodeCodeSymbolAsInput]


theorem cellCodeBits_length (cell : Option Bool) :
    (cellCodeBits cell).length = 4 := by
  cases cell with
  | none => rfl
  | some bit => cases bit <;> rfl


/-! ## Source word and source tape shape -/

/--
The visible source word: header code, the encoded Boolean-word field for the
parsed layout bits, then the boundary bit and the branch suffix tail.  The
branch source tape is exactly this word in right-edge rewind position over the
branch source padding.
-/
def sourceWord (useAccept : Bool) (L : DovetailLayout) : Word Bool :=
  List.append boolWordRawBitsDecoderHeaderBits
    (List.append
      (boolWordRawBitsDecoderEncodedFieldBits (ParsedLayoutBits L))
      (false ::
        countWindowPostFieldDecodedPrefixStructuredSuffixTail useAccept L))

theorem sourceWord_cons
    (useAccept : Bool) (L : DovetailLayout) :
    sourceWord useAccept L =
      false ::
        List.append [false, false, false]
          (List.append
            (boolWordRawBitsDecoderEncodedFieldBits (ParsedLayoutBits L))
            (false ::
              countWindowPostFieldDecodedPrefixStructuredSuffixTail
                useAccept L)) := rfl


/-! ## Output-buffer scan padding decomposition (P4 ground truth) -/

theorem postFieldDecodedPrefixScanPadding_accept_decomp
    (L : DovetailLayout) :
    postFieldDecodedPrefixScanPadding true L =
      none ::
        List.append
          (List.replicate
            (selectedProjectionPaddedTailCleanupScratchCountBits
              true L).length
            (none : Option Bool))
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              L.stage).map some)
            (List.append
              ((selectedProjectionPaddedTailCleanupSelectedConfigBits
                true L).map some)
              (List.append
                ((selectedProjectionPaddedTailCleanupUnselectedConfigBits
                  true L).map some)
                (List.append
                  ((selectedProjectionPaddedTailCleanupSelectedHitBits
                    true L).map some)
                  (none :: List.replicate 5 (none : Option Bool)))))) := by
  simp [postFieldDecodedPrefixScanPadding,
    selectedProjectionPaddedTailCleanupPostCountTailCells,
    selectedProjectionPaddedTailCleanupAcceptPostCountTailCells,
    selectedProjectionPaddedTailCleanupAcceptAfterStageTailCells]

theorem postFieldDecodedPrefixScanPadding_reject_decomp
    (L : DovetailLayout) :
    postFieldDecodedPrefixScanPadding false L =
      none ::
        List.append
          (List.replicate
            (selectedProjectionPaddedTailCleanupScratchCountBits
              false L).length
            (none : Option Bool))
          (List.append
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
                    [none, none]))))) := by
  simp [postFieldDecodedPrefixScanPadding,
    selectedProjectionPaddedTailCleanupPostCountTailCells,
    selectedProjectionPaddedTailCleanupRejectPostCountTailCells,
    selectedProjectionPaddedTailCleanupRejectAfterStageTailCells]

theorem scratchCountBits_length
    (useAccept : Bool) (L : DovetailLayout) :
    (selectedProjectionPaddedTailCleanupScratchCountBits
        useAccept L).length =
      (ParsedLayoutBits L).length -
        selectedProjectionPaddedTailCleanupSentinelBaseScratch useAccept L := by
  simp [selectedProjectionPaddedTailCleanupScratchCountBits]

/-! ## Parsed-layout field decomposition (P1 block arithmetic)

The parsed layout bits split into seven contiguous self-delimiting fields:
transition prefix, input Boolean word, stage number, accept configuration,
reject configuration, accept hit flag, and reject hit flag.  The measure
passes recover the accept-config field width (hence the invisible accept
padding length) and the unselected-config field width from this structure.
-/

theorem boolFieldBits_append_nil
    (b : Bool) (suffixBits : Word Bool) :
    List.append (boolFieldBits b []) suffixBits =
      boolFieldBits b suffixBits := by
  exact cellFieldBits_append_nil (some b) suffixBits

theorem boolWordFieldBits_append_nil
    (w : Word Bool) (suffixBits : Word Bool) :
    List.append (boolWordFieldBits w []) suffixBits =
      boolWordFieldBits w suffixBits := by
  simp [boolWordFieldBits, cellListFieldBits, List.append_assoc]

theorem parsedLayoutBits_fieldDecomp (L : DovetailLayout) :
    ParsedLayoutBits L =
      List.append transitionPrefixBits
        (List.append (boolWordFieldBits L.input [])
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              L.stage)
            (List.append (configurationFieldBits L.acceptConfig [])
              (List.append (configurationFieldBits L.rejectConfig [])
                (List.append (boolFieldBits L.acceptHit [])
                  (boolFieldBits L.rejectHit [])))))) := by
  rw [parsedLayoutBits_eq_dovetailLayoutFieldBits_nil]
  symm
  rw [boolFieldBits_append_nil, configurationFieldBits_append_nil,
    configurationFieldBits_append_nil, boolWordFieldBits_append_nil]
  rfl

theorem transitionPrefixBits_length : transitionPrefixBits.length = 4 := rfl

theorem cellsCodeBits_length (cells : List (Option Bool)) :
    (cellsCodeBits cells).length = 4 * cells.length := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
      simp [cellsCodeBits, cellCodeBits_length, ih, List.length_cons,
        Nat.mul_add, Nat.add_comm]

theorem cellsCodeBits_append (a b : List (Option Bool)) :
    cellsCodeBits (List.append a b) =
      List.append (cellsCodeBits a) (cellsCodeBits b) := by
  induction a with
  | nil => rfl
  | cons cell rest ih =>
      show List.append (cellCodeBits cell)
          (cellsCodeBits (List.append rest b)) = _
      rw [ih]
      exact
        (List.append_assoc (cellCodeBits cell) (cellsCodeBits rest)
          (cellsCodeBits b)).symm

theorem boolWordFieldBits_nil_length (w : Word Bool) :
    (boolWordFieldBits w []).length = 8 * w.length + 4 := by
  simp [boolWordFieldBits, cellListFieldBits, cellsCodeBits_length,
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_length]
  lia

theorem boolFieldBits_nil_length (b : Bool) :
    (boolFieldBits b []).length = 4 := by
  cases b <;> rfl

theorem configurationFieldBits_nil_length (cfg : Configuration) :
    (configurationFieldBits cfg []).length =
      4 * cfg.state + 8 * cfg.tape.left.length +
        8 * cfg.tape.right.length + 16 := by
  simp [configurationFieldBits, tapeFieldBits, cellListFieldBits,
    cellFieldBits, cellsCodeBits_length, cellCodeBits_length,
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_length]
  lia

theorem acceptConfigField_length_of_hdeleted
    {L : DovetailLayout} {deletedTail : Word Bool}
    (hdeleted :
      configurationFieldBits L.acceptConfig [] = false :: deletedTail) :
    (configurationFieldBits L.acceptConfig []).length =
      deletedTail.length + 1 := by
  rw [hdeleted, List.length_cons]

theorem parsedLayoutBits_length (L : DovetailLayout) :
    (ParsedLayoutBits L).length =
      8 * L.input.length + 4 * L.stage +
        (configurationFieldBits L.acceptConfig []).length +
        (configurationFieldBits L.rejectConfig []).length + 20 := by
  rw [parsedLayoutBits_fieldDecomp]
  simp [transitionPrefixBits_length, boolWordFieldBits_nil_length,
    boolFieldBits_nil_length,
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_length]
  lia

end InputMat

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
