import FoC.Computability.Compiler.ClosedCfg.PostTrans.ParsedInnerTransport.CommonSchedule
import FoC.Computability.Compiler.ClosedCfg.ProjTail.PostPaddingFieldEraser

set_option doc.verso true

/-!
# Parsed-inner rejecting transport schedule

The rejecting branch first canonicalizes the accept configuration, so its
terminal sentinel can be stashed while the reject configuration is erased.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

namespace EncRewriters
namespace BoundedLayoutRunner
namespace ParsedInnerTransport

open CanonicalLayouts.DovetailLayoutScanner
open SelectedProjectionPaddedTailCleanup

def rejectPrefixBaseLeft
    (p : SelectedMergeEmitterPayload) : List (Option Bool) :=
  List.append
    ((SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p).reverse.map some)
    [none]

def rejectAfterRejectConfigSuffixBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  List.append
    (SelectedMergePaddedEmitterParsedInnerAcceptHitFieldBits p)
    (List.append
      (SelectedMergePaddedEmitterParsedInnerRejectHitFieldBits p)
      (List.append
        (SelectedMergePaddedEmitterParsedInnerOuterStageFieldBits p)
        (List.append
          (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
          (SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits p))))

def rejectAfterAcceptHitSuffixBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  List.append
    (SelectedMergePaddedEmitterParsedInnerRejectHitFieldBits p)
    (List.append
      (SelectedMergePaddedEmitterParsedInnerOuterStageFieldBits p)
      (List.append
        (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
        (SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits p)))

theorem rejectAfterRejectConfigSuffixBits_eq_acceptHit
    (p : SelectedMergeEmitterPayload) :
    rejectAfterRejectConfigSuffixBits p =
      boolFieldBits p.L.acceptHit (rejectAfterAcceptHitSuffixBits p) := by
  unfold Word
  simpa [rejectAfterRejectConfigSuffixBits,
    rejectAfterAcceptHitSuffixBits,
    SelectedMergePaddedEmitterParsedInnerAcceptHitFieldBits,
    boolFieldBits] using
      (cellFieldBits_append_nil (some p.L.acceptHit)
        (rejectAfterAcceptHitSuffixBits p))

theorem commonAfterAcceptConfigSuffixBits_eq_rejectConfig
    (p : SelectedMergeEmitterPayload) :
    commonAfterAcceptConfigSuffixBits p =
      configurationFieldBits p.L.rejectConfig
        (rejectAfterRejectConfigSuffixBits p) := by
  unfold Word
  simpa [commonAfterAcceptConfigSuffixBits,
    rejectAfterRejectConfigSuffixBits,
    SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits] using
      (configurationFieldBits_append_nil p.L.rejectConfig
        (rejectAfterRejectConfigSuffixBits p))

def rejectAfterAcceptConfigTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  Tape.move Direction.left
    (tapeAtCells
      (List.append
        ((SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits p).reverse.map some)
        (rejectPrefixBaseLeft p))
      (List.append ((commonAfterAcceptConfigSuffixBits p).map some)
        commonRightPadding))

def rejectAcceptConfigHandoffTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  tapeAtCells
    (List.append
      ((SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits p).reverse.map some)
      (rejectPrefixBaseLeft p))
    (List.append ((commonAfterAcceptConfigSuffixBits p).map some)
      commonRightPadding)

@[irreducible] def rejectThroughAcceptConfigScanDescription : MachineDescription :=
  seqSubroutine commonScheduleDescription
    SelectedMergePaddedEmitterConfigScannerDescription Direction.right

theorem rejectThroughAcceptConfigScanDescription_subroutineReady :
    rejectThroughAcceptConfigScanDescription.SubroutineReady := by
  unfold rejectThroughAcceptConfigScanDescription
  exact seqSubroutine_subroutineReady
    commonScheduleDescription_subroutineReady
    selectedMergePaddedEmitterConfigScanner_subroutineReady

theorem commonAfterStageTape_move_right_acceptConfigSource
    (p : SelectedMergeEmitterPayload) :
    Tape.move Direction.right (commonAfterStageTape p) =
      tapeAtCells (rejectPrefixBaseLeft p)
        (List.append ((commonAfterStageSuffixBits p).map some)
          commonRightPadding) := by
  rcases
      configurationFieldBits_cons_false p.L.acceptConfig
        (commonAfterAcceptConfigSuffixBits p) with
    ⟨suffixTail, hsuffix⟩
  rw [commonAfterStageTape, commonAfterStageSuffixBits_eq_acceptConfig, hsuffix]
  rw [CanonicalLayouts.DovetailStagePrefix.nonemptyNatSuffixHandoffConfigWithBaseAndRight_move_right]
  rw [commonStageRestoredBase_eq_outputPrefix_reverse_append_none]
  rfl

theorem rejectAcceptConfigScan_haltsFrom
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterConfigScannerDescription.HaltsFromTape
      (tapeAtCells (rejectPrefixBaseLeft p)
        (List.append ((commonAfterStageSuffixBits p).map some)
          commonRightPadding))
      (rejectAfterAcceptConfigTape p) := by
  rcases
      configurationFieldBits_cons_false p.L.rejectConfig
        (rejectAfterRejectConfigSuffixBits p) with
    ⟨suffixTail, hsuffix⟩
  have hright :
      commonAfterAcceptConfigSuffixBits p = false :: suffixTail := by
    rw [commonAfterAcceptConfigSuffixBits_eq_rejectConfig]
    exact hsuffix
  have hsourceBits :
      commonAfterStageSuffixBits p =
        configurationFieldBits p.L.acceptConfig (false :: suffixTail) := by
    rw [commonAfterStageSuffixBits_eq_acceptConfig, hright]
  have hrestoredLeft :
      cellListCanonicalRestoredLeftWithBase p.L.acceptConfig.tape.right
          (List.append
            ((cellCodeBits p.L.acceptConfig.tape.head).reverse.map some)
            (cellListCanonicalRestoredLeftWithBase p.L.acceptConfig.tape.left
              (List.append
                ((stageNatBits p.L.acceptConfig.state).reverse.map some)
                (rejectPrefixBaseLeft p)))) =
        List.append
          ((configurationFieldBits p.L.acceptConfig []).reverse.map some)
          (rejectPrefixBaseLeft p) := by
    rw [← configurationRestoredLeftWithBase_eq_fieldBits_reverse_append]
    rfl
  rcases
      run_configurationSuffix_raw_to_handoff_withBaseAndRight
        p.L.acceptConfig (rejectPrefixBaseLeft p)
        suffixTail commonRightPadding with
    ⟨steps, hsteps⟩
  have htarget :
      (cellListCanonicalHandoffConfigWithBaseAndRight
        p.L.acceptConfig.tape.right
        (List.append
          ((cellCodeBits p.L.acceptConfig.tape.head).reverse.map some)
          (cellListCanonicalRestoredLeftWithBase p.L.acceptConfig.tape.left
            (List.append
              ((stageNatBits p.L.acceptConfig.state).reverse.map some)
              (rejectPrefixBaseLeft p))))
        (false :: suffixTail) commonRightPadding).tape =
          rejectAfterAcceptConfigTape p := by
    rw [cellListCanonicalHandoffConfigWithBaseAndRight, hrestoredLeft]
    simp [rejectAfterAcceptConfigTape,
      SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits,
      hright, CommonGround.FiniteTransducers.tapeAtCells,
      DovetailInitialLayoutInitializer.tapeAtCells,
      List.map_append, List.map_reverse, List.append_assoc]
  refine ⟨steps, ?_⟩
  constructor
  · simpa [MachineDescription.HaltsFromTapeIn,
      SelectedMergePaddedEmitterConfigScannerDescription,
      hsourceBits,
      DovetailInitialLayoutInitializer.config,
      List.map_append, List.append_assoc] using!
        congrArg Configuration.state hsteps
  · exact Eq.trans
      (by simpa [MachineDescription.HaltsFromTapeIn,
        SelectedMergePaddedEmitterConfigScannerDescription,
        hsourceBits,
        DovetailInitialLayoutInitializer.config,
        List.map_append, List.append_assoc] using!
          congrArg Configuration.tape hsteps)
      htarget

set_option maxHeartbeats 1000000 in
theorem rejectThroughAcceptConfigScanDescription_haltsFrom
    (p : SelectedMergeEmitterPayload) :
    rejectThroughAcceptConfigScanDescription.HaltsFromTape
      (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)
      (rejectAfterAcceptConfigTape p) := by
  unfold rejectThroughAcceptConfigScanDescription
  exact
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      commonScheduleDescription_subroutineReady
      selectedMergePaddedEmitterConfigScanner_subroutineReady
      (commonScheduleDescription_haltsFrom p)
      (commonAfterStageTape_move_right_acceptConfigSource p)
      (rejectAcceptConfigScan_haltsFrom p)

def rejectAfterRestoreTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  tapeAtCells
    (List.append
      ((SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits p).reverse.map some)
      (rejectPrefixBaseLeft p))
    (List.append
      (List.replicate
        (SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).length none)
      (List.append ((rejectAfterRejectConfigSuffixBits p).map some)
        commonRightPadding))

@[irreducible] def rejectThroughStashDescription : MachineDescription :=
  canonicalSeqDescription rejectThroughAcceptConfigScanDescription sentinelStashDescription

@[irreducible] def rejectThroughRejectConfigEraseDescription : MachineDescription :=
  canonicalSeqDescription rejectThroughStashDescription
    configurationFieldBoundaryEraserDescription

@[irreducible] def rejectThroughSentinelRestoreDescription : MachineDescription :=
  canonicalSeqDescription rejectThroughRejectConfigEraseDescription
    sentinelRestoreDescription

theorem rejectThroughStashDescription_subroutineReady :
    rejectThroughStashDescription.SubroutineReady := by
  unfold rejectThroughStashDescription
  exact canonicalSeqDescription_subroutineReady
    rejectThroughAcceptConfigScanDescription_subroutineReady
    sentinelStashDescription_subroutineReady

theorem rejectThroughRejectConfigEraseDescription_subroutineReady :
    rejectThroughRejectConfigEraseDescription.SubroutineReady := by
  unfold rejectThroughRejectConfigEraseDescription
  exact canonicalSeqDescription_subroutineReady
    rejectThroughStashDescription_subroutineReady
    configurationFieldBoundaryEraserDescription_subroutineReady

theorem rejectThroughSentinelRestoreDescription_subroutineReady :
    rejectThroughSentinelRestoreDescription.SubroutineReady := by
  unfold rejectThroughSentinelRestoreDescription
  exact canonicalSeqDescription_subroutineReady
    rejectThroughRejectConfigEraseDescription_subroutineReady
    sentinelRestoreDescription_subroutineReady

set_option maxHeartbeats 1000000 in
theorem rejectThroughSentinelRestoreDescription_haltsFrom
    (p : SelectedMergeEmitterPayload) :
    rejectThroughSentinelRestoreDescription.HaltsFromTape
      (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)
      (rejectAfterRestoreTape p) := by
  rcases configurationFieldBits_ends_valid p.L.acceptConfig with
    ⟨pre, c2, c3, c4, hacceptConfig, hvalid⟩
  rcases
      cellFieldBits_cons_false (some p.L.acceptHit)
        (rejectAfterAcceptHitSuffixBits p) with
    ⟨suffixTail, hpost⟩
  have hpostBits :
      rejectAfterRejectConfigSuffixBits p = false :: suffixTail := by
    rw [rejectAfterRejectConfigSuffixBits_eq_acceptHit]
    simpa [boolFieldBits] using hpost
  rcases
      configurationFieldBits_cons_false p.L.rejectConfig
        (false :: suffixTail) with
    ⟨afterRejectTail, hafterReject⟩
  rcases configurationFieldBits_cons_false p.L.rejectConfig [] with
    ⟨rejectConfigTail, hrejectConfig⟩
  let prefixLeft : List (Option Bool) :=
    List.append (pre.reverse.map some) (rejectPrefixBaseLeft p)
  let stashBase : List (Option Bool) :=
    some c4 :: some c3 :: some c2 :: prefixLeft
  let stashTape : Tape Bool :=
    tapeAtCells (none :: stashBase)
      (List.append ((commonAfterAcceptConfigSuffixBits p).map some)
        commonRightPadding)
  let erasedTape : Tape Bool :=
    leftBoundaryEraserTargetTape stashBase
      (configurationFieldBits p.L.rejectConfig [])
      (some false)
      (List.append (suffixTail.map some) commonRightPadding)
  have hafterBits :
      commonAfterAcceptConfigSuffixBits p = false :: afterRejectTail := by
    rw [commonAfterAcceptConfigSuffixBits_eq_rejectConfig, hpostBits]
    exact hafterReject
  have hafterConfig :
      commonAfterAcceptConfigSuffixBits p =
        configurationFieldBits p.L.rejectConfig (false :: suffixTail) := by
    rw [commonAfterAcceptConfigSuffixBits_eq_rejectConfig, hpostBits]
  have hscanBridge :
      Tape.move Direction.left
          (Tape.move Direction.right (rejectAfterAcceptConfigTape p)) =
        rejectAfterAcceptConfigTape p := by
    rw [rejectAfterAcceptConfigTape,
      SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits,
      hacceptConfig, hafterBits]
    simp [CommonGround.FiniteTransducers.tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight,
      List.map_append, List.map_reverse, List.reverse_append, List.append_assoc]
  have hstash :
      sentinelStashDescription.HaltsFromTape
        (rejectAfterAcceptConfigTape p) stashTape := by
    apply haltsFromTape_of_reaches
    rw [rejectAfterAcceptConfigTape,
      SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits,
      hacceptConfig, hafterBits]
    simpa [stashTape, stashBase, prefixLeft, hafterBits,
      CommonGround.FiniteTransducers.tapeAtCells,
      Tape.move, Tape.moveLeft, sentinelStashDescription,
      List.map_append, List.map_reverse,
      List.reverse_append, List.append_assoc] using
      sentinelStash_run c2 c3 c4 hvalid prefixLeft
        (List.append ((commonAfterAcceptConfigSuffixBits p).map some)
          commonRightPadding)
  have hthroughStash :
      rejectThroughStashDescription.HaltsFromTape
        (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)
        stashTape := by
    unfold rejectThroughStashDescription
    exact
      canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        rejectThroughAcceptConfigScanDescription_subroutineReady
        sentinelStashDescription_subroutineReady
        (rejectThroughAcceptConfigScanDescription_haltsFrom p)
        hscanBridge hstash
  have hstashBridge :
      Tape.move Direction.left (Tape.move Direction.right stashTape) =
        stashTape := by
    unfold stashTape
    rw [hafterBits]
    cases afterRejectTail <;>
      simp [CommonGround.FiniteTransducers.tapeAtCells,
        commonRightPadding, Tape.move, Tape.moveLeft, Tape.moveRight]
  have herase :
      configurationFieldBoundaryEraserDescription.HaltsFromTape
        stashTape erasedTape := by
    simpa [stashTape, stashBase, erasedTape, hafterConfig] using
      configurationFieldBoundaryEraserDescription_haltsFrom_withRight
        p.L.rejectConfig stashBase suffixTail commonRightPadding
  have hthroughErase :
      rejectThroughRejectConfigEraseDescription.HaltsFromTape
        (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)
        erasedTape := by
    unfold rejectThroughRejectConfigEraseDescription
    exact
      canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        rejectThroughStashDescription_subroutineReady
        configurationFieldBoundaryEraserDescription_subroutineReady
        hthroughStash hstashBridge herase
  have herasedBridge :
      Tape.move Direction.left (Tape.move Direction.right erasedTape) =
        erasedTape := by
    unfold erasedTape leftBoundaryEraserTargetTape
    rw [hrejectConfig]
    cases rejectConfigTail <;>
      simp [List.replicate_succ,
        CommonGround.FiniteTransducers.tapeAtCells,
        Tape.move, Tape.moveLeft, Tape.moveRight]
  have hrestore :
      sentinelRestoreDescription.HaltsFromTape
        erasedTape (rejectAfterRestoreTape p) := by
    let rightCells : List (Option Bool) :=
      List.append (List.replicate rejectConfigTail.length none)
        (some false ::
          List.append (suffixTail.map some) commonRightPadding)
    have hrun :=
      sentinelRestore_run c2 c3 c4 hvalid prefixLeft rightCells
    apply haltsFromTape_of_reaches
    unfold erasedTape leftBoundaryEraserTargetTape
    rw [hrejectConfig]
    rw [rejectAfterRestoreTape,
      SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits,
      hacceptConfig,
      SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits,
      hrejectConfig, hpostBits]
    cases rejectConfigTail <;>
      simpa [erasedTape, leftBoundaryEraserTargetTape,
        stashBase, prefixLeft, rightCells,
        CommonGround.FiniteTransducers.tapeAtCells,
        sentinelRestoreDescription, List.replicate_succ, tapeSeenLeft,
        List.map_append, List.map_reverse, List.reverse_append,
        List.append_assoc] using hrun
  unfold rejectThroughSentinelRestoreDescription
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      rejectThroughRejectConfigEraseDescription_subroutineReady
      sentinelRestoreDescription_subroutineReady
      hthroughErase herasedBridge hrestore

def rejectAfterMidBaseLeft
    (p : SelectedMergeEmitterPayload) : List (Option Bool) :=
  List.append
    (List.replicate
      (SelectedMergePaddedEmitterParsedInnerOuterStageFieldBits p).length none)
    (List.append [none, none, none, none]
      (List.append
        ((SelectedMergePaddedEmitterParsedInnerAcceptHitFieldBits p).reverse.map some)
        (List.append
          (List.replicate
            (SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).length none)
          (List.append
          ((SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits p).reverse.map some)
          (rejectPrefixBaseLeft p)))))

def rejectOuterConfigHitBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  List.append
    (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
    (SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits p)

def rejectAfterMidTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  tapeAtCells (rejectAfterMidBaseLeft p)
    (List.append ((rejectOuterConfigHitBits p).map some)
      commonRightPadding)

def rejectAfterOuterConfigTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  Tape.move Direction.left
    (tapeAtCells
      (List.append
        ((SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).reverse.map some)
        (rejectAfterMidBaseLeft p))
      (List.append
        ((SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits p).map some)
        commonRightPadding))

def rejectOuterConfigHandoffTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  tapeAtCells
    (List.append
      ((SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).reverse.map some)
      (rejectAfterMidBaseLeft p))
    (List.append
      ((SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits p).map some)
      commonRightPadding)

def rejectAfterHitLeft
    (p : SelectedMergeEmitterPayload) : List (Option Bool) :=
  List.append
    ((SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits p).reverse.map some)
    (List.append
      ((SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).reverse.map some)
      (rejectAfterMidBaseLeft p))

def rejectAfterHitTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  tapeAtCells (rejectAfterHitLeft p) commonRightPadding

@[irreducible] def rejectThroughMidEraseDescription : MachineDescription :=
  canonicalSeqDescription rejectThroughSentinelRestoreDescription
    rejectMidEraserDescription

@[irreducible] def rejectThroughOuterConfigScanDescription : MachineDescription :=
  canonicalSeqDescription rejectThroughMidEraseDescription
    SelectedMergePaddedEmitterConfigScannerDescription

@[irreducible] def rejectDeleteDescription : MachineDescription :=
  seqSubroutine rejectThroughOuterConfigScanDescription
    SelectedMergePaddedEmitterHitScannerDescription Direction.right

theorem rejectThroughMidEraseDescription_subroutineReady :
    rejectThroughMidEraseDescription.SubroutineReady := by
  unfold rejectThroughMidEraseDescription
  exact canonicalSeqDescription_subroutineReady
    rejectThroughSentinelRestoreDescription_subroutineReady
    rejectMidEraserDescription_subroutineReady

theorem rejectThroughOuterConfigScanDescription_subroutineReady :
    rejectThroughOuterConfigScanDescription.SubroutineReady := by
  unfold rejectThroughOuterConfigScanDescription
  exact canonicalSeqDescription_subroutineReady
    rejectThroughMidEraseDescription_subroutineReady
    selectedMergePaddedEmitterConfigScanner_subroutineReady

theorem rejectDeleteDescription_subroutineReady :
    rejectDeleteDescription.SubroutineReady := by
  unfold rejectDeleteDescription
  exact seqSubroutine_subroutineReady
    rejectThroughOuterConfigScanDescription_subroutineReady
    selectedMergePaddedEmitterHitScanner_subroutineReady

theorem rejectMidEraser_haltsFrom
    (p : SelectedMergeEmitterPayload) :
    rejectMidEraserDescription.HaltsFromTape
      (rejectAfterRestoreTape p) (rejectAfterMidTape p) := by
  apply haltsFromTape_of_reaches
  simpa [rejectAfterRestoreTape, rejectAfterMidTape, rejectAfterMidBaseLeft,
    rejectOuterConfigHitBits, rejectAfterRejectConfigSuffixBits,
    SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits,
    SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits,
    SelectedMergePaddedEmitterParsedInnerAcceptHitFieldBits,
    SelectedMergePaddedEmitterParsedInnerRejectHitFieldBits,
    SelectedMergePaddedEmitterParsedInnerOuterStageFieldBits,
    SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits,
    SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits,
    boolFieldBits_eq_four, stageNatBits_length,
    rejectMidEraserDescription,
    List.map_append, List.append_assoc] using
      rejectMidEraser_run
        (SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).length
        false true p.L.acceptHit (!p.L.acceptHit)
        false true p.L.rejectHit (!p.L.rejectHit)
        p.S.stage
        (List.append
          ((SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits p).reverse.map some)
          (rejectPrefixBaseLeft p))
        (List.append ((rejectOuterConfigHitBits p).map some)
          commonRightPadding)

set_option maxHeartbeats 1000000 in
theorem rejectThroughMidEraseDescription_haltsFrom
    (p : SelectedMergeEmitterPayload) :
    rejectThroughMidEraseDescription.HaltsFromTape
      (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)
      (rejectAfterMidTape p) := by
  unfold rejectThroughMidEraseDescription
  rcases configurationFieldBits_cons_false p.L.rejectConfig [] with
    ⟨tail, htail⟩
  have hbridge :
      Tape.move Direction.left
          (Tape.move Direction.right (rejectAfterRestoreTape p)) =
        rejectAfterRestoreTape p := by
    rw [rejectAfterRestoreTape,
      SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits, htail]
    generalize hsuffix : rejectAfterRejectConfigSuffixBits p = suffix
    cases tail <;> cases suffix <;>
      simp [commonRightPadding, List.replicate_succ,
        CommonGround.FiniteTransducers.tapeAtCells,
        Tape.move, Tape.moveLeft, Tape.moveRight]
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      rejectThroughSentinelRestoreDescription_subroutineReady
      rejectMidEraserDescription_subroutineReady
      (rejectThroughSentinelRestoreDescription_haltsFrom p)
      hbridge (rejectMidEraser_haltsFrom p)

theorem rejectThroughOuterConfigScanDescription_haltsFrom
    (p : SelectedMergeEmitterPayload) :
    rejectThroughOuterConfigScanDescription.HaltsFromTape
      (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)
      (rejectAfterOuterConfigTape p) := by
  rcases cellFieldBits_cons_false (some p.S.hit) [] with
    ⟨suffixTail, hhit⟩
  have hsuffix :
      SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits p =
        false :: suffixTail := by
    unfold Word at hhit ⊢
    simpa [SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits,
      boolFieldBits] using hhit
  have hsourceBits :
      rejectOuterConfigHitBits p =
        configurationFieldBits p.S.config (false :: suffixTail) := by
    unfold Word
    simpa [rejectOuterConfigHitBits,
      SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits, hsuffix] using
        (configurationFieldBits_append_nil p.S.config
          (false :: suffixTail))
  have hbridge :
      Tape.move Direction.left
          (Tape.move Direction.right (rejectAfterMidTape p)) =
        rejectAfterMidTape p := by
    rcases
        configurationFieldBits_false_false_tail p.S.config
          (false :: suffixTail) with
      ⟨fieldTail, hfield⟩
    rw [rejectAfterMidTape, hsourceBits, hfield]
    simp [CommonGround.FiniteTransducers.tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]
  have hrestoredLeft :
      cellListCanonicalRestoredLeftWithBase p.S.config.tape.right
          (List.append
            ((cellCodeBits p.S.config.tape.head).reverse.map some)
            (cellListCanonicalRestoredLeftWithBase p.S.config.tape.left
              (List.append
                ((stageNatBits p.S.config.state).reverse.map some)
                (rejectAfterMidBaseLeft p)))) =
        List.append
          ((configurationFieldBits p.S.config []).reverse.map some)
          (rejectAfterMidBaseLeft p) := by
    rw [← configurationRestoredLeftWithBase_eq_fieldBits_reverse_append]
    rfl
  have hscan :
      SelectedMergePaddedEmitterConfigScannerDescription.HaltsFromTape
        (rejectAfterMidTape p) (rejectAfterOuterConfigTape p) := by
    rcases
        run_configurationSuffix_raw_to_handoff_withBaseAndRight
          p.S.config (rejectAfterMidBaseLeft p)
          suffixTail commonRightPadding with
      ⟨steps, hsteps⟩
    have htarget :
        (cellListCanonicalHandoffConfigWithBaseAndRight
          p.S.config.tape.right
          (List.append
            ((cellCodeBits p.S.config.tape.head).reverse.map some)
            (cellListCanonicalRestoredLeftWithBase p.S.config.tape.left
              (List.append
                ((stageNatBits p.S.config.state).reverse.map some)
                (rejectAfterMidBaseLeft p))))
          (false :: suffixTail) commonRightPadding).tape =
            rejectAfterOuterConfigTape p := by
      rw [cellListCanonicalHandoffConfigWithBaseAndRight, hrestoredLeft]
      simp [rejectAfterOuterConfigTape,
        SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits,
        hsuffix, CommonGround.FiniteTransducers.tapeAtCells,
        DovetailInitialLayoutInitializer.tapeAtCells,
        List.map_reverse]
    refine ⟨steps, ?_⟩
    constructor
    · simpa [MachineDescription.HaltsFromTapeIn,
        SelectedMergePaddedEmitterConfigScannerDescription,
        rejectAfterMidTape, hsourceBits,
        DovetailInitialLayoutInitializer.config,
        List.map_append, List.append_assoc] using!
          congrArg Configuration.state hsteps
    · exact Eq.trans
        (by simpa [MachineDescription.HaltsFromTapeIn,
          SelectedMergePaddedEmitterConfigScannerDescription,
          rejectAfterMidTape, hsourceBits,
          DovetailInitialLayoutInitializer.config,
          List.map_append, List.append_assoc] using!
            congrArg Configuration.tape hsteps)
        htarget
  unfold rejectThroughOuterConfigScanDescription
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      rejectThroughMidEraseDescription_subroutineReady
      selectedMergePaddedEmitterConfigScanner_subroutineReady
      (rejectThroughMidEraseDescription_haltsFrom p)
      hbridge hscan

theorem rejectAfterOuterConfigTape_move_right
    (p : SelectedMergeEmitterPayload) :
    Tape.move Direction.right (rejectAfterOuterConfigTape p) =
      rejectOuterConfigHandoffTape p := by
  rcases configurationFieldBits_eq_reverse_cons_cons p.S.config with
    ⟨x, y, rest, hfield⟩
  simpa [rejectAfterOuterConfigTape, rejectOuterConfigHandoffTape,
    SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits, hfield,
    List.map_reverse] using
      (CommonGround.FiniteTransducers.tapeAtCells_move_right_move_left_append_cons
        ([] : List (Option Bool))
        (some y :: List.append (rest.map some) (rejectAfterMidBaseLeft p))
        (List.append
          ((SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits p).map some)
          commonRightPadding)
        (some x))

theorem rejectHitScannerDescription_haltsFrom
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterHitScannerDescription.HaltsFromTape
      (rejectOuterConfigHandoffTape p) (rejectAfterHitTape p) := by
  have hrun :=
    selectedMergePaddedEmitterHitScanner_runConfig_withRight
      p.S.hit
      (List.append
        ((SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).reverse.map some)
        (rejectAfterMidBaseLeft p))
      commonRightPadding
  have hsource :
      DovetailInitialLayoutInitializer.config 0
        (List.append
          ((SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).reverse.map some)
          (rejectAfterMidBaseLeft p))
        (List.append
          ((encodeCodeWordAsInput (encodeBoolAppend p.S.hit [])).map some)
          commonRightPadding) =
        { state := 0, tape := rejectOuterConfigHandoffTape p } := by
    simp [rejectOuterConfigHandoffTape,
      SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits,
      boolFieldBits, cellFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.boolBits_eq_encodeBoolAppend,
      encodeCodeWordAsInput,
      DovetailInitialLayoutInitializer.config,
      CommonGround.FiniteTransducers.tapeAtCells,
      DovetailInitialLayoutInitializer.tapeAtCells]
    rfl
  have htarget :
      DovetailInitialLayoutInitializer.config 5
        (List.append
          ((encodeCodeWordAsInput (encodeBoolAppend p.S.hit [])).reverse.map some)
          (List.append
            ((SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).reverse.map some)
            (rejectAfterMidBaseLeft p)))
        commonRightPadding =
        { state := 5, tape := rejectAfterHitTape p } := by
    simp [rejectAfterHitTape, rejectAfterHitLeft, rejectAfterMidBaseLeft,
      SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits,
      boolFieldBits, cellFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.boolBits_eq_encodeBoolAppend,
      encodeCodeWordAsInput,
      DovetailInitialLayoutInitializer.config,
      CommonGround.FiniteTransducers.tapeAtCells,
      DovetailInitialLayoutInitializer.tapeAtCells,
      List.map_append, List.map_reverse, List.reverse_append,
      List.append_assoc]
    rfl
  rw [hsource] at hrun
  refine ⟨4, ?_⟩
  constructor
  · simpa [SelectedMergePaddedEmitterHitScannerDescription,
      DovetailInitialLayoutInitializer.config] using
        congrArg Configuration.state hrun
  · exact Eq.trans
      (congrArg Configuration.tape hrun)
      (congrArg Configuration.tape htarget)

set_option maxHeartbeats 1000000 in
theorem rejectDeleteDescription_haltsFrom
    (p : SelectedMergeEmitterPayload) :
    rejectDeleteDescription.HaltsFromTape
      (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)
      (rejectAfterHitTape p) := by
  unfold rejectDeleteDescription
  exact
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      rejectThroughOuterConfigScanDescription_subroutineReady
      selectedMergePaddedEmitterHitScanner_subroutineReady
      (rejectThroughOuterConfigScanDescription_haltsFrom p)
      (rejectAfterOuterConfigTape_move_right p)
      (rejectHitScannerDescription_haltsFrom p)

def rejectRun1Bits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  List.append
    (SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p)
    (SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits p)

def rejectJ2InputTape
    (p : SelectedMergeEmitterPayload)
    (b1 : Bool) (blkT field : Word Bool)
    (g2 : Nat) (R : List (Option Bool)) : Tape Bool :=
  tapeAtCells [none]
    (List.append ((b1 :: blkT).map some)
      (none ::
        List.append ((rejectRun1Bits p).map some)
          (none ::
            List.append
              (List.replicate
                (SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).length none)
              (List.append
                ((SelectedMergePaddedEmitterParsedInnerAcceptHitFieldBits p).map some)
                (none ::
                  List.append (List.replicate g2 none)
                    (List.append (field.map some) (none :: R)))))))

def rejectJ2OutputTape
    (p : SelectedMergeEmitterPayload)
    (b1 : Bool) (blkT field : Word Bool)
    (g2 : Nat) (x : Bool) (R : List (Option Bool)) : Tape Bool :=
  tapeAtCells [none]
    (some x ::
      List.append ((b1 :: blkT).map some)
        (none ::
          List.append ((rejectRun1Bits p).map some)
            (List.append
              (List.replicate
                (SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).length none)
              (none ::
                List.append
                  ((SelectedMergePaddedEmitterParsedInnerAcceptHitFieldBits p).map some)
                  (List.append (List.replicate g2 none)
                    (none ::
                      List.append (field.map some) (none :: none :: R)))))))

theorem rejectJ2_haltsFrom
    (p : SelectedMergeEmitterPayload)
    (b1 : Bool) (blkT field : Word Bool)
    (g2 : Nat) (x : Bool) (R : List (Option Bool)) :
    pullOneBitJ2Description.HaltsFromTape
      (rejectJ2InputTape p b1 blkT (List.append field [x]) g2 R)
      (rejectJ2OutputTape p b1 blkT field g2 x R) := by
  rcases outputPrefixBits_cons p with ⟨prefixTail, hprefix⟩
  apply haltsFromTape_of_reaches
  simpa [rejectJ2InputTape, rejectJ2OutputTape, rejectRun1Bits,
    hprefix, boolFieldBits_eq_four,
    SelectedMergePaddedEmitterParsedInnerAcceptHitFieldBits,
    SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits,
    pullOneBitJ2Description, replicate_none_comm', List.append_assoc] using
    pullOneBitJ2_run b1 blkT
      false
      (List.append prefixTail
        (SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits p))
      (SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).length
      false [true, p.L.acceptHit, !p.L.acceptHit]
      g2 field x R

theorem rejectJ2OutputTape_eq_nextInput
    (p : SelectedMergeEmitterPayload)
    (b1 : Bool) (blkT field : Word Bool)
    (g2 : Nat) (x y : Bool) (R : List (Option Bool)) :
    rejectJ2OutputTape p b1 blkT (List.append field [x]) g2 y R =
      rejectJ2InputTape p y (b1 :: blkT)
        (List.append field [x]) g2 (none :: R) := by
  simp [rejectJ2InputTape, rejectJ2OutputTape,
    replicate_none_comm', List.append_assoc]

theorem rejectJ2OutputTape_canonicalBridge
    (p : SelectedMergeEmitterPayload)
    (b1 : Bool) (blkT field : Word Bool)
    (g2 : Nat) (x y : Bool) (R : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (rejectJ2OutputTape p b1 blkT
            (List.append field [x]) g2 y R)) =
      rejectJ2InputTape p y (b1 :: blkT)
        (List.append field [x]) g2 (none :: R) := by
  rw [show
      Tape.move Direction.left
          (Tape.move Direction.right
            (rejectJ2OutputTape p b1 blkT
              (List.append field [x]) g2 y R)) =
        rejectJ2OutputTape p b1 blkT
          (List.append field [x]) g2 y R by
    simp [rejectJ2OutputTape,
      CommonGround.FiniteTransducers.tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]]
  exact rejectJ2OutputTape_eq_nextInput p b1 blkT field g2 x y R

def rejectAfterFirstPullTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  tapeAtCells [none]
    (some (!p.S.hit) ::
      none ::
        List.append ((rejectRun1Bits p).map some)
          (List.append
            (List.replicate
              (SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).length none)
            (none ::
              List.append
                ((SelectedMergePaddedEmitterParsedInnerAcceptHitFieldBits p).map some)
                (List.append
                  (List.replicate
                    ((SelectedMergePaddedEmitterParsedInnerOuterStageFieldBits p).length + 3)
                    none)
                  (none ::
                    List.append
                      ((List.append
                        (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
                        [false, true, p.S.hit]).map some)
                      (none :: commonRightPadding))))))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem rejectFirstPull_haltsFrom
    (p : SelectedMergeEmitterPayload) :
    pullFirstRejectDescription.HaltsFromTape
      (Tape.move Direction.left (rejectAfterHitTape p))
      (rejectAfterFirstPullTape p) := by
  have hAH :
      (SelectedMergePaddedEmitterParsedInnerAcceptHitFieldBits p).reverse ≠ [] := by
    intro h
    rw [SelectedMergePaddedEmitterParsedInnerAcceptHitFieldBits,
      boolFieldBits_eq_four] at h
    simp at h
  have hrun1 :
      List.append
        (SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits p).reverse
        (SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p).reverse ≠ [] := by
    rcases outputPrefixBits_cons p with ⟨tail, hprefix⟩
    intro h
    rw [hprefix] at h
    simp at h
  apply haltsFromTape_of_reaches
  simpa (config := { maxSteps := 1000000 }) [rejectAfterHitTape, rejectAfterHitLeft, rejectAfterMidBaseLeft,
    rejectAfterFirstPullTape, rejectRun1Bits,
    SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits,
    SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits,
    SelectedMergePaddedEmitterParsedInnerAcceptHitFieldBits,
    SelectedMergePaddedEmitterParsedInnerOuterStageFieldBits,
    SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits,
    SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits,
    boolFieldBits_eq_four, List.map_append, List.map_reverse,
    List.reverse_append, List.replicate_succ, List.append_assoc,
    replicate_none_append_cons', none_cons_replicate_append,
    Tape.move, Tape.moveLeft,
    CommonGround.FiniteTransducers.tapeAtCells] using
      pullFirstReject_run (!p.S.hit)
        (List.append [p.S.hit, true, false]
          (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).reverse)
        ((SelectedMergePaddedEmitterParsedInnerOuterStageFieldBits p).length + 3)
        (SelectedMergePaddedEmitterParsedInnerAcceptHitFieldBits p).reverse hAH
        (SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).length
        (List.append
          (SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits p).reverse
          (SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p).reverse)
        hrun1 commonRightPadding

end ParsedInnerTransport
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
