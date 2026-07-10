import FoC.Computability.Compiler.ClosedCfg.PostTrans.ParsedInnerTransport.CommonSchedule
import FoC.Computability.Compiler.ClosedCfg.ProjTail.PostPaddingFieldEraser

set_option doc.verso true

/-!
# Parsed-inner accepting transport schedule

The accepting branch deletes the inner accept configuration and hit plus the
outer stage, then rebuilds the decoded target to the left of the cell-zero
sentinel.
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

def acceptAfterRejectConfigSuffixBits
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

def acceptAfterAcceptHitSuffixBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  List.append
    (SelectedMergePaddedEmitterParsedInnerRejectHitFieldBits p)
    (List.append
      (SelectedMergePaddedEmitterParsedInnerOuterStageFieldBits p)
      (List.append
        (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
        (SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits p)))

theorem acceptAfterRejectConfigSuffixBits_eq_acceptHit
    (p : SelectedMergeEmitterPayload) :
    acceptAfterRejectConfigSuffixBits p =
      boolFieldBits p.L.acceptHit
        (acceptAfterAcceptHitSuffixBits p) := by
  unfold Word
  simpa [acceptAfterRejectConfigSuffixBits,
    acceptAfterAcceptHitSuffixBits,
    SelectedMergePaddedEmitterParsedInnerAcceptHitFieldBits,
    boolFieldBits] using
      (cellFieldBits_append_nil (some p.L.acceptHit)
        (acceptAfterAcceptHitSuffixBits p))

theorem commonAfterAcceptConfigSuffixBits_eq_rejectConfig
    (p : SelectedMergeEmitterPayload) :
    commonAfterAcceptConfigSuffixBits p =
      configurationFieldBits p.L.rejectConfig
        (acceptAfterRejectConfigSuffixBits p) := by
  unfold Word
  simpa [commonAfterAcceptConfigSuffixBits,
    acceptAfterRejectConfigSuffixBits,
    SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits] using
      (configurationFieldBits_append_nil p.L.rejectConfig
        (acceptAfterRejectConfigSuffixBits p))

def acceptPrefixBaseLeft
    (p : SelectedMergeEmitterPayload) : List (Option Bool) :=
  List.append
    ((SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p).reverse.map
      some)
    [none]

def acceptAfterRestoreTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  tapeAtCells (acceptPrefixBaseLeft p)
    (List.append
      (List.replicate
        (SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits p).length
        none)
      (List.append ((commonAfterAcceptConfigSuffixBits p).map some)
        commonRightPadding))

def acceptAfterBlankWalkBaseLeft
    (p : SelectedMergeEmitterPayload) : List (Option Bool) :=
  List.append
    (List.replicate
      (SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits p).length
      none)
    (acceptPrefixBaseLeft p)

def acceptAfterBlankWalkTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  tapeAtCells (acceptAfterBlankWalkBaseLeft p)
    (List.append ((commonAfterAcceptConfigSuffixBits p).map some)
      commonRightPadding)

def acceptAfterRejectConfigTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  Tape.move Direction.left
    (tapeAtCells
      (List.append
        ((SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).reverse.map
          some)
        (acceptAfterBlankWalkBaseLeft p))
      (List.append ((acceptAfterRejectConfigSuffixBits p).map some)
        commonRightPadding))

def acceptRejectConfigHandoffTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  tapeAtCells
    (List.append
      ((SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).reverse.map
        some)
      (acceptAfterBlankWalkBaseLeft p))
    (List.append ((acceptAfterRejectConfigSuffixBits p).map some)
      commonRightPadding)

def acceptAfterMidBaseLeft
    (p : SelectedMergeEmitterPayload) : List (Option Bool) :=
  List.append
    (List.replicate
      (SelectedMergePaddedEmitterParsedInnerOuterStageFieldBits p).length none)
    (List.append
      ((SelectedMergePaddedEmitterParsedInnerRejectHitFieldBits p).reverse.map
        some)
      (List.append
        (List.replicate
          (SelectedMergePaddedEmitterParsedInnerAcceptHitFieldBits p).length none)
        (List.append
          ((SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).reverse.map
            some)
          (acceptAfterBlankWalkBaseLeft p))))

def acceptOuterConfigHitBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  List.append
    (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
    (SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits p)

def acceptAfterMidTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  tapeAtCells (acceptAfterMidBaseLeft p)
    (List.append ((acceptOuterConfigHitBits p).map some)
      commonRightPadding)

def acceptAfterOuterConfigTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  Tape.move Direction.left
    (tapeAtCells
      (List.append
        ((SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).reverse.map
          some)
        (acceptAfterMidBaseLeft p))
      (List.append
        ((SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits p).map some)
        commonRightPadding))

def acceptOuterConfigHandoffTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  tapeAtCells
    (List.append
      ((SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).reverse.map
        some)
      (acceptAfterMidBaseLeft p))
    (List.append
      ((SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits p).map some)
      commonRightPadding)

def acceptAfterHitLeft
    (p : SelectedMergeEmitterPayload) : List (Option Bool) :=
  List.append
    ((SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits p).reverse.map
      some)
    (List.append
      ((SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).reverse.map
        some)
      (List.append
        (List.replicate
          (SelectedMergePaddedEmitterParsedInnerOuterStageFieldBits p).length
          none)
        (List.append
          ((SelectedMergePaddedEmitterParsedInnerRejectHitFieldBits p).reverse.map
            some)
          (List.append
            (List.replicate
              (SelectedMergePaddedEmitterParsedInnerAcceptHitFieldBits p).length
              none)
            (List.append
              ((SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).reverse.map
                some)
              (List.append
                (List.replicate
                  (SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits p).length
                  none)
                (List.append
                  ((SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p).reverse.map
                    some)
                  [none])))))))

def acceptAfterHitTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  tapeAtCells (acceptAfterHitLeft p) commonRightPadding

def acceptThroughStashDescription : MachineDescription :=
  canonicalSeqDescription commonScheduleDescription sentinelStashDescription

def acceptThroughAcceptConfigEraseDescription : MachineDescription :=
  canonicalSeqDescription acceptThroughStashDescription
    configurationFieldBoundaryEraserDescription

def acceptThroughSentinelRestoreDescription : MachineDescription :=
  canonicalSeqDescription acceptThroughAcceptConfigEraseDescription
    sentinelRestoreDescription

def acceptThroughBlankWalkDescription : MachineDescription :=
  canonicalSeqDescription acceptThroughSentinelRestoreDescription
    blankRightWalkerDescription

def acceptThroughRejectConfigScanDescription : MachineDescription :=
  canonicalSeqDescription acceptThroughBlankWalkDescription
    SelectedMergePaddedEmitterConfigScannerDescription

def acceptThroughMidEraseDescription : MachineDescription :=
  seqSubroutine acceptThroughRejectConfigScanDescription
    acceptMidEraserDescription Direction.right

def acceptThroughOuterConfigScanDescription : MachineDescription :=
  canonicalSeqDescription acceptThroughMidEraseDescription
    SelectedMergePaddedEmitterConfigScannerDescription

def acceptDeleteDescription : MachineDescription :=
  seqSubroutine acceptThroughOuterConfigScanDescription
    SelectedMergePaddedEmitterHitScannerDescription Direction.right

theorem acceptThroughStashDescription_subroutineReady :
    acceptThroughStashDescription.SubroutineReady := by
  exact canonicalSeqDescription_subroutineReady
    commonScheduleDescription_subroutineReady
    sentinelStashDescription_subroutineReady

theorem acceptThroughAcceptConfigEraseDescription_subroutineReady :
    acceptThroughAcceptConfigEraseDescription.SubroutineReady := by
  exact canonicalSeqDescription_subroutineReady
    acceptThroughStashDescription_subroutineReady
    configurationFieldBoundaryEraserDescription_subroutineReady

theorem acceptThroughSentinelRestoreDescription_subroutineReady :
    acceptThroughSentinelRestoreDescription.SubroutineReady := by
  exact canonicalSeqDescription_subroutineReady
    acceptThroughAcceptConfigEraseDescription_subroutineReady
    sentinelRestoreDescription_subroutineReady

theorem acceptThroughBlankWalkDescription_subroutineReady :
    acceptThroughBlankWalkDescription.SubroutineReady := by
  exact canonicalSeqDescription_subroutineReady
    acceptThroughSentinelRestoreDescription_subroutineReady
    blankRightWalkerDescription_subroutineReady

theorem acceptThroughRejectConfigScanDescription_subroutineReady :
    acceptThroughRejectConfigScanDescription.SubroutineReady := by
  exact canonicalSeqDescription_subroutineReady
    acceptThroughBlankWalkDescription_subroutineReady
    selectedMergePaddedEmitterConfigScanner_subroutineReady

theorem acceptThroughMidEraseDescription_subroutineReady :
    acceptThroughMidEraseDescription.SubroutineReady := by
  exact seqSubroutine_subroutineReady
    acceptThroughRejectConfigScanDescription_subroutineReady
    acceptMidEraserDescription_subroutineReady

theorem acceptThroughOuterConfigScanDescription_subroutineReady :
    acceptThroughOuterConfigScanDescription.SubroutineReady := by
  exact canonicalSeqDescription_subroutineReady
    acceptThroughMidEraseDescription_subroutineReady
    selectedMergePaddedEmitterConfigScanner_subroutineReady

theorem acceptDeleteDescription_subroutineReady :
    acceptDeleteDescription.SubroutineReady := by
  exact seqSubroutine_subroutineReady
    acceptThroughOuterConfigScanDescription_subroutineReady
    selectedMergePaddedEmitterHitScanner_subroutineReady

theorem acceptThroughSentinelRestoreDescription_haltsFrom
    (p : SelectedMergeEmitterPayload) :
    acceptThroughSentinelRestoreDescription.HaltsFromTape
      (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)
      (acceptAfterRestoreTape p) := by
  rcases outputPrefixBits_eq_prefix_done p with ⟨pre, hprefix⟩
  rcases
      configurationFieldBits_cons_false p.L.rejectConfig
        (acceptAfterRejectConfigSuffixBits p) with
    ⟨afterAcceptTail, hafterAccept⟩
  rcases
      configurationFieldBits_cons_false p.L.acceptConfig [] with
    ⟨acceptConfigTail, hacceptConfig⟩
  rcases
      configurationFieldBits_cons_false p.L.acceptConfig
        (false :: afterAcceptTail) with
    ⟨acceptConfigFullTail, hacceptConfigFull⟩
  let prefixLeft : List (Option Bool) :=
    List.append (pre.reverse.map some) [none]
  let stashBase : List (Option Bool) :=
    some true :: some true :: some false :: prefixLeft
  let afterStageRight : List (Option Bool) :=
    List.append
      ((configurationFieldBits p.L.acceptConfig
        (false :: afterAcceptTail)).map some)
      commonRightPadding
  let stashTape : Tape Bool :=
    tapeAtCells (none :: stashBase) afterStageRight
  let erasedTape : Tape Bool :=
    leftBoundaryEraserTargetTape stashBase
      (configurationFieldBits p.L.acceptConfig [])
      (some false)
      (List.append (afterAcceptTail.map some) commonRightPadding)
  have hstageShape :
      commonAfterStageTape p =
        tapeSeenLeft
          (some true :: some true :: some false :: some false :: prefixLeft)
          afterStageRight := by
    rw [commonAfterStageTape]
    unfold
      CanonicalLayouts.DovetailStagePrefix.nonemptyNatSuffixHandoffConfigWithBaseAndRight
    rw [commonStageRestoredBase_eq_outputPrefix_reverse_append_none]
    rw [hprefix]
    rw [commonAfterStageSuffixBits_eq_acceptConfig]
    rw [commonAfterAcceptConfigSuffixBits_eq_rejectConfig]
    rw [hafterAccept]
    rw [hacceptConfigFull]
    simp [prefixLeft, afterStageRight, tapeSeenLeft,
      DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.move, Tape.moveLeft, List.map_append, List.map_reverse,
      List.reverse_append, List.append_assoc]
    unfold Word at hacceptConfigFull
    simpa using
      (congrArg
        (fun w : List Bool =>
          List.append (w.map some) commonRightPadding)
        hacceptConfigFull).symm
  have hstageBridge :
      Tape.move Direction.left
          (Tape.move Direction.right (commonAfterStageTape p)) =
        commonAfterStageTape p := by
    rw [hstageShape]
    unfold afterStageRight
    rw [hacceptConfigFull]
    simp [tapeSeenLeft,
      CommonGround.FiniteTransducers.tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]
  have hstash :
      sentinelStashDescription.HaltsFromTape
        (commonAfterStageTape p) stashTape := by
    apply haltsFromTape_of_reaches
    rw [hstageShape]
    simpa [stashTape, stashBase, sentinelStashDescription] using
      sentinelStash_run false true true
        (by simp [SentinelTokenValid]) prefixLeft afterStageRight
  have hthroughStash :
      acceptThroughStashDescription.HaltsFromTape
        (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)
        stashTape := by
    exact
      canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        commonScheduleDescription_subroutineReady
        sentinelStashDescription_subroutineReady
        (commonScheduleDescription_haltsFrom p)
        hstageBridge hstash
  have hstashBridge :
      Tape.move Direction.left (Tape.move Direction.right stashTape) =
        stashTape := by
    rcases
        configurationFieldBits_false_false_tail p.L.acceptConfig
          (false :: afterAcceptTail) with
      ⟨fieldTail, hfield⟩
    unfold stashTape afterStageRight
    rw [hfield]
    simp [CommonGround.FiniteTransducers.tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]
  have herase :
      configurationFieldBoundaryEraserDescription.HaltsFromTape
        stashTape erasedTape := by
    simpa [stashTape, stashBase, afterStageRight, erasedTape] using
      configurationFieldBoundaryEraserDescription_haltsFrom_withRight
        p.L.acceptConfig stashBase afterAcceptTail commonRightPadding
  have hthroughErase :
      acceptThroughAcceptConfigEraseDescription.HaltsFromTape
        (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)
        erasedTape := by
    exact
      canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        acceptThroughStashDescription_subroutineReady
        configurationFieldBoundaryEraserDescription_subroutineReady
        hthroughStash hstashBridge herase
  have herasedBridge :
      Tape.move Direction.left (Tape.move Direction.right erasedTape) =
        erasedTape := by
    unfold erasedTape leftBoundaryEraserTargetTape
    rw [hacceptConfig]
    cases acceptConfigTail <;>
      simp [List.replicate_succ,
      CommonGround.FiniteTransducers.tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]
  have hrestore :
      sentinelRestoreDescription.HaltsFromTape
        erasedTape (acceptAfterRestoreTape p) := by
    have hafterBits :
        commonAfterAcceptConfigSuffixBits p =
          false :: afterAcceptTail := by
      rw [commonAfterAcceptConfigSuffixBits_eq_rejectConfig]
      exact hafterAccept
    let rightCells : List (Option Bool) :=
      List.append (List.replicate acceptConfigTail.length none)
        (some false ::
          List.append (afterAcceptTail.map some) commonRightPadding)
    have hrun :=
      sentinelRestore_run false true true
        (by simp [SentinelTokenValid]) prefixLeft rightCells
    apply haltsFromTape_of_reaches
    unfold erasedTape leftBoundaryEraserTargetTape
    rw [hacceptConfig]
    rw [acceptAfterRestoreTape, acceptPrefixBaseLeft, hprefix,
      SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits,
      hacceptConfig, hafterBits]
    cases acceptConfigTail <;>
      simpa [erasedTape, leftBoundaryEraserTargetTape,
        stashBase, prefixLeft, rightCells, hprefix,
        sentinelRestoreDescription, List.replicate_succ,
        tapeSeenLeft, CommonGround.FiniteTransducers.tapeAtCells,
        List.map_append, List.map_reverse, List.reverse_append,
        List.append_assoc] using hrun
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      acceptThroughAcceptConfigEraseDescription_subroutineReady
      sentinelRestoreDescription_subroutineReady
      hthroughErase herasedBridge hrestore

theorem acceptThroughBlankWalkDescription_haltsFrom
    (p : SelectedMergeEmitterPayload) :
    acceptThroughBlankWalkDescription.HaltsFromTape
      (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)
      (acceptAfterBlankWalkTape p) := by
  rcases
      configurationFieldBits_cons_false p.L.acceptConfig [] with
    ⟨acceptConfigTail, hacceptConfig⟩
  rcases
      configurationFieldBits_cons_false p.L.rejectConfig
        (acceptAfterRejectConfigSuffixBits p) with
    ⟨afterAcceptTail, hafterAccept⟩
  have hafterBits :
      commonAfterAcceptConfigSuffixBits p =
        false :: afterAcceptTail := by
    rw [commonAfterAcceptConfigSuffixBits_eq_rejectConfig]
    exact hafterAccept
  have hbridge :
      Tape.move Direction.left
          (Tape.move Direction.right (acceptAfterRestoreTape p)) =
        acceptAfterRestoreTape p := by
    rw [acceptAfterRestoreTape,
      SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits,
      hacceptConfig, hafterBits]
    cases acceptConfigTail <;>
      simp [List.replicate_succ,
        CommonGround.FiniteTransducers.tapeAtCells,
        Tape.move, Tape.moveLeft, Tape.moveRight]
  have hwalk :
      blankRightWalkerDescription.HaltsFromTape
        (acceptAfterRestoreTape p) (acceptAfterBlankWalkTape p) := by
    apply haltsFromTape_of_reaches
    rw [acceptAfterRestoreTape, acceptAfterBlankWalkTape,
      acceptAfterBlankWalkBaseLeft,
      SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits,
      hacceptConfig, hafterBits]
    simpa [List.replicate_succ, blankRightWalkerDescription] using
      blankRightWalker_run acceptConfigTail.length false
        (acceptPrefixBaseLeft p)
        (List.append (afterAcceptTail.map some) commonRightPadding)
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      acceptThroughSentinelRestoreDescription_subroutineReady
      blankRightWalkerDescription_subroutineReady
      (acceptThroughSentinelRestoreDescription_haltsFrom p)
      hbridge hwalk

theorem acceptThroughRejectConfigScanDescription_haltsFrom
    (p : SelectedMergeEmitterPayload) :
    acceptThroughRejectConfigScanDescription.HaltsFromTape
      (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)
      (acceptAfterRejectConfigTape p) := by
  rcases
      cellFieldBits_cons_false (some p.L.acceptHit)
        (acceptAfterAcceptHitSuffixBits p) with
    ⟨suffixTail, hhit⟩
  have hsuffix :
      acceptAfterRejectConfigSuffixBits p = false :: suffixTail := by
    rw [acceptAfterRejectConfigSuffixBits_eq_acceptHit]
    exact hhit
  have hsourceBits :
      commonAfterAcceptConfigSuffixBits p =
        configurationFieldBits p.L.rejectConfig
          (false :: suffixTail) := by
    rw [commonAfterAcceptConfigSuffixBits_eq_rejectConfig, hsuffix]
  have hbridge :
      Tape.move Direction.left
          (Tape.move Direction.right (acceptAfterBlankWalkTape p)) =
        acceptAfterBlankWalkTape p := by
    rcases
        configurationFieldBits_false_false_tail p.L.rejectConfig
          (false :: suffixTail) with
      ⟨fieldTail, hfield⟩
    rw [acceptAfterBlankWalkTape, hsourceBits, hfield]
    simp [CommonGround.FiniteTransducers.tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]
  have hrestoredLeft :
      cellListCanonicalRestoredLeftWithBase p.L.rejectConfig.tape.right
          (List.append
            ((cellCodeBits p.L.rejectConfig.tape.head).reverse.map some)
            (cellListCanonicalRestoredLeftWithBase p.L.rejectConfig.tape.left
              (List.append
                ((stageNatBits p.L.rejectConfig.state).reverse.map some)
                (acceptAfterBlankWalkBaseLeft p)))) =
        List.append
          ((configurationFieldBits p.L.rejectConfig []).reverse.map some)
          (acceptAfterBlankWalkBaseLeft p) := by
    rw [← configurationRestoredLeftWithBase_eq_fieldBits_reverse_append]
    rfl
  have hscan :
      SelectedMergePaddedEmitterConfigScannerDescription.HaltsFromTape
        (acceptAfterBlankWalkTape p) (acceptAfterRejectConfigTape p) := by
    rcases
        run_configurationSuffix_raw_to_handoff_withBaseAndRight
      p.L.rejectConfig (acceptAfterBlankWalkBaseLeft p)
          suffixTail commonRightPadding with
      ⟨steps, hsteps⟩
    have htarget :
        (cellListCanonicalHandoffConfigWithBaseAndRight
          p.L.rejectConfig.tape.right
          (List.append
            ((cellCodeBits p.L.rejectConfig.tape.head).reverse.map some)
            (cellListCanonicalRestoredLeftWithBase p.L.rejectConfig.tape.left
              (List.append
                ((stageNatBits p.L.rejectConfig.state).reverse.map some)
                (acceptAfterBlankWalkBaseLeft p))))
          (false :: suffixTail) commonRightPadding).tape =
            acceptAfterRejectConfigTape p := by
      rw [cellListCanonicalHandoffConfigWithBaseAndRight, hrestoredLeft]
      simp [acceptAfterRejectConfigTape,
        SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits,
        hsuffix, CommonGround.FiniteTransducers.tapeAtCells,
        DovetailInitialLayoutInitializer.tapeAtCells,
        List.map_append, List.map_reverse, List.append_assoc]
    refine ⟨steps, ?_⟩
    constructor
    · simpa [MachineDescription.HaltsFromTapeIn,
        SelectedMergePaddedEmitterConfigScannerDescription,
        acceptAfterBlankWalkTape, hsourceBits,
        DovetailInitialLayoutInitializer.config,
        List.map_append, List.append_assoc] using!
          congrArg Configuration.state hsteps
    · exact Eq.trans
        (by simpa [MachineDescription.HaltsFromTapeIn,
          SelectedMergePaddedEmitterConfigScannerDescription,
          acceptAfterBlankWalkTape, hsourceBits,
          DovetailInitialLayoutInitializer.config,
          List.map_append, List.append_assoc] using!
            congrArg Configuration.tape hsteps)
        htarget
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      acceptThroughBlankWalkDescription_subroutineReady
      selectedMergePaddedEmitterConfigScanner_subroutineReady
      (acceptThroughBlankWalkDescription_haltsFrom p)
      hbridge hscan

theorem acceptAfterRejectConfigTape_move_right
    (p : SelectedMergeEmitterPayload) :
    Tape.move Direction.right (acceptAfterRejectConfigTape p) =
      acceptRejectConfigHandoffTape p := by
  rcases configurationFieldBits_eq_reverse_cons_cons p.L.rejectConfig with
    ⟨x, y, rest, hfield⟩
  simpa [acceptAfterRejectConfigTape, acceptRejectConfigHandoffTape,
    SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits, hfield,
    List.map_reverse] using
      (CommonGround.FiniteTransducers.tapeAtCells_move_right_move_left_append_cons
        ([] : List (Option Bool))
        (some y :: List.append (rest.map some)
          (acceptAfterBlankWalkBaseLeft p))
        (List.append ((acceptAfterRejectConfigSuffixBits p).map some)
          commonRightPadding)
        (some x))

theorem acceptThroughMidEraseDescription_haltsFrom
    (p : SelectedMergeEmitterPayload) :
    acceptThroughMidEraseDescription.HaltsFromTape
      (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)
      (acceptAfterMidTape p) := by
  have hmid :
      acceptMidEraserDescription.HaltsFromTape
        (acceptRejectConfigHandoffTape p) (acceptAfterMidTape p) := by
    apply haltsFromTape_of_reaches
    simpa [acceptRejectConfigHandoffTape, acceptAfterMidTape,
      acceptAfterMidBaseLeft, acceptAfterBlankWalkBaseLeft,
      acceptAfterRejectConfigSuffixBits,
      acceptAfterAcceptHitSuffixBits, acceptOuterConfigHitBits,
      SelectedMergePaddedEmitterParsedInnerAcceptHitFieldBits,
      SelectedMergePaddedEmitterParsedInnerRejectHitFieldBits,
      SelectedMergePaddedEmitterParsedInnerOuterStageFieldBits,
      SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits,
      SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits,
      boolFieldBits_eq_four, stageNatBits_length,
      acceptMidEraserDescription,
      List.map_append, List.append_assoc] using
        acceptMidEraser_run
          false true p.L.acceptHit (!p.L.acceptHit)
          false true p.L.rejectHit (!p.L.rejectHit)
          p.S.stage
          (List.append
            ((SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).reverse.map
              some)
            (acceptAfterBlankWalkBaseLeft p))
          (List.append ((acceptOuterConfigHitBits p).map some)
            commonRightPadding)
  exact
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      acceptThroughRejectConfigScanDescription_subroutineReady
      acceptMidEraserDescription_subroutineReady
      (acceptThroughRejectConfigScanDescription_haltsFrom p)
      (acceptAfterRejectConfigTape_move_right p)
      hmid

theorem acceptThroughOuterConfigScanDescription_haltsFrom
    (p : SelectedMergeEmitterPayload) :
    acceptThroughOuterConfigScanDescription.HaltsFromTape
      (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)
      (acceptAfterOuterConfigTape p) := by
  rcases cellFieldBits_cons_false (some p.S.hit) [] with
    ⟨suffixTail, hhit⟩
  have hsuffix :
      SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits p =
        false :: suffixTail := by
    unfold Word at hhit ⊢
    simpa [SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits,
      boolFieldBits] using hhit
  have hsourceBits :
      acceptOuterConfigHitBits p =
        configurationFieldBits p.S.config (false :: suffixTail) := by
    unfold Word
    simpa [acceptOuterConfigHitBits,
      SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits, hsuffix] using
        (configurationFieldBits_append_nil p.S.config
          (false :: suffixTail))
  have hbridge :
      Tape.move Direction.left
          (Tape.move Direction.right (acceptAfterMidTape p)) =
        acceptAfterMidTape p := by
    rcases
        configurationFieldBits_false_false_tail p.S.config
          (false :: suffixTail) with
      ⟨fieldTail, hfield⟩
    rw [acceptAfterMidTape, hsourceBits, hfield]
    simp [CommonGround.FiniteTransducers.tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]
  have hrestoredLeft :
      cellListCanonicalRestoredLeftWithBase p.S.config.tape.right
          (List.append
            ((cellCodeBits p.S.config.tape.head).reverse.map some)
            (cellListCanonicalRestoredLeftWithBase p.S.config.tape.left
              (List.append
                ((stageNatBits p.S.config.state).reverse.map some)
                (acceptAfterMidBaseLeft p)))) =
        List.append
          ((configurationFieldBits p.S.config []).reverse.map some)
          (acceptAfterMidBaseLeft p) := by
    rw [← configurationRestoredLeftWithBase_eq_fieldBits_reverse_append]
    rfl
  have hscan :
      SelectedMergePaddedEmitterConfigScannerDescription.HaltsFromTape
        (acceptAfterMidTape p) (acceptAfterOuterConfigTape p) := by
    rcases
        run_configurationSuffix_raw_to_handoff_withBaseAndRight
          p.S.config (acceptAfterMidBaseLeft p)
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
                (acceptAfterMidBaseLeft p))))
          (false :: suffixTail) commonRightPadding).tape =
            acceptAfterOuterConfigTape p := by
      rw [cellListCanonicalHandoffConfigWithBaseAndRight, hrestoredLeft]
      simp [acceptAfterOuterConfigTape,
        SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits,
        hsuffix, CommonGround.FiniteTransducers.tapeAtCells,
        DovetailInitialLayoutInitializer.tapeAtCells,
        List.map_reverse]
    refine ⟨steps, ?_⟩
    constructor
    · simpa [MachineDescription.HaltsFromTapeIn,
        SelectedMergePaddedEmitterConfigScannerDescription,
        acceptAfterMidTape, hsourceBits,
        DovetailInitialLayoutInitializer.config,
        List.map_append, List.append_assoc] using!
          congrArg Configuration.state hsteps
    · exact Eq.trans
        (by simpa [MachineDescription.HaltsFromTapeIn,
          SelectedMergePaddedEmitterConfigScannerDescription,
          acceptAfterMidTape, hsourceBits,
          DovetailInitialLayoutInitializer.config,
          List.map_append, List.append_assoc] using!
            congrArg Configuration.tape hsteps)
        htarget
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      acceptThroughMidEraseDescription_subroutineReady
      selectedMergePaddedEmitterConfigScanner_subroutineReady
      (acceptThroughMidEraseDescription_haltsFrom p)
      hbridge hscan

theorem acceptAfterOuterConfigTape_move_right
    (p : SelectedMergeEmitterPayload) :
    Tape.move Direction.right (acceptAfterOuterConfigTape p) =
      acceptOuterConfigHandoffTape p := by
  rcases configurationFieldBits_eq_reverse_cons_cons p.S.config with
    ⟨x, y, rest, hfield⟩
  simpa [acceptAfterOuterConfigTape, acceptOuterConfigHandoffTape,
    SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits, hfield,
    List.map_reverse] using
      (CommonGround.FiniteTransducers.tapeAtCells_move_right_move_left_append_cons
        ([] : List (Option Bool))
        (some y :: List.append (rest.map some) (acceptAfterMidBaseLeft p))
        (List.append
          ((SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits p).map some)
          commonRightPadding)
        (some x))

theorem acceptHitScannerDescription_haltsFrom
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterHitScannerDescription.HaltsFromTape
      (acceptOuterConfigHandoffTape p) (acceptAfterHitTape p) := by
  have hrun :=
    selectedMergePaddedEmitterHitScanner_runConfig_withRight
      p.S.hit
      (List.append
        ((SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).reverse.map
          some)
        (acceptAfterMidBaseLeft p))
      commonRightPadding
  have hsource :
      DovetailInitialLayoutInitializer.config 0
        (List.append
          ((SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).reverse.map
            some)
          (acceptAfterMidBaseLeft p))
        (List.append
          ((encodeCodeWordAsInput (encodeBoolAppend p.S.hit [])).map some)
          commonRightPadding) =
        { state := 0, tape := acceptOuterConfigHandoffTape p } := by
    simp [acceptOuterConfigHandoffTape,
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
          ((encodeCodeWordAsInput (encodeBoolAppend p.S.hit [])).reverse.map
            some)
          (List.append
            ((SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).reverse.map
              some)
            (acceptAfterMidBaseLeft p)))
        commonRightPadding =
        { state := 5, tape := acceptAfterHitTape p } := by
    simp [acceptAfterHitTape, acceptAfterHitLeft, acceptAfterMidBaseLeft,
      acceptAfterBlankWalkBaseLeft, acceptPrefixBaseLeft,
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

theorem acceptDeleteDescription_haltsFrom
    (p : SelectedMergeEmitterPayload) :
    acceptDeleteDescription.HaltsFromTape
      (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)
      (acceptAfterHitTape p) := by
  exact
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      acceptThroughOuterConfigScanDescription_subroutineReady
      selectedMergePaddedEmitterHitScanner_subroutineReady
      (acceptThroughOuterConfigScanDescription_haltsFrom p)
      (acceptAfterOuterConfigTape_move_right p)
      (acceptHitScannerDescription_haltsFrom p)

end ParsedInnerTransport
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
