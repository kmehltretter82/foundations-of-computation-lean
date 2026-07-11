import FoC.Computability.Compiler.ClosedCfg.PostTrans.Core
import FoC.Computability.Compiler.ClosedCfg.PostTrans.ParsedInnerTransport.Shapes
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.OneGapCompactor

set_option doc.verso true

/-!
# Parsed-inner transport common schedule

The accepting and rejecting transports share the entry rewind, bool-word
input scan, and inner-stage scan.  This module packages that common finite
machine prefix and its exact endpoint.
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

def commonRightPadding : List (Option Bool) :=
  List.replicate 6 none

def commonTransitionBaseLeft : List (Option Bool) :=
  List.append
    ((encodeCodeSymbolAsInput MachineCodeSymbol.transition).reverse.map some)
    [none]

def commonAfterStageSuffixBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  List.append
    (SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits p)
    (List.append
      (SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p)
      (List.append
        (SelectedMergePaddedEmitterParsedInnerAcceptHitFieldBits p)
        (List.append
          (SelectedMergePaddedEmitterParsedInnerRejectHitFieldBits p)
          (List.append
            (SelectedMergePaddedEmitterParsedInnerOuterStageFieldBits p)
            (List.append
              (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
              (SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits p))))))

def commonAfterAcceptConfigSuffixBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  List.append
    (SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p)
    (List.append
      (SelectedMergePaddedEmitterParsedInnerAcceptHitFieldBits p)
      (List.append
        (SelectedMergePaddedEmitterParsedInnerRejectHitFieldBits p)
        (List.append
          (SelectedMergePaddedEmitterParsedInnerOuterStageFieldBits p)
          (List.append
            (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
            (SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits p)))))

theorem commonAfterStageSuffixBits_eq_acceptConfig
    (p : SelectedMergeEmitterPayload) :
    commonAfterStageSuffixBits p =
      configurationFieldBits p.L.acceptConfig
        (commonAfterAcceptConfigSuffixBits p) := by
  unfold Word
  simpa [commonAfterStageSuffixBits, commonAfterAcceptConfigSuffixBits,
    SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits] using
      (configurationFieldBits_append_nil p.L.acceptConfig
        (commonAfterAcceptConfigSuffixBits p))

def commonPostTransitionBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  boolWordFieldBits p.L.input
    (List.append (stageNatBits p.L.stage)
      (commonAfterStageSuffixBits p))

def commonInputSourceTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  tapeAtCells commonTransitionBaseLeft
    (List.append ((commonPostTransitionBits p).map some)
      commonRightPadding)

def commonInputRestoredBaseLeft
    (p : SelectedMergeEmitterPayload) : List (Option Bool) :=
  cellListCanonicalRestoredLeftWithBase
    (p.L.input.map some) commonTransitionBaseLeft

def commonAfterInputTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  (boolWordCanonicalHandoffConfigWithBaseAndRight
    p.L.input commonTransitionBaseLeft
    (List.append (stageNatBits p.L.stage)
      (commonAfterStageSuffixBits p))
    commonRightPadding).tape

def commonStageSourceTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  tapeAtCells (commonInputRestoredBaseLeft p)
    (List.append
      ((List.append (stageNatBits p.L.stage)
        (commonAfterStageSuffixBits p)).map some)
      commonRightPadding)

def commonAfterStageTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  (CanonicalLayouts.DovetailStagePrefix.nonemptyNatSuffixHandoffConfigWithBaseAndRight
    p.L.stage (commonInputRestoredBaseLeft p)
    (commonAfterStageSuffixBits p) commonRightPadding).tape

theorem commonStageRestoredBase_eq_outputPrefix_reverse_append_none
    (p : SelectedMergeEmitterPayload) :
    List.append ((stageNatBits p.L.stage).reverse.map some)
        (commonInputRestoredBaseLeft p) =
      List.append
        ((SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p).reverse.map
          some)
        [none] := by
  rw [commonInputRestoredBaseLeft,
    cellListCanonicalRestoredLeftWithBase_eq_fieldBits_reverse_append]
  simp [commonTransitionBaseLeft,
    SelectedMergePaddedEmitterParsedInnerOutputPrefixBits,
    boolWordFieldBits, cellListFieldBits, encodeCodeSymbolAsInput,
    List.map_append, List.map_reverse, List.reverse_append,
    List.append_assoc]

def commonEntryInputDescription : MachineDescription :=
  canonicalSeqDescription
    transportEntryDescription
    SelectedMergePaddedEmitterInputScannerDescription

def commonScheduleDescription : MachineDescription :=
  seqSubroutine
    commonEntryInputDescription
    SelectedMergePaddedEmitterStageScannerDescription
    Direction.right

theorem commonEntryInputDescription_subroutineReady :
    commonEntryInputDescription.SubroutineReady := by
  exact
    canonicalSeqDescription_subroutineReady
      transportEntryDescription_subroutineReady
      selectedMergePaddedEmitterInputScanner_subroutineReady

theorem commonScheduleDescription_subroutineReady :
    commonScheduleDescription.SubroutineReady := by
  exact
    seqSubroutine_subroutineReady
      commonEntryInputDescription_subroutineReady
      selectedMergePaddedEmitterStageScanner_subroutineReady

theorem commonPostTransitionBits_ne_nil
    (p : SelectedMergeEmitterPayload) :
    commonPostTransitionBits p ≠ [] := by
  rcases
      cellListFieldBits_cons_false
        (p.L.input.map some)
        (List.append (stageNatBits p.L.stage)
          (commonAfterStageSuffixBits p)) with
    ⟨tail, htail⟩
  rw [commonPostTransitionBits, boolWordFieldBits, htail]
  simp

theorem commonPostTransitionBits_eq_entrySplit
    (p : SelectedMergeEmitterPayload) :
    commonPostTransitionBits p =
      List.append
        (SelectedMergePaddedEmitterParsedInnerRightStackRest
          (commonPostTransitionBits p)).reverse
        [SelectedMergePaddedEmitterParsedInnerRightStackCurrent
          (commonPostTransitionBits p)] := by
  have h :=
    SelectedMergePaddedEmitterParsedInnerRightStackCurrentRest_reverse
      (commonPostTransitionBits_ne_nil p)
  unfold Word at *
  simpa using h.symm

theorem postPrefixSourceBits_eq_transition_common
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerPostPrefixSourceBits p =
      List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
        (commonPostTransitionBits p) := by
  simp [postPrefixSourceBits_eq_fields, commonPostTransitionBits,
    commonAfterStageSuffixBits,
    SelectedMergePaddedEmitterParsedInnerOutputPrefixBits,
    boolWordFieldBits, cellListFieldBits, List.append_assoc]

theorem transportEntryDescription_haltsFrom_postPrefixSource
    (p : SelectedMergeEmitterPayload) :
    transportEntryDescription.HaltsFromTape
      (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)
      (commonInputSourceTape p) := by
  let last :=
    SelectedMergePaddedEmitterParsedInnerRightStackCurrent
      (commonPostTransitionBits p)
  let mid :=
    (SelectedMergePaddedEmitterParsedInnerRightStackRest
      (commonPostTransitionBits p)).reverse
  have hsplit :
      commonPostTransitionBits p = List.append mid [last] := by
    simpa [mid, last] using commonPostTransitionBits_eq_entrySplit p
  have hrun :=
    haltsFromTape_of_reaches
      (transportEntry_run mid last)
  simpa [SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape,
    CommonGround.FiniteTransducers.leadingBlankLeftShiftTargetTapeWithPadding,
    postPrefixSourceBits_eq_transition_common, commonInputSourceTape,
    commonTransitionBaseLeft, commonRightPadding,
    SelectedMergePaddedEmitterParsedInnerRemainderDeleteBits,
    CanonicalLayouts.DovetailLayoutScanner.transitionRemainderBits,
    encodeCodeSymbolAsInput, hsplit, tapeSeenLeft,
    CommonGround.FiniteTransducers.tapeAtCells, List.map_append,
    List.append_assoc, List.replicate] using hrun

theorem inputScannerDescription_haltsFrom_commonSource
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterInputScannerDescription.HaltsFromTape
      (commonInputSourceTape p)
      (commonAfterInputTape p) := by
  rcases stageNatBits_cons_false p.L.stage with ⟨tail, hstage⟩
  let suffixTail : Word Bool :=
    List.append tail (commonAfterStageSuffixBits p)
  have hsuffix :
      List.append (stageNatBits p.L.stage)
          (commonAfterStageSuffixBits p) =
        false :: suffixTail := by
    simp [suffixTail, hstage]
  rcases
      run_cellList_raw_to_canonical_handoff_withBaseAndRight
        (p.L.input.map some) commonTransitionBaseLeft
        suffixTail commonRightPadding with
    ⟨steps, hsteps⟩
  let rawSource : Tape Bool :=
    (DovetailInitialLayoutInitializer.config 100
      commonTransitionBaseLeft
      (List.append
        ((stageNatBits (p.L.input.map some).length).map some)
        (List.append ((cellsCodeBits (p.L.input.map some)).map some)
          (some false ::
            List.append (suffixTail.map some) commonRightPadding)))).tape
  let rawTarget : Tape Bool :=
    (cellListCanonicalHandoffConfigWithBaseAndRight
      (p.L.input.map some) commonTransitionBaseLeft
      (false :: suffixTail) commonRightPadding).tape
  have hraw :
      SelectedMergePaddedEmitterInputScannerDescription.HaltsFromTape
        rawSource rawTarget := by
    refine ⟨steps, ?_⟩
    constructor
    · simpa [MachineDescription.HaltsFromTapeIn,
        SelectedMergePaddedEmitterInputScannerDescription,
        rawSource, rawTarget] using!
          congrArg Configuration.state hsteps
    · simpa [MachineDescription.HaltsFromTapeIn,
        SelectedMergePaddedEmitterInputScannerDescription,
        rawSource, rawTarget] using!
          congrArg Configuration.tape hsteps
  have hsource : commonInputSourceTape p = rawSource := by
    rw [commonInputSourceTape, commonPostTransitionBits,
      boolWordFieldBits, cellListFieldBits, hsuffix]
    simp [rawSource,
      DovetailInitialLayoutInitializer.config,
      CommonGround.FiniteTransducers.tapeAtCells,
      DovetailInitialLayoutInitializer.tapeAtCells,
      List.map_append, List.append_assoc]
    rfl
  have htarget : commonAfterInputTape p = rawTarget := by
    unfold commonAfterInputTape rawTarget
    rw [hsuffix]
    rfl
  simpa [hsource, htarget] using hraw

theorem commonAfterInputTape_move_right
    (p : SelectedMergeEmitterPayload) :
    Tape.move Direction.right (commonAfterInputTape p) =
      commonStageSourceTape p := by
  rcases stageNatBits_cons_false p.L.stage with ⟨tail, hstage⟩
  let suffixTail : Word Bool :=
    List.append tail (commonAfterStageSuffixBits p)
  have hsuffix :
      List.append (stageNatBits p.L.stage)
          (commonAfterStageSuffixBits p) =
        false :: suffixTail := by
    simp [suffixTail, hstage]
  rw [commonAfterInputTape, commonStageSourceTape, hsuffix]
  simpa [boolWordCanonicalHandoffConfigWithBaseAndRight,
    commonInputRestoredBaseLeft,
    CommonGround.FiniteTransducers.tapeAtCells,
    DovetailInitialLayoutInitializer.tapeAtCells] using
      cellListCanonicalHandoffConfigWithBaseAndRight_move_right
        (p.L.input.map some) commonTransitionBaseLeft
        false suffixTail commonRightPadding

theorem stageScannerDescription_haltsFrom_commonSource
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterStageScannerDescription.HaltsFromTape
      (commonStageSourceTape p)
      (commonAfterStageTape p) := by
  rcases
      configurationFieldBits_cons_false p.L.acceptConfig
        (commonAfterAcceptConfigSuffixBits p) with
    ⟨suffixTail, hsuffixCfg⟩
  have hsuffix :
      commonAfterStageSuffixBits p = false :: suffixTail := by
    rw [commonAfterStageSuffixBits_eq_acceptConfig]
    exact hsuffixCfg
  rcases
      CanonicalLayouts.DovetailStagePrefix.run_nonemptyNatSuffix_raw_to_handoff_withBaseAndRight
        p.L.stage (commonInputRestoredBaseLeft p)
        false suffixTail commonRightPadding with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [MachineDescription.HaltsFromTapeIn,
      SelectedMergePaddedEmitterStageScannerDescription,
      commonStageSourceTape, commonAfterStageTape, hsuffix,
      DovetailInitialLayoutInitializer.config,
      List.map_append, List.append_assoc] using!
        congrArg Configuration.state hsteps
  · simpa [MachineDescription.HaltsFromTapeIn,
      SelectedMergePaddedEmitterStageScannerDescription,
      commonStageSourceTape, commonAfterStageTape, hsuffix,
      DovetailInitialLayoutInitializer.config,
      CommonGround.FiniteTransducers.tapeAtCells,
      DovetailInitialLayoutInitializer.tapeAtCells,
      List.map_append, List.append_assoc] using!
        congrArg Configuration.tape hsteps

theorem commonInputSourceTape_move_left_move_right
    (p : SelectedMergeEmitterPayload) :
    Tape.move Direction.left
        (Tape.move Direction.right (commonInputSourceTape p)) =
      commonInputSourceTape p := by
  rcases stageNatBits_false_false_tail (p.L.input.map some).length with
    ⟨tail, htail⟩
  rw [commonInputSourceTape, commonPostTransitionBits,
    boolWordFieldBits, cellListFieldBits, htail]
  simp [
    CommonGround.FiniteTransducers.tapeAtCells,
    Tape.move, Tape.moveLeft, Tape.moveRight, List.map_append,
    List.append_assoc]

theorem commonScheduleDescription_haltsFrom
    (p : SelectedMergeEmitterPayload) :
    commonScheduleDescription.HaltsFromTape
      (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)
      (commonAfterStageTape p) := by
  have hentryInput :
      commonEntryInputDescription.HaltsFromTape
        (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)
        (commonAfterInputTape p) := by
    exact
      canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        transportEntryDescription_subroutineReady
        selectedMergePaddedEmitterInputScanner_subroutineReady
        (transportEntryDescription_haltsFrom_postPrefixSource p)
        (commonInputSourceTape_move_left_move_right p)
        (inputScannerDescription_haltsFrom_commonSource p)
  exact
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      commonEntryInputDescription_subroutineReady
      selectedMergePaddedEmitterStageScanner_subroutineReady
      hentryInput
      (commonAfterInputTape_move_right p)
      (stageScannerDescription_haltsFrom_commonSource p)

theorem dropTrailingNone_append_of_all_none
    (xs pad : List (Option Bool))
    (hpad : ∀ z ∈ pad, z = none) :
    Tape.dropTrailingNone (xs ++ pad) = Tape.dropTrailingNone xs := by
  have hrep : pad = List.replicate pad.length none := by
    induction pad with
    | nil => rfl
    | cons a rest ih =>
      have ha : a = none := hpad a (by simp)
      have hr : ∀ z ∈ rest, z = none := by
        intro z hz
        exact hpad z (by simp [hz])
      rw [ha]
      simp only [List.length_cons, List.replicate_succ]
      exact congrArg (List.cons (none : Option Bool)) (ih hr)
  rw [hrep]
  exact FoC.Computability.dropTrailingNone_append_replicate_none xs pad.length

theorem replicate_add_none (m n : Nat) :
    List.replicate (m + n) (none : Option Bool) =
      List.append (List.replicate m none) (List.replicate n none) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_add, List.replicate_succ, List.replicate_succ, ih]
    rfl

end ParsedInnerTransport
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
