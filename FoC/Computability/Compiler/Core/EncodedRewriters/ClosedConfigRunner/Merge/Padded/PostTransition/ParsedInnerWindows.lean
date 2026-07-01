import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.DeleteWindow
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.OneGapCompactor
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Merge.Padded.PostTransition.BranchHandoffShape

set_option doc.verso true

/-!
# Merge post-transition parsed-inner windows

The parsed-inner emitter does not merely copy an encoded transition word.  Its
source is the checked scanner shape: after the outer transition symbol, the
nested layout body still begins with the scanner-local transition remainder.
The target is the ordinary emitted transition code word, so the finite-machine
leaf must delete that marked-body remainder while it replaces the selected
inner config/hit fields with the outer simulator config/hit fields.

This module names those source and target windows without choosing the concrete
finite-machine route.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

def SelectedMergePaddedEmitterParsedInnerMarkedPrefixBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  List.append
    (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
    (List.append
      CanonicalLayouts.DovetailLayoutScanner.transitionRemainderBits
      (CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits
        p.L.input
        (FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          p.L.stage)))

def SelectedMergePaddedEmitterParsedInnerOutputPrefixBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  List.append
    (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
    (CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits
      p.L.input
      (FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        p.L.stage))

def SelectedMergePaddedEmitterParsedInnerSourceFieldTailBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
    p.L.acceptConfig
    (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
      p.L.rejectConfig
      (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
        p.L.acceptHit
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          p.L.rejectHit
          (SelectedMergePaddedEmitterParsedInnerOuterSuffixBits p))))

def SelectedMergePaddedEmitterParsedInnerTargetFieldTailBits
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) : Word Bool :=
  CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
    (SelectedMergeOutputAcceptConfig useAccept p.S p.L)
    (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
      (SelectedMergeOutputRejectConfig useAccept p.S p.L)
      (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
        (SelectedMergeOutputAcceptHit useAccept p.S p.L)
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          (SelectedMergeOutputRejectHit useAccept p.S p.L)
          [])))

def SelectedMergePaddedEmitterParsedInnerOuterConfigHitBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
    p.S.config
    (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits p.S.hit [])

def SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
    p.L.acceptConfig []

def SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
    p.L.rejectConfig []

def SelectedMergePaddedEmitterParsedInnerAcceptHitFieldBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  CanonicalLayouts.DovetailLayoutScanner.boolFieldBits p.L.acceptHit []

def SelectedMergePaddedEmitterParsedInnerRejectHitFieldBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  CanonicalLayouts.DovetailLayoutScanner.boolFieldBits p.L.rejectHit []

def SelectedMergePaddedEmitterParsedInnerOuterStageFieldBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
    p.S.stage

def SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
    p.S.config []

def SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  CanonicalLayouts.DovetailLayoutScanner.boolFieldBits p.S.hit []

def SelectedMergePaddedEmitterParsedInnerSourceFieldTailExpandedBits
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
              (SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits
                p))))))

def SelectedMergePaddedEmitterParsedInnerTargetFieldTailExpandedBits
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) : Word Bool :=
  if useAccept then
    List.append
      (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
      (List.append
        (SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p)
        (List.append
          (SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits p)
          (SelectedMergePaddedEmitterParsedInnerRejectHitFieldBits p)))
  else
    List.append
      (SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits p)
      (List.append
        (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
        (List.append
          (SelectedMergePaddedEmitterParsedInnerAcceptHitFieldBits p)
          (SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits p)))

def SelectedMergePaddedEmitterParsedInnerSourceLeftCells
    (p : SelectedMergeEmitterPayload) : List (Option Bool) :=
  (((SelectedMergePaddedEmitterOuterHitSuffixBits p).reverse.map some) ++
    (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
      p.S.config
      (List.append
        ((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          p.S.stage).reverse.map some)
        (SelectedMergePaddedEmitterNestedLayoutParsedLeft p))))

def SelectedMergePaddedEmitterParsedInnerSourceCells
    (p : SelectedMergeEmitterPayload) : List (Option Bool) :=
  List.append
    (SelectedMergePaddedEmitterParsedInnerSourceLeftCells p).reverse
    [none, none]

def SelectedMergePaddedEmitterParsedInnerTargetPaddingCells
    (p : SelectedMergeEmitterPayload) : List (Option Bool) :=
  List.replicate (SimulatorLayout.asBoolInput p.S).length none

def SelectedMergePaddedEmitterParsedInnerTargetCells
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    List (Option Bool) :=
  List.append
    ((SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p).map some)
    (List.append
      ((SelectedMergePaddedEmitterParsedInnerTargetFieldTailBits
        useAccept p).map some)
      (SelectedMergePaddedEmitterParsedInnerTargetPaddingCells p))

def SelectedMergePaddedEmitterParsedInnerSourceSplitCells
    (p : SelectedMergeEmitterPayload) : List (Option Bool) :=
  List.append
    [none]
    (List.append
      ((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some)
      (List.append
        [none]
        (List.append
          ((SelectedMergePaddedEmitterParsedInnerSourceTailBits p).map some)
          [none, none])))

def SelectedMergePaddedEmitterParsedInnerTargetSplitCells
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    List (Option Bool) :=
  List.append
    ((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some)
    (List.append
      ((SelectedMergePaddedEmitterParsedInnerTargetTailBits
        useAccept p).map some)
      (SelectedMergePaddedEmitterParsedInnerTargetPaddingCells p))

def SelectedMergePaddedEmitterParsedInnerRightStackCurrent
    (bits : Word Bool) : Bool :=
  match bits.reverse with
  | [] => false
  | bit :: _ => bit

def SelectedMergePaddedEmitterParsedInnerRightStackRest
    (bits : Word Bool) : Word Bool :=
  match bits.reverse with
  | [] => []
  | _ :: rest => rest

theorem
    SelectedMergePaddedEmitterParsedInnerRightStackCurrentRest_reverse
    {bits : Word Bool} (hbits : bits ≠ []) :
    (SelectedMergePaddedEmitterParsedInnerRightStackCurrent bits ::
        SelectedMergePaddedEmitterParsedInnerRightStackRest bits).reverse =
      bits := by
  cases hrev : bits.reverse with
  | nil =>
      have hnil : bits = [] := by
        rw [← List.reverse_reverse bits]
        simp [hrev]
      exact (hbits hnil).elim
  | cons bit rest =>
      have hbitsEq : bits = (bit :: rest).reverse := by
        simpa using congrArg List.reverse hrev
      simp [SelectedMergePaddedEmitterParsedInnerRightStackCurrent,
        SelectedMergePaddedEmitterParsedInnerRightStackRest, hbitsEq]

def SelectedMergePaddedEmitterParsedInnerSourceTailCurrent
    (p : SelectedMergeEmitterPayload) : Bool :=
  SelectedMergePaddedEmitterParsedInnerRightStackCurrent
    (SelectedMergePaddedEmitterParsedInnerSourceTailBits p)

def SelectedMergePaddedEmitterParsedInnerSourceTailLeftRest
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  SelectedMergePaddedEmitterParsedInnerRightStackRest
    (SelectedMergePaddedEmitterParsedInnerSourceTailBits p)

def SelectedMergePaddedEmitterParsedInnerGapBaseLeft :
    List (Option Bool) :=
  SelectedMergePaddedEmitterOuterTransitionBaseLeft

def SelectedMergePaddedEmitterParsedInnerGapCompactorSourceTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  CommonGround.FiniteTransducers.rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
    SelectedMergePaddedEmitterParsedInnerGapBaseLeft
    (SelectedMergePaddedEmitterParsedInnerSourceTailCurrent p)
    (SelectedMergePaddedEmitterParsedInnerSourceTailLeftRest p)
    0 [none]

def SelectedMergePaddedEmitterParsedInnerGapCompactorTargetTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  CommonGround.FiniteTransducers.leadingBlankLeftShiftTargetTapeWithPadding
    SelectedMergePaddedEmitterParsedInnerGapBaseLeft
    (SelectedMergePaddedEmitterParsedInnerSourceTailBits p)
    [none]

def SelectedMergePaddedEmitterParsedInnerPostGapRewindSourceTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  CommonGround.FiniteTransducers.rightEdgeRewindSourceTapeWithBase
    []
    (SelectedMergePaddedEmitterParsedInnerSourceBits p)
    [none, none]

def SelectedMergePaddedEmitterParsedInnerDeleteSourceTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  CommonGround.FiniteTransducers.FSTStatefulOptionAppendSourceTapeWithPadding
    (SelectedMergePaddedEmitterParsedInnerSourceBits p)
    1
    [none, none]

def SelectedMergePaddedEmitterParsedInnerRemainderDeletePrefixBits :
    Word Bool :=
  encodeCodeSymbolAsInput MachineCodeSymbol.transition

def SelectedMergePaddedEmitterParsedInnerRemainderDeleteBits :
    Word Bool :=
  CanonicalLayouts.DovetailLayoutScanner.transitionRemainderBits

def SelectedMergePaddedEmitterParsedInnerRemainderDeleteSuffixBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  List.append
    (CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits
      p.L.input
      (FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        p.L.stage))
    (SelectedMergePaddedEmitterParsedInnerSourceFieldTailBits p)

def SelectedMergePaddedEmitterParsedInnerRemainderDeleteDescription :
    MachineDescription :=
  CommonGround.FiniteTransducers.generatedDeleteWindowDescription
    SelectedMergePaddedEmitterParsedInnerRemainderDeletePrefixBits.length
    SelectedMergePaddedEmitterParsedInnerRemainderDeleteBits.length

def SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  CommonGround.FiniteTransducers.FSTStatefulOptionAppendTargetTapeWithPadding
    (CommonGround.FiniteTransducers.deleteWindowNext
      SelectedMergePaddedEmitterParsedInnerRemainderDeletePrefixBits.length
      SelectedMergePaddedEmitterParsedInnerRemainderDeleteBits.length)
    (CommonGround.FiniteTransducers.deleteWindowEmit
      SelectedMergePaddedEmitterParsedInnerRemainderDeletePrefixBits.length
      SelectedMergePaddedEmitterParsedInnerRemainderDeleteBits.length)
    0
    (SelectedMergePaddedEmitterParsedInnerSourceBits p)
    1
    [none, none]

theorem
    SelectedMergePaddedEmitterParsedInnerOuterSuffixBits_eq_stage_outerConfigHit
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerOuterSuffixBits p =
      List.append
        (FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          p.S.stage)
        (SelectedMergePaddedEmitterParsedInnerOuterConfigHitBits p) := by
  simp [SelectedMergePaddedEmitterParsedInnerOuterSuffixBits,
    SelectedMergePaddedEmitterParsedInnerOuterConfigHitBits,
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.tapeFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.boolFieldBits]

theorem
    SelectedMergePaddedEmitterParsedInnerOuterConfigHitBits_eq_fields
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerOuterConfigHitBits p =
      List.append
        (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
        (SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits p) := by
  exact
    (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
      p.S.config
      (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
        p.S.hit [])).symm

theorem
    SelectedMergePaddedEmitterParsedInnerOuterSuffixBits_eq_expanded
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerOuterSuffixBits p =
      List.append
        (SelectedMergePaddedEmitterParsedInnerOuterStageFieldBits p)
        (List.append
          (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
          (SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits p)) := by
  rw [
    SelectedMergePaddedEmitterParsedInnerOuterSuffixBits_eq_stage_outerConfigHit,
    SelectedMergePaddedEmitterParsedInnerOuterConfigHitBits_eq_fields]
  simp [SelectedMergePaddedEmitterParsedInnerOuterStageFieldBits]

theorem
    SelectedMergePaddedEmitterParsedInnerSourceFieldTailExpandedBits_eq_sourceFieldTailBits
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerSourceFieldTailExpandedBits p =
      SelectedMergePaddedEmitterParsedInnerSourceFieldTailBits p := by
  rw [SelectedMergePaddedEmitterParsedInnerSourceFieldTailExpandedBits]
  rw [← SelectedMergePaddedEmitterParsedInnerOuterSuffixBits_eq_expanded]
  rw [SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits,
    SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits,
    SelectedMergePaddedEmitterParsedInnerAcceptHitFieldBits,
    SelectedMergePaddedEmitterParsedInnerRejectHitFieldBits]
  rw [
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
      p.L.acceptConfig]
  rw [
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
      p.L.rejectConfig]
  rw [show
      List.append
          (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            p.L.rejectHit [])
          (SelectedMergePaddedEmitterParsedInnerOuterSuffixBits p) =
        CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          p.L.rejectHit
          (SelectedMergePaddedEmitterParsedInnerOuterSuffixBits p) by
    simpa [CanonicalLayouts.DovetailLayoutScanner.boolFieldBits] using
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits_append_nil
        (some p.L.rejectHit)
        (SelectedMergePaddedEmitterParsedInnerOuterSuffixBits p)]
  rw [show
      List.append
          (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            p.L.acceptHit [])
          (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            p.L.rejectHit
            (SelectedMergePaddedEmitterParsedInnerOuterSuffixBits p)) =
        CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          p.L.acceptHit
          (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            p.L.rejectHit
            (SelectedMergePaddedEmitterParsedInnerOuterSuffixBits p)) by
    simpa [CanonicalLayouts.DovetailLayoutScanner.boolFieldBits] using
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits_append_nil
        (some p.L.acceptHit)
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          p.L.rejectHit
          (SelectedMergePaddedEmitterParsedInnerOuterSuffixBits p))]
  simp [SelectedMergePaddedEmitterParsedInnerSourceFieldTailBits]

theorem
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape_cells_eq_sourceWindow
    (p : SelectedMergeEmitterPayload) :
    Tape.cells
        (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p) =
      SelectedMergePaddedEmitterParsedInnerSourceCells p := by
  rw [SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape,
    SelectedMergePaddedEmitterParsedInnerSourceCells,
    SelectedMergePaddedEmitterParsedInnerSourceLeftCells]
  simp [DovetailInitialLayoutInitializer.tapeAtCells, Tape.cells]

theorem
    SelectedMergePaddedEmitterParsedInnerSourceCells_filterMap_eq_sourceBits
    (p : SelectedMergeEmitterPayload) :
    (SelectedMergePaddedEmitterParsedInnerSourceCells p).filterMap
        (fun cell => cell) =
      SelectedMergePaddedEmitterParsedInnerSourceBits p := by
  have hcells :=
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape_cells_eq_sourceWindow
      p
  have hnorm :=
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape_normalizedOutput_eq_sourceBits
      p
  rw [Tape.normalizedOutput] at hnorm
  rw [hcells] at hnorm
  exact hnorm

theorem
    SelectedMergePaddedEmitterParsedInnerSourceTailBits_ne_nil
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerSourceTailBits p ≠ [] := by
  simp [SelectedMergePaddedEmitterParsedInnerSourceTailBits,
    CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyBits,
    CanonicalLayouts.DovetailLayoutScanner.transitionRemainderBits]

theorem
    SelectedMergePaddedEmitterParsedInnerSourceTailCurrentRest_reverse
    (p : SelectedMergeEmitterPayload) :
    (SelectedMergePaddedEmitterParsedInnerSourceTailCurrent p ::
        SelectedMergePaddedEmitterParsedInnerSourceTailLeftRest p).reverse =
      SelectedMergePaddedEmitterParsedInnerSourceTailBits p := by
  exact
    SelectedMergePaddedEmitterParsedInnerRightStackCurrentRest_reverse
      (SelectedMergePaddedEmitterParsedInnerSourceTailBits_ne_nil p)

theorem
    SelectedMergePaddedEmitterParsedInnerSourceCells_eq_split
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerSourceCells p =
      SelectedMergePaddedEmitterParsedInnerSourceSplitCells p := by
  have hmarked :
      ((CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyRestoredBitsRev
        p.L).map some).reverse =
        (CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyBits
          p.L).map some := by
    rw [← List.map_reverse]
    rw [CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyRestoredBitsRev_reverse]
  have hcfg :
      ((CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev
        p.S.config).map some).reverse =
        (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
          p.S.config []).map some := by
    rw [← List.map_reverse]
    rw [CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev_reverse]
  have hcfgAppend :
      List.append
          (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            p.S.config [])
          (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits p.S.hit []) =
        CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
          p.S.config
          (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            p.S.hit []) :=
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
      p.S.config
      (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits p.S.hit [])
  have hcfgCellAppend :
      List.append
          (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            p.S.config [])
          (CanonicalLayouts.DovetailLayoutScanner.cellCodeBits
            (some p.S.hit)) =
        CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
          p.S.config
          (CanonicalLayouts.DovetailLayoutScanner.cellCodeBits
            (some p.S.hit)) := by
    simpa [CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits] using
      hcfgAppend
  have hcfgCellAppendMap :
      List.append
          ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            p.S.config []).map some)
          ((CanonicalLayouts.DovetailLayoutScanner.cellCodeBits
            (some p.S.hit)).map some) =
        (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
          p.S.config
          (CanonicalLayouts.DovetailLayoutScanner.cellCodeBits
            (some p.S.hit))).map some := by
    simpa [List.map_append] using
      congrArg (fun bits => bits.map some) hcfgCellAppend
  rw [SelectedMergePaddedEmitterParsedInnerSourceCells,
    SelectedMergePaddedEmitterParsedInnerSourceLeftCells]
  rw [←
    CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev_map_some_withBase]
  rw [SelectedMergePaddedEmitterNestedLayoutParsedLeft_eq_markedBodyRestoredBitsRev]
  simp [SelectedMergePaddedEmitterParsedInnerSourceSplitCells,
    SelectedMergePaddedEmitterParsedInnerSourceTailBits,
    SelectedMergePaddedEmitterParsedInnerOuterSuffixBits,
    SelectedMergePaddedEmitterNestedLayoutBodyBaseLeft,
    SelectedMergePaddedEmitterOuterTransitionBaseLeft,
    SelectedMergePaddedEmitterOuterHitSuffixBits,
    SelectedMergePaddedEmitterOuterHitSuffixCode,
    hmarked, hcfg,
    CanonicalLayouts.DovetailLayoutScanner.boolBits_eq_encodeBoolAppend,
    CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
    encodeCodeWordAsInput,
    List.reverse_append, List.map_append, List.map_reverse,
    List.append_assoc]
  simpa [List.append_assoc] using
    congrArg (fun cells => List.append cells [none, none])
      hcfgCellAppendMap

theorem
    SelectedMergePaddedEmitterParsedInnerSourceBits_eq_markedPrefix_fieldTail
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerSourceBits p =
      List.append
        (SelectedMergePaddedEmitterParsedInnerMarkedPrefixBits p)
        (SelectedMergePaddedEmitterParsedInnerSourceFieldTailBits p) := by
  rw [SelectedMergePaddedEmitterParsedInnerSourceBits_eq_nestedFields]
  simp [SelectedMergePaddedEmitterParsedInnerMarkedPrefixBits,
    SelectedMergePaddedEmitterParsedInnerSourceFieldTailBits,
    CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.tapeFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
    List.append_assoc]

theorem
    SelectedMergePaddedEmitterParsedInnerSourceTailBits_eq_markedBody_outerSuffix
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerSourceTailBits p =
      List.append
        CanonicalLayouts.DovetailLayoutScanner.transitionRemainderBits
        (List.append
          (CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits
            p.L.input
            (FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              p.L.stage))
          (SelectedMergePaddedEmitterParsedInnerSourceFieldTailBits p)) := by
  have h :=
    SelectedMergePaddedEmitterParsedInnerSourceBits_eq_markedPrefix_fieldTail
      p
  rw [SelectedMergePaddedEmitterParsedInnerSourceBits_eq_transition_tail] at h
  simp [SelectedMergePaddedEmitterParsedInnerMarkedPrefixBits,
    SelectedMergePaddedEmitterParsedInnerSourceTailBits,
    SelectedMergePaddedEmitterParsedInnerSourceFieldTailBits,
    CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyBits,
    CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.tapeFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
    List.append_assoc] at h ⊢

theorem
    SelectedMergePaddedEmitterParsedInnerSourceBits_eq_remainderDeleteSplit
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerSourceBits p =
      List.append
        SelectedMergePaddedEmitterParsedInnerRemainderDeletePrefixBits
        (List.append
          SelectedMergePaddedEmitterParsedInnerRemainderDeleteBits
          (SelectedMergePaddedEmitterParsedInnerRemainderDeleteSuffixBits
            p)) := by
  rw [SelectedMergePaddedEmitterParsedInnerSourceBits_eq_transition_tail]
  rw [SelectedMergePaddedEmitterParsedInnerSourceTailBits_eq_markedBody_outerSuffix]
  simp [SelectedMergePaddedEmitterParsedInnerRemainderDeletePrefixBits,
    SelectedMergePaddedEmitterParsedInnerRemainderDeleteBits,
    SelectedMergePaddedEmitterParsedInnerRemainderDeleteSuffixBits]

theorem
    SelectedMergePaddedEmitterParsedInnerTargetFieldTailBits_true
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerTargetFieldTailBits true p =
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
        p.S.config
        (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
          p.L.rejectConfig
          (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            p.S.hit
            (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
              p.L.rejectHit []))) := by
  rfl

theorem
    SelectedMergePaddedEmitterParsedInnerTargetFieldTailBits_false
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerTargetFieldTailBits false p =
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
        p.L.acceptConfig
        (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
          p.S.config
          (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            p.L.acceptHit
            (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
              p.S.hit []))) := by
  rfl

theorem
    SelectedMergePaddedEmitterParsedInnerTargetFieldTailExpandedBits_true_eq_targetFieldTailBits
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerTargetFieldTailExpandedBits true p =
      SelectedMergePaddedEmitterParsedInnerTargetFieldTailBits true p := by
  rw [SelectedMergePaddedEmitterParsedInnerTargetFieldTailExpandedBits]
  simp only [if_true]
  rw [SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits,
    SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits,
    SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits,
    SelectedMergePaddedEmitterParsedInnerRejectHitFieldBits]
  rw [
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
      p.S.config]
  rw [
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
      p.L.rejectConfig]
  rw [show
      List.append
          (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            p.S.hit [])
          (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            p.L.rejectHit []) =
        CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          p.S.hit
          (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            p.L.rejectHit []) by
    simpa [CanonicalLayouts.DovetailLayoutScanner.boolFieldBits] using
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits_append_nil
        (some p.S.hit)
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          p.L.rejectHit [])]
  rfl

theorem
    SelectedMergePaddedEmitterParsedInnerTargetFieldTailExpandedBits_false_eq_targetFieldTailBits
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerTargetFieldTailExpandedBits false p =
      SelectedMergePaddedEmitterParsedInnerTargetFieldTailBits false p := by
  rw [SelectedMergePaddedEmitterParsedInnerTargetFieldTailExpandedBits]
  rw [SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits,
    SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits,
    SelectedMergePaddedEmitterParsedInnerAcceptHitFieldBits,
    SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits]
  rw [
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
      p.L.acceptConfig]
  rw [
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
      p.S.config]
  rw [show
      List.append
          (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            p.L.acceptHit [])
          (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            p.S.hit []) =
        CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          p.L.acceptHit
          (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            p.S.hit []) by
    simpa [CanonicalLayouts.DovetailLayoutScanner.boolFieldBits] using
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits_append_nil
        (some p.L.acceptHit)
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          p.S.hit [])]
  rw [
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
      p.S.config]
  simp [SelectedMergePaddedEmitterParsedInnerTargetFieldTailBits_false]

theorem
    SelectedMergePaddedEmitterParsedInnerTargetFieldTailExpandedBits_eq_targetFieldTailBits
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerTargetFieldTailExpandedBits
        useAccept p =
      SelectedMergePaddedEmitterParsedInnerTargetFieldTailBits
        useAccept p := by
  cases useAccept
  · exact
      SelectedMergePaddedEmitterParsedInnerTargetFieldTailExpandedBits_false_eq_targetFieldTailBits
        p
  · exact
      SelectedMergePaddedEmitterParsedInnerTargetFieldTailExpandedBits_true_eq_targetFieldTailBits
        p

theorem
    SelectedMergePaddedEmitterDecodedHandoffBits_eq_outputPrefix_fieldTail
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterDecodedHandoffBits useAccept p =
      List.append
        (SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p)
        (SelectedMergePaddedEmitterParsedInnerTargetFieldTailBits
          useAccept p) := by
  cases useAccept
  · rw [SelectedMergePaddedEmitterDecodedHandoffBits_false_eq_fields]
    simp only [encodeCodeWordAsInput]
    rw [CanonicalLayouts.DovetailLayoutScanner.boolWordBits_eq_encodeBoolWordAppend]
    rw [CanonicalLayouts.DovetailStagePrefix.natBits_eq_encodeNatAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_eq_encodeConfigurationAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_eq_encodeConfigurationAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.boolBits_eq_encodeBoolAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.boolBits_eq_encodeBoolAppend]
    simp [SelectedMergePaddedEmitterParsedInnerOutputPrefixBits,
      SelectedMergePaddedEmitterParsedInnerTargetFieldTailBits,
      SelectedMergeOutputAcceptConfig, SelectedMergeOutputRejectConfig,
      SelectedMergeOutputAcceptHit, SelectedMergeOutputRejectHit,
      CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
      encodeCodeWordAsInput,
      List.append_assoc]
  · rw [SelectedMergePaddedEmitterDecodedHandoffBits_true_eq_fields]
    simp only [encodeCodeWordAsInput]
    rw [CanonicalLayouts.DovetailLayoutScanner.boolWordBits_eq_encodeBoolWordAppend]
    rw [CanonicalLayouts.DovetailStagePrefix.natBits_eq_encodeNatAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_eq_encodeConfigurationAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_eq_encodeConfigurationAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.boolBits_eq_encodeBoolAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.boolBits_eq_encodeBoolAppend]
    simp [SelectedMergePaddedEmitterParsedInnerOutputPrefixBits,
      SelectedMergePaddedEmitterParsedInnerTargetFieldTailBits,
      SelectedMergeOutputAcceptConfig, SelectedMergeOutputRejectConfig,
      SelectedMergeOutputAcceptHit, SelectedMergeOutputRejectHit,
      CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
      encodeCodeWordAsInput,
      List.append_assoc]

theorem
    SelectedMergePaddedEmitterDecodedHandoffBits_eq_outputPrefix_expandedTarget
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterDecodedHandoffBits useAccept p =
      List.append
        (SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p)
        (SelectedMergePaddedEmitterParsedInnerTargetFieldTailExpandedBits
          useAccept p) := by
  rw [SelectedMergePaddedEmitterDecodedHandoffBits_eq_outputPrefix_fieldTail]
  rw [
    SelectedMergePaddedEmitterParsedInnerTargetFieldTailExpandedBits_eq_targetFieldTailBits]

theorem
    SelectedMergePaddedEmitterParsedInnerTargetTailBits_eq_outputPrefixTail
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerTargetTailBits useAccept p =
      List.append
        (CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits
          p.L.input
          (FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            p.L.stage))
        (SelectedMergePaddedEmitterParsedInnerTargetFieldTailBits
          useAccept p) := by
  cases useAccept
  · rw [SelectedMergePaddedEmitterParsedInnerTargetTailBits_false]
    rw [CanonicalLayouts.DovetailLayoutScanner.boolWordBits_eq_encodeBoolWordAppend]
    rw [CanonicalLayouts.DovetailStagePrefix.natBits_eq_encodeNatAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_eq_encodeConfigurationAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_eq_encodeConfigurationAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.boolBits_eq_encodeBoolAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.boolBits_eq_encodeBoolAppend]
    simp [SelectedMergePaddedEmitterParsedInnerTargetFieldTailBits,
      SelectedMergeOutputAcceptConfig, SelectedMergeOutputRejectConfig,
      SelectedMergeOutputAcceptHit, SelectedMergeOutputRejectHit,
      CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
      encodeCodeWordAsInput, List.append_assoc]
  · rw [SelectedMergePaddedEmitterParsedInnerTargetTailBits_true]
    rw [CanonicalLayouts.DovetailLayoutScanner.boolWordBits_eq_encodeBoolWordAppend]
    rw [CanonicalLayouts.DovetailStagePrefix.natBits_eq_encodeNatAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_eq_encodeConfigurationAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_eq_encodeConfigurationAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.boolBits_eq_encodeBoolAppend]
    rw [CanonicalLayouts.DovetailLayoutScanner.boolBits_eq_encodeBoolAppend]
    simp [SelectedMergePaddedEmitterParsedInnerTargetFieldTailBits,
      SelectedMergeOutputAcceptConfig, SelectedMergeOutputRejectConfig,
      SelectedMergeOutputAcceptHit, SelectedMergeOutputRejectHit,
      CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
      encodeCodeWordAsInput, List.append_assoc]

theorem
    SelectedMergePaddedEmitterDecodedHandoffTape_cells_eq_targetWindow
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    Tape.cells (SelectedMergePaddedEmitterDecodedHandoffTape useAccept p) =
      SelectedMergePaddedEmitterParsedInnerTargetCells useAccept p := by
  rw [SelectedMergePaddedEmitterDecodedHandoffTape_cells_eq_bits]
  rw [SelectedMergePaddedEmitterDecodedHandoffBits_eq_outputPrefix_fieldTail]
  simp [SelectedMergePaddedEmitterParsedInnerTargetCells,
    SelectedMergePaddedEmitterParsedInnerTargetPaddingCells, List.map_append,
    List.append_assoc]

theorem
    SelectedMergePaddedEmitterParsedInnerTargetCells_filterMap_eq_bits
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    (SelectedMergePaddedEmitterParsedInnerTargetCells useAccept p).filterMap
        (fun cell => cell) =
      SelectedMergePaddedEmitterDecodedHandoffBits useAccept p := by
  have hcells :=
    SelectedMergePaddedEmitterDecodedHandoffTape_cells_eq_targetWindow
      useAccept p
  have hnorm :=
    SelectedMergePaddedEmitterDecodedHandoffTape_normalizedOutput_eq_bits
      useAccept p
  rw [Tape.normalizedOutput] at hnorm
  rw [hcells] at hnorm
  exact hnorm

theorem
    SelectedMergePaddedEmitterParsedInnerTargetCells_eq_split
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerTargetCells useAccept p =
      SelectedMergePaddedEmitterParsedInnerTargetSplitCells useAccept p := by
  rw [SelectedMergePaddedEmitterParsedInnerTargetCells,
    SelectedMergePaddedEmitterParsedInnerTargetSplitCells]
  rw [SelectedMergePaddedEmitterParsedInnerTargetTailBits_eq_outputPrefixTail]
  simp [SelectedMergePaddedEmitterParsedInnerOutputPrefixBits,
    List.map_append, List.append_assoc]

theorem
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape_cells_eq_split
    (p : SelectedMergeEmitterPayload) :
    Tape.cells
        (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p) =
      SelectedMergePaddedEmitterParsedInnerSourceSplitCells p := by
  rw [
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape_cells_eq_sourceWindow,
    SelectedMergePaddedEmitterParsedInnerSourceCells_eq_split]

theorem
    SelectedMergePaddedEmitterParsedInnerGapCompactorSourceTape_cells_eq_split
    (p : SelectedMergeEmitterPayload) :
    Tape.cells
        (SelectedMergePaddedEmitterParsedInnerGapCompactorSourceTape p) =
      SelectedMergePaddedEmitterParsedInnerSourceSplitCells p := by
  rw [SelectedMergePaddedEmitterParsedInnerGapCompactorSourceTape]
  rw [CommonGround.FiniteTransducers.rightBlankLocalGapCompactorSourceTapeWithBaseAndRight_cells]
  rw [SelectedMergePaddedEmitterParsedInnerSourceTailCurrentRest_reverse]
  simp [SelectedMergePaddedEmitterParsedInnerGapBaseLeft,
    SelectedMergePaddedEmitterParsedInnerSourceSplitCells,
    SelectedMergePaddedEmitterOuterTransitionBaseLeft]

theorem
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape_cells_eq_gapCompactorSource
    (p : SelectedMergeEmitterPayload) :
    Tape.cells
        (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p) =
      Tape.cells
        (SelectedMergePaddedEmitterParsedInnerGapCompactorSourceTape p) := by
  rw [
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape_cells_eq_split,
    SelectedMergePaddedEmitterParsedInnerGapCompactorSourceTape_cells_eq_split]

theorem
    SelectedMergePaddedEmitterParsedInnerGapCompactorTargetTape_normalizedOutput
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterParsedInnerGapCompactorTargetTape p) =
      SelectedMergePaddedEmitterParsedInnerSourceBits p := by
  rw [SelectedMergePaddedEmitterParsedInnerGapCompactorTargetTape]
  rw [CommonGround.FiniteTransducers.leadingBlankLeftShiftTargetTapeWithPadding_normalizedOutput]
  simp [SelectedMergePaddedEmitterParsedInnerGapBaseLeft,
    SelectedMergePaddedEmitterParsedInnerSourceBits,
    SelectedMergePaddedEmitterOuterTransitionBaseLeft,
    Function.comp_def]

theorem
    selectedMergePaddedEmitterParsedInnerGapCompactorDescription_haltsFromTape
    (p : SelectedMergeEmitterPayload) :
    CommonGround.FiniteTransducers.rightBlankLocalGapCompactorDescription.HaltsFromTape
      (SelectedMergePaddedEmitterParsedInnerGapCompactorSourceTape p)
      (SelectedMergePaddedEmitterParsedInnerGapCompactorTargetTape p) := by
  have hgap :=
    CommonGround.FiniteTransducers.rightBlankLocalGapCompactorDescription_haltsFromTapeWithBase_leftStack_rightPadding
      SelectedMergePaddedEmitterParsedInnerGapBaseLeft
      (SelectedMergePaddedEmitterParsedInnerSourceTailCurrent p)
      (SelectedMergePaddedEmitterParsedInnerSourceTailLeftRest p)
      0
      (none : Option Bool)
      []
  have htail :
      (SelectedMergePaddedEmitterParsedInnerSourceTailCurrent p ::
          SelectedMergePaddedEmitterParsedInnerSourceTailLeftRest p).reverse =
        SelectedMergePaddedEmitterParsedInnerSourceTailBits p := by
    exact
      SelectedMergePaddedEmitterParsedInnerSourceTailCurrentRest_reverse p
  rw [htail] at hgap
  simpa [SelectedMergePaddedEmitterParsedInnerGapCompactorSourceTape,
    SelectedMergePaddedEmitterParsedInnerGapCompactorTargetTape] using
    hgap

theorem
    SelectedMergePaddedEmitterParsedInnerGapCompactorTargetTape_moveLeft_moveLeft_eq_rewindSource
    (p : SelectedMergeEmitterPayload) :
    Tape.move Direction.left
        (Tape.move Direction.left
          (SelectedMergePaddedEmitterParsedInnerGapCompactorTargetTape p)) =
      SelectedMergePaddedEmitterParsedInnerPostGapRewindSourceTape p := by
  rw [SelectedMergePaddedEmitterParsedInnerGapCompactorTargetTape,
    SelectedMergePaddedEmitterParsedInnerPostGapRewindSourceTape]
  simp [CommonGround.FiniteTransducers.leadingBlankLeftShiftTargetTapeWithPadding,
    CommonGround.FiniteTransducers.rightEdgeRewindSourceTapeWithBase,
    CommonGround.FiniteTransducers.tapeAtCells, Tape.move, Tape.moveLeft,
    SelectedMergePaddedEmitterParsedInnerGapBaseLeft,
    SelectedMergePaddedEmitterParsedInnerSourceBits,
    SelectedMergePaddedEmitterOuterTransitionBaseLeft, List.map_reverse,
    List.reverse_append, List.append_assoc]

theorem
    SelectedMergePaddedEmitterParsedInnerPostGapRewindTargetTape_eq_deleteSourceTape
    (p : SelectedMergeEmitterPayload) :
    CommonGround.FiniteTransducers.rightEdgeRewindTargetTapeWithBase
        []
        (SelectedMergePaddedEmitterParsedInnerSourceBits p)
        [none, none] =
      SelectedMergePaddedEmitterParsedInnerDeleteSourceTape p := by
  simp [SelectedMergePaddedEmitterParsedInnerDeleteSourceTape,
    CommonGround.FiniteTransducers.rightEdgeRewindTargetTapeWithBase,
    CommonGround.FiniteTransducers.FSTStatefulOptionAppendSourceTapeWithPadding,
    CommonGround.FiniteTransducers.tapeAtCells]

theorem
    selectedMergePaddedEmitterParsedInnerRightEdgeRewindDescription_haltsFromPostGap
    (p : SelectedMergeEmitterPayload) :
    CommonGround.FiniteTransducers.rightEdgeRewindDescription.HaltsFromTape
      (Tape.move Direction.left
        (Tape.move Direction.left
          (SelectedMergePaddedEmitterParsedInnerGapCompactorTargetTape p)))
      (SelectedMergePaddedEmitterParsedInnerDeleteSourceTape p) := by
  rw [
    SelectedMergePaddedEmitterParsedInnerGapCompactorTargetTape_moveLeft_moveLeft_eq_rewindSource]
  rw [←
    SelectedMergePaddedEmitterParsedInnerPostGapRewindTargetTape_eq_deleteSourceTape]
  exact
    CommonGround.FiniteTransducers.rightEdgeRewindDescription_haltsFromTapeWithBase
      []
      (SelectedMergePaddedEmitterParsedInnerSourceBits p)
      [none, none]

theorem
    selectedMergePaddedEmitterParsedInnerRemainderDeleteDescription_subroutineReady :
    SelectedMergePaddedEmitterParsedInnerRemainderDeleteDescription.SubroutineReady := by
  exact
    CommonGround.FiniteTransducers.generatedDeleteWindowDescription_subroutineReady
      SelectedMergePaddedEmitterParsedInnerRemainderDeletePrefixBits.length
      SelectedMergePaddedEmitterParsedInnerRemainderDeleteBits.length

theorem
    selectedMergePaddedEmitterParsedInnerRemainderDeleteDescription_haltsFromDeleteSource
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerRemainderDeleteDescription.HaltsFromTape
      (SelectedMergePaddedEmitterParsedInnerDeleteSourceTape p)
      (SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape p) := by
  rw [SelectedMergePaddedEmitterParsedInnerDeleteSourceTape,
    SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape]
  rw [SelectedMergePaddedEmitterParsedInnerSourceBits_eq_remainderDeleteSplit]
  simpa [SelectedMergePaddedEmitterParsedInnerRemainderDeleteDescription]
    using
      CommonGround.FiniteTransducers.generatedDeleteWindowDescription_haltsFrom_split_withPadding
        SelectedMergePaddedEmitterParsedInnerRemainderDeletePrefixBits.length
        SelectedMergePaddedEmitterParsedInnerRemainderDeleteBits.length
        SelectedMergePaddedEmitterParsedInnerRemainderDeletePrefixBits
        SelectedMergePaddedEmitterParsedInnerRemainderDeleteBits
        (SelectedMergePaddedEmitterParsedInnerRemainderDeleteSuffixBits p)
        1
        [none, none]

theorem
    SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape_cells
    (p : SelectedMergeEmitterPayload) :
    Tape.cells
        (SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape p) =
      List.append
        [none]
        (List.append
          (SelectedMergePaddedEmitterParsedInnerRemainderDeletePrefixBits.map
            some)
          (List.append
            (List.replicate
              SelectedMergePaddedEmitterParsedInnerRemainderDeleteBits.length
              (none : Option Bool))
            (List.append
              ((SelectedMergePaddedEmitterParsedInnerRemainderDeleteSuffixBits
                p).map some)
              [none, none, none]))) := by
  rw [SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape]
  rw [SelectedMergePaddedEmitterParsedInnerSourceBits_eq_remainderDeleteSplit]
  rw [CommonGround.FiniteTransducers.FSTStatefulOptionAppendTargetTapeWithPadding_cells_cons]
  rw [CommonGround.FiniteTransducers.deleteWindowCellsFrom_split
    SelectedMergePaddedEmitterParsedInnerRemainderDeletePrefixBits.length
    SelectedMergePaddedEmitterParsedInnerRemainderDeleteBits.length
    SelectedMergePaddedEmitterParsedInnerRemainderDeletePrefixBits
    SelectedMergePaddedEmitterParsedInnerRemainderDeleteBits
    (SelectedMergePaddedEmitterParsedInnerRemainderDeleteSuffixBits p)
    rfl rfl]
  simp [List.append_assoc]

theorem
    SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape_normalizedOutput_split
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape p) =
      List.append
        SelectedMergePaddedEmitterParsedInnerRemainderDeletePrefixBits
        (SelectedMergePaddedEmitterParsedInnerRemainderDeleteSuffixBits
          p) := by
  rw [Tape.normalizedOutput,
    SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape_cells]
  simp [List.filterMap_append, Function.comp_def]

theorem
    SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape_normalizedOutput
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape p) =
      List.append
        (SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p)
        (SelectedMergePaddedEmitterParsedInnerSourceFieldTailBits p) := by
  rw [
    SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape_normalizedOutput_split]
  simp [SelectedMergePaddedEmitterParsedInnerRemainderDeletePrefixBits,
    SelectedMergePaddedEmitterParsedInnerRemainderDeleteSuffixBits,
    SelectedMergePaddedEmitterParsedInnerOutputPrefixBits,
    List.append_assoc]

theorem
    SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape_normalizedOutput_expandedSource
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape p) =
      List.append
        (SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p)
        (SelectedMergePaddedEmitterParsedInnerSourceFieldTailExpandedBits
          p) := by
  rw [
    SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape_normalizedOutput]
  rw [
    SelectedMergePaddedEmitterParsedInnerSourceFieldTailExpandedBits_eq_sourceFieldTailBits]

theorem
    SelectedMergePaddedEmitterDecodedHandoffTape_cells_eq_split
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    Tape.cells (SelectedMergePaddedEmitterDecodedHandoffTape useAccept p) =
      SelectedMergePaddedEmitterParsedInnerTargetSplitCells useAccept p := by
  rw [SelectedMergePaddedEmitterDecodedHandoffTape_cells_eq_targetWindow,
    SelectedMergePaddedEmitterParsedInnerTargetCells_eq_split]

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
