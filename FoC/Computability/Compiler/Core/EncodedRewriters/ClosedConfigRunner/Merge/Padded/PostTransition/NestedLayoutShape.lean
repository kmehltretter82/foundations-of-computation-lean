import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Merge.Padded.PostTransition.Core

set_option doc.verso true

/-!
# Merge post-transition nested-layout shape

This module isolates the pure source-fields and nested-layout parsed tape facts
used by the padded merge post-transition leaves.  The scanner definitions and
exact source-scanner runs remain in
{module}`FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Merge.Padded.PostTransition.Core`;
branch contracts and finite leaves import this module when they need the parsed
nested-layout source and target shapes.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

def SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells
    (((SelectedMergePaddedEmitterOuterHitSuffixBits p).reverse.map some) ++
      (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
        p.S.config
        (List.append
          ((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            p.S.stage).reverse.map some)
          (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
            ((encodeCodeWordAsInput
              (MachineCodeSymbol.transition ::
                encodeBoolWordAppend p.L.input
                  (encodeNatAppend p.L.stage
                    (encodeConfigurationAppend p.L.acceptConfig
                      (encodeConfigurationAppend p.L.rejectConfig
                        (encodeBoolAppend p.L.acceptHit
                          (encodeBoolAppend p.L.rejectHit []))))))).map some)
            (List.append
              (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse)
              [none])))))
    [none, none]

theorem SelectedMergePaddedEmitterAfterHitPaddedTape_eq_sourceFieldsTape
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterAfterHitPaddedTape p =
      SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape p := by
  rw [SelectedMergePaddedEmitterAfterHitPaddedTape,
    SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape]
  simp [ParsedLayoutBits, DovetailLayout.encode, DovetailLayout.encodeAppend]

theorem SelectedMergePaddedEmitterAfterHitPaddedTape_eq_sourceLeftBitsRev_tapeAtCells
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterAfterHitPaddedTape p =
      DovetailInitialLayoutInitializer.tapeAtCells
        (List.append
          ((SelectedMergePaddedEmitterCleanup.sourceLeftBitsRev p).map some)
          [none])
        [none, none] := by
  rw [SelectedMergePaddedEmitterAfterHitPaddedTape,
    SelectedMergePaddedEmitterCleanup.sourceLeftBitsRev]
  let transitionBase : List (Option Bool) :=
    ((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse
  let parsedCells : List (Option Bool) :=
    (ParsedLayoutBits p.L).map some
  let parsedRestored : List (Option Bool) :=
    CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
      parsedCells transitionBase
  let stageBase : List (Option Bool) :=
    (FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
      p.S.stage).reverse.map some
  have hcell :
      CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
          parsedCells (List.append transitionBase [none]) =
        List.append parsedRestored [none] := by
    exact
      CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase_append_base
        parsedCells transitionBase [none]
  have hcfg :
      CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
          p.S.config
          (List.append stageBase (List.append parsedRestored [none])) =
        List.append
          (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
            p.S.config (List.append stageBase parsedRestored))
          [none] := by
    simpa [List.append_assoc] using
      CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase_append_base
        p.S.config (List.append stageBase parsedRestored) [none]
  have hparsed :
      parsedRestored =
        List.append
          ((CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredBitsRev
            parsedCells).map some)
          transitionBase := by
    dsimp [parsedRestored]
    rw [←
      CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredBitsRev_map_some_withBase
        parsedCells transitionBase]
    rfl
  change
    DovetailInitialLayoutInitializer.tapeAtCells
      (List.append
        ((SelectedMergePaddedEmitterOuterHitSuffixBits p).reverse.map some)
        (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
          p.S.config
          (List.append stageBase
            (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
              parsedCells (List.append transitionBase [none])))))
      [none, none] =
    DovetailInitialLayoutInitializer.tapeAtCells
      (List.append
        ((List.append
          (SelectedMergePaddedEmitterOuterHitSuffixBits p).reverse
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev
              p.S.config)
            (List.append
              (FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                p.S.stage).reverse
              (List.append
                (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredBitsRev
                  ((ParsedLayoutBits p.L).map some))
                (encodeCodeSymbolAsInput MachineCodeSymbol.transition).reverse)))).map
          some)
        [none])
      [none, none]
  rw [hcell, hcfg]
  rw [←
    CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev_map_some_withBase
      p.S.config
      (List.append stageBase parsedRestored)]
  rw [hparsed]
  simp [transitionBase, parsedCells, stageBase,
    List.map_append, List.append_assoc]

theorem
    SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape_eq_sourceLeftBitsRev_tapeAtCells
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape p =
      DovetailInitialLayoutInitializer.tapeAtCells
        (List.append
          ((SelectedMergePaddedEmitterCleanup.sourceLeftBitsRev p).map some)
          [none])
        [none, none] := by
  rw [← SelectedMergePaddedEmitterAfterHitPaddedTape_eq_sourceFieldsTape]
  exact
    SelectedMergePaddedEmitterAfterHitPaddedTape_eq_sourceLeftBitsRev_tapeAtCells
      p

theorem
    SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape_normalizedOutput_eq_sourceBits
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape p) =
      SelectedMergePaddedEmitterCleanup.sourceBits p := by
  rw [
    SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape_eq_sourceLeftBitsRev_tapeAtCells]
  rw [←
    SelectedMergePaddedEmitterCleanup.sourceLeftBitsRev_reverse_eq_sourceBits
      p]
  simp [DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.normalizedOutput, Tape.cells, Function.comp_def]

theorem
    SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape_normalizedOutput_eq_fields
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape p) =
      encodeCodeWordAsInput
        (MachineCodeSymbol.transition ::
          encodeBoolWordAppend
            (encodeCodeWordAsInput
              (MachineCodeSymbol.transition ::
                encodeBoolWordAppend p.L.input
                  (encodeNatAppend p.L.stage
                    (encodeConfigurationAppend p.L.acceptConfig
                      (encodeConfigurationAppend p.L.rejectConfig
                        (encodeBoolAppend p.L.acceptHit
                          (encodeBoolAppend p.L.rejectHit [])))))))
            (encodeNatAppend p.S.stage
              (encodeConfigurationAppend p.S.config
                (encodeBoolAppend p.S.hit [])))) := by
  rw [
    SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape_normalizedOutput_eq_sourceBits,
    SelectedMergePaddedEmitterAfterTransitionSourceBits_eq_fields]

theorem
    SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape_cells_eq_sourceBits
    (p : SelectedMergeEmitterPayload) :
    Tape.cells (SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape p) =
      List.append [none]
        (List.append
          ((SelectedMergePaddedEmitterCleanup.sourceBits p).map some)
          [none, none]) := by
  rw [
    SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape_eq_sourceLeftBitsRev_tapeAtCells]
  rw [←
    SelectedMergePaddedEmitterCleanup.sourceLeftBitsRev_reverse_eq_sourceBits
      p]
  simp [DovetailInitialLayoutInitializer.tapeAtCells, Tape.cells,
    List.map_reverse]

theorem
    SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape_cells_eq_fields
    (p : SelectedMergeEmitterPayload) :
    Tape.cells (SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape p) =
      List.append [none]
        (List.append
          ((encodeCodeWordAsInput
            (MachineCodeSymbol.transition ::
              encodeBoolWordAppend
                (encodeCodeWordAsInput
                  (MachineCodeSymbol.transition ::
                    encodeBoolWordAppend p.L.input
                      (encodeNatAppend p.L.stage
                        (encodeConfigurationAppend p.L.acceptConfig
                          (encodeConfigurationAppend p.L.rejectConfig
                            (encodeBoolAppend p.L.acceptHit
                              (encodeBoolAppend p.L.rejectHit [])))))))
                (encodeNatAppend p.S.stage
                  (encodeConfigurationAppend p.S.config
                    (encodeBoolAppend p.S.hit []))))).map some)
          [none, none]) := by
  rw [
    SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape_cells_eq_sourceBits,
    SelectedMergePaddedEmitterAfterTransitionSourceBits_eq_fields]

theorem SelectedMergePaddedEmitterNestedLayoutSourceBits_eq_dovetailLayoutFieldBits
    (p : SelectedMergeEmitterPayload) :
    encodeCodeWordAsInput
        (MachineCodeSymbol.transition ::
          encodeBoolWordAppend p.L.input
            (encodeNatAppend p.L.stage
              (encodeConfigurationAppend p.L.acceptConfig
                (encodeConfigurationAppend p.L.rejectConfig
                  (encodeBoolAppend p.L.acceptHit
                    (encodeBoolAppend p.L.rejectHit [])))))) =
      CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits
        p.L [] := by
  simpa [DovetailLayout.encodeAppend, encodeCodeWordAsInput] using
    CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits_eq_encodeAppend
      p.L []

theorem SelectedMergePaddedEmitterNestedLayoutSourceBits_eq_markedBodyBits
    (p : SelectedMergeEmitterPayload) :
    encodeCodeWordAsInput
        (MachineCodeSymbol.transition ::
          encodeBoolWordAppend p.L.input
            (encodeNatAppend p.L.stage
              (encodeConfigurationAppend p.L.acceptConfig
                (encodeConfigurationAppend p.L.rejectConfig
                  (encodeBoolAppend p.L.acceptHit
                    (encodeBoolAppend p.L.rejectHit [])))))) =
      false ::
        CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyBits
          p.L := by
  rw [SelectedMergePaddedEmitterNestedLayoutSourceBits_eq_dovetailLayoutFieldBits]
  exact
    CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits_nil_eq_first_body
      p.L

theorem
    SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape_eq_dovetailLayoutFieldBits
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape p =
      DovetailInitialLayoutInitializer.tapeAtCells
        (((SelectedMergePaddedEmitterOuterHitSuffixBits p).reverse.map some) ++
          (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
            p.S.config
            (List.append
              ((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                p.S.stage).reverse.map some)
              (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
                ((CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits
                  p.L []).map some)
                (List.append
                  (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse)
                  [none])))))
        [none, none] := by
  rw [SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape]
  rw [
    SelectedMergePaddedEmitterNestedLayoutSourceBits_eq_dovetailLayoutFieldBits]

theorem markedDovetailLayoutBodyRestoredBitsRev_map_some_withBase
    (L : DovetailLayout) (baseLeft : List (Option Bool)) :
    List.append
        ((CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyRestoredBitsRev
          L).map some)
        baseLeft =
      CanonicalLayouts.DovetailLayoutScanner.finalHitFlagsRestoredLeftWithBase
        L.acceptHit L.rejectHit
        (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
          L.rejectConfig
          (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
            L.acceptConfig
            (List.append
              ((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                L.stage).reverse.map some)
              (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
                (L.input.map some)
                (List.append
                  (CanonicalLayouts.DovetailLayoutScanner.transitionRemainderBits.reverse.map some)
                  baseLeft))))) := by
  let baseAfterTransition :=
    List.append
      (CanonicalLayouts.DovetailLayoutScanner.transitionRemainderBits.reverse.map some)
      baseLeft
  let baseAfterInput :=
    CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
      (L.input.map some) baseAfterTransition
  let baseAfterStage :=
    List.append
      ((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        L.stage).reverse.map some)
      baseAfterInput
  let baseAfterAccept :=
    CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
      L.acceptConfig baseAfterStage
  have hinput :
      List.append
          ((CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredBitsRev
            (L.input.map some)).map some)
          baseAfterTransition =
        baseAfterInput := by
    simpa [baseAfterInput] using
      CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredBitsRev_map_some_withBase
        (L.input.map some) baseAfterTransition
  have haccept :
      List.append
          ((CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev
            L.acceptConfig).map some)
          baseAfterStage =
        baseAfterAccept := by
    simpa [baseAfterAccept] using
      CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev_map_some_withBase
        L.acceptConfig baseAfterStage
  have hreject :
      List.append
          ((CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev
            L.rejectConfig).map some)
          baseAfterAccept =
        CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
          L.rejectConfig baseAfterAccept :=
    CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev_map_some_withBase
      L.rejectConfig baseAfterAccept
  calc
    List.append
        ((CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyRestoredBitsRev
          L).map some)
        baseLeft =
      CanonicalLayouts.DovetailLayoutScanner.finalHitFlagsRestoredLeftWithBase
        L.acceptHit L.rejectHit
        (List.append
          ((CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev
            L.rejectConfig).map some)
          (List.append
            ((CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev
              L.acceptConfig).map some)
            (List.append
              ((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                L.stage).reverse.map some)
              (List.append
                ((CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredBitsRev
                  (L.input.map some)).map some)
                baseAfterTransition)))) := by
          simp [
            CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyRestoredBitsRev,
            CanonicalLayouts.DovetailLayoutScanner.finalHitFlagsRestoredLeftWithBase,
            baseAfterTransition, List.map_append, List.map_reverse,
            List.append_assoc]
    _ =
      CanonicalLayouts.DovetailLayoutScanner.finalHitFlagsRestoredLeftWithBase
        L.acceptHit L.rejectHit
        (List.append
          ((CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev
            L.rejectConfig).map some)
          (List.append
            ((CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev
              L.acceptConfig).map some)
            baseAfterStage)) := by
          rw [hinput]
    _ =
      CanonicalLayouts.DovetailLayoutScanner.finalHitFlagsRestoredLeftWithBase
        L.acceptHit L.rejectHit
        (List.append
          ((CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev
            L.rejectConfig).map some)
          baseAfterAccept) := by
          rw [haccept]
    _ =
      CanonicalLayouts.DovetailLayoutScanner.finalHitFlagsRestoredLeftWithBase
        L.acceptHit L.rejectHit
        (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
          L.rejectConfig baseAfterAccept) := by
          rw [hreject]
    _ =
      CanonicalLayouts.DovetailLayoutScanner.finalHitFlagsRestoredLeftWithBase
        L.acceptHit L.rejectHit
        (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
          L.rejectConfig
          (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
            L.acceptConfig
            (List.append
              ((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                L.stage).reverse.map some)
              (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
                (L.input.map some)
                (List.append
                  (CanonicalLayouts.DovetailLayoutScanner.transitionRemainderBits.reverse.map some)
                  baseLeft))))) := by
          simp [baseAfterTransition, baseAfterInput, baseAfterStage,
            baseAfterAccept]

def SelectedMergePaddedEmitterOuterTransitionBaseLeft :
    List (Option Bool) :=
  List.append
    (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse)
    [none]

def SelectedMergePaddedEmitterNestedLayoutBodyBaseLeft :
    List (Option Bool) :=
  none :: SelectedMergePaddedEmitterOuterTransitionBaseLeft

def SelectedMergePaddedEmitterNestedLayoutParsedLeft
    (p : SelectedMergeEmitterPayload) : List (Option Bool) :=
  CanonicalLayouts.DovetailLayoutScanner.finalHitFlagsRestoredLeftWithBase
    p.L.acceptHit p.L.rejectHit
    (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
      p.L.rejectConfig
      (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
        p.L.acceptConfig
        (List.append
          ((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            p.L.stage).reverse.map some)
          (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
            (p.L.input.map some)
            (List.append
              (CanonicalLayouts.DovetailLayoutScanner.transitionRemainderBits.reverse.map some)
              SelectedMergePaddedEmitterNestedLayoutBodyBaseLeft)))))

def SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells
    (((SelectedMergePaddedEmitterOuterHitSuffixBits p).reverse.map some) ++
      (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
        p.S.config
        (List.append
          ((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            p.S.stage).reverse.map some)
          (SelectedMergePaddedEmitterNestedLayoutParsedLeft p))))
    [none, none]

theorem
    SelectedMergePaddedEmitterNestedLayoutParsedLeft_eq_markedBodyRestoredBitsRev
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterNestedLayoutParsedLeft p =
      List.append
        ((CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyRestoredBitsRev
          p.L).map some)
        SelectedMergePaddedEmitterNestedLayoutBodyBaseLeft := by
  exact
    (markedDovetailLayoutBodyRestoredBitsRev_map_some_withBase
      p.L SelectedMergePaddedEmitterNestedLayoutBodyBaseLeft).symm

theorem
    SelectedMergePaddedEmitterNestedLayoutBodyBaseLeft_reverse_filterMap :
    SelectedMergePaddedEmitterNestedLayoutBodyBaseLeft.reverse.filterMap
        (fun cell => cell) =
      encodeCodeSymbolAsInput MachineCodeSymbol.transition := by
  simp [SelectedMergePaddedEmitterNestedLayoutBodyBaseLeft,
    SelectedMergePaddedEmitterOuterTransitionBaseLeft,
    Function.comp_def]

theorem
    SelectedMergePaddedEmitterNestedLayoutBodyBaseLeft_filterMap_reverse :
    (SelectedMergePaddedEmitterNestedLayoutBodyBaseLeft.filterMap
        (fun cell => cell)).reverse =
      encodeCodeSymbolAsInput MachineCodeSymbol.transition := by
  simp [SelectedMergePaddedEmitterNestedLayoutBodyBaseLeft,
    SelectedMergePaddedEmitterOuterTransitionBaseLeft,
    Function.comp_def]

theorem
    SelectedMergePaddedEmitterNestedLayoutParsedLeft_reverse_filterMap
    (p : SelectedMergeEmitterPayload) :
    (SelectedMergePaddedEmitterNestedLayoutParsedLeft p).reverse.filterMap
        (fun cell => cell) =
      List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
        (CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyBits
          p.L) := by
  rw [SelectedMergePaddedEmitterNestedLayoutParsedLeft_eq_markedBodyRestoredBitsRev]
  simp [List.reverse_append, List.filterMap_append,
    SelectedMergePaddedEmitterNestedLayoutBodyBaseLeft_filterMap_reverse,
    CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyRestoredBitsRev_reverse,
    Function.comp_def]

theorem
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape_normalizedOutput_eq_markedBody
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p) =
      List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
        (List.append
          (CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyBits
            p.L)
          (List.append
            (FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              p.S.stage)
            (List.append
              (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                p.S.config [])
              (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                p.S.hit [])))) := by
  have hbase :
      (List.append
          ((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            p.S.stage).reverse.map some)
          (SelectedMergePaddedEmitterNestedLayoutParsedLeft p)).reverse.filterMap
            (fun cell => cell) =
        List.append
          (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyBits
              p.L)
            (FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              p.S.stage)) := by
    have hreverse :
        List.filterMap (fun cell => cell)
            (((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              p.S.stage).reverse.map some).append
              (SelectedMergePaddedEmitterNestedLayoutParsedLeft p)).reverse =
          List.append
            (List.filterMap (fun cell => cell)
              (SelectedMergePaddedEmitterNestedLayoutParsedLeft p).reverse)
            (List.filterMap (fun cell => cell)
              (((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                p.S.stage).reverse.map some).reverse)) := by
      simp [List.reverse_append, List.filterMap_append]
    rw [hreverse]
    rw [SelectedMergePaddedEmitterNestedLayoutParsedLeft_reverse_filterMap]
    simp [List.append_assoc, Function.comp_def]
  have hcfg :
      (List.filterMap (fun cell => cell)
          (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
            p.S.config
            (List.append
              ((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                p.S.stage).reverse.map some)
              (SelectedMergePaddedEmitterNestedLayoutParsedLeft p)))).reverse =
        List.append
          (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyBits
              p.L)
            (List.append
              (FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                p.S.stage)
              (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                p.S.config []))) := by
    rw [← Tape.filterMap_reverse]
    rw [dovetailScanner_configurationRestoredLeftWithBase_reverse_filterMap]
    rw [hbase]
    simp [List.append_assoc]
  rw [SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape]
  simp [DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.normalizedOutput, Tape.cells, List.reverse_append,
    List.filterMap_append]
  rw [← List.map_reverse]
  have hcfgWithHit :=
    congrArg
      (fun xs =>
        List.append xs
          (List.filterMap ((fun cell => cell) ∘ some)
            (SelectedMergePaddedEmitterOuterHitSuffixBits p)))
      hcfg
  simpa [SelectedMergePaddedEmitterOuterHitSuffixBits,
    SelectedMergePaddedEmitterOuterHitSuffixCode,
    CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.boolBits_eq_encodeBoolAppend,
    encodeCodeWordAsInput, encodeCodeSymbolAsInput, Function.comp_def,
    List.append_assoc]
    using hcfgWithHit

theorem
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape_move_left_move_right
    (p : SelectedMergeEmitterPayload) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p)) =
      SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p := by
  simp [SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape,
    DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem SelectedMergePaddedEmitterAfterHitPaddedTape_move_left_move_right
    (p : SelectedMergeEmitterPayload) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (SelectedMergePaddedEmitterAfterHitPaddedTape p)) =
      SelectedMergePaddedEmitterAfterHitPaddedTape p := by
  rw [SelectedMergePaddedEmitterAfterHitPaddedTape_eq_sourceLeftBitsRev_tapeAtCells]
  simp [DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem sourceRewindDescription_haltsFrom_afterHitPaddedTape
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterCleanup.sourceRewindDescription.HaltsFromTape
      (SelectedMergePaddedEmitterAfterHitPaddedTape p)
      (SelectedMergePaddedEmitterCleanup.rewindTargetPaddedTape
        (SelectedMergePaddedEmitterCleanup.sourceBits p)) := by
  have hleft :
      (SelectedMergePaddedEmitterCleanup.sourceBits p).reverse =
        SelectedMergePaddedEmitterCleanup.sourceLeftBitsRev p := by
    rw [←
      SelectedMergePaddedEmitterCleanup.sourceLeftBitsRev_reverse_eq_sourceBits
        p]
    simp
  rw [SelectedMergePaddedEmitterAfterHitPaddedTape_eq_sourceLeftBitsRev_tapeAtCells,
    ← hleft]
  exact
    SelectedMergePaddedEmitterCleanup.sourceRewindDescription_haltsFromBoundaryPaddedTape
      (SelectedMergePaddedEmitterCleanup.sourceBits p)

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
