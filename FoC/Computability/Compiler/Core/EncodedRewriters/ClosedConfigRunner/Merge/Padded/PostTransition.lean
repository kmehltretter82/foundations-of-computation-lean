import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Merge.Padded.CleanupBase

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

def SelectedMergePaddedEmitterAfterTransitionPaddedTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells
    (List.append
      ((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse
      [none])
    (List.append ((SelectedMergePaddedEmitterOuterTailBits p).map some)
      [none, none])

theorem SelectedMergePaddedEmitterAfterTransitionPaddedTape_cells
    (p : SelectedMergeEmitterPayload) :
    Tape.cells (SelectedMergePaddedEmitterAfterTransitionPaddedTape p) =
      List.append [none]
        (List.append
          ((List.append (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
            (SelectedMergePaddedEmitterOuterTailBits p)).map some)
          [none, none]) := by
  rcases
      SelectedMergePaddedEmitterOuterTailBits_cons_cons_false_false p with
    ⟨tail, htail⟩
  rw [SelectedMergePaddedEmitterAfterTransitionPaddedTape, htail]
  simp [
    DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.cells, List.map_append, List.append_assoc]

theorem SelectedMergePaddedEmitterAfterHitSourceBits_eq_transition_outerTail
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterCleanup.sourceBits p =
      List.append (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
        (SelectedMergePaddedEmitterOuterTailBits p) := by
  rw [SelectedMergePaddedEmitterCleanup.sourceBits,
    SelectedMergePaddedEmitterAfterHitSourceBits,
    SelectedMergePaddedEmitterOuterTailBits_eq_boolWordFieldBits,
    SelectedMergePaddedEmitterOuterSuffixBits_eq_stageFieldBits,
    SelectedMergePaddedEmitterOuterStageSuffixBits_eq_configurationFieldBits]
  simp [SelectedMergePaddedEmitterOuterHitSuffixBits,
    SelectedMergePaddedEmitterOuterHitSuffixCode,
    CanonicalLayouts.DovetailLayoutScanner.boolBits_eq_encodeBoolAppend,
    CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
    encodeCodeWordAsInput]

theorem SelectedMergePaddedEmitterAfterTransitionSourceBits_eq_sourceCode
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterCleanup.sourceBits p =
      encodeCodeWordAsInput
        (SelectedMergePaddedEmitterAfterTransitionSourceCode p) := by
  rw [SelectedMergePaddedEmitterAfterHitSourceBits_eq_transition_outerTail]
  simp [SelectedMergePaddedEmitterAfterTransitionSourceCode,
    SelectedMergePaddedEmitterOuterTailBits, encodeCodeWordAsInput,
    encodeCodeSymbolAsInput]

theorem SelectedMergePaddedEmitterAfterTransitionSourceBits_eq_fields
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterCleanup.sourceBits p =
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
  rw [SelectedMergePaddedEmitterAfterTransitionSourceBits_eq_sourceCode,
    SelectedMergePaddedEmitterAfterTransitionSourceCode_eq_fields]

theorem SelectedMergePaddedEmitterAfterTransitionPaddedTape_normalizedOutput
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterAfterTransitionPaddedTape p) =
      SelectedMergePaddedEmitterCleanup.sourceBits p := by
  rw [Tape.normalizedOutput,
    SelectedMergePaddedEmitterAfterTransitionPaddedTape_cells,
    SelectedMergePaddedEmitterAfterHitSourceBits_eq_transition_outerTail]
  simp [Function.comp_def, List.map_append]

theorem SelectedMergePaddedEmitterAfterTransitionPaddedTape_normalizedOutput_eq_sourceCode
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterAfterTransitionPaddedTape p) =
      encodeCodeWordAsInput
        (SelectedMergePaddedEmitterAfterTransitionSourceCode p) := by
  rw [SelectedMergePaddedEmitterAfterTransitionPaddedTape_normalizedOutput,
    SelectedMergePaddedEmitterAfterTransitionSourceBits_eq_sourceCode]

theorem SelectedMergePaddedEmitterAfterTransitionPaddedTape_contextLength
    (p : SelectedMergeEmitterPayload) :
    Tape.contextLength (SelectedMergePaddedEmitterAfterTransitionPaddedTape p) =
      (SelectedMergePaddedEmitterCleanup.sourceBits p).length + 2 := by
  rcases
      SelectedMergePaddedEmitterOuterTailBits_cons_cons_false_false p with
    ⟨tail, htail⟩
  rw [SelectedMergePaddedEmitterAfterTransitionPaddedTape, htail,
    SelectedMergePaddedEmitterAfterHitSourceBits_eq_transition_outerTail]
  rw [htail]
  simp [DovetailInitialLayoutInitializer.tapeAtCells, Tape.contextLength,
    encodeCodeSymbolAsInput]
  omega

theorem SelectedMergePaddedEmitterAfterHitSourceBits_length_eq_inputBits
    (p : SelectedMergeEmitterPayload) :
    (SelectedMergePaddedEmitterCleanup.sourceBits p).length =
      (SimulatorLayout.asBoolInput p.S).length := by
  rw [SelectedMergePaddedEmitterAfterHitSourceBits_eq_transition_outerTail]
  rw [SelectedMergePaddedEmitterOuterTailBits]
  rw [SimulatorLayout.asBoolInput, SimulatorLayout.encode,
    SimulatorLayout.encodeAppend]
  rw [SelectedMergeEmitterPayload.input_eq_parsedLayoutBits]
  simp [encodeCodeWordAsInput, encodeCodeSymbolAsInput]

theorem SelectedMergeEquivEmitterPaddedOutputTape_contextLength_ge_afterTransitionPadded
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    Tape.contextLength (SelectedMergePaddedEmitterAfterTransitionPaddedTape p) <=
      Tape.contextLength
        (SelectedMergeEquivEmitterPaddedOutputTape useAccept p) := by
  rw [SelectedMergePaddedEmitterAfterTransitionPaddedTape_contextLength,
    SelectedMergePaddedEmitterAfterHitSourceBits_length_eq_inputBits]
  cases useAccept <;>
    simp [SelectedMergeEquivEmitterPaddedOutputTape,
      ScratchPaddedOutputTape, inputWithTrailingBlankPadding,
      selectedMergeOutputCode_eq_fields, encodeCodeWordAsInput,
      encodeCodeSymbolAsInput, Tape.contextLength] <;>
    omega

theorem
    SelectedMergePaddedEmitterAfterTransitionPaddedTape_normalizedOutput_eq_fields
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterAfterTransitionPaddedTape p) =
      encodeCodeWordAsInput
        (MachineCodeSymbol.transition ::
          encodeBoolWordAppend (ParsedLayoutBits p.L)
            (encodeNatAppend p.S.stage
              (encodeConfigurationAppend p.S.config
                (encodeBoolAppend p.S.hit [])))) := by
  rw [SelectedMergePaddedEmitterAfterTransitionPaddedTape_normalizedOutput,
    SelectedMergePaddedEmitterAfterHitSourceBits_eq_transition_outerTail]
  simp [SelectedMergePaddedEmitterOuterTailBits,
    encodeCodeWordAsInput, encodeCodeSymbolAsInput]

theorem
    SelectedMergePaddedEmitterAfterTransitionPaddedTape_normalizedOutput_eq_sourceFields
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterAfterTransitionPaddedTape p) =
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
  rw [SelectedMergePaddedEmitterAfterTransitionPaddedTape_normalizedOutput,
    SelectedMergePaddedEmitterAfterTransitionSourceBits_eq_fields]

theorem SelectedMergePaddedEmitterAfterTransitionPaddedTape_cells_eq_sourceBits
    (p : SelectedMergeEmitterPayload) :
    Tape.cells (SelectedMergePaddedEmitterAfterTransitionPaddedTape p) =
      List.append [none]
        (List.append
          ((SelectedMergePaddedEmitterCleanup.sourceBits p).map some)
          [none, none]) := by
  rw [SelectedMergePaddedEmitterAfterTransitionPaddedTape_cells,
    SelectedMergePaddedEmitterAfterHitSourceBits_eq_transition_outerTail]

theorem SelectedMergePaddedEmitterAfterTransitionPaddedTape_cells_eq_sourceCode
    (p : SelectedMergeEmitterPayload) :
    Tape.cells (SelectedMergePaddedEmitterAfterTransitionPaddedTape p) =
      List.append [none]
        (List.append
          ((encodeCodeWordAsInput
            (SelectedMergePaddedEmitterAfterTransitionSourceCode p)).map some)
          [none, none]) := by
  rw [SelectedMergePaddedEmitterAfterTransitionPaddedTape_cells_eq_sourceBits,
    SelectedMergePaddedEmitterAfterTransitionSourceBits_eq_sourceCode]

theorem SelectedMergePaddedEmitterAfterTransitionPaddedTape_cells_eq_sourceFields
    (p : SelectedMergeEmitterPayload) :
    Tape.cells (SelectedMergePaddedEmitterAfterTransitionPaddedTape p) =
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
  rw [SelectedMergePaddedEmitterAfterTransitionPaddedTape_cells_eq_sourceBits,
    SelectedMergePaddedEmitterAfterTransitionSourceBits_eq_fields]

theorem SelectedMergePaddedEmitterAfterTransitionPaddedTape_cells_eq_fields
    (p : SelectedMergeEmitterPayload) :
    Tape.cells (SelectedMergePaddedEmitterAfterTransitionPaddedTape p) =
      List.append [none]
        (List.append
          ((encodeCodeWordAsInput
            (MachineCodeSymbol.transition ::
              encodeBoolWordAppend (ParsedLayoutBits p.L)
                (encodeNatAppend p.S.stage
                  (encodeConfigurationAppend p.S.config
                    (encodeBoolAppend p.S.hit []))))).map some)
          [none, none]) := by
  rw [SelectedMergePaddedEmitterAfterTransitionPaddedTape_cells_eq_sourceBits,
    SelectedMergePaddedEmitterAfterHitSourceBits_eq_transition_outerTail]
  simp [SelectedMergePaddedEmitterOuterTailBits,
    encodeCodeWordAsInput, encodeCodeSymbolAsInput]

theorem skipTransitionPrefixDescription_haltsFrom_afterHitRewindSource
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterCleanup.skipTransitionPrefixDescription.HaltsFromTape
      (SelectedMergePaddedEmitterCleanup.rewindTargetPaddedTape
        (SelectedMergePaddedEmitterCleanup.sourceBits p))
      (SelectedMergePaddedEmitterAfterTransitionPaddedTape p) := by
  rw [SelectedMergePaddedEmitterCleanup.rewindTargetPaddedTape,
    SelectedMergePaddedEmitterAfterTransitionPaddedTape,
    SelectedMergePaddedEmitterAfterHitSourceBits_eq_transition_outerTail]
  simpa [List.map_append, List.append_assoc] using
    SelectedMergePaddedEmitterCleanup.skipTransitionPrefixDescription_haltsFromTape
      [none]
      (List.append ((SelectedMergePaddedEmitterOuterTailBits p).map some)
        [none, none])

theorem SelectedMergePaddedEmitterAfterTransitionPaddedTape_move_left_move_right
    (p : SelectedMergeEmitterPayload) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (SelectedMergePaddedEmitterAfterTransitionPaddedTape p)) =
      SelectedMergePaddedEmitterAfterTransitionPaddedTape p := by
  rcases
      SelectedMergePaddedEmitterOuterTailBits_cons_cons_false_false p with
    ⟨tail, htail⟩
  rw [SelectedMergePaddedEmitterAfterTransitionPaddedTape, htail]
  simpa [List.map_append, List.append_assoc] using
    tapeAtCells_move_left_move_right_cons_cons
      (List.append
        ((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse
        [none])
      (some false) (some false)
      (List.append (tail.map some) [none, none])

def SelectedMergePaddedEmitterAfterInputPaddedTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  (CanonicalLayouts.DovetailLayoutScanner.boolWordCanonicalHandoffConfigWithBaseAndRight
      (ParsedLayoutBits p.L)
      (List.append
        (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse)
        [none])
      (SelectedMergePaddedEmitterOuterSuffixBits p)
      [none, none]).tape

def SelectedMergePaddedEmitterAfterInputPaddedHandoffTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells
    (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
        ((ParsedLayoutBits p.L).map some)
        (List.append
          (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse)
          [none]))
    (List.append ((SelectedMergePaddedEmitterOuterSuffixBits p).map some)
      [none, none])

theorem selectedMergePaddedEmitterInputScanner_haltsFrom_afterTransitionPadded
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterInputScannerDescription.HaltsFromTape
      (SelectedMergePaddedEmitterAfterTransitionPaddedTape p)
      (SelectedMergePaddedEmitterAfterInputPaddedTape p) := by
  rcases SelectedMergePaddedEmitterOuterSuffixBits_cons_false p with
    ⟨suffixTail, hsuffix⟩
  rcases
      CanonicalLayouts.DovetailLayoutScanner.run_cellList_raw_to_canonical_handoff_withBaseAndRight
          ((ParsedLayoutBits p.L).map some)
          (List.append
            (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse)
            [none])
          suffixTail [none, none] with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [MachineDescription.HaltsFromTapeIn,
      SelectedMergePaddedEmitterInputScannerDescription,
      SelectedMergePaddedEmitterAfterTransitionPaddedTape,
      SelectedMergePaddedEmitterOuterTailBits_eq_boolWordFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits,
      hsuffix,
      DovetailInitialLayoutInitializer.config,
      List.append_assoc]
      using congrArg MachineDescription.Configuration.state hsteps
  · simpa [MachineDescription.HaltsFromTapeIn,
      SelectedMergePaddedEmitterInputScannerDescription,
      SelectedMergePaddedEmitterAfterTransitionPaddedTape,
      SelectedMergePaddedEmitterAfterInputPaddedTape,
      SelectedMergePaddedEmitterOuterTailBits_eq_boolWordFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits,
      hsuffix,
      DovetailInitialLayoutInitializer.config,
      List.append_assoc]
      using congrArg MachineDescription.Configuration.tape hsteps

theorem selectedMergePaddedEmitterAfterInputPaddedTape_move_right
    (p : SelectedMergeEmitterPayload) :
    Tape.move Direction.right
        (SelectedMergePaddedEmitterAfterInputPaddedTape p) =
      SelectedMergePaddedEmitterAfterInputPaddedHandoffTape p := by
  rcases SelectedMergePaddedEmitterOuterSuffixBits_cons_false p with
    ⟨suffixTail, hsuffix⟩
  rw [SelectedMergePaddedEmitterAfterInputPaddedTape,
    SelectedMergePaddedEmitterAfterInputPaddedHandoffTape, hsuffix]
  simpa [CanonicalLayouts.DovetailLayoutScanner.boolWordCanonicalHandoffConfigWithBaseAndRight] using
    CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalHandoffConfigWithBaseAndRight_move_right
        ((ParsedLayoutBits p.L).map some)
        (List.append
          (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse)
          [none])
        false suffixTail [none, none]

def SelectedMergePaddedEmitterAfterStagePaddedTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  (CanonicalLayouts.DovetailStagePrefix.nonemptyNatSuffixHandoffConfigWithBaseAndRight
      p.S.stage
      (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
        ((ParsedLayoutBits p.L).map some)
        (List.append
          (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse)
          [none]))
      (SelectedMergePaddedEmitterOuterStageSuffixBits p)
      [none, none]).tape

def SelectedMergePaddedEmitterAfterStagePaddedHandoffTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells
    (List.append
      ((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          p.S.stage).reverse.map some)
      (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
        ((ParsedLayoutBits p.L).map some)
        (List.append
          (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse)
          [none])))
    (List.append ((SelectedMergePaddedEmitterOuterStageSuffixBits p).map some)
      [none, none])

theorem selectedMergePaddedEmitterStageScanner_haltsFromAfterInputPaddedHandoff
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterStageScannerDescription.HaltsFromTape
      (SelectedMergePaddedEmitterAfterInputPaddedHandoffTape p)
      (SelectedMergePaddedEmitterAfterStagePaddedTape p) := by
  rcases SelectedMergePaddedEmitterOuterStageSuffixBits_cons_false p with
    ⟨suffixTail, hsuffix⟩
  rcases
      CanonicalLayouts.DovetailStagePrefix.run_nonemptyNatSuffix_raw_to_handoff_withBaseAndRight
          p.S.stage
          (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
            ((ParsedLayoutBits p.L).map some)
            (List.append
              (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse)
              [none]))
          false suffixTail [none, none] with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [MachineDescription.HaltsFromTapeIn,
      SelectedMergePaddedEmitterStageScannerDescription,
      CanonicalLayouts.DovetailStagePrefix.NonemptyNatSuffixScannerDescription,
      SelectedMergePaddedEmitterAfterInputPaddedHandoffTape,
      SelectedMergePaddedEmitterOuterSuffixBits_eq_stageFieldBits,
      hsuffix,
      DovetailInitialLayoutInitializer.config,
      List.append_assoc]
      using congrArg MachineDescription.Configuration.state hsteps
  · simpa [MachineDescription.HaltsFromTapeIn,
      SelectedMergePaddedEmitterStageScannerDescription,
      CanonicalLayouts.DovetailStagePrefix.NonemptyNatSuffixScannerDescription,
      SelectedMergePaddedEmitterAfterInputPaddedHandoffTape,
      SelectedMergePaddedEmitterAfterStagePaddedTape,
      SelectedMergePaddedEmitterOuterSuffixBits_eq_stageFieldBits,
      hsuffix,
      DovetailInitialLayoutInitializer.config,
      List.append_assoc]
      using congrArg MachineDescription.Configuration.tape hsteps

theorem selectedMergePaddedEmitterAfterStagePaddedTape_move_right
    (p : SelectedMergeEmitterPayload) :
    Tape.move Direction.right
        (SelectedMergePaddedEmitterAfterStagePaddedTape p) =
      SelectedMergePaddedEmitterAfterStagePaddedHandoffTape p := by
  rcases SelectedMergePaddedEmitterOuterStageSuffixBits_cons_false p with
    ⟨suffixTail, hsuffix⟩
  rw [SelectedMergePaddedEmitterAfterStagePaddedTape,
    SelectedMergePaddedEmitterAfterStagePaddedHandoffTape, hsuffix]
  simpa using
    CanonicalLayouts.DovetailStagePrefix.nonemptyNatSuffixHandoffConfigWithBaseAndRight_move_right
        p.S.stage
        (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
          ((ParsedLayoutBits p.L).map some)
          (List.append
            (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse)
            [none]))
        false suffixTail [none, none]

def SelectedMergePaddedEmitterAfterConfigPaddedTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalHandoffConfigWithBaseAndRight
    p.S.config.tape.right
    (List.append
      ((CanonicalLayouts.DovetailLayoutScanner.cellCodeBits
        p.S.config.tape.head).reverse.map some)
      (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
        p.S.config.tape.left
        (List.append
          ((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            p.S.config.state).reverse.map some)
          (List.append
            ((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              p.S.stage).reverse.map some)
            (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
              ((ParsedLayoutBits p.L).map some)
              (List.append
                (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse)
                [none]))))))
    (SelectedMergePaddedEmitterOuterHitSuffixBits p)
    [none, none]).tape

def SelectedMergePaddedEmitterAfterConfigPaddedHandoffTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells
    (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
      p.S.config
      (List.append
        ((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          p.S.stage).reverse.map some)
        (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
          ((ParsedLayoutBits p.L).map some)
          (List.append
            (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse)
            [none]))))
    (List.append ((SelectedMergePaddedEmitterOuterHitSuffixBits p).map some)
      [none, none])

theorem selectedMergePaddedEmitterConfigScanner_haltsFromAfterStagePaddedHandoff
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterConfigScannerDescription.HaltsFromTape
      (SelectedMergePaddedEmitterAfterStagePaddedHandoffTape p)
      (SelectedMergePaddedEmitterAfterConfigPaddedTape p) := by
  rcases SelectedMergePaddedEmitterOuterHitSuffixBits_cons_false p with
    ⟨suffixTail, hsuffix⟩
  rcases
      CanonicalLayouts.DovetailLayoutScanner.run_configurationSuffix_raw_to_handoff_withBaseAndRight
        p.S.config
        (List.append
          ((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            p.S.stage).reverse.map some)
          (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
            ((ParsedLayoutBits p.L).map some)
            (List.append
              (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse)
              [none])))
        suffixTail [none, none] with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [MachineDescription.HaltsFromTapeIn,
      SelectedMergePaddedEmitterConfigScannerDescription,
      SelectedMergePaddedEmitterAfterStagePaddedHandoffTape,
      SelectedMergePaddedEmitterOuterStageSuffixBits_eq_configurationFieldBits,
      hsuffix,
      DovetailInitialLayoutInitializer.config,
      List.append_assoc]
      using congrArg MachineDescription.Configuration.state hsteps
  · simpa [MachineDescription.HaltsFromTapeIn,
      SelectedMergePaddedEmitterConfigScannerDescription,
      SelectedMergePaddedEmitterAfterStagePaddedHandoffTape,
      SelectedMergePaddedEmitterAfterConfigPaddedTape,
      SelectedMergePaddedEmitterOuterStageSuffixBits_eq_configurationFieldBits,
      hsuffix,
      DovetailInitialLayoutInitializer.config,
      List.append_assoc]
      using congrArg MachineDescription.Configuration.tape hsteps

theorem selectedMergePaddedEmitterAfterConfigPaddedTape_move_right
    (p : SelectedMergeEmitterPayload) :
    Tape.move Direction.right
        (SelectedMergePaddedEmitterAfterConfigPaddedTape p) =
      SelectedMergePaddedEmitterAfterConfigPaddedHandoffTape p := by
  rcases SelectedMergePaddedEmitterOuterHitSuffixBits_cons_false p with
    ⟨suffixTail, hsuffix⟩
  rw [SelectedMergePaddedEmitterAfterConfigPaddedTape,
    SelectedMergePaddedEmitterAfterConfigPaddedHandoffTape, hsuffix]
  have hmove :=
    CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalHandoffConfigWithBaseAndRight_move_right
        p.S.config.tape.right
        (List.append
          ((CanonicalLayouts.DovetailLayoutScanner.cellCodeBits
            p.S.config.tape.head).reverse.map some)
          (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
            p.S.config.tape.left
            (List.append
              ((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                p.S.config.state).reverse.map some)
              (List.append
                ((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  p.S.stage).reverse.map some)
                (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
                  ((ParsedLayoutBits p.L).map some)
                  (List.append
                    (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse)
                    [none]))))))
        false suffixTail [none, none]
  simpa [CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase,
    List.append_assoc] using hmove

theorem cellListCanonicalRestoredLeftWithBase_append_base
    (cells baseLeft extra : List (Option Bool)) :
    CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
        cells (List.append baseLeft extra) =
      List.append
        (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
          cells baseLeft)
        extra := by
  simp [
    CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase,
    CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalFinishStartLeftWithBase,
    List.append_assoc]

theorem configurationRestoredLeftWithBase_append_base
    (cfg : Configuration) (baseLeft extra : List (Option Bool)) :
    CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
        cfg (List.append baseLeft extra) =
      List.append
        (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
          cfg baseLeft)
        extra := by
  rw [←
    CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev_map_some_withBase
      cfg (List.append baseLeft extra)]
  rw [←
    CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev_map_some_withBase
      cfg baseLeft]
  simp [List.append_assoc]

theorem selectedMergePaddedEmitterHitScanner_runConfig_withRight
    (b : Bool) (left rightCells : List (Option Bool)) :
    SelectedMergePaddedEmitterHitScannerDescription.runConfig 4
        (DovetailInitialLayoutInitializer.config 0 left
          (List.append
            ((encodeCodeWordAsInput (encodeBoolAppend b [])).map some)
            rightCells)) =
      DovetailInitialLayoutInitializer.config 5
        (((encodeCodeWordAsInput (encodeBoolAppend b [])).reverse.map some) ++
          left)
        rightCells := by
  cases b <;> cases rightCells <;>
    simp [SelectedMergePaddedEmitterHitScannerDescription,
      DovetailInitialLayoutInitializer.config,
      DovetailInitialLayoutInitializer.tapeAtCells,
      MachineDescription.runConfig,
      MachineDescription.stepConfig,
      MachineDescription.lookupTransition,
      MachineDescription.Matches,
      MachineDescription.transition,
      encodeBoolAppend, encodeCellAppend, encodeCell,
      encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

def SelectedMergePaddedEmitterAfterHitPaddedTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells
    (((SelectedMergePaddedEmitterOuterHitSuffixBits p).reverse.map some) ++
      (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
        p.S.config
        (List.append
          ((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            p.S.stage).reverse.map some)
          (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
            ((ParsedLayoutBits p.L).map some)
            (List.append
              (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse)
              [none])))))
    [none, none]

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
    exact cellListCanonicalRestoredLeftWithBase_append_base
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
      configurationRestoredLeftWithBase_append_base
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

theorem selectedMergePaddedEmitterHitScanner_haltsFromAfterConfigPaddedHandoff
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterHitScannerDescription.HaltsFromTape
      (SelectedMergePaddedEmitterAfterConfigPaddedHandoffTape p)
      (SelectedMergePaddedEmitterAfterHitPaddedTape p) := by
  refine ⟨4, ?_⟩
  constructor
  · simpa [MachineDescription.HaltsFromTapeIn,
      SelectedMergePaddedEmitterAfterConfigPaddedHandoffTape,
      SelectedMergePaddedEmitterAfterHitPaddedTape,
      SelectedMergePaddedEmitterOuterHitSuffixBits,
      SelectedMergePaddedEmitterOuterHitSuffixCode,
      DovetailInitialLayoutInitializer.config,
      List.append_assoc]
      using
        congrArg MachineDescription.Configuration.state
          (selectedMergePaddedEmitterHitScanner_runConfig_withRight
            p.S.hit
            (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
              p.S.config
              (List.append
                ((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  p.S.stage).reverse.map some)
                (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
                  ((ParsedLayoutBits p.L).map some)
                  (List.append
                    (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse)
                    [none]))))
            [none, none])
  · simpa [MachineDescription.HaltsFromTapeIn,
      SelectedMergePaddedEmitterAfterConfigPaddedHandoffTape,
      SelectedMergePaddedEmitterAfterHitPaddedTape,
      SelectedMergePaddedEmitterOuterHitSuffixBits,
      SelectedMergePaddedEmitterOuterHitSuffixCode,
      DovetailInitialLayoutInitializer.config,
      List.append_assoc]
      using
        congrArg MachineDescription.Configuration.tape
          (selectedMergePaddedEmitterHitScanner_runConfig_withRight
            p.S.hit
            (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
              p.S.config
              (List.append
                ((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  p.S.stage).reverse.map some)
                (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
                  ((ParsedLayoutBits p.L).map some)
                  (List.append
                    (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse)
                    [none]))))
            [none, none])

theorem selectedMergePaddedEmitterSourceScanner_haltsFrom_afterTransitionPadded
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterSourceScannerDescription.HaltsFromTape
      (SelectedMergePaddedEmitterAfterTransitionPaddedTape p)
      (SelectedMergePaddedEmitterAfterHitPaddedTape p) := by
  have hconfigHit :
      (seqSubroutine
        SelectedMergePaddedEmitterConfigScannerDescription
        SelectedMergePaddedEmitterHitScannerDescription
        Direction.right).HaltsFromTape
        (SelectedMergePaddedEmitterAfterStagePaddedHandoffTape p)
        (SelectedMergePaddedEmitterAfterHitPaddedTape p) := by
    exact
      CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
        (A := SelectedMergePaddedEmitterConfigScannerDescription)
        (B := SelectedMergePaddedEmitterHitScannerDescription)
        (handoffMove := Direction.right)
        selectedMergePaddedEmitterConfigScanner_subroutineReady
        selectedMergePaddedEmitterHitScanner_subroutineReady
        (selectedMergePaddedEmitterConfigScanner_haltsFromAfterStagePaddedHandoff p)
        (selectedMergePaddedEmitterAfterConfigPaddedTape_move_right p)
        (selectedMergePaddedEmitterHitScanner_haltsFromAfterConfigPaddedHandoff p)
  have hstageConfigHit :
      (seqSubroutine
        SelectedMergePaddedEmitterStageScannerDescription
        (seqSubroutine
          SelectedMergePaddedEmitterConfigScannerDescription
          SelectedMergePaddedEmitterHitScannerDescription
          Direction.right)
        Direction.right).HaltsFromTape
        (SelectedMergePaddedEmitterAfterInputPaddedHandoffTape p)
        (SelectedMergePaddedEmitterAfterHitPaddedTape p) := by
    exact
      CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
        (A := SelectedMergePaddedEmitterStageScannerDescription)
        (B :=
          seqSubroutine
            SelectedMergePaddedEmitterConfigScannerDescription
            SelectedMergePaddedEmitterHitScannerDescription
            Direction.right)
        (handoffMove := Direction.right)
        selectedMergePaddedEmitterStageScanner_subroutineReady
        (seqSubroutine_subroutineReady
          selectedMergePaddedEmitterConfigScanner_subroutineReady
          selectedMergePaddedEmitterHitScanner_subroutineReady)
        (selectedMergePaddedEmitterStageScanner_haltsFromAfterInputPaddedHandoff p)
        (selectedMergePaddedEmitterAfterStagePaddedTape_move_right p)
        hconfigHit
  simpa [SelectedMergePaddedEmitterSourceScannerDescription] using
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      (A := SelectedMergePaddedEmitterInputScannerDescription)
      (B :=
        seqSubroutine
          SelectedMergePaddedEmitterStageScannerDescription
          (seqSubroutine
            SelectedMergePaddedEmitterConfigScannerDescription
            SelectedMergePaddedEmitterHitScannerDescription
            Direction.right)
          Direction.right)
      (handoffMove := Direction.right)
      selectedMergePaddedEmitterInputScanner_subroutineReady
      (seqSubroutine_subroutineReady
        selectedMergePaddedEmitterStageScanner_subroutineReady
        (seqSubroutine_subroutineReady
          selectedMergePaddedEmitterConfigScanner_subroutineReady
          selectedMergePaddedEmitterHitScanner_subroutineReady))
      (selectedMergePaddedEmitterInputScanner_haltsFrom_afterTransitionPadded p)
      (selectedMergePaddedEmitterAfterInputPaddedTape_move_right p)
      hstageConfigHit

def SelectedMergePaddedEmitterAfterTransitionPaddedSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      emitter.HaltsFromTape
        (SelectedMergePaddedEmitterAfterTransitionPaddedTape p)
        (SelectedMergeEquivEmitterPaddedOutputTape useAccept p)

def SelectedMergePaddedEmitterAfterTransitionPaddedConstruction :
    Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedMergePaddedEmitterAfterTransitionPaddedSpec useAccept emitter

def SelectedMergePaddedEmitterAfterTransitionPaddedBranchConstruction
    (useAccept : Bool) : Prop :=
  exists emitter : MachineDescription,
    SelectedMergePaddedEmitterAfterTransitionPaddedSpec useAccept emitter

def SelectedMergePaddedEmitterAfterHitPaddedSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      emitter.HaltsFromTape
        (SelectedMergePaddedEmitterAfterHitPaddedTape p)
        (SelectedMergeEquivEmitterPaddedOutputTape useAccept p)

def SelectedMergePaddedEmitterAfterHitPaddedBranchConstruction
    (useAccept : Bool) : Prop :=
  exists emitter : MachineDescription,
    SelectedMergePaddedEmitterAfterHitPaddedSpec useAccept emitter

def SelectedMergePaddedEmitterAfterHitPaddedFromRewind
    (postRewind : MachineDescription) : MachineDescription :=
  SeqViaCanonical
    SelectedMergePaddedEmitterCleanup.sourceRewindDescription
    postRewind

theorem SelectedMergePaddedEmitterAfterHitPaddedSpec_of_rewind
    {useAccept : Bool} {postRewind : MachineDescription}
    (hpostRewind :
      SelectedMergePaddedEmitterAfterHitRewindSpec
        useAccept postRewind) :
    SelectedMergePaddedEmitterAfterHitPaddedSpec useAccept
      (SelectedMergePaddedEmitterAfterHitPaddedFromRewind postRewind) := by
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        SelectedMergePaddedEmitterCleanup.sourceRewindDescription_subroutineReady
        hpostRewind.left
  · intro p
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        SelectedMergePaddedEmitterCleanup.sourceRewindDescription_subroutineReady
        hpostRewind.left
        (sourceRewindDescription_haltsFrom_afterHitPaddedTape p)
        (SelectedMergePaddedEmitterCleanup.rewindTargetPaddedTape_move_left_move_right
          (SelectedMergePaddedEmitterCleanup.sourceBits p))
        (hpostRewind.right p)

def SelectedMergePaddedEmitterAfterTransitionPaddedFromSourceScanner
    (afterHit : MachineDescription) : MachineDescription :=
  SeqViaCanonical
    SelectedMergePaddedEmitterSourceScannerDescription
    afterHit

theorem SelectedMergePaddedEmitterAfterTransitionPaddedSpec_of_afterHitPadded
    {useAccept : Bool} {afterHit : MachineDescription}
    (hafterHit :
      SelectedMergePaddedEmitterAfterHitPaddedSpec
        useAccept afterHit) :
    SelectedMergePaddedEmitterAfterTransitionPaddedSpec useAccept
      (SelectedMergePaddedEmitterAfterTransitionPaddedFromSourceScanner
        afterHit) := by
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        selectedMergePaddedEmitterSourceScanner_subroutineReady
        hafterHit.left
  · intro p
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        selectedMergePaddedEmitterSourceScanner_subroutineReady
        hafterHit.left
        (selectedMergePaddedEmitterSourceScanner_haltsFrom_afterTransitionPadded p)
        (SelectedMergePaddedEmitterAfterHitPaddedTape_move_left_move_right
          p)
        (hafterHit.right p)

theorem SelectedMergePaddedEmitterAfterTransitionPaddedBranchConstruction_of_afterHitPadded
    {useAccept : Bool}
    (h :
      SelectedMergePaddedEmitterAfterHitPaddedBranchConstruction
        useAccept) :
    SelectedMergePaddedEmitterAfterTransitionPaddedBranchConstruction
        useAccept := by
  rcases h with ⟨afterHit, hafterHit⟩
  exact
    ⟨SelectedMergePaddedEmitterAfterTransitionPaddedFromSourceScanner
        afterHit,
      SelectedMergePaddedEmitterAfterTransitionPaddedSpec_of_afterHitPadded
        hafterHit⟩

def SelectedMergePaddedEmitterAfterHitRewindFromTransition
    (afterTransition : MachineDescription) : MachineDescription :=
  SeqViaCanonical
    SelectedMergePaddedEmitterCleanup.skipTransitionPrefixDescription
    afterTransition

theorem SelectedMergePaddedEmitterAfterHitRewindSpec_of_afterTransition
    {useAccept : Bool} {afterTransition : MachineDescription}
    (hafterTransition :
      SelectedMergePaddedEmitterAfterTransitionPaddedSpec
        useAccept afterTransition) :
    SelectedMergePaddedEmitterAfterHitRewindSpec useAccept
      (SelectedMergePaddedEmitterAfterHitRewindFromTransition
        afterTransition) := by
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        SelectedMergePaddedEmitterCleanup.skipTransitionPrefixDescription_subroutineReady
        hafterTransition.left
  · intro p
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        SelectedMergePaddedEmitterCleanup.skipTransitionPrefixDescription_subroutineReady
        hafterTransition.left
        (skipTransitionPrefixDescription_haltsFrom_afterHitRewindSource p)
        (SelectedMergePaddedEmitterAfterTransitionPaddedTape_move_left_move_right
          p)
        (hafterTransition.right p)

theorem SelectedMergePaddedEmitterAfterHitRewindConstruction_of_afterTransition
    (h :
      SelectedMergePaddedEmitterAfterTransitionPaddedConstruction) :
    SelectedMergePaddedEmitterAfterHitRewindConstruction := by
  intro useAccept
  rcases h useAccept with ⟨afterTransition, hafterTransition⟩
  exact
    ⟨SelectedMergePaddedEmitterAfterHitRewindFromTransition
        afterTransition,
      SelectedMergePaddedEmitterAfterHitRewindSpec_of_afterTransition
        hafterTransition⟩

theorem selectedMergePaddedEmitterAfterTransitionPaddedConstruction_of_branches
    (hAccept :
      SelectedMergePaddedEmitterAfterTransitionPaddedBranchConstruction true)
    (hReject :
      SelectedMergePaddedEmitterAfterTransitionPaddedBranchConstruction false) :
    SelectedMergePaddedEmitterAfterTransitionPaddedConstruction := by
  intro useAccept
  cases useAccept
  · exact hReject
  · exact hAccept

def SelectedMergePaddedEmitterAcceptDecodedHandoffTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells []
    (List.append
      ((encodeCodeWordAsInput
        (MachineCodeSymbol.transition ::
          encodeBoolWordAppend p.L.input
            (encodeNatAppend p.L.stage
              (encodeConfigurationAppend p.S.config
                (encodeConfigurationAppend p.L.rejectConfig
                  (encodeBoolAppend p.S.hit
                    (encodeBoolAppend p.L.rejectHit []))))))).map some)
      (List.replicate (SimulatorLayout.asBoolInput p.S).length none))

def SelectedMergePaddedEmitterRejectDecodedHandoffTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells []
    (List.append
      ((encodeCodeWordAsInput
        (MachineCodeSymbol.transition ::
          encodeBoolWordAppend p.L.input
            (encodeNatAppend p.L.stage
              (encodeConfigurationAppend p.L.acceptConfig
                (encodeConfigurationAppend p.S.config
                  (encodeBoolAppend p.L.acceptHit
                    (encodeBoolAppend p.S.hit []))))))).map some)
      (List.replicate (SimulatorLayout.asBoolInput p.S).length none))

theorem SelectedMergePaddedEmitterAcceptDecodedHandoffTape_eq_outputTape
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterAcceptDecodedHandoffTape p =
      SelectedMergeEquivEmitterPaddedOutputTape true p := by
  rw [SelectedMergePaddedEmitterAcceptDecodedHandoffTape,
    SelectedMergeEquivEmitterPaddedOutputTape_true_eq_tapeAtCells_fields]

theorem SelectedMergePaddedEmitterRejectDecodedHandoffTape_eq_outputTape
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterRejectDecodedHandoffTape p =
      SelectedMergeEquivEmitterPaddedOutputTape false p := by
  rw [SelectedMergePaddedEmitterRejectDecodedHandoffTape,
    SelectedMergeEquivEmitterPaddedOutputTape_false_eq_tapeAtCells_fields]

def SelectedMergePaddedEmitterAfterHitPaddedAcceptDecodedSpec
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      emitter.HaltsFromTape
        (SelectedMergePaddedEmitterAfterHitPaddedTape p)
        (SelectedMergePaddedEmitterAcceptDecodedHandoffTape p)

def SelectedMergePaddedEmitterAfterHitPaddedRejectDecodedSpec
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      emitter.HaltsFromTape
        (SelectedMergePaddedEmitterAfterHitPaddedTape p)
        (SelectedMergePaddedEmitterRejectDecodedHandoffTape p)

def SelectedMergePaddedEmitterAfterHitPaddedAcceptDecodedConstruction :
    Prop :=
  exists emitter : MachineDescription,
    SelectedMergePaddedEmitterAfterHitPaddedAcceptDecodedSpec emitter

def SelectedMergePaddedEmitterAfterHitPaddedRejectDecodedConstruction :
    Prop :=
  exists emitter : MachineDescription,
    SelectedMergePaddedEmitterAfterHitPaddedRejectDecodedSpec emitter

def SelectedMergePaddedEmitterAfterHitPaddedAcceptSourceFieldsSpec
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      emitter.HaltsFromTape
        (SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape p)
        (SelectedMergePaddedEmitterAcceptDecodedHandoffTape p)

def SelectedMergePaddedEmitterAfterHitPaddedRejectSourceFieldsSpec
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      emitter.HaltsFromTape
        (SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape p)
        (SelectedMergePaddedEmitterRejectDecodedHandoffTape p)

def SelectedMergePaddedEmitterAfterHitPaddedAcceptSourceFieldsConstruction :
    Prop :=
  exists emitter : MachineDescription,
    SelectedMergePaddedEmitterAfterHitPaddedAcceptSourceFieldsSpec emitter

def SelectedMergePaddedEmitterAfterHitPaddedRejectSourceFieldsConstruction :
    Prop :=
  exists emitter : MachineDescription,
    SelectedMergePaddedEmitterAfterHitPaddedRejectSourceFieldsSpec emitter

def SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedSpec
    (parser : MachineDescription) : Prop :=
  parser.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      parser.HaltsFromTape
        (SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape p)
        (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p)

def SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedConstruction :
    Prop :=
  exists parser : MachineDescription,
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedSpec parser

def SelectedMergePaddedEmitterAfterHitPaddedAcceptParsedInnerSpec
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      emitter.HaltsFromTape
        (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p)
        (SelectedMergePaddedEmitterAcceptDecodedHandoffTape p)

def SelectedMergePaddedEmitterAfterHitPaddedRejectParsedInnerSpec
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      emitter.HaltsFromTape
        (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p)
        (SelectedMergePaddedEmitterRejectDecodedHandoffTape p)

def SelectedMergePaddedEmitterAfterHitPaddedAcceptParsedInnerConstruction :
    Prop :=
  exists emitter : MachineDescription,
    SelectedMergePaddedEmitterAfterHitPaddedAcceptParsedInnerSpec emitter

def SelectedMergePaddedEmitterAfterHitPaddedRejectParsedInnerConstruction :
    Prop :=
  exists emitter : MachineDescription,
    SelectedMergePaddedEmitterAfterHitPaddedRejectParsedInnerSpec emitter

def SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsFromNestedParsed
    (parser emitter : MachineDescription) : MachineDescription :=
  SeqViaCanonical parser emitter

theorem
    selectedMergePaddedEmitterAfterHitPaddedAcceptSourceFieldsSpec_of_parsedInner
    {parser emitter : MachineDescription}
    (hparser :
      SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedSpec parser)
    (hemitter :
      SelectedMergePaddedEmitterAfterHitPaddedAcceptParsedInnerSpec emitter) :
    SelectedMergePaddedEmitterAfterHitPaddedAcceptSourceFieldsSpec
      (SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsFromNestedParsed
        parser emitter) := by
  constructor
  · exact SeqViaCanonical_subroutineReady hparser.left hemitter.left
  · intro p
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        hparser.left hemitter.left
        (hparser.right p)
        (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape_move_left_move_right
          p)
        (hemitter.right p)

theorem
    selectedMergePaddedEmitterAfterHitPaddedRejectSourceFieldsSpec_of_parsedInner
    {parser emitter : MachineDescription}
    (hparser :
      SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedSpec parser)
    (hemitter :
      SelectedMergePaddedEmitterAfterHitPaddedRejectParsedInnerSpec emitter) :
    SelectedMergePaddedEmitterAfterHitPaddedRejectSourceFieldsSpec
      (SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsFromNestedParsed
        parser emitter) := by
  constructor
  · exact SeqViaCanonical_subroutineReady hparser.left hemitter.left
  · intro p
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        hparser.left hemitter.left
        (hparser.right p)
        (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape_move_left_move_right
          p)
        (hemitter.right p)

theorem
    selectedMergePaddedEmitterAfterHitPaddedAcceptSourceFieldsConstruction_of_parsedInner
    (hparser :
      SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedConstruction)
    (hemitter :
      SelectedMergePaddedEmitterAfterHitPaddedAcceptParsedInnerConstruction) :
    SelectedMergePaddedEmitterAfterHitPaddedAcceptSourceFieldsConstruction := by
  rcases hparser with ⟨parser, hparser⟩
  rcases hemitter with ⟨emitter, hemits⟩
  exact
    ⟨SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsFromNestedParsed
        parser emitter,
      selectedMergePaddedEmitterAfterHitPaddedAcceptSourceFieldsSpec_of_parsedInner
        hparser hemits⟩

theorem
    selectedMergePaddedEmitterAfterHitPaddedRejectSourceFieldsConstruction_of_parsedInner
    (hparser :
      SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedConstruction)
    (hemitter :
      SelectedMergePaddedEmitterAfterHitPaddedRejectParsedInnerConstruction) :
    SelectedMergePaddedEmitterAfterHitPaddedRejectSourceFieldsConstruction := by
  rcases hparser with ⟨parser, hparser⟩
  rcases hemitter with ⟨emitter, hemits⟩
  exact
    ⟨SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsFromNestedParsed
        parser emitter,
      selectedMergePaddedEmitterAfterHitPaddedRejectSourceFieldsSpec_of_parsedInner
        hparser hemits⟩

theorem selectedMergePaddedEmitterAfterHitPaddedAcceptDecodedConstruction_of_sourceFields
    (h :
      SelectedMergePaddedEmitterAfterHitPaddedAcceptSourceFieldsConstruction) :
    SelectedMergePaddedEmitterAfterHitPaddedAcceptDecodedConstruction := by
  rcases h with ⟨emitter, hemits⟩
  refine ⟨emitter, ?_⟩
  constructor
  · exact hemits.left
  · intro p
    rw [SelectedMergePaddedEmitterAfterHitPaddedTape_eq_sourceFieldsTape p]
    exact hemits.right p

theorem selectedMergePaddedEmitterAfterHitPaddedRejectDecodedConstruction_of_sourceFields
    (h :
      SelectedMergePaddedEmitterAfterHitPaddedRejectSourceFieldsConstruction) :
    SelectedMergePaddedEmitterAfterHitPaddedRejectDecodedConstruction := by
  rcases h with ⟨emitter, hemits⟩
  refine ⟨emitter, ?_⟩
  constructor
  · exact hemits.left
  · intro p
    rw [SelectedMergePaddedEmitterAfterHitPaddedTape_eq_sourceFieldsTape p]
    exact hemits.right p

theorem selectedMergePaddedEmitterAfterHitPaddedAcceptConstruction_of_decoded
    (h :
      SelectedMergePaddedEmitterAfterHitPaddedAcceptDecodedConstruction) :
    SelectedMergePaddedEmitterAfterHitPaddedBranchConstruction true := by
  rcases h with ⟨emitter, hemits⟩
  refine ⟨emitter, ?_⟩
  constructor
  · exact hemits.left
  · intro p
    rw [←
      SelectedMergePaddedEmitterAcceptDecodedHandoffTape_eq_outputTape p]
    exact hemits.right p

theorem selectedMergePaddedEmitterAfterHitPaddedRejectConstruction_of_decoded
    (h :
      SelectedMergePaddedEmitterAfterHitPaddedRejectDecodedConstruction) :
    SelectedMergePaddedEmitterAfterHitPaddedBranchConstruction false := by
  rcases h with ⟨emitter, hemits⟩
  refine ⟨emitter, ?_⟩
  constructor
  · exact hemits.left
  · intro p
    rw [←
      SelectedMergePaddedEmitterRejectDecodedHandoffTape_eq_outputTape p]
    exact hemits.right p

/--
Common finite-machine leaf that parses the nested layout code word after the
outer source fields have been restored.
-/
theorem selectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedConstruction :
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedConstruction := by
  sorry

/--
Finite-machine leaf that rewrites the parsed nested layout plus outer source
fields into the decoded accepting-merge field order.
-/
theorem selectedMergePaddedEmitterAfterHitPaddedAcceptParsedInnerConstruction :
    SelectedMergePaddedEmitterAfterHitPaddedAcceptParsedInnerConstruction := by
  sorry

/--
Finite-machine leaf that rewrites the parsed nested layout plus outer source
fields into the decoded rejecting-merge field order.
-/
theorem selectedMergePaddedEmitterAfterHitPaddedRejectParsedInnerConstruction :
    SelectedMergePaddedEmitterAfterHitPaddedRejectParsedInnerConstruction := by
  sorry

theorem selectedMergePaddedEmitterAfterHitPaddedAcceptSourceFieldsConstruction :
    SelectedMergePaddedEmitterAfterHitPaddedAcceptSourceFieldsConstruction := by
  exact
    selectedMergePaddedEmitterAfterHitPaddedAcceptSourceFieldsConstruction_of_parsedInner
      selectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedConstruction
      selectedMergePaddedEmitterAfterHitPaddedAcceptParsedInnerConstruction

theorem selectedMergePaddedEmitterAfterHitPaddedRejectSourceFieldsConstruction :
    SelectedMergePaddedEmitterAfterHitPaddedRejectSourceFieldsConstruction := by
  exact
    selectedMergePaddedEmitterAfterHitPaddedRejectSourceFieldsConstruction_of_parsedInner
      selectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedConstruction
      selectedMergePaddedEmitterAfterHitPaddedRejectParsedInnerConstruction

theorem selectedMergePaddedEmitterAfterHitPaddedAcceptDecodedConstruction :
    SelectedMergePaddedEmitterAfterHitPaddedAcceptDecodedConstruction := by
  exact
    selectedMergePaddedEmitterAfterHitPaddedAcceptDecodedConstruction_of_sourceFields
      selectedMergePaddedEmitterAfterHitPaddedAcceptSourceFieldsConstruction

theorem selectedMergePaddedEmitterAfterHitPaddedRejectDecodedConstruction :
    SelectedMergePaddedEmitterAfterHitPaddedRejectDecodedConstruction := by
  exact
    selectedMergePaddedEmitterAfterHitPaddedRejectDecodedConstruction_of_sourceFields
      selectedMergePaddedEmitterAfterHitPaddedRejectSourceFieldsConstruction

/--
Post-source-scanner finite-machine leaf for selected merge under the accepting
padded equivalence branch.
-/
theorem selectedMergePaddedEmitterAfterHitPaddedAcceptConstruction :
    SelectedMergePaddedEmitterAfterHitPaddedBranchConstruction true := by
  exact
    selectedMergePaddedEmitterAfterHitPaddedAcceptConstruction_of_decoded
      selectedMergePaddedEmitterAfterHitPaddedAcceptDecodedConstruction

/--
Post-source-scanner finite-machine leaf for selected merge under the rejecting
padded equivalence branch.
-/
theorem selectedMergePaddedEmitterAfterHitPaddedRejectConstruction :
    SelectedMergePaddedEmitterAfterHitPaddedBranchConstruction false := by
  exact
    selectedMergePaddedEmitterAfterHitPaddedRejectConstruction_of_decoded
      selectedMergePaddedEmitterAfterHitPaddedRejectDecodedConstruction

/--
Post-transition finite-machine leaf for selected merge under the accepting
padded equivalence branch.  The common source scanner reduces this branch to
the post-source-scanner leaf.
-/
theorem selectedMergePaddedEmitterAfterTransitionPaddedAcceptConstruction :
    SelectedMergePaddedEmitterAfterTransitionPaddedBranchConstruction true := by
  exact
    SelectedMergePaddedEmitterAfterTransitionPaddedBranchConstruction_of_afterHitPadded
      selectedMergePaddedEmitterAfterHitPaddedAcceptConstruction

/--
Post-transition finite-machine leaf for selected merge under the rejecting
padded equivalence branch.  The common source scanner reduces this branch to
the post-source-scanner leaf.
-/
theorem selectedMergePaddedEmitterAfterTransitionPaddedRejectConstruction :
    SelectedMergePaddedEmitterAfterTransitionPaddedBranchConstruction false := by
  exact
    SelectedMergePaddedEmitterAfterTransitionPaddedBranchConstruction_of_afterHitPadded
      selectedMergePaddedEmitterAfterHitPaddedRejectConstruction

/--
Combined post-transition finite-machine leaf for selected merge under the
padded equivalence contract.  The construction is assembled from the two
branch-specific finite-machine leaves.
-/
theorem selectedMergePaddedEmitterAfterTransitionPaddedCoreConstruction :
    SelectedMergePaddedEmitterAfterTransitionPaddedConstruction := by
  exact selectedMergePaddedEmitterAfterTransitionPaddedConstruction_of_branches
    selectedMergePaddedEmitterAfterTransitionPaddedAcceptConstruction
    selectedMergePaddedEmitterAfterTransitionPaddedRejectConstruction

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
