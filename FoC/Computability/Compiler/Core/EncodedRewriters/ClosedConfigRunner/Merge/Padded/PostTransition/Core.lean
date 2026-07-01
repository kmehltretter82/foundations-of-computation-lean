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

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
