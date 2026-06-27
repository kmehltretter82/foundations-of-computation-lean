import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.FiniteDescriptions.MergePadded.Shape

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

def SelectedMergePaddedEmitterHeaderRewriterDescription :
    MachineDescription where
  stateCount := 5
  start := 0
  halt := 4
  transitions :=
    [ MachineDescription.transition 0 (some false) (some false)
        Direction.right 1,
      MachineDescription.transition 1 (some false) (some false)
        Direction.right 2,
      MachineDescription.transition 2 (some false) (some false)
        Direction.right 3,
      MachineDescription.transition 3 (some false) (some true)
        Direction.right 4 ]

theorem selectedMergePaddedEmitterHeaderRewriter_subroutineReady :
    SelectedMergePaddedEmitterHeaderRewriterDescription.SubroutineReady := by
  constructor
  · constructor
    · decide
    constructor
    · decide
    constructor
    · decide
    constructor
    · intro t ht
      simp [SelectedMergePaddedEmitterHeaderRewriterDescription,
        MachineDescription.transition,
        TransitionDescription.WellFormed] at ht ⊢
      rcases ht with rfl | rfl | rfl | rfl <;> decide
    · intro t u ht hu hkey
      simp [SelectedMergePaddedEmitterHeaderRewriterDescription,
        MachineDescription.transition] at ht hu
      rcases ht with rfl | rfl | rfl | rfl <;>
        rcases hu with rfl | rfl | rfl | rfl <;>
          simp [TransitionDescription.SameKey,
            TransitionDescription.SameAction] at hkey ⊢
  · intro t ht
    simp [SelectedMergePaddedEmitterHeaderRewriterDescription,
      MachineDescription.transition] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> decide

theorem selectedMergePaddedEmitterHeaderRewriter_runConfig
    (left rest : List (Option Bool)) :
    SelectedMergePaddedEmitterHeaderRewriterDescription.runConfig 4
        (DovetailInitialLayoutInitializer.config 0 left
          (some false :: some false :: some false :: some false :: rest)) =
      DovetailInitialLayoutInitializer.config 4
        (some true :: some false :: some false :: some false :: left)
        rest := by
  cases rest with
  | nil =>
      simp [SelectedMergePaddedEmitterHeaderRewriterDescription,
        DovetailInitialLayoutInitializer.config,
        DovetailInitialLayoutInitializer.tapeAtCells,
        MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition,
        MachineDescription.Matches,
        MachineDescription.transition,
        Tape.read, Tape.write, Tape.move, Tape.moveRight]
  | cons cell rest =>
      simp [SelectedMergePaddedEmitterHeaderRewriterDescription,
        DovetailInitialLayoutInitializer.config,
        DovetailInitialLayoutInitializer.tapeAtCells,
        MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition,
        MachineDescription.Matches,
        MachineDescription.transition,
        Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem selectedMergePaddedEmitterHeaderRewriter_haltsFromTapeIn
    (left rest : List (Option Bool)) :
    SelectedMergePaddedEmitterHeaderRewriterDescription.HaltsFromTapeIn 4
      (DovetailInitialLayoutInitializer.tapeAtCells left
        (((encodeCodeSymbolAsInput MachineCodeSymbol.header).map some) ++
          rest))
      (DovetailInitialLayoutInitializer.tapeAtCells
        (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse ++
          left)
        rest) := by
  constructor
  · simpa [MachineDescription.HaltsFromTapeIn,
      SelectedMergePaddedEmitterHeaderRewriterDescription,
      encodeCodeSymbolAsInput,
      DovetailInitialLayoutInitializer.config] using
      congrArg MachineDescription.Configuration.state
        (selectedMergePaddedEmitterHeaderRewriter_runConfig left rest)
  · simpa [MachineDescription.HaltsFromTapeIn,
      SelectedMergePaddedEmitterHeaderRewriterDescription,
      encodeCodeSymbolAsInput,
      DovetailInitialLayoutInitializer.config] using
      congrArg MachineDescription.Configuration.tape
        (selectedMergePaddedEmitterHeaderRewriter_runConfig left rest)

theorem selectedMergePaddedEmitterHeaderRewriter_haltsFromTape
    (left rest : List (Option Bool)) :
    SelectedMergePaddedEmitterHeaderRewriterDescription.HaltsFromTape
      (DovetailInitialLayoutInitializer.tapeAtCells left
        (((encodeCodeSymbolAsInput MachineCodeSymbol.header).map some) ++
          rest))
      (DovetailInitialLayoutInitializer.tapeAtCells
        (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse ++
          left)
        rest) :=
  ⟨4, selectedMergePaddedEmitterHeaderRewriter_haltsFromTapeIn left rest⟩

def SelectedMergePaddedEmitterOuterTailBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  encodeCodeWordAsInput
    (encodeBoolWordAppend (ParsedLayoutBits p.L)
      (encodeNatAppend p.S.stage
        (encodeConfigurationAppend p.S.config
          (encodeBoolAppend p.S.hit []))))

def SelectedMergePaddedEmitterOuterSuffixCode
    (p : SelectedMergeEmitterPayload) : Word MachineCodeSymbol :=
  encodeNatAppend p.S.stage
    (encodeConfigurationAppend p.S.config
      (encodeBoolAppend p.S.hit []))

def SelectedMergePaddedEmitterOuterStageSuffixCode
    (p : SelectedMergeEmitterPayload) : Word MachineCodeSymbol :=
  encodeConfigurationAppend p.S.config
    (encodeBoolAppend p.S.hit [])

def SelectedMergePaddedEmitterOuterHitSuffixCode
    (p : SelectedMergeEmitterPayload) : Word MachineCodeSymbol :=
  encodeBoolAppend p.S.hit []

def SelectedMergePaddedEmitterOuterSuffixBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  encodeCodeWordAsInput
    (SelectedMergePaddedEmitterOuterSuffixCode p)

def SelectedMergePaddedEmitterOuterStageSuffixBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  encodeCodeWordAsInput
    (SelectedMergePaddedEmitterOuterStageSuffixCode p)

def SelectedMergePaddedEmitterOuterHitSuffixBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  encodeCodeWordAsInput
    (SelectedMergePaddedEmitterOuterHitSuffixCode p)

theorem SelectedMergePaddedEmitterOuterTailBits_eq_boolWordFieldBits
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterOuterTailBits p =
      CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits
        (ParsedLayoutBits p.L)
        (SelectedMergePaddedEmitterOuterSuffixBits p) := by
  rw [SelectedMergePaddedEmitterOuterTailBits,
    SelectedMergePaddedEmitterOuterSuffixBits,
    SelectedMergePaddedEmitterOuterSuffixCode]
  rw [CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits]
  simpa using
    CanonicalLayouts.DovetailLayoutScanner.boolWordBits_eq_encodeBoolWordAppend
        (ParsedLayoutBits p.L)
        (encodeNatAppend p.S.stage
          (encodeConfigurationAppend p.S.config
            (encodeBoolAppend p.S.hit [])))

theorem SelectedMergePaddedEmitterOuterSuffixBits_cons_false
    (p : SelectedMergeEmitterPayload) :
    exists tail : Word Bool,
      SelectedMergePaddedEmitterOuterSuffixBits p = false :: tail := by
  rw [SelectedMergePaddedEmitterOuterSuffixBits,
    SelectedMergePaddedEmitterOuterSuffixCode]
  rw [CanonicalLayouts.DovetailStagePrefix.natBits_eq_encodeNatAppend]
  rcases
      CanonicalLayouts.DovetailLayoutScanner.stageNatBits_cons_false
        p.S.stage with
    ⟨tail, htail⟩
  refine
    ⟨List.append tail
        (encodeCodeWordAsInput
          (encodeConfigurationAppend p.S.config
            (encodeBoolAppend p.S.hit []))), ?_⟩
  simp [htail]

theorem SelectedMergePaddedEmitterOuterSuffixBits_eq_stageFieldBits
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterOuterSuffixBits p =
      List.append
        (FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          p.S.stage)
        (SelectedMergePaddedEmitterOuterStageSuffixBits p) := by
  rw [SelectedMergePaddedEmitterOuterSuffixBits,
    SelectedMergePaddedEmitterOuterSuffixCode,
    SelectedMergePaddedEmitterOuterStageSuffixBits,
    SelectedMergePaddedEmitterOuterStageSuffixCode]
  exact
    CanonicalLayouts.DovetailStagePrefix.natBits_eq_encodeNatAppend
      p.S.stage
      (encodeConfigurationAppend p.S.config
        (encodeBoolAppend p.S.hit []))

theorem SelectedMergePaddedEmitterOuterStageSuffixBits_cons_false
    (p : SelectedMergeEmitterPayload) :
    exists tail : Word Bool,
      SelectedMergePaddedEmitterOuterStageSuffixBits p = false :: tail := by
  rw [SelectedMergePaddedEmitterOuterStageSuffixBits,
    SelectedMergePaddedEmitterOuterStageSuffixCode,
    encodeConfigurationAppend]
  rw [CanonicalLayouts.DovetailStagePrefix.natBits_eq_encodeNatAppend]
  rcases
      CanonicalLayouts.DovetailLayoutScanner.stageNatBits_cons_false
        p.S.config.state with
    ⟨tail, htail⟩
  refine
    ⟨List.append tail
        (encodeCodeWordAsInput
          (encodeTapeAppend p.S.config.tape
            (encodeBoolAppend p.S.hit []))), ?_⟩
  simp [htail]

theorem SelectedMergePaddedEmitterOuterStageSuffixBits_eq_configurationFieldBits
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterOuterStageSuffixBits p =
      CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
        p.S.config
        (SelectedMergePaddedEmitterOuterHitSuffixBits p) := by
  rw [SelectedMergePaddedEmitterOuterStageSuffixBits,
    SelectedMergePaddedEmitterOuterStageSuffixCode,
    SelectedMergePaddedEmitterOuterHitSuffixBits,
    SelectedMergePaddedEmitterOuterHitSuffixCode]
  rw [CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_eq_encodeConfigurationAppend]

theorem SelectedMergePaddedEmitterOuterHitSuffixBits_cons_false
    (p : SelectedMergeEmitterPayload) :
    exists tail : Word Bool,
      SelectedMergePaddedEmitterOuterHitSuffixBits p = false :: tail := by
  cases hhit : p.S.hit
  · refine ⟨[true, false, true], ?_⟩
    simp [SelectedMergePaddedEmitterOuterHitSuffixBits,
      SelectedMergePaddedEmitterOuterHitSuffixCode,
      hhit,
      encodeBoolAppend, encodeCellAppend, encodeCell,
      encodeCodeWordAsInput, encodeCodeSymbolAsInput]
  · refine ⟨[true, true, false], ?_⟩
    simp [SelectedMergePaddedEmitterOuterHitSuffixBits,
      SelectedMergePaddedEmitterOuterHitSuffixCode,
      hhit,
      encodeBoolAppend, encodeCellAppend, encodeCell,
      encodeCodeWordAsInput, encodeCodeSymbolAsInput]

def SelectedMergePaddedEmitterAfterHeaderTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells
    (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse)
    ((SelectedMergePaddedEmitterOuterTailBits p).map some)

theorem SelectedMergeEmitterInputTape_eq_headerTailCells
    (p : SelectedMergeEmitterPayload) :
    SimulatorLayout.tape p.S =
      DovetailInitialLayoutInitializer.tapeAtCells []
        (((encodeCodeSymbolAsInput MachineCodeSymbol.header).map some) ++
          (SelectedMergePaddedEmitterOuterTailBits p).map some) := by
  change Tape.input (SelectedMergeEmitterInputBits p) = _
  rw [SelectedMergeEmitterInputBits_eq_parsedLayoutFields p]
  simp [SelectedMergePaddedEmitterOuterTailBits,
    encodeCodeWordAsInput, encodeCodeSymbolAsInput,
    DovetailInitialLayoutInitializer.tapeAtCells, Tape.input]

theorem selectedMergePaddedEmitterHeaderRewriter_haltsFromPayload
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterHeaderRewriterDescription.HaltsFromTape
      (SimulatorLayout.tape p.S)
      (SelectedMergePaddedEmitterAfterHeaderTape p) := by
  rw [SelectedMergeEmitterInputTape_eq_headerTailCells p]
  simp [SelectedMergePaddedEmitterAfterHeaderTape]
  exact
    selectedMergePaddedEmitterHeaderRewriter_haltsFromTape
      [] ((SelectedMergePaddedEmitterOuterTailBits p).map some)

def SelectedMergePaddedEmitterOutputTailBits
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) : Word Bool :=
  encodeCodeWordAsInput
    (encodeBoolWordAppend p.L.input
      (encodeNatAppend p.L.stage
        (encodeConfigurationAppend
          (SelectedMergeOutputAcceptConfig useAccept p.S p.L)
          (encodeConfigurationAppend
            (SelectedMergeOutputRejectConfig useAccept p.S p.L)
            (encodeBoolAppend
              (SelectedMergeOutputAcceptHit useAccept p.S p.L)
              (encodeBoolAppend
                (SelectedMergeOutputRejectHit useAccept p.S p.L) []))))))

theorem SelectedMergeEquivEmitterPaddedOutputTape_eq_transitionTailCells
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    SelectedMergeEquivEmitterPaddedOutputTape useAccept p =
      DovetailInitialLayoutInitializer.tapeAtCells []
        (inputWithTrailingBlankPaddingCells
          (List.append
            (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
            (SelectedMergePaddedEmitterOutputTailBits useAccept p))
          (SimulatorLayout.asBoolInput p.S).length) := by
  rw [SelectedMergeEquivEmitterPaddedOutputTape_eq_tapeAtCells_fields]
  simp [SelectedMergePaddedEmitterOutputTailBits, encodeCodeWordAsInput,
    encodeCodeSymbolAsInput]

def SelectedMergePaddedEmitterAfterHeaderSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      emitter.HaltsFromTape
        (SelectedMergePaddedEmitterAfterHeaderTape p)
        (SelectedMergeEquivEmitterPaddedOutputTape useAccept p)

def SelectedMergePaddedEmitterInputScannerDescription :
    MachineDescription :=
  CanonicalLayouts.DovetailLayoutScanner.CellListSuffixScannerDescription

theorem selectedMergePaddedEmitterInputScanner_subroutineReady :
    SelectedMergePaddedEmitterInputScannerDescription.SubroutineReady := by
  simpa [SelectedMergePaddedEmitterInputScannerDescription] using
    CanonicalLayouts.DovetailLayoutScanner.cellListSuffixScannerDescription_subroutineReady

def SelectedMergePaddedEmitterAfterInputTape
  (p : SelectedMergeEmitterPayload) : Tape Bool :=
  (CanonicalLayouts.DovetailLayoutScanner.boolWordCanonicalHandoffConfigWithBase
      (ParsedLayoutBits p.L)
      (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse)
      (SelectedMergePaddedEmitterOuterSuffixBits p)).tape

def SelectedMergePaddedEmitterAfterInputHandoffTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells
    (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
        ((ParsedLayoutBits p.L).map some)
        (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse))
    ((SelectedMergePaddedEmitterOuterSuffixBits p).map some)

theorem selectedMergePaddedEmitterAfterInputTape_move_right
    (p : SelectedMergeEmitterPayload) :
    Tape.move Direction.right
        (SelectedMergePaddedEmitterAfterInputTape p) =
      SelectedMergePaddedEmitterAfterInputHandoffTape p := by
  rcases SelectedMergePaddedEmitterOuterSuffixBits_cons_false p with
    ⟨suffixTail, hsuffix⟩
  rw [SelectedMergePaddedEmitterAfterInputTape,
    SelectedMergePaddedEmitterAfterInputHandoffTape, hsuffix]
  simpa [CanonicalLayouts.DovetailLayoutScanner.boolWordCanonicalHandoffConfigWithBase] using
    CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalHandoffConfigWithBase_move_right
        ((ParsedLayoutBits p.L).map some)
        (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse)
        false suffixTail

def SelectedMergePaddedEmitterAfterInputHandoffSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      emitter.HaltsFromTape
        (SelectedMergePaddedEmitterAfterInputHandoffTape p)
        (SelectedMergeEquivEmitterPaddedOutputTape useAccept p)

def SelectedMergePaddedEmitterStageScannerDescription :
    MachineDescription :=
  CanonicalLayouts.DovetailStagePrefix.NonemptyNatSuffixScannerDescription

theorem selectedMergePaddedEmitterStageScanner_subroutineReady :
    SelectedMergePaddedEmitterStageScannerDescription.SubroutineReady := by
  simpa [SelectedMergePaddedEmitterStageScannerDescription] using
    CanonicalLayouts.DovetailStagePrefix.nonemptyNatSuffixScannerDescription_subroutineReady

def SelectedMergePaddedEmitterAfterStageTape
  (p : SelectedMergeEmitterPayload) : Tape Bool :=
  (CanonicalLayouts.DovetailStagePrefix.nonemptyNatSuffixHandoffConfigWithBase
      p.S.stage
      (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
        ((ParsedLayoutBits p.L).map some)
        (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse))
      (SelectedMergePaddedEmitterOuterStageSuffixBits p)).tape

def SelectedMergePaddedEmitterAfterStageHandoffTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells
    (List.append
      ((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          p.S.stage).reverse.map some)
      (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
        ((ParsedLayoutBits p.L).map some)
        (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse)))
    ((SelectedMergePaddedEmitterOuterStageSuffixBits p).map some)

theorem selectedMergePaddedEmitterAfterStageTape_move_right
    (p : SelectedMergeEmitterPayload) :
    Tape.move Direction.right
        (SelectedMergePaddedEmitterAfterStageTape p) =
      SelectedMergePaddedEmitterAfterStageHandoffTape p := by
  rcases SelectedMergePaddedEmitterOuterStageSuffixBits_cons_false p with
    ⟨suffixTail, hsuffix⟩
  rw [SelectedMergePaddedEmitterAfterStageTape,
    SelectedMergePaddedEmitterAfterStageHandoffTape, hsuffix]
  simpa using
    CanonicalLayouts.DovetailStagePrefix.nonemptyNatSuffixHandoffConfigWithBase_move_right
        p.S.stage
        (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
          ((ParsedLayoutBits p.L).map some)
          (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse))
        false suffixTail

def SelectedMergePaddedEmitterAfterStageHandoffSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      emitter.HaltsFromTape
        (SelectedMergePaddedEmitterAfterStageHandoffTape p)
        (SelectedMergeEquivEmitterPaddedOutputTape useAccept p)

def SelectedMergePaddedEmitterConfigScannerDescription :
    MachineDescription :=
  CanonicalLayouts.DovetailLayoutScanner.ConfigurationSuffixScannerDescription

theorem selectedMergePaddedEmitterConfigScanner_subroutineReady :
    SelectedMergePaddedEmitterConfigScannerDescription.SubroutineReady := by
  simpa [SelectedMergePaddedEmitterConfigScannerDescription] using
    CanonicalLayouts.DovetailLayoutScanner.configurationSuffixScannerDescription_subroutineReady

def SelectedMergePaddedEmitterAfterConfigTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalHandoffConfigWithBase
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
              (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse))))))
    (SelectedMergePaddedEmitterOuterHitSuffixBits p)).tape

def SelectedMergePaddedEmitterAfterConfigHandoffTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells
    (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
      p.S.config
      (List.append
        ((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          p.S.stage).reverse.map some)
        (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
          ((ParsedLayoutBits p.L).map some)
          (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse))))
    ((SelectedMergePaddedEmitterOuterHitSuffixBits p).map some)

theorem selectedMergePaddedEmitterConfigScanner_haltsFromAfterStageHandoff
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterConfigScannerDescription.HaltsFromTape
      (SelectedMergePaddedEmitterAfterStageHandoffTape p)
      (SelectedMergePaddedEmitterAfterConfigTape p) := by
  rcases SelectedMergePaddedEmitterOuterHitSuffixBits_cons_false p with
    ⟨suffixTail, hsuffix⟩
  rcases
      CanonicalLayouts.DovetailLayoutScanner.run_configurationSuffix_raw_to_handoff_withBase
        p.S.config
        (List.append
          ((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            p.S.stage).reverse.map some)
          (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
            ((ParsedLayoutBits p.L).map some)
            (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse)))
        suffixTail with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [MachineDescription.HaltsFromTapeIn,
      SelectedMergePaddedEmitterConfigScannerDescription,
      SelectedMergePaddedEmitterAfterStageHandoffTape,
      SelectedMergePaddedEmitterOuterStageSuffixBits_eq_configurationFieldBits,
      hsuffix,
      DovetailInitialLayoutInitializer.config]
      using congrArg MachineDescription.Configuration.state hsteps
  · simpa [MachineDescription.HaltsFromTapeIn,
      SelectedMergePaddedEmitterConfigScannerDescription,
      SelectedMergePaddedEmitterAfterStageHandoffTape,
      SelectedMergePaddedEmitterAfterConfigTape,
      SelectedMergePaddedEmitterOuterStageSuffixBits_eq_configurationFieldBits,
      hsuffix,
      DovetailInitialLayoutInitializer.config]
      using congrArg MachineDescription.Configuration.tape hsteps

theorem selectedMergePaddedEmitterAfterConfigTape_move_right
    (p : SelectedMergeEmitterPayload) :
    Tape.move Direction.right
        (SelectedMergePaddedEmitterAfterConfigTape p) =
      SelectedMergePaddedEmitterAfterConfigHandoffTape p := by
  rcases SelectedMergePaddedEmitterOuterHitSuffixBits_cons_false p with
    ⟨suffixTail, hsuffix⟩
  rw [SelectedMergePaddedEmitterAfterConfigTape,
    SelectedMergePaddedEmitterAfterConfigHandoffTape, hsuffix]
  have hmove :=
    CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalHandoffConfigWithBase_move_right
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
                  (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse))))))
        false suffixTail
  simpa [CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase,
    List.append_assoc] using hmove

def SelectedMergePaddedEmitterAfterConfigHandoffSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      emitter.HaltsFromTape
        (SelectedMergePaddedEmitterAfterConfigHandoffTape p)
        (SelectedMergeEquivEmitterPaddedOutputTape useAccept p)

def SelectedMergePaddedEmitterHitScannerDescription :
    MachineDescription where
  stateCount := 6
  start := 0
  halt := 5
  transitions :=
    [ MachineDescription.transition 0 (some false) (some false)
        Direction.right 1,
      MachineDescription.transition 1 (some true) (some true)
        Direction.right 2,
      MachineDescription.transition 2 (some false) (some false)
        Direction.right 3,
      MachineDescription.transition 2 (some true) (some true)
        Direction.right 4,
      MachineDescription.transition 3 (some true) (some true)
        Direction.right 5,
      MachineDescription.transition 4 (some false) (some false)
        Direction.right 5 ]

theorem selectedMergePaddedEmitterHitScanner_subroutineReady :
    SelectedMergePaddedEmitterHitScannerDescription.SubroutineReady := by
  constructor
  · constructor
    · decide
    constructor
    · decide
    constructor
    · decide
    constructor
    · intro t ht
      simp [SelectedMergePaddedEmitterHitScannerDescription,
        MachineDescription.transition,
        TransitionDescription.WellFormed] at ht ⊢
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
    · intro t u ht hu hkey
      simp [SelectedMergePaddedEmitterHitScannerDescription,
        MachineDescription.transition] at ht hu
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [TransitionDescription.SameKey,
            TransitionDescription.SameAction] at hkey ⊢
  · intro t ht
    simp [SelectedMergePaddedEmitterHitScannerDescription,
      MachineDescription.transition] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem selectedMergePaddedEmitterHitScanner_runConfig
    (b : Bool) (left : List (Option Bool)) :
    SelectedMergePaddedEmitterHitScannerDescription.runConfig 4
        (DovetailInitialLayoutInitializer.config 0 left
          ((encodeCodeWordAsInput (encodeBoolAppend b [])).map some)) =
      DovetailInitialLayoutInitializer.config 5
        (((encodeCodeWordAsInput (encodeBoolAppend b [])).reverse.map some) ++
          left)
        [] := by
  cases b <;>
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

def SelectedMergePaddedEmitterAfterHitTape
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
            (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse)))))
    []

theorem
    selectedMergePaddedEmitter_cellListCanonicalRestoredLeftWithBase_reverse_filterMap
    (cells baseLeft : List (Option Bool)) :
    (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
        cells baseLeft).reverse.filterMap (fun cell => cell) =
      List.append (baseLeft.reverse.filterMap (fun cell => cell))
        (CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits cells []) := by
  rw [←
    CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredBitsRev_map_some_withBase
      cells baseLeft]
  simp [Function.comp_def, List.reverse_append, List.filterMap_append,
    CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredBitsRev_reverse]

def SelectedMergePaddedEmitterAfterHitSourceBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  List.append
    (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
    (CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits
      (ParsedLayoutBits p.L)
      (List.append
        (FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          p.S.stage)
        (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
          p.S.config
          (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            p.S.hit []))))

theorem SelectedMergePaddedEmitterAfterHitTape_normalizedOutput
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput (SelectedMergePaddedEmitterAfterHitTape p) =
      SelectedMergePaddedEmitterAfterHitSourceBits p := by
  have hbase :
      (List.append
          ((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            p.S.stage).reverse.map some)
          (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
            ((ParsedLayoutBits p.L).map some)
            (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse))).reverse.filterMap
            (fun cell => cell) =
        List.append
          (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
          (CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits
            (ParsedLayoutBits p.L)
            (FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              p.S.stage)) := by
    have hreverse :
        List.filterMap (fun cell => cell)
            (((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                p.S.stage).reverse.map some).append
              (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
                ((ParsedLayoutBits p.L).map some)
                (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse))).reverse =
          List.append
            (List.filterMap (fun cell => cell)
              (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
                ((ParsedLayoutBits p.L).map some)
                (((encodeCodeSymbolAsInput MachineCodeSymbol.transition).map some).reverse)).reverse)
            (List.filterMap (fun cell => cell)
              (((FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                p.S.stage).reverse.map some).reverse)) := by
      simp [List.reverse_append, List.filterMap_append]
    rw [hreverse]
    rw [selectedMergePaddedEmitter_cellListCanonicalRestoredLeftWithBase_reverse_filterMap]
    simp [CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits,
      Function.comp_def, List.append_assoc]
  rw [SelectedMergePaddedEmitterAfterHitTape,
    tapeAtCells_nil_normalizedOutput]
  rw [List.reverse_append, List.filterMap_append]
  rw [dovetailScanner_configurationRestoredLeftWithBase_reverse_filterMap]
  rw [hbase]
  simp [SelectedMergePaddedEmitterAfterHitSourceBits,
    SelectedMergePaddedEmitterOuterHitSuffixBits,
    SelectedMergePaddedEmitterOuterHitSuffixCode,
    CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.tapeFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.boolBits_eq_encodeBoolAppend,
    encodeCodeWordAsInput, Function.comp_def, List.map_reverse,
    List.append_assoc]


end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
