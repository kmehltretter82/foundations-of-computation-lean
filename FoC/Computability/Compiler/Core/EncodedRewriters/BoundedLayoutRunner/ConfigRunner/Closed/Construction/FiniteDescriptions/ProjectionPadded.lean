import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.FiniteDescriptions.Base

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace BoundedLayoutRunner

def SelectedProjectionEquivEmitterPaddedOutputTape
    (useAccept : Bool)
    (L : MachineDescription.DovetailLayout) : Tape Bool :=
  Tape.move Direction.right
    (inputWithTrailingBlankPadding
      (MachineDescription.encodeCodeWordAsInput
        (SelectedProjectionOutputCode useAccept L))
      (ParsedLayoutBits L).length)

theorem SelectedProjectionEquivEmitterPaddedOutputTape_equiv
    (useAccept : Bool) (L : MachineDescription.DovetailLayout) :
    Tape.Equiv
      (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L)
      (SelectedProjectionOutputTape useAccept L) := by
  simpa [SelectedProjectionEquivEmitterPaddedOutputTape,
    SelectedProjectionOutputTape] using
    Tape.Equiv.move
      (inputWithTrailingBlankPadding_equiv_input
        (MachineDescription.encodeCodeWordAsInput
          (SelectedProjectionOutputCode useAccept L))
        (ParsedLayoutBits L).length)
      Direction.right

theorem SelectedProjectionEquivEmitterPaddedOutputTape_normalizedOutput
    (useAccept : Bool) (L : MachineDescription.DovetailLayout) :
    Tape.normalizedOutput
        (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L) =
      MachineDescription.encodeCodeWordAsInput
        (SelectedProjectionOutputCode useAccept L) := by
  simpa [SelectedProjectionEquivEmitterPaddedOutputTape] using
    inputWithTrailingBlankPadding_move_right_normalizedOutput
      (MachineDescription.encodeCodeWordAsInput
        (SelectedProjectionOutputCode useAccept L))
      (ParsedLayoutBits L).length

theorem SelectedProjectionEquivEmitterPaddedOutputTape_normalizedOutput_eq_tail
    (useAccept : Bool) (L : MachineDescription.DovetailLayout) :
    Tape.normalizedOutput
        (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L) =
      SelectedProjectionTailProjector.outputAllBits useAccept L := by
  rw [SelectedProjectionEquivEmitterPaddedOutputTape_normalizedOutput,
    selectedProjectionOutputBits_eq_tailProjector_outputAllBits]

theorem tapeAtCells_nil_normalizedOutput
    (leftRev : List (Option Bool)) :
    Tape.normalizedOutput
        (DovetailInitialLayoutInitializer.tapeAtCells leftRev []) =
      leftRev.reverse.filterMap (fun cell => cell) := by
  simp [DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.normalizedOutput, Tape.cells]

theorem dovetailScanner_configurationRestoredLeftWithBase_reverse_filterMap
    (cfg : MachineDescription.Configuration)
    (baseLeft : List (Option Bool)) :
    (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
        cfg baseLeft).reverse.filterMap (fun cell => cell) =
      List.append (baseLeft.reverse.filterMap (fun cell => cell))
        (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
          cfg []) := by
  rw [←
    CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev_map_some_withBase
      cfg baseLeft]
  simp [Function.comp_def, List.reverse_append, List.filterMap_append,
    CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev_reverse]

theorem dovetailScanner_finalHitFlagsRestoredLeftWithBase_reverse_filterMap
    (acceptHit rejectHit : Bool)
    (baseLeft : List (Option Bool)) :
    (CanonicalLayouts.DovetailLayoutScanner.finalHitFlagsRestoredLeftWithBase
        acceptHit rejectHit baseLeft).reverse.filterMap (fun cell => cell) =
      List.append (baseLeft.reverse.filterMap (fun cell => cell))
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits acceptHit
          (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            rejectHit [])) := by
  simp [CanonicalLayouts.DovetailLayoutScanner.finalHitFlagsRestoredLeftWithBase,
    CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
    Function.comp_def, List.reverse_append, List.filterMap_append,
    List.append_assoc]

theorem SelectedProjectionEquivEmitterPaddedOutputTape_contextLength_ge_input
    (useAccept : Bool) (L : MachineDescription.DovetailLayout) :
    Tape.contextLength (Tape.input (ParsedLayoutBits L)) <=
      Tape.contextLength
        (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L) := by
  have hpad :=
    inputWithTrailingBlankPadding_contextLength_ge_input
      (MachineDescription.encodeCodeWordAsInput
        (SelectedProjectionOutputCode useAccept L))
      (ParsedLayoutBits L)
  have hmove :=
    tape_contextLength_le_move_right
      (inputWithTrailingBlankPadding
        (MachineDescription.encodeCodeWordAsInput
          (SelectedProjectionOutputCode useAccept L))
        (ParsedLayoutBits L).length)
  exact Nat.le_trans hpad hmove

namespace SelectedProjectionTailProjector

theorem parsedLayoutCheckedTape_normalizedOutput_eq_transition_stageInput_sourceRestSuffix
    (L : MachineDescription.DovetailLayout) :
    Tape.normalizedOutput (ParsedLayoutCheckedTape L) =
      List.append
        (MachineDescription.encodeCodeSymbolAsInput
          MachineCodeSymbol.transition)
        (List.append
          (DovetailInitialLayoutInitializer.stageInputBits
            L.input L.stage)
          (MachineDescription.encodeCodeWordAsInput
            (sourceRestSuffix L))) := by
  rw [parsedLayoutCheckedTape_normalizedOutput,
    parsedLayoutBits_eq_transition_stageInput_sourceRestSuffix]

theorem parsedLayoutCheckedTape_normalizedOutput_eq_transition_stageInput_sourceRestFieldBits
    (L : MachineDescription.DovetailLayout) :
    Tape.normalizedOutput (ParsedLayoutCheckedTape L) =
      List.append
        (MachineDescription.encodeCodeSymbolAsInput
          MachineCodeSymbol.transition)
        (List.append
          (DovetailInitialLayoutInitializer.stageInputBits
            L.input L.stage)
          (sourceRestFieldBits L)) := by
  rw [parsedLayoutCheckedTape_normalizedOutput,
    parsedLayoutBits_eq_transition_stageInput_sourceRestFieldBits]

theorem parsedLayoutCheckedTape_eq_transition_stageInput_sourceRestSuffix
    (L : MachineDescription.DovetailLayout) :
    ParsedLayoutCheckedTape L =
      DovetailInitialLayoutInitializer.tapeAtCells []
        (List.append
          ((List.append
            (MachineDescription.encodeCodeSymbolAsInput
              MachineCodeSymbol.transition)
            (List.append
              (DovetailInitialLayoutInitializer.stageInputBits
                L.input L.stage)
              (MachineDescription.encodeCodeWordAsInput
                (sourceRestSuffix L)))).map some)
          [none]) := by
  rw [ParsedLayoutCheckedTape,
    parsedLayoutBits_eq_transition_stageInput_sourceRestSuffix]
  simp [checkedInputTape, DovetailInitialLayoutInitializer.tapeAtCells,
    MachineDescription.encodeCodeSymbolAsInput, List.map_append,
    List.append_assoc]

theorem parsedLayoutCheckedTape_eq_transition_stageInput_sourceRestFieldBits
    (L : MachineDescription.DovetailLayout) :
    ParsedLayoutCheckedTape L =
      DovetailInitialLayoutInitializer.tapeAtCells []
        (List.append
          ((List.append
            (MachineDescription.encodeCodeSymbolAsInput
              MachineCodeSymbol.transition)
            (List.append
              (DovetailInitialLayoutInitializer.stageInputBits
                L.input L.stage)
              (sourceRestFieldBits L))).map some)
          [none]) := by
  rw [ParsedLayoutCheckedTape,
    parsedLayoutBits_eq_transition_stageInput_sourceRestFieldBits]
  simp [checkedInputTape, DovetailInitialLayoutInitializer.tapeAtCells,
    MachineDescription.encodeCodeSymbolAsInput, List.map_append,
    List.append_assoc]

theorem parsedLayoutCheckedHandoffTape_eq_transition_stageInput_sourceRestSuffix
    (L : MachineDescription.DovetailLayout) :
    ParsedLayoutCheckedHandoffTape L =
      DovetailInitialLayoutInitializer.tapeAtCells [some false]
        (List.append [some false, some false, some true]
          (List.append
            ((List.append
              (DovetailInitialLayoutInitializer.stageInputBits
                L.input L.stage)
              (MachineDescription.encodeCodeWordAsInput
                (sourceRestSuffix L))).map some)
            [none])) := by
  rw [ParsedLayoutCheckedHandoffTape,
    parsedLayoutCheckedTape_eq_transition_stageInput_sourceRestSuffix]
  simp [DovetailInitialLayoutInitializer.tapeAtCells,
    MachineDescription.encodeCodeSymbolAsInput, Tape.move, Tape.moveRight,
    List.map_append, List.append_assoc]

theorem parsedLayoutCheckedHandoffTape_eq_transition_stageInput_sourceRestFieldBits
    (L : MachineDescription.DovetailLayout) :
    ParsedLayoutCheckedHandoffTape L =
      DovetailInitialLayoutInitializer.tapeAtCells [some false]
        (List.append [some false, some false, some true]
          (List.append
            ((List.append
              (DovetailInitialLayoutInitializer.stageInputBits
                L.input L.stage)
              (sourceRestFieldBits L)).map some)
            [none])) := by
  rw [ParsedLayoutCheckedHandoffTape,
    parsedLayoutCheckedTape_eq_transition_stageInput_sourceRestFieldBits]
  simp [DovetailInitialLayoutInitializer.tapeAtCells,
    MachineDescription.encodeCodeSymbolAsInput, Tape.move, Tape.moveRight,
    List.map_append, List.append_assoc]

theorem sourceFieldBits_length_le_parsedLayoutBits
    (L : MachineDescription.DovetailLayout) :
    (sourceFieldBits L).length <= (ParsedLayoutBits L).length := by
  rw [← sourceSuffix_bits_eq_fields]
  rw [ParsedLayoutBits,
    dovetailLayout_encode_eq_transition_input_sourceSuffix]
  have happend :
      MachineDescription.encodeBoolWordAppend L.input
          (sourceSuffix L) =
        List.append
          (MachineDescription.encodeBoolWordAppend L.input [])
          (sourceSuffix L) := by
    simpa using
      encodeBoolWordAppend_append L.input ([] : Word MachineCodeSymbol)
        (sourceSuffix L)
  rw [happend]
  change List.length
        (MachineDescription.encodeCodeWordAsInput
          (sourceSuffix L)) <=
      List.length
        (MachineDescription.encodeCodeWordAsInput
          (List.append
            (MachineCodeSymbol.transition ::
              MachineDescription.encodeBoolWordAppend L.input [])
            (sourceSuffix L)))
  rw [MachineDescription.encodeCodeWordAsInput_append]
  simp [MachineDescription.encodeCodeWordAsInput]
  omega

theorem outputPrefixBits_length_ge_parsedLayoutBits
    (L : MachineDescription.DovetailLayout) :
    (ParsedLayoutBits L).length <= (outputPrefixBits L).length := by
  have hquote :
      (ParsedLayoutBits L).length <=
        (MachineDescription.encodeBoolWordAppend
          (ParsedLayoutBits L) []).length := by
    simpa using
      encodeBoolWordAppend_length_ge (ParsedLayoutBits L)
        ([] : Word MachineCodeSymbol)
  have hencoded :
      (MachineDescription.encodeBoolWordAppend
          (ParsedLayoutBits L) []).length <=
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeBoolWordAppend
            (ParsedLayoutBits L) [])).length := by
    rw [encodeCodeWordAsInput_length]
    omega
  have hprefix :
      (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeBoolWordAppend
            (ParsedLayoutBits L) [])).length <=
        (outputPrefixBits L).length := by
    simp [outputPrefixBits, List.length_append]
  exact Nat.le_trans hquote (Nat.le_trans hencoded hprefix)

theorem sourceTape_contextLength_ge_parsedLayoutCheckedTape
    (L : MachineDescription.DovetailLayout) :
    Tape.contextLength (ParsedLayoutCheckedTape L) <=
      Tape.contextLength
        (sourceTape L ((outputPrefixBits L).reverse.map some)) := by
  have hinput :
      Tape.contextLength (ParsedLayoutCheckedTape L) =
        (ParsedLayoutBits L).length := by
    rcases parsedLayoutBits_eq_false_false_tail L with ⟨tail, htail⟩
    simp [ParsedLayoutCheckedTape, checkedInputTape, htail,
      Tape.contextLength]
  have hprefix := outputPrefixBits_length_ge_parsedLayoutBits L
  have htarget :
      (outputPrefixBits L).length <=
        Tape.contextLength
          (sourceTape L ((outputPrefixBits L).reverse.map some)) := by
    rcases stageNatBits_cons_cons L.stage with
      ⟨first, second, rest, hstage⟩
    rw [sourceTape, sourceFieldBits, hstage]
    simp [DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.contextLength, List.length_append]
  rw [hinput]
  exact Nat.le_trans hprefix htarget

theorem sourceTape_normalizedOutput
    (L : MachineDescription.DovetailLayout)
    (baseLeft : List (Option Bool)) :
    Tape.normalizedOutput (sourceTape L baseLeft) =
      List.append (baseLeft.reverse.filterMap (fun cell => cell))
        (sourceFieldBits L) := by
  rcases stageNatBits_cons_cons L.stage with
    ⟨first, second, rest, hstage⟩
  rw [sourceTape, sourceFieldBits, hstage]
  simp [DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.normalizedOutput, Tape.cells, Function.comp_def,
    List.filterMap_append]

theorem sourceTape_normalizedOutput_outputPrefix
    (L : MachineDescription.DovetailLayout) :
    Tape.normalizedOutput
        (sourceTape L ((outputPrefixBits L).reverse.map some)) =
      List.append (outputPrefixBits L) (sourceFieldBits L) := by
  rw [sourceTape_normalizedOutput]
  simp [Function.comp_def, List.map_reverse]

theorem sourceTape_outputPrefix_eq_stageInputSourceRestFieldBits
    (L : MachineDescription.DovetailLayout) :
    sourceTape L ((outputPrefixBits L).reverse.map some) =
      DovetailInitialLayoutInitializer.tapeAtCells
        ((outputPrefixStageInputSourceRestFieldBits L).reverse.map some)
        ((List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage)
          (sourceRestFieldBits L)).map some) := by
  rw [sourceTape, outputPrefixBits_eq_stageInputSourceRestFieldBits,
    sourceFieldBits_eq_stageNatBits_sourceRestFieldBits]

theorem outputPrefixBits_append_sourceFieldBits
    (L : MachineDescription.DovetailLayout) :
    List.append (outputPrefixBits L) (sourceFieldBits L) =
      MachineDescription.encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          MachineDescription.encodeBoolWordAppend
            (ParsedLayoutBits L) (sourceSuffix L)) := by
  have happend :
      MachineDescription.encodeBoolWordAppend
          (ParsedLayoutBits L) (sourceSuffix L) =
        List.append
          (MachineDescription.encodeBoolWordAppend
            (ParsedLayoutBits L) [])
          (sourceSuffix L) := by
    simpa using
      encodeBoolWordAppend_append (ParsedLayoutBits L)
        ([] : Word MachineCodeSymbol) (sourceSuffix L)
  rw [outputPrefixBits, ← sourceSuffix_bits_eq_fields L, happend]
  simp only [MachineDescription.encodeCodeWordAsInput]
  rw [MachineDescription.encodeCodeWordAsInput_append]
  simp [List.append_assoc]

theorem sourceTape_normalizedOutput_outputPrefix_eq_header_input_sourceSuffix
    (L : MachineDescription.DovetailLayout) :
    Tape.normalizedOutput
        (sourceTape L ((outputPrefixBits L).reverse.map some)) =
      MachineDescription.encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          MachineDescription.encodeBoolWordAppend
            (ParsedLayoutBits L) (sourceSuffix L)) := by
  rw [sourceTape_normalizedOutput_outputPrefix,
    outputPrefixBits_append_sourceFieldBits]

theorem sourceTape_normalizedOutput_outputPrefix_eq_quoter_bits
    (L : MachineDescription.DovetailLayout) :
    exists b : Bool,
    exists rest : Word Bool,
      ParsedLayoutBits L = b :: rest ∧
        Tape.normalizedOutput
            (sourceTape L ((outputPrefixBits L).reverse.map some)) =
          List.append
            (MachineDescription.encodeCodeSymbolAsInput
              MachineCodeSymbol.header)
            (CommonGround.BoolWordQuoters.checkedNonemptyBoolWordQuoteDirectSourceBits
              b rest (sourceSuffix L)) := by
  rcases parsedLayoutBits_eq_false_false_tail L with ⟨tail, htail⟩
  refine ⟨false, false :: tail, htail, ?_⟩
  rw [sourceTape_normalizedOutput_outputPrefix_eq_header_input_sourceSuffix,
    htail]
  simp [MachineDescription.encodeCodeWordAsInput,
    CommonGround.BoolWordQuoters.checkedNonemptyBoolWordQuoteDirectSourceBits_eq]

theorem sourceScannerRightHandoffTape_normalizedOutput
    (L : MachineDescription.DovetailLayout)
    (baseLeft : List (Option Bool)) :
    Tape.normalizedOutput
        (sourceScannerRightHandoffTape L baseLeft) =
      List.append (baseLeft.reverse.filterMap (fun cell => cell))
        (sourceFieldBits L) := by
  rw [sourceScannerRightHandoffTape_eq]
  rw [tapeAtCells_nil_normalizedOutput]
  rw [dovetailScanner_finalHitFlagsRestoredLeftWithBase_reverse_filterMap]
  rw [dovetailScanner_configurationRestoredLeftWithBase_reverse_filterMap]
  rw [dovetailScanner_configurationRestoredLeftWithBase_reverse_filterMap]
  simp [sourceFieldBits, Function.comp_def, List.reverse_append,
    List.filterMap_append, List.map_reverse, List.append_assoc,
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.tapeFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.boolFieldBits]

theorem sourceScannerRightHandoffTape_normalizedOutput_eq_sourceTape
    (L : MachineDescription.DovetailLayout)
    (baseLeft : List (Option Bool)) :
    Tape.normalizedOutput
        (sourceScannerRightHandoffTape L baseLeft) =
      Tape.normalizedOutput (sourceTape L baseLeft) := by
  rw [sourceScannerRightHandoffTape_normalizedOutput,
    sourceTape_normalizedOutput]

theorem sourceScannerRightHandoffTape_normalizedOutput_outputPrefix
    (L : MachineDescription.DovetailLayout) :
    Tape.normalizedOutput
        (sourceScannerRightHandoffTape L
          ((outputPrefixBits L).reverse.map some)) =
      List.append (outputPrefixBits L) (sourceFieldBits L) := by
  rw [sourceScannerRightHandoffTape_normalizedOutput]
  simp [Function.comp_def, List.map_reverse]

theorem
    sourceScannerRightHandoffTape_normalizedOutput_outputPrefix_eq_header_input_sourceSuffix
    (L : MachineDescription.DovetailLayout) :
    Tape.normalizedOutput
        (sourceScannerRightHandoffTape L
          ((outputPrefixBits L).reverse.map some)) =
      MachineDescription.encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          MachineDescription.encodeBoolWordAppend
            (ParsedLayoutBits L) (sourceSuffix L)) := by
  rw [sourceScannerRightHandoffTape_normalizedOutput_outputPrefix,
    outputPrefixBits_append_sourceFieldBits]

theorem
    sourceScannerRightHandoffTape_normalizedOutput_outputPrefix_eq_quoter_bits
    (L : MachineDescription.DovetailLayout) :
    exists b : Bool,
    exists rest : Word Bool,
      ParsedLayoutBits L = b :: rest ∧
        Tape.normalizedOutput
          (sourceScannerRightHandoffTape L
            ((outputPrefixBits L).reverse.map some)) =
          List.append
            (MachineDescription.encodeCodeSymbolAsInput
              MachineCodeSymbol.header)
            (CommonGround.BoolWordQuoters.checkedNonemptyBoolWordQuoteDirectSourceBits
              b rest (sourceSuffix L)) := by
  rcases parsedLayoutBits_eq_false_false_tail L with ⟨tail, htail⟩
  refine ⟨false, false :: tail, htail, ?_⟩
  rw [
    sourceScannerRightHandoffTape_normalizedOutput_outputPrefix_eq_header_input_sourceSuffix,
    htail]
  simp [MachineDescription.encodeCodeWordAsInput,
    CommonGround.BoolWordQuoters.checkedNonemptyBoolWordQuoteDirectSourceBits_eq]

theorem sourceScannerRightHandoffTape_contextLength_ge_sourceTape
    (L : MachineDescription.DovetailLayout)
    (baseLeft : List (Option Bool)) :
    Tape.contextLength (sourceTape L baseLeft) <=
      Tape.contextLength (sourceScannerRightHandoffTape L baseLeft) := by
  rcases sourceScanner_haltsFromTape_withBase L baseLeft with
    ⟨steps, hsteps⟩
  let scanner :=
    CanonicalLayouts.DovetailLayoutScanner.StageConfigurationsAndFinalFlagsScannerDescription
  have hmono :=
    MachineDescription.runConfig_contextLength_mono
      scanner steps
      { state := scanner.start
        tape := sourceTape L baseLeft }
  have hhandoff :
      Tape.contextLength
          ((scanner.runConfig steps
            { state := scanner.start
              tape := sourceTape L baseLeft }).tape) =
        Tape.contextLength (sourceScannerHandoffTape L baseLeft) :=
    congrArg Tape.contextLength hsteps.right
  rw [hhandoff] at hmono
  have hmove := tape_contextLength_le_move_right
    (sourceScannerHandoffTape L baseLeft)
  exact Nat.le_trans hmono
    (by simpa [sourceScannerRightHandoffTape] using hmove)

end SelectedProjectionTailProjector

theorem SelectedProjectionEquivEmitterPaddedOutputTape_contextLength_ge_source
    (useAccept : Bool) (L : MachineDescription.DovetailLayout) :
    Tape.contextLength
        (SelectedProjectionTailProjector.sourceTape L
          ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
            some)) <=
      Tape.contextLength
        (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L) := by
  have hsourceLen :=
    SelectedProjectionTailProjector.sourceFieldBits_length_le_parsedLayoutBits
      L
  have hsource :
      Tape.contextLength
          (SelectedProjectionTailProjector.sourceTape L
            ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
              some)) <=
        (SelectedProjectionTailProjector.outputAllBits useAccept L).length +
          (ParsedLayoutBits L).length - 1 := by
    rcases SelectedProjectionTailProjector.stageNatBits_cons_cons L.stage with
      ⟨first, second, rest, hstage⟩
    cases useAccept <;>
      rw [SelectedProjectionTailProjector.sourceTape,
        SelectedProjectionTailProjector.sourceFieldBits,
        SelectedProjectionTailProjector.outputAllBits,
        SelectedProjectionTailProjector.outputPrefixBits,
        SelectedProjectionTailProjector.outputBits_eq_fields,
        SelectedProjectionTailProjector.outputFieldBits,
        hstage]
      <;> simp [SelectedProjectionTailProjector.sourceFieldBits,
        SelectedProjectionTailProjector.selectedConfig,
        SelectedProjectionTailProjector.selectedHit,
        DovetailInitialLayoutInitializer.tapeAtCells, Tape.contextLength,
        CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits,
        CanonicalLayouts.DovetailLayoutScanner.tapeFieldBits,
        CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits,
        CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
        CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
        List.length_append] at hsourceLen ⊢
      <;> omega
  have htarget :
      (SelectedProjectionTailProjector.outputAllBits useAccept L).length +
          (ParsedLayoutBits L).length - 1 <=
        Tape.contextLength
          (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L) := by
    simpa [SelectedProjectionEquivEmitterPaddedOutputTape,
      selectedProjectionOutputBits_eq_tailProjector_outputAllBits] using
      inputWithTrailingBlankPadding_move_right_contextLength_ge_pred
        (SelectedProjectionTailProjector.outputAllBits useAccept L)
        (ParsedLayoutBits L).length
  exact Nat.le_trans hsource htarget

theorem
    SelectedProjectionEquivEmitterPaddedOutputTape_contextLength_ge_checkedInput
    (useAccept : Bool) (L : MachineDescription.DovetailLayout) :
    Tape.contextLength (ParsedLayoutCheckedTape L) <=
      Tape.contextLength
        (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L) := by
  exact
    Nat.le_trans
      (SelectedProjectionTailProjector.sourceTape_contextLength_ge_parsedLayoutCheckedTape
        L)
      (SelectedProjectionEquivEmitterPaddedOutputTape_contextLength_ge_source
        useAccept L)

theorem dovetailScanner_cellListCanonicalRestoredLeftWithBase_length
    (cells baseLeft : List (Option Bool)) :
    (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
        cells baseLeft).length =
      (CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits cells []).length +
        baseLeft.length := by
  rw [←
    CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredBitsRev_map_some_withBase]
  simp [List.length_append]
  rw [← List.length_reverse]
  rw [CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredBitsRev_reverse]

theorem dovetailScanner_configurationRestoredLeftWithBase_length
    (cfg : MachineDescription.Configuration)
    (baseLeft : List (Option Bool)) :
    (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredLeftWithBase
        cfg baseLeft).length =
      (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits cfg []).length +
        baseLeft.length := by
  rw [←
    CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev_map_some_withBase]
  simp [List.length_append]
  rw [← List.length_reverse]
  rw [CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev_reverse]

theorem dovetailScanner_finalHitFlagsRestoredLeftWithBase_length
    (acceptHit rejectHit : Bool)
    (baseLeft : List (Option Bool)) :
    (CanonicalLayouts.DovetailLayoutScanner.finalHitFlagsRestoredLeftWithBase
        acceptHit rejectHit baseLeft).length =
      (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits acceptHit
          (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits rejectHit [])).length +
        baseLeft.length := by
  simp [CanonicalLayouts.DovetailLayoutScanner.finalHitFlagsRestoredLeftWithBase,
    CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
    List.length_append]
  omega

theorem
    SelectedProjectionEquivEmitterPaddedOutputTape_contextLength_ge_sourceScannerRightHandoff
    (useAccept : Bool) (L : MachineDescription.DovetailLayout) :
    Tape.contextLength
        (SelectedProjectionTailProjector.sourceScannerRightHandoffTape L
          ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
            some)) <=
      Tape.contextLength
        (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L) := by
  have hsourceLen :=
    SelectedProjectionTailProjector.sourceFieldBits_length_le_parsedLayoutBits
      L
  have hsourceSucc :
      Tape.contextLength
            (SelectedProjectionTailProjector.sourceScannerRightHandoffTape L
              ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
                some)) + 1 <=
        (SelectedProjectionTailProjector.outputAllBits useAccept L).length +
          (ParsedLayoutBits L).length := by
    rcases SelectedProjectionTailProjector.stageNatBits_cons_cons L.stage with
      ⟨first, second, rest, hstage⟩
    rw [SelectedProjectionTailProjector.sourceScannerRightHandoffTape_eq]
    cases useAccept <;>
      rw [SelectedProjectionTailProjector.outputAllBits,
        SelectedProjectionTailProjector.outputPrefixBits,
        SelectedProjectionTailProjector.outputBits_eq_fields,
        SelectedProjectionTailProjector.outputFieldBits,
        hstage]
      <;> simp [SelectedProjectionTailProjector.sourceFieldBits,
        SelectedProjectionTailProjector.selectedConfig,
        SelectedProjectionTailProjector.selectedHit,
        DovetailInitialLayoutInitializer.tapeAtCells, Tape.contextLength,
        dovetailScanner_configurationRestoredLeftWithBase_length,
        dovetailScanner_finalHitFlagsRestoredLeftWithBase_length,
        CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits,
        CanonicalLayouts.DovetailLayoutScanner.tapeFieldBits,
        CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits,
        CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
        CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
        hstage, List.length_append] at hsourceLen ⊢
      <;> omega
  have hsource :
      Tape.contextLength
          (SelectedProjectionTailProjector.sourceScannerRightHandoffTape L
            ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
              some)) <=
        (SelectedProjectionTailProjector.outputAllBits useAccept L).length +
          (ParsedLayoutBits L).length - 1 := by
    omega
  have htarget :
      (SelectedProjectionTailProjector.outputAllBits useAccept L).length +
          (ParsedLayoutBits L).length - 1 <=
        Tape.contextLength
          (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L) := by
    simpa [SelectedProjectionEquivEmitterPaddedOutputTape,
      selectedProjectionOutputBits_eq_tailProjector_outputAllBits] using
      inputWithTrailingBlankPadding_move_right_contextLength_ge_pred
        (SelectedProjectionTailProjector.outputAllBits useAccept L)
        (ParsedLayoutBits L).length
  exact Nat.le_trans hsource htarget

def SelectedProjectionEquivPaddedEmitterSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  ReadySpec emitter ∧
    forall L : MachineDescription.DovetailLayout,
      emitter.HaltsFromTape
        (Tape.input (ParsedLayoutBits L))
        (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L)

def SelectedProjectionEquivPaddedEmitterConstruction : Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedProjectionEquivPaddedEmitterSpec useAccept emitter

def SelectedProjectionCheckedEquivPaddedEmitterSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  ReadySpec emitter ∧
    forall L : MachineDescription.DovetailLayout,
      emitter.HaltsFromTape
        (ParsedLayoutCheckedTape L)
        (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L)

def SelectedProjectionCheckedEquivPaddedEmitterConstruction : Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedProjectionCheckedEquivPaddedEmitterSpec useAccept emitter

def SelectedProjectionPaddedTailEmitterSpec
    (useAccept : Bool)
    (tail : MachineDescription) : Prop :=
  ReadySpec tail ∧
    forall L : MachineDescription.DovetailLayout,
      tail.HaltsFromTape
        (SelectedProjectionTailProjector.sourceTape L
          ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
            some))
        (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L)

def SelectedProjectionPaddedTailEmitterConstruction : Prop :=
  forall useAccept : Bool,
    exists tail : MachineDescription,
      SelectedProjectionPaddedTailEmitterSpec useAccept tail

def SelectedProjectionPaddedTailCleanupSpec
    (useAccept : Bool)
    (cleanup : MachineDescription) : Prop :=
  ReadySpec cleanup ∧
    forall L : MachineDescription.DovetailLayout,
      cleanup.HaltsFromTape
        (SelectedProjectionTailProjector.sourceScannerRightHandoffTape L
          ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
            some))
        (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L)

def SelectedProjectionPaddedTailCleanupConstruction : Prop :=
  forall useAccept : Bool,
    exists cleanup : MachineDescription,
      SelectedProjectionPaddedTailCleanupSpec useAccept cleanup

def SelectedProjectionPaddedTailEmitterFromCleanup
    (_useAccept : Bool)
    (cleanup : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine
    CanonicalLayouts.DovetailLayoutScanner.StageConfigurationsAndFinalFlagsScannerDescription
    cleanup Direction.right

theorem selectedProjectionPaddedTailEmitterSpec_of_cleanup
    {useAccept : Bool} {cleanup : MachineDescription}
    (hcleanup : SelectedProjectionPaddedTailCleanupSpec useAccept cleanup) :
    SelectedProjectionPaddedTailEmitterSpec useAccept
      (SelectedProjectionPaddedTailEmitterFromCleanup useAccept
        cleanup) := by
  let baseLeft :=
    fun L : MachineDescription.DovetailLayout =>
      (SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
        some
  constructor
  · exact
      MachineDescription.seqSubroutine_subroutineReady
        CanonicalLayouts.DovetailLayoutScanner.stageConfigurationsAndFinalFlagsScannerDescription_subroutineReady
        hcleanup.left
  · intro L
    have hscanner :
        CanonicalLayouts.DovetailLayoutScanner.StageConfigurationsAndFinalFlagsScannerDescription.HaltsFromTape
          (SelectedProjectionTailProjector.sourceTape L (baseLeft L))
          (SelectedProjectionTailProjector.sourceScannerHandoffTape L
            (baseLeft L)) :=
      SelectedProjectionTailProjector.sourceScanner_haltsFromTape_withBase
        L (baseLeft L)
    have hcleanupRun :
        exists nB : Nat,
          cleanup.runConfig nB
              { state := cleanup.start
                tape :=
                  Tape.move Direction.right
                    (SelectedProjectionTailProjector.sourceScannerHandoffTape
                      L (baseLeft L)) } =
            { state := cleanup.halt
              tape := SelectedProjectionEquivEmitterPaddedOutputTape
                useAccept L } := by
      simpa [baseLeft,
        SelectedProjectionTailProjector.sourceScannerRightHandoffTape,
        List.map_reverse]
        using
          MachineDescription.runConfig_eq_halt_of_haltsFromTape
            (hcleanup.right L)
    simpa [SelectedProjectionPaddedTailEmitterFromCleanup, baseLeft,
      List.map_reverse] using
      MachineDescription.seqSubroutine_haltsFromTape_of_haltsFromTape
        (A :=
          CanonicalLayouts.DovetailLayoutScanner.StageConfigurationsAndFinalFlagsScannerDescription)
        (B := cleanup)
        (handoffMove := Direction.right)
        CanonicalLayouts.DovetailLayoutScanner.stageConfigurationsAndFinalFlagsScannerDescription_subroutineReady
        hcleanup.left hscanner hcleanupRun

theorem selectedProjectionPaddedTailEmitterConstruction_of_cleanup
    (hcleanup : SelectedProjectionPaddedTailCleanupConstruction) :
    SelectedProjectionPaddedTailEmitterConstruction := by
  intro useAccept
  rcases hcleanup useAccept with ⟨cleanup, hcleanup⟩
  exact
    ⟨SelectedProjectionPaddedTailEmitterFromCleanup useAccept cleanup,
      selectedProjectionPaddedTailEmitterSpec_of_cleanup hcleanup⟩

def SelectedProjectionCheckedEquivPaddedEmitterComponentConstruction :
    Prop :=
  SelectedProjectionInputQuoterConstruction ∧
    SelectedProjectionPaddedTailEmitterConstruction

def SelectedProjectionCheckedEquivPaddedEmitterFromComponents
    (quoter tail : MachineDescription) : MachineDescription :=
  SeqViaCanonical quoter tail

theorem selectedProjectionCheckedEquivPaddedEmitterSpec_of_components
    {useAccept : Bool}
    {quoter tail : MachineDescription}
    (hquoter : SelectedProjectionInputQuoterSpec quoter)
    (htail : SelectedProjectionPaddedTailEmitterSpec useAccept tail) :
    SelectedProjectionCheckedEquivPaddedEmitterSpec useAccept
      (SelectedProjectionCheckedEquivPaddedEmitterFromComponents
        quoter tail) := by
  let baseLeft :=
    fun L : MachineDescription.DovetailLayout =>
      (SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
        some
  constructor
  · exact SeqViaCanonical_subroutineReady hquoter.left htail.left
  · intro L
    have hquoterRun :
        quoter.HaltsFromTape
          (ParsedLayoutCheckedTape L)
          (SelectedProjectionTailProjector.sourceTape L
            (baseLeft L)) :=
      hquoter.right L
    have htailRun :
        tail.HaltsFromTape
          (SelectedProjectionTailProjector.sourceTape L
            (baseLeft L))
          (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L) :=
      htail.right L
    have hbridge :
        Tape.move Direction.left
            (Tape.move Direction.right
              (SelectedProjectionTailProjector.sourceTape L
                (baseLeft L))) =
          SelectedProjectionTailProjector.sourceTape L
            (baseLeft L) :=
      SelectedProjectionTailProjector.sourceTape_move_left_move_right
        L (baseLeft L)
    simpa [SelectedProjectionCheckedEquivPaddedEmitterFromComponents] using
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        hquoter.left htail.left hquoterRun hbridge htailRun

theorem selectedProjectionCheckedEquivPaddedEmitterConstruction_of_components
    (hcomponents :
      SelectedProjectionCheckedEquivPaddedEmitterComponentConstruction) :
    SelectedProjectionCheckedEquivPaddedEmitterConstruction := by
  intro useAccept
  rcases hcomponents with ⟨⟨quoter, hquoter⟩, htailConstruction⟩
  rcases htailConstruction useAccept with ⟨tail, htail⟩
  exact
    ⟨SelectedProjectionCheckedEquivPaddedEmitterFromComponents quoter tail,
      selectedProjectionCheckedEquivPaddedEmitterSpec_of_components
        hquoter htail⟩

theorem selectedProjectionEquivEmitterSpec_of_padded
    {useAccept : Bool} {emitter : MachineDescription}
    (hemits : SelectedProjectionEquivPaddedEmitterSpec useAccept emitter) :
    SelectedProjectionEquivEmitterSpec useAccept emitter := by
  constructor
  · exact hemits.left
  constructor
  · intro L
    exact
      ⟨SelectedProjectionEquivEmitterPaddedOutputTape useAccept L,
        hemits.right L,
        SelectedProjectionEquivEmitterPaddedOutputTape_equiv useAccept L⟩
  · intro L T hhalt
    have hT :
        T = SelectedProjectionEquivEmitterPaddedOutputTape useAccept L :=
      MachineDescription.haltsFromTape_functional_of_haltTransitionFree
        hemits.left.right hhalt (hemits.right L)
    rw [hT]
    exact SelectedProjectionEquivEmitterPaddedOutputTape_equiv useAccept L

theorem selectedProjectionEquivEmitterConstruction_of_padded
    (h : SelectedProjectionEquivPaddedEmitterConstruction) :
    SelectedProjectionEquivEmitterConstruction := by
  intro useAccept
  rcases h useAccept with ⟨emitter, hemits⟩
  exact ⟨emitter, selectedProjectionEquivEmitterSpec_of_padded hemits⟩

theorem selectedProjectionCheckedEquivEmitterSpec_of_padded
    {useAccept : Bool} {emitter : MachineDescription}
    (hemits :
      SelectedProjectionCheckedEquivPaddedEmitterSpec useAccept emitter) :
    SelectedProjectionCheckedEquivEmitterSpec useAccept emitter := by
  constructor
  · exact hemits.left
  constructor
  · intro L
    exact
      ⟨SelectedProjectionEquivEmitterPaddedOutputTape useAccept L,
        hemits.right L,
        SelectedProjectionEquivEmitterPaddedOutputTape_equiv useAccept L⟩
  · intro L T hhalt
    have hT :
        T = SelectedProjectionEquivEmitterPaddedOutputTape useAccept L :=
      MachineDescription.haltsFromTape_functional_of_haltTransitionFree
        hemits.left.right hhalt (hemits.right L)
    rw [hT]
    exact SelectedProjectionEquivEmitterPaddedOutputTape_equiv useAccept L

theorem selectedProjectionCheckedEquivEmitterConstruction_of_padded
    (h : SelectedProjectionCheckedEquivPaddedEmitterConstruction) :
    SelectedProjectionCheckedEquivEmitterConstruction := by
  intro useAccept
  rcases h useAccept with ⟨emitter, hemits⟩
  exact
    ⟨emitter, selectedProjectionCheckedEquivEmitterSpec_of_padded hemits⟩

def SelectedProjectionInputQuoterExactSourceTape
    (L : MachineDescription.DovetailLayout) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells []
    (List.append
      ((List.append
        (MachineDescription.encodeCodeSymbolAsInput
          MachineCodeSymbol.transition)
        (List.append
          (DovetailInitialLayoutInitializer.stageInputBits
            L.input L.stage)
          (SelectedProjectionTailProjector.sourceRestFieldBits L))).map
        some)
      [none])

def SelectedProjectionInputQuoterExactTargetTape
    (L : MachineDescription.DovetailLayout) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells
    ((SelectedProjectionTailProjector.outputPrefixStageInputSourceRestFieldBits
      L).reverse.map some)
    ((List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        L.stage)
      (SelectedProjectionTailProjector.sourceRestFieldBits L)).map some)

theorem parsedLayoutCheckedTape_eq_inputQuoterExactSourceTape
    (L : MachineDescription.DovetailLayout) :
    ParsedLayoutCheckedTape L =
      SelectedProjectionInputQuoterExactSourceTape L := by
  rw [SelectedProjectionInputQuoterExactSourceTape,
    SelectedProjectionTailProjector.parsedLayoutCheckedTape_eq_transition_stageInput_sourceRestFieldBits]

theorem sourceTape_outputPrefix_eq_inputQuoterExactTargetTape
    (L : MachineDescription.DovetailLayout) :
    SelectedProjectionTailProjector.sourceTape L
        ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
          some) =
      SelectedProjectionInputQuoterExactTargetTape L := by
  rw [SelectedProjectionInputQuoterExactTargetTape,
    SelectedProjectionTailProjector.sourceTape_outputPrefix_eq_stageInputSourceRestFieldBits]

def SelectedProjectionInputQuoterExactShapeSpec
    (quoter : MachineDescription) : Prop :=
  quoter.SubroutineReady ∧
    forall L : MachineDescription.DovetailLayout,
      quoter.HaltsFromTape
        (SelectedProjectionInputQuoterExactSourceTape L)
        (SelectedProjectionInputQuoterExactTargetTape L)

def SelectedProjectionInputQuoterExactShapeConstruction : Prop :=
  exists quoter : MachineDescription,
    SelectedProjectionInputQuoterExactShapeSpec quoter

theorem selectedProjectionInputQuoterSpec_of_exactShape
    {quoter : MachineDescription}
    (hquoter : SelectedProjectionInputQuoterExactShapeSpec quoter) :
    SelectedProjectionInputQuoterSpec quoter := by
  constructor
  · exact hquoter.left
  · intro L
    have hrun := hquoter.right L
    rw [parsedLayoutCheckedTape_eq_inputQuoterExactSourceTape L]
    rw [sourceTape_outputPrefix_eq_inputQuoterExactTargetTape L]
    exact hrun

theorem selectedProjectionInputQuoterConstruction_of_exactShape
    (h : SelectedProjectionInputQuoterExactShapeConstruction) :
    SelectedProjectionInputQuoterConstruction := by
  rcases h with ⟨quoter, hquoter⟩
  exact
    ⟨quoter,
      selectedProjectionInputQuoterSpec_of_exactShape hquoter⟩

/--
Finite-machine leaf for selected projection under the equivalence-based phase
contract.  The checked parser supplies the canonical checked parsed-layout
input.  This first phase quotes the input field and positions the remaining
layout fields for the selected padded tail emitter.
-/
theorem selectedProjectionInputQuoterExactShapeConstruction_scaffold :
    SelectedProjectionInputQuoterExactShapeConstruction := by
  sorry

theorem selectedProjectionInputQuoterConstruction_scaffold :
    SelectedProjectionInputQuoterConstruction :=
  selectedProjectionInputQuoterConstruction_of_exactShape
    selectedProjectionInputQuoterExactShapeConstruction_scaffold

/--
Finite-machine leaf for the selected-projection tail cleanup.  The reusable
stage/configuration/final-flag scanner has already consumed the remaining
layout fields and handed off one cell to the right; this cleanup may leave
trailing blank padding while emitting a tape equivalent to the right-shifted
selected simulator-layout output.
-/
theorem selectedProjectionPaddedTailCleanupConstruction_scaffold :
    SelectedProjectionPaddedTailCleanupConstruction := by
  sorry

theorem selectedProjectionPaddedTailEmitterConstruction_scaffold :
    SelectedProjectionPaddedTailEmitterConstruction :=
  selectedProjectionPaddedTailEmitterConstruction_of_cleanup
    selectedProjectionPaddedTailCleanupConstruction_scaffold

theorem selectedProjectionCheckedEquivPaddedEmitterComponentConstruction_scaffold :
    SelectedProjectionCheckedEquivPaddedEmitterComponentConstruction :=
  ⟨selectedProjectionInputQuoterConstruction_scaffold,
    selectedProjectionPaddedTailEmitterConstruction_scaffold⟩

theorem selectedProjectionCheckedEquivPaddedEmitterConstruction_scaffold :
    SelectedProjectionCheckedEquivPaddedEmitterConstruction :=
  selectedProjectionCheckedEquivPaddedEmitterConstruction_of_components
    selectedProjectionCheckedEquivPaddedEmitterComponentConstruction_scaffold

theorem selectedProjectionCheckedEquivEmitterConstruction_scaffold :
    SelectedProjectionCheckedEquivEmitterConstruction :=
  selectedProjectionCheckedEquivEmitterConstruction_of_padded
    selectedProjectionCheckedEquivPaddedEmitterConstruction_scaffold

theorem selectedProjectionFiniteDescriptionConstruction_scaffold :
    SelectedProjectionFiniteDescriptionConstruction :=
  selectedProjectionFiniteDescriptionConstruction_of_checkedEquivEmitter
    selectedProjectionCheckedEquivEmitterConstruction_scaffold


end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
