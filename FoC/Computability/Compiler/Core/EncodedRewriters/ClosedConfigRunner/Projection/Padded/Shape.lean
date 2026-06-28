import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.FiniteDescriptionContracts

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

def SelectedProjectionEquivEmitterPaddedOutputTape
    (useAccept : Bool)
    (L : DovetailLayout) : Tape Bool :=
  RightScratchPaddedOutputTape
    (fun L : DovetailLayout =>
      encodeCodeWordAsInput
        (SelectedProjectionOutputCode useAccept L))
    (fun L : DovetailLayout =>
      (ParsedLayoutBits L).length)
    L

theorem SelectedProjectionEquivEmitterPaddedOutputTape_equiv
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.Equiv
      (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L)
      (SelectedProjectionOutputTape useAccept L) := by
  simpa [SelectedProjectionEquivEmitterPaddedOutputTape,
    SelectedProjectionOutputTape, RightScratchPaddedOutputTape,
    ScratchPaddedOutputTape] using
    Tape.Equiv.move
      (inputWithTrailingBlankPadding_equiv_input
        (encodeCodeWordAsInput
          (SelectedProjectionOutputCode useAccept L))
        (ParsedLayoutBits L).length)
      Direction.right

theorem SelectedProjectionEquivEmitterPaddedOutputTape_normalizedOutput
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.normalizedOutput
        (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L) =
      encodeCodeWordAsInput
        (SelectedProjectionOutputCode useAccept L) := by
  simpa [SelectedProjectionEquivEmitterPaddedOutputTape,
    RightScratchPaddedOutputTape, ScratchPaddedOutputTape] using
    inputWithTrailingBlankPadding_move_right_normalizedOutput
      (encodeCodeWordAsInput
        (SelectedProjectionOutputCode useAccept L))
      (ParsedLayoutBits L).length

theorem SelectedProjectionEquivEmitterPaddedOutputTape_normalizedOutput_eq_tail
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.normalizedOutput
        (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L) =
      SelectedProjectionTailProjector.outputAllBits useAccept L := by
  rw [SelectedProjectionEquivEmitterPaddedOutputTape_normalizedOutput,
    selectedProjectionOutputBits_eq_tailProjector_outputAllBits]

theorem SelectedProjectionEquivEmitterPaddedOutputTape_eq_outputAllBits
    (useAccept : Bool) (L : DovetailLayout) :
    SelectedProjectionEquivEmitterPaddedOutputTape useAccept L =
      Tape.move Direction.right
        (inputWithTrailingBlankPadding
          (SelectedProjectionTailProjector.outputAllBits useAccept L)
          (ParsedLayoutBits L).length) := by
  simp [SelectedProjectionEquivEmitterPaddedOutputTape,
    RightScratchPaddedOutputTape, ScratchPaddedOutputTape,
    selectedProjectionOutputBits_eq_tailProjector_outputAllBits]

theorem SelectedProjectionEquivEmitterPaddedOutputTape_eq_tapeAtCells
    (useAccept : Bool) (L : DovetailLayout) :
    SelectedProjectionEquivEmitterPaddedOutputTape useAccept L =
      match
          inputWithTrailingBlankPaddingCells
            (SelectedProjectionTailProjector.outputAllBits useAccept L)
            (ParsedLayoutBits L).length with
      | [] => DovetailInitialLayoutInitializer.tapeAtCells [] []
      | cell :: rest =>
          DovetailInitialLayoutInitializer.tapeAtCells [cell] rest := by
  rw [SelectedProjectionEquivEmitterPaddedOutputTape_eq_outputAllBits]
  exact
    inputWithTrailingBlankPadding_move_right_eq_tapeAtCells
      (SelectedProjectionTailProjector.outputAllBits useAccept L)
      (ParsedLayoutBits L).length

theorem selectedProjection_outputAllBits_cons_cons
    (useAccept : Bool) (L : DovetailLayout) :
    exists first : Bool,
    exists second : Bool,
    exists rest : Word Bool,
      SelectedProjectionTailProjector.outputAllBits useAccept L =
        first :: second :: rest := by
  refine ⟨false, false, ?_⟩
  refine
    ⟨false :: false ::
      List.append
        (encodeCodeWordAsInput
          (encodeBoolWordAppend (ParsedLayoutBits L) []))
        (SelectedProjectionTailProjector.outputBits useAccept L), ?_⟩
  simp [SelectedProjectionTailProjector.outputAllBits,
    SelectedProjectionTailProjector.outputPrefixBits,
    encodeCodeSymbolAsInput]

theorem selectedProjection_outputAllBits_headerPrefix
    (useAccept : Bool) (L : DovetailLayout) :
    exists rest : Word Bool,
      SelectedProjectionTailProjector.outputAllBits useAccept L =
        false :: false :: false :: false :: rest := by
  refine
    ⟨List.append
      (encodeCodeWordAsInput
        (encodeBoolWordAppend (ParsedLayoutBits L) []))
      (SelectedProjectionTailProjector.outputBits useAccept L), ?_⟩
  simp [SelectedProjectionTailProjector.outputAllBits,
    SelectedProjectionTailProjector.outputPrefixBits,
    encodeCodeSymbolAsInput]

theorem inputWithTrailingBlankPaddingCells_outputAllBits_eq
    (useAccept : Bool) (L : DovetailLayout) :
    inputWithTrailingBlankPaddingCells
        (SelectedProjectionTailProjector.outputAllBits useAccept L)
        (ParsedLayoutBits L).length =
      List.append
        ((SelectedProjectionTailProjector.outputAllBits useAccept L).map some)
        (List.replicate (ParsedLayoutBits L).length none) := by
  rcases selectedProjection_outputAllBits_cons_cons useAccept L with
    ⟨first, second, rest, hbits⟩
  rw [hbits]
  rfl

theorem SelectedProjectionEquivEmitterPaddedOutputTape_eq_tapeAtCells_of_outputAllBits
    {useAccept : Bool} {L : DovetailLayout}
    {first : Bool} {rest : Word Bool}
    (hbits :
      SelectedProjectionTailProjector.outputAllBits useAccept L =
        first :: rest) :
    SelectedProjectionEquivEmitterPaddedOutputTape useAccept L =
      DovetailInitialLayoutInitializer.tapeAtCells
        [some first]
        (List.append (rest.map some)
          (List.replicate (ParsedLayoutBits L).length none)) := by
  rw [SelectedProjectionEquivEmitterPaddedOutputTape_eq_tapeAtCells]
  rw [inputWithTrailingBlankPaddingCells_outputAllBits_eq]
  rw [hbits]
  rfl

theorem SelectedProjectionEquivEmitterPaddedOutputTape_eq_tapeAtCells_cons_cons
    (useAccept : Bool) (L : DovetailLayout) :
    exists first : Bool,
    exists second : Bool,
    exists rest : Word Bool,
      SelectedProjectionEquivEmitterPaddedOutputTape useAccept L =
        DovetailInitialLayoutInitializer.tapeAtCells
          [some first]
          (some second :: List.append (rest.map some)
            (List.replicate (ParsedLayoutBits L).length none)) ∧
      SelectedProjectionTailProjector.outputAllBits useAccept L =
        first :: second :: rest := by
  rcases selectedProjection_outputAllBits_cons_cons useAccept L with
    ⟨first, second, rest, hbits⟩
  refine ⟨first, second, rest, ?_, hbits⟩
  have htape :=
    SelectedProjectionEquivEmitterPaddedOutputTape_eq_tapeAtCells_of_outputAllBits
      (useAccept := useAccept) (L := L) (first := first)
      (rest := second :: rest) hbits
  simpa using htape

theorem SelectedProjectionEquivEmitterPaddedOutputTape_cells
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.cells (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L) =
      List.append
        ((SelectedProjectionTailProjector.outputAllBits useAccept L).map some)
        (List.replicate (ParsedLayoutBits L).length none) := by
  rcases
      SelectedProjectionEquivEmitterPaddedOutputTape_eq_tapeAtCells_cons_cons
        useAccept L with
    ⟨first, second, rest, htape, hbits⟩
  rw [htape, hbits]
  simp [DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.cells]

theorem SelectedProjectionEquivEmitterPaddedOutputTape_true_cells
    (L : DovetailLayout) :
    Tape.cells (SelectedProjectionEquivEmitterPaddedOutputTape true L) =
      List.append
        (List.map some
          (List.append (SelectedProjectionTailProjector.outputPrefixBits L)
            (List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                L.stage)
              (List.append
                (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                  L.acceptConfig [])
                (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                  L.acceptHit [])))))
        (List.replicate (ParsedLayoutBits L).length none) := by
  rw [SelectedProjectionEquivEmitterPaddedOutputTape_cells]
  rw [SelectedProjectionTailProjector.outputAllBits,
    SelectedProjectionTailProjector.outputBits_true_eq_fields]
  rw [←
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil]

theorem SelectedProjectionEquivEmitterPaddedOutputTape_false_cells
    (L : DovetailLayout) :
    Tape.cells (SelectedProjectionEquivEmitterPaddedOutputTape false L) =
      List.append
        (List.map some
          (List.append (SelectedProjectionTailProjector.outputPrefixBits L)
            (List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                L.stage)
              (List.append
                (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                  L.rejectConfig [])
                (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                  L.rejectHit [])))))
        (List.replicate (ParsedLayoutBits L).length none) := by
  rw [SelectedProjectionEquivEmitterPaddedOutputTape_cells]
  rw [SelectedProjectionTailProjector.outputAllBits,
    SelectedProjectionTailProjector.outputBits_false_eq_fields]
  rw [←
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil]

theorem SelectedProjectionEquivEmitterPaddedOutputTape_move_left_move_right
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L)) =
      SelectedProjectionEquivEmitterPaddedOutputTape useAccept L := by
  rcases selectedProjection_outputAllBits_headerPrefix useAccept L with
    ⟨rest, hbits⟩
  have htape :=
    SelectedProjectionEquivEmitterPaddedOutputTape_eq_tapeAtCells_of_outputAllBits
      (useAccept := useAccept) (L := L) (first := false)
      (rest := false :: false :: false :: rest) hbits
  rw [htape]
  simp [DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem tapeAtCells_nil_normalizedOutput
    (leftRev : List (Option Bool)) :
    Tape.normalizedOutput
        (DovetailInitialLayoutInitializer.tapeAtCells leftRev []) =
      leftRev.reverse.filterMap (fun cell => cell) := by
  simp [DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.normalizedOutput, Tape.cells]

theorem dovetailScanner_configurationRestoredLeftWithBase_reverse_filterMap
    (cfg : Configuration)
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
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.contextLength (Tape.input (ParsedLayoutBits L)) <=
      Tape.contextLength
        (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L) := by
  have hpad :=
    inputWithTrailingBlankPadding_contextLength_ge_input
      (encodeCodeWordAsInput
        (SelectedProjectionOutputCode useAccept L))
      (ParsedLayoutBits L)
  have hmove :=
    tape_contextLength_le_move_right
      (inputWithTrailingBlankPadding
        (encodeCodeWordAsInput
          (SelectedProjectionOutputCode useAccept L))
        (ParsedLayoutBits L).length)
  exact Nat.le_trans hpad hmove

namespace SelectedProjectionTailProjector

theorem parsedLayoutCheckedTape_normalizedOutput_eq_transition_stageInput_sourceRestSuffix
    (L : DovetailLayout) :
    Tape.normalizedOutput (ParsedLayoutCheckedTape L) =
      List.append
        (encodeCodeSymbolAsInput
          MachineCodeSymbol.transition)
        (List.append
          (DovetailInitialLayoutInitializer.stageInputBits
            L.input L.stage)
          (encodeCodeWordAsInput
            (sourceRestSuffix L))) := by
  rw [parsedLayoutCheckedTape_normalizedOutput,
    parsedLayoutBits_eq_transition_stageInput_sourceRestSuffix]

theorem parsedLayoutCheckedTape_normalizedOutput_eq_transition_stageInput_sourceRestFieldBits
    (L : DovetailLayout) :
    Tape.normalizedOutput (ParsedLayoutCheckedTape L) =
      List.append
        (encodeCodeSymbolAsInput
          MachineCodeSymbol.transition)
        (List.append
          (DovetailInitialLayoutInitializer.stageInputBits
            L.input L.stage)
          (sourceRestFieldBits L)) := by
  rw [parsedLayoutCheckedTape_normalizedOutput,
    parsedLayoutBits_eq_transition_stageInput_sourceRestFieldBits]

theorem parsedLayoutCheckedTape_eq_transition_stageInput_sourceRestSuffix
    (L : DovetailLayout) :
    ParsedLayoutCheckedTape L =
      DovetailInitialLayoutInitializer.tapeAtCells []
        (List.append
          ((List.append
            (encodeCodeSymbolAsInput
              MachineCodeSymbol.transition)
            (List.append
              (DovetailInitialLayoutInitializer.stageInputBits
                L.input L.stage)
              (encodeCodeWordAsInput
                (sourceRestSuffix L)))).map some)
          [none]) := by
  rw [ParsedLayoutCheckedTape,
    parsedLayoutBits_eq_transition_stageInput_sourceRestSuffix]
  simp [checkedInputTape, DovetailInitialLayoutInitializer.tapeAtCells,
    encodeCodeSymbolAsInput, List.map_append,
    List.append_assoc]

theorem parsedLayoutCheckedTape_eq_transition_stageInput_sourceRestFieldBits
    (L : DovetailLayout) :
    ParsedLayoutCheckedTape L =
      DovetailInitialLayoutInitializer.tapeAtCells []
        (List.append
          ((List.append
            (encodeCodeSymbolAsInput
              MachineCodeSymbol.transition)
            (List.append
              (DovetailInitialLayoutInitializer.stageInputBits
                L.input L.stage)
              (sourceRestFieldBits L))).map some)
          [none]) := by
  rw [ParsedLayoutCheckedTape,
    parsedLayoutBits_eq_transition_stageInput_sourceRestFieldBits]
  simp [checkedInputTape, DovetailInitialLayoutInitializer.tapeAtCells,
    encodeCodeSymbolAsInput, List.map_append,
    List.append_assoc]

theorem parsedLayoutCheckedHandoffTape_eq_transition_stageInput_sourceRestSuffix
    (L : DovetailLayout) :
    ParsedLayoutCheckedHandoffTape L =
      DovetailInitialLayoutInitializer.tapeAtCells [some false]
        (List.append [some false, some false, some true]
          (List.append
            ((List.append
              (DovetailInitialLayoutInitializer.stageInputBits
                L.input L.stage)
              (encodeCodeWordAsInput
                (sourceRestSuffix L))).map some)
            [none])) := by
  rw [ParsedLayoutCheckedHandoffTape,
    parsedLayoutCheckedTape_eq_transition_stageInput_sourceRestSuffix]
  simp [DovetailInitialLayoutInitializer.tapeAtCells,
    encodeCodeSymbolAsInput, Tape.move, Tape.moveRight,
    List.map_append, List.append_assoc]

theorem parsedLayoutCheckedHandoffTape_eq_transition_stageInput_sourceRestFieldBits
    (L : DovetailLayout) :
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
    encodeCodeSymbolAsInput, Tape.move, Tape.moveRight,
    List.map_append, List.append_assoc]

theorem sourceFieldBits_length_le_parsedLayoutBits
    (L : DovetailLayout) :
    (sourceFieldBits L).length <= (ParsedLayoutBits L).length := by
  rw [← sourceSuffix_bits_eq_fields]
  rw [ParsedLayoutBits,
    dovetailLayout_encode_eq_transition_input_sourceSuffix]
  have happend :
      encodeBoolWordAppend L.input
          (sourceSuffix L) =
        List.append
          (encodeBoolWordAppend L.input [])
          (sourceSuffix L) := by
    simpa using
      encodeBoolWordAppend_append L.input ([] : Word MachineCodeSymbol)
        (sourceSuffix L)
  rw [happend]
  change List.length
        (encodeCodeWordAsInput
          (sourceSuffix L)) <=
      List.length
        (encodeCodeWordAsInput
          (List.append
            (MachineCodeSymbol.transition ::
              encodeBoolWordAppend L.input [])
            (sourceSuffix L)))
  rw [encodeCodeWordAsInput_append]
  simp [encodeCodeWordAsInput]
  omega

theorem outputPrefixBits_length_ge_parsedLayoutBits
    (L : DovetailLayout) :
    (ParsedLayoutBits L).length <= (outputPrefixBits L).length := by
  have hquote :
      (ParsedLayoutBits L).length <=
        (encodeBoolWordAppend
          (ParsedLayoutBits L) []).length := by
    simpa using
      encodeBoolWordAppend_length_ge (ParsedLayoutBits L)
        ([] : Word MachineCodeSymbol)
  have hencoded :
      (encodeBoolWordAppend
          (ParsedLayoutBits L) []).length <=
        (encodeCodeWordAsInput
          (encodeBoolWordAppend
            (ParsedLayoutBits L) [])).length := by
    rw [encodeCodeWordAsInput_length]
    omega
  have hprefix :
      (encodeCodeWordAsInput
          (encodeBoolWordAppend
            (ParsedLayoutBits L) [])).length <=
        (outputPrefixBits L).length := by
    simp [outputPrefixBits, List.length_append]
  exact Nat.le_trans hquote (Nat.le_trans hencoded hprefix)

theorem sourceTape_contextLength_ge_parsedLayoutCheckedTape
    (L : DovetailLayout) :
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
    (L : DovetailLayout)
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
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (sourceTape L ((outputPrefixBits L).reverse.map some)) =
      List.append (outputPrefixBits L) (sourceFieldBits L) := by
  rw [sourceTape_normalizedOutput]
  simp [Function.comp_def, List.map_reverse]

theorem sourceTape_outputPrefix_eq_stageInputSourceRestFieldBits
    (L : DovetailLayout) :
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
    (L : DovetailLayout) :
    List.append (outputPrefixBits L) (sourceFieldBits L) =
      encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          encodeBoolWordAppend
            (ParsedLayoutBits L) (sourceSuffix L)) := by
  have happend :
      encodeBoolWordAppend
          (ParsedLayoutBits L) (sourceSuffix L) =
        List.append
          (encodeBoolWordAppend
            (ParsedLayoutBits L) [])
          (sourceSuffix L) := by
    simpa using
      encodeBoolWordAppend_append (ParsedLayoutBits L)
        ([] : Word MachineCodeSymbol) (sourceSuffix L)
  rw [outputPrefixBits, ← sourceSuffix_bits_eq_fields L, happend]
  simp only [encodeCodeWordAsInput]
  rw [encodeCodeWordAsInput_append]
  simp [List.append_assoc]

theorem sourceTape_normalizedOutput_outputPrefix_eq_header_input_sourceSuffix
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (sourceTape L ((outputPrefixBits L).reverse.map some)) =
      encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          encodeBoolWordAppend
            (ParsedLayoutBits L) (sourceSuffix L)) := by
  rw [sourceTape_normalizedOutput_outputPrefix,
    outputPrefixBits_append_sourceFieldBits]

theorem sourceTape_normalizedOutput_outputPrefix_eq_quoter_bits
    (L : DovetailLayout) :
    exists b : Bool,
    exists rest : Word Bool,
      ParsedLayoutBits L = b :: rest ∧
        Tape.normalizedOutput
            (sourceTape L ((outputPrefixBits L).reverse.map some)) =
          List.append
            (encodeCodeSymbolAsInput
              MachineCodeSymbol.header)
            (CommonGround.BoolWordQuoters.checkedNonemptyBoolWordQuoteDirectSourceBits
              b rest (sourceSuffix L)) := by
  rcases parsedLayoutBits_eq_false_false_tail L with ⟨tail, htail⟩
  refine ⟨false, false :: tail, htail, ?_⟩
  rw [sourceTape_normalizedOutput_outputPrefix_eq_header_input_sourceSuffix,
    htail]
  simp [encodeCodeWordAsInput,
    CommonGround.BoolWordQuoters.checkedNonemptyBoolWordQuoteDirectSourceBits_eq]

theorem sourceScannerRightHandoffTape_normalizedOutput
    (L : DovetailLayout)
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
    (L : DovetailLayout)
    (baseLeft : List (Option Bool)) :
    Tape.normalizedOutput
        (sourceScannerRightHandoffTape L baseLeft) =
      Tape.normalizedOutput (sourceTape L baseLeft) := by
  rw [sourceScannerRightHandoffTape_normalizedOutput,
    sourceTape_normalizedOutput]

theorem sourceScannerRightHandoffTape_normalizedOutput_outputPrefix
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (sourceScannerRightHandoffTape L
          ((outputPrefixBits L).reverse.map some)) =
      List.append (outputPrefixBits L) (sourceFieldBits L) := by
  rw [sourceScannerRightHandoffTape_normalizedOutput]
  simp [Function.comp_def, List.map_reverse]

theorem
    sourceScannerRightHandoffTape_normalizedOutput_outputPrefix_eq_header_input_sourceSuffix
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (sourceScannerRightHandoffTape L
          ((outputPrefixBits L).reverse.map some)) =
      encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          encodeBoolWordAppend
            (ParsedLayoutBits L) (sourceSuffix L)) := by
  rw [sourceScannerRightHandoffTape_normalizedOutput_outputPrefix,
    outputPrefixBits_append_sourceFieldBits]

theorem
    sourceScannerRightHandoffTape_normalizedOutput_outputPrefix_eq_quoter_bits
    (L : DovetailLayout) :
    exists b : Bool,
    exists rest : Word Bool,
      ParsedLayoutBits L = b :: rest ∧
        Tape.normalizedOutput
          (sourceScannerRightHandoffTape L
            ((outputPrefixBits L).reverse.map some)) =
          List.append
            (encodeCodeSymbolAsInput
              MachineCodeSymbol.header)
            (CommonGround.BoolWordQuoters.checkedNonemptyBoolWordQuoteDirectSourceBits
              b rest (sourceSuffix L)) := by
  rcases parsedLayoutBits_eq_false_false_tail L with ⟨tail, htail⟩
  refine ⟨false, false :: tail, htail, ?_⟩
  rw [
    sourceScannerRightHandoffTape_normalizedOutput_outputPrefix_eq_header_input_sourceSuffix,
    htail]
  simp [encodeCodeWordAsInput,
    CommonGround.BoolWordQuoters.checkedNonemptyBoolWordQuoteDirectSourceBits_eq]

theorem sourceScannerRightHandoffTape_contextLength_ge_sourceTape
    (L : DovetailLayout)
    (baseLeft : List (Option Bool)) :
    Tape.contextLength (sourceTape L baseLeft) <=
      Tape.contextLength (sourceScannerRightHandoffTape L baseLeft) := by
  rcases sourceScanner_haltsFromTape_withBase L baseLeft with
    ⟨steps, hsteps⟩
  let scanner :=
    CanonicalLayouts.DovetailLayoutScanner.StageConfigurationsAndFinalFlagsScannerDescription
  have hmono :=
    runConfig_contextLength_mono
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
    (useAccept : Bool) (L : DovetailLayout) :
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
      RightScratchPaddedOutputTape, ScratchPaddedOutputTape,
      selectedProjectionOutputBits_eq_tailProjector_outputAllBits] using
      inputWithTrailingBlankPadding_move_right_contextLength_ge_pred
        (SelectedProjectionTailProjector.outputAllBits useAccept L)
        (ParsedLayoutBits L).length
  exact Nat.le_trans hsource htarget

theorem
    SelectedProjectionEquivEmitterPaddedOutputTape_contextLength_ge_checkedInput
    (useAccept : Bool) (L : DovetailLayout) :
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
    (cfg : Configuration)
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
    (useAccept : Bool) (L : DovetailLayout) :
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
      RightScratchPaddedOutputTape, ScratchPaddedOutputTape,
      selectedProjectionOutputBits_eq_tailProjector_outputAllBits] using
      inputWithTrailingBlankPadding_move_right_contextLength_ge_pred
        (SelectedProjectionTailProjector.outputAllBits useAccept L)
        (ParsedLayoutBits L).length
  exact Nat.le_trans hsource htarget

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
