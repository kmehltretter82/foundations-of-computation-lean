import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Primitives
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner

set_option doc.verso true

/-!
# Selected projection tail projector

This module isolates the suffix projection problem after the scanner has
advanced past the input field of a checked dovetail layout.  At that boundary
the remaining source fields are the stage, both recognizer configurations, and
both hit flags.  The selected projection output keeps the stage and one
configuration/hit pair.
-/

namespace FoC
namespace Computability

open Languages
open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner
open FoC.Computability.EncodedRewriters.CanonicalLayouts
open FoC.Computability.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner

namespace EncodedRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionTailProjector

def selectedConfig
    (useAccept : Bool)
    (L : MachineDescription.DovetailLayout) :
    MachineDescription.Configuration :=
  if useAccept then L.acceptConfig else L.rejectConfig

def selectedHit
    (useAccept : Bool)
    (L : MachineDescription.DovetailLayout) : Bool :=
  if useAccept then L.acceptHit else L.rejectHit

theorem selectedConfig_true
    (L : MachineDescription.DovetailLayout) :
    selectedConfig true L = L.acceptConfig := by
  rfl

theorem selectedConfig_false
    (L : MachineDescription.DovetailLayout) :
    selectedConfig false L = L.rejectConfig := by
  rfl

theorem selectedHit_true
    (L : MachineDescription.DovetailLayout) :
    selectedHit true L = L.acceptHit := by
  rfl

theorem selectedHit_false
    (L : MachineDescription.DovetailLayout) :
    selectedHit false L = L.rejectHit := by
  rfl

def sourceSuffix
    (L : MachineDescription.DovetailLayout) :
    Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend L.stage
    (MachineDescription.encodeConfigurationAppend L.acceptConfig
      (MachineDescription.encodeConfigurationAppend L.rejectConfig
        (MachineDescription.encodeBoolAppend L.acceptHit
          (MachineDescription.encodeBoolAppend L.rejectHit []))))

def sourceRestSuffix
    (L : MachineDescription.DovetailLayout) :
    Word MachineCodeSymbol :=
  MachineDescription.encodeConfigurationAppend L.acceptConfig
    (MachineDescription.encodeConfigurationAppend L.rejectConfig
      (MachineDescription.encodeBoolAppend L.acceptHit
        (MachineDescription.encodeBoolAppend L.rejectHit [])))

def sourceFieldBits
    (L : MachineDescription.DovetailLayout) : Word Bool :=
  List.append (stageNatBits L.stage)
    (configurationFieldBits L.acceptConfig
      (configurationFieldBits L.rejectConfig
        (boolFieldBits L.acceptHit
          (boolFieldBits L.rejectHit []))))

def sourceRestFieldBits
    (L : MachineDescription.DovetailLayout) : Word Bool :=
  configurationFieldBits L.acceptConfig
    (configurationFieldBits L.rejectConfig
      (boolFieldBits L.acceptHit
        (boolFieldBits L.rejectHit [])))

theorem sourceSuffix_eq_encodeNatAppend_sourceRestSuffix
    (L : MachineDescription.DovetailLayout) :
    sourceSuffix L =
      MachineDescription.encodeNatAppend L.stage
        (sourceRestSuffix L) := by
  rfl

theorem sourceFieldBits_eq_stageNatBits_sourceRestFieldBits
    (L : MachineDescription.DovetailLayout) :
    sourceFieldBits L =
      List.append (stageNatBits L.stage) (sourceRestFieldBits L) := by
  rfl

theorem sourceRestSuffix_bits_eq_fields
    (L : MachineDescription.DovetailLayout) :
    MachineDescription.encodeCodeWordAsInput (sourceRestSuffix L) =
      sourceRestFieldBits L := by
  rw [sourceRestSuffix, sourceRestFieldBits]
  rw [configurationFieldBits_eq_encodeConfigurationAppend]
  rw [configurationFieldBits_eq_encodeConfigurationAppend]
  rw [boolBits_eq_encodeBoolAppend]
  rw [boolBits_eq_encodeBoolAppend]
  simp [boolFieldBits, cellFieldBits,
    MachineDescription.encodeCodeWordAsInput]

theorem sourceSuffix_bits_eq_fields
    (L : MachineDescription.DovetailLayout) :
    MachineDescription.encodeCodeWordAsInput (sourceSuffix L) =
      sourceFieldBits L := by
  rw [sourceSuffix, sourceFieldBits]
  rw [DovetailStagePrefix.natBits_eq_encodeNatAppend]
  rw [configurationFieldBits_eq_encodeConfigurationAppend]
  rw [configurationFieldBits_eq_encodeConfigurationAppend]
  rw [boolBits_eq_encodeBoolAppend]
  rw [boolBits_eq_encodeBoolAppend]
  simp [boolFieldBits, cellFieldBits,
    MachineDescription.encodeCodeWordAsInput]

theorem dovetailLayout_encode_eq_transition_input_sourceSuffix
    (L : MachineDescription.DovetailLayout) :
    MachineDescription.DovetailLayout.encode L =
      MachineCodeSymbol.transition ::
        MachineDescription.encodeBoolWordAppend L.input
          (sourceSuffix L) := by
  rfl

theorem parsedLayoutBits_eq_transition_input_sourceSuffix
    (L : MachineDescription.DovetailLayout) :
    ParsedLayoutBits L =
      List.append
        (MachineDescription.encodeCodeSymbolAsInput
          MachineCodeSymbol.transition)
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeBoolWordAppend L.input
            (sourceSuffix L))) := by
  simp [ParsedLayoutBits, dovetailLayout_encode_eq_transition_input_sourceSuffix,
    MachineDescription.encodeCodeWordAsInput]

theorem stageInputBits_append_sourceRestSuffix_bits
    (L : MachineDescription.DovetailLayout) :
    List.append (stageInputBits L.input L.stage)
        (MachineDescription.encodeCodeWordAsInput
          (sourceRestSuffix L)) =
      MachineDescription.encodeCodeWordAsInput
        (MachineDescription.encodeBoolWordAppend L.input
          (sourceSuffix L)) := by
  rw [stageInputBits, PairedRecognizerDovetailStageInputCode,
    MachineDescription.DovetailLayout.stageInputCode,
    MachineDescription.DovetailLayout.stageInputCodeAppend,
    sourceSuffix_eq_encodeNatAppend_sourceRestSuffix]
  rw [show
      MachineDescription.encodeNatAppend L.stage (sourceRestSuffix L) =
        List.append (MachineDescription.encodeNatAppend L.stage [])
          (sourceRestSuffix L) by
      simpa using
        encodeNatAppend_append L.stage ([] : Word MachineCodeSymbol)
          (sourceRestSuffix L)]
  rw [encodeBoolWordAppend_append]
  rw [MachineDescription.encodeCodeWordAsInput_append]

theorem parsedLayoutBits_eq_transition_stageInput_sourceRestSuffix
    (L : MachineDescription.DovetailLayout) :
    ParsedLayoutBits L =
      List.append
        (MachineDescription.encodeCodeSymbolAsInput
          MachineCodeSymbol.transition)
        (List.append (stageInputBits L.input L.stage)
          (MachineDescription.encodeCodeWordAsInput
            (sourceRestSuffix L))) := by
  rw [parsedLayoutBits_eq_transition_input_sourceSuffix]
  rw [← stageInputBits_append_sourceRestSuffix_bits L]

theorem parsedLayoutBits_eq_transition_stageInput_sourceRestFieldBits
    (L : MachineDescription.DovetailLayout) :
    ParsedLayoutBits L =
      List.append
        (MachineDescription.encodeCodeSymbolAsInput
          MachineCodeSymbol.transition)
        (List.append (stageInputBits L.input L.stage)
          (sourceRestFieldBits L)) := by
  rw [parsedLayoutBits_eq_transition_stageInput_sourceRestSuffix]
  rw [sourceRestSuffix_bits_eq_fields]

theorem parsedLayoutBits_eq_transition_input_sourceFieldBits
    (L : MachineDescription.DovetailLayout) :
    ParsedLayoutBits L =
      List.append
        (MachineDescription.encodeCodeSymbolAsInput
          MachineCodeSymbol.transition)
        (List.append
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.encodeBoolWordAppend L.input []))
          (sourceFieldBits L)) := by
  have happend :
      MachineDescription.encodeBoolWordAppend L.input (sourceSuffix L) =
        List.append
          (MachineDescription.encodeBoolWordAppend L.input [])
          (sourceSuffix L) := by
    simpa using
      encodeBoolWordAppend_append L.input
        ([] : Word MachineCodeSymbol) (sourceSuffix L)
  rw [parsedLayoutBits_eq_transition_input_sourceSuffix, happend]
  rw [MachineDescription.encodeCodeWordAsInput_append,
    sourceSuffix_bits_eq_fields]

def sourceTape
    (L : MachineDescription.DovetailLayout)
    (baseLeft : List (Option Bool)) : Tape Bool :=
  tapeAtCells baseLeft ((sourceFieldBits L).map some)

def sourceScannerHandoffTape
    (L : MachineDescription.DovetailLayout)
    (baseLeft : List (Option Bool)) : Tape Bool :=
  (boolFinalHandoffConfigWithBase L.rejectHit
    (List.append ((cellCodeBits (some L.acceptHit)).reverse.map some)
      (configurationRestoredLeftWithBase L.rejectConfig
        (configurationRestoredLeftWithBase L.acceptConfig
            (List.append ((stageNatBits L.stage).reverse.map some)
              baseLeft))))).tape

def sourceScannerRightHandoffTape
    (L : MachineDescription.DovetailLayout)
    (baseLeft : List (Option Bool)) : Tape Bool :=
  Tape.move Direction.right (sourceScannerHandoffTape L baseLeft)

theorem sourceScannerRightHandoffTape_eq
    (L : MachineDescription.DovetailLayout)
    (baseLeft : List (Option Bool)) :
    sourceScannerRightHandoffTape L baseLeft =
      tapeAtCells
        (finalHitFlagsRestoredLeftWithBase L.acceptHit L.rejectHit
          (configurationRestoredLeftWithBase L.rejectConfig
            (configurationRestoredLeftWithBase L.acceptConfig
              (List.append ((stageNatBits L.stage).reverse.map some)
                baseLeft))))
        [] := by
  rw [sourceScannerRightHandoffTape, sourceScannerHandoffTape]
  simpa [finalHitFlagsRestoredLeftWithBase] using
    boolFinalHandoffConfigWithBase_move_right L.rejectHit
      (List.append ((cellCodeBits (some L.acceptHit)).reverse.map some)
        (configurationRestoredLeftWithBase L.rejectConfig
          (configurationRestoredLeftWithBase L.acceptConfig
            (List.append ((stageNatBits L.stage).reverse.map some)
              baseLeft))))

theorem sourceScanner_run_withBase
    (L : MachineDescription.DovetailLayout)
    (baseLeft : List (Option Bool)) :
    exists steps : Nat,
      StageConfigurationsAndFinalFlagsScannerDescription.runConfig steps
          { state := StageConfigurationsAndFinalFlagsScannerDescription.start
            tape := sourceTape L baseLeft } =
        { state := StageConfigurationsAndFinalFlagsScannerDescription.halt
          tape := sourceScannerHandoffTape L baseLeft } := by
  simpa [sourceTape, sourceFieldBits, sourceScannerHandoffTape] using
    run_stageConfigurationsAndFinalFlags_raw_to_handoff_withBase
      L.stage L.acceptConfig L.rejectConfig L.acceptHit L.rejectHit
      baseLeft

theorem sourceScanner_haltsFromTape_withBase
    (L : MachineDescription.DovetailLayout)
    (baseLeft : List (Option Bool)) :
    StageConfigurationsAndFinalFlagsScannerDescription.HaltsFromTape
      (sourceTape L baseLeft)
      (sourceScannerHandoffTape L baseLeft) := by
  rcases sourceScanner_run_withBase L baseLeft with ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · rw [hsteps]
  · rw [hsteps]

def outputSuffix
    (useAccept : Bool)
    (L : MachineDescription.DovetailLayout) :
    Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend L.stage
    (MachineDescription.encodeConfigurationAppend
      (selectedConfig useAccept L)
      (MachineDescription.encodeBoolAppend
        (selectedHit useAccept L) []))

def outputBits
    (useAccept : Bool)
    (L : MachineDescription.DovetailLayout) : Word Bool :=
  MachineDescription.encodeCodeWordAsInput (outputSuffix useAccept L)

def outputPrefixBits
    (L : MachineDescription.DovetailLayout) : Word Bool :=
  List.append
    (MachineDescription.encodeCodeSymbolAsInput MachineCodeSymbol.header)
    (MachineDescription.encodeCodeWordAsInput
      (MachineDescription.encodeBoolWordAppend (ParsedLayoutBits L) []))

theorem outputPrefixBits_eq_header_quote_stageInput_sourceRestSuffix
    (L : MachineDescription.DovetailLayout) :
    outputPrefixBits L =
      List.append
        (MachineDescription.encodeCodeSymbolAsInput
          MachineCodeSymbol.header)
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeBoolWordAppend
            (List.append
              (MachineDescription.encodeCodeSymbolAsInput
                MachineCodeSymbol.transition)
              (List.append (stageInputBits L.input L.stage)
                (MachineDescription.encodeCodeWordAsInput
                  (sourceRestSuffix L)))) [])) := by
  rw [outputPrefixBits,
    parsedLayoutBits_eq_transition_stageInput_sourceRestSuffix]

theorem outputPrefixBits_eq_header_quote_stageInput_sourceRestFieldBits
    (L : MachineDescription.DovetailLayout) :
    outputPrefixBits L =
      List.append
        (MachineDescription.encodeCodeSymbolAsInput
          MachineCodeSymbol.header)
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeBoolWordAppend
            (List.append
              (MachineDescription.encodeCodeSymbolAsInput
                MachineCodeSymbol.transition)
              (List.append (stageInputBits L.input L.stage)
                (sourceRestFieldBits L))) [])) := by
  rw [outputPrefixBits,
    parsedLayoutBits_eq_transition_stageInput_sourceRestFieldBits]

def outputPrefixStageInputSourceRestFieldBits
    (L : MachineDescription.DovetailLayout) : Word Bool :=
  List.append
    (MachineDescription.encodeCodeSymbolAsInput
      MachineCodeSymbol.header)
    (MachineDescription.encodeCodeWordAsInput
      (MachineDescription.encodeBoolWordAppend
        (List.append
          (MachineDescription.encodeCodeSymbolAsInput
            MachineCodeSymbol.transition)
          (List.append (stageInputBits L.input L.stage)
            (sourceRestFieldBits L))) []))

theorem outputPrefixBits_eq_stageInputSourceRestFieldBits
    (L : MachineDescription.DovetailLayout) :
    outputPrefixBits L =
      outputPrefixStageInputSourceRestFieldBits L := by
  rw [outputPrefixStageInputSourceRestFieldBits,
    outputPrefixBits_eq_header_quote_stageInput_sourceRestFieldBits]

theorem sourceScannerRightHandoffTape_outputPrefix_eq_stageInputSourceRestFieldBits
    (L : MachineDescription.DovetailLayout) :
    sourceScannerRightHandoffTape L ((outputPrefixBits L).reverse.map some) =
      tapeAtCells
        (finalHitFlagsRestoredLeftWithBase L.acceptHit L.rejectHit
          (configurationRestoredLeftWithBase L.rejectConfig
            (configurationRestoredLeftWithBase L.acceptConfig
              (List.append ((stageNatBits L.stage).reverse.map some)
                ((outputPrefixStageInputSourceRestFieldBits L).reverse.map
                  some)))))
        [] := by
  rw [sourceScannerRightHandoffTape_eq,
    outputPrefixBits_eq_stageInputSourceRestFieldBits]

def outputAllBits
    (useAccept : Bool)
    (L : MachineDescription.DovetailLayout) : Word Bool :=
  List.append (outputPrefixBits L) (outputBits useAccept L)

def outputFieldBits
    (useAccept : Bool)
    (L : MachineDescription.DovetailLayout) : Word Bool :=
  List.append (stageNatBits L.stage)
    (configurationFieldBits (selectedConfig useAccept L)
      (boolFieldBits (selectedHit useAccept L) []))

theorem outputBits_eq_fields
    (useAccept : Bool)
    (L : MachineDescription.DovetailLayout) :
    outputBits useAccept L = outputFieldBits useAccept L := by
  rw [outputBits, outputSuffix, outputFieldBits]
  rw [DovetailStagePrefix.natBits_eq_encodeNatAppend]
  rw [configurationFieldBits_eq_encodeConfigurationAppend]
  rw [boolBits_eq_encodeBoolAppend]
  simp [boolFieldBits, cellFieldBits,
    MachineDescription.encodeCodeWordAsInput]

theorem outputSuffix_true
    (L : MachineDescription.DovetailLayout) :
    outputSuffix true L =
      MachineDescription.encodeNatAppend L.stage
        (MachineDescription.encodeConfigurationAppend L.acceptConfig
          (MachineDescription.encodeBoolAppend L.acceptHit [])) := by
  rfl

theorem outputSuffix_false
    (L : MachineDescription.DovetailLayout) :
    outputSuffix false L =
      MachineDescription.encodeNatAppend L.stage
        (MachineDescription.encodeConfigurationAppend L.rejectConfig
          (MachineDescription.encodeBoolAppend L.rejectHit [])) := by
  rfl

theorem outputBits_true_eq_fields
    (L : MachineDescription.DovetailLayout) :
    outputBits true L =
      List.append (stageNatBits L.stage)
        (configurationFieldBits L.acceptConfig
          (boolFieldBits L.acceptHit [])) := by
  simpa [outputFieldBits] using outputBits_eq_fields true L

theorem outputBits_false_eq_fields
    (L : MachineDescription.DovetailLayout) :
    outputBits false L =
      List.append (stageNatBits L.stage)
        (configurationFieldBits L.rejectConfig
          (boolFieldBits L.rejectHit [])) := by
  simpa [outputFieldBits] using outputBits_eq_fields false L

theorem selectedProjectionSimulatorLayout_eq_fields
    (useAccept : Bool)
    (L : MachineDescription.DovetailLayout) :
    SelectedProjectionSimulatorLayout useAccept L =
      { input := ParsedLayoutBits L
        stage := L.stage
        config := selectedConfig useAccept L
        hit := selectedHit useAccept L } := by
  cases useAccept <;>
    rfl

theorem simulatorLayout_encode_eq_header_input_outputSuffix
    (useAccept : Bool)
    (L : MachineDescription.DovetailLayout) :
    MachineDescription.SimulatorLayout.encode
        (SelectedProjectionSimulatorLayout useAccept L) =
      MachineCodeSymbol.header ::
        MachineDescription.encodeBoolWordAppend (ParsedLayoutBits L)
          (outputSuffix useAccept L) := by
  rw [selectedProjectionSimulatorLayout_eq_fields]
  rfl

theorem simulatorLayout_asBoolInput_eq_header_input_outputSuffix
    (useAccept : Bool)
    (L : MachineDescription.DovetailLayout) :
    MachineDescription.SimulatorLayout.asBoolInput
        (SelectedProjectionSimulatorLayout useAccept L) =
      MachineDescription.encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          MachineDescription.encodeBoolWordAppend (ParsedLayoutBits L)
            (outputSuffix useAccept L)) := by
  rw [MachineDescription.SimulatorLayout.asBoolInput]
  rw [simulatorLayout_encode_eq_header_input_outputSuffix]

theorem simulatorLayout_asBoolInput_eq_outputAllBits
    (useAccept : Bool)
    (L : MachineDescription.DovetailLayout) :
    MachineDescription.SimulatorLayout.asBoolInput
        (SelectedProjectionSimulatorLayout useAccept L) =
      outputAllBits useAccept L := by
  rw [simulatorLayout_asBoolInput_eq_header_input_outputSuffix]
  unfold outputAllBits outputPrefixBits outputBits
  have happend :
      MachineDescription.encodeBoolWordAppend
          (ParsedLayoutBits L) (outputSuffix useAccept L) =
        List.append
          (MachineDescription.encodeBoolWordAppend
            (ParsedLayoutBits L) [])
          (outputSuffix useAccept L) := by
    simpa using
      encodeBoolWordAppend_append (ParsedLayoutBits L)
        ([] : Word MachineCodeSymbol) (outputSuffix useAccept L)
  rw [happend]
  simp only [MachineDescription.encodeCodeWordAsInput]
  rw [MachineDescription.encodeCodeWordAsInput_append]
  simp [List.append_assoc]

def outputTape
    (useAccept : Bool)
    (L : MachineDescription.DovetailLayout)
    (baseLeft : List (Option Bool)) : Tape Bool :=
  tapeAtCells baseLeft ((outputBits useAccept L).map some)

theorem outputTape_eq_fields
    (useAccept : Bool)
    (L : MachineDescription.DovetailLayout)
    (baseLeft : List (Option Bool)) :
    outputTape useAccept L baseLeft =
      tapeAtCells baseLeft
        ((outputFieldBits useAccept L).map some) := by
  rw [outputTape, outputBits_eq_fields]

theorem stageNatBits_cons_cons
    (n : Nat) :
    exists first : Bool,
    exists second : Bool,
    exists rest : Word Bool,
      stageNatBits n = first :: second :: rest := by
  cases n with
  | zero =>
      exact ⟨false, false, [true, true], by simp [stageNatBits_zero]⟩
  | succ n =>
      exact
        ⟨false, false, true :: false :: stageNatBits n,
          by simp [stageNatBits_succ]⟩

theorem sourceTape_move_left_move_right
    (L : MachineDescription.DovetailLayout)
    (baseLeft : List (Option Bool)) :
    Tape.move Direction.left (Tape.move Direction.right
      (sourceTape L baseLeft)) =
        sourceTape L baseLeft := by
  rcases stageNatBits_cons_cons L.stage with
    ⟨first, second, rest, hstage⟩
  rw [sourceTape, sourceFieldBits, hstage]
  simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem outputTape_move_left_move_right
    (useAccept : Bool)
    (L : MachineDescription.DovetailLayout)
    (baseLeft : List (Option Bool)) :
    Tape.move Direction.left (Tape.move Direction.right
      (outputTape useAccept L baseLeft)) =
        outputTape useAccept L baseLeft := by
  rcases stageNatBits_cons_cons L.stage with
    ⟨first, second, rest, hstage⟩
  rw [outputTape_eq_fields, outputFieldBits, hstage]
  simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

end SelectedProjectionTailProjector
end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
