import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.Basic
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.Main

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

def SelectedMergeEquivEmitterPaddedOutputTape
    (useAccept : Bool)
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  ScratchPaddedOutputTape
    (fun p : SelectedMergeEmitterPayload =>
      encodeCodeWordAsInput
        (SelectedMergeOutputCode useAccept p.S p.L))
    (fun p : SelectedMergeEmitterPayload =>
      (SimulatorLayout.asBoolInput p.S).length)
    p

theorem SelectedMergeEquivEmitterPaddedOutputTape_equiv
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    Tape.Equiv
      (SelectedMergeEquivEmitterPaddedOutputTape useAccept p)
      (SelectedMergeEquivOutputTape useAccept p.S p.L) := by
  simpa [SelectedMergeEquivEmitterPaddedOutputTape,
    SelectedMergeEquivOutputTape, ScratchPaddedOutputTape] using
    inputWithTrailingBlankPadding_equiv_input
      (encodeCodeWordAsInput
        (SelectedMergeOutputCode useAccept p.S p.L))
      (SimulatorLayout.asBoolInput p.S).length

theorem SelectedMergeEquivEmitterPaddedOutputTape_normalizedOutput
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergeEquivEmitterPaddedOutputTape useAccept p) =
      encodeCodeWordAsInput
        (SelectedMergeOutputCode useAccept p.S p.L) := by
  simpa [SelectedMergeEquivEmitterPaddedOutputTape,
    ScratchPaddedOutputTape] using
    inputWithTrailingBlankPadding_normalizedOutput
      (encodeCodeWordAsInput
        (SelectedMergeOutputCode useAccept p.S p.L))
      (SimulatorLayout.asBoolInput p.S).length

theorem SelectedMergeEquivEmitterPaddedOutputTape_contextLength_ge_input
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    Tape.contextLength (SimulatorLayout.tape p.S) <=
      Tape.contextLength
        (SelectedMergeEquivEmitterPaddedOutputTape useAccept p) := by
  simpa [SelectedMergeEquivEmitterPaddedOutputTape,
    ScratchPaddedOutputTape, SimulatorLayout.tape] using
    inputWithTrailingBlankPadding_contextLength_ge_input
      (encodeCodeWordAsInput
        (SelectedMergeOutputCode useAccept p.S p.L))
      (SimulatorLayout.asBoolInput p.S)

theorem SelectedMergeEmitterInputTape_normalizedOutput
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput (SimulatorLayout.tape p.S) =
      SelectedMergeEmitterInputBits p := by
  simpa [SelectedMergeEmitterInputBits] using
    SimulatorLayout.tape_normalizedOutput p.S

theorem SelectedMergeEmitterPayload.input_eq_encodeCodeWordAsInput
    (p : SelectedMergeEmitterPayload) :
    p.S.input =
      encodeCodeWordAsInput
        (DovetailLayout.encode p.L) :=
  decodeCodeWordAsInput_eq_some_encodeCodeWordAsInput
    p.input

theorem SelectedMergeEmitterPayload.input_eq_parsedLayoutBits
    (p : SelectedMergeEmitterPayload) :
    p.S.input = ParsedLayoutBits p.L := by
  rw [SelectedMergeEmitterPayload.input_eq_encodeCodeWordAsInput,
    ParsedLayoutBits]

theorem SelectedMergeEmitterInputBits_eq_fields
    (p : SelectedMergeEmitterPayload) :
    SelectedMergeEmitterInputBits p =
      encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          encodeBoolWordAppend
            (encodeCodeWordAsInput
              (DovetailLayout.encode p.L))
            (encodeNatAppend p.S.stage
              (encodeConfigurationAppend p.S.config
                (encodeBoolAppend p.S.hit [])))) := by
  rw [SelectedMergeEmitterInputBits,
    SimulatorLayout.asBoolInput,
    SimulatorLayout.encode,
    SimulatorLayout.encodeAppend,
    SelectedMergeEmitterPayload.input_eq_encodeCodeWordAsInput]

theorem SelectedMergeEmitterInputTape_normalizedOutput_eq_fields
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput (SimulatorLayout.tape p.S) =
      encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          encodeBoolWordAppend
            (encodeCodeWordAsInput
              (DovetailLayout.encode p.L))
            (encodeNatAppend p.S.stage
              (encodeConfigurationAppend p.S.config
                (encodeBoolAppend p.S.hit [])))) := by
  rw [SelectedMergeEmitterInputTape_normalizedOutput,
    SelectedMergeEmitterInputBits_eq_fields]

theorem SelectedMergeEmitterInputBits_eq_parsedLayoutFields
    (p : SelectedMergeEmitterPayload) :
    SelectedMergeEmitterInputBits p =
      encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          encodeBoolWordAppend (ParsedLayoutBits p.L)
            (encodeNatAppend p.S.stage
              (encodeConfigurationAppend p.S.config
                (encodeBoolAppend p.S.hit [])))) := by
  simpa [ParsedLayoutBits] using
    SelectedMergeEmitterInputBits_eq_fields p

theorem SelectedMergeEmitterInputTape_normalizedOutput_eq_parsedLayoutFields
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput (SimulatorLayout.tape p.S) =
      encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          encodeBoolWordAppend (ParsedLayoutBits p.L)
            (encodeNatAppend p.S.stage
              (encodeConfigurationAppend p.S.config
                (encodeBoolAppend p.S.hit [])))) := by
  rw [SelectedMergeEmitterInputTape_normalizedOutput,
    SelectedMergeEmitterInputBits_eq_parsedLayoutFields]

theorem SelectedMergeEquivEmitterPaddedOutputTape_contextLength_ge_inputBits
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    Tape.contextLength (Tape.input (SelectedMergeEmitterInputBits p)) <=
      Tape.contextLength
        (SelectedMergeEquivEmitterPaddedOutputTape useAccept p) := by
  simpa [SelectedMergeEmitterInputBits,
    SimulatorLayout.tape] using
    SelectedMergeEquivEmitterPaddedOutputTape_contextLength_ge_input
      useAccept p

def SelectedMergePaddedEmitterExactShapeSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      emitter.HaltsFromTape
        (SimulatorLayout.tape p.S)
        (SelectedMergeEquivEmitterPaddedOutputTape useAccept p)

def SelectedMergePaddedEmitterExactShapeConstruction : Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedMergePaddedEmitterExactShapeSpec useAccept emitter

def SelectedMergeEquivPaddedEmitterSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  ScratchPaddedEmitterSpec
    (fun p : SelectedMergeEmitterPayload =>
      SimulatorLayout.tape p.S)
    (fun p : SelectedMergeEmitterPayload =>
      encodeCodeWordAsInput
        (SelectedMergeOutputCode useAccept p.S p.L))
    (fun p : SelectedMergeEmitterPayload =>
      (SimulatorLayout.asBoolInput p.S).length)
    (fun p : SelectedMergeEmitterPayload =>
      SelectedMergeEquivOutputTape useAccept p.S p.L)
    emitter

def SelectedMergeEquivPaddedEmitterConstruction : Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedMergeEquivPaddedEmitterSpec useAccept emitter

theorem selectedMergeEquivPaddedEmitterSpec_of_exactShape
    {useAccept : Bool} {emitter : MachineDescription}
    (hemits :
      SelectedMergePaddedEmitterExactShapeSpec useAccept emitter) :
    SelectedMergeEquivPaddedEmitterSpec useAccept emitter := by
  constructor
  · exact hemits.left
  constructor
  · intro p
    simpa [SelectedMergeEquivPaddedEmitterSpec,
      SelectedMergeEquivEmitterPaddedOutputTape] using
      hemits.right p
  · intro p
    exact SelectedMergeEquivEmitterPaddedOutputTape_equiv useAccept p

theorem selectedMergeEquivPaddedEmitterConstruction_of_exactShape
    (hemits : SelectedMergePaddedEmitterExactShapeConstruction) :
    SelectedMergeEquivPaddedEmitterConstruction := by
  intro useAccept
  rcases hemits useAccept with ⟨emitter, hemits⟩
  exact
    ⟨emitter,
      selectedMergeEquivPaddedEmitterSpec_of_exactShape hemits⟩

theorem selectedMergeEquivEmitterSpec_of_padded
    {useAccept : Bool} {emitter : MachineDescription}
    (hemits : SelectedMergeEquivPaddedEmitterSpec useAccept emitter) :
    SelectedMergeEquivEmitterSpec useAccept emitter := by
  constructor
  · exact hemits.left
  · intro p
    exact PaddedEquivEmitterSpec.haltsFromTapeEquiv hemits p

theorem selectedMergeEquivEmitterConstruction_of_padded
    (h : SelectedMergeEquivPaddedEmitterConstruction) :
    SelectedMergeEquivEmitterConstruction := by
  intro useAccept
  rcases h useAccept with ⟨emitter, hemits⟩
  exact ⟨emitter, selectedMergeEquivEmitterSpec_of_padded hemits⟩

theorem selectedMergeEquivSpec_of_forwardParser_emitter
    {useAccept : Bool} {parser emitter : MachineDescription}
    (hparser : SelectedMergeForwardParserSpec parser)
    (hemitter : SelectedMergeEquivEmitterSpec useAccept emitter) :
    SelectedMergeEquivSpec useAccept
      (SeqViaCanonical parser emitter) := by
  have hrunnerReady :
      (SeqViaCanonical parser emitter).SubroutineReady :=
    SeqViaCanonical_subroutineReady hparser.left hemitter.left
  constructor
  · exact hrunnerReady
  constructor
  · intro S L hinput
    have hparserRun :
        parser.HaltsFromTapeEquiv
          (SimulatorLayout.tape S)
          (SimulatorLayout.tape S) := by
        have hrun :
          parser.HaltsFromTape
            (SimulatorLayout.tape S)
            (SimulatorLayout.tape S) := by
          simpa [SimulatorLayout.tape,
            HaltsWithTape,
            HaltsFromTape,
            HaltsWithTapeIn,
            HaltsFromTapeIn,
            initial] using
            hparser.right S L hinput
        exact HaltsFromTape.toEquiv hrun
    have hbridge :
        Tape.Equiv
          (Tape.move Direction.left
            (Tape.move Direction.right
              (SimulatorLayout.tape S)))
          (Tape.input (SimulatorLayout.asBoolInput S)) := by
      rw [simulatorLayoutTape_move_left_move_right S]
      exact Tape.Equiv.refl _
    have hemits :=
      hemitter.right { S := S, L := L, input := hinput }
    exact
      SeqViaCanonical_haltsFromTapeEquiv_of_equiv
        hparser.left hemitter.left hparserRun hbridge
        (by simpa [SimulatorLayout.tape] using hemits)
  · intro S L hinput T hhalt
    have hforward :
        (SeqViaCanonical parser emitter).HaltsFromTapeEquiv
          (SimulatorLayout.tape S)
          (SelectedMergeEquivOutputTape useAccept S L) := by
      have hparserRun :
          parser.HaltsFromTapeEquiv
            (SimulatorLayout.tape S)
            (SimulatorLayout.tape S) := by
        have hrun :
            parser.HaltsFromTape
              (SimulatorLayout.tape S)
              (SimulatorLayout.tape S) := by
          simpa [SimulatorLayout.tape,
            HaltsWithTape, HaltsFromTape,
            HaltsWithTapeIn,
            HaltsFromTapeIn,
            initial] using
            hparser.right S L hinput
        exact HaltsFromTape.toEquiv hrun
      have hbridge :
          Tape.Equiv
            (Tape.move Direction.left
              (Tape.move Direction.right
                (SimulatorLayout.tape S)))
            (Tape.input (SimulatorLayout.asBoolInput S)) := by
        rw [simulatorLayoutTape_move_left_move_right S]
        exact Tape.Equiv.refl _
      have hemits :=
        hemitter.right { S := S, L := L, input := hinput }
      exact
        SeqViaCanonical_haltsFromTapeEquiv_of_equiv
          hparser.left hemitter.left hparserRun hbridge
          (by simpa [SimulatorLayout.tape] using hemits)
    rcases hforward with ⟨Tactual, hactual, hequiv⟩
    have hT_eq : T = Tactual :=
      haltsFromTape_functional_of_haltTransitionFree
        hrunnerReady.right hhalt hactual
    rw [hT_eq]
    exact hequiv

theorem selectedMergeEquivSpec_of_parser_emitter
    {useAccept : Bool} {parser emitter : MachineDescription}
    (hparser : SelectedMergeParserSpec parser)
    (hemitter : SelectedMergeEquivEmitterSpec useAccept emitter) :
    SelectedMergeEquivSpec useAccept
      (SeqViaCanonical parser emitter) := by
  exact
    selectedMergeEquivSpec_of_forwardParser_emitter
      (selectedMergeForwardParserSpec_of_parser hparser)
      hemitter

theorem selectedMergeEquivConstruction_of_parser_emitter
    (hparser : SelectedMergeParserConstruction)
    (hemitter : SelectedMergeEquivEmitterConstruction) :
    SelectedMergeEquivConstruction := by
  intro useAccept
  rcases hparser with ⟨parser, hparser⟩
  rcases hemitter useAccept with ⟨emitter, hemits⟩
  exact
    ⟨SeqViaCanonical parser emitter,
      selectedMergeEquivSpec_of_parser_emitter hparser hemits⟩

theorem selectedMergeEquivConstruction_of_forwardParser_emitter
    (hparser : SelectedMergeForwardParserConstruction)
    (hemitter : SelectedMergeEquivEmitterConstruction) :
    SelectedMergeEquivConstruction := by
  intro useAccept
  rcases hparser with ⟨parser, hparser⟩
  rcases hemitter useAccept with ⟨emitter, hemits⟩
  exact
    ⟨SeqViaCanonical parser emitter,
      selectedMergeEquivSpec_of_forwardParser_emitter hparser hemits⟩

theorem selectedMergeEquivSpec_of_forwardParser_paddedEmitter
    {useAccept : Bool} {parser emitter : MachineDescription}
    (hparser : SelectedMergeForwardParserSpec parser)
    (hemitter : SelectedMergeEquivPaddedEmitterSpec useAccept emitter) :
    SelectedMergeEquivSpec useAccept
      (SeqViaCanonical parser emitter) :=
  selectedMergeEquivSpec_of_forwardParser_emitter hparser
    (selectedMergeEquivEmitterSpec_of_padded hemitter)

theorem selectedMergeEquivConstruction_of_forwardParser_paddedEmitter
    (hparser : SelectedMergeForwardParserConstruction)
    (hemitter : SelectedMergeEquivPaddedEmitterConstruction) :
    SelectedMergeEquivConstruction := by
  intro useAccept
  rcases hparser with ⟨parser, hparser⟩
  rcases hemitter useAccept with ⟨emitter, hemits⟩
  exact
    ⟨SeqViaCanonical parser emitter,
      selectedMergeEquivSpec_of_forwardParser_paddedEmitter
        hparser hemits⟩

def SelectedMergeCanonicalEmitterConstruction : Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedMergeCanonicalEmitterSpec useAccept emitter

def SelectedMergeCanonicalExactEmitterConstruction : Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedMergeCanonicalExactEmitterSpec useAccept emitter

def SelectedMergeCanonicalEmitterFromExact
    (emitter : MachineDescription) : MachineDescription :=
  seqSubroutine
    emitter ExactIdentityDescription Direction.right

theorem selectedMergeCanonicalEmitterSpec_of_exact
    {useAccept : Bool} {emitter : MachineDescription}
    (hemits :
      SelectedMergeCanonicalExactEmitterSpec useAccept emitter) :
    SelectedMergeCanonicalEmitterSpec useAccept
      (SelectedMergeCanonicalEmitterFromExact emitter) := by
  let identity := ExactIdentityDescription
  have hid : identity.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  constructor
  · exact
      seqSubroutine_subroutineReady
        hemits.left hid
  constructor
  · intro p
    simpa [SelectedMergeCanonicalEmitterFromExact,
      SelectedMergeCanonicalEmitterSpec,
      SelectedMergeCanonicalExactEmitterSpec,
      CanonicalLayouts.OutputTape, CanonicalLayouts.ExactOutputTape,
      identity] using
      seqSubroutine_haltsWithTape_of_haltsWithTape
        (A := emitter) (B := identity) (handoffMove := Direction.right)
        hemits.left hid (hemits.right.left p)
        (CommonGround.Identity.exactIdentityDescription_run_from_start
          (Tape.move Direction.right
            (CanonicalLayouts.ExactOutputTape
              (SelectedMergeEmitterOutputCode useAccept) p)))
  · intro p T hhalt
    rcases
        seqSubroutine_haltsWithTape_inv
          (A := emitter) (B := identity) (handoffMove := Direction.right)
          hemits.left hid
          (by
            simpa [SelectedMergeCanonicalEmitterFromExact, identity]
              using hhalt) with
      ⟨Tmid, hemitsRun, hidentityReach⟩
    have hTmid :
        Tmid =
          CanonicalLayouts.ExactOutputTape
            (SelectedMergeEmitterOutputCode useAccept) p :=
      hemits.right.right p Tmid hemitsRun
    rcases hidentityReach with ⟨n, hn⟩
    have hrun :=
      CommonGround.Identity.exactIdentityDescription_runConfig_from_start
        n (Tape.move Direction.right Tmid)
    rw [hrun] at hn
    have htape :
        Tape.move Direction.right Tmid = T :=
      congrArg Configuration.tape hn
    rw [hTmid] at htape
    simpa [CanonicalLayouts.OutputTape,
      CanonicalLayouts.ExactOutputTape] using htape.symm

theorem selectedMergeCanonicalEmitterConstruction_of_exact
    (hexact : SelectedMergeCanonicalExactEmitterConstruction) :
    SelectedMergeCanonicalEmitterConstruction := by
  intro useAccept
  rcases hexact useAccept with ⟨emitter, hemits⟩
  exact
    ⟨SelectedMergeCanonicalEmitterFromExact emitter,
      selectedMergeCanonicalEmitterSpec_of_exact hemits⟩

theorem selectedMergeEmitterConstruction_of_canonical
    (hcanonical : SelectedMergeCanonicalEmitterConstruction) :
    SelectedMergeEmitterConstruction := by
  intro useAccept
  rcases hcanonical useAccept with ⟨emitter, hemits⟩
  exact
    ⟨emitter,
      (selectedMergeEmitterSpec_iff_canonical useAccept emitter).mpr
        hemits⟩

def SelectedMergeOutputAcceptConfig
    (useAccept : Bool)
    (S : SimulatorLayout)
    (L : DovetailLayout) :
    Configuration :=
  if useAccept then S.config else L.acceptConfig

def SelectedMergeOutputRejectConfig
    (useAccept : Bool)
    (S : SimulatorLayout)
    (L : DovetailLayout) :
    Configuration :=
  if useAccept then L.rejectConfig else S.config

def SelectedMergeOutputAcceptHit
    (useAccept : Bool)
    (S : SimulatorLayout)
    (L : DovetailLayout) : Bool :=
  if useAccept then S.hit else L.acceptHit

def SelectedMergeOutputRejectHit
    (useAccept : Bool)
    (S : SimulatorLayout)
    (L : DovetailLayout) : Bool :=
  if useAccept then L.rejectHit else S.hit

def SelectedMergeOutputLayout
    (useAccept : Bool)
    (S : SimulatorLayout)
    (L : DovetailLayout) :
    DovetailLayout :=
  if useAccept then
    { L with
      acceptConfig := S.config
      acceptHit := S.hit }
  else
    { L with
      rejectConfig := S.config
      rejectHit := S.hit }

theorem selectedMergeOutputCode_eq_outputLayout
    (useAccept : Bool)
    (S : SimulatorLayout)
    (L : DovetailLayout) :
    SelectedMergeOutputCode useAccept S L =
      DovetailLayout.encode
        (SelectedMergeOutputLayout useAccept S L) := by
  cases useAccept <;>
    rfl

theorem selectedMergeOutputCode_eq_fields
    (useAccept : Bool)
    (S : SimulatorLayout)
    (L : DovetailLayout) :
    SelectedMergeOutputCode useAccept S L =
      MachineCodeSymbol.transition ::
        encodeBoolWordAppend L.input
          (encodeNatAppend L.stage
            (encodeConfigurationAppend
              (SelectedMergeOutputAcceptConfig useAccept S L)
              (encodeConfigurationAppend
                (SelectedMergeOutputRejectConfig useAccept S L)
                (encodeBoolAppend
                  (SelectedMergeOutputAcceptHit useAccept S L)
                  (encodeBoolAppend
                    (SelectedMergeOutputRejectHit useAccept S L) []))))) := by
  cases useAccept <;>
    rfl

theorem SelectedMergeEquivEmitterPaddedOutputTape_normalizedOutput_eq_fields
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergeEquivEmitterPaddedOutputTape useAccept p) =
      encodeCodeWordAsInput
        (MachineCodeSymbol.transition ::
          encodeBoolWordAppend p.L.input
            (encodeNatAppend p.L.stage
              (encodeConfigurationAppend
                (SelectedMergeOutputAcceptConfig useAccept p.S p.L)
                (encodeConfigurationAppend
                  (SelectedMergeOutputRejectConfig useAccept p.S p.L)
                  (encodeBoolAppend
                    (SelectedMergeOutputAcceptHit useAccept p.S p.L)
                    (encodeBoolAppend
                      (SelectedMergeOutputRejectHit useAccept p.S p.L)
                      [])))))) := by
  rw [SelectedMergeEquivEmitterPaddedOutputTape_normalizedOutput,
    selectedMergeOutputCode_eq_fields]

theorem SelectedMergeEquivEmitterPaddedOutputTape_eq_fields
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    SelectedMergeEquivEmitterPaddedOutputTape useAccept p =
      inputWithTrailingBlankPadding
        (encodeCodeWordAsInput
          (MachineCodeSymbol.transition ::
            encodeBoolWordAppend p.L.input
              (encodeNatAppend p.L.stage
                (encodeConfigurationAppend
                  (SelectedMergeOutputAcceptConfig useAccept p.S p.L)
                  (encodeConfigurationAppend
                    (SelectedMergeOutputRejectConfig useAccept p.S p.L)
                    (encodeBoolAppend
                      (SelectedMergeOutputAcceptHit useAccept p.S p.L)
                      (encodeBoolAppend
                        (SelectedMergeOutputRejectHit useAccept p.S p.L)
                        [])))))))
        (SimulatorLayout.asBoolInput p.S).length := by
  simp [SelectedMergeEquivEmitterPaddedOutputTape,
    ScratchPaddedOutputTape, selectedMergeOutputCode_eq_fields]

theorem SelectedMergeEquivEmitterPaddedOutputTape_eq_tapeAtCells_fields
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    SelectedMergeEquivEmitterPaddedOutputTape useAccept p =
      DovetailInitialLayoutInitializer.tapeAtCells []
        (inputWithTrailingBlankPaddingCells
          (encodeCodeWordAsInput
            (MachineCodeSymbol.transition ::
              encodeBoolWordAppend p.L.input
                (encodeNatAppend p.L.stage
                  (encodeConfigurationAppend
                    (SelectedMergeOutputAcceptConfig useAccept p.S p.L)
                    (encodeConfigurationAppend
                      (SelectedMergeOutputRejectConfig useAccept p.S p.L)
                      (encodeBoolAppend
                        (SelectedMergeOutputAcceptHit useAccept p.S p.L)
                        (encodeBoolAppend
                          (SelectedMergeOutputRejectHit useAccept p.S p.L)
                          [])))))))
          (SimulatorLayout.asBoolInput p.S).length) := by
  rw [SelectedMergeEquivEmitterPaddedOutputTape_eq_fields]
  exact
    inputWithTrailingBlankPadding_eq_tapeAtCells
      (encodeCodeWordAsInput
        (MachineCodeSymbol.transition ::
          encodeBoolWordAppend p.L.input
            (encodeNatAppend p.L.stage
              (encodeConfigurationAppend
                (SelectedMergeOutputAcceptConfig useAccept p.S p.L)
                (encodeConfigurationAppend
                  (SelectedMergeOutputRejectConfig useAccept p.S p.L)
                  (encodeBoolAppend
                    (SelectedMergeOutputAcceptHit useAccept p.S p.L)
                    (encodeBoolAppend
                      (SelectedMergeOutputRejectHit useAccept p.S p.L)
                      [])))))))
      (SimulatorLayout.asBoolInput p.S).length

theorem
    SelectedMergeEquivEmitterPaddedOutputTape_normalizedOutput_eq_parsedLayoutBits
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergeEquivEmitterPaddedOutputTape useAccept p) =
      ParsedLayoutBits (SelectedMergeOutputLayout useAccept p.S p.L) := by
  rw [SelectedMergeEquivEmitterPaddedOutputTape_normalizedOutput,
    selectedMergeOutputCode_eq_outputLayout, ParsedLayoutBits]

theorem SelectedMergeEquivEmitterPaddedOutputTape_equiv_parsedLayoutTape
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    Tape.Equiv
      (SelectedMergeEquivEmitterPaddedOutputTape useAccept p)
      (ParsedLayoutTape (SelectedMergeOutputLayout useAccept p.S p.L)) := by
  simpa [SelectedMergeEquivEmitterPaddedOutputTape, ParsedLayoutTape,
    ParsedLayoutBits, ScratchPaddedOutputTape,
    selectedMergeOutputCode_eq_outputLayout] using
    inputWithTrailingBlankPadding_equiv_input
      (encodeCodeWordAsInput
        (SelectedMergeOutputCode useAccept p.S p.L))
      (SimulatorLayout.asBoolInput p.S).length

theorem selectedMergeOutputLayout_accept_run
    (accept : MachineDescription) (L : DovetailLayout) :
    SelectedMergeOutputLayout true
        (SimulatorLayout.run
          accept L.stage (AcceptSimulatorLayout L)) L =
      ConfigRunnerAfterAccept accept L := by
  simp [SelectedMergeOutputLayout, ConfigRunnerAfterAccept,
    AcceptSimulatorLayout, SimulatorLayout.run]

theorem selectedMergeOutputLayout_reject_run
    (reject : MachineDescription) (L : DovetailLayout) :
    SelectedMergeOutputLayout false
        (SimulatorLayout.run
          reject L.stage (RejectSimulatorLayout L)) L =
      ConfigRunnerAfterReject reject L := by
  simp [SelectedMergeOutputLayout, ConfigRunnerAfterReject,
    RejectSimulatorLayout, SimulatorLayout.run]

theorem
    SelectedMergeEquivEmitterPaddedOutputTape_normalizedOutput_accept_run
    (accept : MachineDescription) (L : DovetailLayout) :
    Tape.normalizedOutput
        (SelectedMergeEquivEmitterPaddedOutputTape true
          { S :=
              SimulatorLayout.run
                accept L.stage (AcceptSimulatorLayout L)
            L := L
            input := by
              simpa [AcceptSimulatorLayout,
                SimulatorLayout.run] using
                decodeCodeWordAsInput_parsedLayoutBits L }) =
      ParsedLayoutBits (ConfigRunnerAfterAccept accept L) := by
  rw [SelectedMergeEquivEmitterPaddedOutputTape_normalizedOutput_eq_parsedLayoutBits]
  rw [selectedMergeOutputLayout_accept_run]

theorem SelectedMergeEquivEmitterPaddedOutputTape_equiv_accept_run
    (accept : MachineDescription) (L : DovetailLayout) :
    Tape.Equiv
        (SelectedMergeEquivEmitterPaddedOutputTape true
          { S :=
              SimulatorLayout.run
                accept L.stage (AcceptSimulatorLayout L)
            L := L
            input := by
              simpa [AcceptSimulatorLayout,
                SimulatorLayout.run] using
                decodeCodeWordAsInput_parsedLayoutBits L })
        (ParsedLayoutTape (ConfigRunnerAfterAccept accept L)) := by
  simpa [selectedMergeOutputLayout_accept_run] using
    SelectedMergeEquivEmitterPaddedOutputTape_equiv_parsedLayoutTape
      true
      { S :=
          SimulatorLayout.run
            accept L.stage (AcceptSimulatorLayout L)
        L := L
        input := by
          simpa [AcceptSimulatorLayout,
            SimulatorLayout.run] using
            decodeCodeWordAsInput_parsedLayoutBits L }

theorem
    SelectedMergeEquivEmitterPaddedOutputTape_normalizedOutput_reject_run
    (reject : MachineDescription) (L : DovetailLayout) :
    Tape.normalizedOutput
        (SelectedMergeEquivEmitterPaddedOutputTape false
          { S :=
              SimulatorLayout.run
                reject L.stage (RejectSimulatorLayout L)
            L := L
            input := by
              simpa [RejectSimulatorLayout,
                SimulatorLayout.run] using
                decodeCodeWordAsInput_parsedLayoutBits L }) =
      ParsedLayoutBits (ConfigRunnerAfterReject reject L) := by
  rw [SelectedMergeEquivEmitterPaddedOutputTape_normalizedOutput_eq_parsedLayoutBits]
  rw [selectedMergeOutputLayout_reject_run]

theorem SelectedMergeEquivEmitterPaddedOutputTape_equiv_reject_run
    (reject : MachineDescription) (L : DovetailLayout) :
    Tape.Equiv
        (SelectedMergeEquivEmitterPaddedOutputTape false
          { S :=
              SimulatorLayout.run
                reject L.stage (RejectSimulatorLayout L)
            L := L
            input := by
              simpa [RejectSimulatorLayout,
                SimulatorLayout.run] using
                decodeCodeWordAsInput_parsedLayoutBits L })
        (ParsedLayoutTape (ConfigRunnerAfterReject reject L)) := by
  simpa [selectedMergeOutputLayout_reject_run] using
    SelectedMergeEquivEmitterPaddedOutputTape_equiv_parsedLayoutTape
      false
      { S :=
          SimulatorLayout.run
            reject L.stage (RejectSimulatorLayout L)
        L := L
        input := by
          simpa [RejectSimulatorLayout,
            SimulatorLayout.run] using
            decodeCodeWordAsInput_parsedLayoutBits L }


theorem selectedMergeSpec_of_parser_emitter
    {useAccept : Bool} {parser emitter : MachineDescription}
    (hparser : SelectedMergeParserSpec parser)
    (hemitter : SelectedMergeEmitterSpec useAccept emitter) :
    SelectedMergeSpec useAccept
      (SeqViaCanonical parser emitter) := by
  have hrunnerReady :
      (SeqViaCanonical parser emitter).SubroutineReady :=
    SeqViaCanonical_subroutineReady hparser.left hemitter.left
  constructor
  · exact hrunnerReady
  constructor
  · intro S L hinput
    exact
      SeqViaCanonical_haltsWithTape_of_haltsWithTape
        hparser.left hemitter.left
        (hparser.right.left S L hinput)
        (simulatorLayoutTape_move_left_move_right S)
        (hemitter.right.left S L hinput)
  · intro code T hhalt
    let identity := ExactIdentityDescription
    have hid : identity.SubroutineReady :=
      CommonGround.Identity.exactIdentityDescription_subroutineReady
    rcases
        seqSubroutine_haltsWithTape_inv
          (A := seqSubroutine
            parser identity Direction.right)
          (B := emitter)
          (handoffMove := Direction.left)
          (seqSubroutine_subroutineReady
            hparser.left hid)
          hemitter.left
          (by simpa [SeqViaCanonical, identity] using hhalt) with
      ⟨Tmid, hparserIdHalt, _hemitterReach⟩
    rcases
        seqSubroutine_haltsWithTape_inv
          (A := parser) (B := identity)
          (handoffMove := Direction.right)
          hparser.left hid
          (by simpa [identity] using hparserIdHalt) with
      ⟨Tparser, hparserHalt, _hidentityReach⟩
    rcases hparser.right.right code Tparser hparserHalt with
      ⟨S, L, hcode, hinput, _hTparser⟩
    refine ⟨S, L, hcode, hinput, ?_⟩
    have hhalt' :
        (SeqViaCanonical parser emitter).HaltsWithTape
          (SimulatorLayout.asBoolInput S) T := by
      simpa [SimulatorLayout.asBoolInput, hcode] using
        hhalt
    have hforward :
        (SeqViaCanonical parser emitter).HaltsWithTape
          (SimulatorLayout.asBoolInput S)
          (SelectedMergeOutputTape useAccept S L) :=
      SeqViaCanonical_haltsWithTape_of_haltsWithTape
        hparser.left hemitter.left
        (hparser.right.left S L hinput)
        (simulatorLayoutTape_move_left_move_right S)
        (hemitter.right.left S L hinput)
    exact
      MachineDescription.haltsWithTape_functional_of_haltTransitionFree
        hrunnerReady.right hhalt' hforward

theorem selectedMergeFiniteDescriptionConstruction_of_parser_emitter
    (hparser : SelectedMergeParserConstruction)
    (hemitter : SelectedMergeEmitterConstruction) :
    SelectedMergeFiniteDescriptionConstruction := by
  intro useAccept
  rcases hparser with ⟨parser, hparser⟩
  rcases hemitter useAccept with ⟨emitter, hemits⟩
  exact
    ⟨SeqViaCanonical parser emitter,
      selectedMergeSpec_of_parser_emitter hparser hemits⟩

/--
Forward-only parser used by the live equivalence merge construction.  Since the
phase contract starts from a known canonical simulator layout, exact identity is
enough to hand the unchanged tape to the emitter.  The stronger parser
scaffolds below are only for APIs that also need closed input-field validation.
-/
theorem selectedMergeForwardParserConstruction_scaffold :
    SelectedMergeForwardParserConstruction :=
  selectedMergeForwardParserConstruction_identity


end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
