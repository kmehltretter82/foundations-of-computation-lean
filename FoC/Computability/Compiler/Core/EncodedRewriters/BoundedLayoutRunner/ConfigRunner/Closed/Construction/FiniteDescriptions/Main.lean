import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.FiniteDescriptions.ProjectionPadded

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace BoundedLayoutRunner

def SelectedMergeEquivEmitterPaddedOutputTape
    (useAccept : Bool)
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  inputWithTrailingBlankPadding
    (MachineDescription.encodeCodeWordAsInput
      (SelectedMergeOutputCode useAccept p.S p.L))
    (MachineDescription.SimulatorLayout.asBoolInput p.S).length

theorem SelectedMergeEquivEmitterPaddedOutputTape_equiv
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    Tape.Equiv
      (SelectedMergeEquivEmitterPaddedOutputTape useAccept p)
      (SelectedMergeEquivOutputTape useAccept p.S p.L) := by
  simpa [SelectedMergeEquivEmitterPaddedOutputTape,
    SelectedMergeEquivOutputTape] using
    inputWithTrailingBlankPadding_equiv_input
      (MachineDescription.encodeCodeWordAsInput
        (SelectedMergeOutputCode useAccept p.S p.L))
      (MachineDescription.SimulatorLayout.asBoolInput p.S).length

theorem SelectedMergeEquivEmitterPaddedOutputTape_normalizedOutput
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergeEquivEmitterPaddedOutputTape useAccept p) =
      MachineDescription.encodeCodeWordAsInput
        (SelectedMergeOutputCode useAccept p.S p.L) := by
  simpa [SelectedMergeEquivEmitterPaddedOutputTape] using
    inputWithTrailingBlankPadding_normalizedOutput
      (MachineDescription.encodeCodeWordAsInput
        (SelectedMergeOutputCode useAccept p.S p.L))
      (MachineDescription.SimulatorLayout.asBoolInput p.S).length

theorem SelectedMergeEquivEmitterPaddedOutputTape_contextLength_ge_input
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    Tape.contextLength (MachineDescription.SimulatorLayout.tape p.S) <=
      Tape.contextLength
        (SelectedMergeEquivEmitterPaddedOutputTape useAccept p) := by
  simpa [SelectedMergeEquivEmitterPaddedOutputTape,
    MachineDescription.SimulatorLayout.tape] using
    inputWithTrailingBlankPadding_contextLength_ge_input
      (MachineDescription.encodeCodeWordAsInput
        (SelectedMergeOutputCode useAccept p.S p.L))
      (MachineDescription.SimulatorLayout.asBoolInput p.S)

theorem SelectedMergeEmitterInputTape_normalizedOutput
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput (MachineDescription.SimulatorLayout.tape p.S) =
      SelectedMergeEmitterInputBits p := by
  simpa [SelectedMergeEmitterInputBits] using
    MachineDescription.SimulatorLayout.tape_normalizedOutput p.S

theorem SelectedMergeEmitterPayload.input_eq_encodeCodeWordAsInput
    (p : SelectedMergeEmitterPayload) :
    p.S.input =
      MachineDescription.encodeCodeWordAsInput
        (MachineDescription.DovetailLayout.encode p.L) :=
  MachineDescription.decodeCodeWordAsInput_eq_some_encodeCodeWordAsInput
    p.input

theorem SelectedMergeEmitterPayload.input_eq_parsedLayoutBits
    (p : SelectedMergeEmitterPayload) :
    p.S.input = ParsedLayoutBits p.L := by
  rw [SelectedMergeEmitterPayload.input_eq_encodeCodeWordAsInput,
    ParsedLayoutBits]

theorem SelectedMergeEmitterInputBits_eq_fields
    (p : SelectedMergeEmitterPayload) :
    SelectedMergeEmitterInputBits p =
      MachineDescription.encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          MachineDescription.encodeBoolWordAppend
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.DovetailLayout.encode p.L))
            (MachineDescription.encodeNatAppend p.S.stage
              (MachineDescription.encodeConfigurationAppend p.S.config
                (MachineDescription.encodeBoolAppend p.S.hit [])))) := by
  rw [SelectedMergeEmitterInputBits,
    MachineDescription.SimulatorLayout.asBoolInput,
    MachineDescription.SimulatorLayout.encode,
    MachineDescription.SimulatorLayout.encodeAppend,
    SelectedMergeEmitterPayload.input_eq_encodeCodeWordAsInput]

theorem SelectedMergeEmitterInputTape_normalizedOutput_eq_fields
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput (MachineDescription.SimulatorLayout.tape p.S) =
      MachineDescription.encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          MachineDescription.encodeBoolWordAppend
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.DovetailLayout.encode p.L))
            (MachineDescription.encodeNatAppend p.S.stage
              (MachineDescription.encodeConfigurationAppend p.S.config
                (MachineDescription.encodeBoolAppend p.S.hit [])))) := by
  rw [SelectedMergeEmitterInputTape_normalizedOutput,
    SelectedMergeEmitterInputBits_eq_fields]

theorem SelectedMergeEmitterInputBits_eq_parsedLayoutFields
    (p : SelectedMergeEmitterPayload) :
    SelectedMergeEmitterInputBits p =
      MachineDescription.encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          MachineDescription.encodeBoolWordAppend (ParsedLayoutBits p.L)
            (MachineDescription.encodeNatAppend p.S.stage
              (MachineDescription.encodeConfigurationAppend p.S.config
                (MachineDescription.encodeBoolAppend p.S.hit [])))) := by
  simpa [ParsedLayoutBits] using
    SelectedMergeEmitterInputBits_eq_fields p

theorem SelectedMergeEmitterInputTape_normalizedOutput_eq_parsedLayoutFields
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput (MachineDescription.SimulatorLayout.tape p.S) =
      MachineDescription.encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          MachineDescription.encodeBoolWordAppend (ParsedLayoutBits p.L)
            (MachineDescription.encodeNatAppend p.S.stage
              (MachineDescription.encodeConfigurationAppend p.S.config
                (MachineDescription.encodeBoolAppend p.S.hit [])))) := by
  rw [SelectedMergeEmitterInputTape_normalizedOutput,
    SelectedMergeEmitterInputBits_eq_parsedLayoutFields]

theorem SelectedMergeEquivEmitterPaddedOutputTape_contextLength_ge_inputBits
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    Tape.contextLength (Tape.input (SelectedMergeEmitterInputBits p)) <=
      Tape.contextLength
        (SelectedMergeEquivEmitterPaddedOutputTape useAccept p) := by
  simpa [SelectedMergeEmitterInputBits,
    MachineDescription.SimulatorLayout.tape] using
    SelectedMergeEquivEmitterPaddedOutputTape_contextLength_ge_input
      useAccept p

def SelectedMergeEquivPaddedEmitterSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      emitter.HaltsFromTape
        (MachineDescription.SimulatorLayout.tape p.S)
        (SelectedMergeEquivEmitterPaddedOutputTape useAccept p)

def SelectedMergeEquivPaddedEmitterConstruction : Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedMergeEquivPaddedEmitterSpec useAccept emitter

theorem selectedMergeEquivEmitterSpec_of_padded
    {useAccept : Bool} {emitter : MachineDescription}
    (hemits : SelectedMergeEquivPaddedEmitterSpec useAccept emitter) :
    SelectedMergeEquivEmitterSpec useAccept emitter := by
  constructor
  · exact hemits.left
  · intro p
    exact
      ⟨SelectedMergeEquivEmitterPaddedOutputTape useAccept p,
        hemits.right p,
        SelectedMergeEquivEmitterPaddedOutputTape_equiv useAccept p⟩

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
          (MachineDescription.SimulatorLayout.tape S)
          (MachineDescription.SimulatorLayout.tape S) := by
        have hrun :
          parser.HaltsFromTape
            (MachineDescription.SimulatorLayout.tape S)
            (MachineDescription.SimulatorLayout.tape S) := by
          simpa [MachineDescription.SimulatorLayout.tape,
            MachineDescription.HaltsWithTape,
            MachineDescription.HaltsFromTape,
            MachineDescription.HaltsWithTapeIn,
            MachineDescription.HaltsFromTapeIn,
            MachineDescription.initial] using
            hparser.right S L hinput
        exact MachineDescription.HaltsFromTape.toEquiv hrun
    have hbridge :
        Tape.Equiv
          (Tape.move Direction.left
            (Tape.move Direction.right
              (MachineDescription.SimulatorLayout.tape S)))
          (Tape.input (MachineDescription.SimulatorLayout.asBoolInput S)) := by
      rw [simulatorLayoutTape_move_left_move_right S]
      exact Tape.Equiv.refl _
    have hemits :=
      hemitter.right { S := S, L := L, input := hinput }
    exact
      SeqViaCanonical_haltsFromTapeEquiv_of_equiv
        hparser.left hemitter.left hparserRun hbridge
        (by simpa [MachineDescription.SimulatorLayout.tape] using hemits)
  · intro S L hinput T hhalt
    have hforward :
        (SeqViaCanonical parser emitter).HaltsFromTapeEquiv
          (MachineDescription.SimulatorLayout.tape S)
          (SelectedMergeEquivOutputTape useAccept S L) := by
      have hparserRun :
          parser.HaltsFromTapeEquiv
            (MachineDescription.SimulatorLayout.tape S)
            (MachineDescription.SimulatorLayout.tape S) := by
        have hrun :
            parser.HaltsFromTape
              (MachineDescription.SimulatorLayout.tape S)
              (MachineDescription.SimulatorLayout.tape S) := by
          simpa [MachineDescription.SimulatorLayout.tape,
            MachineDescription.HaltsWithTape, MachineDescription.HaltsFromTape,
            MachineDescription.HaltsWithTapeIn,
            MachineDescription.HaltsFromTapeIn,
            MachineDescription.initial] using
            hparser.right S L hinput
        exact MachineDescription.HaltsFromTape.toEquiv hrun
      have hbridge :
          Tape.Equiv
            (Tape.move Direction.left
              (Tape.move Direction.right
                (MachineDescription.SimulatorLayout.tape S)))
            (Tape.input (MachineDescription.SimulatorLayout.asBoolInput S)) := by
        rw [simulatorLayoutTape_move_left_move_right S]
        exact Tape.Equiv.refl _
      have hemits :=
        hemitter.right { S := S, L := L, input := hinput }
      exact
        SeqViaCanonical_haltsFromTapeEquiv_of_equiv
          hparser.left hemitter.left hparserRun hbridge
          (by simpa [MachineDescription.SimulatorLayout.tape] using hemits)
    rcases hforward with ⟨Tactual, hactual, hequiv⟩
    have hT_eq : T = Tactual :=
      MachineDescription.haltsFromTape_functional_of_haltTransitionFree
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
  MachineDescription.seqSubroutine
    emitter MachineDescription.ExactIdentityDescription Direction.right

theorem selectedMergeCanonicalEmitterSpec_of_exact
    {useAccept : Bool} {emitter : MachineDescription}
    (hemits :
      SelectedMergeCanonicalExactEmitterSpec useAccept emitter) :
    SelectedMergeCanonicalEmitterSpec useAccept
      (SelectedMergeCanonicalEmitterFromExact emitter) := by
  let identity := MachineDescription.ExactIdentityDescription
  have hid : identity.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  constructor
  · exact
      MachineDescription.seqSubroutine_subroutineReady
        hemits.left hid
  constructor
  · intro p
    simpa [SelectedMergeCanonicalEmitterFromExact,
      SelectedMergeCanonicalEmitterSpec,
      SelectedMergeCanonicalExactEmitterSpec,
      CanonicalLayouts.OutputTape, CanonicalLayouts.ExactOutputTape,
      identity] using
      MachineDescription.seqSubroutine_haltsWithTape_of_haltsWithTape
        (A := emitter) (B := identity) (handoffMove := Direction.right)
        hemits.left hid (hemits.right.left p)
        (CommonGround.Identity.exactIdentityDescription_run_from_start
          (Tape.move Direction.right
            (CanonicalLayouts.ExactOutputTape
              (SelectedMergeEmitterOutputCode useAccept) p)))
  · intro p T hhalt
    rcases
        MachineDescription.seqSubroutine_haltsWithTape_inv
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
      congrArg MachineDescription.Configuration.tape hn
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
    (S : MachineDescription.SimulatorLayout)
    (L : MachineDescription.DovetailLayout) :
    MachineDescription.Configuration :=
  if useAccept then S.config else L.acceptConfig

def SelectedMergeOutputRejectConfig
    (useAccept : Bool)
    (S : MachineDescription.SimulatorLayout)
    (L : MachineDescription.DovetailLayout) :
    MachineDescription.Configuration :=
  if useAccept then L.rejectConfig else S.config

def SelectedMergeOutputAcceptHit
    (useAccept : Bool)
    (S : MachineDescription.SimulatorLayout)
    (L : MachineDescription.DovetailLayout) : Bool :=
  if useAccept then S.hit else L.acceptHit

def SelectedMergeOutputRejectHit
    (useAccept : Bool)
    (S : MachineDescription.SimulatorLayout)
    (L : MachineDescription.DovetailLayout) : Bool :=
  if useAccept then L.rejectHit else S.hit

def SelectedMergeOutputLayout
    (useAccept : Bool)
    (S : MachineDescription.SimulatorLayout)
    (L : MachineDescription.DovetailLayout) :
    MachineDescription.DovetailLayout :=
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
    (S : MachineDescription.SimulatorLayout)
    (L : MachineDescription.DovetailLayout) :
    SelectedMergeOutputCode useAccept S L =
      MachineDescription.DovetailLayout.encode
        (SelectedMergeOutputLayout useAccept S L) := by
  cases useAccept <;>
    rfl

theorem selectedMergeOutputCode_eq_fields
    (useAccept : Bool)
    (S : MachineDescription.SimulatorLayout)
    (L : MachineDescription.DovetailLayout) :
    SelectedMergeOutputCode useAccept S L =
      MachineCodeSymbol.transition ::
        MachineDescription.encodeBoolWordAppend L.input
          (MachineDescription.encodeNatAppend L.stage
            (MachineDescription.encodeConfigurationAppend
              (SelectedMergeOutputAcceptConfig useAccept S L)
              (MachineDescription.encodeConfigurationAppend
                (SelectedMergeOutputRejectConfig useAccept S L)
                (MachineDescription.encodeBoolAppend
                  (SelectedMergeOutputAcceptHit useAccept S L)
                  (MachineDescription.encodeBoolAppend
                    (SelectedMergeOutputRejectHit useAccept S L) []))))) := by
  cases useAccept <;>
    rfl

theorem SelectedMergeEquivEmitterPaddedOutputTape_normalizedOutput_eq_fields
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergeEquivEmitterPaddedOutputTape useAccept p) =
      MachineDescription.encodeCodeWordAsInput
        (MachineCodeSymbol.transition ::
          MachineDescription.encodeBoolWordAppend p.L.input
            (MachineDescription.encodeNatAppend p.L.stage
              (MachineDescription.encodeConfigurationAppend
                (SelectedMergeOutputAcceptConfig useAccept p.S p.L)
                (MachineDescription.encodeConfigurationAppend
                  (SelectedMergeOutputRejectConfig useAccept p.S p.L)
                  (MachineDescription.encodeBoolAppend
                    (SelectedMergeOutputAcceptHit useAccept p.S p.L)
                    (MachineDescription.encodeBoolAppend
                      (SelectedMergeOutputRejectHit useAccept p.S p.L)
                      [])))))) := by
  rw [SelectedMergeEquivEmitterPaddedOutputTape_normalizedOutput,
    selectedMergeOutputCode_eq_fields]

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
    ParsedLayoutBits, selectedMergeOutputCode_eq_outputLayout] using
    inputWithTrailingBlankPadding_equiv_input
      (MachineDescription.encodeCodeWordAsInput
        (SelectedMergeOutputCode useAccept p.S p.L))
      (MachineDescription.SimulatorLayout.asBoolInput p.S).length

theorem selectedMergeOutputLayout_accept_run
    (accept : MachineDescription) (L : MachineDescription.DovetailLayout) :
    SelectedMergeOutputLayout true
        (MachineDescription.SimulatorLayout.run
          accept L.stage (AcceptSimulatorLayout L)) L =
      ConfigRunnerAfterAccept accept L := by
  simp [SelectedMergeOutputLayout, ConfigRunnerAfterAccept,
    AcceptSimulatorLayout, MachineDescription.SimulatorLayout.run]

theorem selectedMergeOutputLayout_reject_run
    (reject : MachineDescription) (L : MachineDescription.DovetailLayout) :
    SelectedMergeOutputLayout false
        (MachineDescription.SimulatorLayout.run
          reject L.stage (RejectSimulatorLayout L)) L =
      ConfigRunnerAfterReject reject L := by
  simp [SelectedMergeOutputLayout, ConfigRunnerAfterReject,
    RejectSimulatorLayout, MachineDescription.SimulatorLayout.run]

theorem
    SelectedMergeEquivEmitterPaddedOutputTape_normalizedOutput_accept_run
    (accept : MachineDescription) (L : MachineDescription.DovetailLayout) :
    Tape.normalizedOutput
        (SelectedMergeEquivEmitterPaddedOutputTape true
          { S :=
              MachineDescription.SimulatorLayout.run
                accept L.stage (AcceptSimulatorLayout L)
            L := L
            input := by
              simpa [AcceptSimulatorLayout,
                MachineDescription.SimulatorLayout.run] using
                decodeCodeWordAsInput_parsedLayoutBits L }) =
      ParsedLayoutBits (ConfigRunnerAfterAccept accept L) := by
  rw [SelectedMergeEquivEmitterPaddedOutputTape_normalizedOutput_eq_parsedLayoutBits]
  rw [selectedMergeOutputLayout_accept_run]

theorem SelectedMergeEquivEmitterPaddedOutputTape_equiv_accept_run
    (accept : MachineDescription) (L : MachineDescription.DovetailLayout) :
    Tape.Equiv
        (SelectedMergeEquivEmitterPaddedOutputTape true
          { S :=
              MachineDescription.SimulatorLayout.run
                accept L.stage (AcceptSimulatorLayout L)
            L := L
            input := by
              simpa [AcceptSimulatorLayout,
                MachineDescription.SimulatorLayout.run] using
                decodeCodeWordAsInput_parsedLayoutBits L })
        (ParsedLayoutTape (ConfigRunnerAfterAccept accept L)) := by
  simpa [selectedMergeOutputLayout_accept_run] using
    SelectedMergeEquivEmitterPaddedOutputTape_equiv_parsedLayoutTape
      true
      { S :=
          MachineDescription.SimulatorLayout.run
            accept L.stage (AcceptSimulatorLayout L)
        L := L
        input := by
          simpa [AcceptSimulatorLayout,
            MachineDescription.SimulatorLayout.run] using
            decodeCodeWordAsInput_parsedLayoutBits L }

theorem
    SelectedMergeEquivEmitterPaddedOutputTape_normalizedOutput_reject_run
    (reject : MachineDescription) (L : MachineDescription.DovetailLayout) :
    Tape.normalizedOutput
        (SelectedMergeEquivEmitterPaddedOutputTape false
          { S :=
              MachineDescription.SimulatorLayout.run
                reject L.stage (RejectSimulatorLayout L)
            L := L
            input := by
              simpa [RejectSimulatorLayout,
                MachineDescription.SimulatorLayout.run] using
                decodeCodeWordAsInput_parsedLayoutBits L }) =
      ParsedLayoutBits (ConfigRunnerAfterReject reject L) := by
  rw [SelectedMergeEquivEmitterPaddedOutputTape_normalizedOutput_eq_parsedLayoutBits]
  rw [selectedMergeOutputLayout_reject_run]

theorem SelectedMergeEquivEmitterPaddedOutputTape_equiv_reject_run
    (reject : MachineDescription) (L : MachineDescription.DovetailLayout) :
    Tape.Equiv
        (SelectedMergeEquivEmitterPaddedOutputTape false
          { S :=
              MachineDescription.SimulatorLayout.run
                reject L.stage (RejectSimulatorLayout L)
            L := L
            input := by
              simpa [RejectSimulatorLayout,
                MachineDescription.SimulatorLayout.run] using
                decodeCodeWordAsInput_parsedLayoutBits L })
        (ParsedLayoutTape (ConfigRunnerAfterReject reject L)) := by
  simpa [selectedMergeOutputLayout_reject_run] using
    SelectedMergeEquivEmitterPaddedOutputTape_equiv_parsedLayoutTape
      false
      { S :=
          MachineDescription.SimulatorLayout.run
            reject L.stage (RejectSimulatorLayout L)
        L := L
        input := by
          simpa [RejectSimulatorLayout,
            MachineDescription.SimulatorLayout.run] using
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
    let identity := MachineDescription.ExactIdentityDescription
    have hid : identity.SubroutineReady :=
      CommonGround.Identity.exactIdentityDescription_subroutineReady
    rcases
        MachineDescription.seqSubroutine_haltsWithTape_inv
          (A := MachineDescription.seqSubroutine
            parser identity Direction.right)
          (B := emitter)
          (handoffMove := Direction.left)
          (MachineDescription.seqSubroutine_subroutineReady
            hparser.left hid)
          hemitter.left
          (by simpa [SeqViaCanonical, identity] using hhalt) with
      ⟨Tmid, hparserIdHalt, _hemitterReach⟩
    rcases
        MachineDescription.seqSubroutine_haltsWithTape_inv
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
          (MachineDescription.SimulatorLayout.asBoolInput S) T := by
      simpa [MachineDescription.SimulatorLayout.asBoolInput, hcode] using
        hhalt
    have hforward :
        (SeqViaCanonical parser emitter).HaltsWithTape
          (MachineDescription.SimulatorLayout.asBoolInput S)
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

/--
Finite-machine leaf for selected merge under the equivalence-based phase
contract.  It emits the merged dovetail-layout code at the left edge and leaves
blank padding in the old simulator-layout window, so the exact tape is
equivalent to the unshifted merged dovetail-layout tape without requiring a
context-length decrease.
-/
theorem selectedMergeEquivPaddedEmitterConstruction_scaffold :
    SelectedMergeEquivPaddedEmitterConstruction := by
  sorry

theorem selectedMergeEquivEmitterConstruction_scaffold :
    SelectedMergeEquivEmitterConstruction :=
  selectedMergeEquivEmitterConstruction_of_padded
    selectedMergeEquivPaddedEmitterConstruction_scaffold

theorem selectedMergeEquivConstruction_scaffold :
    SelectedMergeEquivConstruction :=
  selectedMergeEquivConstruction_of_forwardParser_emitter
    selectedMergeForwardParserConstruction_scaffold
    selectedMergeEquivEmitterConstruction_scaffold


end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
