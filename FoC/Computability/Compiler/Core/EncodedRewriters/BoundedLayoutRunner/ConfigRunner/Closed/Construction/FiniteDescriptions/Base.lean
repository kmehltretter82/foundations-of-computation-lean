import FoC.Computability.Compiler.Core.CommonGround.BoolWordQuoters
import FoC.Computability.Compiler.Core.CommonGround.CodeWordEmitters
import FoC.Computability.Compiler.Core.CommonGround.Identity
import FoC.Computability.Compiler.Core.CommonGround.Layouts
import FoC.Computability.Compiler.Core.EncodingLemmas
import FoC.Computability.Compiler.Core.EncodedRewriters.RightShifted
import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.PhaseRunner
import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.PaddedEmitters
import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.SelectedProjectionTailProjector

set_option doc.verso true

/-!
# Bounded runner parser and emitter adapters

This module owns the neutral finite-description boundary for selected
projection and selected merge.  The selected-projection route exposed here is
the padded/equivalence route used by the phase runner; exact and right-shifted
selected-projection wrappers are adapter-level compatibility surfaces.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

def SelectedProjectionEmitterSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  ReadySpec emitter ∧
    (forall L : DovetailLayout,
      emitter.HaltsWithTape
        (ParsedLayoutBits L)
        (SelectedProjectionOutputTape useAccept L)) ∧
      forall L : DovetailLayout,
      forall T : Tape Bool,
        emitter.HaltsWithTape (ParsedLayoutBits L) T ->
          T = SelectedProjectionOutputTape useAccept L

def SelectedProjectionCanonicalEmitterSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  CanonicalLayouts.EmitterSpec
    ParsedLayoutBits
    (SelectedProjectionOutputCode useAccept)
    emitter

theorem selectedProjectionEmitterSpec_iff_canonical
    (useAccept : Bool) (emitter : MachineDescription) :
    SelectedProjectionEmitterSpec useAccept emitter ↔
      SelectedProjectionCanonicalEmitterSpec useAccept emitter := by
  rfl

def SelectedProjectionEmitterConstruction : Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedProjectionEmitterSpec useAccept emitter

def SelectedProjectionCheckedEmitterSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  ReadySpec emitter ∧
    forall L : DovetailLayout,
      emitter.HaltsFromTape
        (ParsedLayoutCheckedTape L)
        (SelectedProjectionOutputTape useAccept L)

def SelectedProjectionCheckedEmitterConstruction : Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedProjectionCheckedEmitterSpec useAccept emitter

theorem selectedProjectionOutputCode_true
    (L : DovetailLayout) :
    SelectedProjectionOutputCode true L =
      SimulatorLayout.encode
        (AcceptSimulatorLayout L) := by
  rfl

theorem selectedProjectionOutputCode_false
    (L : DovetailLayout) :
    SelectedProjectionOutputCode false L =
      SimulatorLayout.encode
        (RejectSimulatorLayout L) := by
  rfl

theorem selectedProjectionOutputTape_true
    (L : DovetailLayout) :
    SelectedProjectionOutputTape true L =
      Tape.move Direction.right
        (SimulatorLayout.tape
          (AcceptSimulatorLayout L)) := by
  rfl

theorem selectedProjectionOutputTape_false
    (L : DovetailLayout) :
    SelectedProjectionOutputTape false L =
      Tape.move Direction.right
        (SimulatorLayout.tape
          (RejectSimulatorLayout L)) := by
  rfl

theorem selectedProjectionOutputTape_eq_simulator_tape
    (useAccept : Bool) (L : DovetailLayout) :
    SelectedProjectionOutputTape useAccept L =
      Tape.move Direction.right
        (SimulatorLayout.tape
          (SelectedProjectionSimulatorLayout useAccept L)) := by
  cases useAccept <;>
    rfl

theorem simulatorLayoutRightOutput_contextLength_ge_input
    (input : Word Bool) (stage : Nat)
    (config : Configuration) (hit : Bool) :
    Tape.contextLength (Tape.input input) <=
      Tape.contextLength
        (Tape.move Direction.right
          (SimulatorLayout.tape
            { input := input, stage := stage, config := config, hit := hit })) := by
  cases input with
  | nil =>
      simp [SimulatorLayout.tape,
        SimulatorLayout.asBoolInput,
        SimulatorLayout.encode,
        SimulatorLayout.encodeAppend,
        encodeCodeWordAsInput,
        encodeCodeSymbolAsInput,
        encodeBoolWordAppend,
        encodeCellListAppend,
        encodeNatAppend,
        Tape.input, Tape.blank, Tape.move, Tape.moveRight,
        Tape.contextLength]
  | cons bit rest =>
      have hboolLen :
          (bit :: rest).length +
              (encodeNatAppend stage
                (encodeConfigurationAppend config
                  (encodeBoolAppend hit []))).length <=
            (encodeBoolWordAppend (bit :: rest)
              (encodeNatAppend stage
                (encodeConfigurationAppend config
                  (encodeBoolAppend hit [])))).length :=
        encodeBoolWordAppend_length_ge (bit :: rest)
          (encodeNatAppend stage
            (encodeConfigurationAppend config
              (encodeBoolAppend hit [])))
      simp at hboolLen
      simp [SimulatorLayout.tape,
        SimulatorLayout.asBoolInput,
        SimulatorLayout.encode,
        SimulatorLayout.encodeAppend,
        encodeCodeWordAsInput,
        encodeCodeSymbolAsInput,
        Tape.input, Tape.move, Tape.moveRight, Tape.contextLength,
        encodeCodeWordAsInput_length]
      omega

def SelectedProjectionConfig
    (useAccept : Bool)
    (L : DovetailLayout) :
    Configuration :=
  if useAccept then L.acceptConfig else L.rejectConfig

def SelectedProjectionHit
    (useAccept : Bool)
    (L : DovetailLayout) : Bool :=
  if useAccept then L.acceptHit else L.rejectHit

def SelectedProjectionOutputSuffix
    (useAccept : Bool)
    (L : DovetailLayout) :
    Word MachineCodeSymbol :=
  encodeNatAppend L.stage
    (encodeConfigurationAppend
      (SelectedProjectionConfig useAccept L)
      (encodeBoolAppend
        (SelectedProjectionHit useAccept L) []))

theorem selectedProjectionSimulatorLayout_eq
    (useAccept : Bool)
    (L : DovetailLayout) :
    SelectedProjectionSimulatorLayout useAccept L =
      { input := ParsedLayoutBits L
        stage := L.stage
        config := SelectedProjectionConfig useAccept L
        hit := SelectedProjectionHit useAccept L } := by
  cases useAccept <;>
    rfl

theorem selectedProjectionOutputTape_contextLength_ge_input
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.contextLength (Tape.input (ParsedLayoutBits L)) <=
      Tape.contextLength (SelectedProjectionOutputTape useAccept L) := by
  rw [selectedProjectionOutputTape_eq_simulator_tape,
    selectedProjectionSimulatorLayout_eq]
  exact simulatorLayoutRightOutput_contextLength_ge_input
    (ParsedLayoutBits L) L.stage
    (SelectedProjectionConfig useAccept L)
    (SelectedProjectionHit useAccept L)

theorem selectedProjectionOutputCode_eq_fields
    (useAccept : Bool)
    (L : DovetailLayout) :
    SelectedProjectionOutputCode useAccept L =
      MachineCodeSymbol.header ::
        encodeBoolWordAppend (ParsedLayoutBits L)
          (SelectedProjectionOutputSuffix useAccept L) := by
  rw [SelectedProjectionOutputCode,
    selectedProjectionSimulatorLayout_eq]
  rfl

theorem selectedProjectionOutputSuffix_eq_fields
    (useAccept : Bool)
    (L : DovetailLayout) :
    SelectedProjectionOutputSuffix useAccept L =
      encodeNatAppend L.stage
        (encodeConfigurationAppend
          (SelectedProjectionConfig useAccept L)
          (encodeBoolAppend
            (SelectedProjectionHit useAccept L) [])) := by
  rfl

theorem selectedProjectionOutputBits_eq_tailProjector_outputAllBits
    (useAccept : Bool)
    (L : DovetailLayout) :
    encodeCodeWordAsInput
        (SelectedProjectionOutputCode useAccept L) =
      SelectedProjectionTailProjector.outputAllBits useAccept L := by
  simpa [SelectedProjectionOutputCode] using
    SelectedProjectionTailProjector.simulatorLayout_asBoolInput_eq_outputAllBits
      useAccept L

theorem selectedProjectionOutputBits_eq_quoter_bits
    (useAccept : Bool)
    (L : DovetailLayout) :
    exists b : Bool,
    exists rest : Word Bool,
      ParsedLayoutBits L = b :: rest ∧
        encodeCodeWordAsInput
            (SelectedProjectionOutputCode useAccept L) =
          List.append
            (encodeCodeSymbolAsInput
              MachineCodeSymbol.header)
            (CommonGround.BoolWordQuoters.checkedNonemptyBoolWordQuoteDirectSourceBits
                b rest (SelectedProjectionOutputSuffix useAccept L)) := by
  rcases parsedLayoutBits_eq_false_false_tail L with
    ⟨tail, htail⟩
  refine ⟨false, false :: tail, htail, ?_⟩
  rw [selectedProjectionOutputCode_eq_fields, htail]
  simp [encodeCodeWordAsInput,
    CommonGround.BoolWordQuoters.checkedNonemptyBoolWordQuoteDirectSourceBits_eq]

def SelectedProjectionInputQuoterSpec
    (quoter : MachineDescription) : Prop :=
  quoter.SubroutineReady ∧
    forall L : DovetailLayout,
      quoter.HaltsFromTape
        (ParsedLayoutCheckedTape L)
        (SelectedProjectionTailProjector.sourceTape L
          ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
            some))

def SelectedProjectionInputQuoterConstruction : Prop :=
  exists quoter : MachineDescription,
    SelectedProjectionInputQuoterSpec quoter

def AcceptProjectionCheckedEmitterConstruction : Prop :=
  exists emitter : MachineDescription,
    SelectedProjectionCheckedEmitterSpec true emitter

def RejectProjectionCheckedEmitterConstruction : Prop :=
  exists emitter : MachineDescription,
    SelectedProjectionCheckedEmitterSpec false emitter

def SelectedProjectionCheckedEmitterSideConstruction : Prop :=
  AcceptProjectionCheckedEmitterConstruction ∧
    RejectProjectionCheckedEmitterConstruction

theorem selectedProjectionCheckedEmitterConstruction_of_sides
    (h : SelectedProjectionCheckedEmitterSideConstruction) :
    SelectedProjectionCheckedEmitterConstruction := by
  intro useAccept
  cases useAccept
  · exact h.right
  · exact h.left

def SelectedProjectionEquivEmitterSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  ReadySpec emitter ∧
    (forall L : DovetailLayout,
      emitter.HaltsFromTapeEquiv
        (Tape.input (ParsedLayoutBits L))
        (SelectedProjectionOutputTape useAccept L)) ∧
      forall L : DovetailLayout,
        emitter.ClosedFromTapeEquiv
          (Tape.input (ParsedLayoutBits L))
          (SelectedProjectionOutputTape useAccept L)

def SelectedProjectionEquivEmitterConstruction : Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedProjectionEquivEmitterSpec useAccept emitter

def SelectedProjectionCheckedEquivEmitterSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  ReadySpec emitter ∧
    (forall L : DovetailLayout,
      emitter.HaltsFromTapeEquiv
        (ParsedLayoutCheckedTape L)
        (SelectedProjectionOutputTape useAccept L)) ∧
      forall L : DovetailLayout,
        emitter.ClosedFromTapeEquiv
          (ParsedLayoutCheckedTape L)
          (SelectedProjectionOutputTape useAccept L)

def SelectedProjectionCheckedEquivEmitterConstruction : Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedProjectionCheckedEquivEmitterSpec useAccept emitter

theorem selectedProjectionEquivEmitterSpec_of_exact
    {useAccept : Bool} {emitter : MachineDescription}
    (hemitter : SelectedProjectionEmitterSpec useAccept emitter) :
    SelectedProjectionEquivEmitterSpec useAccept emitter := by
  constructor
  · exact hemitter.left
  constructor
  · intro L
    have hfrom :
        emitter.HaltsFromTape
          (Tape.input (ParsedLayoutBits L))
          (SelectedProjectionOutputTape useAccept L) := by
      simpa [HaltsWithTape,
        HaltsWithTapeIn,
        HaltsFromTape,
        HaltsFromTapeIn,
        initial] using hemitter.right.left L
    exact HaltsFromTape.toEquiv hfrom
  · intro L T hhalt
    have hwith :
        emitter.HaltsWithTape (ParsedLayoutBits L) T := by
      simpa [HaltsWithTape,
        HaltsWithTapeIn,
        HaltsFromTape,
        HaltsFromTapeIn,
        initial] using hhalt
    rw [hemitter.right.right L T hwith]
    exact Tape.Equiv.refl _

theorem selectedProjectionEquivEmitterConstruction_of_exact
    (h : SelectedProjectionEmitterConstruction) :
    SelectedProjectionEquivEmitterConstruction := by
  intro useAccept
  rcases h useAccept with ⟨emitter, hemits⟩
  exact
    ⟨emitter, selectedProjectionEquivEmitterSpec_of_exact hemits⟩

theorem selectedProjectionCheckedEquivEmitterSpec_of_equiv
    {useAccept : Bool} {emitter : MachineDescription}
    (hemitter : SelectedProjectionEquivEmitterSpec useAccept emitter) :
    SelectedProjectionCheckedEquivEmitterSpec useAccept emitter := by
  constructor
  · exact hemitter.left
  constructor
  · intro L
    rcases hemitter.right.left L with ⟨Tactual, hactual, hTactual⟩
    have hcheckedEquiv :
        Tape.Equiv (Tape.input (ParsedLayoutBits L))
          (ParsedLayoutCheckedTape L) :=
      Tape.Equiv.symm (checkedInputTape_equiv_input _)
    rcases
        HaltsFromTapeEquiv_of_input_equiv
          hcheckedEquiv hactual with
      ⟨Tchecked, hchecked, hTchecked⟩
    exact
      ⟨Tchecked, hchecked,
        Tape.Equiv.trans hTchecked hTactual⟩
  · intro L T hhalt
    have hcheckedEquiv :
        Tape.Equiv (ParsedLayoutCheckedTape L)
          (Tape.input (ParsedLayoutBits L)) :=
      checkedInputTape_equiv_input _
    rcases
        HaltsFromTapeEquiv_of_input_equiv
          hcheckedEquiv hhalt with
      ⟨Traw, hraw, hTraw⟩
    have hclosed := hemitter.right.right L Traw hraw
    exact Tape.Equiv.trans (Tape.Equiv.symm hTraw) hclosed

theorem selectedProjectionCheckedEquivEmitterConstruction_of_equiv
    (h : SelectedProjectionEquivEmitterConstruction) :
    SelectedProjectionCheckedEquivEmitterConstruction := by
  intro useAccept
  rcases h useAccept with ⟨emitter, hemits⟩
  exact
    ⟨emitter, selectedProjectionCheckedEquivEmitterSpec_of_equiv hemits⟩

theorem selectedProjectionCheckedEquivEmitterSpec_of_checked
    {useAccept : Bool} {emitter : MachineDescription}
    (hemitter : SelectedProjectionCheckedEmitterSpec useAccept emitter) :
    SelectedProjectionCheckedEquivEmitterSpec useAccept emitter := by
  constructor
  · exact hemitter.left
  constructor
  · intro L
    exact HaltsFromTape.toEquiv (hemitter.right L)
  · intro L T hhalt
    have hT :
        T = SelectedProjectionOutputTape useAccept L :=
      haltsFromTape_functional_of_haltTransitionFree
        hemitter.left.right hhalt (hemitter.right L)
    rw [hT]
    exact Tape.Equiv.refl _

theorem selectedProjectionCheckedEquivEmitterConstruction_of_checked
    (h : SelectedProjectionCheckedEmitterConstruction) :
    SelectedProjectionCheckedEquivEmitterConstruction := by
  intro useAccept
  rcases h useAccept with ⟨emitter, hemits⟩
  exact
    ⟨emitter, selectedProjectionCheckedEquivEmitterSpec_of_checked hemits⟩

theorem selectedProjectionSpec_of_parser_equivEmitter
    {useAccept : Bool} {parser emitter : MachineDescription}
    (hparser : LayoutCheckedParserSpec parser)
    (hemitter : SelectedProjectionEquivEmitterSpec useAccept emitter) :
    SelectedProjectionSpec useAccept
      (SeqViaCanonical parser emitter) := by
  have hrunnerReady :
      (SeqViaCanonical parser emitter).SubroutineReady :=
    SeqViaCanonical_subroutineReady hparser.left hemitter.left
  constructor
  · exact hrunnerReady
  constructor
  · intro L
    have hparserFrom :
        parser.HaltsFromTape
          (Tape.input (ParsedLayoutBits L))
          (ParsedLayoutCheckedTape L) := by
      simpa [HaltsWithTape,
        HaltsWithTapeIn,
        HaltsFromTape,
        HaltsFromTapeIn,
        initial] using hparser.right.left L
    have hbridge :
        Tape.Equiv
          (Tape.move Direction.left
            (Tape.move Direction.right (ParsedLayoutCheckedTape L)))
          (Tape.input (ParsedLayoutBits L)) := by
      rw [parsedLayoutCheckedTape_move_left_move_right L]
      exact checkedInputTape_equiv_input _
    exact
      SeqViaCanonical_haltsFromTapeEquiv_of_equiv
        hparser.left hemitter.left
        (HaltsFromTape.toEquiv hparserFrom)
        hbridge
        (hemitter.right.left L)
  · intro code T hhalt
    rcases
        SeqViaCanonical_haltsFromTape_inv hparser.left hemitter.left hhalt with
      ⟨Tmid, hparser_run, hemitter_run⟩
    rcases hparser.right.right code Tmid hparser_run with
      ⟨L, hcode, hTmid_equiv⟩
    refine ⟨L, CommonGround.DovetailLayouts.decode_eq_some_encode hcode, ?_⟩
    have hemitterRun' :
        emitter.HaltsFromTape
          (ParsedLayoutCheckedTape L) T := by
      rw [hTmid_equiv] at hemitter_run
      simpa [parsedLayoutCheckedTape_move_left_move_right L]
        using hemitter_run
    have hcheckedEquiv :
        Tape.Equiv (ParsedLayoutCheckedTape L)
          (Tape.input (ParsedLayoutBits L)) :=
      checkedInputTape_equiv_input _
    rcases
        HaltsFromTapeEquiv_of_input_equiv
          hcheckedEquiv hemitterRun' with
      ⟨Tactual, hactual, hTactual⟩
    have hclosed := hemitter.right.right L Tactual hactual
    exact Tape.Equiv.trans (Tape.Equiv.symm hTactual) hclosed

theorem selectedProjectionSpec_of_parser_checkedEquivEmitter
    {useAccept : Bool} {parser emitter : MachineDescription}
    (hparser : LayoutCheckedParserSpec parser)
    (hemitter :
      SelectedProjectionCheckedEquivEmitterSpec useAccept emitter) :
    SelectedProjectionSpec useAccept
      (SeqViaCanonical parser emitter) := by
  have hrunnerReady :
      (SeqViaCanonical parser emitter).SubroutineReady :=
    SeqViaCanonical_subroutineReady hparser.left hemitter.left
  constructor
  · exact hrunnerReady
  constructor
  · intro L
    have hparserFrom :
        parser.HaltsFromTape
          (Tape.input (ParsedLayoutBits L))
          (ParsedLayoutCheckedTape L) := by
      simpa [HaltsWithTape,
        HaltsWithTapeIn,
        HaltsFromTape,
        HaltsFromTapeIn,
        initial] using hparser.right.left L
    rcases hemitter.right.left L with ⟨Tactual, hactual, hTactual⟩
    have hseq :
        (SeqViaCanonical parser emitter).HaltsFromTape
          (Tape.input (ParsedLayoutBits L)) Tactual :=
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        hparser.left hemitter.left
        hparserFrom
        (parsedLayoutCheckedTape_move_left_move_right L)
        hactual
    exact ⟨Tactual, hseq, hTactual⟩
  · intro code T hhalt
    rcases
        SeqViaCanonical_haltsFromTape_inv hparser.left hemitter.left hhalt with
      ⟨Tmid, hparser_run, hemitter_run⟩
    rcases hparser.right.right code Tmid hparser_run with
      ⟨L, hcode, hTmid_equiv⟩
    refine ⟨L, CommonGround.DovetailLayouts.decode_eq_some_encode hcode, ?_⟩
    have hemitterRun' :
        emitter.HaltsFromTape
          (ParsedLayoutCheckedTape L) T := by
      rw [hTmid_equiv] at hemitter_run
      simpa [parsedLayoutCheckedTape_move_left_move_right L]
        using hemitter_run
    exact hemitter.right.right L T hemitterRun'

theorem selectedProjectionSpec_of_parser_emitter
    {useAccept : Bool} {parser emitter : MachineDescription}
    (hparser : LayoutCheckedParserSpec parser)
    (hemitter : SelectedProjectionEmitterSpec useAccept emitter) :
    SelectedProjectionSpec useAccept
      (SeqViaCanonical parser emitter) :=
  selectedProjectionSpec_of_parser_equivEmitter hparser
    (selectedProjectionEquivEmitterSpec_of_exact hemitter)

theorem selectedProjectionFiniteDescriptionConstruction_of_equivEmitter
    (hemitter : SelectedProjectionEquivEmitterConstruction) :
    SelectedProjectionFiniteDescriptionConstruction := by
  intro useAccept
  rcases layoutCheckedParserConstruction_scaffold with ⟨parser, hparser⟩
  rcases hemitter useAccept with ⟨emitter, hemits⟩
  exact
    ⟨SeqViaCanonical parser emitter,
      selectedProjectionSpec_of_parser_equivEmitter hparser hemits⟩

theorem selectedProjectionFiniteDescriptionConstruction_of_checkedEquivEmitter
    (hemitter : SelectedProjectionCheckedEquivEmitterConstruction) :
    SelectedProjectionFiniteDescriptionConstruction := by
  intro useAccept
  rcases layoutCheckedParserConstruction_scaffold with ⟨parser, hparser⟩
  rcases hemitter useAccept with ⟨emitter, hemits⟩
  exact
    ⟨SeqViaCanonical parser emitter,
      selectedProjectionSpec_of_parser_checkedEquivEmitter hparser hemits⟩

theorem selectedProjectionFiniteDescriptionConstruction_of_emitter
    (hemitter : SelectedProjectionEmitterConstruction) :
    SelectedProjectionFiniteDescriptionConstruction := by
  intro useAccept
  rcases layoutCheckedParserConstruction_scaffold with ⟨parser, hparser⟩
  rcases hemitter useAccept with ⟨emitter, hemits⟩
  exact
    ⟨SeqViaCanonical parser emitter,
      selectedProjectionSpec_of_parser_emitter hparser hemits⟩

def SelectedMergeParserSpec
    (parser : MachineDescription) : Prop :=
  ReadySpec parser ∧
    (forall S : SimulatorLayout,
     forall L : DovetailLayout,
      decodeCodeWordAsInput S.input =
        some (DovetailLayout.encode L) ->
      parser.HaltsWithTape
        (SimulatorLayout.asBoolInput S)
        (SimulatorLayout.tape S)) ∧
      forall code : Word MachineCodeSymbol,
      forall T : Tape Bool,
        parser.HaltsWithTape
            (encodeCodeWordAsInput code) T ->
          exists S : SimulatorLayout,
          exists L : DovetailLayout,
            code = SimulatorLayout.encode S ∧
              decodeCodeWordAsInput S.input =
                some (DovetailLayout.encode L) ∧
              T = SimulatorLayout.tape S

def SelectedMergeParserConstruction : Prop :=
  exists parser : MachineDescription,
    SelectedMergeParserSpec parser

def SelectedMergeForwardParserSpec
    (parser : MachineDescription) : Prop :=
  parser.SubroutineReady ∧
    forall S : SimulatorLayout,
    forall L : DovetailLayout,
      decodeCodeWordAsInput S.input =
        some (DovetailLayout.encode L) ->
      parser.HaltsWithTape
        (SimulatorLayout.asBoolInput S)
        (SimulatorLayout.tape S)

def SelectedMergeForwardParserConstruction : Prop :=
  exists parser : MachineDescription,
    SelectedMergeForwardParserSpec parser

theorem selectedMergeForwardParserSpec_of_parser
    {parser : MachineDescription}
    (hparser : SelectedMergeParserSpec parser) :
    SelectedMergeForwardParserSpec parser := by
  exact ⟨hparser.left, hparser.right.left⟩

theorem selectedMergeForwardParserConstruction_of_parser
    (hparser : SelectedMergeParserConstruction) :
    SelectedMergeForwardParserConstruction := by
  rcases hparser with ⟨parser, hparser⟩
  exact ⟨parser, selectedMergeForwardParserSpec_of_parser hparser⟩

theorem selectedMergeForwardParserSpec_identity :
    SelectedMergeForwardParserSpec
      ExactIdentityDescription := by
  constructor
  · exact CommonGround.Identity.exactIdentityDescription_subroutineReady
  · intro S _L _hinput
    simpa [SimulatorLayout.tape,
      HaltsWithTape, HaltsFromTape,
      HaltsWithTapeIn,
      HaltsFromTapeIn,
      initial] using
      CommonGround.Identity.exactIdentityDescription_haltsFromTape
        (SimulatorLayout.tape S)

theorem selectedMergeForwardParserConstruction_identity :
    SelectedMergeForwardParserConstruction :=
  ⟨ExactIdentityDescription,
    selectedMergeForwardParserSpec_identity⟩

def SelectedMergeForwardParserFromSimulatorParser
    (parser : MachineDescription) : MachineDescription :=
  seqSubroutine
    parser ExactIdentityDescription Direction.left

theorem selectedMergeForwardParserSpec_of_simulatorParser
    {parser : MachineDescription}
    (hparser :
      CommonGround.SimulatorLayouts.ClosedRecognizerSpec
        parser) :
    SelectedMergeForwardParserSpec
      (SelectedMergeForwardParserFromSimulatorParser parser) := by
  let identity := ExactIdentityDescription
  have hid : identity.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  constructor
  · exact
      seqSubroutine_subroutineReady
        hparser.left hid
  · intro S L _hinput
    have hparserRun :
        parser.HaltsWithTape
          (SimulatorLayout.asBoolInput S)
          (CommonGround.SimulatorLayouts.handoffTape S) := by
      simpa [CommonGround.SimulatorLayouts.bits,
        CommonGround.SimulatorLayouts.encode,
        CommonGround.LayoutTapes.Bits,
        SimulatorLayout.asBoolInput] using
        hparser.right.left S
    have hhandoff :
        Tape.move Direction.left
            (CommonGround.SimulatorLayouts.handoffTape S) =
          SimulatorLayout.tape S := by
      simpa [SimulatorLayout.tape] using
        CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape S
    exact
      seqSubroutine_haltsWithTape_of_haltsWithTape
        hparser.left hid hparserRun
        (by
          rw [hhandoff]
          exact
            CommonGround.Identity.exactIdentityDescription_run_from_start
              (SimulatorLayout.tape S))

theorem selectedMergeForwardParserConstruction_of_simulatorParser
    (hparser :
      CommonGround.SimulatorLayouts.ClosedRecognizerConstruction) :
    SelectedMergeForwardParserConstruction := by
  rcases hparser with ⟨parser, hparser⟩
  exact
    ⟨SelectedMergeForwardParserFromSimulatorParser parser,
      selectedMergeForwardParserSpec_of_simulatorParser hparser⟩

def SelectedMergeInputValidatorSpec
    (validator : MachineDescription) : Prop :=
  ReadySpec validator ∧
    (forall S : SimulatorLayout,
     forall L : DovetailLayout,
      decodeCodeWordAsInput S.input =
        some (DovetailLayout.encode L) ->
      validator.HaltsWithTape
        (SimulatorLayout.asBoolInput S)
        (SimulatorLayout.tape S)) ∧
      forall S : SimulatorLayout,
      forall T : Tape Bool,
        validator.HaltsWithTape
            (SimulatorLayout.asBoolInput S) T ->
          exists L : DovetailLayout,
            decodeCodeWordAsInput S.input =
              some (DovetailLayout.encode L) ∧
              T = SimulatorLayout.tape S

def SelectedMergeInputValidatorConstruction : Prop :=
  exists validator : MachineDescription,
    SelectedMergeInputValidatorSpec validator

def SelectedMergeInputValidatorPrimitive :
    TapeCodePrimitive where
  transform := fun code =>
    match SimulatorLayout.decodeComplete code with
    | none => none
    | some S =>
        match decodeCodeWordAsInput S.input with
        | none => none
        | some inputCode =>
            match DovetailLayout.decodeComplete inputCode with
            | none => none
            | some _ => some (SimulatorLayout.encode S)

theorem selectedMergeInputValidatorPrimitive_transform_eq_some_iff
    (code out : Word MachineCodeSymbol) :
    SelectedMergeInputValidatorPrimitive.transform code = some out ↔
      exists S : SimulatorLayout,
      exists L : DovetailLayout,
        code = SimulatorLayout.encode S ∧
          decodeCodeWordAsInput S.input =
            some (DovetailLayout.encode L) ∧
          out = SimulatorLayout.encode S := by
  constructor
  · intro h
    unfold SelectedMergeInputValidatorPrimitive at h
    cases hS : SimulatorLayout.decodeComplete code with
    | none =>
        simp [hS] at h
    | some S =>
        cases hinput :
            decodeCodeWordAsInput S.input with
        | none =>
            simp [hS, hinput] at h
        | some inputCode =>
            cases hL :
                DovetailLayout.decodeComplete
                  inputCode with
            | none =>
                simp [hS, hinput, hL] at h
            | some L =>
                simp [hS, hinput, hL] at h
                cases h
                have hcode :
                    code = SimulatorLayout.encode S :=
                  CommonGround.SimulatorLayouts.decodeComplete_eq_some_encode
                    hS
                have hinputCode :
                    inputCode = DovetailLayout.encode L :=
                  CommonGround.DovetailLayouts.decode_eq_some_encode
                    hL
                rw [hinputCode] at hinput
                exact ⟨S, L, hcode, hinput, rfl⟩
  · intro h
    rcases h with ⟨S, L, rfl, hinput, rfl⟩
    simp [SelectedMergeInputValidatorPrimitive,
      CommonGround.SimulatorLayouts.decodeComplete_encode,
      hinput,
      DovetailLayout.decodeComplete_encode]

def SelectedMergeInputValidatorPrimitiveRightShiftedConstruction : Prop :=
  exists validator : MachineDescription,
    RightShiftedOutputCompiledSubroutineByDescription
      SelectedMergeInputValidatorPrimitive validator

structure SelectedMergeInputValidatorPayload where
  S : SimulatorLayout
  L : DovetailLayout
  input :
    decodeCodeWordAsInput S.input =
      some (DovetailLayout.encode L)

def SelectedMergeInputValidatorInputCode
    (p : SelectedMergeInputValidatorPayload) :
    Word MachineCodeSymbol :=
  SimulatorLayout.encode p.S

def SelectedMergeInputValidatorOutputCode
    (p : SelectedMergeInputValidatorPayload) :
    Word MachineCodeSymbol :=
  SimulatorLayout.encode p.S

def SelectedMergeInputValidatorOutputTape
    (p : SelectedMergeInputValidatorPayload) : Tape Bool :=
  Tape.move Direction.right
    (Tape.input
      (encodeCodeWordAsInput
        (SelectedMergeInputValidatorOutputCode p)))

theorem selectedMergeInputValidatorOutputTape_eq_handoff
    (p : SelectedMergeInputValidatorPayload) :
    SelectedMergeInputValidatorOutputTape p =
      Tape.move Direction.right
        (SimulatorLayout.tape p.S) := by
  rfl

theorem selectedMergeInputValidatorOutputTape_eq_of_same_simulator
    {p q : SelectedMergeInputValidatorPayload}
    (hS : p.S = q.S) :
    SelectedMergeInputValidatorOutputTape p =
      SelectedMergeInputValidatorOutputTape q := by
  cases p
  cases q
  subst hS
  rfl

def SelectedMergeInputValidatorExactSpec
    (validator : MachineDescription) : Prop :=
  ReadySpec validator ∧
    (forall p : SelectedMergeInputValidatorPayload,
      validator.HaltsWithTape
        (SimulatorLayout.asBoolInput p.S)
        (SelectedMergeInputValidatorOutputTape p)) ∧
      forall code : Word MachineCodeSymbol,
      forall T : Tape Bool,
        validator.HaltsWithTape
            (encodeCodeWordAsInput code) T ->
          exists p : SelectedMergeInputValidatorPayload,
            code = SelectedMergeInputValidatorInputCode p ∧
              T = SelectedMergeInputValidatorOutputTape p

def SelectedMergeInputValidatorExactConstruction : Prop :=
  exists validator : MachineDescription,
    SelectedMergeInputValidatorExactSpec validator

def SelectedMergeInputFieldValidatorSpec
    (validator : MachineDescription) : Prop :=
  validator.SubroutineReady ∧
    (forall S : SimulatorLayout,
     forall L : DovetailLayout,
      forall hinput :
        decodeCodeWordAsInput S.input =
          some (DovetailLayout.encode L),
      validator.HaltsFromTape
        (SimulatorLayout.tape S)
        (SelectedMergeInputValidatorOutputTape
          { S := S, L := L, input := hinput })) ∧
      forall S : SimulatorLayout,
      forall T : Tape Bool,
        validator.HaltsFromTape
            (SimulatorLayout.tape S) T ->
          exists L : DovetailLayout,
          exists hinput :
            decodeCodeWordAsInput S.input =
              some (DovetailLayout.encode L),
            T =
              SelectedMergeInputValidatorOutputTape
                { S := S, L := L, input := hinput }

def SelectedMergeInputFieldValidatorConstruction : Prop :=
  exists validator : MachineDescription,
    SelectedMergeInputFieldValidatorSpec validator

def SelectedMergeInputFieldCheckerSpec
    (checker : MachineDescription) : Prop :=
  checker.SubroutineReady ∧
    (forall S : SimulatorLayout,
     forall L : DovetailLayout,
      forall _hinput :
        decodeCodeWordAsInput S.input =
          some (DovetailLayout.encode L),
      checker.HaltsFromTape
        (SimulatorLayout.tape S)
        (SimulatorLayout.tape S)) ∧
      forall S : SimulatorLayout,
      forall T : Tape Bool,
        checker.HaltsFromTape
            (SimulatorLayout.tape S) T ->
          exists L : DovetailLayout,
          exists _hinput :
            decodeCodeWordAsInput S.input =
              some (DovetailLayout.encode L),
            T = SimulatorLayout.tape S

def SelectedMergeInputFieldCheckerConstruction : Prop :=
  exists checker : MachineDescription,
    SelectedMergeInputFieldCheckerSpec checker

def SelectedMergeInputFieldValidatorFromChecker
    (checker : MachineDescription) : MachineDescription :=
  seqSubroutine
    checker ExactIdentityDescription Direction.right

theorem selectedMergeInputFieldValidatorSpec_of_checker
    {checker : MachineDescription}
    (hchecker : SelectedMergeInputFieldCheckerSpec checker) :
    SelectedMergeInputFieldValidatorSpec
      (SelectedMergeInputFieldValidatorFromChecker checker) := by
  let identity := ExactIdentityDescription
  have hid : identity.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  constructor
  · exact
      seqSubroutine_subroutineReady
        hchecker.left hid
  constructor
  · intro S L hinput
    have hcheck :
        checker.HaltsFromTape
          (SimulatorLayout.tape S)
          (SimulatorLayout.tape S) :=
      hchecker.right.left S L hinput
    simpa [SelectedMergeInputFieldValidatorFromChecker,
      selectedMergeInputValidatorOutputTape_eq_handoff, identity] using
      seqSubroutine_haltsFromTape_of_haltsFromTape
        (A := checker) (B := identity) (handoffMove := Direction.right)
        hchecker.left hid hcheck
        (CommonGround.Identity.exactIdentityDescription_run_from_start
          (Tape.move Direction.right
            (SimulatorLayout.tape S)))
  · intro S T hhalt
    rcases
        seqSubroutine_haltsFromTape_inv
          (A := checker) (B := identity) (handoffMove := Direction.right)
          hchecker.left hid
          (by
            simpa [SelectedMergeInputFieldValidatorFromChecker, identity]
              using hhalt) with
      ⟨Tmid, hcheckRun, hidentityReach⟩
    rcases hchecker.right.right S Tmid hcheckRun with
      ⟨L, hinput, hTmid⟩
    refine ⟨L, hinput, ?_⟩
    rcases hidentityReach with ⟨n, hn⟩
    have hrun :=
      CommonGround.Identity.exactIdentityDescription_runConfig_from_start
        n (Tape.move Direction.right Tmid)
    rw [hrun] at hn
    have htape :
        Tape.move Direction.right Tmid = T :=
      congrArg Configuration.tape hn
    rw [hTmid] at htape
    simpa [selectedMergeInputValidatorOutputTape_eq_handoff] using
      htape.symm

theorem selectedMergeInputFieldValidatorConstruction_of_checker
    (hchecker : SelectedMergeInputFieldCheckerConstruction) :
    SelectedMergeInputFieldValidatorConstruction := by
  rcases hchecker with ⟨checker, hchecker⟩
  exact
    ⟨SelectedMergeInputFieldValidatorFromChecker checker,
      selectedMergeInputFieldValidatorSpec_of_checker hchecker⟩

def SelectedMergeInputValidatorFromParserChecker
    (parser checker : MachineDescription) : MachineDescription :=
  seqSubroutine parser checker Direction.left

theorem selectedMergeInputValidatorSpec_of_parser_checker
    {parser checker : MachineDescription}
    (hparser :
      CommonGround.SimulatorLayouts.ClosedRecognizerSpec
        parser)
    (hchecker : SelectedMergeInputFieldCheckerSpec checker) :
    SelectedMergeInputValidatorSpec
      (SelectedMergeInputValidatorFromParserChecker parser checker) := by
  have hrunnerReady :
      (SelectedMergeInputValidatorFromParserChecker
        parser checker).SubroutineReady :=
    seqSubroutine_subroutineReady
      hparser.left hchecker.left
  constructor
  · exact hrunnerReady
  constructor
  · intro S L hinput
    have hparserRun :
        parser.HaltsWithTape
          (SimulatorLayout.asBoolInput S)
          (CommonGround.SimulatorLayouts.handoffTape S) := by
      simpa [CommonGround.SimulatorLayouts.bits,
        CommonGround.SimulatorLayouts.encode,
        CommonGround.LayoutTapes.Bits,
        SimulatorLayout.asBoolInput] using
        hparser.right.left S
    have hcheckerRun :
        checker.HaltsFromTape
          (SimulatorLayout.tape S)
          (SimulatorLayout.tape S) :=
      hchecker.right.left S L hinput
    rcases runConfig_eq_halt_of_haltsFromTape
      hcheckerRun with ⟨n, hn⟩
    exact
      seqSubroutine_haltsWithTape_of_haltsWithTape
        hparser.left hchecker.left hparserRun
        ⟨n, by
          simpa [
            CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape
              S] using hn⟩
  · intro S T hhalt
    rcases
        seqSubroutine_haltsWithTape_inv
          hparser.left hchecker.left
          (by
            simpa [SelectedMergeInputValidatorFromParserChecker] using
              hhalt) with
      ⟨Tmid, hparserRun, hcheckerReach⟩
    have hparserRun' :
        parser.HaltsWithTape
          (encodeCodeWordAsInput
            (SimulatorLayout.encode S)) Tmid := by
      simpa [SimulatorLayout.asBoolInput] using
        hparserRun
    rcases hparser.right.right
        (SimulatorLayout.encode S) Tmid hparserRun' with
      ⟨S', hdecode, hTmid⟩
    have hS' : S' = S := by
      have hdecode' :
          SimulatorLayout.decodeComplete
              (SimulatorLayout.encode S) =
            some S' := by
        simpa [CommonGround.SimulatorLayouts.decode,
          CommonGround.SimulatorLayouts.encode] using hdecode
      rw [CommonGround.SimulatorLayouts.decodeComplete_encode] at hdecode'
      cases hdecode'
      rfl
    subst S'
    rcases hcheckerReach with ⟨n, hn⟩
    have hcheckerRun :
        checker.HaltsFromTape
          (SimulatorLayout.tape S) T := by
      refine ⟨n, ?_⟩
      constructor
      · simpa [HaltsFromTapeIn,
          initial, hTmid,
          CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape
            S] using congrArg Configuration.state hn
      · simpa [HaltsFromTapeIn,
          initial, hTmid,
          CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape
            S] using congrArg Configuration.tape hn
    rcases hchecker.right.right S T hcheckerRun with
      ⟨L, hinput, hT⟩
    exact ⟨L, hinput, hT⟩

theorem selectedMergeInputValidatorConstruction_of_parser_checker
    (hparser :
      CommonGround.SimulatorLayouts.ClosedRecognizerConstruction)
    (hchecker : SelectedMergeInputFieldCheckerConstruction) :
    SelectedMergeInputValidatorConstruction := by
  rcases hparser with ⟨parser, hparser⟩
  rcases hchecker with ⟨checker, hchecker⟩
  exact
    ⟨SelectedMergeInputValidatorFromParserChecker parser checker,
      selectedMergeInputValidatorSpec_of_parser_checker hparser hchecker⟩

def SelectedMergeInputValidatorFromParserField
    (parser fieldValidator : MachineDescription) : MachineDescription :=
  seqSubroutine parser fieldValidator Direction.left

theorem selectedMergeInputValidatorExactSpec_of_parser_fieldValidator
    {parser fieldValidator : MachineDescription}
    (hparser :
      CommonGround.SimulatorLayouts.ClosedRecognizerSpec
        parser)
    (hfield :
      SelectedMergeInputFieldValidatorSpec fieldValidator) :
    SelectedMergeInputValidatorExactSpec
      (SelectedMergeInputValidatorFromParserField
        parser fieldValidator) := by
  have hrunnerReady :
      (SelectedMergeInputValidatorFromParserField
        parser fieldValidator).SubroutineReady :=
    seqSubroutine_subroutineReady
      hparser.left hfield.left
  constructor
  · exact hrunnerReady
  constructor
  · intro p
    have hparserRun :
        parser.HaltsWithTape
          (SimulatorLayout.asBoolInput p.S)
          (CommonGround.SimulatorLayouts.handoffTape p.S) := by
      simpa [CommonGround.SimulatorLayouts.bits,
        CommonGround.SimulatorLayouts.encode,
        CommonGround.LayoutTapes.Bits,
        SimulatorLayout.asBoolInput] using
        hparser.right.left p.S
    have hfieldRun :
        fieldValidator.HaltsFromTape
          (SimulatorLayout.tape p.S)
          (SelectedMergeInputValidatorOutputTape p) :=
      hfield.right.left p.S p.L p.input
    rcases runConfig_eq_halt_of_haltsFromTape
      hfieldRun with ⟨n, hn⟩
    exact
      seqSubroutine_haltsWithTape_of_haltsWithTape
        hparser.left hfield.left hparserRun
        ⟨n, by
          simpa [
            CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape
              p.S] using hn⟩
  · intro code T hhalt
    rcases
        seqSubroutine_haltsWithTape_inv
          hparser.left hfield.left hhalt with
      ⟨Tmid, hparserRun, hfieldReach⟩
    rcases hparser.right.right code Tmid hparserRun with
      ⟨S, hdecode, hTmid⟩
    have hcode : code = SimulatorLayout.encode S :=
      CommonGround.SimulatorLayouts.decodeComplete_eq_some_encode
        hdecode
    rcases hfieldReach with ⟨n, hn⟩
    have hfieldRun :
        fieldValidator.HaltsFromTape
          (SimulatorLayout.tape S) T := by
      refine ⟨n, ?_⟩
      constructor
      · simpa [HaltsFromTapeIn,
          initial, hTmid,
          CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape
            S] using congrArg Configuration.state hn
      · simpa [HaltsFromTapeIn,
          initial, hTmid,
          CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape
            S] using congrArg Configuration.tape hn
    rcases hfield.right.right S T hfieldRun with
      ⟨L, hinput, hT⟩
    exact
      ⟨{ S := S, L := L, input := hinput },
        by simpa [SelectedMergeInputValidatorInputCode] using hcode,
        hT⟩

theorem selectedMergeInputValidatorExactConstruction_of_parser_fieldValidator
    (hparser :
      CommonGround.SimulatorLayouts.ClosedRecognizerConstruction)
    (hfield :
      SelectedMergeInputFieldValidatorConstruction) :
    SelectedMergeInputValidatorExactConstruction := by
  rcases hparser with ⟨parser, hparser⟩
  rcases hfield with ⟨fieldValidator, hfield⟩
  exact
    ⟨SelectedMergeInputValidatorFromParserField
        parser fieldValidator,
      selectedMergeInputValidatorExactSpec_of_parser_fieldValidator
        hparser hfield⟩

theorem selectedMergeInputValidatorPrimitiveRightShiftedConstruction_of_exact
    (h : SelectedMergeInputValidatorExactConstruction) :
    SelectedMergeInputValidatorPrimitiveRightShiftedConstruction := by
  rcases h with ⟨validator, hvalidator⟩
  refine ⟨validator, ?_⟩
  exact
    CommonGround.CodeWordEmitters.rightShiftedOutputCompiled_of_indexed_tape_spec
      hvalidator.left.left
      hvalidator.left.right
      SelectedMergeInputValidatorInputCode
      SelectedMergeInputValidatorOutputCode
      SelectedMergeInputValidatorOutputTape
      (by
        intro p
        rfl)
      (by
        intro p
        simpa [SelectedMergeInputValidatorInputCode,
          SimulatorLayout.asBoolInput] using
          hvalidator.right.left p)
      hvalidator.right.right
      (by
        intro code out
        constructor
        · intro htransform
          rcases
              (selectedMergeInputValidatorPrimitive_transform_eq_some_iff
                code out).mp htransform with
            ⟨S, L, hcode, hinput, hout⟩
          exact
            ⟨{ S := S, L := L, input := hinput },
              by simpa [SelectedMergeInputValidatorInputCode] using hcode,
              by simpa [SelectedMergeInputValidatorOutputCode] using hout⟩
        · intro hindexed
          rcases hindexed with ⟨p, hcode, hout⟩
          exact
            (selectedMergeInputValidatorPrimitive_transform_eq_some_iff
              code out).mpr
              ⟨p.S, p.L,
                by simpa [SelectedMergeInputValidatorInputCode] using hcode,
                p.input,
                by simpa [SelectedMergeInputValidatorOutputCode] using hout⟩)

def SelectedMergeInputValidatorFromRightShifted
    (validator : MachineDescription) : MachineDescription :=
  seqSubroutine validator
    ExactIdentityDescription Direction.left

theorem selectedMergeInputValidatorSpec_of_rightShifted
    {validator : MachineDescription}
    (hvalidator :
      RightShiftedOutputCompiledSubroutineByDescription
        SelectedMergeInputValidatorPrimitive validator) :
    SelectedMergeInputValidatorSpec
      (SelectedMergeInputValidatorFromRightShifted validator) := by
  have hidentityReady :
      ExactIdentityDescription.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  have hvalidatorReady : validator.SubroutineReady :=
    rightShiftedOutputCompiledSubroutineByDescription_subroutineReady
      hvalidator
  constructor
  · exact
      seqSubroutine_subroutineReady
        hvalidatorReady hidentityReady
  constructor
  · intro S L hinput
    have htransform :
        SelectedMergeInputValidatorPrimitive.transform
            (SimulatorLayout.encode S) =
          some (SimulatorLayout.encode S) :=
      (selectedMergeInputValidatorPrimitive_transform_eq_some_iff
        (SimulatorLayout.encode S)
        (SimulatorLayout.encode S)).mpr
        ⟨S, L, rfl, hinput, rfl⟩
    have hright :
        validator.HaltsWithTape
          (SimulatorLayout.asBoolInput S)
          (Tape.move Direction.right
            (Tape.input
              (encodeCodeWordAsInput
                (SimulatorLayout.encode S)))) := by
      simpa [SimulatorLayout.asBoolInput] using
        rightShiftedOutputCompiled_haltsWithTape_of_transform
          hvalidator htransform
    have hbridge :
        Tape.move Direction.left
            (Tape.move Direction.right
              (Tape.input
                (encodeCodeWordAsInput
                  (SimulatorLayout.encode S)))) =
          SimulatorLayout.tape S := by
      simpa [SimulatorLayout.tape] using
        CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape S
    have hidentity :
        exists n : Nat,
          ExactIdentityDescription.runConfig n
              { state := ExactIdentityDescription.start
                tape :=
                  Tape.move Direction.left
                    (Tape.move Direction.right
                      (Tape.input
                        (encodeCodeWordAsInput
                          (SimulatorLayout.encode S)))) } =
            { state := ExactIdentityDescription.halt
              tape := SimulatorLayout.tape S } := by
      rcases
          CommonGround.Identity.exactIdentityDescription_run_from_start
            (SimulatorLayout.tape S) with
        ⟨n, hn⟩
      exact ⟨n, by simpa [hbridge] using hn⟩
    simpa [SelectedMergeInputValidatorFromRightShifted] using
      seqSubroutine_haltsWithTape_of_haltsWithTape
        hvalidatorReady hidentityReady hright hidentity
  · intro S T hhalt
    rcases
        seqSubroutine_haltsWithTape_inv
          hvalidatorReady hidentityReady
          (by simpa [SelectedMergeInputValidatorFromRightShifted] using hhalt) with
      ⟨Tmid, hvalidatorRun, hidentityReach⟩
    rcases
        rightShiftedOutputCompiledSubroutineByDescription_haltsWithTape_inv
          hvalidator hvalidatorRun with
      ⟨out, htransform, hTmid⟩
    rcases
        (selectedMergeInputValidatorPrimitive_transform_eq_some_iff
          (SimulatorLayout.encode S) out).mp htransform with
      ⟨S', L, hcode, hinput, hout⟩
    have hS : S' = S := by
      have hsome :
          some S = some S' := by
        calc
          some S =
              SimulatorLayout.decodeComplete
                (SimulatorLayout.encode S) := by
                rw [CommonGround.SimulatorLayouts.decodeComplete_encode]
          _ =
              SimulatorLayout.decodeComplete
                (SimulatorLayout.encode S') := by
                rw [hcode]
          _ = some S' := by
                rw [CommonGround.SimulatorLayouts.decodeComplete_encode]
      cases hsome
      rfl
    subst S'
    subst out
    have hTleft :
        T =
          Tape.move Direction.left
            (Tape.move Direction.right
              (Tape.input
                (encodeCodeWordAsInput
                  (SimulatorLayout.encode S)))) := by
      rcases hidentityReach with ⟨n, hn⟩
      have hrun :=
        CommonGround.Identity.exactIdentityDescription_runConfig_from_start
          n (Tape.move Direction.left Tmid)
      rw [hrun] at hn
      have htape :
          Tape.move Direction.left Tmid = T :=
        congrArg Configuration.tape hn
      rw [hTmid] at htape
      exact htape.symm
    have hT : T = SimulatorLayout.tape S := by
      rw [hTleft]
      simpa [SimulatorLayout.tape] using
        CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape S
    exact ⟨L, hinput, hT⟩

theorem selectedMergeInputValidatorConstruction_of_rightShifted
    (h :
      SelectedMergeInputValidatorPrimitiveRightShiftedConstruction) :
    SelectedMergeInputValidatorConstruction := by
  rcases h with ⟨validator, hvalidator⟩
  exact
    ⟨SelectedMergeInputValidatorFromRightShifted validator,
      selectedMergeInputValidatorSpec_of_rightShifted hvalidator⟩

def SelectedMergeParserFromSimulatorValidator
    (parser validator : MachineDescription) : MachineDescription :=
  seqSubroutine parser validator Direction.left

theorem selectedMergeParserSpec_of_simulatorParser_validator
    {parser validator : MachineDescription}
    (hparser :
      CommonGround.SimulatorLayouts.ClosedRecognizerSpec
        parser)
    (hvalidator : SelectedMergeInputValidatorSpec validator) :
    SelectedMergeParserSpec
      (SelectedMergeParserFromSimulatorValidator parser validator) := by
  have hrunnerReady :
      (SelectedMergeParserFromSimulatorValidator
        parser validator).SubroutineReady :=
    seqSubroutine_subroutineReady
      hparser.left hvalidator.left
  constructor
  · exact hrunnerReady
  constructor
  · intro S L hinput
    have hparserRun :
        parser.HaltsWithTape
          (SimulatorLayout.asBoolInput S)
          (CommonGround.SimulatorLayouts.handoffTape S) := by
      simpa [CommonGround.SimulatorLayouts.bits,
        CommonGround.SimulatorLayouts.encode,
        CommonGround.LayoutTapes.Bits,
        SimulatorLayout.asBoolInput] using
        hparser.right.left S
    have hvalidatorRun :
        validator.HaltsWithTape
          (SimulatorLayout.asBoolInput S)
          (SimulatorLayout.tape S) :=
      hvalidator.right.left S L hinput
    rcases runConfig_eq_halt_of_haltsWithTape
      hvalidatorRun with ⟨n, hn⟩
    exact
      seqSubroutine_haltsWithTape_of_haltsWithTape
        hparser.left hvalidator.left hparserRun
        ⟨n, by
          simpa [
            CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape
              S] using hn⟩
  · intro code T hhalt
    rcases
        seqSubroutine_haltsWithTape_inv
          hparser.left hvalidator.left hhalt with
      ⟨Tmid, hparserRun, hvalidatorReach⟩
    rcases hparser.right.right code Tmid hparserRun with
      ⟨S, hdecode, hTmid⟩
    have hcode : code = SimulatorLayout.encode S :=
      CommonGround.SimulatorLayouts.decodeComplete_eq_some_encode
        hdecode
    rcases hvalidatorReach with ⟨n, hn⟩
    have hvalidatorRun :
        validator.HaltsWithTape
          (SimulatorLayout.asBoolInput S) T := by
      refine ⟨n, ?_⟩
      constructor
      · simpa [HaltsWithTapeIn,
          initial, hTmid,
          CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape
            S] using congrArg Configuration.state hn
      · simpa [HaltsWithTapeIn,
          initial, hTmid,
          CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape
            S] using congrArg Configuration.tape hn
    rcases hvalidator.right.right S T hvalidatorRun with
      ⟨L, hinput, hT⟩
    exact ⟨S, L, hcode, hinput, hT⟩

theorem selectedMergeParserConstruction_of_simulatorParser_validator
    (hparser :
      CommonGround.SimulatorLayouts.ClosedRecognizerConstruction)
    (hvalidator : SelectedMergeInputValidatorConstruction) :
    SelectedMergeParserConstruction := by
  rcases hparser with ⟨parser, hparser⟩
  rcases hvalidator with ⟨validator, hvalidator⟩
  exact
    ⟨SelectedMergeParserFromSimulatorValidator parser validator,
      selectedMergeParserSpec_of_simulatorParser_validator
        hparser hvalidator⟩

def SelectedMergeEmitterSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  ReadySpec emitter ∧
    (forall S : SimulatorLayout,
     forall L : DovetailLayout,
      decodeCodeWordAsInput S.input =
        some (DovetailLayout.encode L) ->
      emitter.HaltsWithTape
        (SimulatorLayout.asBoolInput S)
        (SelectedMergeOutputTape useAccept S L)) ∧
      forall S : SimulatorLayout,
      forall L : DovetailLayout,
      forall T : Tape Bool,
        decodeCodeWordAsInput S.input =
          some (DovetailLayout.encode L) ->
        emitter.HaltsWithTape
            (SimulatorLayout.asBoolInput S) T ->
          T = SelectedMergeOutputTape useAccept S L

structure SelectedMergeEmitterPayload where
  S : SimulatorLayout
  L : DovetailLayout
  input :
    decodeCodeWordAsInput S.input =
      some (DovetailLayout.encode L)

def SelectedMergeEmitterInputBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  SimulatorLayout.asBoolInput p.S

def SelectedMergeEmitterOutputCode
    (useAccept : Bool)
    (p : SelectedMergeEmitterPayload) : Word MachineCodeSymbol :=
  SelectedMergeOutputCode useAccept p.S p.L

def SelectedMergeCanonicalEmitterSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  CanonicalLayouts.EmitterSpec
    SelectedMergeEmitterInputBits
    (SelectedMergeEmitterOutputCode useAccept)
    emitter

def SelectedMergeCanonicalExactEmitterSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  CanonicalLayouts.ExactEmitterSpec
    SelectedMergeEmitterInputBits
    (SelectedMergeEmitterOutputCode useAccept)
    emitter

def SelectedMergeEmitterConstruction : Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedMergeEmitterSpec useAccept emitter

theorem selectedMergeEmitterSpec_iff_canonical
    (useAccept : Bool) (emitter : MachineDescription) :
    SelectedMergeEmitterSpec useAccept emitter ↔
      SelectedMergeCanonicalEmitterSpec useAccept emitter := by
  constructor
  · intro h
    constructor
    · exact h.left
    constructor
    · intro p
      simpa [SelectedMergeCanonicalEmitterSpec,
        SelectedMergeEmitterInputBits, SelectedMergeEmitterOutputCode,
        CanonicalLayouts.OutputTape, SelectedMergeOutputTape] using
        h.right.left p.S p.L p.input
    · intro p T hhalt
      simpa [SelectedMergeCanonicalEmitterSpec,
        SelectedMergeEmitterInputBits, SelectedMergeEmitterOutputCode,
        CanonicalLayouts.OutputTape, SelectedMergeOutputTape] using
        h.right.right p.S p.L T p.input hhalt
  · intro h
    constructor
    · exact h.left
    constructor
    · intro S L hinput
      exact
        h.right.left
          { S := S, L := L, input := hinput }
    · intro S L T hinput hhalt
      exact
        h.right.right
          { S := S, L := L, input := hinput } T hhalt

def SelectedMergeEquivEmitterSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      emitter.HaltsFromTapeEquiv
        (SimulatorLayout.tape p.S)
        (SelectedMergeEquivOutputTape useAccept p.S p.L)

def SelectedMergeEquivEmitterConstruction : Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedMergeEquivEmitterSpec useAccept emitter

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
