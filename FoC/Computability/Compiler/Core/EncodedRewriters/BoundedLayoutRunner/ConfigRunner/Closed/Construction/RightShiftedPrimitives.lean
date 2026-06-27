import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.PhaseAdapters
import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.SelectedProjectionTailProjector
import FoC.Computability.Compiler.Core.CommonGround

set_option doc.verso true

/-!
# Bounded runner right-shifted primitive adapters
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace BoundedLayoutRunner

def SelectedProjectionPrimitiveRightShiftedConstruction : Prop :=
  forall useAccept : Bool,
    exists runner : MachineDescription,
      RightShiftedOutputCompiledSubroutineByDescription
        (SelectedProjectionPrimitive useAccept)
        runner

def AcceptProjectionPrimitiveRightShiftedConstruction : Prop :=
  exists runner : MachineDescription,
    RightShiftedOutputCompiledSubroutineByDescription
      AcceptProjectionPrimitive
      runner

def RejectProjectionPrimitiveRightShiftedConstruction : Prop :=
  exists runner : MachineDescription,
    RightShiftedOutputCompiledSubroutineByDescription
      RejectProjectionPrimitive
      runner

def SelectedMergePrimitiveRightShiftedConstruction : Prop :=
  forall useAccept : Bool,
    exists runner : MachineDescription,
      RightShiftedOutputCompiledSubroutineByDescription
        (SelectedMergePrimitive useAccept)
        runner

def AcceptMergePrimitiveRightShiftedConstruction : Prop :=
  exists runner : MachineDescription,
    RightShiftedOutputCompiledSubroutineByDescription
      AcceptMergePrimitive
      runner

def RejectMergePrimitiveRightShiftedConstruction : Prop :=
  exists runner : MachineDescription,
    RightShiftedOutputCompiledSubroutineByDescription
      RejectMergePrimitive
      runner

theorem selectedProjectionFiniteDescriptionConstruction_of_rightShifted
    (h : SelectedProjectionPrimitiveRightShiftedConstruction) :
    SelectedProjectionFiniteDescriptionConstruction := by
  intro useAccept
  rcases h useAccept with ⟨runner, hrunner⟩
  refine ⟨runner, ?_⟩
  constructor
  · exact ⟨hrunner.left, hrunner.right.left⟩
  constructor
  · intro L
    have htransform :
        (SelectedProjectionPrimitive useAccept).transform
            (MachineDescription.DovetailLayout.encode L) =
          some (SelectedProjectionOutputCode useAccept L) :=
      (SelectedProjectionPrimitive_transform_eq_some_iff
        useAccept
        (MachineDescription.DovetailLayout.encode L)
        (SelectedProjectionOutputCode useAccept L)).mpr
        ⟨L, rfl, by simp [SelectedProjectionOutputCode]⟩
    have hexact := rightShiftedOutputCompiled_haltsWithTape_of_transform hrunner htransform
    have hequiv := MachineDescription.HaltsFromTape.toEquiv hexact
    simpa [ParsedLayoutBits, SelectedProjectionOutputTape] using hequiv
  · intro code T hhalt
    rcases hrunner.right.right.right code T hhalt with
      ⟨out, htransform, hT⟩
    rcases
        (SelectedProjectionPrimitive_transform_eq_some_iff
          useAccept code out).mp htransform with
      ⟨L, hcode, hout⟩
    refine ⟨L, hcode, ?_⟩
    rw [hT]
    simpa [SelectedProjectionOutputTape, SelectedProjectionOutputCode,
      hout] using Tape.Equiv.refl _

theorem selectedMergeFiniteDescriptionConstruction_of_rightShifted
    (h : SelectedMergePrimitiveRightShiftedConstruction) :
    SelectedMergeFiniteDescriptionConstruction := by
  intro useAccept
  rcases h useAccept with ⟨runner, hrunner⟩
  refine ⟨runner, ?_⟩
  constructor
  · exact ⟨hrunner.left, hrunner.right.left⟩
  constructor
  · intro S L hinput
    have htransform :
        (SelectedMergePrimitive useAccept).transform
            (MachineDescription.SimulatorLayout.encode S) =
          some (SelectedMergeOutputCode useAccept S L) :=
      (SelectedMergePrimitive_transform_eq_some_iff
        useAccept
        (MachineDescription.SimulatorLayout.encode S)
        (SelectedMergeOutputCode useAccept S L)).mpr
        ⟨S, L, rfl, hinput, rfl⟩
    simpa [MachineDescription.SimulatorLayout.asBoolInput,
      SelectedMergeOutputTape] using
      rightShiftedOutputCompiled_haltsWithTape_of_transform
        hrunner htransform
  · intro code T hhalt
    rcases hrunner.right.right.right code T hhalt with
      ⟨out, htransform, hT⟩
    rcases
        (SelectedMergePrimitive_transform_eq_some_iff
          useAccept code out).mp htransform with
      ⟨S, L, hcode, hinput, hout⟩
    refine ⟨S, L, hcode, hinput, ?_⟩
    simpa [SelectedMergeOutputTape, hout] using hT

theorem selectedMergePrimitiveRightShiftedConstruction_of_finiteDescription
    (h : SelectedMergeFiniteDescriptionConstruction) :
    SelectedMergePrimitiveRightShiftedConstruction := by
  intro useAccept
  rcases h useAccept with ⟨runner, hrunner⟩
  exact ⟨runner, selectedMergeRightShifted_of_spec hrunner⟩

def SelectedProjectionPrimitiveExactSpec
    (useAccept : Bool)
    (runner : MachineDescription) : Prop :=
  ReadySpec runner ∧
    (forall L : MachineDescription.DovetailLayout,
      runner.HaltsWithTape
        (ParsedLayoutBits L)
        (SelectedProjectionOutputTape useAccept L)) ∧
      forall code : Word MachineCodeSymbol,
      forall T : Tape Bool,
        runner.HaltsWithTape
            (MachineDescription.encodeCodeWordAsInput code) T ->
          exists L : MachineDescription.DovetailLayout,
            code = MachineDescription.DovetailLayout.encode L ∧
              T = SelectedProjectionOutputTape useAccept L

def SelectedProjectionPrimitiveExactConstruction : Prop :=
  forall useAccept : Bool,
    exists runner : MachineDescription,
      SelectedProjectionPrimitiveExactSpec useAccept runner

def SelectedProjectionEmitterSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  ReadySpec emitter ∧
    (forall L : MachineDescription.DovetailLayout,
      emitter.HaltsWithTape
        (ParsedLayoutBits L)
        (SelectedProjectionOutputTape useAccept L)) ∧
      forall L : MachineDescription.DovetailLayout,
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
    forall L : MachineDescription.DovetailLayout,
      emitter.HaltsFromTape
        (ParsedLayoutCheckedTape L)
        (SelectedProjectionOutputTape useAccept L)

def SelectedProjectionCheckedEmitterConstruction : Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedProjectionCheckedEmitterSpec useAccept emitter

def SelectedProjectionCheckedProjectorExactSpec
    (useAccept : Bool)
    (projector : MachineDescription) : Prop :=
  projector.SubroutineReady ∧
    forall L : MachineDescription.DovetailLayout,
      projector.HaltsFromTape
        (ParsedLayoutCheckedTape L)
        (MachineDescription.SimulatorLayout.tape
          (SelectedProjectionSimulatorLayout useAccept L))

def SelectedProjectionCheckedProjectorExactConstruction : Prop :=
  forall useAccept : Bool,
    exists projector : MachineDescription,
      SelectedProjectionCheckedProjectorExactSpec useAccept projector

def SelectedProjectionCheckedEmitterFromProjector
    (projector : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine projector
    MachineDescription.ExactIdentityDescription Direction.right

theorem selectedProjectionOutputCode_true
    (L : MachineDescription.DovetailLayout) :
    SelectedProjectionOutputCode true L =
      MachineDescription.SimulatorLayout.encode
        (AcceptSimulatorLayout L) := by
  rfl

theorem selectedProjectionOutputCode_false
    (L : MachineDescription.DovetailLayout) :
    SelectedProjectionOutputCode false L =
      MachineDescription.SimulatorLayout.encode
        (RejectSimulatorLayout L) := by
  rfl

theorem selectedProjectionOutputTape_true
    (L : MachineDescription.DovetailLayout) :
    SelectedProjectionOutputTape true L =
      Tape.move Direction.right
        (MachineDescription.SimulatorLayout.tape
          (AcceptSimulatorLayout L)) := by
  rfl

theorem selectedProjectionOutputTape_false
    (L : MachineDescription.DovetailLayout) :
    SelectedProjectionOutputTape false L =
      Tape.move Direction.right
        (MachineDescription.SimulatorLayout.tape
          (RejectSimulatorLayout L)) := by
  rfl

theorem selectedProjectionOutputTape_eq_simulator_tape
    (useAccept : Bool) (L : MachineDescription.DovetailLayout) :
    SelectedProjectionOutputTape useAccept L =
      Tape.move Direction.right
        (MachineDescription.SimulatorLayout.tape
          (SelectedProjectionSimulatorLayout useAccept L)) := by
  cases useAccept <;>
    rfl

theorem selectedProjectionCheckedEmitterSpec_of_projector
    {useAccept : Bool} {projector : MachineDescription}
    (hprojector :
      SelectedProjectionCheckedProjectorExactSpec useAccept projector) :
    SelectedProjectionCheckedEmitterSpec useAccept
      (SelectedProjectionCheckedEmitterFromProjector projector) := by
  have hid :
      MachineDescription.ExactIdentityDescription.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  constructor
  · exact
      MachineDescription.seqSubroutine_subroutineReady
        hprojector.left hid
  · intro L
    have hprojectorRun := hprojector.right L
    have hidentityReach :
        exists nB : Nat,
          MachineDescription.ExactIdentityDescription.runConfig nB
              { state := MachineDescription.ExactIdentityDescription.start
                tape :=
                  Tape.move Direction.right
                    (MachineDescription.SimulatorLayout.tape
                      (SelectedProjectionSimulatorLayout useAccept L)) } =
            { state := MachineDescription.ExactIdentityDescription.halt
              tape := SelectedProjectionOutputTape useAccept L } := by
      simpa [selectedProjectionOutputTape_eq_simulator_tape] using
        CommonGround.Identity.exactIdentityDescription_run_from_start
          (Tape.move Direction.right
            (MachineDescription.SimulatorLayout.tape
              (SelectedProjectionSimulatorLayout useAccept L)))
    simpa [SelectedProjectionCheckedEmitterFromProjector] using
      MachineDescription.seqSubroutine_haltsFromTape_of_haltsFromTape
        hprojector.left hid hprojectorRun hidentityReach

theorem selectedProjectionCheckedEmitterConstruction_of_projector
    (hprojector :
      SelectedProjectionCheckedProjectorExactConstruction) :
    SelectedProjectionCheckedEmitterConstruction := by
  intro useAccept
  rcases hprojector useAccept with ⟨projector, hprojectorSpec⟩
  exact
    ⟨SelectedProjectionCheckedEmitterFromProjector projector,
      selectedProjectionCheckedEmitterSpec_of_projector hprojectorSpec⟩

def SelectedProjectionConfig
    (useAccept : Bool)
    (L : MachineDescription.DovetailLayout) :
    MachineDescription.Configuration :=
  if useAccept then L.acceptConfig else L.rejectConfig

def SelectedProjectionHit
    (useAccept : Bool)
    (L : MachineDescription.DovetailLayout) : Bool :=
  if useAccept then L.acceptHit else L.rejectHit

def SelectedProjectionOutputSuffix
    (useAccept : Bool)
    (L : MachineDescription.DovetailLayout) :
    Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend L.stage
    (MachineDescription.encodeConfigurationAppend
      (SelectedProjectionConfig useAccept L)
      (MachineDescription.encodeBoolAppend
        (SelectedProjectionHit useAccept L) []))

theorem selectedProjectionSimulatorLayout_eq
    (useAccept : Bool)
    (L : MachineDescription.DovetailLayout) :
    SelectedProjectionSimulatorLayout useAccept L =
      { input := ParsedLayoutBits L
        stage := L.stage
        config := SelectedProjectionConfig useAccept L
        hit := SelectedProjectionHit useAccept L } := by
  cases useAccept <;>
    rfl

theorem selectedProjectionOutputCode_eq_fields
    (useAccept : Bool)
    (L : MachineDescription.DovetailLayout) :
    SelectedProjectionOutputCode useAccept L =
      MachineCodeSymbol.header ::
        MachineDescription.encodeBoolWordAppend (ParsedLayoutBits L)
          (SelectedProjectionOutputSuffix useAccept L) := by
  rw [SelectedProjectionOutputCode,
    selectedProjectionSimulatorLayout_eq]
  rfl

theorem selectedProjectionOutputSuffix_eq_fields
    (useAccept : Bool)
    (L : MachineDescription.DovetailLayout) :
    SelectedProjectionOutputSuffix useAccept L =
      MachineDescription.encodeNatAppend L.stage
        (MachineDescription.encodeConfigurationAppend
          (SelectedProjectionConfig useAccept L)
          (MachineDescription.encodeBoolAppend
            (SelectedProjectionHit useAccept L) [])) := by
  rfl

theorem selectedProjectionOutputBits_eq_quoter_bits
    (useAccept : Bool)
    (L : MachineDescription.DovetailLayout) :
    exists b : Bool,
    exists rest : Word Bool,
      ParsedLayoutBits L = b :: rest ∧
        MachineDescription.encodeCodeWordAsInput
            (SelectedProjectionOutputCode useAccept L) =
          List.append
            (MachineDescription.encodeCodeSymbolAsInput
              MachineCodeSymbol.header)
            (FoC.Computability.CommonGround.BoolWordQuoters.checkedNonemptyBoolWordQuoteDirectSourceBits
                b rest (SelectedProjectionOutputSuffix useAccept L)) := by
  rcases parsedLayoutBits_eq_false_false_tail L with
    ⟨tail, htail⟩
  refine ⟨false, false :: tail, htail, ?_⟩
  rw [selectedProjectionOutputCode_eq_fields, htail]
  simp [MachineDescription.encodeCodeWordAsInput,
    FoC.Computability.CommonGround.BoolWordQuoters.checkedNonemptyBoolWordQuoteDirectSourceBits_eq]

def SelectedProjectionInputQuoterSpec
    (quoter : MachineDescription) : Prop :=
  quoter.SubroutineReady ∧
    forall L : MachineDescription.DovetailLayout,
      quoter.HaltsFromTape
        (ParsedLayoutCheckedTape L)
        (SelectedProjectionTailProjector.sourceTape L
          ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
            some))

def SelectedProjectionInputQuoterConstruction : Prop :=
  exists quoter : MachineDescription,
    SelectedProjectionInputQuoterSpec quoter

def SelectedProjectionOutputReturnSpec
    (useAccept : Bool)
    (returner : MachineDescription) : Prop :=
  returner.SubroutineReady ∧
    forall L : MachineDescription.DovetailLayout,
      returner.HaltsFromTape
        (SelectedProjectionTailProjector.outputTape useAccept L
          ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
            some))
        (MachineDescription.SimulatorLayout.tape
          (SelectedProjectionSimulatorLayout useAccept L))

def SelectedProjectionOutputReturnConstruction : Prop :=
  forall useAccept : Bool,
    exists returner : MachineDescription,
      SelectedProjectionOutputReturnSpec useAccept returner

def SelectedProjectionCheckedProjectorComponentConstruction : Prop :=
  SelectedProjectionInputQuoterConstruction ∧
    SelectedProjectionTailProjector.TailProjectorExactConstruction ∧
      SelectedProjectionOutputReturnConstruction

theorem not_selectedProjectionCheckedProjectorComponentConstruction :
    ¬ SelectedProjectionCheckedProjectorComponentConstruction := by
  intro hcomponents
  exact
    SelectedProjectionTailProjector.not_tailProjectorExactConstruction
      hcomponents.right.left

def SelectedProjectionCheckedProjectorFromComponents
    (quoter tail returner : MachineDescription) : MachineDescription :=
  SeqViaCanonical (SeqViaCanonical quoter tail) returner

theorem selectedProjectionCheckedProjectorExactSpec_of_components
    {useAccept : Bool}
    {quoter tail returner : MachineDescription}
    (hquoter : SelectedProjectionInputQuoterSpec quoter)
    (htail :
      SelectedProjectionTailProjector.TailProjectorExactSpec
        useAccept tail)
    (hreturn : SelectedProjectionOutputReturnSpec useAccept returner) :
    SelectedProjectionCheckedProjectorExactSpec useAccept
      (SelectedProjectionCheckedProjectorFromComponents
        quoter tail returner) := by
  let baseLeft :=
    fun L : MachineDescription.DovetailLayout =>
      (SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
        some
  have hquoterTailReady : (SeqViaCanonical quoter tail).SubroutineReady :=
    SeqViaCanonical_subroutineReady hquoter.left htail.left
  constructor
  · exact
      SeqViaCanonical_subroutineReady hquoterTailReady hreturn.left
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
          (SelectedProjectionTailProjector.outputTape useAccept L
            (baseLeft L)) :=
      htail.right L (baseLeft L)
    have hbridgeTail :
        Tape.move Direction.left
            (Tape.move Direction.right
              (SelectedProjectionTailProjector.sourceTape L
                (baseLeft L))) =
          SelectedProjectionTailProjector.sourceTape L
            (baseLeft L) :=
      SelectedProjectionTailProjector.sourceTape_move_left_move_right
        L (baseLeft L)
    have hquoterTailRun :
        (SeqViaCanonical quoter tail).HaltsFromTape
          (ParsedLayoutCheckedTape L)
          (SelectedProjectionTailProjector.outputTape useAccept L
            (baseLeft L)) :=
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        hquoter.left htail.left hquoterRun hbridgeTail htailRun
    have hreturnRun :
        returner.HaltsFromTape
          (SelectedProjectionTailProjector.outputTape useAccept L
            (baseLeft L))
          (MachineDescription.SimulatorLayout.tape
            (SelectedProjectionSimulatorLayout useAccept L)) :=
      hreturn.right L
    have hbridgeReturn :
        Tape.move Direction.left
            (Tape.move Direction.right
              (SelectedProjectionTailProjector.outputTape useAccept L
                (baseLeft L))) =
          SelectedProjectionTailProjector.outputTape useAccept L
            (baseLeft L) :=
      SelectedProjectionTailProjector.outputTape_move_left_move_right
        useAccept L (baseLeft L)
    simpa [SelectedProjectionCheckedProjectorFromComponents] using
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        hquoterTailReady hreturn.left
        hquoterTailRun hbridgeReturn hreturnRun

theorem selectedProjectionCheckedProjectorExactConstruction_of_components
    (hcomponents :
      SelectedProjectionCheckedProjectorComponentConstruction) :
    SelectedProjectionCheckedProjectorExactConstruction := by
  intro useAccept
  rcases hcomponents with
    ⟨⟨quoter, hquoter⟩, htailConstruction, hreturnConstruction⟩
  rcases htailConstruction useAccept with ⟨tail, htail⟩
  rcases hreturnConstruction useAccept with ⟨returner, hreturn⟩
  exact
    ⟨SelectedProjectionCheckedProjectorFromComponents
        quoter tail returner,
      selectedProjectionCheckedProjectorExactSpec_of_components
        hquoter htail hreturn⟩

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

theorem selectedProjectionPrimitiveRightShiftedConstruction_of_exact
    (h : SelectedProjectionPrimitiveExactConstruction) :
    SelectedProjectionPrimitiveRightShiftedConstruction := by
  intro useAccept
  rcases h useAccept with ⟨runner, hrunner⟩
  refine ⟨runner, ?_⟩
  exact
    CommonGround.CodeWordEmitters.rightShiftedOutputCompiled_of_indexed_tape_spec
      hrunner.left.left
      hrunner.left.right
      (fun L : MachineDescription.DovetailLayout =>
        MachineDescription.DovetailLayout.encode L)
      (fun L : MachineDescription.DovetailLayout =>
        SelectedProjectionOutputCode useAccept L)
      (fun L : MachineDescription.DovetailLayout =>
        SelectedProjectionOutputTape useAccept L)
      (by
        intro L
        simp [SelectedProjectionOutputTape, SelectedProjectionOutputCode])
      hrunner.right.left
      hrunner.right.right
      (by
        intro code out
        simpa [SelectedProjectionOutputCode] using
          SelectedProjectionPrimitive_transform_eq_some_iff
            useAccept code out)

theorem selectedProjectionPrimitiveExactSpec_of_checkedParser_checkedEmitter
    {useAccept : Bool} {parser emitter : MachineDescription}
    (hparser : LayoutCheckedParserSpec parser)
    (hemitter : SelectedProjectionCheckedEmitterSpec useAccept emitter) :
    SelectedProjectionPrimitiveExactSpec useAccept
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
      simpa [MachineDescription.HaltsWithTape,
        MachineDescription.HaltsWithTapeIn,
        MachineDescription.HaltsFromTape,
        MachineDescription.HaltsFromTapeIn,
        MachineDescription.initial] using hparser.right.left L
    have hseq :
        (SeqViaCanonical parser emitter).HaltsFromTape
          (Tape.input (ParsedLayoutBits L))
          (SelectedProjectionOutputTape useAccept L) :=
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        hparser.left hemitter.left
        hparserFrom
        (parsedLayoutCheckedTape_move_left_move_right L)
        (hemitter.right L)
    simpa [MachineDescription.HaltsWithTape,
      MachineDescription.HaltsWithTapeIn,
      MachineDescription.HaltsFromTape,
      MachineDescription.HaltsFromTapeIn,
      MachineDescription.initial] using hseq
  · intro code T hhalt
    have hhaltFrom :
        (SeqViaCanonical parser emitter).HaltsFromTape
          (Tape.input (MachineDescription.encodeCodeWordAsInput code)) T := by
      simpa [MachineDescription.HaltsWithTape,
        MachineDescription.HaltsWithTapeIn,
        MachineDescription.HaltsFromTape,
        MachineDescription.HaltsFromTapeIn,
        MachineDescription.initial] using hhalt
    rcases
        SeqViaCanonical_haltsFromTape_inv
          hparser.left hemitter.left hhaltFrom with
      ⟨Tmid, hparserRun, hemitterRun⟩
    have hparserWith :
        parser.HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput code) Tmid := by
      simpa [MachineDescription.HaltsWithTape,
        MachineDescription.HaltsWithTapeIn,
        MachineDescription.HaltsFromTape,
        MachineDescription.HaltsFromTapeIn,
        MachineDescription.initial] using hparserRun
    rcases hparser.right.right code Tmid hparserWith with
      ⟨L, hdecode, hTmid⟩
    have hemitterRun' :
        emitter.HaltsFromTape
          (ParsedLayoutCheckedTape L) T := by
      rw [hTmid] at hemitterRun
      simpa [parsedLayoutCheckedTape_move_left_move_right L]
        using hemitterRun
    have hT :
        T = SelectedProjectionOutputTape useAccept L :=
      MachineDescription.haltsFromTape_functional_of_haltTransitionFree
        hemitter.left.right hemitterRun' (hemitter.right L)
    refine ⟨L, ?_, hT⟩
    exact MachineDescription.DovetailLayout.decodeComplete_eq_some_encode hdecode

theorem selectedProjectionPrimitiveExactConstruction_of_checkedParser_checkedEmitter
    (hparser : LayoutCheckedParserConstruction)
    (hemitter : SelectedProjectionCheckedEmitterConstruction) :
    SelectedProjectionPrimitiveExactConstruction := by
  intro useAccept
  rcases hparser with ⟨parser, hparser⟩
  rcases hemitter useAccept with ⟨emitter, hemits⟩
  exact
    ⟨SeqViaCanonical parser emitter,
      selectedProjectionPrimitiveExactSpec_of_checkedParser_checkedEmitter
        hparser hemits⟩

/--
Finite-machine leaf for the selected projection primitive.

The earlier checked-projector route is stronger than the public primitive
needs.  This target should validate the canonical dovetail-layout input and
emit the selected simulator-layout code one cell to the right, with the closed
direction ruling out malformed canonical code words.
-/
theorem selectedProjectionPrimitiveExactConstruction_scaffold :
    SelectedProjectionPrimitiveExactConstruction := by
  sorry

theorem selectedProjectionPrimitiveRightShiftedConstruction_core :
    SelectedProjectionPrimitiveRightShiftedConstruction := by
  exact
    selectedProjectionPrimitiveRightShiftedConstruction_of_exact
      selectedProjectionPrimitiveExactConstruction_scaffold

theorem acceptProjectionPrimitiveRightShiftedConstruction_scaffold :
    AcceptProjectionPrimitiveRightShiftedConstruction := by
  rcases selectedProjectionPrimitiveRightShiftedConstruction_core true with
    ⟨runner, hrunner⟩
  refine ⟨runner, ?_⟩
  exact
    rightShiftedOutputCompiledSubroutineByDescription_congr
      (P := SelectedProjectionPrimitive true)
      (Q := AcceptProjectionPrimitive)
      (D := runner)
      (by
        intro code
        rfl)
      hrunner

theorem rejectProjectionPrimitiveRightShiftedConstruction_scaffold :
    RejectProjectionPrimitiveRightShiftedConstruction := by
  rcases selectedProjectionPrimitiveRightShiftedConstruction_core false with
    ⟨runner, hrunner⟩
  refine ⟨runner, ?_⟩
  exact
    rightShiftedOutputCompiledSubroutineByDescription_congr
      (P := SelectedProjectionPrimitive false)
      (Q := RejectProjectionPrimitive)
      (D := runner)
      (by
        intro code
        rfl)
      hrunner

theorem selectedProjectionPrimitiveRightShiftedConstruction_scaffold :
    SelectedProjectionPrimitiveRightShiftedConstruction := by
  exact selectedProjectionPrimitiveRightShiftedConstruction_core

theorem selectedProjectionFiniteDescriptionConstruction_scaffold :
    SelectedProjectionFiniteDescriptionConstruction :=
    selectedProjectionFiniteDescriptionConstruction_of_rightShifted
    selectedProjectionPrimitiveRightShiftedConstruction_scaffold


end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
