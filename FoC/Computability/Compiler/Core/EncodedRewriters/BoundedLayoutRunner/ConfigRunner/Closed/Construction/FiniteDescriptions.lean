import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.RightShiftedPrimitives
import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.PhaseRunner

set_option doc.verso true

/-!
# Bounded runner parser and emitter adapters
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace BoundedLayoutRunner

def SelectedProjectionEquivEmitterSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  ReadySpec emitter ∧
    (forall L : MachineDescription.DovetailLayout,
      emitter.HaltsFromTapeEquiv
        (Tape.input (ParsedLayoutBits L))
        (SelectedProjectionOutputTape useAccept L)) ∧
      forall L : MachineDescription.DovetailLayout,
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
    (forall L : MachineDescription.DovetailLayout,
      emitter.HaltsFromTapeEquiv
        (ParsedLayoutCheckedTape L)
        (SelectedProjectionOutputTape useAccept L)) ∧
      forall L : MachineDescription.DovetailLayout,
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
      simpa [MachineDescription.HaltsWithTape,
        MachineDescription.HaltsWithTapeIn,
        MachineDescription.HaltsFromTape,
        MachineDescription.HaltsFromTapeIn,
        MachineDescription.initial] using hemitter.right.left L
    exact MachineDescription.HaltsFromTape.toEquiv hfrom
  · intro L T hhalt
    have hwith :
        emitter.HaltsWithTape (ParsedLayoutBits L) T := by
      simpa [MachineDescription.HaltsWithTape,
        MachineDescription.HaltsWithTapeIn,
        MachineDescription.HaltsFromTape,
        MachineDescription.HaltsFromTapeIn,
        MachineDescription.initial] using hhalt
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
        MachineDescription.HaltsFromTapeEquiv_of_input_equiv
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
        MachineDescription.HaltsFromTapeEquiv_of_input_equiv
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
    exact MachineDescription.HaltsFromTape.toEquiv (hemitter.right L)
  · intro L T hhalt
    have hT :
        T = SelectedProjectionOutputTape useAccept L :=
      MachineDescription.haltsFromTape_functional_of_haltTransitionFree
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
      simpa [MachineDescription.HaltsWithTape,
        MachineDescription.HaltsWithTapeIn,
        MachineDescription.HaltsFromTape,
        MachineDescription.HaltsFromTapeIn,
        MachineDescription.initial] using hparser.right.left L
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
        (MachineDescription.HaltsFromTape.toEquiv hparserFrom)
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
        MachineDescription.HaltsFromTapeEquiv_of_input_equiv
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
      simpa [MachineDescription.HaltsWithTape,
        MachineDescription.HaltsWithTapeIn,
        MachineDescription.HaltsFromTape,
        MachineDescription.HaltsFromTapeIn,
        MachineDescription.initial] using hparser.right.left L
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
    (forall S : MachineDescription.SimulatorLayout,
     forall L : MachineDescription.DovetailLayout,
      MachineDescription.decodeCodeWordAsInput S.input =
        some (MachineDescription.DovetailLayout.encode L) ->
      parser.HaltsWithTape
        (MachineDescription.SimulatorLayout.asBoolInput S)
        (MachineDescription.SimulatorLayout.tape S)) ∧
      forall code : Word MachineCodeSymbol,
      forall T : Tape Bool,
        parser.HaltsWithTape
            (MachineDescription.encodeCodeWordAsInput code) T ->
          exists S : MachineDescription.SimulatorLayout,
          exists L : MachineDescription.DovetailLayout,
            code = MachineDescription.SimulatorLayout.encode S ∧
              MachineDescription.decodeCodeWordAsInput S.input =
                some (MachineDescription.DovetailLayout.encode L) ∧
              T = MachineDescription.SimulatorLayout.tape S

def SelectedMergeParserConstruction : Prop :=
  exists parser : MachineDescription,
    SelectedMergeParserSpec parser

def SelectedMergeForwardParserSpec
    (parser : MachineDescription) : Prop :=
  parser.SubroutineReady ∧
    forall S : MachineDescription.SimulatorLayout,
    forall L : MachineDescription.DovetailLayout,
      MachineDescription.decodeCodeWordAsInput S.input =
        some (MachineDescription.DovetailLayout.encode L) ->
      parser.HaltsWithTape
        (MachineDescription.SimulatorLayout.asBoolInput S)
        (MachineDescription.SimulatorLayout.tape S)

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
      MachineDescription.ExactIdentityDescription := by
  constructor
  · exact CommonGround.Identity.exactIdentityDescription_subroutineReady
  · intro S _L _hinput
    simpa [MachineDescription.SimulatorLayout.tape,
      MachineDescription.HaltsWithTape, MachineDescription.HaltsFromTape,
      MachineDescription.HaltsWithTapeIn,
      MachineDescription.HaltsFromTapeIn,
      MachineDescription.initial] using
      CommonGround.Identity.exactIdentityDescription_haltsFromTape
        (MachineDescription.SimulatorLayout.tape S)

theorem selectedMergeForwardParserConstruction_identity :
    SelectedMergeForwardParserConstruction :=
  ⟨MachineDescription.ExactIdentityDescription,
    selectedMergeForwardParserSpec_identity⟩

def SelectedMergeForwardParserFromSimulatorParser
    (parser : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine
    parser MachineDescription.ExactIdentityDescription Direction.left

theorem selectedMergeForwardParserSpec_of_simulatorParser
    {parser : MachineDescription}
    (hparser :
      CommonGround.SimulatorLayouts.ClosedRecognizerSpec
        parser) :
    SelectedMergeForwardParserSpec
      (SelectedMergeForwardParserFromSimulatorParser parser) := by
  let identity := MachineDescription.ExactIdentityDescription
  have hid : identity.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  constructor
  · exact
      MachineDescription.seqSubroutine_subroutineReady
        hparser.left hid
  · intro S L _hinput
    have hparserRun :
        parser.HaltsWithTape
          (MachineDescription.SimulatorLayout.asBoolInput S)
          (CommonGround.SimulatorLayouts.handoffTape S) := by
      simpa [CommonGround.SimulatorLayouts.bits,
        CommonGround.SimulatorLayouts.encode,
        CommonGround.LayoutTapes.Bits,
        MachineDescription.SimulatorLayout.asBoolInput] using
        hparser.right.left S
    have hhandoff :
        Tape.move Direction.left
            (CommonGround.SimulatorLayouts.handoffTape S) =
          MachineDescription.SimulatorLayout.tape S := by
      simpa [MachineDescription.SimulatorLayout.tape] using
        CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape S
    exact
      MachineDescription.seqSubroutine_haltsWithTape_of_haltsWithTape
        hparser.left hid hparserRun
        (by
          rw [hhandoff]
          exact
            CommonGround.Identity.exactIdentityDescription_run_from_start
              (MachineDescription.SimulatorLayout.tape S))

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
    (forall S : MachineDescription.SimulatorLayout,
     forall L : MachineDescription.DovetailLayout,
      MachineDescription.decodeCodeWordAsInput S.input =
        some (MachineDescription.DovetailLayout.encode L) ->
      validator.HaltsWithTape
        (MachineDescription.SimulatorLayout.asBoolInput S)
        (MachineDescription.SimulatorLayout.tape S)) ∧
      forall S : MachineDescription.SimulatorLayout,
      forall T : Tape Bool,
        validator.HaltsWithTape
            (MachineDescription.SimulatorLayout.asBoolInput S) T ->
          exists L : MachineDescription.DovetailLayout,
            MachineDescription.decodeCodeWordAsInput S.input =
              some (MachineDescription.DovetailLayout.encode L) ∧
              T = MachineDescription.SimulatorLayout.tape S

def SelectedMergeInputValidatorConstruction : Prop :=
  exists validator : MachineDescription,
    SelectedMergeInputValidatorSpec validator

def SelectedMergeInputValidatorPrimitive :
    MachineDescription.TapeCodePrimitive where
  transform := fun code =>
    match MachineDescription.SimulatorLayout.decodeComplete code with
    | none => none
    | some S =>
        match MachineDescription.decodeCodeWordAsInput S.input with
        | none => none
        | some inputCode =>
            match MachineDescription.DovetailLayout.decodeComplete inputCode with
            | none => none
            | some _ => some (MachineDescription.SimulatorLayout.encode S)

theorem selectedMergeInputValidatorPrimitive_transform_eq_some_iff
    (code out : Word MachineCodeSymbol) :
    SelectedMergeInputValidatorPrimitive.transform code = some out ↔
      exists S : MachineDescription.SimulatorLayout,
      exists L : MachineDescription.DovetailLayout,
        code = MachineDescription.SimulatorLayout.encode S ∧
          MachineDescription.decodeCodeWordAsInput S.input =
            some (MachineDescription.DovetailLayout.encode L) ∧
          out = MachineDescription.SimulatorLayout.encode S := by
  constructor
  · intro h
    unfold SelectedMergeInputValidatorPrimitive at h
    cases hS : MachineDescription.SimulatorLayout.decodeComplete code with
    | none =>
        simp [hS] at h
    | some S =>
        cases hinput :
            MachineDescription.decodeCodeWordAsInput S.input with
        | none =>
            simp [hS, hinput] at h
        | some inputCode =>
            cases hL :
                MachineDescription.DovetailLayout.decodeComplete
                  inputCode with
            | none =>
                simp [hS, hinput, hL] at h
            | some L =>
                simp [hS, hinput, hL] at h
                cases h
                have hcode :
                    code = MachineDescription.SimulatorLayout.encode S :=
                  CommonGround.SimulatorLayouts.decodeComplete_eq_some_encode
                    hS
                have hinputCode :
                    inputCode = MachineDescription.DovetailLayout.encode L :=
                  CommonGround.DovetailLayouts.decode_eq_some_encode
                    hL
                rw [hinputCode] at hinput
                exact ⟨S, L, hcode, hinput, rfl⟩
  · intro h
    rcases h with ⟨S, L, rfl, hinput, rfl⟩
    simp [SelectedMergeInputValidatorPrimitive,
      CommonGround.SimulatorLayouts.decodeComplete_encode,
      hinput,
      MachineDescription.DovetailLayout.decodeComplete_encode]

def SelectedMergeInputValidatorPrimitiveRightShiftedConstruction : Prop :=
  exists validator : MachineDescription,
    RightShiftedOutputCompiledSubroutineByDescription
      SelectedMergeInputValidatorPrimitive validator

structure SelectedMergeInputValidatorPayload where
  S : MachineDescription.SimulatorLayout
  L : MachineDescription.DovetailLayout
  input :
    MachineDescription.decodeCodeWordAsInput S.input =
      some (MachineDescription.DovetailLayout.encode L)

def SelectedMergeInputValidatorInputCode
    (p : SelectedMergeInputValidatorPayload) :
    Word MachineCodeSymbol :=
  MachineDescription.SimulatorLayout.encode p.S

def SelectedMergeInputValidatorOutputCode
    (p : SelectedMergeInputValidatorPayload) :
    Word MachineCodeSymbol :=
  MachineDescription.SimulatorLayout.encode p.S

def SelectedMergeInputValidatorOutputTape
    (p : SelectedMergeInputValidatorPayload) : Tape Bool :=
  Tape.move Direction.right
    (Tape.input
      (MachineDescription.encodeCodeWordAsInput
        (SelectedMergeInputValidatorOutputCode p)))

theorem selectedMergeInputValidatorOutputTape_eq_handoff
    (p : SelectedMergeInputValidatorPayload) :
    SelectedMergeInputValidatorOutputTape p =
      Tape.move Direction.right
        (MachineDescription.SimulatorLayout.tape p.S) := by
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
        (MachineDescription.SimulatorLayout.asBoolInput p.S)
        (SelectedMergeInputValidatorOutputTape p)) ∧
      forall code : Word MachineCodeSymbol,
      forall T : Tape Bool,
        validator.HaltsWithTape
            (MachineDescription.encodeCodeWordAsInput code) T ->
          exists p : SelectedMergeInputValidatorPayload,
            code = SelectedMergeInputValidatorInputCode p ∧
              T = SelectedMergeInputValidatorOutputTape p

def SelectedMergeInputValidatorExactConstruction : Prop :=
  exists validator : MachineDescription,
    SelectedMergeInputValidatorExactSpec validator

def SelectedMergeInputFieldValidatorSpec
    (validator : MachineDescription) : Prop :=
  validator.SubroutineReady ∧
    (forall S : MachineDescription.SimulatorLayout,
     forall L : MachineDescription.DovetailLayout,
      forall hinput :
        MachineDescription.decodeCodeWordAsInput S.input =
          some (MachineDescription.DovetailLayout.encode L),
      validator.HaltsFromTape
        (MachineDescription.SimulatorLayout.tape S)
        (SelectedMergeInputValidatorOutputTape
          { S := S, L := L, input := hinput })) ∧
      forall S : MachineDescription.SimulatorLayout,
      forall T : Tape Bool,
        validator.HaltsFromTape
            (MachineDescription.SimulatorLayout.tape S) T ->
          exists L : MachineDescription.DovetailLayout,
          exists hinput :
            MachineDescription.decodeCodeWordAsInput S.input =
              some (MachineDescription.DovetailLayout.encode L),
            T =
              SelectedMergeInputValidatorOutputTape
                { S := S, L := L, input := hinput }

def SelectedMergeInputFieldValidatorConstruction : Prop :=
  exists validator : MachineDescription,
    SelectedMergeInputFieldValidatorSpec validator

def SelectedMergeInputFieldCheckerSpec
    (checker : MachineDescription) : Prop :=
  checker.SubroutineReady ∧
    (forall S : MachineDescription.SimulatorLayout,
     forall L : MachineDescription.DovetailLayout,
      forall _hinput :
        MachineDescription.decodeCodeWordAsInput S.input =
          some (MachineDescription.DovetailLayout.encode L),
      checker.HaltsFromTape
        (MachineDescription.SimulatorLayout.tape S)
        (MachineDescription.SimulatorLayout.tape S)) ∧
      forall S : MachineDescription.SimulatorLayout,
      forall T : Tape Bool,
        checker.HaltsFromTape
            (MachineDescription.SimulatorLayout.tape S) T ->
          exists L : MachineDescription.DovetailLayout,
          exists _hinput :
            MachineDescription.decodeCodeWordAsInput S.input =
              some (MachineDescription.DovetailLayout.encode L),
            T = MachineDescription.SimulatorLayout.tape S

def SelectedMergeInputFieldCheckerConstruction : Prop :=
  exists checker : MachineDescription,
    SelectedMergeInputFieldCheckerSpec checker

def SelectedMergeInputFieldValidatorFromChecker
    (checker : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine
    checker MachineDescription.ExactIdentityDescription Direction.right

theorem selectedMergeInputFieldValidatorSpec_of_checker
    {checker : MachineDescription}
    (hchecker : SelectedMergeInputFieldCheckerSpec checker) :
    SelectedMergeInputFieldValidatorSpec
      (SelectedMergeInputFieldValidatorFromChecker checker) := by
  let identity := MachineDescription.ExactIdentityDescription
  have hid : identity.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  constructor
  · exact
      MachineDescription.seqSubroutine_subroutineReady
        hchecker.left hid
  constructor
  · intro S L hinput
    have hcheck :
        checker.HaltsFromTape
          (MachineDescription.SimulatorLayout.tape S)
          (MachineDescription.SimulatorLayout.tape S) :=
      hchecker.right.left S L hinput
    simpa [SelectedMergeInputFieldValidatorFromChecker,
      selectedMergeInputValidatorOutputTape_eq_handoff, identity] using
      MachineDescription.seqSubroutine_haltsFromTape_of_haltsFromTape
        (A := checker) (B := identity) (handoffMove := Direction.right)
        hchecker.left hid hcheck
        (CommonGround.Identity.exactIdentityDescription_run_from_start
          (Tape.move Direction.right
            (MachineDescription.SimulatorLayout.tape S)))
  · intro S T hhalt
    rcases
        MachineDescription.seqSubroutine_haltsFromTape_inv
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
      congrArg MachineDescription.Configuration.tape hn
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
  MachineDescription.seqSubroutine parser checker Direction.left

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
    MachineDescription.seqSubroutine_subroutineReady
      hparser.left hchecker.left
  constructor
  · exact hrunnerReady
  constructor
  · intro S L hinput
    have hparserRun :
        parser.HaltsWithTape
          (MachineDescription.SimulatorLayout.asBoolInput S)
          (CommonGround.SimulatorLayouts.handoffTape S) := by
      simpa [CommonGround.SimulatorLayouts.bits,
        CommonGround.SimulatorLayouts.encode,
        CommonGround.LayoutTapes.Bits,
        MachineDescription.SimulatorLayout.asBoolInput] using
        hparser.right.left S
    have hcheckerRun :
        checker.HaltsFromTape
          (MachineDescription.SimulatorLayout.tape S)
          (MachineDescription.SimulatorLayout.tape S) :=
      hchecker.right.left S L hinput
    rcases MachineDescription.runConfig_eq_halt_of_haltsFromTape
      hcheckerRun with ⟨n, hn⟩
    exact
      MachineDescription.seqSubroutine_haltsWithTape_of_haltsWithTape
        hparser.left hchecker.left hparserRun
        ⟨n, by
          simpa [
            CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape
              S] using hn⟩
  · intro S T hhalt
    rcases
        MachineDescription.seqSubroutine_haltsWithTape_inv
          hparser.left hchecker.left
          (by
            simpa [SelectedMergeInputValidatorFromParserChecker] using
              hhalt) with
      ⟨Tmid, hparserRun, hcheckerReach⟩
    have hparserRun' :
        parser.HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.SimulatorLayout.encode S)) Tmid := by
      simpa [MachineDescription.SimulatorLayout.asBoolInput] using
        hparserRun
    rcases hparser.right.right
        (MachineDescription.SimulatorLayout.encode S) Tmid hparserRun' with
      ⟨S', hdecode, hTmid⟩
    have hS' : S' = S := by
      have hdecode' :
          MachineDescription.SimulatorLayout.decodeComplete
              (MachineDescription.SimulatorLayout.encode S) =
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
          (MachineDescription.SimulatorLayout.tape S) T := by
      refine ⟨n, ?_⟩
      constructor
      · simpa [MachineDescription.HaltsFromTapeIn,
          MachineDescription.initial, hTmid,
          CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape
            S] using congrArg MachineDescription.Configuration.state hn
      · simpa [MachineDescription.HaltsFromTapeIn,
          MachineDescription.initial, hTmid,
          CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape
            S] using congrArg MachineDescription.Configuration.tape hn
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
  MachineDescription.seqSubroutine parser fieldValidator Direction.left

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
    MachineDescription.seqSubroutine_subroutineReady
      hparser.left hfield.left
  constructor
  · exact hrunnerReady
  constructor
  · intro p
    have hparserRun :
        parser.HaltsWithTape
          (MachineDescription.SimulatorLayout.asBoolInput p.S)
          (CommonGround.SimulatorLayouts.handoffTape p.S) := by
      simpa [CommonGround.SimulatorLayouts.bits,
        CommonGround.SimulatorLayouts.encode,
        CommonGround.LayoutTapes.Bits,
        MachineDescription.SimulatorLayout.asBoolInput] using
        hparser.right.left p.S
    have hfieldRun :
        fieldValidator.HaltsFromTape
          (MachineDescription.SimulatorLayout.tape p.S)
          (SelectedMergeInputValidatorOutputTape p) :=
      hfield.right.left p.S p.L p.input
    rcases MachineDescription.runConfig_eq_halt_of_haltsFromTape
      hfieldRun with ⟨n, hn⟩
    exact
      MachineDescription.seqSubroutine_haltsWithTape_of_haltsWithTape
        hparser.left hfield.left hparserRun
        ⟨n, by
          simpa [
            CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape
              p.S] using hn⟩
  · intro code T hhalt
    rcases
        MachineDescription.seqSubroutine_haltsWithTape_inv
          hparser.left hfield.left hhalt with
      ⟨Tmid, hparserRun, hfieldReach⟩
    rcases hparser.right.right code Tmid hparserRun with
      ⟨S, hdecode, hTmid⟩
    have hcode : code = MachineDescription.SimulatorLayout.encode S :=
      CommonGround.SimulatorLayouts.decodeComplete_eq_some_encode
        hdecode
    rcases hfieldReach with ⟨n, hn⟩
    have hfieldRun :
        fieldValidator.HaltsFromTape
          (MachineDescription.SimulatorLayout.tape S) T := by
      refine ⟨n, ?_⟩
      constructor
      · simpa [MachineDescription.HaltsFromTapeIn,
          MachineDescription.initial, hTmid,
          CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape
            S] using congrArg MachineDescription.Configuration.state hn
      · simpa [MachineDescription.HaltsFromTapeIn,
          MachineDescription.initial, hTmid,
          CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape
            S] using congrArg MachineDescription.Configuration.tape hn
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
          MachineDescription.SimulatorLayout.asBoolInput] using
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
  MachineDescription.seqSubroutine validator
    MachineDescription.ExactIdentityDescription Direction.left

theorem selectedMergeInputValidatorSpec_of_rightShifted
    {validator : MachineDescription}
    (hvalidator :
      RightShiftedOutputCompiledSubroutineByDescription
        SelectedMergeInputValidatorPrimitive validator) :
    SelectedMergeInputValidatorSpec
      (SelectedMergeInputValidatorFromRightShifted validator) := by
  have hidentityReady :
      MachineDescription.ExactIdentityDescription.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  have hvalidatorReady : validator.SubroutineReady :=
    rightShiftedOutputCompiledSubroutineByDescription_subroutineReady
      hvalidator
  constructor
  · exact
      MachineDescription.seqSubroutine_subroutineReady
        hvalidatorReady hidentityReady
  constructor
  · intro S L hinput
    have htransform :
        SelectedMergeInputValidatorPrimitive.transform
            (MachineDescription.SimulatorLayout.encode S) =
          some (MachineDescription.SimulatorLayout.encode S) :=
      (selectedMergeInputValidatorPrimitive_transform_eq_some_iff
        (MachineDescription.SimulatorLayout.encode S)
        (MachineDescription.SimulatorLayout.encode S)).mpr
        ⟨S, L, rfl, hinput, rfl⟩
    have hright :
        validator.HaltsWithTape
          (MachineDescription.SimulatorLayout.asBoolInput S)
          (Tape.move Direction.right
            (Tape.input
              (MachineDescription.encodeCodeWordAsInput
                (MachineDescription.SimulatorLayout.encode S)))) := by
      simpa [MachineDescription.SimulatorLayout.asBoolInput] using
        rightShiftedOutputCompiled_haltsWithTape_of_transform
          hvalidator htransform
    have hbridge :
        Tape.move Direction.left
            (Tape.move Direction.right
              (Tape.input
                (MachineDescription.encodeCodeWordAsInput
                  (MachineDescription.SimulatorLayout.encode S)))) =
          MachineDescription.SimulatorLayout.tape S := by
      simpa [MachineDescription.SimulatorLayout.tape] using
        CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape S
    have hidentity :
        exists n : Nat,
          MachineDescription.ExactIdentityDescription.runConfig n
              { state := MachineDescription.ExactIdentityDescription.start
                tape :=
                  Tape.move Direction.left
                    (Tape.move Direction.right
                      (Tape.input
                        (MachineDescription.encodeCodeWordAsInput
                          (MachineDescription.SimulatorLayout.encode S)))) } =
            { state := MachineDescription.ExactIdentityDescription.halt
              tape := MachineDescription.SimulatorLayout.tape S } := by
      rcases
          CommonGround.Identity.exactIdentityDescription_run_from_start
            (MachineDescription.SimulatorLayout.tape S) with
        ⟨n, hn⟩
      exact ⟨n, by simpa [hbridge] using hn⟩
    simpa [SelectedMergeInputValidatorFromRightShifted] using
      MachineDescription.seqSubroutine_haltsWithTape_of_haltsWithTape
        hvalidatorReady hidentityReady hright hidentity
  · intro S T hhalt
    rcases
        MachineDescription.seqSubroutine_haltsWithTape_inv
          hvalidatorReady hidentityReady
          (by simpa [SelectedMergeInputValidatorFromRightShifted] using hhalt) with
      ⟨Tmid, hvalidatorRun, hidentityReach⟩
    rcases
        rightShiftedOutputCompiledSubroutineByDescription_haltsWithTape_inv
          hvalidator hvalidatorRun with
      ⟨out, htransform, hTmid⟩
    rcases
        (selectedMergeInputValidatorPrimitive_transform_eq_some_iff
          (MachineDescription.SimulatorLayout.encode S) out).mp htransform with
      ⟨S', L, hcode, hinput, hout⟩
    have hS : S' = S := by
      have hsome :
          some S = some S' := by
        calc
          some S =
              MachineDescription.SimulatorLayout.decodeComplete
                (MachineDescription.SimulatorLayout.encode S) := by
                rw [CommonGround.SimulatorLayouts.decodeComplete_encode]
          _ =
              MachineDescription.SimulatorLayout.decodeComplete
                (MachineDescription.SimulatorLayout.encode S') := by
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
                (MachineDescription.encodeCodeWordAsInput
                  (MachineDescription.SimulatorLayout.encode S)))) := by
      rcases hidentityReach with ⟨n, hn⟩
      have hrun :=
        CommonGround.Identity.exactIdentityDescription_runConfig_from_start
          n (Tape.move Direction.left Tmid)
      rw [hrun] at hn
      have htape :
          Tape.move Direction.left Tmid = T :=
        congrArg MachineDescription.Configuration.tape hn
      rw [hTmid] at htape
      exact htape.symm
    have hT : T = MachineDescription.SimulatorLayout.tape S := by
      rw [hTleft]
      simpa [MachineDescription.SimulatorLayout.tape] using
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
  MachineDescription.seqSubroutine parser validator Direction.left

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
    MachineDescription.seqSubroutine_subroutineReady
      hparser.left hvalidator.left
  constructor
  · exact hrunnerReady
  constructor
  · intro S L hinput
    have hparserRun :
        parser.HaltsWithTape
          (MachineDescription.SimulatorLayout.asBoolInput S)
          (CommonGround.SimulatorLayouts.handoffTape S) := by
      simpa [CommonGround.SimulatorLayouts.bits,
        CommonGround.SimulatorLayouts.encode,
        CommonGround.LayoutTapes.Bits,
        MachineDescription.SimulatorLayout.asBoolInput] using
        hparser.right.left S
    have hvalidatorRun :
        validator.HaltsWithTape
          (MachineDescription.SimulatorLayout.asBoolInput S)
          (MachineDescription.SimulatorLayout.tape S) :=
      hvalidator.right.left S L hinput
    rcases MachineDescription.runConfig_eq_halt_of_haltsWithTape
      hvalidatorRun with ⟨n, hn⟩
    exact
      MachineDescription.seqSubroutine_haltsWithTape_of_haltsWithTape
        hparser.left hvalidator.left hparserRun
        ⟨n, by
          simpa [
            CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape
              S] using hn⟩
  · intro code T hhalt
    rcases
        MachineDescription.seqSubroutine_haltsWithTape_inv
          hparser.left hvalidator.left hhalt with
      ⟨Tmid, hparserRun, hvalidatorReach⟩
    rcases hparser.right.right code Tmid hparserRun with
      ⟨S, hdecode, hTmid⟩
    have hcode : code = MachineDescription.SimulatorLayout.encode S :=
      CommonGround.SimulatorLayouts.decodeComplete_eq_some_encode
        hdecode
    rcases hvalidatorReach with ⟨n, hn⟩
    have hvalidatorRun :
        validator.HaltsWithTape
          (MachineDescription.SimulatorLayout.asBoolInput S) T := by
      refine ⟨n, ?_⟩
      constructor
      · simpa [MachineDescription.HaltsWithTapeIn,
          MachineDescription.initial, hTmid,
          CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape
            S] using congrArg MachineDescription.Configuration.state hn
      · simpa [MachineDescription.HaltsWithTapeIn,
          MachineDescription.initial, hTmid,
          CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape
            S] using congrArg MachineDescription.Configuration.tape hn
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
    (forall S : MachineDescription.SimulatorLayout,
     forall L : MachineDescription.DovetailLayout,
      MachineDescription.decodeCodeWordAsInput S.input =
        some (MachineDescription.DovetailLayout.encode L) ->
      emitter.HaltsWithTape
        (MachineDescription.SimulatorLayout.asBoolInput S)
        (SelectedMergeOutputTape useAccept S L)) ∧
      forall S : MachineDescription.SimulatorLayout,
      forall L : MachineDescription.DovetailLayout,
      forall T : Tape Bool,
        MachineDescription.decodeCodeWordAsInput S.input =
          some (MachineDescription.DovetailLayout.encode L) ->
        emitter.HaltsWithTape
            (MachineDescription.SimulatorLayout.asBoolInput S) T ->
          T = SelectedMergeOutputTape useAccept S L

structure SelectedMergeEmitterPayload where
  S : MachineDescription.SimulatorLayout
  L : MachineDescription.DovetailLayout
  input :
    MachineDescription.decodeCodeWordAsInput S.input =
      some (MachineDescription.DovetailLayout.encode L)

def SelectedMergeEmitterInputBits
    (p : SelectedMergeEmitterPayload) : Word Bool :=
  MachineDescription.SimulatorLayout.asBoolInput p.S

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
        (MachineDescription.SimulatorLayout.tape p.S)
        (SelectedMergeEquivOutputTape useAccept p.S p.L)

def SelectedMergeEquivEmitterConstruction : Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedMergeEquivEmitterSpec useAccept emitter

def inputWithTrailingBlankPadding
    (w : Word Bool) (padding : Nat) : Tape Bool :=
  match w with
  | [] =>
      { left := []
        head := none
        right := List.replicate padding none }
  | bit :: rest =>
      { left := []
        head := some bit
        right := rest.map some ++ List.replicate padding none }

theorem dropTrailingNone_replicate_none
    (padding : Nat) :
    Tape.dropTrailingNone
        (List.replicate padding (none : Option Bool)) = [] := by
  induction padding with
  | zero =>
      rfl
  | succ padding ih =>
      simp [List.replicate, Tape.dropTrailingNone, ih]

theorem dropTrailingNone_append_replicate_none
    (xs : List (Option Bool)) (padding : Nat) :
    Tape.dropTrailingNone
        (xs ++ List.replicate padding (none : Option Bool)) =
      Tape.dropTrailingNone xs := by
  induction padding generalizing xs with
  | zero =>
      simp
  | succ padding ih =>
      calc
        Tape.dropTrailingNone
            (xs ++ List.replicate (padding + 1) (none : Option Bool)) =
          Tape.dropTrailingNone
            ((xs ++ [none]) ++
              List.replicate padding (none : Option Bool)) := by
            simp [List.replicate_succ, List.append_assoc]
        _ = Tape.dropTrailingNone (xs ++ [none]) :=
          ih (xs ++ [none])
        _ = Tape.dropTrailingNone xs :=
          dropTrailingNone_append_none xs

theorem inputWithTrailingBlankPadding_equiv_input
    (w : Word Bool) (padding : Nat) :
    Tape.Equiv (inputWithTrailingBlankPadding w padding)
      (Tape.input w) := by
  cases w with
  | nil =>
      constructor
      · rfl
      · constructor
        · rfl
        · exact dropTrailingNone_replicate_none padding
  | cons bit rest =>
      constructor
      · rfl
      · constructor
        · rfl
        · exact dropTrailingNone_append_replicate_none
            (rest.map some) padding

theorem inputWithTrailingBlankPadding_contextLength_ge_input
    (outputBits inputBits : Word Bool) :
    Tape.contextLength (Tape.input inputBits) <=
      Tape.contextLength
        (inputWithTrailingBlankPadding outputBits inputBits.length) := by
  cases outputBits <;> cases inputBits <;>
    simp [inputWithTrailingBlankPadding, Tape.input, Tape.blank,
      Tape.contextLength] <;>
    omega

theorem inputWithTrailingBlankPadding_move_right_normalizedOutput
    (w : Word Bool) (padding : Nat) :
    Tape.normalizedOutput
        (Tape.move Direction.right
          (inputWithTrailingBlankPadding w padding)) = w := by
  have hequiv :
      Tape.Equiv
        (Tape.move Direction.right
          (inputWithTrailingBlankPadding w padding))
        (Tape.move Direction.right (Tape.input w)) :=
    Tape.Equiv.move
      (inputWithTrailingBlankPadding_equiv_input w padding)
      Direction.right
  rw [Tape.Equiv.normalizedOutput_eq hequiv]
  exact tape_normalizedOutput_move_right_input w

theorem tape_contextLength_le_move_right
    (T : Tape Bool) :
    Tape.contextLength T <=
      Tape.contextLength (Tape.move Direction.right T) := by
  cases T with
  | mk left head right =>
      cases right <;>
        simp [Tape.contextLength, Tape.move, Tape.moveRight] <;>
        omega

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

/--
Finite-machine leaf for selected projection under the equivalence-based phase
contract.  The checked parser supplies the canonical checked parsed-layout
input.  This first phase quotes the input field and positions the remaining
layout fields for the selected padded tail emitter.
-/
theorem selectedProjectionInputQuoterConstruction_scaffold :
    SelectedProjectionInputQuoterConstruction := by
  sorry

/--
Finite-machine leaf for the selected-projection tail.  It starts after the
input quoter, consumes the stage/configuration/hit fields, and may leave
trailing blank padding while emitting a tape equivalent to the right-shifted
selected simulator-layout output.
-/
theorem selectedProjectionPaddedTailEmitterConstruction_scaffold :
    SelectedProjectionPaddedTailEmitterConstruction := by
  sorry

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

namespace SelectedMergeCounterexample

def blankConfig : MachineDescription.Configuration :=
  { state := 0, tape := Tape.blank }

def layout : MachineDescription.DovetailLayout :=
  { input := []
    stage := 0
    acceptConfig := blankConfig
    rejectConfig := blankConfig
    acceptHit := false
    rejectHit := false }

def simulator : MachineDescription.SimulatorLayout :=
  { input := MachineDescription.encodeCodeWordAsInput
      (MachineDescription.DovetailLayout.encode layout)
    stage := 0
    config := blankConfig
    hit := false }

theorem simulator_input :
    MachineDescription.decodeCodeWordAsInput simulator.input =
      some (MachineDescription.DovetailLayout.encode layout) := by
  simp [simulator,
    MachineDescription.decodeCodeWordAsInput_encodeCodeWordAsInput]

def payload : SelectedMergeEmitterPayload :=
  { S := simulator
    L := layout
    input := simulator_input }

theorem output_contextLength_lt_input :
    Tape.contextLength (SelectedMergeOutputTape true simulator layout) <
      Tape.contextLength
        (Tape.input
          (MachineDescription.SimulatorLayout.asBoolInput simulator)) := by
  native_decide

theorem exactOutput_contextLength_lt_input :
    Tape.contextLength
        (CanonicalLayouts.ExactOutputTape
          (SelectedMergeEmitterOutputCode true) payload) <
      Tape.contextLength
        (Tape.input
          (MachineDescription.SimulatorLayout.asBoolInput simulator)) := by
  native_decide

theorem paddedOutput_contextLength_not_lt_input :
    ¬ Tape.contextLength
        (SelectedMergeEquivEmitterPaddedOutputTape true payload) <
      Tape.contextLength
        (Tape.input
          (MachineDescription.SimulatorLayout.asBoolInput simulator)) := by
  simpa [MachineDescription.SimulatorLayout.tape, payload] using
    Nat.not_lt_of_ge
      (SelectedMergeEquivEmitterPaddedOutputTape_contextLength_ge_input
        true payload)

theorem contextLength_eq_of_move_left_eq_input
    {w : Word Bool} {T : Tape Bool}
    (h : Tape.move Direction.left T = Tape.input w) :
    Tape.contextLength T = Tape.contextLength (Tape.input w) := by
  cases T with
  | mk left head right =>
      cases w with
      | nil =>
          cases left with
          | nil =>
              simp [Tape.move, Tape.moveLeft, Tape.input, Tape.blank] at h
          | cons first leftRest =>
              cases leftRest with
              | nil =>
                  simp [Tape.move, Tape.moveLeft, Tape.input, Tape.blank] at h
              | cons second more =>
                  simp [Tape.move, Tape.moveLeft, Tape.input, Tape.blank] at h
      | cons a rest =>
          cases left with
          | nil =>
              simp [Tape.move, Tape.moveLeft, Tape.input] at h
          | cons first leftRest =>
              cases leftRest with
              | nil =>
                  cases rest with
                  | nil =>
                      simp [Tape.move, Tape.moveLeft, Tape.input] at h
                  | cons b restTail =>
                      simp [Tape.move, Tape.moveLeft, Tape.input,
                        Tape.contextLength] at h ⊢
                      rw [h.right.right]
                      simp
                      omega
              | cons second more =>
                  simp [Tape.move, Tape.moveLeft, Tape.input] at h

theorem not_selectedMergeCanonicalExactEmitterConstruction :
    ¬ SelectedMergeCanonicalExactEmitterConstruction := by
  intro hconstruction
  rcases hconstruction true with ⟨emitter, hemits⟩
  have hhalt := hemits.right.left payload
  rcases hhalt with ⟨n, hn⟩
  have hmono :=
    MachineDescription.runConfig_contextLength_mono emitter n
      (emitter.initial (SelectedMergeEmitterInputBits payload))
  have hfinal :
      Tape.contextLength
          (emitter.runConfig n
            (emitter.initial
              (SelectedMergeEmitterInputBits payload))).tape =
        Tape.contextLength
          (CanonicalLayouts.ExactOutputTape
            (SelectedMergeEmitterOutputCode true) payload) := by
    exact congrArg Tape.contextLength hn.right
  rw [hfinal] at hmono
  have hinput :
      Tape.contextLength
          (emitter.initial
            (SelectedMergeEmitterInputBits payload)).tape =
        Tape.contextLength
          (Tape.input
            (MachineDescription.SimulatorLayout.asBoolInput simulator)) := by
    rfl
  rw [hinput] at hmono
  exact (Nat.not_lt_of_ge hmono) exactOutput_contextLength_lt_input

theorem not_selectedMergeEmitterConstruction :
    ¬ SelectedMergeEmitterConstruction := by
  intro hconstruction
  rcases hconstruction true with ⟨emitter, hemits⟩
  have hhalt := hemits.right.left simulator layout simulator_input
  rcases hhalt with ⟨n, hn⟩
  have hmono :=
    MachineDescription.runConfig_contextLength_mono emitter n
      (emitter.initial
        (MachineDescription.SimulatorLayout.asBoolInput simulator))
  have hfinal :
      Tape.contextLength
          (emitter.runConfig n
            (emitter.initial
              (MachineDescription.SimulatorLayout.asBoolInput simulator))).tape =
        Tape.contextLength (SelectedMergeOutputTape true simulator layout) := by
    exact congrArg Tape.contextLength hn.right
  rw [hfinal] at hmono
  have hinput :
      Tape.contextLength
          (emitter.initial
            (MachineDescription.SimulatorLayout.asBoolInput simulator)).tape =
        Tape.contextLength
          (Tape.input
            (MachineDescription.SimulatorLayout.asBoolInput simulator)) :=
    rfl
  rw [hinput] at hmono
  exact (Nat.not_lt_of_ge hmono) output_contextLength_lt_input

theorem not_selectedMergeCanonicalEmitterConstruction :
    ¬ SelectedMergeCanonicalEmitterConstruction := by
  intro hconstruction
  exact not_selectedMergeEmitterConstruction
    (by
      intro useAccept
      rcases hconstruction useAccept with ⟨emitter, hemits⟩
      exact
        ⟨emitter,
          (selectedMergeEmitterSpec_iff_canonical useAccept emitter).mpr
            hemits⟩)

theorem not_selectedMergePrimitiveRightShiftedConstruction :
    ¬ SelectedMergePrimitiveRightShiftedConstruction := by
  intro hconstruction
  rcases hconstruction true with ⟨runner, hrunner⟩
  have htransform :
      (SelectedMergePrimitive true).transform
          (MachineDescription.SimulatorLayout.encode simulator) =
        some (SelectedMergeOutputCode true simulator layout) :=
    (SelectedMergePrimitive_transform_eq_some_iff true
      (MachineDescription.SimulatorLayout.encode simulator)
      (SelectedMergeOutputCode true simulator layout)).mpr
      ⟨simulator, layout, rfl, simulator_input, rfl⟩
  have hhalt :=
    rightShiftedOutputCompiled_haltsWithTape_of_transform
      hrunner htransform
  rcases hhalt with ⟨n, hn⟩
  have hmono :=
    MachineDescription.runConfig_contextLength_mono runner n
      (runner.initial
        (MachineDescription.SimulatorLayout.asBoolInput simulator))
  have hfinal :
      Tape.contextLength
          (runner.runConfig n
            (runner.initial
              (MachineDescription.SimulatorLayout.asBoolInput simulator))).tape =
        Tape.contextLength (SelectedMergeOutputTape true simulator layout) := by
    exact congrArg Tape.contextLength hn.right
  rw [hfinal] at hmono
  have hinput :
      Tape.contextLength
          (runner.initial
            (MachineDescription.SimulatorLayout.asBoolInput simulator)).tape =
        Tape.contextLength
          (Tape.input
            (MachineDescription.SimulatorLayout.asBoolInput simulator)) :=
    rfl
  rw [hinput] at hmono
  exact (Nat.not_lt_of_ge hmono) output_contextLength_lt_input

theorem not_selectedMergePrimitiveClosedHandoffDescription
    (closed : MachineDescription) :
    ¬ TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (SelectedMergePrimitive true) closed
        tapeCodePrimitiveCodeWordHandoffMove := by
  intro hclosed
  have htransform :
      (SelectedMergePrimitive true).transform
          (MachineDescription.SimulatorLayout.encode simulator) =
        some (SelectedMergeOutputCode true simulator layout) :=
    (SelectedMergePrimitive_transform_eq_some_iff true
      (MachineDescription.SimulatorLayout.encode simulator)
      (SelectedMergeOutputCode true simulator layout)).mpr
      ⟨simulator, layout, rfl, simulator_input, rfl⟩
  have houtput :
      closed.HaltsWithOutput
        (MachineDescription.SimulatorLayout.asBoolInput simulator)
        (MachineDescription.encodeCodeWordAsInput
          (SelectedMergeOutputCode true simulator layout)) :=
    (hclosed.left.left.right
      (MachineDescription.SimulatorLayout.encode simulator)
      (SelectedMergeOutputCode true simulator layout)).mpr htransform
  rcases houtput with ⟨n, hn⟩
  let T : Tape Bool :=
    (closed.runConfig n
      (closed.initial
        (MachineDescription.SimulatorLayout.asBoolInput simulator))).tape
  have hhalt :
      closed.HaltsWithTape
        (MachineDescription.SimulatorLayout.asBoolInput simulator) T := by
    exact ⟨n, hn.left, rfl⟩
  rcases hclosed.right
      (MachineDescription.SimulatorLayout.encode simulator) T hhalt with
    ⟨out, hout, _hnormalized, hhandoff⟩
  have hout_eq : out = SelectedMergeOutputCode true simulator layout := by
    rw [htransform] at hout
    cases hout
    rfl
  have hctxT :
      Tape.contextLength T =
        Tape.contextLength
          (CanonicalLayouts.ExactOutputTape
            (SelectedMergeEmitterOutputCode true) payload) := by
    have hctxOut :=
      contextLength_eq_of_move_left_eq_input hhandoff
    rw [hout_eq] at hctxOut
    simpa [CanonicalLayouts.ExactOutputTape,
      SelectedMergeEmitterOutputCode, payload,
      tapeCodePrimitiveCodeWordHandoffMove] using hctxOut
  have hmono :=
    MachineDescription.runConfig_contextLength_mono closed n
      (closed.initial
        (MachineDescription.SimulatorLayout.asBoolInput simulator))
  have hinput :
      Tape.contextLength
          (closed.initial
            (MachineDescription.SimulatorLayout.asBoolInput simulator)).tape =
        Tape.contextLength
          (Tape.input
            (MachineDescription.SimulatorLayout.asBoolInput simulator)) :=
    rfl
  rw [hinput] at hmono
  have hfinal :
      Tape.contextLength
          (closed.runConfig n
            (closed.initial
              (MachineDescription.SimulatorLayout.asBoolInput simulator))).tape =
        Tape.contextLength
          (CanonicalLayouts.ExactOutputTape
            (SelectedMergeEmitterOutputCode true) payload) := by
    simpa [T] using hctxT
  rw [hfinal] at hmono
  exact (Nat.not_lt_of_ge hmono) exactOutput_contextLength_lt_input

theorem not_selectedMergePrimitiveClosedHandoffConstruction :
    ¬ SelectedMergePrimitiveClosedHandoffConstruction := by
  intro hconstruction
  rcases hconstruction true with ⟨closed, hclosed⟩
  exact not_selectedMergePrimitiveClosedHandoffDescription closed hclosed

theorem not_acceptMergePrimitiveClosedHandoffConstruction :
    ¬ AcceptMergePrimitiveClosedHandoffConstruction := by
  intro hconstruction
  rcases hconstruction with ⟨closed, hclosed⟩
  exact
    not_selectedMergePrimitiveClosedHandoffDescription closed
      (by
        simpa [SelectedMergePrimitive, AcceptMergePrimitive,
          SelectedMergeSimulatorResult] using hclosed)

theorem not_configRunnerPrimitiveClosedHandoffConstruction :
    ¬ ConfigRunnerPrimitiveClosedHandoffConstruction := by
  intro hconstruction
  rcases hconstruction with
    ⟨_acceptProject, acceptMerge, _rejectProject, _rejectMerge,
      _hacceptProject, hacceptMerge, _hrejectProject, _hrejectMerge⟩
  exact not_acceptMergePrimitiveClosedHandoffConstruction
    ⟨acceptMerge, hacceptMerge⟩

theorem not_selectedMergeFiniteDescriptionConstruction :
    ¬ SelectedMergeFiniteDescriptionConstruction := by
  intro hconstruction
  exact not_selectedMergePrimitiveRightShiftedConstruction
    (selectedMergePrimitiveRightShiftedConstruction_of_finiteDescription
      hconstruction)

end SelectedMergeCounterexample

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
