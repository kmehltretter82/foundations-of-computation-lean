import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.RightShiftedPrimitives

set_option doc.verso true

/-!
# Bounded runner parser and emitter adapters
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace BoundedLayoutRunner

theorem selectedProjectionSpec_of_parser_emitter
    {useAccept : Bool} {parser emitter : MachineDescription}
    (hparser : LayoutCheckedParserSpec parser)
    (hemitter : SelectedProjectionEmitterSpec useAccept emitter) :
    SelectedProjectionSpec useAccept
      (SeqViaCanonical parser emitter) := by
  have hrunnerReady :
      (SeqViaCanonical parser emitter).SubroutineReady :=
    SeqViaCanonical_subroutineReady hparser.left hemitter.left
  constructor
  · exact hrunnerReady
  constructor
  · intro L
    have hbridge :
        Tape.Equiv
          (Tape.move Direction.left
            (Tape.move Direction.right (ParsedLayoutCheckedTape L)))
          (Tape.input (ParsedLayoutBits L)) := by
      rw [parsedLayoutCheckedTape_move_left_move_right L]
      exact checkedInputTape_equiv_input _
    exact
      SeqViaCanonical_haltsFromTapeEquiv_of_haltsWithTape
        hparser.left hemitter.left
        (MachineDescription.HaltsFromTape.toEquiv (hparser.right.left L))
        hbridge
        (hemitter.right.left L)
  · intro code T hhalt
    rcases
        SeqViaCanonical_haltsFromTape_inv hparser.left hemitter.left hhalt with
      ⟨Tmid, hparser_run, hemitter_run⟩
    rcases hparser.right.right code Tmid hparser_run with
      ⟨L, hcode, hTmid_equiv⟩
    refine ⟨L, MachineDescription.DovetailLayout.decodeComplete_eq_some_encode hcode, ?_⟩
    have hemitter_exact := hemitter.right.left L
    have h_in_equiv :
        Tape.Equiv (Tape.input (ParsedLayoutBits L))
          (Tape.move Direction.left (Tape.move Direction.right Tmid)) := by
      rw [hTmid_equiv]
      rw [parsedLayoutCheckedTape_move_left_move_right L]
      exact Tape.Equiv.symm (checkedInputTape_equiv_input _)
    have h_emitter_equiv_out :=
      MachineDescription.HaltsFromTapeEquiv_of_input_equiv h_in_equiv hemitter_exact
    rcases h_emitter_equiv_out with ⟨Tactual_equiv, h_actual_equiv, h_equiv_out⟩
    have h_eq :=
      MachineDescription.haltsFromTape_functional_of_haltTransitionFree
        hemitter.left.right hemitter_run h_actual_equiv
    subst h_eq
    exact h_equiv_out

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

def SelectedMergeEmitterConstruction : Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedMergeEmitterSpec useAccept emitter

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
      ⟨MachineDescription.exactIdentityDescription_wellFormed,
        MachineDescription.exactIdentityDescription_haltTransitionFree⟩
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


end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
