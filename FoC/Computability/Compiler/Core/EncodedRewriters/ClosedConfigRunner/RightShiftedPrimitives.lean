import FoC.Computability.Compiler.Core.CommonGround.CodeWordEmitters
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.FiniteDescriptionContracts

set_option doc.verso true

/-!
# Bounded runner right-shifted primitive adapters

The selected-projection exact and right-shifted contracts in this file are
compatibility adapters.  The active config-runner proof path uses the
padded/equivalence selected-projection construction exported by
{module}`FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.FiniteDescriptionContracts`
and its padded selected-projection submodule.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

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
            (DovetailLayout.encode L) =
          some (SelectedProjectionOutputCode useAccept L) :=
      (SelectedProjectionPrimitive_transform_eq_some_iff
        useAccept
        (DovetailLayout.encode L)
        (SelectedProjectionOutputCode useAccept L)).mpr
        ⟨L, rfl, by simp [SelectedProjectionOutputCode]⟩
    have hexact := rightShiftedOutputCompiled_haltsWithTape_of_transform hrunner htransform
    have hequiv := HaltsFromTape.toEquiv hexact
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
            (SimulatorLayout.encode S) =
          some (SelectedMergeOutputCode useAccept S L) :=
      (SelectedMergePrimitive_transform_eq_some_iff
        useAccept
        (SimulatorLayout.encode S)
        (SelectedMergeOutputCode useAccept S L)).mpr
        ⟨S, L, rfl, hinput, rfl⟩
    simpa [SimulatorLayout.asBoolInput,
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

theorem selectedProjectionPrimitiveClosedHandoffConstruction_of_rightShifted
    (h : SelectedProjectionPrimitiveRightShiftedConstruction) :
    SelectedProjectionPrimitiveClosedHandoffConstruction := by
  intro useAccept
  rcases h useAccept with ⟨runner, hrunner⟩
  refine ⟨runner, ?_⟩
  exact
    EncodedRewriters.closedHandoffCompiled_of_rightShiftedOutputCompiled
      hrunner
      (by
        intro code out htransform
        rcases
            SelectedProjectionPrimitive_transform_eq_some_cons
              htransform with
          ⟨tail, hout⟩
        exact ⟨MachineCodeSymbol.header, tail, hout⟩)

theorem selectedMergePrimitiveClosedHandoffConstruction_of_rightShifted
    (h : SelectedMergePrimitiveRightShiftedConstruction) :
    SelectedMergePrimitiveClosedHandoffConstruction := by
  intro useAccept
  rcases h useAccept with ⟨runner, hrunner⟩
  refine ⟨runner, ?_⟩
  exact
    EncodedRewriters.closedHandoffCompiled_of_rightShiftedOutputCompiled
      hrunner
      (by
        intro code out htransform
        rcases
            SelectedMergePrimitive_transform_eq_some_cons
              htransform with
          ⟨tail, hout⟩
        exact ⟨MachineCodeSymbol.transition, tail, hout⟩)

def SelectedProjectionPrimitiveExactSpec
    (useAccept : Bool)
    (runner : MachineDescription) : Prop :=
  ReadySpec runner ∧
    (forall L : DovetailLayout,
      runner.HaltsWithTape
        (ParsedLayoutBits L)
        (SelectedProjectionOutputTape useAccept L)) ∧
      forall code : Word MachineCodeSymbol,
      forall T : Tape Bool,
        runner.HaltsWithTape
            (encodeCodeWordAsInput code) T ->
          exists L : DovetailLayout,
            code = DovetailLayout.encode L ∧
              T = SelectedProjectionOutputTape useAccept L

def SelectedProjectionPrimitiveExactConstruction : Prop :=
  forall useAccept : Bool,
    exists runner : MachineDescription,
      SelectedProjectionPrimitiveExactSpec useAccept runner

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
      (fun L : DovetailLayout =>
        DovetailLayout.encode L)
      (fun L : DovetailLayout =>
        SelectedProjectionOutputCode useAccept L)
      (fun L : DovetailLayout =>
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
      simpa [HaltsWithTape,
        HaltsWithTapeIn,
        HaltsFromTape,
        HaltsFromTapeIn,
        initial] using hparser.right.left L
    have hseq :
        (SeqViaCanonical parser emitter).HaltsFromTape
          (Tape.input (ParsedLayoutBits L))
          (SelectedProjectionOutputTape useAccept L) :=
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        hparser.left hemitter.left
        hparserFrom
        (parsedLayoutCheckedTape_move_left_move_right L)
        (hemitter.right L)
    simpa [HaltsWithTape,
      HaltsWithTapeIn,
      HaltsFromTape,
      HaltsFromTapeIn,
      initial] using hseq
  · intro code T hhalt
    have hhaltFrom :
        (SeqViaCanonical parser emitter).HaltsFromTape
          (Tape.input (encodeCodeWordAsInput code)) T := by
      simpa [HaltsWithTape,
        HaltsWithTapeIn,
        HaltsFromTape,
        HaltsFromTapeIn,
        initial] using hhalt
    rcases
        SeqViaCanonical_haltsFromTape_inv
          hparser.left hemitter.left hhaltFrom with
      ⟨Tmid, hparserRun, hemitterRun⟩
    have hparserWith :
        parser.HaltsWithTape
          (encodeCodeWordAsInput code) Tmid := by
      simpa [HaltsWithTape,
        HaltsWithTapeIn,
        HaltsFromTape,
        HaltsFromTapeIn,
        initial] using hparserRun
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
      haltsFromTape_functional_of_haltTransitionFree
        hemitter.left.right hemitterRun' (hemitter.right L)
    refine ⟨L, ?_, hT⟩
    exact CommonGround.DovetailLayouts.decode_eq_some_encode hdecode

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

/-!
No selected-projection exact or right-shifted construction scaffold is exported
here.  The active bounded-runner phase path uses the padded/equivalence
finite-description construction.  If a future API needs exact primitive
packaging, it should supply a real
{name}`SelectedProjectionPrimitiveExactConstruction` witness and then use
{name}`selectedProjectionPrimitiveRightShiftedConstruction_of_exact`.
-/


end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
