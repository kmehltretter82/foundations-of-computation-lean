import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Quoter.SourceRestFinishCore.LTEmitterRuns

set_option doc.verso true

/-!
# Live-tail emitter output contracts

This module records normalized-output views for the live-tail emitter.  The
exact cursor-position contract in
{module}`FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Quoter.SourceRestFinishCore.LTEmitterRuns`
remains the executable boundary.  These output contracts are the weaker
interfaces needed by downstream routes that only inspect the emitted word and
do not depend on the final head position beside the live raw tail.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

open DovetailInitialLayoutInitializer

private theorem haltsFromTapeWithOutput_of_haltsFromTape_target
    {D : MachineDescription} {Tin Tout : Tape Bool}
    (h : D.HaltsFromTape Tin Tout) :
    D.HaltsFromTapeWithOutput Tin (Tape.normalizedOutput Tout) :=
  MachineDescription.haltsFromTapeWithOutput_of_haltsFromTape h

private theorem filterMap_id_comp_some_bool (w : Word Bool) :
    List.filterMap ((fun cell : Option Bool => cell) ∘ some) w = w := by
  simpa [Function.comp] using Tape.filterMap_id_map_some w

def mixedOptionCellQuoteLiveTailEmitterSourceNormalizedOutput
    (leftRev : List (Option Bool))
    (scanInput quoteRest : Word Bool) : Word Bool :=
  List.append
    (List.filterMap (fun cell => cell) leftRev.reverse)
    (List.append scanInput quoteRest)

def mixedOptionCellQuoteLiveTailEmitterSplitSourceNormalizedOutput
    (leftRev : List (Option Bool))
    (quoteScan rawTail quoteRest : Word Bool) : Word Bool :=
  List.append
    (List.filterMap (fun cell => cell) leftRev.reverse)
    (List.append quoteScan (List.append rawTail quoteRest))

def mixedOptionCellQuoteLiveTailEmitterTargetNormalizedOutput
    (emittedPrefix rawTail quoteRest : Word Bool) : Word Bool :=
  List.append emittedPrefix (List.append rawTail quoteRest)

theorem mixedOptionCellQuoteLiveTailEmitterSourceTape_normalizedOutput
    (leftRev : List (Option Bool))
    (scanInput quoteRest : Word Bool) :
    Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailEmitterSourceTape
          leftRev scanInput quoteRest) =
      mixedOptionCellQuoteLiveTailEmitterSourceNormalizedOutput
        leftRev scanInput quoteRest := by
  rw [Tape.normalizedOutput]
  rw [mixedOptionCellQuoteLiveTailEmitterSourceTape]
  cases scanInput <;>
    simp [tapeAtCells, Tape.cells,
      mixedOptionCellQuoteLiveTailEmitterSourceNormalizedOutput,
      filterMap_id_comp_some_bool]

theorem mixedOptionCellQuoteLiveTailEmitterSplitSourceTape_normalizedOutput
    (leftRev : List (Option Bool))
    (quoteScan rawTail quoteRest : Word Bool) :
    Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailEmitterSplitSourceTape
          leftRev quoteScan rawTail quoteRest) =
      mixedOptionCellQuoteLiveTailEmitterSplitSourceNormalizedOutput
        leftRev quoteScan rawTail quoteRest := by
  rw [Tape.normalizedOutput]
  rw [mixedOptionCellQuoteLiveTailEmitterSplitSourceTape_cells]
  simp [mixedOptionCellQuoteLiveTailEmitterSplitSourceNormalizedOutput,
    filterMap_id_comp_some_bool]

theorem mixedOptionCellQuoteLiveTailEmitterTargetTape_normalizedOutput
    (emittedPrefix rawTail quoteRest : Word Bool) :
    Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailEmitterTargetTape
          emittedPrefix rawTail quoteRest) =
      mixedOptionCellQuoteLiveTailEmitterTargetNormalizedOutput
        emittedPrefix rawTail quoteRest := by
  rw [Tape.normalizedOutput]
  rw [mixedOptionCellQuoteLiveTailEmitterTargetTape_cells]
  simp [mixedOptionCellQuoteLiveTailEmitterTargetNormalizedOutput,
    filterMap_id_comp_some_bool]

theorem mixedOptionCellQuoteLiveTailEmitterSourceNormalizedOutput_eq_split
    (leftRev : List (Option Bool))
    (quoteScan rawTail quoteRest : Word Bool) :
    mixedOptionCellQuoteLiveTailEmitterSourceNormalizedOutput
        leftRev (List.append quoteScan rawTail) quoteRest =
      mixedOptionCellQuoteLiveTailEmitterSplitSourceNormalizedOutput
        leftRev quoteScan rawTail quoteRest := by
  rw [mixedOptionCellQuoteLiveTailEmitterSourceNormalizedOutput,
    mixedOptionCellQuoteLiveTailEmitterSplitSourceNormalizedOutput]
  simp [List.append_assoc]

theorem mixedOptionCellQuoteLiveTailEmitterSourceTape_normalizedOutput_eq_split
    (leftRev : List (Option Bool))
    (quoteScan rawTail quoteRest : Word Bool) :
    Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailEmitterSourceTape
          leftRev (List.append quoteScan rawTail) quoteRest) =
      mixedOptionCellQuoteLiveTailEmitterSplitSourceNormalizedOutput
        leftRev quoteScan rawTail quoteRest := by
  rw [mixedOptionCellQuoteLiveTailEmitterSourceTape_normalizedOutput,
    mixedOptionCellQuoteLiveTailEmitterSourceNormalizedOutput_eq_split]

def mixedOptionCellQuoteLiveTailEmitterFamilySourceTape
    {ι : Type}
    (sourceLeftRev : ι -> List (Option Bool))
    (quoteScan rawTail quoteRest : ι -> Word Bool)
    (p : ι) : Tape Bool :=
  mixedOptionCellQuoteLiveTailEmitterSplitSourceTape
    (sourceLeftRev p) (quoteScan p) (rawTail p) (quoteRest p)

def mixedOptionCellQuoteLiveTailEmitterFamilyTargetTape
    {ι : Type}
    (rawTail quoteRest emittedPrefix : ι -> Word Bool)
    (p : ι) : Tape Bool :=
  mixedOptionCellQuoteLiveTailEmitterTargetTape
    (emittedPrefix p) (rawTail p) (quoteRest p)

def mixedOptionCellQuoteLiveTailEmitterFamilySourceOutput
    {ι : Type}
    (sourceLeftRev : ι -> List (Option Bool))
    (quoteScan rawTail quoteRest : ι -> Word Bool)
    (p : ι) : Word Bool :=
  mixedOptionCellQuoteLiveTailEmitterSplitSourceNormalizedOutput
    (sourceLeftRev p) (quoteScan p) (rawTail p) (quoteRest p)

def mixedOptionCellQuoteLiveTailEmitterFamilyTargetOutput
    {ι : Type}
    (rawTail quoteRest emittedPrefix : ι -> Word Bool)
    (p : ι) : Word Bool :=
  mixedOptionCellQuoteLiveTailEmitterTargetNormalizedOutput
    (emittedPrefix p) (rawTail p) (quoteRest p)

theorem mixedOptionCellQuoteLiveTailEmitterFamilySourceTape_eq
    {ι : Type}
    (sourceLeftRev : ι -> List (Option Bool))
    (quoteScan rawTail quoteRest : ι -> Word Bool)
    (p : ι) :
    mixedOptionCellQuoteLiveTailEmitterFamilySourceTape
        sourceLeftRev quoteScan rawTail quoteRest p =
      mixedOptionCellQuoteLiveTailEmitterSplitSourceTape
        (sourceLeftRev p) (quoteScan p) (rawTail p) (quoteRest p) := by
  rfl

theorem mixedOptionCellQuoteLiveTailEmitterFamilyTargetTape_eq
    {ι : Type}
    (rawTail quoteRest emittedPrefix : ι -> Word Bool)
    (p : ι) :
    mixedOptionCellQuoteLiveTailEmitterFamilyTargetTape
        rawTail quoteRest emittedPrefix p =
      mixedOptionCellQuoteLiveTailEmitterTargetTape
        (emittedPrefix p) (rawTail p) (quoteRest p) := by
  rfl

theorem mixedOptionCellQuoteLiveTailEmitterFamilySourceTape_normalizedOutput
    {ι : Type}
    (sourceLeftRev : ι -> List (Option Bool))
    (quoteScan rawTail quoteRest : ι -> Word Bool)
    (p : ι) :
    Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailEmitterFamilySourceTape
          sourceLeftRev quoteScan rawTail quoteRest p) =
      mixedOptionCellQuoteLiveTailEmitterFamilySourceOutput
        sourceLeftRev quoteScan rawTail quoteRest p := by
  rw [mixedOptionCellQuoteLiveTailEmitterFamilySourceTape,
    mixedOptionCellQuoteLiveTailEmitterFamilySourceOutput]
  exact
    mixedOptionCellQuoteLiveTailEmitterSplitSourceTape_normalizedOutput
      (sourceLeftRev p) (quoteScan p) (rawTail p) (quoteRest p)

theorem mixedOptionCellQuoteLiveTailEmitterFamilyTargetTape_normalizedOutput
    {ι : Type}
    (rawTail quoteRest emittedPrefix : ι -> Word Bool)
    (p : ι) :
    Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailEmitterFamilyTargetTape
          rawTail quoteRest emittedPrefix p) =
      mixedOptionCellQuoteLiveTailEmitterFamilyTargetOutput
        rawTail quoteRest emittedPrefix p := by
  rw [mixedOptionCellQuoteLiveTailEmitterFamilyTargetTape,
    mixedOptionCellQuoteLiveTailEmitterFamilyTargetOutput]
  exact
    mixedOptionCellQuoteLiveTailEmitterTargetTape_normalizedOutput
      (emittedPrefix p) (rawTail p) (quoteRest p)

def MixedOptionCellQuoteLiveTailEmitterForAssemblySourceRestOutputSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTapeWithOutput
        (mixedOptionCellQuoteLiveTailEmitterSplitSourceTape
          (some false ::
            List.append
              (List.reverse assemblySourceRestFinishParserMarkerLeftCells)
              [none])
          (assemblySourceRestFinishParserMarkerRightBits w)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)
          (preservingCellPassCellBits sourceRestBits))
        (Tape.normalizedOutput
          (mixedOptionCellQuoteLiveTailEmitterTargetTape
            (assemblySourceRestFinishPrefixQuoteOutputBits
              w sourceRestBits stage)
            (assemblySourceRestFinishRawTailBits sourceRestBits stage)
            (preservingCellPassCellBits sourceRestBits)))

def MixedOptionCellQuoteLiveTailEmitterOutputConstructionForAssemblySourceRest :
    Prop :=
  exists finish : MachineDescription,
    MixedOptionCellQuoteLiveTailEmitterForAssemblySourceRestOutputSpec finish

def MixedOptionCellQuoteLiveTailEmitterFamilyOutputSpec
    {ι : Type}
    (sourceLeftRev : ι -> List (Option Bool))
    (quoteScan rawTail quoteRest emittedPrefix : ι -> Word Bool)
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall p : ι,
      finish.HaltsFromTapeWithOutput
        (mixedOptionCellQuoteLiveTailEmitterFamilySourceTape
          sourceLeftRev quoteScan rawTail quoteRest p)
        (Tape.normalizedOutput
          (mixedOptionCellQuoteLiveTailEmitterFamilyTargetTape
            rawTail quoteRest emittedPrefix p))

def MixedOptionCellQuoteLiveTailEmitterFamilyOutputConstruction
    {ι : Type}
    (sourceLeftRev : ι -> List (Option Bool))
    (quoteScan rawTail quoteRest emittedPrefix : ι -> Word Bool) : Prop :=
  exists finish : MachineDescription,
    MixedOptionCellQuoteLiveTailEmitterFamilyOutputSpec
      sourceLeftRev quoteScan rawTail quoteRest emittedPrefix finish

def MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputSpec
    (finish : MachineDescription) : Prop :=
  MixedOptionCellQuoteLiveTailEmitterFamilyOutputSpec
    assemblySourceRestLiveTailEmitterLeftRev
    assemblySourceRestLiveTailEmitterQuoteScan
    assemblySourceRestLiveTailEmitterRawTail
    assemblySourceRestLiveTailEmitterQuoteRest
    assemblySourceRestLiveTailEmitterEmittedPrefix
    finish

def MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputConstruction :
    Prop :=
  MixedOptionCellQuoteLiveTailEmitterFamilyOutputConstruction
    assemblySourceRestLiveTailEmitterLeftRev
    assemblySourceRestLiveTailEmitterQuoteScan
    assemblySourceRestLiveTailEmitterRawTail
    assemblySourceRestLiveTailEmitterQuoteRest
    assemblySourceRestLiveTailEmitterEmittedPrefix

theorem MixedOptionCellQuoteLiveTailEmitterForAssemblySourceRestOutputSpec_subroutineReady
    {finish : MachineDescription}
    (hfinish :
      MixedOptionCellQuoteLiveTailEmitterForAssemblySourceRestOutputSpec
        finish) :
    finish.SubroutineReady :=
  hfinish.left

theorem MixedOptionCellQuoteLiveTailEmitterForAssemblySourceRestOutputSpec_haltsFromTapeWithOutput
    {finish : MachineDescription}
    (hfinish :
      MixedOptionCellQuoteLiveTailEmitterForAssemblySourceRestOutputSpec
        finish)
    (w sourceRestBits : Word Bool) (stage : Nat) :
    finish.HaltsFromTapeWithOutput
      (mixedOptionCellQuoteLiveTailEmitterSplitSourceTape
        (some false ::
          List.append
            (List.reverse assemblySourceRestFinishParserMarkerLeftCells)
            [none])
        (assemblySourceRestFinishParserMarkerRightBits w)
        (assemblySourceRestFinishRawTailBits sourceRestBits stage)
        (preservingCellPassCellBits sourceRestBits))
      (Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailEmitterTargetTape
          (assemblySourceRestFinishPrefixQuoteOutputBits
            w sourceRestBits stage)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)
          (preservingCellPassCellBits sourceRestBits))) :=
  hfinish.right w sourceRestBits stage

theorem MixedOptionCellQuoteLiveTailEmitterFamilyOutputSpec_subroutineReady
    {ι : Type}
    {sourceLeftRev : ι -> List (Option Bool)}
    {quoteScan rawTail quoteRest emittedPrefix : ι -> Word Bool}
    {finish : MachineDescription}
    (hfinish :
      MixedOptionCellQuoteLiveTailEmitterFamilyOutputSpec
        sourceLeftRev quoteScan rawTail quoteRest emittedPrefix finish) :
    finish.SubroutineReady :=
  hfinish.left

theorem MixedOptionCellQuoteLiveTailEmitterFamilyOutputSpec_haltsFromTapeWithOutput
    {ι : Type}
    {sourceLeftRev : ι -> List (Option Bool)}
    {quoteScan rawTail quoteRest emittedPrefix : ι -> Word Bool}
    {finish : MachineDescription}
    (hfinish :
      MixedOptionCellQuoteLiveTailEmitterFamilyOutputSpec
        sourceLeftRev quoteScan rawTail quoteRest emittedPrefix finish)
    (p : ι) :
    finish.HaltsFromTapeWithOutput
      (mixedOptionCellQuoteLiveTailEmitterFamilySourceTape
        sourceLeftRev quoteScan rawTail quoteRest p)
      (Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailEmitterFamilyTargetTape
          rawTail quoteRest emittedPrefix p)) :=
  hfinish.right p

theorem MixedOptionCellQuoteLiveTailEmitterForAssemblySourceRestOutputSpec_of_exact
    {finish : MachineDescription}
    (hfinish :
      MixedOptionCellQuoteLiveTailEmitterForAssemblySourceRestSpec finish) :
    MixedOptionCellQuoteLiveTailEmitterForAssemblySourceRestOutputSpec
      finish := by
  refine ⟨hfinish.left, ?_⟩
  intro w sourceRestBits stage
  exact
    haltsFromTapeWithOutput_of_haltsFromTape_target
      (hfinish.right w sourceRestBits stage)

theorem MixedOptionCellQuoteLiveTailEmitterOutputConstructionForAssemblySourceRest_of_exact
    (h :
      MixedOptionCellQuoteLiveTailEmitterConstructionForAssemblySourceRest) :
    MixedOptionCellQuoteLiveTailEmitterOutputConstructionForAssemblySourceRest := by
  rcases h with ⟨finish, hfinish⟩
  exact
    ⟨finish,
      MixedOptionCellQuoteLiveTailEmitterForAssemblySourceRestOutputSpec_of_exact
        hfinish⟩

theorem MixedOptionCellQuoteLiveTailEmitterFamilyOutputSpec_of_exact
    {ι : Type}
    {sourceLeftRev : ι -> List (Option Bool)}
    {quoteScan rawTail quoteRest emittedPrefix : ι -> Word Bool}
    {finish : MachineDescription}
    (hfinish :
      MixedOptionCellQuoteLiveTailEmitterFamilySpec
        sourceLeftRev quoteScan rawTail quoteRest emittedPrefix finish) :
    MixedOptionCellQuoteLiveTailEmitterFamilyOutputSpec
      sourceLeftRev quoteScan rawTail quoteRest emittedPrefix finish := by
  refine ⟨hfinish.left, ?_⟩
  intro p
  exact
    haltsFromTapeWithOutput_of_haltsFromTape_target
      (hfinish.right p)

theorem MixedOptionCellQuoteLiveTailEmitterFamilyOutputConstruction_of_exact
    {ι : Type}
    {sourceLeftRev : ι -> List (Option Bool)}
    {quoteScan rawTail quoteRest emittedPrefix : ι -> Word Bool}
    (h :
      MixedOptionCellQuoteLiveTailEmitterFamilyConstruction
        sourceLeftRev quoteScan rawTail quoteRest emittedPrefix) :
    MixedOptionCellQuoteLiveTailEmitterFamilyOutputConstruction
      sourceLeftRev quoteScan rawTail quoteRest emittedPrefix := by
  rcases h with ⟨finish, hfinish⟩
  exact
    ⟨finish,
      MixedOptionCellQuoteLiveTailEmitterFamilyOutputSpec_of_exact
        hfinish⟩

theorem MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputSpec_iff_assemblyOutputSpec
    (finish : MachineDescription) :
    MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputSpec finish ↔
      MixedOptionCellQuoteLiveTailEmitterForAssemblySourceRestOutputSpec
        finish := by
  constructor
  · intro hfinish
    refine ⟨hfinish.left, ?_⟩
    intro w sourceRestBits stage
    exact hfinish.right
      { w := w, sourceRestBits := sourceRestBits, stage := stage }
  · intro hfinish
    refine ⟨hfinish.left, ?_⟩
    intro p
    cases p with
    | mk w sourceRestBits stage =>
        exact hfinish.right w sourceRestBits stage

theorem MixedOptionCellQuoteLiveTailEmitterOutputConstructionForAssemblySourceRest_of_outputFamily
    (h : MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputConstruction) :
    MixedOptionCellQuoteLiveTailEmitterOutputConstructionForAssemblySourceRest := by
  rcases h with ⟨finish, hfinish⟩
  exact
    ⟨finish,
      (MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputSpec_iff_assemblyOutputSpec
        finish).mp hfinish⟩

theorem MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputConstruction_of_assemblyOutput
    (h :
      MixedOptionCellQuoteLiveTailEmitterOutputConstructionForAssemblySourceRest) :
    MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputConstruction := by
  rcases h with ⟨finish, hfinish⟩
  exact
    ⟨finish,
      (MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputSpec_iff_assemblyOutputSpec
        finish).mpr hfinish⟩

def assemblySourceRestFinishPrefixQuotedSeparatedOutput
    (w sourceRestBits : Word Bool) (stage : Nat) : Word Bool :=
  List.append
    (assemblySourceRestFinishPrefixQuoteOutputBits w sourceRestBits stage)
    (List.append
      (assemblySourceRestFinishRawTailBits sourceRestBits stage)
      (preservingCellPassCellBits sourceRestBits))

theorem assemblySourceRestFinishPrefixQuotedSeparatedOutput_eq_emitterTarget
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishPrefixQuotedSeparatedOutput
        w sourceRestBits stage =
      mixedOptionCellQuoteLiveTailEmitterTargetNormalizedOutput
        (assemblySourceRestFinishPrefixQuoteOutputBits
          w sourceRestBits stage)
        (assemblySourceRestFinishRawTailBits sourceRestBits stage)
        (preservingCellPassCellBits sourceRestBits) := by
  rfl

theorem mixedOptionCellQuoteLiveTailEmitterTargetTape_normalizedOutput_assembly
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailEmitterTargetTape
          (assemblySourceRestFinishPrefixQuoteOutputBits
            w sourceRestBits stage)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)
          (preservingCellPassCellBits sourceRestBits)) =
      assemblySourceRestFinishPrefixQuotedSeparatedOutput
        w sourceRestBits stage := by
  rw [mixedOptionCellQuoteLiveTailEmitterTargetTape_normalizedOutput]
  rfl

theorem MixedParserStackWholeSourcePrefixQuotedSeparatedTape_normalizedOutput
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.normalizedOutput
        (MixedParserStackWholeSourcePrefixQuotedSeparatedTape
          w sourceRestBits stage) =
      assemblySourceRestFinishPrefixQuotedSeparatedOutput
        w sourceRestBits stage := by
  rw [
    MixedParserStackWholeSourcePrefixQuotedSeparatedTape_eq_mixedOptionCellQuoteLiveTailEmitterTargetTape]
  exact
    mixedOptionCellQuoteLiveTailEmitterTargetTape_normalizedOutput_assembly
      w sourceRestBits stage

theorem MixedParserStackWholeSourcePrefixQuotedSeparatedTape_normalizedOutput_eq_targetTape
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.normalizedOutput
        (MixedParserStackWholeSourcePrefixQuotedSeparatedTape
          w sourceRestBits stage) =
      Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailEmitterTargetTape
          (assemblySourceRestFinishPrefixQuoteOutputBits
            w sourceRestBits stage)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)
          (preservingCellPassCellBits sourceRestBits)) := by
  rw [
    MixedParserStackWholeSourcePrefixQuotedSeparatedTape_eq_mixedOptionCellQuoteLiveTailEmitterTargetTape]

theorem MixedParserStackRewriterDefaultedInternalMarkerTape_normalizedOutput
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    Tape.normalizedOutput
        (MixedParserStackRewriterDefaultedInternalMarkerTape
          w sourceRestBits quoteRestBits stage) =
      mixedOptionCellQuoteLiveTailEmitterSourceNormalizedOutput
        (some false ::
          List.append
            (List.reverse assemblySourceRestFinishParserMarkerLeftCells)
            [none])
        (assemblySourceRestFinishRightPayloadBits
          w sourceRestBits stage)
        quoteRestBits := by
  rw [
    MixedParserStackRewriterDefaultedInternalMarkerTape_eq_mixedOptionCellQuoteLiveTailEmitterSourceTape,
    mixedOptionCellQuoteLiveTailEmitterSourceTape_normalizedOutput]

theorem MixedParserStackRewriterDefaultedInternalMarkerTape_normalizedOutput_split
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    Tape.normalizedOutput
        (MixedParserStackRewriterDefaultedInternalMarkerTape
          w sourceRestBits quoteRestBits stage) =
      mixedOptionCellQuoteLiveTailEmitterSplitSourceNormalizedOutput
        (some false ::
          List.append
            (List.reverse assemblySourceRestFinishParserMarkerLeftCells)
            [none])
        (assemblySourceRestFinishParserMarkerRightBits w)
        (assemblySourceRestFinishRawTailBits sourceRestBits stage)
        quoteRestBits := by
  rw [
    MixedParserStackRewriterDefaultedInternalMarkerTape_eq_mixedOptionCellQuoteLiveTailEmitterSplitSourceTape,
    mixedOptionCellQuoteLiveTailEmitterSplitSourceTape_normalizedOutput]

def MixedParserStackPrefixQuotedSeparatedFinisherAssemblySourceRestOutputSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTapeWithOutput
        (MixedParserStackRewriterDefaultedInternalMarkerTape
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (Tape.normalizedOutput
          (MixedParserStackWholeSourcePrefixQuotedSeparatedTape
            w sourceRestBits stage))

def MixedParserStackPrefixQuotedSeparatedFinisherOutputConstructionForAssemblySourceRest :
    Prop :=
  exists finish : MachineDescription,
    MixedParserStackPrefixQuotedSeparatedFinisherAssemblySourceRestOutputSpec
      finish

theorem MixedParserStackPrefixQuotedSeparatedFinisherAssemblySourceRestOutputSpec_subroutineReady
    {finish : MachineDescription}
    (hfinish :
      MixedParserStackPrefixQuotedSeparatedFinisherAssemblySourceRestOutputSpec
        finish) :
    finish.SubroutineReady :=
  hfinish.left

theorem MixedParserStackPrefixQuotedSeparatedFinisherAssemblySourceRestOutputSpec_haltsFromTapeWithOutput
    {finish : MachineDescription}
    (hfinish :
      MixedParserStackPrefixQuotedSeparatedFinisherAssemblySourceRestOutputSpec
        finish)
    (w sourceRestBits : Word Bool) (stage : Nat) :
    finish.HaltsFromTapeWithOutput
      (MixedParserStackRewriterDefaultedInternalMarkerTape
        w sourceRestBits
        (preservingCellPassCellBits sourceRestBits)
        stage)
      (Tape.normalizedOutput
        (MixedParserStackWholeSourcePrefixQuotedSeparatedTape
          w sourceRestBits stage)) :=
  hfinish.right w sourceRestBits stage

theorem assemblySourceRestOutputConstruction_ofLiveTailEmitterOutput
    (h :
      MixedOptionCellQuoteLiveTailEmitterOutputConstructionForAssemblySourceRest) :
    MixedParserStackPrefixQuotedSeparatedFinisherOutputConstructionForAssemblySourceRest := by
  rcases h with ⟨finish, hfinish⟩
  refine ⟨finish, hfinish.left, ?_⟩
  intro w sourceRestBits stage
  rw [
    MixedParserStackRewriterDefaultedInternalMarkerTape_eq_mixedOptionCellQuoteLiveTailEmitterSplitSourceTape]
  rw [
    MixedParserStackWholeSourcePrefixQuotedSeparatedTape_eq_mixedOptionCellQuoteLiveTailEmitterTargetTape]
  exact hfinish.right w sourceRestBits stage

theorem MixedParserStackPrefixQuotedSeparatedFinisherOutputConstructionForAssemblySourceRest_of_mixedOptionCellQuoteLiveTailEmitter
    (h :
      MixedOptionCellQuoteLiveTailEmitterConstructionForAssemblySourceRest) :
    MixedParserStackPrefixQuotedSeparatedFinisherOutputConstructionForAssemblySourceRest :=
  assemblySourceRestOutputConstruction_ofLiveTailEmitterOutput
    (MixedOptionCellQuoteLiveTailEmitterOutputConstructionForAssemblySourceRest_of_exact
      h)

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
