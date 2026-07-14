import FoC.Computability.Compiler.ClosedCfg.QuoteAssembly.Finish
import FoC.Computability.Compiler.ClosedCfg.QuoteRest

set_option doc.verso true

/-!
This module connects the canonical quoter assembly prefix execution with the
source-rest finisher and raw-cell quotation loops. The prefix-to-boundary run is
a thin specialization of the checked
{module}`FoC.Computability.Compiler.ClosedCfg.QuoteAssembly` core.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

open DovetailInitialLayoutInitializer
open DovetailInitialLayoutInitializer.StageInputMarkedScanner

def selectedProjectionInputQuoterPrefixBoundaryTape
    (L : DovetailLayout) : Tape Bool :=
  tapeAtCells
    (assemblySourceRestBoundaryLeftRev L.input L.stage)
    (List.append
      ((SelectedProjectionTailProjector.sourceRestFieldBits L).map some)
      [none])

theorem assemblyPrefixDescription_haltsFrom_exactSourceTape_to_prefixBoundary
    (L : DovetailLayout) :
    AssemblyPrefixDescription.HaltsFromTape
      (SelectedProjectionInputQuoterExactSourceTape L)
      (selectedProjectionInputQuoterPrefixBoundaryTape L) := by
  rw [SelectedProjectionInputQuoterExactSourceTape,
    selectedProjectionInputQuoterPrefixBoundaryTape]
  rcases
      assemblyPrefixDescription_run_stageInput_to_sourceRest_boundary_cells_withBase_core
        [] L.input L.stage
        (List.append
          ((SelectedProjectionTailProjector.sourceRestFieldBits L).map some)
          [none]) with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  unfold MachineDescription.HaltsFromTapeIn
  constructor
  · simpa [AssemblyPrefixDescription, config, List.map_append,
      List.append_assoc] using congrArg Configuration.state hsteps
  · simpa [AssemblyPrefixDescription, config, List.map_append,
      List.append_assoc] using congrArg Configuration.tape hsteps

def SelectedProjectionInputQuoterPrefixSpec
    (pref : MachineDescription) : Prop :=
  pref.SubroutineReady ∧
    forall L : DovetailLayout,
      pref.HaltsFromTape
        (SelectedProjectionInputQuoterExactSourceTape L)
        (selectedProjectionInputQuoterPrefixBoundaryTape L)

def SelectedProjectionInputQuoterPrefixConstruction : Prop :=
  exists pref : MachineDescription,
    SelectedProjectionInputQuoterPrefixSpec pref

theorem selectedProjectionInputQuoterPrefixConstruction :
    SelectedProjectionInputQuoterPrefixConstruction := by
  refine ⟨AssemblyPrefixDescription, ?_⟩
  constructor
  · exact assemblyPrefixDescription_subroutineReady
  · exact assemblyPrefixDescription_haltsFrom_exactSourceTape_to_prefixBoundary

def selectedProjectionInputQuoterPostBoundarySourceTape
    (L : DovetailLayout) : Tape Bool :=
  Tape.move Direction.left
    (Tape.move Direction.right
      (selectedProjectionInputQuoterPrefixBoundaryTape L))

def SelectedProjectionInputQuoterPostBoundarySpec
    (post : MachineDescription) : Prop :=
  post.SubroutineReady ∧
    forall L : DovetailLayout,
      post.HaltsFromTapeEquiv
        (selectedProjectionInputQuoterPostBoundarySourceTape L)
        (SelectedProjectionInputQuoterExactTargetTape L)

def SelectedProjectionInputQuoterPostBoundaryConstruction : Prop :=
  exists post : MachineDescription,
    SelectedProjectionInputQuoterPostBoundarySpec post

private theorem sourceRestFieldBits_cons_cons
    (L : DovetailLayout) :
    exists head : Bool,
    exists next : Bool,
    exists right : Word Bool,
      SelectedProjectionTailProjector.sourceRestFieldBits L =
        head :: next :: right := by
  rcases
      SelectedProjectionTailProjector.stageNatBits_cons_cons
        L.acceptConfig.state with
    ⟨head, next, stateTail, hstate⟩
  refine
    ⟨head, next,
      List.append stateTail
        (CanonicalLayouts.DovetailLayoutScanner.tapeFieldBits
          L.acceptConfig.tape
          (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.rejectConfig
            (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
              L.acceptHit
              (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                L.rejectHit [])))), ?_⟩
  simp [SelectedProjectionTailProjector.sourceRestFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits,
    hstate]

private theorem selectedProjectionInputQuoterPostBoundarySourceTape_eq_prefixBoundaryTape
    (L : DovetailLayout) :
    selectedProjectionInputQuoterPostBoundarySourceTape L =
      selectedProjectionInputQuoterPrefixBoundaryTape L := by
  rcases sourceRestFieldBits_cons_cons L with
    ⟨head, next, right, hsource⟩
  rw [selectedProjectionInputQuoterPostBoundarySourceTape,
    selectedProjectionInputQuoterPrefixBoundaryTape, hsource]
  simp [List.map_cons]
  exact
    FoC.Computability.CommonGround.FiniteTransducers.tapeAtCells_move_left_move_right_cons_cons
      (assemblySourceRestBoundaryLeftRev L.input L.stage)
      (some head) (some next)
      (List.append (right.map some) [none])

private theorem selectedProjectionInputQuoterPostBoundarySourceTape_eq_sourceRestBoundary
    (L : DovetailLayout) :
    selectedProjectionInputQuoterPostBoundarySourceTape L =
      tapeAtCells
        (assemblySourceRestBoundaryLeftRev L.input L.stage)
        (List.append
          ((SelectedProjectionTailProjector.sourceRestFieldBits L).map some)
          [none]) := by
  rw [selectedProjectionInputQuoterPostBoundarySourceTape_eq_prefixBoundaryTape,
    selectedProjectionInputQuoterPrefixBoundaryTape]

theorem preservingCellPassDescription_haltsFrom_postBoundarySourceTape
    (L : DovetailLayout) :
    PreservingCellPassDescription.HaltsFromTape
      (selectedProjectionInputQuoterPostBoundarySourceTape L)
      (preservingCellPassHaltTape
        (assemblySourceRestBoundaryLeftRev L.input L.stage)
        (SelectedProjectionTailProjector.sourceRestFieldBits L) []) := by
  rw [selectedProjectionInputQuoterPostBoundarySourceTape_eq_sourceRestBoundary]
  rcases sourceRestFieldBits_cons_cons L with
    ⟨head, next, right, hsource⟩
  rw [hsource]
  simpa [List.map_cons] using
    preservingCellPassDescription_haltsFrom_nonempty_cells_oneBlank
      (assemblySourceRestBoundaryLeftRev L.input L.stage)
      head (next :: right)

private theorem selectedProjectionInputQuoterExactTargetTape_eq_sourceTape_outputPrefix
    (L : DovetailLayout) :
    SelectedProjectionInputQuoterExactTargetTape L =
      SelectedProjectionTailProjector.sourceTape L
        ((SelectedProjectionTailProjector.outputPrefixStageInputSourceRestFieldBits
          L).reverse.map some) := by
  rw [SelectedProjectionInputQuoterExactTargetTape,
    SelectedProjectionTailProjector.sourceTape,
    SelectedProjectionTailProjector.sourceFieldBits_eq_stageNatBits_sourceRestFieldBits]

def selectedProjectionInputQuoterRawCellQuoteTargetTape
    (L : DovetailLayout) : Tape Bool :=
  tapeAtCells
    ((List.append
      (encodeCodeSymbolAsInput MachineCodeSymbol.header)
      (List.append
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          (ParsedLayoutBits L).length)
        (preservingCellPassCellBits (ParsedLayoutBits L)))).reverse.map
      some)
    ((SelectedProjectionTailProjector.sourceFieldBits L).map some)

private theorem selectedProjectionInputQuoterExactTargetTape_eq_rawCellQuoteTargetTape
    (L : DovetailLayout) :
    SelectedProjectionInputQuoterExactTargetTape L =
      selectedProjectionInputQuoterRawCellQuoteTargetTape L := by
  rw [selectedProjectionInputQuoterRawCellQuoteTargetTape]
  rw [SelectedProjectionInputQuoterExactTargetTape,
    SelectedProjectionTailProjector.sourceFieldBits_eq_stageNatBits_sourceRestFieldBits]
  congr 1
  rw [SelectedProjectionTailProjector.outputPrefixStageInputSourceRestFieldBits]
  rw [SelectedProjectionTailProjector.parsedLayoutBits_eq_transition_stageInput_sourceRestFieldBits]
  rw [← preservingCellPassQuoteBits_eq_encodeBoolWordAppend]

private theorem selectedProjectionInputQuoterBoundaryDefaultBits_eq_parsedLayoutBits
    (L : DovetailLayout) :
    List.append
        (List.map optionBitDefaultFalse
          (List.reverse
            (assemblySourceRestBoundaryLeftRev L.input L.stage)))
        (SelectedProjectionTailProjector.sourceRestFieldBits L) =
      ParsedLayoutBits L :=
  assemblySourceRestBoundaryLeftRev_defaultBits_append_sourceRestFieldBits L

def selectedProjectionInputQuoterAfterSourceRestPassTape
    (L : DovetailLayout) : Tape Bool :=
  Tape.move Direction.left
    (Tape.move Direction.right
      (preservingCellPassHaltTape
        (assemblySourceRestBoundaryLeftRev L.input L.stage)
        (SelectedProjectionTailProjector.sourceRestFieldBits L) []))

def selectedProjectionInputQuoterAfterSourceRestSourceShapeTape
    (L : DovetailLayout) : Tape Bool :=
  tapeAtCells
    (none ::
      List.append
        ((SelectedProjectionTailProjector.sourceRestFieldBits L).reverse.map
          some)
        (assemblySourceRestBoundaryLeftRev L.input L.stage))
    (List.append
      ((preservingCellPassCellBits
        (SelectedProjectionTailProjector.sourceRestFieldBits L)).map some)
      [none])

def selectedProjectionInputQuoterRawCellQuoteTargetShapeTape
    (L : DovetailLayout) : Tape Bool :=
  tapeAtCells
    ((SelectedProjectionTailProjector.outputPrefixStageInputSourceRestFieldBits
      L).reverse.map some)
    ((SelectedProjectionTailProjector.sourceFieldBits L).map some)

private theorem selectedProjectionInputQuoterAfterSourceRestPassTape_eq_haltTape
    (L : DovetailLayout) :
    selectedProjectionInputQuoterAfterSourceRestPassTape L =
      preservingCellPassHaltTape
        (assemblySourceRestBoundaryLeftRev L.input L.stage)
        (SelectedProjectionTailProjector.sourceRestFieldBits L) [] := by
  rw [selectedProjectionInputQuoterAfterSourceRestPassTape]
  rcases sourceRestFieldBits_cons_cons L with
    ⟨head, next, right, hsource⟩
  rw [hsource]
  rcases preservingCellPassHaltTape_right_cons_of_nonempty
      (assemblySourceRestBoundaryLeftRev L.input L.stage)
      head (next :: right) with
    ⟨cell, tail, hright⟩
  exact Tape.move_left_move_right_eq_self_of_right_cons _ hright

private theorem selectedProjectionInputQuoterAfterSourceRestPassTape_eq_tapeAtCells
    (L : DovetailLayout) :
    selectedProjectionInputQuoterAfterSourceRestPassTape L =
      selectedProjectionInputQuoterAfterSourceRestSourceShapeTape L := by
  rw [selectedProjectionInputQuoterAfterSourceRestPassTape_eq_haltTape]
  rw [selectedProjectionInputQuoterAfterSourceRestSourceShapeTape]
  rcases sourceRestFieldBits_cons_cons L with
    ⟨head, next, right, hsource⟩
  rw [hsource]
  exact
    preservingCellPassHaltTape_nonempty_empty_output_eq_tapeAtCells
      (assemblySourceRestBoundaryLeftRev L.input L.stage)
      head (next :: right)

private theorem selectedProjectionInputQuoterRawCellQuoteTargetTape_eq_shapeTape
    (L : DovetailLayout) :
    selectedProjectionInputQuoterRawCellQuoteTargetTape L =
      selectedProjectionInputQuoterRawCellQuoteTargetShapeTape L := by
  rw [← selectedProjectionInputQuoterExactTargetTape_eq_rawCellQuoteTargetTape]
  rw [selectedProjectionInputQuoterRawCellQuoteTargetShapeTape]
  rw [SelectedProjectionInputQuoterExactTargetTape,
    SelectedProjectionTailProjector.sourceFieldBits_eq_stageNatBits_sourceRestFieldBits]

private theorem selectedProjectionInputQuoterAfterSourceRestPassTape_cells
    (L : DovetailLayout) :
    Tape.cells (selectedProjectionInputQuoterAfterSourceRestPassTape L) =
      List.append
        (List.reverse (assemblySourceRestBoundaryLeftRev L.input L.stage))
        (List.append
          ((SelectedProjectionTailProjector.sourceRestFieldBits L).map some)
          (none ::
            List.append
              ((preservingCellPassCellBits
                (SelectedProjectionTailProjector.sourceRestFieldBits L)).map
                some)
      [none])) := by
  rw [selectedProjectionInputQuoterAfterSourceRestPassTape_eq_tapeAtCells]
  rw [selectedProjectionInputQuoterAfterSourceRestSourceShapeTape]
  rcases sourceRestFieldBits_cons_cons L with
    ⟨head, next, right, hsource⟩
  rw [hsource]
  cases head <;>
    simp [tapeAtCells, Tape.cells, preservingCellPassCellBits,
      preservingCellPassZeroBits, preservingCellPassOneBits,
      List.map_append, List.append_assoc]

private theorem selectedProjectionInputQuoterAfterSourceRestPassTape_defaultedCells
    (L : DovetailLayout) :
    List.map optionBitDefaultFalse
        (Tape.cells (selectedProjectionInputQuoterAfterSourceRestPassTape L)) =
      List.append (ParsedLayoutBits L)
        (false ::
          List.append
            (preservingCellPassCellBits
              (SelectedProjectionTailProjector.sourceRestFieldBits L))
            [false]) := by
  rw [selectedProjectionInputQuoterAfterSourceRestPassTape_cells]
  have hprefix :=
    selectedProjectionInputQuoterBoundaryDefaultBits_eq_parsedLayoutBits L
  simpa [optionBitDefaultFalse, Function.comp_def, List.map_append,
    List.append_assoc] using
    congrArg
      (fun pref =>
        List.append pref
          (false ::
            List.append
              (preservingCellPassCellBits
                (SelectedProjectionTailProjector.sourceRestFieldBits L))
              [false]))
      hprefix

private theorem selectedProjectionInputQuoterRawCellQuoteTargetTape_normalizedOutput
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedProjectionInputQuoterRawCellQuoteTargetTape L) =
      List.append
        (SelectedProjectionTailProjector.outputPrefixStageInputSourceRestFieldBits
          L)
        (SelectedProjectionTailProjector.sourceFieldBits L) := by
  rw [← selectedProjectionInputQuoterExactTargetTape_eq_rawCellQuoteTargetTape]
  rw [selectedProjectionInputQuoterExactTargetTape_eq_sourceTape_outputPrefix]
  rw [SelectedProjectionTailProjector.sourceTape_normalizedOutput]
  simp [Function.comp_def, List.map_reverse]

private theorem selectedProjectionInputQuoterRawCellQuoteTargetTape_cells
    (L : DovetailLayout) :
    Tape.cells (selectedProjectionInputQuoterRawCellQuoteTargetTape L) =
      List.append
        ((SelectedProjectionTailProjector.outputPrefixStageInputSourceRestFieldBits
          L).map some)
        ((SelectedProjectionTailProjector.sourceFieldBits L).map some) := by
  rw [selectedProjectionInputQuoterRawCellQuoteTargetTape]
  rcases SelectedProjectionTailProjector.stageNatBits_cons_cons L.stage with
    ⟨head, next, right, hstage⟩
  rw [SelectedProjectionTailProjector.sourceFieldBits_eq_stageNatBits_sourceRestFieldBits,
    hstage]
  simp [tapeAtCells, Tape.cells, List.reverse_append, List.map_append,
    List.append_assoc]
  rw [SelectedProjectionTailProjector.parsedLayoutBits_eq_transition_stageInput_sourceRestFieldBits]
  have hquote :=
    congrArg (List.map some)
      (preservingCellPassHeaderQuoteBits_eq_outputPrefixStageInputSourceRestFieldBits
        L)
  simpa [List.map_append, List.length_append, List.append_assoc] using
    congrArg
      (fun pref =>
        List.append pref
          (some head :: some next ::
            (List.append (right.map some)
              ((SelectedProjectionTailProjector.sourceRestFieldBits L).map
                some))))
      hquote

def SelectedProjectionInputQuoterAfterSourceRestPassSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall L : DovetailLayout,
      finish.HaltsFromTapeEquiv
        (selectedProjectionInputQuoterAfterSourceRestPassTape L)
        (selectedProjectionInputQuoterRawCellQuoteTargetTape L)

def SelectedProjectionInputQuoterAfterSourceRestShapeSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall L : DovetailLayout,
      finish.HaltsFromTapeEquiv
        (selectedProjectionInputQuoterAfterSourceRestSourceShapeTape L)
        (selectedProjectionInputQuoterRawCellQuoteTargetShapeTape L)

def SelectedProjectionInputQuoterAfterSourceRestPassConstruction :
    Prop :=
  exists finish : MachineDescription,
    SelectedProjectionInputQuoterAfterSourceRestPassSpec finish

def SelectedProjectionInputQuoterAfterSourceRestShapeConstruction :
    Prop :=
  exists finish : MachineDescription,
    SelectedProjectionInputQuoterAfterSourceRestShapeSpec finish


private theorem assemblySourceRestFinishTargetPrefixBits_eq_outputPrefix
    (L : DovetailLayout) :
    assemblySourceRestFinishTargetPrefixBits L.input
        (SelectedProjectionTailProjector.sourceRestFieldBits L) L.stage =
      SelectedProjectionTailProjector.outputPrefixStageInputSourceRestFieldBits
        L := by
  simpa [assemblySourceRestFinishTargetPrefixBits,
    assemblySourceRestFinishSourceBits] using!
    preservingCellPassHeaderQuoteBits_eq_outputPrefixStageInputSourceRestFieldBits
      L

private theorem assemblySourceRestFinishSourceBits_eq_parsedLayoutBits
    (L : DovetailLayout) :
    assemblySourceRestFinishSourceBits L.input
        (SelectedProjectionTailProjector.sourceRestFieldBits L) L.stage =
      ParsedLayoutBits L := by
  rw [assemblySourceRestFinishSourceBits_eq]
  exact
    (SelectedProjectionTailProjector.parsedLayoutBits_eq_transition_stageInput_sourceRestFieldBits
      L).symm

private theorem assemblySourceRestFinishTargetTape_selected_normalizedOutput
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (assemblySourceRestFinishTargetTape L.input
          (SelectedProjectionTailProjector.sourceRestFieldBits L)
          L.stage) =
      List.append
        (SelectedProjectionTailProjector.outputPrefixStageInputSourceRestFieldBits
          L)
        (SelectedProjectionTailProjector.sourceFieldBits L) := by
  rw [assemblySourceRestFinishTargetTape_normalizedOutput]
  rw [assemblySourceRestFinishTargetPrefixBits_eq_outputPrefix]
  rw [SelectedProjectionTailProjector.sourceFieldBits_eq_stageNatBits_sourceRestFieldBits]

private theorem assemblySourceRestFinishSourceTape_selected_eq_shapeTape
    (L : DovetailLayout) :
    assemblySourceRestFinishSourceTape L.input
        (SelectedProjectionTailProjector.sourceRestFieldBits L) L.stage =
      selectedProjectionInputQuoterAfterSourceRestSourceShapeTape L := by
  rfl

private theorem assemblySourceRestFinishTargetTape_selected_eq_shapeTape
    (L : DovetailLayout) :
    assemblySourceRestFinishTargetTape L.input
        (SelectedProjectionTailProjector.sourceRestFieldBits L) L.stage =
      selectedProjectionInputQuoterRawCellQuoteTargetShapeTape L := by
  rw [assemblySourceRestFinishTargetTape,
    selectedProjectionInputQuoterRawCellQuoteTargetShapeTape]
  rw [assemblySourceRestFinishTargetPrefixBits_eq_outputPrefix]
  rw [SelectedProjectionTailProjector.sourceFieldBits_eq_stageNatBits_sourceRestFieldBits]

theorem selectedProjectionInputQuoterAfterSourceRestShapeConstruction :
    SelectedProjectionInputQuoterAfterSourceRestShapeConstruction := by
  rcases assemblySourceRestFinishEquivConstruction_for_assemblySourceRest with
    ⟨finish, hfinish⟩
  refine ⟨finish, hfinish.left, ?_⟩
  intro L
  rw [← assemblySourceRestFinishSourceTape_selected_eq_shapeTape,
    ← assemblySourceRestFinishTargetTape_selected_eq_shapeTape]
  exact
    hfinish.right L.input
      (SelectedProjectionTailProjector.sourceRestFieldBits L) L.stage

def selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryTape
    (L : DovetailLayout) : Tape Bool :=
  scanRightToBlankLeftHaltTape
    (none ::
      List.append
        ((SelectedProjectionTailProjector.sourceRestFieldBits L).reverse.map
          some)
        (assemblySourceRestBoundaryLeftRev L.input L.stage))
    (preservingCellPassCellBits
      (SelectedProjectionTailProjector.sourceRestFieldBits L))

theorem scanRightToBlankLeftDescription_haltsFrom_afterSourceRestPassTape
    (L : DovetailLayout) :
    scanRightToBlankLeftDescription.HaltsFromTape
      (selectedProjectionInputQuoterAfterSourceRestPassTape L)
      (selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryTape L) := by
  rw [selectedProjectionInputQuoterAfterSourceRestPassTape_eq_tapeAtCells,
    selectedProjectionInputQuoterAfterSourceRestSourceShapeTape,
    selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryTape]
  exact
    scanRightToBlankLeftDescription_haltsFromTape
      (none ::
        List.append
          ((SelectedProjectionTailProjector.sourceRestFieldBits L).reverse.map
            some)
          (assemblySourceRestBoundaryLeftRev L.input L.stage))
      (preservingCellPassCellBits
        (SelectedProjectionTailProjector.sourceRestFieldBits L))

private theorem selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryTape_move_left_move_right
    (L : DovetailLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryTape L)) =
      selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryTape L := by
  rcases sourceRestFieldBits_cons_cons L with
    ⟨head, next, right, hsource⟩
  rcases preservingCellPassCellBits_cons_exists head (next :: right) with
    ⟨quoteHead, quoteTail, hquote⟩
  rw [selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryTape,
    hsource, hquote]
  exact
    scanRightToBlankLeftHaltTape_move_left_move_right_cons
      (none ::
        List.append (((head :: next :: right).reverse).map some)
          (assemblySourceRestBoundaryLeftRev L.input L.stage))
      quoteHead quoteTail

def selectedProjectionInputQuoterAfterSourceRestLeftBoundaryTape
    (L : DovetailLayout) : Tape Bool :=
  scanLeftToBlankLeftHaltTape
    (List.append
      ((SelectedProjectionTailProjector.sourceRestFieldBits L).reverse.map
        some)
      (assemblySourceRestBoundaryLeftRev L.input L.stage))
    (preservingCellPassCellBits
      (SelectedProjectionTailProjector.sourceRestFieldBits L))
    [none]

theorem scanLeftToBlankLeftDescription_haltsFrom_afterSourceRestQuoteBoundaryTape
    (L : DovetailLayout) :
    scanLeftToBlankLeftDescription.HaltsFromTape
      (selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryTape L)
      (selectedProjectionInputQuoterAfterSourceRestLeftBoundaryTape L) := by
  rcases sourceRestFieldBits_cons_cons L with
    ⟨head, next, right, hsource⟩
  rcases preservingCellPassCellBits_cons_exists head (next :: right) with
    ⟨quoteHead, quoteTail, hquote⟩
  rcases exists_reverse_append_singleton_of_cons quoteHead quoteTail with
    ⟨scanRev, current, hscan⟩
  rw [selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryTape,
    selectedProjectionInputQuoterAfterSourceRestLeftBoundaryTape,
    hsource, hquote, hscan]
  exact
    scanLeftToBlankLeftDescription_haltsFrom_scanRightToBlankLeftHaltTape
      (List.append (((head :: next :: right).reverse).map some)
        (assemblySourceRestBoundaryLeftRev L.input L.stage))
      scanRev current

private theorem selectedProjectionInputQuoterAfterSourceRestLeftBoundaryTape_move_left_move_right
    (L : DovetailLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (selectedProjectionInputQuoterAfterSourceRestLeftBoundaryTape L)) =
      selectedProjectionInputQuoterAfterSourceRestLeftBoundaryTape L := by
  rw [selectedProjectionInputQuoterAfterSourceRestLeftBoundaryTape]
  exact
    scanLeftToBlankLeftHaltTape_move_left_move_right_none_right
      (List.append
        ((SelectedProjectionTailProjector.sourceRestFieldBits L).reverse.map
          some)
        (assemblySourceRestBoundaryLeftRev L.input L.stage))
      (preservingCellPassCellBits
        (SelectedProjectionTailProjector.sourceRestFieldBits L))
      []

def SelectedProjectionInputQuoterAfterSourceRestQuoteBoundarySpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall L : DovetailLayout,
      finish.HaltsFromTapeEquiv
        (selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryTape L)
        (selectedProjectionInputQuoterRawCellQuoteTargetTape L)

def SelectedProjectionInputQuoterAfterSourceRestQuoteBoundaryConstruction :
    Prop :=
  exists finish : MachineDescription,
    SelectedProjectionInputQuoterAfterSourceRestQuoteBoundarySpec finish

def SelectedProjectionInputQuoterAfterSourceRestLeftBoundarySpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall L : DovetailLayout,
      finish.HaltsFromTapeEquiv
        (selectedProjectionInputQuoterAfterSourceRestLeftBoundaryTape L)
        (selectedProjectionInputQuoterRawCellQuoteTargetTape L)

def SelectedProjectionInputQuoterAfterSourceRestLeftBoundaryConstruction :
    Prop :=
  exists finish : MachineDescription,
    SelectedProjectionInputQuoterAfterSourceRestLeftBoundarySpec finish

theorem selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryConstruction_of_leftBoundary
    (h : SelectedProjectionInputQuoterAfterSourceRestLeftBoundaryConstruction) :
    SelectedProjectionInputQuoterAfterSourceRestQuoteBoundaryConstruction := by
  rcases h with ⟨finish, hfinish⟩
  refine
    ⟨SeqViaCanonical scanLeftToBlankLeftDescription finish, ?_⟩
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        scanLeftToBlankLeftDescription_subroutineReady
        hfinish.left
  · intro L
    exact
      SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
        scanLeftToBlankLeftDescription_subroutineReady
        hfinish.left
        (scanLeftToBlankLeftDescription_haltsFrom_afterSourceRestQuoteBoundaryTape
          L).toEquiv
        (by
          rw [selectedProjectionInputQuoterAfterSourceRestLeftBoundaryTape_move_left_move_right]
          exact Tape.Equiv.refl _)
        (hfinish.right L)

theorem selectedProjectionInputQuoterAfterSourceRestPassConstruction_of_quoteBoundary
    (h : SelectedProjectionInputQuoterAfterSourceRestQuoteBoundaryConstruction) :
    SelectedProjectionInputQuoterAfterSourceRestPassConstruction := by
  rcases h with ⟨finish, hfinish⟩
  refine
    ⟨SeqViaCanonical scanRightToBlankLeftDescription finish, ?_⟩
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        scanRightToBlankLeftDescription_subroutineReady
        hfinish.left
  · intro L
    exact
      SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
        scanRightToBlankLeftDescription_subroutineReady
        hfinish.left
        (scanRightToBlankLeftDescription_haltsFrom_afterSourceRestPassTape
          L).toEquiv
        (by
          rw [selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryTape_move_left_move_right]
          exact Tape.Equiv.refl _)
        (hfinish.right L)

theorem selectedProjectionInputQuoterAfterSourceRestPassConstruction :
    SelectedProjectionInputQuoterAfterSourceRestPassConstruction := by
  rcases selectedProjectionInputQuoterAfterSourceRestShapeConstruction with
    ⟨finish, hfinish⟩
  refine ⟨finish, hfinish.left, ?_⟩
  intro L
  simpa [selectedProjectionInputQuoterAfterSourceRestPassTape_eq_tapeAtCells,
    selectedProjectionInputQuoterRawCellQuoteTargetTape_eq_shapeTape] using
    hfinish.right L

def SelectedProjectionInputQuoterRawCellQuoteSpec
    (raw : MachineDescription) : Prop :=
  raw.SubroutineReady ∧
    forall L : DovetailLayout,
      raw.HaltsFromTapeEquiv
        (selectedProjectionInputQuoterPostBoundarySourceTape L)
        (selectedProjectionInputQuoterRawCellQuoteTargetTape L)

def SelectedProjectionInputQuoterRawCellQuoteConstruction : Prop :=
  exists raw : MachineDescription,
    SelectedProjectionInputQuoterRawCellQuoteSpec raw

/--
Raw-cell quote/preserve finite-table leaf for the exact input quoter.  At the
source-rest boundary the parsed-layout prefix is split across the defaulted
left context and the remaining source-rest bits under the head.  This machine
must quote that whole defaulted parsed-layout word while preserving the exact
stage/source field expected by the selected-projection tail emitter.
-/
theorem selectedProjectionInputQuoterRawCellQuoteConstruction :
    SelectedProjectionInputQuoterRawCellQuoteConstruction := by
  rcases selectedProjectionInputQuoterAfterSourceRestPassConstruction with
    ⟨finish, hfinish⟩
  refine
    ⟨SeqViaCanonical PreservingCellPassDescription finish, ?_⟩
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        preservingCellPassDescription_subroutineReady
        hfinish.left
  · intro L
    exact
      SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
        preservingCellPassDescription_subroutineReady
        hfinish.left
        (preservingCellPassDescription_haltsFrom_postBoundarySourceTape L).toEquiv
        (Tape.Equiv.refl _)
        (hfinish.right L)

/--
The remaining post-boundary finite-table obligation for the exact input
quoter.  The prefix phase has already restored the source-rest boundary; this
phase must quote the defaulted parsed-layout bits and leave the exact source
field under the head.
-/
theorem selectedProjectionInputQuoterPostBoundaryConstruction :
    SelectedProjectionInputQuoterPostBoundaryConstruction := by
  rcases selectedProjectionInputQuoterRawCellQuoteConstruction with
    ⟨raw, hraw⟩
  refine ⟨raw, hraw.left, ?_⟩
  intro L
  rw [selectedProjectionInputQuoterExactTargetTape_eq_rawCellQuoteTargetTape]
  exact hraw.right L

theorem assemblySkeletonDescription_run_nonempty_stageInput_to_sourceRest_boundary_cells
    (b : Bool) (rest : Word Bool) (stage : Nat)
    (sourceRestCells : List (Option Bool)) :
    exists steps : Nat,
      AssemblySkeletonDescription.runConfig steps
          (config AssemblySkeletonDescription.start []
            (List.append
              (List.map some
                (List.append
                  (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                  (DovetailInitialLayoutInitializer.stageInputBits
                    (b :: rest) stage)))
              sourceRestCells)) =
        config 210
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage).reverse.map some)
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
                (b :: rest)).reverse.map some)
              (List.append [none, some false] transitionPrefixLeftTail)))
          sourceRestCells := by
  exact
    assemblySkeletonDescription_run_nonempty_stageInput_to_sourceRest_boundary_cells_aux
      b rest stage sourceRestCells

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
