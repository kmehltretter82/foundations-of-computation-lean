import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Quoter.RawCells

set_option doc.verso true

/-!
# Raw-cell quote output contracts

The exact raw-cell quoter construction still targets a fully positioned tape.
This module records the parallel normalized-output surface.  It lets later
projection routes use the source-rest finish output construction without
depending on the exact live-tail joiner endpoint.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

open DovetailInitialLayoutInitializer

/-! ## Output word and target tape views -/

def selectedProjectionInputQuoterRawCellQuoteOutput
    (L : DovetailLayout) : Word Bool :=
  List.append
    (SelectedProjectionTailProjector.outputPrefixStageInputSourceRestFieldBits
      L)
    (SelectedProjectionTailProjector.sourceFieldBits L)

theorem selectedProjectionInputQuoterRawCellQuoteOutput_eq_fields
    (L : DovetailLayout) :
    selectedProjectionInputQuoterRawCellQuoteOutput L =
      List.append
        (SelectedProjectionTailProjector.outputPrefixStageInputSourceRestFieldBits
          L)
        (SelectedProjectionTailProjector.sourceFieldBits L) := by
  rfl

theorem assemblySourceRestFinishTargetPrefixBits_selected_eq_outputPrefix
    (L : DovetailLayout) :
    assemblySourceRestFinishTargetPrefixBits L.input
        (SelectedProjectionTailProjector.sourceRestFieldBits L) L.stage =
      SelectedProjectionTailProjector.outputPrefixStageInputSourceRestFieldBits
        L := by
  simpa [assemblySourceRestFinishTargetPrefixBits,
    assemblySourceRestFinishSourceBits] using
    preservingCellPassHeaderQuoteBits_eq_outputPrefixStageInputSourceRestFieldBits
      L

theorem assemblySourceRestFinishSourceBits_selected_eq_parsedLayoutBits
    (L : DovetailLayout) :
    assemblySourceRestFinishSourceBits L.input
        (SelectedProjectionTailProjector.sourceRestFieldBits L) L.stage =
      ParsedLayoutBits L := by
  rw [assemblySourceRestFinishSourceBits_eq]
  exact
    (SelectedProjectionTailProjector.parsedLayoutBits_eq_transition_stageInput_sourceRestFieldBits
      L).symm

theorem assemblySourceRestFinishSourceTape_selected_eq_afterSourceRestShapeTape
    (L : DovetailLayout) :
    assemblySourceRestFinishSourceTape L.input
        (SelectedProjectionTailProjector.sourceRestFieldBits L) L.stage =
      selectedProjectionInputQuoterAfterSourceRestSourceShapeTape L := by
  rfl

theorem assemblySourceRestFinishOutput_selected_eq_rawCellQuoteOutput
    (L : DovetailLayout) :
    assemblySourceRestFinishOutput L.input
        (SelectedProjectionTailProjector.sourceRestFieldBits L) L.stage =
      selectedProjectionInputQuoterRawCellQuoteOutput L := by
  rw [assemblySourceRestFinishOutput_eq_targetTape_namedOutput,
    selectedProjectionInputQuoterRawCellQuoteOutput]
  rw [assemblySourceRestFinishTargetPrefixBits_selected_eq_outputPrefix]
  rw [SelectedProjectionTailProjector.sourceFieldBits_eq_stageNatBits_sourceRestFieldBits]

theorem selectedProjectionInputQuoterRawCellQuoteTargetTape_eq_shapeTape_output
    (L : DovetailLayout) :
    selectedProjectionInputQuoterRawCellQuoteTargetTape L =
      selectedProjectionInputQuoterRawCellQuoteTargetShapeTape L := by
  rw [selectedProjectionInputQuoterRawCellQuoteTargetTape,
    selectedProjectionInputQuoterRawCellQuoteTargetShapeTape]
  rw [SelectedProjectionTailProjector.sourceFieldBits_eq_stageNatBits_sourceRestFieldBits]
  congr 1
  rw [SelectedProjectionTailProjector.outputPrefixStageInputSourceRestFieldBits]
  rw [SelectedProjectionTailProjector.parsedLayoutBits_eq_transition_stageInput_sourceRestFieldBits]
  rw [← preservingCellPassQuoteBits_eq_encodeBoolWordAppend]

theorem selectedProjectionInputQuoterRawCellQuoteTargetShapeTape_cells
    (L : DovetailLayout) :
    Tape.cells (selectedProjectionInputQuoterRawCellQuoteTargetShapeTape L) =
      List.append
        ((SelectedProjectionTailProjector.outputPrefixStageInputSourceRestFieldBits
          L).map some)
        ((SelectedProjectionTailProjector.sourceFieldBits L).map some) := by
  rw [selectedProjectionInputQuoterRawCellQuoteTargetShapeTape]
  rcases SelectedProjectionTailProjector.stageNatBits_cons_cons L.stage with
    ⟨head, next, right, hstage⟩
  rw [SelectedProjectionTailProjector.sourceFieldBits_eq_stageNatBits_sourceRestFieldBits,
    hstage]
  simp [tapeAtCells, Tape.cells, List.map_append]

theorem selectedProjectionInputQuoterRawCellQuoteTargetShapeTape_normalizedOutput
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedProjectionInputQuoterRawCellQuoteTargetShapeTape L) =
      selectedProjectionInputQuoterRawCellQuoteOutput L := by
  rw [Tape.normalizedOutput]
  rw [selectedProjectionInputQuoterRawCellQuoteTargetShapeTape_cells]
  simp [selectedProjectionInputQuoterRawCellQuoteOutput, Function.comp_def]

theorem selectedProjectionInputQuoterRawCellQuoteTargetTape_normalizedOutput_output
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedProjectionInputQuoterRawCellQuoteTargetTape L) =
      selectedProjectionInputQuoterRawCellQuoteOutput L := by
  rw [selectedProjectionInputQuoterRawCellQuoteTargetTape_eq_shapeTape_output]
  exact selectedProjectionInputQuoterRawCellQuoteTargetShapeTape_normalizedOutput
    L

theorem selectedProjectionInputQuoterExactTargetTape_normalizedOutput_output
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (SelectedProjectionInputQuoterExactTargetTape L) =
      selectedProjectionInputQuoterRawCellQuoteOutput L := by
  rw [← sourceTape_outputPrefix_eq_inputQuoterExactTargetTape]
  rw [SelectedProjectionTailProjector.sourceTape_normalizedOutput_outputPrefix]
  rw [selectedProjectionInputQuoterRawCellQuoteOutput]
  rw [SelectedProjectionTailProjector.outputPrefixBits_eq_stageInputSourceRestFieldBits]

/-! ## Source-rest pass tape shape -/

theorem sourceRestFieldBits_cons_cons_output
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

theorem selectedProjectionInputQuoterAfterSourceRestPassTape_eq_haltTape_output
    (L : DovetailLayout) :
    selectedProjectionInputQuoterAfterSourceRestPassTape L =
      preservingCellPassHaltTape
        (assemblySourceRestBoundaryLeftRev L.input L.stage)
        (SelectedProjectionTailProjector.sourceRestFieldBits L) [] := by
  rw [selectedProjectionInputQuoterAfterSourceRestPassTape]
  rcases sourceRestFieldBits_cons_cons_output L with
    ⟨head, next, right, hsource⟩
  rw [hsource]
  rcases preservingCellPassHaltTape_right_cons_of_nonempty
      (assemblySourceRestBoundaryLeftRev L.input L.stage)
      head (next :: right) with
    ⟨cell, tail, hright⟩
  exact Tape.move_left_move_right_eq_self_of_right_cons _ hright

theorem selectedProjectionInputQuoterAfterSourceRestPassTape_eq_sourceShapeTape_output
    (L : DovetailLayout) :
    selectedProjectionInputQuoterAfterSourceRestPassTape L =
      selectedProjectionInputQuoterAfterSourceRestSourceShapeTape L := by
  rw [selectedProjectionInputQuoterAfterSourceRestPassTape_eq_haltTape_output]
  rw [selectedProjectionInputQuoterAfterSourceRestSourceShapeTape]
  rcases sourceRestFieldBits_cons_cons_output L with
    ⟨head, next, right, hsource⟩
  rw [hsource]
  exact
    preservingCellPassHaltTape_nonempty_empty_output_eq_tapeAtCells
      (assemblySourceRestBoundaryLeftRev L.input L.stage)
      head (next :: right)

theorem selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryTape_move_left_move_right_output
    (L : DovetailLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryTape L)) =
      selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryTape L := by
  rcases sourceRestFieldBits_cons_cons_output L with
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

theorem selectedProjectionInputQuoterAfterSourceRestLeftBoundaryTape_move_left_move_right_output
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

/-! ## Output specs -/

def SelectedProjectionInputQuoterAfterSourceRestShapeOutputSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall L : DovetailLayout,
      finish.HaltsFromTapeWithOutput
        (selectedProjectionInputQuoterAfterSourceRestSourceShapeTape L)
        (selectedProjectionInputQuoterRawCellQuoteOutput L)

def SelectedProjectionInputQuoterAfterSourceRestShapeOutputConstruction :
    Prop :=
  exists finish : MachineDescription,
    SelectedProjectionInputQuoterAfterSourceRestShapeOutputSpec finish

def SelectedProjectionInputQuoterAfterSourceRestPassOutputSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall L : DovetailLayout,
      finish.HaltsFromTapeWithOutput
        (selectedProjectionInputQuoterAfterSourceRestPassTape L)
        (selectedProjectionInputQuoterRawCellQuoteOutput L)

def SelectedProjectionInputQuoterAfterSourceRestPassOutputConstruction :
    Prop :=
  exists finish : MachineDescription,
    SelectedProjectionInputQuoterAfterSourceRestPassOutputSpec finish

def SelectedProjectionInputQuoterAfterSourceRestQuoteBoundaryOutputSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall L : DovetailLayout,
      finish.HaltsFromTapeWithOutput
        (selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryTape L)
        (selectedProjectionInputQuoterRawCellQuoteOutput L)

def SelectedProjectionInputQuoterAfterSourceRestQuoteBoundaryOutputConstruction :
    Prop :=
  exists finish : MachineDescription,
    SelectedProjectionInputQuoterAfterSourceRestQuoteBoundaryOutputSpec finish

def SelectedProjectionInputQuoterAfterSourceRestLeftBoundaryOutputSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall L : DovetailLayout,
      finish.HaltsFromTapeWithOutput
        (selectedProjectionInputQuoterAfterSourceRestLeftBoundaryTape L)
        (selectedProjectionInputQuoterRawCellQuoteOutput L)

def SelectedProjectionInputQuoterAfterSourceRestLeftBoundaryOutputConstruction :
    Prop :=
  exists finish : MachineDescription,
    SelectedProjectionInputQuoterAfterSourceRestLeftBoundaryOutputSpec finish

def SelectedProjectionInputQuoterRawCellQuoteOutputSpec
    (raw : MachineDescription) : Prop :=
  raw.SubroutineReady ∧
    forall L : DovetailLayout,
      raw.HaltsFromTapeWithOutput
        (selectedProjectionInputQuoterPostBoundarySourceTape L)
        (selectedProjectionInputQuoterRawCellQuoteOutput L)

def SelectedProjectionInputQuoterRawCellQuoteOutputConstruction :
    Prop :=
  exists raw : MachineDescription,
    SelectedProjectionInputQuoterRawCellQuoteOutputSpec raw

def SelectedProjectionInputQuoterPostBoundaryOutputSpec
    (raw : MachineDescription) : Prop :=
  raw.SubroutineReady ∧
    forall L : DovetailLayout,
      raw.HaltsFromTapeWithOutput
        (selectedProjectionInputQuoterPostBoundarySourceTape L)
        (selectedProjectionInputQuoterRawCellQuoteOutput L)

def SelectedProjectionInputQuoterPostBoundaryOutputConstruction :
    Prop :=
  exists raw : MachineDescription,
    SelectedProjectionInputQuoterPostBoundaryOutputSpec raw

/-! ## Spec accessors -/

theorem SelectedProjectionInputQuoterAfterSourceRestShapeOutputSpec.subroutineReady
    {finish : MachineDescription}
    (hfinish :
      SelectedProjectionInputQuoterAfterSourceRestShapeOutputSpec finish) :
    finish.SubroutineReady :=
  hfinish.left

theorem SelectedProjectionInputQuoterAfterSourceRestShapeOutputSpec.haltsFromTapeWithOutput
    {finish : MachineDescription}
    (hfinish :
      SelectedProjectionInputQuoterAfterSourceRestShapeOutputSpec finish)
    (L : DovetailLayout) :
    finish.HaltsFromTapeWithOutput
      (selectedProjectionInputQuoterAfterSourceRestSourceShapeTape L)
      (selectedProjectionInputQuoterRawCellQuoteOutput L) :=
  hfinish.right L

theorem SelectedProjectionInputQuoterAfterSourceRestPassOutputSpec.subroutineReady
    {finish : MachineDescription}
    (hfinish :
      SelectedProjectionInputQuoterAfterSourceRestPassOutputSpec finish) :
    finish.SubroutineReady :=
  hfinish.left

theorem SelectedProjectionInputQuoterAfterSourceRestPassOutputSpec.haltsFromTapeWithOutput
    {finish : MachineDescription}
    (hfinish :
      SelectedProjectionInputQuoterAfterSourceRestPassOutputSpec finish)
    (L : DovetailLayout) :
    finish.HaltsFromTapeWithOutput
      (selectedProjectionInputQuoterAfterSourceRestPassTape L)
      (selectedProjectionInputQuoterRawCellQuoteOutput L) :=
  hfinish.right L

theorem SelectedProjectionInputQuoterAfterSourceRestQuoteBoundaryOutputSpec.subroutineReady
    {finish : MachineDescription}
    (hfinish :
      SelectedProjectionInputQuoterAfterSourceRestQuoteBoundaryOutputSpec
        finish) :
    finish.SubroutineReady :=
  hfinish.left

theorem SelectedProjectionInputQuoterAfterSourceRestQuoteBoundaryOutputSpec.haltsFromTapeWithOutput
    {finish : MachineDescription}
    (hfinish :
      SelectedProjectionInputQuoterAfterSourceRestQuoteBoundaryOutputSpec
        finish)
    (L : DovetailLayout) :
    finish.HaltsFromTapeWithOutput
      (selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryTape L)
      (selectedProjectionInputQuoterRawCellQuoteOutput L) :=
  hfinish.right L

theorem SelectedProjectionInputQuoterAfterSourceRestLeftBoundaryOutputSpec.subroutineReady
    {finish : MachineDescription}
    (hfinish :
      SelectedProjectionInputQuoterAfterSourceRestLeftBoundaryOutputSpec
        finish) :
    finish.SubroutineReady :=
  hfinish.left

theorem SelectedProjectionInputQuoterAfterSourceRestLeftBoundaryOutputSpec.haltsFromTapeWithOutput
    {finish : MachineDescription}
    (hfinish :
      SelectedProjectionInputQuoterAfterSourceRestLeftBoundaryOutputSpec
        finish)
    (L : DovetailLayout) :
    finish.HaltsFromTapeWithOutput
      (selectedProjectionInputQuoterAfterSourceRestLeftBoundaryTape L)
      (selectedProjectionInputQuoterRawCellQuoteOutput L) :=
  hfinish.right L

theorem SelectedProjectionInputQuoterRawCellQuoteOutputSpec.subroutineReady
    {raw : MachineDescription}
    (hraw : SelectedProjectionInputQuoterRawCellQuoteOutputSpec raw) :
    raw.SubroutineReady :=
  hraw.left

theorem SelectedProjectionInputQuoterRawCellQuoteOutputSpec.haltsFromTapeWithOutput
    {raw : MachineDescription}
    (hraw : SelectedProjectionInputQuoterRawCellQuoteOutputSpec raw)
    (L : DovetailLayout) :
    raw.HaltsFromTapeWithOutput
      (selectedProjectionInputQuoterPostBoundarySourceTape L)
      (selectedProjectionInputQuoterRawCellQuoteOutput L) :=
  hraw.right L

theorem SelectedProjectionInputQuoterPostBoundaryOutputSpec.subroutineReady
    {raw : MachineDescription}
    (hraw : SelectedProjectionInputQuoterPostBoundaryOutputSpec raw) :
    raw.SubroutineReady :=
  hraw.left

theorem SelectedProjectionInputQuoterPostBoundaryOutputSpec.haltsFromTapeWithOutput
    {raw : MachineDescription}
    (hraw : SelectedProjectionInputQuoterPostBoundaryOutputSpec raw)
    (L : DovetailLayout) :
    raw.HaltsFromTapeWithOutput
      (selectedProjectionInputQuoterPostBoundarySourceTape L)
      (selectedProjectionInputQuoterRawCellQuoteOutput L) :=
  hraw.right L

/-! ## Exact-to-output adapters -/

private theorem haltsFromTapeWithOutput_of_haltsFromTape_target
    {D : MachineDescription} {Tin Tout : Tape Bool}
    (h : D.HaltsFromTape Tin Tout) :
    D.HaltsFromTapeWithOutput Tin (Tape.normalizedOutput Tout) :=
  MachineDescription.haltsFromTapeWithOutput_of_haltsFromTape h

theorem SelectedProjectionInputQuoterAfterSourceRestShapeSpec.toOutputSpec
    {finish : MachineDescription}
    (hfinish : SelectedProjectionInputQuoterAfterSourceRestShapeSpec finish) :
    SelectedProjectionInputQuoterAfterSourceRestShapeOutputSpec finish := by
  constructor
  · exact hfinish.left
  · intro L
    simpa [selectedProjectionInputQuoterRawCellQuoteTargetShapeTape_normalizedOutput
      L] using
      haltsFromTapeWithOutput_of_haltsFromTape_target
        (hfinish.right L)

theorem SelectedProjectionInputQuoterAfterSourceRestPassSpec.toOutputSpec
    {finish : MachineDescription}
    (hfinish : SelectedProjectionInputQuoterAfterSourceRestPassSpec finish) :
    SelectedProjectionInputQuoterAfterSourceRestPassOutputSpec finish := by
  constructor
  · exact hfinish.left
  · intro L
    simpa [selectedProjectionInputQuoterRawCellQuoteTargetTape_normalizedOutput_output
      L] using
      haltsFromTapeWithOutput_of_haltsFromTape_target
        (hfinish.right L)

theorem SelectedProjectionInputQuoterAfterSourceRestQuoteBoundarySpec.toOutputSpec
    {finish : MachineDescription}
    (hfinish :
      SelectedProjectionInputQuoterAfterSourceRestQuoteBoundarySpec finish) :
    SelectedProjectionInputQuoterAfterSourceRestQuoteBoundaryOutputSpec
      finish := by
  constructor
  · exact hfinish.left
  · intro L
    simpa [selectedProjectionInputQuoterRawCellQuoteTargetTape_normalizedOutput_output
      L] using
      haltsFromTapeWithOutput_of_haltsFromTape_target
        (hfinish.right L)

theorem SelectedProjectionInputQuoterAfterSourceRestLeftBoundarySpec.toOutputSpec
    {finish : MachineDescription}
    (hfinish :
      SelectedProjectionInputQuoterAfterSourceRestLeftBoundarySpec finish) :
    SelectedProjectionInputQuoterAfterSourceRestLeftBoundaryOutputSpec
      finish := by
  constructor
  · exact hfinish.left
  · intro L
    simpa [selectedProjectionInputQuoterRawCellQuoteTargetTape_normalizedOutput_output
      L] using
      haltsFromTapeWithOutput_of_haltsFromTape_target
        (hfinish.right L)

theorem SelectedProjectionInputQuoterRawCellQuoteSpec.toOutputSpec
    {raw : MachineDescription}
    (hraw : SelectedProjectionInputQuoterRawCellQuoteSpec raw) :
    SelectedProjectionInputQuoterRawCellQuoteOutputSpec raw := by
  constructor
  · exact hraw.left
  · intro L
    simpa [selectedProjectionInputQuoterRawCellQuoteTargetTape_normalizedOutput_output
      L] using
      haltsFromTapeWithOutput_of_haltsFromTape_target
        (hraw.right L)

theorem SelectedProjectionInputQuoterPostBoundarySpec.toOutputSpec
    {raw : MachineDescription}
    (hraw : SelectedProjectionInputQuoterPostBoundarySpec raw) :
    SelectedProjectionInputQuoterPostBoundaryOutputSpec raw := by
  constructor
  · exact hraw.left
  · intro L
    simpa [selectedProjectionInputQuoterExactTargetTape_normalizedOutput_output
      L] using
      haltsFromTapeWithOutput_of_haltsFromTape_target
        (hraw.right L)

/-! ## Output construction adapters -/

theorem selectedProjectionInputQuoterAfterSourceRestShapeOutputConstruction :
    SelectedProjectionInputQuoterAfterSourceRestShapeOutputConstruction := by
  rcases assemblySourceRestFinishOutputConstruction_for_assemblySourceRest with
    ⟨finish, hfinish⟩
  refine ⟨finish, hfinish.left, ?_⟩
  intro L
  rw [← assemblySourceRestFinishSourceTape_selected_eq_afterSourceRestShapeTape]
  rw [← assemblySourceRestFinishOutput_selected_eq_rawCellQuoteOutput]
  exact hfinish.right L.input
    (SelectedProjectionTailProjector.sourceRestFieldBits L) L.stage

theorem selectedProjectionInputQuoterAfterSourceRestPassOutputConstruction_of_shape
    (h : SelectedProjectionInputQuoterAfterSourceRestShapeOutputConstruction) :
    SelectedProjectionInputQuoterAfterSourceRestPassOutputConstruction := by
  rcases h with ⟨finish, hfinish⟩
  refine ⟨finish, hfinish.left, ?_⟩
  intro L
  rw [selectedProjectionInputQuoterAfterSourceRestPassTape_eq_sourceShapeTape_output]
  exact hfinish.right L

theorem selectedProjectionInputQuoterAfterSourceRestPassOutputConstruction :
    SelectedProjectionInputQuoterAfterSourceRestPassOutputConstruction :=
  selectedProjectionInputQuoterAfterSourceRestPassOutputConstruction_of_shape
    selectedProjectionInputQuoterAfterSourceRestShapeOutputConstruction

theorem selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryOutputConstruction_of_leftBoundary
    (h :
      SelectedProjectionInputQuoterAfterSourceRestLeftBoundaryOutputConstruction) :
    SelectedProjectionInputQuoterAfterSourceRestQuoteBoundaryOutputConstruction := by
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
      SeqViaCanonical_haltsFromTapeWithOutput_of_haltsFromTape_eq
        scanLeftToBlankLeftDescription_subroutineReady
        hfinish.left
        (scanLeftToBlankLeftDescription_haltsFrom_afterSourceRestQuoteBoundaryTape
          L)
        (selectedProjectionInputQuoterAfterSourceRestLeftBoundaryTape_move_left_move_right_output
          L)
        (hfinish.right L)

theorem selectedProjectionInputQuoterAfterSourceRestPassOutputConstruction_of_quoteBoundary
    (h :
      SelectedProjectionInputQuoterAfterSourceRestQuoteBoundaryOutputConstruction) :
    SelectedProjectionInputQuoterAfterSourceRestPassOutputConstruction := by
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
      SeqViaCanonical_haltsFromTapeWithOutput_of_haltsFromTape_eq
        scanRightToBlankLeftDescription_subroutineReady
        hfinish.left
        (scanRightToBlankLeftDescription_haltsFrom_afterSourceRestPassTape
          L)
        (selectedProjectionInputQuoterAfterSourceRestQuoteBoundaryTape_move_left_move_right_output
          L)
        (hfinish.right L)

theorem selectedProjectionInputQuoterRawCellQuoteOutputConstruction_of_afterSourceRestPass
    (h : SelectedProjectionInputQuoterAfterSourceRestPassOutputConstruction) :
    SelectedProjectionInputQuoterRawCellQuoteOutputConstruction := by
  rcases h with ⟨finish, hfinish⟩
  refine
    ⟨SeqViaCanonical PreservingCellPassDescription finish, ?_⟩
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        preservingCellPassDescription_subroutineReady
        hfinish.left
  · intro L
    exact
      SeqViaCanonical_haltsFromTapeWithOutput_of_haltsFromTape_eq
        preservingCellPassDescription_subroutineReady
        hfinish.left
        (preservingCellPassDescription_haltsFrom_postBoundarySourceTape L)
        (by rfl)
        (hfinish.right L)

theorem selectedProjectionInputQuoterRawCellQuoteOutputConstruction :
    SelectedProjectionInputQuoterRawCellQuoteOutputConstruction :=
  selectedProjectionInputQuoterRawCellQuoteOutputConstruction_of_afterSourceRestPass
    selectedProjectionInputQuoterAfterSourceRestPassOutputConstruction

theorem selectedProjectionInputQuoterPostBoundaryOutputSpec_of_rawCellQuote
    {raw : MachineDescription}
    (hraw : SelectedProjectionInputQuoterRawCellQuoteOutputSpec raw) :
    SelectedProjectionInputQuoterPostBoundaryOutputSpec raw := by
  exact hraw

theorem selectedProjectionInputQuoterPostBoundaryOutputConstruction_of_rawCellQuote
    (h : SelectedProjectionInputQuoterRawCellQuoteOutputConstruction) :
    SelectedProjectionInputQuoterPostBoundaryOutputConstruction := by
  rcases h with ⟨raw, hraw⟩
  exact ⟨raw, selectedProjectionInputQuoterPostBoundaryOutputSpec_of_rawCellQuote hraw⟩

theorem selectedProjectionInputQuoterPostBoundaryOutputConstruction :
    SelectedProjectionInputQuoterPostBoundaryOutputConstruction :=
  selectedProjectionInputQuoterPostBoundaryOutputConstruction_of_rawCellQuote
    selectedProjectionInputQuoterRawCellQuoteOutputConstruction

theorem selectedProjectionInputQuoterPostBoundaryOutputConstruction_of_exact
    (h : SelectedProjectionInputQuoterPostBoundaryConstruction) :
    SelectedProjectionInputQuoterPostBoundaryOutputConstruction := by
  rcases h with ⟨raw, hraw⟩
  exact ⟨raw, hraw.toOutputSpec⟩

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
