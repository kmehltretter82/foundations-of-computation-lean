import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.Erase

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

def eraseOtherHitFlagDescription
    (useAccept : Bool) : MachineDescription :=
  if useAccept then
    eraseRightBoolFieldAfterCurrentDescription
  else
    eraseLeftBoolFieldBeforeCurrentDescription

theorem eraseOtherHitFlagDescription_subroutineReady
    (useAccept : Bool) :
    (eraseOtherHitFlagDescription useAccept).SubroutineReady := by
  cases useAccept
  · simpa [eraseOtherHitFlagDescription] using
      eraseLeftBoolFieldBeforeCurrentDescription_subroutineReady
  · simpa [eraseOtherHitFlagDescription] using
      eraseRightBoolFieldAfterCurrentDescription_subroutineReady

theorem eraseOtherHitFlagDescription_haltsFrom_selectedHitRightEndTape
    (useAccept : Bool) (L : DovetailLayout) :
    (eraseOtherHitFlagDescription useAccept).HaltsFromTape
      (selectedHitRightEndTape useAccept L)
      (selectedHitOtherFlagErasedTape useAccept L) := by
  cases useAccept
  · refine ⟨8, ?_⟩
    constructor <;>
      by_cases hreject : L.rejectHit <;>
      by_cases haccept : L.acceptHit <;>
        simp [eraseOtherHitFlagDescription,
          selectedHitRightEndTape, selectedHitOtherFlagErasedTape,
          sourceRightEndTape_sourceBits_eq_fields,
          sourceRightEndLeftFields,
          eraseLeftBoolFieldBeforeCurrentDescription,
          hreject, haccept,
          CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
          CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
          CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
          encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
          DovetailInitialLayoutInitializer.tapeAtCells,
          runConfig, stepConfig, lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft]
  · refine ⟨5, ?_⟩
    constructor <;>
      by_cases hreject : L.rejectHit <;>
      by_cases haccept : L.acceptHit <;>
        simp [eraseOtherHitFlagDescription,
          selectedHitRightEndTape, selectedHitOtherFlagErasedTape,
          eraseRightBoolFieldAfterCurrentDescription,
          hreject, haccept,
          CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
          CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
          CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
          encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
          DovetailInitialLayoutInitializer.tapeAtCells,
          runConfig, stepConfig, lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight]

theorem selectedHitRightEndTape_move_left_move_right
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (selectedHitRightEndTape useAccept L)) =
      selectedHitRightEndTape useAccept L := by
  cases useAccept
  · simpa [selectedHitRightEndTape] using
      sourceRightEndTape_move_left_move_right (sourceBits L)
  · by_cases hreject : L.rejectHit
    · by_cases haccept : L.acceptHit
      · simp [selectedHitRightEndTape, hreject, haccept,
          CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
          CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
          CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
          encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
          DovetailInitialLayoutInitializer.tapeAtCells,
          Tape.move, Tape.moveLeft, Tape.moveRight]
      · simp [selectedHitRightEndTape, hreject, haccept,
          CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
          CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
          CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
          encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
          DovetailInitialLayoutInitializer.tapeAtCells,
          Tape.move, Tape.moveLeft, Tape.moveRight]
    · by_cases haccept : L.acceptHit
      · simp [selectedHitRightEndTape, hreject, haccept,
          CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
          CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
          CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
          encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
          DovetailInitialLayoutInitializer.tapeAtCells,
          Tape.move, Tape.moveLeft, Tape.moveRight]
      · simp [selectedHitRightEndTape, hreject, haccept,
          CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
          CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
          CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
          encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
          DovetailInitialLayoutInitializer.tapeAtCells,
          Tape.move, Tape.moveLeft, Tape.moveRight]

def selectedHitFromScannerDescription
    (useAccept : Bool) : MachineDescription :=
  SeqViaCanonical sourceRewindDescription
    (selectedHitFromRewindDescription useAccept)

theorem selectedHitFromScannerDescription_subroutineReady
    (useAccept : Bool) :
    (selectedHitFromScannerDescription useAccept).SubroutineReady :=
  SeqViaCanonical_subroutineReady
    sourceRewindDescription_subroutineReady
    (selectedHitFromRewindDescription_subroutineReady useAccept)

theorem selectedHitFromScannerDescription_haltsFrom_sourceScannerRightHandoffTape
    (useAccept : Bool) (L : DovetailLayout) :
    (selectedHitFromScannerDescription useAccept).HaltsFromTape
      (SelectedProjectionTailProjector.sourceScannerRightHandoffTape L
        ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
          some))
      (selectedHitRightEndTape useAccept L) :=
  SeqViaCanonical_haltsFromTape_of_haltsFromTape
    sourceRewindDescription_subroutineReady
    (selectedHitFromRewindDescription_subroutineReady useAccept)
    (sourceRewindDescription_haltsFrom_sourceScannerRightHandoffTape L)
    (rewindTargetTape_sourceBits_move_left_move_right L)
    (selectedHitFromRewindDescription_haltsFrom_rewindTarget_sourceBits
      useAccept L)

def selectedHitOtherFlagErasedFromScannerDescription
    (useAccept : Bool) : MachineDescription :=
  SeqViaCanonical (selectedHitFromScannerDescription useAccept)
    (eraseOtherHitFlagDescription useAccept)

theorem selectedHitOtherFlagErasedFromScannerDescription_subroutineReady
    (useAccept : Bool) :
    (selectedHitOtherFlagErasedFromScannerDescription useAccept).SubroutineReady :=
  SeqViaCanonical_subroutineReady
    (selectedHitFromScannerDescription_subroutineReady useAccept)
    (eraseOtherHitFlagDescription_subroutineReady useAccept)

theorem selectedHitOtherFlagErasedFromScannerDescription_haltsFrom_sourceScannerRightHandoffTape
    (useAccept : Bool) (L : DovetailLayout) :
    (selectedHitOtherFlagErasedFromScannerDescription useAccept).HaltsFromTape
      (SelectedProjectionTailProjector.sourceScannerRightHandoffTape L
        ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
          some))
      (selectedHitOtherFlagErasedTape useAccept L) :=
  SeqViaCanonical_haltsFromTape_of_haltsFromTape
    (selectedHitFromScannerDescription_subroutineReady useAccept)
    (eraseOtherHitFlagDescription_subroutineReady useAccept)
    (selectedHitFromScannerDescription_haltsFrom_sourceScannerRightHandoffTape
      useAccept L)
    (selectedHitRightEndTape_move_left_move_right useAccept L)
    (eraseOtherHitFlagDescription_haltsFrom_selectedHitRightEndTape
      useAccept L)

def selectedHitOtherFlagErasedRightLeftHandoffTape
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  Tape.move Direction.left
    (Tape.move Direction.right
      (selectedHitOtherFlagErasedTape useAccept L))

theorem selectedHitOtherFlagErasedRightLeftHandoffTape_true_eq_tapeAtCells
    (L : DovetailLayout) :
    selectedHitOtherFlagErasedRightLeftHandoffTape true L =
      DovetailInitialLayoutInitializer.tapeAtCells
        (selectedHitOtherFlagErasedAcceptLeftRev L)
        [none, none] := by
  rw [selectedHitOtherFlagErasedRightLeftHandoffTape,
    selectedHitOtherFlagErasedTape_true_eq_tapeAtCells]
  simp [DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem skipCurrentAndFourBlankPaddingLeftDescription_haltsFrom_acceptHandoff
    (L : DovetailLayout) :
    skipCurrentAndFourBlankPaddingLeftDescription.HaltsFromTape
      (selectedHitOtherFlagErasedRightLeftHandoffTape true L)
      (selectedHitOtherFlagErasedAcceptAfterPaddingTape L) := by
  rw [selectedHitOtherFlagErasedRightLeftHandoffTape_true_eq_tapeAtCells,
    selectedHitOtherFlagErasedAcceptLeftRev_eq_hitHead,
    selectedHitOtherFlagErasedAcceptAfterPaddingTape]
  exact
    skipCurrentAndFourBlankPaddingLeftDescription_haltsFromTape
      (selectedHitOtherFlagErasedAcceptHitHead L.acceptHit)
      (selectedHitOtherFlagErasedAcceptHitRestLeftRev L)
      [none]

theorem selectedHitOtherFlagErasedRightLeftHandoffTape_false_eq_erasedTape
    (L : DovetailLayout) :
    selectedHitOtherFlagErasedRightLeftHandoffTape false L =
      selectedHitOtherFlagErasedTape false L := by
  rw [selectedHitOtherFlagErasedRightLeftHandoffTape,
    selectedHitOtherFlagErasedTape_false_eq_moveLeft_tapeAtCells]
  rw [selectedHitOtherFlagErasedRejectBaseCells]
  rw [tapeAtCells_move_left_right_left_cons_cons]

def selectedHitOtherFlagErasedRejectAfterPaddingTape
    (L : DovetailLayout) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells
    (List.append (List.replicate 4 (none : Option Bool))
      (selectedHitOtherFlagErasedRejectBaseLeftRev L))
    (List.drop 4 (selectedHitOtherFlagErasedRejectBaseCells L))

theorem skipCurrentAndFourBlankPaddingRightDescription_haltsFrom_rejectHandoff_named
    (L : DovetailLayout) :
    skipCurrentAndFourBlankPaddingRightDescription.HaltsFromTape
      (selectedHitOtherFlagErasedRightLeftHandoffTape false L)
      (selectedHitOtherFlagErasedRejectAfterPaddingTape L) := by
  rcases selectedHitOtherFlagErasedRejectBaseLeftRev_cons L with
    ⟨current, left, hleft⟩
  rcases selectedHitOtherFlagErasedRejectBaseCells_eq_hitHead L with
    ⟨hitTail, hcells⟩
  rw [selectedHitOtherFlagErasedRightLeftHandoffTape_false_eq_erasedTape,
    selectedHitOtherFlagErasedTape_false_eq_moveLeft_tapeAtCells,
    selectedHitOtherFlagErasedRejectAfterPaddingTape,
    hleft, hcells]
  simpa [DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.move, Tape.moveLeft, List.append_assoc] using
    skipCurrentAndFourBlankPaddingRightDescription_haltsFromTape
      current false left (List.append (hitTail.map some) [none])

def selectedHitOtherFlagErasedAfterPaddingTape
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  if useAccept then
    selectedHitOtherFlagErasedAcceptAfterPaddingTape L
  else
    selectedHitOtherFlagErasedRejectAfterPaddingTape L

theorem selectedHitOtherFlagErasedAcceptAfterPaddingTape_move_left_move_right
    (L : DovetailLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (selectedHitOtherFlagErasedAcceptAfterPaddingTape L)) =
      selectedHitOtherFlagErasedAcceptAfterPaddingTape L := by
  simpa [selectedHitOtherFlagErasedAcceptAfterPaddingTape] using
    tapeAtCells_move_left_move_right_cons_cons
      (selectedHitOtherFlagErasedAcceptHitRestLeftRev L)
      (some (selectedHitOtherFlagErasedAcceptHitHead L.acceptHit))
      none
      (none :: none :: none :: none :: [none])

theorem selectedHitOtherFlagErasedRejectAfterPaddingTape_move_left_move_right
    (L : DovetailLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (selectedHitOtherFlagErasedRejectAfterPaddingTape L)) =
      selectedHitOtherFlagErasedRejectAfterPaddingTape L := by
  rcases selectedHitOtherFlagErasedRejectBaseCells_eq_hitHead L with
    ⟨hitTail, hcells⟩
  rw [selectedHitOtherFlagErasedRejectAfterPaddingTape, hcells]
  cases hitTail with
  | nil =>
      simpa using
        tapeAtCells_move_left_move_right_cons_cons
          (List.append (List.replicate 4 (none : Option Bool))
            (selectedHitOtherFlagErasedRejectBaseLeftRev L))
          (some false) none []
  | cons bit rest =>
      simpa [List.append_assoc] using
        tapeAtCells_move_left_move_right_cons_cons
          (List.append (List.replicate 4 (none : Option Bool))
            (selectedHitOtherFlagErasedRejectBaseLeftRev L))
          (some false) (some bit)
          (List.append (rest.map some) [none])

theorem selectedHitOtherFlagErasedAfterPaddingTape_move_left_move_right
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (selectedHitOtherFlagErasedAfterPaddingTape useAccept L)) =
      selectedHitOtherFlagErasedAfterPaddingTape useAccept L := by
  cases useAccept
  · simpa [selectedHitOtherFlagErasedAfterPaddingTape] using
      selectedHitOtherFlagErasedRejectAfterPaddingTape_move_left_move_right L
  · simpa [selectedHitOtherFlagErasedAfterPaddingTape] using
      selectedHitOtherFlagErasedAcceptAfterPaddingTape_move_left_move_right L

theorem selectedHitOtherFlagErasedAcceptAfterPaddingTape_cells
    (L : DovetailLayout) :
    Tape.cells (selectedHitOtherFlagErasedAcceptAfterPaddingTape L) =
      List.append [none]
        (List.append
          ((SelectedProjectionTailProjector.outputPrefixBits L).map some)
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              L.stage).map some)
            (List.append
              ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                L.acceptConfig []).map some)
              (List.append
                ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                  L.rejectConfig []).map some)
                (List.append
                  ((CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                    L.acceptHit []).map some)
                  (List.replicate 6 (none : Option Bool))))))) := by
  by_cases haccept : L.acceptHit <;>
    simp [selectedHitOtherFlagErasedAcceptAfterPaddingTape,
      selectedHitOtherFlagErasedAcceptHitRestLeftRev,
      selectedHitOtherFlagErasedAcceptHitHead,
      haccept,
      DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.cells,
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
      encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      List.reverse_append, List.append_assoc]

theorem selectedHitOtherFlagErasedRejectAfterPaddingTape_cells
    (L : DovetailLayout) :
    Tape.cells (selectedHitOtherFlagErasedRejectAfterPaddingTape L) =
      List.append [none]
        (List.append
          ((SelectedProjectionTailProjector.outputPrefixBits L).map some)
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              L.stage).map some)
            (List.append
              ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                L.acceptConfig []).map some)
              (List.append
                ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                  L.rejectConfig []).map some)
                (List.append
                  (List.replicate 4 (none : Option Bool))
                  (List.append
                    ((CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                      L.rejectHit []).map some)
                    [none])))))) := by
  by_cases hreject : L.rejectHit <;>
    simp [selectedHitOtherFlagErasedRejectAfterPaddingTape,
      selectedHitOtherFlagErasedRejectBaseLeftRev,
      selectedHitOtherFlagErasedRejectBaseCells,
      hreject,
      DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.cells,
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
      encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      List.drop, List.reverse_append, List.map_reverse,
      List.append_assoc]

theorem selectedHitOtherFlagErasedAcceptAfterPaddingTape_cells_eq_branchFields
    (L : DovetailLayout) :
    Tape.cells (selectedHitOtherFlagErasedAfterPaddingTape true L) =
      List.append [none]
        (List.append
          ((selectedProjectionPaddedTailCleanupPrefixBits L).map some)
          (List.append
            ((selectedProjectionPaddedTailCleanupSelectedConfigBits
              true L).map some)
            (List.append
              ((selectedProjectionPaddedTailCleanupUnselectedConfigBits
                true L).map some)
              (List.append
                ((selectedProjectionPaddedTailCleanupSelectedHitBits
                  true L).map some)
                (List.replicate 6 (none : Option Bool)))))) := by
  simpa [selectedHitOtherFlagErasedAfterPaddingTape,
    selectedProjectionPaddedTailCleanupPrefixBits,
    selectedProjectionPaddedTailCleanupSelectedConfigBits,
    selectedProjectionPaddedTailCleanupUnselectedConfigBits,
    selectedProjectionPaddedTailCleanupSelectedHitBits,
    List.map_append, List.append_assoc] using
    selectedHitOtherFlagErasedAcceptAfterPaddingTape_cells L

theorem selectedHitOtherFlagErasedRejectAfterPaddingTape_cells_eq_branchFields
    (L : DovetailLayout) :
    Tape.cells (selectedHitOtherFlagErasedAfterPaddingTape false L) =
      List.append [none]
        (List.append
          ((selectedProjectionPaddedTailCleanupPrefixBits L).map some)
          (List.append
            ((selectedProjectionPaddedTailCleanupUnselectedConfigBits
              false L).map some)
            (List.append
              ((selectedProjectionPaddedTailCleanupSelectedConfigBits
                false L).map some)
              (List.append
                (List.replicate 4 (none : Option Bool))
                (List.append
                  ((selectedProjectionPaddedTailCleanupSelectedHitBits
                    false L).map some)
                  [none]))))) := by
  simpa [selectedHitOtherFlagErasedAfterPaddingTape,
    selectedProjectionPaddedTailCleanupPrefixBits,
    selectedProjectionPaddedTailCleanupSelectedConfigBits,
    selectedProjectionPaddedTailCleanupUnselectedConfigBits,
    selectedProjectionPaddedTailCleanupSelectedHitBits,
    List.map_append, List.append_assoc] using
    selectedHitOtherFlagErasedRejectAfterPaddingTape_cells L

theorem selectedHitOtherFlagErasedAfterPaddingTape_cells_eq_branchFields
    (useAccept : Bool) (L : DovetailLayout) :
    if useAccept then
      Tape.cells (selectedHitOtherFlagErasedAfterPaddingTape useAccept L) =
        List.append [none]
          (List.append
            ((selectedProjectionPaddedTailCleanupPrefixBits L).map some)
            (List.append
              ((selectedProjectionPaddedTailCleanupSelectedConfigBits
                useAccept L).map some)
              (List.append
                ((selectedProjectionPaddedTailCleanupUnselectedConfigBits
                  useAccept L).map some)
                (List.append
                  ((selectedProjectionPaddedTailCleanupSelectedHitBits
                    useAccept L).map some)
                  (List.replicate 6 (none : Option Bool))))))
    else
      Tape.cells (selectedHitOtherFlagErasedAfterPaddingTape useAccept L) =
        List.append [none]
          (List.append
            ((selectedProjectionPaddedTailCleanupPrefixBits L).map some)
            (List.append
              ((selectedProjectionPaddedTailCleanupUnselectedConfigBits
                useAccept L).map some)
              (List.append
                ((selectedProjectionPaddedTailCleanupSelectedConfigBits
                  useAccept L).map some)
                (List.append
                  (List.replicate 4 (none : Option Bool))
                  (List.append
                    ((selectedProjectionPaddedTailCleanupSelectedHitBits
                      useAccept L).map some)
                    [none]))))) := by
  cases useAccept
  · exact selectedHitOtherFlagErasedRejectAfterPaddingTape_cells_eq_branchFields
      L
  · exact selectedHitOtherFlagErasedAcceptAfterPaddingTape_cells_eq_branchFields
      L

theorem selectedHitOtherFlagErasedAcceptAfterPaddingTape_cells_eq_sourceFields
    (L : DovetailLayout) :
    Tape.cells (selectedHitOtherFlagErasedAfterPaddingTape true L) =
      List.append [none]
        (List.append
          ((List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
            (List.append
              (selectedProjectionPaddedTailCleanupSelectedConfigBits true L)
              (List.append
                (selectedProjectionPaddedTailCleanupUnselectedConfigBits true L)
                (selectedProjectionPaddedTailCleanupSelectedHitBits true L)))).map
            some)
          (List.replicate 6 (none : Option Bool))) := by
  simpa [List.map_append, List.append_assoc] using
    selectedHitOtherFlagErasedAcceptAfterPaddingTape_cells_eq_branchFields L

theorem selectedHitOtherFlagErasedRejectAfterPaddingTape_cells_eq_sourceFields
    (L : DovetailLayout) :
    Tape.cells (selectedHitOtherFlagErasedAfterPaddingTape false L) =
      List.append [none]
        (List.append
          ((List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
            (List.append
              (selectedProjectionPaddedTailCleanupUnselectedConfigBits false L)
              (selectedProjectionPaddedTailCleanupSelectedConfigBits false L))).map
            some)
          (List.append
            (List.replicate 4 (none : Option Bool))
            (List.append
              ((selectedProjectionPaddedTailCleanupSelectedHitBits false L).map
                some)
              [none]))) := by
  simpa [List.map_append, List.append_assoc] using
    selectedHitOtherFlagErasedRejectAfterPaddingTape_cells_eq_branchFields L

theorem selectedHitOtherFlagErasedAcceptAfterPaddingTape_normalizedOutput
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedHitOtherFlagErasedAcceptAfterPaddingTape L) =
      List.append (SelectedProjectionTailProjector.outputPrefixBits L)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage)
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.acceptConfig [])
            (List.append
              (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                L.rejectConfig [])
              (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                L.acceptHit [])))) := by
  rw [Tape.normalizedOutput]
  rw [selectedHitOtherFlagErasedAcceptAfterPaddingTape_cells]
  simp [Function.comp_def, List.filterMap_append]

theorem selectedHitOtherFlagErasedRejectAfterPaddingTape_normalizedOutput
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedHitOtherFlagErasedRejectAfterPaddingTape L) =
      List.append (SelectedProjectionTailProjector.outputPrefixBits L)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage)
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.acceptConfig [])
            (List.append
              (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                L.rejectConfig [])
              (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                L.rejectHit [])))) := by
  rw [Tape.normalizedOutput]
  rw [selectedHitOtherFlagErasedRejectAfterPaddingTape_cells]
  simp [Function.comp_def, List.filterMap_append]

theorem selectedHitOtherFlagErasedAcceptAfterPaddingTape_normalizedOutput_eq_sourceBits
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedHitOtherFlagErasedAcceptAfterPaddingTape L) =
      selectedProjectionPaddedTailCleanupPostPaddingSourceBits true L := by
  rw [selectedHitOtherFlagErasedAcceptAfterPaddingTape_normalizedOutput,
    selectedProjectionPaddedTailCleanupPostPaddingSourceBits_true]
  simp [selectedProjectionPaddedTailCleanupPrefixBits, List.append_assoc]

theorem selectedHitOtherFlagErasedRejectAfterPaddingTape_normalizedOutput_eq_sourceBits
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedHitOtherFlagErasedRejectAfterPaddingTape L) =
      selectedProjectionPaddedTailCleanupPostPaddingSourceBits false L := by
  rw [selectedHitOtherFlagErasedRejectAfterPaddingTape_normalizedOutput,
    selectedProjectionPaddedTailCleanupPostPaddingSourceBits_false]
  simp [selectedProjectionPaddedTailCleanupPrefixBits, List.append_assoc]

theorem selectedHitOtherFlagErasedAfterPaddingTape_normalizedOutput_eq_sourceBits
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedHitOtherFlagErasedAfterPaddingTape useAccept L) =
      selectedProjectionPaddedTailCleanupPostPaddingSourceBits
        useAccept L := by
  cases useAccept
  · simpa [selectedHitOtherFlagErasedAfterPaddingTape] using
      selectedHitOtherFlagErasedRejectAfterPaddingTape_normalizedOutput_eq_sourceBits
        L
  · simpa [selectedHitOtherFlagErasedAfterPaddingTape] using
      selectedHitOtherFlagErasedAcceptAfterPaddingTape_normalizedOutput_eq_sourceBits
        L

theorem selectedHitOtherFlagErasedAfterPaddingTape_normalizedOutput_eq_deleteBlock
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedHitOtherFlagErasedAfterPaddingTape useAccept L) =
      List.append
        (selectedProjectionPaddedTailCleanupKeptPrefixBits useAccept L)
        (List.append
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits
            useAccept L)
          (selectedProjectionPaddedTailCleanupKeptSuffixBits
            useAccept L)) := by
  rw [selectedHitOtherFlagErasedAfterPaddingTape_normalizedOutput_eq_sourceBits,
    selectedProjectionPaddedTailCleanupPostPaddingSourceBits_eq_deleteBlock]

theorem selectedHitOtherFlagErasedAcceptAfterPaddingTape_normalizedOutput_eq_sourceFields
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedHitOtherFlagErasedAfterPaddingTape true L) =
      List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
        (List.append
          (selectedProjectionPaddedTailCleanupSelectedConfigBits true L)
          (List.append
            (selectedProjectionPaddedTailCleanupUnselectedConfigBits true L)
            (selectedProjectionPaddedTailCleanupSelectedHitBits true L))) := by
  rw [selectedHitOtherFlagErasedAfterPaddingTape_normalizedOutput_eq_sourceBits,
    selectedProjectionPaddedTailCleanupPostPaddingSourceBits_true_eq_selected_unselected]

theorem selectedHitOtherFlagErasedRejectAfterPaddingTape_normalizedOutput_eq_sourceFields
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedHitOtherFlagErasedAfterPaddingTape false L) =
      List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
        (List.append
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits false L)
          (List.append
            (selectedProjectionPaddedTailCleanupSelectedConfigBits false L)
            (selectedProjectionPaddedTailCleanupSelectedHitBits false L))) := by
  rw [selectedHitOtherFlagErasedAfterPaddingTape_normalizedOutput_eq_sourceBits,
    selectedProjectionPaddedTailCleanupPostPaddingSourceBits_false_eq_unselected_selected]

theorem selectedHitOtherFlagErasedRightLeftHandoffTape_normalizedOutput
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedHitOtherFlagErasedRightLeftHandoffTape useAccept L) =
      Tape.normalizedOutput (selectedHitOtherFlagErasedTape useAccept L) := by
  rw [selectedHitOtherFlagErasedRightLeftHandoffTape]
  rw [Tape.normalizedOutput_move]
  rw [Tape.normalizedOutput_move]

def selectedHitOtherFlagErasedRightLeftHandoffBits
    (useAccept : Bool) (L : DovetailLayout) : Word Bool :=
  if useAccept then
    List.append (SelectedProjectionTailProjector.outputPrefixBits L)
      (List.append
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          L.stage)
        (List.append
          (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.acceptConfig [])
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.rejectConfig [])
            (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
              L.acceptHit []))))
  else
    List.append (SelectedProjectionTailProjector.outputPrefixBits L)
      (List.append
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          L.stage)
        (List.append
          (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.acceptConfig [])
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.rejectConfig [])
            (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
              L.rejectHit []))))

def selectedProjectionPaddedTailCleanupBothConfigBits
    (L : DovetailLayout) : Word Bool :=
  List.append
    (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
      L.acceptConfig [])
    (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
      L.rejectConfig [])

theorem selectedHitOtherFlagErasedRightLeftHandoffBits_eq_bothConfigs_selectedHit
    (useAccept : Bool) (L : DovetailLayout) :
    selectedHitOtherFlagErasedRightLeftHandoffBits useAccept L =
      List.append (selectedProjectionPaddedTailCleanupPrefixBits L)
        (List.append
          (selectedProjectionPaddedTailCleanupBothConfigBits L)
          (selectedProjectionPaddedTailCleanupSelectedHitBits
            useAccept L)) := by
  cases useAccept <;>
    simp [selectedHitOtherFlagErasedRightLeftHandoffBits,
      selectedProjectionPaddedTailCleanupPrefixBits,
      selectedProjectionPaddedTailCleanupBothConfigBits,
      selectedProjectionPaddedTailCleanupSelectedHitBits,
      List.append_assoc]

theorem selectedHitOtherFlagErasedRightLeftHandoffTape_true_normalizedOutput
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedHitOtherFlagErasedRightLeftHandoffTape true L) =
      List.append (SelectedProjectionTailProjector.outputPrefixBits L)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage)
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.acceptConfig [])
            (List.append
              (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                L.rejectConfig [])
              (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                L.acceptHit [])))) := by
  rw [selectedHitOtherFlagErasedRightLeftHandoffTape_normalizedOutput,
    selectedHitOtherFlagErasedTape_true_normalizedOutput]

theorem selectedHitOtherFlagErasedRightLeftHandoffTape_true_cells
    (L : DovetailLayout) :
    Tape.cells (selectedHitOtherFlagErasedRightLeftHandoffTape true L) =
      List.append [none]
        (List.append
          ((SelectedProjectionTailProjector.outputPrefixBits L).map some)
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              L.stage).map some)
            (List.append
              ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                L.acceptConfig []).map some)
              (List.append
                ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                  L.rejectConfig []).map some)
                (List.append
                  ((CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                    L.acceptHit []).map some)
                  (List.append
                    (List.replicate 4 (none : Option Bool))
                    [none, none])))))) := by
  simp [selectedHitOtherFlagErasedRightLeftHandoffTape,
    selectedHitOtherFlagErasedTape,
    DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.cells, Tape.move, Tape.moveLeft, Tape.moveRight,
    List.reverse_append, List.map_reverse, List.append_assoc]

theorem selectedHitOtherFlagErasedRightLeftHandoffTape_false_normalizedOutput
    (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedHitOtherFlagErasedRightLeftHandoffTape false L) =
      List.append (SelectedProjectionTailProjector.outputPrefixBits L)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage)
          (List.append
            (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
              L.acceptConfig [])
            (List.append
              (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                L.rejectConfig [])
              (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                L.rejectHit [])))) := by
  rw [selectedHitOtherFlagErasedRightLeftHandoffTape_normalizedOutput,
    selectedHitOtherFlagErasedTape_false_normalizedOutput]

theorem selectedHitOtherFlagErasedRightLeftHandoffTape_normalizedOutput_eq_bits
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedHitOtherFlagErasedRightLeftHandoffTape useAccept L) =
      selectedHitOtherFlagErasedRightLeftHandoffBits useAccept L := by
  cases useAccept
  · simpa [selectedHitOtherFlagErasedRightLeftHandoffBits] using
      selectedHitOtherFlagErasedRightLeftHandoffTape_false_normalizedOutput L
  · simpa [selectedHitOtherFlagErasedRightLeftHandoffBits] using
      selectedHitOtherFlagErasedRightLeftHandoffTape_true_normalizedOutput L

theorem selectedHitOtherFlagErasedRightLeftHandoffTape_false_cells
    (L : DovetailLayout) :
    Tape.cells (selectedHitOtherFlagErasedRightLeftHandoffTape false L) =
      List.append [none]
        (List.append
          ((SelectedProjectionTailProjector.outputPrefixBits L).map some)
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              L.stage).map some)
            (List.append
              ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                L.acceptConfig []).map some)
              (List.append
                ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                  L.rejectConfig []).map some)
                (List.append
                  (List.replicate 4 (none : Option Bool))
                  (List.append
                    ((CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                      L.rejectHit []).map some)
                    [none])))))) := by
  rw [show
      selectedHitOtherFlagErasedRightLeftHandoffTape false L =
        Tape.move Direction.left
          (Tape.move Direction.right
            (Tape.move Direction.left
              (DovetailInitialLayoutInitializer.tapeAtCells
                (List.append
                  (List.append
                    ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                      L.rejectConfig []).reverse.map some)
                    (List.append
                      ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
                        L.acceptConfig []).reverse.map some)
                      (List.append
                        ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                          L.stage).reverse.map some)
                        ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
                          some))))
                  [none])
                (none :: none :: none :: none ::
                  (List.append
                    ((CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
                      L.rejectHit []).map some)
                    [none]))))) by
    simp [selectedHitOtherFlagErasedRightLeftHandoffTape,
      selectedHitOtherFlagErasedTape, List.append_assoc]]
  rw [tapeAtCells_move_left_right_left_append_none_cons_cells]
  simp [List.reverse_append, List.map_reverse, List.append_assoc]

def SelectedProjectionPaddedTailCleanupPostEraseSpec
    (useAccept : Bool)
    (postErase : MachineDescription) : Prop :=
  postErase.SubroutineReady ∧
    forall L : DovetailLayout,
      postErase.HaltsFromTape
        (selectedHitOtherFlagErasedRightLeftHandoffTape useAccept L)
        (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L)

def SelectedProjectionPaddedTailCleanupPostEraseConstruction : Prop :=
  forall useAccept : Bool,
    exists postErase : MachineDescription,
      SelectedProjectionPaddedTailCleanupPostEraseSpec useAccept postErase

def SelectedProjectionPaddedTailCleanupPostPaddingSpec
    (useAccept : Bool) (postPadding : MachineDescription) : Prop :=
  postPadding.SubroutineReady ∧
    forall L : DovetailLayout,
      postPadding.HaltsFromTape
        (selectedHitOtherFlagErasedAfterPaddingTape useAccept L)
        (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L)

def SelectedProjectionPaddedTailCleanupPostPaddingConstruction :
    Prop :=
  forall useAccept : Bool,
    exists postPadding : MachineDescription,
      SelectedProjectionPaddedTailCleanupPostPaddingSpec
        useAccept postPadding

def SelectedProjectionPaddedTailCleanupPostPaddingBranchConstruction
    (useAccept : Bool) : Prop :=
  exists postPadding : MachineDescription,
    SelectedProjectionPaddedTailCleanupPostPaddingSpec
      useAccept postPadding

theorem selectedProjectionPaddedTailCleanupPostPaddingConstruction_of_branches
    (hAccept :
      SelectedProjectionPaddedTailCleanupPostPaddingBranchConstruction true)
    (hReject :
      SelectedProjectionPaddedTailCleanupPostPaddingBranchConstruction false) :
    SelectedProjectionPaddedTailCleanupPostPaddingConstruction := by
  intro useAccept
  cases useAccept
  · exact hReject
  · exact hAccept

/--
Combined post-padding finite-machine leaf for selected-projection tail cleanup.
The branch wrappers below project this single obligation into the accepting and
rejecting branch contracts.
-/
theorem selectedProjectionPaddedTailCleanupPostPaddingCoreConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingConstruction := by
  sorry

def selectedHitOtherFlagErasedPostEraseFromPostPadding
    (useAccept : Bool) (postPadding : MachineDescription) :
    MachineDescription :=
  if useAccept then
    SeqViaCanonical skipCurrentAndFourBlankPaddingLeftDescription
      postPadding
  else
    SeqViaCanonical skipCurrentAndFourBlankPaddingRightDescription
      postPadding

theorem selectedProjectionPaddedTailCleanupPostEraseSpec_of_postPadding
    {useAccept : Bool} {postPadding : MachineDescription}
    (hpostPadding :
      SelectedProjectionPaddedTailCleanupPostPaddingSpec
        useAccept postPadding) :
    SelectedProjectionPaddedTailCleanupPostEraseSpec useAccept
      (selectedHitOtherFlagErasedPostEraseFromPostPadding
        useAccept postPadding) := by
  cases useAccept
  · constructor
    · simpa [selectedHitOtherFlagErasedPostEraseFromPostPadding] using
        SeqViaCanonical_subroutineReady
          skipCurrentAndFourBlankPaddingRightDescription_subroutineReady
          hpostPadding.left
    · intro L
      exact
        SeqViaCanonical_haltsFromTape_of_haltsFromTape
          skipCurrentAndFourBlankPaddingRightDescription_subroutineReady
          hpostPadding.left
          (skipCurrentAndFourBlankPaddingRightDescription_haltsFrom_rejectHandoff_named
            L)
          (by
            simpa [selectedHitOtherFlagErasedAfterPaddingTape] using
              selectedHitOtherFlagErasedAfterPaddingTape_move_left_move_right
                false L)
          (by
            simpa [selectedHitOtherFlagErasedAfterPaddingTape] using
              hpostPadding.right L)
  · constructor
    · simpa [selectedHitOtherFlagErasedPostEraseFromPostPadding] using
        SeqViaCanonical_subroutineReady
          skipCurrentAndFourBlankPaddingLeftDescription_subroutineReady
          hpostPadding.left
    · intro L
      exact
        SeqViaCanonical_haltsFromTape_of_haltsFromTape
          skipCurrentAndFourBlankPaddingLeftDescription_subroutineReady
          hpostPadding.left
          (skipCurrentAndFourBlankPaddingLeftDescription_haltsFrom_acceptHandoff
            L)
          (by
            simpa [selectedHitOtherFlagErasedAfterPaddingTape] using
              selectedHitOtherFlagErasedAfterPaddingTape_move_left_move_right
                true L)
          (by
            simpa [selectedHitOtherFlagErasedAfterPaddingTape] using
              hpostPadding.right L)

theorem selectedProjectionPaddedTailCleanupPostEraseConstruction_of_postPadding
    (h :
      SelectedProjectionPaddedTailCleanupPostPaddingConstruction) :
    SelectedProjectionPaddedTailCleanupPostEraseConstruction := by
  intro useAccept
  rcases h useAccept with ⟨postPadding, hpostPadding⟩
  exact
    ⟨selectedHitOtherFlagErasedPostEraseFromPostPadding
        useAccept postPadding,
      selectedProjectionPaddedTailCleanupPostEraseSpec_of_postPadding
        hpostPadding⟩

/--
Post-padding finite-machine leaf for selected-projection tail cleanup on the
accepting projection branch.
-/
theorem selectedProjectionPaddedTailCleanupPostPaddingAcceptConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingBranchConstruction true := by
  exact selectedProjectionPaddedTailCleanupPostPaddingCoreConstruction true

/--
Post-padding finite-machine leaf for selected-projection tail cleanup on the
rejecting projection branch.
-/
theorem selectedProjectionPaddedTailCleanupPostPaddingRejectConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingBranchConstruction false := by
  exact selectedProjectionPaddedTailCleanupPostPaddingCoreConstruction false

theorem selectedProjectionPaddedTailCleanupPostPaddingConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingConstruction :=
  selectedProjectionPaddedTailCleanupPostPaddingConstruction_of_branches
    selectedProjectionPaddedTailCleanupPostPaddingAcceptConstruction
    selectedProjectionPaddedTailCleanupPostPaddingRejectConstruction

theorem selectedProjectionPaddedTailCleanupPostEraseConstruction :
    SelectedProjectionPaddedTailCleanupPostEraseConstruction :=
  selectedProjectionPaddedTailCleanupPostEraseConstruction_of_postPadding
    selectedProjectionPaddedTailCleanupPostPaddingConstruction


end SelectedProjectionPaddedTailCleanup

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
