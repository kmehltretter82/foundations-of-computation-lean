import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.DeleteWindow
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.PaddedIdentity
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.RightEdgeRewind
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.Erase

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

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

def selectedHitOtherFlagErasedAcceptAfterPaddingRewindLeftStack
    (L : DovetailLayout) : Word Bool :=
  List.append
    (if L.acceptHit then [true, true, false] else [false, true, false])
    (List.append
      (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
        L.rejectConfig []).reverse
      (List.append
        (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
          L.acceptConfig []).reverse
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage).reverse
          (SelectedProjectionTailProjector.outputPrefixBits L).reverse)))

theorem selectedHitOtherFlagErasedAcceptHitRestLeftRev_eq_rewindLeftStack
    (L : DovetailLayout) :
    selectedHitOtherFlagErasedAcceptHitRestLeftRev L =
      List.append
        ((selectedHitOtherFlagErasedAcceptAfterPaddingRewindLeftStack L).map
          some)
        [none] := by
  by_cases haccept : L.acceptHit <;>
    simp [selectedHitOtherFlagErasedAcceptHitRestLeftRev,
      selectedHitOtherFlagErasedAcceptAfterPaddingRewindLeftStack,
      haccept, List.map_append, List.append_assoc]

theorem selectedHitOtherFlagErasedAcceptAfterPaddingRewindBits_eq_source
    (L : DovetailLayout) :
    List.append
        (selectedHitOtherFlagErasedAcceptAfterPaddingRewindLeftStack L).reverse
        [selectedHitOtherFlagErasedAcceptHitHead L.acceptHit] =
      selectedProjectionPaddedTailCleanupPostPaddingSourceBits true L := by
  by_cases haccept : L.acceptHit <;>
    simp [selectedHitOtherFlagErasedAcceptAfterPaddingRewindLeftStack,
      selectedHitOtherFlagErasedAcceptHitHead,
      selectedProjectionPaddedTailCleanupPostPaddingSourceBits_true,
      selectedProjectionPaddedTailCleanupPrefixBits,
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
      encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      haccept, List.reverse_append, List.append_assoc]

theorem rightEdgeRewindDescription_haltsFrom_acceptAfterPadding
    (L : DovetailLayout) :
    rightEdgeRewindDescription.HaltsFromTape
      (selectedHitOtherFlagErasedAfterPaddingTape true L)
      (FSTStatefulOptionAppendSourceTapeWithPadding
        (selectedProjectionPaddedTailCleanupPostPaddingSourceBits true L)
        1
        (List.replicate 5 (none : Option Bool))) := by
  have hrewind :=
    rightEdgeRewindDescription_haltsFrom_lastBitBoundary
      (selectedHitOtherFlagErasedAcceptAfterPaddingRewindLeftStack L)
      (selectedHitOtherFlagErasedAcceptHitHead L.acceptHit)
      (List.replicate 5 (none : Option Bool))
  rw [selectedHitOtherFlagErasedAcceptAfterPaddingRewindBits_eq_source]
    at hrewind
  rw [selectedHitOtherFlagErasedAfterPaddingTape,
    selectedHitOtherFlagErasedAcceptAfterPaddingTape,
    selectedHitOtherFlagErasedAcceptHitRestLeftRev_eq_rewindLeftStack]
  simpa [FSTStatefulOptionAppendSourceTapeWithPadding,
    rightEdgeRewindTargetTape, DovetailInitialLayoutInitializer.tapeAtCells,
    tapeAtCells, List.replicate, List.append_assoc] using hrewind

theorem generatedDeleteWindowDescription_haltsFrom_acceptAfterPaddingFSTSource
    (L : DovetailLayout) :
    (generatedDeleteWindowDescription
      (selectedProjectionPaddedTailCleanupKeptPrefixBits true L).length
      (selectedProjectionPaddedTailCleanupUnselectedConfigBits true L).length).HaltsFromTape
      (FSTStatefulOptionAppendSourceTapeWithPadding
        (selectedProjectionPaddedTailCleanupPostPaddingSourceBits true L)
        1
        (List.replicate 5 (none : Option Bool)))
      (FSTStatefulOptionAppendTargetTapeWithPadding
        (deleteWindowNext
          (selectedProjectionPaddedTailCleanupKeptPrefixBits true L).length
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits true L).length)
        (deleteWindowEmit
          (selectedProjectionPaddedTailCleanupKeptPrefixBits true L).length
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits true L).length)
        0
        (selectedProjectionPaddedTailCleanupPostPaddingSourceBits true L)
        1
        (List.replicate 5 (none : Option Bool))) := by
  rw [selectedProjectionPaddedTailCleanupPostPaddingSourceBits_eq_deleteBlock]
  exact
    generatedDeleteWindowDescription_haltsFrom_split_withPadding
      (selectedProjectionPaddedTailCleanupKeptPrefixBits true L).length
      (selectedProjectionPaddedTailCleanupUnselectedConfigBits true L).length
      (selectedProjectionPaddedTailCleanupKeptPrefixBits true L)
      (selectedProjectionPaddedTailCleanupUnselectedConfigBits true L)
      (selectedProjectionPaddedTailCleanupKeptSuffixBits true L)
      1
      (List.replicate 5 (none : Option Bool))

def deleteWindowThenFourBlankRightDescription
    (keep delete : Nat) : MachineDescription :=
  SeqViaCanonical (generatedDeleteWindowDescription keep delete)
    rightMoveAcrossFourBlanksDescription

theorem deleteWindowThenFourBlankRightDescription_subroutineReady
    (keep delete : Nat) :
    (deleteWindowThenFourBlankRightDescription keep delete).SubroutineReady :=
  SeqViaCanonical_subroutineReady
    (generatedDeleteWindowDescription_subroutineReady keep delete)
    rightMoveAcrossFourBlanksDescription_subroutineReady

def deleteWindowThenFourBlankRightEndLeftCells
    (delete : Nat) (pref suffix : Word Bool) :
    List (Option Bool) :=
  List.append [none]
    (List.append (pref.map some)
      (List.append
        (List.replicate delete (none : Option Bool))
        (List.append (suffix.map some)
          (List.replicate 5 (none : Option Bool)))))

def deleteWindowThenFourBlankRightEndStatefulLeftCells
    (keep delete : Nat) (input : Word Bool) :
    List (Option Bool) :=
  List.append [none]
    (List.append
      (statefulOptionCellsFrom
        (deleteWindowNext keep delete)
        (deleteWindowEmit keep delete)
        0 input)
      (List.replicate 5 (none : Option Bool)))

theorem deleteWindowTargetTapeWithFivePadding_move_left_move_right
    (keep delete : Nat) (input : Word Bool) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (FSTStatefulOptionAppendTargetTapeWithPadding
            (deleteWindowNext keep delete)
            (deleteWindowEmit keep delete)
            0 input 1
            (List.replicate 5 (none : Option Bool)))) =
      FSTStatefulOptionAppendTargetTapeWithPadding
        (deleteWindowNext keep delete)
        (deleteWindowEmit keep delete)
        0 input 1
        (List.replicate 5 (none : Option Bool)) := by
  simp [FSTStatefulOptionAppendTargetTapeWithPadding, tapeAtCells,
    Tape.move, Tape.moveLeft, Tape.moveRight, List.replicate]

theorem rightMoveAcrossFourBlanksDescription_haltsFrom_deleteWindowTarget
    (keep delete : Nat) (input : Word Bool) :
    rightMoveAcrossFourBlanksDescription.HaltsFromTape
      (FSTStatefulOptionAppendTargetTapeWithPadding
        (deleteWindowNext keep delete)
        (deleteWindowEmit keep delete)
        0
        input
        1
        (List.replicate 5 (none : Option Bool)))
      (rightEndCompactionSourceTape
        (deleteWindowThenFourBlankRightEndStatefulLeftCells
          keep delete input)) := by
  have hmove :=
    rightMoveAcrossFourBlanksDescription_haltsFromTape
      (none ::
        List.append
          (statefulOptionCellsFrom
            (deleteWindowNext keep delete)
            (deleteWindowEmit keep delete)
            0
            input).reverse
          (List.replicate 1 (none : Option Bool)))
      [none]
  simpa [FSTStatefulOptionAppendTargetTapeWithPadding,
    rightEndCompactionSourceTape,
    deleteWindowThenFourBlankRightEndStatefulLeftCells,
    List.replicate, List.reverse_append,
    List.append_assoc] using hmove

theorem deleteWindowThenFourBlankRightEndStatefulLeftCells_eq_split
    (keep delete : Nat)
    (pref deleted suffix : Word Bool)
    (hpref : pref.length = keep)
    (hdeleted : deleted.length = delete) :
    deleteWindowThenFourBlankRightEndStatefulLeftCells
        keep delete (List.append pref (List.append deleted suffix)) =
      deleteWindowThenFourBlankRightEndLeftCells delete pref suffix := by
  have hcells :=
    deleteWindowCellsFrom_split
      keep delete pref deleted suffix hpref hdeleted
  rw [deleteWindowThenFourBlankRightEndStatefulLeftCells,
    deleteWindowThenFourBlankRightEndLeftCells, hcells]
  simp [List.append_assoc]

theorem rightMoveAcrossFourBlanksDescription_haltsFrom_deleteWindowTarget_split
    (keep delete : Nat)
    (pref deleted suffix : Word Bool)
    (hpref : pref.length = keep)
    (hdeleted : deleted.length = delete) :
    rightMoveAcrossFourBlanksDescription.HaltsFromTape
      (FSTStatefulOptionAppendTargetTapeWithPadding
        (deleteWindowNext keep delete)
        (deleteWindowEmit keep delete)
        0
        (List.append pref (List.append deleted suffix))
        1
        (List.replicate 5 (none : Option Bool)))
      (rightEndCompactionSourceTape
        (deleteWindowThenFourBlankRightEndLeftCells
          delete pref suffix)) := by
  rw [←
    deleteWindowThenFourBlankRightEndStatefulLeftCells_eq_split
      keep delete pref deleted suffix hpref hdeleted]
  exact
    rightMoveAcrossFourBlanksDescription_haltsFrom_deleteWindowTarget
      keep delete (List.append pref (List.append deleted suffix))

theorem deleteWindowThenFourBlankRightDescription_haltsFrom_split
    (keep delete : Nat)
    (pref deleted suffix : Word Bool)
    (hpref : pref.length = keep)
    (hdeleted : deleted.length = delete) :
    (deleteWindowThenFourBlankRightDescription keep delete).HaltsFromTape
      (FSTStatefulOptionAppendSourceTapeWithPadding
        (List.append pref (List.append deleted suffix))
        1
        (List.replicate 5 (none : Option Bool)))
      (rightEndCompactionSourceTape
        (deleteWindowThenFourBlankRightEndLeftCells
          delete pref suffix)) :=
  SeqViaCanonical_haltsFromTape_of_haltsFromTape
    (generatedDeleteWindowDescription_subroutineReady keep delete)
    rightMoveAcrossFourBlanksDescription_subroutineReady
    (generatedDeleteWindowDescription_haltsFrom_split_withPadding
      keep delete pref deleted suffix 1
      (List.replicate 5 (none : Option Bool)))
    (deleteWindowTargetTapeWithFivePadding_move_left_move_right
      keep delete
      (List.append pref (List.append deleted suffix)))
    (rightMoveAcrossFourBlanksDescription_haltsFrom_deleteWindowTarget_split
      keep delete pref deleted suffix hpref hdeleted)

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

def selectedHitOtherFlagErasedRejectAfterPaddingScanLeft
    (L : DovetailLayout) : List (Option Bool) :=
  List.append (List.replicate 4 (none : Option Bool))
    (selectedHitOtherFlagErasedRejectBaseLeftRev L)

theorem selectedHitOtherFlagErasedRejectAfterPaddingTape_eq_scanSource
    (L : DovetailLayout) :
    selectedHitOtherFlagErasedAfterPaddingTape false L =
      rightEdgeScanSourceTapeFromLeft
        (selectedHitOtherFlagErasedRejectAfterPaddingScanLeft L)
        (selectedProjectionPaddedTailCleanupSelectedHitBits false L)
        [] := by
  by_cases hreject : L.rejectHit <;>
    simp [selectedHitOtherFlagErasedAfterPaddingTape,
      selectedHitOtherFlagErasedRejectAfterPaddingTape,
      selectedHitOtherFlagErasedRejectAfterPaddingScanLeft,
      selectedHitOtherFlagErasedRejectBaseCells,
      rightEdgeScanSourceTapeFromLeft,
      DovetailInitialLayoutInitializer.tapeAtCells, tapeAtCells,
      selectedProjectionPaddedTailCleanupSelectedHitBits,
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
      encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      hreject]

theorem rightEdgeScanDescription_haltsFrom_rejectAfterPadding
    (L : DovetailLayout) :
    rightEdgeScanDescription.HaltsFromTape
      (selectedHitOtherFlagErasedAfterPaddingTape false L)
      (rightEdgeScanTargetTapeFromLeft
        (selectedHitOtherFlagErasedRejectAfterPaddingScanLeft L)
        (selectedProjectionPaddedTailCleanupSelectedHitBits false L)
        []) := by
  rw [selectedHitOtherFlagErasedRejectAfterPaddingTape_eq_scanSource]
  exact rightEdgeScanDescription_haltsFromTape
    (selectedHitOtherFlagErasedRejectAfterPaddingScanLeft L)
    (selectedProjectionPaddedTailCleanupSelectedHitBits false L)
    []

def selectedHitOtherFlagErasedRejectAfterPaddingRightEndLeftCells
    (L : DovetailLayout) : List (Option Bool) :=
  List.append
    (selectedHitOtherFlagErasedRejectAfterPaddingScanLeft L).reverse
    ((selectedProjectionPaddedTailCleanupSelectedHitBits false L).map some)

theorem rightEdgeScanTargetTape_rejectAfterPadding_moveRight_eq_rightEndSource
    (L : DovetailLayout) :
    Tape.move Direction.right
        (rightEdgeScanTargetTapeFromLeft
          (selectedHitOtherFlagErasedRejectAfterPaddingScanLeft L)
          (selectedProjectionPaddedTailCleanupSelectedHitBits false L)
          []) =
      rightEndCompactionSourceTape
        (selectedHitOtherFlagErasedRejectAfterPaddingRightEndLeftCells L) := by
  by_cases hreject : L.rejectHit <;>
    simp [rightEdgeScanTargetTapeFromLeft,
      selectedHitOtherFlagErasedRejectAfterPaddingRightEndLeftCells,
      selectedHitOtherFlagErasedRejectAfterPaddingScanLeft,
      rightEndCompactionSourceTape,
      selectedProjectionPaddedTailCleanupSelectedHitBits,
      selectedHitOtherFlagErasedRejectBaseLeftRev,
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
      encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      hreject, tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight,
      List.map_reverse]

theorem rightMoveOnceDescription_haltsFrom_rejectAfterPaddingScanTarget
    (L : DovetailLayout) :
    rightMoveOnceDescription.HaltsFromTape
      (rightEdgeScanTargetTapeFromLeft
        (selectedHitOtherFlagErasedRejectAfterPaddingScanLeft L)
        (selectedProjectionPaddedTailCleanupSelectedHitBits false L)
        [])
      (rightEndCompactionSourceTape
        (selectedHitOtherFlagErasedRejectAfterPaddingRightEndLeftCells L)) := by
  have hmove :=
    rightMoveOnceDescription_haltsFromTape
      (rightEdgeScanTargetTapeFromLeft
        (selectedHitOtherFlagErasedRejectAfterPaddingScanLeft L)
        (selectedProjectionPaddedTailCleanupSelectedHitBits false L)
        [])
  simpa [rightEdgeScanTargetTape_rejectAfterPadding_moveRight_eq_rightEndSource]
    using hmove

theorem rightEdgeScanTargetTape_rejectAfterPadding_move_left_move_right
    (L : DovetailLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (rightEdgeScanTargetTapeFromLeft
            (selectedHitOtherFlagErasedRejectAfterPaddingScanLeft L)
            (selectedProjectionPaddedTailCleanupSelectedHitBits false L)
            [])) =
      rightEdgeScanTargetTapeFromLeft
        (selectedHitOtherFlagErasedRejectAfterPaddingScanLeft L)
        (selectedProjectionPaddedTailCleanupSelectedHitBits false L)
        [] := by
  by_cases hreject : L.rejectHit <;>
    simp [rightEdgeScanTargetTapeFromLeft,
      selectedHitOtherFlagErasedRejectAfterPaddingScanLeft,
      selectedProjectionPaddedTailCleanupSelectedHitBits,
      selectedHitOtherFlagErasedRejectBaseLeftRev,
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
      encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      hreject, tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight,
      List.map_reverse]

def selectedHitOtherFlagErasedRejectToRightEndDescription :
    MachineDescription :=
  SeqViaCanonical rightEdgeScanDescription rightMoveOnceDescription

theorem selectedHitOtherFlagErasedRejectToRightEndDescription_subroutineReady :
    selectedHitOtherFlagErasedRejectToRightEndDescription.SubroutineReady :=
  SeqViaCanonical_subroutineReady
    rightEdgeScanDescription_subroutineReady
    rightMoveOnceDescription_subroutineReady

theorem selectedHitOtherFlagErasedRejectToRightEndDescription_haltsFrom_afterPadding
    (L : DovetailLayout) :
    selectedHitOtherFlagErasedRejectToRightEndDescription.HaltsFromTape
      (selectedHitOtherFlagErasedAfterPaddingTape false L)
      (rightEndCompactionSourceTape
        (selectedHitOtherFlagErasedRejectAfterPaddingRightEndLeftCells L)) :=
  SeqViaCanonical_haltsFromTape_of_haltsFromTape
    rightEdgeScanDescription_subroutineReady
    rightMoveOnceDescription_subroutineReady
    (rightEdgeScanDescription_haltsFrom_rejectAfterPadding L)
    (rightEdgeScanTargetTape_rejectAfterPadding_move_left_move_right L)
    (rightMoveOnceDescription_haltsFrom_rejectAfterPaddingScanTarget L)

theorem selectedProjectionPaddedTailCleanupTargetTape_eq_FSTTargetTape
    (useAccept : Bool) (L : DovetailLayout) :
    SelectedProjectionEquivEmitterPaddedOutputTape useAccept L =
      FSTTargetTape
        (selectedProjectionPaddedTailCleanupTargetBits useAccept L)
        (ParsedLayoutBits L).length := by
  rw [SelectedProjectionEquivEmitterPaddedOutputTape_eq_outputAllBits]
  rw [selectedProjectionPaddedTailCleanupTargetBits_eq_outputCode,
    selectedProjectionOutputBits_eq_tailProjector_outputAllBits]
  rfl

theorem selectedProjectionPaddedTailCleanupDeleteWindow_compactedCells
    (useAccept : Bool) (L : DovetailLayout)
    (leftScratch extraScratch : Nat) :
    compactedCellsWithScratch
        (Tape.cells
          (FSTStatefulOptionAppendTargetTape
            (deleteWindowNext
              (selectedProjectionPaddedTailCleanupKeptPrefixBits
                useAccept L).length
              (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                useAccept L).length)
            (deleteWindowEmit
              (selectedProjectionPaddedTailCleanupKeptPrefixBits
                useAccept L).length
              (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                useAccept L).length)
            0
            (selectedProjectionPaddedTailCleanupPostPaddingSourceBits
              useAccept L)
            []
            leftScratch))
        extraScratch =
      rightScratchOutputCells
        (selectedProjectionPaddedTailCleanupTargetBits useAccept L)
        (leftScratch +
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits
            useAccept L).length + 2 + extraScratch) := by
  rw [selectedProjectionPaddedTailCleanupPostPaddingSourceBits_eq_deleteBlock]
  simpa [selectedProjectionPaddedTailCleanupTargetBits_eq_kept] using
    FSTDeleteWindowTargetTape_compactedCells_split
      (keep :=
        (selectedProjectionPaddedTailCleanupKeptPrefixBits
          useAccept L).length)
      (delete :=
        (selectedProjectionPaddedTailCleanupUnselectedConfigBits
          useAccept L).length)
      (pref :=
        selectedProjectionPaddedTailCleanupKeptPrefixBits useAccept L)
      (deleted :=
        selectedProjectionPaddedTailCleanupUnselectedConfigBits useAccept L)
      (suffix :=
        selectedProjectionPaddedTailCleanupKeptSuffixBits useAccept L)
      (leftScratch := leftScratch)
      (extraScratch := extraScratch)
      rfl
      rfl

theorem selectedProjectionPaddedTailCleanupDeleteWindow_compactedCells_eq_targetTape_cells
    (useAccept : Bool) (L : DovetailLayout)
    (leftScratch extraScratch : Nat)
    (hscratch :
      leftScratch +
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits
            useAccept L).length + 2 + extraScratch =
        (ParsedLayoutBits L).length) :
    compactedCellsWithScratch
        (Tape.cells
          (FSTStatefulOptionAppendTargetTape
            (deleteWindowNext
              (selectedProjectionPaddedTailCleanupKeptPrefixBits
                useAccept L).length
              (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                useAccept L).length)
            (deleteWindowEmit
              (selectedProjectionPaddedTailCleanupKeptPrefixBits
                useAccept L).length
              (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                useAccept L).length)
            0
            (selectedProjectionPaddedTailCleanupPostPaddingSourceBits
              useAccept L)
            []
            leftScratch))
        extraScratch =
      Tape.cells
        (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L) := by
  rw [selectedProjectionPaddedTailCleanupDeleteWindow_compactedCells]
  rw [selectedProjectionPaddedTailCleanupTargetTape_cells_eq_bits]
  simp [rightScratchOutputCells, hscratch]

def selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells
    (L : DovetailLayout) : List (Option Bool) :=
  List.append [none]
    (List.append
      ((List.append
        (selectedProjectionPaddedTailCleanupPrefixBits L)
        (selectedProjectionPaddedTailCleanupSelectedConfigBits
          true L)).map some)
      (List.append
        (List.replicate
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits
            true L).length
          (none : Option Bool))
        (List.append
          ((selectedProjectionPaddedTailCleanupSelectedHitBits
            true L).map some)
          (List.replicate 5 (none : Option Bool)))))

def selectedProjectionPaddedTailCleanupDeletedRejectRightEndLeftCells
    (L : DovetailLayout) : List (Option Bool) :=
  List.append [none]
    (List.append
      ((selectedProjectionPaddedTailCleanupPrefixBits L).map some)
      (List.append
        (List.replicate
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits
            false L).length
          (none : Option Bool))
        (List.append
          ((selectedProjectionPaddedTailCleanupSelectedConfigBits
            false L).map some)
          (List.append
            (List.replicate 4 (none : Option Bool))
            ((selectedProjectionPaddedTailCleanupSelectedHitBits
              false L).map some)))))

theorem rightMoveAcrossFourBlanksDescription_haltsFrom_acceptDeleteTarget
    (L : DovetailLayout) :
    rightMoveAcrossFourBlanksDescription.HaltsFromTape
      (FSTStatefulOptionAppendTargetTapeWithPadding
        (deleteWindowNext
          (selectedProjectionPaddedTailCleanupKeptPrefixBits true L).length
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits true L).length)
        (deleteWindowEmit
          (selectedProjectionPaddedTailCleanupKeptPrefixBits true L).length
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits true L).length)
        0
        (selectedProjectionPaddedTailCleanupPostPaddingSourceBits true L)
        1
        (List.replicate 5 (none : Option Bool)))
      (rightEndCompactionSourceTape
        (selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells
          L)) := by
  simpa [selectedProjectionPaddedTailCleanupPostPaddingSourceBits_eq_deleteBlock,
    deleteWindowThenFourBlankRightEndLeftCells,
    selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells,
    selectedProjectionPaddedTailCleanupKeptPrefixBits,
    selectedProjectionPaddedTailCleanupKeptSuffixBits,
    List.map_append, List.append_assoc] using
    rightMoveAcrossFourBlanksDescription_haltsFrom_deleteWindowTarget_split
      (selectedProjectionPaddedTailCleanupKeptPrefixBits true L).length
      (selectedProjectionPaddedTailCleanupUnselectedConfigBits true L).length
      (selectedProjectionPaddedTailCleanupKeptPrefixBits true L)
      (selectedProjectionPaddedTailCleanupUnselectedConfigBits true L)
      (selectedProjectionPaddedTailCleanupKeptSuffixBits true L)
      rfl
      rfl

theorem selectedProjectionPaddedTailCleanupDeletedAcceptCells_compacted
    (L : DovetailLayout) (extraScratch : Nat) :
    compactedCellsWithScratch
        (List.append [none]
          (List.append
            ((List.append
              (selectedProjectionPaddedTailCleanupPrefixBits L)
              (selectedProjectionPaddedTailCleanupSelectedConfigBits
                true L)).map some)
            (List.append
              (List.replicate
                (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                  true L).length
                (none : Option Bool))
              (List.append
                ((selectedProjectionPaddedTailCleanupSelectedHitBits
                  true L).map some)
                (List.replicate 6 (none : Option Bool))))))
        extraScratch =
      rightScratchOutputCells
        (selectedProjectionPaddedTailCleanupTargetBits true L)
        (1 +
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits
            true L).length + 6 + extraScratch) := by
  simpa [List.replicate, List.map_append, List.append_assoc,
    selectedProjectionPaddedTailCleanupTargetBits_eq_selectedFields,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    compactedCellsWithScratch_twoChunks
      1
      (selectedProjectionPaddedTailCleanupUnselectedConfigBits
        true L).length
      6
      extraScratch
      (List.append
        (selectedProjectionPaddedTailCleanupPrefixBits L)
        (selectedProjectionPaddedTailCleanupSelectedConfigBits true L))
      (selectedProjectionPaddedTailCleanupSelectedHitBits true L)

theorem selectedProjectionPaddedTailCleanupDeletedAcceptRightEndCells_compacted
    (L : DovetailLayout) (extraScratch : Nat) :
    compactedCellsWithScratch
        (rightEndCompactionVisibleCells
          (selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells
            L))
        extraScratch =
      rightScratchOutputCells
        (selectedProjectionPaddedTailCleanupTargetBits true L)
        (1 +
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits
            true L).length + 6 + extraScratch) := by
  simpa [rightEndCompactionVisibleCells,
    selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells,
    List.replicate, List.append_assoc] using
    selectedProjectionPaddedTailCleanupDeletedAcceptCells_compacted
      L extraScratch

theorem selectedProjectionPaddedTailCleanupDeletedAcceptRightEndTargetTape_eq
    (L : DovetailLayout) (extraScratch : Nat)
    (hscratch :
      1 +
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits
            true L).length + 6 + extraScratch =
        (ParsedLayoutBits L).length) :
    rightEndCompactionTargetTape
        (selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells L)
        extraScratch =
      SelectedProjectionEquivEmitterPaddedOutputTape true L := by
  have hfilter :
      (rightEndCompactionVisibleCells
          (selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells
            L)).filterMap (fun cell => cell) =
        selectedProjectionPaddedTailCleanupTargetBits true L := by
    simp [rightEndCompactionVisibleCells,
      selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells,
      selectedProjectionPaddedTailCleanupTargetBits_eq_selectedFields,
      List.filterMap_append, Function.comp_def, List.map_append,
      List.replicate, List.append_assoc]
  have hwidth :
      compactionScratchWidth
          (rightEndCompactionVisibleCells
            (selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells
              L))
          extraScratch =
        (ParsedLayoutBits L).length := by
    rw [compactionScratchWidth, hfilter]
    simp [rightEndCompactionVisibleCells,
      selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells,
      selectedProjectionPaddedTailCleanupTargetBits_eq_selectedFields,
      List.length_append, List.map_append, List.replicate,
      List.append_assoc] at hscratch ⊢
    omega
  rw [rightEndCompactionTargetTape,
    selectedProjectionPaddedTailCleanupTargetTape_eq_FSTTargetTape,
    hfilter, hwidth]

theorem selectedProjectionPaddedTailCleanupDeletedAcceptRightEndCompactor_haltsFrom
    {D : MachineDescription} {extraScratch : Nat}
    (hD : RightEndCompactionMachineContract D extraScratch)
    (L : DovetailLayout)
    (hscratch :
      1 +
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits
            true L).length + 6 + extraScratch =
        (ParsedLayoutBits L).length) :
    D.HaltsFromTape
      (rightEndCompactionSourceTape
        (selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells L))
      (SelectedProjectionEquivEmitterPaddedOutputTape true L) := by
  rw [←
    selectedProjectionPaddedTailCleanupDeletedAcceptRightEndTargetTape_eq
      L extraScratch hscratch]
  exact hD.haltsFromTape
    (selectedProjectionPaddedTailCleanupDeletedAcceptRightEndLeftCells L)

theorem selectedProjectionPaddedTailCleanupDeletedRejectCells_compacted
    (L : DovetailLayout) (extraScratch : Nat) :
    compactedCellsWithScratch
        (List.append [none]
          (List.append
            ((selectedProjectionPaddedTailCleanupPrefixBits L).map some)
            (List.append
              (List.replicate
                (selectedProjectionPaddedTailCleanupUnselectedConfigBits
                  false L).length
                (none : Option Bool))
              (List.append
                ((selectedProjectionPaddedTailCleanupSelectedConfigBits
                  false L).map some)
                (List.append
                  (List.replicate 4 (none : Option Bool))
                  (List.append
                    ((selectedProjectionPaddedTailCleanupSelectedHitBits
                      false L).map some)
                    [none]))))))
        extraScratch =
      rightScratchOutputCells
        (selectedProjectionPaddedTailCleanupTargetBits false L)
        (1 +
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits
            false L).length + 4 + 1 + extraScratch) := by
  simpa [List.replicate, List.map_append, List.append_assoc,
    selectedProjectionPaddedTailCleanupTargetBits_eq_selectedFields,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    compactedCellsWithScratch_threeChunks
      1
      (selectedProjectionPaddedTailCleanupUnselectedConfigBits
        false L).length
      4
      1
      extraScratch
      (selectedProjectionPaddedTailCleanupPrefixBits L)
      (selectedProjectionPaddedTailCleanupSelectedConfigBits false L)
      (selectedProjectionPaddedTailCleanupSelectedHitBits false L)

theorem selectedProjectionPaddedTailCleanupDeletedRejectRightEndCells_compacted
    (L : DovetailLayout) (extraScratch : Nat) :
    compactedCellsWithScratch
        (rightEndCompactionVisibleCells
          (selectedProjectionPaddedTailCleanupDeletedRejectRightEndLeftCells
            L))
        extraScratch =
      rightScratchOutputCells
        (selectedProjectionPaddedTailCleanupTargetBits false L)
        (1 +
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits
            false L).length + 4 + 1 + extraScratch) := by
  simpa [rightEndCompactionVisibleCells,
    selectedProjectionPaddedTailCleanupDeletedRejectRightEndLeftCells,
    List.append_assoc] using
    selectedProjectionPaddedTailCleanupDeletedRejectCells_compacted
      L extraScratch

theorem selectedProjectionPaddedTailCleanupDeletedRejectRightEndTargetTape_eq
    (L : DovetailLayout) (extraScratch : Nat)
    (hscratch :
      1 +
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits
            false L).length + 4 + 1 + extraScratch =
        (ParsedLayoutBits L).length) :
    rightEndCompactionTargetTape
        (selectedProjectionPaddedTailCleanupDeletedRejectRightEndLeftCells L)
        extraScratch =
      SelectedProjectionEquivEmitterPaddedOutputTape false L := by
  have hfilter :
      (rightEndCompactionVisibleCells
          (selectedProjectionPaddedTailCleanupDeletedRejectRightEndLeftCells
            L)).filterMap (fun cell => cell) =
        selectedProjectionPaddedTailCleanupTargetBits false L := by
    simp [rightEndCompactionVisibleCells,
      selectedProjectionPaddedTailCleanupDeletedRejectRightEndLeftCells,
      selectedProjectionPaddedTailCleanupTargetBits_eq_selectedFields,
      List.filterMap_append, Function.comp_def,
      List.append_assoc]
  have hwidth :
      compactionScratchWidth
          (rightEndCompactionVisibleCells
            (selectedProjectionPaddedTailCleanupDeletedRejectRightEndLeftCells
              L))
          extraScratch =
        (ParsedLayoutBits L).length := by
    rw [compactionScratchWidth, hfilter]
    simp [rightEndCompactionVisibleCells,
      selectedProjectionPaddedTailCleanupDeletedRejectRightEndLeftCells,
      selectedProjectionPaddedTailCleanupTargetBits_eq_selectedFields,
      List.length_append, List.replicate,
      List.append_assoc] at hscratch ⊢
    omega
  rw [rightEndCompactionTargetTape,
    selectedProjectionPaddedTailCleanupTargetTape_eq_FSTTargetTape,
    hfilter, hwidth]

theorem selectedProjectionPaddedTailCleanupDeletedRejectRightEndCompactor_haltsFrom
    {D : MachineDescription} {extraScratch : Nat}
    (hD : RightEndCompactionMachineContract D extraScratch)
    (L : DovetailLayout)
    (hscratch :
      1 +
          (selectedProjectionPaddedTailCleanupUnselectedConfigBits
            false L).length + 4 + 1 + extraScratch =
        (ParsedLayoutBits L).length) :
    D.HaltsFromTape
      (rightEndCompactionSourceTape
        (selectedProjectionPaddedTailCleanupDeletedRejectRightEndLeftCells L))
      (SelectedProjectionEquivEmitterPaddedOutputTape false L) := by
  rw [←
    selectedProjectionPaddedTailCleanupDeletedRejectRightEndTargetTape_eq
      L extraScratch hscratch]
  exact hD.haltsFromTape
    (selectedProjectionPaddedTailCleanupDeletedRejectRightEndLeftCells L)

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

end SelectedProjectionPaddedTailCleanup

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
