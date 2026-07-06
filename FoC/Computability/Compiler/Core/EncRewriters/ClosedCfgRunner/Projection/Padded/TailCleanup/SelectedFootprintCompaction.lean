import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.ScratchExtCountWindowBridge

set_option doc.verso true

/-!
# Selected logical-tape footprint compaction

This module contains the reusable selected logical-tape decoder footprint
shape lemmas and compactor contracts.  Count-window-specific endpoint wrappers
remain in the threaded bridge module that imports this file.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

open CanonicalLayouts.DovetailLayoutScanner

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_nil_nil :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] []) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells [] [] [] := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_nil
      []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_nil_cons
    (pad : Option Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (pad :: padding)) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        [] [] (pad :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_nil
      (pad :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_nil_none
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (none :: padding)) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        [] [] (none :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_nil_cons
      none padding

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_nil_some
    (padBit : Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (some padBit :: padding)) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        [] [] (some padBit :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_nil_cons
      (some padBit) padding

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_cons_nil
    (bit : Bool) (rest : Word Bool) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) []) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        [] (bit :: rest) [] := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_cons
      bit rest []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_cons_cons
    (bit : Bool) (rest : Word Bool)
    (pad : Option Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (pad :: padding)) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        [] (bit :: rest) (pad :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_cons
      bit rest (pad :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_cons_none
    (bit : Bool) (rest : Word Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (none :: padding)) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        [] (bit :: rest) (none :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_cons_cons
      bit rest none padding

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_cons_some
    (bit : Bool) (rest : Word Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (some padBit :: padding)) =
      selectedSegmentLogicalTapeDecoderDensifierSourceCells
        [] (bit :: rest) (some padBit :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_cons_cons
      bit rest (some padBit) padding

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_nil_nil :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] []) =
      selectedSegmentLogicalTapeDecoderDensifierPaddingPreservingCells [] [] := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_nil
      []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_nil_cons
    (pad : Option Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] (pad :: padding)) =
      selectedSegmentLogicalTapeDecoderDensifierPaddingPreservingCells
        [] (pad :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_nil
      (pad :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_nil_none
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] (none :: padding)) =
      selectedSegmentLogicalTapeDecoderDensifierPaddingPreservingCells
        [] (none :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_nil_cons
      none padding

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_nil_some
    (padBit : Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] (some padBit :: padding)) =
      selectedSegmentLogicalTapeDecoderDensifierPaddingPreservingCells
        [] (some padBit :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_nil_cons
      (some padBit) padding

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_cons_nil
    (bit : Bool) (rest : Word Bool) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) []) =
      selectedSegmentLogicalTapeDecoderDensifierPaddingPreservingCells
        (bit :: rest) [] := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_cons
      bit rest []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_cons_cons
    (bit : Bool) (rest : Word Bool)
    (pad : Option Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) (pad :: padding)) =
      selectedSegmentLogicalTapeDecoderDensifierPaddingPreservingCells
        (bit :: rest) (pad :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_cons
      bit rest (pad :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_cons_none
    (bit : Bool) (rest : Word Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) (none :: padding)) =
      selectedSegmentLogicalTapeDecoderDensifierPaddingPreservingCells
        (bit :: rest) (none :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_cons_cons
      bit rest none padding

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_cons_some
    (bit : Bool) (rest : Word Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) (some padBit :: padding)) =
      selectedSegmentLogicalTapeDecoderDensifierPaddingPreservingCells
        (bit :: rest) (some padBit :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_cons_cons
      bit rest (some padBit) padding

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape_nil_nil :
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] [] =
      rightEndCompactionSourceTape
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          [] []) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape
      [] []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape_nil_none
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] (none :: padding) =
      rightEndCompactionSourceTape
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          [] (none :: padding)) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape
      [] (none :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape_nil_some
    (padBit : Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] (some padBit :: padding) =
      rightEndCompactionSourceTape
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          [] (some padBit :: padding)) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape
      [] (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape_cons_nil
    (bit : Bool) (rest : Word Bool) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        (bit :: rest) [] =
      rightEndCompactionSourceTape
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          (bit :: rest) []) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape
      (bit :: rest) []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape_cons_none
    (bit : Bool) (rest : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        (bit :: rest) (none :: padding) =
      rightEndCompactionSourceTape
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          (bit :: rest) (none :: padding)) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape
      (bit :: rest) (none :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape_cons_some
    (bit : Bool) (rest : Word Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        (bit :: rest) (some padBit :: padding) =
      rightEndCompactionSourceTape
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          (bit :: rest) (some padBit :: padding)) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape
      (bit :: rest) (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          bits padding) =
      none ::
        List.append
          (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
            bits padding)
          [none, none] := by
  rw [selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells]
  simp [selectedSegmentLogicalTapeDecoderDensifierSourceCells]

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_eq_paddingPreserving
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          bits padding) =
      List.append (bits.map some) (none :: padding) := by
  rw [selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells]
  rfl

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint_nil_nil :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] []) =
      none ::
        List.append
          (selectedSegmentLogicalTapeDecoderDensifierFootprintCells [] [])
          [none, none] := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint
      [] []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint_nil_none
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (none :: padding)) =
      none ::
        List.append
          (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
            [] (none :: padding))
          [none, none] := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint
      [] (none :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint_nil_some
    (padBit : Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (some padBit :: padding)) =
      none ::
        List.append
          (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
            [] (some padBit :: padding))
          [none, none] := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint
      [] (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint_cons_nil
    (bit : Bool) (rest : Word Bool) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) []) =
      none ::
        List.append
          (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
            (bit :: rest) [])
          [none, none] := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint
      (bit :: rest) []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint_cons_none
    (bit : Bool) (rest : Word Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (none :: padding)) =
      none ::
        List.append
          (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
            (bit :: rest) (none :: padding))
          [none, none] := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint
      (bit :: rest) (none :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint_cons_some
    (bit : Bool) (rest : Word Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (some padBit :: padding)) =
      none ::
        List.append
          (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
            (bit :: rest) (some padBit :: padding))
          [none, none] := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint
      (bit :: rest) (some padBit :: padding)

theorem rightEndCompactionSourceTape_selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells_cells_eq_footprint
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.cells
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            bits padding)) =
      none ::
        List.append
          (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
            bits padding)
          [none, none] := by
  rw [← selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape,
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint]

theorem rightEndCompactionSourceTape_selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells_cells_eq_footprint_nil_nil :
    Tape.cells
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            [] [])) =
      none ::
        List.append
          (selectedSegmentLogicalTapeDecoderDensifierFootprintCells [] [])
          [none, none] := by
  exact
    rightEndCompactionSourceTape_selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells_cells_eq_footprint
      [] []

theorem rightEndCompactionSourceTape_selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells_cells_eq_footprint_nil_none
    (padding : List (Option Bool)) :
    Tape.cells
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            [] (none :: padding))) =
      none ::
        List.append
          (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
            [] (none :: padding))
          [none, none] := by
  exact
    rightEndCompactionSourceTape_selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells_cells_eq_footprint
      [] (none :: padding)

theorem rightEndCompactionSourceTape_selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells_cells_eq_footprint_nil_some
    (padBit : Bool) (padding : List (Option Bool)) :
    Tape.cells
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            [] (some padBit :: padding))) =
      none ::
        List.append
          (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
            [] (some padBit :: padding))
          [none, none] := by
  exact
    rightEndCompactionSourceTape_selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells_cells_eq_footprint
      [] (some padBit :: padding)

theorem rightEndCompactionSourceTape_selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells_cells_eq_footprint_cons_nil
    (bit : Bool) (rest : Word Bool) :
    Tape.cells
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            (bit :: rest) [])) =
      none ::
        List.append
          (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
            (bit :: rest) [])
          [none, none] := by
  exact
    rightEndCompactionSourceTape_selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells_cells_eq_footprint
      (bit :: rest) []

theorem rightEndCompactionSourceTape_selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells_cells_eq_footprint_cons_none
    (bit : Bool) (rest : Word Bool) (padding : List (Option Bool)) :
    Tape.cells
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            (bit :: rest) (none :: padding))) =
      none ::
        List.append
          (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
            (bit :: rest) (none :: padding))
          [none, none] := by
  exact
    rightEndCompactionSourceTape_selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells_cells_eq_footprint
      (bit :: rest) (none :: padding)

theorem rightEndCompactionSourceTape_selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells_cells_eq_footprint_cons_some
    (bit : Bool) (rest : Word Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            (bit :: rest) (some padBit :: padding))) =
      none ::
        List.append
          (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
            (bit :: rest) (some padBit :: padding))
          [none, none] := by
  exact
    rightEndCompactionSourceTape_selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells_cells_eq_footprint
      (bit :: rest) (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_eq_paddingPreserving_nil_nil :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] []) =
      List.append ([].map some) (none :: []) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_eq_paddingPreserving
      [] []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_eq_paddingPreserving_nil_none
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] (none :: padding)) =
      List.append ([].map some) (none :: none :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_eq_paddingPreserving
      [] (none :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_eq_paddingPreserving_nil_some
    (padBit : Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] (some padBit :: padding)) =
      List.append ([].map some) (none :: some padBit :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_eq_paddingPreserving
      [] (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_eq_paddingPreserving_cons_nil
    (bit : Bool) (rest : Word Bool) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) []) =
      List.append ((bit :: rest).map some) (none :: []) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_eq_paddingPreserving
      (bit :: rest) []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_eq_paddingPreserving_cons_none
    (bit : Bool) (rest : Word Bool) (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) (none :: padding)) =
      List.append ((bit :: rest).map some) (none :: none :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_eq_paddingPreserving
      (bit :: rest) (none :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_eq_paddingPreserving_cons_some
    (bit : Bool) (rest : Word Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) (some padBit :: padding)) =
      List.append ((bit :: rest).map some)
        (none :: some padBit :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_eq_paddingPreserving
      (bit :: rest) (some padBit :: padding)

theorem rightEdgeRewindSourceTape_cells_eq_paddingPreserving
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.cells (rightEdgeRewindSourceTape bits padding) =
      List.append (bits.map some) (none :: padding) := by
  exact rightEdgeRewindSourceTape_cells bits padding

theorem rightEdgeRewindSourceTape_cells_eq_paddingPreserving_nil_nil :
    Tape.cells (rightEdgeRewindSourceTape [] []) =
      List.append ([].map some) (none :: []) := by
  exact rightEdgeRewindSourceTape_cells_eq_paddingPreserving [] []

theorem rightEdgeRewindSourceTape_cells_eq_paddingPreserving_nil_none
    (padding : List (Option Bool)) :
    Tape.cells (rightEdgeRewindSourceTape [] (none :: padding)) =
      List.append ([].map some) (none :: none :: padding) := by
  exact rightEdgeRewindSourceTape_cells_eq_paddingPreserving
    [] (none :: padding)

theorem rightEdgeRewindSourceTape_cells_eq_paddingPreserving_nil_some
    (padBit : Bool) (padding : List (Option Bool)) :
    Tape.cells (rightEdgeRewindSourceTape [] (some padBit :: padding)) =
      List.append ([].map some) (none :: some padBit :: padding) := by
  exact rightEdgeRewindSourceTape_cells_eq_paddingPreserving
    [] (some padBit :: padding)

theorem rightEdgeRewindSourceTape_cells_eq_paddingPreserving_cons_nil
    (bit : Bool) (rest : Word Bool) :
    Tape.cells (rightEdgeRewindSourceTape (bit :: rest) []) =
      List.append ((bit :: rest).map some) (none :: []) := by
  exact rightEdgeRewindSourceTape_cells_eq_paddingPreserving
    (bit :: rest) []

theorem rightEdgeRewindSourceTape_cells_eq_paddingPreserving_cons_none
    (bit : Bool) (rest : Word Bool) (padding : List (Option Bool)) :
    Tape.cells (rightEdgeRewindSourceTape (bit :: rest) (none :: padding)) =
      List.append ((bit :: rest).map some) (none :: none :: padding) := by
  exact rightEdgeRewindSourceTape_cells_eq_paddingPreserving
    (bit :: rest) (none :: padding)

theorem rightEdgeRewindSourceTape_cells_eq_paddingPreserving_cons_some
    (bit : Bool) (rest : Word Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (rightEdgeRewindSourceTape
          (bit :: rest) (some padBit :: padding)) =
      List.append ((bit :: rest).map some)
        (none :: some padBit :: padding) := by
  exact rightEdgeRewindSourceTape_cells_eq_paddingPreserving
    (bit :: rest) (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderCellCells_length
    (cell : Option Bool) :
    (selectedSegmentLogicalTapeDecoderCellCells cell).length = 2 := by
  cases cell with
  | none =>
      rfl
  | some bit =>
      cases bit <;> rfl

theorem list_map_const_two_sum {α : Type} (xs : List α) :
    (xs.map (fun _ => 2)).sum = 2 * xs.length := by
  induction xs with
  | nil =>
      rfl
  | cons _ rest ih =>
      change 2 + (rest.map (fun _ => 2)).sum =
        2 * (rest.length + 1)
      rw [ih]
      lia

theorem selectedSegmentLogicalTapeDecoderCellCells_length_sum
    (cells : List (Option Bool)) :
    (cells.map
        (fun cell =>
          (selectedSegmentLogicalTapeDecoderCellCells cell).length)).sum =
      2 * cells.length := by
  simpa [selectedSegmentLogicalTapeDecoderCellCells_length] using
    (list_map_const_two_sum cells)

theorem selectedSegmentLogicalTapeDecoderCellCells_length_comp_sum
    (cells : List (Option Bool)) :
    (List.map
        (List.length ∘ selectedSegmentLogicalTapeDecoderCellCells)
        cells).sum =
      2 * cells.length := by
  simpa [Function.comp_def] using
    selectedSegmentLogicalTapeDecoderCellCells_length_sum cells

theorem selectedSegmentLogicalTapeDecoderCellCells_some_length_comp_sum
    (bits : Word Bool) :
    (List.map
        (List.length ∘ selectedSegmentLogicalTapeDecoderCellCells ∘ some)
        bits).sum =
      2 * bits.length := by
  simpa [Function.comp_def,
    selectedSegmentLogicalTapeDecoderCellCells_length] using
    (list_map_const_two_sum bits)

theorem selectedSegmentLogicalTapeDecoderCellCells_flatten_length
    (cells : List (Option Bool)) :
    ((cells.map selectedSegmentLogicalTapeDecoderCellCells).flatten).length =
      2 * cells.length := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      simp [selectedSegmentLogicalTapeDecoderCellCells_length, ih]
      lia

theorem selectedSegmentLogicalTapeDecoderCellCells_flatten_length_append_none
    (padding : List (Option Bool)) :
    ((List.map selectedSegmentLogicalTapeDecoderCellCells
        (List.append padding [none])).flatten).length =
      2 * padding.length + 2 := by
  rw [selectedSegmentLogicalTapeDecoderCellCells_flatten_length]
  simp
  lia

theorem selectedSegmentLogicalTapeDecoderCellCells_flatten_length_rest_padding
    (rest : Word Bool) (padding : List (Option Bool)) :
    ((List.map selectedSegmentLogicalTapeDecoderCellCells
        (List.append (rest.map some)
          (none :: List.append padding [none]))).flatten).length =
      2 * rest.length + 2 * padding.length + 4 := by
  rw [selectedSegmentLogicalTapeDecoderCellCells_flatten_length]
  simp
  lia

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintCells_length
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderDensifierFootprintCells
      bits padding).length =
      10 + 2 * bits.length + 2 * padding.length := by
  cases bits with
  | nil =>
      simp [selectedSegmentLogicalTapeDecoderDensifierFootprintCells,
        selectedSegmentLogicalTapeDecoderCellCells_length,
        list_map_const_two_sum,
        Function.comp_def]
      lia
  | cons bit rest =>
      simp [selectedSegmentLogicalTapeDecoderDensifierFootprintCells,
        selectedSegmentLogicalTapeDecoderCellCells_length,
        list_map_const_two_sum,
        Function.comp_def, List.length_append]
      lia

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_length
    (bits : Word Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          bits padding)).length =
      13 + 2 * bits.length + 2 * padding.length := by
  rw [selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint]
  simp [selectedSegmentLogicalTapeDecoderDensifierFootprintCells_length]
  lia

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_length
    (bits : Word Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          bits padding)).length =
      bits.length + padding.length + 1 := by
  rw [selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_eq_paddingPreserving]
  simp
  lia

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap
    (bits : Word Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          bits padding)).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_eq_footprint]
  simp [selectedSegmentLogicalTapeDecoderDensifierFootprintCells_filterMap,
    List.filterMap_append]

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_filterMap
    (bits : Word Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          bits padding)).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_eq_paddingPreserving]
  exact
    selectedSegmentLogicalTapeDecoderDensifierPaddingPreservingCells_filterMap
      bits padding

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap_eq_targetTape_cells_filterMap
    (bits : Word Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          bits padding)).filterMap (fun cell => cell) =
      (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          bits padding)).filterMap (fun cell => cell) := by
  rw [selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap,
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_filterMap]

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap_eq_targetTape_cells_filterMap_nil_nil :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] [])).filterMap (fun cell => cell) =
      (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] [])).filterMap (fun cell => cell) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap_eq_targetTape_cells_filterMap
      [] []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap_eq_targetTape_cells_filterMap_nil_none
    (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (none :: padding))).filterMap (fun cell => cell) =
      (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] (none :: padding))).filterMap (fun cell => cell) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap_eq_targetTape_cells_filterMap
      [] (none :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap_eq_targetTape_cells_filterMap_nil_some
    (padBit : Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (some padBit :: padding))).filterMap (fun cell => cell) =
      (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] (some padBit :: padding))).filterMap (fun cell => cell) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap_eq_targetTape_cells_filterMap
      [] (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap_eq_targetTape_cells_filterMap_cons_nil
    (bit : Bool) (rest : Word Bool) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) [])).filterMap (fun cell => cell) =
      (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) [])).filterMap (fun cell => cell) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap_eq_targetTape_cells_filterMap
      (bit :: rest) []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap_eq_targetTape_cells_filterMap_cons_none
    (bit : Bool) (rest : Word Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (none :: padding))).filterMap (fun cell => cell) =
      (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) (none :: padding))).filterMap (fun cell => cell) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap_eq_targetTape_cells_filterMap
      (bit :: rest) (none :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap_eq_targetTape_cells_filterMap_cons_some
    (bit : Bool) (rest : Word Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (some padBit :: padding))).filterMap
        (fun cell => cell) =
      (Tape.cells
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) (some padBit :: padding))).filterMap
        (fun cell => cell) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap_eq_targetTape_cells_filterMap
      (bit :: rest) (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprint_normalizedOutput_eq_nil_nil :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] []) =
      Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] []) := by
  exact selectedSegmentLogicalTapeDecoderDensifierFootprint_normalizedOutput_eq
    [] []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprint_normalizedOutput_eq_nil_none
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (none :: padding)) =
      Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] (none :: padding)) := by
  exact selectedSegmentLogicalTapeDecoderDensifierFootprint_normalizedOutput_eq
    [] (none :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprint_normalizedOutput_eq_nil_some
    (padBit : Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (some padBit :: padding)) =
      Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] (some padBit :: padding)) := by
  exact selectedSegmentLogicalTapeDecoderDensifierFootprint_normalizedOutput_eq
    [] (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprint_normalizedOutput_eq_cons_nil
    (bit : Bool) (rest : Word Bool) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) []) =
      Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) []) := by
  exact selectedSegmentLogicalTapeDecoderDensifierFootprint_normalizedOutput_eq
    (bit :: rest) []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprint_normalizedOutput_eq_cons_none
    (bit : Bool) (rest : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (none :: padding)) =
      Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) (none :: padding)) := by
  exact selectedSegmentLogicalTapeDecoderDensifierFootprint_normalizedOutput_eq
    (bit :: rest) (none :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprint_normalizedOutput_eq_cons_some
    (bit : Bool) (rest : Word Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (some padBit :: padding)) =
      Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) (some padBit :: padding)) := by
  exact selectedSegmentLogicalTapeDecoderDensifierFootprint_normalizedOutput_eq
    (bit :: rest) (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        bits padding =
      rightEdgeRewindSourceTape bits padding := by
  rfl

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape_nil_nil :
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] [] =
      rightEdgeRewindSourceTape [] [] := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape
      [] []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape_nil_none
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] (none :: padding) =
      rightEdgeRewindSourceTape [] (none :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape
      [] (none :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape_nil_some
    (padBit : Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] (some padBit :: padding) =
      rightEdgeRewindSourceTape [] (some padBit :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape
      [] (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape_cons_nil
    (bit : Bool) (rest : Word Bool) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        (bit :: rest) [] =
      rightEdgeRewindSourceTape (bit :: rest) [] := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape
      (bit :: rest) []

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape_cons_none
    (bit : Bool) (rest : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        (bit :: rest) (none :: padding) =
      rightEdgeRewindSourceTape (bit :: rest) (none :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape
      (bit :: rest) (none :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape_cons_some
    (bit : Bool) (rest : Word Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        (bit :: rest) (some padBit :: padding) =
      rightEdgeRewindSourceTape (bit :: rest) (some padBit :: padding) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape
      (bit :: rest) (some padBit :: padding)

theorem rightEndCompactionSourceTape_selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells_cells_length
    (bits : Word Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            bits padding))).length =
      13 + 2 * bits.length + 2 * padding.length := by
  simpa [
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape] using
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_length
      bits padding

theorem rightEdgeRewindSourceTape_cells_length
    (bits : Word Bool) (padding : List (Option Bool)) :
    (Tape.cells (rightEdgeRewindSourceTape bits padding)).length =
      bits.length + padding.length + 1 := by
  simpa [
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape] using
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_length
      bits padding

theorem rightEndCompactionSourceTape_selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells_cells_filterMap
    (bits : Word Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            bits padding))).filterMap (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  simpa [
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape] using
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_cells_filterMap
      bits padding

theorem rightEdgeRewindSourceTape_cells_filterMap
    (bits : Word Bool) (padding : List (Option Bool)) :
    (Tape.cells (rightEdgeRewindSourceTape bits padding)).filterMap
        (fun cell => cell) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  simpa [
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape] using
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cells_filterMap
      bits padding

theorem rightEndCompactionSourceTape_selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells_cells_filterMap_eq_rightEdgeRewindSourceTape_cells_filterMap
    (bits : Word Bool) (padding : List (Option Bool)) :
    (Tape.cells
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            bits padding))).filterMap (fun cell => cell) =
      (Tape.cells (rightEdgeRewindSourceTape bits padding)).filterMap
        (fun cell => cell) := by
  rw [
    rightEndCompactionSourceTape_selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells_cells_filterMap,
    rightEdgeRewindSourceTape_cells_filterMap]

theorem rightEndCompactionSourceTape_selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells_normalizedOutput_eq_rightEdgeRewindSourceTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            bits padding)) =
      Tape.normalizedOutput
        (rightEdgeRewindSourceTape bits padding) := by
  simpa [
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape,
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape] using
    selectedSegmentLogicalTapeDecoderDensifierFootprint_normalizedOutput_eq
      bits padding

theorem rightEdgeRewindDescription_haltsFrom_selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    rightEdgeRewindDescription.HaltsFromTape
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        bits padding)
      (rightEdgeRewindTargetTape bits padding) := by
  simpa [selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape] using
    rightEdgeRewindDescription_haltsFromTape bits padding

theorem rightEdgeRewindDescription_haltsFrom_selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_nil_nil :
    rightEdgeRewindDescription.HaltsFromTape
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] [])
      (rightEdgeRewindTargetTape [] []) := by
  exact
    rightEdgeRewindDescription_haltsFrom_selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
      [] []

theorem rightEdgeRewindDescription_haltsFrom_selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_nil_none
    (padding : List (Option Bool)) :
    rightEdgeRewindDescription.HaltsFromTape
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] (none :: padding))
      (rightEdgeRewindTargetTape [] (none :: padding)) := by
  exact
    rightEdgeRewindDescription_haltsFrom_selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
      [] (none :: padding)

theorem rightEdgeRewindDescription_haltsFrom_selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_nil_some
    (padBit : Bool) (padding : List (Option Bool)) :
    rightEdgeRewindDescription.HaltsFromTape
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] (some padBit :: padding))
      (rightEdgeRewindTargetTape [] (some padBit :: padding)) := by
  exact
    rightEdgeRewindDescription_haltsFrom_selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
      [] (some padBit :: padding)

theorem rightEdgeRewindDescription_haltsFrom_selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cons_nil
    (bit : Bool) (rest : Word Bool) :
    rightEdgeRewindDescription.HaltsFromTape
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        (bit :: rest) [])
      (rightEdgeRewindTargetTape (bit :: rest) []) := by
  exact
    rightEdgeRewindDescription_haltsFrom_selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
      (bit :: rest) []

theorem rightEdgeRewindDescription_haltsFrom_selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cons_none
    (bit : Bool) (rest : Word Bool) (padding : List (Option Bool)) :
    rightEdgeRewindDescription.HaltsFromTape
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        (bit :: rest) (none :: padding))
      (rightEdgeRewindTargetTape (bit :: rest) (none :: padding)) := by
  exact
    rightEdgeRewindDescription_haltsFrom_selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
      (bit :: rest) (none :: padding)

theorem rightEdgeRewindDescription_haltsFrom_selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_cons_some
    (bit : Bool) (rest : Word Bool) (padBit : Bool)
    (padding : List (Option Bool)) :
    rightEdgeRewindDescription.HaltsFromTape
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        (bit :: rest) (some padBit :: padding))
      (rightEdgeRewindTargetTape (bit :: rest) (some padBit :: padding)) := by
  exact
    rightEdgeRewindDescription_haltsFrom_selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
      (bit :: rest) (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_nil_source_equiv_target :
    Tape.Equiv
      (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] [])
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] []) := by
  simp [Tape.Equiv,
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape,
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape,
    selectedSegmentLogicalTapeDecoderTargetTape,
    rightEdgeScanSourceTapeFromLeft, rightEdgeRewindSourceTape,
    FSTStatefulOptionAppendTargetTapeFromLeft,
    statefulOptionAppendWriteTargetTapeAtBlank, tapeAtCells,
    statefulOptionCellsFrom, logicalTapeBits, logicalCellListBits,
    logicalCellBits, guardLogicalTape,
    selectedSegmentLogicalTapeDecoderStart,
    selectedSegmentLogicalTapeDecoderNext,
    selectedSegmentLogicalTapeDecoderEmit,
    Tape.dropTrailingNone]

theorem exactIdentityDescription_haltsFromTapeEquiv_selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_nil :
    ExactIdentityDescription.HaltsFromTapeEquiv
      (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] [])
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] []) := by
  refine
    ⟨selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
      [] [], ?_, ?_⟩
  · refine ⟨0, ?_⟩
    constructor <;> rfl
  · exact
      selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_nil_source_equiv_target

theorem selectedSegmentLogicalTapeDecoder_statefulCells_logicalCellListBits_replicate_none_dropTrailingNone
    (n suffixWidth : Nat) :
    Tape.dropTrailingNone
        (List.append
          (statefulOptionCellsFrom selectedSegmentLogicalTapeDecoderNext
            selectedSegmentLogicalTapeDecoderEmit
            selectedSegmentLogicalTapeDecoderStart
            (List.append
              (logicalCellListBits
                (List.replicate n (none : Option Bool)))
              [false, false])).reverse
          (List.replicate suffixWidth (none : Option Bool))) =
      [] := by
  induction n generalizing suffixWidth with
  | zero =>
      simpa [statefulOptionCellsFrom, logicalCellListBits,
        selectedSegmentLogicalTapeDecoderStart,
        selectedSegmentLogicalTapeDecoderNext,
        selectedSegmentLogicalTapeDecoderEmit, List.replicate_succ,
        Nat.add_assoc] using
        FoC.Computability.dropTrailingNone_replicate_none
          (suffixWidth + 2)
  | succ n ih =>
      simpa [List.replicate_succ, logicalCellListBits, logicalCellBits,
        statefulOptionCellsFrom, selectedSegmentLogicalTapeDecoderStart,
        selectedSegmentLogicalTapeDecoderNext,
        selectedSegmentLogicalTapeDecoderEmit, Nat.add_assoc] using
        ih (suffixWidth + 2)

theorem selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_replicate_none_source_equiv_target
    (n : Nat) :
    Tape.Equiv
      (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] (List.replicate n (none : Option Bool)))
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] (List.replicate n (none : Option Bool))) := by
  induction n with
  | zero =>
      simpa using
        selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_nil_source_equiv_target
  | succ n _ih =>
      simp [Tape.Equiv,
        selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape,
        selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape,
        selectedSegmentLogicalTapeDecoderTargetTape,
        rightEdgeScanSourceTapeFromLeft, rightEdgeRewindSourceTape,
        FSTStatefulOptionAppendTargetTapeFromLeft,
        statefulOptionAppendWriteTargetTapeAtBlank, tapeAtCells,
        statefulOptionCellsFrom, logicalTapeBits, logicalCellListBits,
        logicalCellBits, guardLogicalTape,
        selectedSegmentLogicalTapeDecoderStart,
        selectedSegmentLogicalTapeDecoderNext,
        selectedSegmentLogicalTapeDecoderEmit,
        FoC.Computability.dropTrailingNone_replicate_none,
        Tape.dropTrailingNone]
      simpa using
        selectedSegmentLogicalTapeDecoder_statefulCells_logicalCellListBits_replicate_none_dropTrailingNone
          (n + 1) 9

theorem exactIdentityDescription_haltsFromTapeEquiv_selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_replicate_none
    (n : Nat) :
    ExactIdentityDescription.HaltsFromTapeEquiv
      (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] (List.replicate n (none : Option Bool)))
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] (List.replicate n (none : Option Bool))) := by
  refine
    ⟨selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
      [] (List.replicate n (none : Option Bool)), ?_, ?_⟩
  · refine ⟨0, ?_⟩
    constructor <;> rfl
  · exact
      selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_replicate_none_source_equiv_target
        n

theorem optionList_eq_replicate_none_of_filterMap_eq_nil
    (padding : List (Option Bool))
    (hpadding : padding.filterMap (fun cell => cell) = []) :
    exists n : Nat, padding = List.replicate n (none : Option Bool) := by
  induction padding with
  | nil =>
      exact ⟨0, rfl⟩
  | cons cell rest ih =>
      cases cell with
      | none =>
          have hrest : rest.filterMap (fun cell => cell) = [] := by
            simpa using hpadding
          rcases ih hrest with ⟨n, hn⟩
          exact ⟨n + 1, by simp [hn, List.replicate_succ]⟩
      | some _bit =>
          simp at hpadding

theorem selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_blank_padding_source_equiv_target
    (padding : List (Option Bool))
    (hpadding : padding.filterMap (fun cell => cell) = []) :
    Tape.Equiv
      (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] padding)
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] padding) := by
  rcases optionList_eq_replicate_none_of_filterMap_eq_nil
      padding hpadding with
    ⟨n, rfl⟩
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_replicate_none_source_equiv_target
      n

theorem exactIdentityDescription_haltsFromTapeEquiv_selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_blank_padding
    (padding : List (Option Bool))
    (hpadding : padding.filterMap (fun cell => cell) = []) :
    ExactIdentityDescription.HaltsFromTapeEquiv
      (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] padding)
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] padding) := by
  refine
    ⟨selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
      [] padding, ?_, ?_⟩
  · refine ⟨0, ?_⟩
    constructor <;> rfl
  · exact
      selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_blank_padding_source_equiv_target
        padding hpadding

theorem selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_none_blank_padding_source_equiv_target
    (padding : List (Option Bool))
    (hpadding : padding.filterMap (fun cell => cell) = []) :
    Tape.Equiv
      (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] (none :: padding))
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] (none :: padding)) := by
  exact
    selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_blank_padding_source_equiv_target
      (none :: padding) (by simp [hpadding])

theorem exactIdentityDescription_haltsFromTapeEquiv_selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_none_blank_padding
    (padding : List (Option Bool))
    (hpadding : padding.filterMap (fun cell => cell) = []) :
    ExactIdentityDescription.HaltsFromTapeEquiv
      (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] (none :: padding))
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] (none :: padding)) := by
  exact
    exactIdentityDescription_haltsFromTapeEquiv_selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_blank_padding
      (none :: padding) (by simp [hpadding])

def SelectedSegmentLogicalTapeDecoderFootprintCompactorBlankPaddingCaseSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    compactor.HaltsFromTapeEquiv
      (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] [])
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] []) ∧
    forall padding : List (Option Bool),
      padding.filterMap (fun cell => cell) = [] →
        compactor.HaltsFromTapeEquiv
          (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
            [] (none :: padding))
          (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
            [] (none :: padding))

def SelectedSegmentLogicalTapeDecoderFootprintCompactorBlankPaddingCaseConstruction :
    Prop :=
  exists compactor : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintCompactorBlankPaddingCaseSpec
      compactor

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorBlankPaddingCaseConstruction_core :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorBlankPaddingCaseConstruction := by
  refine
    ⟨ExactIdentityDescription,
      CommonGround.Identity.exactIdentityDescription_subroutineReady,
      ?_, ?_⟩
  · exact
      exactIdentityDescription_haltsFromTapeEquiv_selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_nil
  · intro padding hpadding
    exact
      exactIdentityDescription_haltsFromTapeEquiv_selectedSegmentLogicalTapeDecoderDensifierFootprint_nil_none_blank_padding
        padding hpadding

def SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeBlankPaddingCaseSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    compactor.HaltsFromTapeEquiv
      (rightEndCompactionSourceTape
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          [] []))
      (rightEdgeRewindSourceTape [] []) ∧
    forall padding : List (Option Bool),
      padding.filterMap (fun cell => cell) = [] →
        compactor.HaltsFromTapeEquiv
          (rightEndCompactionSourceTape
            (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
              [] (none :: padding)))
          (rightEdgeRewindSourceTape [] (none :: padding))

def SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeBlankPaddingCaseConstruction :
    Prop :=
  exists compactor : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeBlankPaddingCaseSpec
      compactor

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeBlankPaddingCaseConstruction_of_blankPaddingCase
    (hblank :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorBlankPaddingCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeBlankPaddingCaseConstruction := by
  rcases hblank with ⟨compactor, hready, hnilNil, hnilNone⟩
  refine ⟨compactor, hready, ?_, ?_⟩
  · simpa [
      selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape_nil_nil,
      selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape_nil_nil] using
      hnilNil
  · intro padding hpadding
    simpa [
      selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape_nil_none,
      selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape_nil_none] using
      hnilNone padding hpadding

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeBlankPaddingCaseConstruction_core :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeBlankPaddingCaseConstruction := by
  exact
    selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeBlankPaddingCaseConstruction_of_blankPaddingCase
      selectedSegmentLogicalTapeDecoderFootprintCompactorBlankPaddingCaseConstruction_core

def SelectedSegmentLogicalTapeDecoderFootprintCompactorPadSymbolCaseSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    compactor.HaltsFromTapeEquiv
      (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] [])
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] []) ∧
    (forall padding : List (Option Bool),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (none :: padding))
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] (none :: padding))) ∧
    (forall (padBit : Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] (some padBit :: padding))) ∧
    (forall (bit : Bool) (rest : Word Bool),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) [])
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) [])) ∧
    (forall (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (none :: padding))
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) (none :: padding))) ∧
    forall (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderFootprintCompactorPadSymbolCaseConstruction :
    Prop :=
  exists compactor : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintCompactorPadSymbolCaseSpec
      compactor

def SelectedSegmentLogicalTapeDecoderFootprintCompactorNilPadSymbolCaseSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    compactor.HaltsFromTapeEquiv
      (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] [])
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] []) ∧
    (forall padding : List (Option Bool),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (none :: padding))
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] (none :: padding))) ∧
    forall (padBit : Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          [] (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderFootprintCompactorConsPadSymbolCaseSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    (forall (bit : Bool) (rest : Word Bool),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) [])
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) [])) ∧
    (forall (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (none :: padding))
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) (none :: padding))) ∧
    forall (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
          (bit :: rest) (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderFootprintCompactorSplitPadSymbolCaseSpec
    (compactor : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderFootprintCompactorNilPadSymbolCaseSpec
      compactor ∧
    SelectedSegmentLogicalTapeDecoderFootprintCompactorConsPadSymbolCaseSpec
      compactor

def SelectedSegmentLogicalTapeDecoderFootprintCompactorSplitPadSymbolCaseConstruction :
    Prop :=
  exists compactor : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintCompactorSplitPadSymbolCaseSpec
      compactor

def SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    compactor.HaltsFromTapeEquiv
      (rightEndCompactionSourceTape
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          [] []))
      (rightEdgeRewindSourceTape [] []) ∧
    (forall padding : List (Option Bool),
      compactor.HaltsFromTapeEquiv
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            [] (none :: padding)))
        (rightEdgeRewindSourceTape [] (none :: padding))) ∧
    (forall (padBit : Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            [] (some padBit :: padding)))
        (rightEdgeRewindSourceTape [] (some padBit :: padding))) ∧
    (forall (bit : Bool) (rest : Word Bool),
      compactor.HaltsFromTapeEquiv
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            (bit :: rest) []))
        (rightEdgeRewindSourceTape (bit :: rest) [])) ∧
    (forall (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            (bit :: rest) (none :: padding)))
        (rightEdgeRewindSourceTape (bit :: rest) (none :: padding))) ∧
    forall (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            (bit :: rest) (some padBit :: padding)))
        (rightEdgeRewindSourceTape
          (bit :: rest) (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConstruction :
    Prop :=
  exists compactor : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSpec
      compactor

def SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeNilSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    compactor.HaltsFromTapeEquiv
      (rightEndCompactionSourceTape
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          [] []))
      (rightEdgeRewindSourceTape [] []) ∧
    (forall padding : List (Option Bool),
      compactor.HaltsFromTapeEquiv
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            [] (none :: padding)))
        (rightEdgeRewindSourceTape [] (none :: padding))) ∧
    forall (padBit : Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            [] (some padBit :: padding)))
        (rightEdgeRewindSourceTape [] (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConsSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    (forall (bit : Bool) (rest : Word Bool),
      compactor.HaltsFromTapeEquiv
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            (bit :: rest) []))
        (rightEdgeRewindSourceTape (bit :: rest) [])) ∧
    (forall (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            (bit :: rest) (none :: padding)))
        (rightEdgeRewindSourceTape (bit :: rest) (none :: padding))) ∧
    forall (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            (bit :: rest) (some padBit :: padding)))
        (rightEdgeRewindSourceTape
          (bit :: rest) (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitSpec
    (compactor : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeNilSpec
      compactor ∧
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConsSpec
      compactor

def SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitConstruction :
    Prop :=
  exists compactor : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitSpec
      compactor

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorPadSymbolCaseConstruction_of_split
    (hsplit :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorSplitPadSymbolCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorPadSymbolCaseConstruction := by
  rcases hsplit with ⟨compactor, hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  exact
    ⟨compactor, hready, hnilNil, hnilNone, hnilSome,
      hconsNil, hconsNone, hconsSome⟩

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction_of_padSymbolCases
    (hcases :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorPadSymbolCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction := by
  rcases hcases with
    ⟨compactor, hready, hnilNil, hnilNone, hnilSome, hconsNil,
      hconsNone, hconsSome⟩
  refine ⟨compactor, hready, hnilNil, ?_, hconsNil, ?_⟩
  · intro pad padding
    cases pad with
    | none =>
        exact hnilNone padding
    | some padBit =>
        exact hnilSome padBit padding
  · intro bit rest pad padding
    cases pad with
    | none =>
        exact hconsNone bit rest padding
    | some padBit =>
        exact hconsSome bit rest padBit padding

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorSplitPadSymbolCaseConstruction_of_rightEndBridge
    (hbridge :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorSplitPadSymbolCaseConstruction := by
  rcases hbridge with
    ⟨compactor, hready, hnilNil, hnilNone, hnilSome, hconsNil,
      hconsNone, hconsSome⟩
  refine ⟨compactor, ?_, ?_⟩
  · refine ⟨hready, ?_, ?_, ?_⟩
    · simpa [
        selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape_nil_nil,
        selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape_nil_nil] using
        hnilNil
    · intro padding
      simpa [
        selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape_nil_none,
        selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape_nil_none] using
        hnilNone padding
    · intro padBit padding
      simpa [
        selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape_nil_some,
        selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape_nil_some] using
        hnilSome padBit padding
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro bit rest
      simpa [
        selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape_cons_nil,
        selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape_cons_nil] using
        hconsNil bit rest
    · intro bit rest padding
      simpa [
        selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape_cons_none,
        selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape_cons_none] using
        hconsNone bit rest padding
    · intro bit rest padBit padding
      simpa [
        selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape_cons_some,
        selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape_cons_some] using
        hconsSome bit rest padBit padding

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConstruction_of_split
    (hsplit :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConstruction := by
  rcases hsplit with ⟨compactor, hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  exact
    ⟨compactor, hready, hnilNil, hnilNone, hnilSome,
      hconsNil, hconsNone, hconsSome⟩

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitConstruction_core :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitConstruction := by
  sorry

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConstruction_core :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConstruction := by
  exact
    selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConstruction_of_split
      selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitConstruction_core

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorSplitPadSymbolCaseConstruction_core :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorSplitPadSymbolCaseConstruction := by
  exact
    selectedSegmentLogicalTapeDecoderFootprintCompactorSplitPadSymbolCaseConstruction_of_rightEndBridge
      selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConstruction_core

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorPadSymbolCaseConstruction_core :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorPadSymbolCaseConstruction := by
  exact
    selectedSegmentLogicalTapeDecoderFootprintCompactorPadSymbolCaseConstruction_of_split
      selectedSegmentLogicalTapeDecoderFootprintCompactorSplitPadSymbolCaseConstruction_core

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction_core :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction := by
  exact
    selectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction_of_padSymbolCases
      selectedSegmentLogicalTapeDecoderFootprintCompactorPadSymbolCaseConstruction_core

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction_core :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction := by
  exact
    selectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction_of_bitPaddingCases
      selectedSegmentLogicalTapeDecoderFootprintCompactorBitPaddingCaseConstruction_core

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorConstruction_core :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorConstruction := by
  exact
    selectedSegmentLogicalTapeDecoderFootprintCompactorConstruction_of_cases
      selectedSegmentLogicalTapeDecoderFootprintCompactorCaseConstruction_core


end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
