import FoC.Computability.Compiler.DescriptionExecution
import FoC.Computability.Compiler.Structured.Lowering.Composition
import FoC.Computability.Compiler.Structured.Lowering.PairEncodedOptionCellCompactor
import FoC.Computability.Compiler.Structured.HeadRoutes.Endpoints
import FoC.Computability.Compiler.Structured.HeadRoutes
import FoC.Computability.Compiler.ClosedCfg.ProjTail.SelectedFootprintCompactionPaddingOutput

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

theorem rightEdgeRewindSourceTape_cells_eq_paddingPreserving
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.cells (rightEdgeRewindSourceTape bits padding) =
      List.append (bits.map some) (none :: padding) := by
  exact rightEdgeRewindSourceTape_cells bits padding

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
      simp [ih]
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
        list_map_const_two_sum,
        Function.comp_def]
      lia
  | cons bit rest =>
      simp [selectedSegmentLogicalTapeDecoderDensifierFootprintCells,
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

theorem selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        bits padding =
      rightEdgeRewindSourceTape bits padding := by
  rfl

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

theorem rightEndSource_cells_filterMap_eq_rewindSource
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

theorem rightEndSource_normalizedOutput_eq_rewindSource
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
      selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape,
      selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape] using
      hnilNil
  · intro padding hpadding
    simpa [
      selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape,
      selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape] using
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

/--
Generic selected-footprint bridge contract.

This is the reusable spine behind the nil/cons and padding split contracts
below: a single machine compacts every selected logical-tape decoder footprint
from the right-end compaction source shape to the selected rewind source shape,
up to tape equivalence.
-/
def SelectedFootprintCompactorBridgeSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    forall (bits : Word Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            bits padding))
        (rightEdgeRewindSourceTape bits padding)

def SelectedFootprintCompactorBridgeConstruction : Prop :=
  exists compactor : MachineDescription,
    SelectedFootprintCompactorBridgeSpec compactor

def SelectedSegmentLogicalTapeDecoderFootprintCompactorOutputSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    forall (bits : Word Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          bits padding)
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
            bits padding))

def SelectedSegmentLogicalTapeDecoderFootprintCompactorOutputConstruction :
    Prop :=
  exists compactor : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintCompactorOutputSpec
      compactor

/--
Normalized-output version of {name}`SelectedFootprintCompactorBridgeSpec`.
It deliberately forgets the final head position while preserving the decoded
selected-footprint output.
-/
def SelectedFootprintCompactorBridgeOutputSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    forall (bits : Word Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeWithOutput
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            bits padding))
        (Tape.normalizedOutput
          (rightEdgeRewindSourceTape bits padding))

def SelectedFootprintCompactorBridgeOutputConstruction : Prop :=
  exists compactor : MachineDescription,
    SelectedFootprintCompactorBridgeOutputSpec compactor

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorOutputSpec_of_exact
    {compactor : MachineDescription}
    (hcompactor :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorSpec
        compactor) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorOutputSpec
      compactor := by
  rcases hcompactor with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  rcases hrun bits padding with ⟨actual, hhalt, hequiv⟩
  have houtput :=
    MachineDescription.haltsFromTapeWithOutput_of_haltsFromTape hhalt
  rw [Tape.Equiv.normalizedOutput_eq hequiv] at houtput
  exact houtput

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorOutputConstruction_of_exact
    (hcompactor :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorOutputConstruction := by
  rcases hcompactor with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedSegmentLogicalTapeDecoderFootprintCompactorOutputSpec_of_exact
        hspec⟩

theorem selectedFootprintCompactorBridgeOutputSpec_of_exact
    {compactor : MachineDescription}
    (hcompactor :
      SelectedFootprintCompactorBridgeSpec compactor) :
    SelectedFootprintCompactorBridgeOutputSpec compactor := by
  rcases hcompactor with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  rcases hrun bits padding with ⟨actual, hhalt, hequiv⟩
  have houtput :=
    MachineDescription.haltsFromTapeWithOutput_of_haltsFromTape hhalt
  rw [Tape.Equiv.normalizedOutput_eq hequiv] at houtput
  exact houtput

theorem selectedFootprintCompactorBridgeOutputConstruction_of_exact
    (hbridge : SelectedFootprintCompactorBridgeConstruction) :
    SelectedFootprintCompactorBridgeOutputConstruction := by
  rcases hbridge with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedFootprintCompactorBridgeOutputSpec_of_exact hspec⟩

theorem selectedFootprintCompactorBridgeOutputSpec_of_compactorOutputSpec
    {compactor : MachineDescription}
    (hcompactor :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorOutputSpec
        compactor) :
    SelectedFootprintCompactorBridgeOutputSpec compactor := by
  rcases hcompactor with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  simpa [
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape,
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape] using
    hrun bits padding

theorem selectedFootprintCompactorBridgeOutputConstruction_of_compactorOutput
    (hcompactor :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorOutputConstruction) :
    SelectedFootprintCompactorBridgeOutputConstruction := by
  rcases hcompactor with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedFootprintCompactorBridgeOutputSpec_of_compactorOutputSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorOutputSpec_of_bridgeOutputSpec
    {compactor : MachineDescription}
    (hbridge : SelectedFootprintCompactorBridgeOutputSpec compactor) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorOutputSpec
      compactor := by
  rcases hbridge with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  simpa [
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape,
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape] using
    hrun bits padding

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorOutputConstruction_of_bridgeOutput
    (hbridge : SelectedFootprintCompactorBridgeOutputConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorOutputConstruction := by
  rcases hbridge with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedSegmentLogicalTapeDecoderFootprintCompactorOutputSpec_of_bridgeOutputSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorOutputSpec_iff_bridgeOutputSpec
    (compactor : MachineDescription) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorOutputSpec compactor ↔
      SelectedFootprintCompactorBridgeOutputSpec compactor := by
  constructor
  · exact selectedFootprintCompactorBridgeOutputSpec_of_compactorOutputSpec
  · exact selectedSegmentLogicalTapeDecoderFootprintCompactorOutputSpec_of_bridgeOutputSpec

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorOutputConstruction_iff_bridgeOutputConstruction :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorOutputConstruction ↔
      SelectedFootprintCompactorBridgeOutputConstruction := by
  constructor
  · exact selectedFootprintCompactorBridgeOutputConstruction_of_compactorOutput
  · exact selectedSegmentLogicalTapeDecoderFootprintCompactorOutputConstruction_of_bridgeOutput

theorem selectedFootprintCompactorBridgeSpec_of_compactorSpec
    {compactor : MachineDescription}
    (hcompactor :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorSpec
        compactor) :
    SelectedFootprintCompactorBridgeSpec compactor := by
  rcases hcompactor with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  simpa [
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape,
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape] using
    hrun bits padding

theorem selectedFootprintCompactorBridgeConstruction_of_compactor
    (hcompactor :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorConstruction) :
    SelectedFootprintCompactorBridgeConstruction := by
  rcases hcompactor with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedFootprintCompactorBridgeSpec_of_compactorSpec hspec⟩

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorSpec_of_bridgeSpec
    {compactor : MachineDescription}
    (hbridge : SelectedFootprintCompactorBridgeSpec compactor) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorSpec
      compactor := by
  rcases hbridge with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  simpa [
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape,
    selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape] using
    hrun bits padding

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorConstruction_of_bridge
    (hbridge : SelectedFootprintCompactorBridgeConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorConstruction := by
  rcases hbridge with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedSegmentLogicalTapeDecoderFootprintCompactorSpec_of_bridgeSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorSpec_iff_bridgeSpec
    (compactor : MachineDescription) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorSpec compactor ↔
      SelectedFootprintCompactorBridgeSpec compactor := by
  constructor
  · exact selectedFootprintCompactorBridgeSpec_of_compactorSpec
  · exact selectedSegmentLogicalTapeDecoderFootprintCompactorSpec_of_bridgeSpec

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorConstruction_iff_bridgeConstruction :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorConstruction ↔
      SelectedFootprintCompactorBridgeConstruction := by
  constructor
  · exact selectedFootprintCompactorBridgeConstruction_of_compactor
  · exact selectedSegmentLogicalTapeDecoderFootprintCompactorConstruction_of_bridge

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSpec_of_bridgeSpec
    {compactor : MachineDescription}
    (hbridge : SelectedFootprintCompactorBridgeSpec compactor) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSpec
      compactor := by
  rcases hbridge with ⟨hready, hrun⟩
  refine ⟨hready, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hrun [] []
  · intro padding
    exact hrun [] (none :: padding)
  · intro padBit padding
    exact hrun [] (some padBit :: padding)
  · intro bit rest
    exact hrun (bit :: rest) []
  · intro bit rest padding
    exact hrun (bit :: rest) (none :: padding)
  · intro bit rest padBit padding
    exact hrun (bit :: rest) (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConstruction_of_bridge
    (hbridge : SelectedFootprintCompactorBridgeConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConstruction := by
  rcases hbridge with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSpec_of_bridgeSpec
        hspec⟩

theorem selectedFootprintCompactorBridgeSpec_of_rightEndBridgeSpec
    {compactor : MachineDescription}
    (hbridge :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSpec
        compactor) :
    SelectedFootprintCompactorBridgeSpec compactor := by
  rcases hbridge with
    ⟨hready, hnilNil, hnilNone, hnilSome, hconsNil,
      hconsNone, hconsSome⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  cases bits with
  | nil =>
      cases padding with
      | nil =>
          exact hnilNil
      | cons pad padding =>
          cases pad with
          | none =>
              exact hnilNone padding
          | some padBit =>
              exact hnilSome padBit padding
  | cons bit rest =>
      cases padding with
      | nil =>
          exact hconsNil bit rest
      | cons pad padding =>
          cases pad with
          | none =>
              exact hconsNone bit rest padding
          | some padBit =>
              exact hconsSome bit rest padBit padding

theorem selectedFootprintCompactorBridgeConstruction_of_rightEndBridge
    (hbridge :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConstruction) :
    SelectedFootprintCompactorBridgeConstruction := by
  rcases hbridge with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedFootprintCompactorBridgeSpec_of_rightEndBridgeSpec hspec⟩

theorem selectedFootprintCompactorBridgeSpec_iff_rightEndBridgeSpec
    (compactor : MachineDescription) :
    SelectedFootprintCompactorBridgeSpec compactor ↔
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSpec
        compactor := by
  constructor
  · exact selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSpec_of_bridgeSpec
  · exact selectedFootprintCompactorBridgeSpec_of_rightEndBridgeSpec

theorem selectedFootprintCompactorBridgeConstruction_iff_rightEndBridgeConstruction :
    SelectedFootprintCompactorBridgeConstruction ↔
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConstruction := by
  constructor
  · exact selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConstruction_of_bridge
  · exact selectedFootprintCompactorBridgeConstruction_of_rightEndBridge

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

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeNilSpec_of_guardedFootprintSpec
    {compactor : MachineDescription}
    (hguard :
      GuardedLogicalTapeDecoderFootprintCompactorNilSpec compactor) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeNilSpec
      compactor := by
  rcases hguard with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  refine ⟨hready, ?_, ?_, ?_⟩
  · simpa [
      selectedSegmentLogicalTapeDecoderFootprintSourceTape_eq_fromPayload,
      selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload_eq] using
      hnilNil
  · intro padding
    simpa [
      selectedSegmentLogicalTapeDecoderFootprintSourceTape_eq_fromPayload,
      selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload_eq] using
      hnilNone padding
  · intro padBit padding
    simpa [
      selectedSegmentLogicalTapeDecoderFootprintSourceTape_eq_fromPayload,
      selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload_eq] using
      hnilSome padBit padding

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConsSpec_of_guardedFootprintSpec
    {compactor : MachineDescription}
    (hguard :
      GuardedLogicalTapeDecoderFootprintCompactorConsSpec compactor) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConsSpec
      compactor := by
  rcases hguard with ⟨hready, hconsNil, hconsNone, hconsSome⟩
  refine ⟨hready, ?_, ?_, ?_⟩
  · intro bit rest
    simpa [
      selectedSegmentLogicalTapeDecoderFootprintSourceTape_eq_fromPayload,
      selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload_eq] using
      hconsNil bit rest
  · intro bit rest padding
    simpa [
      selectedSegmentLogicalTapeDecoderFootprintSourceTape_eq_fromPayload,
      selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload_eq] using
      hconsNone bit rest padding
  · intro bit rest padBit padding
    simpa [
      selectedSegmentLogicalTapeDecoderFootprintSourceTape_eq_fromPayload,
      selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload_eq] using
      hconsSome bit rest padBit padding

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitSpec_of_guardedFootprintSpec
    {compactor : MachineDescription}
    (hguard :
      GuardedLogicalTapeDecoderFootprintCompactorSplitSpec compactor) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitSpec
      compactor := by
  rcases hguard with ⟨hnil, hcons⟩
  exact
    ⟨selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeNilSpec_of_guardedFootprintSpec
        hnil,
      selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConsSpec_of_guardedFootprintSpec
        hcons⟩

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitConstruction_of_guardedFootprint
    (hguard :
      GuardedLogicalTapeDecoderFootprintCompactorSplitConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitConstruction := by
  rcases hguard with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitSpec_of_guardedFootprintSpec
        hspec⟩

theorem selectedFootprintCompactorBridgeSpec_of_guardedFootprintSpec
    {compactor : MachineDescription}
    (hguard :
      GuardedLogicalTapeDecoderFootprintCompactorSpec compactor) :
    SelectedFootprintCompactorBridgeSpec compactor := by
  rcases hguard with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  simpa [
    selectedSegmentLogicalTapeDecoderFootprintSourceTape_eq_fromPayload,
    selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload_eq] using
    hrun bits padding

theorem selectedFootprintCompactorBridgeConstruction_of_guardedFootprint
    (hguard :
      GuardedLogicalTapeDecoderFootprintCompactorConstruction) :
    SelectedFootprintCompactorBridgeConstruction := by
  rcases hguard with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedFootprintCompactorBridgeSpec_of_guardedFootprintSpec
        hspec⟩

def SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeOutputSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    compactor.HaltsFromTapeWithOutput
      (rightEndCompactionSourceTape
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          [] []))
      (Tape.normalizedOutput (rightEdgeRewindSourceTape [] [])) ∧
    (forall padding : List (Option Bool),
      compactor.HaltsFromTapeWithOutput
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            [] (none :: padding)))
        (Tape.normalizedOutput
          (rightEdgeRewindSourceTape [] (none :: padding)))) ∧
    (forall (padBit : Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeWithOutput
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            [] (some padBit :: padding)))
        (Tape.normalizedOutput
          (rightEdgeRewindSourceTape [] (some padBit :: padding)))) ∧
    (forall (bit : Bool) (rest : Word Bool),
      compactor.HaltsFromTapeWithOutput
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            (bit :: rest) []))
        (Tape.normalizedOutput
          (rightEdgeRewindSourceTape (bit :: rest) []))) ∧
    (forall (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      compactor.HaltsFromTapeWithOutput
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            (bit :: rest) (none :: padding)))
        (Tape.normalizedOutput
          (rightEdgeRewindSourceTape (bit :: rest) (none :: padding)))) ∧
    forall (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeWithOutput
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            (bit :: rest) (some padBit :: padding)))
        (Tape.normalizedOutput
          (rightEdgeRewindSourceTape
            (bit :: rest) (some padBit :: padding)))

def SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeOutputConstruction :
    Prop :=
  exists compactor : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeOutputSpec
      compactor

def SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeNilOutputSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    compactor.HaltsFromTapeWithOutput
      (rightEndCompactionSourceTape
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          [] []))
      (Tape.normalizedOutput (rightEdgeRewindSourceTape [] [])) ∧
    (forall padding : List (Option Bool),
      compactor.HaltsFromTapeWithOutput
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            [] (none :: padding)))
        (Tape.normalizedOutput
          (rightEdgeRewindSourceTape [] (none :: padding)))) ∧
    forall (padBit : Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeWithOutput
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            [] (some padBit :: padding)))
        (Tape.normalizedOutput
          (rightEdgeRewindSourceTape [] (some padBit :: padding)))

def SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConsOutputSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    (forall (bit : Bool) (rest : Word Bool),
      compactor.HaltsFromTapeWithOutput
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            (bit :: rest) []))
        (Tape.normalizedOutput
          (rightEdgeRewindSourceTape (bit :: rest) []))) ∧
    (forall (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      compactor.HaltsFromTapeWithOutput
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            (bit :: rest) (none :: padding)))
        (Tape.normalizedOutput
          (rightEdgeRewindSourceTape (bit :: rest) (none :: padding)))) ∧
    forall (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeWithOutput
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            (bit :: rest) (some padBit :: padding)))
        (Tape.normalizedOutput
          (rightEdgeRewindSourceTape
            (bit :: rest) (some padBit :: padding)))

def SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitOutputSpec
    (compactor : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeNilOutputSpec
      compactor ∧
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConsOutputSpec
      compactor

def SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitOutputConstruction :
    Prop :=
  exists compactor : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitOutputSpec
      compactor

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeOutputSpec_of_bridgeOutputSpec
    {compactor : MachineDescription}
    (hbridge : SelectedFootprintCompactorBridgeOutputSpec compactor) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeOutputSpec
      compactor := by
  rcases hbridge with ⟨hready, hrun⟩
  refine ⟨hready, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hrun [] []
  · intro padding
    exact hrun [] (none :: padding)
  · intro padBit padding
    exact hrun [] (some padBit :: padding)
  · intro bit rest
    exact hrun (bit :: rest) []
  · intro bit rest padding
    exact hrun (bit :: rest) (none :: padding)
  · intro bit rest padBit padding
    exact hrun (bit :: rest) (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeOutputConstruction_of_bridgeOutput
    (hbridge : SelectedFootprintCompactorBridgeOutputConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeOutputConstruction := by
  rcases hbridge with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeOutputSpec_of_bridgeOutputSpec
        hspec⟩

theorem selectedFootprintCompactorBridgeOutputSpec_of_rightEndBridgeOutputSpec
    {compactor : MachineDescription}
    (hbridge :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeOutputSpec
        compactor) :
    SelectedFootprintCompactorBridgeOutputSpec compactor := by
  rcases hbridge with
    ⟨hready, hnilNil, hnilNone, hnilSome, hconsNil,
      hconsNone, hconsSome⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  cases bits with
  | nil =>
      cases padding with
      | nil =>
          exact hnilNil
      | cons pad padding =>
          cases pad with
          | none =>
              exact hnilNone padding
          | some padBit =>
              exact hnilSome padBit padding
  | cons bit rest =>
      cases padding with
      | nil =>
          exact hconsNil bit rest
      | cons pad padding =>
          cases pad with
          | none =>
              exact hconsNone bit rest padding
          | some padBit =>
              exact hconsSome bit rest padBit padding

theorem selectedFootprintCompactorBridgeOutputConstruction_of_rightEndBridgeOutput
    (hbridge :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeOutputConstruction) :
    SelectedFootprintCompactorBridgeOutputConstruction := by
  rcases hbridge with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedFootprintCompactorBridgeOutputSpec_of_rightEndBridgeOutputSpec
        hspec⟩

theorem selectedFootprintCompactorBridgeOutputSpec_iff_rightEndBridgeOutputSpec
    (compactor : MachineDescription) :
    SelectedFootprintCompactorBridgeOutputSpec compactor ↔
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeOutputSpec
        compactor := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeOutputSpec_of_bridgeOutputSpec
  · exact selectedFootprintCompactorBridgeOutputSpec_of_rightEndBridgeOutputSpec

theorem selectedFootprintCompactorBridgeOutputConstruction_iff_rightEndBridgeOutputConstruction :
    SelectedFootprintCompactorBridgeOutputConstruction ↔
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeOutputConstruction := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeOutputConstruction_of_bridgeOutput
  · exact selectedFootprintCompactorBridgeOutputConstruction_of_rightEndBridgeOutput

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitOutputSpec_of_bridgeOutputSpec
    {compactor : MachineDescription}
    (hbridge : SelectedFootprintCompactorBridgeOutputSpec compactor) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitOutputSpec
      compactor := by
  rcases hbridge with ⟨hready, hrun⟩
  refine ⟨?_, ?_⟩
  · refine ⟨hready, ?_, ?_, ?_⟩
    · exact hrun [] []
    · intro padding
      exact hrun [] (none :: padding)
    · intro padBit padding
      exact hrun [] (some padBit :: padding)
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro bit rest
      exact hrun (bit :: rest) []
    · intro bit rest padding
      exact hrun (bit :: rest) (none :: padding)
    · intro bit rest padBit padding
      exact hrun (bit :: rest) (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitOutputConstruction_of_bridgeOutput
    (hbridge : SelectedFootprintCompactorBridgeOutputConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitOutputConstruction := by
  rcases hbridge with ⟨compactor, hready, hrun⟩
  refine ⟨compactor, ?_, ?_⟩
  · refine ⟨hready, ?_, ?_, ?_⟩
    · exact hrun [] []
    · intro padding
      exact hrun [] (none :: padding)
    · intro padBit padding
      exact hrun [] (some padBit :: padding)
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro bit rest
      exact hrun (bit :: rest) []
    · intro bit rest padding
      exact hrun (bit :: rest) (none :: padding)
    · intro bit rest padBit padding
      exact hrun (bit :: rest) (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeOutputSpec_of_splitOutputSpec
    {compactor : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitOutputSpec
        compactor) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeOutputSpec
      compactor := by
  rcases hsplit with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  exact
    ⟨hready, hnilNil, hnilNone, hnilSome,
      hconsNil, hconsNone, hconsSome⟩

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeOutputConstruction_of_splitOutput
    (hsplit :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitOutputConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeOutputConstruction := by
  rcases hsplit with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeOutputSpec_of_splitOutputSpec
        hspec⟩

theorem selectedFootprintCompactorBridgeOutputSpec_of_rightEndBridgeSplitOutputSpec
    {compactor : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitOutputSpec
        compactor) :
    SelectedFootprintCompactorBridgeOutputSpec compactor :=
  selectedFootprintCompactorBridgeOutputSpec_of_rightEndBridgeOutputSpec
    (selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeOutputSpec_of_splitOutputSpec
      hsplit)

theorem selectedFootprintCompactorBridgeOutputConstruction_of_rightEndBridgeSplitOutput
    (hsplit :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitOutputConstruction) :
    SelectedFootprintCompactorBridgeOutputConstruction :=
  selectedFootprintCompactorBridgeOutputConstruction_of_rightEndBridgeOutput
    (selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeOutputConstruction_of_splitOutput
      hsplit)

theorem selectedFootprintCompactorBridgeOutputSpec_iff_rightEndBridgeSplitOutputSpec
    (compactor : MachineDescription) :
    SelectedFootprintCompactorBridgeOutputSpec compactor ↔
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitOutputSpec
        compactor := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitOutputSpec_of_bridgeOutputSpec
  · exact selectedFootprintCompactorBridgeOutputSpec_of_rightEndBridgeSplitOutputSpec

theorem selectedFootprintCompactorBridgeOutputConstruction_iff_rightEndBridgeSplitOutputConstruction :
    SelectedFootprintCompactorBridgeOutputConstruction ↔
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitOutputConstruction := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitOutputConstruction_of_bridgeOutput
  · exact selectedFootprintCompactorBridgeOutputConstruction_of_rightEndBridgeSplitOutput

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeOutputSpec_of_exact
    {compactor : MachineDescription}
    (hbridge :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSpec
        compactor) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeOutputSpec
      compactor :=
  selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeOutputSpec_of_bridgeOutputSpec
    (selectedFootprintCompactorBridgeOutputSpec_of_exact
      (selectedFootprintCompactorBridgeSpec_of_rightEndBridgeSpec
        hbridge))

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeOutputConstruction_of_exact
    (hbridge :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeOutputConstruction := by
  rcases hbridge with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeOutputSpec_of_exact
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitOutputSpec_of_exact
    {compactor : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitSpec
        compactor) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitOutputSpec
      compactor := by
  rcases hsplit with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  have toOutput :
      forall {Tin Tout : Tape Bool},
        compactor.HaltsFromTapeEquiv Tin Tout ->
          compactor.HaltsFromTapeWithOutput Tin
            (Tape.normalizedOutput Tout) := by
    intro Tin Tout hhaltEquiv
    rcases hhaltEquiv with ⟨actual, hhalt, hequiv⟩
    have houtput :=
      MachineDescription.haltsFromTapeWithOutput_of_haltsFromTape hhalt
    rw [Tape.Equiv.normalizedOutput_eq hequiv] at houtput
    exact houtput
  refine ⟨?_, ?_⟩
  · refine ⟨hready, ?_, ?_, ?_⟩
    · exact toOutput hnilNil
    · intro padding
      exact toOutput (hnilNone padding)
    · intro padBit padding
      exact toOutput (hnilSome padBit padding)
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro bit rest
      exact toOutput (hconsNil bit rest)
    · intro bit rest padding
      exact toOutput (hconsNone bit rest padding)
    · intro bit rest padBit padding
      exact toOutput (hconsSome bit rest padBit padding)

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitOutputConstruction_of_exact
    (hsplit :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitOutputConstruction := by
  rcases hsplit with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitOutputSpec_of_exact
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitSpec_of_bridgeSpec
    {compactor : MachineDescription}
    (hbridge : SelectedFootprintCompactorBridgeSpec compactor) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitSpec
      compactor := by
  rcases hbridge with ⟨hready, hrun⟩
  refine ⟨?_, ?_⟩
  · refine ⟨hready, ?_, ?_, ?_⟩
    · exact hrun [] []
    · intro padding
      exact hrun [] (none :: padding)
    · intro padBit padding
      exact hrun [] (some padBit :: padding)
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro bit rest
      exact hrun (bit :: rest) []
    · intro bit rest padding
      exact hrun (bit :: rest) (none :: padding)
    · intro bit rest padBit padding
      exact hrun (bit :: rest) (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitConstruction_of_bridge
    (hbridge : SelectedFootprintCompactorBridgeConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitConstruction := by
  rcases hbridge with ⟨compactor, hready, hrun⟩
  refine ⟨compactor, ?_, ?_⟩
  · refine ⟨hready, ?_, ?_, ?_⟩
    · exact hrun [] []
    · intro padding
      exact hrun [] (none :: padding)
    · intro padBit padding
      exact hrun [] (some padBit :: padding)
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro bit rest
      exact hrun (bit :: rest) []
    · intro bit rest padding
      exact hrun (bit :: rest) (none :: padding)
    · intro bit rest padBit padding
      exact hrun (bit :: rest) (some padBit :: padding)

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
        selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape,
        selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape] using
        hnilNil
    · intro padding
      simpa [
        selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape,
        selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape] using
        hnilNone padding
    · intro padBit padding
      simpa [
        selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape,
        selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape] using
        hnilSome padBit padding
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro bit rest
      simpa [
        selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape,
        selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape] using
        hconsNil bit rest
    · intro bit rest padding
      simpa [
        selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape,
        selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape] using
        hconsNone bit rest padding
    · intro bit rest padBit padding
      simpa [
        selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape,
        selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_eq_rightEdgeRewindSourceTape] using
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

theorem selectedFootprintCompactorBridgeSpec_of_rightEndBridgeSplitSpec
    {compactor : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitSpec
        compactor) :
    SelectedFootprintCompactorBridgeSpec compactor := by
  rcases hsplit with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  cases bits with
  | nil =>
      cases padding with
      | nil =>
          exact hnilNil
      | cons pad padding =>
          cases pad with
          | none =>
              exact hnilNone padding
          | some padBit =>
              exact hnilSome padBit padding
  | cons bit rest =>
      cases padding with
      | nil =>
          exact hconsNil bit rest
      | cons pad padding =>
          cases pad with
          | none =>
              exact hconsNone bit rest padding
          | some padBit =>
              exact hconsSome bit rest padBit padding

theorem selectedFootprintCompactorBridgeConstruction_of_rightEndBridgeSplit
    (hsplit :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitConstruction) :
    SelectedFootprintCompactorBridgeConstruction := by
  rcases hsplit with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedFootprintCompactorBridgeSpec_of_rightEndBridgeSplitSpec
        hspec⟩

theorem selectedFootprintCompactorBridgeSpec_iff_rightEndBridgeSplitSpec
    (compactor : MachineDescription) :
    SelectedFootprintCompactorBridgeSpec compactor ↔
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitSpec
        compactor := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitSpec_of_bridgeSpec
  · exact selectedFootprintCompactorBridgeSpec_of_rightEndBridgeSplitSpec

theorem selectedFootprintCompactorBridgeConstruction_iff_rightEndBridgeSplitConstruction :
    SelectedFootprintCompactorBridgeConstruction ↔
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitConstruction := by
  constructor
  · exact selectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitConstruction_of_bridge
  · exact selectedFootprintCompactorBridgeConstruction_of_rightEndBridgeSplit


end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
