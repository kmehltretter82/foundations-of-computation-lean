import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Compaction
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StatefulOptionAppendGenerated

set_option doc.verso true

/-!
# Fixed-window deletion transducer

This module instantiates the generated stateful optional-output compiler with a
finite-control adapter that keeps a fixed prefix, deletes a fixed-size middle
window, and keeps the remaining suffix.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

def deleteWindowBoundary (keep delete : Nat) : Nat :=
  keep + delete

def deleteWindowScanStateCount (keep delete : Nat) : Nat :=
  deleteWindowBoundary keep delete + 1

def deleteWindowNext (keep delete : Nat) (state : Nat) (_bit : Bool) :
    Nat :=
  if state < deleteWindowBoundary keep delete then
    state + 1
  else
    deleteWindowBoundary keep delete

def deleteWindowEmit (keep delete : Nat) (state : Nat) (bit : Bool) :
    Option Bool :=
  if keep ≤ state ∧ state < deleteWindowBoundary keep delete then
    none
  else
    some bit

def deleteWindowTransducer (keep delete : Nat) : FiniteTransducer :=
  statefulOptionAppendTransducer
    (deleteWindowScanStateCount keep delete)
    0
    (deleteWindowNext keep delete)
    (deleteWindowEmit keep delete)
    []

def generatedDeleteWindowDescription
    (keep delete : Nat) : MachineDescription :=
  generatedStatefulOptionAppendDescription
    (deleteWindowScanStateCount keep delete)
    0
    (deleteWindowNext keep delete)
    (deleteWindowEmit keep delete)
    []

theorem deleteWindow_start_lt (keep delete : Nat) :
    0 < deleteWindowScanStateCount keep delete := by
  simp [deleteWindowScanStateCount]

theorem deleteWindow_next_lt (keep delete : Nat) :
    forall state bit,
      state < deleteWindowScanStateCount keep delete ->
        deleteWindowNext keep delete state bit <
          deleteWindowScanStateCount keep delete := by
  intro state bit hstate
  by_cases hlt : state < deleteWindowBoundary keep delete
  · simp [deleteWindowNext, hlt, deleteWindowScanStateCount]
  · simp [deleteWindowNext, hlt, deleteWindowScanStateCount]

theorem generatedDeleteWindowDescription_subroutineReady
    (keep delete : Nat) :
    (generatedDeleteWindowDescription keep delete).SubroutineReady := by
  simpa [generatedDeleteWindowDescription] using
    generatedStatefulOptionAppendDescription_subroutineReady
      (deleteWindowScanStateCount keep delete)
      0
      (deleteWindowNext keep delete)
      (deleteWindowEmit keep delete)
      []
      (deleteWindow_start_lt keep delete)
      (deleteWindow_next_lt keep delete)

theorem deleteWindowAfter_before
    (keep delete state : Nat) (input : Word Bool)
    (h : state + input.length ≤ keep) :
    statefulOptionAfter (deleteWindowNext keep delete) state input =
      state + input.length := by
  induction input generalizing state with
  | nil =>
      simp [statefulOptionAfter]
  | cons bit rest ih =>
      have hstateLt : state < keep := by
        simp at h
        omega
      have hltBoundary :
          state < deleteWindowBoundary keep delete := by
        simp [deleteWindowBoundary]
        omega
      have hrest : state + 1 + rest.length ≤ keep := by
        simp at h
        omega
      have hih := ih (state + 1) hrest
      simp [statefulOptionAfter, deleteWindowNext, hltBoundary, hih]
      omega

theorem deleteWindowOutput_before
    (keep delete state : Nat) (input : Word Bool)
    (h : state + input.length ≤ keep) :
    statefulOptionOutputFrom
        (deleteWindowNext keep delete)
        (deleteWindowEmit keep delete)
        state input =
      input := by
  induction input generalizing state with
  | nil =>
      simp [statefulOptionOutputFrom]
  | cons bit rest ih =>
      have hstateLt : state < keep := by
        simp at h
        omega
      have hnotDelete :
          ¬ (keep ≤ state ∧
            state < deleteWindowBoundary keep delete) := by
        intro hdel
        omega
      have hnotKeep : ¬ keep ≤ state := by
        omega
      have hltBoundary :
          state < deleteWindowBoundary keep delete := by
        simp [deleteWindowBoundary]
        omega
      have hrest : state + 1 + rest.length ≤ keep := by
        simp at h
        omega
      have hih := ih (state + 1) hrest
      simp [statefulOptionOutputFrom, deleteWindowEmit,
        hnotKeep, optionEmitWord, deleteWindowNext, hltBoundary,
        hih]

theorem deleteWindowCells_before
    (keep delete state : Nat) (input : Word Bool)
    (h : state + input.length ≤ keep) :
    statefulOptionCellsFrom
        (deleteWindowNext keep delete)
        (deleteWindowEmit keep delete)
        state input =
      input.map some := by
  induction input generalizing state with
  | nil =>
      simp [statefulOptionCellsFrom]
  | cons bit rest ih =>
      have hnotKeep : ¬ keep ≤ state := by
        simp at h
        omega
      have hltBoundary :
          state < deleteWindowBoundary keep delete := by
        simp [deleteWindowBoundary]
        omega
      have hrest : state + 1 + rest.length ≤ keep := by
        simp at h
        omega
      have hih := ih (state + 1) hrest
      simp [statefulOptionCellsFrom, deleteWindowEmit,
        hnotKeep, deleteWindowNext, hltBoundary, hih]

theorem deleteWindowAfter_delete
    (keep delete state : Nat) (input : Word Bool)
    (hge : keep ≤ state)
    (hlen : state + input.length = deleteWindowBoundary keep delete) :
    statefulOptionAfter (deleteWindowNext keep delete) state input =
      deleteWindowBoundary keep delete := by
  induction input generalizing state with
  | nil =>
      simp [statefulOptionAfter] at hlen ⊢
      exact hlen
  | cons bit rest ih =>
      have hltBoundary :
          state < deleteWindowBoundary keep delete := by
        simp at hlen
        omega
      have hgeNext : keep ≤ state + 1 := by omega
      have hlenNext :
          state + 1 + rest.length =
            deleteWindowBoundary keep delete := by
        simp at hlen
        omega
      have hih := ih (state + 1) hgeNext hlenNext
      simp [statefulOptionAfter, deleteWindowNext, hltBoundary, hih]

theorem deleteWindowOutput_delete
    (keep delete state : Nat) (input : Word Bool)
    (hge : keep ≤ state)
    (hlen : state + input.length = deleteWindowBoundary keep delete) :
    statefulOptionOutputFrom
        (deleteWindowNext keep delete)
        (deleteWindowEmit keep delete)
        state input =
      [] := by
  induction input generalizing state with
  | nil =>
      simp [statefulOptionOutputFrom]
  | cons bit rest ih =>
      have hltBoundary :
          state < deleteWindowBoundary keep delete := by
        simp at hlen
        omega
      have hdelete :
          keep ≤ state ∧
            state < deleteWindowBoundary keep delete :=
        ⟨hge, hltBoundary⟩
      have hgeNext : keep ≤ state + 1 := by omega
      have hlenNext :
          state + 1 + rest.length =
            deleteWindowBoundary keep delete := by
        simp at hlen
        omega
      have hih := ih (state + 1) hgeNext hlenNext
      simp [statefulOptionOutputFrom, deleteWindowEmit, hdelete,
        optionEmitWord, deleteWindowNext, hih]

theorem deleteWindowCells_delete
    (keep delete state : Nat) (input : Word Bool)
    (hge : keep ≤ state)
    (hlen : state + input.length = deleteWindowBoundary keep delete) :
    statefulOptionCellsFrom
        (deleteWindowNext keep delete)
        (deleteWindowEmit keep delete)
        state input =
      List.replicate input.length (none : Option Bool) := by
  induction input generalizing state with
  | nil =>
      simp [statefulOptionCellsFrom]
  | cons bit rest ih =>
      have hltBoundary :
          state < deleteWindowBoundary keep delete := by
        simp at hlen
        omega
      have hdelete :
          keep ≤ state ∧
            state < deleteWindowBoundary keep delete :=
        ⟨hge, hltBoundary⟩
      have hgeNext : keep ≤ state + 1 := by omega
      have hlenNext :
          state + 1 + rest.length =
            deleteWindowBoundary keep delete := by
        simp at hlen
        omega
      have hih := ih (state + 1) hgeNext hlenNext
      change
        statefulOptionCellsFrom
            (deleteWindowNext keep delete)
            (deleteWindowEmit keep delete)
            state (bit :: rest) =
          none :: List.replicate rest.length (none : Option Bool)
      simp [statefulOptionCellsFrom, deleteWindowEmit, hdelete,
        deleteWindowNext, hih]

theorem deleteWindowAfter_suffix
    (keep delete : Nat) (suffix : Word Bool) :
    statefulOptionAfter
        (deleteWindowNext keep delete)
        (deleteWindowBoundary keep delete) suffix =
      deleteWindowBoundary keep delete := by
  induction suffix with
  | nil =>
      simp [statefulOptionAfter]
  | cons bit rest ih =>
      simp [statefulOptionAfter, deleteWindowNext, ih]

theorem deleteWindowOutput_suffix
    (keep delete : Nat) (suffix : Word Bool) :
    statefulOptionOutputFrom
        (deleteWindowNext keep delete)
        (deleteWindowEmit keep delete)
        (deleteWindowBoundary keep delete) suffix =
      suffix := by
  induction suffix with
  | nil =>
      simp [statefulOptionOutputFrom]
  | cons bit rest ih =>
      have hnotDelete :
          ¬ (keep ≤ deleteWindowBoundary keep delete ∧
            deleteWindowBoundary keep delete <
              deleteWindowBoundary keep delete) := by
        intro hdel
        omega
      simp [statefulOptionOutputFrom, deleteWindowEmit,
        optionEmitWord, deleteWindowNext, ih]

theorem deleteWindowCells_suffix
    (keep delete : Nat) (suffix : Word Bool) :
    statefulOptionCellsFrom
        (deleteWindowNext keep delete)
        (deleteWindowEmit keep delete)
        (deleteWindowBoundary keep delete) suffix =
      suffix.map some := by
  induction suffix with
  | nil =>
      simp [statefulOptionCellsFrom]
  | cons bit rest ih =>
      have hnotDelete :
          ¬ (keep ≤ deleteWindowBoundary keep delete ∧
            deleteWindowBoundary keep delete <
              deleteWindowBoundary keep delete) := by
        intro hdel
        omega
      simp [statefulOptionCellsFrom, deleteWindowEmit,
        deleteWindowNext, ih]

theorem deleteWindowOutputFrom_split
    (keep delete : Nat)
    (pref deleted suffix : Word Bool)
    (hpref : pref.length = keep)
    (hdeleted : deleted.length = delete) :
    statefulOptionOutputFrom
        (deleteWindowNext keep delete)
        (deleteWindowEmit keep delete)
        0
        (List.append pref (List.append deleted suffix)) =
      List.append pref suffix := by
  rw [statefulOptionOutputFrom_append]
  have hprefixOut :
      statefulOptionOutputFrom
          (deleteWindowNext keep delete)
          (deleteWindowEmit keep delete)
          0 pref =
        pref := by
    exact deleteWindowOutput_before keep delete 0 pref (by omega)
  have hprefixAfter :
      statefulOptionAfter
          (deleteWindowNext keep delete)
          0 pref =
        keep := by
    have h := deleteWindowAfter_before keep delete 0 pref (by omega)
    simpa [hpref] using h
  rw [hprefixOut, hprefixAfter]
  rw [statefulOptionOutputFrom_append]
  have hdeletedOut :
      statefulOptionOutputFrom
          (deleteWindowNext keep delete)
          (deleteWindowEmit keep delete)
          keep deleted =
        [] := by
    apply deleteWindowOutput_delete
    · exact Nat.le_refl keep
    · simp [deleteWindowBoundary, hdeleted]
  have hdeletedAfter :
      statefulOptionAfter
          (deleteWindowNext keep delete)
          keep deleted =
        deleteWindowBoundary keep delete := by
    apply deleteWindowAfter_delete
    · exact Nat.le_refl keep
    · simp [deleteWindowBoundary, hdeleted]
  rw [hdeletedOut, hdeletedAfter]
  rw [deleteWindowOutput_suffix]
  simp

theorem deleteWindowCellsFrom_split
    (keep delete : Nat)
    (pref deleted suffix : Word Bool)
    (hpref : pref.length = keep)
    (hdeleted : deleted.length = delete) :
    statefulOptionCellsFrom
        (deleteWindowNext keep delete)
        (deleteWindowEmit keep delete)
        0
        (List.append pref (List.append deleted suffix)) =
      List.append (pref.map some)
        (List.append
          (List.replicate delete (none : Option Bool))
          (suffix.map some)) := by
  rw [statefulOptionCellsFrom_append]
  have hprefixCells :
      statefulOptionCellsFrom
          (deleteWindowNext keep delete)
          (deleteWindowEmit keep delete)
          0 pref =
        pref.map some := by
    exact deleteWindowCells_before keep delete 0 pref (by omega)
  have hprefixAfter :
      statefulOptionAfter
          (deleteWindowNext keep delete)
          0 pref =
        keep := by
    have h := deleteWindowAfter_before keep delete 0 pref (by omega)
    simpa [hpref] using h
  rw [hprefixCells, hprefixAfter]
  rw [statefulOptionCellsFrom_append]
  have hdeletedCells :
      statefulOptionCellsFrom
          (deleteWindowNext keep delete)
          (deleteWindowEmit keep delete)
          keep deleted =
        List.replicate delete (none : Option Bool) := by
    have hcells :=
      deleteWindowCells_delete keep delete keep deleted
        (Nat.le_refl keep)
        (by simp [deleteWindowBoundary, hdeleted])
    simpa [hdeleted] using hcells
  have hdeletedAfter :
      statefulOptionAfter
          (deleteWindowNext keep delete)
          keep deleted =
        deleteWindowBoundary keep delete := by
    apply deleteWindowAfter_delete
    · exact Nat.le_refl keep
    · simp [deleteWindowBoundary, hdeleted]
  rw [hdeletedCells, hdeletedAfter]
  rw [deleteWindowCells_suffix]

theorem deleteWindowTransducer_runsToOutput_split
    (keep delete : Nat)
    (pref deleted suffix : Word Bool)
    (hpref : pref.length = keep)
    (hdeleted : deleted.length = delete) :
    (deleteWindowTransducer keep delete).RunsToOutput
      (List.append pref (List.append deleted suffix))
      (List.append pref suffix) := by
  have hrun :=
    statefulOptionAppendTransducer_runsToOutput
      (deleteWindowScanStateCount keep delete)
      0
      (deleteWindowNext keep delete)
      (deleteWindowEmit keep delete)
      []
      (List.append pref (List.append deleted suffix))
      (deleteWindow_start_lt keep delete)
      (deleteWindow_next_lt keep delete)
  have hout :=
    deleteWindowOutputFrom_split keep delete pref deleted suffix
      hpref hdeleted
  rw [← hout]
  simpa [deleteWindowTransducer] using hrun

theorem FSTDeleteWindowTargetTape_normalizedOutput_split
    (keep delete : Nat)
    (pref deleted suffix : Word Bool)
    (leftScratch : Nat)
    (hpref : pref.length = keep)
    (hdeleted : deleted.length = delete) :
    Tape.normalizedOutput
        (FSTStatefulOptionAppendTargetTape
          (deleteWindowNext keep delete)
          (deleteWindowEmit keep delete)
          0
          (List.append pref (List.append deleted suffix))
          []
          leftScratch) =
      List.append pref suffix := by
  rw [FSTStatefulOptionAppendTargetTape_normalizedOutput]
  rw [deleteWindowOutputFrom_split keep delete pref deleted suffix
    hpref hdeleted]
  simp

theorem FSTDeleteWindowTargetTape_cells_split
    (keep delete : Nat)
    (pref deleted suffix : Word Bool)
    (leftScratch : Nat)
    (hpref : pref.length = keep)
    (hdeleted : deleted.length = delete) :
    Tape.cells
        (FSTStatefulOptionAppendTargetTape
          (deleteWindowNext keep delete)
          (deleteWindowEmit keep delete)
          0
          (List.append pref (List.append deleted suffix))
          []
          leftScratch) =
      List.append
        (List.replicate leftScratch (none : Option Bool))
        (List.append
          (pref.map some)
          (List.append
            (List.replicate delete (none : Option Bool))
            (List.append (suffix.map some) [none, none]))) := by
  rw [FSTStatefulOptionAppendTargetTape_cells]
  rw [deleteWindowCellsFrom_split keep delete pref deleted suffix
    hpref hdeleted]
  simp [List.append_assoc]

theorem FSTDeleteWindowTargetTape_compactedCells_split
    (keep delete : Nat)
    (pref deleted suffix : Word Bool)
    (leftScratch extraScratch : Nat)
    (hpref : pref.length = keep)
    (hdeleted : deleted.length = delete) :
    compactedCellsWithScratch
        (Tape.cells
          (FSTStatefulOptionAppendTargetTape
            (deleteWindowNext keep delete)
            (deleteWindowEmit keep delete)
            0
            (List.append pref (List.append deleted suffix))
            []
            leftScratch))
        extraScratch =
      rightScratchOutputCells
        (List.append pref suffix)
        (leftScratch + delete + 2 + extraScratch) := by
  rw [FSTDeleteWindowTargetTape_cells_split
    keep delete pref deleted suffix leftScratch hpref hdeleted]
  simpa [List.replicate, List.append_assoc,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    compactedCellsWithScratch_twoChunks
      leftScratch delete 2 extraScratch pref suffix

theorem FSTDeleteWindowTargetTape_compactedCells_eq_FSTTargetTape_cells_split
    (keep delete : Nat)
    (pref deleted suffix : Word Bool)
    (leftScratch extraScratch : Nat)
    (first second : Bool) (rest : Word Bool)
    (hpref : pref.length = keep)
    (hdeleted : deleted.length = delete)
    (houtput :
      List.append pref suffix = first :: second :: rest) :
    compactedCellsWithScratch
        (Tape.cells
          (FSTStatefulOptionAppendTargetTape
            (deleteWindowNext keep delete)
            (deleteWindowEmit keep delete)
            0
            (List.append pref (List.append deleted suffix))
            []
            leftScratch))
        extraScratch =
      Tape.cells
        (FSTTargetTape
          (List.append pref suffix)
          (leftScratch + delete + 2 + extraScratch)) := by
  rw [FSTDeleteWindowTargetTape_compactedCells_split
    keep delete pref deleted suffix leftScratch extraScratch hpref hdeleted]
  rw [FSTTargetTape_cells_eq_rightScratchOutputCells
    (List.append pref suffix)
    (leftScratch + delete + 2 + extraScratch)
    first second rest houtput]

theorem FSTDeleteWindowPrefixedTargetTape_normalizedOutput_split
    (delete : Nat)
    (pref deleted suffix : Word Bool)
    (leftScratch : Nat)
    (hdeleted : deleted.length = delete) :
    Tape.normalizedOutput
        (FSTStatefulOptionAppendPrefixedTargetTape
          (deleteWindowNext 0 delete)
          (deleteWindowEmit 0 delete)
          0
          pref
          (List.append deleted suffix)
          []
          leftScratch) =
      List.append pref suffix := by
  rw [FSTStatefulOptionAppendPrefixedTargetTape_normalizedOutput]
  have hout :
      statefulOptionOutputFrom
          (deleteWindowNext 0 delete)
          (deleteWindowEmit 0 delete)
          0
          (List.append deleted suffix) =
        suffix := by
    simpa using
      deleteWindowOutputFrom_split
        0 delete ([] : Word Bool) deleted suffix rfl hdeleted
  rw [hout]
  simp

theorem FSTDeleteWindowPrefixedTargetTape_cells_split
    (delete : Nat)
    (pref deleted suffix : Word Bool)
    (leftScratch : Nat)
    (hdeleted : deleted.length = delete) :
    Tape.cells
        (FSTStatefulOptionAppendPrefixedTargetTape
          (deleteWindowNext 0 delete)
          (deleteWindowEmit 0 delete)
          0
          pref
          (List.append deleted suffix)
          []
          leftScratch) =
      List.append
        (List.replicate leftScratch (none : Option Bool))
        (List.append
          (pref.map some)
          (List.append
            (List.replicate delete (none : Option Bool))
            (List.append (suffix.map some) [none, none]))) := by
  rw [FSTStatefulOptionAppendPrefixedTargetTape_cells]
  have hcells :
      statefulOptionCellsFrom
          (deleteWindowNext 0 delete)
          (deleteWindowEmit 0 delete)
          0
          (List.append deleted suffix) =
        List.append
          (List.replicate delete (none : Option Bool))
          (suffix.map some) := by
    simpa using
      deleteWindowCellsFrom_split
        0 delete ([] : Word Bool) deleted suffix rfl hdeleted
  rw [hcells]
  simp [List.append_assoc]

theorem FSTDeleteWindowPrefixedTargetTape_compactedCells_split
    (delete : Nat)
    (pref deleted suffix : Word Bool)
    (leftScratch extraScratch : Nat)
    (hdeleted : deleted.length = delete) :
    compactedCellsWithScratch
        (Tape.cells
          (FSTStatefulOptionAppendPrefixedTargetTape
            (deleteWindowNext 0 delete)
            (deleteWindowEmit 0 delete)
            0
            pref
            (List.append deleted suffix)
            []
            leftScratch))
        extraScratch =
      rightScratchOutputCells
        (List.append pref suffix)
        (leftScratch + delete + 2 + extraScratch) := by
  rw [FSTDeleteWindowPrefixedTargetTape_cells_split
    delete pref deleted suffix leftScratch hdeleted]
  simpa [List.replicate, List.append_assoc,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    compactedCellsWithScratch_twoChunks
      leftScratch delete 2 extraScratch pref suffix

theorem FSTDeleteWindowPrefixedTargetTape_compactedCells_eq_FSTTargetTape_cells_split
    (delete : Nat)
    (pref deleted suffix : Word Bool)
    (leftScratch extraScratch : Nat)
    (first second : Bool) (rest : Word Bool)
    (hdeleted : deleted.length = delete)
    (houtput :
      List.append pref suffix = first :: second :: rest) :
    compactedCellsWithScratch
        (Tape.cells
          (FSTStatefulOptionAppendPrefixedTargetTape
            (deleteWindowNext 0 delete)
            (deleteWindowEmit 0 delete)
            0
            pref
            (List.append deleted suffix)
            []
            leftScratch))
        extraScratch =
      Tape.cells
        (FSTTargetTape
          (List.append pref suffix)
          (leftScratch + delete + 2 + extraScratch)) := by
  rw [FSTDeleteWindowPrefixedTargetTape_compactedCells_split
    delete pref deleted suffix leftScratch extraScratch hdeleted]
  rw [FSTTargetTape_cells_eq_rightScratchOutputCells
    (List.append pref suffix)
    (leftScratch + delete + 2 + extraScratch)
    first second rest houtput]

theorem deleteWindowTransducer_compiledByGeneratedDescription
    (keep delete : Nat) :
    ExactCompiledByDescription
      (deleteWindowTransducer keep delete)
      (generatedDeleteWindowDescription keep delete)
      (fun input _output leftScratch =>
        FSTStatefulOptionAppendTargetTape
          (deleteWindowNext keep delete)
          (deleteWindowEmit keep delete)
          0
          input
          []
          leftScratch) := by
  simpa [deleteWindowTransducer, generatedDeleteWindowDescription] using
    statefulOptionAppendTransducer_compiledByGeneratedDescription
      (deleteWindowScanStateCount keep delete)
      0
      (deleteWindowNext keep delete)
      (deleteWindowEmit keep delete)
      []
      (deleteWindow_start_lt keep delete)
      (deleteWindow_next_lt keep delete)

theorem generatedDeleteWindowDescription_haltsFrom_split
    (keep delete : Nat)
    (pref deleted suffix : Word Bool)
    (leftScratch : Nat)
    (hpref : pref.length = keep)
    (hdeleted : deleted.length = delete) :
    (generatedDeleteWindowDescription keep delete).HaltsFromTape
      (FSTSourceTape
        (List.append pref (List.append deleted suffix))
        leftScratch)
      (FSTStatefulOptionAppendTargetTape
        (deleteWindowNext keep delete)
        (deleteWindowEmit keep delete)
        0
        (List.append pref (List.append deleted suffix))
        []
        leftScratch) := by
  exact
    (deleteWindowTransducer_compiledByGeneratedDescription
      keep delete).right
      (List.append pref (List.append deleted suffix))
      (List.append pref suffix)
      leftScratch
      (deleteWindowTransducer_runsToOutput_split
        keep delete pref deleted suffix hpref hdeleted)

theorem generatedDeleteWindowDescription_haltsFrom_split_withPadding
    (keep delete : Nat)
    (pref deleted suffix : Word Bool)
    (leftScratch : Nat) (padding : List (Option Bool)) :
    (generatedDeleteWindowDescription keep delete).HaltsFromTape
      (FSTStatefulOptionAppendSourceTapeWithPadding
        (List.append pref (List.append deleted suffix))
        leftScratch padding)
      (FSTStatefulOptionAppendTargetTapeWithPadding
        (deleteWindowNext keep delete)
        (deleteWindowEmit keep delete)
        0
        (List.append pref (List.append deleted suffix))
        leftScratch padding) := by
  simpa [generatedDeleteWindowDescription,
    FSTStatefulOptionAppendSourceTapeWithPadding,
    FSTStatefulOptionAppendTargetTapeWithPadding] using
    generatedStatefulOptionAppendDescription_haltsFrom_tapeAtCells_nil_withPadding
      (deleteWindowScanStateCount keep delete)
      0
      (deleteWindowNext keep delete)
      (deleteWindowEmit keep delete)
      (List.append pref (List.append deleted suffix))
      (List.replicate leftScratch (none : Option Bool))
      padding
      (deleteWindow_start_lt keep delete)
      (deleteWindow_next_lt keep delete)

theorem generatedDeleteWindowDescription_haltsFrom_prefixed
    (delete : Nat)
    (pref input : Word Bool)
    (leftScratch : Nat) :
    (generatedDeleteWindowDescription 0 delete).HaltsFromTape
      (FSTStatefulOptionAppendPrefixedSourceTape
        pref input leftScratch)
      (FSTStatefulOptionAppendPrefixedTargetTape
        (deleteWindowNext 0 delete)
        (deleteWindowEmit 0 delete)
        0
        pref
        input
        []
        leftScratch) := by
  simpa [generatedDeleteWindowDescription] using
    generatedStatefulOptionAppendDescription_haltsFrom_prefixedSourceTape
      (deleteWindowScanStateCount 0 delete)
      0
      (deleteWindowNext 0 delete)
      (deleteWindowEmit 0 delete)
      []
      pref
      input
      leftScratch
      (deleteWindow_start_lt 0 delete)
      (deleteWindow_next_lt 0 delete)

end FiniteTransducers
end CommonGround

end Computability
end FoC
