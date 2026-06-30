import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Basic

set_option doc.verso true

/-!
# Physical cell compaction shapes

These helpers specify the exact right-scratch-padded cell lists produced by
compacting nonblank cells left and turning skipped/deleted cells into trailing
scratch blanks.  They are pure shape lemmas; later finite-machine leaves can use
them as the target contract for certified compaction passes.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

def rightScratchOutputCells
    (output : Word Bool) (scratchWidth : Nat) :
    List (Option Bool) :=
  List.append (output.map some)
    (List.replicate scratchWidth (none : Option Bool))

def compactedCellsWithScratch
    (cells : List (Option Bool)) (extraScratch : Nat) :
    List (Option Bool) :=
  rightScratchOutputCells
    (cells.filterMap (fun cell => cell))
    (cells.length - (cells.filterMap (fun cell => cell)).length +
      extraScratch)

def compactionScratchWidth
    (cells : List (Option Bool)) (extraScratch : Nat) : Nat :=
  cells.length - (cells.filterMap (fun cell => cell)).length +
    extraScratch

def rightEndCompactionVisibleCells
    (leftCells : List (Option Bool)) : List (Option Bool) :=
  List.append leftCells [none]

def rightEndCompactionSourceTape
    (leftCells : List (Option Bool)) : Tape Bool :=
  tapeAtCells leftCells.reverse [none]

def rightEndCompactionSourceTapeWithRightPadding
    (leftCells rightPadding : List (Option Bool)) : Tape Bool :=
  tapeAtCells leftCells.reverse (none :: rightPadding)

def rightEndCompactionTargetTape
    (leftCells : List (Option Bool)) (extraScratch : Nat) :
    Tape Bool :=
  FSTTargetTape
    ((rightEndCompactionVisibleCells leftCells).filterMap
      (fun cell => cell))
    (compactionScratchWidth
      (rightEndCompactionVisibleCells leftCells)
      extraScratch)

structure RightEndCompactionMachineContract
    (D : MachineDescription) (extraScratch : Nat) : Prop where
  subroutineReady : D.SubroutineReady
  haltsFromTape :
    forall leftCells : List (Option Bool),
      D.HaltsFromTape
        (rightEndCompactionSourceTape leftCells)
        (rightEndCompactionTargetTape leftCells extraScratch)

theorem filterMap_replicate_none
    (n : Nat) :
    (List.replicate n (none : Option Bool)).filterMap
        (fun cell => cell) = [] := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [List.replicate, ih]

theorem filterMap_map_some
    (bits : Word Bool) :
    (bits.map some).filterMap (fun cell => cell) = bits := by
  simp [Function.comp_def]

theorem filterMap_length_le
    (cells : List (Option Bool)) :
    (cells.filterMap (fun cell => cell)).length <= cells.length := by
  induction cells with
  | nil =>
      simp
  | cons cell rest ih =>
      cases cell <;> simp [ih] <;> omega

theorem rightScratchOutputCells_filterMap
    (output : Word Bool) (scratchWidth : Nat) :
    (rightScratchOutputCells output scratchWidth).filterMap
        (fun cell => cell) =
      output := by
  simp [rightScratchOutputCells, List.filterMap_append,
    Function.comp_def]

theorem rightScratchOutputCells_length
    (output : Word Bool) (scratchWidth : Nat) :
    (rightScratchOutputCells output scratchWidth).length =
      output.length + scratchWidth := by
  simp [rightScratchOutputCells]

theorem FSTTargetTape_cells_cons_cons
    (first second : Bool) (rest : Word Bool)
    (scratchWidth : Nat) :
    Tape.cells
        (FSTTargetTape (first :: second :: rest) scratchWidth) =
      rightScratchOutputCells
        (first :: second :: rest) scratchWidth := by
  simp [FSTTargetTape, inputWithTrailingBlankPadding,
    rightScratchOutputCells, Tape.move, Tape.moveRight, Tape.cells]

theorem FSTTargetTape_cells_eq_rightScratchOutputCells
    (output : Word Bool) (scratchWidth : Nat)
    (first second : Bool) (rest : Word Bool)
    (houtput : output = first :: second :: rest) :
    Tape.cells (FSTTargetTape output scratchWidth) =
      rightScratchOutputCells output scratchWidth := by
  rw [houtput]
  exact FSTTargetTape_cells_cons_cons first second rest scratchWidth

theorem compactedCellsWithScratch_filterMap
    (cells : List (Option Bool)) (extraScratch : Nat) :
    (compactedCellsWithScratch cells extraScratch).filterMap
        (fun cell => cell) =
      cells.filterMap (fun cell => cell) := by
  rw [compactedCellsWithScratch]
  exact rightScratchOutputCells_filterMap
    (cells.filterMap (fun cell => cell))
    (cells.length - (cells.filterMap (fun cell => cell)).length +
      extraScratch)

theorem compactedCellsWithScratch_length
    (cells : List (Option Bool)) (extraScratch : Nat) :
    (compactedCellsWithScratch cells extraScratch).length =
      cells.length + extraScratch := by
  have hle := filterMap_length_le cells
  rw [compactedCellsWithScratch, rightScratchOutputCells_length]
  omega

theorem compactedCellsWithScratch_of_filterMap_length
    (cells : List (Option Bool)) (output : Word Bool)
    (baseScratch extraScratch : Nat)
    (hfilter : cells.filterMap (fun cell => cell) = output)
    (hlen : cells.length = output.length + baseScratch) :
    compactedCellsWithScratch cells extraScratch =
      rightScratchOutputCells output (baseScratch + extraScratch) := by
  rw [compactedCellsWithScratch, hfilter]
  have hscratch :
      cells.length - output.length + extraScratch =
        baseScratch + extraScratch := by
    omega
  rw [hscratch]

theorem rightEndCompactionVisibleCells_filterMap
    (leftCells : List (Option Bool)) :
    (rightEndCompactionVisibleCells leftCells).filterMap
        (fun cell => cell) =
      leftCells.filterMap (fun cell => cell) := by
  simp [rightEndCompactionVisibleCells, List.filterMap_append]

theorem rightEndCompactionSourceTape_cells
    (leftCells : List (Option Bool)) :
    Tape.cells (rightEndCompactionSourceTape leftCells) =
      rightEndCompactionVisibleCells leftCells := by
  simp [rightEndCompactionSourceTape,
    rightEndCompactionVisibleCells, tapeAtCells, Tape.cells]

theorem rightEndCompactionSourceTapeWithRightPadding_nil
    (leftCells : List (Option Bool)) :
    rightEndCompactionSourceTapeWithRightPadding leftCells [] =
      rightEndCompactionSourceTape leftCells := by
  rfl

theorem rightEndCompactionSourceTapeWithRightPadding_cells
    (leftCells rightPadding : List (Option Bool)) :
    Tape.cells
        (rightEndCompactionSourceTapeWithRightPadding
          leftCells rightPadding) =
      List.append (rightEndCompactionVisibleCells leftCells)
        rightPadding := by
  simp [rightEndCompactionSourceTapeWithRightPadding,
    rightEndCompactionVisibleCells, tapeAtCells, Tape.cells,
    List.append_assoc]

theorem rightEndCompactionTargetTape_normalizedOutput
    (leftCells : List (Option Bool)) (extraScratch : Nat) :
    Tape.normalizedOutput
        (rightEndCompactionTargetTape leftCells extraScratch) =
      leftCells.filterMap (fun cell => cell) := by
  rw [rightEndCompactionTargetTape]
  rw [FSTTargetTape_normalizedOutput]
  exact rightEndCompactionVisibleCells_filterMap leftCells

theorem rightEndCompactionTargetTape_cells_eq_compacted
    (leftCells : List (Option Bool)) (extraScratch : Nat)
    (first second : Bool) (rest : Word Bool)
    (houtput :
      (rightEndCompactionVisibleCells leftCells).filterMap
          (fun cell => cell) =
        first :: second :: rest) :
    Tape.cells
        (rightEndCompactionTargetTape leftCells extraScratch) =
      compactedCellsWithScratch
        (rightEndCompactionVisibleCells leftCells)
        extraScratch := by
  rw [rightEndCompactionTargetTape]
  rw [FSTTargetTape_cells_eq_rightScratchOutputCells
    ((rightEndCompactionVisibleCells leftCells).filterMap
      (fun cell => cell))
    (compactionScratchWidth
      (rightEndCompactionVisibleCells leftCells) extraScratch)
    first second rest houtput]
  rfl

theorem compactedCellsWithScratch_twoChunks
    (leftBlanks gapBlanks trailingBlanks extraScratch : Nat)
    (pref suffix : Word Bool) :
    compactedCellsWithScratch
        (List.append
          (List.replicate leftBlanks (none : Option Bool))
          (List.append
            (pref.map some)
            (List.append
              (List.replicate gapBlanks (none : Option Bool))
              (List.append
                (suffix.map some)
                (List.replicate trailingBlanks
                  (none : Option Bool))))))
        extraScratch =
      rightScratchOutputCells
        (List.append pref suffix)
        (leftBlanks + gapBlanks + trailingBlanks + extraScratch) := by
  apply compactedCellsWithScratch_of_filterMap_length
  · simp [List.filterMap_append, Function.comp_def]
  · simp
    omega

theorem compactedCellsWithScratch_threeChunks
    (leftBlanks firstGapBlanks secondGapBlanks trailingBlanks
      extraScratch : Nat)
    (pref middle suffix : Word Bool) :
    compactedCellsWithScratch
        (List.append
          (List.replicate leftBlanks (none : Option Bool))
          (List.append
            (pref.map some)
            (List.append
              (List.replicate firstGapBlanks (none : Option Bool))
              (List.append
                (middle.map some)
                (List.append
                  (List.replicate secondGapBlanks
                    (none : Option Bool))
                  (List.append
                    (suffix.map some)
                    (List.replicate trailingBlanks
                      (none : Option Bool))))))))
        extraScratch =
      rightScratchOutputCells
        (List.append pref (List.append middle suffix))
        (leftBlanks + firstGapBlanks + secondGapBlanks +
          trailingBlanks + extraScratch) := by
  apply compactedCellsWithScratch_of_filterMap_length
  · simp [List.filterMap_append, Function.comp_def]
  · simp
    omega

end FiniteTransducers
end CommonGround

end Computability
end FoC
