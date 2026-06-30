import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Compaction

set_option doc.verso true

/-!
# Executable left-shift compaction core

This module proves the first executable compaction slice.  The machine starts
on a blank immediately before a contiguous Boolean payload, shifts that payload
one cell left over the blank, leaves right scratch blanks, and halts at the
right edge.  Later compaction passes can use this as the local movement core
inside a repeated gap-closing loop.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

def leadingBlankLeftShiftDescription : MachineDescription where
  stateCount := 6
  start := 0
  halt := 5
  transitions :=
    [ transition 0 none none Direction.right 1
    , transition 1 none none Direction.right 5
    , transition 1 (some false) none Direction.left 2
    , transition 1 (some true) none Direction.left 3
    , transition 2 none (some false) Direction.right 4
    , transition 3 none (some true) Direction.right 4
    , transition 4 none none Direction.right 1 ]

def leadingBlankLeftShiftSourceTape
    (baseLeft : List (Option Bool)) (bits : Word Bool) : Tape Bool :=
  tapeAtCells baseLeft
    (none :: List.append (bits.map some) [none])

def leadingBlankLeftShiftLoopTape
    (baseLeft : List (Option Bool))
    (processed remaining : Word Bool) : Tape Bool :=
  tapeAtCells
    (none :: List.append (processed.reverse.map some) baseLeft)
    (List.append (remaining.map some) [none])

def leadingBlankLeftShiftTargetTape
    (baseLeft : List (Option Bool)) (bits : Word Bool) : Tape Bool :=
  tapeAtCells
    (none :: none ::
      List.append (bits.reverse.map some) baseLeft)
    []

def leadingBlankLeftShiftSourceTapeWithPadding
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells baseLeft
    (none :: List.append (bits.map some) (none :: padding))

def leadingBlankLeftShiftLoopTapeWithPadding
    (baseLeft : List (Option Bool))
    (processed remaining : Word Bool)
    (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (none :: List.append (processed.reverse.map some) baseLeft)
    (List.append (remaining.map some) (none :: padding))

def leadingBlankLeftShiftTargetTapeWithPadding
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (none :: none ::
      List.append (bits.reverse.map some) baseLeft)
    padding

def leadingBlankLeftShiftSourceCells
    (baseLeft : List (Option Bool)) (bits : Word Bool) :
    List (Option Bool) :=
  List.append baseLeft.reverse
    (none :: List.append (bits.map some) [none])

def leadingBlankLeftShiftTargetCells
    (baseLeft : List (Option Bool)) (bits : Word Bool) :
    List (Option Bool) :=
  List.append baseLeft.reverse
    (List.append (bits.map some) [none, none, none])

def leadingBlankLeftShiftSourceCellsWithPadding
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) : List (Option Bool) :=
  List.append baseLeft.reverse
    (none :: List.append (bits.map some) (none :: padding))

def leadingBlankLeftShiftTargetVisiblePadding
    (padding : List (Option Bool)) : List (Option Bool) :=
  match padding with
  | [] => [none]
  | _ :: _ => padding

def leadingBlankLeftShiftTargetCellsWithPadding
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) : List (Option Bool) :=
  List.append baseLeft.reverse
    (List.append (bits.map some)
      (List.append [none, none]
        (leadingBlankLeftShiftTargetVisiblePadding padding)))

def leadingBlankGapBaseLeft
    (pref : Word Bool) (gap : Nat) : List (Option Bool) :=
  List.append
    (List.replicate gap (none : Option Bool))
    (pref.reverse.map some)

structure LeadingBlankLeftShiftMachineContract
    (D : MachineDescription) : Prop where
  subroutineReady : D.SubroutineReady
  haltsFromTape :
    forall (baseLeft : List (Option Bool)) (bits : Word Bool),
      D.HaltsFromTape
        (leadingBlankLeftShiftSourceTape baseLeft bits)
        (leadingBlankLeftShiftTargetTape baseLeft bits)

structure LeadingBlankLeftShiftWithPaddingMachineContract
    (D : MachineDescription) : Prop where
  subroutineReady : D.SubroutineReady
  haltsFromTape :
    forall (baseLeft : List (Option Bool)) (bits : Word Bool)
      (padding : List (Option Bool)),
      D.HaltsFromTape
        (leadingBlankLeftShiftSourceTapeWithPadding
          baseLeft bits padding)
        (leadingBlankLeftShiftTargetTapeWithPadding
          baseLeft bits padding)

theorem leadingBlankLeftShiftDescription_wellFormed :
    leadingBlankLeftShiftDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := leadingBlankLeftShiftDescription.transitions)
      (stateCount := leadingBlankLeftShiftDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := leadingBlankLeftShiftDescription.transitions)
      (by decide)

theorem leadingBlankLeftShiftDescription_haltTransitionFree :
    leadingBlankLeftShiftDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := leadingBlankLeftShiftDescription.transitions)
    (state := leadingBlankLeftShiftDescription.halt)
    (by decide)

theorem leadingBlankLeftShiftDescription_subroutineReady :
    leadingBlankLeftShiftDescription.SubroutineReady :=
  ⟨leadingBlankLeftShiftDescription_wellFormed,
    leadingBlankLeftShiftDescription_haltTransitionFree⟩

theorem leadingBlankLeftShiftDescription_run_start
    (baseLeft : List (Option Bool)) (bits : Word Bool) :
    leadingBlankLeftShiftDescription.runConfig 1
        { state := leadingBlankLeftShiftDescription.start
          tape := leadingBlankLeftShiftSourceTape baseLeft bits } =
      { state := 1
        tape := leadingBlankLeftShiftLoopTape baseLeft [] bits } := by
  cases bits <;>
    simp [leadingBlankLeftShiftDescription,
      leadingBlankLeftShiftSourceTape,
      leadingBlankLeftShiftLoopTape, runConfig, stepConfig,
      lookupTransition, Matches, transition, Tape.read, Tape.write,
      Tape.move, Tape.moveRight, tapeAtCells]

theorem leadingBlankLeftShiftDescription_run_bit
    (baseLeft : List (Option Bool))
    (processed rest : Word Bool) (bit : Bool) :
    leadingBlankLeftShiftDescription.runConfig 3
        { state := 1
          tape :=
            leadingBlankLeftShiftLoopTape
              baseLeft processed (bit :: rest) } =
      { state := 1
        tape :=
          leadingBlankLeftShiftLoopTape
            baseLeft (List.append processed [bit]) rest } := by
  cases bit <;> cases rest <;>
    simp [leadingBlankLeftShiftDescription,
      leadingBlankLeftShiftLoopTape, runConfig, stepConfig,
      lookupTransition, Matches, transition, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells,
      List.reverse_append]

theorem leadingBlankLeftShiftDescription_run_finish
    (baseLeft : List (Option Bool)) (processed : Word Bool) :
    leadingBlankLeftShiftDescription.runConfig 1
        { state := 1
          tape := leadingBlankLeftShiftLoopTape baseLeft processed [] } =
      { state := leadingBlankLeftShiftDescription.halt
        tape := leadingBlankLeftShiftTargetTape baseLeft processed } := by
  simp [leadingBlankLeftShiftDescription,
    leadingBlankLeftShiftLoopTape, leadingBlankLeftShiftTargetTape,
    runConfig, stepConfig, lookupTransition, Matches, transition,
    Tape.read, Tape.write, Tape.move, Tape.moveRight, tapeAtCells]

theorem leadingBlankLeftShiftDescription_run_loop
    (baseLeft : List (Option Bool))
    (processed remaining : Word Bool) :
    leadingBlankLeftShiftDescription.runConfig
        (3 * remaining.length + 1)
        { state := 1
          tape :=
            leadingBlankLeftShiftLoopTape
              baseLeft processed remaining } =
      { state := leadingBlankLeftShiftDescription.halt
        tape :=
          leadingBlankLeftShiftTargetTape
            baseLeft (List.append processed remaining) } := by
  induction remaining generalizing processed with
  | nil =>
      simpa using
        leadingBlankLeftShiftDescription_run_finish baseLeft processed
  | cons bit rest ih =>
      rw [show 3 * (bit :: rest).length + 1 =
          3 + (3 * rest.length + 1) by
        simp
        omega]
      rw [runConfig_add]
      rw [leadingBlankLeftShiftDescription_run_bit]
      simpa [List.append_assoc] using
        ih (List.append processed [bit])

theorem leadingBlankLeftShiftDescription_run_to_target
    (baseLeft : List (Option Bool)) (bits : Word Bool) :
    leadingBlankLeftShiftDescription.runConfig
        (3 * bits.length + 2)
        { state := leadingBlankLeftShiftDescription.start
          tape := leadingBlankLeftShiftSourceTape baseLeft bits } =
      { state := leadingBlankLeftShiftDescription.halt
        tape := leadingBlankLeftShiftTargetTape baseLeft bits } := by
  rw [show 3 * bits.length + 2 =
      1 + (3 * bits.length + 1) by omega]
  rw [runConfig_add]
  rw [leadingBlankLeftShiftDescription_run_start]
  simpa using
    leadingBlankLeftShiftDescription_run_loop baseLeft [] bits

theorem leadingBlankLeftShiftDescription_haltsFromTape
    (baseLeft : List (Option Bool)) (bits : Word Bool) :
    leadingBlankLeftShiftDescription.HaltsFromTape
      (leadingBlankLeftShiftSourceTape baseLeft bits)
      (leadingBlankLeftShiftTargetTape baseLeft bits) := by
  refine ⟨3 * bits.length + 2, ?_⟩
  constructor <;>
    rw [leadingBlankLeftShiftDescription_run_to_target]

theorem leadingBlankLeftShiftDescription_run_start_withPadding
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    leadingBlankLeftShiftDescription.runConfig 1
        { state := leadingBlankLeftShiftDescription.start
          tape :=
            leadingBlankLeftShiftSourceTapeWithPadding
              baseLeft bits padding } =
      { state := 1
        tape :=
          leadingBlankLeftShiftLoopTapeWithPadding
            baseLeft [] bits padding } := by
  cases bits <;>
    simp [leadingBlankLeftShiftDescription,
      leadingBlankLeftShiftSourceTapeWithPadding,
      leadingBlankLeftShiftLoopTapeWithPadding, runConfig, stepConfig,
      lookupTransition, Matches, transition, Tape.read, Tape.write,
      Tape.move, Tape.moveRight, tapeAtCells]

theorem leadingBlankLeftShiftDescription_run_bit_withPadding
    (baseLeft : List (Option Bool))
    (processed rest : Word Bool) (bit : Bool)
    (padding : List (Option Bool)) :
    leadingBlankLeftShiftDescription.runConfig 3
        { state := 1
          tape :=
            leadingBlankLeftShiftLoopTapeWithPadding
              baseLeft processed (bit :: rest) padding } =
      { state := 1
        tape :=
          leadingBlankLeftShiftLoopTapeWithPadding
            baseLeft (List.append processed [bit]) rest padding } := by
  cases bit <;> cases rest <;>
    simp [leadingBlankLeftShiftDescription,
      leadingBlankLeftShiftLoopTapeWithPadding, runConfig, stepConfig,
      lookupTransition, Matches, transition, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells,
      List.reverse_append]

theorem leadingBlankLeftShiftDescription_run_finish_withPadding
    (baseLeft : List (Option Bool)) (processed : Word Bool)
    (padding : List (Option Bool)) :
    leadingBlankLeftShiftDescription.runConfig 1
        { state := 1
          tape :=
            leadingBlankLeftShiftLoopTapeWithPadding
              baseLeft processed [] padding } =
      { state := leadingBlankLeftShiftDescription.halt
        tape :=
          leadingBlankLeftShiftTargetTapeWithPadding
            baseLeft processed padding } := by
  cases padding <;>
    simp [leadingBlankLeftShiftDescription,
      leadingBlankLeftShiftLoopTapeWithPadding,
      leadingBlankLeftShiftTargetTapeWithPadding,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight, tapeAtCells]

theorem leadingBlankLeftShiftDescription_run_loop_withPadding
    (baseLeft : List (Option Bool))
    (processed remaining : Word Bool)
    (padding : List (Option Bool)) :
    leadingBlankLeftShiftDescription.runConfig
        (3 * remaining.length + 1)
        { state := 1
          tape :=
            leadingBlankLeftShiftLoopTapeWithPadding
              baseLeft processed remaining padding } =
      { state := leadingBlankLeftShiftDescription.halt
        tape :=
          leadingBlankLeftShiftTargetTapeWithPadding
            baseLeft (List.append processed remaining) padding } := by
  induction remaining generalizing processed with
  | nil =>
      simpa using
        leadingBlankLeftShiftDescription_run_finish_withPadding
          baseLeft processed padding
  | cons bit rest ih =>
      rw [show 3 * (bit :: rest).length + 1 =
          3 + (3 * rest.length + 1) by
        simp
        omega]
      rw [runConfig_add]
      rw [leadingBlankLeftShiftDescription_run_bit_withPadding]
      simpa [List.append_assoc] using
        ih (List.append processed [bit])

theorem leadingBlankLeftShiftDescription_run_to_target_withPadding
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    leadingBlankLeftShiftDescription.runConfig
        (3 * bits.length + 2)
        { state := leadingBlankLeftShiftDescription.start
          tape :=
            leadingBlankLeftShiftSourceTapeWithPadding
              baseLeft bits padding } =
      { state := leadingBlankLeftShiftDescription.halt
        tape :=
          leadingBlankLeftShiftTargetTapeWithPadding
            baseLeft bits padding } := by
  rw [show 3 * bits.length + 2 =
      1 + (3 * bits.length + 1) by omega]
  rw [runConfig_add]
  rw [leadingBlankLeftShiftDescription_run_start_withPadding]
  simpa using
    leadingBlankLeftShiftDescription_run_loop_withPadding
      baseLeft [] bits padding

theorem leadingBlankLeftShiftDescription_haltsFromTape_withPadding
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    leadingBlankLeftShiftDescription.HaltsFromTape
      (leadingBlankLeftShiftSourceTapeWithPadding
        baseLeft bits padding)
      (leadingBlankLeftShiftTargetTapeWithPadding
        baseLeft bits padding) := by
  refine ⟨3 * bits.length + 2, ?_⟩
  constructor <;>
    rw [leadingBlankLeftShiftDescription_run_to_target_withPadding]

theorem leadingBlankLeftShiftDescription_contract :
    LeadingBlankLeftShiftMachineContract
      leadingBlankLeftShiftDescription where
  subroutineReady := leadingBlankLeftShiftDescription_subroutineReady
  haltsFromTape := leadingBlankLeftShiftDescription_haltsFromTape

theorem leadingBlankLeftShiftDescription_withPadding_contract :
    LeadingBlankLeftShiftWithPaddingMachineContract
      leadingBlankLeftShiftDescription where
  subroutineReady := leadingBlankLeftShiftDescription_subroutineReady
  haltsFromTape := leadingBlankLeftShiftDescription_haltsFromTape_withPadding

theorem leadingBlankLeftShiftSourceTape_cells
    (baseLeft : List (Option Bool)) (bits : Word Bool) :
    Tape.cells (leadingBlankLeftShiftSourceTape baseLeft bits) =
      leadingBlankLeftShiftSourceCells baseLeft bits := by
  cases bits <;>
    simp [leadingBlankLeftShiftSourceCells,
      leadingBlankLeftShiftSourceTape, tapeAtCells, Tape.cells]

theorem leadingBlankLeftShiftTargetTape_cells
    (baseLeft : List (Option Bool)) (bits : Word Bool) :
    Tape.cells (leadingBlankLeftShiftTargetTape baseLeft bits) =
      leadingBlankLeftShiftTargetCells baseLeft bits := by
  simp [leadingBlankLeftShiftTargetTape, tapeAtCells, Tape.cells,
    leadingBlankLeftShiftTargetCells, List.reverse_append,
    List.map_reverse, List.append_assoc]

theorem leadingBlankLeftShiftSourceTapeWithPadding_cells
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (leadingBlankLeftShiftSourceTapeWithPadding
          baseLeft bits padding) =
      leadingBlankLeftShiftSourceCellsWithPadding
        baseLeft bits padding := by
  cases bits <;>
    simp [leadingBlankLeftShiftSourceTapeWithPadding,
      leadingBlankLeftShiftSourceCellsWithPadding,
      tapeAtCells, Tape.cells]

theorem leadingBlankLeftShiftTargetTapeWithPadding_cells
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (leadingBlankLeftShiftTargetTapeWithPadding
          baseLeft bits padding) =
      leadingBlankLeftShiftTargetCellsWithPadding
        baseLeft bits padding := by
  cases padding <;>
    simp [leadingBlankLeftShiftTargetTapeWithPadding,
      leadingBlankLeftShiftTargetCellsWithPadding,
      leadingBlankLeftShiftTargetVisiblePadding,
      tapeAtCells, Tape.cells, List.reverse_append,
      List.map_reverse, List.append_assoc]

theorem leadingBlankGapBaseLeft_reverse
    (pref : Word Bool) (gap : Nat) :
    (leadingBlankGapBaseLeft pref gap).reverse =
      List.append (pref.map some)
        (List.replicate gap (none : Option Bool)) := by
  simp [leadingBlankGapBaseLeft, List.reverse_append,
    List.map_reverse]

theorem leadingBlankLeftShiftTargetCells_eq_shifted
    (baseLeft : List (Option Bool)) (bits : Word Bool) :
    leadingBlankLeftShiftTargetCells baseLeft bits =
      List.append baseLeft.reverse
        (List.append (bits.map some)
          (List.replicate 3 (none : Option Bool))) := by
  simp [leadingBlankLeftShiftTargetCells, List.replicate]

theorem leadingBlankLeftShiftSourceCellsWithPadding_gap
    (pref suffix : Word Bool) (gap : Nat)
    (padding : List (Option Bool)) :
    leadingBlankLeftShiftSourceCellsWithPadding
        (leadingBlankGapBaseLeft pref gap)
        suffix padding =
      List.append (pref.map some)
        (List.append
          (List.replicate gap (none : Option Bool))
          (none :: List.append (suffix.map some)
            (none :: padding))) := by
  rw [leadingBlankLeftShiftSourceCellsWithPadding,
    leadingBlankGapBaseLeft_reverse]
  simp [List.append_assoc]

theorem leadingBlankLeftShiftTargetCellsWithPadding_gap
    (pref suffix : Word Bool) (gap : Nat)
    (padding : List (Option Bool)) :
    leadingBlankLeftShiftTargetCellsWithPadding
        (leadingBlankGapBaseLeft pref gap)
        suffix padding =
      List.append (pref.map some)
        (List.append
          (List.replicate gap (none : Option Bool))
          (List.append (suffix.map some)
            (List.append [none, none]
              (leadingBlankLeftShiftTargetVisiblePadding padding)))) := by
  rw [leadingBlankLeftShiftTargetCellsWithPadding,
    leadingBlankGapBaseLeft_reverse]
  simp [List.append_assoc]

theorem leadingBlankLeftShiftSourceCells_filterMap
    (baseLeft : List (Option Bool)) (bits : Word Bool) :
    (leadingBlankLeftShiftSourceCells baseLeft bits).filterMap
        (fun cell => cell) =
      List.append (baseLeft.reverse.filterMap (fun cell => cell))
        bits := by
  simp [leadingBlankLeftShiftSourceCells, List.filterMap_append,
    Function.comp_def]

theorem leadingBlankLeftShiftTargetCells_filterMap
    (baseLeft : List (Option Bool)) (bits : Word Bool) :
    (leadingBlankLeftShiftTargetCells baseLeft bits).filterMap
        (fun cell => cell) =
      List.append (baseLeft.reverse.filterMap (fun cell => cell))
        bits := by
  simp [leadingBlankLeftShiftTargetCells, List.filterMap_append,
    Function.comp_def]

theorem leadingBlankLeftShiftTargetVisiblePadding_filterMap
    (padding : List (Option Bool)) :
    (leadingBlankLeftShiftTargetVisiblePadding padding).filterMap
        (fun cell => cell) =
      padding.filterMap (fun cell => cell) := by
  cases padding <;>
    simp [leadingBlankLeftShiftTargetVisiblePadding]

theorem leadingBlankLeftShiftSourceCellsWithPadding_filterMap
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
  (leadingBlankLeftShiftSourceCellsWithPadding
        baseLeft bits padding).filterMap (fun cell => cell) =
      List.append
        (baseLeft.reverse.filterMap (fun cell => cell))
        (List.append bits (padding.filterMap (fun cell => cell))) := by
  simp [leadingBlankLeftShiftSourceCellsWithPadding,
    List.filterMap_append, Function.comp_def]

theorem leadingBlankLeftShiftTargetCellsWithPadding_filterMap
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
  (leadingBlankLeftShiftTargetCellsWithPadding
        baseLeft bits padding).filterMap (fun cell => cell) =
      List.append
        (baseLeft.reverse.filterMap (fun cell => cell))
        (List.append bits (padding.filterMap (fun cell => cell))) := by
  simp [leadingBlankLeftShiftTargetCellsWithPadding,
    leadingBlankLeftShiftTargetVisiblePadding_filterMap,
    List.filterMap_append, Function.comp_def]

theorem leadingBlankLeftShiftSourceTape_normalizedOutput
    (baseLeft : List (Option Bool)) (bits : Word Bool) :
    Tape.normalizedOutput
        (leadingBlankLeftShiftSourceTape baseLeft bits) =
      List.append (baseLeft.reverse.filterMap (fun cell => cell))
        bits := by
  rw [Tape.normalizedOutput, leadingBlankLeftShiftSourceTape_cells]
  simp [leadingBlankLeftShiftSourceCells, List.filterMap_append,
    Function.comp_def]

theorem leadingBlankLeftShiftSourceTapeWithPadding_normalizedOutput
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (leadingBlankLeftShiftSourceTapeWithPadding
          baseLeft bits padding) =
      List.append
        (baseLeft.reverse.filterMap (fun cell => cell))
        (List.append bits (padding.filterMap (fun cell => cell))) := by
  rw [Tape.normalizedOutput,
    leadingBlankLeftShiftSourceTapeWithPadding_cells]
  exact leadingBlankLeftShiftSourceCellsWithPadding_filterMap
    baseLeft bits padding

theorem leadingBlankLeftShiftTargetTape_cells_eq_compacted_source
    (bits : Word Bool) :
    Tape.cells (leadingBlankLeftShiftTargetTape [] bits) =
      compactedCellsWithScratch
        (Tape.cells (leadingBlankLeftShiftSourceTape [] bits))
        1 := by
  rw [leadingBlankLeftShiftTargetTape_cells,
    leadingBlankLeftShiftSourceTape_cells]
  simpa [List.replicate, List.append_assoc,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (compactedCellsWithScratch_twoChunks
      1 0 1 1 ([] : Word Bool) bits).symm

theorem leadingBlankLeftShiftTargetTape_normalizedOutput
    (baseLeft : List (Option Bool)) (bits : Word Bool) :
    Tape.normalizedOutput
        (leadingBlankLeftShiftTargetTape baseLeft bits) =
      List.append (baseLeft.reverse.filterMap (fun cell => cell))
        bits := by
  rw [Tape.normalizedOutput, leadingBlankLeftShiftTargetTape_cells]
  simp [leadingBlankLeftShiftTargetCells, List.filterMap_append,
    Function.comp_def]

theorem leadingBlankLeftShiftTargetTapeWithPadding_normalizedOutput
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (leadingBlankLeftShiftTargetTapeWithPadding
          baseLeft bits padding) =
      List.append
        (baseLeft.reverse.filterMap (fun cell => cell))
        (List.append bits (padding.filterMap (fun cell => cell))) := by
  rw [Tape.normalizedOutput,
    leadingBlankLeftShiftTargetTapeWithPadding_cells]
  exact leadingBlankLeftShiftTargetCellsWithPadding_filterMap
    baseLeft bits padding

theorem leadingBlankLeftShift_normalizedOutput_preserved
    (baseLeft : List (Option Bool)) (bits : Word Bool) :
    Tape.normalizedOutput
        (leadingBlankLeftShiftTargetTape baseLeft bits) =
      Tape.normalizedOutput
        (leadingBlankLeftShiftSourceTape baseLeft bits) := by
  rw [leadingBlankLeftShiftTargetTape_normalizedOutput,
    leadingBlankLeftShiftSourceTape_normalizedOutput]

theorem leadingBlankLeftShift_withPadding_normalizedOutput_preserved
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (leadingBlankLeftShiftTargetTapeWithPadding
          baseLeft bits padding) =
      Tape.normalizedOutput
        (leadingBlankLeftShiftSourceTapeWithPadding
          baseLeft bits padding) := by
  rw [leadingBlankLeftShiftTargetTapeWithPadding_normalizedOutput,
    leadingBlankLeftShiftSourceTapeWithPadding_normalizedOutput]

end FiniteTransducers
end CommonGround

end Computability
end FoC
