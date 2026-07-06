import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.Projection
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.ConcreteRefresh
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.ThreeTapeTactic
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTableChecks

set_option doc.verso true

/-!
# Pair-encoded option-cell compactor

This module contains a small lowerer-facing three-tape component for the
selected-footprint compaction route.  Tape 0 carries cells encoded as
{lit}`[none, cell]`, tape 1 carries one marker per decoded cell, and tape 2 receives
all decoded cells except the final pending boundary cell.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering
namespace PairEncodedOptionCellCompactor

def markerCell : Option Bool := some true

@[simp] theorem replicate_markerCell_add_one (n : Nat) :
    List.replicate (n + 1) markerCell =
      markerCell :: List.replicate n markerCell := by
  simp [markerCell, List.replicate_succ]

@[simp] theorem replicate_some_true_add_one (n : Nat) :
    List.replicate (n + 1) (some true : Option Bool) =
      some true :: List.replicate n (some true : Option Bool) := by
  simpa [markerCell] using replicate_markerCell_add_one n

def encodedCells (cells : List (Option Bool)) : List (Option Bool) :=
  (cells.map selectedSegmentLogicalTapeDecoderCellCells).flatten

@[simp] theorem selectedSegmentLogicalTapeDecoderCellCells_eq_pair
    (cell : Option Bool) :
    selectedSegmentLogicalTapeDecoderCellCells cell = [none, cell] := by
  cases cell with
  | none =>
      rfl
  | some bit =>
      rfl

@[simp] theorem encodedCells_nil :
    encodedCells [] = [] := by
  rfl

@[simp] theorem encodedCells_cons
    (cell : Option Bool) (rest : List (Option Bool)) :
    encodedCells (cell :: rest) = none :: cell :: encodedCells rest := by
  simp [encodedCells]

theorem encodedCells_append
    (left right : List (Option Bool)) :
    encodedCells (left ++ right) = encodedCells left ++ encodedCells right := by
  induction left with
  | nil =>
      rfl
  | cons cell rest ih =>
      simp [ih]

theorem encodedCells_append_singleton
    (cells : List (Option Bool)) (boundary : Option Bool) :
    encodedCells (cells ++ [boundary]) =
      encodedCells cells ++ [none, boundary] := by
  simp [encodedCells_append]

@[simp] theorem encodedCells_eq_nil_iff
    (cells : List (Option Bool)) :
    encodedCells cells = [] ↔ cells = [] := by
  cases cells <;> simp

@[simp] theorem mappedSelectedCells_flatten_eq_nil_iff
    (cells : List (Option Bool)) :
    (List.map selectedSegmentLogicalTapeDecoderCellCells cells).flatten = [] ↔
      cells = [] := by
  simpa [encodedCells] using encodedCells_eq_nil_iff cells

@[simp] theorem forall_not_mem_option_bool_iff_eq_nil
    (cells : List (Option Bool)) :
    (forall cell : Option Bool, ¬ cell ∈ cells) ↔ cells = [] := by
  constructor
  · intro h
    cases cells with
    | nil =>
        rfl
    | cons cell rest =>
        exact False.elim (h cell (by simp))
  · intro h cell hmem
    simp [h] at hmem

def dropLastWithPending
    (pending : Option Bool) : List (Option Bool) -> List (Option Bool)
  | [] => []
  | cell :: rest => pending :: dropLastWithPending cell rest

def dropFinalCell : List (Option Bool) -> List (Option Bool)
  | [] => []
  | cell :: rest => dropLastWithPending cell rest

private theorem dropLastWithPending_append_singleton
    (pending : Option Bool) (cells : List (Option Bool))
    (last : Option Bool) :
    dropLastWithPending pending (cells ++ [last]) =
      pending :: cells := by
  induction cells generalizing pending with
  | nil =>
      rfl
  | cons cell rest ih =>
      simp [dropLastWithPending, ih]

theorem dropFinalCell_append_singleton
    (cells : List (Option Bool)) (last : Option Bool) :
    dropFinalCell (cells ++ [last]) = cells := by
  cases cells with
  | nil =>
      rfl
  | cons cell rest =>
      exact dropLastWithPending_append_singleton cell rest last

def sourceTapeAt
    (consumed remaining : List (Option Bool)) : Tape Bool :=
  tapeAtCells (encodedCells consumed).reverse (encodedCells remaining)

def sourceTape (cells : List (Option Bool)) : Tape Bool :=
  sourceTapeAt [] cells

theorem sourceTapeAt_append_singleton
    (consumed remaining : List (Option Bool)) (boundary : Option Bool) :
    sourceTapeAt consumed (remaining ++ [boundary]) =
      tapeAtCells (encodedCells consumed).reverse
        (encodedCells remaining ++ [none, boundary]) := by
  simp [sourceTapeAt, encodedCells_append_singleton]

def markerTapeAt (used remaining : Nat) : Tape Bool :=
  tapeAtCells
    (List.replicate used markerCell)
    (List.replicate remaining markerCell)

def markerTape (count : Nat) : Tape Bool :=
  markerTapeAt 0 count

theorem markerTapeAt_succ (used n : Nat) :
    markerTapeAt used (n + 1) =
      tapeAtCells
        (List.replicate used markerCell)
        (markerCell :: List.replicate n markerCell) := by
  simp [markerTapeAt, List.replicate_succ]

@[simp] theorem markerTapeAt_preserveRight_succ
    (used n : Nat) :
    (TapeAction.preserveMove HeadMove.right).apply
        (markerTapeAt used (n + 1)) =
      markerTapeAt (used + 1) n := by
  cases n <;>
    simp [markerTapeAt, tapeAtCells, List.replicate_succ, TapeAction.apply,
      HeadMove.apply, Tape.move, Tape.moveRight, markerCell]

@[simp] theorem markerTapeAt_stay
    (used remaining : Nat) :
    TapeAction.stay.apply (markerTapeAt used remaining) =
      markerTapeAt used remaining := by
  rfl

def outputTape (out : List (Option Bool)) : Tape Bool :=
  tapeAtCells out.reverse []

def pendingState : Option Bool -> Nat
  | none => 10
  | some false => 11
  | some true => 12

def pendingCell : Nat := 20

def haltState : Nat := 99

def rows : List Transition :=
  [ ThreeTape.row 0 none markerCell none ThreeTape.keepR ThreeTape.keepS ThreeTape.keepS 1
  , ThreeTape.row 1 none markerCell none ThreeTape.keepR ThreeTape.keepR ThreeTape.keepS
      (pendingState none)
  , ThreeTape.row 1 (some false) markerCell none ThreeTape.keepR ThreeTape.keepR ThreeTape.keepS
      (pendingState (some false))
  , ThreeTape.row 1 (some true) markerCell none ThreeTape.keepR ThreeTape.keepR ThreeTape.keepS
      (pendingState (some true))
  , ThreeTape.row (pendingState none) none markerCell none
      ThreeTape.keepR ThreeTape.keepS (ThreeTape.writeR none) pendingCell
  , ThreeTape.row (pendingState (some false)) none markerCell none
      ThreeTape.keepR ThreeTape.keepS (ThreeTape.writeR (some false)) pendingCell
  , ThreeTape.row (pendingState (some true)) none markerCell none
      ThreeTape.keepR ThreeTape.keepS (ThreeTape.writeR (some true)) pendingCell
  , ThreeTape.row (pendingState none) none none none
      ThreeTape.keepS ThreeTape.keepS ThreeTape.keepS haltState
  , ThreeTape.row (pendingState (some false)) none none none
      ThreeTape.keepS ThreeTape.keepS ThreeTape.keepS haltState
  , ThreeTape.row (pendingState (some true)) none none none
      ThreeTape.keepS ThreeTape.keepS ThreeTape.keepS haltState
  , ThreeTape.row pendingCell none markerCell none ThreeTape.keepR ThreeTape.keepR ThreeTape.keepS
      (pendingState none)
  , ThreeTape.row pendingCell (some false) markerCell none ThreeTape.keepR ThreeTape.keepR ThreeTape.keepS
      (pendingState (some false))
  , ThreeTape.row pendingCell (some true) markerCell none ThreeTape.keepR ThreeTape.keepR ThreeTape.keepS
      (pendingState (some true)) ]

def description : Description :=
  ThreeTape.description 100 0 haltState rows

theorem description_wellFormed :
    description.WellFormed := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
  · exact
      structuredTransition_wellFormed_of_all
        (l := description.transitions)
        (stateCount := description.stateCount)
        (tapeCount := description.tapeCount)
        (by decide)
  · exact
      structuredTransition_deterministic_of_all
        (l := description.transitions)
        (by decide)

theorem description_haltTransitionFree :
    description.HaltTransitionFree :=
  structuredTransition_notFrom_of_all
    (l := description.transitions)
    (state := description.halt)
    (by decide)

theorem description_supportsReadWriteRows3 :
    SupportsReadWriteRows3 description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

def initialConfig
    (first : Option Bool) (rest : List (Option Bool)) :
  Configuration :=
  ThreeTape.config 0
    (sourceTape (first :: rest))
    (markerTape (first :: rest).length)
    (outputTape [])

def pendingConfig
    (pending : Option Bool)
    (consumed remaining out : List (Option Bool)) :
  Configuration :=
  ThreeTape.config (pendingState pending)
    (sourceTapeAt consumed remaining)
    (markerTapeAt consumed.length remaining.length)
    (outputTape out)

def finalConfig
    (cells out : List (Option Bool)) : Configuration :=
  ThreeTape.config haltState
    (sourceTapeAt cells [])
    (markerTapeAt cells.length 0)
    (outputTape out)

private theorem outputTape_writeR
    (out : List (Option Bool)) (cell : Option Bool) :
    (ThreeTape.writeR cell).apply (outputTape out) =
      outputTape (out ++ [cell]) := by
  cases cell <;>
    simp [ThreeTape.writeR, outputTape, tapeAtCells, Tape.write,
      Structured.TapeAction.apply, Structured.HeadMove.apply,
      Tape.move, Tape.moveRight, List.reverse_append]

private theorem initial_run
    (first : Option Bool) (rest : List (Option Bool)) :
    description.runConfig 2 (initialConfig first rest) =
      pendingConfig first [first] rest [] := by
  cases first with
  | none =>
      three_tape_step [
        description, rows, initialConfig, pendingConfig, sourceTape,
        sourceTapeAt, markerTape, outputTape, encodedCells,
        markerTapeAt_succ, selectedSegmentLogicalTapeDecoderCellCells,
        markerCell, pendingState] <;>
        (constructor
         · split <;> simp_all
         · split <;> simp_all [markerTapeAt, markerCell, tapeAtCells])
  | some bit =>
      cases bit <;>
        three_tape_step [
          description, rows, initialConfig, pendingConfig, sourceTape,
          sourceTapeAt, markerTape, outputTape, encodedCells,
          markerTapeAt_succ, selectedSegmentLogicalTapeDecoderCellCells,
          markerCell, pendingState] <;>
          (constructor
           · split <;> simp_all
           · split <;> simp_all [markerTapeAt, markerCell, tapeAtCells])

private theorem pending_step
    (pending head : Option Bool)
    (consumed tail out : List (Option Bool)) :
    description.runConfig 2
        (pendingConfig pending consumed (head :: tail) out) =
      pendingConfig head (consumed ++ [head]) tail
        (out ++ [pending]) := by
  cases pending with
  | none =>
      cases head with
      | none =>
          three_tape_step [
            description, rows, pendingConfig, sourceTapeAt,
            outputTape, outputTape_writeR, encodedCells,
            markerTapeAt_succ, selectedSegmentLogicalTapeDecoderCellCells,
            markerCell, pendingState, pendingCell] <;>
            (constructor
             · split <;> simp_all
             · split <;> simp_all [markerTapeAt, markerCell, tapeAtCells])
      | some bit =>
          cases bit <;>
            three_tape_step [
              description, rows, pendingConfig, sourceTapeAt,
              outputTape, outputTape_writeR, encodedCells,
              markerTapeAt_succ, selectedSegmentLogicalTapeDecoderCellCells,
              markerCell, pendingState, pendingCell] <;>
              (constructor
               · split <;> simp_all
               · split <;> simp_all [markerTapeAt, markerCell, tapeAtCells])
  | some pendingBit =>
      cases pendingBit <;>
        cases head with
        | none =>
            three_tape_step [
              description, rows, pendingConfig, sourceTapeAt,
              outputTape, outputTape_writeR, encodedCells,
              markerTapeAt_succ, selectedSegmentLogicalTapeDecoderCellCells,
              markerCell, pendingState, pendingCell] <;>
              (constructor
               · split <;> simp_all
               · split <;> simp_all [markerTapeAt, markerCell, tapeAtCells])
        | some bit =>
            cases bit <;>
              three_tape_step [
                description, rows, pendingConfig, sourceTapeAt,
                outputTape, outputTape_writeR, encodedCells,
                markerTapeAt_succ, selectedSegmentLogicalTapeDecoderCellCells,
                markerCell, pendingState, pendingCell] <;>
                (constructor
                 · split <;> simp_all
                 · split <;> simp_all [markerTapeAt, markerCell, tapeAtCells])

private theorem pending_done
    (pending : Option Bool)
    (consumed out : List (Option Bool)) :
    description.runConfig 1 (pendingConfig pending consumed [] out) =
      finalConfig consumed out := by
  cases pending with
  | none =>
      three_tape_step [
        description, rows, pendingConfig, finalConfig, sourceTapeAt,
        markerTapeAt, outputTape, encodedCells,
        selectedSegmentLogicalTapeDecoderCellCells, markerCell, pendingState]
  | some bit =>
      cases bit <;>
        three_tape_step [
          description, rows, pendingConfig, finalConfig, sourceTapeAt,
          markerTapeAt, outputTape, encodedCells,
          selectedSegmentLogicalTapeDecoderCellCells, markerCell,
          pendingState]

private theorem pending_run
    (pending : Option Bool)
    (consumed remaining out : List (Option Bool)) :
    description.runConfig (2 * remaining.length + 1)
        (pendingConfig pending consumed remaining out) =
      finalConfig (consumed ++ remaining)
        (out ++ dropLastWithPending pending remaining) := by
  induction remaining generalizing pending consumed out with
  | nil =>
      simpa [dropLastWithPending] using
        pending_done pending consumed out
  | cons head tail ih =>
      rw [show 2 * (head :: tail).length + 1 =
          2 + (2 * tail.length + 1) by simp; lia]
      rw [Description.runConfig_add]
      rw [pending_step pending head consumed tail out]
      rw [ih head (consumed ++ [head]) (out ++ [pending])]
      simp [dropLastWithPending, List.append_assoc]

theorem run
    (first : Option Bool) (rest : List (Option Bool)) :
    description.runConfig (2 * rest.length + 3)
        (initialConfig first rest) =
      finalConfig (first :: rest) (dropFinalCell (first :: rest)) := by
  rw [show 2 * rest.length + 3 = 2 + (2 * rest.length + 1) by lia]
  rw [Description.runConfig_add]
  rw [initial_run first rest]
  simpa [dropFinalCell] using
    pending_run first [first] rest []

def loweredDescription : MachineDescription :=
  lowerStructured3Description description

theorem loweredDescription_wellFormed :
    loweredDescription.WellFormed := by
  simpa [loweredDescription] using
    lowerStructured3Description_wellFormed
      description_wellFormed
      description_supportsReadWriteRows3

theorem loweredDescription_subroutineReady :
    loweredDescription.SubroutineReady := by
  simpa [loweredDescription] using
    lowerStructured3Description_subroutineReady
      description_wellFormed
      description_supportsReadWriteRows3

theorem loweredDescription_haltsFromTape
    (first : Option Bool) (rest : List (Option Bool)) :
    loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructuredTapes
        [ sourceTape (first :: rest)
        , markerTape (first :: rest).length
        , outputTape [] ])
      (encodedGuardedStructuredTapes
        [ sourceTapeAt (first :: rest) []
        , markerTapeAt (first :: rest).length 0
        , outputTape (dropFinalCell (first :: rest)) ]) := by
  simpa [loweredDescription, initialConfig, finalConfig] using
    lowerStructured3Description_haltsFromConfigWithTapes
      description_wellFormed
      description_haltTransitionFree
      description_supportsReadWriteRows3
      (c := initialConfig first rest)
      (tapes :=
        [ sourceTapeAt (first :: rest) []
        , markerTapeAt (first :: rest).length 0
        , outputTape (dropFinalCell (first :: rest)) ])
      rfl
      (by simp [description, initialConfig, ThreeTape.description])
      ⟨2 * rest.length + 3, run first rest⟩

theorem loweredDescription_haltsFromTape3
    (first : Option Bool) (rest : List (Option Bool)) :
    loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (sourceTape (first :: rest))
        (markerTape (first :: rest).length)
        (outputTape []))
      (encodedGuardedStructured3Tapes
        (sourceTapeAt (first :: rest) [])
        (markerTapeAt (first :: rest).length 0)
        (outputTape (dropFinalCell (first :: rest)))) := by
  simpa [encodedGuardedStructured3Tapes] using
    loweredDescription_haltsFromTape first rest

theorem loweredDescription_haltsFromTape_cells
    (cells : List (Option Bool)) (hcells : cells ≠ []) :
    loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (sourceTape cells)
        (markerTape cells.length)
        (outputTape []))
      (encodedGuardedStructured3Tapes
        (sourceTapeAt cells [])
        (markerTapeAt cells.length 0)
        (outputTape (dropFinalCell cells))) := by
  cases cells with
  | nil =>
      exact False.elim (hcells rfl)
  | cons first rest =>
      simpa using loweredDescription_haltsFromTape3 first rest

theorem loweredDescription_haltsFromTape_append_singleton
    (cells : List (Option Bool)) (last : Option Bool) :
    loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (sourceTape (cells ++ [last]))
        (markerTape (cells ++ [last]).length)
        (outputTape []))
      (encodedGuardedStructured3Tapes
        (sourceTapeAt (cells ++ [last]) [])
        (markerTapeAt (cells ++ [last]).length 0)
        (outputTape cells)) := by
  have hcells : cells ++ [last] ≠ [] := by simp
  simpa [dropFinalCell_append_singleton] using
    loweredDescription_haltsFromTape_cells (cells ++ [last]) hcells

def LoweredSpec (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    forall (first : Option Bool) (rest : List (Option Bool)),
      compactor.HaltsFromTapeEquiv
        (encodedGuardedStructuredTapes
          [ sourceTape (first :: rest)
          , markerTape (first :: rest).length
          , outputTape [] ])
        (encodedGuardedStructuredTapes
          [ sourceTapeAt (first :: rest) []
          , markerTapeAt (first :: rest).length 0
          , outputTape (dropFinalCell (first :: rest)) ])

def LoweredConstruction : Prop :=
  exists compactor : MachineDescription, LoweredSpec compactor

theorem loweredConstruction_core : LoweredConstruction := by
  exact
    ⟨loweredDescription,
      loweredDescription_subroutineReady,
      loweredDescription_haltsFromTape⟩

end PairEncodedOptionCellCompactor
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
