import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.PairEncodedOptionCellCompactor.Base

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering
namespace PairEncodedOptionCellCompactor

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
