import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.Assembly

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

open DovetailInitialLayoutInitializer

def scanRightToBlankLeftDescription : MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ transition 0 none none Direction.left 1
    , transition 0 (some false) (some false) Direction.right 0
    , transition 0 (some true) (some true) Direction.right 0 ]

theorem scanRightToBlankLeftDescription_wellFormed :
    scanRightToBlankLeftDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := scanRightToBlankLeftDescription.transitions)
      (stateCount := scanRightToBlankLeftDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := scanRightToBlankLeftDescription.transitions)
      (by decide)

theorem scanRightToBlankLeftDescription_haltTransitionFree :
    scanRightToBlankLeftDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := scanRightToBlankLeftDescription.transitions)
    (state := scanRightToBlankLeftDescription.halt)
    (by decide)

theorem scanRightToBlankLeftDescription_subroutineReady :
    scanRightToBlankLeftDescription.SubroutineReady :=
  ⟨scanRightToBlankLeftDescription_wellFormed,
    scanRightToBlankLeftDescription_haltTransitionFree⟩

def scanRightToBlankLeftHaltTape
    (leftRev : List (Option Bool)) (bits : Word Bool) : Tape Bool :=
  Tape.move Direction.left
    (tapeAtCells (List.append (bits.reverse.map some) leftRev) [none])

theorem scanRightToBlankLeftDescription_run
    (leftRev : List (Option Bool)) (bits : Word Bool) :
    scanRightToBlankLeftDescription.runConfig (bits.length + 1)
        (config scanRightToBlankLeftDescription.start leftRev
          (List.append (bits.map some) [none])) =
      { state := scanRightToBlankLeftDescription.halt
        tape := scanRightToBlankLeftHaltTape leftRev bits } := by
  induction bits generalizing leftRev with
  | nil =>
      simp [scanRightToBlankLeftDescription,
        scanRightToBlankLeftHaltTape, config, tapeAtCells,
        runConfig, stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft]
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 = 1 + (rest.length + 1) by
        simp
        omega]
      rw [runConfig_add]
      have hstep :
          scanRightToBlankLeftDescription.runConfig 1
              (config scanRightToBlankLeftDescription.start leftRev
                (List.append ((bit :: rest).map some) [none])) =
            config scanRightToBlankLeftDescription.start (some bit :: leftRev)
              (List.append (rest.map some) [none]) := by
        cases bit <;>
          cases rest <;>
          simp [scanRightToBlankLeftDescription, config, tapeAtCells,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveRight]
      rw [hstep]
      simpa [scanRightToBlankLeftHaltTape, List.reverse_cons,
        List.map_append, List.append_assoc] using ih (some bit :: leftRev)

theorem scanRightToBlankLeftDescription_haltsFromTape
    (leftRev : List (Option Bool)) (bits : Word Bool) :
    scanRightToBlankLeftDescription.HaltsFromTape
      (tapeAtCells leftRev (List.append (bits.map some) [none]))
      (scanRightToBlankLeftHaltTape leftRev bits) := by
  refine ⟨bits.length + 1, ?_⟩
  have hrun := scanRightToBlankLeftDescription_run leftRev bits
  constructor
  · simpa [config] using congrArg Configuration.state hrun
  · simpa [config] using congrArg Configuration.tape hrun

theorem scanRightToBlankLeftHaltTape_move_left_move_right_cons
    (leftRev : List (Option Bool)) (bit : Bool) (rest : Word Bool) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (scanRightToBlankLeftHaltTape leftRev (bit :: rest))) =
      scanRightToBlankLeftHaltTape leftRev (bit :: rest) := by
  unfold scanRightToBlankLeftHaltTape
  cases hrev : rest.reverse with
  | nil =>
      simp [hrev, tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons head tail =>
      simp [hrev, tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight,
        List.map_append, List.append_assoc]

theorem preservingCellPassCellBits_cons_exists
    (bit : Bool) (rest : Word Bool) :
    exists head : Bool,
    exists tail : Word Bool,
      preservingCellPassCellBits (bit :: rest) = head :: tail := by
  cases bit
  · exact
      ⟨false, true :: false :: true ::
        preservingCellPassCellBits rest, by
          simp [preservingCellPassCellBits,
            preservingCellPassZeroBits]⟩
  · exact
      ⟨false, true :: true :: false ::
        preservingCellPassCellBits rest, by
          simp [preservingCellPassCellBits,
            preservingCellPassOneBits]⟩

theorem exists_reverse_append_singleton_of_nonempty
    (bits : Word Bool) (h : bits ≠ []) :
    exists scanRev : Word Bool,
    exists current : Bool,
      bits = List.append scanRev.reverse [current] := by
  induction bits with
  | nil =>
      contradiction
  | cons head tail ih =>
      cases tail with
      | nil =>
          exact ⟨[], head, by simp⟩
      | cons next rest =>
          rcases ih (by simp) with ⟨scanRev, current, htail⟩
          refine ⟨List.append scanRev [head], current, ?_⟩
          simp [List.reverse_append, htail]

theorem exists_reverse_append_singleton_of_cons
    (head : Bool) (tail : Word Bool) :
    exists scanRev : Word Bool,
    exists current : Bool,
      head :: tail = List.append scanRev.reverse [current] :=
  exists_reverse_append_singleton_of_nonempty (head :: tail) (by simp)

def scanLeftToBlankLeftDescription : MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ transition 0 none none Direction.left 1
    , transition 0 (some false) (some false) Direction.left 0
    , transition 0 (some true) (some true) Direction.left 0 ]

theorem scanLeftToBlankLeftDescription_wellFormed :
    scanLeftToBlankLeftDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := scanLeftToBlankLeftDescription.transitions)
      (stateCount := scanLeftToBlankLeftDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := scanLeftToBlankLeftDescription.transitions)
      (by decide)

theorem scanLeftToBlankLeftDescription_haltTransitionFree :
    scanLeftToBlankLeftDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := scanLeftToBlankLeftDescription.transitions)
    (state := scanLeftToBlankLeftDescription.halt)
    (by decide)

theorem scanLeftToBlankLeftDescription_subroutineReady :
    scanLeftToBlankLeftDescription.SubroutineReady :=
  ⟨scanLeftToBlankLeftDescription_wellFormed,
    scanLeftToBlankLeftDescription_haltTransitionFree⟩

def scanLeftToBlankLeftHaltTape
    (leftBase : List (Option Bool)) (bits : Word Bool)
    (right : List (Option Bool)) : Tape Bool :=
  Tape.move Direction.left
    (tapeAtCells leftBase
      (none :: List.append (bits.map some) right))

theorem scanLeftToBlankLeftDescription_run_scanRev
    (leftBase : List (Option Bool)) (scanRev : Word Bool)
    (current : Bool) (right : List (Option Bool)) :
    scanLeftToBlankLeftDescription.runConfig (scanRev.length + 2)
        (config scanLeftToBlankLeftDescription.start
          (List.append (scanRev.map some) (none :: leftBase))
          (some current :: right)) =
      { state := scanLeftToBlankLeftDescription.halt
        tape :=
          scanLeftToBlankLeftHaltTape leftBase
            (List.append scanRev.reverse [current]) right } := by
  induction scanRev generalizing current right with
  | nil =>
      cases current <;>
        simp [scanLeftToBlankLeftDescription,
          scanLeftToBlankLeftHaltTape, config, tapeAtCells,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft]
  | cons prev rest ih =>
      rw [show (prev :: rest).length + 2 = 1 + (rest.length + 2) by
        simp
        omega]
      rw [runConfig_add]
      have hstep :
          scanLeftToBlankLeftDescription.runConfig 1
              (config scanLeftToBlankLeftDescription.start
                (List.append ((prev :: rest).map some) (none :: leftBase))
                (some current :: right)) =
            config scanLeftToBlankLeftDescription.start
              (List.append (rest.map some) (none :: leftBase))
              (some prev :: some current :: right) := by
        cases current <;> cases prev <;>
          simp [scanLeftToBlankLeftDescription, config, tapeAtCells,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [hstep]
      simpa [scanLeftToBlankLeftHaltTape, List.map_append,
        List.reverse_cons, List.append_assoc] using
        ih prev (some current :: right)

theorem scanRightToBlankLeftHaltTape_eq_scanRev
    (leftBase : List (Option Bool)) (scanRev : Word Bool)
    (current : Bool) :
    scanRightToBlankLeftHaltTape (none :: leftBase)
        (List.append scanRev.reverse [current]) =
      tapeAtCells
        (List.append (scanRev.map some) (none :: leftBase))
        [some current, none] := by
  induction scanRev with
  | nil =>
      simp [scanRightToBlankLeftHaltTape, tapeAtCells,
        Tape.move, Tape.moveLeft]
  | cons bit rest ih =>
      simp [scanRightToBlankLeftHaltTape, tapeAtCells,
        Tape.move, Tape.moveLeft, List.reverse_cons,
        List.append_assoc]

theorem scanLeftToBlankLeftDescription_haltsFrom_scanRightToBlankLeftHaltTape
    (leftBase : List (Option Bool)) (scanRev : Word Bool)
    (current : Bool) :
    scanLeftToBlankLeftDescription.HaltsFromTape
      (scanRightToBlankLeftHaltTape (none :: leftBase)
        (List.append scanRev.reverse [current]))
      (scanLeftToBlankLeftHaltTape leftBase
        (List.append scanRev.reverse [current]) [none]) := by
  refine ⟨scanRev.length + 2, ?_⟩
  have hrun :=
    scanLeftToBlankLeftDescription_run_scanRev
      leftBase scanRev current [none]
  have hsource :=
    scanRightToBlankLeftHaltTape_eq_scanRev
      leftBase scanRev current
  constructor
  · rw [hsource]
    simpa [config] using congrArg Configuration.state hrun
  · rw [hsource]
    simpa [config] using congrArg Configuration.tape hrun

theorem scanLeftToBlankLeftHaltTape_move_left_move_right_none_right
    (leftBase : List (Option Bool)) (bits : Word Bool)
    (right : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (scanLeftToBlankLeftHaltTape leftBase bits (none :: right))) =
      scanLeftToBlankLeftHaltTape leftBase bits (none :: right) := by
  exact
    Tape.move_left_move_right_eq_self_of_right_cons
      (scanLeftToBlankLeftHaltTape leftBase bits (none :: right))
      (cell := none) (right := List.append (bits.map some) (none :: right))
      (by
        cases leftBase <;>
          simp [scanLeftToBlankLeftHaltTape, tapeAtCells,
            Tape.move, Tape.moveLeft])

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
