import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Basic

set_option doc.verso true

/-!
# Boundary-marked left eraser

This module provides the fixed finite-machine pass used after a scanner has
validated an encoded field and restored that field onto the left stack.  Given
a blank boundary immediately to the left of the restored field, the machine
erases leftward over the field and halts back on the first erased cell, ready
for a later gap-compaction pass.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

def leftBoundaryEraserDescription : MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ transition 0 (some false) none Direction.left 0
    , transition 0 (some true) none Direction.left 0
    , transition 0 none none Direction.right 1 ]

def leftBoundaryEraserSourceTape
    (baseLeft : List (Option Bool)) (field : Word Bool)
    (suffixHead : Option Bool) (suffixTail : List (Option Bool)) :
    Tape Bool :=
  Tape.move Direction.left
    (tapeAtCells
      (List.append (field.reverse.map some)
        (none :: baseLeft))
      (suffixHead :: suffixTail))

def leftBoundaryEraserTargetTape
    (baseLeft : List (Option Bool)) (field : Word Bool)
    (suffixHead : Option Bool) (suffixTail : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells (none :: baseLeft)
    (List.append
      (List.replicate field.length (none : Option Bool))
      (suffixHead :: suffixTail))

theorem leftBoundaryEraserSourceTape_move_left_move_right
    (baseLeft : List (Option Bool)) (field : Word Bool)
    (suffixHead : Option Bool) (suffixTail : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (leftBoundaryEraserSourceTape
            baseLeft field suffixHead suffixTail)) =
      leftBoundaryEraserSourceTape
        baseLeft field suffixHead suffixTail := by
  cases hrev : field.reverse with
  | nil =>
      simp [leftBoundaryEraserSourceTape, hrev, tapeAtCells,
        Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons current leftRev =>
      simp [leftBoundaryEraserSourceTape, hrev, tapeAtCells,
        Tape.move, Tape.moveLeft, Tape.moveRight]

theorem leftBoundaryEraserDescription_wellFormed :
    leftBoundaryEraserDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := leftBoundaryEraserDescription.transitions)
      (stateCount := leftBoundaryEraserDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := leftBoundaryEraserDescription.transitions)
      (by decide)

theorem leftBoundaryEraserDescription_haltTransitionFree :
    leftBoundaryEraserDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := leftBoundaryEraserDescription.transitions)
    (state := leftBoundaryEraserDescription.halt)
    (by decide)

theorem leftBoundaryEraserDescription_subroutineReady :
    leftBoundaryEraserDescription.SubroutineReady :=
  ⟨leftBoundaryEraserDescription_wellFormed,
    leftBoundaryEraserDescription_haltTransitionFree⟩

theorem leftBoundaryEraserDescription_step_finish
    (baseLeft right : List (Option Bool)) :
    leftBoundaryEraserDescription.runConfig 1
        { state := leftBoundaryEraserDescription.start
          tape := tapeAtCells baseLeft (none :: right) } =
      { state := leftBoundaryEraserDescription.halt
        tape := tapeAtCells (none :: baseLeft) right } := by
  cases right <;>
    simp [leftBoundaryEraserDescription, runConfig, stepConfig,
      lookupTransition, Matches, transition, Tape.read, Tape.write,
      Tape.move, Tape.moveRight, tapeAtCells]

theorem leftBoundaryEraserDescription_run_loop
    (baseLeft : List (Option Bool)) (leftRev : Word Bool)
    (current : Bool) (erased : Nat)
    (suffix : List (Option Bool)) :
    leftBoundaryEraserDescription.runConfig (leftRev.length + 1)
        { state := leftBoundaryEraserDescription.start
          tape :=
            tapeAtCells
              (List.append (leftRev.map some)
                (none :: baseLeft))
              (some current ::
                List.append
                  (List.replicate erased (none : Option Bool))
                  suffix) } =
      { state := leftBoundaryEraserDescription.start
        tape :=
          tapeAtCells baseLeft
            (none ::
              List.append
                (List.replicate (leftRev.length + 1 + erased)
                  (none : Option Bool))
                suffix) } := by
  induction leftRev generalizing current erased with
  | nil =>
      cases current <;>
        simp [leftBoundaryEraserDescription, runConfig, stepConfig,
          lookupTransition, Matches, transition, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft, tapeAtCells, List.replicate_succ,
          Nat.add_comm]
  | cons next rest ih =>
      rw [show (next :: rest).length + 1 = 1 + (rest.length + 1) by
        simp
        omega]
      rw [runConfig_add]
      cases current <;>
        simp [leftBoundaryEraserDescription, runConfig, stepConfig,
          lookupTransition, Matches, transition, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft, tapeAtCells]
      · simpa [List.replicate_succ, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm, List.append_assoc] using
          ih next (erased + 1)
      · simpa [List.replicate_succ, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm, List.append_assoc] using
          ih next (erased + 1)

theorem leftBoundaryEraserDescription_run_nonempty
    (baseLeft : List (Option Bool)) (leftRev : Word Bool)
    (current : Bool)
    (suffixHead : Option Bool) (suffixTail : List (Option Bool)) :
    leftBoundaryEraserDescription.runConfig (leftRev.length + 2)
        { state := leftBoundaryEraserDescription.start
          tape :=
            tapeAtCells
              (List.append (leftRev.map some)
                (none :: baseLeft))
              (some current :: suffixHead :: suffixTail) } =
      { state := leftBoundaryEraserDescription.halt
        tape :=
          tapeAtCells (none :: baseLeft)
            (List.append
              (List.replicate (leftRev.length + 1)
                (none : Option Bool))
              (suffixHead :: suffixTail)) } := by
  rw [show leftRev.length + 2 = (leftRev.length + 1) + 1 by omega]
  rw [runConfig_add]
  have hloop :=
    leftBoundaryEraserDescription_run_loop
      baseLeft leftRev current 0 (suffixHead :: suffixTail)
  change
    leftBoundaryEraserDescription.runConfig 1
      (leftBoundaryEraserDescription.runConfig (leftRev.length + 1)
        { state := leftBoundaryEraserDescription.start
          tape :=
            tapeAtCells
              (List.append (leftRev.map some)
                (none :: baseLeft))
              (some current ::
                List.append
                  (List.replicate 0 (none : Option Bool))
                  (suffixHead :: suffixTail)) }) =
      { state := leftBoundaryEraserDescription.halt
        tape :=
          tapeAtCells (none :: baseLeft)
            (List.append
              (List.replicate (leftRev.length + 1)
                (none : Option Bool))
              (suffixHead :: suffixTail)) }
  rw [hloop]
  rw [leftBoundaryEraserDescription_step_finish]

theorem leftBoundaryEraserDescription_haltsFromTape
    (baseLeft : List (Option Bool)) (field : Word Bool)
    (suffixHead : Option Bool) (suffixTail : List (Option Bool)) :
    leftBoundaryEraserDescription.HaltsFromTape
      (leftBoundaryEraserSourceTape
        baseLeft field suffixHead suffixTail)
      (leftBoundaryEraserTargetTape
        baseLeft field suffixHead suffixTail) := by
  cases hrev : field.reverse with
  | nil =>
      have hfield : field = [] := by
        simpa using congrArg List.reverse hrev
      have hsource :
          leftBoundaryEraserSourceTape
              baseLeft field suffixHead suffixTail =
            tapeAtCells baseLeft (none :: suffixHead :: suffixTail) := by
        simp [leftBoundaryEraserSourceTape, hfield, tapeAtCells,
          Tape.move, Tape.moveLeft]
      have htarget :
          leftBoundaryEraserTargetTape
              baseLeft field suffixHead suffixTail =
            tapeAtCells (none :: baseLeft) (suffixHead :: suffixTail) := by
        simp [leftBoundaryEraserTargetTape, hfield]
      refine ⟨1, ?_⟩
      constructor
      · rw [hsource, leftBoundaryEraserDescription_step_finish]
      · rw [hsource, leftBoundaryEraserDescription_step_finish,
          htarget]
  | cons current leftRev =>
      refine ⟨field.length + 1, ?_⟩
      have hfieldLen : field.length = leftRev.length + 1 := by
        have hlen := congrArg List.length hrev
        simp at hlen
        omega
      have hsource :
          leftBoundaryEraserSourceTape
              baseLeft field suffixHead suffixTail =
            tapeAtCells
              (List.append (leftRev.map some)
                (none :: baseLeft))
              (some current :: suffixHead :: suffixTail) := by
        rw [leftBoundaryEraserSourceTape, hrev]
        simp [tapeAtCells, Tape.move, Tape.moveLeft]
      have hrun :=
        leftBoundaryEraserDescription_run_nonempty
          baseLeft leftRev current suffixHead suffixTail
      constructor
      · simpa [hfieldLen, hsource] using
          congrArg Configuration.state hrun
      · simpa [hfieldLen, hsource, leftBoundaryEraserTargetTape] using
          congrArg Configuration.tape hrun

end FiniteTransducers
end CommonGround

end Computability
end FoC
