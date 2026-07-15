import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame

set_option doc.verso true

/-!
# Strict-probe selected-transition dispatch

This module compiles the fixed selected machine's finite transition behavior
into a two-exit dispatch block.  It is the local action kernel of the strict
probe: a present transition writes, moves, and returns the selected successor
state to a retargetable loop exit; a missing transition takes a two-step bounce
to a retargetable failure exit while preserving the simulated tape up to
far-edge blank padding.

The block operates on
{name (full := FoC.Computability.FiniteRecognizer.ExactFuel.Layout.tape)}`Layout.tape`.
Scanning and rewriting the
serialized protected frame are separate phases, so this module does not claim
that a semantic code transformer is already a one-tape implementation.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace Machine

/-- Finite control states of the selected-transition dispatch block. -/
inductive Control (stateCount : Nat) where
  /-- Dispatch one selected-machine state and tape-head cell. -/
  | dispatch (state : Fin stateCount)
  /-- Retargetable continuation after one present transition. -/
  | loop (state : Fin stateCount)
  /-- First half of the missing-transition return bounce. -/
  | failureReturn (state : Fin stateCount)
  /-- Retargetable success exit, reserved for the fuel-zero phase. -/
  | successExit
  /-- Retargetable missing/exhausted failure exit. -/
  | failureExit
deriving DecidableEq, Repr

namespace Control

/-- Explicit finite enumeration of all dispatch control states. -/
def elems (stateCount : Nat) : List (Control stateCount) :=
  List.append
    ((List.finRange stateCount).map Control.dispatch)
    (List.append
      ((List.finRange stateCount).map Control.loop)
      (List.append
        ((List.finRange stateCount).map Control.failureReturn)
        [Control.successExit, Control.failureExit]))

/-- Finiteness witness for the generic dispatch control. -/
def finite (stateCount : Nat) : Foundation.FiniteType (Control stateCount) where
  elems := elems stateCount
  complete := by
    intro control
    cases control with
    | dispatch state =>
        simp [elems, List.mem_finRange]
    | loop state =>
        simp [elems, List.mem_finRange]
    | failureReturn state =>
        simp [elems, List.mem_finRange]
    | successExit =>
        simp [elems]
    | failureExit =>
        simp [elems]

end Control

/-- One explicit row of the selected-transition dispatch block. -/
structure Row (stateCount : Nat) where
  source : Control stateCount
  read : Option MachineCodeSymbol
  write : Option MachineCodeSymbol
  direction : Direction
  target : Control stateCount
deriving DecidableEq

/--
Compile one selected-machine lookup into a dispatch row.  A missing lookup
begins a right/left return bounce; a present lookup performs its real action.
-/
def dispatchRow {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (state : Fin stateCount) (cell : Option MachineCodeSymbol) :
    Row stateCount :=
  match M.transition state cell with
  | none =>
      { source := .dispatch state
        read := cell
        write := cell
        direction := Direction.right
        target := .failureReturn state }
  | some (write, direction, nextState) =>
      { source := .dispatch state
        read := cell
        write := write
        direction := direction
        target := .loop nextState }

/-- Second row of the missing-transition return bounce. -/
def failureReturnRow {stateCount : Nat}
    (state : Fin stateCount) (cell : Option MachineCodeSymbol) :
    Row stateCount where
  source := .failureReturn state
  read := cell
  write := cell
  direction := Direction.left
  target := .failureExit

/--
Lookup in the finite dispatch blocks.  Loop and exit states intentionally have
no rows so later composition can retarget them without replaying dispatch.
-/
def lookupRow {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (control : Control stateCount) (cell : Option MachineCodeSymbol) :
    Option (Row stateCount) :=
  match control with
  | .dispatch state => some (dispatchRow M state cell)
  | .failureReturn state => some (failureReturnRow state cell)
  | .loop _ | .successExit | .failureExit => none

/-- Lookup exposes the real action when the selected transition is present. -/
theorem lookupRow_dispatch_of_transition_eq_some
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {state : Fin stateCount} {cell write : Option MachineCodeSymbol}
    {direction : Direction} {nextState : Fin stateCount}
    (htransition :
      M.transition state cell = some (write, direction, nextState)) :
    lookupRow M (.dispatch state) cell =
      some
        { source := .dispatch state
          read := cell
          write := write
          direction := direction
          target := .loop nextState } := by
  simp [lookupRow, dispatchRow, htransition]

/-- Lookup exposes the failure bounce when the selected transition is absent. -/
theorem lookupRow_dispatch_of_transition_eq_none
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {state : Fin stateCount} {cell : Option MachineCodeSymbol}
    (htransition : M.transition state cell = none) :
    lookupRow M (.dispatch state) cell =
      some
        { source := .dispatch state
          read := cell
          write := cell
          direction := Direction.right
          target := .failureReturn state } := by
  simp [lookupRow, dispatchRow, htransition]

/-- Every read cell has a failure-return row. -/
theorem lookupRow_failureReturn
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (state : Fin stateCount) (cell : Option MachineCodeSymbol) :
    lookupRow M (.failureReturn state) cell =
      some (failureReturnRow state cell) := by
  rfl

@[simp] theorem lookupRow_loop
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (state : Fin stateCount) (cell : Option MachineCodeSymbol) :
    lookupRow M (.loop state) cell = none := by
  rfl

@[simp] theorem lookupRow_successExit
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (cell : Option MachineCodeSymbol) :
    lookupRow M .successExit cell = none := by
  rfl

@[simp] theorem lookupRow_failureExit
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (cell : Option MachineCodeSymbol) :
    lookupRow M .failureExit cell = none := by
  rfl

/-- Turn a successful row lookup into one Turing-machine action. -/
def transitionOfLookup {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (control : Control stateCount) (cell : Option MachineCodeSymbol) :
    Option
      (Option MachineCodeSymbol × Direction × Control stateCount) :=
  match lookupRow M control cell with
  | none => none
  | some row => some (row.write, row.direction, row.target)

/-- Generic finite selected-transition dispatch machine. -/
def dispatchMachine {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    TuringMachine MachineCodeSymbol (Control stateCount) where
  start := .dispatch M.start
  halt := .successExit
  transition := transitionOfLookup M
  statesFinite := Control.finite stateCount

/-- Present selected lookup as the concrete dispatch-machine transition. -/
theorem dispatchMachine_transition_of_transition_eq_some
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {state : Fin stateCount} {cell write : Option MachineCodeSymbol}
    {direction : Direction} {nextState : Fin stateCount}
    (htransition :
      M.transition state cell = some (write, direction, nextState)) :
    (dispatchMachine M).transition (.dispatch state) cell =
      some (write, direction, .loop nextState) := by
  change transitionOfLookup M (.dispatch state) cell = _
  unfold transitionOfLookup
  rw [show lookupRow M (.dispatch state) cell =
      some
        { source := Control.dispatch state
          read := cell
          write := write
          direction := direction
          target := Control.loop nextState } from
    lookupRow_dispatch_of_transition_eq_some htransition]

/-- Missing selected lookup as the first concrete failure-bounce transition. -/
theorem dispatchMachine_transition_of_transition_eq_none
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {state : Fin stateCount} {cell : Option MachineCodeSymbol}
    (htransition : M.transition state cell = none) :
    (dispatchMachine M).transition (.dispatch state) cell =
      some (cell, Direction.right, .failureReturn state) := by
  change transitionOfLookup M (.dispatch state) cell = _
  unfold transitionOfLookup
  rw [show lookupRow M (.dispatch state) cell =
      some
        { source := Control.dispatch state
          read := cell
          write := cell
          direction := Direction.right
          target := Control.failureReturn state } from
    lookupRow_dispatch_of_transition_eq_none htransition]

/-- Every read cell has the second concrete failure-bounce transition. -/
theorem dispatchMachine_transition_failureReturn
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (state : Fin stateCount) (cell : Option MachineCodeSymbol) :
    (dispatchMachine M).transition (.failureReturn state) cell =
      some (cell, Direction.left, .failureExit) := by
  rfl

/-- Dispatch configuration for the exact simulated layout. -/
def dispatchConfig {stateCount : Nat} (L : Layout stateCount) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount) where
  state := .dispatch L.state
  tape := L.tape

/-- Retargetable loop configuration after a selected transition. -/
def loopConfig {stateCount : Nat} (L : Layout stateCount) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount) where
  state := .loop L.state
  tape := L.tape

/-- Exact semantic layout produced by one selected transition. -/
def transitionTarget {stateCount : Nat}
    (fuel : Nat) (write : Option MachineCodeSymbol)
    (direction : Direction) (nextState : Fin stateCount)
    (L : Layout stateCount) : Layout stateCount :=
  Layout.ofConfig fuel
    { state := nextState
      tape := Tape.move direction (Tape.write write L.tape) }

/--
The transition-present branch performs the real selected action in one exact
dispatch step and exposes the successor state at the loop exit.
-/
theorem dispatchMachine_runConfigExact_one_of_transition_eq_some
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {L : Layout stateCount} {fuel : Nat}
    {write : Option MachineCodeSymbol} {direction : Direction}
    {nextState : Fin stateCount}
    (htransition :
      M.transition L.state (Tape.read L.tape) =
        some (write, direction, nextState)) :
    (dispatchMachine M).runConfigExact? 1 (dispatchConfig L) =
      some
        (loopConfig
          (transitionTarget fuel write direction nextState L)) := by
  have hstep :
      (dispatchMachine M).stepConfig (dispatchConfig L) =
        some
          (loopConfig
            (transitionTarget fuel write direction nextState L)) := by
    unfold TuringMachine.stepConfig
    change
      (match
          (dispatchMachine M).transition (.dispatch L.state)
            (Tape.read L.tape) with
        | none => none
        | some (written, dir, targetState) =>
            some
              ({ state := targetState
                 tape := Tape.move dir (Tape.write written L.tape) } :
                TuringMachine.Configuration MachineCodeSymbol
                  (Control stateCount))) = _
    rw [dispatchMachine_transition_of_transition_eq_some htransition]
    rfl
  simp [TuringMachine.runConfigExact?, hstep]

/-- The transition target is exactly the existing semantic layout step. -/
theorem transitionTarget_eq_of_layout_step
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {L : Layout stateCount} {fuel : Nat}
    {write : Option MachineCodeSymbol} {direction : Direction}
    {nextState : Fin stateCount}
    (hfuel : L.fuel = fuel + 1)
    (htransition :
      M.transition L.state (Tape.read L.tape) =
        some (write, direction, nextState)) :
    Layout.step M L =
      some (transitionTarget fuel write direction nextState L) := by
  exact Layout.step_of_transition_eq_some hfuel htransition

private theorem write_read_eq_self
    (T : Tape MachineCodeSymbol) :
    Tape.write (Tape.read T) T = T := by
  cases T
  rfl

/-- A right/left bounce preserves a tape up to far-edge blank padding. -/
theorem moveLeft_moveRight_equiv_self
    (T : Tape MachineCodeSymbol) :
    Tape.Equiv
      (Tape.move Direction.left (Tape.move Direction.right T)) T := by
  cases T with
  | mk left head right =>
      simp [Tape.Equiv, Tape.move, Tape.moveLeft, Tape.moveRight]
      cases right <;> simp [Tape.dropTrailingNone]

/--
A missing selected transition reaches the failure exit in two exact steps.
The explicit target records the harmless administrative bounce.
-/
theorem dispatchMachine_runConfigExact_two_of_transition_eq_none
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {L : Layout stateCount}
    (htransition :
      M.transition L.state (Tape.read L.tape) = none) :
    (dispatchMachine M).runConfigExact? 2 (dispatchConfig L) =
      some
        { state := Control.failureExit
          tape :=
            Tape.move Direction.left
              (Tape.move Direction.right L.tape) } := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    dispatchMachine, dispatchConfig, transitionOfLookup, lookupRow,
    dispatchRow, failureReturnRow, htransition, write_read_eq_self]

/-- The missing-transition exit retains the exact simulated tape modulo padding. -/
theorem dispatchMachine_failure_tape_equiv
    {stateCount : Nat} (L : Layout stateCount) :
    Tape.Equiv
      (Tape.move Direction.left (Tape.move Direction.right L.tape))
      L.tape :=
  moveLeft_moveRight_equiv_self L.tape

/--
The serialized successor frame keeps the caller suffix literally and decodes
back to the exact transition target.
-/
theorem decode_transitionTarget_protectedWord
    {stateCount : Nat}
    (fuel : Nat) (write : Option MachineCodeSymbol)
    (direction : Direction) (nextState : Fin stateCount)
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    Layout.decode stateCount
        (Frame.protectedWord
          (transitionTarget fuel write direction nextState L)
          callerData) =
      some
        (transitionTarget fuel write direction nextState L,
          Frame.callerTag :: callerData) :=
  Frame.decode_protectedWord
    (transitionTarget fuel write direction nextState L) callerData

end Machine
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
