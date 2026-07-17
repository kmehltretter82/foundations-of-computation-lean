import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame.Fuel

set_option doc.verso true

/-!
# Serialized-head dispatch

The dispatch machine locates the encoded head cell, queries the selected
machine transition, and exposes either the failure exit or a finite update
payload.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace SerializedHeadDispatch

open SerializedFieldComposer

/-- Finite payload exposed to the selected-update phase after lookup. -/
structure Selected (stateCount : Nat) where
  write : Option MachineCodeSymbol
  direction : Direction
  nextState : Fin stateCount
deriving DecidableEq

namespace Selected

def directionFinite : Foundation.FiniteType Direction where
  elems := [Direction.left, Direction.right]
  complete := by
    intro direction
    cases direction <;> simp

def payloadFinite (stateCount : Nat) :
    Foundation.FiniteType
      (Option MachineCodeSymbol × (Direction × Fin stateCount)) :=
  Foundation.FiniteType.prod
    (Foundation.FiniteType.option MachineCodeSymbol.finite)
    (Foundation.FiniteType.prod directionFinite
      (Foundation.FiniteType.fin stateCount))

def elems (stateCount : Nat) : List (Selected stateCount) :=
  (payloadFinite stateCount).elems.map fun payload =>
    { write := payload.1
      direction := payload.2.1
      nextState := payload.2.2 }

def finite (stateCount : Nat) : Foundation.FiniteType (Selected stateCount) where
  elems := elems stateCount
  complete := by
    intro selected
    cases selected with
    | mk write direction nextState =>
        apply List.mem_map.mpr
        refine ⟨(write, direction, nextState), ?_, rfl⟩
        exact (payloadFinite stateCount).complete _

end Selected

/-- Unified locator/dispatch control. Endpoint controls intentionally have no
rows so later physical-update composition can retarget them. -/
inductive Control (stateCount : Nat) where
  | locate (carriedState : Fin stateCount) (inner : HeadLocator.Control)
  | dispatchReturn (selected : Option (Selected stateCount))
  | failureExit
  | selectedEntry (selected : Selected stateCount)
deriving DecidableEq

namespace Control

def locateFinite (stateCount : Nat) :
    Foundation.FiniteType (Fin stateCount × HeadLocator.Control) :=
  Foundation.FiniteType.prod
    (Foundation.FiniteType.fin stateCount) HeadLocator.Control.finite

def elems (stateCount : Nat) : List (Control stateCount) :=
  List.append
    ((locateFinite stateCount).elems.map fun payload =>
      Control.locate payload.1 payload.2)
    (List.append
      ((Foundation.FiniteType.option (Selected.finite stateCount)).elems.map
        Control.dispatchReturn)
      (Control.failureExit ::
        (Selected.elems stateCount).map Control.selectedEntry))

def finite (stateCount : Nat) : Foundation.FiniteType (Control stateCount) where
  elems := elems stateCount
  complete := by
    intro control
    cases control with
    | locate carriedState inner =>
        have h := (locateFinite stateCount).complete (carriedState, inner)
        simp [elems, h]
    | dispatchReturn selected =>
        have h := (Foundation.FiniteType.option
          (Selected.finite stateCount)).complete selected
        simp [elems, h]
    | failureExit =>
        simp [elems]
    | selectedEntry selected =>
        have h : selected ∈ Selected.elems stateCount :=
          (Selected.finite stateCount).complete selected
        simp [elems, h]

end Control

def transition {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    Control stateCount -> Option MachineCodeSymbol ->
      Option
        (Option MachineCodeSymbol × Direction × Control stateCount)
  | .locate carriedState inner, read =>
      match HeadLocator.transition inner read with
      | some (write, direction, target) =>
          some (write, direction, .locate carriedState target)
      | none =>
          match inner with
          | .gate decodedHead =>
              match M.transition carriedState decodedHead with
              | none =>
                  some (read, Direction.right, .dispatchReturn none)
              | some (write, direction, nextState) =>
                  some
                    (read, Direction.right,
                      .dispatchReturn
                        (some
                          { write := write
                            direction := direction
                            nextState := nextState }))
          | _ => none
  | .dispatchReturn none, read =>
      some (read, Direction.left, .failureExit)
  | .dispatchReturn (some selected), read =>
      some (read, Direction.left, .selectedEntry selected)
  | .failureExit, _ => none
  | .selectedEntry _, _ => none

def machine {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    TuringMachine MachineCodeSymbol (Control stateCount) where
  start := .locate M.start .header
  halt := .failureExit
  transition := transition M
  statesFinite := Control.finite stateCount

def locateConfig {stateCount : Nat}
    (carriedState : Fin stateCount)
    (c : TuringMachine.Configuration MachineCodeSymbol HeadLocator.Control) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount) where
  state := .locate carriedState c.state
  tape := c.tape

def sourceConfig {stateCount : Nat}
    (carriedState : Fin stateCount) (L : Layout stateCount)
    (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount) :=
  locateConfig carriedState (HeadLocator.locatorStartConfig L callerData)

def roundTripTape (T : Tape MachineCodeSymbol) : Tape MachineCodeSymbol :=
  Tape.move Direction.left (Tape.move Direction.right T)

def failureConfig {stateCount : Nat} (T : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount) where
  state := .failureExit
  tape := roundTripTape T

def selectedConfig {stateCount : Nat}
    (selected : Selected stateCount) (T : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount) where
  state := .selectedEntry selected
  tape := roundTripTape T

theorem roundTripTape_equiv (T : Tape MachineCodeSymbol) :
    Tape.Equiv (roundTripTape T) T := by
  exact Machine.moveLeft_moveRight_equiv_self T

theorem locator_step_of_some {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (carriedState : Fin stateCount)
    (c d : TuringMachine.Configuration MachineCodeSymbol HeadLocator.Control)
    (hstep : HeadLocator.machine.stepConfig c = some d) :
    (machine M).stepConfig (locateConfig carriedState c) =
      some (locateConfig carriedState d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [HeadLocator.machine] at hstep
      cases htransition : HeadLocator.transition inner (Tape.read tape) with
      | none =>
          simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, target⟩
          simp only [htransition] at hstep
          cases hstep
          simp [machine, transition, locateConfig, htransition]

theorem locator_run_of_some {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (carriedState : Fin stateCount) :
    forall (steps : Nat)
      (c d : TuringMachine.Configuration MachineCodeSymbol HeadLocator.Control),
      HeadLocator.machine.runConfigExact? steps c = some d ->
        (machine M).runConfigExact? steps (locateConfig carriedState c) =
          some (locateConfig carriedState d) := by
  intro steps
  induction steps with
  | zero =>
      intro c d hrun
      simpa [TuringMachine.runConfigExact?] using congrArg
        (locateConfig carriedState) (Option.some.inj hrun)
  | succ steps ih =>
      intro c d hrun
      rw [TuringMachine.runConfigExact?] at hrun ⊢
      cases hstep : HeadLocator.machine.stepConfig c with
      | none =>
          simp [hstep] at hrun
      | some next =>
          simp only [hstep] at hrun
          rw [locator_step_of_some M carriedState c next hstep]
          simp only
          exact ih next d hrun

theorem locator_run_exact {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (carriedState : Fin stateCount) (L : Layout stateCount)
    (callerData : Word MachineCodeSymbol) :
    (machine M).runConfigExact? (HeadLocator.locatorSteps L)
        (sourceConfig carriedState L callerData) =
      some
        (locateConfig carriedState
          (HeadLocator.gateConfig L.head
            (Frame.protectedWord L callerData))) := by
  exact locator_run_of_some M carriedState _ _ _
    (HeadLocator.run_exact L callerData)

theorem missing_dispatch_run_exact {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (carriedState : Fin stateCount)
    (decodedHead : Option MachineCodeSymbol) (T : Tape MachineCodeSymbol)
    (hmissing : M.transition carriedState decodedHead = none) :
    (machine M).runConfigExact? 2
        { state := Control.locate carriedState (.gate decodedHead)
          tape := T } =
      some (failureConfig T) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, HeadLocator.transition, hmissing,
    failureConfig, roundTripTape, Tape.write_read_eq_self]

theorem selected_dispatch_run_exact {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (carriedState : Fin stateCount)
    (decodedHead write : Option MachineCodeSymbol)
    (direction : Direction) (nextState : Fin stateCount)
    (T : Tape MachineCodeSymbol)
    (hselected :
      M.transition carriedState decodedHead =
        some (write, direction, nextState)) :
    (machine M).runConfigExact? 2
        { state := Control.locate carriedState (.gate decodedHead)
          tape := T } =
      some
        (selectedConfig
          { write := write
            direction := direction
            nextState := nextState }
          T) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, HeadLocator.transition, hselected,
    selectedConfig, roundTripTape, Tape.write_read_eq_self]

theorem succMissing_run_exact {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (carriedState : Fin stateCount) (L : Layout stateCount)
    (callerData : Word MachineCodeSymbol)
    (hmissing : M.transition carriedState L.head = none) :
    (machine M).runConfigExact? (HeadLocator.locatorSteps L + 2)
        (sourceConfig carriedState L callerData) =
      some
        (failureConfig
          (HeadLocator.gateTape (Frame.protectedWord L callerData))) := by
  exact TuringMachine.runConfigExact?_trans
    (locator_run_exact M carriedState L callerData)
    (missing_dispatch_run_exact M carriedState L.head
      (HeadLocator.gateTape (Frame.protectedWord L callerData)) hmissing)

theorem succPresent_run_exact {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (carriedState : Fin stateCount) (L : Layout stateCount)
    (callerData : Word MachineCodeSymbol)
    (write : Option MachineCodeSymbol) (direction : Direction)
    (nextState : Fin stateCount)
    (hselected :
      M.transition carriedState L.head =
        some (write, direction, nextState)) :
    (machine M).runConfigExact? (HeadLocator.locatorSteps L + 2)
        (sourceConfig carriedState L callerData) =
      some
        (selectedConfig
          { write := write
            direction := direction
            nextState := nextState }
          (HeadLocator.gateTape (Frame.protectedWord L callerData))) := by
  exact TuringMachine.runConfigExact?_trans
    (locator_run_exact M carriedState L callerData)
    (selected_dispatch_run_exact M carriedState L.head write direction
      nextState (HeadLocator.gateTape (Frame.protectedWord L callerData))
      hselected)

end SerializedHeadDispatch
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
