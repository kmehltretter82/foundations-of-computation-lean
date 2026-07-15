import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseEmbedding
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.TapeEquivTransport
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Dispatch.SerializedHead

set_option doc.verso true

/-!
# Selected present-action prefix

The selected-action prefix decrements fuel, returns to the protected-frame
header, and locates the left payload. Its endpoint remains retargetable by the
left-update machine.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace Update
namespace PresentAction

open SerializedFieldComposer

namespace SelectedFuelThenLeftBoundary

/-- One actual finite machine carrying the selected row while it decrements
fuel, returns to the protected-frame header, and locates the left payload. -/
inductive Control (stateCount : Nat) where
  | fuel
      (selected : SerializedHeadDispatch.Selected stateCount)
      (inner : FuelDecrementMachine.Control)
  | handoffReturn
      (selected : SerializedHeadDispatch.Selected stateCount)
  | locate
      (selected : SerializedHeadDispatch.Selected stateCount)
      (inner : FieldLocator.Control)
deriving DecidableEq

namespace Control

def fuelFinite (stateCount : Nat) :
    Foundation.FiniteType
      (SerializedHeadDispatch.Selected stateCount ×
        FuelDecrementMachine.Control) :=
  Foundation.FiniteType.prod
    (SerializedHeadDispatch.Selected.finite stateCount)
    FuelDecrementMachine.Control.finite

def locateFinite (stateCount : Nat) :
    Foundation.FiniteType
      (SerializedHeadDispatch.Selected stateCount ×
        FieldLocator.Control) :=
  Foundation.FiniteType.prod
    (SerializedHeadDispatch.Selected.finite stateCount)
    FieldLocator.Control.finite

def elems (stateCount : Nat) : List (Control stateCount) :=
  List.append
    ((fuelFinite stateCount).elems.map fun payload =>
      Control.fuel payload.1 payload.2)
    (List.append
      ((SerializedHeadDispatch.Selected.elems stateCount).map
        Control.handoffReturn)
      ((locateFinite stateCount).elems.map fun payload =>
        Control.locate payload.1 payload.2))

def finite (stateCount : Nat) : Foundation.FiniteType (Control stateCount) where
  elems := elems stateCount
  complete := by
    intro control
    cases control with
    | fuel selected inner =>
        have h := (fuelFinite stateCount).complete (selected, inner)
        simp [elems, h]
    | handoffReturn selected =>
        have h : selected ∈
            SerializedHeadDispatch.Selected.elems stateCount :=
          (SerializedHeadDispatch.Selected.finite
            stateCount).complete selected
        simp [elems, h]
    | locate selected inner =>
        have h := (locateFinite stateCount).complete (selected, inner)
        simp [elems, h]

end Control

def transition {stateCount : Nat} :
    Control stateCount -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control stateCount)
  | .fuel selected inner, read =>
      match FuelDecrementMachine.transition inner read with
      | some (write, direction, target) =>
          some (write, direction, .fuel selected target)
      | none =>
          if inner = .update (.rewind .gate) then
            some (read, Direction.right, .handoffReturn selected)
          else
            none
  | .handoffReturn selected, read =>
      some (read, Direction.left, .locate selected .header)
  | .locate selected inner, read =>
      match FieldLocator.transition .leftPayload inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .locate selected target)

def machine {stateCount : Nat}
    (selected : SerializedHeadDispatch.Selected stateCount) :
    TuringMachine MachineCodeSymbol (Control stateCount) where
  start := .fuel selected .header
  halt := .locate selected .gate
  transition := transition
  statesFinite := Control.finite stateCount

def fuelConfig {stateCount : Nat}
    (selected : SerializedHeadDispatch.Selected stateCount)
    (c : TuringMachine.Configuration MachineCodeSymbol
      FuelDecrementMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount) where
  state := .fuel selected c.state
  tape := c.tape

def locateConfig {stateCount : Nat}
    (selected : SerializedHeadDispatch.Selected stateCount)
    (c : TuringMachine.Configuration MachineCodeSymbol FieldLocator.Control) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount) :=
  TuringMachine.PhaseEmbedding.liftConfig
    (Control.locate selected) c

/-- A genuine fuel step is unchanged by the wrapper.  The wrapper only adds a
row at the otherwise stuck fuel gate. -/
theorem fuel_step_of_some {stateCount : Nat}
    (selected : SerializedHeadDispatch.Selected stateCount)
    (c d : TuringMachine.Configuration MachineCodeSymbol
      FuelDecrementMachine.Control)
    (hstep : FuelDecrementMachine.machine.stepConfig c = some d) :
    (machine selected).stepConfig (fuelConfig selected c) =
      some (fuelConfig selected d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [FuelDecrementMachine.machine] at hstep
      cases htransition :
          FuelDecrementMachine.transition inner (Tape.read tape) with
      | none =>
          simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, target⟩
          simp only [htransition] at hstep
          cases hstep
          simp [machine, transition, fuelConfig, htransition]

/-- Exact fuel runs lift until their endpoint, despite that endpoint being
retargetable in the enclosing machine. -/
theorem fuel_run_of_some {stateCount : Nat}
    (selected : SerializedHeadDispatch.Selected stateCount) :
    forall (steps : Nat)
      (c d : TuringMachine.Configuration MachineCodeSymbol
        FuelDecrementMachine.Control),
      FuelDecrementMachine.machine.runConfigExact? steps c = some d ->
        (machine selected).runConfigExact? steps (fuelConfig selected c) =
          some (fuelConfig selected d) := by
  intro steps
  induction steps with
  | zero =>
      intro c d hrun
      simpa [TuringMachine.runConfigExact?] using congrArg
        (fuelConfig selected) (Option.some.inj hrun)
  | succ steps ih =>
      intro c d hrun
      rw [TuringMachine.runConfigExact?] at hrun ⊢
      cases hstep : FuelDecrementMachine.machine.stepConfig c with
      | none =>
          simp [hstep] at hrun
      | some next =>
          simp only [hstep] at hrun
          rw [fuel_step_of_some selected c next hstep]
          simp only
          exact ih next d hrun

theorem fuel_run_exact {stateCount : Nat}
    (selected : SerializedHeadDispatch.Selected stateCount)
    (fuel : Nat) (L : Layout stateCount)
    (callerData : Word MachineCodeSymbol) :
    (machine selected).runConfigExact?
        (FuelDecrementMachine.runSteps fuel L callerData)
        (fuelConfig selected
          (FuelDecrementMachine.startConfig
            (Frame.protectedWord
              (FuelDecrementMachine.withFuel (fuel + 1) L) callerData))) =
      some
        (fuelConfig selected
          (FuelDecrementMachine.updateConfig
            (DeleteOneRestagedMachine.rewindConfig
              (RewindWord.gateConfig
                (Frame.protectedWord
                  (FuelDecrementMachine.withFuel fuel L) callerData) 1)))) := by
  exact fuel_run_of_some selected _ _ _
    (FuelDecrementMachine.run_exact fuel L callerData)

def roundTripTape (T : Tape MachineCodeSymbol) : Tape MachineCodeSymbol :=
  Tape.move Direction.left (Tape.move Direction.right T)

private theorem write_read_eq_self (T : Tape MachineCodeSymbol) :
    Tape.write (Tape.read T) T = T := by
  cases T
  rfl

theorem roundTripTape_equiv (T : Tape MachineCodeSymbol) :
    Tape.Equiv (roundTripTape T) T := by
  exact Machine.moveLeft_moveRight_equiv_self T

/-- The mandatory right/left bounce changes only far-edge blank padding and
enters the field locator on the same protected frame. -/
theorem fuel_handoff_run_exact {stateCount : Nat}
    (selected : SerializedHeadDispatch.Selected stateCount)
    (word : Word MachineCodeSymbol) :
    (machine selected).runConfigExact? 2
        (fuelConfig selected
          (FuelDecrementMachine.updateConfig
            (DeleteOneRestagedMachine.rewindConfig
              (RewindWord.gateConfig word 1)))) =
      some
        (locateConfig selected
          { state := FieldLocator.Control.header
            tape := roundTripTape (RewindWord.gateTape word 1) }) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, fuelConfig, locateConfig,
    TuringMachine.PhaseEmbedding.liftConfig,
    FuelDecrementMachine.updateConfig, FuelDecrementMachine.config,
    FuelDecrementMachine.transition,
    DeleteOneRestagedMachine.transition, RewindWord.transition,
    DeleteOneRestagedMachine.rewindConfig, RewindWord.gateConfig,
    roundTripTape, write_read_eq_self]

/-- The locator phase uses the generic phase embedding; no locator-specific
run induction is repeated here. -/
theorem locate_run_of_some {stateCount : Nat}
    (selected : SerializedHeadDispatch.Selected stateCount)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      FieldLocator.Control}
    (hrun : (FieldLocator.machine .leftPayload).runConfigExact?
      steps source = some target) :
    (machine selected).runConfigExact? steps (locateConfig selected source) =
      some (locateConfig selected target) := by
  apply TuringMachine.PhaseEmbedding.runConfigExact?_lift_of_eq_some
    (inner := FieldLocator.machine .leftPayload)
    (outer := machine selected)
    (Control.locate selected)
  · intro c
    cases c with
    | mk inner tape =>
        unfold TuringMachine.stepConfig
        simp only [TuringMachine.PhaseEmbedding.liftConfig,
          machine, transition, FieldLocator.machine]
        cases htransition :
            FieldLocator.transition .leftPayload inner (Tape.read tape) with
        | none => rfl
        | some action =>
            rcases action with ⟨write, direction, target⟩
            rfl
  · exact hrun

theorem runConfigExact_trans {stateCount : Nat}
    (selected : SerializedHeadDispatch.Selected stateCount)
    {first second : Nat}
    {a b c : TuringMachine.Configuration MachineCodeSymbol
      (Control stateCount)}
    (hab : (machine selected).runConfigExact? first a = some b)
    (hbc : (machine selected).runConfigExact? second b = some c) :
    (machine selected).runConfigExact? (first + second) a = some c := by
  apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr
  exact TuringMachine.computesIn_trans
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hab)
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hbc)

def postFuelLocatorSource {stateCount : Nat}
    (fuel : Nat) (L : Layout stateCount)
    (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol FieldLocator.Control where
  state := .header
  tape := roundTripTape
    (RewindWord.gateTape
      (Frame.protectedWord
        (FuelDecrementMachine.withFuel fuel L) callerData) 1)

theorem postFuelLocatorSource_equiv_clean {stateCount : Nat}
    (fuel : Nat) (L : Layout stateCount)
    (callerData : Word MachineCodeSymbol) :
    Tape.Equiv (postFuelLocatorSource fuel L callerData).tape
      (FieldLocator.startConfig
        (FuelDecrementMachine.withFuel fuel L) callerData).tape := by
  exact Tape.Equiv.trans
    (roundTripTape_equiv
      (RewindWord.gateTape
        (Frame.protectedWord
          (FuelDecrementMachine.withFuel fuel L) callerData) 1))
    (FuelDecrementMachine.endpoint_tape_equiv_input fuel L callerData)

/-- The fuel/padding seam is not the blocker: the left-payload locator runs
from the actual padded endpoint with the same exact step count and final
control as on a canonical input. -/
theorem postFuel_leftPayload_locator_run {stateCount : Nat}
    (fuel : Nat) (L : Layout stateCount)
    (callerData : Word MachineCodeSymbol) :
    let target := FuelDecrementMachine.withFuel fuel L
    exists endpoint,
      (FieldLocator.machine .leftPayload).runConfigExact?
          (FieldLocator.leftPayloadSteps target)
          (postFuelLocatorSource fuel L callerData) = some endpoint ∧
      endpoint.state = .gate ∧
      Tape.Equiv
        (FieldLocator.config .gate
          (LeftPrepend.leftPayloadPrefix target).reverse
          (LeftPrepend.leftPayloadSuffix target callerData)).tape
        endpoint.tape := by
  let target := FuelDecrementMachine.withFuel fuel L
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        (FieldLocator.locate_leftPayload_exact target callerData)
        (Tape.Equiv.symm
          (postFuelLocatorSource_equiv_clean fuel L callerData)) with
    ⟨endpoint, hrun, hstate, htape⟩
  exact ⟨endpoint, hrun, hstate, htape⟩

def runSteps {stateCount : Nat}
    (fuel : Nat) (L : Layout stateCount)
    (callerData : Word MachineCodeSymbol) : Nat :=
  (FuelDecrementMachine.runSteps fuel L callerData + 2) +
    FieldLocator.leftPayloadSteps
      (FuelDecrementMachine.withFuel fuel L)

/-- One exact run of one finite machine, from the canonical protected frame
through fuel decrement and into the actual padded left-payload boundary. -/
theorem unified_run_to_leftPayload {stateCount : Nat}
    (selected : SerializedHeadDispatch.Selected stateCount)
    (fuel : Nat) (L : Layout stateCount)
    (callerData : Word MachineCodeSymbol) :
    let target := FuelDecrementMachine.withFuel fuel L
    exists endpoint,
      (machine selected).runConfigExact? (runSteps fuel L callerData)
          (fuelConfig selected
            (FuelDecrementMachine.startConfig
              (Frame.protectedWord
                (FuelDecrementMachine.withFuel (fuel + 1) L)
                callerData))) = some endpoint ∧
      endpoint.state = .locate selected .gate ∧
      Tape.Equiv
        (FieldLocator.config .gate
          (LeftPrepend.leftPayloadPrefix target).reverse
          (LeftPrepend.leftPayloadSuffix target callerData)).tape
        endpoint.tape := by
  let target := FuelDecrementMachine.withFuel fuel L
  rcases postFuel_leftPayload_locator_run fuel L callerData with
    ⟨locatorEndpoint, hlocator, hlocatorState, hlocatorTape⟩
  let outerEndpoint := locateConfig selected locatorEndpoint
  have hfuel := fuel_run_exact selected fuel L callerData
  have hhandoff := fuel_handoff_run_exact selected
    (Frame.protectedWord target callerData)
  have hlocatorOuter := locate_run_of_some selected hlocator
  have hpref := runConfigExact_trans selected hfuel hhandoff
  have hrun := runConfigExact_trans selected hpref hlocatorOuter
  refine ⟨outerEndpoint, ?_, ?_, ?_⟩
  · simpa [runSteps, target, postFuelLocatorSource, outerEndpoint]
      using hrun
  · simp [outerEndpoint, locateConfig,
      TuringMachine.PhaseEmbedding.liftConfig, hlocatorState]
  · exact hlocatorTape

end SelectedFuelThenLeftBoundary

end PresentAction
end Update
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
