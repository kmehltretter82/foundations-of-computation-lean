import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Update.Runs

namespace FoC
namespace Computability

open Languages

namespace Section53FixedPlaceholderUpdate

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer

/-!
**Dynamic-to-fixed placeholder update bridge.** This bridge converts a
dynamically encoded Boolean-tape configuration into the source of the verified
strict-probe selected-update kernel. The kernel uses one physical placeholder
state; the interpreter's unbounded runtime state stays as caller-owned tape
data.
-/

def encodeCell : Option Bool -> Option MachineCodeSymbol
  | none => none
  | some false => some MachineCodeSymbol.zero
  | some true => some MachineCodeSymbol.one

def encodeTape (tape : Tape Bool) : Tape MachineCodeSymbol where
  left := tape.left.map encodeCell
  head := encodeCell tape.head
  right := tape.right.map encodeCell

def placeholder : Fin 1 := ⟨0, by decide⟩

def layout (fuel : Nat) (tape : Tape Bool) : Layout 1 where
  fuel := fuel
  state := placeholder
  left := tape.left.map encodeCell
  head := encodeCell tape.head
  right := tape.right.map encodeCell

def frame (fuel : Nat) (tape : Tape Bool) :
    CarriedStateFrame.LoopFrame 1 :=
  CarriedStateFrame.ofParsed (layout fuel tape)

/-- Mutable runtime state and immutable table retained behind the verified
fixed-placeholder tape frame. -/
def callerData
    (runtimeState haltState : Nat)
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend runtimeState
    (MachineCodeSymbol.header ::
      MachineDescription.encodeNatAppend haltState
        (MachineCodeSymbol.header ::
          MachineDescription.encodeTransitionsAppend transitions suffix))

def workWord
    (fuel runtimeState haltState : Nat) (tape : Tape Bool)
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  Frame.protectedWord (layout fuel tape)
    (callerData runtimeState haltState transitions suffix)

theorem decode_workWord
    (fuel runtimeState haltState : Nat) (tape : Tape Bool)
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    Layout.decode 1
        (workWord fuel runtimeState haltState tape transitions suffix) =
      some
        (layout fuel tape,
          Frame.callerTag ::
            callerData runtimeState haltState transitions suffix) := by
  exact Layout.decode_encodeAppend _ _

theorem headLocator_run_workWord
    (fuel runtimeState haltState : Nat) (tape : Tape Bool)
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    HeadLocator.machine.runConfigExact?
        (HeadLocator.locatorSteps (layout fuel tape))
        (HeadLocator.locatorStartConfig (layout fuel tape)
          (callerData runtimeState haltState transitions suffix)) =
      some
        (HeadLocator.gateConfig (encodeCell tape.head)
          (workWord fuel runtimeState haltState tape transitions
            suffix)) := by
  exact HeadLocator.run_exact (layout fuel tape)
    (callerData runtimeState haltState transitions suffix)

def dummyMachine
    (write : Option Bool) (direction : Direction) :
    TuringMachine MachineCodeSymbol (Fin 1) where
  start := placeholder
  halt := placeholder
  transition := fun _ _ => some (encodeCell write, direction, placeholder)
  statesFinite := Foundation.FiniteType.fin 1

@[simp] theorem semanticConfig_frame
    (fuel : Nat) (tape : Tape Bool) :
    RelationalDriverInduction.semanticConfig (frame fuel tape) =
      { state := placeholder, tape := encodeTape tape } := by
  rfl

@[simp] theorem dummyMachine_transition
    (write : Option Bool) (direction : Direction)
    (tape : Tape Bool) :
    (dummyMachine write direction).transition
        (RelationalDriverInduction.semanticConfig
          (frame 0 tape)).state
        (Tape.read
          (RelationalDriverInduction.semanticConfig
            (frame 0 tape)).tape) =
      some (encodeCell write, direction, placeholder) := by
  rfl

theorem encodeTape_write
    (write : Option Bool) (tape : Tape Bool) :
    encodeTape (Tape.write write tape) =
      Tape.write (encodeCell write) (encodeTape tape) := by
  cases tape
  rfl

theorem encodeTape_move
    (direction : Direction) (tape : Tape Bool) :
    encodeTape (Tape.move direction tape) =
      Tape.move direction (encodeTape tape) := by
  cases direction with
  | left =>
      cases tape with
      | mk left head right =>
          cases left <;> rfl
  | right =>
      cases tape with
      | mk left head right =>
          cases right <;> rfl

theorem encodeTape_apply
    (write : Option Bool) (direction : Direction) (tape : Tape Bool) :
    encodeTape (Tape.move direction (Tape.write write tape)) =
      Tape.move direction (Tape.write (encodeCell write) (encodeTape tape)) := by
  rw [encodeTape_move, encodeTape_write]

theorem semanticConfig_afterSelected
    (fuel : Nat) (write : Option Bool) (direction : Direction)
    (tape : Tape Bool) :
    RelationalDriverInduction.semanticConfig
        (CarriedStateFrame.afterSelected fuel (encodeCell write)
          direction placeholder (frame (fuel + 1) tape)) =
      { state := placeholder
        tape := encodeTape
          (Tape.move direction (Tape.write write tape)) } := by
  rw [RelationalDriverInduction.semanticConfig_afterSelected]
  simp [DriverInduction.selectedTarget, encodeTape_apply]

theorem physicalFrame_afterSelected
    (fuel : Nat) (write : Option Bool) (direction : Direction)
    (tape : Tape Bool) :
    (CarriedStateFrame.withFuel fuel
      (CarriedStateFrame.afterSelected fuel (encodeCell write)
        direction placeholder (frame (fuel + 1) tape))).physicalFrame =
      layout fuel (Tape.move direction (Tape.write write tape)) := by
  cases direction with
  | left =>
      cases tape with
      | mk left head right =>
          cases left <;> rfl
  | right =>
      cases tape with
      | mk left head right =>
          cases right <;> rfl

/-- Existing finite update kernel, specialized to the one-state physical
placeholder, executes every dynamically selected Boolean write/move action.
The arbitrary caller data can contain the decoded runtime state, transition
table, and outer continuation.
-/
theorem selected_update_run
    (callerData : Word MachineCodeSymbol)
    (fuel : Nat) (tape : Tape Bool)
    (write : Option Bool) (direction : Direction) :
    let selected := Update.LeftKernel.selectedPayload
      (encodeCell write) direction placeholder
    exists steps targetTape,
      (Update.Kernel.machine selected).runConfigExact? steps
          { state := (Update.Kernel.machine selected).start
            tape := Update.LeftKernel.selectedPrefixTape
              callerData fuel (frame (fuel + 1) tape)
              (encodeCell write) direction placeholder } =
        some
          { state := Update.Kernel.Control.done
            tape := targetTape } ∧
      RelationalDriverInduction.Represents callerData fuel
        (CarriedStateFrame.afterSelected fuel (encodeCell write)
          direction placeholder (frame (fuel + 1) tape))
        (CyclicDriverIntegration.roundTripTape targetTape) := by
  let M := dummyMachine write direction
  have hrun := Update.Runs.selectedUpdateRuns M callerData
  exact hrun.run fuel (frame (fuel + 1) tape)
    (encodeCell write) direction placeholder (by rfl)

theorem selected_update_run_to_layout
    (callerData : Word MachineCodeSymbol)
    (fuel : Nat) (tape : Tape Bool)
    (write : Option Bool) (direction : Direction) :
    let selected := Update.LeftKernel.selectedPayload
      (encodeCell write) direction placeholder
    exists steps targetTape,
      (Update.Kernel.machine selected).runConfigExact? steps
          { state := (Update.Kernel.machine selected).start
            tape := Update.LeftKernel.selectedPrefixTape
              callerData fuel (frame (fuel + 1) tape)
              (encodeCell write) direction placeholder } =
        some
          { state := Update.Kernel.Control.done
            tape := targetTape } ∧
      Tape.Equiv
        (CyclicDriverIntegration.roundTripTape targetTape)
        (Tape.input
          (Frame.protectedWord
            (layout fuel
              (Tape.move direction (Tape.write write tape)))
            callerData)) := by
  rcases selected_update_run callerData fuel tape write direction with
    ⟨steps, targetTape, hrun, htarget⟩
  refine ⟨steps, targetTape, hrun, ?_⟩
  unfold RelationalDriverInduction.Represents at htarget
  rw [physicalFrame_afterSelected] at htarget
  exact htarget

theorem selected_transition_update_run
    (fuel : Nat) (tape : Tape Bool)
    (selected : TransitionDescription)
    (haltState : Nat)
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    let action := Update.LeftKernel.selectedPayload
      (encodeCell selected.write) selected.move placeholder
    exists steps targetTape,
      (Update.Kernel.machine action).runConfigExact? steps
          { state := (Update.Kernel.machine action).start
            tape := Update.LeftKernel.selectedPrefixTape
              (callerData selected.target haltState transitions suffix)
              fuel (frame (fuel + 1) tape)
              (encodeCell selected.write) selected.move placeholder } =
        some
          { state := Update.Kernel.Control.done
            tape := targetTape } ∧
      Tape.Equiv
        (CyclicDriverIntegration.roundTripTape targetTape)
        (Tape.input
          (workWord fuel selected.target
            haltState
            (Tape.move selected.move
              (Tape.write selected.write tape))
            transitions suffix)) := by
  simpa [workWord] using
    selected_update_run_to_layout
      (callerData selected.target haltState transitions suffix)
      fuel tape selected.write selected.move


end Section53FixedPlaceholderUpdate

end Computability
end FoC
