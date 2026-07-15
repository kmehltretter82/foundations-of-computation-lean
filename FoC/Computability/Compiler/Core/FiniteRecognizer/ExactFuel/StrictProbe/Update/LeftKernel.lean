import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Update.LeftFirst
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Dispatch.SerializedHead

set_option doc.verso true

/-!
# Nonempty-left kernel bridge

Canonical selected-entry configurations and layout identities connect the
first-edit runner to the complete nonempty-left update.
-/

namespace FoC
namespace Computability
open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace Update
namespace LeftKernel
open SerializedFieldComposer

def selectedPayload {stateCount : Nat}
    (write : Option MachineCodeSymbol) (direction : Direction)
    (nextState : Fin stateCount) :
    SerializedHeadDispatch.Selected stateCount where
  write := write
  direction := direction
  nextState := nextState

def roundTripTape (T : Tape MachineCodeSymbol) : Tape MachineCodeSymbol :=
  Tape.move Direction.left (Tape.move Direction.right T)

def selectedPrefixTape {stateCount : Nat}
    (callerData : Word MachineCodeSymbol) (fuel : Nat)
    (F : CarriedStateFrame.LoopFrame stateCount)
    (write : Option MachineCodeSymbol) (direction : Direction)
    (nextState : Fin stateCount) : Tape MachineCodeSymbol :=
  let L := (CarriedStateFrame.withFuel (fuel + 1) F).physicalFrame
  roundTripTape
    (SerializedHeadDispatch.selectedConfig
      (selectedPayload write direction nextState)
      (HeadLocator.gateTape (Frame.protectedWord L callerData))).tape

theorem headLocator_gateTape_equiv_input (word : Word MachineCodeSymbol) :
    Tape.Equiv (HeadLocator.gateTape word) (Tape.input word) := by
  cases word with
  | nil =>
      simp [HeadLocator.gateTape, Tape.input, Tape.blank, Tape.Equiv, Tape.dropTrailingNone]
  | cons first rest =>
      simp [HeadLocator.gateTape, Tape.input, Tape.Equiv, Tape.dropTrailingNone]
/-- The two mandatory dispatch bounces and the head-locator rewind add only
far-edge padding to the canonical protected input. -/
theorem selectedPrefixTape_equiv_input {stateCount : Nat} (callerData : Word MachineCodeSymbol) (fuel : Nat)
    (F : CarriedStateFrame.LoopFrame stateCount)
    (write : Option MachineCodeSymbol) (direction : Direction) (nextState : Fin stateCount) :
    let L := (CarriedStateFrame.withFuel (fuel + 1) F).physicalFrame
    Tape.Equiv (Tape.input (Frame.protectedWord L callerData)) (selectedPrefixTape
        callerData fuel F write direction nextState) := by
  let L := (CarriedStateFrame.withFuel (fuel + 1) F).physicalFrame
  let word := Frame.protectedWord L callerData
  let selected := selectedPayload
    write direction nextState
  have hhead := headLocator_gateTape_equiv_input word
  have hinner := SerializedHeadDispatch.roundTripTape_equiv (HeadLocator.gateTape word)
  have houter := Machine.moveLeft_moveRight_equiv_self (SerializedHeadDispatch.roundTripTape
      (HeadLocator.gateTape word))
  have hchain := Tape.Equiv.trans houter (Tape.Equiv.trans hinner hhead)
  exact Tape.Equiv.symm (by
    simpa [selectedPrefixTape, selectedPayload,
      roundTripTape, SerializedHeadDispatch.selectedConfig,
      L, word, selected] using hchain)
/-- Direct bridge from the selected-entry tape to the canonical nonempty-left
checkpoint.  This is not yet the full update-kernel run: head replacement and
right prepend remain after the returned endpoint. -/
theorem selectedPrefix_run_to_removed_left_layout {stateCount : Nat} (callerData : Word MachineCodeSymbol) (fuel : Nat)
    (F : CarriedStateFrame.LoopFrame stateCount) (write : Option MachineCodeSymbol) (nextState : Fin stateCount)
    (nextHead : Option MachineCodeSymbol) (remainingLeft : List (Option MachineCodeSymbol))
    (hleft : F.physicalFrame.left = nextHead :: remainingLeft) :
    let selected := selectedPayload
      write Direction.left nextState
    let target := FuelDecrementMachine.withFuel fuel F.physicalFrame
    let removed := MoveLeftNonempty.removedLeftLayout target remainingLeft
    exists endpoint, (Update.LeftFirst.machine selected).runConfigExact?
          (Update.LeftFirst.throughCountSteps fuel F.physicalFrame callerData nextHead remainingLeft)
          { state := (Update.LeftFirst.machine selected).start
            tape := selectedPrefixTape
              callerData fuel F write Direction.left nextState } = some endpoint ∧
      endpoint.state = Update.LeftFirst.Control.count selected nextHead
          (.delete (.rewind .gate)) ∧ Tape.Equiv
        (Tape.input (Frame.protectedWord removed callerData)) endpoint.tape := by
  let selected := selectedPayload
    write Direction.left nextState
  have hsource := selectedPrefixTape_equiv_input callerData fuel F write Direction.left nextState
  simpa [selected, CarriedStateFrame.withFuel, FuelDecrementMachine.withFuel] using
    Update.LeftFirst.unified_run_to_removed_left_layout_of_source_equiv
      selected fuel F.physicalFrame callerData nextHead remainingLeft hleft
      (selectedPrefixTape callerData fuel F write Direction.left nextState)
      (by simpa [CarriedStateFrame.withFuel, FuelDecrementMachine.withFuel] using hsource)
theorem completed_left_shape_eq_afterSelected_physicalFrame
    {stateCount : Nat} (fuel : Nat) (F : CarriedStateFrame.LoopFrame stateCount)
    (write : Option MachineCodeSymbol) (nextState : Fin stateCount)
    (nextHead : Option MachineCodeSymbol) (remainingLeft : List (Option MachineCodeSymbol))
    (hleft : F.physicalFrame.left = nextHead :: remainingLeft) : MoveLeftNonempty.reshapedLayout
        (FuelDecrementMachine.withFuel fuel F.physicalFrame) write nextHead remainingLeft =
      (CarriedStateFrame.afterSelected fuel write Direction.left nextState F).physicalFrame := by
  cases F with
  | mk carried physical =>
      cases physical with
      | mk layoutFuel state left head right =>
          simp only at hleft
          subst left
          rfl
/-- The two exact right-side edits target precisely the physical frame used by
the recursive selected-action contract. -/
theorem right_tail_target_eq_afterSelected {stateCount : Nat} (fuel : Nat) (F : CarriedStateFrame.LoopFrame stateCount)
    (write : Option MachineCodeSymbol) (nextState : Fin stateCount)
    (nextHead : Option MachineCodeSymbol) (remainingLeft : List (Option MachineCodeSymbol))
    (hleft : F.physicalFrame.left = nextHead :: remainingLeft) :
    let target := FuelDecrementMachine.withFuel fuel F.physicalFrame
    let removed := MoveLeftNonempty.removedLeftLayout target remainingLeft
    let replaced := HeadReplacement.replaceHead removed nextHead
    RightPrepend.prependedRightLayout replaced write = (CarriedStateFrame.afterSelected fuel write Direction.left
        nextState F).physicalFrame := by
  simpa [MoveLeftNonempty.reshapedLayout, MoveLeftNonempty.headReplacedLayout] using
    completed_left_shape_eq_afterSelected_physicalFrame fuel F write nextState nextHead remainingLeft hleft
end LeftKernel
end Update
end StrictProbe
end ExactFuel
end FiniteRecognizer
end Computability
end FoC
