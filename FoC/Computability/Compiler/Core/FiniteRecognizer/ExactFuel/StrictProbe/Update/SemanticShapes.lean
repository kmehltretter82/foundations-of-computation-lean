import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame.Fuel

set_option doc.verso true

/-!
# Selected-update semantic shapes

Relate the four physical motion layouts to the carried-frame successor used by
the exact-fuel driver induction.
-/

namespace FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.Update.SemanticShapes

open SerializedFieldComposer

theorem emptyLeft_target_eq_afterSelected {stateCount : Nat}
    (fuel : Nat) (F : CarriedStateFrame.LoopFrame stateCount)
    (write : Option MachineCodeSymbol) (nextState : Fin stateCount)
    (hleft : F.physicalFrame.left = []) :
    MoveLeftEmpty.reshapedLayout
        (FuelDecrementMachine.withFuel fuel F.physicalFrame) write =
      (CarriedStateFrame.afterSelected fuel write Direction.left
        nextState F).physicalFrame := by
  calc
    MoveLeftEmpty.reshapedLayout
        (FuelDecrementMachine.withFuel fuel F.physicalFrame) write =
        HeadActionShape.moveLeftTarget
          (FuelDecrementMachine.withFuel fuel F.physicalFrame).fuel write
          (FuelDecrementMachine.withFuel fuel F.physicalFrame).state
          (FuelDecrementMachine.withFuel fuel F.physicalFrame) :=
      MoveLeftEmpty.reshapedLayout_eq_moveLeftTarget
        (FuelDecrementMachine.withFuel fuel F.physicalFrame) write
        (by simpa [FuelDecrementMachine.withFuel] using hleft)
    _ = (CarriedStateFrame.afterSelected fuel write Direction.left
          nextState F).physicalFrame := by
      cases F with
      | mk carried physical =>
          cases physical with
          | mk layoutFuel state left head right =>
              simp only at hleft
              subst left
              rfl

theorem emptyRight_target_eq_afterSelected {stateCount : Nat}
    (fuel : Nat) (F : CarriedStateFrame.LoopFrame stateCount)
    (write : Option MachineCodeSymbol) (nextState : Fin stateCount)
    (hright : F.physicalFrame.right = []) :
    MoveRightEmpty.reshapedLayout
        (FuelDecrementMachine.withFuel fuel F.physicalFrame) write =
      (CarriedStateFrame.afterSelected fuel write Direction.right
        nextState F).physicalFrame := by
  calc
    MoveRightEmpty.reshapedLayout
        (FuelDecrementMachine.withFuel fuel F.physicalFrame) write =
        HeadActionShape.moveRightTarget
          (FuelDecrementMachine.withFuel fuel F.physicalFrame).fuel write
          (FuelDecrementMachine.withFuel fuel F.physicalFrame).state
          (FuelDecrementMachine.withFuel fuel F.physicalFrame) :=
      MoveRightEmpty.reshapedLayout_eq_moveRightTarget
        (FuelDecrementMachine.withFuel fuel F.physicalFrame) write
        (by simpa [FuelDecrementMachine.withFuel] using hright)
    _ = (CarriedStateFrame.afterSelected fuel write Direction.right
          nextState F).physicalFrame := by
      cases F with
      | mk carried physical =>
          cases physical with
          | mk layoutFuel state left head right =>
              simp only at hright
              subst right
              rfl

theorem nonemptyRight_target_eq_afterSelected {stateCount : Nat}
    (fuel : Nat) (F : CarriedStateFrame.LoopFrame stateCount)
    (write : Option MachineCodeSymbol) (nextState : Fin stateCount)
    (nextHead : Option MachineCodeSymbol)
    (remainingRight : List (Option MachineCodeSymbol))
    (hright : F.physicalFrame.right = nextHead :: remainingRight) :
    MoveRightNonempty.reshapedLayout
        (FuelDecrementMachine.withFuel fuel F.physicalFrame)
        write nextHead remainingRight =
      (CarriedStateFrame.afterSelected fuel write Direction.right
        nextState F).physicalFrame := by
  calc
    MoveRightNonempty.reshapedLayout
        (FuelDecrementMachine.withFuel fuel F.physicalFrame)
        write nextHead remainingRight =
        HeadActionShape.moveRightTarget
          (FuelDecrementMachine.withFuel fuel F.physicalFrame).fuel write
          (FuelDecrementMachine.withFuel fuel F.physicalFrame).state
          (FuelDecrementMachine.withFuel fuel F.physicalFrame) :=
      MoveRightNonempty.reshapedLayout_eq_moveRightTarget
        (FuelDecrementMachine.withFuel fuel F.physicalFrame)
        write nextHead remainingRight
        (by simpa [FuelDecrementMachine.withFuel] using hright)
    _ = (CarriedStateFrame.afterSelected fuel write Direction.right
          nextState F).physicalFrame := by
      cases F with
      | mk carried physical =>
          cases physical with
          | mk layoutFuel state left head right =>
              simp only at hright
              subst right
              rfl

end FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.Update.SemanticShapes
