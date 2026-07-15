import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Dispatch.NeighborProbe
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Dispatch.SerializedHead
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Update.LeftNonempty
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Update.FuelPrefix
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Update.LeftEmpty
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Update.RightEmpty
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Update.RightNonempty
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Driver.CyclicMachine
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Update.SemanticShapes

set_option doc.verso true

/-!
# Selected-update kernel

The selected-update kernel dispatches on neighboring payload emptiness and
joins all four left/right update branches in one finite control type.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace Update
namespace Kernel

open SerializedFieldComposer

/-- The three cases that share the ordinary fuel-decrement prefix.  The
nonempty-left case has its own already-fused selected-prefix machine. -/
inductive FuelBranch where
  | leftEmpty
  | rightEmpty
  | rightNonempty
deriving DecidableEq

namespace FuelBranch

def elems : List FuelBranch := [.leftEmpty, .rightEmpty, .rightNonempty]

def finite : Foundation.FiniteType FuelBranch where
  elems := elems
  complete := by
    intro branch
    cases branch <;> simp [elems]

end FuelBranch

/-- A single finite control union for the selected transition update.  Every
handoff uses a right/left bounce, so the next phase receives a tape equivalent
to the preceding endpoint without requiring a fixed physical window. -/
inductive Control (stateCount : Nat) where
  | probe (inner : Dispatch.NeighborProbe.Control)
  | probeLeftReturn
  | probeFuelReturn (branch : FuelBranch)
  | leftNonempty
      (inner : Update.LeftNonempty.Control stateCount)
  | fuel (branch : FuelBranch) (inner : FuelDecrementMachine.Control)
  | fuelReturn (branch : FuelBranch)
  | leftEmpty (inner : Update.LeftEmpty.Control)
  | rightEmpty (inner : Update.RightEmpty.Control)
  | rightNonempty
      (inner : Update.RightNonempty.FullMachine.Control)
  | finishReturn
  | done
deriving DecidableEq

namespace Control

def fuelPairs : Foundation.FiniteType
    (FuelBranch × FuelDecrementMachine.Control) :=
  Foundation.FiniteType.prod FuelBranch.finite
    FuelDecrementMachine.Control.finite

def elems (stateCount : Nat) : List (Control stateCount) :=
  List.append
    (Dispatch.NeighborProbe.Control.finite.elems.map Control.probe)
    (List.append [.probeLeftReturn]
      (List.append
        (FuelBranch.elems.map Control.probeFuelReturn)
        (List.append
          ((Update.LeftNonempty.Control.finite stateCount).elems.map
            Control.leftNonempty)
          (List.append
            (fuelPairs.elems.map (fun payload =>
              Control.fuel payload.1 payload.2))
            (List.append
              (FuelBranch.elems.map Control.fuelReturn)
              (List.append
                (Update.LeftEmpty.Control.finite.elems.map
                  Control.leftEmpty)
                (List.append
                  (Update.RightEmpty.Control.finite.elems.map
                    Control.rightEmpty)
                  (List.append
                    (Update.RightNonempty.FullMachine.Control.finite.elems.map
                      Control.rightNonempty)
                    [.finishReturn, .done]))))))))

def finite (stateCount : Nat) :
    Foundation.FiniteType (Control stateCount) where
  elems := elems stateCount
  complete := by
    intro control
    cases control with
    | probe inner =>
        have h := Dispatch.NeighborProbe.Control.finite.complete inner
        simp [elems, h]
    | probeLeftReturn => simp [elems]
    | probeFuelReturn branch =>
        have h := FuelBranch.finite.complete branch
        change branch ∈ FuelBranch.elems at h
        simp [elems, h]
    | leftNonempty inner =>
        have h :=
          (Update.LeftNonempty.Control.finite stateCount).complete
            inner
        simp [elems, h]
    | fuel branch inner =>
        have h := fuelPairs.complete (branch, inner)
        simp [elems, h]
    | fuelReturn branch =>
        have h := FuelBranch.finite.complete branch
        change branch ∈ FuelBranch.elems at h
        simp [elems, h]
    | leftEmpty inner =>
        have h := Update.LeftEmpty.Control.finite.complete inner
        simp [elems, h]
    | rightEmpty inner =>
        have h := Update.RightEmpty.Control.finite.complete inner
        simp [elems, h]
    | rightNonempty inner =>
        have h :=
          Update.RightNonempty.FullMachine.Control.finite.complete
            inner
        simp [elems, h]
    | finishReturn => simp [elems]
    | done => simp [elems]

end Control

abbrev Selected (stateCount : Nat) :=
  SerializedHeadDispatch.Selected stateCount

def transition {stateCount : Nat} (selected : Selected stateCount) :
    Control stateCount -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control stateCount)
  | .probe (.done isEmpty), read =>
      match selected.direction, isEmpty with
      | .left, false =>
          some (read, Direction.right, .probeLeftReturn)
      | .left, true =>
          some (read, Direction.right, .probeFuelReturn .leftEmpty)
      | .right, false =>
          some (read, Direction.right, .probeFuelReturn .rightNonempty)
      | .right, true =>
          some (read, Direction.right, .probeFuelReturn .rightEmpty)
  | .probe inner, read =>
      match Dispatch.NeighborProbe.transition inner read with
      | none => none
      | some (written, direction, target) =>
          some (written, direction, .probe target)
  | .probeLeftReturn, read =>
      some
        (read, Direction.left,
          .leftNonempty
            (Update.LeftNonempty.machine selected).start)
  | .probeFuelReturn branch, read =>
      some
        (read, Direction.left,
          .fuel branch FuelDecrementMachine.machine.start)
  | .leftNonempty inner, read =>
      if inner = (Update.LeftNonempty.machine selected).halt then
        some (read, Direction.right, .finishReturn)
      else
        match Update.LeftNonempty.transition selected inner read with
        | none => none
        | some (written, direction, target) =>
            some (written, direction, .leftNonempty target)
  | .fuel branch inner, read =>
      if inner = FuelDecrementMachine.machine.halt then
        some (read, Direction.right, .fuelReturn branch)
      else
        match FuelDecrementMachine.transition inner read with
        | none => none
        | some (written, direction, target) =>
            some (written, direction, .fuel branch target)
  | .fuelReturn .leftEmpty, read =>
      some
        (read, Direction.left,
          .leftEmpty
            (Update.LeftEmpty.machine selected.write).start)
  | .fuelReturn .rightEmpty, read =>
      some
        (read, Direction.left,
          .rightEmpty
            (Update.RightEmpty.machine selected.write).start)
  | .fuelReturn .rightNonempty, read =>
      some
        (read, Direction.left,
          .rightNonempty
            (Update.RightNonempty.FullMachine.machine
              selected.write).start)
  | .leftEmpty inner, read =>
      if inner = (Update.LeftEmpty.machine selected.write).halt then
        some (read, Direction.right, .finishReturn)
      else
        match Update.LeftEmpty.transition selected.write inner read with
        | none => none
        | some (written, direction, target) =>
            some (written, direction, .leftEmpty target)
  | .rightEmpty inner, read =>
      if inner = (Update.RightEmpty.machine selected.write).halt then
        some (read, Direction.right, .finishReturn)
      else
        match Update.RightEmpty.transition selected.write inner read with
        | none => none
        | some (written, direction, target) =>
            some (written, direction, .rightEmpty target)
  | .rightNonempty inner, read =>
      if inner =
          (Update.RightNonempty.FullMachine.machine
            selected.write).halt then
        some (read, Direction.right, .finishReturn)
      else
        match Update.RightNonempty.FullMachine.transition
            selected.write inner read with
        | none => none
        | some (written, direction, target) =>
            some (written, direction, .rightNonempty target)
  | .finishReturn, read =>
      some (read, Direction.left, .done)
  | .done, _ => none

def machine {stateCount : Nat} (selected : Selected stateCount) :
    TuringMachine MachineCodeSymbol (Control stateCount) where
  start := .probe
    (Dispatch.NeighborProbe.machine selected.direction).start
  halt := .done
  transition := transition selected
  statesFinite := Control.finite stateCount

def kernel (stateCount : Nat) :
    CyclicDriverIntegration.UpdateKernel stateCount
      (Control stateCount) where
  finite := Control.finite stateCount
  start selected := (machine selected).start
  halt selected := (machine selected).halt
  transition selected := transition selected
  halt_transition_none := by
    intro selected read
    rfl

end Kernel
end Update
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
