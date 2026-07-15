import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Update.Kernel
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseEmbedding
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseRetarget

set_option doc.verso true

/-!
# Selected-update kernel lifts

Exact phase embeddings and handoff runs compose each selected-update branch
inside the unified production kernel.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace Update
namespace KernelLifts

open SerializedFieldComposer

abbrev KernelControl (stateCount : Nat) :=
  Update.Kernel.Control stateCount

abbrev Selected (stateCount : Nat) :=
  Update.Kernel.Selected stateCount

def probeConfig {stateCount : Nat}
    (c : TuringMachine.Configuration MachineCodeSymbol
      Dispatch.NeighborProbe.Control) :
    TuringMachine.Configuration MachineCodeSymbol (KernelControl stateCount) :=
  TuringMachine.PhaseEmbedding.liftConfig
    Update.Kernel.Control.probe c

def leftNonemptyConfig {stateCount : Nat}
    (c : TuringMachine.Configuration MachineCodeSymbol
      (Update.LeftNonempty.Control stateCount)) :
    TuringMachine.Configuration MachineCodeSymbol (KernelControl stateCount) :=
  TuringMachine.PhaseEmbedding.liftConfig
    Update.Kernel.Control.leftNonempty c

def fuelConfig {stateCount : Nat}
    (branch : Update.Kernel.FuelBranch)
    (c : TuringMachine.Configuration MachineCodeSymbol
      FuelDecrementMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol (KernelControl stateCount) :=
  TuringMachine.PhaseEmbedding.liftConfig
    (Update.Kernel.Control.fuel branch) c

def leftEmptyConfig {stateCount : Nat}
    (c : TuringMachine.Configuration MachineCodeSymbol
      Update.LeftEmpty.Control) :
    TuringMachine.Configuration MachineCodeSymbol (KernelControl stateCount) :=
  TuringMachine.PhaseEmbedding.liftConfig
    Update.Kernel.Control.leftEmpty c

def rightEmptyConfig {stateCount : Nat}
    (c : TuringMachine.Configuration MachineCodeSymbol
      Update.RightEmpty.Control) :
    TuringMachine.Configuration MachineCodeSymbol (KernelControl stateCount) :=
  TuringMachine.PhaseEmbedding.liftConfig
    Update.Kernel.Control.rightEmpty c

def rightNonemptyConfig {stateCount : Nat}
    (c : TuringMachine.Configuration MachineCodeSymbol
      Update.RightNonempty.FullMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol (KernelControl stateCount) :=
  TuringMachine.PhaseEmbedding.liftConfig
    Update.Kernel.Control.rightNonempty c

theorem probe_step_of_some {stateCount : Nat}
    (selected : Selected stateCount)
    (c d : TuringMachine.Configuration MachineCodeSymbol
      Dispatch.NeighborProbe.Control)
    (hstep :
      (Dispatch.NeighborProbe.machine selected.direction).stepConfig c =
        some d) :
    (Update.Kernel.machine selected).stepConfig (probeConfig c) =
      some (probeConfig d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [Dispatch.NeighborProbe.machine] at hstep
      cases htransition : Dispatch.NeighborProbe.transition inner
          (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨written, direction, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          cases inner with
          | done isEmpty =>
              simp [Dispatch.NeighborProbe.transition] at htransition
          | leftLocate inner
          | leftRewind isEmpty inner
          | rightLocate inner
          | rightMarkedRewind isEmpty inner
          | rightRestore isEmpty inner
          | rightCleanRewind isEmpty inner =>
              simp [Update.Kernel.machine,
                Update.Kernel.transition, probeConfig,
                TuringMachine.PhaseEmbedding.liftConfig,
                htransition]

theorem probe_run_of_some {stateCount : Nat}
    (selected : Selected stateCount)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      Dispatch.NeighborProbe.Control}
    (hrun :
      (Dispatch.NeighborProbe.machine selected.direction).runConfigExact?
        steps source = some target) :
    (Update.Kernel.machine selected).runConfigExact? steps
        (probeConfig source) = some (probeConfig target) := by
  apply
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      Update.Kernel.Control.probe
  · exact probe_step_of_some selected
  · exact hrun

theorem leftNonempty_step_of_some {stateCount : Nat}
    (selected : Selected stateCount)
    (c d : TuringMachine.Configuration MachineCodeSymbol
      (Update.LeftNonempty.Control stateCount))
    (hstep :
      (Update.LeftNonempty.machine selected).stepConfig c =
        some d) :
    (Update.Kernel.machine selected).stepConfig
        (leftNonemptyConfig c) = some (leftNonemptyConfig d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [Update.LeftNonempty.machine] at hstep
      cases htransition : Update.LeftNonempty.transition selected
          inner (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨written, direction, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          have hactive : inner ≠
              (Update.LeftNonempty.machine selected).halt := by
            intro heq
            subst inner
            simp [Update.LeftNonempty.machine,
              Update.LeftNonempty.transition] at htransition
          simp [Update.Kernel.machine,
            Update.Kernel.transition, leftNonemptyConfig,
            TuringMachine.PhaseEmbedding.liftConfig,
            hactive, htransition]

theorem leftNonempty_run_of_some {stateCount : Nat}
    (selected : Selected stateCount)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      (Update.LeftNonempty.Control stateCount)}
    (hrun :
      (Update.LeftNonempty.machine selected).runConfigExact?
        steps source = some target) :
    (Update.Kernel.machine selected).runConfigExact? steps
        (leftNonemptyConfig source) = some (leftNonemptyConfig target) := by
  apply
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      Update.Kernel.Control.leftNonempty
  · exact leftNonempty_step_of_some selected
  · exact hrun

theorem fuel_step_of_some {stateCount : Nat}
    (selected : Selected stateCount)
    (branch : Update.Kernel.FuelBranch)
    (c d : TuringMachine.Configuration MachineCodeSymbol
      FuelDecrementMachine.Control)
    (hstep : FuelDecrementMachine.machine.stepConfig c = some d) :
    (Update.Kernel.machine selected).stepConfig
        (fuelConfig branch c) = some (fuelConfig branch d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [FuelDecrementMachine.machine] at hstep
      cases htransition : FuelDecrementMachine.transition inner
          (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨written, direction, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          have hactive : inner ≠ FuelDecrementMachine.machine.halt := by
            intro heq
            subst inner
            simp [FuelDecrementMachine.machine,
              FuelDecrementMachine.transition,
              DeleteOneRestagedMachine.transition,
              RewindWord.transition] at htransition
          simp [Update.Kernel.machine,
            Update.Kernel.transition, fuelConfig,
            TuringMachine.PhaseEmbedding.liftConfig,
            hactive, htransition]

theorem fuel_run_of_some {stateCount : Nat}
    (selected : Selected stateCount)
    (branch : Update.Kernel.FuelBranch)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      FuelDecrementMachine.Control}
    (hrun : FuelDecrementMachine.machine.runConfigExact?
      steps source = some target) :
    (Update.Kernel.machine selected).runConfigExact? steps
        (fuelConfig branch source) = some (fuelConfig branch target) := by
  apply
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      (Update.Kernel.Control.fuel branch)
  · exact fuel_step_of_some selected branch
  · exact hrun

theorem leftEmpty_step_of_some {stateCount : Nat}
    (selected : Selected stateCount)
    (c d : TuringMachine.Configuration MachineCodeSymbol
      Update.LeftEmpty.Control)
    (hstep : (Update.LeftEmpty.machine selected.write).stepConfig c =
      some d) :
    (Update.Kernel.machine selected).stepConfig
        (leftEmptyConfig c) = some (leftEmptyConfig d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [Update.LeftEmpty.machine] at hstep
      cases htransition : Update.LeftEmpty.transition selected.write
          inner (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨written, direction, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          have hactive : inner ≠
              (Update.LeftEmpty.machine selected.write).halt := by
            intro heq
            subst inner
            simp [Update.LeftEmpty.machine,
              Update.LeftEmpty.transition] at htransition
          simp [Update.Kernel.machine,
            Update.Kernel.transition, leftEmptyConfig,
            TuringMachine.PhaseEmbedding.liftConfig,
            hactive, htransition]

theorem leftEmpty_run_of_some {stateCount : Nat}
    (selected : Selected stateCount)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      Update.LeftEmpty.Control}
    (hrun :
      (Update.LeftEmpty.machine selected.write).runConfigExact?
        steps source = some target) :
    (Update.Kernel.machine selected).runConfigExact? steps
        (leftEmptyConfig source) = some (leftEmptyConfig target) := by
  apply
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      Update.Kernel.Control.leftEmpty
  · exact leftEmpty_step_of_some selected
  · exact hrun

theorem rightEmpty_step_of_some {stateCount : Nat}
    (selected : Selected stateCount)
    (c d : TuringMachine.Configuration MachineCodeSymbol
      Update.RightEmpty.Control)
    (hstep :
      (Update.RightEmpty.machine selected.write).stepConfig c =
        some d) :
    (Update.Kernel.machine selected).stepConfig
        (rightEmptyConfig c) = some (rightEmptyConfig d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [Update.RightEmpty.machine] at hstep
      cases htransition : Update.RightEmpty.transition selected.write
          inner (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨written, direction, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          have hactive : inner ≠
              (Update.RightEmpty.machine selected.write).halt := by
            intro heq
            subst inner
            simp [Update.RightEmpty.machine,
              Update.RightEmpty.transition] at htransition
          simp [Update.Kernel.machine,
            Update.Kernel.transition, rightEmptyConfig,
            TuringMachine.PhaseEmbedding.liftConfig,
            hactive, htransition]

theorem rightEmpty_run_of_some {stateCount : Nat}
    (selected : Selected stateCount)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      Update.RightEmpty.Control}
    (hrun :
      (Update.RightEmpty.machine selected.write).runConfigExact?
        steps source = some target) :
    (Update.Kernel.machine selected).runConfigExact? steps
        (rightEmptyConfig source) = some (rightEmptyConfig target) := by
  apply
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      Update.Kernel.Control.rightEmpty
  · exact rightEmpty_step_of_some selected
  · exact hrun

theorem rightNonempty_step_of_some {stateCount : Nat}
    (selected : Selected stateCount)
    (c d : TuringMachine.Configuration MachineCodeSymbol
      Update.RightNonempty.FullMachine.Control)
    (hstep :
      (Update.RightNonempty.FullMachine.machine
        selected.write).stepConfig c = some d) :
    (Update.Kernel.machine selected).stepConfig
        (rightNonemptyConfig c) = some (rightNonemptyConfig d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [Update.RightNonempty.FullMachine.machine] at hstep
      cases htransition :
          Update.RightNonempty.FullMachine.transition selected.write
            inner (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨written, direction, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          have hactive : inner ≠
              (Update.RightNonempty.FullMachine.machine
                selected.write).halt := by
            intro heq
            subst inner
            simp [Update.RightNonempty.FullMachine.machine,
              Update.RightNonempty.FullMachine.transition,
              Update.RightNonempty.FullMachine.prependEmbed,
              Update.RightNonempty.LeftPrependMachine.machine,
              Update.RightNonempty.LeftPrependMachine.transition,
              Update.RightNonempty.LeftPrependMachine.countEmbed,
              Update.RightNonempty.LeftPrependMachine.countInnerMachine,
              Edits.PositionedLeft.machine,
              Edits.PositionedLeft.transition,
              InsertRestagedMachine.transition,
              RewindWord.transition] at htransition
          simp [Update.Kernel.machine,
            Update.Kernel.transition, rightNonemptyConfig,
            TuringMachine.PhaseEmbedding.liftConfig,
            hactive, htransition]

theorem rightNonempty_run_of_some {stateCount : Nat}
    (selected : Selected stateCount)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      Update.RightNonempty.FullMachine.Control}
    (hrun :
      (Update.RightNonempty.FullMachine.machine
        selected.write).runConfigExact? steps source = some target) :
    (Update.Kernel.machine selected).runConfigExact? steps
        (rightNonemptyConfig source) = some (rightNonemptyConfig target) := by
  apply
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      Update.Kernel.Control.rightNonempty
  · exact rightNonempty_step_of_some selected
  · exact hrun

theorem runConfigExact_trans {stateCount : Nat}
    (selected : Selected stateCount)
    {first second : Nat}
    {a b c : TuringMachine.Configuration MachineCodeSymbol
      (KernelControl stateCount)}
    (hab : (Update.Kernel.machine selected).runConfigExact?
      first a = some b)
    (hbc : (Update.Kernel.machine selected).runConfigExact?
      second b = some c) :
    (Update.Kernel.machine selected).runConfigExact?
      (first + second) a = some c := by
  apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr
  exact TuringMachine.computesIn_trans
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hab)
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hbc)

private theorem write_read_eq_self (T : Tape MachineCodeSymbol) :
    Tape.write (Tape.read T) T = T := by
  cases T
  rfl

theorem probe_left_nonempty_handoff_run_exact {stateCount : Nat}
    (selected : Selected stateCount)
    (hdirection : selected.direction = Direction.left)
    (T : Tape MachineCodeSymbol) :
    (Update.Kernel.machine selected).runConfigExact? 2
        { state := Update.Kernel.Control.probe (.done false)
          tape := T } =
      some
        (leftNonemptyConfig
          { state := (Update.LeftNonempty.machine selected).start
            tape := CyclicDriverIntegration.roundTripTape T }) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    Update.Kernel.machine,
    Update.Kernel.transition, hdirection,
    leftNonemptyConfig,
    TuringMachine.PhaseEmbedding.liftConfig,
    CyclicDriverIntegration.roundTripTape, write_read_eq_self]

theorem probe_left_empty_handoff_run_exact {stateCount : Nat}
    (selected : Selected stateCount)
    (hdirection : selected.direction = Direction.left)
    (T : Tape MachineCodeSymbol) :
    (Update.Kernel.machine selected).runConfigExact? 2
        { state := Update.Kernel.Control.probe (.done true)
          tape := T } =
      some
        (fuelConfig Update.Kernel.FuelBranch.leftEmpty
          { state := FuelDecrementMachine.machine.start
            tape := CyclicDriverIntegration.roundTripTape T }) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    Update.Kernel.machine,
    Update.Kernel.transition, hdirection, fuelConfig,
    TuringMachine.PhaseEmbedding.liftConfig,
    CyclicDriverIntegration.roundTripTape, write_read_eq_self]

theorem probe_right_nonempty_handoff_run_exact {stateCount : Nat}
    (selected : Selected stateCount)
    (hdirection : selected.direction = Direction.right)
    (T : Tape MachineCodeSymbol) :
    (Update.Kernel.machine selected).runConfigExact? 2
        { state := Update.Kernel.Control.probe (.done false)
          tape := T } =
      some
        (fuelConfig Update.Kernel.FuelBranch.rightNonempty
          { state := FuelDecrementMachine.machine.start
            tape := CyclicDriverIntegration.roundTripTape T }) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    Update.Kernel.machine,
    Update.Kernel.transition, hdirection, fuelConfig,
    TuringMachine.PhaseEmbedding.liftConfig,
    CyclicDriverIntegration.roundTripTape, write_read_eq_self]

theorem probe_right_empty_handoff_run_exact {stateCount : Nat}
    (selected : Selected stateCount)
    (hdirection : selected.direction = Direction.right)
    (T : Tape MachineCodeSymbol) :
    (Update.Kernel.machine selected).runConfigExact? 2
        { state := Update.Kernel.Control.probe (.done true)
          tape := T } =
      some
        (fuelConfig Update.Kernel.FuelBranch.rightEmpty
          { state := FuelDecrementMachine.machine.start
            tape := CyclicDriverIntegration.roundTripTape T }) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    Update.Kernel.machine,
    Update.Kernel.transition, hdirection, fuelConfig,
    TuringMachine.PhaseEmbedding.liftConfig,
    CyclicDriverIntegration.roundTripTape, write_read_eq_self]

theorem fuel_left_empty_handoff_run_exact {stateCount : Nat}
    (selected : Selected stateCount) (T : Tape MachineCodeSymbol) :
    (Update.Kernel.machine selected).runConfigExact? 2
        { state := Update.Kernel.Control.fuel
            .leftEmpty FuelDecrementMachine.machine.halt
          tape := T } =
      some
        (leftEmptyConfig
          { state := (Update.LeftEmpty.machine selected.write).start
            tape := CyclicDriverIntegration.roundTripTape T }) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    Update.Kernel.machine,
    Update.Kernel.transition, leftEmptyConfig,
    TuringMachine.PhaseEmbedding.liftConfig,
    CyclicDriverIntegration.roundTripTape, write_read_eq_self]

theorem fuel_right_empty_handoff_run_exact {stateCount : Nat}
    (selected : Selected stateCount) (T : Tape MachineCodeSymbol) :
    (Update.Kernel.machine selected).runConfigExact? 2
        { state := Update.Kernel.Control.fuel
            .rightEmpty FuelDecrementMachine.machine.halt
          tape := T } =
      some
        (rightEmptyConfig
          { state := (Update.RightEmpty.machine selected.write).start
            tape := CyclicDriverIntegration.roundTripTape T }) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    Update.Kernel.machine,
    Update.Kernel.transition, rightEmptyConfig,
    TuringMachine.PhaseEmbedding.liftConfig,
    CyclicDriverIntegration.roundTripTape, write_read_eq_self]

theorem fuel_right_nonempty_handoff_run_exact {stateCount : Nat}
    (selected : Selected stateCount) (T : Tape MachineCodeSymbol) :
    (Update.Kernel.machine selected).runConfigExact? 2
        { state := Update.Kernel.Control.fuel
            .rightNonempty FuelDecrementMachine.machine.halt
          tape := T } =
      some
        (rightNonemptyConfig
          { state :=
              (Update.RightNonempty.FullMachine.machine
                selected.write).start
            tape := CyclicDriverIntegration.roundTripTape T }) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    Update.Kernel.machine,
    Update.Kernel.transition, rightNonemptyConfig,
    TuringMachine.PhaseEmbedding.liftConfig,
    CyclicDriverIntegration.roundTripTape, write_read_eq_self]

theorem left_nonempty_finish_handoff_run_exact {stateCount : Nat}
    (selected : Selected stateCount) (T : Tape MachineCodeSymbol) :
    (Update.Kernel.machine selected).runConfigExact? 2
        (leftNonemptyConfig
          { state := (Update.LeftNonempty.machine selected).halt
            tape := T }) =
      some
        { state := Update.Kernel.Control.done
          tape := CyclicDriverIntegration.roundTripTape T } := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    Update.Kernel.machine,
    Update.Kernel.transition, leftNonemptyConfig,
    TuringMachine.PhaseEmbedding.liftConfig,
    CyclicDriverIntegration.roundTripTape, write_read_eq_self]

theorem left_empty_finish_handoff_run_exact {stateCount : Nat}
    (selected : Selected stateCount) (T : Tape MachineCodeSymbol) :
    (Update.Kernel.machine selected).runConfigExact? 2
        (leftEmptyConfig
          { state := (Update.LeftEmpty.machine selected.write).halt
            tape := T }) =
      some
        { state := Update.Kernel.Control.done
          tape := CyclicDriverIntegration.roundTripTape T } := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    Update.Kernel.machine,
    Update.Kernel.transition, leftEmptyConfig,
    TuringMachine.PhaseEmbedding.liftConfig,
    CyclicDriverIntegration.roundTripTape, write_read_eq_self]

theorem right_empty_finish_handoff_run_exact {stateCount : Nat}
    (selected : Selected stateCount) (T : Tape MachineCodeSymbol) :
    (Update.Kernel.machine selected).runConfigExact? 2
        (rightEmptyConfig
          { state := (Update.RightEmpty.machine selected.write).halt
            tape := T }) =
      some
        { state := Update.Kernel.Control.done
          tape := CyclicDriverIntegration.roundTripTape T } := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    Update.Kernel.machine,
    Update.Kernel.transition, rightEmptyConfig,
    TuringMachine.PhaseEmbedding.liftConfig,
    CyclicDriverIntegration.roundTripTape, write_read_eq_self]

theorem right_nonempty_finish_handoff_run_exact {stateCount : Nat}
    (selected : Selected stateCount) (T : Tape MachineCodeSymbol) :
    (Update.Kernel.machine selected).runConfigExact? 2
        (rightNonemptyConfig
          { state :=
              (Update.RightNonempty.FullMachine.machine
                selected.write).halt
            tape := T }) =
      some
        { state := Update.Kernel.Control.done
          tape := CyclicDriverIntegration.roundTripTape T } := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    Update.Kernel.machine,
    Update.Kernel.transition, rightNonemptyConfig,
    TuringMachine.PhaseEmbedding.liftConfig,
    CyclicDriverIntegration.roundTripTape, write_read_eq_self]

end KernelLifts
end Update
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
