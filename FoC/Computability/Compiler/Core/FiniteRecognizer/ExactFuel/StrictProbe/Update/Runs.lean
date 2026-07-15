import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Update.Kernel
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Update.KernelLifts
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Update.FuelPrefix
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Update.LeftKernel
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Update.SemanticShapes
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Update.LeftEmpty
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Update.LeftNonempty
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Update.RightEmpty
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Update.RightNonempty
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Dispatch.NeighborProbe
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Dispatch.SerializedHead
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Driver.Induction
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Driver.CyclicMachine
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Driver.Witnesses
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseEmbedding

set_option doc.verso true

/-!
# Selected-update runs

Exact neighbor probing, branch witnesses, representation transport, and the
final relational run theorem for the production selected-update kernel.
-/

namespace FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.Update.Runs

open Languages
open SerializedFieldComposer

namespace ProbeWitness

/-- Run the neighbor-emptiness probe directly from the selected update-prefix
tape.  The dispatch payload affects the physical padding but not the protected
pre-fuel frame inspected by the probe. -/
theorem run_from_selectedPrefix {stateCount : Nat}
    (callerData : Word MachineCodeSymbol) (fuel : Nat)
    (F : CarriedStateFrame.LoopFrame stateCount)
    (write : Option MachineCodeSymbol) (direction : Direction)
    (nextState : Fin stateCount) :
    let L := (CarriedStateFrame.withFuel (fuel + 1) F).physicalFrame
    exists steps endpoint,
      (Dispatch.NeighborProbe.machine direction).runConfigExact? steps
          { state :=
              (Dispatch.NeighborProbe.machine direction).start
            tape := Update.LeftKernel.selectedPrefixTape
              callerData fuel F write direction nextState } =
        some endpoint ∧
      endpoint.state =
        Dispatch.NeighborProbe.Control.done
          (Dispatch.NeighborProbe.expected direction L) ∧
      Tape.Equiv
        (Tape.input (Frame.protectedWord L callerData)) endpoint.tape := by
  let L := (CarriedStateFrame.withFuel (fuel + 1) F).physicalFrame
  have hsource :=
    Update.LeftKernel.selectedPrefixTape_equiv_input
      callerData fuel F write direction nextState
  rcases Dispatch.NeighborProbe.run_from_equiv
      direction L callerData
      (Update.LeftKernel.selectedPrefixTape
        callerData fuel F write direction nextState)
      (by simpa [L] using hsource) with
    ⟨endpoint, hrun, hstate, htape⟩
  exact ⟨Dispatch.NeighborProbe.runSteps direction L,
    endpoint, hrun, hstate, htape⟩


end ProbeWitness

namespace Representation

theorem withFuel_afterSelected_physicalFrame {stateCount : Nat}
    (fuel : Nat) (F : CarriedStateFrame.LoopFrame stateCount)
    (write : Option MachineCodeSymbol) (direction : Direction)
    (nextState : Fin stateCount) :
    (CarriedStateFrame.withFuel fuel
      (CarriedStateFrame.afterSelected
        fuel write direction nextState F)).physicalFrame =
      (CarriedStateFrame.afterSelected
        fuel write direction nextState F).physicalFrame := by
  cases F with
  | mk carried physical =>
      cases physical with
      | mk layoutFuel state left head right =>
          cases direction with
          | left => cases left <;> rfl
          | right => cases right <;> rfl

theorem represents_roundTrip_of_endpoint_equiv {stateCount : Nat}
    (callerData : Word MachineCodeSymbol)
    (fuel : Nat) (F : CarriedStateFrame.LoopFrame stateCount)
    (write : Option MachineCodeSymbol) (direction : Direction)
    (nextState : Fin stateCount) (endpointTape : Tape MachineCodeSymbol)
    (hendpoint :
      Tape.Equiv
        (Tape.input
          (Frame.protectedWord
            (CarriedStateFrame.afterSelected
              fuel write direction nextState F).physicalFrame
            callerData))
        endpointTape) :
    RelationalDriverInduction.Represents callerData fuel
      (CarriedStateFrame.afterSelected
        fuel write direction nextState F)
      (CyclicDriverIntegration.roundTripTape endpointTape) := by
  unfold RelationalDriverInduction.Represents
  rw [withFuel_afterSelected_physicalFrame]
  exact Tape.Equiv.trans
    (by
      simpa [CyclicDriverIntegration.roundTripTape] using
        (Machine.moveLeft_moveRight_equiv_self endpointTape))
    (Tape.Equiv.symm hendpoint)


end Representation

namespace Branches

theorem emptyLeft_run_from_equiv_represents {stateCount : Nat}
    (callerData : Word MachineCodeSymbol) (fuel : Nat)
    (F : CarriedStateFrame.LoopFrame stateCount)
    (write : Option MachineCodeSymbol) (nextState : Fin stateCount)
    (hleft : F.physicalFrame.left = [])
    (T : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input
        (Frame.protectedWord
          (FuelDecrementMachine.withFuel fuel F.physicalFrame) callerData))
      T) :
    exists steps endpoint,
      (Update.LeftEmpty.machine write).runConfigExact? steps
          { state := (Update.LeftEmpty.machine write).start
            tape := T } = some endpoint ∧
      endpoint.state = (Update.LeftEmpty.machine write).halt ∧
      RelationalDriverInduction.Represents callerData fuel
        (CarriedStateFrame.afterSelected fuel write Direction.left
          nextState F)
        (CyclicDriverIntegration.roundTripTape endpoint.tape) := by
  let target := FuelDecrementMachine.withFuel fuel F.physicalFrame
  have htargetLeft : target.left = [] := by
    simpa [target, FuelDecrementMachine.withFuel] using hleft
  rcases Update.LeftEmpty.run_from_equiv
      target write callerData htargetLeft T
      (by simpa [target] using hsource) with
    ⟨steps, endpoint, hrun, hstate, htape⟩
  have hshape :
      MoveLeftEmpty.reshapedLayout target write =
        (CarriedStateFrame.afterSelected fuel write Direction.left
          nextState F).physicalFrame := by
    simpa [target] using
      Update.SemanticShapes.emptyLeft_target_eq_afterSelected
        fuel F write nextState hleft
  have hcanonical :
      Tape.Equiv
        (Tape.input
          (Frame.protectedWord
            (CarriedStateFrame.afterSelected fuel write Direction.left
              nextState F).physicalFrame callerData))
        endpoint.tape := by
    rw [← hshape]
    exact htape
  exact ⟨steps, endpoint, hrun, hstate,
    Representation.represents_roundTrip_of_endpoint_equiv
        callerData fuel F write Direction.left nextState endpoint.tape
        hcanonical⟩

theorem nonemptyLeft_run_from_selectedPrefix_equiv_represents
    {stateCount : Nat}
    (callerData : Word MachineCodeSymbol) (fuel : Nat)
    (F : CarriedStateFrame.LoopFrame stateCount)
    (write : Option MachineCodeSymbol) (nextState : Fin stateCount)
    (nextHead : Option MachineCodeSymbol)
    (remainingLeft : List (Option MachineCodeSymbol))
    (hleft : F.physicalFrame.left = nextHead :: remainingLeft)
    (T : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Update.LeftKernel.selectedPrefixTape
        callerData fuel F write Direction.left nextState) T) :
    let selected := Update.LeftKernel.selectedPayload
      write Direction.left nextState
    exists endpoint,
      (Update.LeftNonempty.machine selected).runConfigExact?
          (Update.LeftNonempty.runSteps
            fuel F write nextHead remainingLeft callerData)
          { state :=
              (Update.LeftNonempty.machine selected).start
            tape := T } = some endpoint ∧
      endpoint.state =
        (Update.LeftNonempty.machine selected).halt ∧
      RelationalDriverInduction.Represents callerData fuel
        (CarriedStateFrame.afterSelected fuel write Direction.left
          nextState F)
        (CyclicDriverIntegration.roundTripTape endpoint.tape) := by
  let selected := Update.LeftKernel.selectedPayload
    write Direction.left nextState
  rcases
      Update.LeftNonempty.run_from_selectedPrefix_equiv
        callerData fuel F write nextState nextHead remainingLeft hleft
        T hsource with
    ⟨endpoint, hrun, hstate, htape⟩
  exact ⟨endpoint, hrun, hstate,
    Representation.represents_roundTrip_of_endpoint_equiv
        callerData fuel F write Direction.left nextState endpoint.tape htape⟩

theorem emptyRight_run_from_equiv_represents {stateCount : Nat}
    (callerData : Word MachineCodeSymbol) (fuel : Nat)
    (F : CarriedStateFrame.LoopFrame stateCount)
    (write : Option MachineCodeSymbol) (nextState : Fin stateCount)
    (hright : F.physicalFrame.right = [])
    (T : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input
        (Frame.protectedWord
          (FuelDecrementMachine.withFuel fuel F.physicalFrame) callerData))
      T) :
    exists steps endpoint,
      (Update.RightEmpty.machine write).runConfigExact? steps
          { state := (Update.RightEmpty.machine write).start
            tape := T } = some endpoint ∧
      endpoint.state = Update.RightEmpty.Control.done ∧
      RelationalDriverInduction.Represents callerData fuel
        (CarriedStateFrame.afterSelected fuel write Direction.right
          nextState F)
        (CyclicDriverIntegration.roundTripTape endpoint.tape) := by
  let target := FuelDecrementMachine.withFuel fuel F.physicalFrame
  have htargetRight : target.right = [] := by
    simpa [target, FuelDecrementMachine.withFuel] using hright
  rcases Update.RightEmpty.run_from_equiv
      target write callerData htargetRight T
      (by simpa [target] using hsource) with
    ⟨steps, endpoint, hrun, hstate, htape⟩
  have hshape :
      MoveRightEmpty.reshapedLayout target write =
        (CarriedStateFrame.afterSelected fuel write Direction.right
          nextState F).physicalFrame := by
    simpa [target] using
      Update.SemanticShapes.emptyRight_target_eq_afterSelected
        fuel F write nextState hright
  have hcanonical :
      Tape.Equiv
        (Tape.input
          (Frame.protectedWord
            (CarriedStateFrame.afterSelected fuel write Direction.right
              nextState F).physicalFrame callerData))
        endpoint.tape := by
    rw [← hshape]
    exact htape
  exact ⟨steps, endpoint, hrun, hstate,
    Representation.represents_roundTrip_of_endpoint_equiv
        callerData fuel F write Direction.right nextState endpoint.tape
        hcanonical⟩

theorem nonemptyRight_run_from_equiv_represents {stateCount : Nat}
    (callerData : Word MachineCodeSymbol) (fuel : Nat)
    (F : CarriedStateFrame.LoopFrame stateCount)
    (write : Option MachineCodeSymbol) (nextState : Fin stateCount)
    (nextHead : Option MachineCodeSymbol)
    (remainingRight : List (Option MachineCodeSymbol))
    (hright : F.physicalFrame.right = nextHead :: remainingRight)
    (T : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input
        (Frame.protectedWord
          (FuelDecrementMachine.withFuel fuel F.physicalFrame) callerData))
      T) :
    exists steps endpoint,
      (Update.RightNonempty.FullMachine.machine write).runConfigExact?
          steps
          { state :=
              (Update.RightNonempty.FullMachine.machine write).start
            tape := T } = some endpoint ∧
      endpoint.state =
        Update.RightNonempty.FullMachine.prependEmbed
          (Update.RightNonempty.LeftPrependMachine.machine
            write).halt ∧
      RelationalDriverInduction.Represents callerData fuel
        (CarriedStateFrame.afterSelected fuel write Direction.right
          nextState F)
        (CyclicDriverIntegration.roundTripTape endpoint.tape) := by
  let target := FuelDecrementMachine.withFuel fuel F.physicalFrame
  have htargetRight : target.right = nextHead :: remainingRight := by
    simpa [target, FuelDecrementMachine.withFuel] using hright
  rcases Update.RightNonempty.run_from_equiv
      target write nextHead remainingRight callerData htargetRight T
      (by simpa [target] using hsource) with
    ⟨steps, endpoint, hrun, hstate, htape⟩
  have hbranchShape :
      MoveRightNonempty.reshapedLayout
          target write nextHead remainingRight =
        HeadActionShape.moveRightTarget
          target.fuel write target.state target :=
    MoveRightNonempty.reshapedLayout_eq_moveRightTarget
      target write nextHead remainingRight htargetRight
  have hsemanticShape :
      MoveRightNonempty.reshapedLayout
          target write nextHead remainingRight =
        (CarriedStateFrame.afterSelected fuel write Direction.right
          nextState F).physicalFrame := by
    simpa [target] using
      Update.SemanticShapes.nonemptyRight_target_eq_afterSelected
        fuel F write nextState nextHead remainingRight hright
  have hcanonical :
      Tape.Equiv
        (Tape.input
          (Frame.protectedWord
            (CarriedStateFrame.afterSelected fuel write Direction.right
              nextState F).physicalFrame callerData))
        endpoint.tape := by
    rw [← hsemanticShape, hbranchShape]
    exact htape
  exact ⟨steps, endpoint, hrun, hstate,
    Representation.represents_roundTrip_of_endpoint_equiv
      callerData fuel F write Direction.right nextState endpoint.tape
      hcanonical⟩


end Branches

private theorem roundTrip_equiv_self (T : Tape MachineCodeSymbol) :
    Tape.Equiv (CyclicDriverIntegration.roundTripTape T) T := by
  simpa [CyclicDriverIntegration.roundTripTape] using
    Machine.moveLeft_moveRight_equiv_self T

private theorem self_equiv_roundTrip (T : Tape MachineCodeSymbol) :
    Tape.Equiv T (CyclicDriverIntegration.roundTripTape T) :=
  Tape.Equiv.symm (roundTrip_equiv_self T)

private theorem represents_double_roundTrip {stateCount : Nat}
    {callerData : Word MachineCodeSymbol} {fuel : Nat}
    {F : CarriedStateFrame.LoopFrame stateCount}
    (T : Tape MachineCodeSymbol)
    (hrep : RelationalDriverInduction.Represents
      callerData fuel F (CyclicDriverIntegration.roundTripTape T)) :
    RelationalDriverInduction.Represents callerData fuel F
      (CyclicDriverIntegration.roundTripTape
        (CyclicDriverIntegration.roundTripTape T)) :=
  RelationalDriverInduction.represents_of_equiv
    (roundTrip_equiv_self
      (CyclicDriverIntegration.roundTripTape T)) hrep

private theorem kernel_machine_eq {stateCount : Nat}
    (selected : Update.Kernel.Selected stateCount) :
    (Update.Kernel.kernel stateCount).machine selected =
      Update.Kernel.machine selected := by
  rfl

private theorem selectedPayload_eq_driver {stateCount : Nat}
    (write : Option MachineCodeSymbol) (direction : Direction)
    (nextState : Fin stateCount) :
    Update.LeftKernel.selectedPayload write direction nextState =
      CyclicDriverWitnesses.selectedPayload write direction nextState := by
  rfl

private theorem selectedPrefixTape_eq_driver {stateCount : Nat}
    (callerData : Word MachineCodeSymbol) (fuel : Nat)
    (F : CarriedStateFrame.LoopFrame stateCount)
    (write : Option MachineCodeSymbol) (direction : Direction)
    (nextState : Fin stateCount) :
    Update.LeftKernel.selectedPrefixTape
        callerData fuel F write direction nextState =
      CyclicDriverWitnesses.selectedPrefixTape
        callerData fuel F write direction nextState := by
  rfl

private theorem probe_run {stateCount : Nat}
    (callerData : Word MachineCodeSymbol) (fuel : Nat)
    (F : CarriedStateFrame.LoopFrame stateCount)
    (write : Option MachineCodeSymbol) (direction : Direction)
    (nextState : Fin stateCount) :
    let selected := Update.LeftKernel.selectedPayload
      write direction nextState
    let L := (CarriedStateFrame.withFuel (fuel + 1) F).physicalFrame
    exists steps endpoint,
      (Update.Kernel.machine selected).runConfigExact? steps
          { state := (Update.Kernel.machine selected).start
            tape := Update.LeftKernel.selectedPrefixTape
              callerData fuel F write direction nextState } =
        some (Update.KernelLifts.probeConfig endpoint) ∧
      endpoint.state = Dispatch.NeighborProbe.Control.done
        (Dispatch.NeighborProbe.expected direction L) ∧
      Tape.Equiv
        (Tape.input (Frame.protectedWord L callerData)) endpoint.tape := by
  let selected := Update.LeftKernel.selectedPayload
    write direction nextState
  let L := (CarriedStateFrame.withFuel (fuel + 1) F).physicalFrame
  rcases ProbeWitness.run_from_selectedPrefix
      callerData fuel F write direction nextState with
    ⟨steps, endpoint, hrun, hstate, htape⟩
  refine ⟨steps, endpoint, ?_, hstate, htape⟩
  simpa [selected, Update.LeftKernel.selectedPayload,
    Update.Kernel.machine,
    Update.KernelLifts.probeConfig,
    TuringMachine.PhaseEmbedding.liftConfig] using
      Update.KernelLifts.probe_run_of_some selected hrun

private theorem left_nonempty_run {stateCount : Nat}
    (callerData : Word MachineCodeSymbol) (fuel : Nat)
    (F : CarriedStateFrame.LoopFrame stateCount)
    (write : Option MachineCodeSymbol) (nextState : Fin stateCount)
    (nextHead : Option MachineCodeSymbol)
    (remainingLeft : List (Option MachineCodeSymbol))
    (hleft : F.physicalFrame.left = nextHead :: remainingLeft) :
    let selected := Update.LeftKernel.selectedPayload
      write Direction.left nextState
    exists steps targetTape,
      (Update.Kernel.machine selected).runConfigExact? steps
          { state := (Update.Kernel.machine selected).start
            tape := Update.LeftKernel.selectedPrefixTape
              callerData fuel F write Direction.left nextState } =
        some { state := Update.Kernel.Control.done
               tape := targetTape } ∧
      RelationalDriverInduction.Represents callerData fuel
        (CarriedStateFrame.afterSelected fuel write Direction.left nextState F)
        (CyclicDriverIntegration.roundTripTape targetTape) := by
  let selected := Update.LeftKernel.selectedPayload
    write Direction.left nextState
  let L := (CarriedStateFrame.withFuel (fuel + 1) F).physicalFrame
  rcases probe_run callerData fuel F write Direction.left nextState with
    ⟨probeSteps, ⟨probeState, probeTape⟩,
      hprobeRun, hprobeState, hprobeTape⟩
  have hexpected :
      Dispatch.NeighborProbe.expected Direction.left L = false := by
    simp [Dispatch.NeighborProbe.expected, L,
      CarriedStateFrame.withFuel, FuelDecrementMachine.withFuel, hleft]
  change probeState = Dispatch.NeighborProbe.Control.done
    (Dispatch.NeighborProbe.expected Direction.left L) at hprobeState
  rw [hexpected] at hprobeState
  subst probeState
  have hprobeRun' :
      (Update.Kernel.machine selected).runConfigExact?
          probeSteps
          { state := (Update.Kernel.machine selected).start
            tape := Update.LeftKernel.selectedPrefixTape
              callerData fuel F write Direction.left nextState } =
        some
          { state := Update.Kernel.Control.probe (.done false)
            tape := probeTape } := by
    simpa [Update.KernelLifts.probeConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using hprobeRun
  have hprobeHandoff :=
    Update.KernelLifts.probe_left_nonempty_handoff_run_exact
      selected (by rfl) probeTape
  have hselectedPrefix :=
    Update.LeftKernel.selectedPrefixTape_equiv_input
      callerData fuel F write Direction.left nextState
  have hbranchSource :
      Tape.Equiv
        (Update.LeftKernel.selectedPrefixTape
          callerData fuel F write Direction.left nextState)
        (CyclicDriverIntegration.roundTripTape probeTape) :=
    Tape.Equiv.trans (Tape.Equiv.symm hselectedPrefix)
      (Tape.Equiv.trans hprobeTape (self_equiv_roundTrip probeTape))
  rcases
      Branches.nonemptyLeft_run_from_selectedPrefix_equiv_represents
          callerData fuel F write nextState nextHead remainingLeft hleft
          (CyclicDriverIntegration.roundTripTape probeTape)
          hbranchSource with
    ⟨⟨branchState, branchTape⟩, hbranchRun, hbranchState, hbranchRep⟩
  change branchState =
    (Update.LeftNonempty.machine selected).halt at hbranchState
  subst branchState
  have hbranchLift :=
    Update.KernelLifts.leftNonempty_run_of_some
      selected hbranchRun
  have hfinish :=
    Update.KernelLifts.left_nonempty_finish_handoff_run_exact
      selected branchTape
  have hthroughProbe :=
    Update.KernelLifts.runConfigExact_trans selected
      hprobeRun' hprobeHandoff
  have hthroughBranch :=
    Update.KernelLifts.runConfigExact_trans selected
      hthroughProbe hbranchLift
  have htotal :=
    Update.KernelLifts.runConfigExact_trans selected
      hthroughBranch hfinish
  exact ⟨_, CyclicDriverIntegration.roundTripTape branchTape,
    htotal, represents_double_roundTrip branchTape hbranchRep⟩

private theorem left_empty_run {stateCount : Nat}
    (callerData : Word MachineCodeSymbol) (fuel : Nat)
    (F : CarriedStateFrame.LoopFrame stateCount)
    (write : Option MachineCodeSymbol) (nextState : Fin stateCount)
    (hleft : F.physicalFrame.left = []) :
    let selected := Update.LeftKernel.selectedPayload
      write Direction.left nextState
    exists steps targetTape,
      (Update.Kernel.machine selected).runConfigExact? steps
          { state := (Update.Kernel.machine selected).start
            tape := Update.LeftKernel.selectedPrefixTape
              callerData fuel F write Direction.left nextState } =
        some { state := Update.Kernel.Control.done
               tape := targetTape } ∧
      RelationalDriverInduction.Represents callerData fuel
        (CarriedStateFrame.afterSelected fuel write Direction.left nextState F)
        (CyclicDriverIntegration.roundTripTape targetTape) := by
  let selected := Update.LeftKernel.selectedPayload
    write Direction.left nextState
  let L := (CarriedStateFrame.withFuel (fuel + 1) F).physicalFrame
  rcases probe_run callerData fuel F write Direction.left nextState with
    ⟨probeSteps, ⟨probeState, probeTape⟩,
      hprobeRun, hprobeState, hprobeTape⟩
  have hexpected :
      Dispatch.NeighborProbe.expected Direction.left L = true := by
    simp [Dispatch.NeighborProbe.expected, L,
      CarriedStateFrame.withFuel, FuelDecrementMachine.withFuel, hleft]
  change probeState = Dispatch.NeighborProbe.Control.done
    (Dispatch.NeighborProbe.expected Direction.left L) at hprobeState
  rw [hexpected] at hprobeState
  subst probeState
  have hprobeRun' :
      (Update.Kernel.machine selected).runConfigExact?
          probeSteps
          { state := (Update.Kernel.machine selected).start
            tape := Update.LeftKernel.selectedPrefixTape
              callerData fuel F write Direction.left nextState } =
        some
          { state := Update.Kernel.Control.probe (.done true)
            tape := probeTape } := by
    simpa [Update.KernelLifts.probeConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using hprobeRun
  have hprobeHandoff :=
    Update.KernelLifts.probe_left_empty_handoff_run_exact
      selected (by rfl) probeTape
  have hfuelSource : Tape.Equiv
      (Tape.input
        (Frame.protectedWord
          (FuelDecrementMachine.withFuel
            (fuel + 1) F.physicalFrame) callerData))
      (CyclicDriverIntegration.roundTripTape probeTape) := by
    exact Tape.Equiv.trans (by
      simpa [L, CarriedStateFrame.withFuel] using hprobeTape)
      (self_equiv_roundTrip probeTape)
  rcases Update.FuelPrefix.run_from_equiv
      fuel F.physicalFrame callerData
      (CyclicDriverIntegration.roundTripTape probeTape)
      hfuelSource with
    ⟨⟨fuelState, fuelTape⟩, hfuelRun, hfuelState, hfuelTape⟩
  change fuelState = FuelDecrementMachine.machine.halt at hfuelState
  subst fuelState
  have hfuelLift :=
    Update.KernelLifts.fuel_run_of_some selected
      Update.Kernel.FuelBranch.leftEmpty hfuelRun
  have hfuelHandoff :=
    Update.KernelLifts.fuel_left_empty_handoff_run_exact
      selected fuelTape
  have hbranchSource : Tape.Equiv
      (Tape.input
        (Frame.protectedWord
          (FuelDecrementMachine.withFuel fuel F.physicalFrame) callerData))
      (CyclicDriverIntegration.roundTripTape fuelTape) :=
    Tape.Equiv.trans hfuelTape (self_equiv_roundTrip fuelTape)
  rcases Branches.emptyLeft_run_from_equiv_represents
      callerData fuel F write nextState hleft
      (CyclicDriverIntegration.roundTripTape fuelTape)
      hbranchSource with
    ⟨branchSteps, ⟨branchState, branchTape⟩,
      hbranchRun, hbranchState, hbranchRep⟩
  change branchState =
    (Update.LeftEmpty.machine selected.write).halt at hbranchState
  subst branchState
  have hbranchLift :=
    Update.KernelLifts.leftEmpty_run_of_some selected hbranchRun
  have hfinish :=
    Update.KernelLifts.left_empty_finish_handoff_run_exact
      selected branchTape
  have h01 := Update.KernelLifts.runConfigExact_trans selected
    hprobeRun' hprobeHandoff
  have h02 := Update.KernelLifts.runConfigExact_trans selected
    h01 hfuelLift
  have h03 := Update.KernelLifts.runConfigExact_trans selected
    h02 hfuelHandoff
  have h04 := Update.KernelLifts.runConfigExact_trans selected
    h03 hbranchLift
  have htotal := Update.KernelLifts.runConfigExact_trans selected
    h04 hfinish
  exact ⟨_, CyclicDriverIntegration.roundTripTape branchTape,
    htotal, represents_double_roundTrip branchTape hbranchRep⟩

private theorem right_empty_run {stateCount : Nat}
    (callerData : Word MachineCodeSymbol) (fuel : Nat)
    (F : CarriedStateFrame.LoopFrame stateCount)
    (write : Option MachineCodeSymbol) (nextState : Fin stateCount)
    (hright : F.physicalFrame.right = []) :
    let selected := Update.LeftKernel.selectedPayload
      write Direction.right nextState
    exists steps targetTape,
      (Update.Kernel.machine selected).runConfigExact? steps
          { state := (Update.Kernel.machine selected).start
            tape := Update.LeftKernel.selectedPrefixTape
              callerData fuel F write Direction.right nextState } =
        some { state := Update.Kernel.Control.done
               tape := targetTape } ∧
      RelationalDriverInduction.Represents callerData fuel
        (CarriedStateFrame.afterSelected fuel write Direction.right nextState F)
        (CyclicDriverIntegration.roundTripTape targetTape) := by
  let selected := Update.LeftKernel.selectedPayload
    write Direction.right nextState
  let L := (CarriedStateFrame.withFuel (fuel + 1) F).physicalFrame
  rcases probe_run callerData fuel F write Direction.right nextState with
    ⟨probeSteps, ⟨probeState, probeTape⟩,
      hprobeRun, hprobeState, hprobeTape⟩
  have hexpected :
      Dispatch.NeighborProbe.expected Direction.right L = true := by
    simp [Dispatch.NeighborProbe.expected, L,
      CarriedStateFrame.withFuel, FuelDecrementMachine.withFuel, hright]
  change probeState = Dispatch.NeighborProbe.Control.done
    (Dispatch.NeighborProbe.expected Direction.right L) at hprobeState
  rw [hexpected] at hprobeState
  subst probeState
  have hprobeRun' :
      (Update.Kernel.machine selected).runConfigExact?
          probeSteps
          { state := (Update.Kernel.machine selected).start
            tape := Update.LeftKernel.selectedPrefixTape
              callerData fuel F write Direction.right nextState } =
        some
          { state := Update.Kernel.Control.probe (.done true)
            tape := probeTape } := by
    simpa [Update.KernelLifts.probeConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using hprobeRun
  have hprobeHandoff :=
    Update.KernelLifts.probe_right_empty_handoff_run_exact
      selected (by rfl) probeTape
  have hfuelSource : Tape.Equiv
      (Tape.input
        (Frame.protectedWord
          (FuelDecrementMachine.withFuel
            (fuel + 1) F.physicalFrame) callerData))
      (CyclicDriverIntegration.roundTripTape probeTape) := by
    exact Tape.Equiv.trans (by
      simpa [L, CarriedStateFrame.withFuel] using hprobeTape)
      (self_equiv_roundTrip probeTape)
  rcases Update.FuelPrefix.run_from_equiv
      fuel F.physicalFrame callerData
      (CyclicDriverIntegration.roundTripTape probeTape)
      hfuelSource with
    ⟨⟨fuelState, fuelTape⟩, hfuelRun, hfuelState, hfuelTape⟩
  change fuelState = FuelDecrementMachine.machine.halt at hfuelState
  subst fuelState
  have hfuelLift :=
    Update.KernelLifts.fuel_run_of_some selected
      Update.Kernel.FuelBranch.rightEmpty hfuelRun
  have hfuelHandoff :=
    Update.KernelLifts.fuel_right_empty_handoff_run_exact
      selected fuelTape
  have hbranchSource : Tape.Equiv
      (Tape.input
        (Frame.protectedWord
          (FuelDecrementMachine.withFuel fuel F.physicalFrame) callerData))
      (CyclicDriverIntegration.roundTripTape fuelTape) :=
    Tape.Equiv.trans hfuelTape (self_equiv_roundTrip fuelTape)
  rcases Branches.emptyRight_run_from_equiv_represents
      callerData fuel F write nextState hright
      (CyclicDriverIntegration.roundTripTape fuelTape)
      hbranchSource with
    ⟨branchSteps, ⟨branchState, branchTape⟩,
      hbranchRun, hbranchState, hbranchRep⟩
  change branchState =
    (Update.RightEmpty.machine selected.write).halt at hbranchState
  subst branchState
  have hbranchLift :=
    Update.KernelLifts.rightEmpty_run_of_some selected hbranchRun
  have hfinish :=
    Update.KernelLifts.right_empty_finish_handoff_run_exact
      selected branchTape
  have h01 := Update.KernelLifts.runConfigExact_trans selected
    hprobeRun' hprobeHandoff
  have h02 := Update.KernelLifts.runConfigExact_trans selected
    h01 hfuelLift
  have h03 := Update.KernelLifts.runConfigExact_trans selected
    h02 hfuelHandoff
  have h04 := Update.KernelLifts.runConfigExact_trans selected
    h03 hbranchLift
  have htotal := Update.KernelLifts.runConfigExact_trans selected
    h04 hfinish
  exact ⟨_, CyclicDriverIntegration.roundTripTape branchTape,
    htotal, represents_double_roundTrip branchTape hbranchRep⟩

private theorem right_nonempty_run {stateCount : Nat}
    (callerData : Word MachineCodeSymbol) (fuel : Nat)
    (F : CarriedStateFrame.LoopFrame stateCount)
    (write : Option MachineCodeSymbol) (nextState : Fin stateCount)
    (nextHead : Option MachineCodeSymbol)
    (remainingRight : List (Option MachineCodeSymbol))
    (hright : F.physicalFrame.right = nextHead :: remainingRight) :
    let selected := Update.LeftKernel.selectedPayload
      write Direction.right nextState
    exists steps targetTape,
      (Update.Kernel.machine selected).runConfigExact? steps
          { state := (Update.Kernel.machine selected).start
            tape := Update.LeftKernel.selectedPrefixTape
              callerData fuel F write Direction.right nextState } =
        some { state := Update.Kernel.Control.done
               tape := targetTape } ∧
      RelationalDriverInduction.Represents callerData fuel
        (CarriedStateFrame.afterSelected fuel write Direction.right nextState F)
        (CyclicDriverIntegration.roundTripTape targetTape) := by
  let selected := Update.LeftKernel.selectedPayload
    write Direction.right nextState
  let L := (CarriedStateFrame.withFuel (fuel + 1) F).physicalFrame
  rcases probe_run callerData fuel F write Direction.right nextState with
    ⟨probeSteps, ⟨probeState, probeTape⟩,
      hprobeRun, hprobeState, hprobeTape⟩
  have hexpected :
      Dispatch.NeighborProbe.expected Direction.right L = false := by
    simp [Dispatch.NeighborProbe.expected, L,
      CarriedStateFrame.withFuel, FuelDecrementMachine.withFuel, hright]
  change probeState = Dispatch.NeighborProbe.Control.done
    (Dispatch.NeighborProbe.expected Direction.right L) at hprobeState
  rw [hexpected] at hprobeState
  subst probeState
  have hprobeRun' :
      (Update.Kernel.machine selected).runConfigExact?
          probeSteps
          { state := (Update.Kernel.machine selected).start
            tape := Update.LeftKernel.selectedPrefixTape
              callerData fuel F write Direction.right nextState } =
        some
          { state := Update.Kernel.Control.probe (.done false)
            tape := probeTape } := by
    simpa [Update.KernelLifts.probeConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using hprobeRun
  have hprobeHandoff :=
    Update.KernelLifts.probe_right_nonempty_handoff_run_exact
      selected (by rfl) probeTape
  have hfuelSource : Tape.Equiv
      (Tape.input
        (Frame.protectedWord
          (FuelDecrementMachine.withFuel
            (fuel + 1) F.physicalFrame) callerData))
      (CyclicDriverIntegration.roundTripTape probeTape) := by
    exact Tape.Equiv.trans (by
      simpa [L, CarriedStateFrame.withFuel] using hprobeTape)
      (self_equiv_roundTrip probeTape)
  rcases Update.FuelPrefix.run_from_equiv
      fuel F.physicalFrame callerData
      (CyclicDriverIntegration.roundTripTape probeTape)
      hfuelSource with
    ⟨⟨fuelState, fuelTape⟩, hfuelRun, hfuelState, hfuelTape⟩
  change fuelState = FuelDecrementMachine.machine.halt at hfuelState
  subst fuelState
  have hfuelLift :=
    Update.KernelLifts.fuel_run_of_some selected
      Update.Kernel.FuelBranch.rightNonempty hfuelRun
  have hfuelHandoff :=
    Update.KernelLifts.fuel_right_nonempty_handoff_run_exact
      selected fuelTape
  have hbranchSource : Tape.Equiv
      (Tape.input
        (Frame.protectedWord
          (FuelDecrementMachine.withFuel fuel F.physicalFrame) callerData))
      (CyclicDriverIntegration.roundTripTape fuelTape) :=
    Tape.Equiv.trans hfuelTape (self_equiv_roundTrip fuelTape)
  rcases
      Branches.nonemptyRight_run_from_equiv_represents
        callerData fuel F write nextState nextHead remainingRight hright
        (CyclicDriverIntegration.roundTripTape fuelTape)
        hbranchSource with
    ⟨branchSteps, ⟨branchState, branchTape⟩,
      hbranchRun, hbranchState, hbranchRep⟩
  change branchState =
    (Update.RightNonempty.FullMachine.machine
      selected.write).halt at hbranchState
  subst branchState
  have hbranchLift :=
    Update.KernelLifts.rightNonempty_run_of_some
      selected hbranchRun
  have hfinish :=
    Update.KernelLifts.right_nonempty_finish_handoff_run_exact
      selected branchTape
  have h01 := Update.KernelLifts.runConfigExact_trans selected
    hprobeRun' hprobeHandoff
  have h02 := Update.KernelLifts.runConfigExact_trans selected
    h01 hfuelLift
  have h03 := Update.KernelLifts.runConfigExact_trans selected
    h02 hfuelHandoff
  have h04 := Update.KernelLifts.runConfigExact_trans selected
    h03 hbranchLift
  have htotal := Update.KernelLifts.runConfigExact_trans selected
    h04 hfinish
  exact ⟨_, CyclicDriverIntegration.roundTripTape branchTape,
    htotal, represents_double_roundTrip branchTape hbranchRep⟩

/-- The concrete selected-update kernel realizes the relational update
obligation for every direction and physical neighbor shape. -/
theorem selectedUpdateRuns {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (callerData : Word MachineCodeSymbol) :
    CyclicDriverWitnesses.SelectedUpdateRuns M
      (Update.Kernel.kernel stateCount) callerData := by
  constructor
  intro fuel F write direction nextState _htransition
  cases direction with
  | left =>
      cases hleft : F.physicalFrame.left with
      | nil =>
          simpa [kernel_machine_eq, selectedPayload_eq_driver,
            selectedPrefixTape_eq_driver, Update.Kernel.kernel,
            Update.Kernel.machine,
            CyclicDriverIntegration.UpdateKernel.machine] using
              left_empty_run callerData fuel F write nextState hleft
      | cons nextHead remainingLeft =>
          simpa [kernel_machine_eq, selectedPayload_eq_driver,
            selectedPrefixTape_eq_driver, Update.Kernel.kernel,
            Update.Kernel.machine,
            CyclicDriverIntegration.UpdateKernel.machine] using
              left_nonempty_run callerData fuel F write nextState
                nextHead remainingLeft hleft
  | right =>
      cases hright : F.physicalFrame.right with
      | nil =>
          simpa [kernel_machine_eq, selectedPayload_eq_driver,
            selectedPrefixTape_eq_driver, Update.Kernel.kernel,
            Update.Kernel.machine,
            CyclicDriverIntegration.UpdateKernel.machine] using
              right_empty_run callerData fuel F write nextState hright
      | cons nextHead remainingRight =>
          simpa [kernel_machine_eq, selectedPayload_eq_driver,
            selectedPrefixTape_eq_driver, Update.Kernel.kernel,
            Update.Kernel.machine,
            CyclicDriverIntegration.UpdateKernel.machine] using
              right_nonempty_run callerData fuel F write nextState
                nextHead remainingRight hright


end FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.Update.Runs
