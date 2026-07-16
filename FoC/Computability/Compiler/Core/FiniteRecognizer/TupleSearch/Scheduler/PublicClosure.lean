import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.Cycle
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.InitializerRoutes
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.PublicBridge

set_option doc.verso true

/-!
**Finite tuple-scheduler assembly.** The unbounded and bounded public machines
differ only in their finite initializer.  Both permanently hand off to the
same concrete scheduler cycle.
-/

namespace FoC
namespace Computability
namespace FiniteRecognizer
namespace TupleSearch
namespace Scheduler.PublicClosure

open Languages

abbrev Frame := Scheduler.Layout.Frame

def unboundedSearcher {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount)) :=
  Scheduler.InitializerRoutes.unboundedMachine
    (Scheduler.Cycle.machine selected)

def boundedSearcher {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount)) :=
  Scheduler.InitializerRoutes.boundedMachine
    (Scheduler.Cycle.machine selected)

theorem unboundedSearcher_haltingTransitionsDisabled
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    TuringMachine.HaltingTransitionsDisabled
      (unboundedSearcher selected) := by
  exact Scheduler.InitializerDriver.machine_haltingTransitionsDisabled
    Scheduler.UnboundedInitializer.machine
    (Scheduler.Cycle.machine selected)
    (Scheduler.Cycle.machine_haltingTransitionsDisabled selected)

theorem boundedSearcher_haltingTransitionsDisabled
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    TuringMachine.HaltingTransitionsDisabled
      (boundedSearcher selected) := by
  exact Scheduler.InitializerDriver.machine_haltingTransitionsDisabled
    Scheduler.BoundedInitializer.machine
    (Scheduler.Cycle.machine selected)
    (Scheduler.Cycle.machine_haltingTransitionsDisabled selected)

theorem driverPhase_success
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    [DecidableEq initializerState]
    (represents : Frame ->
      TuringMachine.Configuration MachineCodeSymbol
        (Scheduler.Cycle.Control selected) -> Prop)
    (hsuccess : forall frame config,
      represents frame config ->
        Scheduler.Reachability.CandidateSucceeds selected frame ->
          TuringMachine.HaltsFrom
            (Scheduler.Cycle.machine selected) config)
    (frame : Frame)
    (config : TuringMachine.Configuration MachineCodeSymbol
      (Scheduler.InitializerDriver.Control initializerState
        (Scheduler.Cycle.Control selected)))
    (hrep :
      @Scheduler.InitializerRoutes.DriverPhaseRepresents
        (Scheduler.Cycle.Control selected) initializerState
        represents frame config)
    (hcandidate :
      Scheduler.Reachability.CandidateSucceeds selected frame) :
    TuringMachine.HaltsFrom
      (Scheduler.InitializerDriver.machine initializer
        (Scheduler.Cycle.machine selected)) config := by
  rcases hrep with ⟨driverConfig, rfl, hdriver⟩
  rcases hsuccess frame driverConfig hdriver hcandidate with
    ⟨finalConfig, hrun, hhalt⟩
  rcases TuringMachine.computes_to_computesIn hrun with
    ⟨steps, hrunIn⟩
  refine ⟨Scheduler.InitializerDriver.driverConfig finalConfig, ?_, ?_⟩
  · exact TuringMachine.computesIn_to_computes
      (Scheduler.InitializerDriver.driver_computesIn_lift initializer
        (Scheduler.Cycle.machine selected) hrunIn)
  · change Scheduler.InitializerDriver.Control.driver
        finalConfig.state =
      Scheduler.InitializerDriver.Control.driver
        (Scheduler.Cycle.machine selected).halt
    exact congrArg Scheduler.InitializerDriver.Control.driver hhalt
  done

theorem driverPhase_failure
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    [DecidableEq initializerState]
    (represents : Frame ->
      TuringMachine.Configuration MachineCodeSymbol
        (Scheduler.Cycle.Control selected) -> Prop)
    (hfailure : forall frame config,
      represents frame config ->
        ¬ Scheduler.Reachability.CandidateSucceeds selected frame ->
          exists steps : Nat,
          exists nextConfig : TuringMachine.Configuration
            MachineCodeSymbol (Scheduler.Cycle.Control selected),
            0 < steps ∧
              TuringMachine.ComputesIn
                (Scheduler.Cycle.machine selected)
                steps config nextConfig ∧
              represents frame.advance nextConfig)
    (frame : Frame)
    (config : TuringMachine.Configuration MachineCodeSymbol
      (Scheduler.InitializerDriver.Control initializerState
        (Scheduler.Cycle.Control selected)))
    (hrep :
      @Scheduler.InitializerRoutes.DriverPhaseRepresents
        (Scheduler.Cycle.Control selected) initializerState
        represents frame config)
    (hcandidate :
      ¬ Scheduler.Reachability.CandidateSucceeds selected frame) :
    exists steps : Nat,
    exists nextConfig : TuringMachine.Configuration MachineCodeSymbol
      (Scheduler.InitializerDriver.Control initializerState
        (Scheduler.Cycle.Control selected)),
      0 < steps ∧
        TuringMachine.ComputesIn
          (Scheduler.InitializerDriver.machine initializer
            (Scheduler.Cycle.machine selected))
          steps config nextConfig ∧
        @Scheduler.InitializerRoutes.DriverPhaseRepresents
          (Scheduler.Cycle.Control selected) initializerState
          represents frame.advance nextConfig := by
  rcases hrep with ⟨driverConfig, rfl, hdriver⟩
  rcases hfailure frame driverConfig hdriver hcandidate with
    ⟨steps, nextDriverConfig, hpositive, hrun, hnext⟩
  refine ⟨steps,
    Scheduler.InitializerDriver.driverConfig nextDriverConfig,
    hpositive, ?_, ?_⟩
  · exact Scheduler.InitializerDriver.driver_computesIn_lift
      initializer (Scheduler.Cycle.machine selected) hrun
  · exact ⟨nextDriverConfig, rfl, hnext⟩
  done

theorem unboundedSpec_of_cycle_contracts
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (represents : Frame ->
      TuringMachine.Configuration MachineCodeSymbol
        (Scheduler.Cycle.Control selected) -> Prop)
    (hsuccess : forall frame config,
      represents frame config ->
        Scheduler.Reachability.CandidateSucceeds selected frame ->
          TuringMachine.HaltsFrom
            (Scheduler.Cycle.machine selected) config)
    (hfailure : forall frame config,
      represents frame config ->
        ¬ Scheduler.Reachability.CandidateSucceeds selected frame ->
          exists steps : Nat,
          exists nextConfig : TuringMachine.Configuration
            MachineCodeSymbol (Scheduler.Cycle.Control selected),
            0 < steps ∧
              TuringMachine.ComputesIn
                (Scheduler.Cycle.machine selected)
                steps config nextConfig ∧
              represents frame.advance nextConfig)
    (hstart : forall (input : Word MachineCodeSymbol)
        (tape : Tape MachineCodeSymbol),
      Tape.Equiv
          (Tape.input
            (Scheduler.SplitLayout.encode
              (Scheduler.Reachability.initialFrame
                .unbounded input))) tape ->
        represents
          (Scheduler.Reachability.initialFrame .unbounded input)
          { state := (Scheduler.Cycle.machine selected).start
            tape := tape }) :
    GeneratedUnboundedHiddenFuelPairSpec
      (unboundedSearcher selected) selected := by
  intro input
  rcases
      Scheduler.InitializerRoutes.unbounded_initialization_computesIn
        (Scheduler.Cycle.machine selected) input with
    ⟨initialSteps, endpointTape, hinitial, htape⟩
  let driverConfig : TuringMachine.Configuration MachineCodeSymbol
      (Scheduler.Cycle.Control selected) :=
    { state := (Scheduler.Cycle.machine selected).start
      tape := Scheduler.InitializerDriver.roundTripTape endpointTape }
  let cycleConfig :=
    Scheduler.InitializerRoutes.unboundedCycleConfig
      (Scheduler.Cycle.machine selected)
      (Scheduler.InitializerDriver.roundTripTape endpointTape)
  have hcycle :
      Scheduler.InitializerRoutes.UnboundedDriverPhaseRepresents
        represents
        (Scheduler.Reachability.initialFrame .unbounded input)
        cycleConfig := by
    exact ⟨driverConfig, rfl,
      hstart input
        (Scheduler.InitializerDriver.roundTripTape endpointTape) htape⟩
  exact Scheduler.PublicBridge.unbounded_spec_of_rel_cycle
    selected (unboundedSearcher selected)
    (Scheduler.InitializerRoutes.UnboundedDriverPhaseRepresents
      represents)
    (unboundedSearcher_haltingTransitionsDisabled selected)
    (driverPhase_success selected
      Scheduler.UnboundedInitializer.machine represents hsuccess)
    (driverPhase_failure selected
      Scheduler.UnboundedInitializer.machine represents hfailure)
    input initialSteps cycleConfig
    (by simpa [unboundedSearcher] using hinitial) hcycle
  done

theorem boundedSpec_of_cycle_contracts
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (represents : Frame ->
      TuringMachine.Configuration MachineCodeSymbol
        (Scheduler.Cycle.Control selected) -> Prop)
    (hsuccess : forall frame config,
      represents frame config ->
        Scheduler.Reachability.CandidateSucceeds selected frame ->
          TuringMachine.HaltsFrom
            (Scheduler.Cycle.machine selected) config)
    (hfailure : forall frame config,
      represents frame config ->
        ¬ Scheduler.Reachability.CandidateSucceeds selected frame ->
          exists steps : Nat,
          exists nextConfig : TuringMachine.Configuration
            MachineCodeSymbol (Scheduler.Cycle.Control selected),
            0 < steps ∧
              TuringMachine.ComputesIn
                (Scheduler.Cycle.machine selected)
                steps config nextConfig ∧
              represents frame.advance nextConfig)
    (hstart : forall (input : Word MachineCodeSymbol) (budget : Nat)
        (tape : Tape MachineCodeSymbol),
      Tape.Equiv
          (Tape.input
            (Scheduler.SplitLayout.encode
              (Scheduler.Reachability.initialFrame
                (.bounded budget) input))) tape ->
        represents
          (Scheduler.Reachability.initialFrame
            (.bounded budget) input)
          { state := (Scheduler.Cycle.machine selected).start
            tape := tape }) :
    GeneratedBoundedHiddenFuelPairSpec
      (boundedSearcher selected) selected := by
  intro input budget
  rcases
      Scheduler.InitializerRoutes.bounded_initialization_computesIn
        (Scheduler.Cycle.machine selected) input budget with
    ⟨initialSteps, endpointTape, hinitial, htape, _hvalid⟩
  let driverConfig : TuringMachine.Configuration MachineCodeSymbol
      (Scheduler.Cycle.Control selected) :=
    { state := (Scheduler.Cycle.machine selected).start
      tape := Scheduler.InitializerDriver.roundTripTape endpointTape }
  let cycleConfig :=
    Scheduler.InitializerRoutes.boundedCycleConfig
      (Scheduler.Cycle.machine selected)
      (Scheduler.InitializerDriver.roundTripTape endpointTape)
  have hcycle :
      Scheduler.InitializerRoutes.BoundedDriverPhaseRepresents
        represents
        (Scheduler.Reachability.initialFrame
          (.bounded budget) input)
        cycleConfig := by
    exact ⟨driverConfig, rfl,
      hstart input budget
        (Scheduler.InitializerDriver.roundTripTape endpointTape) htape⟩
  exact Scheduler.PublicBridge.bounded_spec_of_rel_cycle
    selected (boundedSearcher selected)
    (Scheduler.InitializerRoutes.BoundedDriverPhaseRepresents
      represents)
    (boundedSearcher_haltingTransitionsDisabled selected)
    (driverPhase_success selected
      Scheduler.BoundedInitializer.machine represents hsuccess)
    (driverPhase_failure selected
      Scheduler.BoundedInitializer.machine represents hfailure)
    input budget initialSteps cycleConfig
    (by simpa [boundedSearcher] using hinitial) hcycle
  done

end Scheduler.PublicClosure
end TupleSearch
end FiniteRecognizer
end Computability
end FoC
