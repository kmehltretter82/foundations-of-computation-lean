import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.InitializerDriver
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.UnboundedInitializer
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.BoundedInitializer
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.Reachability

set_option doc.verso true

/-!
**Initializer routes.** These are the unbounded and bounded initializer/driver
instantiations for the public scheduler inputs.

The driver and its semantic frame relation remain arbitrary.  The relation
accepts the driver's start configuration on every tape equivalent to the
canonical split-layout encoding of the represented frame.
-/

namespace FoC
namespace Computability
namespace FiniteRecognizer
namespace TupleSearch
namespace Scheduler.InitializerRoutes

open Languages
open ExactFuel.StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer

abbrev Frame := Scheduler.Layout.Frame

abbrev UnboundedInitializerState :=
  Scheduler.UnboundedInitializer.LeftPrefixWriter.Control
    Scheduler.UnboundedInitializer.initialPrefix.reverse

abbrev BoundedInitializerState :=
  Scheduler.BoundedInitializer.Control

def AcceptsEquivalentFrames
    (driver : TuringMachine MachineCodeSymbol driverState)
    (represents : Frame ->
      TuringMachine.Configuration MachineCodeSymbol driverState -> Prop) :
    Prop :=
  forall (frame : Frame) (tape : Tape MachineCodeSymbol),
    Tape.Equiv
        (Tape.input (Scheduler.SplitLayout.encode frame)) tape ->
      represents frame { state := driver.start, tape := tape }

def DriverPhaseRepresents
    (represents : Frame ->
      TuringMachine.Configuration MachineCodeSymbol driverState -> Prop)
    (frame : Frame)
    (config : TuringMachine.Configuration MachineCodeSymbol
      (Scheduler.InitializerDriver.Control
        initializerState driverState)) : Prop :=
  exists driverInner :
      TuringMachine.Configuration MachineCodeSymbol driverState,
    config = Scheduler.InitializerDriver.driverConfig driverInner ∧
      represents frame driverInner

def unboundedMachine
    (driver : TuringMachine MachineCodeSymbol driverState) :=
  Scheduler.InitializerDriver.machine
    Scheduler.UnboundedInitializer.machine driver

def boundedMachine
    (driver : TuringMachine MachineCodeSymbol driverState) :=
  Scheduler.InitializerDriver.machine
    Scheduler.BoundedInitializer.machine driver

def unboundedCycleConfig
    (driver : TuringMachine MachineCodeSymbol driverState)
    (tape : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      (Scheduler.InitializerDriver.Control
        UnboundedInitializerState driverState) :=
  @Scheduler.InitializerDriver.driverConfig
    driverState UnboundedInitializerState
    { state := driver.start, tape := tape }

def boundedCycleConfig
    (driver : TuringMachine MachineCodeSymbol driverState)
    (tape : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      (Scheduler.InitializerDriver.Control
        BoundedInitializerState driverState) :=
  @Scheduler.InitializerDriver.driverConfig
    driverState BoundedInitializerState
    { state := driver.start, tape := tape }

def UnboundedDriverPhaseRepresents
    (represents : Frame ->
      TuringMachine.Configuration MachineCodeSymbol driverState -> Prop) :
    Frame ->
      TuringMachine.Configuration MachineCodeSymbol
        (Scheduler.InitializerDriver.Control
          UnboundedInitializerState driverState) -> Prop :=
  @DriverPhaseRepresents driverState UnboundedInitializerState represents

def BoundedDriverPhaseRepresents
    (represents : Frame ->
      TuringMachine.Configuration MachineCodeSymbol driverState -> Prop) :
    Frame ->
      TuringMachine.Configuration MachineCodeSymbol
        (Scheduler.InitializerDriver.Control
          BoundedInitializerState driverState) -> Prop :=
  @DriverPhaseRepresents driverState BoundedInitializerState represents

theorem unbounded_initializer_haltingTransitionsDisabled :
    TuringMachine.HaltingTransitionsDisabled
      Scheduler.UnboundedInitializer.machine := by
  intro read
  rfl
  done

theorem bounded_initializer_haltingTransitionsDisabled :
    TuringMachine.HaltingTransitionsDisabled
      Scheduler.BoundedInitializer.machine := by
  intro read
  simp [Scheduler.BoundedInitializer.machine,
    Scheduler.BoundedInitializer.transition,
    InsertRestagedMachine.machine,
    InsertRestagedMachine.transition,
    RewindWord.transition]
  done

theorem unbounded_initialFrame_eq
    (input : Word MachineCodeSymbol) :
    Scheduler.UnboundedInitializer.initialFrame input =
      Scheduler.Reachability.initialFrame .unbounded input := by
  rfl

theorem bounded_initialFrame_eq
    (budget : Nat) (input : Word MachineCodeSymbol) :
    Scheduler.BoundedInitializer.initialFrame budget input =
      Scheduler.Reachability.initialFrame (.bounded budget) input := by
  rfl

theorem unbounded_initialization_computesIn
    (driver : TuringMachine MachineCodeSymbol driverState)
    (input : Word MachineCodeSymbol) :
    exists initialSteps : Nat,
    exists endpointTape : Tape MachineCodeSymbol,
      TuringMachine.ComputesIn (unboundedMachine driver) initialSteps
        (TuringMachine.initial (unboundedMachine driver) input)
        (unboundedCycleConfig driver
          (Scheduler.InitializerDriver.roundTripTape endpointTape)) ∧
      Tape.Equiv
        (Tape.input
          (Scheduler.SplitLayout.encode
            (Scheduler.Reachability.initialFrame
              .unbounded input)))
        (Scheduler.InitializerDriver.roundTripTape endpointTape) := by
  rcases Scheduler.UnboundedInitializer.initializes input with
    ⟨hinitializer, hendpoint⟩
  rcases Scheduler.InitializerDriver.initialization_computesIn_exists
      Scheduler.UnboundedInitializer.machine driver
      unbounded_initializer_haltingTransitionsDisabled
      input
      (Scheduler.UnboundedInitializer.targetConfig input).tape
      hinitializer with
    ⟨initialSteps, hcombined⟩
  refine ⟨initialSteps,
    (Scheduler.UnboundedInitializer.targetConfig input).tape,
    ?_, ?_⟩
  · simpa [unboundedMachine, unboundedCycleConfig] using hcombined
  · exact Tape.Equiv.trans
      (by
        rw [← unbounded_initialFrame_eq]
        exact Tape.Equiv.symm hendpoint)
      (Tape.Equiv.symm
        (Scheduler.InitializerDriver.roundTripTape_equiv
          (Scheduler.UnboundedInitializer.targetConfig input).tape))
  done

theorem bounded_initialization_computesIn
    (driver : TuringMachine MachineCodeSymbol driverState)
    (input : Word MachineCodeSymbol) (budget : Nat) :
    exists initialSteps : Nat,
    exists endpointTape : Tape MachineCodeSymbol,
      TuringMachine.ComputesIn (boundedMachine driver) initialSteps
        (TuringMachine.initial (boundedMachine driver)
          (GeneratedCode.stageCode input budget))
        (boundedCycleConfig driver
          (Scheduler.InitializerDriver.roundTripTape endpointTape)) ∧
      Tape.Equiv
        (Tape.input
          (Scheduler.SplitLayout.encode
            (Scheduler.Reachability.initialFrame
              (.bounded budget) input)))
        (Scheduler.InitializerDriver.roundTripTape endpointTape) ∧
      (Scheduler.Reachability.initialFrame
          (.bounded budget) input).cursor.Valid
        (Scheduler.Reachability.initialFrame
          (.bounded budget) input).geometry := by
  rcases
      Scheduler.BoundedInitializer.computes_stageCode_to_initialFrame
        budget input with
    ⟨endpointTape, hinitializer, hendpoint, hvalid⟩
  rcases Scheduler.InitializerDriver.initialization_computesIn_exists
      Scheduler.BoundedInitializer.machine driver
      bounded_initializer_haltingTransitionsDisabled
      (GeneratedCode.stageCode input budget) endpointTape
      (by
        simpa [TuringMachine.initial] using hinitializer) with
    ⟨initialSteps, hcombined⟩
  refine ⟨initialSteps, endpointTape, ?_, ?_, ?_⟩
  · simpa [boundedMachine, boundedCycleConfig] using hcombined
  · exact Tape.Equiv.trans
      (by
        rw [← bounded_initialFrame_eq]
        exact hendpoint)
      (Tape.Equiv.symm
        (Scheduler.InitializerDriver.roundTripTape_equiv endpointTape))
  · simpa [← bounded_initialFrame_eq] using hvalid
  done

theorem unbounded_public_prefix
    (driver : TuringMachine MachineCodeSymbol driverState)
    (represents : Frame ->
      TuringMachine.Configuration MachineCodeSymbol driverState -> Prop)
    (haccepts : AcceptsEquivalentFrames driver represents)
    (input : Word MachineCodeSymbol) :
    exists initialSteps : Nat,
    exists cycleConfig : TuringMachine.Configuration MachineCodeSymbol
      (Scheduler.InitializerDriver.Control
        UnboundedInitializerState driverState),
      TuringMachine.ComputesIn (unboundedMachine driver) initialSteps
        (TuringMachine.initial (unboundedMachine driver) input)
        cycleConfig ∧
      UnboundedDriverPhaseRepresents represents
        (Scheduler.Reachability.initialFrame .unbounded input)
        cycleConfig := by
  rcases unbounded_initialization_computesIn driver input with
    ⟨initialSteps, endpointTape, hrun, htape⟩
  let driverInner :
      TuringMachine.Configuration MachineCodeSymbol driverState :=
    { state := driver.start
      tape := Scheduler.InitializerDriver.roundTripTape endpointTape }
  let cycleConfig := unboundedCycleConfig driver
    (Scheduler.InitializerDriver.roundTripTape endpointTape)
  refine ⟨initialSteps, cycleConfig, ?_, ?_⟩
  · simpa [cycleConfig] using hrun
  · refine ⟨driverInner, ?_, ?_⟩
    · rfl
    · exact haccepts
        (Scheduler.Reachability.initialFrame .unbounded input)
        (Scheduler.InitializerDriver.roundTripTape endpointTape) htape
  done

theorem bounded_public_prefix
    (driver : TuringMachine MachineCodeSymbol driverState)
    (represents : Frame ->
      TuringMachine.Configuration MachineCodeSymbol driverState -> Prop)
    (haccepts : AcceptsEquivalentFrames driver represents)
    (input : Word MachineCodeSymbol) (budget : Nat) :
    exists initialSteps : Nat,
    exists cycleConfig : TuringMachine.Configuration MachineCodeSymbol
      (Scheduler.InitializerDriver.Control
        BoundedInitializerState driverState),
      TuringMachine.ComputesIn (boundedMachine driver) initialSteps
        (TuringMachine.initial (boundedMachine driver)
          (GeneratedCode.stageCode input budget))
        cycleConfig ∧
      BoundedDriverPhaseRepresents represents
        (Scheduler.Reachability.initialFrame
          (.bounded budget) input)
        cycleConfig ∧
      (Scheduler.Reachability.initialFrame
          (.bounded budget) input).cursor.Valid
        (Scheduler.Reachability.initialFrame
          (.bounded budget) input).geometry := by
  rcases bounded_initialization_computesIn driver input budget with
    ⟨initialSteps, endpointTape, hrun, htape, hvalid⟩
  let driverInner :
      TuringMachine.Configuration MachineCodeSymbol driverState :=
    { state := driver.start
      tape := Scheduler.InitializerDriver.roundTripTape endpointTape }
  let cycleConfig := boundedCycleConfig driver
    (Scheduler.InitializerDriver.roundTripTape endpointTape)
  refine ⟨initialSteps, cycleConfig, ?_, ?_, hvalid⟩
  · simpa [cycleConfig] using hrun
  · refine ⟨driverInner, ?_, ?_⟩
    · rfl
    · exact haccepts
        (Scheduler.Reachability.initialFrame
          (.bounded budget) input)
        (Scheduler.InitializerDriver.roundTripTape endpointTape) htape
  done

end Scheduler.InitializerRoutes
end TupleSearch
end FiniteRecognizer
end Computability
end FoC
