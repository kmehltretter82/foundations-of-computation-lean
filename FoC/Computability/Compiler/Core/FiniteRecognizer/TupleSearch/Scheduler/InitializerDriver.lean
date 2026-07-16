import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseRetarget
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Machine
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.StageInput.Basic

set_option doc.verso true

/-!
**Initializer/driver composition.** This sequential shell runs a finite
initializer and then permanently enters a scheduler driver.  A two-step
right/left bounce retargets the phase while preserving the initializer endpoint
up to tape equivalence.
-/

namespace FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.InitializerDriver

open Languages
open ExactFuel.StrictProbe

inductive Control (initializerState driverState : Type) where
  | initializer (inner : initializerState)
  | handoff
  | driver (inner : driverState)
deriving DecidableEq

namespace Control

def elems
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (driver : TuringMachine MachineCodeSymbol driverState) :
    List (Control initializerState driverState) :=
  List.append
    (initializer.statesFinite.elems.map Control.initializer)
    (Control.handoff :: driver.statesFinite.elems.map Control.driver)

def finite
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (driver : TuringMachine MachineCodeSymbol driverState) :
    Foundation.FiniteType (Control initializerState driverState) where
  elems := elems initializer driver
  complete := by
    intro control
    cases control with
    | initializer inner =>
        have h := initializer.statesFinite.complete inner
        simp [elems, h]
    | handoff => simp [elems]
    | driver inner =>
        have h := driver.statesFinite.complete inner
        simp [elems, h]

end Control

def mapAction (embed : innerState ->
    Control initializerState driverState) :
    Option (Option MachineCodeSymbol × Direction × innerState) ->
      Option (Option MachineCodeSymbol × Direction ×
        Control initializerState driverState)
  | none => none
  | some (write, direction, target) =>
      some (write, direction, embed target)

def transition [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (driver : TuringMachine MachineCodeSymbol driverState) :
    Control initializerState driverState -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction ×
        Control initializerState driverState)
  | .initializer inner, read =>
      if inner = initializer.halt then
        some (read, Direction.right, .handoff)
      else
        mapAction Control.initializer
          (initializer.transition inner read)
  | .handoff, read =>
      some (read, Direction.left, .driver driver.start)
  | .driver inner, read =>
      mapAction Control.driver (driver.transition inner read)

def machine [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (driver : TuringMachine MachineCodeSymbol driverState) :
    TuringMachine MachineCodeSymbol
      (Control initializerState driverState) where
  start := .initializer initializer.start
  halt := .driver driver.halt
  transition := transition initializer driver
  statesFinite := Control.finite initializer driver

def initializerConfig
    (config : TuringMachine.Configuration MachineCodeSymbol
      initializerState) :
    TuringMachine.Configuration MachineCodeSymbol
      (Control initializerState driverState) :=
  TuringMachine.PhaseEmbedding.liftConfig Control.initializer config

def driverConfig
    (config : TuringMachine.Configuration MachineCodeSymbol driverState) :
    TuringMachine.Configuration MachineCodeSymbol
      (Control initializerState driverState) :=
  TuringMachine.PhaseEmbedding.liftConfig Control.driver config

def roundTripTape (tape : Tape MachineCodeSymbol) : Tape MachineCodeSymbol :=
  Tape.move Direction.left (Tape.move Direction.right tape)

theorem roundTripTape_equiv (tape : Tape MachineCodeSymbol) :
    Tape.Equiv (roundTripTape tape) tape := by
  exact Machine.moveLeft_moveRight_equiv_self tape

theorem write_read_eq_self (tape : Tape MachineCodeSymbol) :
    Tape.write (Tape.read tape) tape = tape := by
  cases tape
  rfl

theorem initializer_step_of_some
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (driver : TuringMachine MachineCodeSymbol driverState)
    (hstop : TuringMachine.HaltingTransitionsDisabled initializer)
    (source target : TuringMachine.Configuration MachineCodeSymbol
      initializerState)
    (hstep : initializer.stepConfig source = some target) :
    (machine initializer driver).stepConfig (initializerConfig source) =
      some (initializerConfig target) := by
  have hactive : source.state ≠ initializer.halt := by
    intro hhalt
    unfold TuringMachine.stepConfig at hstep
    rw [hhalt, hstop] at hstep
    contradiction
  unfold TuringMachine.stepConfig at hstep ⊢
  simp only [machine, initializerConfig,
    TuringMachine.PhaseEmbedding.liftConfig, transition,
    hactive, ↓reduceIte]
  cases htransition : initializer.transition source.state
      (Tape.read source.tape) with
  | none =>
      rw [htransition] at hstep
      contradiction
  | some action =>
      rcases action with ⟨write, direction, nextState⟩
      rw [htransition] at hstep
      simp only at hstep
      cases hstep
      simp [mapAction, htransition]

theorem driver_step_of_some
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (driver : TuringMachine MachineCodeSymbol driverState)
    (source target : TuringMachine.Configuration MachineCodeSymbol
      driverState)
    (hstep : driver.stepConfig source = some target) :
    (machine initializer driver).stepConfig (driverConfig source) =
      some (driverConfig target) := by
  unfold TuringMachine.stepConfig at hstep ⊢
  simp only [machine, driverConfig,
    TuringMachine.PhaseEmbedding.liftConfig, transition]
  cases htransition : driver.transition source.state
      (Tape.read source.tape) with
  | none =>
      rw [htransition] at hstep
      contradiction
  | some action =>
      rcases action with ⟨write, direction, nextState⟩
      rw [htransition] at hstep
      simp only at hstep
      cases hstep
      simp [mapAction, htransition]

theorem initializer_run_lift
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (driver : TuringMachine MachineCodeSymbol driverState)
    (hstop : TuringMachine.HaltingTransitionsDisabled initializer)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      initializerState}
    (hrun : initializer.runConfigExact? steps source = some target) :
    (machine initializer driver).runConfigExact? steps
        (initializerConfig source) =
      some (initializerConfig target) := by
  exact TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    Control.initializer
    (initializer_step_of_some initializer driver hstop) hrun

theorem driver_run_lift
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (driver : TuringMachine MachineCodeSymbol driverState)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      driverState}
    (hrun : driver.runConfigExact? steps source = some target) :
    (machine initializer driver).runConfigExact? steps
        (driverConfig source) =
      some (driverConfig target) := by
  exact TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    Control.driver (driver_step_of_some initializer driver) hrun

theorem driver_computesIn_lift
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (driver : TuringMachine MachineCodeSymbol driverState)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      driverState}
    (hrun : TuringMachine.ComputesIn driver steps source target) :
    TuringMachine.ComputesIn (machine initializer driver) steps
      (driverConfig source) (driverConfig target) := by
  apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
  exact driver_run_lift initializer driver
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr hrun)

theorem handoff_run_exact
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (driver : TuringMachine MachineCodeSymbol driverState)
    (tape : Tape MachineCodeSymbol) :
    (machine initializer driver).runConfigExact? 2
        { state := .initializer initializer.halt, tape := tape } =
      some
        (driverConfig
          { state := driver.start, tape := roundTripTape tape }) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, driverConfig,
    TuringMachine.PhaseEmbedding.liftConfig, roundTripTape,
    write_read_eq_self]

theorem initialization_run_exact
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (driver : TuringMachine MachineCodeSymbol driverState)
    (hstop : TuringMachine.HaltingTransitionsDisabled initializer)
    (input : Word MachineCodeSymbol)
    (steps : Nat) (endpointTape : Tape MachineCodeSymbol)
    (hrun : initializer.runConfigExact? steps
      (TuringMachine.initial initializer input) =
        some { state := initializer.halt, tape := endpointTape }) :
    (machine initializer driver).runConfigExact? (steps + 2)
        (TuringMachine.initial (machine initializer driver) input) =
      some
        (driverConfig
          { state := driver.start
            tape := roundTripTape endpointTape }) := by
  have hfirst := initializer_run_lift initializer driver hstop hrun
  have hfirst' :
      (machine initializer driver).runConfigExact? steps
          (TuringMachine.initial (machine initializer driver) input) =
        some
          { state := Control.initializer initializer.halt
            tape := endpointTape } := by
    simpa [TuringMachine.initial, machine, initializerConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using hfirst
  rw [InitialMaterializer.ExactRun.append, hfirst']
  exact handoff_run_exact initializer driver endpointTape

theorem initialization_computes
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (driver : TuringMachine MachineCodeSymbol driverState)
    (hstop : TuringMachine.HaltingTransitionsDisabled initializer)
    (input : Word MachineCodeSymbol)
    (endpointTape : Tape MachineCodeSymbol)
    (hrun : TuringMachine.Computes initializer
      (TuringMachine.initial initializer input)
      { state := initializer.halt, tape := endpointTape }) :
    TuringMachine.Computes (machine initializer driver)
      (TuringMachine.initial (machine initializer driver) input)
      (driverConfig
        { state := driver.start
          tape := roundTripTape endpointTape }) := by
  rcases TuringMachine.computes_to_computesIn hrun with
    ⟨steps, hrunIn⟩
  have hexact := initialization_run_exact initializer driver hstop input
    steps endpointTape
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr hrunIn)
  exact TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hexact)

theorem initialization_computesIn_exists
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (driver : TuringMachine MachineCodeSymbol driverState)
    (hstop : TuringMachine.HaltingTransitionsDisabled initializer)
    (input : Word MachineCodeSymbol)
    (endpointTape : Tape MachineCodeSymbol)
    (hrun : TuringMachine.Computes initializer
      (TuringMachine.initial initializer input)
      { state := initializer.halt, tape := endpointTape }) :
    exists steps : Nat,
      TuringMachine.ComputesIn (machine initializer driver) steps
        (TuringMachine.initial (machine initializer driver) input)
        (driverConfig
          { state := driver.start
            tape := roundTripTape endpointTape }) := by
  exact TuringMachine.computes_to_computesIn
    (initialization_computes initializer driver hstop input endpointTape hrun)

theorem machine_haltingTransitionsDisabled
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (driver : TuringMachine MachineCodeSymbol driverState)
    (hstop : TuringMachine.HaltingTransitionsDisabled driver) :
    TuringMachine.HaltingTransitionsDisabled
      (machine initializer driver) := by
  intro read
  change mapAction Control.driver
    (driver.transition driver.halt read) = none
  rw [hstop]
  rfl

end FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.InitializerDriver
