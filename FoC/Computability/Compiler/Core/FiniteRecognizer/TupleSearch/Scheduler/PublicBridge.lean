import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.Reachability

set_option doc.verso true

/-!
**Tuple-scheduler public-contract bridge.** The bridge requires a finite
initialization prefix and a relational one-round invariant from the concrete
driver.  Fairness and tuple coverage then yield the exact public unbounded and
bounded hidden-fuel specifications.
-/

namespace FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.PublicBridge

open Languages
open Scheduler.Layout
open Scheduler.Reachability

theorem unbounded_spec_of_rel_cycle
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (driver : TuringMachine MachineCodeSymbol driverState)
    (represents : Frame ->
      TuringMachine.Configuration MachineCodeSymbol driverState -> Prop)
    (hstop : TuringMachine.HaltingTransitionsDisabled driver)
    (hsuccess : forall frame config,
      represents frame config -> CandidateSucceeds selected frame ->
        TuringMachine.HaltsFrom driver config)
    (hfailure : forall frame config,
      represents frame config -> ¬ CandidateSucceeds selected frame ->
        exists steps : Nat,
        exists nextConfig :
            TuringMachine.Configuration MachineCodeSymbol driverState,
          0 < steps ∧
            TuringMachine.ComputesIn driver steps config nextConfig ∧
            represents frame.advance nextConfig)
    (input : Word MachineCodeSymbol)
    (initialSteps : Nat)
    (cycleConfig :
      TuringMachine.Configuration MachineCodeSymbol driverState)
    (hinitial : TuringMachine.ComputesIn driver initialSteps
      (TuringMachine.initial driver input) cycleConfig)
    (hcycle : represents (initialFrame .unbounded input) cycleConfig) :
    TuringMachine.HaltsOnInput driver input <->
      exists inner outer selectedFuel : Nat,
        TuringMachine.HaltsOnInputIn selected selectedFuel
          (GeneratedCode.nestedStageCode input inner outer) := by
  exact Iff.trans
    (TuringMachine.FairCycle.haltsFrom_iff_of_computesIn_prefix
      hstop hinitial)
    (unbounded_haltsFrom_iff_of_rel_cycle selected driver represents hstop
      hsuccess hfailure input cycleConfig hcycle)

theorem bounded_spec_of_rel_cycle
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (driver : TuringMachine MachineCodeSymbol driverState)
    (represents : Frame ->
      TuringMachine.Configuration MachineCodeSymbol driverState -> Prop)
    (hstop : TuringMachine.HaltingTransitionsDisabled driver)
    (hsuccess : forall frame config,
      represents frame config -> CandidateSucceeds selected frame ->
        TuringMachine.HaltsFrom driver config)
    (hfailure : forall frame config,
      represents frame config -> ¬ CandidateSucceeds selected frame ->
        exists steps : Nat,
        exists nextConfig :
            TuringMachine.Configuration MachineCodeSymbol driverState,
          0 < steps ∧
            TuringMachine.ComputesIn driver steps config nextConfig ∧
            represents frame.advance nextConfig)
    (input : Word MachineCodeSymbol) (budget : Nat)
    (initialSteps : Nat)
    (cycleConfig :
      TuringMachine.Configuration MachineCodeSymbol driverState)
    (hinitial : TuringMachine.ComputesIn driver initialSteps
      (TuringMachine.initial driver
        (GeneratedCode.stageCode input budget)) cycleConfig)
    (hcycle : represents
      (initialFrame (.bounded budget) input) cycleConfig) :
    TuringMachine.HaltsOnInput driver
        (GeneratedCode.stageCode input budget) <->
      exists inner outer selectedFuel : Nat,
        inner ≤ budget ∧ outer ≤ budget ∧
          TuringMachine.HaltsOnInputIn selected selectedFuel
            (GeneratedCode.nestedStageCode input inner outer) := by
  exact Iff.trans
    (TuringMachine.FairCycle.haltsFrom_iff_of_computesIn_prefix
      hstop hinitial)
    (bounded_haltsFrom_iff_of_rel_cycle selected driver represents hstop
      hsuccess hfailure input budget cycleConfig hcycle)

end FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.PublicBridge
