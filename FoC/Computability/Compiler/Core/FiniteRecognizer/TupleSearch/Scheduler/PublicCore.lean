import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.PublicClosure
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.Cycle
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Basic

set_option doc.verso true

/-!
# Tuple-search scheduler cycle contracts

Common representation and progress contracts for the finite tuple-search
scheduler.
-/

namespace FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.PublicCore

open Languages

abbrev Frame := Scheduler.Layout.Frame

def ConcreteCycleRepresents {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : Frame)
    (config : TuringMachine.Configuration MachineCodeSymbol
      (Scheduler.Cycle.Control selected)) : Prop :=
  frame.cursor.Valid frame.geometry ∧
    config.state = (Scheduler.Cycle.machine selected).start ∧
    Tape.Equiv
      (Tape.input (Scheduler.SplitLayout.encode frame)) config.tape

def CycleSuccessObligation {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount)) : Prop :=
  forall frame config,
    ConcreteCycleRepresents selected frame config ->
      Scheduler.Reachability.CandidateSucceeds selected frame ->
        TuringMachine.HaltsFrom (Scheduler.Cycle.machine selected) config

def CycleFailureObligation {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount)) : Prop :=
  forall frame config,
    ConcreteCycleRepresents selected frame config ->
      ¬ Scheduler.Reachability.CandidateSucceeds selected frame ->
        exists steps : Nat,
        exists nextConfig : TuringMachine.Configuration MachineCodeSymbol
          (Scheduler.Cycle.Control selected),
          0 < steps ∧
            TuringMachine.ComputesIn (Scheduler.Cycle.machine selected)
              steps config nextConfig ∧
            ConcreteCycleRepresents selected frame.advance nextConfig

theorem concreteCycleRepresents_initial
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (geometry : Scheduler.Layout.Geometry)
    (input : Word MachineCodeSymbol) (tape : Tape MachineCodeSymbol)
    (htape : Tape.Equiv
      (Tape.input
        (Scheduler.SplitLayout.encode
          (Scheduler.Reachability.initialFrame geometry input))) tape) :
    ConcreteCycleRepresents selected
      (Scheduler.Reachability.initialFrame geometry input)
      { state := (Scheduler.Cycle.machine selected).start
        tape := tape } := by
  exact ⟨Scheduler.Layout.Cursor.initial_valid geometry, rfl, htape⟩

theorem concreteCycle_success
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    CycleSuccessObligation selected := by
  simpa [CycleSuccessObligation, ConcreteCycleRepresents,
    Scheduler.Cycle.Represents] using
      (Scheduler.Cycle.success_haltsFrom selected)

theorem concreteCycle_failure
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    CycleFailureObligation selected := by
  simpa [CycleFailureObligation, ConcreteCycleRepresents,
    Scheduler.Cycle.Represents] using
      (Scheduler.Cycle.failure_advances selected)

end FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.PublicCore
