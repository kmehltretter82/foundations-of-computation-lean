import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.PublicCore
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Basic

set_option doc.verso true

/-!
# Unbounded tuple-search scheduler

Finite-state construction of the unbounded hidden-fuel pair searcher.
-/

namespace FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.Unbounded

open Languages

theorem unboundedSearcher_spec
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    GeneratedUnboundedHiddenFuelPairSpec
      (Scheduler.PublicClosure.unboundedSearcher selected) selected := by
  exact Scheduler.PublicClosure.unboundedSpec_of_cycle_contracts
    selected
    (Scheduler.PublicCore.ConcreteCycleRepresents selected)
    (Scheduler.PublicCore.concreteCycle_success selected)
    (Scheduler.PublicCore.concreteCycle_failure selected)
    (Scheduler.PublicCore.concreteCycleRepresents_initial
      selected .unbounded)

theorem generatedUnboundedHiddenFuelPairFinStateConstructionExplicit :
    forall stateCount : Nat,
    forall selected : TuringMachine MachineCodeSymbol (Fin stateCount),
      exists searcherState : Type,
      exists searcher : TuringMachine MachineCodeSymbol searcherState,
        GeneratedUnboundedHiddenFuelPairSpec searcher selected := by
  intro stateCount selected
  exact ⟨_, Scheduler.PublicClosure.unboundedSearcher selected,
    unboundedSearcher_spec selected⟩

end FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.Unbounded
