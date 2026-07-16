import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.PublicCore
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Basic

set_option doc.verso true

/-!
# Bounded tuple-search scheduler

Finite-state construction of the budget-bounded hidden-fuel pair searcher.
-/

namespace FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.Bounded

open Languages

theorem boundedSearcher_spec
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    GeneratedBoundedHiddenFuelPairSpec
      (Scheduler.PublicClosure.boundedSearcher selected) selected := by
  exact Scheduler.PublicClosure.boundedSpec_of_cycle_contracts
    selected
    (Scheduler.PublicCore.ConcreteCycleRepresents selected)
    (Scheduler.PublicCore.concreteCycle_success selected)
    (Scheduler.PublicCore.concreteCycle_failure selected)
    (fun input budget =>
      Scheduler.PublicCore.concreteCycleRepresents_initial
        selected (.bounded budget) input)

theorem generatedBoundedHiddenFuelPairFinStateConstructionExplicit :
    forall stateCount : Nat,
    forall selected : TuringMachine MachineCodeSymbol (Fin stateCount),
      exists searcherState : Type,
      exists searcher : TuringMachine MachineCodeSymbol searcherState,
        GeneratedBoundedHiddenFuelPairSpec searcher selected := by
  intro stateCount selected
  exact ⟨_, Scheduler.PublicClosure.boundedSearcher selected,
    boundedSearcher_spec selected⟩

end FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.Bounded
