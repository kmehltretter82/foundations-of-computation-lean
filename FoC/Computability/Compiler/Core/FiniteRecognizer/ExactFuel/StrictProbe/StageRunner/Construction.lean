import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PrefixHalting
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Driver.Contracts
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.StageInput.EndpointViews
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.StageInput.TwoBlankCompactor
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.StageRunner.Runs
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.Runner
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StageProgram.Spec

set_option doc.verso true

/-!
# Exact-fuel stage-runner construction

Stage-input prefix witnesses and cyclic-driver witnesses assemble the public
exact-fuel runner specification and finite runner construction.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace StageRunner

/-- The only prefix information consumed by the public semantic adapter: for
each public stage input, reach some equivalent representative of the initial
protected frame at the cyclic gate. -/
structure StagePrefixWitnesses {stateCount : Nat} {updateState : Type}
    [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel stateCount updateState) :
    Prop where
  reach : forall input fuel,
    exists T : Tape MachineCodeSymbol,
      RelationalDriverInduction.Represents
          ([] : Word MachineCodeSymbol) fuel
          (initialFrame M input fuel) T ∧
        TuringMachine.Computes (machine M K)
          (TuringMachine.initial (machine M K)
            (StageProgram.stageCode input fuel))
          (cyclicConfig
            (CyclicRelationalContract.sourceConfig
              fuel (initialFrame M input fuel) T))

theorem stagePrefixWitnesses {stateCount : Nat} {updateState : Type}
    [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel stateCount updateState) :
    StagePrefixWitnesses M K := by
  refine { reach := ?_ }
  intro input fuel
  cases input with
  | nil =>
      rcases
          InitialMaterializer.FullMaterializerMachine.empty_run_to_padded_endpoint
            M fuel with
        ⟨materializerSteps, materializerEndpoint,
          hmaterializer, hmaterializerState, hmaterializerTape, _⟩
      let T := Tape.move Direction.left materializerEndpoint.tape
      refine ⟨T, ?_, ?_⟩
      · unfold RelationalDriverInduction.Represents
        rw [initialFrame_withFuel_physicalFrame]
        simpa [T,
          StageInput.EndpointViews.bouncedEmptyTape,
          hmaterializerTape] using
          (StageInput.EndpointViews.bouncedEmptyTape_equiv_protectedInput
            M fuel)
      · have hmaterializerOuter :=
          materializer_run_lift M K hmaterializer
        have hhandoffOuter :
            (machine M K).runConfigExact? 1
                (materializerConfig materializerEndpoint) =
              some (cyclicStartConfig M T) := by
          simpa [materializerConfig,
            TuringMachine.PhaseEmbedding.liftConfig,
            hmaterializerState, emptyEndpoint, T] using
            (empty_handoff_run_exact M K materializerEndpoint.tape)
        rw [initial_eq_materializerConfig M K [] fuel]
        rw [← cyclicStartConfig_eq_sourceConfig
          (updateState := updateState) M [] fuel T]
        exact TuringMachine.computes_trans
          (computes_of_runConfigExact?_eq_some hmaterializerOuter)
          (computes_of_runConfigExact?_eq_some hhandoffOuter)
  | cons headSymbol rest =>
      rcases
          InitialMaterializer.FullMaterializerMachine.nonempty_run_to_padded_endpoint
            M fuel headSymbol rest with
        ⟨materializerSteps, materializerEndpoint,
          hmaterializer, hmaterializerState, hmaterializerTape, _⟩
      let bounced := roundTripTape materializerEndpoint.tape
      have hbounced :
          Tape.Equiv
            (InitialMaterializer.FullMaterializerMachine.nonemptyHaltTape
              M fuel headSymbol rest)
            bounced := by
        exact Tape.Equiv.trans hmaterializerTape
          (Tape.Equiv.symm (roundTripTape_equiv materializerEndpoint.tape))
      rcases
          StageInput.TwoBlankCompactor.run_from_equiv_materializerTape
            M fuel headSymbol rest bounced hbounced with
        ⟨compactorEndpoint, hcompactor, hcompactorState, hcompactorTape⟩
      let T := roundTripTape compactorEndpoint.tape
      refine ⟨T, ?_, ?_⟩
      · unfold RelationalDriverInduction.Represents
        rw [initialFrame_withFuel_physicalFrame]
        exact Tape.Equiv.trans (roundTripTape_equiv compactorEndpoint.tape)
          hcompactorTape
      · have hmaterializerOuter :=
          materializer_run_lift M K hmaterializer
        have hfirstHandoff :
            (machine M K).runConfigExact? 2
                (materializerConfig materializerEndpoint) =
              some
                (compactorConfig
                  (StageInput.TwoBlankCompactor.config
                    .seek bounced)) := by
          simpa [materializerConfig,
            TuringMachine.PhaseEmbedding.liftConfig,
            hmaterializerState, nonemptyEndpoint, bounced] using
            (nonempty_handoff_run_exact M K materializerEndpoint.tape)
        have hcompactorOuter := compactor_run_lift M K hcompactor
        have hsecondHandoff :
            (machine M K).runConfigExact? 2
                (compactorConfig compactorEndpoint) =
              some (cyclicStartConfig M T) := by
          simpa [compactorConfig,
            TuringMachine.PhaseEmbedding.liftConfig,
            hcompactorState, T] using
            (compactor_handoff_run_exact M K compactorEndpoint.tape)
        rw [initial_eq_materializerConfig M K (headSymbol :: rest) fuel]
        rw [← cyclicStartConfig_eq_sourceConfig
          (updateState := updateState) M (headSymbol :: rest) fuel T]
        exact TuringMachine.computes_trans
          (computes_of_runConfigExact?_eq_some hmaterializerOuter)
          (TuringMachine.computes_trans
            (computes_of_runConfigExact?_eq_some hfirstHandoff)
            (TuringMachine.computes_trans
              (computes_of_runConfigExact?_eq_some hcompactorOuter)
              (computes_of_runConfigExact?_eq_some hsecondHandoff)))

theorem exactFuelRunnerSpec_of_witnesses {stateCount : Nat}
    {updateState : Type} [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel stateCount updateState)
    (P : StagePrefixWitnesses M K)
    (W : CyclicRelationalContract.CyclicRunWitnesses
      M K ([] : Word MachineCodeSymbol)) :
    ExactFuelRunnerSpec (machine M K) M StageProgram.stageCode := by
  intro input fuel
  rcases P.reach input fuel with ⟨T, hrep, hprefix⟩
  exact Iff.trans
    (TuringMachine.PrefixHalting.haltsFrom_iff_of_computes
      (machine_haltingTransitionsDisabled M K) hprefix)
    (Iff.trans
      (cyclic_haltsFrom_iff M K
        (CyclicRelationalContract.sourceConfig
          fuel (initialFrame M input fuel) T))
      (by
        rw [CyclicRelationalContract.haltsFrom_source_iff
          M K [] W fuel (initialFrame M input fuel) T hrep]
        rw [initialFrame_semanticConfig]
        rfl))

theorem exactFuelRunnerSpec {stateCount : Nat}
    {updateState : Type} [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel stateCount updateState)
    (W : CyclicRelationalContract.CyclicRunWitnesses
      M K ([] : Word MachineCodeSymbol)) :
    ExactFuelRunnerSpec (machine M K) M StageProgram.stageCode :=
  exactFuelRunnerSpec_of_witnesses M K (stagePrefixWitnesses M K) W

theorem runnerConstruction {stateCount : Nat}
    {updateState : Type} [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel stateCount updateState)
    (W : CyclicRelationalContract.CyclicRunWitnesses
      M K ([] : Word MachineCodeSymbol)) :
    RunnerConstruction M StageProgram.stageCode :=
  ⟨Control M updateState, machine M K, exactFuelRunnerSpec M K W⟩

end StageRunner
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
