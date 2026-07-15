import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Driver.Witnesses

set_option doc.verso true

/-!
# Product probe success endpoints

A successful cyclic exact-fuel probe preserves the protected caller-data
representation needed by the next product phase.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace ProductSuccess

open SerializedFieldComposer

theorem zeroAccept_preserves_representation
    {stateCount : Nat} {updateState : Type}
    [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel stateCount updateState)
    (callerData : Word MachineCodeSymbol)
    (F : CarriedStateFrame.LoopFrame stateCount)
    (T : Tape MachineCodeSymbol)
    (hrep : RelationalDriverInduction.Represents callerData 0 F T)
    (hhalt : (RelationalDriverInduction.semanticConfig F).state = M.halt) :
    exists endpointTape : Tape MachineCodeSymbol,
      RelationalDriverInduction.Represents callerData 0 F endpointTape ∧
      TuringMachine.Computes
        (CyclicDriverIntegration.machine M K)
        (CyclicRelationalContract.sourceConfig 0 F T)
        (CyclicRelationalContract.acceptConfig endpointTape) := by
  have hcanonical :=
    CyclicDriverIntegration.zero_accept_run_exact
      M K F callerData (by
        simpa [CyclicDriverIntegration.semanticConfig,
          RelationalDriverInduction.semanticConfig] using hhalt)
  have hsourceEquiv :
      Tape.Equiv (CyclicDriverWitnesses.canonicalTape callerData 0 F) T :=
    Tape.Equiv.symm hrep
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        hcanonical hsourceEquiv with
    ⟨endpoint, hrun, hstate, htargetEquiv⟩
  refine ⟨endpoint.tape, ?_, ?_⟩
  · unfold RelationalDriverInduction.Represents
    exact Tape.Equiv.symm htargetEquiv
  · have hcomputes := TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hrun)
    cases endpoint with
    | mk endpointState endpointTape =>
        change endpointState = CyclicDriverIntegration.Control.accept at hstate
        subst endpointState
        simpa [CyclicRelationalContract.sourceConfig,
          CyclicRelationalContract.acceptConfig,
          CyclicDriverIntegration.loopSourceConfig,
          CyclicDriverIntegration.gateConfig,
          CarriedFuelGate.sourceConfig,
          CyclicDriverWitnesses.canonicalTape] using hcomputes

theorem success_endpoint_of_witnesses
    {stateCount : Nat} {updateState : Type}
    [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel stateCount updateState)
    (callerData : Word MachineCodeSymbol)
    (W : CyclicRelationalContract.CyclicRunWitnesses M K callerData) :
    forall fuel (F : CarriedStateFrame.LoopFrame stateCount)
        (T : Tape MachineCodeSymbol),
      RelationalDriverInduction.Represents callerData fuel F T ->
      TuringMachine.HaltsFromIn M fuel
        (RelationalDriverInduction.semanticConfig F) ->
      exists endpointFrame : CarriedStateFrame.LoopFrame stateCount,
        exists endpointTape : Tape MachineCodeSymbol,
          RelationalDriverInduction.Represents callerData 0
              endpointFrame endpointTape ∧
            TuringMachine.Computes
              (CyclicDriverIntegration.machine M K)
              (CyclicRelationalContract.sourceConfig fuel F T)
              (CyclicRelationalContract.acceptConfig endpointTape) := by
  intro fuel
  induction fuel with
  | zero =>
      intro F T hrep hhalts
      have hhalt :
          (RelationalDriverInduction.semanticConfig F).state = M.halt :=
        TuringMachine.haltsFromIn_zero_iff.mp hhalts
      rcases zeroAccept_preserves_representation M K callerData F T hrep hhalt with
        ⟨endpointTape, hendpointRep, hrun⟩
      exact ⟨F, endpointTape, hendpointRep, hrun⟩
  | succ fuel ih =>
      intro F T hrep hhalts
      cases htransition :
          M.transition
            (RelationalDriverInduction.semanticConfig F).state
            (Tape.read (RelationalDriverInduction.semanticConfig F).tape) with
      | none =>
          exact False.elim
            (TuringMachine.not_haltsFromIn_succ_of_transition_eq_none
              htransition hhalts)
      | some action =>
          rcases action with ⟨write, direction, nextState⟩
          rcases W.succPresent fuel F T write direction nextState
              hrep htransition with
            ⟨T', hrep', hprefix⟩
          have htail :
              TuringMachine.HaltsFromIn M fuel
                (RelationalDriverInduction.semanticConfig
                  (CarriedStateFrame.afterSelected
                    fuel write direction nextState F)) := by
            rw [RelationalDriverInduction.semanticConfig_afterSelected]
            exact
              (TuringMachine.haltsFromIn_succ_iff_of_transition_eq_some
                htransition).mp hhalts
          rcases ih _ T' hrep' htail with
            ⟨endpointFrame, endpointTape, hfinalRep, htailRun⟩
          exact ⟨endpointFrame, endpointTape, hfinalRep,
            TuringMachine.computes_trans hprefix htailRun⟩

end ProductSuccess
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC

