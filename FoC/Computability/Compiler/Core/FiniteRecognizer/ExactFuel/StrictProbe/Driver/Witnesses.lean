import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Driver.Contracts
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.TapeEquivTransport

set_option doc.verso true

/-!
# Cyclic-driver run witnesses

Canonical runs are transported across equivalent protected-frame tape
representatives and assembled into the cyclic relational contract.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace CyclicDriverWitnesses

open SerializedFieldComposer

def canonicalTape {stateCount : Nat}
    (callerData : Word MachineCodeSymbol) (fuel : Nat)
    (F : CarriedStateFrame.LoopFrame stateCount) : Tape MachineCodeSymbol :=
  Tape.input
    (Frame.protectedWord
      (CarriedStateFrame.withFuel fuel F).physicalFrame callerData)

theorem zeroAccept {stateCount : Nat} {updateState : Type}
    [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel
      stateCount updateState)
    (callerData : Word MachineCodeSymbol)
    (F : CarriedStateFrame.LoopFrame stateCount)
    (T : Tape MachineCodeSymbol)
    (hrep :
      RelationalDriverInduction.Represents callerData 0 F T)
    (hhalt :
      (RelationalDriverInduction.semanticConfig F).state = M.halt) :
    exists endpointTape : Tape MachineCodeSymbol,
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
      Tape.Equiv (canonicalTape callerData 0 F) T :=
    Tape.Equiv.symm hrep
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        hcanonical hsourceEquiv with
    ⟨endpoint, hrun, hstate, _⟩
  refine ⟨endpoint.tape, ?_⟩
  have hcomputes := TuringMachine.computesIn_to_computes
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
        canonicalTape] using hcomputes

theorem zeroReject {stateCount : Nat} {updateState : Type}
    [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel
      stateCount updateState)
    (callerData : Word MachineCodeSymbol)
    (F : CarriedStateFrame.LoopFrame stateCount)
    (T : Tape MachineCodeSymbol)
    (hrep :
      RelationalDriverInduction.Represents callerData 0 F T)
    (hnotHalt :
      (RelationalDriverInduction.semanticConfig F).state ≠ M.halt) :
    exists endpointTape : Tape MachineCodeSymbol,
      TuringMachine.Computes
        (CyclicDriverIntegration.machine M K)
        (CyclicRelationalContract.sourceConfig 0 F T)
        (CyclicRelationalContract.rejectConfig endpointTape) := by
  have hcanonical :=
    CyclicDriverIntegration.zero_reject_run_exact
      M K F callerData (by
        simpa [CyclicDriverIntegration.semanticConfig,
          RelationalDriverInduction.semanticConfig] using hnotHalt)
  have hsourceEquiv :
      Tape.Equiv (canonicalTape callerData 0 F) T :=
    Tape.Equiv.symm hrep
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        hcanonical hsourceEquiv with
    ⟨endpoint, hrun, hstate, _⟩
  refine ⟨endpoint.tape, ?_⟩
  have hcomputes := TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hrun)
  cases endpoint with
  | mk endpointState endpointTape =>
      change endpointState = CyclicDriverIntegration.Control.reject at hstate
      subst endpointState
      simpa [CyclicRelationalContract.sourceConfig,
        CyclicRelationalContract.rejectConfig,
        CyclicDriverIntegration.loopSourceConfig,
        CyclicDriverIntegration.gateConfig,
        CarriedFuelGate.sourceConfig,
        canonicalTape] using hcomputes

theorem succMissing {stateCount : Nat} {updateState : Type}
    [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel
      stateCount updateState)
    (callerData : Word MachineCodeSymbol)
    (fuel : Nat) (F : CarriedStateFrame.LoopFrame stateCount)
    (T : Tape MachineCodeSymbol)
    (hrep :
      RelationalDriverInduction.Represents
        callerData (fuel + 1) F T)
    (hmissing :
      M.transition
          (RelationalDriverInduction.semanticConfig F).state
          (Tape.read
            (RelationalDriverInduction.semanticConfig F).tape) =
        none) :
    exists endpointTape : Tape MachineCodeSymbol,
      TuringMachine.Computes
        (CyclicDriverIntegration.machine M K)
        (CyclicRelationalContract.sourceConfig (fuel + 1) F T)
        (CyclicRelationalContract.rejectConfig endpointTape) := by
  have hcanonical :=
    CyclicDriverIntegration.succ_missing_run_exact
      M K fuel F callerData (by
        simpa [CyclicDriverIntegration.semanticConfig,
          RelationalDriverInduction.semanticConfig] using hmissing)
  have hsourceEquiv :
      Tape.Equiv (canonicalTape callerData (fuel + 1) F) T :=
    Tape.Equiv.symm hrep
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        hcanonical hsourceEquiv with
    ⟨endpoint, hrun, hstate, _⟩
  refine ⟨endpoint.tape, ?_⟩
  have hcomputes := TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hrun)
  cases endpoint with
  | mk endpointState endpointTape =>
      change endpointState = CyclicDriverIntegration.Control.reject at hstate
      subst endpointState
      simpa [CyclicRelationalContract.sourceConfig,
        CyclicRelationalContract.rejectConfig,
        CyclicDriverIntegration.loopSourceConfig,
        CyclicDriverIntegration.gateConfig,
        CarriedFuelGate.sourceConfig,
        canonicalTape] using hcomputes

def selectedPayload {stateCount : Nat}
    (write : Option MachineCodeSymbol) (direction : Direction)
    (nextState : Fin stateCount) :
    SerializedHeadDispatch.Selected stateCount where
  write := write
  direction := direction
  nextState := nextState

def selectedPrefixTape {stateCount : Nat}
    (callerData : Word MachineCodeSymbol) (fuel : Nat)
    (F : CarriedStateFrame.LoopFrame stateCount)
    (write : Option MachineCodeSymbol) (direction : Direction)
    (nextState : Fin stateCount) : Tape MachineCodeSymbol :=
  let L := (CarriedStateFrame.withFuel (fuel + 1) F).physicalFrame
  CyclicDriverIntegration.roundTripTape
    (SerializedHeadDispatch.selectedConfig
      (selectedPayload write direction nextState)
      (SerializedFieldComposer.HeadLocator.gateTape
        (Frame.protectedWord L callerData))).tape

/-- Execute the selected write/move update
kernel and return a representative of the recursive protected frame. -/
structure SelectedUpdateRuns {stateCount : Nat} {updateState : Type}
    [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel
      stateCount updateState)
    (callerData : Word MachineCodeSymbol) : Prop where
  run :
    forall fuel F write direction nextState,
      M.transition
          (RelationalDriverInduction.semanticConfig F).state
          (Tape.read
            (RelationalDriverInduction.semanticConfig F).tape) =
        some (write, direction, nextState) ->
      exists steps targetTape,
        (K.machine (selectedPayload write direction nextState)).runConfigExact?
            steps
            { state :=
                K.start (selectedPayload write direction nextState)
              tape :=
                selectedPrefixTape callerData fuel F
                  write direction nextState } =
          some
            { state :=
                K.halt (selectedPayload write direction nextState)
              tape := targetTape } ∧
        RelationalDriverInduction.Represents callerData fuel
          (CarriedStateFrame.afterSelected
            fuel write direction nextState F)
          (CyclicDriverIntegration.roundTripTape targetTape)

theorem canonicalSelectedPrefix {stateCount : Nat} {updateState : Type}
    [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel
      stateCount updateState)
    (callerData : Word MachineCodeSymbol)
    (fuel : Nat) (F : CarriedStateFrame.LoopFrame stateCount)
    (write : Option MachineCodeSymbol) (direction : Direction)
    (nextState : Fin stateCount)
    (hselected :
      M.transition
          (RelationalDriverInduction.semanticConfig F).state
          (Tape.read
            (RelationalDriverInduction.semanticConfig F).tape) =
        some (write, direction, nextState)) :
    let L := (CarriedStateFrame.withFuel (fuel + 1) F).physicalFrame
    let selected := selectedPayload write direction nextState
    (CyclicDriverIntegration.machine M K).runConfigExact?
        (4 +
          ((SerializedFieldComposer.HeadLocator.locatorSteps L + 2) +
            2))
        (CyclicDriverIntegration.loopSourceConfig
          (updateState := updateState) (fuel + 1) F callerData) =
      some
        { state :=
            CyclicDriverIntegration.Control.update selected
              (K.start selected)
          tape :=
            selectedPrefixTape callerData fuel F
              write direction nextState } := by
  dsimp
  simpa [selectedPayload, selectedPrefixTape,
      RelationalDriverInduction.semanticConfig,
      CyclicDriverIntegration.semanticConfig] using
    CyclicDriverIntegration.succ_present_prefix_run_exact
      M K fuel F callerData write direction nextState hselected

theorem canonicalSuccPresent {stateCount : Nat} {updateState : Type}
    [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel
      stateCount updateState)
    (callerData : Word MachineCodeSymbol)
    (U : SelectedUpdateRuns M K callerData)
    (fuel : Nat) (F : CarriedStateFrame.LoopFrame stateCount)
    (write : Option MachineCodeSymbol) (direction : Direction)
    (nextState : Fin stateCount)
    (hselected :
      M.transition
          (RelationalDriverInduction.semanticConfig F).state
          (Tape.read
            (RelationalDriverInduction.semanticConfig F).tape) =
        some (write, direction, nextState)) :
    exists T' : Tape MachineCodeSymbol,
      RelationalDriverInduction.Represents callerData fuel
          (CarriedStateFrame.afterSelected
            fuel write direction nextState F) T' ∧
        TuringMachine.Computes
          (CyclicDriverIntegration.machine M K)
          (CyclicRelationalContract.sourceConfig (fuel + 1) F
            (canonicalTape callerData (fuel + 1) F))
          (CyclicRelationalContract.sourceConfig fuel
            (CarriedStateFrame.afterSelected
              fuel write direction nextState F) T') := by
  rcases U.run fuel F write direction nextState hselected with
    ⟨steps, targetTape, hupdate, hrep⟩
  let selected := selectedPayload write direction nextState
  let T' := CyclicDriverIntegration.roundTripTape targetTape
  refine ⟨T', hrep, ?_⟩
  have hprefix :=
    canonicalSelectedPrefix M K callerData fuel F write direction nextState
      hselected
  have htail :=
    CyclicDriverIntegration.update_stage_run_exact
      M K selected
      (selectedPrefixTape callerData fuel F write direction nextState)
      targetTape hupdate
  have htotal :=
    TuringMachine.runConfigExact?_trans hprefix htail
  have hcomputes := TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp htotal)
  simpa [CyclicRelationalContract.sourceConfig,
      CyclicDriverIntegration.loopSourceConfig,
      CyclicDriverIntegration.gateConfig,
      CarriedFuelGate.sourceConfig,
      canonicalTape, selected, selectedPayload, T',
      CarriedStateFrame.afterSelected] using hcomputes

theorem succPresent {stateCount : Nat} {updateState : Type}
    [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel
      stateCount updateState)
    (callerData : Word MachineCodeSymbol)
    (U : SelectedUpdateRuns M K callerData)
    (fuel : Nat) (F : CarriedStateFrame.LoopFrame stateCount)
    (T : Tape MachineCodeSymbol)
    (write : Option MachineCodeSymbol) (direction : Direction)
    (nextState : Fin stateCount)
    (hrep :
      RelationalDriverInduction.Represents
        callerData (fuel + 1) F T)
    (hselected :
      M.transition
          (RelationalDriverInduction.semanticConfig F).state
          (Tape.read
            (RelationalDriverInduction.semanticConfig F).tape) =
        some (write, direction, nextState)) :
    exists T' : Tape MachineCodeSymbol,
      RelationalDriverInduction.Represents callerData fuel
          (CarriedStateFrame.afterSelected
            fuel write direction nextState F) T' ∧
        TuringMachine.Computes
          (CyclicDriverIntegration.machine M K)
          (CyclicRelationalContract.sourceConfig (fuel + 1) F T)
          (CyclicRelationalContract.sourceConfig fuel
            (CarriedStateFrame.afterSelected
              fuel write direction nextState F) T') := by
  rcases canonicalSuccPresent M K callerData U fuel F write direction
      nextState hselected with
    ⟨canonicalTarget, htargetRep, hcanonical⟩
  rcases TuringMachine.computes_to_computesIn hcanonical with
    ⟨steps, hcanonicalIn⟩
  have hsourceEquiv :
      Tape.Equiv
        (CyclicRelationalContract.sourceConfig
          (updateState := updateState) (fuel + 1) F
          (canonicalTape callerData (fuel + 1) F)).tape T := by
    simpa [CyclicRelationalContract.sourceConfig, canonicalTape] using
      Tape.Equiv.symm hrep
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      hcanonicalIn hsourceEquiv with
    ⟨endpoint, hrun, hstate, htargetEquiv⟩
  have hcomputes := TuringMachine.computesIn_to_computes hrun
  cases endpoint with
  | mk endpointState endpointTape =>
      change endpointState =
        CyclicDriverIntegration.Control.gate
          (.header
            (CarriedStateFrame.afterSelected
              fuel write direction nextState F).carriedState) at hstate
      subst endpointState
      have hactualRep :
          RelationalDriverInduction.Represents callerData fuel
            (CarriedStateFrame.afterSelected
              fuel write direction nextState F) endpointTape := by
        apply RelationalDriverInduction.represents_of_equiv
          (hU := htargetRep)
        exact Tape.Equiv.symm (by
          simpa [CyclicRelationalContract.sourceConfig] using
            htargetEquiv)
      refine ⟨endpointTape, hactualRep, ?_⟩
      simpa [CyclicRelationalContract.sourceConfig] using hcomputes

def runWitnesses {stateCount : Nat} {updateState : Type}
    [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel
      stateCount updateState)
    (callerData : Word MachineCodeSymbol)
    (U : SelectedUpdateRuns M K callerData) :
    CyclicRelationalContract.CyclicRunWitnesses M K callerData where
  zeroAccept := by
    intro F T hrep hhalt
    exact zeroAccept M K callerData F T hrep hhalt
  zeroReject := by
    intro F T hrep hnotHalt
    exact zeroReject M K callerData F T hrep hnotHalt
  succMissing := by
    intro fuel F T hrep hmissing
    exact succMissing M K callerData fuel F T hrep hmissing
  succPresent := by
    intro fuel F T write direction nextState hrep hselected
    exact succPresent M K callerData U fuel F T write direction nextState
      hrep hselected


end CyclicDriverWitnesses
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
