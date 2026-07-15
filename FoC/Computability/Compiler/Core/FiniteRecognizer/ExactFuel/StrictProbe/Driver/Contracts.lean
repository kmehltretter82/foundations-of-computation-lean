import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Driver.Induction
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Driver.CyclicMachine

set_option doc.verso true

/-!
# Cyclic-driver relational contract

Representative-indexed run witnesses instantiate the generic exact-fuel driver
induction for the cyclic machine.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace CyclicRelationalContract

open SerializedFieldComposer

def sourceConfig {stateCount : Nat} {updateState : Type}
    (_fuel : Nat) (F : CarriedStateFrame.LoopFrame stateCount)
    (T : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      (CyclicDriverIntegration.Control stateCount updateState) where
  state := .gate (.header F.carriedState)
  tape := T

def acceptConfig {stateCount : Nat} {updateState : Type}
    (T : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      (CyclicDriverIntegration.Control stateCount updateState) where
  state := .accept
  tape := T

def rejectConfig {stateCount : Nat} {updateState : Type}
    (T : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      (CyclicDriverIntegration.Control stateCount updateState) where
  state := .reject
  tape := T

/-- Only the four concrete physical run families remain as obligations.  Exit
state facts and representative bookkeeping are derived below. -/
structure CyclicRunWitnesses {stateCount : Nat} {updateState : Type}
    [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel stateCount updateState)
    (callerData : Word MachineCodeSymbol) : Prop where
  zeroAccept :
    forall F T,
      RelationalDriverInduction.Represents callerData 0 F T ->
      (RelationalDriverInduction.semanticConfig F).state = M.halt ->
      exists endpointTape : Tape MachineCodeSymbol,
        TuringMachine.Computes
          (CyclicDriverIntegration.machine M K)
          (sourceConfig 0 F T) (acceptConfig endpointTape)
  zeroReject :
    forall F T,
      RelationalDriverInduction.Represents callerData 0 F T ->
      (RelationalDriverInduction.semanticConfig F).state ≠ M.halt ->
      exists endpointTape : Tape MachineCodeSymbol,
        TuringMachine.Computes
          (CyclicDriverIntegration.machine M K)
          (sourceConfig 0 F T) (rejectConfig endpointTape)
  succMissing :
    forall fuel F T,
      RelationalDriverInduction.Represents
        callerData (fuel + 1) F T ->
      M.transition
          (RelationalDriverInduction.semanticConfig F).state
          (Tape.read
            (RelationalDriverInduction.semanticConfig F).tape) =
        none ->
      exists endpointTape : Tape MachineCodeSymbol,
        TuringMachine.Computes
          (CyclicDriverIntegration.machine M K)
          (sourceConfig (fuel + 1) F T) (rejectConfig endpointTape)
  succPresent :
    forall fuel F T write direction nextState,
      RelationalDriverInduction.Represents
        callerData (fuel + 1) F T ->
      M.transition
          (RelationalDriverInduction.semanticConfig F).state
          (Tape.read
            (RelationalDriverInduction.semanticConfig F).tape) =
        some (write, direction, nextState) ->
      exists T' : Tape MachineCodeSymbol,
        RelationalDriverInduction.Represents callerData fuel
          (CarriedStateFrame.afterSelected
            fuel write direction nextState F) T' ∧
        TuringMachine.Computes
          (CyclicDriverIntegration.machine M K)
          (sourceConfig (fuel + 1) F T)
          (sourceConfig fuel
            (CarriedStateFrame.afterSelected
              fuel write direction nextState F) T')

def runContract {stateCount : Nat} {updateState : Type}
    [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel stateCount updateState)
    (callerData : Word MachineCodeSymbol)
    (W : CyclicRunWitnesses M K callerData) :
    RelationalDriverInduction.RunContract M
      (CyclicDriverIntegration.machine M K) callerData where
  source := sourceConfig
  sourceTape := by
    intro fuel F T
    rfl
  zeroAccept := by
    intro F T hrep hhalt
    rcases W.zeroAccept F T hrep hhalt with ⟨endpointTape, hrun⟩
    exact ⟨acceptConfig endpointTape, hrun, rfl⟩
  zeroReject := by
    intro F T hrep hnotHalt
    rcases W.zeroReject F T hrep hnotHalt with ⟨endpointTape, hrun⟩
    refine ⟨rejectConfig endpointTape, hrun, ?_, ?_⟩
    · simp [TuringMachine.Halted, rejectConfig,
        CyclicDriverIntegration.machine]
    · intro next
      exact TuringMachine.not_step_of_transition_eq_none
        (CyclicDriverIntegration.reject_transition_none
          M K (Tape.read endpointTape))
  succMissing := by
    intro fuel F T hrep hmissing
    rcases W.succMissing fuel F T hrep hmissing with
      ⟨endpointTape, hrun⟩
    refine ⟨rejectConfig endpointTape, hrun, ?_, ?_⟩
    · simp [TuringMachine.Halted, rejectConfig,
        CyclicDriverIntegration.machine]
    · intro next
      exact TuringMachine.not_step_of_transition_eq_none
        (CyclicDriverIntegration.reject_transition_none
          M K (Tape.read endpointTape))
  succPresent := by
    intro fuel F T write direction nextState hrep hselected
    exact W.succPresent fuel F T write direction nextState hrep hselected

def exitContract {stateCount : Nat} {updateState : Type}
    [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel stateCount updateState)
    (callerData : Word MachineCodeSymbol)
    (W : CyclicRunWitnesses M K callerData) :
    RelationalDriverInduction.ExitContract
      (runContract M K callerData W) where
  haltingTransitionsDisabled :=
    CyclicDriverIntegration.machine_haltingTransitionsDisabled M K

theorem haltsFrom_source_iff {stateCount : Nat} {updateState : Type}
    [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel stateCount updateState)
    (callerData : Word MachineCodeSymbol)
    (W : CyclicRunWitnesses M K callerData)
    (fuel : Nat) (F : CarriedStateFrame.LoopFrame stateCount)
    (T : Tape MachineCodeSymbol)
    (hrep :
      RelationalDriverInduction.Represents callerData fuel F T) :
    TuringMachine.HaltsFrom
        (CyclicDriverIntegration.machine M K)
        (sourceConfig fuel F T) <->
      TuringMachine.HaltsFromIn M fuel
        (RelationalDriverInduction.semanticConfig F) := by
  exact RelationalDriverInduction.haltsFrom_source_iff
    (runContract M K callerData W)
    (exitContract M K callerData W) fuel F T hrep


end CyclicRelationalContract
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
