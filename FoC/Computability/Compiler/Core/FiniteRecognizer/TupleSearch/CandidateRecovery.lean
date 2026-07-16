import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.CandidateKernel
import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.Handoff

set_option doc.verso true

/-!
# Tuple-search candidate recovery

Miss-side representative bookkeeping for the exact-candidate kernel, followed
by structural protected-frame erasure that exposes the scheduler caller word.
-/

namespace FoC.Computability.FiniteRecognizer.TupleSearch.CandidateKernel.ProbeReturn

open Languages
open ExactFuel.StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer

namespace Recovery

theorem roundTrip_represents {stateCount : Nat}
    {callerData : Word MachineCodeSymbol} {fuel : Nat}
    {F : CarriedStateFrame.LoopFrame stateCount}
    {T : Tape MachineCodeSymbol}
    (hrep : RelationalDriverInduction.Represents callerData fuel F T) :
    RelationalDriverInduction.Represents callerData fuel F
      (CyclicDriverIntegration.roundTripTape T) := by
  exact RelationalDriverInduction.represents_of_equiv
    (ExactFuel.StrictProbe.Machine.moveLeft_moveRight_equiv_self T) hrep

theorem recoveredCaller_read_eq
    {callerData : Word MachineCodeSymbol}
    {T : Tape MachineCodeSymbol}
    (hcaller : Tape.Equiv T (Tape.input callerData)) :
    Tape.read T = Tape.read (Tape.input callerData) := by
  exact Tape.Equiv.read_eq hcaller

theorem recoveredCaller_normalizedOutput_eq
    {callerData : Word MachineCodeSymbol}
    {T : Tape MachineCodeSymbol}
    (hcaller : Tape.Equiv T (Tape.input callerData)) :
    Tape.normalizedOutput T = callerData := by
  calc
    Tape.normalizedOutput T =
        Tape.normalizedOutput (Tape.input callerData) :=
      Tape.Equiv.normalizedOutput_eq hcaller
    _ = callerData := by
      simpa [Tape.output] using
        (Tape.normalizedOutput_output callerData)

theorem zero_reject_with_rep {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (callerData : Word MachineCodeSymbol)
    (F : CarriedStateFrame.LoopFrame stateCount)
    (T : Tape MachineCodeSymbol)
    (hrep : RelationalDriverInduction.Represents callerData 0 F T)
    (hnotHalt :
      (RelationalDriverInduction.semanticConfig F).state ≠ selected.halt) :
    exists endpointTape,
      RelationalDriverInduction.Represents callerData 0 F endpointTape ∧
      TuringMachine.Computes (probeMachine selected)
        (CyclicRelationalContract.sourceConfig 0 F T)
        (CyclicRelationalContract.rejectConfig endpointTape) := by
  have hcanonical := CyclicDriverIntegration.zero_reject_run_exact
    selected (Kernel stateCount) F callerData (by
      simpa [CyclicDriverIntegration.semanticConfig,
        RelationalDriverInduction.semanticConfig] using hnotHalt)
  have hsourceEquiv :
      Tape.Equiv (CyclicDriverWitnesses.canonicalTape callerData 0 F) T := by
    simpa [CyclicDriverWitnesses.canonicalTape,
      RelationalDriverInduction.Represents] using Tape.Equiv.symm hrep
  have hcanonical' :
      (probeMachine selected).runConfigExact? 8
          (CyclicRelationalContract.sourceConfig 0 F
            (CyclicDriverWitnesses.canonicalTape callerData 0 F)) =
        some (CyclicRelationalContract.rejectConfig
          (CyclicDriverWitnesses.canonicalTape callerData 0 F)) := by
    simpa [probeMachine, CyclicRelationalContract.sourceConfig,
      CyclicRelationalContract.rejectConfig,
      CyclicDriverIntegration.loopSourceConfig,
      CyclicDriverIntegration.gateConfig,
      CarriedFuelGate.sourceConfig,
      CyclicDriverWitnesses.canonicalTape] using hcanonical
  rcases TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
      hcanonical' hsourceEquiv with ⟨endpoint, hrun, hstate, hequiv⟩
  cases endpoint with
  | mk endpointState endpointTape =>
      change endpointState = CyclicDriverIntegration.Control.reject at hstate
      subst endpointState
      refine ⟨endpointTape, ?_, ?_⟩
      · simpa [CyclicRelationalContract.rejectConfig,
          CyclicDriverWitnesses.canonicalTape,
          RelationalDriverInduction.Represents] using Tape.Equiv.symm hequiv
      · have hcomputes := TuringMachine.computesIn_to_computes
          (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hrun)
        simpa [CyclicRelationalContract.sourceConfig,
          CyclicRelationalContract.rejectConfig] using hcomputes

def missingTargetTape {stateCount : Nat}
    (callerData : Word MachineCodeSymbol) (fuel : Nat)
    (F : CarriedStateFrame.LoopFrame stateCount) : Tape MachineCodeSymbol :=
  let L := (CarriedStateFrame.withFuel (fuel + 1) F).physicalFrame
  CyclicDriverIntegration.roundTripTape
    (SerializedHeadDispatch.failureConfig (stateCount := stateCount)
      (HeadLocator.gateTape (Frame.protectedWord L callerData))).tape

theorem missingTargetTape_represents {stateCount : Nat}
    (callerData : Word MachineCodeSymbol) (fuel : Nat)
    (F : CarriedStateFrame.LoopFrame stateCount) :
    RelationalDriverInduction.Represents callerData (fuel + 1) F
      (missingTargetTape callerData fuel F) := by
  let L := (CarriedStateFrame.withFuel (fuel + 1) F).physicalFrame
  let word := Frame.protectedWord L callerData
  let gate := HeadLocator.gateTape word
  have houter : Tape.Equiv
      (CyclicDriverIntegration.roundTripTape
        (SerializedHeadDispatch.failureConfig (stateCount := stateCount)
          gate).tape)
      (SerializedHeadDispatch.failureConfig (stateCount := stateCount)
        gate).tape := by
    exact ExactFuel.StrictProbe.Machine.moveLeft_moveRight_equiv_self _
  have hinner : Tape.Equiv
      (SerializedHeadDispatch.failureConfig (stateCount := stateCount)
        gate).tape gate := by
    exact SerializedHeadDispatch.roundTripTape_equiv gate
  have hgate : Tape.Equiv gate (Tape.input word) := by
    exact ExactFuel.StrictProbe.Update.LeftKernel.headLocator_gateTape_equiv_input
      word
  simpa [RelationalDriverInduction.Represents, missingTargetTape,
    L, word, gate] using
      Tape.Equiv.trans houter (Tape.Equiv.trans hinner hgate)

theorem succ_missing_with_rep {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (callerData : Word MachineCodeSymbol)
    (fuel : Nat) (F : CarriedStateFrame.LoopFrame stateCount)
    (T : Tape MachineCodeSymbol)
    (hrep : RelationalDriverInduction.Represents
      callerData (fuel + 1) F T)
    (hmissing :
      selected.transition
          (RelationalDriverInduction.semanticConfig F).state
          (Tape.read (RelationalDriverInduction.semanticConfig F).tape) =
        none) :
    exists endpointTape,
      RelationalDriverInduction.Represents
          callerData (fuel + 1) F endpointTape ∧
        TuringMachine.Computes (probeMachine selected)
          (CyclicRelationalContract.sourceConfig (fuel + 1) F T)
          (CyclicRelationalContract.rejectConfig endpointTape) := by
  have hcanonical := CyclicDriverIntegration.succ_missing_run_exact
    selected (Kernel stateCount) fuel F callerData (by
      simpa [CyclicDriverIntegration.semanticConfig,
        RelationalDriverInduction.semanticConfig] using hmissing)
  have hsourceEquiv : Tape.Equiv
      (CyclicDriverWitnesses.canonicalTape callerData (fuel + 1) F) T := by
    simpa [CyclicDriverWitnesses.canonicalTape,
      RelationalDriverInduction.Represents] using Tape.Equiv.symm hrep
  let L := (CarriedStateFrame.withFuel (fuel + 1) F).physicalFrame
  let steps := 4 + ((HeadLocator.locatorSteps L + 2) + 2)
  have hcanonical' :
      (probeMachine selected).runConfigExact? steps
          (CyclicRelationalContract.sourceConfig (fuel + 1) F
            (CyclicDriverWitnesses.canonicalTape
              callerData (fuel + 1) F)) =
        some (CyclicRelationalContract.rejectConfig
          (missingTargetTape callerData fuel F)) := by
    simpa [probeMachine, steps, L,
      CyclicRelationalContract.sourceConfig,
      CyclicRelationalContract.rejectConfig,
      CyclicDriverIntegration.loopSourceConfig,
      CyclicDriverIntegration.gateConfig,
      CarriedFuelGate.sourceConfig,
      CyclicDriverWitnesses.canonicalTape,
      missingTargetTape] using hcanonical
  rcases TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
      hcanonical' hsourceEquiv with ⟨endpoint, hrun, hstate, hequiv⟩
  cases endpoint with
  | mk endpointState endpointTape =>
      change endpointState = CyclicDriverIntegration.Control.reject at hstate
      subst endpointState
      refine ⟨endpointTape, ?_, ?_⟩
      · exact RelationalDriverInduction.represents_of_equiv
          (Tape.Equiv.symm hequiv)
          (missingTargetTape_represents callerData fuel F)
      · have hcomputes := TuringMachine.computesIn_to_computes
          (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hrun)
        simpa [CyclicRelationalContract.sourceConfig,
          CyclicRelationalContract.rejectConfig] using hcomputes

theorem cyclic_reject_with_rep_of_not_halts {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (callerData : Word MachineCodeSymbol) :
    forall fuel (F : CarriedStateFrame.LoopFrame stateCount)
      (T : Tape MachineCodeSymbol),
      RelationalDriverInduction.Represents callerData fuel F T →
      ¬ TuringMachine.HaltsFromIn selected fuel
          (RelationalDriverInduction.semanticConfig F) →
      exists remainingFuel,
      exists finalFrame : CarriedStateFrame.LoopFrame stateCount,
      exists endpointTape,
        RelationalDriverInduction.Represents
            callerData remainingFuel finalFrame endpointTape ∧
          TuringMachine.Computes (probeMachine selected)
            (CyclicRelationalContract.sourceConfig fuel F T)
            (CyclicRelationalContract.rejectConfig endpointTape) := by
  intro fuel
  induction fuel with
  | zero =>
      intro F T hrep hnot
      have hstate :
          (RelationalDriverInduction.semanticConfig F).state ≠
            selected.halt := by
        intro hhalt
        apply hnot
        exact TuringMachine.haltsFromIn_zero_iff.mpr hhalt
      rcases zero_reject_with_rep selected callerData F T hrep hstate with
        ⟨endpointTape, htargetRep, hrun⟩
      exact ⟨0, F, endpointTape, htargetRep, hrun⟩
  | succ fuel ih =>
      intro F T hrep hnot
      cases htransition :
          selected.transition
            (RelationalDriverInduction.semanticConfig F).state
            (Tape.read (RelationalDriverInduction.semanticConfig F).tape) with
      | none =>
          rcases succ_missing_with_rep selected callerData fuel F T hrep
              htransition with ⟨endpointTape, htargetRep, hrun⟩
          exact ⟨fuel + 1, F, endpointTape, htargetRep, hrun⟩
      | some action =>
          rcases action with ⟨write, direction, nextState⟩
          rcases CyclicDriverWitnesses.succPresent selected
              (Kernel stateCount) callerData
              (ExactFuel.StrictProbe.Update.Runs.selectedUpdateRuns
                selected callerData)
              fuel F T write direction nextState hrep htransition with
            ⟨T', hrep', hprefix⟩
          have hnotTail :
              ¬ TuringMachine.HaltsFromIn selected fuel
                (RelationalDriverInduction.semanticConfig
                  (CarriedStateFrame.afterSelected
                    fuel write direction nextState F)) := by
            intro htail
            apply hnot
            apply
              (TuringMachine.haltsFromIn_succ_iff_of_transition_eq_some
                htransition).mpr
            rw [RelationalDriverInduction.semanticConfig_afterSelected]
              at htail
            simpa [DriverInduction.selectedTarget] using htail
          rcases ih
              (CarriedStateFrame.afterSelected
                fuel write direction nextState F)
              T' hrep' hnotTail with
            ⟨remainingFuel, finalFrame, endpointTape,
              htargetRep, htail⟩
          exact ⟨remainingFuel, finalFrame, endpointTape,
            htargetRep, TuringMachine.computes_trans hprefix htail⟩

theorem candidate_miss_with_rep_of_not_exact {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (callerData input : Word MachineCodeSymbol)
    (inner outer selectedFuel : Nat)
    (hnot :
      ¬ TuringMachine.HaltsOnInputIn selected selectedFuel
          (GeneratedCode.nestedStageCode input inner outer)) :
    exists remainingFuel,
    exists finalFrame : CarriedStateFrame.LoopFrame stateCount,
    exists endpointTape,
      RelationalDriverInduction.Represents
          callerData remainingFuel finalFrame
          (CyclicDriverIntegration.roundTripTape endpointTape) ∧
        TuringMachine.Computes (machine selected)
          (candidateSource selected callerData input
            inner outer selectedFuel)
          (missConfig
            (CyclicDriverIntegration.roundTripTape endpointTape)) := by
  have hrep :
      RelationalDriverInduction.Represents callerData selectedFuel
        (candidateFrame selected input inner outer selectedFuel)
        (candidateTape selected callerData input inner outer selectedFuel) := by
    unfold candidateTape CyclicDriverWitnesses.canonicalTape
      RelationalDriverInduction.Represents
    exact Tape.Equiv.refl _
  have hnotSemantic :
      ¬ TuringMachine.HaltsFromIn selected selectedFuel
        (RelationalDriverInduction.semanticConfig
          (candidateFrame selected input inner outer selectedFuel)) := by
    intro hhalt
    apply hnot
    simpa [TuringMachine.HaltsOnInputIn, candidateFrame,
      ExactFuel.StrictProbe.StageRunner.initialFrame_semanticConfig]
      using hhalt
  rcases cyclic_reject_with_rep_of_not_halts selected callerData
      selectedFuel
      (candidateFrame selected input inner outer selectedFuel)
      (candidateTape selected callerData input inner outer selectedFuel)
      hrep hnotSemantic with
    ⟨remainingFuel, finalFrame, endpointTape, htargetRep, hreject⟩
  have hrejectOuter := probe_computes_lift selected hreject
  refine ⟨remainingFuel, finalFrame, endpointTape,
    roundTrip_represents htargetRep, ?_⟩
  simpa [candidateSource] using
    TuringMachine.computes_trans hrejectOuter
      (reject_to_miss_computes selected endpointTape)

theorem candidate_miss_recovers_caller_of_not_exact {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (callerData input : Word MachineCodeSymbol)
    (inner outer selectedFuel : Nat)
    (hnot :
      ¬ TuringMachine.HaltsOnInputIn selected selectedFuel
          (GeneratedCode.nestedStageCode input inner outer)) :
    exists remainingFuel,
    exists finalFrame : CarriedStateFrame.LoopFrame stateCount,
    exists endpointTape,
    exists recoveryEndpoint : TuringMachine.Configuration MachineCodeSymbol
        ExactFuel.StrictProbe.ProductHandoff.Control,
      RelationalDriverInduction.Represents
          callerData remainingFuel finalFrame
          (CyclicDriverIntegration.roundTripTape endpointTape) ∧
        TuringMachine.Computes (machine selected)
          (candidateSource selected callerData input
            inner outer selectedFuel)
          (missConfig
            (CyclicDriverIntegration.roundTripTape endpointTape)) ∧
        ExactFuel.StrictProbe.ProductHandoff.machine.runConfigExact?
            ((ExactFuel.Layout.encode
              (CarriedStateFrame.withFuel
                remainingFuel finalFrame).physicalFrame).length + 1)
            { state := .scan,
              tape := CyclicDriverIntegration.roundTripTape endpointTape } =
          some recoveryEndpoint ∧
        recoveryEndpoint.state = .gate ∧
        Tape.Equiv recoveryEndpoint.tape (Tape.input callerData) ∧
        Tape.read recoveryEndpoint.tape =
          Tape.read (Tape.input callerData) ∧
        Tape.normalizedOutput recoveryEndpoint.tape = callerData := by
  rcases candidate_miss_with_rep_of_not_exact selected callerData input
      inner outer selectedFuel hnot with
    ⟨remainingFuel, finalFrame, endpointTape, htargetRep, hmiss⟩
  rcases ExactFuel.StrictProbe.ProductHandoff.run_from_representation
      callerData remainingFuel finalFrame
      (CyclicDriverIntegration.roundTripTape endpointTape) htargetRep with
    ⟨recoveryEndpoint, hrecovery, hgate, hcaller⟩
  exact ⟨remainingFuel, finalFrame, endpointTape, recoveryEndpoint,
    htargetRep, hmiss, hrecovery, hgate, hcaller,
    recoveredCaller_read_eq hcaller,
    recoveredCaller_normalizedOutput_eq hcaller⟩


end Recovery

end FoC.Computability.FiniteRecognizer.TupleSearch.CandidateKernel.ProbeReturn
