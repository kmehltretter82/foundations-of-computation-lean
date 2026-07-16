import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.Composition
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PrefixHalting

set_option doc.verso true

/-!
# Product phase inversion

Invert public product halting through the prefix, left probe, protected-frame
handoff, and right probe to recover both exact-fuel predicates.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace ProductInversion

open ProductComposition

section

variable {materializerState : Type} [DecidableEq materializerState]
variable {leftCount rightCount : Nat}
variable {leftUpdateState rightUpdateState : Type}
variable [DecidableEq leftUpdateState] [DecidableEq rightUpdateState]

variable (materializer : TuringMachine MachineCodeSymbol materializerState)
variable (left : TuringMachine MachineCodeSymbol (Fin leftCount))
variable (right : TuringMachine MachineCodeSymbol (Fin rightCount))
variable (leftKernel :
  CyclicDriverIntegration.UpdateKernel leftCount leftUpdateState)
variable (rightKernel :
  CyclicDriverIntegration.UpdateKernel rightCount rightUpdateState)

theorem outer_haltingTransitionsDisabled :
    TuringMachine.HaltingTransitionsDisabled
      (outerMachine materializer left right leftKernel rightKernel) := by
  intro read
  rfl

theorem not_outer_haltsFrom_of_left_failure
    (callerData : Word MachineCodeSymbol)
    (leftWitnesses :
      CyclicRelationalContract.CyclicRunWitnesses left leftKernel callerData)
    (fuel : Nat)
    (F : SerializedFieldComposer.CarriedStateFrame.LoopFrame leftCount)
    (T : Tape MachineCodeSymbol)
    (hrep :
      RelationalDriverInduction.Represents callerData fuel F T)
    (hfailure :
      ¬ TuringMachine.HaltsFromIn left fuel
        (RelationalDriverInduction.semanticConfig F)) :
    ¬ TuringMachine.HaltsFrom
      (outerMachine materializer left right leftKernel rightKernel)
      (TuringMachine.PhaseEmbedding.liftConfig
        (ProductAssembly.embedLeft
          (materializerState := materializerState)
          (rightCount := rightCount)
          (rightUpdateState := rightUpdateState))
        (CyclicRelationalContract.sourceConfig fuel F T)) := by
  intro houter
  let D := CyclicRelationalContract.runContract left leftKernel
    callerData leftWitnesses
  rcases RelationalDriverInduction.total_run D fuel F T hrep with
    hsuccess | hfailed
  · exact hfailure hsuccess.left
  · rcases hfailed.right with
      ⟨endpoint, hrun, hnotHalted, hstuck⟩
    have hrun' :
        TuringMachine.Computes
          (CyclicDriverIntegration.machine left leftKernel)
          (CyclicRelationalContract.sourceConfig fuel F T) endpoint := by
      simpa [D, CyclicRelationalContract.runContract] using hrun
    have hrunOuter :=
      left_computes_lift materializer left right leftKernel rightKernel hrun'
    have hstate : endpoint.state ≠ CyclicDriverIntegration.Control.accept := by
      simpa [TuringMachine.Halted, CyclicDriverIntegration.machine] using
        hnotHalted
    have hinnerNone :
        (CyclicDriverIntegration.machine left leftKernel).transition
          endpoint.state endpoint.tape.read = none := by
      cases htransition :
          (CyclicDriverIntegration.machine left leftKernel).transition
            endpoint.state endpoint.tape.read with
      | none => rfl
      | some action =>
          rcases action with ⟨write, direction, nextState⟩
          exact False.elim
            (hstuck
              { state := nextState,
                tape := Tape.move direction
                  (Tape.write write endpoint.tape) }
              (TuringMachine.Step.mk htransition))
    have hinnerTransitionNone :
        CyclicDriverIntegration.transition left leftKernel endpoint.state
          endpoint.tape.read = none := by
      simpa [CyclicDriverIntegration.machine] using hinnerNone
    have houterNone :
        (outerMachine materializer left right leftKernel rightKernel).transition
          (ProductAssembly.embedLeft
            (materializerState := materializerState)
            (rightCount := rightCount)
            (rightUpdateState := rightUpdateState) endpoint.state)
          endpoint.tape.read = none := by
      rw [embedLeft_eq_left_of_ne_accept
        (materializerState := materializerState)
        (rightCount := rightCount)
        (rightUpdateState := rightUpdateState) endpoint.state hstate]
      simp [outerMachine, ProductAssembly.machine,
        ProductAssembly.transition,
        ProductAssembly.mapAction,
        ProductAssembly.leftControl,
        hinnerTransitionNone]
    have houterNotHalted :
        ¬ TuringMachine.Halted
          (outerMachine materializer left right leftKernel rightKernel)
          (TuringMachine.PhaseEmbedding.liftConfig
            (ProductAssembly.embedLeft
              (materializerState := materializerState)
              (rightCount := rightCount)
              (rightUpdateState := rightUpdateState)) endpoint) := by
      simp [TuringMachine.Halted, outerMachine,
        ProductAssembly.machine,
        TuringMachine.PhaseEmbedding.liftConfig,
        embedLeft_eq_left_of_ne_accept
          (materializerState := materializerState)
          (rightCount := rightCount)
          (rightUpdateState := rightUpdateState) endpoint.state hstate,
        ProductAssembly.leftControl,
        ProductAssembly.rightControl]
    have houterStuck :
        forall next,
          ¬ TuringMachine.Step
            (outerMachine materializer left right leftKernel rightKernel)
            (TuringMachine.PhaseEmbedding.liftConfig
              (ProductAssembly.embedLeft
                (materializerState := materializerState)
                (rightCount := rightCount)
                (rightUpdateState := rightUpdateState)) endpoint)
            next := by
      intro next
      apply TuringMachine.not_step_of_transition_eq_none
      simpa [TuringMachine.PhaseEmbedding.liftConfig] using houterNone
    exact
      (TuringMachine.StuckSink.not_haltsFrom_of_computes_to_stuck_nonhalt
        (outer_haltingTransitionsDisabled materializer left right leftKernel
          rightKernel)
        hrunOuter houterNotHalted houterStuck) houter

theorem pair_of_haltsFrom
    (input : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat)
    (leftWitnesses :
      CyclicRelationalContract.CyclicRunWitnesses left leftKernel
        (Frame.protectedWord (Layout.initial right input rightFuel) []))
    (rightWitnesses :
      CyclicRelationalContract.CyclicRunWitnesses right rightKernel [])
    (pairPrefix : PairPrefixWitness materializer left right
      input leftFuel rightFuel)
    (houter :
      TuringMachine.HaltsFrom
        (outerMachine materializer left right leftKernel rightKernel)
        (TuringMachine.PhaseEmbedding.liftConfig
          (ProductAssembly.embedMaterializer
            (rightCount := rightCount)
            (leftUpdateState := leftUpdateState)
            (rightUpdateState := rightUpdateState)
            materializer left) pairPrefix.source)) :
    TuringMachine.HaltsFromIn left leftFuel
          (RelationalDriverInduction.semanticConfig
            (SerializedFieldComposer.CarriedStateFrame.ofParsed
              (Layout.initial left input leftFuel))) ∧
      TuringMachine.HaltsFromIn right rightFuel
          (RelationalDriverInduction.semanticConfig
            (SerializedFieldComposer.CarriedStateFrame.ofParsed
              (Layout.initial right input rightFuel))) := by
  let rightData :=
    Frame.protectedWord (Layout.initial right input rightFuel) []
  let leftFrame :=
    SerializedFieldComposer.CarriedStateFrame.ofParsed
      (Layout.initial left input leftFuel)
  let rightFrame :=
    SerializedFieldComposer.CarriedStateFrame.ofParsed
      (Layout.initial right input rightFuel)
  have hmaterializer := materializer_computes_lift materializer left right
    leftKernel rightKernel pairPrefix.haltingTransitionsDisabled pairPrefix.run
  have hstop := outer_haltingTransitionsDisabled materializer left right
    leftKernel rightKernel
  have hafterMaterializer :=
    (TuringMachine.PrefixHalting.haltsFrom_iff_of_computes
      hstop hmaterializer).mp houter
  have hleftOuterHalts :
      TuringMachine.HaltsFrom
        (outerMachine materializer left right leftKernel rightKernel)
        (TuringMachine.PhaseEmbedding.liftConfig
          (ProductAssembly.embedLeft
            (materializerState := materializerState)
            (rightCount := rightCount)
            (rightUpdateState := rightUpdateState))
          (CyclicRelationalContract.sourceConfig leftFuel leftFrame
            pairPrefix.targetTape)) := by
    simpa [CyclicRelationalContract.sourceConfig,
      ProductAssembly.embedMaterializer,
      ProductAssembly.embedLeft,
      ProductAssembly.leftControl,
      leftFrame, SerializedFieldComposer.CarriedStateFrame.ofParsed,
      Layout.initial, Layout.ofConfig, TuringMachine.initial,
      TuringMachine.PhaseEmbedding.liftConfig] using hafterMaterializer
  have hleftRep :
      RelationalDriverInduction.Represents rightData leftFuel leftFrame
        pairPrefix.targetTape := by
    simpa [rightData, leftFrame] using pairPrefix.leftRepresents
  have hleftExact :
      TuringMachine.HaltsFromIn left leftFuel
        (RelationalDriverInduction.semanticConfig leftFrame) := by
    by_cases hsuccess :
        TuringMachine.HaltsFromIn left leftFuel
          (RelationalDriverInduction.semanticConfig leftFrame)
    · exact hsuccess
    · exact False.elim
        ((not_outer_haltsFrom_of_left_failure materializer left right
          leftKernel rightKernel rightData
          (by simpa [rightData] using leftWitnesses)
          leftFuel leftFrame pairPrefix.targetTape hleftRep hsuccess)
          hleftOuterHalts)
  rcases ProductSuccess.success_endpoint_of_witnesses
      left leftKernel rightData
      (by simpa [rightData] using leftWitnesses)
      leftFuel leftFrame pairPrefix.targetTape hleftRep hleftExact with
    ⟨leftEndpointFrame, leftEndpointTape,
      hleftEndpointRep, hleftRun⟩
  have hleftOuterRun := left_computes_lift materializer left right leftKernel
    rightKernel hleftRun
  have hafterLeft :=
    (TuringMachine.PrefixHalting.haltsFrom_iff_of_computes
      hstop hleftOuterRun).mp hleftOuterHalts
  rcases ProductHandoff.run_from_representation rightData 0
      leftEndpointFrame leftEndpointTape hleftEndpointRep with
    ⟨handoffEndpoint, hhandoffExact, hhandoffState,
      hrightTapeEquiv⟩
  have hhandoffRun :
      TuringMachine.Computes ProductHandoff.machine
        { state := ProductHandoff.Control.scan,
          tape := leftEndpointTape }
        handoffEndpoint :=
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
        hhandoffExact)
  have hhandoffOuterRun := handoff_computes_lift materializer left right
    leftKernel rightKernel hhandoffRun
  have hhandoffSourceHalts :
      TuringMachine.HaltsFrom
        (outerMachine materializer left right leftKernel rightKernel)
        (TuringMachine.PhaseEmbedding.liftConfig
          (ProductAssembly.embedHandoff
            (materializerState := materializerState)
            (leftCount := leftCount)
            (leftUpdateState := leftUpdateState)
            (rightUpdateState := rightUpdateState) right)
          { state := ProductHandoff.Control.scan,
            tape := leftEndpointTape }) := by
    simpa [CyclicRelationalContract.acceptConfig,
      ProductAssembly.embedLeft,
      ProductAssembly.embedHandoff,
      ProductAssembly.handoffControl,
      TuringMachine.PhaseEmbedding.liftConfig] using hafterLeft
  have hafterHandoff :=
    (TuringMachine.PrefixHalting.haltsFrom_iff_of_computes
      hstop hhandoffOuterRun).mp hhandoffSourceHalts
  have hrightRep :
      RelationalDriverInduction.Represents ([] : Word MachineCodeSymbol)
        rightFuel rightFrame handoffEndpoint.tape := by
    unfold RelationalDriverInduction.Represents
    simpa [rightData, rightFrame,
      SerializedFieldComposer.CarriedStateFrame.withFuel,
      SerializedFieldComposer.CarriedStateFrame.ofParsed,
      SerializedFieldComposer.FuelDecrementMachine.withFuel,
      Layout.initial, Layout.ofConfig] using hrightTapeEquiv
  have hrightOuterHalts :
      TuringMachine.HaltsFrom
        (outerMachine materializer left right leftKernel rightKernel)
        (TuringMachine.PhaseEmbedding.liftConfig
          (ProductAssembly.embedRight
            (materializerState := materializerState)
            (leftCount := leftCount)
            (leftUpdateState := leftUpdateState))
          (CyclicRelationalContract.sourceConfig rightFuel rightFrame
            handoffEndpoint.tape)) := by
    cases handoffEndpoint with
    | mk handoffState handoffTape =>
        change handoffState = ProductHandoff.Control.gate at hhandoffState
        subst handoffState
        simpa [CyclicRelationalContract.sourceConfig,
          ProductAssembly.embedHandoff,
          ProductAssembly.embedRight,
          ProductAssembly.rightControl,
          rightFrame, SerializedFieldComposer.CarriedStateFrame.ofParsed,
          Layout.initial, Layout.ofConfig, TuringMachine.initial,
          TuringMachine.PhaseEmbedding.liftConfig] using hafterHandoff
  have hrightInnerHalts :
      TuringMachine.HaltsFrom
        (CyclicDriverIntegration.machine right rightKernel)
        (CyclicRelationalContract.sourceConfig rightFuel rightFrame
          handoffEndpoint.tape) :=
    (right_haltsFrom_iff materializer left right leftKernel rightKernel
      (CyclicRelationalContract.sourceConfig rightFuel rightFrame
        handoffEndpoint.tape)).mp hrightOuterHalts
  have hrightExact :
      TuringMachine.HaltsFromIn right rightFuel
        (RelationalDriverInduction.semanticConfig rightFrame) :=
    (CyclicRelationalContract.haltsFrom_source_iff
      right rightKernel ([] : Word MachineCodeSymbol) rightWitnesses
      rightFuel rightFrame handoffEndpoint.tape hrightRep).mp
      hrightInnerHalts
  exact ⟨by simpa [leftFrame] using hleftExact,
    by simpa [rightFrame] using hrightExact⟩

theorem haltsFrom_iff_pair
    (input : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat)
    (leftWitnesses :
      CyclicRelationalContract.CyclicRunWitnesses left leftKernel
        (Frame.protectedWord (Layout.initial right input rightFuel) []))
    (rightWitnesses :
      CyclicRelationalContract.CyclicRunWitnesses right rightKernel [])
    (pairPrefix : PairPrefixWitness materializer left right
      input leftFuel rightFuel) :
    TuringMachine.HaltsFrom
        (outerMachine materializer left right leftKernel rightKernel)
        (TuringMachine.PhaseEmbedding.liftConfig
          (ProductAssembly.embedMaterializer
            (rightCount := rightCount)
            (leftUpdateState := leftUpdateState)
            (rightUpdateState := rightUpdateState)
            materializer left) pairPrefix.source) ↔
      TuringMachine.HaltsFromIn left leftFuel
          (RelationalDriverInduction.semanticConfig
            (SerializedFieldComposer.CarriedStateFrame.ofParsed
              (Layout.initial left input leftFuel))) ∧
        TuringMachine.HaltsFromIn right rightFuel
          (RelationalDriverInduction.semanticConfig
            (SerializedFieldComposer.CarriedStateFrame.ofParsed
              (Layout.initial right input rightFuel))) := by
  constructor
  · exact pair_of_haltsFrom materializer left right leftKernel rightKernel
      input leftFuel rightFuel leftWitnesses rightWitnesses pairPrefix
  · intro hpair
    exact haltsFrom_of_pair materializer left right leftKernel rightKernel
      input leftFuel rightFuel leftWitnesses rightWitnesses pairPrefix
      hpair.1 hpair.2

end


end ProductInversion
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
