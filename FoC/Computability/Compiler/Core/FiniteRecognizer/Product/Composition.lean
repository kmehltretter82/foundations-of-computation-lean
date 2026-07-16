import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.Assembly
import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.Success

set_option doc.verso true

/-!
# Product phase composition

Lift exact runs through the assembled product control and compose successful
materialization, left-probe, handoff, and right-probe executions.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace ProductComposition

theorem computes_lift_active
    {inner : TuringMachine symbol innerState}
    {outer : TuringMachine symbol outerState}
    (embed : innerState -> outerState)
    (hstep : forall
      (c d : TuringMachine.Configuration symbol innerState),
      inner.stepConfig c = some d ->
        outer.stepConfig
            (TuringMachine.PhaseEmbedding.liftConfig embed c) =
          some (TuringMachine.PhaseEmbedding.liftConfig embed d))
    {source target : TuringMachine.Configuration symbol innerState}
    (hrun : TuringMachine.Computes inner source target) :
    TuringMachine.Computes outer
      (TuringMachine.PhaseEmbedding.liftConfig embed source)
      (TuringMachine.PhaseEmbedding.liftConfig embed target) := by
  rcases TuringMachine.computes_to_computesIn hrun with
    ⟨steps, hrunIn⟩
  apply TuringMachine.computesIn_to_computes
  apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
  apply TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    embed hstep
  exact TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr hrunIn

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

abbrev outerMachine :=
  ProductAssembly.machine materializer left right
    leftKernel rightKernel

abbrev leftMachine := CyclicDriverIntegration.machine left leftKernel

abbrev rightMachine := CyclicDriverIntegration.machine right rightKernel

theorem right_stepConfig
    (c : TuringMachine.Configuration MachineCodeSymbol
      (CyclicDriverIntegration.Control rightCount rightUpdateState)) :
    (outerMachine materializer left right leftKernel rightKernel).stepConfig
        (TuringMachine.PhaseEmbedding.liftConfig
          ProductAssembly.embedRight c) =
      Option.map
        (TuringMachine.PhaseEmbedding.liftConfig
          ProductAssembly.embedRight)
        ((rightMachine right rightKernel).stepConfig c) := by
  cases c with
  | mk state tape =>
      cases haction :
          CyclicDriverIntegration.transition right rightKernel state tape.read with
      | none =>
          simp [outerMachine, rightMachine, TuringMachine.stepConfig,
            CyclicDriverIntegration.machine,
            ProductAssembly.machine,
            ProductAssembly.transition,
            ProductAssembly.mapAction,
            ProductAssembly.embedRight,
            ProductAssembly.rightControl,
            TuringMachine.PhaseEmbedding.liftConfig, haction]
      | some action =>
          rcases action with ⟨write, direction, target⟩
          simp [outerMachine, rightMachine, TuringMachine.stepConfig,
            CyclicDriverIntegration.machine,
            ProductAssembly.machine,
            ProductAssembly.transition,
            ProductAssembly.mapAction,
            ProductAssembly.embedRight,
            ProductAssembly.rightControl,
            TuringMachine.PhaseEmbedding.liftConfig, haction]

theorem right_runConfigExact?_lift
    (steps : Nat)
    (c : TuringMachine.Configuration MachineCodeSymbol
      (CyclicDriverIntegration.Control rightCount rightUpdateState)) :
    (outerMachine materializer left right leftKernel rightKernel).runConfigExact?
        steps
        (TuringMachine.PhaseEmbedding.liftConfig
          ProductAssembly.embedRight c) =
      Option.map
        (TuringMachine.PhaseEmbedding.liftConfig
          ProductAssembly.embedRight)
        ((rightMachine right rightKernel).runConfigExact? steps c) := by
  exact TuringMachine.PhaseEmbedding.runConfigExact?_lift
    ProductAssembly.embedRight
    (right_stepConfig materializer left right leftKernel rightKernel)
    steps c

theorem right_computes_lift
    {source target : TuringMachine.Configuration MachineCodeSymbol
      (CyclicDriverIntegration.Control rightCount rightUpdateState)}
    (hrun : TuringMachine.Computes (rightMachine right rightKernel)
      source target) :
    TuringMachine.Computes
      (outerMachine materializer left right leftKernel rightKernel)
      (TuringMachine.PhaseEmbedding.liftConfig
        ProductAssembly.embedRight source)
      (TuringMachine.PhaseEmbedding.liftConfig
        ProductAssembly.embedRight target) := by
  exact TuringMachine.PhaseEmbedding.computes_lift
    ProductAssembly.embedRight
    (right_stepConfig materializer left right leftKernel rightKernel)
    hrun

theorem right_haltsFrom_iff
    (c : TuringMachine.Configuration MachineCodeSymbol
      (CyclicDriverIntegration.Control rightCount rightUpdateState)) :
    TuringMachine.HaltsFrom
        (outerMachine materializer left right leftKernel rightKernel)
        (TuringMachine.PhaseEmbedding.liftConfig
          ProductAssembly.embedRight c) <->
      TuringMachine.HaltsFrom (rightMachine right rightKernel) c := by
  constructor
  · intro houter
    rcases houter with ⟨outerFinal, houterRun, houterHalted⟩
    rcases TuringMachine.computes_to_computesIn houterRun with
      ⟨steps, houterRunIn⟩
    have houterExact :=
      TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr houterRunIn
    have hlift := right_runConfigExact?_lift materializer left right
      leftKernel rightKernel steps c
    rw [houterExact] at hlift
    cases hinnerExact :
        (rightMachine right rightKernel).runConfigExact? steps c with
    | none =>
        simp [hinnerExact] at hlift
    | some innerFinal =>
        simp only [hinnerExact, Option.map] at hlift
        cases hlift
        refine ⟨innerFinal, ?_, ?_⟩
        · exact TuringMachine.computesIn_to_computes
            (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
              hinnerExact)
        · simpa [TuringMachine.Halted, outerMachine, rightMachine,
            ProductAssembly.machine,
            ProductAssembly.embedRight,
            ProductAssembly.rightControl,
            TuringMachine.PhaseEmbedding.liftConfig,
            CyclicDriverIntegration.machine] using houterHalted
  · intro hinner
    rcases hinner with ⟨innerFinal, hinnerRun, hinnerHalted⟩
    refine ⟨
      TuringMachine.PhaseEmbedding.liftConfig
        ProductAssembly.embedRight innerFinal,
      right_computes_lift materializer left right leftKernel rightKernel
        hinnerRun, ?_⟩
    simpa [TuringMachine.Halted, outerMachine, rightMachine,
      ProductAssembly.machine,
      ProductAssembly.embedRight,
      ProductAssembly.rightControl,
      TuringMachine.PhaseEmbedding.liftConfig,
      CyclicDriverIntegration.machine] using hinnerHalted

theorem materializer_step_active
    (hdisabled : TuringMachine.HaltingTransitionsDisabled materializer)
    (c d : TuringMachine.Configuration MachineCodeSymbol materializerState)
    (hstep : materializer.stepConfig c = some d) :
    (outerMachine materializer left right leftKernel rightKernel).stepConfig
        (TuringMachine.PhaseEmbedding.liftConfig
          (ProductAssembly.embedMaterializer
            (rightCount := rightCount)
            (leftUpdateState := leftUpdateState)
            (rightUpdateState := rightUpdateState)
            materializer left) c) =
      some
        (TuringMachine.PhaseEmbedding.liftConfig
          (ProductAssembly.embedMaterializer
            (rightCount := rightCount)
            (leftUpdateState := leftUpdateState)
            (rightUpdateState := rightUpdateState)
            materializer left) d) := by
  cases c with
  | mk sourceState sourceTape =>
      cases d with
      | mk targetState targetTape =>
          cases haction :
              materializer.transition sourceState sourceTape.read with
          | none =>
              simp [TuringMachine.stepConfig, haction] at hstep
          | some action =>
              rcases action with ⟨write, direction, nextState⟩
              simp [TuringMachine.stepConfig, haction] at hstep
              cases hstep
              have hsource : sourceState ≠ materializer.halt := by
                intro heq
                subst sourceState
                rw [hdisabled sourceTape.read] at haction
                contradiction
              simp_all [outerMachine, TuringMachine.stepConfig,
                ProductAssembly.machine,
                ProductAssembly.transition,
                ProductAssembly.mapAction,
                ProductAssembly.embedMaterializer,
                ProductAssembly.materializerControl,
                ProductAssembly.leftControl,
                TuringMachine.PhaseEmbedding.liftConfig]

theorem materializer_runConfigExact?_lift
    (hdisabled : TuringMachine.HaltingTransitionsDisabled materializer)
    {steps : Nat}
    {source target :
      TuringMachine.Configuration MachineCodeSymbol materializerState}
    (hrun : materializer.runConfigExact? steps source = some target) :
    (outerMachine materializer left right leftKernel rightKernel).runConfigExact?
        steps
        (TuringMachine.PhaseEmbedding.liftConfig
          (ProductAssembly.embedMaterializer
            (rightCount := rightCount)
            (leftUpdateState := leftUpdateState)
            (rightUpdateState := rightUpdateState)
            materializer left) source) =
      some
        (TuringMachine.PhaseEmbedding.liftConfig
          (ProductAssembly.embedMaterializer
            (rightCount := rightCount)
            (leftUpdateState := leftUpdateState)
            (rightUpdateState := rightUpdateState)
            materializer left) target) := by
  exact
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      _ (materializer_step_active materializer left right leftKernel
        rightKernel hdisabled) hrun

theorem materializer_computes_lift
    (hdisabled : TuringMachine.HaltingTransitionsDisabled materializer)
    {source target :
      TuringMachine.Configuration MachineCodeSymbol materializerState}
    (hrun : TuringMachine.Computes materializer source target) :
    TuringMachine.Computes
      (outerMachine materializer left right leftKernel rightKernel)
      (TuringMachine.PhaseEmbedding.liftConfig
        (ProductAssembly.embedMaterializer
          (rightCount := rightCount)
          (leftUpdateState := leftUpdateState)
          (rightUpdateState := rightUpdateState)
          materializer left) source)
      (TuringMachine.PhaseEmbedding.liftConfig
        (ProductAssembly.embedMaterializer
          (rightCount := rightCount)
          (leftUpdateState := leftUpdateState)
          (rightUpdateState := rightUpdateState)
          materializer left) target) := by
  exact computes_lift_active _
    (materializer_step_active materializer left right leftKernel rightKernel
      hdisabled) hrun

omit [DecidableEq materializerState] [DecidableEq leftUpdateState]
    [DecidableEq rightUpdateState] in
theorem embedLeft_eq_left_of_ne_accept
    (state : CyclicDriverIntegration.Control leftCount leftUpdateState)
    (hstate : state ≠ .accept) :
    ProductAssembly.embedLeft
        (materializerState := materializerState)
        (rightCount := rightCount)
        (rightUpdateState := rightUpdateState) state =
      ProductAssembly.leftControl state := by
  cases state <;> simp_all [ProductAssembly.embedLeft,
    ProductAssembly.leftControl]

theorem left_step_active
    (c d : TuringMachine.Configuration MachineCodeSymbol
      (CyclicDriverIntegration.Control leftCount leftUpdateState))
    (hstep : (leftMachine left leftKernel).stepConfig c = some d) :
    (outerMachine materializer left right leftKernel rightKernel).stepConfig
        (TuringMachine.PhaseEmbedding.liftConfig
          (ProductAssembly.embedLeft
            (materializerState := materializerState)
            (rightCount := rightCount)
            (rightUpdateState := rightUpdateState)) c) =
      some
        (TuringMachine.PhaseEmbedding.liftConfig
          (ProductAssembly.embedLeft
            (materializerState := materializerState)
            (rightCount := rightCount)
            (rightUpdateState := rightUpdateState)) d) := by
  cases c with
  | mk sourceState sourceTape =>
      cases d with
      | mk targetState targetTape =>
          cases haction :
              CyclicDriverIntegration.transition left leftKernel sourceState
                sourceTape.read with
          | none =>
              simp [leftMachine, CyclicDriverIntegration.machine,
                TuringMachine.stepConfig, haction] at hstep
          | some action =>
              rcases action with ⟨write, direction, nextState⟩
              simp [leftMachine, CyclicDriverIntegration.machine,
                TuringMachine.stepConfig, haction] at hstep
              cases hstep
              have hsource : sourceState ≠ .accept := by
                intro heq
                subst sourceState
                have hnone :=
                  CyclicDriverIntegration.machine_haltingTransitionsDisabled
                    left leftKernel sourceTape.read
                simp [CyclicDriverIntegration.machine] at hnone
                rw [hnone] at haction
                contradiction
              simp only [TuringMachine.PhaseEmbedding.liftConfig]
              rw [embedLeft_eq_left_of_ne_accept
                (materializerState := materializerState)
                (rightCount := rightCount)
                (rightUpdateState := rightUpdateState)
                sourceState hsource]
              simp_all [outerMachine, TuringMachine.stepConfig,
                ProductAssembly.machine,
                ProductAssembly.transition,
                ProductAssembly.mapAction,
                ProductAssembly.leftControl]

theorem left_runConfigExact?_lift
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      (CyclicDriverIntegration.Control leftCount leftUpdateState)}
    (hrun : (leftMachine left leftKernel).runConfigExact? steps source =
      some target) :
    (outerMachine materializer left right leftKernel rightKernel).runConfigExact?
        steps
        (TuringMachine.PhaseEmbedding.liftConfig
          (ProductAssembly.embedLeft
            (materializerState := materializerState)
            (rightCount := rightCount)
            (rightUpdateState := rightUpdateState)) source) =
      some
        (TuringMachine.PhaseEmbedding.liftConfig
          (ProductAssembly.embedLeft
            (materializerState := materializerState)
            (rightCount := rightCount)
            (rightUpdateState := rightUpdateState)) target) := by
  exact
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      _ (left_step_active materializer left right leftKernel rightKernel) hrun

theorem left_computes_lift
    {source target : TuringMachine.Configuration MachineCodeSymbol
      (CyclicDriverIntegration.Control leftCount leftUpdateState)}
    (hrun : TuringMachine.Computes (leftMachine left leftKernel)
      source target) :
    TuringMachine.Computes
      (outerMachine materializer left right leftKernel rightKernel)
      (TuringMachine.PhaseEmbedding.liftConfig
        (ProductAssembly.embedLeft
          (materializerState := materializerState)
          (rightCount := rightCount)
          (rightUpdateState := rightUpdateState)) source)
      (TuringMachine.PhaseEmbedding.liftConfig
        (ProductAssembly.embedLeft
          (materializerState := materializerState)
          (rightCount := rightCount)
          (rightUpdateState := rightUpdateState)) target) := by
  exact computes_lift_active _
    (left_step_active materializer left right leftKernel rightKernel) hrun

theorem handoff_step_active
    (c d : TuringMachine.Configuration MachineCodeSymbol
      ProductHandoff.Control)
    (hstep : ProductHandoff.machine.stepConfig c = some d) :
    (outerMachine materializer left right leftKernel rightKernel).stepConfig
        (TuringMachine.PhaseEmbedding.liftConfig
          (ProductAssembly.embedHandoff
            (materializerState := materializerState)
            (leftCount := leftCount)
            (leftUpdateState := leftUpdateState)
            (rightUpdateState := rightUpdateState) right) c) =
      some
        (TuringMachine.PhaseEmbedding.liftConfig
          (ProductAssembly.embedHandoff
            (materializerState := materializerState)
            (leftCount := leftCount)
            (leftUpdateState := leftUpdateState)
            (rightUpdateState := rightUpdateState) right) d) := by
  cases c with
  | mk sourceState sourceTape =>
      cases d with
      | mk targetState targetTape =>
          cases sourceState with
          | gate =>
              simp [ProductHandoff.machine,
                ProductHandoff.transition,
                TuringMachine.stepConfig] at hstep
          | scan =>
              cases haction :
                  ProductHandoff.transition .scan sourceTape.read with
              | none =>
                  simp [ProductHandoff.machine,
                    TuringMachine.stepConfig, haction] at hstep
              | some action =>
                  rcases action with ⟨write, direction, nextState⟩
                  simp [ProductHandoff.machine,
                    TuringMachine.stepConfig, haction] at hstep
                  cases hstep
                  simp_all [outerMachine, TuringMachine.stepConfig,
                    ProductAssembly.machine,
                    ProductAssembly.transition,
                    ProductAssembly.mapAction,
                    ProductAssembly.embedHandoff,
                    ProductAssembly.handoffControl,
                    ProductAssembly.rightControl,
                    TuringMachine.PhaseEmbedding.liftConfig]

theorem handoff_runConfigExact?_lift
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      ProductHandoff.Control}
    (hrun : ProductHandoff.machine.runConfigExact? steps source =
      some target) :
    (outerMachine materializer left right leftKernel rightKernel).runConfigExact?
        steps
        (TuringMachine.PhaseEmbedding.liftConfig
          (ProductAssembly.embedHandoff
            (materializerState := materializerState)
            (leftCount := leftCount)
            (leftUpdateState := leftUpdateState)
            (rightUpdateState := rightUpdateState) right) source) =
      some
        (TuringMachine.PhaseEmbedding.liftConfig
          (ProductAssembly.embedHandoff
            (materializerState := materializerState)
            (leftCount := leftCount)
            (leftUpdateState := leftUpdateState)
            (rightUpdateState := rightUpdateState) right) target) := by
  exact
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      _ (handoff_step_active materializer left right leftKernel rightKernel)
      hrun

theorem handoff_computes_lift
    {source target : TuringMachine.Configuration MachineCodeSymbol
      ProductHandoff.Control}
    (hrun : TuringMachine.Computes ProductHandoff.machine
      source target) :
    TuringMachine.Computes
      (outerMachine materializer left right leftKernel rightKernel)
      (TuringMachine.PhaseEmbedding.liftConfig
        (ProductAssembly.embedHandoff
          (materializerState := materializerState)
          (leftCount := leftCount)
          (leftUpdateState := leftUpdateState)
          (rightUpdateState := rightUpdateState) right) source)
      (TuringMachine.PhaseEmbedding.liftConfig
        (ProductAssembly.embedHandoff
          (materializerState := materializerState)
          (leftCount := leftCount)
          (leftUpdateState := leftUpdateState)
          (rightUpdateState := rightUpdateState) right) target) := by
  exact computes_lift_active _
    (handoff_step_active materializer left right leftKernel rightKernel) hrun

structure PairPrefixWitness
    (input : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) where
  source : TuringMachine.Configuration MachineCodeSymbol materializerState
  targetTape : Tape MachineCodeSymbol
  haltingTransitionsDisabled :
    TuringMachine.HaltingTransitionsDisabled materializer
  run :
    TuringMachine.Computes materializer source
      { state := materializer.halt, tape := targetTape }
  leftRepresents :
    RelationalDriverInduction.Represents
      (Frame.protectedWord (Layout.initial right input rightFuel) [])
      leftFuel
      (SerializedFieldComposer.CarriedStateFrame.ofParsed
        (Layout.initial left input leftFuel))
      targetTape

theorem haltsFrom_of_pair
    (input : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat)
    (leftWitnesses :
      CyclicRelationalContract.CyclicRunWitnesses left leftKernel
        (Frame.protectedWord (Layout.initial right input rightFuel) []))
    (rightWitnesses :
      CyclicRelationalContract.CyclicRunWitnesses right rightKernel [])
    (pairPrefix : PairPrefixWitness materializer left right
      input leftFuel rightFuel)
    (hleft :
      TuringMachine.HaltsFromIn left leftFuel
        (RelationalDriverInduction.semanticConfig
          (SerializedFieldComposer.CarriedStateFrame.ofParsed
            (Layout.initial left input leftFuel))))
    (hright :
      TuringMachine.HaltsFromIn right rightFuel
        (RelationalDriverInduction.semanticConfig
          (SerializedFieldComposer.CarriedStateFrame.ofParsed
            (Layout.initial right input rightFuel)))) :
    TuringMachine.HaltsFrom
      (outerMachine materializer left right leftKernel rightKernel)
      (TuringMachine.PhaseEmbedding.liftConfig
        (ProductAssembly.embedMaterializer
          (rightCount := rightCount)
          (leftUpdateState := leftUpdateState)
          (rightUpdateState := rightUpdateState)
          materializer left) pairPrefix.source) := by
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
  have hleftRep :
      RelationalDriverInduction.Represents rightData leftFuel leftFrame
        pairPrefix.targetTape := by
    simpa [rightData, leftFrame] using pairPrefix.leftRepresents
  rcases ProductSuccess.success_endpoint_of_witnesses
      left leftKernel rightData
      (by simpa [rightData] using leftWitnesses)
      leftFuel leftFrame pairPrefix.targetTape hleftRep
      (by simpa [leftFrame] using hleft) with
    ⟨leftEndpointFrame, leftEndpointTape,
      hleftEndpointRep, hleftRun⟩
  have hleftOuter := left_computes_lift materializer left right leftKernel
    rightKernel hleftRun
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
  have hhandoffOuter := handoff_computes_lift materializer left right
    leftKernel rightKernel hhandoffRun
  have hrightRep :
      RelationalDriverInduction.Represents ([] : Word MachineCodeSymbol)
        rightFuel rightFrame handoffEndpoint.tape := by
    unfold RelationalDriverInduction.Represents
    simpa [rightData, rightFrame,
      SerializedFieldComposer.CarriedStateFrame.withFuel,
      SerializedFieldComposer.CarriedStateFrame.ofParsed,
      SerializedFieldComposer.FuelDecrementMachine.withFuel,
      Layout.initial, Layout.ofConfig] using
      hrightTapeEquiv
  rcases ProductSuccess.success_endpoint_of_witnesses
      right rightKernel ([] : Word MachineCodeSymbol) rightWitnesses
      rightFuel rightFrame handoffEndpoint.tape hrightRep
      (by simpa [rightFrame] using hright) with
    ⟨rightEndpointFrame, rightEndpointTape,
      hrightEndpointRep, hrightRun⟩
  have hrightOuter := right_computes_lift materializer left right leftKernel
    rightKernel hrightRun
  have hleftOuter' :
      TuringMachine.Computes
        (outerMachine materializer left right leftKernel rightKernel)
        (TuringMachine.PhaseEmbedding.liftConfig
          (ProductAssembly.embedMaterializer
            (rightCount := rightCount)
            (leftUpdateState := leftUpdateState)
            (rightUpdateState := rightUpdateState)
            materializer left)
          { state := materializer.halt, tape := pairPrefix.targetTape })
        (TuringMachine.PhaseEmbedding.liftConfig
          (ProductAssembly.embedLeft
            (materializerState := materializerState)
            (rightCount := rightCount)
            (rightUpdateState := rightUpdateState))
          (CyclicRelationalContract.acceptConfig leftEndpointTape)) := by
    simpa [CyclicRelationalContract.sourceConfig,
      ProductAssembly.embedMaterializer,
      leftFrame, SerializedFieldComposer.CarriedStateFrame.ofParsed,
      Layout.initial, Layout.ofConfig, TuringMachine.initial,
      TuringMachine.PhaseEmbedding.liftConfig,
      ProductAssembly.embedLeft,
      ProductAssembly.leftControl] using hleftOuter
  have hthroughLeft := TuringMachine.computes_trans hmaterializer hleftOuter'
  have hthroughHandoff :=
    TuringMachine.computes_trans hthroughLeft hhandoffOuter
  have hrightOuter' :
      TuringMachine.Computes
        (outerMachine materializer left right leftKernel rightKernel)
        (TuringMachine.PhaseEmbedding.liftConfig
          (ProductAssembly.embedHandoff
            (materializerState := materializerState)
            (leftCount := leftCount)
            (leftUpdateState := leftUpdateState)
            (rightUpdateState := rightUpdateState) right)
          handoffEndpoint)
        (TuringMachine.PhaseEmbedding.liftConfig
          (ProductAssembly.embedRight
            (materializerState := materializerState)
            (leftCount := leftCount)
            (leftUpdateState := leftUpdateState))
          (CyclicRelationalContract.acceptConfig rightEndpointTape)) := by
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
          TuringMachine.PhaseEmbedding.liftConfig] using hrightOuter
  have htotal := TuringMachine.computes_trans hthroughHandoff hrightOuter'
  refine ⟨_, htotal, ?_⟩
  rfl

end


end ProductComposition
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
