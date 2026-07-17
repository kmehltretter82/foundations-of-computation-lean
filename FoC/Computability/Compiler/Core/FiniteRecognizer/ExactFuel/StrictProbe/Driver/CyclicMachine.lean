import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseEmbedding
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseRetarget
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Dispatch.SerializedHead
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Driver.Gate
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Driver.ZeroExit

set_option doc.verso true

/-!
# Generic cyclic exact-fuel driver

A finite cyclic driver connects fuel classification, zero-fuel exit selection,
serialized-head dispatch, and a parameterized selected-update kernel.
-/
namespace FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe
open Languages
namespace CyclicDriverIntegration
/-- Typed interface for a selected-update implementation. -/
structure UpdateKernel (stateCount : Nat) (updateState : Type)
    [DecidableEq updateState] where
  finite : Foundation.FiniteType updateState
  start : SerializedHeadDispatch.Selected stateCount -> updateState
  halt : SerializedHeadDispatch.Selected stateCount -> updateState
  transition :
    SerializedHeadDispatch.Selected stateCount ->
      updateState -> Option MachineCodeSymbol ->
        Option (Option MachineCodeSymbol × Direction × updateState)
  halt_transition_none :
    forall selected read, transition selected (halt selected) read = none
namespace UpdateKernel
def machine {stateCount : Nat} {updateState : Type}
    [DecidableEq updateState]
    (K : UpdateKernel stateCount updateState)
    (selected : SerializedHeadDispatch.Selected stateCount) :
    TuringMachine MachineCodeSymbol updateState where
  start := K.start selected
  halt := K.halt selected
  transition := K.transition selected
  statesFinite := K.finite
end UpdateKernel
/-- One finite cyclic control space.  The update payload remains in finite
control across the parameterized physical phase. -/
inductive Control (stateCount : Nat) (updateState : Type) where
  | gate (inner : CarriedFuelGate.Control stateCount)
  | gateZeroReturn (carriedState : Fin stateCount)
  | gatePositiveReturn (carriedState : Fin stateCount)
  | zero (inner : ZeroExitRoundTrip.Control stateCount)
  | acceptReturn
  | rejectReturn
  | dispatch (inner : SerializedHeadDispatch.Control stateCount)
  | selectedReturn (selected : SerializedHeadDispatch.Selected stateCount)
  | update (selected : SerializedHeadDispatch.Selected stateCount)
      (inner : updateState)
  | updateReturn (selected : SerializedHeadDispatch.Selected stateCount)
  | accept
  | reject
deriving DecidableEq
namespace Control
def selectedUpdateFinite (stateCount : Nat)
    (updateFinite : Foundation.FiniteType updateState) :
    Foundation.FiniteType
      (SerializedHeadDispatch.Selected stateCount × updateState) :=
  Foundation.FiniteType.prod
    (SerializedHeadDispatch.Selected.finite stateCount) updateFinite
def elems (stateCount : Nat)
    (updateFinite : Foundation.FiniteType updateState) :
    List (Control stateCount updateState) :=
  (CarriedFuelGate.Control.finite stateCount).elems.map Control.gate ++
  (List.finRange stateCount).map Control.gateZeroReturn ++
  (List.finRange stateCount).map Control.gatePositiveReturn ++
  (ZeroExitRoundTrip.Control.finite stateCount).elems.map Control.zero ++
  [.acceptReturn, .rejectReturn] ++
  (SerializedHeadDispatch.Control.finite stateCount).elems.map
      Control.dispatch ++
  (SerializedHeadDispatch.Selected.elems stateCount).map
      Control.selectedReturn ++
  (selectedUpdateFinite stateCount updateFinite).elems.map
      (fun payload => Control.update payload.1 payload.2) ++
  (SerializedHeadDispatch.Selected.elems stateCount).map
      Control.updateReturn ++ [.accept, .reject]
def finite (stateCount : Nat)
    (updateFinite : Foundation.FiniteType updateState) :
    Foundation.FiniteType (Control stateCount updateState) where
  elems := elems stateCount updateFinite
  complete := by
    intro control
    cases control <;>
      simp [elems, List.mem_finRange,
        (CarriedFuelGate.Control.finite stateCount).complete,
        (ZeroExitRoundTrip.Control.finite stateCount).complete,
        (SerializedHeadDispatch.Control.finite stateCount).complete,
        (selectedUpdateFinite stateCount updateFinite).complete]
    case selectedReturn selected =>
      exact (SerializedHeadDispatch.Selected.finite stateCount).complete
        selected
    case updateReturn selected =>
      exact (SerializedHeadDispatch.Selected.finite stateCount).complete
        selected
end Control
def transition {stateCount : Nat} {updateState : Type}
    [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : UpdateKernel stateCount updateState) :
    Control stateCount updateState -> Option MachineCodeSymbol ->
      Option
        (Option MachineCodeSymbol × Direction ×
          Control stateCount updateState)
  | .gate (.zeroEntry carriedState), read =>
      some (read, Direction.right, .gateZeroReturn carriedState)
  | .gate (.positiveEntry carriedState), read =>
      some (read, Direction.right, .gatePositiveReturn carriedState)
  | .gate inner, read =>
      match CarriedFuelGate.transition inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .gate target)
  | .gateZeroReturn carriedState, read =>
    some (read, Direction.left, .zero (.check carriedState))
  | .gatePositiveReturn carriedState, read =>
    some (read, Direction.left, .dispatch (.locate carriedState .header))
  | .zero .successContinuation, read =>
      some (read, Direction.right, .acceptReturn)
  | .zero .failureContinuation, read =>
      some (read, Direction.right, .rejectReturn)
  | .zero inner, read =>
      match ZeroExitRoundTrip.transition M inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .zero target)
  | .acceptReturn, read =>
    some (read, Direction.left, .accept)
  | .rejectReturn, read =>
    some (read, Direction.left, .reject)
  | .dispatch .failureExit, read =>
      some (read, Direction.right, .rejectReturn)
  | .dispatch (.selectedEntry selected), read =>
      some (read, Direction.right, .selectedReturn selected)
  | .dispatch inner, read =>
      match SerializedHeadDispatch.transition M inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .dispatch target)
  | .selectedReturn selected, read =>
    some (read, Direction.left, .update selected (K.start selected))
  | .update selected inner, read =>
      if inner = K.halt selected then
        some (read, Direction.right, .updateReturn selected)
      else
        match K.transition selected inner read with
        | none => none
        | some (write, direction, target) =>
            some (write, direction, .update selected target)
  | .updateReturn selected, read =>
    some (read, Direction.left, .gate (.header selected.nextState))
  | .accept, _ => none
  | .reject, _ => none
def machine {stateCount : Nat} {updateState : Type}
    [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : UpdateKernel stateCount updateState) :
    TuringMachine MachineCodeSymbol (Control stateCount updateState) where
  start := .gate (.header M.start)
  halt := .accept
  transition := transition M K
  statesFinite := Control.finite stateCount K.finite
theorem machine_haltingTransitionsDisabled {stateCount : Nat}
    {updateState : Type} [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : UpdateKernel stateCount updateState) :
    TuringMachine.HaltingTransitionsDisabled (machine M K) := by intro read; rfl
theorem reject_transition_none {stateCount : Nat}
    {updateState : Type} [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : UpdateKernel stateCount updateState)
    (read : Option MachineCodeSymbol) :
    (machine M K).transition .reject read = none := by rfl
def gateConfig {stateCount : Nat} {updateState : Type}
    (c : TuringMachine.Configuration MachineCodeSymbol
      (CarriedFuelGate.Control stateCount)) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount updateState) :=
  ⟨.gate c.state, c.tape⟩
def zeroConfig {stateCount : Nat} {updateState : Type}
    (c : TuringMachine.Configuration MachineCodeSymbol
      (ZeroExitRoundTrip.Control stateCount)) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount updateState) :=
  ⟨.zero c.state, c.tape⟩
def dispatchConfig {stateCount : Nat} {updateState : Type}
    (c : TuringMachine.Configuration MachineCodeSymbol
      (SerializedHeadDispatch.Control stateCount)) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount updateState) :=
  ⟨.dispatch c.state, c.tape⟩
def updateConfig {stateCount : Nat} {updateState : Type}
    (selected : SerializedHeadDispatch.Selected stateCount)
    (c : TuringMachine.Configuration MachineCodeSymbol updateState) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount updateState) :=
  ⟨.update selected c.state, c.tape⟩
private theorem lift_step_of_transition
    {innerState outerState : Type}
    (inner : TuringMachine MachineCodeSymbol innerState)
    (outer : TuringMachine MachineCodeSymbol outerState)
    (embed : innerState -> outerState)
    (htransition : forall state read write direction target,
      inner.transition state read = some (write, direction, target) ->
        outer.transition (embed state) read =
          some (write, direction, embed target))
    (c d : TuringMachine.Configuration MachineCodeSymbol innerState)
    (hstep : inner.stepConfig c = some d) :
    outer.stepConfig
        (TuringMachine.PhaseEmbedding.liftConfig embed c) =
      some (TuringMachine.PhaseEmbedding.liftConfig embed d) := by
  cases c with
  | mk state tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      cases hinner : inner.transition state (Tape.read tape) with
      | none => simp_all
      | some action =>
          rcases action with ⟨write, direction, target⟩
          rw [hinner] at hstep
          simp only at hstep
          cases hstep
          simp only [TuringMachine.PhaseEmbedding.liftConfig]
          rw [htransition state (Tape.read tape) write direction target hinner]
private theorem gate_runConfigExact_of_some {stateCount : Nat}
    {updateState : Type} [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : UpdateKernel stateCount updateState)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      (CarriedFuelGate.Control stateCount)}
    (hrun : (CarriedFuelGate.machine M.start).runConfigExact?
      steps source = some target) :
    (machine M K).runConfigExact? steps (gateConfig source) =
      some (gateConfig target) := by
  apply
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      Control.gate
  · intro c d hstep
    apply lift_step_of_transition
      (CarriedFuelGate.machine M.start) (machine M K) Control.gate
      ?_ c d hstep
    intro state read write direction next htransition
    cases state <;>
      simp_all [CarriedFuelGate.machine,
        CarriedFuelGate.transition, machine, transition]
  · simpa [gateConfig, TuringMachine.PhaseEmbedding.liftConfig]
      using hrun
private theorem zero_runConfigExact_of_some {stateCount : Nat}
    {updateState : Type} [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : UpdateKernel stateCount updateState)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      (ZeroExitRoundTrip.Control stateCount)}
    (hrun : (ZeroExitRoundTrip.machine M).runConfigExact?
      steps source = some target) :
    (machine M K).runConfigExact? steps (zeroConfig source) =
      some (zeroConfig target) := by
  apply
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      Control.zero
  · intro c d hstep
    apply lift_step_of_transition
      (ZeroExitRoundTrip.machine M) (machine M K) Control.zero
      ?_ c d hstep
    intro state read write direction next htransition
    cases state <;>
      simp_all [ZeroExitRoundTrip.machine,
        ZeroExitRoundTrip.transition, machine, transition]
  · simpa [zeroConfig, TuringMachine.PhaseEmbedding.liftConfig]
      using hrun
private theorem dispatch_runConfigExact_of_some {stateCount : Nat}
    {updateState : Type} [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : UpdateKernel stateCount updateState)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      (SerializedHeadDispatch.Control stateCount)}
    (hrun : (SerializedHeadDispatch.machine M).runConfigExact?
      steps source = some target) :
    (machine M K).runConfigExact? steps (dispatchConfig source) =
      some (dispatchConfig target) := by
  apply
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      Control.dispatch
  · intro c d hstep
    apply lift_step_of_transition
      (SerializedHeadDispatch.machine M) (machine M K) Control.dispatch
      ?_ c d hstep
    intro state read write direction next htransition
    cases state <;>
      simp_all [SerializedHeadDispatch.machine,
        SerializedHeadDispatch.transition, machine, transition]
  · simpa [dispatchConfig, TuringMachine.PhaseEmbedding.liftConfig]
      using hrun
private theorem update_runConfigExact_of_some {stateCount : Nat}
    {updateState : Type} [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : UpdateKernel stateCount updateState)
    (selected : SerializedHeadDispatch.Selected stateCount)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol updateState}
    (hrun : (K.machine selected).runConfigExact? steps source = some target) :
    (machine M K).runConfigExact? steps (updateConfig selected source) =
      some (updateConfig selected target) := by
  apply
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      (Control.update selected)
  · intro c d hstep
    apply lift_step_of_transition
      (K.machine selected) (machine M K) (Control.update selected)
      ?_ c d hstep
    intro state read write direction next htransition
    change K.transition selected state read =
      some (write, direction, next) at htransition
    have hnotHalt : state ≠ K.halt selected := by
      intro hhalt
      subst state
      rw [K.halt_transition_none] at htransition
      contradiction
    simp [machine, transition, hnotHalt, htransition]
  · simpa [updateConfig, TuringMachine.PhaseEmbedding.liftConfig]
      using hrun
def roundTripTape (T : Tape MachineCodeSymbol) : Tape MachineCodeSymbol :=
  Tape.move .left (Tape.move .right T)
private theorem handoff_run_exact {stateCount : Nat}
    {updateState : Type} [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : UpdateKernel stateCount updateState)
    (source middle target : Control stateCount updateState)
    (T : Tape MachineCodeSymbol)
    (hsource : transition M K source (Tape.read T) =
      some (Tape.read T, Direction.right, middle))
    (hmiddle : transition M K middle
        (Tape.read (Tape.move Direction.right T)) =
      some (Tape.read (Tape.move Direction.right T), Direction.left, target)) :
    (machine M K).runConfigExact? 2 { state := source, tape := T } =
      some { state := target, tape := roundTripTape T } := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, hsource, hmiddle, roundTripTape, Tape.write_read_eq_self]
theorem update_stage_run_exact {stateCount : Nat}
    {updateState : Type} [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : UpdateKernel stateCount updateState)
    (selected : SerializedHeadDispatch.Selected stateCount)
    {steps : Nat} (sourceTape targetTape : Tape MachineCodeSymbol)
    (hrun :
      (K.machine selected).runConfigExact? steps
          { state := K.start selected, tape := sourceTape } =
        some { state := K.halt selected, tape := targetTape }) :
    (machine M K).runConfigExact? (steps + 2)
        { state := Control.update selected (K.start selected)
          tape := sourceTape } =
      some
        { state := Control.gate (.header selected.nextState)
          tape := roundTripTape targetTape } := by
  exact TuringMachine.runConfigExact?_trans
    (update_runConfigExact_of_some M K selected hrun)
    (handoff_run_exact M K
      (Control.update selected (K.halt selected))
      (Control.updateReturn selected)
      (Control.gate (.header selected.nextState)) targetTape
      (by simp [transition]) rfl)
def loopSourceConfig {stateCount : Nat} {updateState : Type}
    (fuel : Nat)
    (F : SerializedFieldComposer.CarriedStateFrame.LoopFrame
      stateCount)
    (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      (Control stateCount updateState) :=
  gateConfig
    (CarriedFuelGate.sourceConfig
      (SerializedFieldComposer.CarriedStateFrame.withFuel fuel F)
      callerData)
def semanticConfig {stateCount : Nat}
    (F : SerializedFieldComposer.CarriedStateFrame.LoopFrame
      stateCount) :
    TuringMachine.Configuration MachineCodeSymbol (Fin stateCount) :=
  (SerializedFieldComposer.CarriedStateFrame.semanticLayout F).config
theorem zero_gate_stage_run_exact {stateCount : Nat}
    {updateState : Type} [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : UpdateKernel stateCount updateState)
    (F : SerializedFieldComposer.CarriedStateFrame.LoopFrame
      stateCount)
    (callerData : Word MachineCodeSymbol) :
    (machine M K).runConfigExact? 4
        (loopSourceConfig (updateState := updateState) 0 F callerData) =
      some
        { state := Control.zero (.check F.carriedState)
          tape :=
            Tape.input
              (Frame.protectedWord
                (SerializedFieldComposer.CarriedStateFrame.withFuel
                  0 F).physicalFrame
                callerData) } := by
  let T :=
    Tape.input
      (Frame.protectedWord
        (SerializedFieldComposer.CarriedStateFrame.withFuel
          0 F).physicalFrame
        callerData)
  have hround : roundTripTape T = T := by
    exact
      CarriedFuelGate.roundTrip_protected_input_eq
        (SerializedFieldComposer.CarriedStateFrame.withFuel 0 F)
        callerData
  have hdouble :
      roundTripTape (CarriedFuelGate.roundTripTape T) = T := by
    change roundTripTape (roundTripTape T) = T
    rw [hround, hround]
  simpa [loopSourceConfig, gateConfig, CarriedFuelGate.sourceConfig,
      T, hdouble] using
    TuringMachine.runConfigExact?_trans
      (gate_runConfigExact_of_some M K
        (CarriedFuelGate.zero_run_exact_on_tape
          M.start F.carriedState T (by rfl) (by rfl)))
      (handoff_run_exact M K _ _ _
        (CarriedFuelGate.roundTripTape T) rfl rfl)
theorem positive_gate_stage_run_exact {stateCount : Nat}
    {updateState : Type} [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : UpdateKernel stateCount updateState)
    (fuel : Nat)
    (F : SerializedFieldComposer.CarriedStateFrame.LoopFrame
      stateCount)
    (callerData : Word MachineCodeSymbol) :
    (machine M K).runConfigExact? 4
        (loopSourceConfig (updateState := updateState) (fuel + 1) F callerData) =
      some
        { state := Control.dispatch (.locate F.carriedState .header)
          tape :=
            Tape.input
              (Frame.protectedWord
                (SerializedFieldComposer.CarriedStateFrame.withFuel
                  (fuel + 1) F).physicalFrame
                callerData) } := by
  let T :=
    Tape.input
      (Frame.protectedWord
        (SerializedFieldComposer.CarriedStateFrame.withFuel
          (fuel + 1) F).physicalFrame
        callerData)
  have hround : roundTripTape T = T := by
    exact
      CarriedFuelGate.roundTrip_protected_input_eq
        (SerializedFieldComposer.CarriedStateFrame.withFuel
          (fuel + 1) F)
        callerData
  have hdouble :
      roundTripTape (CarriedFuelGate.roundTripTape T) = T := by
    change roundTripTape (roundTripTape T) = T
    rw [hround, hround]
  simpa [loopSourceConfig, gateConfig, CarriedFuelGate.sourceConfig,
      T, hdouble] using
    TuringMachine.runConfigExact?_trans
      (gate_runConfigExact_of_some M K
        (CarriedFuelGate.positive_run_exact_on_tape
          M.start F.carriedState T (by rfl) (by rfl)))
      (handoff_run_exact M K _ _ _
        (CarriedFuelGate.roundTripTape T) rfl rfl)
theorem zero_accept_run_exact {stateCount : Nat}
    {updateState : Type} [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : UpdateKernel stateCount updateState)
    (F : SerializedFieldComposer.CarriedStateFrame.LoopFrame
      stateCount)
    (callerData : Word MachineCodeSymbol)
    (hhalt : (semanticConfig F).state = M.halt) :
    (machine M K).runConfigExact? 8
        (loopSourceConfig (updateState := updateState) 0 F callerData) =
      some
        { state := Control.accept
          tape :=
            Tape.input
              (Frame.protectedWord
                (SerializedFieldComposer.CarriedStateFrame.withFuel
                  0 F).physicalFrame
                callerData) } := by
  let T :=
    Tape.input
      (Frame.protectedWord
        (SerializedFieldComposer.CarriedStateFrame.withFuel
          0 F).physicalFrame
        callerData)
  have hphysical : F.carriedState = M.halt := by
    simpa [semanticConfig,
      SerializedFieldComposer.CarriedStateFrame.semanticLayout,
      Layout.config] using hhalt
  have hround : roundTripTape T = T := by
    exact
      CarriedFuelGate.roundTrip_protected_input_eq
        (SerializedFieldComposer.CarriedStateFrame.withFuel 0 F)
        callerData
  have hdouble :
      roundTripTape
          (ZeroExitRoundTrip.continuationTapeConfig
            (.successContinuation :
              ZeroExitRoundTrip.Control stateCount) T).tape = T := by
    change roundTripTape (roundTripTape T) = T
    rw [hround, hround]
  simpa [T, hdouble] using
    TuringMachine.runConfigExact?_trans
      (zero_gate_stage_run_exact M K F callerData)
      (TuringMachine.runConfigExact?_trans
        (zero_runConfigExact_of_some M K
          (ZeroExitRoundTrip.success_run_exact_on_tape
            M F.carriedState T hphysical))
        (handoff_run_exact M K _ _ _
          (ZeroExitRoundTrip.continuationTapeConfig
            (.successContinuation :
              ZeroExitRoundTrip.Control stateCount) T).tape rfl rfl))
theorem zero_reject_run_exact {stateCount : Nat}
    {updateState : Type} [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : UpdateKernel stateCount updateState)
    (F : SerializedFieldComposer.CarriedStateFrame.LoopFrame
      stateCount)
    (callerData : Word MachineCodeSymbol)
    (hnotHalt : (semanticConfig F).state ≠ M.halt) :
    (machine M K).runConfigExact? 8
        (loopSourceConfig (updateState := updateState) 0 F callerData) =
      some
        { state := Control.reject
          tape :=
            Tape.input
              (Frame.protectedWord
                (SerializedFieldComposer.CarriedStateFrame.withFuel
                  0 F).physicalFrame
                callerData) } := by
  let T :=
    Tape.input
      (Frame.protectedWord
        (SerializedFieldComposer.CarriedStateFrame.withFuel
          0 F).physicalFrame
        callerData)
  have hphysical : F.carriedState ≠ M.halt := by
    simpa [semanticConfig,
      SerializedFieldComposer.CarriedStateFrame.semanticLayout,
      Layout.config] using hnotHalt
  have hround : roundTripTape T = T := by
    exact
      CarriedFuelGate.roundTrip_protected_input_eq
        (SerializedFieldComposer.CarriedStateFrame.withFuel 0 F)
        callerData
  have hdouble :
      roundTripTape
          (ZeroExitRoundTrip.continuationTapeConfig
            (.failureContinuation :
              ZeroExitRoundTrip.Control stateCount) T).tape = T := by
    change roundTripTape (roundTripTape T) = T
    rw [hround, hround]
  simpa [T, hdouble] using
    TuringMachine.runConfigExact?_trans
      (zero_gate_stage_run_exact M K F callerData)
      (TuringMachine.runConfigExact?_trans
        (zero_runConfigExact_of_some M K
          (ZeroExitRoundTrip.failure_run_exact_on_tape
            M F.carriedState T hphysical))
        (handoff_run_exact M K _ _ _
          (ZeroExitRoundTrip.continuationTapeConfig
            (.failureContinuation :
              ZeroExitRoundTrip.Control stateCount) T).tape rfl rfl))
theorem dispatchConfig_sourceConfig_eq {stateCount : Nat}
    {updateState : Type}
    (carriedState : Fin stateCount) (L : Layout stateCount)
    (callerData : Word MachineCodeSymbol) :
    dispatchConfig (updateState := updateState)
        (SerializedHeadDispatch.sourceConfig
          carriedState L callerData) =
      { state := Control.dispatch (.locate carriedState .header)
        tape := Tape.input (Frame.protectedWord L callerData) } := by
  unfold dispatchConfig SerializedHeadDispatch.sourceConfig
    SerializedHeadDispatch.locateConfig
    SerializedFieldComposer.HeadLocator.locatorStartConfig
    SerializedFieldComposer.HeadLocator.cursorConfig
  cases Frame.protectedWord L callerData <;> rfl
theorem succ_missing_run_exact {stateCount : Nat}
    {updateState : Type} [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : UpdateKernel stateCount updateState)
    (fuel : Nat)
    (F : SerializedFieldComposer.CarriedStateFrame.LoopFrame
      stateCount)
    (callerData : Word MachineCodeSymbol)
    (hmissing :
      M.transition (semanticConfig F).state
          (Tape.read (semanticConfig F).tape) = none) :
    let L :=
      (SerializedFieldComposer.CarriedStateFrame.withFuel
        (fuel + 1) F).physicalFrame
    (machine M K).runConfigExact?
        (4 +
          ((SerializedFieldComposer.HeadLocator.locatorSteps L + 2) +
            2))
        (loopSourceConfig (updateState := updateState)
          (fuel + 1) F callerData) =
      some
        { state := Control.reject
          tape :=
            roundTripTape
              (SerializedHeadDispatch.failureConfig
                (stateCount := stateCount)
                (SerializedFieldComposer.HeadLocator.gateTape
                  (Frame.protectedWord L callerData))).tape } := by
  dsimp
  let L :=
    (SerializedFieldComposer.CarriedStateFrame.withFuel
      (fuel + 1) F).physicalFrame
  have hphysical : M.transition F.carriedState L.head = none := by
    simpa [semanticConfig,
      SerializedFieldComposer.CarriedStateFrame.semanticLayout,
      SerializedFieldComposer.CarriedStateFrame.withFuel,
      SerializedFieldComposer.FuelDecrementMachine.withFuel,
      Layout.config, Layout.tape, Tape.read, L] using hmissing
  have hgate := positive_gate_stage_run_exact M K fuel F callerData
  rw [← dispatchConfig_sourceConfig_eq
    (updateState := updateState) F.carriedState L callerData] at hgate
  exact TuringMachine.runConfigExact?_trans hgate
    (TuringMachine.runConfigExact?_trans
      (dispatch_runConfigExact_of_some M K
        (SerializedHeadDispatch.succMissing_run_exact
          M F.carriedState L callerData hphysical))
      (handoff_run_exact M K _ _ _
        (SerializedHeadDispatch.failureConfig
          (stateCount := stateCount)
          (SerializedFieldComposer.HeadLocator.gateTape
            (Frame.protectedWord L callerData))).tape rfl rfl))
theorem succ_present_prefix_run_exact {stateCount : Nat}
    {updateState : Type} [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : UpdateKernel stateCount updateState)
    (fuel : Nat)
    (F : SerializedFieldComposer.CarriedStateFrame.LoopFrame
      stateCount)
    (callerData : Word MachineCodeSymbol)
    (write : Option MachineCodeSymbol) (direction : Direction)
    (nextState : Fin stateCount)
    (hselected :
      M.transition (semanticConfig F).state
          (Tape.read (semanticConfig F).tape) =
        some (write, direction, nextState)) :
    let L :=
      (SerializedFieldComposer.CarriedStateFrame.withFuel
        (fuel + 1) F).physicalFrame
    let selected : SerializedHeadDispatch.Selected stateCount :=
      { write := write
        direction := direction
        nextState := nextState }
    (machine M K).runConfigExact?
        (4 +
          ((SerializedFieldComposer.HeadLocator.locatorSteps L + 2) +
            2))
        (loopSourceConfig (updateState := updateState)
          (fuel + 1) F callerData) =
      some
        { state := Control.update selected (K.start selected)
          tape :=
            roundTripTape
              (SerializedHeadDispatch.selectedConfig selected
                (SerializedFieldComposer.HeadLocator.gateTape
                  (Frame.protectedWord L callerData))).tape } := by
  dsimp
  let L :=
    (SerializedFieldComposer.CarriedStateFrame.withFuel
      (fuel + 1) F).physicalFrame
  have hphysical :
      M.transition F.carriedState L.head =
        some (write, direction, nextState) := by
    simpa [semanticConfig,
      SerializedFieldComposer.CarriedStateFrame.semanticLayout,
      SerializedFieldComposer.CarriedStateFrame.withFuel,
      SerializedFieldComposer.FuelDecrementMachine.withFuel,
      Layout.config, Layout.tape, Tape.read, L] using hselected
  have hgate := positive_gate_stage_run_exact M K fuel F callerData
  rw [← dispatchConfig_sourceConfig_eq
    (updateState := updateState) F.carriedState L callerData] at hgate
  exact TuringMachine.runConfigExact?_trans hgate
    (TuringMachine.runConfigExact?_trans
      (dispatch_runConfigExact_of_some M K
        (SerializedHeadDispatch.succPresent_run_exact
          M F.carriedState L callerData write direction nextState hphysical))
      (handoff_run_exact M K _ _ _
        (SerializedHeadDispatch.selectedConfig
          { write := write, direction := direction, nextState := nextState }
          (SerializedFieldComposer.HeadLocator.gateTape
            (Frame.protectedWord L callerData))).tape rfl rfl))
end CyclicDriverIntegration
end FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe
