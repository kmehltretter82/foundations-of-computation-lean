import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.CallerAwareFinish
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.CandidateKernel
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.Layout

namespace FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.CandidateMaterializer

open Languages
open ExactFuel.StrictProbe
open ExactFuel.StrictProbe.InitialMaterializer
open ExactFuel.StrictProbe.ProductCallerAwareFinish

inductive Control {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount)) where
  | materializer (inner : FullMaterializerMachine.Control selected)
  | materializerReturn
  | compactor (inner : StageInput.TwoBlankCompactor.Control)
  | compactorReturn
  | halt
deriving DecidableEq

namespace Control

def elems {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    List (Control selected) :=
  List.append
    ((FullMaterializerMachine.machine selected).statesFinite.elems.map
      Control.materializer)
    (List.append [.materializerReturn]
      (List.append
        (StageInput.TwoBlankCompactor.machine.statesFinite.elems.map
          Control.compactor)
        [.compactorReturn, .halt]))

def finite {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    Foundation.FiniteType (Control selected) where
  elems := elems selected
  complete := by
    intro control
    cases control with
    | materializer inner =>
        have h :=
          (FullMaterializerMachine.machine selected).statesFinite.complete inner
        simp [elems, h]
    | materializerReturn => simp [elems]
    | compactor inner =>
        have h :=
          StageInput.TwoBlankCompactor.machine.statesFinite.complete inner
        simp [elems, h]
    | compactorReturn => simp [elems]
    | halt => simp [elems]

end Control

def materializerEndpoint {stateCount : Nat}
    {selected : TuringMachine MachineCodeSymbol (Fin stateCount)} :
    FullMaterializerMachine.Control selected :=
  .header .halt

def transition {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    Control selected -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control selected)
  | .materializer inner, read =>
      if inner = materializerEndpoint then
        some (read, Direction.right, .materializerReturn)
      else
        match FullMaterializerMachine.transition selected inner read with
        | none => none
        | some (write, direction, target) =>
            some (write, direction, .materializer target)
  | .materializerReturn, read =>
      some (read, Direction.left, .compactor .seek)
  | .compactor inner, read =>
      if inner = StageInput.TwoBlankCompactor.machine.halt then
        some (read, Direction.right, .compactorReturn)
      else
        match StageInput.TwoBlankCompactor.transition inner read with
        | none => none
        | some (write, direction, target) =>
            some (write, direction, .compactor target)
  | .compactorReturn, read => some (read, Direction.left, .halt)
  | .halt, _ => none

def machine {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    TuringMachine MachineCodeSymbol (Control selected) where
  start := .materializer (FullMaterializerMachine.machine selected).start
  halt := .halt
  transition := transition selected
  statesFinite := Control.finite selected

def materializerConfig {stateCount : Nat}
    {selected : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (c : TuringMachine.Configuration MachineCodeSymbol
      (FullMaterializerMachine.Control selected)) :
    TuringMachine.Configuration MachineCodeSymbol (Control selected) :=
  TuringMachine.PhaseEmbedding.liftConfig Control.materializer c

def compactorConfig {stateCount : Nat}
    {selected : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (c : TuringMachine.Configuration MachineCodeSymbol
      StageInput.TwoBlankCompactor.Control) :
    TuringMachine.Configuration MachineCodeSymbol (Control selected) :=
  TuringMachine.PhaseEmbedding.liftConfig Control.compactor c

theorem materializer_endpoint_transition_none {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (read : Option MachineCodeSymbol) :
    (FullMaterializerMachine.machine selected).transition
        materializerEndpoint read = none := by
  rfl

theorem materializer_stepConfig_of_some {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (c d : TuringMachine.Configuration MachineCodeSymbol
      (FullMaterializerMachine.Control selected))
    (hstep : (FullMaterializerMachine.machine selected).stepConfig c =
      some d) :
    (machine selected).stepConfig (materializerConfig c) =
      some (materializerConfig d) := by
  have hactive : c.state ≠ materializerEndpoint := by
    intro hc
    unfold TuringMachine.stepConfig at hstep
    rw [hc, materializer_endpoint_transition_none] at hstep
    contradiction
  unfold TuringMachine.stepConfig at hstep ⊢
  simp only [machine, materializerConfig,
    TuringMachine.PhaseEmbedding.liftConfig, transition,
    hactive, ↓reduceIte]
  cases htransition :
      FullMaterializerMachine.transition selected c.state
        (Tape.read c.tape) with
  | none =>
      simp [FullMaterializerMachine.machine, htransition] at hstep
  | some action =>
      rcases action with ⟨write, direction, target⟩
      simp [FullMaterializerMachine.machine, htransition] at hstep ⊢
      cases hstep
      exact ⟨rfl, rfl⟩

theorem materializer_run_lift {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      (FullMaterializerMachine.Control selected)}
    (hrun : (FullMaterializerMachine.machine selected).runConfigExact?
      steps source = some target) :
    (machine selected).runConfigExact? steps (materializerConfig source) =
      some (materializerConfig target) := by
  apply TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    Control.materializer
  · exact materializer_stepConfig_of_some selected
  · exact hrun

theorem compactor_stepConfig_of_some {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (c d : TuringMachine.Configuration MachineCodeSymbol
      StageInput.TwoBlankCompactor.Control)
    (hstep : StageInput.TwoBlankCompactor.machine.stepConfig c = some d) :
    (machine selected).stepConfig (compactorConfig c) =
      some (compactorConfig d) := by
  have hactive :
      c.state ≠ StageInput.TwoBlankCompactor.machine.halt := by
    intro hc
    unfold TuringMachine.stepConfig at hstep
    rw [hc, StageRunner.compactor_halt_transition_none] at hstep
    contradiction
  unfold TuringMachine.stepConfig at hstep ⊢
  simp only [machine, compactorConfig,
    TuringMachine.PhaseEmbedding.liftConfig, transition,
    hactive, ↓reduceIte]
  cases htransition :
      StageInput.TwoBlankCompactor.transition c.state
        (Tape.read c.tape) with
  | none =>
      simp [StageInput.TwoBlankCompactor.machine, htransition] at hstep
  | some action =>
      rcases action with ⟨write, direction, target⟩
      simp [StageInput.TwoBlankCompactor.machine, htransition] at hstep ⊢
      cases hstep
      exact ⟨rfl, rfl⟩

theorem compactor_run_lift {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      StageInput.TwoBlankCompactor.Control}
    (hrun : StageInput.TwoBlankCompactor.machine.runConfigExact? steps
      source = some target) :
    (machine selected).runConfigExact? steps (compactorConfig source) =
      some (compactorConfig target) := by
  apply TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    Control.compactor
  · exact compactor_stepConfig_of_some selected
  · exact hrun

theorem materializer_handoff_run_exact {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tape : Tape MachineCodeSymbol) :
    (machine selected).runConfigExact? 2
        { state := .materializer materializerEndpoint, tape := tape } =
      some
        (compactorConfig
          (StageInput.TwoBlankCompactor.config .seek
            (StageRunner.roundTripTape tape))) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, materializerEndpoint, compactorConfig,
    TuringMachine.PhaseEmbedding.liftConfig,
    StageInput.TwoBlankCompactor.config, StageRunner.roundTripTape,
    Tape.write_read_eq_self]

theorem compactor_handoff_run_exact {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tape : Tape MachineCodeSymbol) :
    (machine selected).runConfigExact? 2
        { state := .compactor
            StageInput.TwoBlankCompactor.machine.halt,
          tape := tape } =
      some
        { state := (machine selected).halt
          tape := StageRunner.roundTripTape tape } := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, StageRunner.roundTripTape,
    Tape.write_read_eq_self]

private theorem exactRun_trans
    {state : Type}
    (M : TuringMachine MachineCodeSymbol state)
    {first second : Nat}
    {source middle target : TuringMachine.Configuration MachineCodeSymbol state}
    (hfirst : M.runConfigExact? first source = some middle)
    (hsecond : M.runConfigExact? second middle = some target) :
    M.runConfigExact? (first + second) source = some target := by
  rw [InitialMaterializer.ExactRun.append, hfirst]
  exact hsecond

structure BlockFinishResult {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol)
    (rest callerData : Word MachineCodeSymbol)
    (fuel : Nat)
    (blockSource : TuringMachine.Configuration MachineCodeSymbol
      (FullMaterializerMachine.Control selected)) where
  targetTape : Tape MachineCodeSymbol
  steps : Nat
  run_exact :
    (machine selected).runConfigExact? steps
        (materializerConfig blockSource) =
      some
        { state := (machine selected).halt
          tape := targetTape }
  targetTape_equiv : Tape.Equiv targetTape
    (Tape.input
      (Frame.protectedWord
        (ExactFuel.Layout.initial selected (headSymbol :: rest) fuel)
        callerData))

def finish_from_related_block_source {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol)
    (rest callerData : Word MachineCodeSymbol)
    (fuel : Nat)
    (blockSource : TuringMachine.Configuration MachineCodeSymbol
      (FullMaterializerMachine.Control selected))
    (hstate :
      (ProductCallerAwareTail.blockPaddedSourceConfig selected headSymbol rest
        (MachineDescription.encodeNat fuel).reverse callerData).state =
      blockSource.state)
    (htape : Tape.Equiv
      (ProductCallerAwareTail.blockPaddedSourceConfig selected headSymbol rest
        (MachineDescription.encodeNat fuel).reverse callerData).tape
      blockSource.tape) :
    BlockFinishResult selected headSymbol rest callerData fuel
      blockSource := by
  let cleanSource := cleanBlockSource selected headSymbol rest
    (MachineDescription.encodeNat fuel).reverse callerData
  let cleanFinal := cleanHeaderEndpoint selected fuel
    (callerBody selected headSymbol rest callerData)
  have hclean :
      (FullMaterializerMachine.machine selected).runConfigExact?
          (blockHeaderSteps selected headSymbol rest callerData fuel)
          cleanSource = some cleanFinal := by
    exact clean_block_header_run_exact selected headSymbol rest callerData fuel
  have hsourceState : cleanSource.state = blockSource.state := hstate
  have hsourceTape : Tape.Equiv cleanSource.tape blockSource.tape :=
    Tape.Equiv.trans
      (cleanBlockSource_equiv_blockPaddedSource selected headSymbol rest
        (MachineDescription.encodeNat fuel).reverse callerData)
      htape
  have hheaderExists := TuringExactEquiv.runConfigExact?_some_of_equiv
    (clean := cleanSource) (padded := blockSource)
    (cleanFinal := cleanFinal)
    (FullMaterializerMachine.machine selected)
    (blockHeaderSteps selected headSymbol rest callerData fuel)
    hsourceState hsourceTape hclean
  let headerResult :=
    (FullMaterializerMachine.machine selected).runConfigExact?
      (blockHeaderSteps selected headSymbol rest callerData fuel) blockSource
  have hheaderSome : headerResult.isSome := by
    rcases hheaderExists with ⟨endpoint, hrun, _hstate, _htape⟩
    simp [headerResult, hrun]
  let actualHeader := headerResult.get hheaderSome
  have hheader : headerResult = some actualHeader :=
    (Option.some_get hheaderSome).symm
  have hheaderRun :
      (FullMaterializerMachine.machine selected).runConfigExact?
          (blockHeaderSteps selected headSymbol rest callerData fuel)
          blockSource = some actualHeader := hheader
  have hheaderState : cleanFinal.state = actualHeader.state := by
    rcases hheaderExists with ⟨endpoint, hrun, hstate', _htape⟩
    have heq : endpoint = actualHeader :=
      Option.some.inj (hrun.symm.trans hheaderRun)
    simpa [heq] using hstate'
  have hheaderTape : Tape.Equiv cleanFinal.tape actualHeader.tape := by
    rcases hheaderExists with ⟨endpoint, hrun, _hstate, htape'⟩
    have heq : endpoint = actualHeader :=
      Option.some.inj (hrun.symm.trans hheaderRun)
    simpa [heq] using htape'
  let bounced := StageRunner.roundTripTape actualHeader.tape
  have hheaderEndpoint : actualHeader.state = materializerEndpoint :=
    hheaderState.symm
  have hheaderOuter := materializer_run_lift selected hheaderRun
  have hfirstHandoff :
      (machine selected).runConfigExact? 2
          (materializerConfig actualHeader) =
        some
          (compactorConfig
            (StageInput.TwoBlankCompactor.config .seek bounced)) := by
    simpa [materializerConfig,
      TuringMachine.PhaseEmbedding.liftConfig,
      hheaderEndpoint, bounced] using
      (materializer_handoff_run_exact selected actualHeader.tape)
  have hbounced : Tape.Equiv
      (HeaderLeftInstaller.haltTape
        (MachineDescription.encodeNat fuel)
        (callerBody selected headSymbol rest callerData)) bounced :=
    Tape.Equiv.trans
      (by simpa [cleanFinal, cleanHeaderEndpoint,
          FullMaterializerMachine.headerConfig,
          HeaderLeftInstaller.haltConfig] using hheaderTape)
      (Tape.Equiv.symm
        (StageRunner.roundTripTape_equiv actualHeader.tape))
  have hcompactorExists := compactor_run_from_equiv_header_halt fuel
    (callerBody selected headSymbol rest callerData) bounced hbounced
  let compactorResult :=
    StageInput.TwoBlankCompactor.machine.runConfigExact?
      (compactorSteps fuel (callerBody selected headSymbol rest callerData))
      (StageInput.TwoBlankCompactor.config .seek bounced)
  have hcompactorSome : compactorResult.isSome := by
    rcases hcompactorExists with ⟨endpoint, hrun, _hstate, _htape⟩
    simp [compactorResult, hrun]
  let compactorEndpoint := compactorResult.get hcompactorSome
  have hcompactor : compactorResult = some compactorEndpoint :=
    (Option.some_get hcompactorSome).symm
  have hcompactorRun :
      StageInput.TwoBlankCompactor.machine.runConfigExact?
          (compactorSteps fuel
            (callerBody selected headSymbol rest callerData))
          (StageInput.TwoBlankCompactor.config .seek bounced) =
        some compactorEndpoint := hcompactor
  have hcompactorState :
      compactorEndpoint.state =
        StageInput.TwoBlankCompactor.machine.halt := by
    rcases hcompactorExists with ⟨endpoint, hrun, hstate', _htape⟩
    have heq : endpoint = compactorEndpoint :=
      Option.some.inj (hrun.symm.trans hcompactorRun)
    simpa [heq] using hstate'
  have hcompactorTape : Tape.Equiv compactorEndpoint.tape
      (Tape.input
        (MachineCodeSymbol.header ::
          List.append (MachineDescription.encodeNat fuel)
            (callerBody selected headSymbol rest callerData))) := by
    rcases hcompactorExists with ⟨endpoint, hrun, _hstate, htape'⟩
    have heq : endpoint = compactorEndpoint :=
      Option.some.inj (hrun.symm.trans hcompactorRun)
    simpa [heq] using htape'
  have hcompactorOuter := compactor_run_lift selected hcompactorRun
  let targetTape := StageRunner.roundTripTape compactorEndpoint.tape
  have hsecondHandoff :
      (machine selected).runConfigExact? 2
          (compactorConfig compactorEndpoint) =
        some
          { state := (machine selected).halt
            tape := targetTape } := by
    simpa [compactorConfig,
      TuringMachine.PhaseEmbedding.liftConfig,
      hcompactorState, targetTape] using
      (compactor_handoff_run_exact selected compactorEndpoint.tape)
  have hthroughHeader := exactRun_trans
    (machine selected) hheaderOuter hfirstHandoff
  have hthroughCompactor := exactRun_trans
    (machine selected) hthroughHeader hcompactorOuter
  have hfull := exactRun_trans
    (machine selected) hthroughCompactor hsecondHandoff
  refine
    { targetTape := targetTape
      steps :=
        ((blockHeaderSteps selected headSymbol rest callerData fuel + 2) +
          compactorSteps fuel
            (callerBody selected headSymbol rest callerData)) + 2
      run_exact := hfull
      targetTape_equiv := ?_ }
  rw [← callerTargetWord_eq selected headSymbol rest callerData fuel]
  exact Tape.Equiv.trans
    (StageRunner.roundTripTape_equiv compactorEndpoint.tape)
    hcompactorTape

def NonemptyMaterializeSpec {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol)
    (rest callerData : Word MachineCodeSymbol)
    (fuel : Nat) : Prop :=
  exists targetTape : Tape MachineCodeSymbol,
  exists steps : Nat,
    (machine selected).runConfigExact? steps
          (materializerConfig
            (FullMaterializerMachine.tailConfig selected
              (ProductCallerTail.NonemptyCallerTail.haltConfig
                headSymbol (MachineDescription.encodeNat fuel).reverse
                rest.reverse callerData))) =
        some
          { state := (machine selected).halt
            tape := targetTape } ∧
      Tape.Equiv targetTape
        (Tape.input
          (Frame.protectedWord
            (ExactFuel.Layout.initial selected (headSymbol :: rest) fuel)
            callerData))

theorem materialize_nonempty_from_tail {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol)
    (rest callerData : Word MachineCodeSymbol)
    (fuel : Nat) :
    NonemptyMaterializeSpec selected headSymbol rest callerData fuel := by
  let tailSteps := ProductCallerAwareTail.tailBaseRawSteps
    rest.reverse callerData
  let innerSource :=
    FullMaterializerMachine.tailConfig selected
      (ProductCallerTail.NonemptyCallerTail.haltConfig
        headSymbol (MachineDescription.encodeNat fuel).reverse
        rest.reverse callerData)
  rcases ProductCallerAwareTail.tail_base_raw_to_block_exact
      selected headSymbol (MachineDescription.encodeNat fuel).reverse
      rest.reverse callerData with
    ⟨blockSource, htail, hblockState, hblockTape⟩
  have htailOuter := materializer_run_lift selected htail
  have hblockState' :
      (ProductCallerAwareTail.blockPaddedSourceConfig selected headSymbol rest
        (MachineDescription.encodeNat fuel).reverse callerData).state =
      blockSource.state := by
    simpa using hblockState
  have hblockTape' : Tape.Equiv
      (ProductCallerAwareTail.blockPaddedSourceConfig selected headSymbol rest
        (MachineDescription.encodeNat fuel).reverse callerData).tape
      blockSource.tape := by
    simpa using hblockTape
  let finish := finish_from_related_block_source selected headSymbol rest
    callerData fuel blockSource hblockState' hblockTape'
  have hfull := exactRun_trans (machine selected)
    htailOuter finish.run_exact
  exact ⟨finish.targetTape, tailSteps + finish.steps,
    by simpa [tailSteps, innerSource] using hfull,
    finish.targetTape_equiv⟩

def candidateHead (outer : Nat) : MachineCodeSymbol :=
  match outer with
  | 0 => MachineCodeSymbol.done
  | _ + 1 => MachineCodeSymbol.tick

def candidateRest (input : Word MachineCodeSymbol)
    (inner : Nat) : Nat -> Word MachineCodeSymbol
  | 0 => GeneratedCode.stageCode input inner
  | outer + 1 => GeneratedCode.nestedStageCode input inner outer

theorem candidateHead_cons_candidateRest
    (input : Word MachineCodeSymbol) (inner outer : Nat) :
    candidateHead outer :: candidateRest input inner outer =
      GeneratedCode.nestedStageCode input inner outer := by
  cases outer <;> rfl

def CandidateMaterializeSpec {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (callerData input : Word MachineCodeSymbol)
    (inner outer selectedFuel : Nat) : Prop :=
  exists targetTape : Tape MachineCodeSymbol,
  exists steps : Nat,
    (machine selected).runConfigExact? steps
          (materializerConfig
            (FullMaterializerMachine.tailConfig selected
              (ProductCallerTail.NonemptyCallerTail.haltConfig
                (candidateHead outer)
                (MachineDescription.encodeNat selectedFuel).reverse
                (candidateRest input inner outer).reverse callerData))) =
        some
          { state := (machine selected).halt
            tape := targetTape } ∧
      Tape.Equiv targetTape
        (CandidateKernel.ProbeReturn.candidateTape selected callerData input
          inner outer selectedFuel)

theorem materialize_candidate_from_tail {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (callerData input : Word MachineCodeSymbol)
    (inner outer selectedFuel : Nat) :
    CandidateMaterializeSpec selected callerData input
      inner outer selectedFuel := by
  rcases materialize_nonempty_from_tail selected
      (candidateHead outer) (candidateRest input inner outer)
      callerData selectedFuel with
    ⟨targetTape, steps, hrun, htape⟩
  refine ⟨targetTape, steps, hrun, ?_⟩
  rw [CandidateKernel.ProbeReturn.candidateTape_eq_canonical_input]
  simpa [candidateHead_cons_candidateRest] using htape

abbrev SchedulerFrame := Scheduler.Layout.Frame

def schedulerCallerData (frame : SchedulerFrame) :
    Word MachineCodeSymbol :=
  Scheduler.Layout.encode frame

def schedulerTailSource {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : SchedulerFrame) :
    TuringMachine.Configuration MachineCodeSymbol (Control selected) :=
  materializerConfig
    (FullMaterializerMachine.tailConfig selected
      (ProductCallerTail.NonemptyCallerTail.sourceConfig
        (MachineDescription.encodeNat frame.cursor.selectedFuel).reverse
        (candidateHead frame.cursor.outer)
        (candidateRest frame.input frame.cursor.inner frame.cursor.outer)
        (schedulerCallerData frame)))

def schedulerTailHandoff {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : SchedulerFrame) :
    TuringMachine.Configuration MachineCodeSymbol (Control selected) :=
  materializerConfig
    (FullMaterializerMachine.tailConfig selected
      (ProductCallerTail.NonemptyCallerTail.haltConfig
        (candidateHead frame.cursor.outer)
        (MachineDescription.encodeNat frame.cursor.selectedFuel).reverse
        (candidateRest frame.input frame.cursor.inner
          frame.cursor.outer).reverse
        (schedulerCallerData frame)))

theorem schedulerTailSource_left {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : SchedulerFrame) :
    (schedulerTailSource selected frame).tape.left =
      (MachineDescription.encodeNat frame.cursor.selectedFuel).reverse.map
        some := by
  rfl

theorem schedulerTailSource_head {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : SchedulerFrame) :
    (schedulerTailSource selected frame).tape.head =
      some (candidateHead frame.cursor.outer) := by
  rfl

theorem schedulerTailSource_right {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : SchedulerFrame) :
    (schedulerTailSource selected frame).tape.right =
      List.append
        ((candidateRest frame.input frame.cursor.inner
          frame.cursor.outer).map some)
        (none :: none :: none :: (schedulerCallerData frame).map some) := by
  rfl

theorem scheduler_tail_to_handoff_run_exact {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : SchedulerFrame) :
    (machine selected).runConfigExact?
        ((candidateRest frame.input frame.cursor.inner
          frame.cursor.outer).length + 4)
        (schedulerTailSource selected frame) =
      some (schedulerTailHandoff selected frame) := by
  have htail := ProductCallerTail.NonemptyCallerTail.run_exact
    (MachineDescription.encodeNat frame.cursor.selectedFuel).reverse
    (candidateHead frame.cursor.outer)
    (candidateRest frame.input frame.cursor.inner frame.cursor.outer)
    (schedulerCallerData frame)
  have hmaterializer := FullMaterializerMachine.tail_run_of_eq_some
    selected
    ((candidateRest frame.input frame.cursor.inner
      frame.cursor.outer).length + 4) _ _ htail
  exact materializer_run_lift selected hmaterializer

def SchedulerCandidateMaterializeSpec {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : SchedulerFrame) : Prop :=
  exists targetTape : Tape MachineCodeSymbol,
  exists steps : Nat,
    (machine selected).runConfigExact? steps
          (schedulerTailSource selected frame) =
        some
          { state := (machine selected).halt
            tape := targetTape } ∧
      Tape.Equiv targetTape
        (CandidateKernel.ProbeReturn.candidateTape selected
          (schedulerCallerData frame) frame.input
          frame.cursor.inner frame.cursor.outer
          frame.cursor.selectedFuel)

theorem materialize_scheduler_candidate {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : SchedulerFrame) :
    SchedulerCandidateMaterializeSpec selected frame := by
  have htail := scheduler_tail_to_handoff_run_exact selected frame
  rcases materialize_candidate_from_tail selected
      (schedulerCallerData frame) frame.input frame.cursor.inner
      frame.cursor.outer frame.cursor.selectedFuel with
    ⟨targetTape, finishSteps, hfinish, htape⟩
  refine ⟨targetTape,
    (candidateRest frame.input frame.cursor.inner
      frame.cursor.outer).length + 4 + finishSteps, ?_, htape⟩
  exact exactRun_trans (machine selected) htail hfinish

end FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.CandidateMaterializer
