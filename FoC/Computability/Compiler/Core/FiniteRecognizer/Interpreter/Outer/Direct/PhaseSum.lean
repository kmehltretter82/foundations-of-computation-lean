import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Outer.Direct
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseRetarget

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.ZeroFinalPhaseSum

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep

/-!
# Finite zero-branch comparator materializer

This finite phase sum implements the three pieces specified by
`FinalComparatorMaterialization`: insert the comparator header, locate the
start-field boundary, and insert the blank/transition separator. Its terminal
state exposes a tape equivalent to the runtime comparator source. The
enclosing interpreter retargets that state directly into the comparator
phase.
-/

inductive Control where
  | header (state : InsertRestagedMachine.Control)
  | boundary (state : StartBoundaryLocator.Control)
  | separator (state : InsertRestagedMachine.Control)
  | ready
deriving DecidableEq

namespace Control

def elems : List Control :=
  (InsertRestagedMachine.Control.finite.elems.map Control.header) ++
    (StartBoundaryLocator.Control.finite.elems.map Control.boundary) ++
    (InsertRestagedMachine.Control.finite.elems.map Control.separator) ++
    [Control.ready]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro state
    cases state with
    | header inner =>
        simp [elems, InsertRestagedMachine.Control.finite.complete inner]
    | boundary inner =>
        simp [elems, StartBoundaryLocator.Control.finite.complete inner]
    | separator inner =>
        simp [elems, InsertRestagedMachine.Control.finite.complete inner]
    | ready => simp [elems]

end Control

def mapAction {innerState : Type}
    (target : innerState -> Control) :
    (Option MachineCodeSymbol × Direction × innerState) ->
      (Option MachineCodeSymbol × Direction × Control)
  | (write, direction, next) => (write, direction, target next)

def headerTarget : InsertRestagedMachine.Control -> Control
  | .rewind .gate => .boundary .needHeader
  | state => .header state

def boundaryTarget : StartBoundaryLocator.Control -> Control
  | .ready =>
      .separator (InsertRestagedMachine.machine separatorBuffer).start
  | state => .boundary state

def separatorTarget : InsertRestagedMachine.Control -> Control
  | .rewind .gate => .ready
  | state => .separator state

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .header state, read =>
      Option.map (mapAction headerTarget)
        ((InsertRestagedMachine.machine headerBuffer).transition state read)
  | .boundary state, read =>
      Option.map (mapAction boundaryTarget)
        (StartBoundaryLocator.machine.transition state read)
  | .separator state, read =>
      Option.map (mapAction separatorTarget)
        ((InsertRestagedMachine.machine separatorBuffer).transition state read)
  | .ready, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .header (InsertRestagedMachine.machine headerBuffer).start
  halt := .ready
  transition := transition
  statesFinite := Control.finite

def headerConfig
    (config : TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig headerTarget config

def boundaryConfig
    (config : TuringMachine.Configuration MachineCodeSymbol
      StartBoundaryLocator.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig boundaryTarget config

def separatorConfig
    (config : TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig separatorTarget config

def sourceConfig
    (leftPadding start halt rightPadding : Nat) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  headerConfig (headerInsertSourceConfig
    leftPadding start halt rightPadding)

def targetConfig
    (tape : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .ready, tape := tape }

theorem step_of_transition_embedding
    {innerState : Type}
    (inner : TuringMachine MachineCodeSymbol innerState)
    (embed : innerState -> Control)
    (hsimulate : forall
      (source target : innerState)
      (read write : Option MachineCodeSymbol)
      (direction : Direction),
        inner.transition source read = some (write, direction, target) ->
        transition (embed source) read =
          some (write, direction, embed target))
    (source target :
      TuringMachine.Configuration MachineCodeSymbol innerState)
    (hstep : inner.stepConfig source = some target) :
    machine.stepConfig
        (TuringMachine.PhaseEmbedding.liftConfig embed source) =
      some (TuringMachine.PhaseEmbedding.liftConfig embed target) := by
  cases source with
  | mk sourceState tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [machine]
      cases htransition :
          inner.transition sourceState (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨write, direction, targetState⟩
          rw [htransition] at hstep
          simp only at hstep
          simp only [TuringMachine.PhaseEmbedding.liftConfig]
          rw [hsimulate sourceState targetState (Tape.read tape) write
            direction htransition]
          cases hstep
          rfl

theorem computes_of_transition_embedding
    {innerState : Type}
    (inner : TuringMachine MachineCodeSymbol innerState)
    (embed : innerState -> Control)
    (hsimulate : forall
      (source target : innerState)
      (read write : Option MachineCodeSymbol)
      (direction : Direction),
        inner.transition source read = some (write, direction, target) ->
        transition (embed source) read =
          some (write, direction, embed target))
    {source target :
      TuringMachine.Configuration MachineCodeSymbol innerState}
    (hrun : TuringMachine.Computes inner source target) :
    TuringMachine.Computes machine
      (TuringMachine.PhaseEmbedding.liftConfig embed source)
      (TuringMachine.PhaseEmbedding.liftConfig embed target) := by
  rcases TuringMachine.computes_to_computesIn hrun with ⟨steps, hrunIn⟩
  apply TuringMachine.computesIn_to_computes
  apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
  apply TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    embed
  · intro source target hstep
    exact step_of_transition_embedding inner embed hsimulate source target
      hstep
  · exact TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr hrunIn

theorem header_transition_of_eq_some
    (source target : InsertRestagedMachine.Control)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (htransition :
      (InsertRestagedMachine.machine headerBuffer).transition source read =
        some (write, direction, target)) :
    transition (headerTarget source) read =
      some (write, direction, headerTarget target) := by
  cases source with
  | edit inner =>
      simp [headerTarget, transition, htransition, mapAction]
  | rewind inner =>
      cases inner with
      | start =>
          simp [InsertRestagedMachine.machine,
            InsertRestagedMachine.transition, RewindWord.transition]
            at htransition
          rcases htransition with ⟨rfl, rfl, rfl⟩
          rfl
      | scan =>
          cases read with
          | none =>
              simp [InsertRestagedMachine.machine,
                InsertRestagedMachine.transition, RewindWord.transition]
                at htransition
              rcases htransition with ⟨rfl, rfl, rfl⟩
              rfl
          | some symbol =>
              simp [InsertRestagedMachine.machine,
                InsertRestagedMachine.transition, RewindWord.transition]
                at htransition
              rcases htransition with ⟨rfl, rfl, rfl⟩
              rfl
      | gate =>
          simp [InsertRestagedMachine.machine,
            InsertRestagedMachine.transition, RewindWord.transition]
            at htransition

theorem boundary_transition_of_eq_some
    (source target : StartBoundaryLocator.Control)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (htransition : StartBoundaryLocator.machine.transition source read =
      some (write, direction, target)) :
    transition (boundaryTarget source) read =
      some (write, direction, boundaryTarget target) := by
  cases source <;> cases read with
  | none =>
      simp [StartBoundaryLocator.machine,
        StartBoundaryLocator.transition] at htransition
  | some symbol =>
      cases symbol <;>
        simp [StartBoundaryLocator.machine,
          StartBoundaryLocator.transition] at htransition
      all_goals rcases htransition with ⟨rfl, rfl, rfl⟩ <;> rfl

theorem separator_transition_of_eq_some
    (source target : InsertRestagedMachine.Control)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (htransition :
      (InsertRestagedMachine.machine separatorBuffer).transition source read =
        some (write, direction, target)) :
    transition (separatorTarget source) read =
      some (write, direction, separatorTarget target) := by
  cases source with
  | edit inner =>
      simp [separatorTarget, transition, htransition, mapAction]
  | rewind inner =>
      cases inner with
      | start =>
          simp [InsertRestagedMachine.machine,
            InsertRestagedMachine.transition, RewindWord.transition]
            at htransition
          rcases htransition with ⟨rfl, rfl, rfl⟩
          rfl
      | scan =>
          cases read with
          | none =>
              simp [InsertRestagedMachine.machine,
                InsertRestagedMachine.transition, RewindWord.transition]
                at htransition
              rcases htransition with ⟨rfl, rfl, rfl⟩
              rfl
          | some symbol =>
              simp [InsertRestagedMachine.machine,
                InsertRestagedMachine.transition, RewindWord.transition]
                at htransition
              rcases htransition with ⟨rfl, rfl, rfl⟩
              rfl
      | gate =>
          simp [InsertRestagedMachine.machine,
            InsertRestagedMachine.transition, RewindWord.transition]
            at htransition

theorem header_computes
    {source target : TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control}
    (hrun : TuringMachine.Computes
      (InsertRestagedMachine.machine headerBuffer) source target) :
    TuringMachine.Computes machine
      (headerConfig source) (headerConfig target) := by
  exact computes_of_transition_embedding
    (InsertRestagedMachine.machine headerBuffer) headerTarget
      header_transition_of_eq_some hrun

theorem boundary_computes
    {source target : TuringMachine.Configuration MachineCodeSymbol
      StartBoundaryLocator.Control}
    (hrun : TuringMachine.Computes
      StartBoundaryLocator.machine source target) :
    TuringMachine.Computes machine
      (boundaryConfig source) (boundaryConfig target) := by
  exact computes_of_transition_embedding StartBoundaryLocator.machine
    boundaryTarget boundary_transition_of_eq_some hrun

theorem separator_computes
    {source target : TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control}
    (hrun : TuringMachine.Computes
      (InsertRestagedMachine.machine separatorBuffer) source target) :
    TuringMachine.Computes machine
      (separatorConfig source) (separatorConfig target) := by
  exact computes_of_transition_embedding
    (InsertRestagedMachine.machine separatorBuffer) separatorTarget
      separator_transition_of_eq_some hrun

/-- The complete finite materializer route, retaining the authoritative tape
equivalence to the shared runtime comparator source. -/
theorem computes_to_ready
    (leftPadding start halt rightPadding : Nat) :
    exists comparatorTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        (sourceConfig leftPadding start halt rightPadding)
        (targetConfig comparatorTape) ∧
      Tape.Equiv comparatorTape
        (finalComparatorSourceConfig start halt []).tape := by
  rcases finalComparator_materialization
      leftPadding start halt rightPadding with
    ⟨headerTape, boundaryTape, comparatorTape,
      hheader, _hheaderEquiv, hboundary, _hboundaryEquiv,
      hseparator, hcomparatorEquiv, _hcompare⟩
  have hheaderComputes : TuringMachine.Computes
      (InsertRestagedMachine.machine headerBuffer)
      (headerInsertSourceConfig leftPadding start halt rightPadding)
      { state := InsertRestagedMachine.Control.rewind .gate
        tape := headerTape } :=
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hheader)
  have hseparatorComputes : TuringMachine.Computes
      (InsertRestagedMachine.machine separatorBuffer)
      (separatorInsertSourceConfig boundaryTape)
      { state := InsertRestagedMachine.Control.rewind .gate
        tape := comparatorTape } :=
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hseparator)
  have hfirst := header_computes hheaderComputes
  have hsecond := boundary_computes hboundary
  have hthird := separator_computes hseparatorComputes
  refine ⟨comparatorTape, ?_, hcomparatorEquiv⟩
  exact TuringMachine.computes_trans hfirst
    (TuringMachine.computes_trans
      (by
        simpa [headerConfig, headerTarget, boundaryConfig,
          boundaryTarget,
          TuringMachine.PhaseEmbedding.liftConfig,
          separatorInsertSourceConfig] using hsecond)
      (by
        simpa [boundaryConfig, boundaryTarget, separatorConfig,
          separatorTarget, separatorInsertSourceConfig,
          InsertRestagedMachine.machine,
          TuringMachine.PhaseEmbedding.liftConfig,
          targetConfig] using hthird))

theorem haltingTransitionsDisabled :
    TuringMachine.HaltingTransitionsDisabled machine := by
  intro read
  rfl


namespace Decision

inductive Control where
  | materialize (state : FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.Control)
  | compare (state : RuntimeKeyComparatorState)
  | accept
  | reject
deriving DecidableEq

namespace Control

def elems : List Control :=
  FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.Control.finite.elems.map Control.materialize ++
    RuntimeKeyComparatorState.finite.elems.map Control.compare ++
    [Control.accept, Control.reject]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro state
    cases state with
    | materialize inner =>
        simp [elems,
          FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.Control.finite.complete inner]
    | compare inner =>
        simp [elems, RuntimeKeyComparatorState.finite.complete inner]
    | accept => simp [elems]
    | reject => simp [elems]

end Control

def mapAction {innerState : Type}
    (target : innerState -> Control) :
    (Option MachineCodeSymbol × Direction × innerState) ->
      (Option MachineCodeSymbol × Direction × Control)
  | (write, direction, next) => (write, direction, target next)

def materializeTarget : FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.Control -> Control
  | .ready => .compare .needHeader
  | state => .materialize state

def compareTarget : RuntimeKeyComparatorState -> Control
  | .matched => .accept
  | .missed => .reject
  | state => .compare state

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .materialize state, read =>
      Option.map (mapAction materializeTarget)
        (FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.machine.transition state read)
  | .compare state, read =>
      Option.map (mapAction compareTarget)
        (runtimeKeyComparatorMachine.transition state read)
  | .accept, _ => none
  | .reject, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .materialize FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.machine.start
  halt := .accept
  transition := transition
  statesFinite := Control.finite

def materializeConfig
    (config : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig materializeTarget config

def compareConfig
    (config : TuringMachine.Configuration MachineCodeSymbol
      RuntimeKeyComparatorState) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig compareTarget config

theorem step_of_transition_embedding
    {innerState : Type}
    (inner : TuringMachine MachineCodeSymbol innerState)
    (embed : innerState -> Control)
    (hsimulate : forall
      (source target : innerState)
      (read write : Option MachineCodeSymbol)
      (direction : Direction),
        inner.transition source read = some (write, direction, target) ->
        transition (embed source) read =
          some (write, direction, embed target))
    (source target :
      TuringMachine.Configuration MachineCodeSymbol innerState)
    (hstep : inner.stepConfig source = some target) :
    machine.stepConfig
        (TuringMachine.PhaseEmbedding.liftConfig embed source) =
      some (TuringMachine.PhaseEmbedding.liftConfig embed target) := by
  cases source with
  | mk sourceState tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [machine]
      cases htransition : inner.transition sourceState (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨write, direction, targetState⟩
          rw [htransition] at hstep
          simp only at hstep
          simp only [TuringMachine.PhaseEmbedding.liftConfig]
          rw [hsimulate sourceState targetState (Tape.read tape) write
            direction htransition]
          cases hstep
          rfl

theorem computes_of_transition_embedding
    {innerState : Type}
    (inner : TuringMachine MachineCodeSymbol innerState)
    (embed : innerState -> Control)
    (hsimulate : forall
      (source target : innerState)
      (read write : Option MachineCodeSymbol)
      (direction : Direction),
        inner.transition source read = some (write, direction, target) ->
        transition (embed source) read =
          some (write, direction, embed target))
    {source target :
      TuringMachine.Configuration MachineCodeSymbol innerState}
    (hrun : TuringMachine.Computes inner source target) :
    TuringMachine.Computes machine
      (TuringMachine.PhaseEmbedding.liftConfig embed source)
      (TuringMachine.PhaseEmbedding.liftConfig embed target) := by
  rcases TuringMachine.computes_to_computesIn hrun with ⟨steps, hrunIn⟩
  apply TuringMachine.computesIn_to_computes
  apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
  apply TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    embed
  · intro source target hstep
    exact step_of_transition_embedding inner embed hsimulate source target
      hstep
  · exact TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr hrunIn

theorem materialize_transition_of_eq_some
    (source target : FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.Control)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (htransition : FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.machine.transition source read =
      some (write, direction, target)) :
    transition (materializeTarget source) read =
      some (write, direction, materializeTarget target) := by
  have hsource :
      materializeTarget source = .materialize source := by
    cases source <;> try rfl
    change none = some (write, direction, target) at htransition
    contradiction
  rw [hsource]
  simp only [transition]
  rw [htransition]
  rfl

theorem compare_transition_of_eq_some
    (source target : RuntimeKeyComparatorState)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (htransition : runtimeKeyComparatorMachine.transition source read =
      some (write, direction, target)) :
    transition (compareTarget source) read =
      some (write, direction, compareTarget target) := by
  have hsource : compareTarget source = .compare source := by
    cases source <;> try rfl
    all_goals
      change none = some (write, direction, target) at htransition
      contradiction
  rw [hsource]
  simp only [transition]
  rw [htransition]
  rfl

theorem materialize_computes
    {source target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.Control}
    (hrun : TuringMachine.Computes FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.machine
      source target) :
    TuringMachine.Computes machine
      (materializeConfig source) (materializeConfig target) :=
  computes_of_transition_embedding FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.machine
    materializeTarget materialize_transition_of_eq_some hrun

theorem compare_computes
    {source target : TuringMachine.Configuration MachineCodeSymbol
      RuntimeKeyComparatorState}
    (hrun : TuringMachine.Computes runtimeKeyComparatorMachine
      source target) :
    TuringMachine.Computes machine
      (compareConfig source) (compareConfig target) :=
  computes_of_transition_embedding runtimeKeyComparatorMachine
    compareTarget compare_transition_of_eq_some hrun

def sourceConfig
    (leftPadding start halt rightPadding : Nat) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  materializeConfig
    (FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.sourceConfig
      leftPadding start halt rightPadding)

def decisionConfig
    (start halt : Nat) (tape : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := if start = halt then .accept else .reject
    tape := tape }

theorem computes_to_decision
    (leftPadding start halt rightPadding : Nat) :
    exists finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        (sourceConfig leftPadding start halt rightPadding)
        (decisionConfig start halt finalTape) := by
  rcases FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.computes_to_ready
      leftPadding start halt rightPadding with
    ⟨comparatorTape, hmaterialize, hcomparatorTape⟩
  have hmaterialize' := materialize_computes hmaterialize
  have hcanonical := finalComparator_computes_exact start halt []
  rcases TuringMachine.computes_to_computesIn hcanonical with
    ⟨steps, hcanonicalIn⟩
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      hcanonicalIn (Tape.Equiv.symm hcomparatorTape) with
    ⟨actualTarget, hactualRun, hactualState, _hactualTape⟩
  rcases actualTarget with ⟨actualState, actualTape⟩
  simp only at hactualState
  subst actualState
  have hcompare := compare_computes
    (TuringMachine.computesIn_to_computes hactualRun)
  refine ⟨actualTape, TuringMachine.computes_trans hmaterialize' ?_⟩
  by_cases heq : start = halt
  · simpa [materializeConfig, materializeTarget, compareConfig,
      compareTarget, FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.targetConfig,
      finalComparatorSourceConfig, finalComparatorTargetConfig,
      decisionConfig, heq,
      TuringMachine.PhaseEmbedding.liftConfig] using hcompare
  · simpa [materializeConfig, materializeTarget, compareConfig,
      compareTarget, FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.targetConfig,
      finalComparatorSourceConfig, finalComparatorTargetConfig,
      decisionConfig, heq,
      TuringMachine.PhaseEmbedding.liftConfig] using hcompare

theorem reject_transition_none
    (read : Option MachineCodeSymbol) :
    machine.transition .reject read = none := by
  rfl

theorem haltsFrom_iff
    (leftPadding start halt rightPadding : Nat) :
    TuringMachine.HaltsFrom machine
        (sourceConfig leftPadding start halt rightPadding) ↔
      start = halt := by
  constructor
  · intro hhalts
    by_cases heq : start = halt
    · exact heq
    · rcases computes_to_decision
          leftPadding start halt rightPadding with
        ⟨finalTape, hrun⟩
      have hreject : (decisionConfig start halt finalTape).state = .reject := by
        simp [decisionConfig, heq]
      have hnot :=
        TuringMachine.StuckSink.not_haltsFrom_of_computes_to_stuck_nonhalt
          (M := machine)
          (by intro read; rfl)
          (by simpa [hreject] using hrun)
          (by simp [TuringMachine.Halted, machine, decisionConfig, heq])
          (by
            intro next
            apply TuringMachine.not_step_of_transition_eq_none
            simpa [decisionConfig, heq] using
              reject_transition_none (Tape.read finalTape))
      exact False.elim (hnot hhalts)
  · intro heq
    rcases computes_to_decision
        leftPadding start halt rightPadding with
      ⟨finalTape, hrun⟩
    apply TuringMachine.halts_from_of_computes hrun
    simp [TuringMachine.Halted, decisionConfig, machine, heq]


end Decision

end FiniteRecognizer.Interpreter.ZeroFinalPhaseSum
end Computability
end FoC
