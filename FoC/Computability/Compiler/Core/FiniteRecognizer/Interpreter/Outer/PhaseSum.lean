import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Parser.Branch.PhaseSum
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Parser.Branch.Projection
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Parser.Branch.Canonical
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.PhaseSum.Routes
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Outer.ParserInversion
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Outer.PublicBoundary

namespace FoC
namespace Computability

open Languages

namespace Section53OuterPhaseSumGeneric

abbrev ParserControl := Section53ParserBranchPhaseSum.Control
abbrev RuntimeControl := Section53RuntimePhaseSum.Control

/-!
# Interpreter phase composition

This module joins the concrete parser/direct-decision machine, the positive
initializer contract, and the concrete bounded runtime. The concrete
specialization instantiates the initializer contract with one finite control
type.
-/

inductive Control (initializerState : Type) where
  | parser (state : ParserControl)
  | initializer (state : initializerState)
  | runtime (state : RuntimeControl)
  | accept
  | reject
deriving DecidableEq

namespace Control

def elems
    (initializerFinite : Foundation.FiniteType initializerState) :
    List (Control initializerState) :=
  Section53ParserBranchPhaseSum.Control.finite.elems.map Control.parser ++
    initializerFinite.elems.map Control.initializer ++
    Section53RuntimePhaseSum.Control.finite.elems.map Control.runtime ++
    [Control.accept, Control.reject]

def finite
    (initializerFinite : Foundation.FiniteType initializerState) :
    Foundation.FiniteType (Control initializerState) where
  elems := elems initializerFinite
  complete := by
    intro state
    cases state with
    | parser inner =>
        simp [elems,
          Section53ParserBranchPhaseSum.Control.finite.complete inner]
    | initializer inner =>
        simp [elems, initializerFinite.complete inner]
    | runtime inner =>
        simp [elems, Section53RuntimePhaseSum.Control.finite.complete inner]
    | accept => simp [elems]
    | reject => simp [elems]

end Control

def mapAction {sourceState targetState : Type}
    (embed : sourceState -> targetState) :
    (Option MachineCodeSymbol × Direction × sourceState) ->
      (Option MachineCodeSymbol × Direction × targetState)
  | (write, direction, next) => (write, direction, embed next)

private theorem haltsFrom_tail_of_step
    {M : TuringMachine symbol state}
    (hstop : TuringMachine.HaltingTransitionsDisabled M)
    {source next : TuringMachine.Configuration symbol state}
    (hstep : TuringMachine.Step M source next)
    (hhalts : TuringMachine.HaltsFrom M source) :
    TuringMachine.HaltsFrom M next := by
  rcases TuringMachine.halts_from_to_halts_from_in hhalts with
    ⟨steps, hhaltsIn⟩
  cases steps with
  | zero =>
      have hhalted := TuringMachine.haltsFromIn_zero_iff.mp hhaltsIn
      exact False.elim (TuringMachine.no_step_from_halted hstop hhalted hstep)
  | succ steps =>
      exact TuringMachine.halts_from_in_to_halts_from
        (TuringMachine.haltsFromIn_tail_of_step hstep hhaltsIn)

/-- For a deterministic machine with disabled halt transitions, a known
computation prefix can be cancelled from ordinary halting. -/
theorem haltsFrom_iff_after_computes
    {M : TuringMachine symbol state}
    (hstop : TuringMachine.HaltingTransitionsDisabled M)
    {source target : TuringMachine.Configuration symbol state}
    (hrun : TuringMachine.Computes M source target) :
    TuringMachine.HaltsFrom M source ↔
      TuringMachine.HaltsFrom M target := by
  constructor
  · intro hhalts
    induction hrun with
    | refl _ => exact hhalts
    | step hstep _ ih =>
        exact ih (haltsFrom_tail_of_step hstop hstep hhalts)
  · exact TuringMachine.halts_from_of_computes_prefix hrun

def parserEmbed
    (initializerEntry : Option MachineCodeSymbol -> initializerState) :
    ParserControl -> Control initializerState
  | .positiveReady saved => .initializer (initializerEntry saved)
  | .accept => .accept
  | .reject => .reject
  | state => .parser state

/-- The initializer enters the runtime at the already-materialized query
scan, not at the runtime machine's clean-input parser start. -/
def runtimeLoopEntry : RuntimeControl :=
  Section53RuntimePhaseSum.scanEmbed
    (.inner Section53UniformInterpreterOneStep.RuntimeKeyComparatorState.scanQuery)

def initializerEmbed [DecidableEq initializerState]
    (initializerReady : initializerState) :
    initializerState -> Control initializerState
  | state =>
      if state = initializerReady then
        .runtime runtimeLoopEntry
      else
        .initializer state

def runtimeEmbed : RuntimeControl -> Control initializerState
  | .accept => .accept
  | .reject => .reject
  | state => .runtime state

def transition [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState) :
    Control initializerState -> Option MachineCodeSymbol ->
      Option
        (Option MachineCodeSymbol × Direction × Control initializerState)
  | .parser state, read =>
      Option.map (mapAction (parserEmbed initializerEntry))
        (Section53ParserBranchPhaseSum.machine.transition state read)
  | .initializer state, read =>
      Option.map (mapAction (initializerEmbed initializerReady))
        (initializer.transition state read)
  | .runtime state, read =>
      Option.map (mapAction runtimeEmbed)
        (Section53RuntimePhaseSum.machine.transition state read)
  | .accept, _ => none
  | .reject, _ => none

def machine [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState) :
    TuringMachine MachineCodeSymbol (Control initializerState) where
  start := .parser Section53ParserBranchPhaseSum.machine.start
  halt := .accept
  transition := transition initializer initializerEntry initializerReady
  statesFinite := Control.finite initializer.statesFinite

def parserConfig
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (config : TuringMachine.Configuration MachineCodeSymbol ParserControl) :
    TuringMachine.Configuration MachineCodeSymbol (Control initializerState) :=
  TuringMachine.PhaseEmbedding.liftConfig
    (parserEmbed initializerEntry) config

def initializerConfig [DecidableEq initializerState]
    (initializerReady : initializerState)
    (config : TuringMachine.Configuration MachineCodeSymbol initializerState) :
    TuringMachine.Configuration MachineCodeSymbol (Control initializerState) :=
  TuringMachine.PhaseEmbedding.liftConfig
    (initializerEmbed initializerReady) config

def runtimeConfig
    (config : TuringMachine.Configuration MachineCodeSymbol RuntimeControl) :
    TuringMachine.Configuration MachineCodeSymbol (Control initializerState) :=
  TuringMachine.PhaseEmbedding.liftConfig runtimeEmbed config

def sourceConfig
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (tokens : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control initializerState) :=
  parserConfig initializerEntry
    (Section53ParserBranchPhaseSum.sourceConfig tokens)

def prefixEmbed
    (initializerEntry : Option MachineCodeSymbol -> initializerState) :
    Section53ParserPrefixPhaseSum.Control -> Control initializerState :=
  fun state =>
    parserEmbed initializerEntry
      (Section53ParserBranchPhaseSum.parserTarget state)

def prefixConfig
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (config : TuringMachine.Configuration MachineCodeSymbol
      Section53ParserPrefixPhaseSum.Control) :
    TuringMachine.Configuration MachineCodeSymbol (Control initializerState) :=
  TuringMachine.PhaseEmbedding.liftConfig
    (prefixEmbed initializerEntry) config

theorem sourceConfig_eq_prefixConfig
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (tokens : Word MachineCodeSymbol) :
    sourceConfig initializerEntry tokens =
      prefixConfig initializerEntry
        (Section53ParserPrefixPhaseSum.sourceConfig tokens) := by
  rfl

theorem sourceConfig_eq_initial [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    (tokens : Word MachineCodeSymbol) :
    sourceConfig initializerEntry tokens =
      TuringMachine.initial
        (machine initializer initializerEntry initializerReady) tokens := by
  cases tokens <;> rfl

theorem accept_transition_none [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    (read : Option MachineCodeSymbol) :
    (machine initializer initializerEntry initializerReady).transition
        .accept read = none := by
  rfl

theorem reject_transition_none [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    (read : Option MachineCodeSymbol) :
    (machine initializer initializerEntry initializerReady).transition
        .reject read = none := by
  rfl

theorem haltingTransitionsDisabled [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState) :
    TuringMachine.HaltingTransitionsDisabled
      (machine initializer initializerEntry initializerReady) := by
  intro read
  exact accept_transition_none initializer initializerEntry initializerReady
    read

theorem step_of_transition_embedding
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    {innerState : Type}
    (inner : TuringMachine MachineCodeSymbol innerState)
    (embed : innerState -> Control initializerState)
    (hsimulate : forall
      (source target : innerState)
      (read write : Option MachineCodeSymbol)
      (direction : Direction),
        inner.transition source read = some (write, direction, target) ->
        transition initializer initializerEntry initializerReady
            (embed source) read =
          some (write, direction, embed target))
    (source target :
      TuringMachine.Configuration MachineCodeSymbol innerState)
    (hstep : inner.stepConfig source = some target) :
    (machine initializer initializerEntry initializerReady).stepConfig
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
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    {innerState : Type}
    (inner : TuringMachine MachineCodeSymbol innerState)
    (embed : innerState -> Control initializerState)
    (hsimulate : forall
      (source target : innerState)
      (read write : Option MachineCodeSymbol)
      (direction : Direction),
        inner.transition source read = some (write, direction, target) ->
        transition initializer initializerEntry initializerReady
            (embed source) read =
          some (write, direction, embed target))
    {source target :
      TuringMachine.Configuration MachineCodeSymbol innerState}
    (hrun : TuringMachine.Computes inner source target) :
    TuringMachine.Computes
      (machine initializer initializerEntry initializerReady)
      (TuringMachine.PhaseEmbedding.liftConfig embed source)
      (TuringMachine.PhaseEmbedding.liftConfig embed target) := by
  rcases TuringMachine.computes_to_computesIn hrun with ⟨steps, hrunIn⟩
  apply TuringMachine.computesIn_to_computes
  apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
  apply TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    embed
  · intro source target hstep
    exact step_of_transition_embedding initializer initializerEntry
      initializerReady inner embed hsimulate source target hstep
  · exact TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr hrunIn

theorem parser_transition_of_eq_some
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    (source target : ParserControl)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (htransition : Section53ParserBranchPhaseSum.machine.transition
      source read = some (write, direction, target)) :
    transition initializer initializerEntry initializerReady
        (parserEmbed initializerEntry source) read =
      some (write, direction, parserEmbed initializerEntry target) := by
  have hsource : parserEmbed initializerEntry source = .parser source := by
    cases source <;> try rfl
    all_goals
      change none = some (write, direction, target) at htransition
      contradiction
  rw [hsource]
  simp only [transition]
  rw [htransition]
  rfl

theorem initializer_transition_of_eq_some
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    (hready : forall read,
      initializer.transition initializerReady read = none)
    (source target : initializerState)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (htransition : initializer.transition source read =
      some (write, direction, target)) :
    transition initializer initializerEntry initializerReady
        (initializerEmbed initializerReady source) read =
      some (write, direction, initializerEmbed initializerReady target) := by
  have hne : source ≠ initializerReady := by
    intro heq
    subst source
    rw [hready read] at htransition
    contradiction
  rw [initializerEmbed]
  simp only [if_neg hne, transition]
  rw [htransition]
  rfl

theorem runtime_transition_of_eq_some
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    (source target : RuntimeControl)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (htransition : Section53RuntimePhaseSum.machine.transition source read =
      some (write, direction, target)) :
    transition initializer initializerEntry initializerReady
        (runtimeEmbed source) read =
      some (write, direction, runtimeEmbed target) := by
  have hsource : runtimeEmbed source =
      (Control.runtime source : Control initializerState) := by
    cases source <;> try rfl
    all_goals
      change none = some (write, direction, target) at htransition
      contradiction
  rw [hsource]
  simp only [transition]
  rw [htransition]
  rfl

theorem parser_computes
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    {source target :
      TuringMachine.Configuration MachineCodeSymbol ParserControl}
    (hrun : TuringMachine.Computes Section53ParserBranchPhaseSum.machine
      source target) :
    TuringMachine.Computes
      (machine initializer initializerEntry initializerReady)
      (parserConfig initializerEntry source)
      (parserConfig initializerEntry target) :=
  computes_of_transition_embedding initializer initializerEntry
    initializerReady Section53ParserBranchPhaseSum.machine
      (parserEmbed initializerEntry)
      (parser_transition_of_eq_some initializer initializerEntry
        initializerReady) hrun

theorem initializer_computes
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    (hready : forall read,
      initializer.transition initializerReady read = none)
    {source target :
      TuringMachine.Configuration MachineCodeSymbol initializerState}
    (hrun : TuringMachine.Computes initializer source target) :
    TuringMachine.Computes
      (machine initializer initializerEntry initializerReady)
      (initializerConfig initializerReady source)
      (initializerConfig initializerReady target) :=
  computes_of_transition_embedding initializer initializerEntry
    initializerReady initializer (initializerEmbed initializerReady)
      (initializer_transition_of_eq_some initializer initializerEntry
        initializerReady hready) hrun

theorem runtime_computes
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    {source target :
      TuringMachine.Configuration MachineCodeSymbol RuntimeControl}
    (hrun : TuringMachine.Computes Section53RuntimePhaseSum.machine
      source target) :
    TuringMachine.Computes
      (machine initializer initializerEntry initializerReady)
      (runtimeConfig source)
      (runtimeConfig target) :=
  computes_of_transition_embedding initializer initializerEntry
    initializerReady Section53RuntimePhaseSum.machine runtimeEmbed
      (runtime_transition_of_eq_some initializer initializerEntry
        initializerReady) hrun

def directDecisionConfig
    (start halt : Nat)
    (tape : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control initializerState) :=
  { state := if start = halt then .accept else .reject
    tape := tape }

theorem parserConfig_directDecisionConfig
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (start halt : Nat)
    (tape : Tape MachineCodeSymbol) :
    parserConfig initializerEntry
        (Section53ParserBranchPhaseSum.directDecisionConfig
          start halt tape) =
      directDecisionConfig start halt tape := by
  by_cases heq : start = halt <;>
    simp [parserConfig, Section53ParserBranchPhaseSum.directDecisionConfig,
      directDecisionConfig, parserEmbed,
      TuringMachine.PhaseEmbedding.liftConfig, heq]

/-- A direct parser decision has the same accept/reject behavior after being
embedded in the final phase sum. -/
theorem haltsFrom_iff_of_parser_computes_to_directDecision
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    {source : TuringMachine.Configuration MachineCodeSymbol ParserControl}
    (start halt : Nat)
    (finalTape : Tape MachineCodeSymbol)
    (hrun : TuringMachine.Computes Section53ParserBranchPhaseSum.machine
      source
      (Section53ParserBranchPhaseSum.directDecisionConfig
        start halt finalTape)) :
    TuringMachine.HaltsFrom
        (machine initializer initializerEntry initializerReady)
        (parserConfig initializerEntry source) ↔
      start = halt := by
  have houterRun := parser_computes initializer initializerEntry
    initializerReady hrun
  rw [parserConfig_directDecisionConfig] at houterRun
  constructor
  · intro hhalts
    by_cases heq : start = halt
    · exact heq
    · have hnot :=
        TuringMachine.StuckSink.not_haltsFrom_of_computes_to_stuck_nonhalt
          (M := machine initializer initializerEntry initializerReady)
          (by intro read; rfl)
          (by simpa [directDecisionConfig, heq] using houterRun)
          (by
            simp [TuringMachine.Halted, machine])
          (by
            intro next
            apply TuringMachine.not_step_of_transition_eq_none
            exact reject_transition_none initializer initializerEntry
              initializerReady (Tape.read finalTape))
      exact False.elim (hnot hhalts)
  · intro heq
    apply TuringMachine.halts_from_of_computes houterRun
    simp [TuringMachine.Halted, directDecisionConfig, machine, heq]

def RuntimeTerminal
    (config : TuringMachine.Configuration MachineCodeSymbol RuntimeControl) :
    Prop :=
  config.state = .accept ∨ config.state = .reject

private theorem runtimeEmbed_eq_active_runtime
    (source : TuringMachine.Configuration MachineCodeSymbol RuntimeControl)
    (hactive : ¬ RuntimeTerminal source) :
    runtimeEmbed source.state =
      (Control.runtime source.state : Control initializerState) := by
  rcases source with ⟨state, tape⟩
  cases state <;> try rfl
  · exact False.elim (hactive (Or.inl rfl))
  · exact False.elim (hactive (Or.inr rfl))

private theorem runtime_stepConfig_eq_map_of_embed_eq_runtime
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    (state : RuntimeControl)
    (tape : Tape MachineCodeSymbol)
    (hstate : runtimeEmbed state =
      (Control.runtime state : Control initializerState)) :
    (machine initializer initializerEntry initializerReady).stepConfig
        (runtimeConfig { state := state, tape := tape }) =
      Option.map runtimeConfig
        (Section53RuntimePhaseSum.machine.stepConfig
          { state := state, tape := tape }) := by
  unfold TuringMachine.stepConfig
  simp only [runtimeConfig, TuringMachine.PhaseEmbedding.liftConfig]
  rw [hstate]
  simp only [machine, transition]
  cases htransition : Section53RuntimePhaseSum.machine.transition state
      (Tape.read tape) with
  | none => simp
  | some action =>
      rcases action with ⟨write, direction, nextState⟩
      simp [mapAction, runtimeConfig,
        TuringMachine.PhaseEmbedding.liftConfig]

theorem active_runtime_stepConfig_eq_map
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    (source : TuringMachine.Configuration MachineCodeSymbol RuntimeControl)
    (hactive : ¬ RuntimeTerminal source) :
    (machine initializer initializerEntry initializerReady).stepConfig
        (runtimeConfig source) =
      Option.map runtimeConfig
        (Section53RuntimePhaseSum.machine.stepConfig source) := by
  rcases source with ⟨state, tape⟩
  exact runtime_stepConfig_eq_map_of_embed_eq_runtime
    initializer initializerEntry initializerReady state tape
      (runtimeEmbed_eq_active_runtime
        { state := state, tape := tape } hactive)

theorem active_runtime_step_inversion
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    (source : TuringMachine.Configuration MachineCodeSymbol RuntimeControl)
    (target : TuringMachine.Configuration MachineCodeSymbol
      (Control initializerState))
    (hactive : ¬ RuntimeTerminal source)
    (hstep : TuringMachine.Step
      (machine initializer initializerEntry initializerReady)
      (runtimeConfig source) target) :
    exists innerTarget : TuringMachine.Configuration MachineCodeSymbol
        RuntimeControl,
      TuringMachine.Step Section53RuntimePhaseSum.machine
          source innerTarget ∧
        target = runtimeConfig innerTarget := by
  have houter := TuringMachine.stepConfig_eq_some_iff_step.mpr hstep
  rw [active_runtime_stepConfig_eq_map initializer initializerEntry
    initializerReady source hactive] at houter
  cases hinner : Section53RuntimePhaseSum.machine.stepConfig source with
  | none => simp [hinner] at houter
  | some innerTarget =>
      simp [hinner] at houter
      subst target
      exact ⟨innerTarget,
        TuringMachine.stepConfig_eq_some_iff_step.mp hinner, rfl⟩

theorem active_runtimeConfig_not_halted
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    (source : TuringMachine.Configuration MachineCodeSymbol RuntimeControl)
    (hactive : ¬ RuntimeTerminal source) :
    ¬ TuringMachine.Halted
      (machine initializer initializerEntry initializerReady)
      (runtimeConfig source) := by
  have hstate : runtimeEmbed source.state =
      (Control.runtime source.state : Control initializerState) :=
    runtimeEmbed_eq_active_runtime source hactive
  intro hhalted
  change runtimeEmbed source.state =
    (Control.accept : Control initializerState) at hhalted
  rw [hstate] at hhalted
  contradiction

theorem exists_runtimeTerminal_of_haltsFromIn
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    {steps : Nat}
    {source : TuringMachine.Configuration MachineCodeSymbol RuntimeControl}
    (hhalts : TuringMachine.HaltsFromIn
      (machine initializer initializerEntry initializerReady) steps
      (runtimeConfig source)) :
    exists innerSteps : Nat,
    exists target : TuringMachine.Configuration MachineCodeSymbol
        RuntimeControl,
      innerSteps ≤ steps ∧
      TuringMachine.ComputesIn Section53RuntimePhaseSum.machine
          innerSteps source target ∧
        RuntimeTerminal target := by
  exact
    TuringMachine.PhaseExitProjection.exists_bounded_inner_exit_of_haltsFromIn_lift
      (runtimeEmbed : RuntimeControl -> Control initializerState)
      RuntimeTerminal
      (active_runtime_step_inversion initializer initializerEntry
        initializerReady)
      (active_runtimeConfig_not_halted initializer initializerEntry
        initializerReady)
      hhalts

/-- Entering the runtime phase does not change its halting behavior: the
runtime accept/reject terminals are retargeted to the unique final accept and
the final stuck reject of the enclosing interpreter. -/
theorem runtime_haltsFrom_iff
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    (source : TuringMachine.Configuration MachineCodeSymbol RuntimeControl) :
    TuringMachine.HaltsFrom
        (machine initializer initializerEntry initializerReady)
        (runtimeConfig source) ↔
      TuringMachine.HaltsFrom Section53RuntimePhaseSum.machine source := by
  constructor
  · intro houterHalts
    rcases TuringMachine.halts_from_to_halts_from_in houterHalts with
      ⟨steps, houterHaltsIn⟩
    rcases exists_runtimeTerminal_of_haltsFromIn initializer
        initializerEntry initializerReady houterHaltsIn with
      ⟨_innerSteps, target, _hbound, hrunIn, hterminal⟩
    rcases target with ⟨targetState, targetTape⟩
    rcases hterminal with haccept | hreject
    · change targetState = .accept at haccept
      subst targetState
      exact TuringMachine.halts_from_of_computes
        (TuringMachine.computesIn_to_computes hrunIn) (by rfl)
    · change targetState = .reject at hreject
      subst targetState
      have houterRun := runtime_computes initializer initializerEntry
        initializerReady
        (TuringMachine.computesIn_to_computes hrunIn)
      have hnot :=
        TuringMachine.StuckSink.not_haltsFrom_of_computes_to_stuck_nonhalt
          (M := machine initializer initializerEntry initializerReady)
          (by intro read; rfl)
          (by simpa [runtimeConfig, runtimeEmbed,
            TuringMachine.PhaseEmbedding.liftConfig] using houterRun)
          (by simp [TuringMachine.Halted, machine])
          (by
            intro next
            apply TuringMachine.not_step_of_transition_eq_none
            exact reject_transition_none initializer initializerEntry
              initializerReady (Tape.read targetTape))
      exact False.elim (hnot houterHalts)
  · intro hinnerHalts
    rcases hinnerHalts with ⟨final, hrun, hhalted⟩
    refine
      ⟨runtimeConfig final,
        runtime_computes initializer initializerEntry initializerReady hrun,
        ?_⟩
    change runtimeEmbed final.state =
      (Control.accept : Control initializerState)
    change final.state = Section53RuntimePhaseSum.machine.halt at hhalted
    rw [hhalted]
    rfl

def outerCanonicalSourceConfig
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control initializerState) :=
  parserConfig initializerEntry
    (Section53ParserCanonicalBranches.canonicalSourceConfig D fuel input)

/-- Concrete forward obligations needed from the parser and positive
initializer.  Runtime semantics and all outer phase plumbing are already
discharged generically. -/
structure CanonicalPhaseContract
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState) : Prop where
  entry_ne_ready :
    forall saved, initializerEntry saved ≠ initializerReady
  ready_transition_none :
    forall read, initializer.transition initializerReady read = none
  direct :
    forall (D : MachineDescription)
      (fuel : Nat)
      (input : Word MachineCodeSymbol),
      (fuel = 0 ∨ D.transitions = []) ->
      exists finalTape : Tape MachineCodeSymbol,
        TuringMachine.Computes Section53ParserBranchPhaseSum.machine
          (Section53ParserCanonicalBranches.canonicalSourceConfig
            D fuel input)
          (Section53ParserBranchPhaseSum.directDecisionConfig
            D.start D.halt finalTape)
  positive :
    forall (D : MachineDescription)
      (first : TransitionDescription)
      (rest : List TransitionDescription)
      (remainingFuel : Nat)
      (input : Word MachineCodeSymbol),
      D.transitions = first :: rest ->
      exists parserTape : Tape MachineCodeSymbol,
      exists initializerTape : Tape MachineCodeSymbol,
        TuringMachine.Computes Section53ParserBranchPhaseSum.machine
          (Section53ParserCanonicalBranches.canonicalSourceConfig
            D (remainingFuel + 1) input)
          { state := Section53ParserBranchPhaseSum.Control.positiveReady
              (transitionListParserSavedHead input)
            tape := parserTape } ∧
        TuringMachine.Computes initializer
          { state := initializerEntry (transitionListParserSavedHead input)
            tape := parserTape }
          { state := initializerReady
            tape := initializerTape } ∧
        Tape.Equiv
          (Section53BoundedLoopInduction.loopSourceConfig
            (Section53InitializerFrontier.initialConfiguration D input)
            (first :: rest) remainingFuel D.halt []).tape
          initializerTape

theorem directCanonical_haltsFrom_iff_haltsIn
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol)
    (hbranch : fuel = 0 ∨ D.transitions = [])
    (finalTape : Tape MachineCodeSymbol)
    (hrun : TuringMachine.Computes Section53ParserBranchPhaseSum.machine
      (Section53ParserCanonicalBranches.canonicalSourceConfig D fuel input)
      (Section53ParserBranchPhaseSum.directDecisionConfig
        D.start D.halt finalTape)) :
    TuringMachine.HaltsFrom
        (machine initializer initializerEntry initializerReady)
        (outerCanonicalSourceConfig initializerEntry D fuel input) ↔
      D.HaltsIn fuel
        (MachineDescription.encodeCodeWordAsInput input) := by
  exact Iff.trans
    (haltsFrom_iff_of_parser_computes_to_directDecision initializer
      initializerEntry initializerReady D.start D.halt finalTape hrun)
    (Section53SemanticAcceptance.direct_state_eq_iff_haltsIn
      D fuel input hbranch)

theorem positiveCanonical_haltsFrom_iff_haltsIn
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    (contract : CanonicalPhaseContract initializer initializerEntry
      initializerReady)
    (D : MachineDescription)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (remainingFuel : Nat)
    (input : Word MachineCodeSymbol)
    (htransitions : D.transitions = first :: rest) :
    TuringMachine.HaltsFrom
        (machine initializer initializerEntry initializerReady)
        (outerCanonicalSourceConfig initializerEntry D
          (remainingFuel + 1) input) ↔
      D.HaltsIn (remainingFuel + 1)
        (MachineDescription.encodeCodeWordAsInput input) := by
  rcases contract.positive D first rest remainingFuel input htransitions with
    ⟨parserTape, initializerTape, hparser, hinitializer, htape⟩
  have hparserOuter := parser_computes initializer initializerEntry
    initializerReady hparser
  have hinitializerOuter := initializer_computes initializer
    initializerEntry initializerReady contract.ready_transition_none
    hinitializer
  have hparserToInitializer :
      TuringMachine.Computes
        (machine initializer initializerEntry initializerReady)
        (outerCanonicalSourceConfig initializerEntry D
          (remainingFuel + 1) input)
        (initializerConfig initializerReady
          { state := initializerEntry
              (transitionListParserSavedHead input)
            tape := parserTape }) := by
    simpa [outerCanonicalSourceConfig, parserConfig, parserEmbed,
      initializerConfig, initializerEmbed,
      contract.entry_ne_ready,
      TuringMachine.PhaseEmbedding.liftConfig] using hparserOuter
  have hinitializerToRuntime :
      TuringMachine.Computes
        (machine initializer initializerEntry initializerReady)
        (initializerConfig initializerReady
          { state := initializerEntry
              (transitionListParserSavedHead input)
            tape := parserTape })
        (runtimeConfig
          (Section53BoundedLoopInduction.outerLoopConfig
            Section53RuntimePhaseSum.scanEmbed
            (Section53InitializerFrontier.initialConfiguration D input)
            (first :: rest) remainingFuel D.halt [] initializerTape)) := by
    simpa [initializerConfig, initializerEmbed, runtimeConfig,
      runtimeEmbed, runtimeLoopEntry, Section53RuntimePhaseSum.scanEmbed,
      Section53BoundedLoopInduction.outerLoopConfig,
      Section53BoundedLoopInduction.loopSourceConfig,
      Section53UniformInterpreterOneStep.RuntimeKeySingleKeyRepair.canonicalScanRowsConfig,
      Section53RuntimePhaseSum.machine,
      TuringMachine.PhaseEmbedding.liftConfig] using hinitializerOuter
  have hprefix := TuringMachine.computes_trans hparserToInitializer
    hinitializerToRuntime
  exact Iff.trans
    (haltsFrom_iff_after_computes
      (haltingTransitionsDisabled initializer initializerEntry
        initializerReady) hprefix)
    (Iff.trans
      (runtime_haltsFrom_iff initializer initializerEntry initializerReady _)
      (Section53SemanticAcceptance.positive_runtime_haltsFrom_iff_haltsIn
        D first rest htransitions remainingFuel input initializerTape htape))

theorem canonical_haltsFrom_iff_haltsIn
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    (contract : CanonicalPhaseContract initializer initializerEntry
      initializerReady)
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.HaltsFrom
        (machine initializer initializerEntry initializerReady)
        (outerCanonicalSourceConfig initializerEntry D fuel input) ↔
      D.HaltsIn fuel
        (MachineDescription.encodeCodeWordAsInput input) := by
  cases htransitions : D.transitions with
  | nil =>
      rcases contract.direct D fuel input (Or.inr htransitions) with
        ⟨finalTape, hrun⟩
      exact directCanonical_haltsFrom_iff_haltsIn initializer
        initializerEntry initializerReady D fuel input
        (Or.inr htransitions) finalTape hrun
  | cons first rest =>
      cases fuel with
      | zero =>
          rcases contract.direct D 0 input (Or.inl rfl) with
            ⟨finalTape, hrun⟩
          exact directCanonical_haltsFrom_iff_haltsIn initializer
            initializerEntry initializerReady D 0 input
            (Or.inl rfl) finalTape hrun
      | succ remainingFuel =>
          simpa [Nat.succ_eq_add_one] using
            positiveCanonical_haltsFrom_iff_haltsIn initializer
              initializerEntry initializerReady contract D first rest
              remainingFuel input htransitions

theorem outerCanonicalSourceConfig_eq_initial
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    outerCanonicalSourceConfig initializerEntry D fuel input =
      TuringMachine.initial
        (machine initializer initializerEntry initializerReady)
        (FiniteRecognizer.GeneratedCode.stageCode
          (List.append (MachineDescription.encodeDescription D) input)
          fuel) := by
  rw [FiniteRecognizer.GeneratedCode.stageCode_eq_encodeNatAppend]
  rw [← MachineDescription.encodeDescriptionAppend_eq_encodeDescription_append]
  rw [← sourceConfig_eq_initial initializer initializerEntry
    initializerReady]
  rfl

theorem canonicalStageSpec
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    (contract : CanonicalPhaseContract initializer initializerEntry
      initializerReady) :
    FiniteRecognizer.DecodedDescriptionCanonicalStageSpec
      (machine initializer initializerEntry initializerReady) := by
  intro D input fuel
  change TuringMachine.HaltsFrom
      (machine initializer initializerEntry initializerReady)
      (TuringMachine.initial
        (machine initializer initializerEntry initializerReady)
        (FiniteRecognizer.GeneratedCode.stageCode
          (List.append (MachineDescription.encodeDescription D) input)
          fuel)) ↔ _
  rw [← outerCanonicalSourceConfig_eq_initial initializer
    initializerEntry initializerReady]
  exact canonical_haltsFrom_iff_haltsIn initializer initializerEntry
    initializerReady contract D fuel input

private theorem parser_stepConfig_eq_map_of_embed_eq_parser
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    (state : ParserControl)
    (tape : Tape MachineCodeSymbol)
    (hstate : parserEmbed initializerEntry state = .parser state) :
    (machine initializer initializerEntry initializerReady).stepConfig
        (parserConfig initializerEntry { state := state, tape := tape }) =
      Option.map (parserConfig initializerEntry)
        (Section53ParserBranchPhaseSum.machine.stepConfig
          { state := state, tape := tape }) := by
  unfold TuringMachine.stepConfig
  simp only [parserConfig, TuringMachine.PhaseEmbedding.liftConfig]
  rw [hstate]
  simp only [machine, transition]
  cases htransition :
      Section53ParserBranchPhaseSum.machine.transition state
        (Tape.read tape) with
  | none => simp
  | some action =>
      rcases action with ⟨write, direction, nextState⟩
      simp [mapAction, parserConfig,
        TuringMachine.PhaseEmbedding.liftConfig]

private theorem active_prefix_stepConfig_eq_map_of_embed_eq_parser
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    (source : TuringMachine.Configuration MachineCodeSymbol
      Section53ParserPrefixPhaseSum.Control)
    (hactive : ¬ Section53ParserPrefixPhaseSum.SuccessfulTerminal source)
    (hstate : prefixEmbed initializerEntry source.state =
      .parser (Section53ParserBranchPhaseSum.parserTarget source.state)) :
    (machine initializer initializerEntry initializerReady).stepConfig
        (prefixConfig initializerEntry source) =
      Option.map (prefixConfig initializerEntry)
        (Section53ParserPrefixPhaseSum.machine.stepConfig source) := by
  rcases source with ⟨state, tape⟩
  have houter := parser_stepConfig_eq_map_of_embed_eq_parser
    initializer initializerEntry initializerReady
    (Section53ParserBranchPhaseSum.parserTarget state) tape hstate
  have hbranch :=
    Section53ParserBranchProjection.active_stepConfig_eq_map
      { state := state, tape := tape } hactive
  change
    Section53ParserBranchPhaseSum.machine.stepConfig
        { state := Section53ParserBranchPhaseSum.parserTarget state,
          tape := tape } =
      Option.map Section53ParserBranchPhaseSum.parserConfig
        (Section53ParserPrefixPhaseSum.machine.stepConfig
          { state := state, tape := tape }) at hbranch
  rw [hbranch] at houter
  rw [Option.map_map] at houter
  have hsourceConfig :
      parserConfig initializerEntry
          { state := Section53ParserBranchPhaseSum.parserTarget state,
            tape := tape } =
        prefixConfig initializerEntry { state := state, tape := tape } := by
    rfl
  have hconfigFunction :
      (parserConfig initializerEntry ∘
          Section53ParserBranchPhaseSum.parserConfig) =
        prefixConfig initializerEntry := by
    funext config
    rcases config with ⟨innerState, innerTape⟩
    rfl
  rw [hsourceConfig, hconfigFunction] at houter
  exact houter

/-- Before a successful prefix terminal, the final phase sum takes exactly
the embedded prefix step.  This is the sole operational fact needed to
project parser evidence from an arbitrary final-machine halting run. -/
theorem active_prefix_stepConfig_eq_map
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    (source : TuringMachine.Configuration MachineCodeSymbol
      Section53ParserPrefixPhaseSum.Control)
    (hactive : ¬ Section53ParserPrefixPhaseSum.SuccessfulTerminal source) :
    (machine initializer initializerEntry initializerReady).stepConfig
        (prefixConfig initializerEntry source) =
      Option.map (prefixConfig initializerEntry)
        (Section53ParserPrefixPhaseSum.machine.stepConfig source) := by
  rcases source with ⟨state, tape⟩
  cases state with
  | fuel fuelZero state =>
      exact active_prefix_stepConfig_eq_map_of_embed_eq_parser
        initializer initializerEntry initializerReady _ hactive rfl
  | header fuelZero state =>
      exact active_prefix_stepConfig_eq_map_of_embed_eq_parser
        initializer initializerEntry initializerReady _ hactive rfl
  | shift fuelZero state =>
      exact active_prefix_stepConfig_eq_map_of_embed_eq_parser
        initializer initializerEntry initializerReady _ hactive rfl
  | countValidate fuelZero =>
      exact active_prefix_stepConfig_eq_map_of_embed_eq_parser
        initializer initializerEntry initializerReady _ hactive rfl
  | countRewind fuelZero =>
      exact active_prefix_stepConfig_eq_map_of_embed_eq_parser
        initializer initializerEntry initializerReady _ hactive rfl
  | table fuelZero state =>
      cases state with
      | parser parserState =>
          cases parserState <;>
            exact active_prefix_stepConfig_eq_map_of_embed_eq_parser
              initializer initializerEntry initializerReady _ hactive rfl
      | ready saved =>
          exact False.elim (hactive ⟨fuelZero, Or.inr ⟨saved, rfl⟩⟩)
      | halt => rfl

theorem active_prefix_step_inversion
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    (source : TuringMachine.Configuration MachineCodeSymbol
      Section53ParserPrefixPhaseSum.Control)
    (target : TuringMachine.Configuration MachineCodeSymbol
      (Control initializerState))
    (hactive : ¬ Section53ParserPrefixPhaseSum.SuccessfulTerminal source)
    (hstep : TuringMachine.Step
      (machine initializer initializerEntry initializerReady)
      (prefixConfig initializerEntry source) target) :
    exists innerTarget : TuringMachine.Configuration MachineCodeSymbol
        Section53ParserPrefixPhaseSum.Control,
      TuringMachine.Step Section53ParserPrefixPhaseSum.machine
          source innerTarget ∧
        target = prefixConfig initializerEntry innerTarget := by
  have houter := TuringMachine.stepConfig_eq_some_iff_step.mpr hstep
  rw [active_prefix_stepConfig_eq_map initializer initializerEntry
    initializerReady source hactive] at houter
  cases hinner : Section53ParserPrefixPhaseSum.machine.stepConfig source with
  | none => simp [hinner] at houter
  | some innerTarget =>
      simp [hinner] at houter
      subst target
      exact ⟨innerTarget,
        TuringMachine.stepConfig_eq_some_iff_step.mp hinner, rfl⟩

theorem active_prefixConfig_not_halted
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    (source : TuringMachine.Configuration MachineCodeSymbol
      Section53ParserPrefixPhaseSum.Control)
    (hactive : ¬ Section53ParserPrefixPhaseSum.SuccessfulTerminal source) :
    ¬ TuringMachine.Halted
      (machine initializer initializerEntry initializerReady)
      (prefixConfig initializerEntry source) := by
  rcases source with ⟨state, tape⟩
  cases state with
  | fuel fuelZero state =>
      simp [TuringMachine.Halted, prefixConfig, prefixEmbed, parserEmbed,
        Section53ParserBranchPhaseSum.parserTarget,
        TuringMachine.PhaseEmbedding.liftConfig, machine]
  | header fuelZero state =>
      simp [TuringMachine.Halted, prefixConfig, prefixEmbed, parserEmbed,
        Section53ParserBranchPhaseSum.parserTarget,
        TuringMachine.PhaseEmbedding.liftConfig, machine]
  | shift fuelZero state =>
      simp [TuringMachine.Halted, prefixConfig, prefixEmbed, parserEmbed,
        Section53ParserBranchPhaseSum.parserTarget,
        TuringMachine.PhaseEmbedding.liftConfig, machine]
  | countValidate fuelZero =>
      simp [TuringMachine.Halted, prefixConfig, prefixEmbed, parserEmbed,
        Section53ParserBranchPhaseSum.parserTarget,
        TuringMachine.PhaseEmbedding.liftConfig, machine]
  | countRewind fuelZero =>
      simp [TuringMachine.Halted, prefixConfig, prefixEmbed, parserEmbed,
        Section53ParserBranchPhaseSum.parserTarget,
        TuringMachine.PhaseEmbedding.liftConfig, machine]
  | table fuelZero state =>
      cases state with
      | parser parserState =>
          cases parserState <;>
            simp [TuringMachine.Halted, prefixConfig, prefixEmbed,
              parserEmbed, Section53ParserBranchPhaseSum.parserTarget,
              TuringMachine.PhaseEmbedding.liftConfig, machine]
      | ready saved =>
          exact False.elim (hactive ⟨fuelZero, Or.inr ⟨saved, rfl⟩⟩)
      | halt =>
          simp [TuringMachine.Halted, prefixConfig, prefixEmbed,
            parserEmbed, Section53ParserBranchPhaseSum.parserTarget,
            TuringMachine.PhaseEmbedding.liftConfig, machine]

/-- Every halting run of the final phase sum crosses an honest successful
prefix terminal.  The terminal is reached within the original run bound. -/
theorem exists_successfulPrefixTerminal_of_haltsFromIn
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    {steps : Nat}
    {source : TuringMachine.Configuration MachineCodeSymbol
      Section53ParserPrefixPhaseSum.Control}
    (hhalts : TuringMachine.HaltsFromIn
      (machine initializer initializerEntry initializerReady) steps
      (prefixConfig initializerEntry source)) :
    exists innerSteps : Nat,
    exists target : TuringMachine.Configuration MachineCodeSymbol
        Section53ParserPrefixPhaseSum.Control,
      innerSteps ≤ steps ∧
      TuringMachine.ComputesIn Section53ParserPrefixPhaseSum.machine
          innerSteps source target ∧
        Section53ParserPrefixPhaseSum.SuccessfulTerminal target := by
  exact
    TuringMachine.PhaseExitProjection.exists_bounded_inner_exit_of_haltsFromIn_lift
      (prefixEmbed initializerEntry)
      Section53ParserPrefixPhaseSum.SuccessfulTerminal
      (active_prefix_step_inversion initializer initializerEntry
        initializerReady)
      (active_prefixConfig_not_halted initializer initializerEntry
        initializerReady)
      hhalts

/-- Parser-specific evidence recovered from any honest successful prefix run.
The concrete parser proof supplies this interface independently of the final
initializer and runtime controls. -/
structure SuccessfulPrefixEvidenceContract : Prop where
  project :
    forall (tokens : Word MachineCodeSymbol)
      (steps : Nat)
      (target : TuringMachine.Configuration MachineCodeSymbol
        Section53ParserPrefixPhaseSum.Control),
      TuringMachine.ComputesIn Section53ParserPrefixPhaseSum.machine steps
          (Section53ParserPrefixPhaseSum.sourceConfig tokens) target ->
      Section53ParserPrefixPhaseSum.SuccessfulTerminal target ->
        Nonempty
          (Section53OuterParserInversion.OuterParserPhaseEvidence tokens)

/-- The generic initial-phase projection turns the concrete successful-prefix
evidence interface into the exact contract consumed by total input inversion.
-/
noncomputable def outerParserPhaseEvidenceContract
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    (evidence : SuccessfulPrefixEvidenceContract) :
    Section53OuterParserInversion.OuterParserPhaseEvidenceContract
      (machine initializer initializerEntry initializerReady) where
  projectEvidence := by
    intro tokens hhalts
    apply Classical.choice
    have hhalts' : TuringMachine.HaltsFrom
          (machine initializer initializerEntry initializerReady)
          (prefixConfig initializerEntry
            (Section53ParserPrefixPhaseSum.sourceConfig tokens)) := by
        rw [← sourceConfig_eq_prefixConfig]
        rw [sourceConfig_eq_initial initializer initializerEntry
          initializerReady]
        exact hhalts
    rcases TuringMachine.halts_from_to_halts_from_in hhalts' with
      ⟨steps, hhaltsIn⟩
    rcases exists_successfulPrefixTerminal_of_haltsFromIn initializer
        initializerEntry initializerReady hhaltsIn with
      ⟨innerSteps, target, _hbound, hrun, hterminal⟩
    exact evidence.project tokens innerSteps target hrun hterminal

/-- Total source-shape inversion for every specialization of the final phase
sum.  The sole noncomputable boundary is the already isolated conversion from
actual parser evidence to the abstract decoded witness. -/
theorem totalShapeSpec
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    (evidence : SuccessfulPrefixEvidenceContract) :
    FiniteRecognizer.DecodedDescriptionTotalShapeSpec
      (machine initializer initializerEntry initializerReady) := by
  intro tokens hhalts
  exact Section53TotalInversion.outerInterpreter_halts_only_decoded
    (machine initializer initializerEntry initializerReady)
    ((outerParserPhaseEvidenceContract initializer initializerEntry
      initializerReady evidence).toPhaseEmbeddingContract)
    hhalts

/-- Assemble the canonical forward behavior and total source inversion into
the arbitrary finite-state construction expected by the public leaf. -/
theorem construction
    {initializerState : Type}
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    (canonical : CanonicalPhaseContract initializer initializerEntry
      initializerReady)
    (evidence : SuccessfulPrefixEvidenceContract) :
    FiniteRecognizer.DecodedDescriptionInterpreterConstruction := by
  refine
    ⟨Control initializerState,
      machine initializer initializerEntry initializerReady, ?_⟩
  exact FiniteRecognizer.decodedDescriptionInterpreterTotalSpec_of_components
    (canonicalStageSpec initializer initializerEntry initializerReady
      canonical)
    (totalShapeSpec initializer initializerEntry initializerReady evidence)

/-- Index the concrete finite outer control space to obtain the exact public
`Fin n` construction target. -/
theorem finStateConstruction
    {initializerState : Type}
    [DecidableEq initializerState]
    (initializer : TuringMachine MachineCodeSymbol initializerState)
    (initializerEntry : Option MachineCodeSymbol -> initializerState)
    (initializerReady : initializerState)
    (canonical : CanonicalPhaseContract initializer initializerEntry
      initializerReady)
    (evidence : SuccessfulPrefixEvidenceContract) :
    FiniteRecognizer.DecodedDescriptionInterpreterFinStateConstruction :=
  FiniteRecognizer.decodedDescriptionInterpreterFinStateConstruction_of_construction
    (construction initializer initializerEntry initializerReady canonical
      evidence)


end Section53OuterPhaseSumGeneric
end Computability
end FoC
