import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Parser.Prefix.PhaseSum
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Outer.Direct.PhaseSum

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.ParserBranchPhaseSum

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal

abbrev ParserControl := FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.Control
abbrev ExtractControl := FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.Control
abbrev DecisionControl := FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.Decision.Control

/-!
# Parser and direct-final branch phase sum

The prefix parses outer fuel, header fields, and the transition table.  Its
successful endpoints are retargeted without an extra tape step:

* count zero enters the no-barrier metadata extractor;
* positive table plus zero fuel enters the contextual extractor;
* positive table plus positive fuel exposes one saved-cell materializer
  endpoint.

Both direct-final routes then share the finite comparator decision machine.
-/

inductive Control where
  | parser (state : ParserControl)
  | zeroProbe
  | zeroBounce
  | extract (state : ExtractControl)
  | decision (state : DecisionControl)
  | positiveReady (saved : Option MachineCodeSymbol)
  | accept
  | reject
deriving DecidableEq

namespace Control

def savedOptions : List (Option MachineCodeSymbol) :=
  none :: MachineCodeSymbol.finite.elems.map some

theorem savedOptions_complete
    (saved : Option MachineCodeSymbol) : saved ∈ savedOptions := by
  cases saved with
  | none => simp [savedOptions]
  | some symbol =>
      simp [savedOptions, MachineCodeSymbol.finite.complete symbol]

def elems : List Control :=
  FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.Control.finite.elems.map Control.parser ++
    [Control.zeroProbe, Control.zeroBounce] ++
    FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.Control.finite.elems.map
      Control.extract ++
    FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.Decision.Control.finite.elems.map
      Control.decision ++
    savedOptions.map Control.positiveReady ++
    [Control.accept, Control.reject]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro state
    cases state with
    | parser inner =>
        simp [elems,
          FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.Control.finite.complete inner]
    | zeroProbe => simp [elems]
    | zeroBounce => simp [elems]
    | extract inner =>
        simp [elems,
          FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.Control.finite.complete inner]
    | decision inner =>
        simp [elems,
          FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.Decision.Control.finite.complete inner]
    | positiveReady saved =>
        simp [elems, savedOptions_complete saved]
    | accept => simp [elems]
    | reject => simp [elems]

end Control

def mapAction {innerState : Type}
    (target : innerState -> Control) :
    (Option MachineCodeSymbol × Direction × innerState) ->
      (Option MachineCodeSymbol × Direction × Control)
  | (write, direction, next) => (write, direction, target next)

def parserTarget : ParserControl -> Control
  | .table _ (.parser TransitionListParserState.halt) =>
      .zeroProbe
  | .table true (.ready _) =>
      .extract .preserveContextBlank
  | .table false (.ready saved) => .positiveReady saved
  | .table _ .halt => .reject
  | state => .parser state

def extractTarget : ExtractControl -> Control
  | .ready =>
      .decision FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.Decision.machine.start
  | .halt => .reject
  | state => .extract state

def decisionTarget : DecisionControl -> Control
  | .accept => .accept
  | .reject => .reject
  | state => .decision state

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .parser state, read =>
      Option.map (mapAction parserTarget)
        (FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.machine.transition state read)
  | .zeroProbe, none =>
      some (some MachineCodeSymbol.blank, Direction.left, .zeroBounce)
  | .zeroProbe, some symbol =>
      some (some symbol, Direction.left, .zeroBounce)
  | .zeroBounce, read =>
      some (read, Direction.right, .extract .preserveContextBlank)
  | .extract state, read =>
      Option.map (mapAction extractTarget)
        (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.machine.transition state read)
  | .decision state, read =>
      Option.map (mapAction decisionTarget)
        (FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.Decision.machine.transition state read)
  | .positiveReady _, _ => none
  | .accept, _ => none
  | .reject, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .parser FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.machine.start
  halt := .accept
  transition := transition
  statesFinite := Control.finite

def parserConfig
    (config : TuringMachine.Configuration MachineCodeSymbol ParserControl) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig parserTarget config

def extractConfig
    (config : TuringMachine.Configuration MachineCodeSymbol ExtractControl) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig extractTarget config

def decisionConfig
    (config : TuringMachine.Configuration MachineCodeSymbol
      DecisionControl) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig decisionTarget config

def sourceConfig (tokens : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  parserConfig (FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.sourceConfig tokens)

theorem sourceConfig_eq_initial (tokens : Word MachineCodeSymbol) :
    sourceConfig tokens = TuringMachine.initial machine tokens := by
  cases tokens <;> rfl

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

theorem parser_transition_of_eq_some
    (source target : ParserControl)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (htransition : FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.machine.transition
      source read = some (write, direction, target)) :
    transition (parserTarget source) read =
      some (write, direction, parserTarget target) := by
  have hsource : parserTarget source = .parser source := by
    cases source with
    | fuel _ _ => rfl
    | header _ _ => rfl
    | shift _ _ => rfl
    | countValidate _ => rfl
    | countRewind _ => rfl
    | table fuelZero inner =>
        cases inner with
        | parser parserState =>
            cases parserState <;> try rfl
            change none = some (write, direction, target) at htransition
            contradiction
        | ready saved =>
            change none = some (write, direction, target) at htransition
            contradiction
        | halt =>
            change none = some (write, direction, target) at htransition
            contradiction
  rw [hsource]
  simp only [transition]
  rw [htransition]
  rfl

theorem extract_transition_of_eq_some
    (source target : ExtractControl)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (htransition : FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.machine.transition
      source read = some (write, direction, target)) :
    transition (extractTarget source) read =
      some (write, direction, extractTarget target) := by
  have hsource : extractTarget source = .extract source := by
    cases source <;> try rfl
    all_goals
      change none = some (write, direction, target) at htransition
      contradiction
  rw [hsource]
  simp only [transition]
  rw [htransition]
  rfl

theorem decision_transition_of_eq_some
    (source target : DecisionControl)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (htransition : FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.Decision.machine.transition
      source read = some (write, direction, target)) :
    transition (decisionTarget source) read =
      some (write, direction, decisionTarget target) := by
  have hsource : decisionTarget source = .decision source := by
    cases source <;> try rfl
    all_goals
      change none = some (write, direction, target) at htransition
      contradiction
  rw [hsource]
  simp only [transition]
  rw [htransition]
  rfl

theorem parser_computes
    {source target : TuringMachine.Configuration MachineCodeSymbol
      ParserControl}
    (hrun : TuringMachine.Computes FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.machine
      source target) :
    TuringMachine.Computes machine
      (parserConfig source) (parserConfig target) :=
  computes_of_transition_embedding FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.machine
    parserTarget parser_transition_of_eq_some hrun

theorem extract_computes
    {source target : TuringMachine.Configuration MachineCodeSymbol
      ExtractControl}
    (hrun : TuringMachine.Computes FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.machine
      source target) :
    TuringMachine.Computes machine
      (extractConfig source) (extractConfig target) :=
  computes_of_transition_embedding FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.machine
    extractTarget extract_transition_of_eq_some hrun

theorem decision_computes
    {source target : TuringMachine.Configuration MachineCodeSymbol
      DecisionControl}
    (hrun : TuringMachine.Computes
      FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.Decision.machine source target) :
    TuringMachine.Computes machine
      (decisionConfig source) (decisionConfig target) :=
  computes_of_transition_embedding
    FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.Decision.machine decisionTarget
      decision_transition_of_eq_some hrun

def directDecisionConfig
    (start halt : Nat) (tape : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := if start = halt then .accept else .reject
    tape := tape }

/-- The count-zero parser may stop on the implicit blank just beyond an empty
suffix.  Materialize that one cell so the contextual extractor has the same
nonempty entry shape in both cases. -/
def zeroPayload : Word MachineCodeSymbol -> Word MachineCodeSymbol
  | [] => [MachineCodeSymbol.blank]
  | first :: rest => first :: rest

def zeroProbeConfig
    (leftTail : List (Option MachineCodeSymbol))
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .zeroProbe
    tape := transitionListParserOptionTape
      (some MachineCodeSymbol.done :: leftTail) (input.map some) }

def zeroExtractConfig
    (leftTail : List (Option MachineCodeSymbol))
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .extract .preserveContextBlank
    tape := FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.contextCursorTape
      (some MachineCodeSymbol.done :: leftTail) (zeroPayload input) }

/-- The sacrificial count-zero probe is a two-step left/right bounce.  It
preserves every real suffix and turns only the implicit empty-suffix blank into
an explicit cell that the extractor immediately consumes. -/
theorem zero_probe_run_exact
    (leftTail : List (Option MachineCodeSymbol))
    (input : Word MachineCodeSymbol) :
    machine.runConfigExact? 2 (zeroProbeConfig leftTail input) =
      some (zeroExtractConfig leftTail input) := by
  cases input <;> rfl

theorem zero_probe_computes
    (leftTail : List (Option MachineCodeSymbol))
    (input : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (zeroProbeConfig leftTail input)
      (zeroExtractConfig leftTail input) := by
  exact TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
      (zero_probe_run_exact leftTail input))

/-- Padding-transparent composition from either metadata extractor entry
through the shared direct-final decision machine. -/
theorem extract_then_decide_of_tape_equiv
    (sourceState : ExtractControl)
    (canonicalSourceTape actualSourceTape : Tape MachineCodeSymbol)
    (leftPadding start halt rightPadding : Nat)
    (hextract : TuringMachine.Computes
      FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.machine
        { state := sourceState, tape := canonicalSourceTape }
        (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.readyConfig
          leftPadding
          (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.extractedWord start halt)
          rightPadding))
    (hsource : Tape.Equiv canonicalSourceTape actualSourceTape) :
    exists finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := extractTarget sourceState, tape := actualSourceTape }
        (directDecisionConfig start halt finalTape) := by
  rcases TuringMachine.computes_to_computesIn hextract with
    ⟨extractSteps, hextractIn⟩
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      hextractIn hsource with
    ⟨actualReady, hactualExtractIn, hactualReadyState,
      hactualReadyTape⟩
  rcases actualReady with ⟨actualReadyState, actualReadyTape⟩
  simp only at hactualReadyState
  subst actualReadyState
  have hactualExtract := extract_computes
    (TuringMachine.computesIn_to_computes hactualExtractIn)
  rcases FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.Decision.computes_to_decision
      leftPadding start halt rightPadding with
    ⟨canonicalFinalTape, hdecision⟩
  rcases TuringMachine.computes_to_computesIn hdecision with
    ⟨decisionSteps, hdecisionIn⟩
  have hdecisionSource : Tape.Equiv
      (FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.Decision.sourceConfig
        leftPadding start halt rightPadding).tape
      actualReadyTape := by
    simpa [FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.Decision.sourceConfig,
      FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.Decision.materializeConfig,
      FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.sourceConfig,
      FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.headerConfig,
      TuringMachine.PhaseEmbedding.liftConfig,
      headerInsertSourceConfig] using hactualReadyTape
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      hdecisionIn hdecisionSource with
    ⟨actualDecision, hactualDecisionIn, hactualDecisionState,
      _hactualDecisionTape⟩
  rcases actualDecision with ⟨actualDecisionState, actualDecisionTape⟩
  simp only at hactualDecisionState
  subst actualDecisionState
  have hactualDecision := decision_computes
    (TuringMachine.computesIn_to_computes hactualDecisionIn)
  refine ⟨actualDecisionTape,
    TuringMachine.computes_trans hactualExtract ?_⟩
  by_cases heq : start = halt
  · simpa [extractConfig, extractTarget, decisionConfig,
      decisionTarget,
      FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.Decision.sourceConfig,
      FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.Decision.decisionConfig,
      FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.Decision.materializeConfig,
      FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.Decision.materializeTarget,
      FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.Decision.machine,
      FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.sourceConfig,
      FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.headerConfig,
      FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.headerTarget,
      FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.machine,
      InsertRestagedMachine.machine,
      headerInsertSourceConfig,
      FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.readyConfig,
      directDecisionConfig, heq,
      TuringMachine.PhaseEmbedding.liftConfig] using hactualDecision
  · simpa [extractConfig, extractTarget, decisionConfig,
      decisionTarget,
      FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.Decision.sourceConfig,
      FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.Decision.decisionConfig,
      FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.Decision.materializeConfig,
      FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.Decision.materializeTarget,
      FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.Decision.machine,
      FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.sourceConfig,
      FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.headerConfig,
      FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.headerTarget,
      FiniteRecognizer.Interpreter.ZeroFinalPhaseSum.machine,
      InsertRestagedMachine.machine,
      headerInsertSourceConfig,
      FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.readyConfig,
      directDecisionConfig, heq,
      TuringMachine.PhaseEmbedding.liftConfig] using hactualDecision

/-- Padding-transparent count-zero completion from the shifted parser
terminal.  The two-step probe supplies a real payload cell when the input
suffix is empty; the ordinary contextual extractor and direct comparator then
finish the branch. -/
theorem zero_probe_then_decide_of_tape_equiv
    (fuel stateCount start halt : Nat)
    (input : Word MachineCodeSymbol)
    (actualSourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (zeroProbeConfig
        (none ::
          (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.metadataLeftRev
            fuel stateCount start halt).map some)
        input).tape
      actualSourceTape) :
    exists finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := .zeroProbe, tape := actualSourceTape }
        (directDecisionConfig start halt finalTape) := by
  have hcanonicalProbeIn : TuringMachine.ComputesIn machine 2
      (zeroProbeConfig
        (none ::
          (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.metadataLeftRev
            fuel stateCount start halt).map some)
        input)
      (zeroExtractConfig
        (none ::
          (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.metadataLeftRev
            fuel stateCount start halt).map some)
        input) :=
    TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
      (zero_probe_run_exact
        (none ::
          (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.metadataLeftRev
            fuel stateCount start halt).map some)
        input)
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      hcanonicalProbeIn hsource with
    ⟨actualExtract, hactualProbeIn, hactualExtractState,
      hactualExtractTape⟩
  rcases actualExtract with ⟨actualExtractState, actualExtractTape⟩
  simp only at hactualExtractState
  subst actualExtractState
  have hactualProbe : TuringMachine.Computes machine
      { state := .zeroProbe, tape := actualSourceTape }
      { state := .extract .preserveContextBlank,
        tape := actualExtractTape } := by
    exact TuringMachine.computesIn_to_computes hactualProbeIn
  cases input with
  | nil =>
      have hcanonicalExtract :=
        FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.contextual_extractor_computes
          fuel stateCount start halt 0 MachineCodeSymbol.blank []
      have hactualSource : Tape.Equiv
          (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.contextSourceConfig
            (parsedTableLeftRev 0 ++
              (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.metadataLeftRev
                fuel stateCount start halt).map some)
            MachineCodeSymbol.blank []).tape
          actualExtractTape := by
        simpa [zeroExtractConfig, zeroPayload, parsedTableLeftRev,
          FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.contextSourceConfig] using
          hactualExtractTape
      rcases extract_then_decide_of_tape_equiv
          .preserveContextBlank
          (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.contextSourceConfig
            (parsedTableLeftRev 0 ++
              (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.metadataLeftRev
                fuel stateCount start halt).map some)
            MachineCodeSymbol.blank []).tape
          actualExtractTape
          ((FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.olderMetadataLeftRev
            fuel stateCount).length + 2)
          start halt
          ((MachineCodeSymbol.done ::
            List.replicate 0 MachineCodeSymbol.blank).length + 1).succ
          hcanonicalExtract hactualSource with
        ⟨finalTape, hfinish⟩
      exact ⟨finalTape,
        TuringMachine.computes_trans hactualProbe hfinish⟩
  | cons first rest =>
      have hcanonicalExtract :=
        FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.contextual_extractor_computes
          fuel stateCount start halt 0 first rest
      have hactualSource : Tape.Equiv
          (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.contextSourceConfig
            (parsedTableLeftRev 0 ++
              (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.metadataLeftRev
                fuel stateCount start halt).map some)
            first rest).tape
          actualExtractTape := by
        simpa [zeroExtractConfig, zeroPayload, parsedTableLeftRev,
          FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.contextSourceConfig] using
          hactualExtractTape
      rcases extract_then_decide_of_tape_equiv
          .preserveContextBlank
          (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.contextSourceConfig
            (parsedTableLeftRev 0 ++
              (FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.metadataLeftRev
                fuel stateCount start halt).map some)
            first rest).tape
          actualExtractTape
          ((FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal.olderMetadataLeftRev
            fuel stateCount).length + 2)
          start halt
          ((MachineCodeSymbol.done ::
            List.replicate 0 MachineCodeSymbol.blank).length +
            (rest.length + 1)).succ
          hcanonicalExtract hactualSource with
        ⟨finalTape, hfinish⟩
      exact ⟨finalTape,
        TuringMachine.computes_trans hactualProbe hfinish⟩

theorem reject_transition_none
    (read : Option MachineCodeSymbol) :
    machine.transition .reject read = none := by
  rfl

/-- Any route that reaches the shared direct-decision endpoint halts exactly
in the equal-state case.  This packages the common stuck-reject argument for
both the empty-table and zero-fuel parser branches. -/
theorem haltsFrom_iff_of_computes_to_directDecision
    {source : TuringMachine.Configuration MachineCodeSymbol Control}
    (start halt : Nat)
    (finalTape : Tape MachineCodeSymbol)
    (hrun : TuringMachine.Computes machine source
      (directDecisionConfig start halt finalTape)) :
    TuringMachine.HaltsFrom machine source ↔ start = halt := by
  constructor
  · intro hhalts
    by_cases heq : start = halt
    · exact heq
    · have hnot :=
        TuringMachine.StuckSink.not_haltsFrom_of_computes_to_stuck_nonhalt
          (M := machine)
          (by intro read; rfl)
          (by simpa [directDecisionConfig, heq] using hrun)
          (by simp [TuringMachine.Halted, machine])
          (by
            intro next
            apply TuringMachine.not_step_of_transition_eq_none
            exact reject_transition_none (Tape.read finalTape))
      exact False.elim (hnot hhalts)
  · intro heq
    apply TuringMachine.halts_from_of_computes hrun
    simp [TuringMachine.Halted, directDecisionConfig, machine, heq]

theorem haltingTransitionsDisabled :
    TuringMachine.HaltingTransitionsDisabled machine := by
  intro read
  rfl


end FiniteRecognizer.Interpreter.ParserBranchPhaseSum
end Computability
end FoC
