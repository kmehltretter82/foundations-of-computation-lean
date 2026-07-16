import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Parser.Assembly
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseEmbedding

namespace FoC
namespace Computability

open Languages

namespace Section53SavedCellTransitionParser

/-!
# Saved-cell transition-parser handoff

The production transition-list parser deliberately erases its finite-control
marker when it enters `halt`.  This wrapper preserves every physical parser
action, but retargets the unique final action from
`findCount (.saved saved)` on `done` to `ready saved`.
-/

inductive Control where
  | parser (state : TransitionListParserState) : Control
  | ready (saved : Option MachineCodeSymbol) : Control
  | halt : Control
deriving DecidableEq

namespace Control

def elems : List Control :=
  TransitionListParserState.elems.map Control.parser ++
    TransitionListParserState.optionCells.map Control.ready ++
    [Control.halt]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro state
    cases state with
    | parser parserState =>
        have hparser :
            parserState ∈ TransitionListParserState.elems :=
          TransitionListParserState.finite.complete parserState
        simp [elems, hparser]
    | ready saved =>
        have hsaved :
            saved ∈ TransitionListParserState.optionCells :=
          TransitionListParserState.optionCells_complete saved
        simp [elems, hsaved]
    | halt =>
        simp [elems]

end Control

def mapParserAction :
    (Option MachineCodeSymbol × Direction × TransitionListParserState) ->
      (Option MachineCodeSymbol × Direction × Control)
  | (write, direction, next) =>
      (write, direction, Control.parser next)

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | Control.parser
        (TransitionListParserState.findCount
          (TransitionListParserMarker.saved saved)),
      some MachineCodeSymbol.done =>
      some
        (some MachineCodeSymbol.done, Direction.right,
          Control.ready saved)
  | Control.parser state, cell =>
      Option.map mapParserAction
        (transitionListParserMachine.transition state cell)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := Control.parser transitionListParserMachine.start
  halt := Control.halt
  transition := transition
  statesFinite := Control.finite

def parserConfig
    (config : TuringMachine.Configuration MachineCodeSymbol
      TransitionListParserState) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig Control.parser config

def readyConfig
    (saved : Option MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := Control.ready saved
    tape := tape }

def projectState : Control -> TransitionListParserState
  | Control.parser state => state
  | Control.ready _ => TransitionListParserState.halt
  | Control.halt => TransitionListParserState.halt

def projectConfig
    (config : TuringMachine.Configuration MachineCodeSymbol Control) :
    TuringMachine.Configuration MachineCodeSymbol
      TransitionListParserState :=
  TuringMachine.PhaseEmbedding.liftConfig projectState config

def projectAction :
    (Option MachineCodeSymbol × Direction × Control) ->
      (Option MachineCodeSymbol × Direction × TransitionListParserState)
  | (write, direction, next) =>
      (write, direction, projectState next)

set_option linter.unusedSimpArgs false in
theorem transition_project
    (state : Control) (cell : Option MachineCodeSymbol) :
    transitionListParserMachine.transition (projectState state) cell =
      Option.map projectAction (transition state cell) := by
  cases state with
  | parser parserState =>
      cases parserState with
      | findCount marker =>
          cases marker with
          | initial =>
              cases cell with
              | none =>
                  simp [transition, projectState, projectAction,
                    mapParserAction, transitionListParserMachine]
              | some symbol =>
                  cases symbol <;>
                    simp [transition, projectState, projectAction,
                      mapParserAction, transitionListParserMachine,
                      transitionListParserKeep]
          | saved saved =>
              cases cell with
              | none =>
                  simp [transition, projectState, projectAction,
                    mapParserAction, transitionListParserMachine]
              | some symbol =>
                  cases symbol <;>
                    simp [transition, projectState, projectAction,
                      mapParserAction, transitionListParserMachine,
                      transitionListParserKeep]
      | seekCountDone marker =>
          cases marker <;>
            cases cell with
            | none =>
                simp [transition, projectState, projectAction,
                  mapParserAction, transitionListParserMachine]
            | some symbol =>
                cases symbol <;>
                  simp [transition, projectState, projectAction,
                    mapParserAction, transitionListParserMachine,
                    transitionListParserKeep]
      | seekMarker saved =>
          cases cell with
          | none =>
              simp [transition, projectState, projectAction,
                mapParserAction, transitionListParserMachine]
          | some symbol =>
              cases symbol <;>
                simp [transition, projectState, projectAction,
                  mapParserAction, transitionListParserMachine,
                  transitionListParserKeep]
      | enterMarkedPosition | needTransition | sourceNat | readCell |
          writeCell | moveField | targetNat | markPosition | halt =>
          cases cell with
          | none =>
              simp [transition, projectState, projectAction,
                mapParserAction, transitionListParserMachine,
                transitionListParserKeep]
          | some symbol =>
              cases symbol <;>
                simp [transition, projectState, projectAction,
                  mapParserAction, transitionListParserMachine,
                  transitionListParserKeep]
      | returnLeft saved =>
          cases cell with
          | none =>
              simp [transition, projectState, projectAction,
                mapParserAction, transitionListParserMachine,
                transitionListParserKeep]
          | some symbol =>
              cases symbol <;>
                simp [transition, projectState, projectAction,
                  mapParserAction, transitionListParserMachine,
                  transitionListParserKeep]
  | ready saved =>
      cases cell <;>
        simp [transition, projectState, projectAction,
          transitionListParserMachine]
  | halt =>
      cases cell <;>
        simp [transition, projectState, projectAction,
          transitionListParserMachine]

theorem stepConfig_project
    (config : TuringMachine.Configuration MachineCodeSymbol Control) :
    transitionListParserMachine.stepConfig (projectConfig config) =
      Option.map projectConfig (machine.stepConfig config) := by
  cases config with
  | mk state tape =>
      unfold TuringMachine.stepConfig
      simp only [projectConfig,
        TuringMachine.PhaseEmbedding.liftConfig]
      rw [transition_project]
      cases haction : transition state (Tape.read tape) with
      | none =>
          simp [machine, haction]
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp [machine, haction, projectAction, projectConfig,
            TuringMachine.PhaseEmbedding.liftConfig]

theorem computes_project
    {source target :
      TuringMachine.Configuration MachineCodeSymbol Control}
    (hrun : TuringMachine.Computes machine source target) :
    TuringMachine.Computes transitionListParserMachine
      (projectConfig source) (projectConfig target) := by
  exact
    TuringMachine.PhaseEmbedding.computes_lift
      projectState stepConfig_project hrun

theorem parser_haltingTransitionsDisabled :
    TuringMachine.HaltingTransitionsDisabled
      transitionListParserMachine := by
  intro cell
  cases cell <;>
    simp [transitionListParserMachine]

theorem transition_lift_of_next_ne_halt
    {state next : TransitionListParserState}
    {cell write : Option MachineCodeSymbol}
    {direction : Direction}
    (htransition :
      transitionListParserMachine.transition state cell =
        some (write, direction, next))
    (hnext : next ≠ TransitionListParserState.halt) :
    transition (Control.parser state) cell =
      some (write, direction, Control.parser next) := by
  have hproject := transition_project (Control.parser state) cell
  simp only [projectState] at hproject
  cases houter : transition (Control.parser state) cell with
  | none =>
      rw [houter] at hproject
      simp only [Option.map] at hproject
      rw [htransition] at hproject
      contradiction
  | some action =>
      rcases action with ⟨outerWrite, outerDirection, outerNext⟩
      rw [houter, htransition] at hproject
      simp only [Option.map, projectAction] at hproject
      have hfields := Prod.mk.inj (Option.some.inj hproject)
      have hwrite : outerWrite = write := hfields.1.symm
      have htail := Prod.mk.inj hfields.2
      have hdirection : outerDirection = direction := htail.1.symm
      have hstate : projectState outerNext = next := htail.2.symm
      subst outerWrite
      subst outerDirection
      cases outerNext with
      | parser parserNext =>
          simp only [projectState] at hstate
          subst parserNext
          rfl
      | ready saved =>
          simp only [projectState] at hstate
          exact False.elim (hnext hstate.symm)
      | halt =>
          simp only [projectState] at hstate
          exact False.elim (hnext hstate.symm)

theorem step_lift_of_target_ne_halt
    {source target :
      TuringMachine.Configuration MachineCodeSymbol
        TransitionListParserState}
    (hstep :
      TuringMachine.Step transitionListParserMachine source target)
    (htarget : target.state ≠ TransitionListParserState.halt) :
    TuringMachine.Step machine
      (parserConfig source) (parserConfig target) := by
  cases hstep with
  | mk htransition =>
      exact
        TuringMachine.Step.mk
          (transition_lift_of_next_ne_halt htransition htarget)

theorem computes_lift_of_target_ne_halt
    {source target :
      TuringMachine.Configuration MachineCodeSymbol
        TransitionListParserState}
    (hrun :
      TuringMachine.Computes transitionListParserMachine source target)
    (htarget : target.state ≠ TransitionListParserState.halt) :
    TuringMachine.Computes machine
      (parserConfig source) (parserConfig target) := by
  induction hrun with
  | refl config =>
      exact TuringMachine.Computes.refl _
  | @step source middle target hstep hrest ih =>
      have hmiddle :
          middle.state ≠ TransitionListParserState.halt := by
        intro hhalt
        have heq : middle = target :=
          TuringMachine.computes_from_halted_eq
            parser_haltingTransitionsDisabled hhalt hrest
        apply htarget
        rw [← heq]
        exact hhalt
      exact
        TuringMachine.Computes.step
          (step_lift_of_target_ne_halt hstep hmiddle)
          (ih htarget)

theorem step_findCount_saved_done
    (saved : Option MachineCodeSymbol)
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step machine
      { state :=
          Control.parser
            (TransitionListParserState.findCount
              (TransitionListParserMarker.saved saved))
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.done :: suffix) }
      { state := Control.ready saved
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.done :: leftRev) suffix } := by
  have haction :
      machine.transition
          (Control.parser
            (TransitionListParserState.findCount
              (TransitionListParserMarker.saved saved)))
          (Tape.read
            (transitionListParserOptionTape leftRev
              (some MachineCodeSymbol.done :: suffix))) =
        some
          (some MachineCodeSymbol.done, Direction.right,
            Control.ready saved) := by
    rfl
  have hstep :=
    @TuringMachine.Step.mk MachineCodeSymbol Control machine
      { state :=
          Control.parser
            (TransitionListParserState.findCount
              (TransitionListParserMarker.saved saved))
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.done :: suffix) }
      (some MachineCodeSymbol.done) Direction.right
      (Control.ready saved) haction
  cases suffix <;>
    simpa [transitionListParserOptionTape, Tape.write,
      Tape.move, Tape.moveRight] using hstep

/-- Exact final scan and handoff.  The tape is byte-for-byte the original
parser's final physical tape; only the outer state retains `saved`. -/
theorem computes_findCount_saved_blanks_done_exact
    (saved : Option MachineCodeSymbol)
    (blanks : Nat)
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Computes machine
      { state :=
          Control.parser
            (TransitionListParserState.findCount
              (TransitionListParserMarker.saved saved))
        tape :=
          transitionListParserOptionTape leftRev
            (List.append
              (List.replicate blanks
                (some MachineCodeSymbol.blank))
              (some MachineCodeSymbol.done :: suffix)) }
      { state := Control.ready saved
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.done ::
              List.append
                (List.replicate blanks
                  (some MachineCodeSymbol.blank))
                leftRev)
            suffix } := by
  have hscan :=
    transitionListParserMachine_computes_findCount_blanks
      (TransitionListParserMarker.saved saved)
      blanks leftRev (some MachineCodeSymbol.done :: suffix)
  have hscanLift :=
    computes_lift_of_target_ne_halt hscan (by simp)
  exact
    TuringMachine.computes_trans hscanLift
      (TuringMachine.Computes.step
        (step_findCount_saved_done saved
          (List.append
            (List.replicate blanks (some MachineCodeSymbol.blank))
            leftRev)
          suffix)
        (TuringMachine.Computes.refl _))

/-- A reached `ready saved` state is an honest original parser halt on the
identical physical tape.  This is the projection needed by total inversion. -/
theorem parser_computes_halt_of_computes_ready
    {source :
      TuringMachine.Configuration MachineCodeSymbol
        TransitionListParserState}
    {saved : Option MachineCodeSymbol}
    {targetTape : Tape MachineCodeSymbol}
    (hrun :
      TuringMachine.Computes machine (parserConfig source)
        (readyConfig saved targetTape)) :
    TuringMachine.Computes transitionListParserMachine source
      { state := TransitionListParserState.halt
        tape := targetTape } := by
  simpa [parserConfig, readyConfig, projectConfig, projectState,
    TuringMachine.PhaseEmbedding.liftConfig] using computes_project hrun

theorem parser_haltsFrom_of_computes_ready
    {source :
      TuringMachine.Configuration MachineCodeSymbol
        TransitionListParserState}
    {saved : Option MachineCodeSymbol}
    {targetTape : Tape MachineCodeSymbol}
    (hrun :
      TuringMachine.Computes machine (parserConfig source)
        (readyConfig saved targetTape)) :
    TuringMachine.HaltsFrom transitionListParserMachine source := by
  exact
    ⟨{ state := TransitionListParserState.halt, tape := targetTape },
      parser_computes_halt_of_computes_ready hrun, rfl⟩

/-- Ready-state reachability from the contextual raw source is strong enough
to reuse the authoritative transition-table inversion without re-proving any
malformed-row cases. -/
theorem contextual_ready_only_encoded
    (baseLeftRev : Word MachineCodeSymbol)
    (count : Nat)
    (tokens : Word MachineCodeSymbol)
    {saved : Option MachineCodeSymbol}
    {targetTape : Tape MachineCodeSymbol}
    (hrun :
      TuringMachine.Computes machine
        (parserConfig
          { state :=
              TransitionListParserState.findCount
                TransitionListParserMarker.initial
            tape :=
              transitionListParserOptionTape
                (none :: baseLeftRev.map some)
                ((MachineDescription.encodeNatAppend count tokens).map
                  some) })
        (readyConfig saved targetTape)) :
    exists transitions : List TransitionDescription,
    exists suffix : Word MachineCodeSymbol,
      count = transitions.length ∧
        tokens =
          MachineDescription.encodeTransitionsAppend transitions suffix := by
  exact
    Section53ParserAssembly.contextualTransitionParserHaltInversion
      baseLeftRev count tokens
      (parser_haltsFrom_of_computes_ready hrun)


end Section53SavedCellTransitionParser
end Computability
end FoC
