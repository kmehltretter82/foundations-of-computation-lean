import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Outer.ParserInversion
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Parser.SavedCell.Forward
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseRetarget

namespace FoC
namespace Computability

open Languages
open FiniteRecognizer ExactFuel StrictProbe

namespace Section53ParserPrefixPhaseSum

open Section53ParserAssembly
open Section53OuterParserInversion

/-!
# Finite parser-prefix phase sum

This finite control sum stops at the two honest transition-table endpoints.
It contains only the outer unary parser, the three pre-count header fields,
the physical one-cell right shift that installs the table separator, and the
saved-cell table parser.  Initializer and runtime controls are deliberately
absent.
-/

inductive Control where
  | fuel (fuelZero : Bool)
      (state : ProductInput.PairFuelParser.Control)
  | header (fuelZero : Bool)
      (state : HeaderFieldsParserState)
  | shift (fuelZero : Bool)
      (state : ContextualPrefixRightShiftOne.Control)
  | countValidate (fuelZero : Bool)
  | countRewind (fuelZero : Bool)
  | table (fuelZero : Bool)
      (state : Section53SavedCellTransitionParser.Control)
deriving DecidableEq

namespace Control

def elems : List Control :=
  (ProductInput.PairFuelParser.machine.statesFinite.elems.map
    (Control.fuel false)) ++
  (ProductInput.PairFuelParser.machine.statesFinite.elems.map
    (Control.fuel true)) ++
  (headerFieldsParserMachine.statesFinite.elems.map
    (Control.header false)) ++
  (headerFieldsParserMachine.statesFinite.elems.map
    (Control.header true)) ++
  (ContextualPrefixRightShiftOne.machine.statesFinite.elems.map
    (Control.shift false)) ++
  (ContextualPrefixRightShiftOne.machine.statesFinite.elems.map
    (Control.shift true)) ++
  [Control.countValidate false, Control.countValidate true,
    Control.countRewind false, Control.countRewind true] ++
  (Section53SavedCellTransitionParser.machine.statesFinite.elems.map
    (Control.table false)) ++
  (Section53SavedCellTransitionParser.machine.statesFinite.elems.map
    (Control.table true))

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro state
    cases state with
    | fuel fuelZero innerState =>
        have h :=
          ProductInput.PairFuelParser.machine.statesFinite.complete innerState
        cases fuelZero <;> simp [elems, h]
    | header fuelZero innerState =>
        have h := headerFieldsParserMachine.statesFinite.complete innerState
        cases fuelZero <;> simp [elems, h]
    | shift fuelZero innerState =>
        have h :=
          ContextualPrefixRightShiftOne.machine.statesFinite.complete
            innerState
        cases fuelZero <;> simp [elems, h]
    | countValidate fuelZero =>
        cases fuelZero <;> simp [elems]
    | countRewind fuelZero =>
        cases fuelZero <;> simp [elems]
    | table fuelZero innerState =>
        have h :=
          Section53SavedCellTransitionParser.machine.statesFinite.complete
            innerState
        cases fuelZero <;> simp [elems, h]

end Control

def mapAction {localState : Type}
    (target : localState -> Control) :
    (Option MachineCodeSymbol × Direction × localState) ->
      (Option MachineCodeSymbol × Direction × Control)
  | (write, direction, next) => (write, direction, target next)

def fuelTarget (fuelZero : Bool) :
    ProductInput.PairFuelParser.Control -> Control
  | .outer => .fuel false .outer
  | .inner => .header fuelZero .needHeader
  | .gate => .fuel fuelZero .gate

def headerTarget (fuelZero : Bool) : HeaderFieldsParserState -> Control
  | .transitionCount => .shift fuelZero .takeFirst
  | state => .header fuelZero state

def shiftTarget (fuelZero : Bool) :
    ContextualPrefixRightShiftOne.Control -> Control
  | .halt => .countValidate fuelZero
  | state => .shift fuelZero state

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .fuel fuelZero .outer, read =>
      Option.map (mapAction (fuelTarget fuelZero))
        (outerFuelRetargetTransition .outer read)
  | .fuel _ _, _ => none
  | .header _ .transitionCount, _ => none
  | .header _ .done, _ => none
  | .header fuelZero state, read =>
      Option.map (mapAction (headerTarget fuelZero))
        (headerFieldsParserMachine.transition state read)
  | .shift fuelZero state, read =>
      Option.map (mapAction (shiftTarget fuelZero))
        (ContextualPrefixRightShiftOne.machine.transition state read)
  | .countValidate fuelZero, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right,
        .countValidate fuelZero)
  | .countValidate fuelZero, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.left,
        .countRewind fuelZero)
  | .countRewind fuelZero, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.left,
        .countRewind fuelZero)
  | .countRewind fuelZero, none =>
      some (none, Direction.right,
        .table fuelZero Section53SavedCellTransitionParser.machine.start)
  | .countValidate _, _ => none
  | .countRewind _, _ => none
  | .table fuelZero state, read =>
      Option.map (mapAction (Control.table fuelZero))
        (Section53SavedCellTransitionParser.machine.transition state read)

def machine : TuringMachine MachineCodeSymbol Control where
  start := .fuel true .outer
  halt := .table false .halt
  transition := transition
  statesFinite := Control.finite

def fuelConfig (fuelZero : Bool)
    (config : TuringMachine.Configuration MachineCodeSymbol
      ProductInput.PairFuelParser.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig (Control.fuel fuelZero) config

def headerConfig (fuelZero : Bool)
    (config : TuringMachine.Configuration MachineCodeSymbol
      HeaderFieldsParserState) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig (headerTarget fuelZero) config

def shiftConfig (fuelZero : Bool)
    (config : TuringMachine.Configuration MachineCodeSymbol
      ContextualPrefixRightShiftOne.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig (shiftTarget fuelZero) config

def tableConfig (fuelZero : Bool)
    (config : TuringMachine.Configuration MachineCodeSymbol
      Section53SavedCellTransitionParser.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig
    (Control.table fuelZero) config

def sourceConfig (tokens : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  fuelConfig true (ProductInput.PairFuelParser.config .outer [] tokens)

theorem sourceConfig_eq_initial (tokens : Word MachineCodeSymbol) :
    sourceConfig tokens = TuringMachine.initial machine tokens := by
  cases tokens <;> rfl

/-- The parser prefix has two successful stuck endpoints. -/
def SuccessfulTerminal
    (config : TuringMachine.Configuration MachineCodeSymbol Control) : Prop :=
  exists fuelZero : Bool,
    config.state =
        Control.table fuelZero
          (Section53SavedCellTransitionParser.Control.parser
            TransitionListParserState.halt) ∨
      exists saved : Option MachineCodeSymbol,
      config.state =
        Control.table fuelZero
          (Section53SavedCellTransitionParser.Control.ready saved)

theorem successfulTerminal_no_step
    {config : TuringMachine.Configuration MachineCodeSymbol Control}
    (hsuccess : SuccessfulTerminal config)
    (next : TuringMachine.Configuration MachineCodeSymbol Control) :
    ¬ TuringMachine.Step machine config next := by
  rcases config with ⟨state, tape⟩
  rcases hsuccess with ⟨fuelZero, hparser | ⟨saved, hready⟩⟩
  · simp only at hparser
    subst state
    apply TuringMachine.not_step_of_transition_eq_none
    cases tape.head with
    | none => rfl
    | some symbol => cases symbol <;> rfl
  · simp only at hready
    subst state
    exact TuringMachine.not_step_of_transition_eq_none rfl

theorem computes_suffix_of_computesIn_of_successful
    {steps : Nat}
    {source middle final :
      TuringMachine.Configuration MachineCodeSymbol Control}
    (hprefix : TuringMachine.ComputesIn machine steps source middle)
    (hrun : TuringMachine.Computes machine source final)
    (hsuccess : SuccessfulTerminal final) :
    TuringMachine.Computes machine middle final := by
  induction hprefix generalizing final with
  | zero source =>
      exact hrun
  | succ hstep htail ih =>
      cases hrun with
      | refl =>
          exact False.elim (successfulTerminal_no_step hsuccess _ hstep)
      | step hstep' hrest =>
          have hnext := TuringMachine.step_deterministic hstep hstep'
          cases hnext
          exact ih hrest hsuccess

theorem fuel_tick_step
    (fuelZero : Bool)
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (fuelConfig fuelZero
          (ProductInput.PairFuelParser.config .outer leftRev
            (MachineCodeSymbol.tick :: suffix))) =
      some
        (fuelConfig false
          (ProductInput.PairFuelParser.config .outer
            (MachineCodeSymbol.tick :: leftRev) suffix)) := by
  cases suffix <;> rfl

theorem fuel_done_step
    (fuelZero : Bool)
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (fuelConfig fuelZero
          (ProductInput.PairFuelParser.config .outer leftRev
            (MachineCodeSymbol.done :: suffix))) =
      some
        (headerConfig fuelZero
          { state := HeaderFieldsParserState.needHeader
            tape := headerFieldsParserTape
              (MachineCodeSymbol.done :: leftRev) suffix }) := by
  cases suffix <;> rfl

theorem fuel_false_run_exact
    (fuel : Nat) (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (fuel + 1)
        (fuelConfig false
          (ProductInput.PairFuelParser.config .outer leftRev
            (MachineDescription.encodeNatAppend fuel suffix))) =
      some
        (headerConfig false
          { state := HeaderFieldsParserState.needHeader
            tape := headerFieldsParserTape
              (List.append (MachineDescription.encodeNat fuel).reverse
                leftRev)
              suffix }) := by
  induction fuel generalizing leftRev with
  | zero =>
      exact fuel_done_step false leftRev suffix
  | succ fuel ih =>
      change
        machine.runConfigExact? ((fuel + 1) + 1)
          (fuelConfig false
            (ProductInput.PairFuelParser.config .outer leftRev
              (MachineCodeSymbol.tick ::
                MachineDescription.encodeNatAppend fuel suffix))) = _
      rw [TuringMachine.runConfigExact?]
      rw [fuel_tick_step]
      simp only
      rw [ih]
      simp [MachineDescription.encodeNat, List.reverse_cons,
        List.append_assoc]

theorem fuel_initial_run_zero
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? 1
        (fuelConfig true
          (ProductInput.PairFuelParser.config .outer leftRev
            (MachineDescription.encodeNatAppend 0 suffix))) =
      some
        (headerConfig true
          { state := HeaderFieldsParserState.needHeader
            tape := headerFieldsParserTape
              (List.append (MachineDescription.encodeNat 0).reverse leftRev)
              suffix }) := by
  exact fuel_done_step true leftRev suffix

theorem fuel_initial_run_positive
    (fuel : Nat) (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? ((fuel + 1) + 1)
        (fuelConfig true
          (ProductInput.PairFuelParser.config .outer leftRev
            (MachineDescription.encodeNatAppend (fuel + 1) suffix))) =
      some
        (headerConfig false
          { state := HeaderFieldsParserState.needHeader
            tape := headerFieldsParserTape
              (List.append
                (MachineDescription.encodeNat (fuel + 1)).reverse leftRev)
              suffix }) := by
  change
    machine.runConfigExact? ((fuel + 1) + 1)
      (fuelConfig true
        (ProductInput.PairFuelParser.config .outer leftRev
          (MachineCodeSymbol.tick ::
            MachineDescription.encodeNatAppend fuel suffix))) = _
  rw [TuringMachine.runConfigExact?]
  rw [fuel_tick_step]
  simp only
  simpa [MachineDescription.encodeNat, List.reverse_cons,
    List.append_assoc] using
    fuel_false_run_exact fuel
      (MachineCodeSymbol.tick :: leftRev) suffix

theorem fuel_success_only_encodeNatAppend
    (fuelZero : Bool)
    (leftRev rest : Word MachineCodeSymbol)
    {final : TuringMachine.Configuration MachineCodeSymbol Control}
    (hrun : TuringMachine.Computes machine
      (fuelConfig fuelZero
        (ProductInput.PairFuelParser.config .outer leftRev rest)) final)
    (hsuccess : SuccessfulTerminal final) :
    exists fuel : Nat,
    exists encoded : Word MachineCodeSymbol,
      rest = MachineDescription.encodeNatAppend fuel encoded := by
  induction rest generalizing fuelZero leftRev with
  | nil =>
      cases hrun with
      | refl =>
          simp [SuccessfulTerminal, fuelConfig,
            TuringMachine.PhaseEmbedding.liftConfig] at hsuccess
      | step hstep _ =>
          exact False.elim
            ((TuringMachine.not_step_of_transition_eq_none
              (M := machine)
              (c := fuelConfig fuelZero
                (ProductInput.PairFuelParser.config .outer leftRev []))
              (by rfl)) hstep)
  | cons symbol suffix ih =>
      cases symbol with
      | tick =>
          have hstep : TuringMachine.Step machine
              (fuelConfig fuelZero
                (ProductInput.PairFuelParser.config .outer leftRev
                  (MachineCodeSymbol.tick :: suffix)))
              (fuelConfig false
                (ProductInput.PairFuelParser.config .outer
                  (MachineCodeSymbol.tick :: leftRev) suffix)) :=
            TuringMachine.stepConfig_eq_some_iff_step.mp
              (fuel_tick_step fuelZero leftRev suffix)
          have hprefix : TuringMachine.ComputesIn machine 1
              (fuelConfig fuelZero
                (ProductInput.PairFuelParser.config .outer leftRev
                  (MachineCodeSymbol.tick :: suffix)))
              (fuelConfig false
                (ProductInput.PairFuelParser.config .outer
                  (MachineCodeSymbol.tick :: leftRev) suffix)) :=
            TuringMachine.ComputesIn.succ hstep
              (TuringMachine.ComputesIn.zero _)
          have htail :=
            computes_suffix_of_computesIn_of_successful
              hprefix hrun hsuccess
          rcases ih false (MachineCodeSymbol.tick :: leftRev) htail with
            ⟨fuel, encoded, hsuffix⟩
          exact ⟨fuel + 1, encoded, by
            simp [MachineDescription.encodeNatAppend,
              MachineDescription.encodeNat, hsuffix]⟩
      | done =>
          exact ⟨0, suffix, by
            simp [MachineDescription.encodeNatAppend,
              MachineDescription.encodeNat]⟩
      | header | transition | blank | zero | one | moveLeft | moveRight =>
          cases hrun with
          | refl =>
              simp [SuccessfulTerminal, fuelConfig,
                TuringMachine.PhaseEmbedding.liftConfig] at hsuccess
          | step hstep _ =>
              exact False.elim
                ((TuringMachine.not_step_of_transition_eq_none
                  (M := machine)
                  (c := fuelConfig fuelZero
                    (ProductInput.PairFuelParser.config .outer leftRev
                      (_ :: suffix)))
                  (by rfl)) hstep)

theorem header_step_header
    (fuelZero : Bool)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step machine
      (headerConfig fuelZero
        { state := HeaderFieldsParserState.needHeader
          tape := headerFieldsParserTape leftRev
            (MachineCodeSymbol.header :: suffix) })
      (headerConfig fuelZero
        { state := HeaderFieldsParserState.stateCount
          tape := headerFieldsParserTape
            (MachineCodeSymbol.header :: leftRev) suffix }) := by
  apply TuringMachine.stepConfig_eq_some_iff_step.mp
  cases suffix <;> rfl

theorem header_step_tick_stateCount
    (fuelZero : Bool)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step machine
      (headerConfig fuelZero
        { state := HeaderFieldsParserState.stateCount
          tape := headerFieldsParserTape leftRev
            (MachineCodeSymbol.tick :: suffix) })
      (headerConfig fuelZero
        { state := HeaderFieldsParserState.stateCount
          tape := headerFieldsParserTape
            (MachineCodeSymbol.tick :: leftRev) suffix }) := by
  apply TuringMachine.stepConfig_eq_some_iff_step.mp
  cases suffix <;> rfl

theorem header_step_done_stateCount
    (fuelZero : Bool)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step machine
      (headerConfig fuelZero
        { state := HeaderFieldsParserState.stateCount
          tape := headerFieldsParserTape leftRev
            (MachineCodeSymbol.done :: suffix) })
      (headerConfig fuelZero
        { state := HeaderFieldsParserState.startField
          tape := headerFieldsParserTape
            (MachineCodeSymbol.done :: leftRev) suffix }) := by
  apply TuringMachine.stepConfig_eq_some_iff_step.mp
  cases suffix <;> rfl

theorem header_step_tick_startField
    (fuelZero : Bool)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step machine
      (headerConfig fuelZero
        { state := HeaderFieldsParserState.startField
          tape := headerFieldsParserTape leftRev
            (MachineCodeSymbol.tick :: suffix) })
      (headerConfig fuelZero
        { state := HeaderFieldsParserState.startField
          tape := headerFieldsParserTape
            (MachineCodeSymbol.tick :: leftRev) suffix }) := by
  apply TuringMachine.stepConfig_eq_some_iff_step.mp
  cases suffix <;> rfl

theorem header_step_done_startField
    (fuelZero : Bool)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step machine
      (headerConfig fuelZero
        { state := HeaderFieldsParserState.startField
          tape := headerFieldsParserTape leftRev
            (MachineCodeSymbol.done :: suffix) })
      (headerConfig fuelZero
        { state := HeaderFieldsParserState.haltField
          tape := headerFieldsParserTape
            (MachineCodeSymbol.done :: leftRev) suffix }) := by
  apply TuringMachine.stepConfig_eq_some_iff_step.mp
  cases suffix <;> rfl

theorem header_step_tick_haltField
    (fuelZero : Bool)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step machine
      (headerConfig fuelZero
        { state := HeaderFieldsParserState.haltField
          tape := headerFieldsParserTape leftRev
            (MachineCodeSymbol.tick :: suffix) })
      (headerConfig fuelZero
        { state := HeaderFieldsParserState.haltField
          tape := headerFieldsParserTape
            (MachineCodeSymbol.tick :: leftRev) suffix }) := by
  apply TuringMachine.stepConfig_eq_some_iff_step.mp
  cases suffix <;> rfl

theorem header_step_done_haltField
    (fuelZero : Bool)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step machine
      (headerConfig fuelZero
        { state := HeaderFieldsParserState.haltField
          tape := headerFieldsParserTape leftRev
            (MachineCodeSymbol.done :: suffix) })
      (headerConfig fuelZero
        { state := HeaderFieldsParserState.transitionCount
          tape := headerFieldsParserTape
            (MachineCodeSymbol.done :: leftRev) suffix }) := by
  apply TuringMachine.stepConfig_eq_some_iff_step.mp
  cases suffix <;> rfl

theorem header_unary_success_only_encodeNatAppend
    (fuelZero : Bool)
    (current : HeaderFieldsParserState)
    (hcurrent :
      current = HeaderFieldsParserState.stateCount ∨
      current = HeaderFieldsParserState.startField ∨
      current = HeaderFieldsParserState.haltField)
    (htick : forall (leftRev suffix : Word MachineCodeSymbol),
      TuringMachine.Step machine
        (headerConfig fuelZero
          { state := current
            tape := headerFieldsParserTape leftRev
              (MachineCodeSymbol.tick :: suffix) })
        (headerConfig fuelZero
          { state := current
            tape := headerFieldsParserTape
              (MachineCodeSymbol.tick :: leftRev) suffix }))
    (leftRev rest : Word MachineCodeSymbol)
    {final : TuringMachine.Configuration MachineCodeSymbol Control}
    (hrun : TuringMachine.Computes machine
      (headerConfig fuelZero
        { state := current
          tape := headerFieldsParserTape leftRev rest }) final)
    (hsuccess : SuccessfulTerminal final) :
    exists value : Nat,
    exists suffix : Word MachineCodeSymbol,
      rest = MachineDescription.encodeNatAppend value suffix := by
  induction rest generalizing leftRev with
  | nil =>
      cases hrun with
      | refl =>
          rcases hcurrent with hstate | hstate
          · subst current
            simp [SuccessfulTerminal, headerConfig,
              TuringMachine.PhaseEmbedding.liftConfig, headerTarget] at hsuccess
          · rcases hstate with hstate | hstate
            · subst current
              simp [SuccessfulTerminal, headerConfig,
                TuringMachine.PhaseEmbedding.liftConfig, headerTarget] at hsuccess
            · subst current
              simp [SuccessfulTerminal, headerConfig,
                TuringMachine.PhaseEmbedding.liftConfig, headerTarget] at hsuccess
      | step hstep _ =>
          have hnone :
              machine.transition
                  (headerConfig fuelZero
                    { state := current
                      tape := headerFieldsParserTape leftRev [] }).state
                  (Tape.read
                    (headerConfig fuelZero
                      { state := current
                        tape := headerFieldsParserTape leftRev [] }).tape) =
                none := by
            rcases hcurrent with hstate | hstate
            · subst current
              rfl
            · rcases hstate with hstate | hstate
              · subst current
                rfl
              · subst current
                rfl
          exact False.elim
            ((TuringMachine.not_step_of_transition_eq_none hnone) hstep)
  | cons symbol suffix ih =>
      cases symbol with
      | tick =>
          have hprefix : TuringMachine.ComputesIn machine 1
              (headerConfig fuelZero
                { state := current
                  tape := headerFieldsParserTape leftRev
                    (MachineCodeSymbol.tick :: suffix) })
              (headerConfig fuelZero
                { state := current
                  tape := headerFieldsParserTape
                    (MachineCodeSymbol.tick :: leftRev) suffix }) :=
            TuringMachine.ComputesIn.succ (htick leftRev suffix)
              (TuringMachine.ComputesIn.zero _)
          have htail :=
            computes_suffix_of_computesIn_of_successful
              hprefix hrun hsuccess
          rcases ih (MachineCodeSymbol.tick :: leftRev) htail with
            ⟨value, encoded, hsuffix⟩
          exact ⟨value + 1, encoded, by
            simp [MachineDescription.encodeNatAppend,
              MachineDescription.encodeNat, hsuffix]⟩
      | done =>
          exact ⟨0, suffix, by
            simp [MachineDescription.encodeNatAppend,
              MachineDescription.encodeNat]⟩
      | header | transition | blank | zero | one | moveLeft | moveRight =>
          cases hrun with
          | refl =>
              rcases hcurrent with hstate | hstate
              · subst current
                simp [SuccessfulTerminal, headerConfig,
                  TuringMachine.PhaseEmbedding.liftConfig, headerTarget] at hsuccess
              · rcases hstate with hstate | hstate
                · subst current
                  simp [SuccessfulTerminal, headerConfig,
                    TuringMachine.PhaseEmbedding.liftConfig, headerTarget] at hsuccess
                · subst current
                  simp [SuccessfulTerminal, headerConfig,
                    TuringMachine.PhaseEmbedding.liftConfig, headerTarget] at hsuccess
          | step hstep _ =>
              cases hstep with
              | mk haction =>
                rcases hcurrent with hstate | hstate
                · subst current
                  simp [machine, transition, headerConfig,
                    TuringMachine.PhaseEmbedding.liftConfig, headerTarget,
                    headerFieldsParserMachine, headerFieldsParserTape,
                    Tape.read] at haction
                · rcases hstate with hstate | hstate
                  · subst current
                    simp [machine, transition, headerConfig,
                      TuringMachine.PhaseEmbedding.liftConfig, headerTarget,
                      headerFieldsParserMachine, headerFieldsParserTape,
                      Tape.read] at haction
                  · subst current
                    simp [machine, transition, headerConfig,
                      TuringMachine.PhaseEmbedding.liftConfig, headerTarget,
                      headerFieldsParserMachine, headerFieldsParserTape,
                      Tape.read] at haction

theorem header_computesIn_nat
    (fuelZero : Bool)
    {current next : HeaderFieldsParserState}
    (htick :
      forall leftRev suffix : Word MachineCodeSymbol,
        TuringMachine.Step machine
          (headerConfig fuelZero
            { state := current
              tape := headerFieldsParserTape leftRev
                (MachineCodeSymbol.tick :: suffix) })
          (headerConfig fuelZero
            { state := current
              tape := headerFieldsParserTape
                (MachineCodeSymbol.tick :: leftRev) suffix }))
    (hdone :
      forall leftRev suffix : Word MachineCodeSymbol,
        TuringMachine.Step machine
          (headerConfig fuelZero
            { state := current
              tape := headerFieldsParserTape leftRev
                (MachineCodeSymbol.done :: suffix) })
          (headerConfig fuelZero
            { state := next
              tape := headerFieldsParserTape
                (MachineCodeSymbol.done :: leftRev) suffix }))
    (leftRev : Word MachineCodeSymbol) (n : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.ComputesIn machine (n + 1)
      (headerConfig fuelZero
        { state := current
          tape := headerFieldsParserTape leftRev
            (MachineDescription.encodeNatAppend n suffix) })
      (headerConfig fuelZero
        { state := next
          tape := headerFieldsParserTape
            (List.append (MachineDescription.encodeNat n).reverse leftRev)
            suffix }) := by
  induction n generalizing leftRev with
  | zero =>
      simpa [MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat] using
        TuringMachine.ComputesIn.succ
          (hdone leftRev suffix)
          (TuringMachine.ComputesIn.zero _)
  | succ n ih =>
      have htail := ih (MachineCodeSymbol.tick :: leftRev)
      have hcomp :=
        TuringMachine.ComputesIn.succ
          (htick leftRev (MachineDescription.encodeNatAppend n suffix))
          htail
      simpa [MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat, List.append_assoc] using hcomp

theorem header_success_only_three_fields
    (fuelZero : Bool)
    (leftRev rest : Word MachineCodeSymbol)
    {final : TuringMachine.Configuration MachineCodeSymbol Control}
    (hrun : TuringMachine.Computes machine
      (headerConfig fuelZero
        { state := HeaderFieldsParserState.needHeader
          tape := headerFieldsParserTape leftRev rest }) final)
    (hsuccess : SuccessfulTerminal final) :
    exists stateCount start halt : Nat,
    exists tail : Word MachineCodeSymbol,
      rest =
        MachineCodeSymbol.header ::
          MachineDescription.encodeNatAppend stateCount
            (MachineDescription.encodeNatAppend start
              (MachineDescription.encodeNatAppend halt tail)) := by
  cases rest with
  | nil =>
      cases hrun with
      | refl =>
          simp [SuccessfulTerminal, headerConfig,
            TuringMachine.PhaseEmbedding.liftConfig, headerTarget] at hsuccess
      | step hstep _ =>
          exact False.elim
            ((TuringMachine.not_step_of_transition_eq_none
              (M := machine)
              (c := headerConfig fuelZero
                { state := HeaderFieldsParserState.needHeader
                  tape := headerFieldsParserTape leftRev [] })
              (by rfl)) hstep)
  | cons symbol afterHeader =>
      cases symbol with
      | header =>
          have hheaderPrefix : TuringMachine.ComputesIn machine 1
              (headerConfig fuelZero
                { state := HeaderFieldsParserState.needHeader
                  tape := headerFieldsParserTape leftRev
                    (MachineCodeSymbol.header :: afterHeader) })
              (headerConfig fuelZero
                { state := HeaderFieldsParserState.stateCount
                  tape := headerFieldsParserTape
                    (MachineCodeSymbol.header :: leftRev) afterHeader }) :=
            TuringMachine.ComputesIn.succ
              (header_step_header fuelZero leftRev afterHeader)
              (TuringMachine.ComputesIn.zero _)
          have hstateRun :=
            computes_suffix_of_computesIn_of_successful
              hheaderPrefix hrun hsuccess
          rcases
              header_unary_success_only_encodeNatAppend fuelZero
                HeaderFieldsParserState.stateCount (Or.inl rfl)
                (header_step_tick_stateCount fuelZero)
                (MachineCodeSymbol.header :: leftRev) afterHeader
                hstateRun hsuccess with
            ⟨stateCount, afterState, hstateShape⟩
          rw [hstateShape] at hstateRun
          have hstatePrefix :=
            header_computesIn_nat fuelZero
              (header_step_tick_stateCount fuelZero)
              (header_step_done_stateCount fuelZero)
              (MachineCodeSymbol.header :: leftRev) stateCount afterState
          have hstartRun :=
            computes_suffix_of_computesIn_of_successful
              hstatePrefix hstateRun hsuccess
          let afterStateLeftRev : Word MachineCodeSymbol :=
            List.append (MachineDescription.encodeNat stateCount).reverse
              (MachineCodeSymbol.header :: leftRev)
          rcases
              header_unary_success_only_encodeNatAppend fuelZero
                HeaderFieldsParserState.startField (Or.inr (Or.inl rfl))
                (header_step_tick_startField fuelZero)
                afterStateLeftRev afterState hstartRun hsuccess with
            ⟨start, afterStart, hstartShape⟩
          rw [hstartShape] at hstartRun
          have hstartPrefix :=
            header_computesIn_nat fuelZero
              (header_step_tick_startField fuelZero)
              (header_step_done_startField fuelZero)
              afterStateLeftRev start afterStart
          have hhaltRun :=
            computes_suffix_of_computesIn_of_successful
              hstartPrefix hstartRun hsuccess
          let afterStartLeftRev : Word MachineCodeSymbol :=
            List.append (MachineDescription.encodeNat start).reverse
              afterStateLeftRev
          rcases
              header_unary_success_only_encodeNatAppend fuelZero
                HeaderFieldsParserState.haltField (Or.inr (Or.inr rfl))
                (header_step_tick_haltField fuelZero)
                afterStartLeftRev afterStart hhaltRun hsuccess with
            ⟨halt, tail, hhaltShape⟩
          exact ⟨stateCount, start, halt, tail, by
            rw [hstateShape, hstartShape, hhaltShape]⟩
      | transition | tick | done | blank | zero | one | moveLeft | moveRight =>
          cases hrun with
          | refl =>
              simp [SuccessfulTerminal, headerConfig,
                TuringMachine.PhaseEmbedding.liftConfig, headerTarget] at hsuccess
          | step hstep _ =>
              cases hstep with
              | mk haction =>
                  simp [machine, transition, headerConfig,
                    TuringMachine.PhaseEmbedding.liftConfig, headerTarget,
                    headerFieldsParserMachine, headerFieldsParserTape,
                    Tape.read] at haction

/-- Canonical header execution stops immediately before consuming the table
count; its retargeted endpoint is the shift machine's `takeFirst` state. -/
theorem header_computes_to_shift_source
    (fuelZero : Bool)
    (D : MachineDescription) (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (headerConfig fuelZero (headerParserSourceConfig D fuel input))
      (headerConfig fuelZero
        (headerParserTransitionCountConfig D fuel input)) := by
  let suffixState : Word MachineCodeSymbol :=
    MachineDescription.encodeNatAppend D.start
      (MachineDescription.encodeNatAppend D.halt
        (MachineDescription.encodeNatAppend D.transitions.length
          (MachineDescription.encodeTransitionsAppend D.transitions input)))
  let suffixStart : Word MachineCodeSymbol :=
    MachineDescription.encodeNatAppend D.halt
      (MachineDescription.encodeNatAppend D.transitions.length
        (MachineDescription.encodeTransitionsAppend D.transitions input))
  let suffixHalt : Word MachineCodeSymbol :=
    MachineDescription.encodeNatAppend D.transitions.length
      (MachineDescription.encodeTransitionsAppend D.transitions input)
  have hheader :
      TuringMachine.Step machine
        (headerConfig fuelZero (headerParserSourceConfig D fuel input))
        (headerConfig fuelZero
          { state := HeaderFieldsParserState.stateCount
            tape := headerFieldsParserTape
              (headerAfterHeaderLeftRev fuel)
              (MachineDescription.encodeNatAppend D.stateCount
                suffixState) }) := by
    simpa [headerParserSourceConfig, headerAfterHeaderLeftRev,
      MachineDescription.encodeDescriptionAppend, suffixState] using
      header_step_header fuelZero (MachineDescription.encodeNat fuel).reverse
        (MachineDescription.encodeNatAppend D.stateCount suffixState)
  have hstate :=
    TuringMachine.computesIn_to_computes
      (header_computesIn_nat fuelZero
        (header_step_tick_stateCount fuelZero)
        (header_step_done_stateCount fuelZero)
        (headerAfterHeaderLeftRev fuel) D.stateCount suffixState)
  have hstart :=
    TuringMachine.computesIn_to_computes
      (header_computesIn_nat fuelZero
        (header_step_tick_startField fuelZero)
        (header_step_done_startField fuelZero)
        (headerAfterStateLeftRev D fuel) D.start suffixStart)
  have hhalt :=
    TuringMachine.computesIn_to_computes
      (header_computesIn_nat fuelZero
        (header_step_tick_haltField fuelZero)
        (header_step_done_haltField fuelZero)
        (headerAfterStartLeftRev D fuel) D.halt suffixHalt)
  exact
    TuringMachine.Computes.step hheader
      (TuringMachine.computes_trans hstate
        (TuringMachine.computes_trans
          (by
            simpa [suffixState, headerAfterStateLeftRev] using hstart)
          (by
            simpa [suffixStart, suffixHalt,
              headerParserTransitionCountConfig,
              headerAfterStateLeftRev,
              headerAfterStartLeftRev,
              headerAfterHaltLeftRev] using hhalt)))

def headerAfterThreeFieldsLeftRev
    (leftRev : Word MachineCodeSymbol)
    (stateCount start halt : Nat) : Word MachineCodeSymbol :=
  List.append (MachineDescription.encodeNat halt).reverse
    (List.append (MachineDescription.encodeNat start).reverse
      (List.append (MachineDescription.encodeNat stateCount).reverse
        (MachineCodeSymbol.header :: leftRev)))

theorem header_three_fields_computes_to_shift_source
    (fuelZero : Bool)
    (leftRev : Word MachineCodeSymbol)
    (stateCount start halt : Nat)
    (tail : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (headerConfig fuelZero
        { state := HeaderFieldsParserState.needHeader
          tape := headerFieldsParserTape leftRev
            (MachineCodeSymbol.header ::
              MachineDescription.encodeNatAppend stateCount
                (MachineDescription.encodeNatAppend start
                  (MachineDescription.encodeNatAppend halt tail))) })
      (headerConfig fuelZero
        { state := HeaderFieldsParserState.transitionCount
          tape := headerFieldsParserTape
            (headerAfterThreeFieldsLeftRev leftRev stateCount start halt)
            tail }) := by
  let afterHeader := MachineCodeSymbol.header :: leftRev
  let afterState :=
    List.append (MachineDescription.encodeNat stateCount).reverse
      afterHeader
  let afterStart :=
    List.append (MachineDescription.encodeNat start).reverse afterState
  have hheader : TuringMachine.Step machine
      (headerConfig fuelZero
        { state := HeaderFieldsParserState.needHeader
          tape := headerFieldsParserTape leftRev
            (MachineCodeSymbol.header ::
              MachineDescription.encodeNatAppend stateCount
                (MachineDescription.encodeNatAppend start
                  (MachineDescription.encodeNatAppend halt tail))) })
      (headerConfig fuelZero
        { state := HeaderFieldsParserState.stateCount
          tape := headerFieldsParserTape afterHeader
            (MachineDescription.encodeNatAppend stateCount
              (MachineDescription.encodeNatAppend start
                (MachineDescription.encodeNatAppend halt tail))) }) := by
    simpa [afterHeader] using
      header_step_header fuelZero leftRev
        (MachineDescription.encodeNatAppend stateCount
          (MachineDescription.encodeNatAppend start
            (MachineDescription.encodeNatAppend halt tail)))
  have hstate := TuringMachine.computesIn_to_computes
    (header_computesIn_nat fuelZero
      (header_step_tick_stateCount fuelZero)
      (header_step_done_stateCount fuelZero)
      afterHeader stateCount
      (MachineDescription.encodeNatAppend start
        (MachineDescription.encodeNatAppend halt tail)))
  have hstart := TuringMachine.computesIn_to_computes
    (header_computesIn_nat fuelZero
      (header_step_tick_startField fuelZero)
      (header_step_done_startField fuelZero)
      afterState start (MachineDescription.encodeNatAppend halt tail))
  have hhalt := TuringMachine.computesIn_to_computes
    (header_computesIn_nat fuelZero
      (header_step_tick_haltField fuelZero)
      (header_step_done_haltField fuelZero)
      afterStart halt tail)
  dsimp [afterHeader, afterState, afterStart,
    headerAfterThreeFieldsLeftRev] at hheader hstate hstart hhalt ⊢
  exact TuringMachine.Computes.step hheader
    (TuringMachine.computes_trans hstate
      (TuringMachine.computes_trans hstart hhalt))

/-- Forward halting of the standalone four-field header parser on a canonical
header prefix, with arbitrary retained left context and arbitrary suffix. -/
theorem header_four_fields_haltsFromIn
    (leftRev : Word MachineCodeSymbol)
    (stateCount start halt count : Nat)
    (tail : Word MachineCodeSymbol) :
    exists steps : Nat,
      TuringMachine.HaltsFromIn headerFieldsParserMachine steps
        { state := HeaderFieldsParserState.needHeader
          tape := headerFieldsParserTape leftRev
            (MachineCodeSymbol.header ::
              MachineDescription.encodeNatAppend stateCount
                (MachineDescription.encodeNatAppend start
                  (MachineDescription.encodeNatAppend halt
                    (MachineDescription.encodeNatAppend count tail)))) } := by
  let afterHeader := MachineCodeSymbol.header :: leftRev
  let afterState :=
    List.append (MachineDescription.encodeNat stateCount).reverse
      afterHeader
  let afterStart :=
    List.append (MachineDescription.encodeNat start).reverse afterState
  let afterHalt :=
    List.append (MachineDescription.encodeNat halt).reverse afterStart
  let final : TuringMachine.Configuration MachineCodeSymbol
      HeaderFieldsParserState :=
    { state := HeaderFieldsParserState.done
      tape := headerFieldsParserTape
        (List.append (MachineDescription.encodeNat count).reverse afterHalt)
        tail }
  have hheader :=
    headerFieldsParserMachine_step_header leftRev
      (MachineDescription.encodeNatAppend stateCount
        (MachineDescription.encodeNatAppend start
          (MachineDescription.encodeNatAppend halt
            (MachineDescription.encodeNatAppend count tail))))
  have hstate := TuringMachine.computesIn_to_computes
    (headerFieldsParserMachine_computesIn_nat
      headerFieldsParserMachine_step_tick_stateCount
      headerFieldsParserMachine_step_done_stateCount
      afterHeader stateCount
      (MachineDescription.encodeNatAppend start
        (MachineDescription.encodeNatAppend halt
          (MachineDescription.encodeNatAppend count tail))))
  have hstart := TuringMachine.computesIn_to_computes
    (headerFieldsParserMachine_computesIn_nat
      headerFieldsParserMachine_step_tick_startField
      headerFieldsParserMachine_step_done_startField
      afterState start
      (MachineDescription.encodeNatAppend halt
        (MachineDescription.encodeNatAppend count tail)))
  have hhalt := TuringMachine.computesIn_to_computes
    (headerFieldsParserMachine_computesIn_nat
      headerFieldsParserMachine_step_tick_haltField
      headerFieldsParserMachine_step_done_haltField
      afterStart halt (MachineDescription.encodeNatAppend count tail))
  have hcount := TuringMachine.computesIn_to_computes
    (headerFieldsParserMachine_computesIn_nat
      headerFieldsParserMachine_step_tick_transitionCount
      headerFieldsParserMachine_step_done_transitionCount
      afterHalt count tail)
  have hrun : TuringMachine.Computes headerFieldsParserMachine
      { state := HeaderFieldsParserState.needHeader
        tape := headerFieldsParserTape leftRev
          (MachineCodeSymbol.header ::
            MachineDescription.encodeNatAppend stateCount
              (MachineDescription.encodeNatAppend start
                (MachineDescription.encodeNatAppend halt
                  (MachineDescription.encodeNatAppend count tail)))) }
      final := by
    dsimp [afterHeader, afterState, afterStart, afterHalt, final]
      at hheader hstate hstart hhalt hcount ⊢
    exact TuringMachine.Computes.step hheader
      (TuringMachine.computes_trans hstate
        (TuringMachine.computes_trans hstart
          (TuringMachine.computes_trans hhalt hcount)))
  rcases TuringMachine.computes_to_computesIn hrun with ⟨steps, hrunIn⟩
  exact ⟨steps, final, hrunIn, rfl⟩

theorem shift_step_lift_active
    (fuelZero : Bool)
    {source target :
      TuringMachine.Configuration MachineCodeSymbol
        ContextualPrefixRightShiftOne.Control}
    (hstep :
      ContextualPrefixRightShiftOne.machine.stepConfig source =
        some target) :
    machine.stepConfig (shiftConfig fuelZero source) =
      some (shiftConfig fuelZero target) := by
  cases source with
  | mk state tape =>
      cases target with
      | mk targetState targetTape =>
          cases haction :
              ContextualPrefixRightShiftOne.machine.transition state
                (Tape.read tape) with
          | none =>
              simp [TuringMachine.stepConfig, haction] at hstep
          | some action =>
              rcases action with ⟨write, direction, next⟩
              simp [TuringMachine.stepConfig, haction] at hstep
              rcases hstep with ⟨rfl, rfl⟩
              have hstate :
                  state ≠
                    ProductCleanupGap.PrefixRightShiftOne.Control.halt := by
                intro heq
                subst state
                change none = some (write, direction, next) at haction
                contradiction
              cases state with
              | halt => contradiction
              | takeFirst | carry _ | turnGap | rewind =>
                  simp only [shiftConfig,
                    TuringMachine.PhaseEmbedding.liftConfig,
                    machine, TuringMachine.stepConfig, transition,
                    shiftTarget]
                  rw [haction]
                  rfl

theorem shift_run_exact_lift
    (fuelZero : Bool)
    {steps : Nat}
    {source target :
      TuringMachine.Configuration MachineCodeSymbol
        ContextualPrefixRightShiftOne.Control}
    (hrun :
      ContextualPrefixRightShiftOne.machine.runConfigExact? steps source =
        some target) :
    machine.runConfigExact? steps (shiftConfig fuelZero source) =
      some (shiftConfig fuelZero target) := by
  exact
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      (shiftTarget fuelZero)
      (fun _ _ hstep => shift_step_lift_active fuelZero hstep) hrun

end Section53ParserPrefixPhaseSum
end Computability
end FoC
