import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Parser.Prefix.Basic

namespace FoC
namespace Computability

open Languages
open FiniteRecognizer ExactFuel StrictProbe

namespace Section53ParserPrefixPhaseSum

open Section53ParserAssembly
open Section53OuterParserInversion

def countValidateConfig
    (fuelZero : Bool) (tape : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .countValidate fuelZero, tape := tape }

def countRewindConfig
    (fuelZero : Bool) (tape : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .countRewind fuelZero, tape := tape }

def tableStartConfig
    (fuelZero : Bool) (tape : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state :=
      .table fuelZero Section53SavedCellTransitionParser.machine.start
    tape := tape }

def countValidatorSourceTape
    (farLeft : List (Option MachineCodeSymbol))
    (count : Nat) (suffix : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  transitionListParserOptionTape (none :: farLeft)
    ((MachineDescription.encodeNatAppend count suffix).map some)

def countValidatorRawScanTape
    (farLeft : List (Option MachineCodeSymbol))
    (scanned : Nat) (rest : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  transitionListParserOptionTape
    (List.append
      (List.replicate scanned (some MachineCodeSymbol.tick))
      (none :: farLeft))
    (rest.map some)

theorem count_validate_raw_tick_step
    (fuelZero : Bool)
    (farLeft : List (Option MachineCodeSymbol))
    (scanned : Nat)
    (suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (countValidateConfig fuelZero
          (countValidatorRawScanTape farLeft scanned
            (MachineCodeSymbol.tick :: suffix))) =
      some
        (countValidateConfig fuelZero
          (countValidatorRawScanTape farLeft (scanned + 1) suffix)) := by
  cases scanned <;> cases farLeft <;> cases suffix <;>
    simp [countValidateConfig, countValidatorRawScanTape,
      transitionListParserOptionTape, List.replicate_succ,
      machine, transition, TuringMachine.stepConfig,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

/-- Reaching a successful table endpoint through the count validator implies
that the remaining word starts with one complete unary count field. -/
theorem count_validate_success_only_encodeNatAppend
    (fuelZero : Bool)
    (farLeft : List (Option MachineCodeSymbol))
    (scanned : Nat)
    (rest : Word MachineCodeSymbol)
    {final : TuringMachine.Configuration MachineCodeSymbol Control}
    (hrun : TuringMachine.Computes machine
      (countValidateConfig fuelZero
        (countValidatorRawScanTape farLeft scanned rest)) final)
    (hsuccess : SuccessfulTerminal final) :
    exists count : Nat,
    exists suffix : Word MachineCodeSymbol,
      rest = MachineDescription.encodeNatAppend count suffix := by
  induction rest generalizing scanned with
  | nil =>
      cases hrun with
      | refl =>
          simp [SuccessfulTerminal, countValidateConfig] at hsuccess
      | step hstep _ =>
          exact False.elim
            ((TuringMachine.not_step_of_transition_eq_none
              (M := machine)
              (c := countValidateConfig fuelZero
                (countValidatorRawScanTape farLeft scanned []))
              (by
                cases scanned <;> cases farLeft <;>
                  simp [machine, transition, countValidateConfig,
                    countValidatorRawScanTape,
                    transitionListParserOptionTape, Tape.read])) hstep)
  | cons symbol suffix ih =>
      cases symbol with
      | tick =>
          have hstep : TuringMachine.Step machine
              (countValidateConfig fuelZero
                (countValidatorRawScanTape farLeft scanned
                  (MachineCodeSymbol.tick :: suffix)))
              (countValidateConfig fuelZero
                (countValidatorRawScanTape farLeft (scanned + 1)
                  suffix)) :=
            TuringMachine.stepConfig_eq_some_iff_step.mp
              (count_validate_raw_tick_step fuelZero farLeft scanned suffix)
          have hprefix : TuringMachine.ComputesIn machine 1
              (countValidateConfig fuelZero
                (countValidatorRawScanTape farLeft scanned
                  (MachineCodeSymbol.tick :: suffix)))
              (countValidateConfig fuelZero
                (countValidatorRawScanTape farLeft (scanned + 1)
                  suffix)) :=
            TuringMachine.ComputesIn.succ hstep
              (TuringMachine.ComputesIn.zero _)
          have htail :=
            computes_suffix_of_computesIn_of_successful
              hprefix hrun hsuccess
          rcases ih (scanned + 1) htail with
            ⟨count, tail, hsuffix⟩
          exact ⟨count + 1, tail, by
            simp [MachineDescription.encodeNatAppend,
              MachineDescription.encodeNat, hsuffix]⟩
      | done =>
          exact ⟨0, suffix, by
            simp [MachineDescription.encodeNatAppend,
              MachineDescription.encodeNat]⟩
      | header | transition | blank | zero | one | moveLeft | moveRight =>
          cases hrun with
          | refl =>
              simp [SuccessfulTerminal, countValidateConfig] at hsuccess
          | step hstep _ =>
              cases hstep with
              | mk haction =>
                  cases scanned <;> cases farLeft <;> cases suffix <;>
                    simp [machine, transition, countValidateConfig,
                      countValidatorRawScanTape,
                      transitionListParserOptionTape, Tape.read] at haction

def countValidatorScanTape
    (farLeft : List (Option MachineCodeSymbol))
    (scanned remaining : Nat)
    (suffix : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  transitionListParserOptionTape
    (List.append
      (List.replicate scanned (some MachineCodeSymbol.tick))
      (none :: farLeft))
    ((MachineDescription.encodeNatAppend remaining suffix).map some)

def countValidatorRewindTape
    (farLeft : List (Option MachineCodeSymbol))
    (remaining crossed : Nat)
    (suffix : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match remaining with
  | 0 =>
      { left := farLeft
        head := none
        right :=
          List.append
            (List.replicate crossed (some MachineCodeSymbol.tick))
            (some MachineCodeSymbol.done :: suffix.map some) }
  | n + 1 =>
      { left :=
          List.append
            (List.replicate n (some MachineCodeSymbol.tick))
            (none :: farLeft)
        head := some MachineCodeSymbol.tick
        right :=
          List.append
            (List.replicate crossed (some MachineCodeSymbol.tick))
            (some MachineCodeSymbol.done :: suffix.map some) }

theorem map_encodeNat_eq_replicate_tick_done (count : Nat) :
    (MachineDescription.encodeNat count).map some =
      List.replicate count (some MachineCodeSymbol.tick) ++
        [some MachineCodeSymbol.done] := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [MachineDescription.encodeNat, List.replicate_succ, ih]

theorem count_validate_tick_step
    (fuelZero : Bool)
    (farLeft : List (Option MachineCodeSymbol))
    (scanned remaining : Nat)
    (suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (countValidateConfig fuelZero
          (countValidatorScanTape farLeft scanned (remaining + 1) suffix)) =
      some
        (countValidateConfig fuelZero
          (countValidatorScanTape farLeft (scanned + 1) remaining suffix)) := by
  cases remaining <;> cases suffix <;>
    simp [countValidateConfig, countValidatorScanTape,
      transitionListParserOptionTape,
      MachineDescription.encodeNatAppend, MachineDescription.encodeNat,
      List.replicate_succ,
      machine, transition, TuringMachine.stepConfig,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem count_validate_done_step
    (fuelZero : Bool)
    (farLeft : List (Option MachineCodeSymbol))
    (scanned : Nat)
    (suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (countValidateConfig fuelZero
          (countValidatorScanTape farLeft scanned 0 suffix)) =
      some
        (countRewindConfig fuelZero
          (countValidatorRewindTape farLeft scanned 0 suffix)) := by
  cases scanned <;> cases farLeft <;> cases suffix <;>
    simp [countValidateConfig, countRewindConfig,
      countValidatorScanTape, countValidatorRewindTape,
      transitionListParserOptionTape,
      MachineDescription.encodeNatAppend, MachineDescription.encodeNat,
      List.replicate_succ,
      machine, transition, TuringMachine.stepConfig,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem count_rewind_tick_step
    (fuelZero : Bool)
    (farLeft : List (Option MachineCodeSymbol))
    (remaining crossed : Nat)
    (suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (countRewindConfig fuelZero
          (countValidatorRewindTape farLeft (remaining + 1) crossed suffix)) =
      some
        (countRewindConfig fuelZero
          (countValidatorRewindTape farLeft remaining (crossed + 1)
            suffix)) := by
  cases remaining <;> cases farLeft <;> cases suffix <;>
    simp [countRewindConfig, countValidatorRewindTape,
      List.replicate_succ,
      machine, transition, TuringMachine.stepConfig,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem count_rewind_finish_step
    (fuelZero : Bool)
    (farLeft : List (Option MachineCodeSymbol))
    (crossed : Nat)
    (suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (countRewindConfig fuelZero
          (countValidatorRewindTape farLeft 0 crossed suffix)) =
      some
        (tableStartConfig fuelZero
          (countValidatorSourceTape farLeft crossed suffix)) := by
  cases crossed <;> cases suffix <;>
    simp [countRewindConfig, tableStartConfig,
      countValidatorRewindTape, countValidatorSourceTape,
      transitionListParserOptionTape,
      MachineDescription.encodeNatAppend, MachineDescription.encodeNat,
      map_encodeNat_eq_replicate_tick_done,
      List.replicate_succ, List.append_assoc,
      machine, transition, TuringMachine.stepConfig,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem count_validate_run_exact
    (fuelZero : Bool)
    (farLeft : List (Option MachineCodeSymbol))
    (scanned remaining : Nat)
    (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (remaining + 1)
        (countValidateConfig fuelZero
          (countValidatorScanTape farLeft scanned remaining suffix)) =
      some
        (countRewindConfig fuelZero
          (countValidatorRewindTape farLeft (scanned + remaining) 0
            suffix)) := by
  induction remaining generalizing scanned with
  | zero =>
      rw [TuringMachine.runConfigExact?]
      exact count_validate_done_step fuelZero farLeft scanned suffix
  | succ remaining ih =>
      change
        machine.runConfigExact? ((remaining + 1) + 1)
            (countValidateConfig fuelZero
              (countValidatorScanTape farLeft scanned (remaining + 1)
                suffix)) = _
      rw [TuringMachine.runConfigExact?]
      rw [count_validate_tick_step]
      simp only
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (scanned + 1)

theorem count_rewind_run_exact
    (fuelZero : Bool)
    (farLeft : List (Option MachineCodeSymbol))
    (remaining crossed : Nat)
    (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (remaining + 1)
        (countRewindConfig fuelZero
          (countValidatorRewindTape farLeft remaining crossed suffix)) =
      some
        (tableStartConfig fuelZero
          (countValidatorSourceTape farLeft (remaining + crossed)
            suffix)) := by
  induction remaining generalizing crossed with
  | zero =>
      rw [TuringMachine.runConfigExact?]
      rw [count_rewind_finish_step]
      simp [TuringMachine.runConfigExact?]
  | succ remaining ih =>
      change
        machine.runConfigExact? ((remaining + 1) + 1)
            (countRewindConfig fuelZero
              (countValidatorRewindTape farLeft (remaining + 1) crossed
                suffix)) = _
      rw [TuringMachine.runConfigExact?]
      rw [count_rewind_tick_step]
      simp only
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (crossed + 1)

theorem count_validator_run_exact
    (fuelZero : Bool)
    (farLeft : List (Option MachineCodeSymbol))
    (count : Nat) (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? ((count + 1) + (count + 1))
        (countValidateConfig fuelZero
          (countValidatorSourceTape farLeft count suffix)) =
      some
        (tableStartConfig fuelZero
          (countValidatorSourceTape farLeft count suffix)) := by
  apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr
  apply TuringMachine.computesIn_trans
  · apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
    simpa [countValidatorSourceTape, countValidatorScanTape] using
      count_validate_run_exact fuelZero farLeft 0 count suffix
  · apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
    simpa using count_rewind_run_exact fuelZero farLeft count 0 suffix

def canonicalSourceConfig
    (D : MachineDescription) (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  sourceConfig
    (MachineDescription.encodeNatAppend fuel
      (MachineDescription.encodeDescriptionAppend D input))

def canonicalSavedTableSourceConfig
    (D : MachineDescription) (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      Section53SavedCellTransitionParser.Control :=
  Section53SavedCellTransitionParser.parserConfig
    (TransitionParserContextTransport.contextualCanonicalSource
      (headerAfterHaltLeftRev D fuel) D.transitions input)

def fuelZeroFlag : Nat -> Bool
  | 0 => true
  | _ + 1 => false

theorem fuel_initial_computes_to_header
    (fuel : Nat) (encoded : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (sourceConfig (MachineDescription.encodeNatAppend fuel encoded))
      (headerConfig (fuelZeroFlag fuel)
        { state := HeaderFieldsParserState.needHeader
          tape := headerFieldsParserTape
            (MachineDescription.encodeNat fuel).reverse encoded }) := by
  cases fuel with
  | zero =>
      apply TuringMachine.computesIn_to_computes
      apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
      simpa [sourceConfig, fuelZeroFlag] using
        fuel_initial_run_zero ([] : Word MachineCodeSymbol) encoded
  | succ fuel =>
      apply TuringMachine.computesIn_to_computes
      apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
      simpa [sourceConfig, fuelZeroFlag] using
        fuel_initial_run_positive fuel
          ([] : Word MachineCodeSymbol) encoded

/-- Canonical fuel/header parsing and physical separator installation.  The
actual shift endpoint is retained, together with its equivalence to the
saved-table parser's padded contextual source. -/
theorem canonical_computes_to_count_validation
    (D : MachineDescription) (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    exists shiftEndpoint :
        TuringMachine.Configuration MachineCodeSymbol
          ContextualPrefixRightShiftOne.Control,
      TuringMachine.Computes machine
        (canonicalSourceConfig D fuel input)
        (shiftConfig (fuelZeroFlag fuel) shiftEndpoint) ∧
      shiftEndpoint.state =
        ProductCleanupGap.PrefixRightShiftOne.Control.halt ∧
      Tape.Equiv
        (canonicalSavedTableSourceConfig D fuel input).tape
        shiftEndpoint.tape := by
  let encoded := MachineDescription.encodeDescriptionAppend D input
  have hfuel :
      TuringMachine.Computes machine
        (canonicalSourceConfig D fuel input)
        (headerConfig (fuelZeroFlag fuel)
          (headerParserSourceConfig D fuel input)) := by
    cases fuel with
    | zero =>
        apply TuringMachine.computesIn_to_computes
        apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
        simpa [canonicalSourceConfig, sourceConfig, encoded,
          headerParserSourceConfig, fuelZeroFlag] using
          fuel_initial_run_zero ([] : Word MachineCodeSymbol) encoded
    | succ fuel =>
        apply TuringMachine.computesIn_to_computes
        apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
        simpa [canonicalSourceConfig, sourceConfig, encoded,
          headerParserSourceConfig, fuelZeroFlag] using
          fuel_initial_run_positive fuel
            ([] : Word MachineCodeSymbol) encoded
  have hheader :=
    header_computes_to_shift_source
      (fuelZeroFlag fuel) D fuel input
  rcases headerEndpoint_prefixRightShiftOne_forward D fuel input with
    ⟨first, rest, shiftEndpoint, hword, hshiftExact,
      hshiftState, hshiftTape⟩
  have hshift :
      TuringMachine.Computes machine
        (headerConfig (fuelZeroFlag fuel)
          (headerParserTransitionCountConfig D fuel input))
        (shiftConfig (fuelZeroFlag fuel) shiftEndpoint) := by
    have hsource :
        headerConfig (fuelZeroFlag fuel)
            (headerParserTransitionCountConfig D fuel input) =
          shiftConfig (fuelZeroFlag fuel)
            { state :=
                ProductCleanupGap.PrefixRightShiftOne.Control.takeFirst
              tape := (headerParserTransitionCountConfig D fuel input).tape } :=
      rfl
    rw [hsource]
    apply TuringMachine.computesIn_to_computes
    apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
    exact shift_run_exact_lift (fuelZeroFlag fuel) hshiftExact
  have hcanonical :=
    shiftedTarget_equiv_contextualParserSource
      (headerAfterHaltLeftRev D fuel) D.transitions input first rest
      (by
        simpa [TransitionParserContextTransport.canonicalWord,
          transitionParserWord] using hword)
  refine
    ⟨shiftEndpoint,
      TuringMachine.computes_trans hfuel
        (TuringMachine.computes_trans hheader hshift),
      hshiftState, ?_⟩
  exact
    Tape.Equiv.trans (Tape.Equiv.symm (by
      simpa [canonicalSavedTableSourceConfig,
        Section53SavedCellTransitionParser.parserConfig,
        TuringMachine.PhaseEmbedding.liftConfig] using hcanonical))
      hshiftTape

theorem canonical_saved_source_tape_eq_validator_source
    (D : MachineDescription) (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    (canonicalSavedTableSourceConfig D fuel input).tape =
      countValidatorSourceTape
        ((headerAfterHaltLeftRev D fuel).map some)
        D.transitions.length
        (MachineDescription.encodeTransitionsAppend D.transitions input) := by
  cases hword :
      (MachineDescription.encodeNatAppend D.transitions.length
        (MachineDescription.encodeTransitionsAppend D.transitions input)).map
          some <;>
    simp [canonicalSavedTableSourceConfig,
    Section53SavedCellTransitionParser.parserConfig,
    TuringMachine.PhaseEmbedding.liftConfig,
    TransitionParserContextTransport.contextualCanonicalSource,
    TransitionParserContextTransport.appendLeftContextConfig,
    TransitionParserContextTransport.appendLeftContext,
    TransitionParserContextTransport.paddedCanonicalSource,
    TransitionParserContextTransport.canonicalWord,
    countValidatorSourceTape, transitionListParserOptionTape, hword]

/-- Canonical parsing reaches the saved-table start only after validating and
rewinding the unary transition count installed beyond the fresh separator. -/
theorem canonical_computes_to_table_ingress
    (D : MachineDescription) (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    exists tableSource :
        TuringMachine.Configuration MachineCodeSymbol
          Section53SavedCellTransitionParser.Control,
      TuringMachine.Computes machine
        (canonicalSourceConfig D fuel input)
        (tableConfig (fuelZeroFlag fuel) tableSource) ∧
      tableSource.state =
        Section53SavedCellTransitionParser.machine.start ∧
      Tape.Equiv
        (canonicalSavedTableSourceConfig D fuel input).tape
        tableSource.tape := by
  rcases canonical_computes_to_count_validation D fuel input with
    ⟨shiftEndpoint, hprefix, hshiftState, htape⟩
  have hvalidatorCanonical :
      TuringMachine.ComputesIn machine
        ((D.transitions.length + 1) + (D.transitions.length + 1))
        (countValidateConfig (fuelZeroFlag fuel)
          (canonicalSavedTableSourceConfig D fuel input).tape)
        (tableStartConfig (fuelZeroFlag fuel)
          (canonicalSavedTableSourceConfig D fuel input).tape) := by
    apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
    rw [canonical_saved_source_tape_eq_validator_source]
    exact count_validator_run_exact
      (fuelZeroFlag fuel)
      ((headerAfterHaltLeftRev D fuel).map some)
      D.transitions.length
      (MachineDescription.encodeTransitionsAppend D.transitions input)
  rcases
      TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
        hvalidatorCanonical htape with
    ⟨actualTarget, hactualRunIn, hactualState, hactualTape⟩
  let actualSource :
      TuringMachine.Configuration MachineCodeSymbol Control :=
    { state :=
        (countValidateConfig (fuelZeroFlag fuel)
          (canonicalSavedTableSourceConfig D fuel input).tape).state
      tape := shiftEndpoint.tape }
  let tableSource :
      TuringMachine.Configuration MachineCodeSymbol
        Section53SavedCellTransitionParser.Control :=
    { state := Section53SavedCellTransitionParser.machine.start
      tape := actualTarget.tape }
  have hshiftHandoff :
      shiftConfig (fuelZeroFlag fuel) shiftEndpoint = actualSource := by
    cases shiftEndpoint with
    | mk state tape =>
        simp only at hshiftState
        subst state
        rfl
  have htargetHandoff :
      actualTarget = tableConfig (fuelZeroFlag fuel) tableSource := by
    cases actualTarget with
    | mk state tape =>
        simp only [tableStartConfig] at hactualState
        subst state
        rfl
  have hvalidator :
      TuringMachine.Computes machine actualSource
        (tableConfig (fuelZeroFlag fuel) tableSource) := by
    apply TuringMachine.computesIn_to_computes
    rw [← htargetHandoff]
    simpa [actualSource] using hactualRunIn
  refine ⟨tableSource, TuringMachine.computes_trans hprefix ?_, rfl, ?_⟩
  · rw [hshiftHandoff]
    exact hvalidator
  · simpa [tableSource, tableStartConfig] using hactualTape

theorem table_stepConfig
    (fuelZero : Bool)
    (config : TuringMachine.Configuration MachineCodeSymbol
      Section53SavedCellTransitionParser.Control) :
    machine.stepConfig (tableConfig fuelZero config) =
      Option.map (tableConfig fuelZero)
        (Section53SavedCellTransitionParser.machine.stepConfig config) := by
  cases config with
  | mk state tape =>
      unfold TuringMachine.stepConfig
      cases haction :
          Section53SavedCellTransitionParser.machine.transition state
            (Tape.read tape) with
      | none =>
          simp [machine, transition, tableConfig, haction,
            TuringMachine.PhaseEmbedding.liftConfig]
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp [machine, transition, tableConfig, haction, mapAction,
            TuringMachine.PhaseEmbedding.liftConfig]

theorem table_computes_lift
    (fuelZero : Bool)
    {source target : TuringMachine.Configuration MachineCodeSymbol
      Section53SavedCellTransitionParser.Control}
    (hrun : TuringMachine.Computes
      Section53SavedCellTransitionParser.machine source target) :
    TuringMachine.Computes machine
      (tableConfig fuelZero source) (tableConfig fuelZero target) := by
  exact
    TuringMachine.PhaseEmbedding.computes_lift
      (Control.table fuelZero) (table_stepConfig fuelZero) hrun

theorem table_step_inversion
    (fuelZero : Bool)
    {source : TuringMachine.Configuration MachineCodeSymbol
      Section53SavedCellTransitionParser.Control}
    {outerTarget : TuringMachine.Configuration MachineCodeSymbol Control}
    (hstep : TuringMachine.Step machine
      (tableConfig fuelZero source) outerTarget) :
    exists target : TuringMachine.Configuration MachineCodeSymbol
        Section53SavedCellTransitionParser.Control,
      TuringMachine.Step Section53SavedCellTransitionParser.machine
          source target ∧
        outerTarget = tableConfig fuelZero target := by
  have houter := TuringMachine.stepConfig_eq_some_iff_step.mpr hstep
  rw [table_stepConfig] at houter
  cases hinner :
      Section53SavedCellTransitionParser.machine.stepConfig source with
  | none => simp [hinner] at houter
  | some target =>
      simp [hinner] at houter
      subst outerTarget
      exact ⟨target,
        TuringMachine.stepConfig_eq_some_iff_step.mp hinner, rfl⟩

/-- A computation that starts in the table phase cannot leave it before one
of the saved parser's own stuck endpoints; strip the inert phase tag. -/
theorem table_computes_project
    (fuelZero : Bool)
    {source : TuringMachine.Configuration MachineCodeSymbol
      Section53SavedCellTransitionParser.Control}
    {outerTarget : TuringMachine.Configuration MachineCodeSymbol Control}
    (hrun : TuringMachine.Computes machine
      (tableConfig fuelZero source) outerTarget) :
    exists target : TuringMachine.Configuration MachineCodeSymbol
        Section53SavedCellTransitionParser.Control,
      TuringMachine.Computes Section53SavedCellTransitionParser.machine
          source target ∧
        outerTarget = tableConfig fuelZero target := by
  generalize hsourceEq : tableConfig fuelZero source = outerSource at hrun
  induction hrun generalizing source with
  | refl config =>
      exact ⟨source, TuringMachine.Computes.refl _, hsourceEq.symm⟩
  | @step outerSource outerMiddle outerTarget hstep htail ih =>
      have hstep' : TuringMachine.Step machine
          (tableConfig fuelZero source) outerMiddle := by
        rw [hsourceEq]
        exact hstep
      rcases table_step_inversion fuelZero hstep' with
        ⟨middle, hinnerStep, hmiddle⟩
      rcases ih hmiddle.symm with ⟨target, hinnerTail, htarget⟩
      exact ⟨target,
        TuringMachine.Computes.step hinnerStep hinnerTail, htarget⟩

def zeroSavedTableSourceConfig
    (baseLeftRev input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      Section53SavedCellTransitionParser.Control :=
  Section53SavedCellTransitionParser.parserConfig
    (TransitionParserContextTransport.contextualCanonicalSource
      baseLeftRev [] input)

def zeroSavedTableTargetConfig
    (baseLeftRev input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      Section53SavedCellTransitionParser.Control :=
  { state :=
      Section53SavedCellTransitionParser.Control.parser
        TransitionListParserState.halt
    tape :=
      transitionListParserOptionTape
        (some MachineCodeSymbol.done :: none :: baseLeftRev.map some)
        (input.map some) }

theorem zeroSavedTable_step
    (baseLeftRev input : Word MachineCodeSymbol) :
    Section53SavedCellTransitionParser.machine.stepConfig
        (zeroSavedTableSourceConfig baseLeftRev input) =
      some (zeroSavedTableTargetConfig baseLeftRev input) := by
  cases input <;> rfl

theorem zeroSavedTable_computes
    (baseLeftRev input : Word MachineCodeSymbol) :
    TuringMachine.Computes Section53SavedCellTransitionParser.machine
      (zeroSavedTableSourceConfig baseLeftRev input)
      (zeroSavedTableTargetConfig baseLeftRev input) := by
  exact
    TuringMachine.computes_of_step
      (TuringMachine.stepConfig_eq_some_iff_step.mp
        (zeroSavedTable_step baseLeftRev input))

/-- A canonical zero-row description reaches the count-zero parser terminal
while retaining the exact zero-vs-positive fuel bit. -/
theorem canonical_zeroTable_computes_to_terminal_with_tape_equiv
    (D : MachineDescription)
    (htransitions : D.transitions = [])
    (fuel : Nat) (input : Word MachineCodeSymbol) :
    exists final : TuringMachine.Configuration MachineCodeSymbol Control,
      TuringMachine.Computes machine
        (canonicalSourceConfig D fuel input) final ∧
      final.state =
        Control.table (fuelZeroFlag fuel)
          (Section53SavedCellTransitionParser.Control.parser
            TransitionListParserState.halt) ∧
      Tape.Equiv
        (zeroSavedTableTargetConfig
          (headerAfterHaltLeftRev D fuel) input).tape
        final.tape := by
  rcases canonical_computes_to_table_ingress D fuel input with
    ⟨tableSource, hprefix, htableState, htape⟩
  let canonicalLocal :=
    zeroSavedTableSourceConfig (headerAfterHaltLeftRev D fuel) input
  have hcanonicalSource :
      canonicalSavedTableSourceConfig D fuel input = canonicalLocal := by
    simp [canonicalSavedTableSourceConfig, canonicalLocal,
      zeroSavedTableSourceConfig, htransitions]
  have htape' : Tape.Equiv canonicalLocal.tape tableSource.tape := by
    rw [← hcanonicalSource]
    exact htape
  have hcanonicalRunIn :
      TuringMachine.ComputesIn
        Section53SavedCellTransitionParser.machine 1 canonicalLocal
        (zeroSavedTableTargetConfig
          (headerAfterHaltLeftRev D fuel) input) := by
    apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
    rw [TuringMachine.runConfigExact?]
    exact zeroSavedTable_step (headerAfterHaltLeftRev D fuel) input
  rcases
      TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
        hcanonicalRunIn htape' with
    ⟨actualTarget, hactualRunIn, hactualState, hactualTape⟩
  let actualSource :
      TuringMachine.Configuration MachineCodeSymbol
        Section53SavedCellTransitionParser.Control :=
    { state := canonicalLocal.state
      tape := tableSource.tape }
  have hactualRun :
      TuringMachine.Computes Section53SavedCellTransitionParser.machine
        actualSource actualTarget := by
    apply TuringMachine.computesIn_to_computes
    simpa [actualSource] using hactualRunIn
  have hcanonicalState :
      canonicalLocal.state =
        Section53SavedCellTransitionParser.machine.start := by
    rfl
  have hhandoff :
      tableConfig (fuelZeroFlag fuel) tableSource =
        tableConfig (fuelZeroFlag fuel) actualSource := by
    cases tableSource with
    | mk state tape =>
        simp only at htableState
        subst state
        unfold tableConfig actualSource
          TuringMachine.PhaseEmbedding.liftConfig
        rw [hcanonicalState]
  refine
    ⟨tableConfig (fuelZeroFlag fuel) actualTarget,
      TuringMachine.computes_trans hprefix (by
        rw [hhandoff]
        exact table_computes_lift (fuelZeroFlag fuel) hactualRun), ?_, ?_⟩
  · simpa [tableConfig, TuringMachine.PhaseEmbedding.liftConfig,
      zeroSavedTableTargetConfig] using hactualState
  · simpa [tableConfig, TuringMachine.PhaseEmbedding.liftConfig] using
      hactualTape

theorem canonical_zeroTable_computes_to_terminal
    (D : MachineDescription)
    (htransitions : D.transitions = [])
    (fuel : Nat) (input : Word MachineCodeSymbol) :
    exists final : TuringMachine.Configuration MachineCodeSymbol Control,
      TuringMachine.Computes machine
        (canonicalSourceConfig D fuel input) final ∧
      final.state =
        Control.table (fuelZeroFlag fuel)
          (Section53SavedCellTransitionParser.Control.parser
            TransitionListParserState.halt) := by
  rcases
      canonical_zeroTable_computes_to_terminal_with_tape_equiv
        D htransitions fuel input with
    ⟨final, hrun, hstate, _htape⟩
  exact ⟨final, hrun, hstate⟩

/-- A canonical nonempty table reaches the saved-cell terminal while retaining
the exact zero-vs-positive fuel bit. -/
theorem canonical_nonemptyTable_computes_to_terminal_with_tape_equiv
    (D : MachineDescription)
    (t : TransitionDescription)
    (rest : List TransitionDescription)
    (htransitions : D.transitions = t :: rest)
    (fuel : Nat) (input : Word MachineCodeSymbol) :
    exists final : TuringMachine.Configuration MachineCodeSymbol Control,
    exists canonicalTarget : TuringMachine.Configuration MachineCodeSymbol
        Section53SavedCellTransitionParser.Control,
      TuringMachine.Computes machine
        (canonicalSourceConfig D fuel input) final ∧
      TuringMachine.Computes Section53SavedCellTransitionParser.machine
        (canonicalSavedTableSourceConfig D fuel input) canonicalTarget ∧
      final.state =
        Control.table (fuelZeroFlag fuel)
          (Section53SavedCellTransitionParser.Control.ready
            (transitionListParserSavedHead input)) ∧
      canonicalTarget.state =
        Section53SavedCellTransitionParser.Control.ready
          (transitionListParserSavedHead input) ∧
      Tape.Equiv canonicalTarget.tape final.tape := by
  rcases canonical_computes_to_table_ingress D fuel input with
    ⟨tableSource, hprefix, htableState, htape⟩
  let canonicalLocal :
      TuringMachine.Configuration MachineCodeSymbol
        Section53SavedCellTransitionParser.Control :=
    Section53SavedCellTransitionParser.parserConfig
      (TransitionParserContextTransport.contextualCanonicalSource
        (headerAfterHaltLeftRev D fuel) (t :: rest) input)
  have hcanonicalSource :
      canonicalSavedTableSourceConfig D fuel input = canonicalLocal := by
    simp [canonicalSavedTableSourceConfig, canonicalLocal, htransitions]
  have htape' : Tape.Equiv canonicalLocal.tape tableSource.tape := by
    rw [← hcanonicalSource]
    exact htape
  rcases
      Section53SavedCellTransitionParser.contextual_nonempty_computes_to_ready
        (headerAfterHaltLeftRev D fuel) t rest input with
    ⟨canonicalTarget, hcanonicalRun, hcanonicalTargetState⟩
  rcases TuringMachine.computes_to_computesIn hcanonicalRun with
    ⟨steps, hcanonicalRunIn⟩
  rcases
      TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
        hcanonicalRunIn htape' with
    ⟨actualTarget, hactualRunIn, hactualState, hactualTape⟩
  let actualSource :
      TuringMachine.Configuration MachineCodeSymbol
        Section53SavedCellTransitionParser.Control :=
    { state := canonicalLocal.state
      tape := tableSource.tape }
  have hactualRun :
      TuringMachine.Computes Section53SavedCellTransitionParser.machine
        actualSource actualTarget := by
    apply TuringMachine.computesIn_to_computes
    simpa [actualSource] using hactualRunIn
  have hcanonicalState :
      canonicalLocal.state =
        Section53SavedCellTransitionParser.machine.start := by
    rfl
  have hhandoff :
      tableConfig (fuelZeroFlag fuel) tableSource =
        tableConfig (fuelZeroFlag fuel) actualSource := by
    cases tableSource with
    | mk state tape =>
        simp only at htableState
        subst state
        unfold tableConfig actualSource
          TuringMachine.PhaseEmbedding.liftConfig
        rw [hcanonicalState]
  refine
    ⟨tableConfig (fuelZeroFlag fuel) actualTarget, canonicalTarget,
      TuringMachine.computes_trans hprefix (by
        rw [hhandoff]
        exact table_computes_lift (fuelZeroFlag fuel) hactualRun), ?_, ?_,
      hcanonicalTargetState, ?_⟩
  · rw [hcanonicalSource]
    simpa [canonicalLocal] using hcanonicalRun
  · change
      Control.table (fuelZeroFlag fuel) actualTarget.state =
        Control.table (fuelZeroFlag fuel)
          (Section53SavedCellTransitionParser.Control.ready
            (transitionListParserSavedHead input))
    rw [hactualState, hcanonicalTargetState]
  · simpa [tableConfig, TuringMachine.PhaseEmbedding.liftConfig] using
      hactualTape

theorem canonical_nonemptyTable_computes_to_terminal
    (D : MachineDescription)
    (t : TransitionDescription)
    (rest : List TransitionDescription)
    (htransitions : D.transitions = t :: rest)
    (fuel : Nat) (input : Word MachineCodeSymbol) :
    exists final : TuringMachine.Configuration MachineCodeSymbol Control,
      TuringMachine.Computes machine
        (canonicalSourceConfig D fuel input) final ∧
      final.state =
        Control.table (fuelZeroFlag fuel)
          (Section53SavedCellTransitionParser.Control.ready
            (transitionListParserSavedHead input)) := by
  rcases
      canonical_nonemptyTable_computes_to_terminal_with_tape_equiv
        D t rest htransitions fuel input with
    ⟨final, _canonicalTarget, hrun, _hcanonicalRun, hstate,
      _hcanonicalState, _htape⟩
  exact ⟨final, hrun, hstate⟩

end Section53ParserPrefixPhaseSum
end Computability
end FoC
