import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Parser.Prefix.Validator

namespace FoC
namespace Computability

open Languages
open FiniteRecognizer ExactFuel StrictProbe

namespace FiniteRecognizer.Interpreter.ParserPrefixPhaseSum

open FiniteRecognizer.Interpreter.ParserAssembly
open FiniteRecognizer.Interpreter.OuterParserInversion

/-! ## Successful-prefix evidence projection -/

/-- Any successful prefix run exposes all four header fields and an honest
halt of the original transition-list parser on the barrier-delimited padded
source. -/
theorem successfulTerminal_recovers_parser_fields
    {tokens : Word MachineCodeSymbol}
    {final : TuringMachine.Configuration MachineCodeSymbol Control}
    (hrun : TuringMachine.Computes machine (sourceConfig tokens) final)
    (hsuccess : SuccessfulTerminal final) :
    exists fuel stateCount start halt count : Nat,
    exists encoded rowTokens : Word MachineCodeSymbol,
      tokens = MachineDescription.encodeNatAppend fuel encoded ∧
      encoded =
        MachineCodeSymbol.header ::
          MachineDescription.encodeNatAppend stateCount
            (MachineDescription.encodeNatAppend start
              (MachineDescription.encodeNatAppend halt
                (MachineDescription.encodeNatAppend count rowTokens))) ∧
      TuringMachine.HaltsFrom transitionListParserMachine
        { state :=
            TransitionListParserState.findCount
              TransitionListParserMarker.initial
          tape :=
            transitionListParserOptionTape [none]
              ((MachineDescription.encodeNatAppend count rowTokens).map
                some) } := by
  rcases fuel_success_only_encodeNatAppend true [] tokens hrun hsuccess with
    ⟨fuel, encoded, htokens⟩
  have hrun' : TuringMachine.Computes machine
      (sourceConfig (MachineDescription.encodeNatAppend fuel encoded))
      final := by
    simpa [htokens] using hrun
  have hfuel := fuel_initial_computes_to_header fuel encoded
  rcases TuringMachine.computes_to_computesIn hfuel with
    ⟨fuelSteps, hfuelIn⟩
  have hheaderRun :=
    computes_suffix_of_computesIn_of_successful
      hfuelIn hrun' hsuccess
  rcases
      header_success_only_three_fields
        (fuelZeroFlag fuel) (MachineDescription.encodeNat fuel).reverse
        encoded hheaderRun hsuccess with
    ⟨stateCount, start, halt, tail, hheaderShape⟩
  have hheaderRun' : TuringMachine.Computes machine
      (headerConfig (fuelZeroFlag fuel)
        { state := HeaderFieldsParserState.needHeader
          tape := headerFieldsParserTape
            (MachineDescription.encodeNat fuel).reverse
            (MachineCodeSymbol.header ::
              MachineDescription.encodeNatAppend stateCount
                (MachineDescription.encodeNatAppend start
                  (MachineDescription.encodeNatAppend halt tail))) })
      final := by
    simpa [hheaderShape] using hheaderRun
  have hheaderPrefix :=
    header_three_fields_computes_to_shift_source
      (fuelZeroFlag fuel) (MachineDescription.encodeNat fuel).reverse
      stateCount start halt tail
  rcases TuringMachine.computes_to_computesIn hheaderPrefix with
    ⟨headerSteps, hheaderIn⟩
  have hshiftRun :=
    computes_suffix_of_computesIn_of_successful
      hheaderIn hheaderRun' hsuccess
  let baseLeftRev :=
    headerAfterThreeFieldsLeftRev
      (MachineDescription.encodeNat fuel).reverse stateCount start halt
  cases htail : tail with
  | nil =>
      cases hshiftRun with
      | refl =>
          simp [SuccessfulTerminal, headerConfig, headerTarget,
            TuringMachine.PhaseEmbedding.liftConfig] at hsuccess
      | step hstep _ =>
          exact False.elim
            ((TuringMachine.not_step_of_transition_eq_none
              (M := machine)
              (c := headerConfig (fuelZeroFlag fuel)
                { state := HeaderFieldsParserState.transitionCount
                  tape := headerFieldsParserTape baseLeftRev [] })
              (by rfl)) (by simpa [htail, baseLeftRev] using hstep))
  | cons first rest =>
      rcases
          ContextualPrefixRightShiftOne.run_from_cursor
            baseLeftRev first rest with
        ⟨shiftEndpoint, hshiftExact, hshiftState, hshiftTape⟩
      have hshiftExactOuter :=
        shift_run_exact_lift (fuelZeroFlag fuel) hshiftExact
      have hshiftIn :=
        TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
          hshiftExactOuter
      have hshiftRun' : TuringMachine.Computes machine
          (shiftConfig (fuelZeroFlag fuel)
            (ContextualPrefixRightShiftOne.cursorSourceConfig
              baseLeftRev first rest)) final := by
        simpa [hheaderShape, htail, baseLeftRev,
          headerConfig, headerTarget, shiftConfig, shiftTarget,
          TuringMachine.PhaseEmbedding.liftConfig,
          ContextualPrefixRightShiftOne.cursorSourceConfig,
          ContextualPrefixRightShiftOne.config] using hshiftRun
      have hvalidatorFromEndpoint :=
        computes_suffix_of_computesIn_of_successful
          hshiftIn hshiftRun' hsuccess
      have hvalidatorActual : TuringMachine.Computes machine
          (countValidateConfig (fuelZeroFlag fuel) shiftEndpoint.tape)
          final := by
        rcases shiftEndpoint with ⟨shiftState, shiftTape⟩
        simp only at hshiftState
        subst shiftState
        simpa [shiftConfig, shiftTarget,
          TuringMachine.PhaseEmbedding.liftConfig,
          countValidateConfig] using hvalidatorFromEndpoint
      rcases TuringMachine.computes_to_computesIn hvalidatorActual with
        ⟨validatorTailSteps, hvalidatorActualIn⟩
      rcases
          TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
            hvalidatorActualIn (Tape.Equiv.symm hshiftTape) with
        ⟨canonicalFinal, hcanonicalRunIn, hcanonicalState,
          _hcanonicalTape⟩
      have hcanonicalRun : TuringMachine.Computes machine
          (countValidateConfig (fuelZeroFlag fuel)
            (ContextualPrefixRightShiftOne.targetTape
              baseLeftRev first rest [])) canonicalFinal :=
        TuringMachine.computesIn_to_computes hcanonicalRunIn
      have hcanonicalSuccess : SuccessfulTerminal canonicalFinal := by
        simpa [SuccessfulTerminal, hcanonicalState] using hsuccess
      have htargetRawTape : Tape.Equiv
          (ContextualPrefixRightShiftOne.targetTape
            baseLeftRev first rest [])
          (countValidatorRawScanTape (baseLeftRev.map some) 0
            (first :: rest)) := by
        refine ⟨rfl, rfl, ?_⟩
        change Tape.dropTrailingNone (rest.map some ++ [none]) =
          Tape.dropTrailingNone (rest.map some)
        rw [dropTrailingNone_append_none]
      rcases TuringMachine.computes_to_computesIn hcanonicalRun with
        ⟨rawSteps, hcanonicalRunIn'⟩
      rcases
          TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
            hcanonicalRunIn' htargetRawTape with
        ⟨rawFinal, hrawRunIn, hrawState, _hrawTape⟩
      have hrawRun : TuringMachine.Computes machine
          (countValidateConfig (fuelZeroFlag fuel)
            (countValidatorRawScanTape (baseLeftRev.map some) 0
              (first :: rest))) rawFinal :=
        TuringMachine.computesIn_to_computes hrawRunIn
      have hrawSuccess : SuccessfulTerminal rawFinal := by
        simpa [SuccessfulTerminal, hrawState] using hcanonicalSuccess
      rcases
          count_validate_success_only_encodeNatAppend
            (fuelZeroFlag fuel) (baseLeftRev.map some) 0 (first :: rest)
            hrawRun hrawSuccess with
        ⟨count, rowTokens, hcountShape⟩
      have hcountRun : TuringMachine.Computes machine
          (countValidateConfig (fuelZeroFlag fuel)
            (countValidatorSourceTape (baseLeftRev.map some)
              count rowTokens)) rawFinal := by
        simpa [hcountShape, countValidatorSourceTape,
          countValidatorRawScanTape] using hrawRun
      have hvalidatorPrefix :=
        TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
          (count_validator_run_exact (fuelZeroFlag fuel)
            (baseLeftRev.map some) count rowTokens)
      have htableOuter :=
        computes_suffix_of_computesIn_of_successful
          hvalidatorPrefix hcountRun hrawSuccess
      let savedSource : TuringMachine.Configuration MachineCodeSymbol
          FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control :=
        { state := FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine.start
          tape := countValidatorSourceTape (baseLeftRev.map some)
            count rowTokens }
      have htableOuter' : TuringMachine.Computes machine
          (tableConfig (fuelZeroFlag fuel) savedSource) rawFinal := by
        simpa [savedSource, tableStartConfig, tableConfig,
          TuringMachine.PhaseEmbedding.liftConfig] using htableOuter
      rcases table_computes_project (fuelZeroFlag fuel) htableOuter' with
        ⟨savedFinal, hsavedRun, hrawFinal⟩
      have hsavedTerminal :
          savedFinal.state =
              FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control.parser
                TransitionListParserState.halt ∨
            exists saved : Option MachineCodeSymbol,
              savedFinal.state =
                FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control.ready saved := by
        rcases hrawSuccess with
          ⟨terminalFuel, hparser | ⟨saved, hready⟩⟩
        · left
          rw [hrawFinal] at hparser
          have hpair :
              fuelZeroFlag fuel = terminalFuel ∧
                savedFinal.state =
                  FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control.parser
                    TransitionListParserState.halt := by
            simpa [tableConfig,
              TuringMachine.PhaseEmbedding.liftConfig] using hparser
          exact hpair.2
        · right
          refine ⟨saved, ?_⟩
          rw [hrawFinal] at hready
          have hpair :
              fuelZeroFlag fuel = terminalFuel ∧
                savedFinal.state =
                  FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control.ready saved := by
            simpa [tableConfig,
              TuringMachine.PhaseEmbedding.liftConfig] using hready
          exact hpair.2
      have hparserRun :=
        FiniteRecognizer.Interpreter.SavedCellTransitionParser.computes_project hsavedRun
      have hparserHalted : TuringMachine.Halted transitionListParserMachine
          (FiniteRecognizer.Interpreter.SavedCellTransitionParser.projectConfig savedFinal) := by
        rcases hsavedTerminal with hparser | ⟨saved, hready⟩
        · change
            FiniteRecognizer.Interpreter.SavedCellTransitionParser.projectState
                savedFinal.state =
              transitionListParserMachine.halt
          rw [hparser]
          rfl
        · change
            FiniteRecognizer.Interpreter.SavedCellTransitionParser.projectState
                savedFinal.state =
              transitionListParserMachine.halt
          rw [hready]
          rfl
      have hcontextualHalts : TuringMachine.HaltsFrom
          transitionListParserMachine
          { state :=
              TransitionListParserState.findCount
                TransitionListParserMarker.initial
            tape := countValidatorSourceTape (baseLeftRev.map some)
              count rowTokens } := by
        refine
          ⟨FiniteRecognizer.Interpreter.SavedCellTransitionParser.projectConfig savedFinal,
            ?_, hparserHalted⟩
        simpa [savedSource,
          FiniteRecognizer.Interpreter.SavedCellTransitionParser.projectConfig,
          FiniteRecognizer.Interpreter.SavedCellTransitionParser.projectState,
          FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine,
          transitionListParserMachine,
          TuringMachine.PhaseEmbedding.liftConfig] using hparserRun
      rcases hcontextualHalts with
        ⟨contextualFinal, hcontextualRun, hcontextualHalted⟩
      have hcontextualSource :
          { state :=
              TransitionListParserState.findCount
                TransitionListParserMarker.initial
            tape := countValidatorSourceTape (baseLeftRev.map some)
              count rowTokens } =
            TransitionParserContextTransport.appendLeftContextConfig
              baseLeftRev
              (FiniteRecognizer.Interpreter.ParserAssembly.paddedRawTransitionParserSource
                count rowTokens) := by
        simpa [countValidatorSourceTape] using
          FiniteRecognizer.Interpreter.ParserAssembly.contextualRawTransitionParserSource_eq_append
            baseLeftRev count rowTokens
      rcases
          TransitionParserContextTransport.computes_remove_left_context_of_eq
            baseLeftRev hcontextualSource
            (FiniteRecognizer.Interpreter.ParserAssembly.paddedRawTransitionParserSource_has_barrier
              count rowTokens)
            hcontextualRun with
        ⟨cleanFinal, hcleanRun, hcleanFinalEq, _hcleanBarrier⟩
      have hcleanHalted : TuringMachine.Halted transitionListParserMachine
          cleanFinal := by
        rw [hcleanFinalEq] at hcontextualHalted
        simpa [TuringMachine.Halted,
          TransitionParserContextTransport.appendLeftContextConfig]
          using hcontextualHalted
      refine ⟨fuel, stateCount, start, halt, count, encoded, rowTokens,
        htokens, ?_, ?_⟩
      · rw [hheaderShape, htail, hcountShape]
      · change TuringMachine.HaltsFrom transitionListParserMachine
          (FiniteRecognizer.Interpreter.ParserAssembly.paddedRawTransitionParserSource
            count rowTokens)
        exact ⟨cleanFinal, hcleanRun, hcleanHalted⟩

/-- The concrete evidence package consumed by total parser inversion follows
from any honest successful endpoint of the parser-prefix machine. -/
theorem successfulTerminal_outerParserPhaseEvidence
    {tokens : Word MachineCodeSymbol}
    {final : TuringMachine.Configuration MachineCodeSymbol Control}
    (hrun : TuringMachine.Computes machine (sourceConfig tokens) final)
    (hsuccess : SuccessfulTerminal final) :
    Nonempty (OuterParserPhaseEvidence tokens) := by
  rcases successfulTerminal_recovers_parser_fields hrun hsuccess with
    ⟨fuel, stateCount, start, halt, count, encoded, rowTokens,
      htokens, hencoded, htable⟩
  apply Nonempty.intro
  refine
    { fuelSteps := fuel + 1
      fuel_halts := ?_
      header_halts := ?_
      table_halts := ?_ }
  · let fuelFinal : TuringMachine.Configuration MachineCodeSymbol
        ProductInput.PairFuelParser.Control :=
      ProductInput.PairFuelParser.config .inner
        (MachineDescription.encodeNat fuel).reverse encoded
    refine ⟨fuelFinal, ?_, rfl⟩
    apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
    simpa [htokens, fuelFinal] using
      outerFuelRetargetMachine_run_exact fuel
        ([] : Word MachineCodeSymbol) encoded
  · intro otherFuel otherEncoded htokens'
    have houterEq :
        MachineDescription.encodeNatAppend fuel encoded =
          MachineDescription.encodeNatAppend otherFuel otherEncoded :=
      htokens.symm.trans htokens'
    rcases encodeNatAppend_inj houterEq with
      ⟨hfuel, hrest⟩
    cases hfuel
    cases hrest
    rcases
        header_four_fields_haltsFromIn
          (MachineDescription.encodeNat fuel).reverse
          stateCount start halt count rowTokens with
      ⟨headerSteps, hheader⟩
    exact ⟨headerSteps, by simpa [hencoded] using hheader⟩
  · intro otherFuel otherStateCount otherStart otherHalt otherCount
      otherEncoded otherRowTokens htokensOther hencodedOther
    have houterEq :
        MachineDescription.encodeNatAppend fuel encoded =
          MachineDescription.encodeNatAppend otherFuel otherEncoded :=
      htokens.symm.trans htokensOther
    rcases encodeNatAppend_inj houterEq with
      ⟨hfuel, hrest⟩
    cases hfuel
    cases hrest
    have hfields :
        MachineDescription.encodeNatAppend stateCount
            (MachineDescription.encodeNatAppend start
              (MachineDescription.encodeNatAppend halt
                (MachineDescription.encodeNatAppend count rowTokens))) =
          MachineDescription.encodeNatAppend otherStateCount
            (MachineDescription.encodeNatAppend otherStart
              (MachineDescription.encodeNatAppend otherHalt
                (MachineDescription.encodeNatAppend otherCount
                  otherRowTokens))) := by
      exact (List.cons.inj (hencoded.symm.trans hencodedOther)).2
    rcases encodeNatAppend_inj hfields with
      ⟨hstateCount, hafterState⟩
    cases hstateCount
    rcases encodeNatAppend_inj hafterState with
      ⟨hstart, hafterStart⟩
    cases hstart
    rcases encodeNatAppend_inj hafterStart with
      ⟨hhalt, hafterHalt⟩
    cases hhalt
    rcases encodeNatAppend_inj hafterHalt with
      ⟨hcount, hrows⟩
    cases hcount
    cases hrows
    exact htable

theorem successfulTerminal_outerParserPhaseEvidence_of_computesIn
    {tokens : Word MachineCodeSymbol}
    {steps : Nat}
    {final : TuringMachine.Configuration MachineCodeSymbol Control}
    (hrun : TuringMachine.ComputesIn machine steps
      (sourceConfig tokens) final)
    (hsuccess : SuccessfulTerminal final) :
    Nonempty (OuterParserPhaseEvidence tokens) :=
  successfulTerminal_outerParserPhaseEvidence
    (TuringMachine.computesIn_to_computes hrun) hsuccess

end FiniteRecognizer.Interpreter.ParserPrefixPhaseSum
end Computability
end FoC
