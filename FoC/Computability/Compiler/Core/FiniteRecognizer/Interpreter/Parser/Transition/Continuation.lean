import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Parser.Transition.Basic

namespace FoC
namespace Computability

open Languages

namespace Section53TransitionParserHandoff

/-!
## Exact continuation contracts

The first contract is the exact computation already proved privately in
{module}`FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.TransitionListParser.Runs`.
Making that theorem public closes the two-row case without duplicating its
execution proof.  The boundary form is the strengthened invariant needed to
iterate over three or more rows while preserving the parser's visited blank.
-/

def TransitionListParserExactContinuationStep : Prop :=
  forall
    (blanks : Nat)
    (pre : Word MachineCodeSymbol),
    transitionListParserNoHeader pre ->
    forall
      (t u : TransitionDescription)
      (more : List TransitionDescription)
      (suffix : Word MachineCodeSymbol),
      TuringMachine.Computes transitionListParserMachine
        { state := TransitionListParserState.markPosition
          tape :=
            transitionListParserOptionTape
              ((List.append
                (List.append
                  (List.replicate blanks MachineCodeSymbol.blank)
                  (MachineDescription.encodeNat (u :: more).length))
                (List.append pre
                  (MachineDescription.encodeTransition t))).reverse.map
                some)
              ((MachineDescription.encodeTransitionsAppend
                (u :: more) suffix).map some) }
        { state := TransitionListParserState.markPosition
          tape :=
            transitionListParserOptionTape
              (List.append
                ((List.append
                  (List.append
                    (List.replicate (blanks + 1)
                      MachineCodeSymbol.blank)
                    (MachineDescription.encodeNat more.length))
                  (List.append
                    (List.append pre
                      (MachineDescription.encodeTransition t))
                    (MachineDescription.encodeTransition u))).reverse.map
                  some)
                [none])
              ((MachineDescription.encodeTransitionsAppend more suffix).map
                some) }

def TransitionListParserExactBoundaryContinuationStep : Prop :=
  forall
    (blanks : Nat)
    (pre : Word MachineCodeSymbol),
    transitionListParserNoHeader pre ->
    forall
      (t u : TransitionDescription)
      (more : List TransitionDescription)
      (suffix : Word MachineCodeSymbol),
      TuringMachine.Computes transitionListParserMachine
        { state := TransitionListParserState.markPosition
          tape :=
            transitionListParserOptionTape
              (List.append
                ((List.append
                  (List.append
                    (List.replicate blanks MachineCodeSymbol.blank)
                    (MachineDescription.encodeNat (u :: more).length))
                  (List.append pre
                    (MachineDescription.encodeTransition t))).reverse.map
                  some)
                [none])
              ((MachineDescription.encodeTransitionsAppend
                (u :: more) suffix).map some) }
        { state := TransitionListParserState.markPosition
          tape :=
            transitionListParserOptionTape
              (List.append
                ((List.append
                  (List.append
                    (List.replicate (blanks + 1)
                      MachineCodeSymbol.blank)
                    (MachineDescription.encodeNat more.length))
                  (List.append
                    (List.append pre
                      (MachineDescription.encodeTransition t))
                    (MachineDescription.encodeTransition u))).reverse.map
                  some)
                [none])
              ((MachineDescription.encodeTransitionsAppend more suffix).map
                some) }

def ParserRunsToEquiv
    (source canonical :
      TuringMachine.Configuration MachineCodeSymbol
        TransitionListParserState) : Prop :=
  exists endpoint :
      TuringMachine.Configuration MachineCodeSymbol
        TransitionListParserState,
    TuringMachine.Computes transitionListParserMachine source endpoint ∧
    endpoint.state = canonical.state ∧
    Tape.Equiv canonical.tape endpoint.tape

namespace ParserRunsToEquiv

def exact
    {source target :
      TuringMachine.Configuration MachineCodeSymbol
        TransitionListParserState}
    (hrun :
      TuringMachine.Computes transitionListParserMachine source target) :
    ParserRunsToEquiv source target :=
  ⟨target, hrun, rfl, Tape.Equiv.refl _⟩

def sourceEquiv
    {source canonical :
      TuringMachine.Configuration MachineCodeSymbol
        TransitionListParserState}
    (hstate : source.state = canonical.state)
    (htape : Tape.Equiv canonical.tape source.tape) :
    ParserRunsToEquiv source canonical :=
  ⟨source, TuringMachine.Computes.refl _, hstate, htape⟩

theorem retarget
    {source oldCanonical newCanonical :
      TuringMachine.Configuration MachineCodeSymbol
        TransitionListParserState}
    (run : ParserRunsToEquiv source oldCanonical)
    (hstate : oldCanonical.state = newCanonical.state)
    (htape : Tape.Equiv newCanonical.tape oldCanonical.tape) :
    ParserRunsToEquiv source newCanonical := by
  rcases run with
    ⟨endpoint, endpointRun, endpointStateEq,
      endpointTapeEquiv⟩
  exact
    ⟨endpoint, endpointRun, endpointStateEq.trans hstate,
      Tape.Equiv.trans htape endpointTapeEquiv⟩

theorem trans
    {source middle target :
      TuringMachine.Configuration MachineCodeSymbol
        TransitionListParserState}
    (first : ParserRunsToEquiv source middle)
    (second : ParserRunsToEquiv middle target) :
    ParserRunsToEquiv source target := by
  rcases first with
    ⟨⟨firstState, firstTape⟩, firstRun, firstStateEq,
      firstTapeEquiv⟩
  rcases second with
    ⟨secondEndpoint, secondRun, secondStateEq,
      secondTapeEquiv⟩
  change firstState = middle.state at firstStateEq
  subst firstState
  rcases TuringMachine.computes_to_computesIn secondRun with
    ⟨steps, secondRunIn⟩
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      secondRunIn firstTapeEquiv with
    ⟨endpoint, endpointRunIn, endpointStateEq, endpointTapeEquiv⟩
  exact
    ⟨endpoint,
      TuringMachine.computes_trans firstRun
        (TuringMachine.computesIn_to_computes endpointRunIn),
      endpointStateEq.trans secondStateEq,
      Tape.Equiv.trans secondTapeEquiv endpointTapeEquiv⟩

end ParserRunsToEquiv

/-- Canonical mark-position configuration with its left window trimmed. -/
def canonicalMarkConfig
    (blanks : Nat)
    (pre : Word MachineCodeSymbol)
    (t : TransitionDescription)
    (rest : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      TransitionListParserState :=
  { state := TransitionListParserState.markPosition
    tape :=
      transitionListParserOptionTape
        ((List.append
          (List.append
            (List.replicate blanks MachineCodeSymbol.blank)
            (MachineDescription.encodeNat rest.length))
          (List.append pre
            (MachineDescription.encodeTransition t))).reverse.map some)
        ((MachineDescription.encodeTransitionsAppend rest suffix).map
          some) }

def canonicalBoundaryMarkConfig
    (blanks : Nat)
    (pre : Word MachineCodeSymbol)
    (t : TransitionDescription)
    (rest : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      TransitionListParserState :=
  { state := TransitionListParserState.markPosition
    tape :=
      transitionListParserOptionTape
        (List.append
          ((List.append
            (List.append
              (List.replicate blanks MachineCodeSymbol.blank)
              (MachineDescription.encodeNat rest.length))
            (List.append pre
              (MachineDescription.encodeTransition t))).reverse.map some)
          [none])
        ((MachineDescription.encodeTransitionsAppend rest suffix).map
          some) }

theorem canonicalMarkConfig_tape_equiv_boundary
    (blanks : Nat)
    (pre : Word MachineCodeSymbol)
    (t : TransitionDescription)
    (rest : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    Tape.Equiv
      (canonicalMarkConfig blanks pre t rest suffix).tape
      (canonicalBoundaryMarkConfig blanks pre t rest suffix).tape := by
  exact transitionListParserOptionTape_append_none_equiv _ _

def canonicalParsedSymbols
    (pre : Word MachineCodeSymbol)
    (t : TransitionDescription)
    (rest : List TransitionDescription) :
    Word MachineCodeSymbol :=
  List.append pre
    (MachineDescription.encodeTransitionAppend t
      (MachineDescription.encodeTransitions rest))

/-- Iterated parser schedule in tape-equivalence currency.  The exact
continuation theorem may trim the left window before every row; transport
replays the next phase from the physically padded endpoint. -/
theorem transitionListParserMachine_runs_rows_to_equiv_of_step
    (hexact : TransitionListParserExactContinuationStep)
    (blanks : Nat)
    (pre : Word MachineCodeSymbol)
    (hpre : transitionListParserNoHeader pre)
    (t : TransitionDescription)
    (rest : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    ParserRunsToEquiv
      (canonicalMarkConfig blanks pre t rest suffix)
      (parsedTransitionHaltConfig (blanks + rest.length)
        (canonicalParsedSymbols pre t rest) suffix) := by
  induction rest generalizing blanks pre t with
  | nil =>
      have hboundary :
          ParserRunsToEquiv
            (canonicalMarkConfig blanks pre t [] suffix)
            (canonicalBoundaryMarkConfig blanks pre t [] suffix) :=
        ParserRunsToEquiv.sourceEquiv rfl
          (Tape.Equiv.symm
            (canonicalMarkConfig_tape_equiv_boundary
              blanks pre t [] suffix))
      have hfinal :=
        transitionListParserMachine_computes_final_mark_exact
          blanks (canonicalParsedSymbols pre t []) suffix
      have hfinal' :
          TuringMachine.Computes transitionListParserMachine
            (canonicalBoundaryMarkConfig blanks pre t [] suffix)
            (parsedTransitionHaltConfig blanks
              (canonicalParsedSymbols pre t []) suffix) := by
        simpa [canonicalBoundaryMarkConfig,
          canonicalParsedSymbols, finalTransitionMarkConfig,
          MachineDescription.encodeTransitions,
          MachineDescription.encodeTransitionsAppend,
          MachineDescription.encodeTransition,
          MachineDescription.encodeTransitionAppend,
          MachineDescription.encodeNatAppend,
          MachineDescription.encodeCellAppend,
          MachineDescription.encodeDirectionAppend,
          MachineDescription.encodeNat,
          List.map_append, List.reverse_append,
          List.append_assoc]
          using hfinal
      simpa using
        (ParserRunsToEquiv.trans hboundary
          (ParserRunsToEquiv.exact hfinal'))
  | cons u more ih =>
      have hstep := hexact blanks pre hpre t u more suffix
      have hstep' :
          TuringMachine.Computes transitionListParserMachine
            (canonicalMarkConfig blanks pre t (u :: more) suffix)
            (canonicalBoundaryMarkConfig (blanks + 1)
              (List.append pre
                (MachineDescription.encodeTransition t))
              u more suffix) := by
        simpa [canonicalMarkConfig, canonicalBoundaryMarkConfig,
          List.append_assoc]
          using hstep
      have hnext :
          ParserRunsToEquiv
            (canonicalMarkConfig blanks pre t (u :: more) suffix)
            (canonicalMarkConfig (blanks + 1)
              (List.append pre
                (MachineDescription.encodeTransition t))
              u more suffix) :=
        ParserRunsToEquiv.retarget
          (ParserRunsToEquiv.exact hstep') rfl
          (canonicalMarkConfig_tape_equiv_boundary
            (blanks + 1)
            (List.append pre
              (MachineDescription.encodeTransition t))
            u more suffix)
      have hpre' :
          transitionListParserNoHeader
            (List.append pre
              (MachineDescription.encodeTransition t)) :=
        transitionListParserNoHeader_append hpre
          (transitionListParser_encodeTransition_noHeader t)
      have hrest :=
        ih (blanks + 1)
          (List.append pre (MachineDescription.encodeTransition t))
          hpre' u
      have hsymbols :
          canonicalParsedSymbols
              (List.append pre
                (MachineDescription.encodeTransition t))
              u more =
            canonicalParsedSymbols pre t (u :: more) := by
        simp [canonicalParsedSymbols,
          MachineDescription.encodeTransitions,
          MachineDescription.encodeTransitionsAppend,
          MachineDescription.encodeTransition,
          MachineDescription.encodeTransitionAppend,
          MachineDescription.encodeNatAppend,
          MachineDescription.encodeCellAppend,
          MachineDescription.encodeDirectionAppend,
          List.append_assoc]
      have hcount :
          blanks + 1 + more.length =
            blanks + (u :: more).length := by
        simp [Nat.add_comm, Nat.add_left_comm]
      rw [hsymbols, hcount] at hrest
      exact ParserRunsToEquiv.trans hnext hrest

theorem transitionListParserMachine_computes_boundary_rows_exact_of_step
    (hexactBoundary : TransitionListParserExactBoundaryContinuationStep)
    (blanks : Nat)
    (pre : Word MachineCodeSymbol)
    (hpre : transitionListParserNoHeader pre)
    (t : TransitionDescription)
    (rest : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes transitionListParserMachine
      (canonicalBoundaryMarkConfig blanks pre t rest suffix)
      (parsedTransitionHaltConfig (blanks + rest.length)
        (canonicalParsedSymbols pre t rest) suffix) := by
  induction rest generalizing blanks pre t with
  | nil =>
      have hfinal :=
        transitionListParserMachine_computes_final_mark_exact
          blanks (canonicalParsedSymbols pre t []) suffix
      simpa [canonicalBoundaryMarkConfig,
        canonicalParsedSymbols, finalTransitionMarkConfig,
        MachineDescription.encodeTransitions,
        MachineDescription.encodeTransitionsAppend,
        MachineDescription.encodeTransition,
        MachineDescription.encodeTransitionAppend,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeCellAppend,
        MachineDescription.encodeDirectionAppend,
        MachineDescription.encodeNat,
        List.map_append, List.reverse_append,
        List.append_assoc]
        using hfinal
  | cons u more ih =>
      have hstep :=
        hexactBoundary blanks pre hpre t u more suffix
      have hpre' :
          transitionListParserNoHeader
            (List.append pre
              (MachineDescription.encodeTransition t)) :=
        transitionListParserNoHeader_append hpre
          (transitionListParser_encodeTransition_noHeader t)
      have hrest :=
        ih (blanks + 1)
          (List.append pre (MachineDescription.encodeTransition t))
          hpre' u
      have hstep' :
          TuringMachine.Computes transitionListParserMachine
            (canonicalBoundaryMarkConfig blanks pre t (u :: more)
              suffix)
            (canonicalBoundaryMarkConfig (blanks + 1)
              (List.append pre
                (MachineDescription.encodeTransition t))
              u more suffix) := by
        simpa [canonicalBoundaryMarkConfig, List.append_assoc]
          using hstep
      have hsymbols :
          canonicalParsedSymbols
              (List.append pre
                (MachineDescription.encodeTransition t))
              u more =
            canonicalParsedSymbols pre t (u :: more) := by
        simp [canonicalParsedSymbols,
          MachineDescription.encodeTransitions,
          MachineDescription.encodeTransitionsAppend,
          MachineDescription.encodeTransition,
          MachineDescription.encodeTransitionAppend,
          MachineDescription.encodeNatAppend,
          MachineDescription.encodeCellAppend,
          MachineDescription.encodeDirectionAppend,
          List.append_assoc]
      have hcount :
          blanks + 1 + more.length =
            blanks + (u :: more).length := by
        simp [Nat.add_comm, Nat.add_left_comm]
      rw [hsymbols, hcount] at hrest
      exact TuringMachine.computes_trans hstep' hrest

def canonicalTransitionParserHaltConfig
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      TransitionListParserState :=
  match transitions with
  | [] => zeroTransitionHaltConfig suffix
  | _ =>
      parsedTransitionHaltConfig transitions.length
        (MachineDescription.encodeTransitions transitions) suffix

theorem transitionListParserMachine_computes_encodeTransitions_exact_of_steps
    (hexact : TransitionListParserExactContinuationStep)
    (hexactBoundary : TransitionListParserExactBoundaryContinuationStep)
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes transitionListParserMachine
      (TuringMachine.initial transitionListParserMachine
        (MachineDescription.encodeNatAppend transitions.length
          (MachineDescription.encodeTransitionsAppend transitions suffix)))
      (canonicalTransitionParserHaltConfig transitions suffix) := by
  cases transitions with
  | nil =>
      simpa [canonicalTransitionParserHaltConfig,
        MachineDescription.encodeTransitionsAppend]
        using
          transitionListParserMachine_computes_count_zero_exact suffix
  | cons t rest =>
      cases rest with
      | nil =>
          simpa [canonicalTransitionParserHaltConfig,
            parsedTransitionHaltConfig, parsedTableLeftRev,
            oneTransitionHaltConfig,
            MachineDescription.encodeTransitions,
            MachineDescription.encodeTransitionsAppend,
            MachineDescription.encodeTransition,
            List.append_assoc]
            using
              transitionListParserMachine_computes_oneTransition_exact
                t suffix
      | cons u more =>
          have hfirst :=
            transitionListParserMachine_computes_nextTransition_to_markPosition
              (u :: more).length t
              (MachineDescription.encodeTransitionsAppend
                (u :: more) suffix)
          have hcontinue :=
            hexact 1 []
              (by
                intro symbol hmem
                simp at hmem)
              t u more suffix
          have hpre :
              transitionListParserNoHeader
                (MachineDescription.encodeTransition t) :=
            transitionListParser_encodeTransition_noHeader t
          have hrest :=
            transitionListParserMachine_computes_boundary_rows_exact_of_step
              hexactBoundary 2
              (MachineDescription.encodeTransition t) hpre
              u more suffix
          have hfirst' :
              TuringMachine.Computes transitionListParserMachine
                (TuringMachine.initial transitionListParserMachine
                  (MachineDescription.encodeNatAppend
                    (t :: u :: more).length
                    (MachineDescription.encodeTransitionsAppend
                      (t :: u :: more) suffix)))
                { state := TransitionListParserState.markPosition
                  tape :=
                    transitionListParserOptionTape
                      ((List.append
                        (List.append
                          (List.replicate 1
                            MachineCodeSymbol.blank)
                          (MachineDescription.encodeNat
                            (u :: more).length))
                        (MachineDescription.encodeTransition t)).reverse.map
                        some)
                      ((MachineDescription.encodeTransitionsAppend
                        (u :: more) suffix).map some) } := by
            simpa [TuringMachine.initial, transitionListParserMachine,
              transitionListParserOptionTape_nil_eq_input,
              MachineDescription.encodeTransitionsAppend,
              List.append_assoc]
              using hfirst
          have hcontinue' :
              TuringMachine.Computes transitionListParserMachine
                { state := TransitionListParserState.markPosition
                  tape :=
                    transitionListParserOptionTape
                      ((List.append
                        (List.append
                          (List.replicate 1
                            MachineCodeSymbol.blank)
                          (MachineDescription.encodeNat
                            (u :: more).length))
                        (MachineDescription.encodeTransition t)).reverse.map
                        some)
                      ((MachineDescription.encodeTransitionsAppend
                        (u :: more) suffix).map some) }
                (canonicalBoundaryMarkConfig 2
                  (MachineDescription.encodeTransition t)
                  u more suffix) := by
            simpa [canonicalBoundaryMarkConfig, List.append_assoc]
              using hcontinue
          have hcount :
              2 + more.length = (t :: u :: more).length := by
            simp
            lia
          have hsymbols :
              canonicalParsedSymbols
                  (MachineDescription.encodeTransition t) u more =
                MachineDescription.encodeTransitions (t :: u :: more) := by
            simp [canonicalParsedSymbols,
              MachineDescription.encodeTransitions,
              MachineDescription.encodeTransitionsAppend,
              MachineDescription.encodeTransition,
              MachineDescription.encodeTransitionAppend,
              MachineDescription.encodeNatAppend,
              MachineDescription.encodeCellAppend,
              MachineDescription.encodeDirectionAppend,
              List.append_assoc]
          rw [hcount, hsymbols] at hrest
          exact
            TuringMachine.computes_trans hfirst'
              (TuringMachine.computes_trans hcontinue'
                (by
                  simpa [canonicalTransitionParserHaltConfig]
                    using hrest))

/-- Arbitrary canonical transition tables need only the existing unpadded
continuation theorem.  Each later phase is replayed from the equivalent padded
endpoint left by the preceding phase. -/
theorem transitionListParserMachine_runs_encodeTransitions_to_equiv_of_step
    (hexact : TransitionListParserExactContinuationStep)
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    ParserRunsToEquiv
      (TuringMachine.initial transitionListParserMachine
        (MachineDescription.encodeNatAppend transitions.length
          (MachineDescription.encodeTransitionsAppend transitions suffix)))
      (canonicalTransitionParserHaltConfig transitions suffix) := by
  cases transitions with
  | nil =>
      exact ParserRunsToEquiv.exact
        (by
          simpa [canonicalTransitionParserHaltConfig,
            MachineDescription.encodeTransitionsAppend]
            using
              transitionListParserMachine_computes_count_zero_exact suffix)
  | cons t rest =>
      have hfirst :=
        transitionListParserMachine_computes_nextTransition_to_markPosition
          rest.length t
          (MachineDescription.encodeTransitionsAppend rest suffix)
      have hfirst' :
          TuringMachine.Computes transitionListParserMachine
            (TuringMachine.initial transitionListParserMachine
              (MachineDescription.encodeNatAppend
                (t :: rest).length
                (MachineDescription.encodeTransitionsAppend
                  (t :: rest) suffix)))
            (canonicalMarkConfig 1 [] t rest suffix) := by
        simpa [canonicalMarkConfig, TuringMachine.initial,
          transitionListParserMachine,
          transitionListParserOptionTape_nil_eq_input,
          MachineDescription.encodeTransitionsAppend,
          List.append_assoc]
          using hfirst
      have hnoHeader : transitionListParserNoHeader ([] :
          Word MachineCodeSymbol) := by
        intro symbol hmem
        simp at hmem
      have hrest :=
        transitionListParserMachine_runs_rows_to_equiv_of_step
          hexact 1 [] hnoHeader t rest suffix
      have hcount :
          1 + rest.length = (t :: rest).length := by
        simp
        lia
      have hsymbols :
          canonicalParsedSymbols [] t rest =
            MachineDescription.encodeTransitions (t :: rest) := by
        simp [canonicalParsedSymbols,
          MachineDescription.encodeTransitions,
          MachineDescription.encodeTransitionsAppend,
          MachineDescription.encodeTransitionAppend,
          MachineDescription.encodeNatAppend,
          MachineDescription.encodeCellAppend,
          MachineDescription.encodeDirectionAppend]
      rw [hcount, hsymbols] at hrest
      simpa [canonicalTransitionParserHaltConfig] using
        (ParserRunsToEquiv.trans
          (ParserRunsToEquiv.exact hfirst') hrest)

theorem transitionListParserMachine_computes_twoTransitions_exact_of_step
    (hexact : TransitionListParserExactContinuationStep)
    (t u : TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes transitionListParserMachine
      (TuringMachine.initial transitionListParserMachine
        (MachineDescription.encodeNatAppend 2
          (MachineDescription.encodeTransitionsAppend [t, u] suffix)))
      (parsedTransitionHaltConfig 2
        (MachineDescription.encodeTransitions [t, u]) suffix) := by
  have hfirst :=
    transitionListParserMachine_computes_nextTransition_to_markPosition
      1 t (MachineDescription.encodeTransitionAppend u suffix)
  have hcontinue :=
    hexact 1 []
      (by
        intro symbol hmem
        simp at hmem)
      t u [] suffix
  have hfinal :=
    transitionListParserMachine_computes_final_mark_exact
      2 (MachineDescription.encodeTransitions [t, u]) suffix
  exact
    TuringMachine.computes_trans
      (by
        simpa [TuringMachine.initial, transitionListParserMachine,
          transitionListParserOptionTape_nil_eq_input,
          MachineDescription.encodeTransitionsAppend,
          List.append_assoc]
          using hfirst)
      (TuringMachine.computes_trans
        (by
          simpa [finalTransitionMarkConfig,
            MachineDescription.encodeTransitions,
            MachineDescription.encodeTransitionsAppend,
            MachineDescription.encodeTransition,
            MachineDescription.encodeTransitionAppend,
            MachineDescription.encodeNatAppend,
            MachineDescription.encodeCellAppend,
            MachineDescription.encodeDirectionAppend,
            MachineDescription.encodeNat, List.map_append,
            List.map_replicate, List.reverse_append,
            List.append_assoc]
            using hcontinue)
        hfinal)

end Section53TransitionParserHandoff

end Computability
end FoC
