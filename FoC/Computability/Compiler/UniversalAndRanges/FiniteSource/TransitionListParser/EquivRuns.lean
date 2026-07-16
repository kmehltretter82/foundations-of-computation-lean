import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.TransitionListParser.ExactEndpoints
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.TapeEquivTransport

set_option doc.verso true

/-!
# Transition-list parser runs up to tape equivalence

Canonical parser phases compose across harmless differences in their trailing
blank windows.  This yields one schedule for every encoded transition table.
-/

namespace FoC
namespace Computability

open Languages

/-- A parser run whose actual endpoint has the canonical control state and an
equivalent physical tape. -/
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

/-- The same canonical mark-position configuration with its visited blank
retained in the left window. -/
def canonicalPaddedMarkConfig
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

theorem canonicalMarkConfig_tape_equiv_padded
    (blanks : Nat)
    (pre : Word MachineCodeSymbol)
    (t : TransitionDescription)
    (rest : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    Tape.Equiv
      (canonicalMarkConfig blanks pre t rest suffix).tape
      (canonicalPaddedMarkConfig blanks pre t rest suffix).tape := by
  exact transitionListParserOptionTape_append_none_equiv _ _

def canonicalParsedSymbols
    (pre : Word MachineCodeSymbol)
    (t : TransitionDescription)
    (rest : List TransitionDescription) :
    Word MachineCodeSymbol :=
  List.append pre
    (MachineDescription.encodeTransitionAppend t
      (MachineDescription.encodeTransitions rest))

/-- Iterate the exact canonical-context phase while transporting each later
phase across the preceding endpoint's visited blank. -/
theorem transitionListParserMachine_runs_rows_to_equiv
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
            (canonicalPaddedMarkConfig blanks pre t [] suffix) :=
        ParserRunsToEquiv.sourceEquiv rfl
          (Tape.Equiv.symm
            (canonicalMarkConfig_tape_equiv_padded
              blanks pre t [] suffix))
      have hfinal :=
        transitionListParserMachine_computes_final_mark_exact
          blanks (canonicalParsedSymbols pre t []) suffix
      have hfinal' :
          TuringMachine.Computes transitionListParserMachine
            (canonicalPaddedMarkConfig blanks pre t [] suffix)
            (parsedTransitionHaltConfig blanks
              (canonicalParsedSymbols pre t []) suffix) := by
        simpa [canonicalPaddedMarkConfig,
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
      have hstep :=
        transitionListParserMachine_computes_markPosition_canonicalContext_step
          blanks pre hpre t u more suffix
      have hstep' :
          TuringMachine.Computes transitionListParserMachine
            (canonicalMarkConfig blanks pre t (u :: more) suffix)
            (canonicalPaddedMarkConfig (blanks + 1)
              (List.append pre
                (MachineDescription.encodeTransition t))
              u more suffix) := by
        simpa [canonicalMarkConfig, canonicalPaddedMarkConfig,
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
          (canonicalMarkConfig_tape_equiv_padded
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

/-- Canonical parser halt configuration for an arbitrary encoded transition
table, including the zero-row case. -/
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

/-- Parse every canonical transition table to a canonical endpoint up to tape
equivalence. -/
theorem transitionListParserMachine_runs_encodeTransitions_to_equiv
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
        transitionListParserMachine_runs_rows_to_equiv
          1 [] hnoHeader t rest suffix
      have hcount :
          1 + rest.length = (t :: rest).length := by
        simp [Nat.add_comm]
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

end Computability
end FoC
