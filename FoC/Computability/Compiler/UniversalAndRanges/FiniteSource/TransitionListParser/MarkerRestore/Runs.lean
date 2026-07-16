import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.TransitionListParser.EquivRuns
import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.TransitionListParser.MarkerRestore.Basic

set_option doc.verso true

/-!
# Marker-restorer runs after transition-list parsing

Exact restoration schedules and tape-equivalence transport connect an actual
parser endpoint to a restored canonical transition table.
-/

namespace FoC
namespace Computability

open Languages

/-- Exact suffix cells after restoration; an empty suffix retains one visited
blank. -/
def markerRestoreRestoredTail
    (suffix : Word MachineCodeSymbol) :
    List (Option MachineCodeSymbol) :=
  match suffix with
  | [] => [none]
  | _ => suffix.map some

def parsedMarkerRestoreSourceConfig
    (rowCount : Nat)
    (symbols suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol MarkerRestoreState :=
  { state :=
      MarkerRestoreState.seek
        (transitionListParserSavedHead suffix)
    tape := (parsedTransitionHaltConfig rowCount symbols suffix).tape }

def parsedMarkerRestoreTargetConfig
    (rowCount : Nat)
    (symbols suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol MarkerRestoreState :=
  { state := MarkerRestoreState.halt
    tape :=
      transitionListParserOptionTape
        (parsedTableLeftRev rowCount)
        (List.append (symbols.map some)
          (markerRestoreRestoredTail suffix)) }

/-- A marker-restorer run whose actual endpoint has the canonical control state
and an equivalent physical tape. -/
def MarkerRunsToEquiv
    (source canonical :
      TuringMachine.Configuration MachineCodeSymbol MarkerRestoreState) :
    Prop :=
  exists endpoint :
      TuringMachine.Configuration MachineCodeSymbol MarkerRestoreState,
    TuringMachine.Computes markerRestoreMachine source endpoint ∧
    endpoint.state = canonical.state ∧
    Tape.Equiv canonical.tape endpoint.tape

/-- Replay an exact marker-restorer run from any equivalent physical parser
endpoint. -/
theorem markerRestoreMachine_runs_to_equiv_of_source_equiv
    {source target :
      TuringMachine.Configuration MachineCodeSymbol MarkerRestoreState}
    {physicalTape : Tape MachineCodeSymbol}
    (hrun : TuringMachine.Computes markerRestoreMachine source target)
    (htape : Tape.Equiv source.tape physicalTape) :
    MarkerRunsToEquiv
      { state := source.state, tape := physicalTape } target := by
  rcases TuringMachine.computes_to_computesIn hrun with
    ⟨steps, hrunIn⟩
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      hrunIn htape with
    ⟨endpoint, endpointRunIn, endpointStateEq, endpointTapeEquiv⟩
  exact
    ⟨endpoint, TuringMachine.computesIn_to_computes endpointRunIn,
      endpointStateEq, endpointTapeEquiv⟩

theorem markerRestoreMachine_computes_marked_blanks_exact
    (saved : Option MachineCodeSymbol)
    (symbols : Word MachineCodeSymbol)
    (hsymbols : transitionListParserNoHeader symbols)
    (hsymbolsNonempty : symbols ≠ [])
    (extraBlanks : Nat)
    (markerTail : List (Option MachineCodeSymbol)) :
    TuringMachine.Computes markerRestoreMachine
      { state := MarkerRestoreState.seek saved
        tape :=
          transitionListParserOptionTape
            (parsedTableLeftRev (extraBlanks + 1))
            (List.append (symbols.map some)
              (some MachineCodeSymbol.header :: markerTail)) }
      { state := MarkerRestoreState.halt
        tape :=
          transitionListParserOptionTape
            (parsedTableLeftRev (extraBlanks + 1))
            (List.append (symbols.map some)
              (saved :: markerTail)) } := by
  have hreverseNonempty : symbols.reverse ≠ [] := by
    intro hreverseEmpty
    apply hsymbolsNonempty
    have h := congrArg List.reverse hreverseEmpty
    simpa using! h
  cases hreverse : symbols.reverse with
  | nil =>
      exact False.elim (hreverseNonempty hreverse)
  | cons current leftSymbols =>
      have hsymbolsShape :
          symbols = List.append leftSymbols.reverse [current] := by
        have h := congrArg List.reverse hreverse
        simpa using! h
      have hmappedShape :
          List.append (leftSymbols.map some).reverse [some current] =
            symbols.map some := by
        rw [hsymbolsShape]
        simp [List.map_append, List.map_reverse]
      have hrestShape :
          List.append (leftSymbols.map some).reverse
              (some current :: saved :: markerTail) =
            List.append (symbols.map some) (saved :: markerTail) := by
        rw [← hmappedShape]
        simp [List.append_assoc]
      have hseek :=
        markerRestoreMachine_computes_seek_prefix
          saved symbols hsymbols
          (parsedTableLeftRev (extraBlanks + 1)) markerTail
      have hrestore :=
        markerRestoreMachine_step_restore_marker saved
          (List.append (leftSymbols.map some)
            (parsedTableLeftRev (extraBlanks + 1)))
          markerTail (some current)
      let rewindSymbols : Word MachineCodeSymbol :=
        List.append leftSymbols
          (MachineCodeSymbol.done ::
            List.replicate (extraBlanks + 1)
              MachineCodeSymbol.blank)
      have hrewind :=
        markerRestoreMachine_computes_rewind_to_boundary
          rewindSymbols current (saved :: markerTail)
      have hrewindPhysical :
          TuringMachine.Computes markerRestoreMachine
            { state := MarkerRestoreState.rewind
              tape :=
                transitionListParserOptionTape
                  (List.append (leftSymbols.map some)
                    (parsedTableLeftRev (extraBlanks + 1)))
                  (some current :: saved :: markerTail) }
            { state := MarkerRestoreState.rewind
              tape :=
                transitionListParserOptionTape []
                  (none ::
                    List.append
                      (List.replicate (extraBlanks + 1)
                        (some MachineCodeSymbol.blank))
                      (some MachineCodeSymbol.done ::
                        List.append (leftSymbols.map some).reverse
                          (some current :: saved :: markerTail))) } := by
        simpa [rewindSymbols, parsedTableLeftRev, List.map_append,
          List.map_replicate, List.map_reverse, List.reverse_append,
          List.append_assoc]
          using hrewind
      rw [hrestShape] at hrewindPhysical
      have hboundary :=
        markerRestoreMachine_step_rewind_boundary
          (List.append
            (List.replicate (extraBlanks + 1)
              (some MachineCodeSymbol.blank))
            (some MachineCodeSymbol.done ::
              List.append (symbols.map some) (saved :: markerTail)))
      have hblank :=
        markerRestoreMachine_step_enter_blank [none]
          (List.append
            (List.replicate extraBlanks
              (some MachineCodeSymbol.blank))
            (some MachineCodeSymbol.done ::
              List.append (symbols.map some) (saved :: markerTail)))
      have hfinish :=
        markerRestoreMachine_computes_enterDone_blanks
          extraBlanks
          [some MachineCodeSymbol.blank, none]
          (List.append (symbols.map some) (saved :: markerTail))
      have hcounter :=
        congrArg (List.cons (some MachineCodeSymbol.done))
          (transitionListParser_blank_cons_replicate_append_none
            extraBlanks)
      have hcounterLeft :
          parsedTableLeftRev (extraBlanks + 1) =
            some MachineCodeSymbol.done ::
              List.append
                (List.replicate extraBlanks
                  (some MachineCodeSymbol.blank))
                [some MachineCodeSymbol.blank, none] := by
        simpa [parsedTableLeftRev, List.replicate_succ]
          using hcounter
      have hfinishNormalized :
          TuringMachine.Computes markerRestoreMachine
            { state := MarkerRestoreState.enterDone
              tape :=
                transitionListParserOptionTape
                  [some MachineCodeSymbol.blank, none]
                  (List.append
                    (List.replicate extraBlanks
                      (some MachineCodeSymbol.blank))
                    (some MachineCodeSymbol.done ::
                      List.append (symbols.map some)
                        (saved :: markerTail))) }
            { state := MarkerRestoreState.halt
              tape :=
                transitionListParserOptionTape
                  (parsedTableLeftRev (extraBlanks + 1))
                  (List.append (symbols.map some)
                    (saved :: markerTail)) } := by
        rw [hcounterLeft]
        exact hfinish
      exact
        TuringMachine.computes_trans
          (by
            simpa [hreverse, List.append_assoc]
              using hseek)
          (TuringMachine.Computes.step
            (by simpa using hrestore)
            (TuringMachine.computes_trans
              hrewindPhysical
              (TuringMachine.Computes.step
                (by simpa using hboundary)
                (TuringMachine.Computes.step
                  (by
                    simpa [List.replicate_succ]
                      using hblank)
                  hfinishNormalized))))

theorem markerRestoreMachine_computes_parsed_exact
    (extraBlanks : Nat)
    (symbols suffix : Word MachineCodeSymbol)
    (hsymbols : transitionListParserNoHeader symbols)
    (hsymbolsNonempty : symbols ≠ []) :
    TuringMachine.Computes markerRestoreMachine
      (parsedMarkerRestoreSourceConfig (extraBlanks + 1)
        symbols suffix)
      (parsedMarkerRestoreTargetConfig (extraBlanks + 1)
        symbols suffix) := by
  cases suffix with
  | nil =>
      simpa [parsedMarkerRestoreSourceConfig,
        parsedMarkerRestoreTargetConfig, parsedTransitionHaltConfig,
        transitionListParserSavedHead, transitionListParserMarkedTail,
        markerRestoreRestoredTail]
        using
          markerRestoreMachine_computes_marked_blanks_exact
            none symbols hsymbols hsymbolsNonempty extraBlanks []
  | cons first rest =>
      simpa [parsedMarkerRestoreSourceConfig,
        parsedMarkerRestoreTargetConfig, parsedTransitionHaltConfig,
        transitionListParserSavedHead, transitionListParserMarkedTail,
        markerRestoreRestoredTail]
        using
          markerRestoreMachine_computes_marked_blanks_exact
            (some first) symbols hsymbols hsymbolsNonempty
            extraBlanks (rest.map some)

/-- Start marker restoration from any physical parser endpoint equivalent to
the canonical parsed table. -/
theorem markerRestoreMachine_runs_parsed_to_equiv
    (extraBlanks : Nat)
    (symbols suffix : Word MachineCodeSymbol)
    (hsymbols : transitionListParserNoHeader symbols)
    (hsymbolsNonempty : symbols ≠ [])
    {physicalTape : Tape MachineCodeSymbol}
    (htape :
      Tape.Equiv
        (parsedTransitionHaltConfig (extraBlanks + 1)
          symbols suffix).tape
        physicalTape) :
    MarkerRunsToEquiv
      { state :=
          MarkerRestoreState.seek
            (transitionListParserSavedHead suffix)
        tape := physicalTape }
      (parsedMarkerRestoreTargetConfig (extraBlanks + 1)
        symbols suffix) := by
  have hcanonical :=
    markerRestoreMachine_computes_parsed_exact
      extraBlanks symbols suffix hsymbols hsymbolsNonempty
  simpa [parsedMarkerRestoreSourceConfig] using
    (markerRestoreMachine_runs_to_equiv_of_source_equiv
      hcanonical htape)

/-- Parse and restore every nonempty canonical transition table, starting the
restorer on the parser's actual physical endpoint. -/
theorem nonemptyTransitionTable_parser_and_restorer_to_equiv
    (t : TransitionDescription)
    (rest : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    exists parserEndpoint :
        TuringMachine.Configuration MachineCodeSymbol
          TransitionListParserState,
      TuringMachine.Computes transitionListParserMachine
          (TuringMachine.initial transitionListParserMachine
            (MachineDescription.encodeNatAppend (t :: rest).length
              (MachineDescription.encodeTransitionsAppend
                (t :: rest) suffix)))
          parserEndpoint ∧
      parserEndpoint.state = TransitionListParserState.halt ∧
      Tape.Equiv
          (parsedTransitionHaltConfig (t :: rest).length
            (MachineDescription.encodeTransitions (t :: rest)) suffix).tape
          parserEndpoint.tape ∧
      MarkerRunsToEquiv
        { state :=
            MarkerRestoreState.seek
              (transitionListParserSavedHead suffix)
          tape := parserEndpoint.tape }
        (parsedMarkerRestoreTargetConfig (t :: rest).length
          (MachineDescription.encodeTransitions (t :: rest)) suffix) := by
  have hparser :=
    transitionListParserMachine_runs_encodeTransitions_to_equiv
      (t :: rest) suffix
  change ParserRunsToEquiv _
    (parsedTransitionHaltConfig (t :: rest).length
      (MachineDescription.encodeTransitions (t :: rest)) suffix) at hparser
  rcases hparser with
    ⟨parserEndpoint, parserRun, parserStateEq, parserTapeEquiv⟩
  have hsymbols :
      transitionListParserNoHeader
        (MachineDescription.encodeTransitions (t :: rest)) := by
    simpa [MachineDescription.encodeTransitions] using
      transitionListParser_encodeTransitionsAppend_noHeader
        (t :: rest) (suffix := [])
        (by
          intro symbol hmem
          simp at hmem)
  have hsymbolsNonempty :
      MachineDescription.encodeTransitions (t :: rest) ≠ [] := by
    simp [MachineDescription.encodeTransitions,
      MachineDescription.encodeTransitionsAppend,
      MachineDescription.encodeTransitionAppend]
  have hmarker :=
    markerRestoreMachine_runs_parsed_to_equiv
      rest.length (MachineDescription.encodeTransitions (t :: rest)) suffix
      hsymbols hsymbolsNonempty parserTapeEquiv
  refine ⟨parserEndpoint, parserRun, parserStateEq, parserTapeEquiv, ?_⟩
  simpa using hmarker

end Computability
end FoC
