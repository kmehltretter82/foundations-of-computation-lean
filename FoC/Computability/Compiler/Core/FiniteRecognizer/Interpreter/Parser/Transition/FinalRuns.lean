import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Parser.Transition.Continuation

namespace FoC
namespace Computability

open Languages

namespace Section53TransitionParserHandoff

def parsedMarkerRestoreSourceConfig
    (rowCount : Nat)
    (symbols suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol MarkerRestoreState :=
  { state := MarkerRestoreState.seek (savedSuffixHead suffix)
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
          (restoredSuffixCells suffix)) }

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
        savedSuffixHead, markedSuffixCells, restoredSuffixCells]
        using
          markerRestoreMachine_computes_marked_blanks_exact
            none symbols hsymbols hsymbolsNonempty extraBlanks []
  | cons first rest =>
      simpa [parsedMarkerRestoreSourceConfig,
        parsedMarkerRestoreTargetConfig, parsedTransitionHaltConfig,
        savedSuffixHead, markedSuffixCells, restoredSuffixCells]
        using
          markerRestoreMachine_computes_marked_blanks_exact
            (some first) symbols hsymbols hsymbolsNonempty
            extraBlanks (rest.map some)

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
      { state := MarkerRestoreState.seek (savedSuffixHead suffix)
        tape := physicalTape }
      (parsedMarkerRestoreTargetConfig (extraBlanks + 1)
        symbols suffix) := by
  have hcanonical :=
    markerRestoreMachine_computes_parsed_exact
      extraBlanks symbols suffix hsymbols hsymbolsNonempty
  simpa [parsedMarkerRestoreSourceConfig] using
    (markerRestoreMachine_runs_to_equiv_of_source_equiv
      hcanonical htape)

theorem transitionListParser_encodeTransitions_noHeader
    (transitions : List TransitionDescription) :
    transitionListParserNoHeader
      (MachineDescription.encodeTransitions transitions) := by
  induction transitions with
  | nil =>
      simpa [MachineDescription.encodeTransitions,
        MachineDescription.encodeTransitionsAppend] using
        (show transitionListParserNoHeader [] by
          intro symbol hmem
          simp at hmem)
  | cons t rest ih =>
      simpa [MachineDescription.encodeTransitions,
        MachineDescription.encodeTransitionsAppend] using
        transitionListParser_encodeTransitionAppend_noHeader t ih

theorem transitionListParser_encodeTransitions_cons_nonempty
    (t : TransitionDescription)
    (rest : List TransitionDescription) :
    MachineDescription.encodeTransitions (t :: rest) ≠ [] := by
  simp [MachineDescription.encodeTransitions,
    MachineDescription.encodeTransitionsAppend,
    MachineDescription.encodeTransitionAppend]

/-- End-to-end seam for every nonempty canonical transition table.  The
marker restorer starts on the parser's actual physical endpoint and is
transported from the canonical parsed tape. -/
theorem nonemptyTransitionTable_parser_and_restorer_to_equiv_of_step
    (hexact : TransitionListParserExactContinuationStep)
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
        { state := MarkerRestoreState.seek (savedSuffixHead suffix)
          tape := parserEndpoint.tape }
        (parsedMarkerRestoreTargetConfig (t :: rest).length
          (MachineDescription.encodeTransitions (t :: rest)) suffix) := by
  have hparser :=
    transitionListParserMachine_runs_encodeTransitions_to_equiv_of_step
      hexact (t :: rest) suffix
  change ParserRunsToEquiv _
    (parsedTransitionHaltConfig (t :: rest).length
      (MachineDescription.encodeTransitions (t :: rest)) suffix) at hparser
  rcases hparser with
    ⟨parserEndpoint, parserRun, parserStateEq, parserTapeEquiv⟩
  have hmarker :=
    markerRestoreMachine_runs_parsed_to_equiv
      rest.length (MachineDescription.encodeTransitions (t :: rest)) suffix
      (transitionListParser_encodeTransitions_noHeader (t :: rest))
      (transitionListParser_encodeTransitions_cons_nonempty t rest)
      parserTapeEquiv
  refine ⟨parserEndpoint, parserRun, parserStateEq, parserTapeEquiv, ?_⟩
  simpa using hmarker

theorem transitionListParser_encodeTwoTransitions_noHeader
    (t u : TransitionDescription) :
    transitionListParserNoHeader
      (MachineDescription.encodeTransitions [t, u]) := by
  have h :=
    transitionListParserNoHeader_append
      (transitionListParser_encodeTransition_noHeader t)
      (transitionListParser_encodeTransition_noHeader u)
  simpa [MachineDescription.encodeTransitions,
    MachineDescription.encodeTransitionsAppend,
    MachineDescription.encodeTransition,
    MachineDescription.encodeTransitionAppend,
    MachineDescription.encodeNatAppend,
    MachineDescription.encodeCellAppend,
    MachineDescription.encodeDirectionAppend,
    List.append_assoc]
    using h

theorem transitionListParser_encodeTwoTransitions_nonempty
    (t u : TransitionDescription) :
    MachineDescription.encodeTransitions [t, u] ≠ [] := by
  simp [MachineDescription.encodeTransitions,
    MachineDescription.encodeTransitionsAppend,
    MachineDescription.encodeTransitionAppend]

theorem twoTransitions_parser_and_restorer_exact_of_step
    (hexact : TransitionListParserExactContinuationStep)
    (t u : TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes transitionListParserMachine
        (TuringMachine.initial transitionListParserMachine
          (MachineDescription.encodeNatAppend 2
            (MachineDescription.encodeTransitionsAppend [t, u] suffix)))
        (parsedTransitionHaltConfig 2
          (MachineDescription.encodeTransitions [t, u]) suffix) ∧
      TuringMachine.Computes markerRestoreMachine
        (parsedMarkerRestoreSourceConfig 2
          (MachineDescription.encodeTransitions [t, u]) suffix)
        (parsedMarkerRestoreTargetConfig 2
          (MachineDescription.encodeTransitions [t, u]) suffix) := by
  constructor
  · exact
      transitionListParserMachine_computes_twoTransitions_exact_of_step
        hexact t u suffix
  · exact
      markerRestoreMachine_computes_parsed_exact
        1 (MachineDescription.encodeTransitions [t, u]) suffix
        (transitionListParser_encodeTwoTransitions_noHeader t u)
        (transitionListParser_encodeTwoTransitions_nonempty t u)

theorem markerRestoreMachine_computes_marked_exact
    (saved : Option MachineCodeSymbol)
    (symbols : Word MachineCodeSymbol)
    (hsymbols : transitionListParserNoHeader symbols)
    (hsymbolsNonempty : symbols ≠ [])
    (markerTail : List (Option MachineCodeSymbol)) :
    TuringMachine.Computes markerRestoreMachine
      { state := MarkerRestoreState.seek saved
        tape :=
          transitionListParserOptionTape
            [some MachineCodeSymbol.done,
              some MachineCodeSymbol.blank,
              none]
            (List.append (symbols.map some)
              (some MachineCodeSymbol.header :: markerTail)) }
      { state := MarkerRestoreState.halt
        tape :=
          transitionListParserOptionTape
            [some MachineCodeSymbol.done,
              some MachineCodeSymbol.blank,
              none]
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
      let rewindSymbols : Word MachineCodeSymbol :=
        List.append leftSymbols
          [MachineCodeSymbol.done, MachineCodeSymbol.blank]
      have hseek :=
        markerRestoreMachine_computes_seek_prefix
          saved symbols hsymbols
          [some MachineCodeSymbol.done,
            some MachineCodeSymbol.blank,
            none]
          markerTail
      have hrestore :=
        markerRestoreMachine_step_restore_marker saved
          (List.append (leftSymbols.map some)
            [some MachineCodeSymbol.done,
              some MachineCodeSymbol.blank,
              none])
          markerTail (some current)
      have hrewind :=
        markerRestoreMachine_computes_rewind_to_boundary
          rewindSymbols current (saved :: markerTail)
      have hrewindPhysical :
          TuringMachine.Computes markerRestoreMachine
            { state := MarkerRestoreState.rewind
              tape :=
                transitionListParserOptionTape
                  (List.append (leftSymbols.map some)
                    [some MachineCodeSymbol.done,
                      some MachineCodeSymbol.blank,
                      none])
                  (some current :: saved :: markerTail) }
            { state := MarkerRestoreState.rewind
              tape :=
                transitionListParserOptionTape []
                  (none ::
                    some MachineCodeSymbol.blank ::
                    some MachineCodeSymbol.done ::
                    List.append (leftSymbols.map some).reverse
                      (some current :: saved :: markerTail)) } := by
        simpa [rewindSymbols, List.map_append,
          List.map_reverse, List.append_assoc]
          using hrewind
      have hrewindNormalized :
          TuringMachine.Computes markerRestoreMachine
            { state := MarkerRestoreState.rewind
              tape :=
                transitionListParserOptionTape
                  (List.append (leftSymbols.map some)
                    [some MachineCodeSymbol.done,
                      some MachineCodeSymbol.blank,
                      none])
                  (some current :: saved :: markerTail) }
            { state := MarkerRestoreState.rewind
              tape :=
                transitionListParserOptionTape []
                  (none ::
                    some MachineCodeSymbol.blank ::
                    some MachineCodeSymbol.done ::
                    List.append (symbols.map some)
                      (saved :: markerTail)) } := by
        rw [hrestShape] at hrewindPhysical
        exact hrewindPhysical
      have hboundary :=
        markerRestoreMachine_step_rewind_boundary
          (some MachineCodeSymbol.blank ::
            some MachineCodeSymbol.done ::
            List.append (symbols.map some) (saved :: markerTail))
      have hblank :=
        markerRestoreMachine_step_enter_blank [none]
          (some MachineCodeSymbol.done ::
            List.append (symbols.map some) (saved :: markerTail))
      have hdone :=
        markerRestoreMachine_step_enter_done
          [some MachineCodeSymbol.blank, none]
          (List.append (symbols.map some) (saved :: markerTail))
      exact
        TuringMachine.computes_trans
          (by
            simpa [hreverse, List.append_assoc]
              using hseek)
          (TuringMachine.Computes.step
            (by simpa using hrestore)
            (TuringMachine.computes_trans
              hrewindNormalized
              (TuringMachine.Computes.step
                (by simpa using hboundary)
                (TuringMachine.Computes.step
                  (by simpa using hblank)
                  (TuringMachine.Computes.step
                    (by simpa using hdone)
                    (TuringMachine.Computes.refl _))))))

theorem markerRestoreMachine_computes_oneTransition_exact
    (t : TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes markerRestoreMachine
      (markerRestoreSourceConfig t suffix)
      (markerRestoreTargetConfig t suffix) := by
  have hsymbols :
      transitionListParserNoHeader
        (MachineDescription.encodeTransition t) :=
    transitionListParser_encodeTransition_noHeader t
  have hsymbolsNonempty :
      MachineDescription.encodeTransition t ≠ [] := by
    simp [MachineDescription.encodeTransition,
      MachineDescription.encodeTransitionAppend]
  cases suffix with
  | nil =>
      simpa [markerRestoreSourceConfig, markerRestoreTargetConfig,
        oneTransitionHaltConfig, savedSuffixHead, markedSuffixCells,
        restoredSuffixCells] using
        markerRestoreMachine_computes_marked_exact
          none (MachineDescription.encodeTransition t)
          hsymbols hsymbolsNonempty []
  | cons first rest =>
      simpa [markerRestoreSourceConfig, markerRestoreTargetConfig,
        oneTransitionHaltConfig, savedSuffixHead, markedSuffixCells,
        restoredSuffixCells] using
        markerRestoreMachine_computes_marked_exact
          (some first) (MachineDescription.encodeTransition t)
          hsymbols hsymbolsNonempty (rest.map some)

/--
The exact parser handoff and the runtime semantics agree on the smallest
nonempty table: the parsed row is selected and its write/move/target action is
the next configuration.  No well-formedness or state-range hypothesis is used.
-/
theorem oneTransition_parser_handoff_and_runtime_step
    (D : MachineDescription)
    (t : TransitionDescription)
    (remaining : Nat)
    (config : MachineDescription.Configuration)
    (suffix : Word MachineCodeSymbol)
    (hmatch :
      MachineDescription.Matches config.state (Tape.read config.tape) t =
        true) :
    TuringMachine.Computes transitionListParserMachine
        (TuringMachine.initial transitionListParserMachine
          (MachineDescription.encodeNatAppend 1
            (MachineDescription.encodeTransitionAppend t suffix)))
        (oneTransitionHaltConfig t suffix) ∧
      ({ D with transitions := [t] }).runConfig (remaining + 1) config =
        ({ D with transitions := [t] }).runConfig remaining
          { state := t.target
            tape :=
              Tape.move t.move
                (Tape.write t.write config.tape) } := by
  constructor
  · exact
      transitionListParserMachine_computes_oneTransition_exact t suffix
  · simp [MachineDescription.runConfig,
      MachineDescription.stepConfig,
      MachineDescription.lookupTransition, hmatch]
    done


end Section53TransitionParserHandoff

end Computability
end FoC
