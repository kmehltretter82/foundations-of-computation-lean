import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Parser.SavedCell.Handoff

namespace FoC
namespace Computability

open Languages
open FiniteRecognizer.Interpreter.ParserAssembly

namespace FiniteRecognizer.Interpreter.SavedCellTransitionParser

def finalReadyConfig
    (rowCount : Nat)
    (symbols suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  readyConfig (transitionListParserSavedHead suffix)
    (parsedTransitionHaltConfig rowCount symbols suffix).tape

/-- The last parser row reaches the saved-cell endpoint on the same physical
tape as the production parser's canonical halt configuration. -/
theorem computes_final_mark_ready_exact
    (rowCount : Nat)
    (symbols suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (parserConfig (finalTransitionMarkConfig rowCount symbols suffix))
      (finalReadyConfig rowCount symbols suffix) := by
  let leftNormal : Word MachineCodeSymbol :=
    List.append
      (List.replicate rowCount MachineCodeSymbol.blank)
      (MachineCodeSymbol.done :: symbols)
  have hreverseNonempty : leftNormal.reverse ≠ [] := by
    simp [leftNormal]
  cases hreverse : leftNormal.reverse with
  | nil =>
      exact False.elim (hreverseNonempty hreverse)
  | cons current leftSymbols =>
      have hleft :
          leftNormal = List.append leftSymbols.reverse [current] := by
        have h := congrArg List.reverse hreverse
        simpa using! h
      cases suffix with
      | nil =>
          have hreturn :=
            transitionListParserMachine_markPosition_empty_returnLeft_toBoundary
              leftSymbols [] current
          have hprefix :
              List.append (leftSymbols.map some).reverse [some current] =
                leftNormal.map some := by
            have hmap := congrArg (List.map some) hleft
            simpa [List.map_append, List.map_reverse,
              List.append_assoc]
              using hmap.symm
          have htargetRest :
              List.append (leftSymbols.map some).reverse
                  [some current, some MachineCodeSymbol.header] =
                List.append
                  (List.replicate rowCount
                    (some MachineCodeSymbol.blank))
                  (some MachineCodeSymbol.done ::
                    List.append (symbols.map some)
                      [some MachineCodeSymbol.header]) := by
            calc
              List.append (leftSymbols.map some).reverse
                  [some current, some MachineCodeSymbol.header] =
                List.append
                  (List.append (leftSymbols.map some).reverse
                    [some current])
                  [some MachineCodeSymbol.header] := by
                  simp [List.append_assoc]
              _ = List.append (leftNormal.map some)
                    [some MachineCodeSymbol.header] := by
                  rw [hprefix]
              _ = List.append
                    (List.replicate rowCount
                      (some MachineCodeSymbol.blank))
                    (some MachineCodeSymbol.done ::
                      List.append (symbols.map some)
                        [some MachineCodeSymbol.header]) := by
                  simp [leftNormal, List.map_append,
                    List.map_replicate, List.append_assoc]
          have hfinish :=
            computes_findCount_saved_blanks_done_exact
              none rowCount [none]
              (List.append (symbols.map some)
                [some MachineCodeSymbol.header])
          have htargetRest' :
              List.append (leftSymbols.reverse.map some)
                  [some current, some MachineCodeSymbol.header] =
                List.append
                  (List.replicate rowCount
                    (some MachineCodeSymbol.blank))
                  (some MachineCodeSymbol.done ::
                    List.append (symbols.map some)
                      [some MachineCodeSymbol.header]) := by
            simpa [List.map_reverse] using htargetRest
          rw [htargetRest'] at hreturn
          have hsourceLeft :
              List.append
                  ((List.append
                    (List.replicate rowCount
                      MachineCodeSymbol.blank)
                    (MachineCodeSymbol.done :: symbols)).reverse.map
                    some)
                  [none] =
                some current ::
                  List.append (leftSymbols.map some) [none] := by
            change
              List.append (leftNormal.reverse.map some) [none] = _
            rw [hreverse]
            rfl
          have hreturnLift :=
            computes_lift_of_target_ne_halt hreturn (by simp)
          exact
            TuringMachine.computes_trans
              (by
                simpa only [parserConfig, finalTransitionMarkConfig,
                  hsourceLeft, List.map,
                  TuringMachine.PhaseEmbedding.liftConfig]
                  using hreturnLift)
              (by
                simpa [finalReadyConfig, readyConfig,
                  parsedTransitionHaltConfig, parsedTableLeftRev,
                  transitionListParserMarkedTail,
                  transitionListParserSavedHead]
                  using hfinish)
      | cons first rest =>
          have hreturn :=
            transitionListParserMachine_markPosition_returnLeft_toBoundary
              (some first) leftSymbols [] current (rest.map some)
          have hprefix :
              List.append (leftSymbols.map some).reverse [some current] =
                leftNormal.map some := by
            have hmap := congrArg (List.map some) hleft
            simpa [List.map_append, List.map_reverse,
              List.append_assoc]
              using hmap.symm
          have htargetRest :
              List.append (leftSymbols.map some).reverse
                  (some current ::
                    some MachineCodeSymbol.header :: rest.map some) =
                List.append
                  (List.replicate rowCount
                    (some MachineCodeSymbol.blank))
                  (some MachineCodeSymbol.done ::
                    List.append (symbols.map some)
                      (some MachineCodeSymbol.header ::
                        rest.map some)) := by
            calc
              List.append (leftSymbols.map some).reverse
                  (some current ::
                    some MachineCodeSymbol.header :: rest.map some) =
                List.append
                  (List.append (leftSymbols.map some).reverse
                    [some current])
                  (some MachineCodeSymbol.header :: rest.map some) := by
                  simp [List.append_assoc]
              _ = List.append (leftNormal.map some)
                    (some MachineCodeSymbol.header :: rest.map some) := by
                  rw [hprefix]
              _ = List.append
                    (List.replicate rowCount
                      (some MachineCodeSymbol.blank))
                    (some MachineCodeSymbol.done ::
                      List.append (symbols.map some)
                        (some MachineCodeSymbol.header ::
                          rest.map some)) := by
                  simp [leftNormal, List.map_append,
                    List.map_replicate, List.append_assoc]
          have hfinish :=
            computes_findCount_saved_blanks_done_exact
              (some first) rowCount [none]
              (List.append (symbols.map some)
                (some MachineCodeSymbol.header :: rest.map some))
          have htargetRest' :
              List.append (leftSymbols.reverse.map some)
                  (some current ::
                    some MachineCodeSymbol.header :: rest.map some) =
                List.append
                  (List.replicate rowCount
                    (some MachineCodeSymbol.blank))
                  (some MachineCodeSymbol.done ::
                    List.append (symbols.map some)
                      (some MachineCodeSymbol.header ::
                        rest.map some)) := by
            simpa [List.map_reverse] using htargetRest
          rw [htargetRest'] at hreturn
          have hsourceLeft :
              List.append
                  ((List.append
                    (List.replicate rowCount
                      MachineCodeSymbol.blank)
                    (MachineCodeSymbol.done :: symbols)).reverse.map
                    some)
                  [none] =
                some current ::
                  List.append (leftSymbols.map some) [none] := by
            change
              List.append (leftNormal.reverse.map some) [none] = _
            rw [hreverse]
            rfl
          have hreturnLift :=
            computes_lift_of_target_ne_halt hreturn (by simp)
          exact
            TuringMachine.computes_trans
              (by
                simpa only [parserConfig, finalTransitionMarkConfig,
                  hsourceLeft, List.map,
                  TuringMachine.PhaseEmbedding.liftConfig]
                  using hreturnLift)
              (by
                simpa [finalReadyConfig, readyConfig,
                  parsedTransitionHaltConfig, parsedTableLeftRev,
                  transitionListParserMarkedTail,
                  transitionListParserSavedHead]
                  using hfinish)

/-- A saved-cell parser run whose actual endpoint has the canonical ready
state and an equivalent physical tape. -/
def RunsToEquiv
    (source canonical :
      TuringMachine.Configuration MachineCodeSymbol Control) : Prop :=
  exists endpoint : TuringMachine.Configuration MachineCodeSymbol Control,
    TuringMachine.Computes machine source endpoint ∧
    endpoint.state = canonical.state ∧
    Tape.Equiv canonical.tape endpoint.tape

namespace RunsToEquiv

def exact
    {source target :
      TuringMachine.Configuration MachineCodeSymbol Control}
    (hrun : TuringMachine.Computes machine source target) :
    RunsToEquiv source target :=
  ⟨target, hrun, rfl, Tape.Equiv.refl _⟩

def sourceEquiv
    {source canonical :
      TuringMachine.Configuration MachineCodeSymbol Control}
    (hstate : source.state = canonical.state)
    (htape : Tape.Equiv canonical.tape source.tape) :
    RunsToEquiv source canonical :=
  ⟨source, TuringMachine.Computes.refl _, hstate, htape⟩

theorem retarget
    {source oldCanonical newCanonical :
      TuringMachine.Configuration MachineCodeSymbol Control}
    (run : RunsToEquiv source oldCanonical)
    (hstate : oldCanonical.state = newCanonical.state)
    (htape : Tape.Equiv newCanonical.tape oldCanonical.tape) :
    RunsToEquiv source newCanonical := by
  rcases run with
    ⟨endpoint, endpointRun, endpointStateEq, endpointTapeEquiv⟩
  exact
    ⟨endpoint, endpointRun, endpointStateEq.trans hstate,
      Tape.Equiv.trans htape endpointTapeEquiv⟩

theorem trans
    {source middle target :
      TuringMachine.Configuration MachineCodeSymbol Control}
    (first : RunsToEquiv source middle)
    (second : RunsToEquiv middle target) :
    RunsToEquiv source target := by
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

end RunsToEquiv

/-- Iterate all remaining canonical rows while preserving the saved cell at
the final ready endpoint. -/
theorem runs_rows_to_ready_equiv
    (blanks : Nat)
    (pre : Word MachineCodeSymbol)
    (hpre : transitionListParserNoHeader pre)
    (t : TransitionDescription)
    (rest : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    RunsToEquiv
      (parserConfig (canonicalMarkConfig blanks pre t rest suffix))
      (finalReadyConfig (blanks + rest.length)
        (canonicalParsedSymbols pre t rest) suffix) := by
  induction rest generalizing blanks pre t with
  | nil =>
      have hboundary :
          RunsToEquiv
            (parserConfig (canonicalMarkConfig blanks pre t [] suffix))
            (parserConfig
              (canonicalPaddedMarkConfig blanks pre t [] suffix)) :=
        RunsToEquiv.sourceEquiv rfl
          (Tape.Equiv.symm
            (canonicalMarkConfig_tape_equiv_padded
              blanks pre t [] suffix))
      have hfinal :=
        computes_final_mark_ready_exact
          blanks (canonicalParsedSymbols pre t []) suffix
      have hfinal' :
          TuringMachine.Computes machine
            (parserConfig
              (canonicalPaddedMarkConfig blanks pre t [] suffix))
            (finalReadyConfig blanks
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
        (RunsToEquiv.trans hboundary (RunsToEquiv.exact hfinal'))
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
      have hstepLift :=
        computes_lift_of_target_ne_halt hstep' (by simp
          [canonicalPaddedMarkConfig])
      have hnext :
          RunsToEquiv
            (parserConfig
              (canonicalMarkConfig blanks pre t (u :: more) suffix))
            (parserConfig
              (canonicalMarkConfig (blanks + 1)
                (List.append pre
                  (MachineDescription.encodeTransition t))
                u more suffix)) :=
        RunsToEquiv.retarget
          (RunsToEquiv.exact hstepLift) rfl
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
      exact RunsToEquiv.trans hnext hrest

/-- Every nonempty canonical table reaches a ready endpoint, up to harmless
trailing-window differences. -/
theorem padded_nonempty_runs_to_ready_equiv
    (t : TransitionDescription)
    (rest : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    RunsToEquiv
      (parserConfig
        (TransitionParserContextTransport.paddedCanonicalSource
          (t :: rest) suffix))
      (finalReadyConfig (t :: rest).length
        (MachineDescription.encodeTransitions (t :: rest)) suffix) := by
  have hpad :
      RunsToEquiv
        (parserConfig
          (TransitionParserContextTransport.paddedCanonicalSource
            (t :: rest) suffix))
        (parserConfig
          (TuringMachine.initial transitionListParserMachine
            (TransitionParserContextTransport.canonicalWord
              (t :: rest) suffix))) :=
    RunsToEquiv.sourceEquiv rfl
      (TransitionParserContextTransport.cleanCanonicalSource_tape_equiv_padded
        (t :: rest) suffix)
  have hfirst :=
    transitionListParserMachine_computes_nextTransition_to_markPosition
      rest.length t
      (MachineDescription.encodeTransitionsAppend rest suffix)
  have hfirst' :
      TuringMachine.Computes transitionListParserMachine
        (TuringMachine.initial transitionListParserMachine
          (TransitionParserContextTransport.canonicalWord
            (t :: rest) suffix))
        (canonicalMarkConfig 1 [] t rest suffix) := by
    simpa [canonicalMarkConfig,
      TransitionParserContextTransport.canonicalWord,
      TuringMachine.initial, transitionListParserMachine,
      transitionListParserOptionTape_nil_eq_input,
      MachineDescription.encodeTransitionsAppend,
      List.append_assoc]
      using hfirst
  have hfirstLift :=
    computes_lift_of_target_ne_halt hfirst' (by simp [canonicalMarkConfig])
  have hnoHeader :
      transitionListParserNoHeader ([] : Word MachineCodeSymbol) := by
    intro symbol hmem
    simp at hmem
  have hrest :=
    runs_rows_to_ready_equiv 1 [] hnoHeader t rest suffix
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
  exact RunsToEquiv.trans hpad
    (RunsToEquiv.trans (RunsToEquiv.exact hfirstLift) hrest)

def appendLeftContextConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (config : TuringMachine.Configuration MachineCodeSymbol Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := config.state
    tape :=
      TransitionParserContextTransport.appendLeftContext
        baseLeftRev config.tape }

theorem step_project
    {source target :
      TuringMachine.Configuration MachineCodeSymbol Control}
    (hstep : TuringMachine.Step machine source target) :
    TuringMachine.Step transitionListParserMachine
      (projectConfig source) (projectConfig target) := by
  cases hstep with
  | @mk write direction nextState haction =>
      apply TuringMachine.Step.mk
      change transition source.state (Tape.read source.tape) =
        some (write, direction, nextState) at haction
      have hproject := transition_project source.state (Tape.read source.tape)
      rw [haction] at hproject
      simpa [projectConfig, projectAction,
        TuringMachine.PhaseEmbedding.liftConfig] using hproject

theorem step_append_left_context
    (baseLeftRev : Word MachineCodeSymbol)
    {source target :
      TuringMachine.Configuration MachineCodeSymbol Control}
    (hbarrier :
      TransitionParserContextTransport.configHasBlankBarrier
        (projectConfig source))
    (hstep : TuringMachine.Step machine source target) :
    TuringMachine.Step machine
      (appendLeftContextConfig baseLeftRev source)
      (appendLeftContextConfig baseLeftRev target) := by
  cases hstep with
  | @mk write direction nextState haction =>
      change transition source.state (Tape.read source.tape) =
        some (write, direction, nextState) at haction
      have hprojectAction :
          transitionListParserMachine.transition
              (projectState source.state) (Tape.read source.tape) =
            some (write, direction, projectState nextState) := by
        have hproject :=
          transition_project source.state (Tape.read source.tape)
        rw [haction] at hproject
        simpa [projectAction] using hproject
      cases direction with
      | left =>
          have hleft : source.tape.left ≠ [] :=
            TransitionParserContextTransport.left_source_nonempty
              write (projectState nextState) hbarrier hprojectAction
          change
            TuringMachine.Step machine
              { state := source.state
                tape :=
                  TransitionParserContextTransport.appendLeftContext
                    baseLeftRev source.tape }
              { state := nextState
                tape :=
                  TransitionParserContextTransport.appendLeftContext
                    baseLeftRev
                    (Tape.move Direction.left
                      (Tape.write write source.tape)) }
          rw [TransitionParserContextTransport.appendLeftContext_write_move_left_of_nonempty
            baseLeftRev write source.tape hleft]
          exact TuringMachine.Step.mk (by
            simpa [machine,
              TransitionParserContextTransport.appendLeftContext,
              Tape.read] using haction)
      | right =>
          change
            TuringMachine.Step machine
              { state := source.state
                tape :=
                  TransitionParserContextTransport.appendLeftContext
                    baseLeftRev source.tape }
              { state := nextState
                tape :=
                  TransitionParserContextTransport.appendLeftContext
                    baseLeftRev
                    (Tape.move Direction.right
                      (Tape.write write source.tape)) }
          rw [TransitionParserContextTransport.appendLeftContext_write_move_right]
          exact TuringMachine.Step.mk (by
            simpa [machine,
              TransitionParserContextTransport.appendLeftContext,
              Tape.read] using haction)

theorem computes_append_left_context
    (baseLeftRev : Word MachineCodeSymbol)
    {source target :
      TuringMachine.Configuration MachineCodeSymbol Control}
    (hbarrier :
      TransitionParserContextTransport.configHasBlankBarrier
        (projectConfig source))
    (hrun : TuringMachine.Computes machine source target) :
    TuringMachine.Computes machine
      (appendLeftContextConfig baseLeftRev source)
      (appendLeftContextConfig baseLeftRev target) := by
  revert hbarrier
  induction hrun with
  | refl config =>
      intro hbarrier
      exact TuringMachine.Computes.refl _
  | step hstep hrest ih =>
      intro hbarrier
      have hnextBarrier :=
        TransitionParserContextTransport.step_preserves_blank_barrier
          hbarrier (step_project hstep)
      exact
        TuringMachine.Computes.step
          (step_append_left_context baseLeftRev hbarrier hstep)
          (ih hnextBarrier)

/-- A nonempty contextual table reaches the endpoint that still carries the
saved cell needed by the next phase. -/
theorem contextual_nonempty_computes_to_ready
    (baseLeftRev : Word MachineCodeSymbol)
    (t : TransitionDescription)
    (rest : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    exists endpoint : TuringMachine.Configuration MachineCodeSymbol Control,
      TuringMachine.Computes machine
        (parserConfig
          (TransitionParserContextTransport.contextualCanonicalSource
            baseLeftRev (t :: rest) suffix)) endpoint ∧
      endpoint.state =
        Control.ready (transitionListParserSavedHead suffix) := by
  rcases padded_nonempty_runs_to_ready_equiv t rest suffix with
    ⟨cleanEndpoint, hcleanRun, hcleanState, _hcleanTape⟩
  have hbarrier :
      TransitionParserContextTransport.configHasBlankBarrier
        (projectConfig
          (parserConfig
            (TransitionParserContextTransport.paddedCanonicalSource
              (t :: rest) suffix))) := by
    simpa [projectConfig, parserConfig, projectState,
      TuringMachine.PhaseEmbedding.liftConfig] using
      TransitionParserContextTransport.paddedCanonicalSource_has_barrier
        (t :: rest) suffix
  have hcontextRun :=
    computes_append_left_context baseLeftRev hbarrier hcleanRun
  refine
    ⟨appendLeftContextConfig baseLeftRev cleanEndpoint, ?_, ?_⟩
  · simpa [appendLeftContextConfig, parserConfig,
      TransitionParserContextTransport.contextualCanonicalSource,
      TransitionParserContextTransport.appendLeftContextConfig,
      TuringMachine.PhaseEmbedding.liftConfig]
      using hcontextRun
  · simpa [appendLeftContextConfig, finalReadyConfig, readyConfig]
      using hcleanState

end FiniteRecognizer.Interpreter.SavedCellTransitionParser
end Computability
end FoC
