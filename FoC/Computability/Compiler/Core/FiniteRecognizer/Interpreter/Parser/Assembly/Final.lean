import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Parser.Assembly.Context

namespace FoC
namespace Computability

open Languages
open FiniteRecognizer ExactFuel StrictProbe

namespace Section53ParserAssembly

theorem shiftedTarget_equiv_contextualParserSource
    (baseLeftRev : Word MachineCodeSymbol)
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (hword :
      TransitionParserContextTransport.canonicalWord transitions suffix =
        first :: rest) :
    Tape.Equiv
      (ContextualPrefixRightShiftOne.targetTape
        baseLeftRev first rest [])
      (TransitionParserContextTransport.contextualCanonicalSource
        baseLeftRev transitions suffix).tape := by
  simp only [ContextualPrefixRightShiftOne.targetTape,
    ContextualPrefixRightShiftOne.targetTapeWord,
    TransitionParserContextTransport.contextualCanonicalSource,
    TransitionParserContextTransport.appendLeftContextConfig,
    TransitionParserContextTransport.paddedCanonicalSource,
    TransitionParserContextTransport.appendLeftContext, hword,
    List.map, transitionListParserOptionTape]
  refine ⟨?_, rfl, ?_⟩
  · change
      Tape.dropTrailingNone (none :: baseLeftRev.map some) =
        Tape.dropTrailingNone (none :: baseLeftRev.map some)
    rfl
  · change
      Tape.dropTrailingNone (rest.map some ++ [none]) =
        Tape.dropTrailingNone (rest.map some)
    exact dropTrailingNone_append_none (rest.map some)

/-- Forward parser/restorer contract after the separator has been inserted.
The parser covers 0/1/N rows; marker restoration is required exactly in the
nonempty branch. -/
def ContextualParserRestorerForwardContract
    (baseLeftRev : Word MachineCodeSymbol)
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) : Prop :=
  (exists parserEndpoint :
      TuringMachine.Configuration MachineCodeSymbol
        TransitionListParserState,
    TuringMachine.Computes transitionListParserMachine
        (TransitionParserContextTransport.contextualCanonicalSource
          baseLeftRev transitions suffix)
        (TransitionParserContextTransport.appendLeftContextConfig
          baseLeftRev parserEndpoint) ∧
    parserEndpoint.state =
      (canonicalTransitionParserHaltConfig transitions suffix).state ∧
    Tape.Equiv
      (canonicalTransitionParserHaltConfig transitions suffix).tape
      parserEndpoint.tape ∧
    TransitionParserContextTransport.configHasBlankBarrier parserEndpoint) ∧
  forall t rest,
    transitions = t :: rest ->
      exists parserEndpoint :
          TuringMachine.Configuration MachineCodeSymbol
            TransitionListParserState,
      exists markerEndpoint :
          TuringMachine.Configuration MachineCodeSymbol MarkerRestoreState,
        TuringMachine.Computes transitionListParserMachine
            (TransitionParserContextTransport.contextualCanonicalSource
              baseLeftRev (t :: rest) suffix)
            (TransitionParserContextTransport.appendLeftContextConfig
              baseLeftRev parserEndpoint) ∧
        parserEndpoint.state = TransitionListParserState.halt ∧
        Tape.Equiv
            (parsedTransitionHaltConfig (t :: rest).length
              (MachineDescription.encodeTransitions (t :: rest))
              suffix).tape
            parserEndpoint.tape ∧
        TuringMachine.Computes markerRestoreMachine
            (MarkerRestoreContextTransport.appendLeftContextConfig
              baseLeftRev
              { state :=
                  MarkerRestoreState.seek
                    (transitionListParserSavedHead suffix)
                tape := parserEndpoint.tape })
            (MarkerRestoreContextTransport.appendLeftContextConfig
              baseLeftRev markerEndpoint) ∧
        markerEndpoint.state = MarkerRestoreState.halt ∧
        Tape.Equiv
            (parsedMarkerRestoreTargetConfig (t :: rest).length
              (MachineDescription.encodeTransitions (t :: rest))
              suffix).tape
            markerEndpoint.tape

theorem contextualParserRestorerForwardContract
    (baseLeftRev : Word MachineCodeSymbol)
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    ContextualParserRestorerForwardContract
      baseLeftRev transitions suffix := by
  constructor
  · exact
      TransitionParserContextTransport.contextualCanonicalSource_parser_forward
        baseLeftRev transitions suffix
  · intro t rest htransitions
    subst transitions
    exact
      MarkerRestoreContextTransport.contextualNonemptyParserRestorer_forward
        baseLeftRev t rest suffix

/-- Complete canonical forward parser assembly from
`encodeNat fuel ++ encodeDescription D ++ input`.  The conjunction records the
cross-machine physical seams explicitly; no monolithic wrapper machine is
assumed. -/
theorem canonicalDescriptionParserAssembly_forward
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol) :
    ProductInput.PairFuelParser.machine.runConfigExact? (fuel + 1)
        (outerFuelSourceConfig D fuel input) =
      some (outerFuelEndpointConfig D fuel input) ∧
    (outerFuelEndpointConfig D fuel input).tape =
      (headerParserSourceConfig D fuel input).tape ∧
    TuringMachine.Computes headerFieldsParserMachine
      (headerParserSourceConfig D fuel input)
      (headerParserTransitionCountConfig D fuel input) ∧
    exists first : MachineCodeSymbol,
    exists rest : Word MachineCodeSymbol,
    exists shiftEndpoint :
        TuringMachine.Configuration MachineCodeSymbol
          ContextualPrefixRightShiftOne.Control,
      transitionParserWord D input = first :: rest ∧
      ContextualPrefixRightShiftOne.machine.runConfigExact?
          (ProductCleanupGap.PrefixRightShiftOne.runSteps (first :: rest))
          { state :=
              ProductCleanupGap.PrefixRightShiftOne.Control.takeFirst
            tape := (headerParserTransitionCountConfig D fuel input).tape } =
        some shiftEndpoint ∧
      shiftEndpoint.state =
        ProductCleanupGap.PrefixRightShiftOne.Control.halt ∧
      Tape.Equiv
        (ContextualPrefixRightShiftOne.targetTape
          (headerAfterHaltLeftRev D fuel) first rest [])
        shiftEndpoint.tape ∧
      Tape.Equiv
        (ContextualPrefixRightShiftOne.targetTape
          (headerAfterHaltLeftRev D fuel) first rest [])
        (TransitionParserContextTransport.contextualCanonicalSource
          (headerAfterHaltLeftRev D fuel) D.transitions input).tape ∧
      ContextualParserRestorerForwardContract
        (headerAfterHaltLeftRev D fuel) D.transitions input := by
  refine ⟨outerFuelParser_run_exact D fuel input, ?_, ?_, ?_⟩
  · exact outerFuelEndpoint_headerSource_tape D fuel input
  · exact headerParser_computes_to_transitionCount_exact D fuel input
  · rcases headerEndpoint_prefixRightShiftOne_forward D fuel input with
      ⟨first, rest, shiftEndpoint, hword, hshift,
        hshiftState, hshiftTape⟩
    have hcanonicalWord :
        TransitionParserContextTransport.canonicalWord
            D.transitions input =
          first :: rest := by
      simpa [TransitionParserContextTransport.canonicalWord,
        transitionParserWord] using hword
    have hsourceSeam :=
      shiftedTarget_equiv_contextualParserSource
        (headerAfterHaltLeftRev D fuel) D.transitions input
        first rest hcanonicalWord
    exact
      ⟨first, rest, shiftEndpoint, hword, hshift,
        hshiftState, hshiftTape, hsourceSeam,
        contextualParserRestorerForwardContract
          (headerAfterHaltLeftRev D fuel) D.transitions input⟩

/-- Contextual closedness contract needed by the parser assembly.  Unlike the
clean-input soundness theorem, this statement starts behind the inserted blank
separator with arbitrary retained header/fuel context. -/
def ContextualTransitionParserHaltInversion : Prop :=
  forall (baseLeftRev : Word MachineCodeSymbol)
    (count : Nat) (tokens : Word MachineCodeSymbol),
    TuringMachine.HaltsFrom transitionListParserMachine
        { state :=
            TransitionListParserState.findCount
              TransitionListParserMarker.initial
          tape :=
            transitionListParserOptionTape
              (none :: baseLeftRev.map some)
              ((MachineDescription.encodeNatAppend count tokens).map some) } ->
      exists transitions : List TransitionDescription,
      exists suffix : Word MachineCodeSymbol,
        count = transitions.length ∧
          tokens =
            MachineDescription.encodeTransitionsAppend transitions suffix

def paddedRawTransitionParserSource
    (count : Nat)
    (tokens : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      TransitionListParserState :=
  { state :=
      TransitionListParserState.findCount
        TransitionListParserMarker.initial
    tape :=
      transitionListParserOptionTape [none]
        ((MachineDescription.encodeNatAppend count tokens).map some) }

theorem paddedRawTransitionParserSource_has_barrier
    (count : Nat)
    (tokens : Word MachineCodeSymbol) :
    TransitionParserContextTransport.configHasBlankBarrier
      (paddedRawTransitionParserSource count tokens) := by
  right
  cases hword : MachineDescription.encodeNatAppend count tokens <;>
    refine ⟨[], ?_⟩ <;>
    simp [paddedRawTransitionParserSource,
      transitionListParserOptionTape, hword]

theorem contextualRawTransitionParserSource_eq_append
    (baseLeftRev : Word MachineCodeSymbol)
    (count : Nat)
    (tokens : Word MachineCodeSymbol) :
    { state :=
        TransitionListParserState.findCount
          TransitionListParserMarker.initial
      tape :=
        transitionListParserOptionTape
          (none :: baseLeftRev.map some)
          ((MachineDescription.encodeNatAppend count tokens).map some) } =
      TransitionParserContextTransport.appendLeftContextConfig
        baseLeftRev (paddedRawTransitionParserSource count tokens) := by
  cases hword : MachineDescription.encodeNatAppend count tokens <;>
    simp [paddedRawTransitionParserSource,
      TransitionParserContextTransport.appendLeftContextConfig,
      TransitionParserContextTransport.appendLeftContext,
      transitionListParserOptionTape, hword]

theorem cleanRawTransitionParserSource_tape_equiv_padded
    (count : Nat)
    (tokens : Word MachineCodeSymbol) :
    Tape.Equiv
      (TuringMachine.initial transitionListParserMachine
        (MachineDescription.encodeNatAppend count tokens)).tape
      (paddedRawTransitionParserSource count tokens).tape := by
  simpa [paddedRawTransitionParserSource,
    TuringMachine.initial, transitionListParserMachine,
    transitionListParserOptionTape_nil_eq_input] using
      transitionListParserOptionTape_append_none_equiv
        ([] : List (Option MachineCodeSymbol))
        ((MachineDescription.encodeNatAppend count tokens).map some)

/-- The contextual halt inversion follows by deleting the inert far-left
context step-for-step, trimming the remaining separator by tape equivalence,
and invoking the existing clean-input parser soundness theorem. -/
theorem contextualTransitionParserHaltInversion :
    ContextualTransitionParserHaltInversion := by
  intro baseLeftRev count tokens hhalt
  rcases hhalt with
    ⟨contextualFinal, hcontextualRun, hcontextualHalt⟩
  have hsourceEq :=
    contextualRawTransitionParserSource_eq_append
      baseLeftRev count tokens
  have hsourceBarrier :=
    paddedRawTransitionParserSource_has_barrier count tokens
  rcases
      TransitionParserContextTransport.computes_remove_left_context_of_eq
        baseLeftRev hsourceEq hsourceBarrier hcontextualRun with
    ⟨paddedFinal, hpaddedRun, hfinalEq, hpaddedBarrier⟩
  have hpaddedHalt :
      TuringMachine.Halted transitionListParserMachine paddedFinal := by
    rw [hfinalEq] at hcontextualHalt
    simpa only [TuringMachine.Halted,
      TransitionParserContextTransport.appendLeftContextConfig]
      using hcontextualHalt
  rcases TuringMachine.computes_to_computesIn hpaddedRun with
    ⟨steps, hpaddedRunIn⟩
  have hsourceTape :=
    Tape.Equiv.symm
      (cleanRawTransitionParserSource_tape_equiv_padded count tokens)
  rcases
      TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
        hpaddedRunIn hsourceTape with
    ⟨cleanFinal, hcleanRunIn, hcleanState, hcleanTape⟩
  have hcleanHalt :
      TuringMachine.Halted transitionListParserMachine cleanFinal :=
    hcleanState.trans hpaddedHalt
  have hcleanHalts :
      TuringMachine.HaltsOnInput transitionListParserMachine
        (MachineDescription.encodeNatAppend count tokens) :=
    ⟨cleanFinal,
      TuringMachine.computesIn_to_computes hcleanRunIn,
      hcleanHalt⟩
  exact
    transitionListParserMachine_halts_encodeNatAppend_only_encodeTransitionsAppend
      hcleanHalts

/-- Exact closedness for the two staged parsing phases.  The header parser
selects the four numeric fields.  If the contextual table parser then halts
for that selected count and remaining token stream, the original stream is
exactly one encoded machine description followed by a suffix. -/
theorem canonicalDescriptionParserAssembly_halts_only_encoded
    {headerLeftRev parserBaseLeftRev rest : Word MachineCodeSymbol}
    {headerSteps : Nat}
    (hheader :
      TuringMachine.HaltsFromIn headerFieldsParserMachine headerSteps
        { state := HeaderFieldsParserState.needHeader
          tape := headerFieldsParserTape headerLeftRev rest })
    (hparser :
      forall stateCount start halt count : Nat,
      forall tokens : Word MachineCodeSymbol,
        rest =
            MachineCodeSymbol.header ::
              MachineDescription.encodeNatAppend stateCount
                (MachineDescription.encodeNatAppend start
                  (MachineDescription.encodeNatAppend halt
                    (MachineDescription.encodeNatAppend count tokens))) ->
          TuringMachine.HaltsFrom transitionListParserMachine
            { state :=
                TransitionListParserState.findCount
                  TransitionListParserMarker.initial
              tape :=
                transitionListParserOptionTape
                  (none :: parserBaseLeftRev.map some)
                  ((MachineDescription.encodeNatAppend count tokens).map
                    some) }) :
    exists D : MachineDescription,
    exists suffix : Word MachineCodeSymbol,
      rest = MachineDescription.encodeDescriptionAppend D suffix := by
  rcases headerFieldsParserMachine_haltsFromIn_only_header hheader with
    ⟨stateCount, start, halt, count, tokens, hshape⟩
  have htable :=
    hparser stateCount start halt count tokens hshape
  rcases contextualTransitionParserHaltInversion
      parserBaseLeftRev count tokens htable with
    ⟨transitions, suffix, hcount, htokens⟩
  refine
    ⟨{ stateCount := stateCount
       start := start
       halt := halt
       transitions := transitions }, suffix, ?_⟩
  rw [hshape, htokens, hcount]
  rfl

/-- Current header-parser soundness gives malformed-input nonhalting directly
in the exact physical cursor currency, with arbitrary retained left context. -/
theorem headerFieldsParserMachine_nonhalts_of_malformed
    {leftRev rest : Word MachineCodeSymbol}
    (hmalformed :
      ¬ exists stateCount start halt transitionCount : Nat,
        exists suffix : Word MachineCodeSymbol,
          rest =
            MachineCodeSymbol.header ::
              MachineDescription.encodeNatAppend stateCount
                (MachineDescription.encodeNatAppend start
                  (MachineDescription.encodeNatAppend halt
                    (MachineDescription.encodeNatAppend transitionCount
                      suffix)))) :
    forall steps : Nat,
      ¬ TuringMachine.HaltsFromIn headerFieldsParserMachine steps
        { state := HeaderFieldsParserState.needHeader
          tape := headerFieldsParserTape leftRev rest } := by
  intro steps hhalts
  exact hmalformed
    (headerFieldsParserMachine_haltsFromIn_only_header hhalts)

/-- Current transition-parser soundness gives clean-source malformed-input
nonhalting in the canonical count/table/suffix decomposition currency. -/
theorem transitionListParserMachine_nonhalts_of_malformed
    {count : Nat}
    {tokens : Word MachineCodeSymbol}
    (hmalformed :
      ¬ exists transitions : List TransitionDescription,
        exists suffix : Word MachineCodeSymbol,
          count = transitions.length ∧
            tokens =
              MachineDescription.encodeTransitionsAppend transitions
                suffix) :
    ¬ TuringMachine.HaltsOnInput transitionListParserMachine
      (MachineDescription.encodeNatAppend count tokens) := by
  intro hhalts
  exact hmalformed
    (transitionListParserMachine_halts_encodeNatAppend_only_encodeTransitionsAppend
      hhalts)

/-- Canonical downstream forward seam once the transition count and table have
been placed behind the parser's required physical blank boundary. -/
theorem canonicalTransitionTable_parser_forward
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    ParserRunsToEquiv
      (TuringMachine.initial transitionListParserMachine
        (MachineDescription.encodeNatAppend transitions.length
          (MachineDescription.encodeTransitionsAppend transitions suffix)))
      (canonicalTransitionParserHaltConfig transitions suffix) := by
  exact
    transitionListParserMachine_runs_encodeTransitions_to_equiv
      transitions suffix

/-- Canonical nonempty parser/restorer seam; the suffix is carried unchanged
through both existing machines. -/
theorem canonicalNonemptyTransitionTable_parser_restorer_forward
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
  exact nonemptyTransitionTable_parser_and_restorer_to_equiv t rest suffix

end Section53ParserAssembly
end Computability
end FoC
