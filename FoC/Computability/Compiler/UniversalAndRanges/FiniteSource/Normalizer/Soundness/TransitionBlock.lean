import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.Normalizer.Soundness.Inversion

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

theorem decodeDescriptionPrefix_of_header_and_decodeTransitions
    {tokens rest : Word MachineCodeSymbol}
    {stateCount start halt transitionCount : Nat}
    {transitions : List TransitionDescription}
    {input : Word MachineCodeSymbol}
    (htokens :
      tokens =
        MachineCodeSymbol.header ::
          MachineDescription.encodeNatAppend stateCount
            (MachineDescription.encodeNatAppend start
              (MachineDescription.encodeNatAppend halt
                (MachineDescription.encodeNatAppend transitionCount rest))))
    (htrans :
      MachineDescription.decodeTransitions transitionCount rest =
        some (transitions, input)) :
    MachineDescription.decodeDescriptionPrefix tokens =
      some
        (({ stateCount := stateCount
            start := start
            halt := halt
            transitions := transitions } : MachineDescription),
          input) := by
  subst tokens
  simp [MachineDescription.decodeDescriptionPrefix,
    MachineDescription.decodeNat_encodeNatAppend, htrans]

theorem codePrefixParserNormalizerMachine_computes_headerFields_to_findInitialCount
    (stateCount start halt : Nat)
    (transitionBlock : Word MachineCodeSymbol) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.needHeader
        tape :=
          codePrefixParserNormalizerTape []
            (MachineCodeSymbol.header ::
              MachineDescription.encodeNatAppend stateCount
                (MachineDescription.encodeNatAppend start
                  (MachineDescription.encodeNatAppend halt
                    transitionBlock))) }
      { state :=
          CodePrefixParserNormalizerState.findInitialCount
        tape :=
          transitionListParserOptionTape
            (codePrefixParserNormalizerMarkedHeaderLeft
              { stateCount := stateCount
                start := start
                halt := halt
                transitions := [] })
            (transitionBlock.map some) } := by
  let afterHeader : Word MachineCodeSymbol :=
    [MachineCodeSymbol.header]
  let afterState : Word MachineCodeSymbol :=
    List.append (MachineDescription.encodeNat stateCount).reverse
      afterHeader
  let afterStart : Word MachineCodeSymbol :=
    List.append (MachineDescription.encodeNat start).reverse
      afterState
  have hheader :
      TuringMachine.Computes codePrefixParserNormalizerMachine
        { state := CodePrefixParserNormalizerState.needHeader
          tape :=
            codePrefixParserNormalizerTape []
              (MachineCodeSymbol.header ::
                MachineDescription.encodeNatAppend stateCount
                  (MachineDescription.encodeNatAppend start
                    (MachineDescription.encodeNatAppend halt
                      transitionBlock))) }
        { state := CodePrefixParserNormalizerState.stateCount
          tape :=
            codePrefixParserNormalizerTape afterHeader
              (MachineDescription.encodeNatAppend stateCount
                (MachineDescription.encodeNatAppend start
                  (MachineDescription.encodeNatAppend halt
                    transitionBlock))) } :=
    TuringMachine.computes_of_step
      (by
        simpa [afterHeader] using
          codePrefixParserNormalizer_step_header []
            (MachineDescription.encodeNatAppend stateCount
              (MachineDescription.encodeNatAppend start
                (MachineDescription.encodeNatAppend halt
                  transitionBlock))))
  have hstate :
      TuringMachine.Computes codePrefixParserNormalizerMachine
        { state := CodePrefixParserNormalizerState.stateCount
          tape :=
            codePrefixParserNormalizerTape afterHeader
              (MachineDescription.encodeNatAppend stateCount
                (MachineDescription.encodeNatAppend start
                  (MachineDescription.encodeNatAppend halt
                    transitionBlock))) }
        { state := CodePrefixParserNormalizerState.startField
          tape :=
            codePrefixParserNormalizerTape afterState
              (MachineDescription.encodeNatAppend start
                (MachineDescription.encodeNatAppend halt
                  transitionBlock)) } := by
    simpa [afterState] using
      codePrefixParserNormalizer_computes_nat'
        CodePrefixParserNormalizerState.stateCount
        CodePrefixParserNormalizerState.startField
        codePrefixParserNormalizer_step_tick_stateCount
        codePrefixParserNormalizer_step_done_stateCount
        afterHeader stateCount
        (MachineDescription.encodeNatAppend start
          (MachineDescription.encodeNatAppend halt transitionBlock))
  have hstart :
      TuringMachine.Computes codePrefixParserNormalizerMachine
        { state := CodePrefixParserNormalizerState.startField
          tape :=
            codePrefixParserNormalizerTape afterState
              (MachineDescription.encodeNatAppend start
                (MachineDescription.encodeNatAppend halt
                  transitionBlock)) }
        { state := CodePrefixParserNormalizerState.haltField
          tape :=
            codePrefixParserNormalizerTape afterStart
              (MachineDescription.encodeNatAppend halt
                transitionBlock) } := by
    simpa [afterStart] using
      codePrefixParserNormalizer_computes_nat'
        CodePrefixParserNormalizerState.startField
        CodePrefixParserNormalizerState.haltField
        codePrefixParserNormalizer_step_tick_startField
        codePrefixParserNormalizer_step_done_startField
        afterState start
        (MachineDescription.encodeNatAppend halt transitionBlock)
  have hhalt :
      TuringMachine.Computes codePrefixParserNormalizerMachine
        { state := CodePrefixParserNormalizerState.haltField
          tape :=
            codePrefixParserNormalizerTape afterStart
              (MachineDescription.encodeNatAppend halt
                transitionBlock) }
        { state :=
            CodePrefixParserNormalizerState.findInitialCount
          tape :=
            transitionListParserOptionTape
              (codePrefixParserNormalizerMarkedHeaderLeft
                { stateCount := stateCount
                  start := start
                  halt := halt
                  transitions := [] })
              (transitionBlock.map some) } := by
    simpa [afterStart, afterState, afterHeader,
      codePrefixParserNormalizerMarkedHeaderLeft,
      List.map_append, List.append_assoc] using
      codePrefixParserNormalizerMachine_computes_haltField_marked
        afterStart halt transitionBlock
  exact
    TuringMachine.computes_trans hheader
      (TuringMachine.computes_trans hstate
        (TuringMachine.computes_trans hstart
          (by
            simpa [afterHeader, afterState, afterStart,
              codePrefixParserNormalizerMarkedHeaderLeft,
              List.map_append, List.append_assoc] using hhalt)))

theorem codePrefixParserNormalizerMachine_computes_headerFields_to_needTransition_cons
    (stateCount start halt : Nat)
    (t : TransitionDescription)
    (rest : List TransitionDescription)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.needHeader
        tape :=
          codePrefixParserNormalizerTape []
            (MachineDescription.encodeDescriptionAppend
              { stateCount := stateCount
                start := start
                halt := halt
                transitions := t :: rest }
              input) }
      { state := CodePrefixParserNormalizerState.needTransition
        tape :=
          transitionListParserOptionTape
            (List.append
              ((MachineDescription.encodeNat rest.length).reverse.map some)
              (some MachineCodeSymbol.blank ::
                codePrefixParserNormalizerMarkedHeaderLeft
                  { stateCount := stateCount
                    start := start
                    halt := halt
                    transitions := [] }))
            ((MachineDescription.encodeTransitionsAppend (t :: rest)
              input).map some) } := by
  have hheader :=
    codePrefixParserNormalizerMachine_computes_headerFields_to_findInitialCount
      stateCount start halt
      (MachineDescription.encodeNatAppend (t :: rest).length
        (MachineDescription.encodeTransitionsAppend (t :: rest) input))
  have hcount :=
    codePrefixParserNormalizerMachine_computes_findInitialCount_succ
      rest.length
      (codePrefixParserNormalizerMarkedHeaderLeft
        { stateCount := stateCount
          start := start
          halt := halt
          transitions := [] })
      (MachineDescription.encodeTransitionsAppend (t :: rest) input)
  exact
    TuringMachine.computes_trans
      (by
        simpa [MachineDescription.encodeDescriptionAppend] using
          hheader)
      (by
        simpa using hcount)

theorem codePrefixParserNormalizerMachine_computes_headerFields_to_markPosition_cons
    (stateCount start halt : Nat)
    (t : TransitionDescription)
    (rest : List TransitionDescription)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.needHeader
        tape :=
          codePrefixParserNormalizerTape []
            (MachineDescription.encodeDescriptionAppend
              { stateCount := stateCount
                start := start
                halt := halt
                transitions := t :: rest }
              input) }
      { state := CodePrefixParserNormalizerState.markPosition
        tape :=
          transitionListParserOptionTape
            (List.append
              ((MachineDescription.encodeNat t.target).reverse.map some)
              (List.append
                ((MachineDescription.encodeDirection t.move).reverse.map
                  some)
                (List.append
                  ((MachineDescription.encodeCell t.write).reverse.map
                    some)
                  (List.append
                    ((MachineDescription.encodeCell t.read).reverse.map
                      some)
                    (List.append
                      ((MachineDescription.encodeNat t.source).reverse.map
                        some)
                      (some MachineCodeSymbol.transition ::
                        List.append
                          ((MachineDescription.encodeNat rest.length).reverse.map
                            some)
                          (some MachineCodeSymbol.blank ::
                            codePrefixParserNormalizerMarkedHeaderLeft
                              { stateCount := stateCount
                                start := start
                                halt := halt
                                transitions := [] })))))))
            ((MachineDescription.encodeTransitionsAppend rest input).map
              some) } := by
  have hprefix :=
    codePrefixParserNormalizerMachine_computes_headerFields_to_needTransition_cons
      stateCount start halt t rest input
  have htransition :=
    codePrefixParserNormalizerMachine_computes_transition
      t
      (List.append
        ((MachineDescription.encodeNat rest.length).reverse.map some)
        (some MachineCodeSymbol.blank ::
          codePrefixParserNormalizerMarkedHeaderLeft
            { stateCount := stateCount
              start := start
              halt := halt
              transitions := [] }))
      (MachineDescription.encodeTransitionsAppend rest input)
  exact
    TuringMachine.computes_trans hprefix
      (by
        simpa [MachineDescription.encodeTransitionsAppend] using
          htransition)

theorem codePrefixParserNormalizerMachine_markPosition_returnLeft_toBoundary
    (saved : Option MachineCodeSymbol)
    (leftSymbols : Word MachineCodeSymbol)
    (prefixLeft : List (Option MachineCodeSymbol))
    (current : MachineCodeSymbol)
    (suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.markPosition
        tape :=
          transitionListParserOptionTape
            (some current ::
              List.append (leftSymbols.map some) (none :: prefixLeft))
            (saved :: suffix) }
      { state :=
          CodePrefixParserNormalizerState.findCount
            (TransitionListParserMarker.saved saved)
        tape :=
          transitionListParserOptionTape (none :: prefixLeft)
            (List.append (leftSymbols.reverse.map some)
              (some current ::
                some MachineCodeSymbol.header :: suffix)) } :=
  TuringMachine.Computes.step
    (codePrefixParserNormalizerMachine_step_write_left_nonempty
      (by simp [codePrefixParserNormalizerMachine]))
    (codePrefixParserNormalizerMachine_returnLeft_toBoundary
      saved leftSymbols prefixLeft
      (some MachineCodeSymbol.header :: suffix)
      current)

theorem codePrefixParserNormalizerMachine_markPosition_empty_returnLeft_toBoundary
    (leftSymbols : Word MachineCodeSymbol)
    (prefixLeft : List (Option MachineCodeSymbol))
    (current : MachineCodeSymbol) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.markPosition
        tape :=
          transitionListParserOptionTape
            (some current ::
              List.append (leftSymbols.map some) (none :: prefixLeft))
            [] }
      { state :=
          CodePrefixParserNormalizerState.findCount
            (TransitionListParserMarker.saved none)
        tape :=
          transitionListParserOptionTape (none :: prefixLeft)
            (List.append (leftSymbols.reverse.map some)
              (some current ::
                some MachineCodeSymbol.header :: [])) } :=
  TuringMachine.Computes.step
    (codePrefixParserNormalizerMachine_step_write_left_empty
      (by simp [codePrefixParserNormalizerMachine]))
    (codePrefixParserNormalizerMachine_returnLeft_toBoundary
      none leftSymbols prefixLeft
      [some MachineCodeSymbol.header]
      current)

theorem codePrefixParserNormalizerMachine_step_restoreSeekMarker_nonHeader
    (saved : Option MachineCodeSymbol)
    {symbol : MachineCodeSymbol}
    (hsymbol : symbol ≠ MachineCodeSymbol.header)
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.restoreSeekMarker saved
        tape :=
          transitionListParserOptionTape leftRev
            (some symbol :: suffix) }
      { state := CodePrefixParserNormalizerState.restoreSeekMarker saved
        tape :=
          transitionListParserOptionTape
            (some symbol :: leftRev) suffix } :=
  codePrefixParserNormalizerMachine_step_keep_right
    (by
      cases symbol <;>
        simp [codePrefixParserNormalizerMachine,
          codePrefixParserNormalizerKeep] at hsymbol ⊢)

theorem codePrefixParserNormalizerMachine_restoreSeekMarker_scan_noHeader
    (saved : Option MachineCodeSymbol)
    (pre : Word MachineCodeSymbol)
    (hpre : transitionListParserNoHeader pre)
    (leftRev : List (Option MachineCodeSymbol))
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.restoreSeekMarker saved
        tape :=
          transitionListParserOptionTape leftRev
            ((List.append pre
              (MachineCodeSymbol.header :: suffix)).map some) }
      { state := CodePrefixParserNormalizerState.restoreSeekMarker saved
        tape :=
          transitionListParserOptionTape
            (List.append (pre.reverse.map some) leftRev)
            (some MachineCodeSymbol.header :: suffix.map some) } := by
  induction pre generalizing leftRev with
  | nil =>
      exact TuringMachine.Computes.refl _
  | cons symbol rest ih =>
      have hsymbol : symbol ≠ MachineCodeSymbol.header :=
        hpre symbol (by simp)
      have hrest : transitionListParserNoHeader rest := by
        intro head hmem
        exact hpre head (by simp [hmem])
      have htail := ih hrest (some symbol :: leftRev)
      exact
        TuringMachine.Computes.step
          (by
            simpa [List.append_assoc] using
              codePrefixParserNormalizerMachine_step_restoreSeekMarker_nonHeader
                saved hsymbol leftRev
                ((List.append rest
                  (MachineCodeSymbol.header :: suffix)).map some))
          (by
            simpa [List.map_append, List.append_assoc] using htail)

theorem codePrefixParserNormalizerMachine_restoreSeekMarker_toBoundary
    (saved : Option MachineCodeSymbol)
    (leftSymbols : Word MachineCodeSymbol)
    (prefixLeft : List (Option MachineCodeSymbol))
    (current : MachineCodeSymbol)
    (suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.restoreSeekMarker saved
        tape :=
          transitionListParserOptionTape
            (some current ::
              List.append (leftSymbols.map some) (none :: prefixLeft))
            (some MachineCodeSymbol.header :: suffix) }
      { state :=
          CodePrefixParserNormalizerState.findCount
            TransitionListParserMarker.initial
        tape :=
          transitionListParserOptionTape (none :: prefixLeft)
            (List.append (leftSymbols.reverse.map some)
              (some current :: saved :: suffix)) } :=
  TuringMachine.Computes.step
    (codePrefixParserNormalizerMachine_step_write_left_nonempty
      (by simp [codePrefixParserNormalizerMachine]))
    (codePrefixParserNormalizerMachine_restoreReturnLeft_toBoundary
      leftSymbols prefixLeft (saved :: suffix) current)

theorem codePrefixParserNormalizerMachine_step_seekCountDone_saved_tick
    (saved : Option MachineCodeSymbol)
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state :=
          CodePrefixParserNormalizerState.seekCountDone
            (TransitionListParserMarker.saved saved)
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.tick :: suffix) }
      { state :=
          CodePrefixParserNormalizerState.seekCountDone
            (TransitionListParserMarker.saved saved)
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.tick :: leftRev) suffix } :=
  codePrefixParserNormalizerMachine_step_keep_right
    (by simp [codePrefixParserNormalizerMachine,
      codePrefixParserNormalizerKeep])

theorem codePrefixParserNormalizerMachine_step_findCount_tick
    (marker : TransitionListParserMarker)
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.findCount marker
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.tick :: suffix) }
      { state :=
          CodePrefixParserNormalizerState.seekCountDone marker
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.blank :: leftRev) suffix } :=
  codePrefixParserNormalizerMachine_step_write_right
    (by
      cases marker <;>
        simp [codePrefixParserNormalizerMachine,
          codePrefixParserNormalizerKeep])

theorem codePrefixParserNormalizerMachine_computes_findCount_blanks_tick
    (marker : TransitionListParserMarker)
    (blanks : Nat)
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.findCount marker
        tape :=
          transitionListParserOptionTape leftRev
            (List.append
              (List.replicate blanks (some MachineCodeSymbol.blank))
              (some MachineCodeSymbol.tick :: suffix)) }
      { state := CodePrefixParserNormalizerState.seekCountDone marker
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.blank ::
              List.append
                (List.replicate blanks (some MachineCodeSymbol.blank))
                leftRev)
            suffix } := by
  induction blanks generalizing leftRev with
  | zero =>
      simpa using
        TuringMachine.Computes.step
          (codePrefixParserNormalizerMachine_step_findCount_tick
            marker leftRev suffix)
          (TuringMachine.Computes.refl _)
  | succ blanks ih =>
      exact
        TuringMachine.Computes.step
          (by
            simpa [List.append_assoc] using
              codePrefixParserNormalizerMachine_step_findCount_blank
                marker leftRev
                (List.append
                  (List.replicate blanks
                    (some MachineCodeSymbol.blank))
                  (some MachineCodeSymbol.tick :: suffix)))
          (by
            rw [←
              codePrefixParserNormalizer_replicate_append_self
                (some MachineCodeSymbol.blank) blanks leftRev]
            exact ih (some MachineCodeSymbol.blank :: leftRev))

theorem codePrefixParserNormalizerMachine_computes_findCount_initial_blanks_done_halt
    (blanks : Nat)
    (prefixLeft suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state :=
          CodePrefixParserNormalizerState.findCount
            TransitionListParserMarker.initial
        tape :=
          transitionListParserOptionTape (none :: prefixLeft)
            (List.append
              (List.replicate blanks (some MachineCodeSymbol.blank))
              (some MachineCodeSymbol.done :: suffix)) }
      { state := CodePrefixParserNormalizerState.halt
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.done ::
              codePrefixParserNormalizerRestoredTicksLeft blanks
                (some MachineCodeSymbol.done :: prefixLeft))
            suffix } := by
  have hscan :
      forall leftRev : List (Option MachineCodeSymbol),
        TuringMachine.Computes codePrefixParserNormalizerMachine
          { state :=
              CodePrefixParserNormalizerState.findCount
                TransitionListParserMarker.initial
            tape :=
              transitionListParserOptionTape leftRev
                (List.append
                  (List.replicate blanks
                    (some MachineCodeSymbol.blank))
                  (some MachineCodeSymbol.done :: suffix)) }
          { state :=
              CodePrefixParserNormalizerState.findCount
                TransitionListParserMarker.initial
            tape :=
              transitionListParserOptionTape
                (List.append
                  (List.replicate blanks
                    (some MachineCodeSymbol.blank))
                  leftRev)
                (some MachineCodeSymbol.done :: suffix) } := by
    induction blanks with
    | zero =>
        intro leftRev
        exact TuringMachine.Computes.refl _
    | succ blanks ih =>
        intro leftRev
        exact
          TuringMachine.Computes.step
            (by
              simpa [List.append_assoc] using
                codePrefixParserNormalizerMachine_step_findCount_blank
                  TransitionListParserMarker.initial
                  leftRev
                  (List.append
                    (List.replicate blanks
                      (some MachineCodeSymbol.blank))
                    (some MachineCodeSymbol.done :: suffix)))
            (by
              have htail := ih (some MachineCodeSymbol.blank :: leftRev)
              rw [codePrefixParserNormalizer_replicate_append_self
                (some MachineCodeSymbol.blank) blanks leftRev] at htail
              simpa [List.append_assoc] using htail)
  have hrestore :=
    codePrefixParserNormalizerMachine_computes_findCount_done_restoreForward
      blanks prefixLeft suffix
  have hforward :=
    codePrefixParserNormalizerMachine_computes_restoreForward_ticks
      blanks (some MachineCodeSymbol.done :: prefixLeft) suffix
  exact
    TuringMachine.computes_trans
      (by simpa using hscan (none :: prefixLeft))
      (TuringMachine.computes_trans hrestore
        (by simpa using hforward))

theorem codePrefixParserNormalizerRestoredTicksLeft_eq
    (ticks : Nat) (leftRev : List (Option MachineCodeSymbol)) :
    codePrefixParserNormalizerRestoredTicksLeft ticks leftRev =
      List.append
        (List.replicate ticks (some MachineCodeSymbol.tick))
        leftRev := by
  induction ticks generalizing leftRev with
  | zero =>
      rfl
  | succ ticks ih =>
      simpa [codePrefixParserNormalizerRestoredTicksLeft, ih,
        List.replicate_succ, List.append_assoc] using
        (codePrefixParserNormalizer_replicate_append_self
          (some MachineCodeSymbol.tick) ticks leftRev)

theorem codePrefixParserNormalizerMachine_step_seekCountDone_saved_done
    (saved : Option MachineCodeSymbol)
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state :=
          CodePrefixParserNormalizerState.seekCountDone
            (TransitionListParserMarker.saved saved)
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.done :: suffix) }
      { state := CodePrefixParserNormalizerState.seekMarker saved
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.done :: leftRev) suffix } :=
  codePrefixParserNormalizerMachine_step_keep_right
    (by simp [codePrefixParserNormalizerMachine,
      codePrefixParserNormalizerKeep])

theorem codePrefixParserNormalizerMachine_computes_seekCountDone_saved
    (saved : Option MachineCodeSymbol)
    (leftRev : List (Option MachineCodeSymbol)) (count : Nat)
    (tokens : Word MachineCodeSymbol) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state :=
          CodePrefixParserNormalizerState.seekCountDone
            (TransitionListParserMarker.saved saved)
        tape :=
          transitionListParserOptionTape leftRev
            ((MachineDescription.encodeNatAppend count tokens).map some) }
      { state := CodePrefixParserNormalizerState.seekMarker saved
        tape :=
          transitionListParserOptionTape
            (List.append
              ((MachineDescription.encodeNat count).reverse.map some)
              leftRev)
            (tokens.map some) } :=
  codePrefixParserNormalizerMachine_computes_nat_option
    (codePrefixParserNormalizerMachine_step_seekCountDone_saved_tick saved)
    (codePrefixParserNormalizerMachine_step_seekCountDone_saved_done saved)
    leftRev count tokens

theorem codePrefixParserNormalizerMachine_step_seekMarker_nonHeader
    (saved : Option MachineCodeSymbol)
    {symbol : MachineCodeSymbol}
    (hsymbol : symbol ≠ MachineCodeSymbol.header)
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.seekMarker saved
        tape :=
          transitionListParserOptionTape leftRev
            (some symbol :: suffix) }
      { state := CodePrefixParserNormalizerState.seekMarker saved
        tape :=
          transitionListParserOptionTape
            (some symbol :: leftRev) suffix } :=
  codePrefixParserNormalizerMachine_step_keep_right
    (by
      cases symbol <;>
        simp [codePrefixParserNormalizerMachine,
          codePrefixParserNormalizerKeep] at hsymbol ⊢)

theorem codePrefixParserNormalizerMachine_seekMarker_scan_noHeader
    (saved : Option MachineCodeSymbol)
    (pre : Word MachineCodeSymbol)
    (hpre : transitionListParserNoHeader pre)
    (leftRev : List (Option MachineCodeSymbol))
    (suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.seekMarker saved
        tape :=
          transitionListParserOptionTape leftRev
            (List.append (pre.map some)
              (some MachineCodeSymbol.header :: suffix)) }
      { state := CodePrefixParserNormalizerState.seekMarker saved
        tape :=
          transitionListParserOptionTape
            (List.append (pre.reverse.map some) leftRev)
            (some MachineCodeSymbol.header :: suffix) } := by
  induction pre generalizing leftRev with
  | nil =>
      exact TuringMachine.Computes.refl _
  | cons symbol rest ih =>
      have hsymbol : symbol ≠ MachineCodeSymbol.header :=
        hpre symbol (by simp)
      have hrest : transitionListParserNoHeader rest := by
        intro head hmem
        exact hpre head (by simp [hmem])
      have htail := ih hrest (some symbol :: leftRev)
      exact
        TuringMachine.Computes.step
          (by
            simpa [List.append_assoc] using
              codePrefixParserNormalizerMachine_step_seekMarker_nonHeader
                saved hsymbol leftRev
                (List.append (rest.map some)
                  (some MachineCodeSymbol.header :: suffix)))
          (by
            simpa [List.map_append, List.append_assoc] using htail)

theorem codePrefixParserNormalizerMachine_step_seekMarker_header
    (saved : Option MachineCodeSymbol)
    (leftTail suffix : List (Option MachineCodeSymbol))
    (leftHead : Option MachineCodeSymbol) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.seekMarker saved
        tape :=
          transitionListParserOptionTape
            (leftHead :: leftTail)
            (some MachineCodeSymbol.header :: suffix) }
      { state := CodePrefixParserNormalizerState.enterMarkedPosition
        tape :=
          transitionListParserOptionTape leftTail
            (leftHead :: saved :: suffix) } :=
  codePrefixParserNormalizerMachine_step_write_left_nonempty
    (by simp [codePrefixParserNormalizerMachine,
      codePrefixParserNormalizerKeep])

theorem codePrefixParserNormalizerMachine_step_enterMarkedPosition
    (leftRev suffix : List (Option MachineCodeSymbol))
    (cell : Option MachineCodeSymbol) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.enterMarkedPosition
        tape :=
          transitionListParserOptionTape leftRev
            (cell :: suffix) }
      { state := CodePrefixParserNormalizerState.needTransition
        tape :=
          transitionListParserOptionTape (cell :: leftRev) suffix } :=
  codePrefixParserNormalizerMachine_step_keep_right
    (by
      cases cell <;>
        simp [codePrefixParserNormalizerMachine,
          codePrefixParserNormalizerKeep])

def codePrefixParserNormalizerMarkedContextLeft
    (prefixLeft : List (Option MachineCodeSymbol))
    (blanks count : Nat)
    (pre : Word MachineCodeSymbol) :
    List (Option MachineCodeSymbol) :=
  List.append
    ((List.append
      (List.append
        (List.replicate blanks MachineCodeSymbol.blank)
        (MachineDescription.encodeNat count))
      pre).reverse.map some)
    (none :: prefixLeft)

def codePrefixParserNormalizerRestoredTail
    (pre input : Word MachineCodeSymbol) :
    List (Option MachineCodeSymbol) :=
  List.append (pre.map some)
    (match input with
    | [] => [none]
    | symbol :: suffix => some symbol :: suffix.map some)

theorem codePrefixParserNormalizerRestoredTail_normalized
    (pre input : Word MachineCodeSymbol) :
    (codePrefixParserNormalizerRestoredTail pre input).filterMap
        (fun cell => cell) =
      List.append pre input := by
  cases input <;>
    simp [codePrefixParserNormalizerRestoredTail,
      codePrefixParserNormalizer_filterMap_comp_some,
      List.filterMap_append]

theorem codePrefixParserNormalizerMachine_computes_markPosition_context_to_needTransition_saved
    (prefixLeft : List (Option MachineCodeSymbol))
    (blanks count : Nat)
    (pre : Word MachineCodeSymbol)
    (hpre : transitionListParserNoHeader pre)
    (saved : Option MachineCodeSymbol) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.markPosition
        tape :=
          transitionListParserOptionTape
            (codePrefixParserNormalizerMarkedContextLeft
              prefixLeft blanks (count + 1) pre)
            (saved :: suffix.map some) }
      { state := CodePrefixParserNormalizerState.needTransition
        tape :=
          transitionListParserOptionTape
            (codePrefixParserNormalizerMarkedContextLeft
              prefixLeft (blanks + 1) count pre)
            (saved :: suffix.map some) } := by
  let leftNormal : Word MachineCodeSymbol :=
    List.append
      (List.append
        (List.replicate blanks MachineCodeSymbol.blank)
        (MachineDescription.encodeNat (count + 1)))
      pre
  let countTail : Word MachineCodeSymbol :=
    List.append pre (MachineCodeSymbol.header :: suffix)
  let countLeft : List (Option MachineCodeSymbol) :=
    List.append
      ((MachineDescription.encodeNat count).reverse.map some)
      (some MachineCodeSymbol.blank ::
        List.append
          (List.replicate blanks (some MachineCodeSymbol.blank))
          (none :: prefixLeft))
  let targetLeft : List (Option MachineCodeSymbol) :=
    codePrefixParserNormalizerMarkedContextLeft
      prefixLeft (blanks + 1) count pre
  have hrevNonempty : leftNormal.reverse ≠ [] := by
    simp [leftNormal, MachineDescription.encodeNat]
  cases hrev : leftNormal.reverse with
  | nil =>
      exact False.elim (hrevNonempty hrev)
  | cons current leftSymbols =>
      have hleft :
          leftNormal = List.append leftSymbols.reverse [current] := by
        have h := congrArg List.reverse hrev
        simpa using h
      have hprefix :
          List.append (leftSymbols.reverse.map some) [some current] =
            leftNormal.map some := by
        have hmap :=
          congrArg (fun xs : List MachineCodeSymbol => xs.map some)
            hleft
        simpa [List.map_append, List.map_reverse,
          List.append_assoc] using hmap.symm
      have hleftStart :
          codePrefixParserNormalizerMarkedContextLeft
              prefixLeft blanks (count + 1) pre =
            some current ::
              List.append (leftSymbols.map some) (none :: prefixLeft) := by
        have hmapRev :
            List.append (leftNormal.reverse.map some)
                (none :: prefixLeft) =
              some current ::
                List.append (leftSymbols.map some)
                  (none :: prefixLeft) := by
          simp [hrev]
        simpa [codePrefixParserNormalizerMarkedContextLeft,
          leftNormal, List.append_assoc] using hmapRev
      have hreturn :
          TuringMachine.Computes codePrefixParserNormalizerMachine
            { state := CodePrefixParserNormalizerState.markPosition
              tape :=
                transitionListParserOptionTape
                  (codePrefixParserNormalizerMarkedContextLeft
                    prefixLeft blanks (count + 1) pre)
                  (saved :: suffix.map some) }
            { state :=
                CodePrefixParserNormalizerState.findCount
                  (TransitionListParserMarker.saved saved)
              tape :=
                transitionListParserOptionTape (none :: prefixLeft)
                  (List.append (leftNormal.map some)
                    (some MachineCodeSymbol.header ::
                      suffix.map some)) } := by
        have hrun :=
          codePrefixParserNormalizerMachine_markPosition_returnLeft_toBoundary
            saved leftSymbols prefixLeft current
            (suffix.map some)
        have htargetRest :
            List.append (List.map some leftSymbols).reverse
                (some current ::
                  some MachineCodeSymbol.header ::
                    suffix.map some) =
              List.append (leftNormal.map some)
                (some MachineCodeSymbol.header ::
                  suffix.map some) := by
          calc
            List.append (List.map some leftSymbols).reverse
                (some current ::
                  some MachineCodeSymbol.header ::
                    suffix.map some)
                =
              List.append
                (List.append (List.map some leftSymbols).reverse
                  [some current])
                (some MachineCodeSymbol.header ::
                  suffix.map some) := by
                  simp [List.append_assoc]
            _ =
              List.append (leftNormal.map some)
                (some MachineCodeSymbol.header ::
                  suffix.map some) := by
                  simpa [List.map_reverse] using
                    congrArg
                      (fun xs => List.append xs
                        (some MachineCodeSymbol.header ::
                          suffix.map some))
                      hprefix
        rw [hleftStart]
        rw [← htargetRest]
        simpa [List.map_reverse] using hrun
      have hfind :
          TuringMachine.Computes codePrefixParserNormalizerMachine
            { state :=
                CodePrefixParserNormalizerState.findCount
                  (TransitionListParserMarker.saved saved)
              tape :=
                transitionListParserOptionTape (none :: prefixLeft)
                  (List.append (leftNormal.map some)
                    (some MachineCodeSymbol.header ::
                      suffix.map some)) }
            { state :=
                CodePrefixParserNormalizerState.seekCountDone
                  (TransitionListParserMarker.saved saved)
              tape :=
                transitionListParserOptionTape
                  (some MachineCodeSymbol.blank ::
                    List.append
                      (List.replicate blanks
                        (some MachineCodeSymbol.blank))
                      (none :: prefixLeft))
                  ((MachineDescription.encodeNatAppend count
                    countTail).map some) } := by
        have hrun :=
          codePrefixParserNormalizerMachine_computes_findCount_blanks_tick
            (TransitionListParserMarker.saved saved)
            blanks (none :: prefixLeft)
            ((MachineDescription.encodeNatAppend count countTail).map some)
        simpa [leftNormal, countTail, MachineDescription.encodeNat,
          MachineDescription.encodeNatAppend, List.map_append,
          List.map_replicate, List.append_assoc] using hrun
      have hseek :
          TuringMachine.Computes codePrefixParserNormalizerMachine
            { state :=
                CodePrefixParserNormalizerState.seekCountDone
                  (TransitionListParserMarker.saved saved)
              tape :=
                transitionListParserOptionTape
                  (some MachineCodeSymbol.blank ::
                    List.append
                      (List.replicate blanks
                        (some MachineCodeSymbol.blank))
                      (none :: prefixLeft))
                  ((MachineDescription.encodeNatAppend count
                    countTail).map some) }
            { state :=
                CodePrefixParserNormalizerState.seekMarker saved
              tape :=
                transitionListParserOptionTape countLeft
                  (countTail.map some) } := by
        simpa [countLeft] using
          codePrefixParserNormalizerMachine_computes_seekCountDone_saved
            saved
            (some MachineCodeSymbol.blank ::
              List.append
                (List.replicate blanks (some MachineCodeSymbol.blank))
                (none :: prefixLeft))
            count countTail
      have hscan :
          TuringMachine.Computes codePrefixParserNormalizerMachine
            { state :=
                CodePrefixParserNormalizerState.seekMarker saved
              tape :=
                transitionListParserOptionTape countLeft
                  (countTail.map some) }
            { state :=
                CodePrefixParserNormalizerState.seekMarker saved
              tape :=
                transitionListParserOptionTape targetLeft
                  (some MachineCodeSymbol.header ::
                    suffix.map some) } := by
        have hrun :=
          codePrefixParserNormalizerMachine_seekMarker_scan_noHeader
            saved pre hpre countLeft
            (suffix.map some)
        have hblank :
            some MachineCodeSymbol.blank ::
                List.append
                  (List.replicate blanks
                    (some MachineCodeSymbol.blank))
                  (none :: prefixLeft) =
              List.append
                (List.replicate blanks
                  (some MachineCodeSymbol.blank))
                  (some MachineCodeSymbol.blank ::
                  none :: prefixLeft) := by
          calc
            some MachineCodeSymbol.blank ::
                List.append
                  (List.replicate blanks
                    (some MachineCodeSymbol.blank))
                  (none :: prefixLeft)
                =
              List.append
                (List.replicate (blanks + 1)
                  (some MachineCodeSymbol.blank))
                (none :: prefixLeft) := by
                simp [List.replicate_succ]
            _ =
              List.append
                (List.replicate blanks
                  (some MachineCodeSymbol.blank))
                (some MachineCodeSymbol.blank ::
                  none :: prefixLeft) := by
                exact
                  (codePrefixParserNormalizer_replicate_append_self
                    (some MachineCodeSymbol.blank) blanks
                    (none :: prefixLeft)).symm
        have htargetLeft :
            targetLeft =
              List.append (pre.reverse.map some)
                (List.append
                  ((MachineDescription.encodeNat count).reverse.map some)
                  (some MachineCodeSymbol.blank ::
                    List.append
                      (List.replicate blanks
                        (some MachineCodeSymbol.blank))
                      (none :: prefixLeft))) := by
          simpa [targetLeft, codePrefixParserNormalizerMarkedContextLeft,
            List.reverse_append, List.map_append, List.map_reverse,
            List.map_replicate, List.replicate_succ,
            List.append_assoc] using hblank.symm
        rw [htargetLeft]
        simpa [countTail, countLeft, List.map_append,
          List.append_assoc] using hrun
      have htargetNonempty : targetLeft ≠ [] := by
        simp [targetLeft, codePrefixParserNormalizerMarkedContextLeft]
      cases htarget : targetLeft with
      | nil =>
          exact False.elim (htargetNonempty htarget)
      | cons leftHead leftTail =>
          have hheader :
              TuringMachine.Step codePrefixParserNormalizerMachine
                { state := CodePrefixParserNormalizerState.seekMarker saved
                  tape :=
                    transitionListParserOptionTape targetLeft
                      (some MachineCodeSymbol.header ::
                        suffix.map some) }
                { state :=
                    CodePrefixParserNormalizerState.enterMarkedPosition
                  tape :=
                    transitionListParserOptionTape leftTail
                      (leftHead :: saved :: suffix.map some) } := by
            rw [htarget]
            exact
              codePrefixParserNormalizerMachine_step_seekMarker_header
                saved leftTail (suffix.map some) leftHead
          have henter :
              TuringMachine.Step codePrefixParserNormalizerMachine
                { state :=
                    CodePrefixParserNormalizerState.enterMarkedPosition
                  tape :=
                    transitionListParserOptionTape leftTail
                      (leftHead :: saved :: suffix.map some) }
                { state := CodePrefixParserNormalizerState.needTransition
                  tape :=
                    transitionListParserOptionTape targetLeft
                      (saved :: suffix.map some) } := by
            rw [htarget]
            exact
              codePrefixParserNormalizerMachine_step_enterMarkedPosition
                leftTail (saved :: suffix.map some) leftHead
          exact
            TuringMachine.computes_trans hreturn
              (TuringMachine.computes_trans hfind
                (TuringMachine.computes_trans hseek
                  (TuringMachine.computes_trans hscan
                      (TuringMachine.Computes.step hheader
                        (TuringMachine.Computes.step henter
                          (TuringMachine.Computes.refl _))))))

theorem codePrefixParserNormalizerMachine_computes_markPosition_context_to_needTransition
    (prefixLeft : List (Option MachineCodeSymbol))
    (blanks count : Nat)
    (pre : Word MachineCodeSymbol)
    (hpre : transitionListParserNoHeader pre)
    (symbol : MachineCodeSymbol) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.markPosition
        tape :=
          transitionListParserOptionTape
            (codePrefixParserNormalizerMarkedContextLeft
              prefixLeft blanks (count + 1) pre)
            ((symbol :: suffix).map some) }
      { state := CodePrefixParserNormalizerState.needTransition
        tape :=
          transitionListParserOptionTape
            (codePrefixParserNormalizerMarkedContextLeft
              prefixLeft (blanks + 1) count pre)
            ((symbol :: suffix).map some) } := by
  simpa using
    codePrefixParserNormalizerMachine_computes_markPosition_context_to_needTransition_saved
      prefixLeft blanks count pre hpre (some symbol) suffix

theorem codePrefixParserNormalizerMachine_computes_markPosition_context_empty_to_needTransition
    (prefixLeft : List (Option MachineCodeSymbol))
    (blanks count : Nat)
    (pre : Word MachineCodeSymbol)
    (hpre : transitionListParserNoHeader pre) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.markPosition
        tape :=
          transitionListParserOptionTape
            (codePrefixParserNormalizerMarkedContextLeft
              prefixLeft blanks (count + 1) pre)
            [] }
      { state := CodePrefixParserNormalizerState.needTransition
        tape :=
          transitionListParserOptionTape
            (codePrefixParserNormalizerMarkedContextLeft
              prefixLeft (blanks + 1) count pre)
            [none] } := by
  simpa using
    codePrefixParserNormalizerMachine_computes_markPosition_context_to_needTransition_saved
      prefixLeft blanks count pre hpre none []

theorem codePrefixParserNormalizerMachine_computes_markPosition_context_zero_halt
    (prefixLeft : List (Option MachineCodeSymbol))
    (blanks : Nat)
    (pre input : Word MachineCodeSymbol)
    (hpre : transitionListParserNoHeader pre) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.markPosition
        tape :=
          transitionListParserOptionTape
            (codePrefixParserNormalizerMarkedContextLeft
              prefixLeft blanks 0 pre)
            (input.map some) }
      { state := CodePrefixParserNormalizerState.halt
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.done ::
              codePrefixParserNormalizerRestoredTicksLeft blanks
                (some MachineCodeSymbol.done :: prefixLeft))
            (codePrefixParserNormalizerRestoredTail pre input) } := by
  let leftNormal : Word MachineCodeSymbol :=
    List.append
      (List.append
        (List.replicate blanks MachineCodeSymbol.blank)
        (MachineDescription.encodeNat 0))
      pre
  have hrevNonempty : leftNormal.reverse ≠ [] := by
    simp [leftNormal, MachineDescription.encodeNat]
  cases hrev : leftNormal.reverse with
  | nil =>
      exact False.elim (hrevNonempty hrev)
  | cons current leftSymbols =>
      have hleft :
          leftNormal = List.append leftSymbols.reverse [current] := by
        have h := congrArg List.reverse hrev
        simpa using h
      have hprefix :
          List.append (List.map some leftSymbols).reverse [some current] =
            leftNormal.map some := by
        have hmap :=
          congrArg (fun xs : List MachineCodeSymbol => xs.map some)
            hleft
        simpa [List.map_append, List.map_reverse,
          List.append_assoc] using hmap.symm
      have hleftStart :
          codePrefixParserNormalizerMarkedContextLeft
              prefixLeft blanks 0 pre =
            some current ::
              List.append (leftSymbols.map some) (none :: prefixLeft) := by
        have hmapRev :
            List.append (leftNormal.reverse.map some)
                (none :: prefixLeft) =
              some current ::
                List.append (leftSymbols.map some)
                  (none :: prefixLeft) := by
          simp [hrev]
        simpa [codePrefixParserNormalizerMarkedContextLeft,
          leftNormal, List.append_assoc] using hmapRev
      cases input with
      | nil =>
          have hreturn :
              TuringMachine.Computes codePrefixParserNormalizerMachine
                { state := CodePrefixParserNormalizerState.markPosition
                  tape :=
                    transitionListParserOptionTape
                      (codePrefixParserNormalizerMarkedContextLeft
                        prefixLeft blanks 0 pre)
                      [] }
                { state :=
                    CodePrefixParserNormalizerState.findCount
                      (TransitionListParserMarker.saved none)
                  tape :=
                    transitionListParserOptionTape (none :: prefixLeft)
                      (List.append (leftNormal.map some)
                        [some MachineCodeSymbol.header]) } := by
            have hrun :=
              codePrefixParserNormalizerMachine_markPosition_empty_returnLeft_toBoundary
                leftSymbols prefixLeft current
            have htargetRest :
                List.append (List.map some leftSymbols).reverse
                    [some current, some MachineCodeSymbol.header] =
                  List.append (leftNormal.map some)
                    [some MachineCodeSymbol.header] := by
              calc
                List.append (List.map some leftSymbols).reverse
                    [some current, some MachineCodeSymbol.header]
                    =
                  List.append
                    (List.append (List.map some leftSymbols).reverse
                      [some current])
                    [some MachineCodeSymbol.header] := by
                    simp [List.append_assoc]
                _ =
                  List.append (leftNormal.map some)
                    [some MachineCodeSymbol.header] := by
                    simpa using
                      congrArg
                        (fun xs => List.append xs
                          [some MachineCodeSymbol.header])
                        hprefix
            rw [hleftStart]
            rw [← htargetRest]
            simpa [List.map_reverse] using hrun
          have hfind :
              TuringMachine.Computes codePrefixParserNormalizerMachine
                { state :=
                    CodePrefixParserNormalizerState.findCount
                      (TransitionListParserMarker.saved none)
                  tape :=
                    transitionListParserOptionTape (none :: prefixLeft)
                      (List.append (leftNormal.map some)
                        [some MachineCodeSymbol.header]) }
                { state := CodePrefixParserNormalizerState.restoreSeekMarker none
                  tape :=
                    transitionListParserOptionTape
                      (some MachineCodeSymbol.done ::
                        List.append
                          (List.replicate blanks
                            (some MachineCodeSymbol.blank))
                          (none :: prefixLeft))
                      (List.append (pre.map some)
                        [some MachineCodeSymbol.header]) } := by
            have hrun :=
              codePrefixParserNormalizerMachine_computes_findCount_saved_blanks_done
                none blanks (none :: prefixLeft)
                (List.append (pre.map some)
                  [some MachineCodeSymbol.header])
            simpa [leftNormal, MachineDescription.encodeNat,
              List.map_append, List.map_replicate,
              List.append_assoc] using hrun
          let scanLeft : List (Option MachineCodeSymbol) :=
            some MachineCodeSymbol.done ::
              List.append
                (List.replicate blanks
                  (some MachineCodeSymbol.blank))
                (none :: prefixLeft)
          have hscan :
              TuringMachine.Computes codePrefixParserNormalizerMachine
                { state := CodePrefixParserNormalizerState.restoreSeekMarker none
                  tape :=
                    transitionListParserOptionTape scanLeft
                      (List.append (pre.map some)
                        [some MachineCodeSymbol.header]) }
                { state := CodePrefixParserNormalizerState.restoreSeekMarker none
                  tape :=
                    transitionListParserOptionTape
                      (codePrefixParserNormalizerMarkedContextLeft
                        prefixLeft blanks 0 pre)
                      [some MachineCodeSymbol.header] } := by
            have hrun :=
              codePrefixParserNormalizerMachine_restoreSeekMarker_scan_noHeader
                none pre hpre scanLeft []
            have htargetLeft :
                codePrefixParserNormalizerMarkedContextLeft
                    prefixLeft blanks 0 pre =
                  List.append (pre.reverse.map some) scanLeft := by
              simp [scanLeft, codePrefixParserNormalizerMarkedContextLeft,
                MachineDescription.encodeNat, List.reverse_append,
                List.map_append, List.map_reverse, List.map_replicate,
                List.append_assoc]
            rw [htargetLeft]
            simpa [scanLeft, List.map_append, List.append_assoc] using hrun
          have hrestore :
              TuringMachine.Computes codePrefixParserNormalizerMachine
                { state := CodePrefixParserNormalizerState.restoreSeekMarker none
                  tape :=
                    transitionListParserOptionTape
                      (codePrefixParserNormalizerMarkedContextLeft
                        prefixLeft blanks 0 pre)
                      [some MachineCodeSymbol.header] }
                { state :=
                    CodePrefixParserNormalizerState.findCount
                      TransitionListParserMarker.initial
                  tape :=
                    transitionListParserOptionTape (none :: prefixLeft)
                      (List.append (leftNormal.map some) [none]) } := by
            have hrun :=
              codePrefixParserNormalizerMachine_restoreSeekMarker_toBoundary
                none leftSymbols prefixLeft current []
            have htargetRest :
                List.append (List.map some leftSymbols).reverse
                    [some current, none] =
                  List.append (leftNormal.map some) [none] := by
              calc
                List.append (List.map some leftSymbols).reverse
                    [some current, none]
                    =
                  List.append
                    (List.append (List.map some leftSymbols).reverse
                      [some current])
                    [none] := by
                    simp [List.append_assoc]
                _ =
                  List.append (leftNormal.map some) [none] := by
                    simpa using
                      congrArg
                        (fun xs => List.append xs [none])
                        hprefix
            rw [hleftStart]
            rw [← htargetRest]
            simpa [List.map_reverse] using hrun
          have hfinish :
              TuringMachine.Computes codePrefixParserNormalizerMachine
                { state :=
                    CodePrefixParserNormalizerState.findCount
                      TransitionListParserMarker.initial
                  tape :=
                    transitionListParserOptionTape (none :: prefixLeft)
                      (List.append (leftNormal.map some) [none]) }
                { state := CodePrefixParserNormalizerState.halt
                  tape :=
                    transitionListParserOptionTape
                      (some MachineCodeSymbol.done ::
                        codePrefixParserNormalizerRestoredTicksLeft blanks
                          (some MachineCodeSymbol.done :: prefixLeft))
                      (codePrefixParserNormalizerRestoredTail pre []) } := by
            have hrun :=
              codePrefixParserNormalizerMachine_computes_findCount_initial_blanks_done_halt
                blanks prefixLeft
                (codePrefixParserNormalizerRestoredTail pre [])
            simpa [leftNormal, MachineDescription.encodeNat,
              codePrefixParserNormalizerRestoredTail, List.map_append,
              List.map_replicate, List.append_assoc] using hrun
          exact
            TuringMachine.computes_trans hreturn
              (TuringMachine.computes_trans hfind
                (TuringMachine.computes_trans
                  (by simpa [scanLeft] using hscan)
                  (TuringMachine.computes_trans hrestore hfinish)))
      | cons symbol suffix =>
          have hreturn :
              TuringMachine.Computes codePrefixParserNormalizerMachine
                { state := CodePrefixParserNormalizerState.markPosition
                  tape :=
                    transitionListParserOptionTape
                      (codePrefixParserNormalizerMarkedContextLeft
                        prefixLeft blanks 0 pre)
                      (some symbol :: suffix.map some) }
                { state :=
                    CodePrefixParserNormalizerState.findCount
                      (TransitionListParserMarker.saved
                        (some symbol))
                  tape :=
                    transitionListParserOptionTape (none :: prefixLeft)
                      (List.append (leftNormal.map some)
                        (some MachineCodeSymbol.header ::
                          suffix.map some)) } := by
            have hrun :=
              codePrefixParserNormalizerMachine_markPosition_returnLeft_toBoundary
                (some symbol) leftSymbols prefixLeft current
                (suffix.map some)
            have htargetRest :
                List.append (List.map some leftSymbols).reverse
                    (some current ::
                      some MachineCodeSymbol.header ::
                        suffix.map some) =
                  List.append (leftNormal.map some)
                    (some MachineCodeSymbol.header ::
                      suffix.map some) := by
              calc
                List.append (List.map some leftSymbols).reverse
                    (some current ::
                      some MachineCodeSymbol.header ::
                        suffix.map some)
                    =
                  List.append
                    (List.append (List.map some leftSymbols).reverse
                      [some current])
                    (some MachineCodeSymbol.header ::
                      suffix.map some) := by
                    simp [List.append_assoc]
                _ =
                  List.append (leftNormal.map some)
                    (some MachineCodeSymbol.header ::
                      suffix.map some) := by
                    simpa using
                      congrArg
                        (fun xs => List.append xs
                          (some MachineCodeSymbol.header ::
                            suffix.map some))
                        hprefix
            rw [hleftStart]
            rw [← htargetRest]
            simpa [List.map_reverse] using hrun
          have hfind :
              TuringMachine.Computes codePrefixParserNormalizerMachine
                { state :=
                    CodePrefixParserNormalizerState.findCount
                      (TransitionListParserMarker.saved
                        (some symbol))
                  tape :=
                    transitionListParserOptionTape (none :: prefixLeft)
                      (List.append (leftNormal.map some)
                        (some MachineCodeSymbol.header ::
                          suffix.map some)) }
                { state :=
                    CodePrefixParserNormalizerState.restoreSeekMarker
                      (some symbol)
                  tape :=
                    transitionListParserOptionTape
                      (some MachineCodeSymbol.done ::
                        List.append
                          (List.replicate blanks
                            (some MachineCodeSymbol.blank))
                          (none :: prefixLeft))
                      (List.append (pre.map some)
                        (some MachineCodeSymbol.header ::
                          suffix.map some)) } := by
            have hrun :=
              codePrefixParserNormalizerMachine_computes_findCount_saved_blanks_done
                (some symbol) blanks (none :: prefixLeft)
                (List.append (pre.map some)
                  (some MachineCodeSymbol.header :: suffix.map some))
            simpa [leftNormal, MachineDescription.encodeNat,
              List.map_append, List.map_replicate,
              List.append_assoc] using hrun
          let scanLeft : List (Option MachineCodeSymbol) :=
            some MachineCodeSymbol.done ::
              List.append
                (List.replicate blanks
                  (some MachineCodeSymbol.blank))
                (none :: prefixLeft)
          have hscan :
              TuringMachine.Computes codePrefixParserNormalizerMachine
                { state :=
                    CodePrefixParserNormalizerState.restoreSeekMarker
                      (some symbol)
                  tape :=
                    transitionListParserOptionTape scanLeft
                      (List.append (pre.map some)
                        (some MachineCodeSymbol.header ::
                          suffix.map some)) }
                { state :=
                    CodePrefixParserNormalizerState.restoreSeekMarker
                      (some symbol)
                  tape :=
                    transitionListParserOptionTape
                      (codePrefixParserNormalizerMarkedContextLeft
                        prefixLeft blanks 0 pre)
                      (some MachineCodeSymbol.header ::
                        suffix.map some) } := by
            have hrun :=
              codePrefixParserNormalizerMachine_restoreSeekMarker_scan_noHeader
                (some symbol) pre hpre scanLeft suffix
            have htargetLeft :
                codePrefixParserNormalizerMarkedContextLeft
                    prefixLeft blanks 0 pre =
                  List.append (pre.reverse.map some) scanLeft := by
              simp [scanLeft, codePrefixParserNormalizerMarkedContextLeft,
                MachineDescription.encodeNat, List.reverse_append,
                List.map_append, List.map_reverse, List.map_replicate,
                List.append_assoc]
            rw [htargetLeft]
            simpa [scanLeft, List.map_append, List.append_assoc] using hrun
          have hrestore :
              TuringMachine.Computes codePrefixParserNormalizerMachine
                { state :=
                    CodePrefixParserNormalizerState.restoreSeekMarker
                      (some symbol)
                  tape :=
                    transitionListParserOptionTape
                      (codePrefixParserNormalizerMarkedContextLeft
                        prefixLeft blanks 0 pre)
                      (some MachineCodeSymbol.header ::
                        suffix.map some) }
                { state :=
                    CodePrefixParserNormalizerState.findCount
                      TransitionListParserMarker.initial
                  tape :=
                    transitionListParserOptionTape (none :: prefixLeft)
                      (List.append (leftNormal.map some)
                        (some symbol :: suffix.map some)) } := by
            have hrun :=
              codePrefixParserNormalizerMachine_restoreSeekMarker_toBoundary
                (some symbol) leftSymbols prefixLeft current
                (suffix.map some)
            have htargetRest :
                List.append (List.map some leftSymbols).reverse
                    (some current ::
                      some symbol :: suffix.map some) =
                  List.append (leftNormal.map some)
                    (some symbol :: suffix.map some) := by
              calc
                List.append (List.map some leftSymbols).reverse
                    (some current ::
                      some symbol :: suffix.map some)
                    =
                  List.append
                    (List.append (List.map some leftSymbols).reverse
                      [some current])
                    (some symbol :: suffix.map some) := by
                    simp [List.append_assoc]
                _ =
                  List.append (leftNormal.map some)
                    (some symbol :: suffix.map some) := by
                    simpa using
                      congrArg
                        (fun xs => List.append xs
                          (some symbol :: suffix.map some))
                        hprefix
            rw [hleftStart]
            rw [← htargetRest]
            simpa [List.map_reverse] using hrun
          have hfinish :
              TuringMachine.Computes codePrefixParserNormalizerMachine
                { state :=
                    CodePrefixParserNormalizerState.findCount
                      TransitionListParserMarker.initial
                  tape :=
                    transitionListParserOptionTape (none :: prefixLeft)
                      (List.append (leftNormal.map some)
                        (some symbol :: suffix.map some)) }
                { state := CodePrefixParserNormalizerState.halt
                  tape :=
                    transitionListParserOptionTape
                      (some MachineCodeSymbol.done ::
                        codePrefixParserNormalizerRestoredTicksLeft blanks
                          (some MachineCodeSymbol.done :: prefixLeft))
                      (codePrefixParserNormalizerRestoredTail pre
                        (symbol :: suffix)) } := by
            have hrun :=
              codePrefixParserNormalizerMachine_computes_findCount_initial_blanks_done_halt
                blanks prefixLeft
                (codePrefixParserNormalizerRestoredTail pre
                  (symbol :: suffix))
            simpa [leftNormal, MachineDescription.encodeNat,
              codePrefixParserNormalizerRestoredTail, List.map_append,
              List.map_replicate, List.append_assoc] using hrun
          exact
            TuringMachine.computes_trans hreturn
              (TuringMachine.computes_trans hfind
                (TuringMachine.computes_trans
                  (by simpa [scanLeft] using hscan)
                  (TuringMachine.computes_trans hrestore hfinish)))

theorem codePrefixParserNormalizerMachine_computes_markPosition_context_halt
    (prefixLeft : List (Option MachineCodeSymbol))
    (blanks : Nat)
    (pre : Word MachineCodeSymbol)
    (rest : List TransitionDescription)
    (input : Word MachineCodeSymbol)
    (hpre : transitionListParserNoHeader pre) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.markPosition
        tape :=
          transitionListParserOptionTape
            (codePrefixParserNormalizerMarkedContextLeft
              prefixLeft blanks rest.length pre)
            ((MachineDescription.encodeTransitionsAppend rest input).map
              some) }
      { state := CodePrefixParserNormalizerState.halt
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.done ::
              codePrefixParserNormalizerRestoredTicksLeft
                (blanks + rest.length)
                (some MachineCodeSymbol.done :: prefixLeft))
            (codePrefixParserNormalizerRestoredTail
              (List.append pre
                (MachineDescription.encodeTransitions rest))
              input) } := by
  induction rest generalizing blanks pre with
  | nil =>
      simpa [MachineDescription.encodeTransitions,
        MachineDescription.encodeTransitionsAppend] using
        codePrefixParserNormalizerMachine_computes_markPosition_context_zero_halt
          prefixLeft blanks pre input hpre
  | cons transition rest ih =>
      let afterTransition : Word MachineCodeSymbol :=
        MachineDescription.encodeNatAppend transition.source
          (MachineDescription.encodeCellAppend transition.read
            (MachineDescription.encodeCellAppend transition.write
              (MachineDescription.encodeDirectionAppend transition.move
                (MachineDescription.encodeNatAppend transition.target
                  (MachineDescription.encodeTransitionsAppend rest input)))))
      have htokens :
          MachineDescription.encodeTransitionsAppend
              (transition :: rest) input =
            MachineCodeSymbol.transition :: afterTransition := by
        simp [afterTransition,
          MachineDescription.encodeTransitionsAppend,
          MachineDescription.encodeTransitionAppend]
      have hstep :=
        codePrefixParserNormalizerMachine_computes_markPosition_context_to_needTransition
          prefixLeft blanks rest.length pre hpre
          MachineCodeSymbol.transition afterTransition
      have hparse :=
        codePrefixParserNormalizerMachine_computes_transition
          transition
          (codePrefixParserNormalizerMarkedContextLeft
            prefixLeft (blanks + 1) rest.length pre)
          (MachineDescription.encodeTransitionsAppend rest input)
      have hpre' :
          transitionListParserNoHeader
            (List.append pre
              (MachineDescription.encodeTransition transition)) :=
        transitionListParserNoHeader_append hpre
          (by
            simpa [MachineDescription.encodeTransition] using
              transitionListParser_encodeTransitionAppend_noHeader
                transition (suffix := []) (by
                  intro symbol hmem
                  simp at hmem))
      have htail :=
        ih (blanks + 1)
          (List.append pre
            (MachineDescription.encodeTransition transition))
          hpre'
      have hparse' :
          TuringMachine.Computes codePrefixParserNormalizerMachine
            { state := CodePrefixParserNormalizerState.needTransition
              tape :=
                transitionListParserOptionTape
                  (codePrefixParserNormalizerMarkedContextLeft
                    prefixLeft (blanks + 1) rest.length pre)
                  ((MachineDescription.encodeTransitionsAppend
                    (transition :: rest) input).map some) }
            { state := CodePrefixParserNormalizerState.markPosition
              tape :=
                transitionListParserOptionTape
                  (codePrefixParserNormalizerMarkedContextLeft
                    prefixLeft (blanks + 1) rest.length
                    (List.append pre
                      (MachineDescription.encodeTransition transition)))
                  ((MachineDescription.encodeTransitionsAppend rest input).map
                    some) } := by
        simpa [codePrefixParserNormalizerMarkedContextLeft,
          MachineDescription.encodeTransitionsAppend,
          MachineDescription.encodeTransition,
          MachineDescription.encodeTransitionAppend,
          MachineDescription.encodeNatAppend,
          MachineDescription.encodeCellAppend,
          MachineDescription.encodeDirectionAppend,
          List.reverse_append, List.map_append, List.map_reverse,
          List.map_replicate, List.append_assoc] using hparse
      exact
        TuringMachine.computes_trans
          (by simpa [htokens] using hstep)
          (TuringMachine.computes_trans hparse'
            (by
              simpa [MachineDescription.encodeTransitions,
                MachineDescription.encodeTransitionsAppend,
                MachineDescription.encodeTransition,
                MachineDescription.encodeTransitionAppend,
                MachineDescription.encodeNatAppend,
                MachineDescription.encodeCellAppend,
                MachineDescription.encodeDirectionAppend,
                  List.append_assoc, Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm] using htail))

theorem codePrefixParserNormalizerMachine_haltsFrom_markPosition_context_inv
    (prefixLeft : List (Option MachineCodeSymbol))
    (count : Nat) :
    forall (blanks : Nat) (pre tokens : Word MachineCodeSymbol),
      transitionListParserNoHeader pre ->
      TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
        { state := CodePrefixParserNormalizerState.markPosition
          tape :=
            transitionListParserOptionTape
              (codePrefixParserNormalizerMarkedContextLeft
                prefixLeft blanks count pre)
              (tokens.map some) } ->
      exists transitions : List TransitionDescription,
      exists suffix : Word MachineCodeSymbol,
        count = transitions.length ∧
          tokens =
            MachineDescription.encodeTransitionsAppend transitions suffix := by
  induction count with
  | zero =>
      intro blanks pre tokens hpre h
      exact ⟨[], tokens, rfl, rfl⟩
  | succ count ih =>
      intro blanks pre tokens hpre h
      cases tokens with
      | nil =>
          have hneed :
              TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
                { state := CodePrefixParserNormalizerState.needTransition
                  tape :=
                    transitionListParserOptionTape
                      (codePrefixParserNormalizerMarkedContextLeft
                        prefixLeft (blanks + 1) count pre)
                      [none] } :=
            codePrefixParserNormalizerMachine_halts_from_of_computes_suffix
              (codePrefixParserNormalizerMachine_computes_markPosition_context_empty_to_needTransition
                prefixLeft blanks count pre hpre)
              h
          exact False.elim
            ((codePrefixParserNormalizerMachine_not_haltsFrom_needTransition_none
                (codePrefixParserNormalizerMarkedContextLeft
                  prefixLeft (blanks + 1) count pre)
                [])
              hneed)
      | cons symbol rest =>
          have hneed :
              TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
                { state := CodePrefixParserNormalizerState.needTransition
                  tape :=
                    transitionListParserOptionTape
                      (codePrefixParserNormalizerMarkedContextLeft
                        prefixLeft (blanks + 1) count pre)
                      ((symbol :: rest).map some) } :=
            codePrefixParserNormalizerMachine_halts_from_of_computes_suffix
              (codePrefixParserNormalizerMachine_computes_markPosition_context_to_needTransition
                prefixLeft blanks count pre hpre symbol rest)
              h
          rcases
              codePrefixParserNormalizerMachine_haltsFrom_needTransition_inv
                hneed with
            ⟨t, restTokens, htokens, hmarkFrom⟩
          have hpre' :
              transitionListParserNoHeader
                (List.append pre
                  (MachineDescription.encodeTransition t)) :=
            transitionListParserNoHeader_append hpre
              (by
                simpa [MachineDescription.encodeTransition] using
                  transitionListParser_encodeTransitionAppend_noHeader
                    t (suffix := []) (by
                      intro symbol hmem
                      simp at hmem))
          have hmarkContext :
              TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
                { state := CodePrefixParserNormalizerState.markPosition
                  tape :=
                    transitionListParserOptionTape
                      (codePrefixParserNormalizerMarkedContextLeft
                        prefixLeft (blanks + 1) count
                        (List.append pre
                          (MachineDescription.encodeTransition t)))
                      (restTokens.map some) } := by
            simpa [codePrefixParserNormalizerMarkedContextLeft,
              MachineDescription.encodeTransition,
              MachineDescription.encodeTransitionAppend,
              MachineDescription.encodeNatAppend,
              MachineDescription.encodeCellAppend,
              MachineDescription.encodeDirectionAppend,
              List.reverse_append, List.map_append, List.map_reverse,
              List.map_replicate, List.append_assoc] using hmarkFrom
          rcases
              ih (blanks + 1)
                (List.append pre
                  (MachineDescription.encodeTransition t))
                restTokens hpre' hmarkContext with
            ⟨transitions, suffix, hcount, hrestTokens⟩
          refine ⟨t :: transitions, suffix, ?_, ?_⟩
          · simp [hcount]
          · simp [MachineDescription.encodeTransitionsAppend,
              htokens, hrestTokens]

theorem codePrefixParserNormalizerMachine_haltsFrom_findInitialCount_decodeTransitions
    (prefixLeft : List (Option MachineCodeSymbol))
    {transitionBlock : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
        { state := CodePrefixParserNormalizerState.findInitialCount
          tape :=
            transitionListParserOptionTape (none :: prefixLeft)
              (transitionBlock.map some) }) :
    exists transitionCount : Nat,
    exists rest : Word MachineCodeSymbol,
    exists transitions : List TransitionDescription,
    exists input : Word MachineCodeSymbol,
      transitionBlock =
          MachineDescription.encodeNatAppend transitionCount rest ∧
        MachineDescription.decodeTransitions transitionCount rest =
          some (transitions, input) := by
  cases transitionBlock with
  | nil =>
      exact False.elim
        ((codePrefixParserNormalizerMachine_not_haltsFrom_of_stuck
            (by simp [TuringMachine.Halted,
              codePrefixParserNormalizerMachine])
            (by
              intro d hstep
              cases hstep with
              | mk htransition =>
                  simp [codePrefixParserNormalizerMachine,
                    transitionListParserOptionTape, Tape.read] at htransition))
          h)
  | cons symbol rest =>
      have hstuck
          (hsymbol :
            symbol ≠ MachineCodeSymbol.tick ∧
              symbol ≠ MachineCodeSymbol.done) :
          ¬ TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
            { state := CodePrefixParserNormalizerState.findInitialCount
              tape :=
                transitionListParserOptionTape (none :: prefixLeft)
                  ((symbol :: rest).map some) } := by
        refine codePrefixParserNormalizerMachine_not_haltsFrom_of_stuck ?_ ?_
        · simp [TuringMachine.Halted, codePrefixParserNormalizerMachine]
        · intro d hstep
          cases hstep with
          | mk htransition =>
              cases symbol <;>
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read] at hsymbol htransition
      cases symbol with
      | done =>
          exact ⟨0, rest, [], rest, rfl, rfl⟩
      | tick =>
          have hseek :
              TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
                { state :=
                    CodePrefixParserNormalizerState.seekCountDone
                      TransitionListParserMarker.initial
                  tape :=
                    transitionListParserOptionTape
                      (some MachineCodeSymbol.blank :: none :: prefixLeft)
                      (rest.map some) } :=
            codePrefixParserNormalizerMachine_halts_from_of_computes_suffix
              (TuringMachine.computes_of_step
                (codePrefixParserNormalizerMachine_step_findInitialCount_tick
                  (none :: prefixLeft) (rest.map some)))
              h
          rcases
              codePrefixParserNormalizerMachine_haltsFrom_seekCountDone_initial_inv
                hseek with
            ⟨count, suffix, hrest, hneed⟩
          rcases
              codePrefixParserNormalizerMachine_haltsFrom_needTransition_inv
                (by
                  simpa [codePrefixParserNormalizerMarkedContextLeft,
                    MachineDescription.encodeNat, List.append_assoc] using
                    hneed) with
            ⟨t, restTokens, htokens, hmarkFrom⟩
          have hpre :
              transitionListParserNoHeader
                (MachineDescription.encodeTransition t) := by
            simpa [MachineDescription.encodeTransition] using
              transitionListParser_encodeTransitionAppend_noHeader
                t (suffix := []) (by
                  intro symbol hmem
                  simp at hmem)
          have hmarkContext :
              TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
                { state := CodePrefixParserNormalizerState.markPosition
                  tape :=
                    transitionListParserOptionTape
                      (codePrefixParserNormalizerMarkedContextLeft
                        prefixLeft 1 count
                        (MachineDescription.encodeTransition t))
                      (restTokens.map some) } := by
            simpa [codePrefixParserNormalizerMarkedContextLeft,
              MachineDescription.encodeTransition,
              MachineDescription.encodeTransitionAppend,
              MachineDescription.encodeNatAppend,
              MachineDescription.encodeCellAppend,
              MachineDescription.encodeDirectionAppend,
              List.reverse_append, List.map_append, List.map_reverse,
              List.map_replicate, List.append_assoc] using hmarkFrom
          rcases
              codePrefixParserNormalizerMachine_haltsFrom_markPosition_context_inv
                prefixLeft count 1
                (MachineDescription.encodeTransition t)
                restTokens hpre hmarkContext with
            ⟨transitions, input, hcount, hrestTokens⟩
          refine ⟨count + 1, suffix, t :: transitions, input, ?_, ?_⟩
          · simp [MachineDescription.encodeNatAppend,
              MachineDescription.encodeNat, hrest]
          · simpa [hcount, htokens, hrestTokens,
              MachineDescription.encodeTransitionsAppend] using
              MachineDescription.decodeTransitions_encodeTransitions_append
                (t :: transitions) input
      | header =>
          exact False.elim (hstuck (by simp) h)
      | transition =>
          exact False.elim (hstuck (by simp) h)
      | blank =>
          exact False.elim (hstuck (by simp) h)
      | zero =>
          exact False.elim (hstuck (by simp) h)
      | one =>
          exact False.elim (hstuck (by simp) h)
      | moveLeft =>
          exact False.elim (hstuck (by simp) h)
      | moveRight =>
          exact False.elim (hstuck (by simp) h)


end Computability
end FoC
