import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.Normalizer.Soundness.Inversion
set_option doc.verso true

/-!
# Normalizer Soundness: Transition Blocks

Soundness facts for individual transition blocks within the normalizer.
-/

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


end Computability
end FoC
