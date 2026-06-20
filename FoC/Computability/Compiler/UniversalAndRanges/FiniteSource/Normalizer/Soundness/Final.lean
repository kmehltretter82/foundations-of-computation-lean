import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.Normalizer.Soundness.Basic

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

theorem codePrefixParserNormalizerMachine_haltsWithOutput_decodeTransitions
    {tokens out transitionBlock : Word MachineCodeSymbol}
    {stateCount start halt : Nat}
    (h :
      TuringMachine.HaltsWithOutput
        codePrefixParserNormalizerMachine tokens out)
    (htokens :
      tokens =
        MachineCodeSymbol.header ::
          MachineDescription.encodeNatAppend stateCount
            (MachineDescription.encodeNatAppend start
              (MachineDescription.encodeNatAppend halt transitionBlock))) :
    exists transitionCount : Nat,
    exists rest : Word MachineCodeSymbol,
    exists transitions : List TransitionDescription,
    exists input : Word MachineCodeSymbol,
      transitionBlock =
          MachineDescription.encodeNatAppend transitionCount rest ∧
        MachineDescription.decodeTransitions transitionCount rest =
          some (transitions, input) := by
  sorry

theorem codePrefixParserNormalizerMachine_haltsWithOutput_decodePrefix
    (tokens out : Word MachineCodeSymbol)
    (h :
      TuringMachine.HaltsWithOutput
        codePrefixParserNormalizerMachine tokens out) :
    exists D : MachineDescription,
    exists input : Word MachineCodeSymbol,
      MachineDescription.decodeDescriptionPrefix tokens =
        some (D, input) := by
  rcases
      codePrefixParserNormalizerMachine_haltsWithOutput_needHeader_fields
        h with
    ⟨stateCount, start, halt, transitionBlock, htokens⟩
  rcases
      codePrefixParserNormalizerMachine_haltsWithOutput_decodeTransitions
        h htokens with
    ⟨transitionCount, rest, transitions, input, hblock, htrans⟩
  refine
    ⟨{ stateCount := stateCount
       start := start
       halt := halt
       transitions := transitions }, input, ?_⟩
  exact
    decodeDescriptionPrefix_of_header_and_decodeTransitions
      (stateCount := stateCount) (start := start) (halt := halt)
      (transitionCount := transitionCount) (rest := rest)
      (transitions := transitions) (input := input)
      (by simpa [hblock] using htokens)
      htrans

theorem codePrefixParserNormalizerMachine_haltsWithOutput_encodeDescriptionAppend_nil
    (stateCount start halt : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.HaltsWithOutput
      codePrefixParserNormalizerMachine
      (MachineDescription.encodeDescriptionAppend
        { stateCount := stateCount
          start := start
          halt := halt
          transitions := [] }
        input)
      (MachineDescription.encodeDescriptionAppend
        { stateCount := stateCount
          start := start
          halt := halt
          transitions := [] }
        input) := by
  let D : MachineDescription :=
    { stateCount := stateCount
      start := start
      halt := halt
      transitions := [] }
  let prefixLeft : List (Option MachineCodeSymbol) :=
    List.append
      (List.replicate halt (some MachineCodeSymbol.tick))
      (List.append
        ((MachineDescription.encodeNat start).reverse.map some)
        (List.append
          ((MachineDescription.encodeNat stateCount).reverse.map some)
          [some MachineCodeSymbol.header]))
  have hheader :=
    codePrefixParserNormalizerMachine_computes_headerFields_marked D input
  have hzero :
      TuringMachine.Computes codePrefixParserNormalizerMachine
        { state := CodePrefixParserNormalizerState.findInitialCount
          tape :=
            transitionListParserOptionTape
              (codePrefixParserNormalizerMarkedHeaderLeft D)
              ((MachineDescription.encodeNatAppend D.transitions.length
                (MachineDescription.encodeTransitionsAppend
                  D.transitions input)).map some) }
        { state := CodePrefixParserNormalizerState.halt
          tape :=
            transitionListParserOptionTape
              (some MachineCodeSymbol.done ::
                some MachineCodeSymbol.done :: prefixLeft)
              (input.map some) } := by
    simpa [D, prefixLeft, MachineDescription.encodeNatAppend,
      MachineDescription.encodeNat,
      MachineDescription.encodeTransitionsAppend,
      codePrefixParserNormalizerMarkedHeaderLeft,
      codePrefixParserNormalizerMarkedNatReverse_eq,
      List.map_append, List.append_assoc] using
      codePrefixParserNormalizerMachine_computes_findInitialCount_zero_halt
        prefixLeft (input.map some)
  refine
    ⟨{ state := CodePrefixParserNormalizerState.halt
       tape :=
        transitionListParserOptionTape
          (some MachineCodeSymbol.done ::
            some MachineCodeSymbol.done :: prefixLeft)
          (input.map some) },
      TuringMachine.computes_trans hheader hzero, ?_, ?_⟩
  · simp [TuringMachine.Halted, codePrefixParserNormalizerMachine]
  · simp [prefixLeft,
      MachineDescription.encodeDescriptionAppend,
      MachineDescription.encodeTransitionsAppend,
      MachineDescription.encodeNatAppend,
      codePrefixParserNormalizer_encodeNat_eq_replicate_tick_done,
      codePrefixParserNormalizer_filterMap_comp_some,
      transitionListParserOptionTape_normalizedOutput,
      List.filterMap_map, List.reverse_append,
      List.append_assoc]

theorem codePrefixParserNormalizerMachine_haltsWithOutput_encodeDescriptionAppend
    (D : MachineDescription) (input : Word MachineCodeSymbol) :
    TuringMachine.HaltsWithOutput
      codePrefixParserNormalizerMachine
      (MachineDescription.encodeDescriptionAppend D input)
      (MachineDescription.encodeDescriptionAppend D input) := by
  cases D with
  | mk stateCount start halt transitions =>
      cases transitions with
      | nil =>
          simpa using
            codePrefixParserNormalizerMachine_haltsWithOutput_encodeDescriptionAppend_nil
              stateCount start halt input
      | cons transition transitions =>
          sorry

theorem codePrefixParserNormalizerMachine_haltsWithOutput_encodeDescription_append
    (D : MachineDescription) (input : Word MachineCodeSymbol) :
    TuringMachine.HaltsWithOutput
      codePrefixParserNormalizerMachine
      (List.append (MachineDescription.encodeDescription D) input)
      (List.append (MachineDescription.encodeDescription D) input) := by
  rw [← MachineDescription.encodeDescriptionAppend_eq_encodeDescription_append
    D input]
  exact
    codePrefixParserNormalizerMachine_haltsWithOutput_encodeDescriptionAppend
      D input

theorem codePrefixParserNormalizerMachine_haltsWithOutput_output_eq_input
    (tokens out : Word MachineCodeSymbol)
    (h :
      TuringMachine.HaltsWithOutput
        codePrefixParserNormalizerMachine tokens out) :
    out = tokens := by
  rcases
      codePrefixParserNormalizerMachine_haltsWithOutput_decodePrefix
        tokens out h with
    ⟨D, input, hdecode⟩
  have htokens :
      tokens = List.append (MachineDescription.encodeDescription D) input :=
    MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescription_append
      hdecode
  have hcanonical :
      TuringMachine.HaltsWithOutput
        codePrefixParserNormalizerMachine tokens tokens := by
    rw [htokens]
    exact
      codePrefixParserNormalizerMachine_haltsWithOutput_encodeDescription_append
        D input
  exact
    TuringMachine.halts_with_output_unique
      codePrefixParserNormalizerMachine_haltingTransitionsDisabled
      h hcanonical

theorem codePrefixParserNormalizerMachine_haltsWithOutput_only_decode
    (tokens out : Word MachineCodeSymbol)
    (h :
      TuringMachine.HaltsWithOutput
        codePrefixParserNormalizerMachine tokens out) :
    out = tokens ∧
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeDescriptionPrefix tokens =
          some (D, input) := by
  exact
    ⟨codePrefixParserNormalizerMachine_haltsWithOutput_output_eq_input
        tokens out h,
      codePrefixParserNormalizerMachine_haltsWithOutput_decodePrefix
        tokens out h⟩

theorem codePrefixParserNormalizerMachine_code_sound
    (tokens out : Word MachineCodeSymbol)
    (h :
      TuringMachine.HaltsWithOutput
        codePrefixParserNormalizerMachine tokens out) :
    CodePrefixParserNormalizerCode.transform tokens = some out := by
  rcases
      codePrefixParserNormalizerMachine_haltsWithOutput_only_decode
        tokens out h with
    ⟨hout, D, input, hdecode⟩
  exact
    (codePrefixParserNormalizerCode_transform_eq_some_iff
      tokens out).mpr
      ⟨D, input, hdecode,
        by
          rw [hout]
          exact
            MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescription_append
              hdecode⟩

theorem codePrefixParserNormalizerMachine_code_complete
    (tokens out : Word MachineCodeSymbol)
    (h : CodePrefixParserNormalizerCode.transform tokens = some out) :
    TuringMachine.HaltsWithOutput
      codePrefixParserNormalizerMachine tokens out := by
  rcases
      (codePrefixParserNormalizerCode_transform_eq_some_iff
        tokens out).mp h with
    ⟨D, input, hdecode, hout⟩
  have htokens :
      tokens = List.append (MachineDescription.encodeDescription D) input :=
    MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescription_append
      hdecode
  rw [htokens, hout]
  exact
    codePrefixParserNormalizerMachine_haltsWithOutput_encodeDescription_append
      D input

theorem codePrefixParserNormalizerMachine_code_spec :
    CodePrefixParserNormalizerCodeMachineSpec
      codePrefixParserNormalizerMachine := by
  intro tokens out
  constructor
  · exact codePrefixParserNormalizerMachine_code_sound tokens out
  · exact codePrefixParserNormalizerMachine_code_complete tokens out



end Computability
end FoC
