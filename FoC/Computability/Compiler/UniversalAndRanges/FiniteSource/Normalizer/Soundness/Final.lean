import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.Normalizer.Soundness.TransitionBlock

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

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
  rcases h with ⟨final, hcomp, hhalt, hout⟩
  let D : MachineDescription :=
    { stateCount := stateCount
      start := start
      halt := halt
      transitions := [] }
  let prefixLeft : List (Option MachineCodeSymbol) :=
    List.append (List.replicate halt (some MachineCodeSymbol.tick))
      (List.append ((MachineDescription.encodeNat start).reverse.map some)
        (List.append
          ((MachineDescription.encodeNat stateCount).reverse.map some)
          [some MachineCodeSymbol.header]))
  have hfromStart :
      TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
        { state := CodePrefixParserNormalizerState.needHeader
          tape :=
            codePrefixParserNormalizerTape []
              (MachineCodeSymbol.header ::
                MachineDescription.encodeNatAppend stateCount
                  (MachineDescription.encodeNatAppend start
                    (MachineDescription.encodeNatAppend halt
                      transitionBlock))) } := by
    refine ⟨final, ?_, hhalt⟩
    simpa [TuringMachine.initial, codePrefixParserNormalizerMachine,
      codePrefixParserNormalizerTape_nil_eq_input, htokens] using hcomp
  have hprefix :=
    codePrefixParserNormalizerMachine_computes_headerFields_to_findInitialCount
      stateCount start halt transitionBlock
  have htail :
      TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
        { state := CodePrefixParserNormalizerState.findInitialCount
          tape :=
            transitionListParserOptionTape
              (codePrefixParserNormalizerMarkedHeaderLeft D)
              (transitionBlock.map some) } :=
    codePrefixParserNormalizerMachine_halts_from_of_computes_suffix
      (by simpa [D] using hprefix) hfromStart
  have hleft :
      codePrefixParserNormalizerMarkedHeaderLeft D =
        none :: prefixLeft := by
    simp [D, prefixLeft, codePrefixParserNormalizerMarkedHeaderLeft,
      codePrefixParserNormalizerMarkedNatReverse_eq]
  exact
    codePrefixParserNormalizerMachine_haltsFrom_findInitialCount_decodeTransitions
      prefixLeft
      (by simpa [hleft] using htail)

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
            let prefixLeft : List (Option MachineCodeSymbol) :=
              List.append
                (List.replicate halt (some MachineCodeSymbol.tick))
                (List.append
                  ((MachineDescription.encodeNat start).reverse.map some)
                  (List.append
                    ((MachineDescription.encodeNat stateCount).reverse.map some)
                    [some MachineCodeSymbol.header]))
            let parsedPrefix : Word MachineCodeSymbol :=
              MachineDescription.encodeTransition transition
            have hheader :=
              codePrefixParserNormalizerMachine_computes_headerFields_to_markPosition_cons
                stateCount start halt transition transitions input
            have hpre :
                transitionListParserNoHeader parsedPrefix := by
              simpa [parsedPrefix, MachineDescription.encodeTransition] using
                transitionListParser_encodeTransitionAppend_noHeader
                  transition (suffix := []) (by
                    intro symbol hmem
                    simp at hmem)
            have htail :=
              codePrefixParserNormalizerMachine_computes_markPosition_context_halt
                prefixLeft 1 parsedPrefix transitions input hpre
            have hlen :
                1 + transitions.length = transitions.length + 1 := by
              omega
            have htransAppend :
                MachineDescription.encodeTransitionsAppend transitions input =
                  List.append
                    (MachineDescription.encodeTransitionsAppend transitions [])
                    input := by
              simpa using
                (MachineDescription.encodeTransitionsAppend_append
                  transitions [] input).symm
            have hheader' :
                TuringMachine.Computes codePrefixParserNormalizerMachine
                    { state := CodePrefixParserNormalizerState.needHeader
                      tape :=
                        codePrefixParserNormalizerTape []
                          (MachineDescription.encodeDescriptionAppend
                            { stateCount := stateCount
                              start := start
                              halt := halt
                              transitions := transition :: transitions }
                            input) }
                    { state := CodePrefixParserNormalizerState.markPosition
                      tape :=
                        transitionListParserOptionTape
                          (codePrefixParserNormalizerMarkedContextLeft
                            prefixLeft 1 transitions.length parsedPrefix)
                          ((MachineDescription.encodeTransitionsAppend
                            transitions input).map some) } := by
                simpa [prefixLeft, parsedPrefix,
                  codePrefixParserNormalizerMarkedContextLeft,
                  codePrefixParserNormalizerMarkedHeaderLeft,
                  codePrefixParserNormalizerMarkedNatReverse_eq,
                  MachineDescription.encodeTransition,
                  MachineDescription.encodeTransitionAppend,
                  MachineDescription.encodeNatAppend,
                  MachineDescription.encodeCellAppend,
                  MachineDescription.encodeDirectionAppend,
                  MachineDescription.encodeTransitionsAppend,
                  MachineDescription.encodeNat,
                  List.reverse_append, List.map_append,
                  List.map_reverse, List.map_replicate,
                  List.reverse_cons, List.append_assoc] using hheader
            refine
              ⟨{ state := CodePrefixParserNormalizerState.halt
                 tape :=
                  transitionListParserOptionTape
                    (some MachineCodeSymbol.done ::
                      codePrefixParserNormalizerRestoredTicksLeft
                        (1 + transitions.length)
                        (some MachineCodeSymbol.done :: prefixLeft))
                    (codePrefixParserNormalizerRestoredTail
                      (List.append parsedPrefix
                        (MachineDescription.encodeTransitions transitions))
                      input) },
                TuringMachine.computes_trans hheader' htail, ?_, ?_⟩
            · simp [TuringMachine.Halted, codePrefixParserNormalizerMachine]
            · simp [prefixLeft, parsedPrefix,
                MachineDescription.encodeDescriptionAppend,
                MachineDescription.encodeTransitions,
                MachineDescription.encodeTransitionsAppend,
                MachineDescription.encodeTransition,
                MachineDescription.encodeTransitionAppend,
                MachineDescription.encodeNatAppend,
                MachineDescription.encodeCellAppend,
                MachineDescription.encodeDirectionAppend,
                MachineDescription.encodeNat,
                codePrefixParserNormalizer_encodeNat_eq_replicate_tick_done,
                codePrefixParserNormalizerRestoredTicksLeft_eq,
                codePrefixParserNormalizerRestoredTail_normalized,
                transitionListParserOptionTape_normalizedOutput,
                List.reverse_append, List.map_replicate,
                List.append_assoc, hlen, htransAppend]
              simp [List.replicate_succ]

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
