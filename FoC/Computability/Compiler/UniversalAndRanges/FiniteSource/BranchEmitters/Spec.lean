import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.BranchEmitters

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

theorem codePrefixParserBranchMachine_haltsWithOutput_encodeDescriptionAppend
    (D : MachineDescription) (input : Word MachineCodeSymbol) :
    TuringMachine.HaltsWithOutput
      codePrefixParserBranchMachine
      (MachineDescription.encodeDescriptionAppend D input)
      (MachineDescription.encodeBoolWordAppend [true]
        (MachineDescription.encodeDescriptionAppend D input)) := by
  cases D with
  | mk stateCount start halt transitions =>
      cases transitions with
      | nil =>
          let D0 : MachineDescription :=
            { stateCount := stateCount
              start := start
              halt := halt
              transitions := [] }
          let prefixLeft : Word MachineCodeSymbol :=
            List.append
              (List.replicate halt MachineCodeSymbol.tick)
              (List.append
                (MachineDescription.encodeNat start).reverse
                (List.append
                  (MachineDescription.encodeNat stateCount).reverse
                  [MachineCodeSymbol.header]))
          have hheader :=
            codePrefixParserNormalizerMachine_computes_headerFields_marked
              D0 input
          have hzero :
              TuringMachine.Computes codePrefixParserNormalizerMachine
                { state := CodePrefixParserNormalizerState.findInitialCount
                  tape :=
                    transitionListParserOptionTape
                      (codePrefixParserNormalizerMarkedHeaderLeft D0)
                      ((MachineDescription.encodeNatAppend
                        D0.transitions.length
                        (MachineDescription.encodeTransitionsAppend
                          D0.transitions input)).map some) }
                { state := CodePrefixParserNormalizerState.halt
                  tape :=
                    transitionListParserOptionTape
                      ((MachineCodeSymbol.done ::
                        MachineCodeSymbol.done :: prefixLeft).map some)
                      (input.map some) } := by
            simpa [D0, prefixLeft, MachineDescription.encodeNatAppend,
              MachineDescription.encodeNat,
              MachineDescription.encodeTransitionsAppend,
              codePrefixParserNormalizerMarkedHeaderLeft,
              codePrefixParserNormalizerMarkedNatReverse_eq,
              List.map_append, List.append_assoc] using
              codePrefixParserNormalizerMachine_computes_findInitialCount_zero_halt
                (prefixLeft.map some) (input.map some)
          have hnormalizer :
              TuringMachine.Computes codePrefixParserNormalizerMachine
                { state := CodePrefixParserNormalizerState.needHeader
                  tape :=
                    codePrefixParserNormalizerTape []
                      (MachineDescription.encodeDescriptionAppend D0 input) }
                { state := CodePrefixParserNormalizerState.halt
                  tape :=
                    transitionListParserOptionTape
                      ((MachineCodeSymbol.done ::
                        MachineCodeSymbol.done :: prefixLeft).map some)
                      (input.map some) } :=
            TuringMachine.computes_trans hheader hzero
          have hprefix :
              TuringMachine.Computes codePrefixParserBranchMachine
                (TuringMachine.initial codePrefixParserBranchMachine
                  (MachineDescription.encodeDescriptionAppend D0 input))
                { state := CodePrefixParserBranchState.normalizer
                    CodePrefixParserNormalizerState.halt
                  tape :=
                    transitionListParserOptionTape
                      ((MachineCodeSymbol.done ::
                        MachineCodeSymbol.done :: prefixLeft).map some)
                      (input.map some) } := by
            have hbranch :=
              codePrefixParserBranchMachine_computes_of_normalizer_computes
                hnormalizer
            simpa [TuringMachine.initial, codePrefixParserBranchMachine,
              codePrefixParserBranchLiftConfig,
              codePrefixParserNormalizerMachine,
              codePrefixParserNormalizerTape_nil_eq_input] using hbranch
          rcases
              codePrefixParserBranch_success_from_clean_halt
                (MachineCodeSymbol.done ::
                  MachineCodeSymbol.done :: prefixLeft)
                input with
            ⟨final, hcleanup, hhalt, hout⟩
          refine
            ⟨final, TuringMachine.computes_trans hprefix hcleanup,
              hhalt, ?_⟩
          simpa [D0, prefixLeft, codePrefixParserBranchTruePrefix_append,
            MachineDescription.encodeDescriptionAppend,
            MachineDescription.encodeTransitionsAppend,
            MachineDescription.encodeNatAppend,
            codePrefixParserNormalizer_encodeNat_eq_replicate_tick_done,
            List.reverse_append, List.append_assoc] using hout
      | cons transition rest =>
          let D0 : MachineDescription :=
            { stateCount := stateCount
              start := start
              halt := halt
              transitions := transition :: rest }
          let prefixLeft : List (Option MachineCodeSymbol) :=
            List.append
              (List.replicate halt (some MachineCodeSymbol.tick))
              (List.append
                ((MachineDescription.encodeNat start).reverse.map some)
                (List.append
                  ((MachineDescription.encodeNat stateCount).reverse.map some)
                  [some MachineCodeSymbol.header]))
          let prefixLeftSymbols : Word MachineCodeSymbol :=
            List.append
              (List.replicate halt MachineCodeSymbol.tick)
              (List.append
                (MachineDescription.encodeNat start).reverse
                (List.append
                  (MachineDescription.encodeNat stateCount).reverse
                  [MachineCodeSymbol.header]))
          let parsedPrefix : Word MachineCodeSymbol :=
            MachineDescription.encodeTransition transition
          have hheader :=
            codePrefixParserNormalizerMachine_computes_headerFields_to_markPosition_cons
              stateCount start halt transition rest input
          have hpre :
              transitionListParserNoHeader parsedPrefix := by
            simpa [parsedPrefix, MachineDescription.encodeTransition] using
              transitionListParser_encodeTransitionAppend_noHeader
                transition (suffix := []) (by
                  intro symbol hmem
                  simp at hmem)
          have htail :=
            codePrefixParserNormalizerMachine_computes_markPosition_context_halt
              prefixLeft 1 parsedPrefix rest input hpre
          let leftSymbols : Word MachineCodeSymbol :=
            MachineCodeSymbol.done ::
              List.append
                (List.replicate (1 + rest.length) MachineCodeSymbol.tick)
                (MachineCodeSymbol.done :: prefixLeftSymbols)
          let right : List (Option MachineCodeSymbol) :=
            codePrefixParserNormalizerRestoredTail
              (List.append parsedPrefix
                (MachineDescription.encodeTransitions rest))
              input
          have hheader' :
              TuringMachine.Computes codePrefixParserNormalizerMachine
                { state := CodePrefixParserNormalizerState.needHeader
                  tape :=
                    codePrefixParserNormalizerTape []
                      (MachineDescription.encodeDescriptionAppend D0 input) }
                { state := CodePrefixParserNormalizerState.markPosition
                  tape :=
                    transitionListParserOptionTape
                      (codePrefixParserNormalizerMarkedContextLeft
                        prefixLeft 1 rest.length parsedPrefix)
                      ((MachineDescription.encodeTransitionsAppend rest input).map
                        some) } := by
            simpa [D0, prefixLeft, prefixLeftSymbols, parsedPrefix,
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
          have hnormalizer :
              TuringMachine.Computes codePrefixParserNormalizerMachine
                { state := CodePrefixParserNormalizerState.needHeader
                  tape :=
                    codePrefixParserNormalizerTape []
                      (MachineDescription.encodeDescriptionAppend D0 input) }
                { state := CodePrefixParserNormalizerState.halt
                  tape :=
                    transitionListParserOptionTape
                      (leftSymbols.map some)
                      right } := by
            have hcomp := TuringMachine.computes_trans hheader' htail
            simpa [leftSymbols, right, prefixLeft, prefixLeftSymbols,
              codePrefixParserNormalizerRestoredTicksLeft_eq,
              List.map_append, List.map_replicate, List.append_assoc] using
              hcomp
          have hprefix :
              TuringMachine.Computes codePrefixParserBranchMachine
                (TuringMachine.initial codePrefixParserBranchMachine
                  (MachineDescription.encodeDescriptionAppend D0 input))
                { state := CodePrefixParserBranchState.normalizer
                    CodePrefixParserNormalizerState.halt
                  tape :=
                    transitionListParserOptionTape
                      (leftSymbols.map some)
                      right } := by
            have hbranch :=
              codePrefixParserBranchMachine_computes_of_normalizer_computes
                hnormalizer
            simpa [TuringMachine.initial, codePrefixParserBranchMachine,
              codePrefixParserBranchLiftConfig,
              codePrefixParserNormalizerMachine,
              codePrefixParserNormalizerTape_nil_eq_input] using hbranch
          rcases
              codePrefixParserBranch_success_from_clean_halt_options
                leftSymbols right with
            ⟨final, hcleanup, hhalt, hout⟩
          refine
            ⟨final, TuringMachine.computes_trans hprefix hcleanup,
              hhalt, ?_⟩
          have hlen :
              1 + rest.length = rest.length + 1 := by
            omega
          have htransAppend :
              MachineDescription.encodeTransitionsAppend rest input =
                List.append
                  (MachineDescription.encodeTransitionsAppend rest [])
                  input := by
            simpa using
              (MachineDescription.encodeTransitionsAppend_append
                rest [] input).symm
          simpa [D0, prefixLeft, prefixLeftSymbols, parsedPrefix, leftSymbols,
            right, codePrefixParserBranchTruePrefix_append,
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
            codePrefixParserNormalizerRestoredTail_normalized,
            List.reverse_append, List.map_replicate,
            List.append_assoc, hlen, htransAppend] using hout

theorem codePrefixParserBranchMachine_haltsWithOutput_decodeDescriptionPrefix
    {tokens : Word MachineCodeSymbol} {D : MachineDescription}
    {input : Word MachineCodeSymbol}
    (hdecode :
      MachineDescription.decodeDescriptionPrefix tokens = some (D, input)) :
    TuringMachine.HaltsWithOutput codePrefixParserBranchMachine tokens
      (MachineDescription.encodeBoolWordAppend [true] tokens) := by
  have htokens :
      tokens = List.append (MachineDescription.encodeDescription D) input :=
    MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescription_append
      hdecode
  rw [htokens]
  simpa [MachineDescription.encodeDescriptionAppend_eq_encodeDescription_append]
    using
      codePrefixParserBranchMachine_haltsWithOutput_encodeDescriptionAppend
        D input

theorem codePrefixParserBranchMachine_haltsWithOutput_iff
    (tokens out : Word MachineCodeSymbol) :
    TuringMachine.HaltsWithOutput codePrefixParserBranchMachine tokens out <->
      (MachineDescription.decodeDescriptionPrefix tokens = none ∧
        out = MachineDescription.encodeBoolWord [false]) ∨
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeDescriptionPrefix tokens =
            some (D, input) ∧
          out =
            MachineDescription.encodeBoolWordAppend [true] tokens := by
  constructor
  · intro h
    cases hdecode : MachineDescription.decodeDescriptionPrefix tokens with
    | none =>
        have hcanonical :=
          codePrefixParserBranch_failure_decodeDescriptionPrefix
            tokens hdecode
        have hout :
            out = MachineDescription.encodeBoolWord [false] :=
          TuringMachine.halts_with_output_unique
            codePrefixParserBranchMachine_haltingTransitionsDisabled
            h hcanonical
        exact Or.inl ⟨rfl, hout⟩
    | some parsed =>
        rcases parsed with ⟨D, input⟩
        have hcanonical :=
          codePrefixParserBranchMachine_haltsWithOutput_decodeDescriptionPrefix
            (tokens := tokens) (D := D) (input := input) hdecode
        have hout :
            out = MachineDescription.encodeBoolWordAppend [true] tokens :=
          TuringMachine.halts_with_output_unique
            codePrefixParserBranchMachine_haltingTransitionsDisabled
            h hcanonical
        exact Or.inr ⟨D, input, rfl, hout⟩
  · intro h
    rcases h with hfailure | hsuccess
    · rcases hfailure with ⟨hdecode, hout⟩
      rw [hout]
      exact
        codePrefixParserBranch_failure_decodeDescriptionPrefix
          tokens hdecode
    · rcases hsuccess with ⟨D, input, hdecode, hout⟩
      rw [hout]
      exact
        codePrefixParserBranchMachine_haltsWithOutput_decodeDescriptionPrefix
          (tokens := tokens) (D := D) (input := input) hdecode

end Computability
end FoC
