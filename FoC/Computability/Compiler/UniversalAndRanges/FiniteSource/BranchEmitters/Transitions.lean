import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.BranchEmitters.Fields

set_option doc.verso true

/-!
# Branch emitter transition and description cases

Continuation of the split finite-source branch emitter development.
-/

namespace FoC
namespace Computability

open Languages

theorem codePrefixParserBranch_computes_needTransition_transition
    (leftSymbols prefixLeft suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes codePrefixParserBranchMachine
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.needTransition
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            ((MachineCodeSymbol.transition :: suffix).map some) }
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.sourceNat
        tape :=
          transitionListParserOptionTape
            (List.append
              ((MachineCodeSymbol.transition :: leftSymbols).map some)
              (none :: prefixLeft.map some))
            (suffix.map some) } := by
  simpa [List.append_assoc] using
    codePrefixParserBranchMachine_computes_of_normalizer_computes
      (codePrefixParserNormalizerMachine_computes_needTransition
        (List.append (leftSymbols.map some)
          (none :: prefixLeft.map some))
        suffix)

theorem codePrefixParserBranch_computes_nat_boundary
    {current next : CodePrefixParserNormalizerState}
    (htick :
      forall leftRev suffix : List (Option MachineCodeSymbol),
        TuringMachine.Step codePrefixParserNormalizerMachine
          { state := current
            tape :=
              transitionListParserOptionTape leftRev
                (some MachineCodeSymbol.tick :: suffix) }
          { state := current
            tape :=
              transitionListParserOptionTape
                (some MachineCodeSymbol.tick :: leftRev) suffix })
    (hdone :
      forall leftRev suffix : List (Option MachineCodeSymbol),
        TuringMachine.Step codePrefixParserNormalizerMachine
          { state := current
            tape :=
              transitionListParserOptionTape leftRev
                (some MachineCodeSymbol.done :: suffix) }
          { state := next
            tape :=
              transitionListParserOptionTape
                (some MachineCodeSymbol.done :: leftRev) suffix })
    (leftSymbols prefixLeft tokens suffix : Word MachineCodeSymbol)
    (n : Nat)
    (hdecode : MachineDescription.decodeNat tokens = some (n, suffix)) :
    TuringMachine.Computes codePrefixParserBranchMachine
      { state := CodePrefixParserBranchState.normalizer current
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            (tokens.map some) }
      { state := CodePrefixParserBranchState.normalizer next
        tape :=
          transitionListParserOptionTape
            (List.append
              ((List.append (MachineDescription.encodeNat n).reverse
                leftSymbols).map some)
              (none :: prefixLeft.map some))
            (suffix.map some) } := by
  have htokens :
      tokens = MachineDescription.encodeNatAppend n suffix :=
    MachineDescription.decodeNat_eq_some_encodeNatAppend hdecode
  have hcomp :=
    codePrefixParserNormalizerMachine_computes_nat_option
      htick hdone
      (List.append (leftSymbols.map some)
        (none :: prefixLeft.map some))
      n suffix
  simpa [htokens, List.map_append, List.map_reverse,
    List.append_assoc] using
    codePrefixParserBranchMachine_computes_of_normalizer_computes hcomp

theorem codePrefixParserBranch_computes_readCell_boundary
    (leftSymbols prefixLeft tokens suffix : Word MachineCodeSymbol)
    (cell : Option Bool)
    (hdecode : MachineDescription.decodeCell tokens = some (cell, suffix)) :
    TuringMachine.Computes codePrefixParserBranchMachine
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.readCell
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            (tokens.map some) }
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.writeCell
        tape :=
          transitionListParserOptionTape
            (List.append
              ((List.append (MachineDescription.encodeCell cell).reverse
                leftSymbols).map some)
              (none :: prefixLeft.map some))
            (suffix.map some) } := by
  have htokens :
      tokens = MachineDescription.encodeCellAppend cell suffix :=
    MachineDescription.decodeCell_eq_some_encodeCellAppend hdecode
  have hcomp :=
    codePrefixParserNormalizerMachine_computes_readCell
      cell
      (List.append (leftSymbols.map some)
        (none :: prefixLeft.map some))
      suffix
  simpa [htokens, List.map_append, List.map_reverse,
    List.append_assoc] using
    codePrefixParserBranchMachine_computes_of_normalizer_computes hcomp

theorem codePrefixParserBranch_computes_writeCell_boundary
    (leftSymbols prefixLeft tokens suffix : Word MachineCodeSymbol)
    (cell : Option Bool)
    (hdecode : MachineDescription.decodeCell tokens = some (cell, suffix)) :
    TuringMachine.Computes codePrefixParserBranchMachine
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.writeCell
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            (tokens.map some) }
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.moveField
        tape :=
          transitionListParserOptionTape
            (List.append
              ((List.append (MachineDescription.encodeCell cell).reverse
                leftSymbols).map some)
              (none :: prefixLeft.map some))
            (suffix.map some) } := by
  have htokens :
      tokens = MachineDescription.encodeCellAppend cell suffix :=
    MachineDescription.decodeCell_eq_some_encodeCellAppend hdecode
  have hcomp :=
    codePrefixParserNormalizerMachine_computes_writeCell
      cell
      (List.append (leftSymbols.map some)
        (none :: prefixLeft.map some))
      suffix
  simpa [htokens, List.map_append, List.map_reverse,
    List.append_assoc] using
    codePrefixParserBranchMachine_computes_of_normalizer_computes hcomp

theorem codePrefixParserBranch_computes_moveField_boundary
    (leftSymbols prefixLeft tokens suffix : Word MachineCodeSymbol)
    (dir : Direction)
    (hdecode :
      MachineDescription.decodeDirection tokens = some (dir, suffix)) :
    TuringMachine.Computes codePrefixParserBranchMachine
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.moveField
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            (tokens.map some) }
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.targetNat
        tape :=
          transitionListParserOptionTape
            (List.append
              ((List.append (MachineDescription.encodeDirection dir).reverse
                leftSymbols).map some)
              (none :: prefixLeft.map some))
            (suffix.map some) } := by
  have htokens :
      tokens = MachineDescription.encodeDirectionAppend dir suffix :=
    MachineDescription.decodeDirection_eq_some_encodeDirectionAppend hdecode
  have hcomp :=
    codePrefixParserNormalizerMachine_computes_moveField
      dir
      (List.append (leftSymbols.map some)
        (none :: prefixLeft.map some))
      suffix
  simpa [htokens, List.map_append, List.map_reverse,
    List.append_assoc] using
    codePrefixParserBranchMachine_computes_of_normalizer_computes hcomp

theorem codePrefixParserBranch_failure_transitionRecord_boundary
    (leftSymbols prefixLeft tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeTransition tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.needTransition
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            (tokens.map some) }
      codePrefixParserBranchFalseOutput := by
  cases tokens with
  | nil =>
      exact
        codePrefixParserBranch_failure_from_stuck_boundary
          CodePrefixParserNormalizerState.needTransition
          (by rfl) leftSymbols prefixLeft [] (by
            simp [codePrefixParserNormalizerMachine,
              transitionListParserOptionTape, Tape.read])
  | cons symbol rest =>
      cases symbol with
      | transition =>
          simp [MachineDescription.decodeTransition] at hdecode
          let afterTransition : Word MachineCodeSymbol :=
            MachineCodeSymbol.transition :: leftSymbols
          have hneed :=
            codePrefixParserBranch_computes_needTransition_transition
              leftSymbols prefixLeft rest
          cases hsource : MachineDescription.decodeNat rest with
          | none =>
              rcases
                  codePrefixParserBranch_failure_sourceNat_boundary
                    afterTransition prefixLeft rest hsource with
                ⟨final, hcomp, hhalt, hout⟩
              exact
                ⟨final, TuringMachine.computes_trans hneed hcomp,
                  hhalt, hout⟩
          | some parsedSource =>
              rcases parsedSource with ⟨source, restAfterSource⟩
              simp [hsource] at hdecode
              let afterSource : Word MachineCodeSymbol :=
                List.append (MachineDescription.encodeNat source).reverse
                  afterTransition
              have hsourceComp :=
                codePrefixParserBranch_computes_nat_boundary
                  codePrefixParserNormalizerMachine_step_sourceNat_tick
                  codePrefixParserNormalizerMachine_step_sourceNat_done
                  afterTransition prefixLeft rest restAfterSource
                  source hsource
              cases hread : MachineDescription.decodeCell restAfterSource with
              | none =>
                  rcases
                      codePrefixParserBranch_failure_readCell_boundary
                        afterSource prefixLeft restAfterSource hread with
                    ⟨final, hcomp, hhalt, hout⟩
                  refine ⟨final, ?_, hhalt, hout⟩
                  exact
                    TuringMachine.computes_trans hneed
                      (TuringMachine.computes_trans
                          (by
                            simpa [afterSource, List.map_append,
                              List.map_reverse, List.append_assoc] using
                              hsourceComp)
                        hcomp)
              | some parsedRead =>
                  rcases parsedRead with ⟨read, restAfterRead⟩
                  simp [hread] at hdecode
                  let afterRead : Word MachineCodeSymbol :=
                    List.append (MachineDescription.encodeCell read).reverse
                      afterSource
                  have hreadComp :=
                    codePrefixParserBranch_computes_readCell_boundary
                      afterSource prefixLeft restAfterSource
                      restAfterRead read hread
                  cases hwrite :
                      MachineDescription.decodeCell restAfterRead with
                  | none =>
                      rcases
                          codePrefixParserBranch_failure_writeCell_boundary
                            afterRead prefixLeft restAfterRead hwrite with
                        ⟨final, hcomp, hhalt, hout⟩
                      refine ⟨final, ?_, hhalt, hout⟩
                      exact
                        TuringMachine.computes_trans hneed
                          (TuringMachine.computes_trans
                              (by
                                simpa [afterSource, List.map_append,
                                  List.map_reverse, List.append_assoc] using
                                  hsourceComp)
                              (TuringMachine.computes_trans
                                (by
                                  simpa [afterRead, afterSource,
                                    List.map_append, List.map_reverse,
                                    List.append_assoc] using hreadComp)
                                hcomp))
                  | some parsedWrite =>
                      rcases parsedWrite with ⟨write, restAfterWrite⟩
                      simp [hwrite] at hdecode
                      let afterWrite : Word MachineCodeSymbol :=
                        List.append
                          (MachineDescription.encodeCell write).reverse
                          afterRead
                      have hwriteComp :=
                        codePrefixParserBranch_computes_writeCell_boundary
                          afterRead prefixLeft restAfterRead
                          restAfterWrite write hwrite
                      cases hmove :
                          MachineDescription.decodeDirection
                            restAfterWrite with
                      | none =>
                          rcases
                              codePrefixParserBranch_failure_moveField_boundary
                                afterWrite prefixLeft restAfterWrite
                                hmove with
                            ⟨final, hcomp, hhalt, hout⟩
                          refine ⟨final, ?_, hhalt, hout⟩
                          exact
                            TuringMachine.computes_trans hneed
                              (TuringMachine.computes_trans
                                  (by
                                    simpa [afterSource, List.map_append,
                                      List.map_reverse,
                                      List.append_assoc] using hsourceComp)
                                  (TuringMachine.computes_trans
                                    (by
                                      simpa [afterRead, afterSource,
                                        List.map_append, List.map_reverse,
                                        List.append_assoc] using hreadComp)
                                    (TuringMachine.computes_trans
                                      (by
                                        simpa [afterWrite, afterRead,
                                          afterSource, List.map_append,
                                          List.map_reverse,
                                          List.append_assoc] using
                                          hwriteComp)
                                    hcomp)))
                      | some parsedMove =>
                          rcases parsedMove with ⟨move, restAfterMove⟩
                          simp [hmove] at hdecode
                          let afterMove : Word MachineCodeSymbol :=
                            List.append
                              (MachineDescription.encodeDirection move).reverse
                              afterWrite
                          have hmoveComp :=
                            codePrefixParserBranch_computes_moveField_boundary
                              afterWrite prefixLeft restAfterWrite
                              restAfterMove move hmove
                          cases htarget :
                              MachineDescription.decodeNat
                                restAfterMove with
                          | none =>
                              rcases
                                  codePrefixParserBranch_failure_targetNat_boundary
                                    afterMove prefixLeft restAfterMove
                                    htarget with
                                ⟨final, hcomp, hhalt, hout⟩
                              refine ⟨final, ?_, hhalt, hout⟩
                              exact
                                TuringMachine.computes_trans hneed
                                  (TuringMachine.computes_trans
                                    (by
                                        simpa [afterSource, List.map_append,
                                          List.map_reverse,
                                          List.append_assoc] using
                                          hsourceComp)
                                      (TuringMachine.computes_trans
                                        (by
                                          simpa [afterRead, afterSource,
                                            List.map_append,
                                            List.map_reverse,
                                            List.append_assoc] using hreadComp)
                                        (TuringMachine.computes_trans
                                          (by
                                            simpa [afterWrite, afterRead,
                                              afterSource, List.map_append,
                                              List.map_reverse,
                                              List.append_assoc] using
                                              hwriteComp)
                                          (TuringMachine.computes_trans
                                            (by
                                              simpa [afterMove, afterWrite,
                                                afterRead, afterSource,
                                                List.map_append,
                                                List.map_reverse,
                                                List.append_assoc] using
                                                hmoveComp)
                                            hcomp))))
                          | some parsedTarget =>
                              rcases parsedTarget with
                                ⟨target, restAfterTarget⟩
                              simp [htarget] at hdecode
      | header =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              CodePrefixParserNormalizerState.needTransition
              (by rfl) leftSymbols prefixLeft
              (MachineCodeSymbol.header :: rest) (by
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read])
      | tick =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              CodePrefixParserNormalizerState.needTransition
              (by rfl) leftSymbols prefixLeft
              (MachineCodeSymbol.tick :: rest) (by
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read])
      | done =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              CodePrefixParserNormalizerState.needTransition
              (by rfl) leftSymbols prefixLeft
              (MachineCodeSymbol.done :: rest) (by
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read])
      | blank =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              CodePrefixParserNormalizerState.needTransition
              (by rfl) leftSymbols prefixLeft
              (MachineCodeSymbol.blank :: rest) (by
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read])
      | zero =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              CodePrefixParserNormalizerState.needTransition
              (by rfl) leftSymbols prefixLeft
              (MachineCodeSymbol.zero :: rest) (by
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read])
      | one =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              CodePrefixParserNormalizerState.needTransition
              (by rfl) leftSymbols prefixLeft
              (MachineCodeSymbol.one :: rest) (by
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read])
      | moveLeft =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              CodePrefixParserNormalizerState.needTransition
              (by rfl) leftSymbols prefixLeft
              (MachineCodeSymbol.moveLeft :: rest) (by
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read])
      | moveRight =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              CodePrefixParserNormalizerState.needTransition
              (by rfl) leftSymbols prefixLeft
                (MachineCodeSymbol.moveRight :: rest) (by
                  simp [codePrefixParserNormalizerMachine,
                    transitionListParserOptionTape, Tape.read])

theorem codePrefixParserBranch_failure_decodeTransitions_needTransition_boundary
    (count : Nat)
    (prefixLeft : Word MachineCodeSymbol)
    (blanks : Nat)
    (pre tokens : Word MachineCodeSymbol)
    (hpre : transitionListParserNoHeader pre)
    (hdecode :
      MachineDescription.decodeTransitions (count + 1) tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.needTransition
        tape :=
          transitionListParserOptionTape
            (codePrefixParserNormalizerMarkedContextLeft
              (prefixLeft.map some) blanks count pre)
            (tokens.map some) }
      codePrefixParserBranchFalseOutput := by
  induction count generalizing blanks pre tokens with
  | zero =>
      let leftSymbols : Word MachineCodeSymbol :=
        (List.append
          (List.append
            (List.replicate blanks MachineCodeSymbol.blank)
            (MachineDescription.encodeNat 0))
          pre).reverse
      have hleft :
          codePrefixParserNormalizerMarkedContextLeft
              (prefixLeft.map some) blanks 0 pre =
            List.append (leftSymbols.map some)
              (none :: prefixLeft.map some) := by
        simp [leftSymbols, codePrefixParserNormalizerMarkedContextLeft,
          List.reverse_append, List.map_append, List.map_reverse,
          List.append_assoc]
      cases htransition : MachineDescription.decodeTransition tokens with
      | none =>
          rcases
              codePrefixParserBranch_failure_transitionRecord_boundary
                leftSymbols prefixLeft tokens htransition with
            ⟨final, hcomp, hhalt, hout⟩
          exact
            ⟨final, by simpa [hleft] using hcomp, hhalt, hout⟩
      | some parsed =>
          simp [MachineDescription.decodeTransitions, htransition] at hdecode
  | succ count ih =>
      let leftSymbols : Word MachineCodeSymbol :=
        (List.append
          (List.append
            (List.replicate blanks MachineCodeSymbol.blank)
            (MachineDescription.encodeNat (count + 1)))
          pre).reverse
      have hleft :
          codePrefixParserNormalizerMarkedContextLeft
              (prefixLeft.map some) blanks (count + 1) pre =
            List.append (leftSymbols.map some)
              (none :: prefixLeft.map some) := by
        simp [leftSymbols, codePrefixParserNormalizerMarkedContextLeft,
          List.reverse_append, List.map_append, List.map_reverse,
          List.append_assoc]
      cases htransition : MachineDescription.decodeTransition tokens with
      | none =>
          rcases
              codePrefixParserBranch_failure_transitionRecord_boundary
                leftSymbols prefixLeft tokens htransition with
            ⟨final, hcomp, hhalt, hout⟩
          exact
            ⟨final, by simpa [hleft] using hcomp, hhalt, hout⟩
      | some parsed =>
          rcases parsed with ⟨transition, restTokens⟩
          have htail :
              MachineDescription.decodeTransitions (count + 1)
                restTokens = none := by
            have hdecodeTail :
                (match
                    MachineDescription.decodeTransitions (count + 1)
                      restTokens with
                  | none => none
                  | some (transitions, suffix) =>
                      some (transition :: transitions, suffix)) = none := by
              simpa [MachineDescription.decodeTransitions, htransition] using
                hdecode
            cases htail :
                MachineDescription.decodeTransitions (count + 1)
                  restTokens with
            | none =>
                rfl
            | some parsedTail =>
                rw [htail] at hdecodeTail
                cases hdecodeTail
          let pre' : Word MachineCodeSymbol :=
            List.append pre (MachineDescription.encodeTransition transition)
          have htokens :
              tokens =
                MachineDescription.encodeTransitionAppend transition
                  restTokens :=
            MachineDescription.decodeTransition_eq_some_encodeTransitionAppend
              htransition
          have hparseNorm :=
            codePrefixParserNormalizerMachine_computes_transition
              transition
              (codePrefixParserNormalizerMarkedContextLeft
                (prefixLeft.map some) blanks (count + 1) pre)
              restTokens
          have hparse :
              TuringMachine.Computes codePrefixParserBranchMachine
                { state := CodePrefixParserBranchState.normalizer
                    CodePrefixParserNormalizerState.needTransition
                  tape :=
                    transitionListParserOptionTape
                      (codePrefixParserNormalizerMarkedContextLeft
                        (prefixLeft.map some) blanks (count + 1) pre)
                      (tokens.map some) }
                { state := CodePrefixParserBranchState.normalizer
                    CodePrefixParserNormalizerState.markPosition
                  tape :=
                    transitionListParserOptionTape
                      (codePrefixParserNormalizerMarkedContextLeft
                        (prefixLeft.map some) blanks (count + 1) pre')
                      (restTokens.map some) } := by
            have hbranch :=
              codePrefixParserBranchMachine_computes_of_normalizer_computes
                hparseNorm
            simpa [htokens, pre', codePrefixParserNormalizerMarkedContextLeft,
              MachineDescription.encodeTransition,
              MachineDescription.encodeTransitionAppend,
              MachineDescription.encodeNatAppend,
              MachineDescription.encodeCellAppend,
              MachineDescription.encodeDirectionAppend,
              List.reverse_append, List.map_append, List.map_reverse,
              List.map_replicate, List.append_assoc] using hbranch
          have htransitionNoHeader :
              transitionListParserNoHeader
                (MachineDescription.encodeTransition transition) := by
            simpa [MachineDescription.encodeTransition] using
              transitionListParser_encodeTransitionAppend_noHeader
                transition (suffix := []) (by
                  intro symbol hmem
                  simp at hmem)
          have hpre' : transitionListParserNoHeader pre' :=
            transitionListParserNoHeader_append hpre htransitionNoHeader
          have hmark :
              TuringMachine.Computes codePrefixParserBranchMachine
                { state := CodePrefixParserBranchState.normalizer
                    CodePrefixParserNormalizerState.markPosition
                  tape :=
                    transitionListParserOptionTape
                      (codePrefixParserNormalizerMarkedContextLeft
                        (prefixLeft.map some) blanks (count + 1) pre')
                      (restTokens.map some) }
                { state := CodePrefixParserBranchState.normalizer
                    CodePrefixParserNormalizerState.needTransition
                  tape :=
                    transitionListParserOptionTape
                      (codePrefixParserNormalizerMarkedContextLeft
                        (prefixLeft.map some) (blanks + 1) count pre')
                      (restTokens.map some) } := by
            cases restTokens with
            | nil =>
                have hnorm :=
                  codePrefixParserNormalizerMachine_computes_markPosition_context_empty_to_needTransition
                    (prefixLeft.map some) blanks count pre' hpre'
                have hbranch :=
                  codePrefixParserBranchMachine_computes_of_normalizer_computes
                    hnorm
                simpa [transitionListParserOptionTape] using hbranch
            | cons symbol suffix =>
                have hnorm :=
                  codePrefixParserNormalizerMachine_computes_markPosition_context_to_needTransition
                    (prefixLeft.map some) blanks count pre' hpre'
                    symbol suffix
                exact
                  codePrefixParserBranchMachine_computes_of_normalizer_computes
                    hnorm
          rcases ih (blanks + 1) pre' restTokens hpre' htail with
            ⟨final, hcomp, hhalt, hout⟩
          exact
            ⟨final,
              TuringMachine.computes_trans hparse
                (TuringMachine.computes_trans hmark hcomp),
              hhalt, hout⟩

theorem codePrefixParserBranch_failure_decodeTransitions_findInitialCount
    (count : Nat)
    (prefixLeft tokens : Word MachineCodeSymbol)
    (hdecode :
      MachineDescription.decodeTransitions count tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.findInitialCount
        tape :=
          transitionListParserOptionTape
            (none :: prefixLeft.map some)
            ((MachineDescription.encodeNatAppend count tokens).map some) }
      codePrefixParserBranchFalseOutput := by
  cases count with
  | zero =>
      simp [MachineDescription.decodeTransitions] at hdecode
  | succ count =>
      have hcountNorm :=
        codePrefixParserNormalizerMachine_computes_findInitialCount_succ
          count (none :: prefixLeft.map some) tokens
      have hcount :
          TuringMachine.Computes codePrefixParserBranchMachine
            { state := CodePrefixParserBranchState.normalizer
                CodePrefixParserNormalizerState.findInitialCount
              tape :=
                transitionListParserOptionTape
                  (none :: prefixLeft.map some)
                  ((MachineDescription.encodeNatAppend (count + 1)
                    tokens).map some) }
            { state := CodePrefixParserBranchState.normalizer
                CodePrefixParserNormalizerState.needTransition
              tape :=
                transitionListParserOptionTape
                  (codePrefixParserNormalizerMarkedContextLeft
                    (prefixLeft.map some) 1 count [])
                  (tokens.map some) } := by
        have hbranch :=
          codePrefixParserBranchMachine_computes_of_normalizer_computes
            hcountNorm
        simpa [codePrefixParserNormalizerMarkedContextLeft,
          MachineDescription.encodeNatAppend, MachineDescription.encodeNat,
          List.reverse_append, List.map_append, List.map_reverse,
          List.map_replicate, List.append_assoc] using hbranch
      have hpre : transitionListParserNoHeader ([] : Word MachineCodeSymbol) := by
        simp [transitionListParserNoHeader]
      rcases
          codePrefixParserBranch_failure_decodeTransitions_needTransition_boundary
            count prefixLeft 1 [] tokens hpre
            (by simpa [Nat.succ_eq_add_one] using hdecode) with
        ⟨final, hcomp, hhalt, hout⟩
      exact
        ⟨final, TuringMachine.computes_trans hcount hcomp, hhalt, hout⟩

theorem codePrefixParserBranch_failure_decodeDescriptionPrefix
    (tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeDescriptionPrefix tokens = none) :
    TuringMachine.HaltsWithOutput codePrefixParserBranchMachine tokens
      codePrefixParserBranchFalseOutput := by
  have hfrom :
      codePrefixParserBranchHaltsFromWithOutput
        { state := CodePrefixParserBranchState.normalizer
            CodePrefixParserNormalizerState.needHeader
          tape := transitionListParserOptionTape [] (tokens.map some) }
        codePrefixParserBranchFalseOutput := by
    cases tokens with
    | nil =>
        exact
          codePrefixParserBranch_failure_from_clean_stuck_noBoundary
            CodePrefixParserNormalizerState.needHeader
            (by intro h; cases h)
            (by rfl) [] [] (by
              simp [codePrefixParserNormalizerMachine,
                transitionListParserOptionTape, Tape.read])
    | cons symbol rest =>
        cases symbol with
        | header =>
            simp [MachineDescription.decodeDescriptionPrefix] at hdecode
            let leftAfterHeader : Word MachineCodeSymbol :=
              [MachineCodeSymbol.header]
            have hheaderStep :
                TuringMachine.Step codePrefixParserBranchMachine
                  { state := CodePrefixParserBranchState.normalizer
                      CodePrefixParserNormalizerState.needHeader
                    tape :=
                      transitionListParserOptionTape []
                        ((MachineCodeSymbol.header :: rest).map some) }
                  { state := CodePrefixParserBranchState.normalizer
                      CodePrefixParserNormalizerState.stateCount
                    tape :=
                      transitionListParserOptionTape
                        (leftAfterHeader.map some)
                        (rest.map some) } := by
              have hstep :=
                codePrefixParserBranchMachine_step_of_normalizer_step
                  (codePrefixParserNormalizer_step_header
                    ([] : Word MachineCodeSymbol) rest)
              simpa [leftAfterHeader, codePrefixParserBranchLiftConfig,
                codePrefixParserNormalizerTape,
                transitionListParserTape_eq_optionTape_map] using hstep
            cases hstate : MachineDescription.decodeNat rest with
            | none =>
                rcases
                    codePrefixParserBranch_failure_stateCount_noBoundary
                      leftAfterHeader rest hstate with
                  ⟨final, hcomp, hhalt, hout⟩
                exact
                  ⟨final, TuringMachine.Computes.step hheaderStep hcomp,
                    hhalt, hout⟩
            | some parsedState =>
                rcases parsedState with ⟨stateCount, restAfterState⟩
                simp [hstate] at hdecode
                let leftAfterState : Word MachineCodeSymbol :=
                  List.append (MachineDescription.encodeNat stateCount).reverse
                    leftAfterHeader
                have hstateComp :=
                  codePrefixParserBranch_computes_nat_noBoundary
                    codePrefixParserNormalizer_step_tick_stateCount
                    codePrefixParserNormalizer_step_done_stateCount
                    leftAfterHeader rest restAfterState stateCount hstate
                cases hstart :
                    MachineDescription.decodeNat restAfterState with
                | none =>
                    rcases
                        codePrefixParserBranch_failure_startField_noBoundary
                          leftAfterState restAfterState hstart with
                      ⟨final, hcomp, hhalt, hout⟩
                    exact
                      ⟨final,
                        TuringMachine.Computes.step hheaderStep
                          (TuringMachine.computes_trans
                            (by simpa [leftAfterState] using hstateComp)
                            hcomp),
                        hhalt, hout⟩
                | some parsedStart =>
                    rcases parsedStart with ⟨start, restAfterStart⟩
                    simp [hstart] at hdecode
                    let leftAfterStart : Word MachineCodeSymbol :=
                      List.append (MachineDescription.encodeNat start).reverse
                        leftAfterState
                    have hstartComp :=
                      codePrefixParserBranch_computes_nat_noBoundary
                        codePrefixParserNormalizer_step_tick_startField
                        codePrefixParserNormalizer_step_done_startField
                        leftAfterState restAfterState restAfterStart
                        start hstart
                    cases hhaltNat :
                        MachineDescription.decodeNat restAfterStart with
                    | none =>
                        rcases
                            codePrefixParserBranch_failure_haltField_noBoundary
                              leftAfterStart restAfterStart hhaltNat with
                          ⟨final, hcomp, hhalt, hout⟩
                        exact
                          ⟨final,
                            TuringMachine.Computes.step hheaderStep
                              (TuringMachine.computes_trans
                                (by simpa [leftAfterState] using hstateComp)
                                  (TuringMachine.computes_trans
                                    (by
                                      simpa [leftAfterStart,
                                        leftAfterState, List.map_append,
                                        List.map_reverse,
                                        List.append_assoc] using
                                        hstartComp)
                                  hcomp)),
                            hhalt, hout⟩
                    | some parsedHalt =>
                        rcases parsedHalt with ⟨halt, restAfterHalt⟩
                        simp [hhaltNat] at hdecode
                        let D0 : MachineDescription :=
                          { stateCount := stateCount
                            start := start
                            halt := halt
                            transitions := [] }
                        let headerPrefixLeft : Word MachineCodeSymbol :=
                          List.append
                            (List.replicate halt MachineCodeSymbol.tick)
                            (List.append
                              (MachineDescription.encodeNat start).reverse
                              (List.append
                                (MachineDescription.encodeNat
                                  stateCount).reverse
                                [MachineCodeSymbol.header]))
                        have hmarked :
                            codePrefixParserNormalizerMarkedHeaderLeft D0 =
                              none :: headerPrefixLeft.map some := by
                          simp [D0, headerPrefixLeft,
                            codePrefixParserNormalizerMarkedHeaderLeft,
                              codePrefixParserNormalizerMarkedNatReverse_eq,
                              List.map_append]
                        have hhaltTokens :
                            restAfterStart =
                              MachineDescription.encodeNatAppend halt
                                restAfterHalt :=
                          MachineDescription.decodeNat_eq_some_encodeNatAppend
                            hhaltNat
                        have hhaltNorm :=
                          codePrefixParserNormalizerMachine_computes_haltField_marked
                            leftAfterStart halt restAfterHalt
                        have hhaltComp :
                            TuringMachine.Computes
                              codePrefixParserBranchMachine
                              { state :=
                                  CodePrefixParserBranchState.normalizer
                                    CodePrefixParserNormalizerState.haltField
                                tape :=
                                  transitionListParserOptionTape
                                    (leftAfterStart.map some)
                                    (restAfterStart.map some) }
                              { state :=
                                  CodePrefixParserBranchState.normalizer
                                    CodePrefixParserNormalizerState.findInitialCount
                                tape :=
                                  transitionListParserOptionTape
                                    (codePrefixParserNormalizerMarkedHeaderLeft
                                      D0)
                                    (restAfterHalt.map some) } := by
                          have hbranch :=
                            codePrefixParserBranchMachine_computes_of_normalizer_computes
                              hhaltNorm
                          exact
                            by
                              simpa [hhaltTokens, D0, leftAfterStart,
                                leftAfterState, leftAfterHeader,
                                codePrefixParserNormalizerMarkedHeaderLeft,
                                codePrefixParserNormalizerMarkedNatReverse_eq,
                                codePrefixParserBranchLiftConfig,
                                codePrefixParserNormalizerTape,
                                transitionListParserTape_eq_optionTape_map,
                                List.map_append, List.map_reverse,
                                List.append_assoc] using hbranch
                        have hprefixComp :
                            TuringMachine.Computes
                              codePrefixParserBranchMachine
                              { state :=
                                  CodePrefixParserBranchState.normalizer
                                    CodePrefixParserNormalizerState.needHeader
                                tape :=
                                  transitionListParserOptionTape []
                                    ((MachineCodeSymbol.header ::
                                      rest).map some) }
                              { state :=
                                  CodePrefixParserBranchState.normalizer
                                    CodePrefixParserNormalizerState.findInitialCount
                                tape :=
                                  transitionListParserOptionTape
                                    (codePrefixParserNormalizerMarkedHeaderLeft
                                      D0)
                                    (restAfterHalt.map some) } :=
                          TuringMachine.Computes.step hheaderStep
                            (TuringMachine.computes_trans
                              (by simpa [leftAfterState] using hstateComp)
                                (TuringMachine.computes_trans
                                  (by
                                    simpa [leftAfterStart,
                                      leftAfterState, List.map_append,
                                      List.map_reverse,
                                      List.append_assoc] using
                                      hstartComp)
                                hhaltComp))
                        cases hcount :
                            MachineDescription.decodeNat restAfterHalt with
                        | none =>
                            rcases
                                codePrefixParserBranch_failure_findInitialCount_boundary
                                  [] headerPrefixLeft restAfterHalt hcount with
                              ⟨final, hcomp, hhalt, hout⟩
                            exact
                              ⟨final,
                                TuringMachine.computes_trans hprefixComp
                                  (by simpa [hmarked] using hcomp),
                                hhalt, hout⟩
                        | some parsedCount =>
                            rcases parsedCount with
                              ⟨transitionCount, restAfterCount⟩
                            simp [hcount] at hdecode
                            cases htrans :
                                MachineDescription.decodeTransitions
                                  transitionCount restAfterCount with
                            | none =>
                                have hcountTokens :
                                    restAfterHalt =
                                      MachineDescription.encodeNatAppend
                                        transitionCount restAfterCount :=
                                  MachineDescription.decodeNat_eq_some_encodeNatAppend
                                    hcount
                                rcases
                                    codePrefixParserBranch_failure_decodeTransitions_findInitialCount
                                      transitionCount headerPrefixLeft
                                      restAfterCount htrans with
                                  ⟨final, hcomp, hhalt, hout⟩
                                exact
                                  ⟨final,
                                    TuringMachine.computes_trans hprefixComp
                                      (by
                                        simpa [hmarked, hcountTokens] using
                                          hcomp),
                                    hhalt, hout⟩
                            | some parsedTransitions =>
                                simp [htrans] at hdecode
        | tick =>
            exact
              codePrefixParserBranch_failure_from_clean_stuck_noBoundary
                CodePrefixParserNormalizerState.needHeader
                (by intro h; cases h)
                (by rfl) [] (MachineCodeSymbol.tick :: rest) (by
                  simp [codePrefixParserNormalizerMachine,
                    transitionListParserOptionTape, Tape.read])
        | done =>
            exact
              codePrefixParserBranch_failure_from_clean_stuck_noBoundary
                CodePrefixParserNormalizerState.needHeader
                (by intro h; cases h)
                (by rfl) [] (MachineCodeSymbol.done :: rest) (by
                  simp [codePrefixParserNormalizerMachine,
                    transitionListParserOptionTape, Tape.read])
        | transition =>
            exact
              codePrefixParserBranch_failure_from_clean_stuck_noBoundary
                CodePrefixParserNormalizerState.needHeader
                (by intro h; cases h)
                (by rfl) [] (MachineCodeSymbol.transition :: rest) (by
                  simp [codePrefixParserNormalizerMachine,
                    transitionListParserOptionTape, Tape.read])
        | blank =>
            exact
              codePrefixParserBranch_failure_from_clean_stuck_noBoundary
                CodePrefixParserNormalizerState.needHeader
                (by intro h; cases h)
                (by rfl) [] (MachineCodeSymbol.blank :: rest) (by
                  simp [codePrefixParserNormalizerMachine,
                    transitionListParserOptionTape, Tape.read])
        | zero =>
            exact
              codePrefixParserBranch_failure_from_clean_stuck_noBoundary
                CodePrefixParserNormalizerState.needHeader
                (by intro h; cases h)
                (by rfl) [] (MachineCodeSymbol.zero :: rest) (by
                  simp [codePrefixParserNormalizerMachine,
                    transitionListParserOptionTape, Tape.read])
        | one =>
            exact
              codePrefixParserBranch_failure_from_clean_stuck_noBoundary
                CodePrefixParserNormalizerState.needHeader
                (by intro h; cases h)
                (by rfl) [] (MachineCodeSymbol.one :: rest) (by
                  simp [codePrefixParserNormalizerMachine,
                    transitionListParserOptionTape, Tape.read])
        | moveLeft =>
            exact
              codePrefixParserBranch_failure_from_clean_stuck_noBoundary
                CodePrefixParserNormalizerState.needHeader
                (by intro h; cases h)
                (by rfl) [] (MachineCodeSymbol.moveLeft :: rest) (by
                  simp [codePrefixParserNormalizerMachine,
                    transitionListParserOptionTape, Tape.read])
        | moveRight =>
            exact
              codePrefixParserBranch_failure_from_clean_stuck_noBoundary
                CodePrefixParserNormalizerState.needHeader
                (by intro h; cases h)
                (by rfl) [] (MachineCodeSymbol.moveRight :: rest) (by
                  simp [codePrefixParserNormalizerMachine,
                    transitionListParserOptionTape, Tape.read])
  rcases hfrom with ⟨final, hcomp, hhalt, hout⟩
  exact
    ⟨final,
      by
        simpa [TuringMachine.initial, codePrefixParserBranchMachine,
          transitionListParserOptionTape_nil_eq_input] using hcomp,
      hhalt, hout⟩

end Computability
end FoC
