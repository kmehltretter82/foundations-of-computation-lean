import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Parser.Transition.Handoff
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Parser.SavedCell.Forward
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Initializer.Frontier

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.ExactBoundaryContinuation

open FiniteRecognizer.Interpreter.TransitionParserHandoff
open FiniteRecognizer.Interpreter.ParserAssembly

/-!
# Exact parser continuation across a retained boundary

The source is the canonical parser configuration whose left window contains
the retained blank boundary. The first return scan consumes that boundary;
subsequent parser phases coincide with the canonical unpadded continuation.
-/

theorem exactBoundaryContinuationStep :
    TransitionListParserExactBoundaryContinuationStep := by
  intro blanks pre hpre t u more suffix
  let leftNormal : Word MachineCodeSymbol :=
    List.append
      (List.append
        (List.replicate blanks MachineCodeSymbol.blank)
        (MachineDescription.encodeNat (u :: more).length))
      (List.append pre (MachineDescription.encodeTransition t))
  let parsedPrefix : Word MachineCodeSymbol :=
    List.append pre (MachineDescription.encodeTransition t)
  let afterTransition : Word MachineCodeSymbol :=
    MachineDescription.encodeNatAppend u.source
      (MachineDescription.encodeCellAppend u.read
        (MachineDescription.encodeCellAppend u.write
          (MachineDescription.encodeDirectionAppend u.move
            (MachineDescription.encodeNatAppend u.target
              (MachineDescription.encodeTransitionsAppend more suffix)))))
  have hrest :
      MachineDescription.encodeTransitionsAppend (u :: more) suffix =
        MachineCodeSymbol.transition :: afterTransition := by
    rfl
  have hrevNonempty : leftNormal.reverse ≠ [] := by
    simp [leftNormal, MachineDescription.encodeNat]
  cases hrev : leftNormal.reverse with
  | nil =>
      exact False.elim (hrevNonempty hrev)
  | cons current leftSymbols =>
      have hleft :
          leftNormal = List.append leftSymbols.reverse [current] := by
        have h := congrArg List.reverse hrev
        simpa using! h
      have hreturn :=
        transitionListParserMachine_markPosition_returnLeft_toBoundary
          (some MachineCodeSymbol.transition) leftSymbols [] current
          (afterTransition.map some)
      have hprefix :
          List.append (List.map some leftSymbols).reverse
              [some current] =
            leftNormal.map some := by
        have hmap :=
          congrArg (fun xs : List MachineCodeSymbol => xs.map some)
            hleft
        simpa [List.map_append, List.map_reverse,
          List.append_assoc] using hmap.symm
      let countTail : Word MachineCodeSymbol :=
        MachineDescription.encodeNat more.length
      let markerTail : Word MachineCodeSymbol :=
        MachineCodeSymbol.header :: afterTransition
      have htargetRest :
          List.append (List.map some leftSymbols).reverse
              (some current :: markerTail.map some) =
            List.append
              (List.replicate blanks (some MachineCodeSymbol.blank))
              (some MachineCodeSymbol.tick ::
                List.append (countTail.map some)
                  (List.append (parsedPrefix.map some)
                    (markerTail.map some))) := by
        calc
          List.append (List.map some leftSymbols).reverse
              (some current :: markerTail.map some)
              =
            List.append
              (List.append (List.map some leftSymbols).reverse
                [some current])
              (markerTail.map some) := by
                simp [List.append_assoc]
          _ =
            List.append (leftNormal.map some) (markerTail.map some) := by
                rw [hprefix]
          _ =
            List.append
              (List.replicate blanks (some MachineCodeSymbol.blank))
              (some MachineCodeSymbol.tick ::
                List.append (countTail.map some)
                  (List.append (parsedPrefix.map some)
                    (markerTail.map some))) := by
                simp [leftNormal, parsedPrefix, countTail, markerTail,
                  MachineDescription.encodeNat, List.map_append,
                  List.map_replicate, List.append_assoc]
      have hfind :=
        transitionListParserMachine_computes_findCount_blanks
          (TransitionListParserMarker.saved
            (some MachineCodeSymbol.transition))
          blanks [none]
          (some MachineCodeSymbol.tick ::
            List.append (countTail.map some)
              (List.append (parsedPrefix.map some)
                (markerTail.map some)))
      have htick :
          TuringMachine.Step transitionListParserMachine
            { state :=
                TransitionListParserState.findCount
                  (TransitionListParserMarker.saved
                    (some MachineCodeSymbol.transition))
              tape :=
                transitionListParserOptionTape
                  (List.append
                    (List.replicate blanks
                      (some MachineCodeSymbol.blank))
                    [none])
                  (some MachineCodeSymbol.tick ::
                    List.append (countTail.map some)
                      (List.append (parsedPrefix.map some)
                        (markerTail.map some))) }
            { state :=
                TransitionListParserState.seekCountDone
                  (TransitionListParserMarker.saved
                    (some MachineCodeSymbol.transition))
              tape :=
                transitionListParserOptionTape
                  (some MachineCodeSymbol.blank ::
                    List.append
                      (List.replicate blanks
                        (some MachineCodeSymbol.blank))
                      [none])
                  (List.append (countTail.map some)
                    (List.append (parsedPrefix.map some)
                      (markerTail.map some))) } :=
        transitionListParserMachine_step_findCount_tick
          (TransitionListParserMarker.saved
            (some MachineCodeSymbol.transition))
          (List.append
            (List.replicate blanks (some MachineCodeSymbol.blank))
            [none])
          (List.append (countTail.map some)
            (List.append (parsedPrefix.map some)
              (markerTail.map some)))
      have hseek :=
        transitionListParserMachine_computes_seekCountDone_saved
          (some MachineCodeSymbol.transition)
          (some MachineCodeSymbol.blank ::
            List.append
              (List.replicate blanks (some MachineCodeSymbol.blank))
              [none])
          more.length
          (List.append parsedPrefix markerTail)
      have hpre' : transitionListParserNoHeader parsedPrefix :=
        transitionListParserNoHeader_append hpre
          (transitionListParser_encodeTransition_noHeader t)
      have hmarker :=
        transitionListParserMachine_computes_seekMarker_prefix
          (some MachineCodeSymbol.transition)
          parsedPrefix markerTail hpre'
          (List.append (countTail.reverse.map some)
            (some MachineCodeSymbol.blank ::
              List.append
                (List.replicate blanks (some MachineCodeSymbol.blank))
                [none]))
      have hprefixNonempty :
          parsedPrefix.reverse ≠ [] := by
        intro h
        have hpempty : parsedPrefix = [] := by
          have h' := congrArg List.reverse h
          simpa using! h'
        have htransitionNonempty :
            MachineDescription.encodeTransition t ≠ [] := by
          simp [MachineDescription.encodeTransition,
            MachineDescription.encodeTransitionAppend]
        have happend :
            List.append pre (MachineDescription.encodeTransition t) = [] := by
          change parsedPrefix = []
          exact hpempty
        have hparts :
            pre = [] ∧ MachineDescription.encodeTransition t = [] :=
          List.eq_nil_of_append_eq_nil happend
        rcases hparts with
          ⟨_, htransitionEmpty⟩
        exact htransitionNonempty htransitionEmpty
      cases hprefRev : parsedPrefix.reverse with
      | nil =>
          exact False.elim (hprefixNonempty hprefRev)
      | cons prefixCurrent prefixLeft =>
          have hparsedPrefix :
              parsedPrefix =
                List.append prefixLeft.reverse [prefixCurrent] := by
            have h := congrArg List.reverse hprefRev
            simpa using! h
          have hheader :
              TuringMachine.Step transitionListParserMachine
                { state :=
                    TransitionListParserState.seekMarker
                      (some MachineCodeSymbol.transition)
                  tape :=
                    transitionListParserOptionTape
                      (List.append (parsedPrefix.reverse.map some)
                        (List.append (countTail.reverse.map some)
                          (some MachineCodeSymbol.blank ::
                            List.append
                              (List.replicate blanks
                                (some MachineCodeSymbol.blank))
                              [none])))
                      (markerTail.map some) }
                { state := TransitionListParserState.enterMarkedPosition
                  tape :=
                    transitionListParserOptionTape
                      (List.append (prefixLeft.map some)
                        (List.append (countTail.reverse.map some)
                          (some MachineCodeSymbol.blank ::
                            List.append
                              (List.replicate blanks
                                (some MachineCodeSymbol.blank))
                              [none])))
                      (some prefixCurrent ::
                        some MachineCodeSymbol.transition ::
                          afterTransition.map some) } := by
            have hstep :=
              transitionListParserMachine_step_seekMarker_header
                (some MachineCodeSymbol.transition)
                (List.append (prefixLeft.map some)
                  (List.append (countTail.reverse.map some)
                    (some MachineCodeSymbol.blank ::
                      List.append
                        (List.replicate blanks
                          (some MachineCodeSymbol.blank))
                        [none])))
                (afterTransition.map some)
                (some prefixCurrent)
            simpa [markerTail, hparsedPrefix, List.map_append,
              List.map_reverse, List.append_assoc] using hstep
          have henter :
              TuringMachine.Step transitionListParserMachine
                { state := TransitionListParserState.enterMarkedPosition
                  tape :=
                    transitionListParserOptionTape
                      (List.append (prefixLeft.map some)
                        (List.append (countTail.reverse.map some)
                          (some MachineCodeSymbol.blank ::
                            List.append
                              (List.replicate blanks
                                (some MachineCodeSymbol.blank))
                              [none])))
                      (some prefixCurrent ::
                        some MachineCodeSymbol.transition ::
                          afterTransition.map some) }
                { state := TransitionListParserState.needTransition
                  tape :=
                    transitionListParserOptionTape
                      (some prefixCurrent ::
                        List.append (prefixLeft.map some)
                          (List.append (countTail.reverse.map some)
                            (some MachineCodeSymbol.blank ::
                              List.append
                                (List.replicate blanks
                                  (some MachineCodeSymbol.blank))
                                [none])))
                      (some MachineCodeSymbol.transition ::
                        afterTransition.map some) } :=
            transitionListParserMachine_step_enterMarkedPosition
              (List.append (prefixLeft.map some)
                (List.append (countTail.reverse.map some)
                  (some MachineCodeSymbol.blank ::
                    List.append
                      (List.replicate blanks
                        (some MachineCodeSymbol.blank))
                      [none])))
              (some MachineCodeSymbol.transition ::
                afterTransition.map some)
              (some prefixCurrent)
          have hparse :=
            transitionListParserMachine_computes_transition u
              (some prefixCurrent ::
                List.append (prefixLeft.map some)
                  (List.append (countTail.reverse.map some)
                    (some MachineCodeSymbol.blank ::
                      List.append
                        (List.replicate blanks
                          (some MachineCodeSymbol.blank))
                        [none])))
              (MachineDescription.encodeTransitionsAppend more suffix)
          have hblankTail :=
            transitionListParser_blank_cons_replicate_append_none blanks
          have hcomp :=
            TuringMachine.computes_trans
              (by
                simpa [leftNormal, hrev, hrest, List.map_append,
                  List.append_assoc] using hreturn)
              (TuringMachine.computes_trans
                (by
                  change
                    TuringMachine.Computes transitionListParserMachine
                      { state :=
                          TransitionListParserState.findCount
                            (TransitionListParserMarker.saved
                              (some MachineCodeSymbol.transition))
                        tape :=
                          transitionListParserOptionTape [none]
                            (List.append
                              (List.map some leftSymbols).reverse
                              (some current :: markerTail.map some)) }
                      { state :=
                          TransitionListParserState.findCount
                            (TransitionListParserMarker.saved
                              (some MachineCodeSymbol.transition))
                        tape :=
                          transitionListParserOptionTape
                            (List.append
                              (List.replicate blanks
                                (some MachineCodeSymbol.blank))
                              [none])
                            (some MachineCodeSymbol.tick ::
                              List.append (countTail.map some)
                                (List.append (parsedPrefix.map some)
                                  (markerTail.map some))) }
                  rw [htargetRest]
                  exact hfind)
                (TuringMachine.Computes.step htick
                  (TuringMachine.computes_trans
                    (by
                      simpa [countTail, markerTail,
                        MachineDescription.encodeNatAppend,
                        List.map_append, List.append_assoc] using hseek)
                    (TuringMachine.computes_trans
                      (by
                        simpa [List.map_append, List.append_assoc] using!
                          hmarker)
                      (TuringMachine.Computes.step hheader
                        (TuringMachine.Computes.step henter
                          (by
                            simpa [afterTransition, hparsedPrefix, hrest,
                              MachineDescription.encodeTransition,
                              MachineDescription.encodeTransitionAppend,
                              MachineDescription.encodeNatAppend,
                              MachineDescription.encodeCellAppend,
                              MachineDescription.encodeDirectionAppend,
                              List.map_append, List.reverse_append,
                              List.append_assoc] using hparse)))))))
          have hcomp' := by
            simpa [hblankTail, List.append_assoc] using hcomp
          have hparsedTail :
              some prefixCurrent ::
                  (List.map some prefixLeft ++
                    ((List.map some countTail).reverse ++
                      some MachineCodeSymbol.blank ::
                        (List.replicate blanks
                          (some MachineCodeSymbol.blank) ++ [none]))) =
              some prefixCurrent ::
                  (List.map some prefixLeft ++
                    ((List.map some countTail).reverse ++
                      (List.replicate blanks
                        (some MachineCodeSymbol.blank) ++
                          [some MachineCodeSymbol.blank, none]))) := by
            have hcountTail :=
              congrArg
                (fun xs =>
                  (List.map some countTail).reverse ++ xs)
                hblankTail
            exact
              congrArg
                (fun xs =>
                  some prefixCurrent ::
                    (List.map some prefixLeft ++ xs))
                hcountTail
          have hcomp'' := hcomp'
          rw [hparsedTail] at hcomp''
          have hparsedFull :
              some prefixCurrent ::
                  (List.map some prefixLeft ++
                    ((List.map some countTail).reverse ++
                      (List.replicate blanks
                        (some MachineCodeSymbol.blank) ++
                          [some MachineCodeSymbol.blank, none]))) =
                (List.map some parsedPrefix).reverse ++
                  ((List.map some countTail).reverse ++
                    (List.replicate blanks
                      (some MachineCodeSymbol.blank) ++
                        [some MachineCodeSymbol.blank, none])) := by
            have hmapRev :
                (List.map some parsedPrefix).reverse =
                  List.map some (List.reverse parsedPrefix) :=
              (List.map_reverse (f := some) (l := parsedPrefix)).symm
            rw [hmapRev, hprefRev]
            simp
          have hcomp''' := hcomp''
          rw [hparsedFull] at hcomp'''
          simpa [leftNormal, parsedPrefix, countTail, hprefRev,
            MachineDescription.encodeNat, MachineDescription.encodeTransition,
            MachineDescription.encodeTransitionAppend,
            MachineDescription.encodeNatAppend,
            MachineDescription.encodeCellAppend,
            MachineDescription.encodeDirectionAppend,
            List.map_append, List.reverse_append, List.replicate_succ,
            List.append_assoc, hrest] using hcomp'''

/-! ## Exact padded-source composition -/

/-- The initial unary count and first row consume the already-present blank
boundary and reach the exact padded mark-position configuration. -/
theorem paddedNextTransitionToBoundaryMark
    (count : Nat)
    (t : TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes transitionListParserMachine
      { state :=
          TransitionListParserState.findCount
            TransitionListParserMarker.initial
        tape :=
          transitionListParserOptionTape [none]
            ((MachineDescription.encodeNatAppend (count + 1)
              (MachineDescription.encodeTransitionAppend t suffix)).map
              some) }
      { state := TransitionListParserState.markPosition
        tape :=
          transitionListParserOptionTape
            (List.append
              ((List.append
                (MachineCodeSymbol.blank ::
                  MachineDescription.encodeNat count)
                (MachineDescription.encodeTransition t)).reverse.map some)
              [none])
            (suffix.map some) } := by
  have htick :
      TuringMachine.Step transitionListParserMachine
        { state :=
            TransitionListParserState.findCount
              TransitionListParserMarker.initial
          tape :=
            transitionListParserOptionTape [none]
              ((MachineDescription.encodeNatAppend (count + 1)
                (MachineDescription.encodeTransitionAppend t suffix)).map
                some) }
        { state :=
            TransitionListParserState.seekCountDone
              TransitionListParserMarker.initial
          tape :=
            transitionListParserOptionTape
              [some MachineCodeSymbol.blank, none]
              ((MachineDescription.encodeNatAppend count
                (MachineDescription.encodeTransitionAppend t suffix)).map
                some) } := by
    simpa [MachineDescription.encodeNatAppend,
      MachineDescription.encodeNat] using
      transitionListParserMachine_step_findCount_tick
        TransitionListParserMarker.initial [none]
        ((MachineDescription.encodeNatAppend count
          (MachineDescription.encodeTransitionAppend t suffix)).map some)
  have hseek :=
    transitionListParserMachine_computes_seekCountDone_initial
      [some MachineCodeSymbol.blank, none] count
      (MachineDescription.encodeTransitionAppend t suffix)
  have hparse :=
    transitionListParserMachine_computes_transition t
      (List.append
        ((MachineDescription.encodeNat count).reverse.map some)
        [some MachineCodeSymbol.blank, none])
      suffix
  exact
    TuringMachine.Computes.step htick
      (TuringMachine.computes_trans
        (by
          simpa [MachineDescription.encodeNatAppend,
            MachineDescription.encodeNat] using hseek)
        (by
          simpa [MachineDescription.encodeTransition,
            MachineDescription.encodeTransitionAppend,
            MachineDescription.encodeNatAppend,
            MachineDescription.encodeCellAppend,
            MachineDescription.encodeDirectionAppend,
            List.reverse_append, List.map_append,
            List.append_assoc] using hparse))

/-- Iterate the padded boundary through every unprocessed row, then use the
saved-cell wrapper's exact final handoff so the saved suffix head is preserved
at parser halt. -/
theorem boundaryRowsToReadyExact
    (blanks : Nat)
    (pre : Word MachineCodeSymbol)
    (hpre : transitionListParserNoHeader pre)
    (t : TransitionDescription)
    (rest : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine
      (FiniteRecognizer.Interpreter.SavedCellTransitionParser.parserConfig
        (canonicalBoundaryMarkConfig blanks pre t rest suffix))
      (FiniteRecognizer.Interpreter.SavedCellTransitionParser.finalReadyConfig
        (blanks + rest.length)
        (canonicalParsedSymbols pre t rest) suffix) := by
  induction rest generalizing blanks pre t with
  | nil =>
      have hfinal :=
        FiniteRecognizer.Interpreter.SavedCellTransitionParser.computes_final_mark_ready_exact
          blanks (canonicalParsedSymbols pre t []) suffix
      simpa [canonicalBoundaryMarkConfig,
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
  | cons u more ih =>
      have hstep :=
        exactBoundaryContinuationStep blanks pre hpre t u more suffix
      have hstep' :
          TuringMachine.Computes transitionListParserMachine
            (canonicalBoundaryMarkConfig blanks pre t (u :: more)
              suffix)
            (canonicalBoundaryMarkConfig (blanks + 1)
              (List.append pre
                (MachineDescription.encodeTransition t))
              u more suffix) := by
        simpa [canonicalBoundaryMarkConfig, List.append_assoc]
          using hstep
      have hstepLift :=
        FiniteRecognizer.Interpreter.SavedCellTransitionParser.computes_lift_of_target_ne_halt
          hstep' (by simp [canonicalBoundaryMarkConfig])
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
      exact TuringMachine.computes_trans hstepLift hrest

/-- A nonempty table starting at the physically padded canonical source reaches
the byte-for-byte canonical saved ready endpoint. -/
theorem paddedNonemptyComputesToReadyExact
    (t : TransitionDescription)
    (rest : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine
      (FiniteRecognizer.Interpreter.SavedCellTransitionParser.parserConfig
        (TransitionParserContextTransport.paddedCanonicalSource
          (t :: rest) suffix))
      (FiniteRecognizer.Interpreter.SavedCellTransitionParser.finalReadyConfig
        (t :: rest).length
        (MachineDescription.encodeTransitions (t :: rest)) suffix) := by
  have hfirst :=
    paddedNextTransitionToBoundaryMark rest.length t
      (MachineDescription.encodeTransitionsAppend rest suffix)
  have hfirst' :
      TuringMachine.Computes transitionListParserMachine
        (TransitionParserContextTransport.paddedCanonicalSource
          (t :: rest) suffix)
        (canonicalBoundaryMarkConfig 1 [] t rest suffix) := by
    simpa [TransitionParserContextTransport.paddedCanonicalSource,
      TransitionParserContextTransport.canonicalWord,
      canonicalBoundaryMarkConfig,
      MachineDescription.encodeTransitionsAppend,
      List.append_assoc]
      using hfirst
  have hfirstLift :=
    FiniteRecognizer.Interpreter.SavedCellTransitionParser.computes_lift_of_target_ne_halt
      hfirst' (by simp [canonicalBoundaryMarkConfig])
  have hnoHeader :
      transitionListParserNoHeader ([] : Word MachineCodeSymbol) := by
    intro symbol hmem
    simp at hmem
  have hrest :=
    boundaryRowsToReadyExact 1 [] hnoHeader t rest suffix
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
  exact TuringMachine.computes_trans hfirstLift hrest

/-- Retain an arbitrary caller prefix behind the protected blank barrier while
running a nonempty canonical table to its exact saved ready endpoint. -/
theorem contextualNonemptyComputesToReadyExact
    (baseLeftRev : Word MachineCodeSymbol)
    (t : TransitionDescription)
    (rest : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine
      (FiniteRecognizer.Interpreter.SavedCellTransitionParser.parserConfig
        (TransitionParserContextTransport.contextualCanonicalSource
          baseLeftRev (t :: rest) suffix))
      (FiniteRecognizer.Interpreter.SavedCellTransitionParser.appendLeftContextConfig
        baseLeftRev
        (FiniteRecognizer.Interpreter.SavedCellTransitionParser.finalReadyConfig
          (t :: rest).length
          (MachineDescription.encodeTransitions (t :: rest)) suffix)) := by
  have hclean := paddedNonemptyComputesToReadyExact t rest suffix
  have hbarrier :
      TransitionParserContextTransport.configHasBlankBarrier
        (FiniteRecognizer.Interpreter.SavedCellTransitionParser.projectConfig
          (FiniteRecognizer.Interpreter.SavedCellTransitionParser.parserConfig
            (TransitionParserContextTransport.paddedCanonicalSource
              (t :: rest) suffix))) := by
    simpa [FiniteRecognizer.Interpreter.SavedCellTransitionParser.projectConfig,
      FiniteRecognizer.Interpreter.SavedCellTransitionParser.parserConfig,
      FiniteRecognizer.Interpreter.SavedCellTransitionParser.projectState,
      TuringMachine.PhaseEmbedding.liftConfig] using
      TransitionParserContextTransport.paddedCanonicalSource_has_barrier
        (t :: rest) suffix
  have hcontext :=
    FiniteRecognizer.Interpreter.SavedCellTransitionParser.computes_append_left_context
      baseLeftRev hbarrier hclean
  simpa [FiniteRecognizer.Interpreter.SavedCellTransitionParser.appendLeftContextConfig,
    FiniteRecognizer.Interpreter.SavedCellTransitionParser.parserConfig,
    TransitionParserContextTransport.contextualCanonicalSource,
    TransitionParserContextTransport.appendLeftContextConfig,
    TuringMachine.PhaseEmbedding.liftConfig]
    using hcontext

/-- The exact contextual endpoint is precisely the marked materializer source
used by the positive branch. -/
theorem contextualNonemptyComputesToMarkedReady
    (baseLeftRev : Word MachineCodeSymbol)
    (t : TransitionDescription)
    (rest : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine
      (FiniteRecognizer.Interpreter.SavedCellTransitionParser.parserConfig
        (TransitionParserContextTransport.contextualCanonicalSource
          baseLeftRev (t :: rest) suffix))
      (FiniteRecognizer.Interpreter.InitializerFrontier.savedParserMaterializerSourceConfig
        baseLeftRev t rest suffix) := by
  simpa [FiniteRecognizer.Interpreter.SavedCellTransitionParser.appendLeftContextConfig,
    FiniteRecognizer.Interpreter.SavedCellTransitionParser.finalReadyConfig,
    FiniteRecognizer.Interpreter.SavedCellTransitionParser.readyConfig,
    FiniteRecognizer.Interpreter.InitializerFrontier.savedParserMaterializerSourceConfig,
    FiniteRecognizer.Interpreter.InitializerFrontier.markedParserMaterializerSourceTape,
    FiniteRecognizer.Interpreter.InitializerFrontier.appendParsedLeftContext,
    TransitionParserContextTransport.appendLeftContext]
    using contextualNonemptyComputesToReadyExact
      baseLeftRev t rest suffix

/-- Deterministic runs ending at stuck configurations have the same exact
endpoint. -/
theorem computesToStuckUnique
    {symbol state : Type}
    {M : TuringMachine symbol state}
    {source first second : TuringMachine.Configuration symbol state}
    (hfirst : TuringMachine.Computes M source first)
    (hfirstStuck : forall next, ¬ TuringMachine.Step M first next)
    (hsecond : TuringMachine.Computes M source second)
    (hsecondStuck : forall next, ¬ TuringMachine.Step M second next) :
    first = second := by
  induction hfirst generalizing second with
  | refl source =>
      cases hsecond with
      | refl => rfl
      | step hstep _ => exact False.elim (hfirstStuck _ hstep)
  | step hstep htail ih =>
      cases hsecond with
      | refl => exact False.elim (hsecondStuck _ hstep)
      | step hstep' htail' =>
          have hnext := TuringMachine.step_deterministic hstep hstep'
          cases hnext
          exact ih hfirstStuck htail' hsecondStuck

/-- Any reached saved-ready endpoint from the contextual nonempty source has
the marked materializer tape, not merely an equivalent canonical projection. -/
theorem contextualNonemptyReadyTapeEquivMarked
    (baseLeftRev : Word MachineCodeSymbol)
    (t : TransitionDescription)
    (rest : List TransitionDescription)
    (suffix : Word MachineCodeSymbol)
    (target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control)
    (hrun : TuringMachine.Computes
      FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine
      (FiniteRecognizer.Interpreter.SavedCellTransitionParser.parserConfig
        (TransitionParserContextTransport.contextualCanonicalSource
          baseLeftRev (t :: rest) suffix))
      target)
    (hstate : target.state =
      FiniteRecognizer.Interpreter.SavedCellTransitionParser.Control.ready
        (transitionListParserSavedHead suffix)) :
    Tape.Equiv
      (FiniteRecognizer.Interpreter.InitializerFrontier.markedParserMaterializerSourceTape
        baseLeftRev t rest suffix)
      target.tape := by
  let exactTarget :=
    FiniteRecognizer.Interpreter.InitializerFrontier.savedParserMaterializerSourceConfig
      baseLeftRev t rest suffix
  have hexact : TuringMachine.Computes
      FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine
      (FiniteRecognizer.Interpreter.SavedCellTransitionParser.parserConfig
        (TransitionParserContextTransport.contextualCanonicalSource
          baseLeftRev (t :: rest) suffix))
      exactTarget :=
    contextualNonemptyComputesToMarkedReady
      baseLeftRev t rest suffix
  have hexactStuck : forall next,
      ¬ TuringMachine.Step FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine
        exactTarget next := by
    intro next hstep
    cases hstep with
    | mk haction =>
        simp [exactTarget,
          FiniteRecognizer.Interpreter.InitializerFrontier.savedParserMaterializerSourceConfig,
          FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine,
          FiniteRecognizer.Interpreter.SavedCellTransitionParser.transition] at haction
  have htargetStuck : forall next,
      ¬ TuringMachine.Step FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine
        target next := by
    intro next hstep
    cases hstep with
    | mk haction =>
        rw [hstate] at haction
        simp [FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine,
          FiniteRecognizer.Interpreter.SavedCellTransitionParser.transition] at haction
  have heq : exactTarget = target :=
    computesToStuckUnique hexact hexactStuck hrun htargetStuck
  subst target
  exact Tape.Equiv.refl _


end FiniteRecognizer.Interpreter.ExactBoundaryContinuation

end Computability
end FoC
