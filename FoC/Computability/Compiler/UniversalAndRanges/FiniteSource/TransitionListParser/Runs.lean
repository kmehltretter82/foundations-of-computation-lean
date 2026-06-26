import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.TransitionListParser.Basic
set_option doc.verso true

/-!
# Transition List Parser Runs

Explicit run lemmas and configuration sequences for the transition-list parser.
-/

namespace FoC
namespace Computability

open Languages

def transitionListParserSavedHead
    (tokens : Word MachineCodeSymbol) : Option MachineCodeSymbol :=
  match tokens with
  | [] => none
  | symbol :: _ => some symbol

def transitionListParserMarkedTail
    (tokens : Word MachineCodeSymbol) :
    List (Option MachineCodeSymbol) :=
  match tokens with
  | [] => [some MachineCodeSymbol.header]
  | _ :: suffix => some MachineCodeSymbol.header :: suffix.map some

theorem transitionListParserMarkedTail_cons
    (symbol : MachineCodeSymbol) (suffix : Word MachineCodeSymbol) :
    transitionListParserMarkedTail (symbol :: suffix) =
      some MachineCodeSymbol.header :: suffix.map some := by
  rfl

theorem transitionListParserSavedHead_cons
    (symbol : MachineCodeSymbol) (suffix : Word MachineCodeSymbol) :
    transitionListParserSavedHead (symbol :: suffix) =
      some symbol := by
  rfl

theorem transitionListParserMachine_haltsFrom_markPosition_after_oneCount
    (tail suffix : Word MachineCodeSymbol) :
    TuringMachine.HaltsFrom transitionListParserMachine
      { state := TransitionListParserState.markPosition
        tape :=
          transitionListParserOptionTape
            ((List.append
              [MachineCodeSymbol.blank, MachineCodeSymbol.done]
              tail).reverse.map some)
            (suffix.map some) } := by
  let leftNormal : Word MachineCodeSymbol :=
    List.append [MachineCodeSymbol.blank, MachineCodeSymbol.done] tail
  have hrevNonempty : leftNormal.reverse ≠ [] := by
    simp [leftNormal]
  cases hrev : leftNormal.reverse with
  | nil =>
      exact False.elim (hrevNonempty hrev)
  | cons current leftSymbols =>
      have hleft :
          leftNormal = List.append leftSymbols.reverse [current] := by
        have h := congrArg List.reverse hrev
        simpa using h
      cases suffix with
      | nil =>
          have hreturn :=
            transitionListParserMachine_markPosition_empty_returnLeft_noBoundary
              leftSymbols current
          have hprefix :
              List.append (List.map some leftSymbols).reverse
                  [some current] =
                some MachineCodeSymbol.blank ::
                  some MachineCodeSymbol.done :: tail.map some := by
            have hmap :=
              congrArg (fun xs : List MachineCodeSymbol => xs.map some)
                hleft
            simpa [leftNormal, List.map_append, List.map_reverse,
              List.append_assoc] using hmap.symm
          have hhalt :=
            transitionListParserMachine_haltsFrom_findCount_blank_done
              (TransitionListParserMarker.saved none)
              [none]
              (List.append (tail.map some)
                [some MachineCodeSymbol.header])
          have htargetRest :
              List.append (List.map some leftSymbols).reverse
                  [some current, some MachineCodeSymbol.header] =
                some MachineCodeSymbol.blank ::
                  some MachineCodeSymbol.done ::
                    (List.append (tail.map some)
                      [some MachineCodeSymbol.header]) := by
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
                List.append
                  (some MachineCodeSymbol.blank ::
                    some MachineCodeSymbol.done :: tail.map some)
                  [some MachineCodeSymbol.header] := by
                    rw [hprefix]
              _ =
                some MachineCodeSymbol.blank ::
                  some MachineCodeSymbol.done ::
                    (List.append (tail.map some)
                      [some MachineCodeSymbol.header]) := by
                    rfl
          exact
            TuringMachine.halts_from_of_computes_prefix
              (by
                simpa [leftNormal, hrev] using hreturn)
              (by
                change
                  TuringMachine.HaltsFrom transitionListParserMachine
                    { state :=
                        TransitionListParserState.findCount
                          (TransitionListParserMarker.saved none)
                      tape :=
                        transitionListParserOptionTape [none]
                          (List.append
                            (List.map some leftSymbols).reverse
                            [some current,
                              some MachineCodeSymbol.header]) }
                rw [htargetRest]
                exact hhalt)
      | cons first rest =>
          have hreturn :=
            transitionListParserMachine_markPosition_returnLeft_noBoundary
              (some first) leftSymbols current (rest.map some)
          have hprefix :
              List.append (List.map some leftSymbols).reverse
                  [some current] =
                some MachineCodeSymbol.blank ::
                  some MachineCodeSymbol.done :: tail.map some := by
            have hmap :=
              congrArg (fun xs : List MachineCodeSymbol => xs.map some)
                hleft
            simpa [leftNormal, List.map_append, List.map_reverse,
              List.append_assoc] using hmap.symm
          have hhalt :=
            transitionListParserMachine_haltsFrom_findCount_blank_done
              (TransitionListParserMarker.saved (some first))
              [none]
              (List.append (tail.map some)
                (some MachineCodeSymbol.header :: rest.map some))
          have htargetRest :
              List.append (List.map some leftSymbols).reverse
                  (some current ::
                    some MachineCodeSymbol.header :: rest.map some) =
                some MachineCodeSymbol.blank ::
                  some MachineCodeSymbol.done ::
                    (List.append (tail.map some)
                      (some MachineCodeSymbol.header ::
                        rest.map some)) := by
            calc
              List.append (List.map some leftSymbols).reverse
                  (some current ::
                    some MachineCodeSymbol.header :: rest.map some)
                  =
                List.append
                  (List.append (List.map some leftSymbols).reverse
                    [some current])
                  (some MachineCodeSymbol.header :: rest.map some) := by
                    simp [List.append_assoc]
              _ =
                List.append
                  (some MachineCodeSymbol.blank ::
                    some MachineCodeSymbol.done :: tail.map some)
                  (some MachineCodeSymbol.header :: rest.map some) := by
                    rw [hprefix]
              _ =
                some MachineCodeSymbol.blank ::
                  some MachineCodeSymbol.done ::
                    (List.append (tail.map some)
                      (some MachineCodeSymbol.header ::
                        rest.map some)) := by
                    rfl
          exact
            TuringMachine.halts_from_of_computes_prefix
              (by
                simpa [leftNormal, hrev] using hreturn)
              (by
                change
                  TuringMachine.HaltsFrom transitionListParserMachine
                    { state :=
                        TransitionListParserState.findCount
                          (TransitionListParserMarker.saved
                            (some first))
                      tape :=
                        transitionListParserOptionTape [none]
                          (List.append
                            (List.map some leftSymbols).reverse
                            (some current ::
                              some MachineCodeSymbol.header ::
                                rest.map some)) }
                rw [htargetRest]
                exact hhalt)

theorem transitionListParserMachine_computes_seekMarker_prefix
    (saved : Option MachineCodeSymbol)
    (pre rest : List MachineCodeSymbol)
    (hpre :
      forall symbol : MachineCodeSymbol,
        symbol ∈ pre -> symbol ≠ MachineCodeSymbol.header)
    (leftRev : List (Option MachineCodeSymbol)) :
    TuringMachine.Computes transitionListParserMachine
      { state := TransitionListParserState.seekMarker saved
        tape :=
          transitionListParserOptionTape leftRev
            ((List.append pre rest).map some) }
      { state := TransitionListParserState.seekMarker saved
        tape :=
          transitionListParserOptionTape
            (List.append (pre.reverse.map some) leftRev)
            (rest.map some) } := by
  induction pre generalizing leftRev with
  | nil =>
      exact TuringMachine.Computes.refl _
  | cons symbol tail ih =>
      have hsymbol : symbol ≠ MachineCodeSymbol.header :=
        hpre symbol (by simp)
      have htail :
          forall symbol' : MachineCodeSymbol,
            symbol' ∈ tail ->
              symbol' ≠ MachineCodeSymbol.header := by
        intro symbol' hmem
        exact hpre symbol' (by simp [hmem])
      have hcomp :=
        ih htail (some symbol :: leftRev)
      exact
        TuringMachine.Computes.step
          (transitionListParserMachine_step_seekMarker_nonHeader
            saved hsymbol leftRev
            ((List.append tail rest).map some))
          (by
            simpa [List.append_assoc] using hcomp)

theorem transitionListParserMachine_computes_oneTransition_to_markPosition
    (t : TransitionDescription) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes transitionListParserMachine
      { state :=
          TransitionListParserState.findCount
            TransitionListParserMarker.initial
        tape :=
          transitionListParserOptionTape []
            ((MachineDescription.encodeNatAppend 1
              (MachineDescription.encodeTransitionAppend t suffix)).map
              some) }
      { state := TransitionListParserState.markPosition
        tape :=
          transitionListParserOptionTape
            ((List.append
              [MachineCodeSymbol.blank, MachineCodeSymbol.done]
              (MachineDescription.encodeTransition t)).reverse.map some)
            (suffix.map some) } := by
  have htick :
      TuringMachine.Step transitionListParserMachine
        { state :=
            TransitionListParserState.findCount
              TransitionListParserMarker.initial
          tape :=
            transitionListParserOptionTape []
              ((MachineDescription.encodeNatAppend 1
                (MachineDescription.encodeTransitionAppend t suffix)).map
                some) }
        { state :=
            TransitionListParserState.seekCountDone
              TransitionListParserMarker.initial
          tape :=
            transitionListParserOptionTape
              [some MachineCodeSymbol.blank]
              ((MachineDescription.encodeNatAppend 0
                (MachineDescription.encodeTransitionAppend t suffix)).map
                some) } := by
    simpa [MachineDescription.encodeNatAppend,
      MachineDescription.encodeNat] using
      transitionListParserMachine_step_findCount_tick
        TransitionListParserMarker.initial []
        ((MachineDescription.encodeNatAppend 0
          (MachineDescription.encodeTransitionAppend t suffix)).map some)
  have hseek :=
    transitionListParserMachine_computes_seekCountDone_initial
      [some MachineCodeSymbol.blank] 0
      (MachineDescription.encodeTransitionAppend t suffix)
  have hparse :=
    transitionListParserMachine_computes_transition t
      [some MachineCodeSymbol.done, some MachineCodeSymbol.blank]
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

theorem transitionListParserMachine_halts_oneTransition
    (t : TransitionDescription) (suffix : Word MachineCodeSymbol) :
    TuringMachine.HaltsOnInput transitionListParserMachine
      (MachineDescription.encodeNatAppend 1
        (MachineDescription.encodeTransitionAppend t suffix)) := by
  have hcomp :=
    transitionListParserMachine_computes_oneTransition_to_markPosition
      t suffix
  have hmark :
      TuringMachine.HaltsFrom transitionListParserMachine
        { state := TransitionListParserState.markPosition
          tape :=
            transitionListParserOptionTape
              ((List.append
                [MachineCodeSymbol.blank, MachineCodeSymbol.done]
                (MachineDescription.encodeTransition t)).reverse.map some)
              (suffix.map some) } :=
    transitionListParserMachine_haltsFrom_markPosition_after_oneCount
      (MachineDescription.encodeTransition t) suffix
  have hfrom :=
    TuringMachine.halts_from_of_computes_prefix hcomp hmark
  simpa [TuringMachine.HaltsOnInput, TuringMachine.initial,
    transitionListParserMachine,
    transitionListParserOptionTape_nil_eq_input] using hfrom

theorem transitionListParserMachine_computes_markPosition_canonicalContext_step
    (blanks : Nat)
    (pre : Word MachineCodeSymbol)
    (hpre : transitionListParserNoHeader pre)
    (t u : TransitionDescription)
    (more : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes transitionListParserMachine
      { state := TransitionListParserState.markPosition
        tape :=
          transitionListParserOptionTape
            ((List.append
              (List.append
                (List.replicate blanks MachineCodeSymbol.blank)
                (MachineDescription.encodeNat (u :: more).length))
              (List.append pre
                (MachineDescription.encodeTransition t))).reverse.map some)
            ((MachineDescription.encodeTransitionsAppend
              (u :: more) suffix).map some) }
      { state := TransitionListParserState.markPosition
        tape :=
          transitionListParserOptionTape
            (List.append
              ((List.append
                (List.append
                  (List.replicate (blanks + 1)
                    MachineCodeSymbol.blank)
                  (MachineDescription.encodeNat more.length))
                (List.append
                  (List.append pre
                    (MachineDescription.encodeTransition t))
                  (MachineDescription.encodeTransition u))).reverse.map
                some)
              [none])
            ((MachineDescription.encodeTransitionsAppend more suffix).map
              some) } := by
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
        simpa using h
      have hreturn :=
        transitionListParserMachine_markPosition_returnLeft_noBoundary
          (some MachineCodeSymbol.transition) leftSymbols current
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
          simpa using h'
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
            simpa using h
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
                simpa [leftNormal, hrev, hrest] using hreturn)
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
                        simpa [List.map_append, List.append_assoc] using
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

theorem transitionListParserMachine_haltsFrom_markPosition_canonicalBoundary
    (blanks : Nat)
    (pre : Word MachineCodeSymbol)
    (hpre : transitionListParserNoHeader pre)
    (t : TransitionDescription)
    (rest : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.HaltsFrom transitionListParserMachine
      { state := TransitionListParserState.markPosition
        tape :=
          transitionListParserOptionTape
            (List.append
              ((List.append
                (List.append
                  (List.replicate blanks MachineCodeSymbol.blank)
                  (MachineDescription.encodeNat rest.length))
                (List.append pre
                  (MachineDescription.encodeTransition t))).reverse.map
                some)
              [none])
            ((MachineDescription.encodeTransitionsAppend rest suffix).map
              some) } := by
  induction rest generalizing blanks pre t with
  | nil =>
      let leftNormal : Word MachineCodeSymbol :=
        List.append
          (List.append
            (List.replicate blanks MachineCodeSymbol.blank)
            (MachineDescription.encodeNat 0))
          (List.append pre (MachineDescription.encodeTransition t))
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
          cases suffix with
          | nil =>
              have hreturn :=
                transitionListParserMachine_markPosition_empty_returnLeft_toBoundary
                  leftSymbols [] current
              have hprefix :
                  List.append (List.map some leftSymbols).reverse
                      [some current] =
                    leftNormal.map some := by
                have hmap :=
                  congrArg (fun xs : List MachineCodeSymbol => xs.map some)
                    hleft
                simpa [List.map_append, List.map_reverse,
                  List.append_assoc] using hmap.symm
              have hhalt :=
                transitionListParserMachine_haltsFrom_findCount_blanks_done
                  (TransitionListParserMarker.saved none)
                  blanks [none]
                  (List.append
                    ((List.append pre
                      (MachineDescription.encodeTransition t)).map some)
                    [some MachineCodeSymbol.header])
              have htargetRest :
                  List.append (List.map some leftSymbols).reverse
                      [some current, some MachineCodeSymbol.header] =
                    List.append
                      (List.replicate blanks
                        (some MachineCodeSymbol.blank))
                      (some MachineCodeSymbol.done ::
                        List.append
                          ((List.append pre
                            (MachineDescription.encodeTransition t)).map
                            some)
                          [some MachineCodeSymbol.header]) := by
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
                        rw [hprefix]
                  _ =
                    List.append
                      (List.replicate blanks
                        (some MachineCodeSymbol.blank))
                      (some MachineCodeSymbol.done ::
                        List.append
                          ((List.append pre
                            (MachineDescription.encodeTransition t)).map
                            some)
                          [some MachineCodeSymbol.header]) := by
                        simp [leftNormal, MachineDescription.encodeNat,
                          List.map_append, List.map_replicate,
                          List.append_assoc]
              exact
                TuringMachine.halts_from_of_computes_prefix
                  (by
                    simpa [leftNormal, hrev] using hreturn)
                  (by
                    change
                      TuringMachine.HaltsFrom transitionListParserMachine
                        { state :=
                            TransitionListParserState.findCount
                              (TransitionListParserMarker.saved none)
                          tape :=
                            transitionListParserOptionTape [none]
                              (List.append
                                (List.map some leftSymbols).reverse
                                [some current,
                                  some MachineCodeSymbol.header]) }
                    rw [htargetRest]
                    exact hhalt)
          | cons first restSuffix =>
              have hreturn :=
                transitionListParserMachine_markPosition_returnLeft_toBoundary
                  (some first) leftSymbols [] current
                  (restSuffix.map some)
              have hprefix :
                  List.append (List.map some leftSymbols).reverse
                      [some current] =
                    leftNormal.map some := by
                have hmap :=
                  congrArg (fun xs : List MachineCodeSymbol => xs.map some)
                    hleft
                simpa [List.map_append, List.map_reverse,
                  List.append_assoc] using hmap.symm
              have hhalt :=
                transitionListParserMachine_haltsFrom_findCount_blanks_done
                  (TransitionListParserMarker.saved (some first))
                  blanks [none]
                  (List.append
                    ((List.append pre
                      (MachineDescription.encodeTransition t)).map some)
                    (some MachineCodeSymbol.header ::
                      restSuffix.map some))
              have htargetRest :
                  List.append (List.map some leftSymbols).reverse
                      (some current ::
                        some MachineCodeSymbol.header ::
                          restSuffix.map some) =
                    List.append
                      (List.replicate blanks
                        (some MachineCodeSymbol.blank))
                      (some MachineCodeSymbol.done ::
                        List.append
                          ((List.append pre
                            (MachineDescription.encodeTransition t)).map
                            some)
                          (some MachineCodeSymbol.header ::
                            restSuffix.map some)) := by
                calc
                  List.append (List.map some leftSymbols).reverse
                      (some current ::
                        some MachineCodeSymbol.header ::
                          restSuffix.map some)
                      =
                    List.append
                      (List.append (List.map some leftSymbols).reverse
                        [some current])
                      (some MachineCodeSymbol.header ::
                        restSuffix.map some) := by
                        simp [List.append_assoc]
                  _ =
                    List.append (leftNormal.map some)
                      (some MachineCodeSymbol.header ::
                        restSuffix.map some) := by
                        rw [hprefix]
                  _ =
                    List.append
                      (List.replicate blanks
                        (some MachineCodeSymbol.blank))
                      (some MachineCodeSymbol.done ::
                        List.append
                          ((List.append pre
                            (MachineDescription.encodeTransition t)).map
                            some)
                          (some MachineCodeSymbol.header ::
                            restSuffix.map some)) := by
                        simp [leftNormal, MachineDescription.encodeNat,
                          List.map_append, List.map_replicate,
                          List.append_assoc]
              exact
                TuringMachine.halts_from_of_computes_prefix
                  (by
                    simpa [leftNormal, hrev] using hreturn)
                  (by
                    change
                      TuringMachine.HaltsFrom transitionListParserMachine
                        { state :=
                            TransitionListParserState.findCount
                              (TransitionListParserMarker.saved
                                (some first))
                          tape :=
                            transitionListParserOptionTape [none]
                              (List.append
                                (List.map some leftSymbols).reverse
                                (some current ::
                                  some MachineCodeSymbol.header ::
                                    restSuffix.map some)) }
                    rw [htargetRest]
                    exact hhalt)
  | cons u more ih =>
      let leftNormal : Word MachineCodeSymbol :=
        List.append
          (List.append
            (List.replicate blanks MachineCodeSymbol.blank)
            (MachineDescription.encodeNat (u :: more).length))
          (List.append pre (MachineDescription.encodeTransition t))
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
          have hreturnBoundary :=
            transitionListParserMachine_markPosition_returnLeft_toBoundary
              (some MachineCodeSymbol.transition)
              leftSymbols [] current (afterTransition.map some)
          have hreturnNoBoundary :=
            transitionListParserMachine_markPosition_returnLeft_noBoundary
              (some MachineCodeSymbol.transition)
              leftSymbols current (afterTransition.map some)
          have hstep :=
            transitionListParserMachine_computes_markPosition_canonicalContext_step
              blanks pre hpre t u more suffix
          have hpre' :
          transitionListParserNoHeader
                (List.append pre (MachineDescription.encodeTransition t)) :=
            transitionListParserNoHeader_append hpre
              (transitionListParser_encodeTransition_noHeader t)
          have htarget :=
            ih (blanks + 1)
              (List.append pre (MachineDescription.encodeTransition t))
              hpre' u
          have hstartNoBoundary :=
            TuringMachine.halts_from_of_computes_prefix hstep htarget
          have hleftStart :
              leftNormal.reverse.map some =
                some current :: leftSymbols.map some := by
            simp [hrev]
          have hleftStartBoundary :
              List.append (leftNormal.reverse.map some) [none] =
                some current ::
                  List.append (leftSymbols.map some) [none] := by
            simp [hrev]
          have hfind :=
            transitionListParserMachine_halts_from_of_computes_suffix
              (by
                have hreturnNoBoundary' := hreturnNoBoundary
                rw [← hleftStart] at hreturnNoBoundary'
                simpa [leftNormal, hrest] using
                  hreturnNoBoundary')
              hstartNoBoundary
          exact
            TuringMachine.halts_from_of_computes_prefix
              (by
                simpa [leftNormal, hrev, hrest, List.map_append,
                  List.append_assoc] using hreturnBoundary)
              hfind

theorem transitionListParserMachine_haltsFrom_markPosition_canonicalContext
    (blanks : Nat)
    (pre : Word MachineCodeSymbol)
    (hpre : transitionListParserNoHeader pre)
    (t : TransitionDescription)
    (rest : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.HaltsFrom transitionListParserMachine
      { state := TransitionListParserState.markPosition
        tape :=
          transitionListParserOptionTape
            ((List.append
              (List.append
                (List.replicate blanks MachineCodeSymbol.blank)
                (MachineDescription.encodeNat rest.length))
              (List.append pre
                (MachineDescription.encodeTransition t))).reverse.map some)
            ((MachineDescription.encodeTransitionsAppend rest suffix).map
              some) } := by
  induction rest generalizing blanks pre t with
  | nil =>
      let leftNormal : Word MachineCodeSymbol :=
        List.append
          (List.append
            (List.replicate blanks MachineCodeSymbol.blank)
            (MachineDescription.encodeNat 0))
          (List.append pre (MachineDescription.encodeTransition t))
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
          cases suffix with
          | nil =>
              have hreturn :=
                transitionListParserMachine_markPosition_empty_returnLeft_noBoundary
                  leftSymbols current
              have hprefix :
                  List.append (List.map some leftSymbols).reverse
                      [some current] =
                    (leftNormal.map some) := by
                have hmap :=
                  congrArg (fun xs : List MachineCodeSymbol => xs.map some)
                    hleft
                simpa [List.map_append, List.map_reverse,
                  List.append_assoc] using hmap.symm
              have hhalt :=
                transitionListParserMachine_haltsFrom_findCount_blanks_done
                  (TransitionListParserMarker.saved none)
                  blanks [none]
                  (List.append
                    ((List.append pre
                      (MachineDescription.encodeTransition t)).map some)
                    [some MachineCodeSymbol.header])
              have htargetRest :
                  List.append (List.map some leftSymbols).reverse
                      [some current, some MachineCodeSymbol.header] =
                    List.append
                      (List.replicate blanks
                        (some MachineCodeSymbol.blank))
                      (some MachineCodeSymbol.done ::
                        List.append
                          ((List.append pre
                            (MachineDescription.encodeTransition t)).map
                            some)
                          [some MachineCodeSymbol.header]) := by
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
                        rw [hprefix]
                  _ =
                    List.append
                      (List.replicate blanks
                        (some MachineCodeSymbol.blank))
                      (some MachineCodeSymbol.done ::
                        List.append
                          ((List.append pre
                            (MachineDescription.encodeTransition t)).map
                            some)
                          [some MachineCodeSymbol.header]) := by
                        simp [leftNormal, MachineDescription.encodeNat,
                          List.map_append, List.map_replicate,
                          List.append_assoc]
              exact
                TuringMachine.halts_from_of_computes_prefix
                  (by
                    simpa [leftNormal, hrev] using hreturn)
                  (by
                    change
                      TuringMachine.HaltsFrom transitionListParserMachine
                        { state :=
                            TransitionListParserState.findCount
                              (TransitionListParserMarker.saved none)
                          tape :=
                            transitionListParserOptionTape [none]
                              (List.append
                                (List.map some leftSymbols).reverse
                                [some current,
                                  some MachineCodeSymbol.header]) }
                    rw [htargetRest]
                    exact hhalt)
          | cons first restSuffix =>
              have hreturn :=
                transitionListParserMachine_markPosition_returnLeft_noBoundary
                  (some first) leftSymbols current (restSuffix.map some)
              have hprefix :
                  List.append (List.map some leftSymbols).reverse
                      [some current] =
                    (leftNormal.map some) := by
                have hmap :=
                  congrArg (fun xs : List MachineCodeSymbol => xs.map some)
                    hleft
                simpa [List.map_append, List.map_reverse,
                  List.append_assoc] using hmap.symm
              have hhalt :=
                transitionListParserMachine_haltsFrom_findCount_blanks_done
                  (TransitionListParserMarker.saved (some first))
                  blanks [none]
                  (List.append
                    ((List.append pre
                      (MachineDescription.encodeTransition t)).map some)
                    (some MachineCodeSymbol.header ::
                      restSuffix.map some))
              have htargetRest :
                  List.append (List.map some leftSymbols).reverse
                      (some current ::
                        some MachineCodeSymbol.header ::
                          restSuffix.map some) =
                    List.append
                      (List.replicate blanks
                        (some MachineCodeSymbol.blank))
                      (some MachineCodeSymbol.done ::
                        List.append
                          ((List.append pre
                            (MachineDescription.encodeTransition t)).map
                            some)
                          (some MachineCodeSymbol.header ::
                            restSuffix.map some)) := by
                calc
                  List.append (List.map some leftSymbols).reverse
                      (some current ::
                        some MachineCodeSymbol.header ::
                          restSuffix.map some)
                      =
                    List.append
                      (List.append (List.map some leftSymbols).reverse
                        [some current])
                      (some MachineCodeSymbol.header ::
                        restSuffix.map some) := by
                        simp [List.append_assoc]
                  _ =
                    List.append (leftNormal.map some)
                      (some MachineCodeSymbol.header ::
                        restSuffix.map some) := by
                        rw [hprefix]
                  _ =
                    List.append
                      (List.replicate blanks
                        (some MachineCodeSymbol.blank))
                      (some MachineCodeSymbol.done ::
                        List.append
                          ((List.append pre
                            (MachineDescription.encodeTransition t)).map
                            some)
                          (some MachineCodeSymbol.header ::
                            restSuffix.map some)) := by
                        simp [leftNormal, MachineDescription.encodeNat,
                          List.map_append, List.map_replicate,
                          List.append_assoc]
              exact
                TuringMachine.halts_from_of_computes_prefix
                  (by
                    simpa [leftNormal, hrev] using hreturn)
                  (by
                    change
                      TuringMachine.HaltsFrom transitionListParserMachine
                        { state :=
                            TransitionListParserState.findCount
                              (TransitionListParserMarker.saved
                                (some first))
                          tape :=
                            transitionListParserOptionTape [none]
                              (List.append
                                (List.map some leftSymbols).reverse
                                (some current ::
                                  some MachineCodeSymbol.header ::
                                    restSuffix.map some)) }
                    rw [htargetRest]
                    exact hhalt)
  | cons u more ih =>
      have hstep :=
        transitionListParserMachine_computes_markPosition_canonicalContext_step
          blanks pre hpre t u more suffix
      have hpre' :
          transitionListParserNoHeader
            (List.append pre (MachineDescription.encodeTransition t)) :=
        transitionListParserNoHeader_append hpre
          (transitionListParser_encodeTransition_noHeader t)
      have hhalt :=
        transitionListParserMachine_haltsFrom_markPosition_canonicalBoundary
          (blanks + 1)
          (List.append pre (MachineDescription.encodeTransition t))
          hpre' u more suffix
      exact TuringMachine.halts_from_of_computes_prefix hstep hhalt

theorem transitionListParserMachine_haltsFrom_markPosition_canonicalContinuation
    (t : TransitionDescription)
    (rest : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.HaltsFrom transitionListParserMachine
      { state := TransitionListParserState.markPosition
        tape :=
          transitionListParserOptionTape
            ((List.append
              (MachineCodeSymbol.blank ::
                MachineDescription.encodeNat rest.length)
              (MachineDescription.encodeTransition t)).reverse.map some)
            ((MachineDescription.encodeTransitionsAppend rest suffix).map
              some) } := by
  simpa [MachineDescription.encodeNat, List.append_assoc] using
    transitionListParserMachine_haltsFrom_markPosition_canonicalContext
      1 [] (by intro symbol hmem; simp at hmem)
      t rest suffix

theorem transitionListParserMachine_halts_count_zero
    (tokens : Word MachineCodeSymbol) :
    TuringMachine.HaltsOnInput transitionListParserMachine
      (MachineDescription.encodeNatAppend 0 tokens) := by
  have hstep :
      TuringMachine.Step transitionListParserMachine
        { state := TransitionListParserState.findCount
            TransitionListParserMarker.initial
          tape :=
            transitionListParserOptionTape []
              ((MachineDescription.encodeNatAppend 0 tokens).map some) }
        { state := TransitionListParserState.halt
          tape :=
            transitionListParserOptionTape
              [some MachineCodeSymbol.done]
              (tokens.map some) } := by
    simpa [MachineDescription.encodeNatAppend,
      MachineDescription.encodeNat] using
      transitionListParserMachine_step_findCount_done
        TransitionListParserMarker.initial [] (tokens.map some)
  have hcomp :
      TuringMachine.Computes transitionListParserMachine
        { state := TransitionListParserState.findCount
            TransitionListParserMarker.initial
          tape :=
            transitionListParserOptionTape []
              ((MachineDescription.encodeNatAppend 0 tokens).map some) }
        { state := TransitionListParserState.halt
          tape :=
            transitionListParserOptionTape
              [some MachineCodeSymbol.done]
              (tokens.map some) } :=
    TuringMachine.Computes.step hstep
      (TuringMachine.Computes.refl _)
  have hhalts :
      TuringMachine.HaltsFrom transitionListParserMachine
        { state := TransitionListParserState.findCount
            TransitionListParserMarker.initial
          tape :=
            transitionListParserOptionTape []
              ((MachineDescription.encodeNatAppend 0 tokens).map some) } :=
    TuringMachine.halts_from_of_computes hcomp rfl
  simpa [TuringMachine.HaltsOnInput, TuringMachine.initial,
    transitionListParserMachine,
    transitionListParserOptionTape_nil_eq_input] using hhalts

theorem transitionListParserMachine_count_zero_spec
    (tokens : Word MachineCodeSymbol) :
    TuringMachine.HaltsOnInput transitionListParserMachine
        (MachineDescription.encodeNatAppend 0 tokens) ∧
      (exists transitions : List TransitionDescription,
       exists suffix : Word MachineCodeSymbol,
        MachineDescription.decodeTransitions 0 tokens =
          some (transitions, suffix)) := by
  exact
    ⟨transitionListParserMachine_halts_count_zero tokens,
      ⟨[], tokens, rfl⟩⟩

theorem transitionListParserMachine_halts_consTransition
    (t : TransitionDescription)
    (rest : List TransitionDescription)
    (suffix : Word MachineCodeSymbol)
    (hrest :
      TuringMachine.HaltsOnInput transitionListParserMachine
        (MachineDescription.encodeNatAppend rest.length
          (MachineDescription.encodeTransitionsAppend rest suffix))) :
    TuringMachine.HaltsOnInput transitionListParserMachine
      (MachineDescription.encodeNatAppend (t :: rest).length
        (MachineDescription.encodeTransitionsAppend (t :: rest) suffix)) := by
  cases rest with
  | nil =>
      simpa [MachineDescription.encodeTransitionsAppend] using
        transitionListParserMachine_halts_oneTransition t suffix
  | cons u more =>
      have hcomp :=
        transitionListParserMachine_computes_nextTransition_to_markPosition
          (u :: more).length t
          (MachineDescription.encodeTransitionsAppend (u :: more) suffix)
      have hmark :=
        transitionListParserMachine_haltsFrom_markPosition_canonicalContinuation
          t (u :: more) suffix
      have hfrom :=
        TuringMachine.halts_from_of_computes_prefix hcomp hmark
      simpa [TuringMachine.HaltsOnInput, TuringMachine.initial,
        transitionListParserMachine,
        transitionListParserOptionTape_nil_eq_input,
        MachineDescription.encodeTransitionsAppend] using hfrom

theorem transitionListParserMachine_halts_encodeTransitionsAppend
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.HaltsOnInput transitionListParserMachine
      (MachineDescription.encodeNatAppend transitions.length
        (MachineDescription.encodeTransitionsAppend transitions suffix)) := by
  cases transitions with
  | nil =>
      simpa [MachineDescription.encodeTransitionsAppend] using
        transitionListParserMachine_halts_count_zero suffix
  | cons t rest =>
      exact
        transitionListParserMachine_halts_consTransition
          t rest suffix
          (transitionListParserMachine_halts_encodeTransitionsAppend
            rest suffix)


end Computability
end FoC
